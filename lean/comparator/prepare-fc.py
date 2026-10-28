#!/usr/bin/env python3
"""Build the pinned, unmodified FC utility closure with the local FC overlay.

Downloads only public, hash-pinned sources. Does not submit anything or run CI.
"""
from pathlib import Path
import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import shutil
import subprocess
import time
import urllib.request


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def prepare(root, fc_root, packages, jobs=3, offline=False):
    pins = json.loads((root / 'lean/comparator/fc-upstream.json').read_text())
    fc_root.mkdir(parents=True, exist_ok=True)
    index = 'FormalConjecturesForMathlib.lean'
    support = 'FormalConjecturesForMathlib/Probability/SimplePointProcess.lean'
    extra_import = 'public import FormalConjecturesForMathlib.Probability.SimplePointProcess\n'
    for name, digest in pins['files_sha256'].items():
        dest = fc_root / name
        # The index is the only upstream source intentionally changed by the overlay.
        content = dest.read_bytes() if dest.exists() else b''
        original = content.replace(extra_import.encode(), b'') if name == index else content
        if hashlib.sha256(original).hexdigest() != digest:
            if dest.exists():
                raise RuntimeError('Unexpected upstream source: ' + name)
            if offline:
                raise RuntimeError('Missing pinned source in offline mode: ' + name)
            url = f"https://raw.githubusercontent.com/{pins['repository']}/{pins['commit']}/{name}"
            with urllib.request.urlopen(url, timeout=60) as response:
                content = response.read()
            if hashlib.sha256(content).hexdigest() != digest:
                raise RuntimeError('Upstream hash mismatch: ' + name)
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(content)
    if (fc_root / 'lean-toolchain').read_bytes() != (root / 'lean/lean-toolchain').read_bytes():
        raise RuntimeError('FC toolchain does not match canonical toolchain')
    def mathlib_rev(path):
        return next(p['rev'] for p in json.loads(path.read_text())['packages'] if p['name'] == 'mathlib')
    if mathlib_rev(fc_root / 'lake-manifest.json') != mathlib_rev(root / 'lean/lake-manifest.json'):
        raise RuntimeError('FC Mathlib pin does not match canonical Mathlib pin')
    text = (fc_root / index).read_text().replace(extra_import, '')
    anchor = 'public import FormalConjecturesForMathlib.Probability.FiniteMethod\n'
    if text.count(anchor) != 1:
        raise RuntimeError('Unexpected ForMathlib index')
    (fc_root / index).write_text(text.replace(anchor, anchor + extra_import))
    (fc_root / support).parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(root / 'FClikelean' / support, fc_root / support)
    out = fc_root / '.lake/build/lib/lean'
    logs = fc_root / '.lake/upstream-build'
    out.mkdir(parents=True, exist_ok=True)
    logs.mkdir(parents=True, exist_ok=True)
    sources = {name[:-5].replace('/', '.'): fc_root / name
               for name in [*pins['files_sha256'], support] if name.endswith('.lean')}
    def imported_modules(path):
        return [name.replace('«', '').replace('»', '') for name in
                re.findall(r'^(?:public )?(?:meta )?import (\S+)', path.read_text(), re.M)]
    deps = {m: [d for d in imported_modules(p)
                if d in sources] for m, p in sources.items()}
    needed = set()
    def visit(m):
        if m not in needed:
            needed.add(m)
            for dep in deps[m]:
                visit(dep)
    visit('FormalConjecturesUtil')
    env = os.environ.copy()
    env['LEAN_NUM_THREADS'] = '1'
    package_libs = sorted(p / '.lake/build/lib/lean' for p in packages.iterdir()
                          if (p / '.lake/build/lib/lean').is_dir())
    env['LEAN_PATH'] = os.pathsep.join(map(str, [out, *package_libs]))
    options = ['-j1', '-DElab.async=false', '-Dpp.unicode.fun=true',
               '-DautoImplicit=false', '-DrelaxedAutoImplicit=false']
    input_hashes = {}
    def input_hash(m):
        if m not in input_hashes:
            value = dict(source=sha(sources[m]), options=options,
                         toolchain=(fc_root / 'lean-toolchain').read_text(),
                         mathlib=mathlib_rev(fc_root / 'lake-manifest.json'),
                         dependencies={d: input_hash(d) for d in deps[m]})
            input_hashes[m] = hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()
        return input_hashes[m]
    previous = {}
    if (logs / 'build.json').exists():
        previous = {r['module']: r for r in json.loads((logs / 'build.json').read_text())['records']
                    if r['exit_code'] == 0}
    # Reuse only a dependency-closed set of successfully compiled, unchanged sources.
    done, records = set(), []
    changed = True
    while changed:
        changed = False
        for m in sorted(needed - done):
            record = previous.get(m)
            # Legacy local research-build records predate the overlay; only
            # unaffected upstream modules can be migrated from those records.
            inputs_match = record and (record.get('input_sha256') == input_hash(m) or
                ('input_sha256' not in record and m not in
                 ['FormalConjecturesForMathlib', 'FormalConjecturesUtil',
                  'FormalConjecturesForMathlib.Probability.SimplePointProcess']))
            if (inputs_match and set(deps[m]) <= done and
                    record['source_sha256'] == sha(sources[m]) and
                    (out / (m.replace('.', '/') + '.olean')).exists()):
                record = dict(record, input_sha256=input_hash(m))
                done.add(m)
                records.append(record)
                changed = True
    todo, running = needed - done, {}
    print(f'FC utility: {len(needed)} modules; {len(done)} verified cached sources', flush=True)
    def compile_module(m):
        dest = out / (m.replace('.', '/') + '.olean')
        dest.parent.mkdir(parents=True, exist_ok=True)
        start = time.monotonic()
        result = subprocess.run(['lean', *options, '-o', str(dest), str(sources[m])],
                                cwd=fc_root, env=env, capture_output=True, text=True, timeout=900)
        output = result.stdout + result.stderr
        (logs / (m + '.log')).write_text(output)
        if result.returncode or not dest.exists():
            raise RuntimeError(m + '\n' + output[-12000:])
        return dict(module=m, exit_code=0, elapsed_seconds=time.monotonic() - start,
                    source_sha256=sha(sources[m]), input_sha256=input_hash(m), object_created=True)
    def save(success):
        (logs / 'build.json').write_text(json.dumps(dict(success=success,
            upstream_commit=pins['commit'], completed=len(records), required=len(needed),
            options=options, records=records), indent=2) + '\n')
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        while todo or running:
            ready = sorted(m for m in todo if set(deps[m]) <= done)
            for m in ready[:max(0, jobs - len(running))]:
                todo.remove(m)
                running[pool.submit(compile_module, m)] = m
            if not running:
                raise RuntimeError('FC import dependency cycle')
            finished, _ = concurrent.futures.wait(running, timeout=10,
                         return_when=concurrent.futures.FIRST_COMPLETED)
            for future in finished:
                m = running.pop(future)
                records.append(future.result())
                done.add(m)
                save(False)
                print(f'{len(done)}/{len(needed)} {m}', flush=True)
    save(True)
    return env, dict(upstream_repository=pins['repository'], upstream_commit=pins['commit'],
                     upstream_pinned_inputs=len(pins['files_sha256']),
                     utility_modules=len(needed), upstream_source_changes=[index],
                     overlay_support_sha256=sha(fc_root / support),
                     utility_source_sha256=sha(fc_root / 'FormalConjecturesUtil.lean'))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--fc-root', type=Path, required=True)
    parser.add_argument('--packages', type=Path)
    parser.add_argument('--offline', action='store_true')
    args = parser.parse_args()
    _, result = prepare(args.root.resolve(), args.fc_root.resolve(),
                        (args.packages or args.root / 'lean/.lake/packages').resolve(),
                        offline=args.offline)
    print(json.dumps(result))
