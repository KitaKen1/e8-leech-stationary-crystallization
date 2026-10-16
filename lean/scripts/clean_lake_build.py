"""Compile every local module with Lake, failing on warnings or internal panic.

Targets are built in dependency order to keep memory bounded. This uses Lake's
normal package options and trace handling, unlike direct pinned-cache builds.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

p = argparse.ArgumentParser()
p.add_argument('--root', type=Path, default=Path.cwd())
p.add_argument('--record', type=Path, required=True)
p.add_argument('--batch-size', type=int, default=1)
p.add_argument('--module', action='append',
               help='Build selected modules and their local dependencies; this is not a full check')
p.add_argument('--threads', type=int, default=1, help='Lean threads per process')
args = p.parse_args()
root = args.root.resolve()
toolchain = (root / 'lean-toolchain').read_text().strip()
sources = {'E8Leech': root / 'E8Leech.lean'}
sources.update({'E8Leech.' + f.stem: f for f in (root / 'E8Leech').glob('*.lean')})
imports = {m: set(re.findall(r'(?m)^import\s+(E8Leech[\w.]*)\s*$', f.read_text()))
           for m, f in sources.items()}
order, active, seen = [], set(), set()

def visit(m):
    assert m not in active, m
    if m in seen:
        return
    active.add(m)
    for dependency in sorted(imports[m]):
        visit(dependency)
    active.remove(m)
    seen.add(m)
    order.append(m)

assert args.threads >= 1
for m in args.module or sorted(sources):
    assert m in sources, m
    visit(m)
if not args.module:
    assert order[-1] == 'E8Leech.Audit'
snapshot = root / 'clean-snapshot.json'
snapshot_record = json.loads(snapshot.read_text()) if snapshot.exists() else None
if snapshot_record:
    assert snapshot_record['project_build_outputs_present_before_build'] is False
    for rel, sha in snapshot_record['snapshot_source_sha256'].items():
        assert hashlib.sha256((root / rel).read_bytes()).hexdigest() == sha, rel
assert not list((root / '.lake/build/lib/lean').glob('E8Leech*.olean')), 'Use a new clean checkout'
assert not list((root / '.lake/build/lib/lean/E8Leech').glob('*.olean')), 'Use a new clean checkout'
env = os.environ.copy()
env.pop('LEAN_PATH', None)
env['LEAN_NUM_THREADS'] = str(args.threads)
records = []
result = {'toolchain': toolchain, 'root': str(root), 'method': 'clean source-only checkout; bounded Lake batches; warnings fatal',
          'snapshot': snapshot_record, 'modules': records, 'success': False,
          'driver_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
result['project_build_outputs_absent_at_driver_start'] = True
result['complete_local_library'] = set(order) == set(sources)
result['selected_modules'] = args.module
result['lean_threads'] = args.threads
args.record.parent.mkdir(parents=True, exist_ok=True)
built = set()
assert 1 <= args.batch_size <= 4
while len(built) < len(order):
    batch = [m for m in order if m not in built and imports[m] <= built][:args.batch_size]
    assert batch
    m = batch[-1]
    start = time.monotonic()
    proc = subprocess.run(['lake', '+' + toolchain, '--no-ansi', '--no-cache', '--wfail', 'build', *['+' + m for m in batch]],
                          cwd=root, env=env, text=True, capture_output=True)
    output = proc.stdout + proc.stderr
    panic = bool(re.search(r'(?im)^\s*PANIC\b', output))
    warnings = bool(re.search(r'(?im)\bwarning:', output))
    code = proc.returncode or int(panic or warnings)
    elapsed = time.monotonic() - start
    for m in batch:
        f = sources[m]
        record = {'module': m, 'exit_code': code, 'compiler_exit_code': proc.returncode,
                  'internal_panic_detected': panic, 'warnings_detected': warnings,
                  'elapsed_seconds': elapsed, 'batch': batch,
                  'source_sha256': hashlib.sha256(f.read_bytes()).hexdigest(), 'output': output}
        objects = root / '.lake/build/lib/lean' / (m.replace('.', '/') + '.olean')
        if objects.is_file():
            record['olean_sha256'] = hashlib.sha256(objects.read_bytes()).hexdigest()
            record['object_sha256'] = {
                str(obj.relative_to(root)): hashlib.sha256(obj.read_bytes()).hexdigest()
                for obj in [objects, Path(str(objects) + '.server'), Path(str(objects) + '.private')]
                if obj.is_file()}
        records.append(record)
        print(f'{len(records)}/{len(order)} {m}: exit {code}, batch {elapsed:.1f}s', flush=True)
    args.record.write_text(json.dumps(result, indent=2) + '\n')
    built.update(batch)
    if code:
        print(output, flush=True)
        raise SystemExit(code)
requested, axioms = set(), set()
if 'E8Leech.Audit' in built:
    audit = next(record['output'] for record in records if record['module'] == 'E8Leech.Audit')
    requested = set(re.findall(r"#print axioms ([\w.']+)", sources['E8Leech.Audit'].read_text()))
    reported = set(re.findall(r"'([\w.']+?)' (?:depends on axioms:|does not depend on any axioms)", audit))
    assert requested <= reported, sorted(requested - reported)
    axioms = {a.strip() for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]', audit)
              for a in group.split(',') if a.strip()}
    assert axioms <= {'propext', 'Classical.choice', 'Quot.sound'}, axioms
result.update(success=True, audited_declarations=len(requested), axioms=sorted(axioms),
              axiom_audit_performed='E8Leech.Audit' in built)
args.record.write_text(json.dumps(result, indent=2) + '\n')
print(f'Clean Lake build passed: {len(order)} modules; full coverage={result["complete_local_library"]}; '
      f'audited declarations={len(requested)}', flush=True)
