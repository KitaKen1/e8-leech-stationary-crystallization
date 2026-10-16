"""Replay all project declarations together with Lean's bundled kernel API.

Exported/server/private parts are loaded as in the pinned LeanChecker.lean.
External imports are loaded once; no project declaration may already be present.
This remains the Lean kernel, not an independent implementation.
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
p.add_argument('--clean-build-record', type=Path, required=True)
p.add_argument('--record', type=Path, required=True)
args = p.parse_args()
root = args.root.resolve()
helper = Path(__file__).with_name('ReplayProjectOnce.lean')
driver_sha = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
helper_sha = hashlib.sha256(helper.read_bytes()).hexdigest()
args.record.parent.mkdir(parents=True, exist_ok=True)
args.record.write_text(json.dumps({'root': str(root), 'success': False,
    'phase': 'validating_clean_build', 'independent_implementation': False,
    'complete_project_source_and_object_hashes_verified': False,
    'driver_sha256': driver_sha, 'helper_source_sha256': helper_sha}, indent=2) + '\n')
build = json.loads(args.clean_build_record.read_text())
assert build['success'] is True and Path(build['root']).resolve() == root
sources = [root / 'E8Leech.lean', *sorted((root / 'E8Leech').glob('*.lean'))]
expected = {str(source.relative_to(root)).removesuffix('.lean').replace('/', '.')
            for source in sources}
assert len(build['modules']) == len(expected), 'Incomplete clean module coverage'
assert {module['module'] for module in build['modules']} == expected, 'Incomplete clean module coverage'
for module in build['modules']:
    source = root / (module['module'].replace('.', '/') + '.lean')
    assert module['exit_code'] == 0 and not module['warnings_detected']
    assert not module['internal_panic_detected']
    assert hashlib.sha256(source.read_bytes()).hexdigest() == module['source_sha256']
    obj = root / '.lake/build/lib/lean' / (module['module'].replace('.', '/') + '.olean')
    assert hashlib.sha256(obj.read_bytes()).hexdigest() == module['olean_sha256']
    expected_objects = {str(file.relative_to(root)) for file in
        [obj, Path(str(obj) + '.server'), Path(str(obj) + '.private')] if file.is_file()}
    assert set(module['object_sha256']) == expected_objects
    for relative, expected_sha in module['object_sha256'].items():
        assert hashlib.sha256((root / relative).read_bytes()).hexdigest() == expected_sha
env = os.environ.copy()
env.pop('LEAN_PATH', None)
env['LEAN_NUM_THREADS'] = '2'
toolchain = (root / 'lean-toolchain').read_text().strip()
command = ['lake', '+' + toolchain, 'env', 'lean', '-DwarningAsError=true',
           '--run', str(helper), *sorted(expected)]
start = time.monotonic()
output_lines = []
with args.record.with_suffix('.log').open('w') as log:
    proc = subprocess.Popen(command, cwd=root, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, bufsize=1)
    for line in proc.stdout:
        log.write(line)
        log.flush()
        output_lines.append(line)
    proc.wait()
output = ''.join(output_lines)
replayed = set(re.findall(r'(?m)^replaying ([\w.]+)$', output))
panic = bool(re.search(r'(?im)^\s*PANIC\b', output))
warnings = bool(re.search(r'(?im)\bwarning:', output))
inventory = re.findall(r'(?m)^project declaration inventory: (\d+)$', output)
result = {'root': str(root), 'command': command, 'toolchain': toolchain,
          'success': proc.returncode == 0 and not panic and not warnings and expected == replayed
              and len(inventory) == 1 and int(inventory[0]) > 0
              and 'Aggregate project replay passed' in output,
          'exit_code': proc.returncode, 'elapsed_seconds': time.monotonic() - start,
          'module_count': len(replayed), 'replayed_modules': sorted(replayed),
          'independent_implementation': False, 'imports_replayed_from_empty_environment': False,
          'implementation': 'Lean.Environment.replay via source-pinned aggregate loader',
          'all_project_declarations_replayed_together': True,
          'project_declarations_preloaded_in_imported_environment': False,
          'project_declaration_inventory': int(inventory[0]) if len(inventory) == 1 else None,
          'helper_source_sha256': helper_sha,
          'complete_project_source_and_object_hashes_verified': True,
          'clean_build_record_sha256': hashlib.sha256(args.clean_build_record.read_bytes()).hexdigest(),
          'driver_sha256': driver_sha, 'output': output}
args.record.parent.mkdir(parents=True, exist_ok=True)
args.record.write_text(json.dumps(result, indent=2) + '\n')
args.record.with_suffix('.log').write_text(output)
print(output, flush=True)
assert result['success'], 'Project replay failed or module coverage differed'
