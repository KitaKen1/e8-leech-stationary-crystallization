#!/usr/bin/env python3
"""Verify provenance and all restored source/object hashes before CI resumes."""
from pathlib import Path
import base64
import hashlib
import json
import os
import re
import sys
import urllib.request

root = Path(__file__).resolve().parents[2]
run_id = sys.argv[1]
if not re.fullmatch(r'[1-9][0-9]*', run_id):
    raise SystemExit('Resume run ID must be a positive integer')
repo = os.environ['GITHUB_REPOSITORY']
if not re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', repo):
    raise SystemExit('Invalid repository')
headers = {'Accept': 'application/vnd.github+json', 'User-Agent': 'E8Leech-CI-resume',
           'Authorization': 'Bearer ' + os.environ['GH_TOKEN']}


def api(path):
    request = urllib.request.Request('https://api.github.com/repos/' + repo + '/' + path,
                                     headers=headers)
    with urllib.request.urlopen(request, timeout=60) as response:
        return json.load(response)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


run = api('actions/runs/' + run_id)
if run['path'] != '.github/workflows/comparator.yml' or run['status'] != 'completed':
    raise SystemExit('Resume source is not a completed verification workflow')
jobs = api('actions/runs/' + run_id + '/jobs?per_page=100')['jobs']
for stage in range(5):
    matches = [job for job in jobs if job['name'] == 'build_' + str(stage)]
    if len(matches) != 1 or matches[0]['conclusion'] != 'success':
        raise SystemExit('Source build stage did not succeed: ' + str(stage))
artifacts = api('actions/runs/' + run_id + '/artifacts?per_page=100')['artifacts']
matches = [a for a in artifacts if a['name'] == 'proof-stage-4' and not a['expired']]
if len(matches) != 1:
    raise SystemExit('Missing or expired stage-4 artifact')
source_commit = run['head_sha']
required_inputs = ['lean/lean-toolchain', 'lean/lake-manifest.json', 'lean/lakefile.toml',
                   'lean/comparator/build-plan.json', 'lean/comparator/shared-proof-sources.json']
for name in required_inputs:
    data = api('contents/' + name + '?ref=' + source_commit)
    if base64.b64decode(data['content']) != (root / name).read_bytes():
        raise SystemExit('Resume build input changed: ' + name)
plan = json.loads((root / 'lean/comparator/build-plan.json').read_text())
receipt = json.loads((root / 'build-receipt/build.json').read_text())
expected = [module for stage in plan['stages'][:5] for module in stage]
if (receipt.get('complete_stages') != 5 or
        [record['module'] for record in receipt['modules']] != expected):
    raise SystemExit('Restored receipt does not cover the first five complete stages')
objects = 0
for record in receipt['modules']:
    source = root / 'lean' / record['source']
    if (record['exit_code'] != 0 or record['local_warnings'] or not record['objects'] or
            sha(source) != record['source_sha256']):
        raise SystemExit('Invalid restored source receipt: ' + record['module'])
    for name, digest in record['objects'].items():
        path = root / 'lean' / name
        if not path.is_file() or sha(path) != digest:
            raise SystemExit('Restored object hash mismatch: ' + name)
        objects += 1
result = dict(success=True, source_repository=repo, source_run_id=int(run_id),
              source_commit=source_commit, current_commit=os.environ['GITHUB_SHA'],
              source_run_attempt=run['run_attempt'], source_artifact_id=matches[0]['id'],
              source_artifact_digest=matches[0].get('digest'),
              verified_build_inputs=required_inputs, source_modules_verified=len(expected),
              compiled_objects_verified=objects, resumed_at_stage=5,
              subsequent_source_build_and_comparator_and_replay_required=True)
(root / 'build-receipt/resume-provenance.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
