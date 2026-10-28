#!/usr/bin/env python3
"""Run the user-requested private -> public CI sequence with exact-commit success gates.
Authentication uses Git's configured GitHub credential helper; credentials never enter receipts.
"""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,urllib.request,urllib.error
ROOT=Path(__file__).resolve().parents[1];OWNER='KitaKen1';PUBLIC='e8-leech-stationary-crystallization';PRIVATE='e8-leech-crystallization-ci-20261016'
p=argparse.ArgumentParser();p.add_argument('stage',choices=['private','status','jobs','public','public-status','public-jobs']);a=p.parse_args()
manifest=ROOT/'PUBLICATION-MANIFEST.json';state=json.loads(manifest.read_text())
if a.stage in ['private','public'] and state.get('ci_resume_requires_user_instruction',False):raise SystemExit('CI/publication are on hold at the user request. Do not resume without a new user instruction.')
env=os.environ.copy();env['GIT_TERMINAL_PROMPT']='0'
r=subprocess.run(['git','credential','fill'],input='protocol=https\nhost=github.com\n\n',env=env,text=True,capture_output=True,timeout=20)
if r.returncode:raise SystemExit('No noninteractive GitHub credential')
fields=dict(l.split('=',1) for l in r.stdout.splitlines() if '=' in l);token=fields.get('password')
if not token:raise SystemExit('Git credential helper returned no token')
def api(path,data=None,method=None):
 req=urllib.request.Request('https://api.github.com/'+path,data=json.dumps(data).encode() if data is not None else None,headers={'User-Agent':'E8Leech-publication','Accept':'application/vnd.github+json','Authorization':'Bearer '+token,'Content-Type':'application/json'},method=method)
 try:
  with urllib.request.urlopen(req,timeout=45) as response:
   body=response.read();return json.loads(body) if body else None
 except urllib.error.HTTPError as e:
  if e.code==404:return None
  raise RuntimeError('GitHub API HTTP '+str(e.code)+' for '+path) from None
if api('user')['login']!=OWNER:raise SystemExit('Authenticated account does not match the intended owner')
def git(*args):return subprocess.check_output(['git','-C',str(ROOT),*args],env=env,text=True).strip()
if git('remote','get-url','origin')!='https://github.com/'+OWNER+'/'+PUBLIC+'.git':raise SystemExit('Unexpected public remote')
commit=git('rev-parse','HEAD')
if a.stage=='private':
 local=json.loads((ROOT/'verification/local-comparator-apis.json').read_text());review=json.loads((ROOT/'verification/statement-review.json').read_text())
 if not local['success']:raise SystemExit('Local formal comparison has not passed')
 if not review['success']:
  # The author explicitly resumed formal CI before completion of the manuscript
  # review. Keep that review incomplete instead of treating a build as its proof.
  authorization_path=state.get('ci_authorization')
  authorization=json.loads((ROOT/authorization_path).read_text()) if authorization_path else {}
  if not (authorization.get('formal_ci_authorized') and authorization.get('manuscript_review_may_remain_incomplete')):
   raise SystemExit('Manuscript review incomplete and no explicit formal-CI authorization recorded')
 for name,h in local['source_sha256'].items():
  if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=h:raise SystemExit('Source changed after local comparison: '+name)
 subprocess.run(['git','-C',str(ROOT),'diff','--quiet','HEAD','--','lean','leanWithoutComparator','FClikelean','.github'],check=True)
 subprocess.run(['python3',str(ROOT/'lean/comparator/check-inputs.py')],check=True)
 repo=api('repos/'+OWNER+'/'+PRIVATE)
 if repo is None:repo=api('user/repos',dict(name=PRIVATE,private=True,description='Private CI staging for E8/Leech stationary crystallization, 2026-10-16'))
 if not repo['private']:raise SystemExit('Private CI repository is not private')
 subprocess.run(['git','-C',str(ROOT),'push','https://github.com/'+OWNER+'/'+PRIVATE+'.git','HEAD:refs/heads/publication-test'],env=env,check=True)
 state.update(status='private CI candidate pushed; awaiting exact-commit result',private_repository=OWNER+'/'+PRIVATE,private_tested_commit=commit,private_candidate_pushed=True,public_candidate_pushed=False,private_ci_run=None)
 manifest.write_text(json.dumps(state,indent=2)+'\n');print(json.dumps({k:state[k] for k in ['status','private_repository','private_tested_commit']}))
else:
 public_check=a.stage.startswith('public-')
 repo_name=PUBLIC if public_check else PRIVATE;branch='main' if public_check else 'publication-test'
 runs=api('repos/'+OWNER+'/'+repo_name+'/actions/runs?branch='+branch+'&per_page=30')
 if runs is None:raise SystemExit('Private CI repository or Actions is inaccessible')
 expected=state.get('public_tested_commit' if public_check else 'private_tested_commit');matching=[r for r in runs['workflow_runs'] if r['head_sha']==expected and r['path']=='.github/workflows/comparator.yml']
 if not matching:raise SystemExit('No workflow run exists for the exact private candidate')
 run=matching[0];summary={k:run[k] for k in ['id','html_url','head_sha','status','conclusion','run_attempt']};state['public_ci_run' if public_check else 'private_ci_run']=summary;manifest.write_text(json.dumps(state,indent=2)+'\n');print(json.dumps(summary))
 if a.stage in ['jobs','public-jobs']:
  jobs=api('repos/'+OWNER+'/'+repo_name+'/actions/runs/'+str(run['id'])+'/jobs?per_page=100')
  print(json.dumps([{k:j[k] for k in ['id','name','status','conclusion','html_url','steps']} for j in jobs['jobs']]))
 if public_check and run['status']=='completed' and run['conclusion']=='success':
  state['status']='private and public CI passed at the exact candidate commit';manifest.write_text(json.dumps(state,indent=2)+'\n')
 if a.stage=='public':
  if run['status']!='completed' or run['conclusion']!='success':raise SystemExit('Public publication blocked: private CI has not succeeded for the exact commit')
  if commit!=expected:raise SystemExit('Local commit changed after private CI; test it privately first')
  subprocess.run(['git','-C',str(ROOT),'diff','--quiet','HEAD','--','lean','leanWithoutComparator','FClikelean','.github'],check=True)
  subprocess.run(['python3',str(ROOT/'lean/comparator/check-inputs.py')],check=True)
  public=api('repos/'+OWNER+'/'+PUBLIC)
  if public is None or public['private']:raise SystemExit('Existing public repository is missing or not public')
  subprocess.run(['git','-C',str(ROOT),'fetch','origin','main'],env=env,check=True)
  subprocess.run(['git','-C',str(ROOT),'merge-base','--is-ancestor','origin/main',commit],check=True)
  subprocess.run(['git','-C',str(ROOT),'push','origin','HEAD:refs/heads/main'],env=env,check=True)
  state.update(status='private CI passed; public candidate pushed, awaiting public CI',public_candidate_pushed=True,public_tested_commit=commit)
  manifest.write_text(json.dumps(state,indent=2)+'\n')
