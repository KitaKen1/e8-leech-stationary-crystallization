#!/usr/bin/env python3
"""Build one dependency-ordered CI stage, retaining source/object receipts for every module."""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,time
p=argparse.ArgumentParser();p.add_argument('stage',type=int);a=p.parse_args();root=Path(__file__).resolve().parents[1];repo=root.parent
plan=json.loads((root/'comparator/build-plan.json').read_text());record=repo/'build-receipt/build.json';record.parent.mkdir(exist_ok=True)
state=json.loads(record.read_text()) if record.exists() else dict(success=False,method='source-only staged Linux Lake build',modules=[])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for r in state['modules']:
 if sha(root/r['source'])!=r['source_sha256']:raise SystemExit('Stale source receipt: '+r['module'])
 for f,h in r['objects'].items():
  if sha(root/f)!=h:raise SystemExit('Stale object receipt: '+f)
for m in plan['stages'][a.stage]:
 source=root/(m.replace('.','/')+'.lean');start=time.monotonic();log=record.parent/(m+'.log')
 env=os.environ.copy();env['LEAN_NUM_THREADS']='1';env['PYTHONOPTIMIZE']='0'
 with log.open('w') as f:r=subprocess.run(['lake','--no-ansi','--no-cache','build','+'+m],cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=7200)
 output=log.read_text();fatal=r.returncode!=0 or re.search(r'(?im)^\s*PANIC\b',output)
 # Imported upstream linter warnings do not weaken any checked theorem. Local warnings are fatal.
 local_warning=bool(re.search(r'(?m)(?:^|\n)(?:[^\n]*?/)?(?:E8Leech/|FCSolution\.lean|FCAudit\.lean)[^\n]*warning:',output))
 obj=root/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean')
 result=dict(module=m,source=source.relative_to(root).as_posix(),source_sha256=sha(source),exit_code=r.returncode,elapsed_seconds=time.monotonic()-start,local_warnings=local_warning,objects={})
 if obj.is_file():
  for f in [obj,Path(str(obj)+'.server'),Path(str(obj)+'.private')]:
   if f.is_file():result['objects'][f.relative_to(root).as_posix()]=sha(f)
 state['modules'].append(result);state['last_stage']=a.stage;state['success']=False;record.write_text(json.dumps(state,indent=2)+'\n');print(m,r.returncode,round(result['elapsed_seconds'],1),flush=True)
 if fatal or local_warning or not obj.is_file():print(output[-12000:]);raise SystemExit(1)
 # Large Lake setup metadata is reproducible and not required by downstream jobs.
 for f in (root/'.lake/build/ir').rglob('*.setup.json'):f.unlink()
expected=[m for stage in plan['stages'][:a.stage+1] for m in stage]
if [r['module'] for r in state['modules']]!=expected:raise SystemExit('Incomplete stage coverage')
if a.stage==len(plan['stages'])-1:
 subprocess.run(['python3',str(root/'comparator/check-all-axioms.py'),str(record.parent/'E8Leech.Audit.log'),str(record.parent/'all-axioms.json')],check=True)
state['success']=a.stage==len(plan['stages'])-1;state['complete_stages']=a.stage+1;record.write_text(json.dumps(state,indent=2)+'\n')
print('STAGE_PASS',a.stage,flush=True)
