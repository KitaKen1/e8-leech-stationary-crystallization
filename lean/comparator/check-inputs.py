#!/usr/bin/env python3
"""Check immutable targets, definition isolation and byte-identical proof distributions."""
from pathlib import Path
import argparse,hashlib,json,re,sys
ROOT=Path(__file__).resolve().parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(p,msg):
 if not p:raise SystemExit(msg)
def strip(s):
 # Delegate nested-comment and string handling to the project's declaration scanner.
 sys.path.insert(0,str(ROOT/'lean/scripts'))
 from lean_declarations import _without_comments
 return _without_comments(s)
def headers(s):return re.findall(r'(?m)^theorem ([\s\S]*?) := by\n',s)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--receipt-dir',type=Path);a=ap.parse_args()
 pins=json.loads((ROOT/'lean/comparator/pins.json').read_text());cfg=json.loads((ROOT/'lean/comparator.json').read_text())
 for name,h in pins['files_sha256'].items():require((ROOT/name).is_file() and sha(ROOT/name)==h,'Pinned file changed: '+name)
 require(cfg['theorem_names']==pins['targets'] and len(cfg['theorem_names'])==13,'Incomplete target list')
 require(cfg['permitted_axioms']==['propext','Classical.choice','Quot.sound'],'Unexpected axiom permissions')
 modules=json.loads((ROOT/'lean/comparator/reference-definition-modules.json').read_text())
 refs=[(ROOT/'lean'/(m.replace('.','/')+'.lean')).read_text() for m in modules]
 law=(ROOT/'lean/FCTargetDefinitions.lean').read_text();reference='\n'.join(refs)+'\n'+law;challenge=(ROOT/'lean/Challenge.lean').read_text();solution=(ROOT/'lean/FCSolution.lean').read_text();draft=(ROOT/'FClikelean/E8Leech.lean').read_text()
 require(all(n.startswith('Mathlib.') for n in re.findall(r'^import (\S+)',refs[0],re.M)),'Reference imports proof')
 require(all(re.findall(r'^import (\S+)',s,re.M)==[modules[i-1]] for i,s in enumerate(refs) if i),'Reference dependency isolation changed')
 require(re.findall(r'^import (\S+)',law,re.M)==[modules[-1]],'Reference aggregate import changed')
 require(re.findall(r'^import (\S+)',challenge,re.M)==['FCTargetDefinitions'],'Challenge import changed')
 require('FCTargetDefinitions' not in solution and 'Challenge' not in solution,'Solution imports trusted statement environment')
 require(headers(challenge)==headers(solution)==headers(draft),'The 13 mathematical statements differ')
 require(all(re.sub(r'\s+',' ',strip(re.sub(r'^import \S+\n','',x,flags=re.M))).strip() in re.sub(r'\s+',' ',strip(draft)).strip() for x in refs),'FC-like draft definitions differ from independent reference')
 require(not re.search(r'\b(sorry|admit|axiom|native_decide)\b',strip(reference)),'Hole or custom axiom in reference definitions')
 require(not re.search(r'\b(sorry|admit|axiom|native_decide)\b',strip(solution)),'Hole or custom axiom in solution')
 require(len(re.findall(r'\bsorry\b',strip(challenge)))==13,'Unexpected challenge holes')
 require(len(re.findall(r'\bsorry\b',strip(draft)))==13,'Unexpected FC-like draft holes')
 shared=json.loads((ROOT/'lean/comparator/shared-proof-sources.json').read_text())
 for name,h in shared.items():
  for folder in ['lean','leanWithoutComparator']:require(sha(ROOT/folder/name)==h,'Shared proof source changed: '+folder+'/'+name)
 actual={p.relative_to(ROOT/'leanWithoutComparator').as_posix() for p in (ROOT/'leanWithoutComparator').rglob('*.lean') if '.lake' not in p.parts}
 require(actual==set(shared),'Supplementary proof source coverage differs')
 require((ROOT/'lean/lean-toolchain').read_bytes()==(ROOT/'leanWithoutComparator/lean-toolchain').read_bytes(),'Toolchain mismatch')
 require((ROOT/'lean/lake-manifest.json').read_bytes()==(ROOT/'leanWithoutComparator/lake-manifest.json').read_bytes(),'Dependency mismatch')
 result=dict(success=True,targets=cfg['theorem_names'],target_count=13,shared_proof_sources=len(shared),independent_reference_imports_mathlib_only=True,fc_draft_matches_reference=True,proof_bridge_does_not_import_challenge=True,pins_sha256=sha(ROOT/'lean/comparator/pins.json'))
 if a.receipt_dir:a.receipt_dir.mkdir(parents=True,exist_ok=True);(a.receipt_dir/'input-check.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result))
if __name__=='__main__':main()
