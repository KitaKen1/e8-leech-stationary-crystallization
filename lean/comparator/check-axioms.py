from pathlib import Path
import json,re,sys
root=Path(__file__).resolve().parents[1];cfg=json.loads((root/'comparator.json').read_text());s=Path(sys.argv[1]).read_text();observed={n:set(a.strip() for a in group.split(',') if a.strip()) for n,group in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",s,re.S)}
for n in re.findall(r"'([^']+)' does not depend on any axioms",s):observed[n]=set()
assert set(cfg['theorem_names'])<=observed.keys()
assert all(v<=set(cfg['permitted_axioms']) for v in observed.values())
print(json.dumps(dict(success=True,target_count=len(cfg['theorem_names']),unexpected_axioms=[])))
