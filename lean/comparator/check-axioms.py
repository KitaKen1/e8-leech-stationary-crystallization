from pathlib import Path
import json,re,sys
from axiom_log import parse_axioms, check_axioms
root=Path(__file__).resolve().parents[1];cfg=json.loads((root/'comparator.json').read_text());s=Path(sys.argv[1]).read_text();observed=parse_axioms(s)
check_axioms(observed,cfg['theorem_names'],cfg['permitted_axioms'])
print(json.dumps(dict(success=True,target_count=len(cfg['theorem_names']),unexpected_axioms=[])))
