"""Require every original audit request and reject nonstandard axioms in its closure."""
from pathlib import Path
import json,re,sys
from axiom_log import parse_axioms, check_axioms
root=Path(__file__).resolve().parents[1];log=Path(sys.argv[1]);s=log.read_text();expected=set(re.findall(r'^#print axioms\s+(\S+)',(root/'E8Leech/Audit.lean').read_text(),re.M))
observed=parse_axioms(s)
check_axioms(observed,expected,{'propext','Classical.choice','Quot.sound'})
unexpected={}
result=dict(success=True,unique_audit_requests=len(expected),reported_declarations=len(observed),unexpected_axioms=unexpected)
if len(sys.argv)>2:Path(sys.argv[2]).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
