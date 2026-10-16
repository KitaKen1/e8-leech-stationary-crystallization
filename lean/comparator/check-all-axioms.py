"""Require every original audit request and reject nonstandard axioms in its closure."""
from pathlib import Path
import json,re,sys
root=Path(__file__).resolve().parents[1];log=Path(sys.argv[1]);s=log.read_text();expected=set(re.findall(r'^#print axioms\s+(\S+)',(root/'E8Leech/Audit.lean').read_text(),re.M))
observed={n:{a.strip() for a in ax.split(',') if a.strip()} for n,ax in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",s,re.S)}
for n in re.findall(r"'([^']+)' does not depend on any axioms",s):observed[n]=set()
assert expected<=observed.keys(),sorted(expected-observed.keys())
unexpected={n:sorted(ax-{'propext','Classical.choice','Quot.sound'}) for n,ax in observed.items() if ax-{'propext','Classical.choice','Quot.sound'}};assert not unexpected,unexpected
result=dict(success=True,unique_audit_requests=len(expected),reported_declarations=len(observed),unexpected_axioms=unexpected)
if len(sys.argv)>2:Path(sys.argv[2]).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
