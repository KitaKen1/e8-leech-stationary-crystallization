"""Parse Lean's printed axiom dependencies, including apostrophes in names."""
import re


def parse_axioms(text):
    observed = {}
    # The closing delimiter is the quote before the literal message, not the
    # first apostrophe inside a Lean identifier. Names never span log lines.
    entries = [(name, {a.strip() for a in axioms.split(',') if a.strip()})
               for name, axioms in re.findall(
                   r"'([^\r\n]+)' depends on axioms:\s*\[([^\]]*)\]", text)]
    entries += [(name, set()) for name in re.findall(
        r"'([^\r\n]+)' does not depend on any axioms", text)]
    for name, axioms in entries:
        if name in observed and observed[name] != axioms:
            raise ValueError('Conflicting axiom reports for ' + name)
        observed[name] = axioms
    return observed


def check_axioms(observed, expected, permitted):
    missing = set(expected) - observed.keys()
    if missing:
        raise ValueError('Missing axiom reports: ' + repr(sorted(missing)))
    unexpected = {name: sorted(axioms - set(permitted))
                  for name, axioms in observed.items() if axioms - set(permitted)}
    if unexpected:
        raise ValueError('Unexpected axioms: ' + repr(unexpected))
