# Formal Conjectures style draft

This is a local overlay for
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/tree/c77fdd446d23539302aa73bcfae4a9fa962b8382),
reviewed against seven geometry, probability and analysis examples and its
`CONTRIBUTING.md` and `STATEMENTS.md`. It is not an FC submission or acceptance.

The review compared the following actual patterns, rather than imposing a
definition-count limit:

| Upstream example | Pattern checked |
|---|---|
| `Wikipedia/SquarePacking.lean` | Named shapes and a packing structure; bounds and question statements |
| `Arxiv/2607.03582/LpRogersShephard.lean` | Named geometric predicates, source-specific docstrings and a proved constant check |
| `Arxiv/2605.18081/FisherInformationConvexity.lean` | Named admissibility conditions and explicit regularity variants |
| `Paper/CourtadeKumar.lean` | Concrete probability models, proved model correspondence and special cases |
| `Arxiv/2209.04540/SpectralSetsAndWeakTiling.lean` | Named product properties and dimension-specific statements |
| `Wikipedia/Kakeya.lean` | A named conjecture predicate and small proved cases |
| `Paper/DeGiorgi.lean` | A solution structure and a named common conclusion |

| Local file | Destination in that FC checkout |
|---|---|
| `E8Leech.lean` | `FormalConjectures/Paper/E8Leech.lean` |
| `FormalConjecturesForMathlib/Probability/SimplePointProcess.lean` | Same relative path |
| `for-mathlib-index.patch` | Apply to `FormalConjecturesForMathlib.lean` |

The problem file imports `FormalConjecturesUtil`, uses the module/public-section
conventions, gives its manuscript source and has category and AMS attributes.
The copyright/license header is omitted from this local draft at the author's
request. Its checker omits only FC's copyright-header linter; all other project
linters remain enabled.
Its four definitions describe the two lattices, the Golay block and the
quantitative crystallization property. Generic point-process definitions belong
in the support file, whose API lemmas are proved without `sorry`.

The two research statements have intentional `sorry` slots. Two short coordinate
tests have complete proofs. Complete research proofs, plus Gaussian, positive
mixture and equality-law results, remain in `../lean/` and its 13 Comparator targets.
No `formal_proof` URL is asserted before the matching proof is published.
Coordinate and Golay-data provenance is retained in `../THIRD_PARTY.txt`.

From `../lean/`, after dependencies and canonical proof objects are available:

```sh
lake env python3 comparator/check-fc-draft.py --compile
```

This downloads hash-pinned public FC utility sources into `.lake/fc-upstream`,
applies the support overlay, builds the utility closure, runs the actual FC
project linters on the problem at its intended module path, and separately
proves correspondence to the canonical primary types. To use an existing local
source snapshot and dependency directory without network access:

```sh
lake env python3 comparator/check-fc-draft.py --compile \
  --fc-root /path/to/fc-checkout --packages /path/to/lean/.lake/packages --offline
```

`../lean/comparator/fc-upstream.json` records the upstream commit and source hashes.
`../verification/fc-upstream-style-review.json` records the examples reviewed;
`../verification/local-FClikelean.json` and `fc-style-correspondence.json` record
the actual checks. These checks do not complete the original-manuscript review:
the draft explicitly states the measurable-subevent form, while the manuscript's
full-event Borelness and other bridges remain under review. The author
reauthorized formal CI on 28 October 2026; issue posting remains on hold.
