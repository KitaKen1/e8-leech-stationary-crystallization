# Reproducible target verification

Run `python3 lean/comparator/check-inputs.py` from the repository root for source
pins, target isolation and the shared proof-source identities.
The configured workflow builds `lean/`, compares all 13 targets in
[comparator.json](../comparator.json), audits permitted axioms and replays the
exported solution in Lean's builtin kernel. A separate fresh replay job checks
the complete FCSolution environment.

The proof, reference, Comparator and Lean4export use Lean 4.33.1. Dependency
revisions and the two checker toolchain-only changes from 4.33.0 to 4.33.1 are
recorded in [pins.json](pins.json). The trusted reference definitions depend
only on Mathlib, contain no holes, and are compiled before proof products are
restored in the comparison job.

## Local checks

After installing dependencies, build the canonical proof from `lean/` with:

```sh
lake exe cache get
lake build
lake build Challenge FCAudit
lake env lean FCAudit.lean
```

From the same directory, check the FC overlay and its primary proof correspondence:

```sh
lake env python3 comparator/check-fc-draft.py --compile
```

This obtains hash-pinned public FC utility sources, installs the support overlay
and runs the actual FC project linters. See [the FC-style guide](../../FClikelean/README.md)
for an offline-source option.

## Linux verification

[The workflow](../../.github/workflows/comparator.yml) prepares pinned Comparator,
Lean4export and Landrun binaries, builds six proof stages and runs
[run-check.sh](run-check.sh) with Linux sandboxing and AF_UNIX disabled.
It also performs a separate `leanchecker --fresh FCSolution` replay.
Intermediate proof artifacts are retained for two days and receipts for 90 days.

## Actual status

Local independent-reference compilation, all 13 direct upstream API comparisons,
the permitted-axiom audit and FC primary-type correspondence passed. The local
proof check reused development objects. The complete Comparator CLI, exported
JSON parser, Linux sandbox and fresh replay are not certified by those local
receipts.

[Original-manuscript review](../../verification/original-statement-review.json)
is incomplete. The earlier private CI run was cancelled; the current revision
has no successful private/public CI or archive yet. The author reauthorized
formal CI on 28 October 2026, with private CI preceding public CI. See
[PUBLICATION-MANIFEST.json](../../PUBLICATION-MANIFEST.json) for the actual status.
