# Reproducible target verification

Run `python3 lean/comparator/check-inputs.py` from the repository root for source
pins, target isolation and the shared proof-source identities.
The configured workflow builds `lean/` and compares all 13 targets in
[comparator.json](../comparator.json) in three required jobs: six E₈ targets,
six Leech targets and the stationary lattice-law target. Each job audits
permitted axioms and replays its complete exported dependency closure in Lean's
builtin kernel. A separate fresh replay job checks the complete FCSolution
environment.

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

## Resume successful source stages

The workflow-dispatch input `resume_run_id` can reuse `proof-stage-4` from an
older run of this same repository. It requires successful source stages 0-4,
matching toolchain/dependency/build-plan inputs, and matching hashes for every
restored source and compiled object. Stage 5 is rebuilt from source, and the full
axiom audit, Comparator and fresh replay remain required. The new receipt records
the source run, artifact and commit; reuse is not described as a new clean build.

For a run whose complete `build_5` succeeded, `resume_complete_build=true`
reuses `proof-stage-5` instead. It requires all 928 source/object receipts and
matching build inputs, rechecks the full axiom audit, and then reruns FC checks,
Comparator and the independent fresh kernel replay. It does not label restored
proof objects as a new clean source build.

Each Comparator job has a sandboxed CLI budget of 340 minutes, inside its
360-minute job budget. Both earlier single-job attempts timed out, including
[the 340-minute retry](https://github.com/KitaKen1/e8-leech-crystallization-ci-20261016/actions/runs/40821237822).
Its log reached `Running Lean default kernel on solution.` before the timeout;
the separate fresh replay succeeded in 3:58:03. Increasing the single-job limit
did not resolve the failure.

[comparison_groups.py](comparison_groups.py) now partitions the canonical
configuration into the three groups. It rejects missing, duplicate or unassigned
targets and copies every other configuration field unchanged. The matrix runs
the unmodified upstream Comparator separately on each group, including its
builtin kernel replay. All three matrix jobs and the independent full fresh
replay must succeed. Each artifact records the canonical configuration hash and
the exact partition. Grouped execution has not yet passed CI.

The 29 October 2026 repair fixes apostrophes in the axiom-log parser. In the
previous run all 928 modules compiled; the final Python audit rejected 50 report
names containing apostrophes. Rechecking its actual logs with the corrected
parser covered all 9,582 audit declarations and all 13 comparison targets with
only the three permitted axioms. That local repair check is not a successful CI
run; the revised workflow must still complete.

## Actual status

Local independent-reference compilation, all 13 direct upstream API comparisons,
the permitted-axiom audit and FC primary-type correspondence passed. The local
proof check reused development objects. The complete Comparator CLI, exported
JSON parser, Linux sandbox and fresh replay are not certified by those local
receipts.

[Original-manuscript review](../../verification/original-statement-review.json)
is incomplete. The initial private CI run was cancelled, and later retries failed;
there is no successful complete private/public CI or archive yet. The author reauthorized
formal CI on 28 October 2026, with private CI preceding public CI. See
[PUBLICATION-MANIFEST.json](../../PUBLICATION-MANIFEST.json) for the actual status.
