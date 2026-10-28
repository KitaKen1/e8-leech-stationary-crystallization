# Canonical Lean proof

The entry point is [FCSolution.lean](FCSolution.lean), importing the completed
[E8Leech.lean](E8Leech.lean) proof library.

```sh
lake exe cache get
lake build
```

Lean 4.33.1 and FC Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` are fixed.
[Challenge.lean](Challenge.lean) contains the 13 reference theorem holes and imports
standalone Mathlib-based [definitions](FCTargetDefinitions.lean). The proof never
imports it. [comparator.json](comparator.json) lists the comparison targets and
three permitted axioms.

The two primary targets cover quantitative Riesz crystallization for E₈ and Leech
at every `0 < γ < 1/12`. Supporting targets cover Gaussian and positive-mixture
crystallization, six zero-excess/exact-lattice equivalences and a generic
stationary exact-lattice law classification. See
[the correspondence table](comparator/TARGET-CORRESPONDENCE.md).

The configured CI builds six proof stages from source. The checking job builds
the trusted Challenge before restoring proof products, then runs Comparator in
an unprivileged Linux sandbox. A separate job runs a fresh Lean-kernel replay.
Formal CI was reauthorized on 28 October 2026. The earlier private run was
cancelled; the revised candidate has not yet passed private or public CI. Local checks reused development proof
objects; [the manifest](../PUBLICATION-MANIFEST.json) records their scope.

[comparator/shared-proof-sources.json](comparator/shared-proof-sources.json)
records the 1,537 Lean sources shared byte-for-byte with `leanWithoutComparator/`.
That supplementary copy omits the independent reference, audit and Comparator
configuration/scripts; its shared definitions and proofs are unchanged.
See [the verification guide](comparator/README.md) for local checks and the
remaining original-manuscript review.
