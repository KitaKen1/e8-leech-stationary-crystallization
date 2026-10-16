# Quantitative stationary crystallization for E₈ and Leech lattices

Lean 4.33.1 formalization of quantitative crystallization and zero-excess law
classification for stationary simple locally finite point processes of intensity
one in dimensions 8 and 24. Mathlib is pinned to
`0df444a360eaa60ab8c11dca51a86af692955474`.

For the covolume-one E₈ or Leech lattice Λ and Riesz exponent s>d, write

```math
\mathcal E_s(\mu)=\mathbb E_\mu\sum_{x\in\Xi\cap[0,1)^d}
  \sum_{y\in\Xi\setminus\{x\}}|x-y|^{-s},\qquad
L_s=\sum_{z\in\Lambda\setminus\{0\}}|z|^{-s}.
```

For every fixed `0<γ<1/12`, constants `C>0` and `0<δ₀<exp(-e)` can be chosen
before the process law. If `0<δ<δ₀` and the ordered energy is at most `L_s+δ`, set

```math
R=\frac{\log(1/\delta)}{\log\log(1/\delta)}.
```

There is a **measurable subevent** of probability at least `1-C R^(-1/2)` on
which **all original points** in the closed ball of radius R admit a two-sided
Hausdorff matching, with error `C δ^γ`, to the isometric image of a finite
subset of Λ; their count is at least `(1-C R^(-1/2)) vol(B̄_R)`.
The case `γ=1/13` is included. Neither ergodicity nor a samplewise density limit
is assumed. The inner energy sum is over the entire configuration, with no
factor of 1/2.

The same conclusion holds for every positive Gaussian parameter, including π,
and every nonzero positive Gaussian mixture with finite lattice energy.
Zero excess is equivalent to an arbitrary Borel orientation probability mixture
of lattices with Lebesgue-uniform fundamental-domain phase. A measurable
orientation probability kernel is constructed; no single measurable orientation
selection or conditional-measure disintegration is assumed.

## Contents

| Location | Purpose |
|---|---|
| [lean/](lean/) | Canonical complete Lean sources, independent Challenge, solution bridge, Comparator and CI scripts |
| [leanWithoutComparator/](leanWithoutComparator/) | Byte-identical proof sources and bridge, with Comparator-only files removed |
| [FClikelean/E8Leech.lean](FClikelean/E8Leech.lean) | Self-contained proposed FC-style statements; 13 intentional statement-only proof slots |
| [lean/FCSolution.lean](lean/FCSolution.lean) | Completed proofs of all 13 comparison targets |
| [lean/comparator/TARGET-CORRESPONDENCE.md](lean/comparator/TARGET-CORRESPONDENCE.md) | Clause-by-clause natural-language/formal statement review |
| [PDF/](PDF/) and [manuscript/](manuscript/) | Existing manuscript and timestamp evidence |
| [verification/](verification/) | Actual local and remote verification status and receipts |

The underlying proof files are shared byte for byte between the two proof
projects. `Challenge.lean` imports only independently compiled mathematical
definitions from Mathlib. The solution does not import the Challenge.
The 13 targets cover general-exponent Riesz crystallization, Gaussian and
positive-mixture crystallization, six zero-excess/exact-lattice equivalences,
and the generic orientation/uniform-phase law classification.

**Scope boundary.** The formal quantitative statement guarantees a measurable
high-probability subevent. It does not establish the manuscript's additional
claim that the whole existential success event is Borel. The published statement
above uses exactly the measurable-subevent formulation. The full existential
exact-lattice predicate is likewise not asserted Borel. The endpoint γ=1/12 and
uniqueness of the orientation mixing distribution are not asserted.

## Build and verify

```sh
cd lean
lake exe cache get
lake build FCSolution FCAudit
lake env lean FCAudit.lean
```

For ordinary browsing/building without Comparator, use `leanWithoutComparator/`
with the same commands (omit `FCAudit`). The FC-style bundle compiles with the
same pinned Mathlib independently of the proof project; it is not an accepted
upstream FC statement and its `sorry`s are not a proof.

Local receipts record successful independent reference and FC-style compilation,
all 13 target/definition comparisons through the pinned upstream Comparator APIs,
and the standard-three-axiom audit. The local proof compilation reused development
objects; it is not a fresh full build or a Linux sandbox/kernel-replay result.

The GitHub workflow builds six dependency-ordered stages from source on fresh
Linux runners, then runs pinned upstream Comparator with Linux sandboxing and
permitted-axiom checks, plus a separate fresh Lean-kernel replay. Intermediate
build artifacts are retained for two days; verification receipts for 90 days.
Comparator's builtin replay and `leanchecker` use Lean's kernel; `enable_nanoda`
is false, so this workflow does not certify a separate kernel implementation.

The requested publication order is: local statement review and checks, private
Linux CI, then public Linux CI. [PUBLICATION-MANIFEST.json](PUBLICATION-MANIFEST.json)
records the actual stage reached. Pending checks are not reported as successes.

## Attribution

See [THIRD_PARTY.txt](THIRD_PARTY.txt), [licenses/](licenses/), and retained
file headers for Tau Ceti, Mathlib and Sphere-Packing-Lean provenance.
Comparator setup follows the structure of
[KitaKen1/entropic-rogers-shephard](https://github.com/KitaKen1/entropic-rogers-shephard),
with independent E₈/Leech mathematical targets. ChatGPT and OpenAI Codex assisted
the mathematical exploration, formal proof development and publication preparation.
