# Lean proofs of quantitative stationary crystallization for E₈ and Leech lattices

Quantitative stationary crystallization asks whether a point process whose energy
is close to that of a lattice must look like that lattice on a large ball.
The two primary Lean targets state the following measurable-subevent version
of the [proof note](PDF/e8-leech-stationary-crystallization.pdf), Sections 1 and 7.

> **Quantitative stationary crystallization.** Let $`d\in\{8,24\}`$ and let
> $`\Lambda`$ be the corresponding covolume-one E₈ or Leech lattice. Fix
> $`s>d`$ and $`0<\gamma<1/12`$. There are constants $`C>0`$ and
> $`0<\delta_0<\exp(-e)`$, depending only on these fixed parameters, such that
> the following holds for every stationary simple locally finite point-process
> law $`\mu`$ of intensity one.
>
> If $`0<\delta<\delta_0`$ and
>
> $$\mathcal E_s(\mu)\le L_s(\Lambda)+\delta,\qquad
> R=\frac{\log(1/\delta)}{\log\log(1/\delta)},$$
>
> there is a measurable event $`G`$ with $`\mu(G)\ge1-CR^{-1/2}`$ such that
> every configuration $`\Xi\in G`$ has the following properties. All points of
> $`\Xi\cap\overline B_R`$ admit a two-sided distance matching, with error
> $`C\delta^\gamma`$, to the isometric image of a finite subset of $`\Lambda`$;
> and
>
> ```math
> |\Xi\cap\overline B_R|\ge(1-CR^{-1/2})\mathrm{vol}(\overline B_R).
> ```

Here the ordered Riesz energy and lattice energy are

```math
\mathcal E_s(\mu)=\mathbb E_\mu\sum_{x\in\Xi\cap[0,1)^d}
  \sum_{y\in\Xi\setminus\{x\}}|x-y|^{-s},\qquad
L_s(\Lambda)=\sum_{z\in\Lambda\setminus\{0\}}|z|^{-s}.
```

The second energy endpoint ranges over the entire configuration; there is no
factor of $`1/2`$. All logarithms are natural. No ergodicity or samplewise density
limit is assumed. The exponent $`\gamma=1/13`$ is included.

This repository contains Lean 4.33.1 proofs of the formal targets, using FC's
pinned Mathlib version. The library also proves the Gaussian and positive
Gaussian-mixture versions, and classifies zero-excess laws through exact lattice
configurations and orientation mixtures with uniform fundamental-domain phase.
**Review of the original manuscript against Lean is still incomplete.**
The author authorized GitHub updates and formal CI on 28 October 2026. The
remaining scope questions are listed below; a successful CI run will not itself
complete that review.

The two main components are:

1. **A Formal Conjectures style statement.**
   [FClikelean/](FClikelean/) contains the two primary Riesz statements, short
   problem-specific definitions and two proved coordinate checks. Reusable
   point-process definitions are supplied in a separate FC support file.
2. **The full Lean proof.**
   [E8Leech.lean](lean/E8Leech.lean) imports the proof library.
   [FCSolution.lean](lean/FCSolution.lean) connects its results to the 13
   Comparator targets, including the Gaussian, mixture and equality-law results.

## Formal Conjectures like targets

### FClikelean

The local draft is [E8Leech.lean](FClikelean/E8Leech.lean). Its four definitions
specify the E₈ lattice, the binary Golay block, the Leech lattice and the common
quantitative crystallization property. The point-process model, stationarity,
intensity and energies are in the accompanying
[FC support file](FClikelean/FormalConjecturesForMathlib/Probability/SimplePointProcess.lean).

The draft follows the module, import, category and AMS conventions of a pinned
Formal Conjectures checkout. Its actual FC linter check and the correspondence
of both primary types to the completed proofs passed locally. The two research
`sorry`s are statement slots. No FC issue or pull request has been submitted,
and no public proof link for this revised candidate is asserted.
See [the FC-style guide](FClikelean/README.md) for the reviewed examples and installation.

### Comparator target

[Challenge.lean](lean/Challenge.lean) supplies the independent reference
statements, and [FCSolution.lean](lean/FCSolution.lean) proves them without
importing the Challenge. The primary targets are
`E8LeechFC.e8_quantitative_crystallization` and
`E8LeechFC.leech_quantitative_crystallization`.

The 11 supporting targets cover Gaussian and positive-mixture crystallization,
six zero-excess/exact-lattice equivalences, and a generic stationary exact-lattice
law classification. The [correspondence table](lean/comparator/TARGET-CORRESPONDENCE.md)
identifies the natural-language clauses, formal statements and outstanding
manuscript-review questions.

## Mathematical explanation (AI generated)

**1. Express energy through stationary pair counts.** Counting kernels and
stationarity turn local pair sums into full-space energy identities. A sharp
[off-diagonal linear-programming bound](lean/E8Leech/StationaryOffDiagonalLP.lean)
provides the analytic energy estimate after subtracting the diagonal contribution.

**2. Obtain quantitative geometric control.** Gaussian auxiliary-function
certificates and periodic packing stability feed the
[crystallization transfer](lean/E8Leech/PotentialCrystallization.lean).
Deletion, restoration and guarded periodization connect these estimates to the
original point process. The final matching includes all original points in the
observation ball.

**3. Choose the observation and error scales.** The
[general-exponent theorem](lean/E8Leech/GeneralGammaCrystallization.lean) chooses
constants before the process law and energy excess. For every
$`0<\gamma<1/12`$, it obtains

```math
R=\frac{\log(1/\delta)}{\log\log(1/\delta)},\qquad
\text{position error }C\delta^\gamma,\qquad
\text{probability and count losses }CR^{-1/2}.
```

The result supplies a measurable good subevent of the geometric matching event.

**4. Pass to positive Gaussian mixtures.**
[Tonelli identities](lean/E8Leech/GaussianPotentialMixtures.lean) relate process
and lattice energies to their Gaussian mixtures. The
[potential transfer](lean/E8Leech/GeneralGammaPotentialTransfer.lean) gives the
same conclusion for every positive Gaussian parameter, including $`\pi`$, and
for every positive mixture with nonzero mass on positive parameters and finite
lattice energy. The mixing measure need not be atomic.

**5. Classify zero excess.** At zero excess,
[configuration rigidity](lean/E8Leech/ZeroExcessExactLattice.lean) removes every
missing point from the reconstructed lattice. A
[measurable orientation probability kernel](lean/E8Leech/GlobalOrientationKernel.lean)
and stationary phase averaging then identify the law as an arbitrary orientation
mixture with uniform fundamental-domain phase. The
[direct mixture equivalences](lean/E8Leech/ZeroExcessLawClassification.lean)
are in the proof library; they are not all direct Comparator targets.

The [proof note](PDF/e8-leech-stationary-crystallization.pdf) gives the paper
argument. Its exact agreement with these formal statements remains under review.

## Files

| Directory | Lean version | Purpose |
|---|---|---|
| [lean/](lean/) | `v4.33.1` | Canonical proof, pinned dependencies, Challenge and FCSolution. |
| [leanWithoutComparator/](leanWithoutComparator/) | `v4.33.1` | The same proof for browsing and building, with Comparator-only files removed. |
| [FClikelean/](FClikelean/) | `v4.33.1` | FC-style primary statements and support overlay; local FC compilation and primary-type correspondence passed. |
| [lean/comparator/](lean/comparator/) | `v4.33.1` | Input pins, source correspondence, verification scripts and guide. |
| [.github/workflows/](.github/workflows/) | GitHub-hosted Linux | Source builds, Comparator, axiom audit and fresh kernel replay; formal CI authorized. |
| [PDF/](PDF/) | — | Proof note and its existing timestamp evidence. |
| [manuscript/](manuscript/) | — | Manuscript sources being compared with Lean. |
| [verification/](verification/) | — | Local check receipts and actual CI/publication status. |

The 1,537 common Lean sources in the canonical and supplementary projects are
byte-identical. [PUBLICATION-MANIFEST.json](PUBLICATION-MANIFEST.json) records the
candidate and its verification status. Attribution and dependency licenses are
in [THIRD_PARTY.txt](THIRD_PARTY.txt), [licenses/](licenses/) and retained file headers.
ChatGPT and OpenAI Codex assisted the mathematical exploration, proof development
and publication preparation.

## Verification

### Lean execution results

The toolchain is Lean 4.33.1 with Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`.
The [reference compilation](verification/local-reference-compilation.json)
passed independently. [FCSolution and FCAudit](verification/local-compilation.json)
compiled locally using existing development proof objects.
All [13 audited targets](verification/local-axioms.json) use only
`[propext, Classical.choice, Quot.sound]`.
This is not a fresh full build of the complete candidate.

The [FC compilation](verification/local-FClikelean.json) passed with the genuine
upstream FC utility module and project linters. A
[separate proof bridge](verification/fc-style-correspondence.json) checked the
two primary statements against the canonical types without using their `sorry`s.

### Lean Comparator check

The proof, reference, Comparator and Lean4export use Lean 4.33.1. Comparator and
Lean4export are pinned to their recorded 4.33 source revisions; only their
toolchain declarations are changed from 4.33.0 to 4.33.1.

The [local comparison](verification/local-comparator-apis.json) passed all 13
statement/definition comparisons and permitted-axiom checks through unmodified
upstream Comparator APIs, using direct imported constant maps. The exported-JSON
parser, complete Comparator CLI, Linux sandbox and fresh kernel replay have not
been validated locally for this candidate. Private and public CI success are
not claimed.

### Statement correspondence

[Original-manuscript review](verification/original-statement-review.json) remains
incomplete. In particular:

- Lean supplies a measurable high-probability subevent; the manuscript additionally
  asserts that the whole existential geometric success event is Borel.
- The manuscript's orientation quotient and Haar torus phase must be matched
  explicitly to Lean's full linear-isometry parameter and fundamental-domain phase.
- Bounded-Borel versus all-Borel counting conventions, and coverage of the direct
  zero-excess/mixture equivalences by the comparison targets, remain under review.

The statement at the top of this README uses the measurable-subevent formulation.
Rewording the README does not complete the original-manuscript review.

## Appendix: timeline (AI generated)

| Date | Contributor | Contribution |
|---|---|---|
| March 2016 | Maryna Viazovska | Proved optimal sphere packing in dimension 8 ([paper](https://arxiv.org/abs/1603.04246)). |
| March 2016 | Henry Cohn, Abhinav Kumar, Stephen D. Miller, Danylo Radchenko and Maryna Viazovska | Proved optimal sphere packing in dimension 24 ([paper](https://arxiv.org/abs/1603.06518)). |
| February 2019 | Cohn, Kumar, Miller, Radchenko and Viazovska | Proved universal optimality of the E₈ and Leech lattices for completely monotonic functions of squared distance ([paper](https://arxiv.org/abs/1902.05438)). |
| October 2026 | This project | Developed Lean proofs for the quantitative stationary, positive-mixture and zero-excess targets. Original-statement review and full candidate CI remain unfinished. |

Universal optimality concerns energy minimization. This project's formal targets
also quantify how a small energy excess controls local lattice matching and
classify the stationary laws at zero excess.

## Appendix: Verification by Lean Comparator on GitHub CI runner

The [workflow](.github/workflows/comparator.yml) is configured to build six
stages from source on fresh Linux runners, compare the reference statements and
dependent definitions, audit permitted axioms and replay the solution in Lean's
builtin kernel. Comparator runs in three required groups (six E₈ targets,
six Leech targets and one lattice-law target); their union is checked against
the canonical list of 13 targets. A separate job performs a full fresh
Lean-kernel replay.
`enable_nanoda` is false; no independent kernel implementation is certified.

### Certification Within 90 days: CI results

**Formal CI was reauthorized by the author on 28 October 2026.** The earlier
private run was cancelled. Subsequent private retries failed, most recently
during Comparator's builtin kernel replay at the 340-minute time limit.
The source build, axiom audit and independent full fresh replay succeeded.
The grouped Comparator retry still requires a successful result; public CI
will follow only after complete private success at the same candidate commit.

| Candidate check | Actual status |
|---|---|
| Earlier private candidate | Cancelled; recorded in [ci-hold.json](verification/ci-hold.json). |
| Private Linux CI | [Previous retry failed](https://github.com/KitaKen1/e8-leech-crystallization-ci-20261016/actions/runs/40821237822); grouped retry pending. |
| Current local revision: public Linux CI | Not run. |

The current order is local formal-input checks, private CI, then public CI.
Original-statement review remains incomplete and is not replaced by these checks.

### Certification After 90 days: archive

There is no successful CI archive for this candidate. The configured workflow
retains intermediate proof artifacts for two days and verification receipts for
90 days. Successful-run logs, metadata and checksums can be archived after the
verification has actually completed.

### Reproduce the verification

For a local proof build:

```sh
cd lean
lake exe cache get
lake build
```

For the reference and axiom audit, also run `lake build Challenge FCAudit` and
`lake env lean FCAudit.lean`. The supplementary project builds with the same
commands for the proof. See the
[verification guide](lean/comparator/README.md) for the local input checks,
FC-style check and configured Linux verification. Original-statement review
remains incomplete; issue posting awaits a separate instruction.
