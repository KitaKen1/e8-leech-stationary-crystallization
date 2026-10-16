-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.DistanceSpectrum.Reduction
public import SpherePacking.Dim24.Uniqueness.Rigidity.Lemmas
public import SpherePacking.Dim24.Uniqueness.Input.EqualityCase
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.CE.Defs

/-!
# Equality-case interfaces for the CE route

In the CE Section 8 approach, sharpness of the LP bound forces vanishing of two slack terms:

1. pairwise slack (pointwise): `f (x - y) = 0` for distinct centers,
2. Fourier slack: a nonnegative Fourier-side term vanishes termwise on nonzero dual frequencies.

This file packages these hypotheses as reusable predicates and derives them from the equality-case
results in `SpherePacking/Dim24/Uniqueness/Input/EqualityCase.lean`.

## Main definitions
* `Uniqueness.RigidityClassify.CE.CEPairwiseVanishing`
* `Uniqueness.RigidityClassify.CE.CEFourierVanishing`
* `Uniqueness.RigidityClassify.CE.CEEqualityCaseNormalized`

## Main statements
* `Uniqueness.RigidityClassify.CE.cePairwiseVanishing_of_optimality_normalized`
* `Uniqueness.RigidityClassify.CE.ceFourierVanishing_of_optimality_normalized`
* `Uniqueness.RigidityClassify.CE.ceEqualityCaseNormalized_of_optimality_normalized`
-/


namespace SpherePacking.Dim24.Uniqueness.RigidityClassify.CE

noncomputable section

open scoped FourierTransform SchwartzMap RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- CE equality-case, pairwise slack vanishing: for distinct centers, the auxiliary function
`f(x-y)` must vanish.

In this repo, `f` is the concrete auxiliary Schwartz function constructed from `dim_24.tex`. -/
@[expose]
public def CEPairwiseVanishing (S : PeriodicSpherePacking 24) : Prop :=
  ∀ x y : S.centers, x ≠ y → f ((x : ℝ²⁴) - (y : ℝ²⁴)) = 0

/-- CE equality-case, Fourier slack vanishing (normalized, periodic packing form).

We express this in the `sep=1` normalization for the scaled packing `S₁ := (1/2)•S` and the
scaled auxiliary function `scaledF(x) = f(2x)`, because the generic Cohn-Elkies development
(`SpherePacking.CohnElkies.*`) is written in that normalization.

The statement matches the Fourier-side complementary slackness: for each nonzero dual-lattice
frequency `m`, the nonnegative summand
`((𝓕 scaledF) m).re * ‖expSum(m)‖^2` vanishes. -/
@[expose]
public def CEFourierVanishing (S : PeriodicSpherePacking 24) : Prop :=
  ∃ hc : (0 : ℝ) < (1 / 2 : ℝ),
    let S₁ : PeriodicSpherePacking 24 := PeriodicSpherePacking.scale (S := S) hc
    ∃ D : Set ℝ²⁴, Bornology.IsBounded D ∧
      (∀ x, ∃! g : S₁.lattice, g +ᵥ x ∈ D) ∧
        ∀ m : SchwartzMap.dualLattice (d := 24) S₁.lattice, m ≠ 0 →
          ((𝓕 (scaledF : 𝓢(ℝ²⁴, ℂ))) (m : ℝ²⁴)).re *
            (norm (SpherePacking.CohnElkies.expSum S₁ D m) ^ 2) = 0

/-- Bundled equality-case package for the CE §8 route (normalized). -/
@[expose]
public def CEEqualityCaseNormalized (S : PeriodicSpherePacking 24) : Prop :=
  CEPairwiseVanishing S ∧ CEFourierVanishing S

/-- Optimality (after normalization) implies CE pairwise slack vanishing. -/
public theorem cePairwiseVanishing_of_optimality_normalized
    (S : PeriodicSpherePacking 24)
    (hSep : S.separation = 2) (hDens : S.density = LeechPacking.density) :
    CEPairwiseVanishing S := by
  simpa [CEPairwiseVanishing] using!
    (Dim24.optimality_normalized_forces_f_of_sub_eq_zero (S := S) hSep hDens)

/-- Optimality (after normalization) implies CE Fourier-side slack vanishing. -/
public theorem ceFourierVanishing_of_optimality_normalized
    (S : PeriodicSpherePacking 24)
    (hSep : S.separation = 2) (hDens : S.density = LeechPacking.density) :
    CEFourierVanishing S := by
  -- Scale down by `1/2` to enter the `sep=1` normalization used by `scaledF`.
  have hc : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
  let S₁ : PeriodicSpherePacking 24 := PeriodicSpherePacking.scale (S := S) hc
  have hSep₁ : S₁.separation = 1 := by
    have : (PeriodicSpherePacking.scale (S := S) hc).separation = (1 / 2 : ℝ) * S.separation := by
      simp [PeriodicSpherePacking.scale, SpherePacking.scale]
    simpa [S₁, hSep, this, mul_assoc] using! this
  have hDens₁ : S₁.density = LeechPacking.density := by
    have : S₁.density = S.density := by
      simpa [S₁] using! (PeriodicSpherePacking.scale_density (d := 24) (S := S) (hc := hc))
    simpa [this] using! hDens
  -- Apply the dimension-24 equality-case bookkeeping for `scaledF`.
  rcases Dim24.optimality_sep_one_forces_scaledF_slack_vanishing (S := S₁) hSep₁ hDens₁ with
    ⟨-, ⟨D, hDbdd, hCovers, hFourier⟩⟩
  refine ⟨hc, ?_⟩
  dsimp [CEFourierVanishing, S₁]
  exact ⟨D, hDbdd, hCovers, hFourier⟩

/-- Optimality (after normalization) implies the bundled CE equality-case predicate. -/
public theorem ceEqualityCaseNormalized_of_optimality_normalized
    (S : PeriodicSpherePacking 24)
    (hSep : S.separation = 2) (hDens : S.density = LeechPacking.density) :
    CEEqualityCaseNormalized S :=
  ⟨cePairwiseVanishing_of_optimality_normalized (S := S) hSep hDens,
    ceFourierVanishing_of_optimality_normalized (S := S) hSep hDens⟩

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify.CE
