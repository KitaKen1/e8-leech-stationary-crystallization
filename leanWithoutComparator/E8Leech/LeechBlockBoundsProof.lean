import E8Leech.KronLUStrip
import E8Leech.LeechTruncLinear
import E8Leech.LeechBlockLower
import E8Leech.LeechKernelInequalitiesProof

/-!
# The bounds on the block, and the Leech target from the Fourier identities

* `leech_trunc_linear`: the linear growth of the truncated kernel on the block `q ∈ [3, 4]`, from
  the quantitative form of the truncated inequality on the strip (`leechTruncMargin_block`, one
  kernel-checked cell with a margin) and the bounds of `LeechTruncLinear`.
* `leechBlockBounds`: the structure `LeechBlockBounds` is inhabited.
* `leech_analyticUnitCostInput_of_fourierIdentities`,
  `leech_stationaryCrystallization_of_fourierIdentities`: the Leech analytic input and the Leech
  crystallization target from the Fourier identities (**) `LeechFourierIdentities`.

`LeechFourierIdentities` is the only remaining hypothesis on the Leech side. It is proved in
`LeechFourierIdentityProof`; the Leech case of the main theorem is
`leechCrystallizationTarget_holds` (`LeechCrystallization`).
-/

noncomputable section

namespace E8Leech

open Set
open scoped Real

/-- **Linear growth of the truncated Leech kernel on the block `q ∈ [3, 4]`.** -/
theorem leech_trunc_linear :
    ∃ c₁ T : ℝ, 0 < c₁ ∧ 4 < T ∧ ∀ q ∈ Icc (3 : ℝ) 4, ∀ t : ℝ, T ≤ t →
      c₁ * t ≤ leechDualKernel (q, t) -
        ((leechAxisCusp (-1) q 0).re * t + (leechAxisCusp (-1) q 1).re) *
          Real.exp (2 * π * t) :=
  leech_trunc_linear_of_margin (Λ := Kron.LT.Λ) (by decide) (μ := 10000000000000000000)
    (by norm_num) (T₀ := 6) fun _ hq _ ht => leechTruncMargin_block hq.1 hq.2 ht

/-- **The quantitative bounds on the block `q ∈ [3, 4]`.** -/
theorem leechBlockBounds : LeechBlockBounds :=
  leechBlockBounds_of_trunc_linear leech_trunc_linear

/-- The Leech analytic unit-cost input from the Fourier identities (**). -/
theorem leech_analyticUnitCostInput_of_fourierIdentities {s : ℝ} (hs : 0 < s)
    (hF : LeechFourierIdentities) :
    ∃ C : ℝ, 0 < C ∧ AnalyticUnitCostInput leechSet s 2 C⁻¹ (1 / 8) :=
  leech_analyticUnitCostInput_of_ckmrv hs leechKernelInequalities hF leechBlockBounds

/-- **The Leech crystallization target from the Fourier identities (**).** The hypothesis is
proved in `LeechFourierIdentityProof` (`leechFourierIdentities`). -/
theorem leech_stationaryCrystallization_of_fourierIdentities (hF : LeechFourierIdentities) :
    leechCrystallizationTarget :=
  leech_stationaryCrystallization_of_ckmrv leechKernelInequalities hF leechBlockBounds

end E8Leech
