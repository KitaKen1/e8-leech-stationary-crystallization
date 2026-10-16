import E8Leech.KronLH
import E8Leech.KronLeechAll
import E8Leech.LeechUnitCost
import E8Leech.E8UnitCostFinal

/-!
# Three of the four bounds on the block `q ∈ [3, 4]` for the Leech kernel

`LeechBlockBounds` asks for four quantitative facts on the block `q ∈ [3, 4]`. Three of them
follow from statements that are already proved, by continuity on a compact set:

* `leech_block_lower`: `𝒦̂⁽²⁴⁾(iq, it) ≥ B > 0` on `[3, 4] × [1, 2]`, from the positivity (6.4)(1)
  (`ckmrvLeechHatKernel_pos`; the block does not meet the singular curves) and the continuity of
  the kernel on the regular locus;
* `leech_lead_lower`: `a₁(q) ≥ m > 0` on `[3, 4]`, from `leechAxisCusp_lead_pos` and the
  continuity of the explicit form of `a₁`;
* the ratio `a₀ + (5/4) a₁ ≥ 0` is `leechAxisCusp_ratio_pos`.

The fourth one, the linear growth of the truncated kernel for large `t`, is not proved here:
`leechBlockBounds_of_trunc_linear` gives `LeechBlockBounds` from it.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Set
open UpperHalfPlane hiding I
open scoped Real Manifold

/-! ## The kernel on the block -/

theorem continuousOn_ckmrvLeechPlusKernel_regular :
    ContinuousOn (fun p : ℍ × ℍ => ckmrvLeechPlusKernel p.1 p.2) ckmrvRegularLocus := by
  simp only [ckmrvLeechPlusKernel, ckmrvCoreContraction]
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
  exact ((((mdifferentiable_ckmrvPhiBasis i).continuous.comp continuous_fst).continuousOn).mul
    (continuousOn_ckmrvLeechPlusCoefficientMatrix_entry i j)).mul
    (((mdifferentiable_ckmrvTildePhiBasis j).continuous.comp continuous_snd).continuousOn)

theorem continuousOn_ckmrvLeechMinusKernel_regular :
    ContinuousOn (fun p : ℍ × ℍ => ckmrvLeechMinusKernel p.1 p.2) ckmrvRegularLocus := by
  simp only [ckmrvLeechMinusKernel, ckmrvCoreContraction]
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
  exact ((((mdifferentiable_ckmrvPsiBasis i).continuous.comp continuous_fst).continuousOn).mul
    (continuousOn_ckmrvLeechMinusCoefficientMatrix_entry i j)).mul
    (((continuous_ckmrvTildePsiBasis j).comp continuous_snd).continuousOn)

/-- `K̂(q, t) = Re 𝒦̂⁽²⁴⁾(iq, it)` is continuous on the block `[3,4] × [1,2]`. -/
theorem continuousOn_leechDualKernel_block :
    ContinuousOn leechDualKernel (Icc (3 : ℝ) 4 ×ˢ Icc (1 : ℝ) 2) := by
  have hmaps : MapsTo ckmrvImaginaryPair (Icc (3 : ℝ) 4 ×ˢ Icc (1 : ℝ) 2) ckmrvRegularLocus :=
    fun p hp => ckmrvFixedImaginaryRectangle_subset_regular ⟨p, hp, rfl⟩
  have hp := continuousOn_ckmrvLeechPlusKernel_regular.comp
    continuousOn_ckmrvImaginaryPair_rectangle hmaps
  have hm := continuousOn_ckmrvLeechMinusKernel_regular.comp
    continuousOn_ckmrvImaginaryPair_rectangle hmaps
  have h := (Complex.continuous_re.comp_continuousOn ((hp.sub hm).div_const 2))
  refine h.congr fun p _ => ?_
  simp only [leechDualKernel, ckmrvLeechHatKernel, Pi.sub_apply, Function.comp_apply,
    ckmrvImaginaryPair, imagPt]

/-- **A positive lower bound of the Leech kernel on the block `[3, 4] × [1, 2]`.** -/
theorem leech_block_lower :
    ∃ B : ℝ, 0 < B ∧ ∀ q ∈ Icc (3 : ℝ) 4, ∀ t ∈ Icc (1 : ℝ) 2, B ≤ leechDualKernel (q, t) :=
  compact_rectangle_positive_lower continuousOn_leechDualKernel_block fun p hp => by
    have hq : 0 < p.1 := by linarith [hp.1.1]
    have ht : 0 < p.2 := by linarith [hp.2.1]
    have hinv : p.1⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith [hp.1.1])
    exact ckmrvLeechHatKernel_pos hq ht
      (kleinModularJ_imagPt_ne hq ht (by linarith [hp.1.1, hp.2.2]) (by linarith [hp.2.1]))

/-! ## The leading cusp coefficient on the block -/

/-- The real part of a continuous function on the upper half plane is continuous along the
imaginary axis. -/
theorem continuousOn_re_imagPt {g : ℍ → ℂ} (hg : Continuous g) :
    ContinuousOn (fun u : ℝ => (g (imagPt u)).re) (Ioi 0) :=
  Complex.continuous_re.comp_continuousOn (hg.comp_continuousOn continuousOn_ofComplex_I_mul)

theorem continuousOn_axE2 : ContinuousOn axE2 (Ioi 0) :=
  continuousOn_re_imagPt E2_mdifferentiable.continuous

theorem continuousOn_axV : ContinuousOn axV (Ioi 0) :=
  continuousOn_re_imagPt mdifferentiable_thetaV.continuous

theorem continuousOn_axW : ContinuousOn axW (Ioi 0) :=
  continuousOn_re_imagPt mdifferentiable_thetaW.continuous

/-- The leading cusp coefficient `a₁(q)` is continuous in `q > 0`. -/
theorem continuousOn_leechAxisCusp_zero_re :
    ContinuousOn (fun q : ℝ => (leechAxisCusp (-1) q 0).re) (Ioi 0) := by
  have key : ∀ f g h : ℝ → ℝ, ContinuousOn f (Ioi 0) → ContinuousOn g (Ioi 0) →
      ContinuousOn h (Ioi 0) →
      ContinuousOn (fun q : ℝ => axCuspA1 (f q) (g q) (h q) q) (Ioi 0) := by
    intro f g h hf hg hh
    unfold axCuspA1 axCuspY axCuspZ axE4 axE6
    fun_prop
  exact (key axE2 axV axW continuousOn_axE2 continuousOn_axV continuousOn_axW).congr
    fun q hq => leechAxisCusp_zero_re hq

/-- **A positive lower bound of the leading cusp coefficient on the block `q ∈ [3, 4]`.** -/
theorem leech_lead_lower :
    ∃ m : ℝ, 0 < m ∧ ∀ q ∈ Icc (3 : ℝ) 4, m ≤ (leechAxisCusp (-1) q 0).re := by
  have hc : ContinuousOn (fun q : ℝ => (leechAxisCusp (-1) q 0).re) (Icc 3 4) :=
    continuousOn_leechAxisCusp_zero_re.mono fun q hq => lt_of_lt_of_le (by norm_num) hq.1
  obtain ⟨q₀, hq₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (by norm_num)) hc
  exact ⟨_, leechAxisCusp_lead_pos (by linarith [hq₀.1]), fun q hq => hmin hq⟩

/-! ## The block bounds from the linear growth -/

/-- **`LeechBlockBounds` from the linear growth of the truncated kernel**, the only one of its
four fields that is not proved. -/
theorem leechBlockBounds_of_trunc_linear
    (h : ∃ c₁ T : ℝ, 0 < c₁ ∧ 4 < T ∧ ∀ q ∈ Icc (3 : ℝ) 4, ∀ t : ℝ, T ≤ t →
      c₁ * t ≤ leechDualKernel (q, t) -
        ((leechAxisCusp (-1) q 0).re * t + (leechAxisCusp (-1) q 1).re) *
          Real.exp (2 * π * t)) :
    LeechBlockBounds where
  block_lower := leech_block_lower
  lead_lower := leech_lead_lower
  lead_ratio := fun _ hq => (leechAxisCusp_ratio_pos hq.1 hq.2).le
  trunc_linear := h

end E8Leech
