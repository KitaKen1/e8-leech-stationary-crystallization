-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.Numerators
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingDeltaBounds

/-!
# Clearing denominators for the `ineq2` transformation (`t ≤ 1`)

For the `t ≤ 1` case of Appendix A, Lemma `ineq2`, we apply the modular transformation `t ↦ 1 / t`
and study a transformed expression `ineq2_transformed_neg` on `t ≥ 1`. To obtain certified
real-part bounds, we clear the common denominator `Δ(it)^2` and work with the numerator
`ineq2_num`.

## Main definitions
* `ineq2_transformed_neg`
* `ineq2_num`

## Main statements
* `ineq2_transformed_neg_eq_num_div_Delta_sq`
* `ineq2_transformed_neg_re_eq`
* `ineq2_lowerBound_of_num`
-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.Ineq2LeOneTruncAux

/-- The transformed expression whose real part is bounded below by truncation
(`t ≤ 1` case of Lemma `ineq2`, after the substitution `t ↦ 1/t`). -/
@[expose]
public def ineq2_transformed_neg (t : ℝ) (ht0 : 0 < t) : ℂ :=
  ((t : ℂ) ^ (2 : ℕ)) * varphi (it t ht0)
    - Complex.I * (t : ℂ) * varphi₁ (it t ht0)
    - varphi₂ (it t ht0)
    + (432 / (Real.pi ^ 2) : ℂ) * ψI (it t ht0)

/-- Cleared numerator for `ineq2_transformed_neg` after multiplying by `Δ(it)^2`. -/
@[expose]
public def ineq2_num (t : ℝ) (ht0 : 0 < t) : ℂ :=
  ((t : ℂ) ^ (2 : ℕ)) * AppendixA.varphi_num (it t ht0)
    + (t : ℂ) * AppendixA.phi1_num (it t ht0)
    - AppendixA.phi2_num (it t ht0)
    + (432 / (Real.pi ^ 2) : ℂ) * AppendixA.psiI_num (it t ht0)

/-- Express `ineq2_transformed_neg` as the quotient of `ineq2_num` by `Δ(it)^2`. -/
public lemma ineq2_transformed_neg_eq_num_div_Delta_sq (t : ℝ) (ht0 : 0 < t) :
    ineq2_transformed_neg t ht0 = (ineq2_num t ht0) / (Δ (it t ht0)) ^ (2 : ℕ) := by
  -- Rewrite each term using the numerator identities from `AppendixA` and factor out `Δ(it)^2`.
  set z : ℍ := it t ht0
  have hvarphi : varphi z = AppendixA.varphi_num z / (Δ z) ^ (2 : ℕ) := by
    simp [Dim24.varphi, AppendixA.varphi_num]
  have hvarphi₁ := AppendixA.varphi₁_eq_I_mul_phi1_num_div_Delta_sq z
  have hvarphi₂ := AppendixA.varphi₂_eq_phi2_num_div_Delta_sq z
  have hψI := AppendixA.ψI_eq_psiI_num_div_Delta_sq z
  simp [ineq2_transformed_neg, ineq2_num, hvarphi, hvarphi₁, hvarphi₂, hψI, z, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg, add_left_comm, add_comm]
  ring_nf
  simp

/-- On the imaginary axis, `Δ(it)` is real, so the real part of `ineq2_transformed_neg` is the real
part of `ineq2_num` divided by `Δ(it).re^2`. -/
public lemma ineq2_transformed_neg_re_eq (t : ℝ) (ht0 : 0 < t) :
    (ineq2_transformed_neg t ht0).re =
      (ineq2_num t ht0).re / ((Δ (it t ht0)).re ^ (2 : ℕ)) := by
  -- Rewrite as a quotient by `Δ(it)^2`.
  rw [ineq2_transformed_neg_eq_num_div_Delta_sq (t := t) (ht0 := ht0)]
  -- On the imaginary axis, `Δ(it)` is real.
  have hΔim : (Δ (it t ht0)).im = 0 := Delta_it_im (t := t) ht0
  have hΔ2 : (Δ (it t ht0) : ℂ) ^ (2 : ℕ) = ((Δ (it t ht0)).re ^ (2 : ℕ) : ℂ) := by
    refine Complex.ext ?_ ?_
    · simp [pow_two, Complex.mul_re, hΔim]
    · have hleft : ((Δ (it t ht0) : ℂ) ^ (2 : ℕ)).im = 0 :=
        Complex.im_pow_eq_zero_of_im_eq_zero hΔim 2
      have hright : (((Δ (it t ht0)).re : ℂ) ^ (2 : ℕ)).im = 0 :=
        Complex.im_pow_eq_zero_of_im_eq_zero (by simp) 2
      simp [hleft, hright]
  rw [hΔ2]
  set d : ℝ := (Δ (it t ht0)).re ^ (2 : ℕ)
  have hd : d ≠ 0 := by
    have hΔpos : 0 < (Δ (it t ht0)).re := Delta_it_re_pos (t := t) ht0
    exact pow_ne_zero 2 (ne_of_gt hΔpos)
  have hdiv :
      ((ineq2_num t ht0) / (d : ℂ)).re = (ineq2_num t ht0).re / d := by
    -- `d` is real, so real-part division is scalar division.
    exact Complex.div_ofReal_re (ineq2_num t ht0) d
  simpa [d] using! hdiv

/-- If `0 ≤ L ≤ (ineq2_num t).re`, then `L ≤ (ineq2_transformed_neg t).re`. -/
public theorem ineq2_lowerBound_of_num {t : ℝ} (ht0 : 0 < t) {L : ℝ}
    (hL : 0 ≤ L) (hnum : L ≤ (ineq2_num t ht0).re) :
    L ≤ (ineq2_transformed_neg t ht0).re := by
  have hsq_le_one : (Δ (it t ht0)).re ^ (2 : ℕ) ≤ 1 := Delta_it_re_sq_le_one (t := t) ht0
  have hpos : 0 < (Δ (it t ht0)).re := Delta_it_re_pos (t := t) ht0
  have hinv_ge_one : (1 : ℝ) ≤ 1 / ((Δ (it t ht0)).re ^ (2 : ℕ)) := by
    have hpos' : 0 < (Δ (it t ht0)).re ^ (2 : ℕ) := by positivity
    exact one_le_one_div hpos' hsq_le_one
  have hdiff :
      (ineq2_transformed_neg t ht0).re =
        (ineq2_num t ht0).re / (Δ (it t ht0)).re ^ (2 : ℕ) :=
    ineq2_transformed_neg_re_eq (t := t) (ht0 := ht0)
  have hmul : L ≤ (ineq2_num t ht0).re / (Δ (it t ht0)).re ^ (2 : ℕ) := by
    have hscale :
        L * (1 / ((Δ (it t ht0)).re ^ (2 : ℕ))) ≤
          (ineq2_num t ht0).re * (1 / ((Δ (it t ht0)).re ^ (2 : ℕ))) :=
      mul_le_mul_of_nonneg_right hnum (by positivity)
    have hL' : L ≤ L * (1 / ((Δ (it t ht0)).re ^ (2 : ℕ))) := by
      simpa [mul_one] using! (mul_le_mul_of_nonneg_left hinv_ge_one hL)
    rw [div_eq_mul_one_div]
    linarith
  simpa [hdiff] using! hmul

end SpherePacking.Dim24.Ineq2LeOneTruncAux
