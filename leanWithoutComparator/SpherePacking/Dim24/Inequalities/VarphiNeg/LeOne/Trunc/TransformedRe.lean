-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.VarphiNeg.LeOne.Trunc.DeltaBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.Numerators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Transformed real part

Relate the transformed expression on the imaginary axis to the cleared numerator and provide a
simple lower bound obtained by dividing by `Δ(it)^2`.

## Main definitions
* `transformed_num`

## Main statements
* `transformed_re_lowerBound_of_num`
-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24

open AppendixA

/-- Cleared numerator for the transformed expression in the `t ≤ 1` case. -/
@[expose] public def transformed_num (t : ℝ) (ht0 : 0 < t) : ℂ :=
  -((t : ℂ) ^ (2 : ℕ)) * AppendixA.varphi_num (it t ht0) -
      (t : ℂ) * AppendixA.phi1_num (it t ht0) +
    AppendixA.phi2_num (it t ht0)

private lemma transformed_eq_num_over_Delta_sq (t : ℝ) (ht0 : 0 < t) :
    -((t : ℂ) ^ (2 : ℕ)) * varphi (it t ht0)
        + Complex.I * (t : ℂ) * varphi₁ (it t ht0)
        + varphi₂ (it t ht0)
      =
      (transformed_num t ht0) / (Δ (it t ht0)) ^ 2 := by
  set z : ℍ := it t ht0
  have hvarphi : varphi z = AppendixA.varphi_num z / (Δ z) ^ 2 :=
    by simp [Dim24.varphi, AppendixA.varphi_num]
  have hIvarphi1 : Complex.I * varphi₁ z = -AppendixA.phi1_num z / (Δ z) ^ 2 := by
    -- `varphi₁ = I * phi1_num / Δ^2`, hence `I * varphi₁ = - phi1_num / Δ^2`.
    have h1 := AppendixA.varphi₁_eq_I_mul_phi1_num_div_Delta_sq (z := z)
    rw [h1]
    simp [div_eq_mul_inv, mul_assoc]
    ring_nf
    simp
  have hvarphi2 : varphi₂ z = AppendixA.phi2_num z / (Δ z) ^ 2 :=
    AppendixA.varphi₂_eq_phi2_num_div_Delta_sq (z := z)
  rw [hvarphi, hvarphi2]
  have : Complex.I * (t : ℂ) * varphi₁ z = (t : ℂ) * (Complex.I * varphi₁ z) := by ring_nf
  rw [this, hIvarphi1]
  simp [transformed_num, z, div_eq_mul_inv, sub_eq_add_neg, mul_comm, add_left_comm, add_comm]
  ring_nf

private lemma transformed_re_eq_num_re_div_Delta_re_sq (t : ℝ) (ht0 : 0 < t) :
    (-((t : ℂ) ^ (2 : ℕ)) * varphi (it t ht0)
          + Complex.I * (t : ℂ) * varphi₁ (it t ht0)
          + varphi₂ (it t ht0)).re
      =
      (transformed_num t ht0).re / (Δ (it t ht0)).re ^ 2 := by
  set z : ℍ := it t ht0
  have hmain :
      (-((t : ℂ) ^ (2 : ℕ)) * varphi z
            + Complex.I * (t : ℂ) * varphi₁ z
            + varphi₂ z).re
        =
        ((transformed_num t ht0) / (Δ z) ^ (2 : ℕ)).re := by
    simpa [z] using! congrArg Complex.re (transformed_eq_num_over_Delta_sq (t := t) ht0)
  have hΔim : (Δ z).im = 0 := by simp [z]
  have hden_im : ((Δ z) ^ (2 : ℕ)).im = 0 := by simp [pow_two, Complex.mul_im, hΔim]
  have hden_re : ((Δ z) ^ (2 : ℕ)).re = (Δ z).re ^ 2 := by
    simp [pow_two, Complex.mul_re, hΔim, pow_two]
  have hden_re0 : ((Δ z) ^ (2 : ℕ)).re ≠ 0 := by
    have hΔre0 : (Δ z).re ≠ 0 :=
      ne_of_gt (Delta_it_re_pos (t := t) ht0)
    have : (Δ z).re ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hΔre0
    simpa [hden_re] using! this
  have hdiv :
      ((transformed_num t ht0 / (Δ z) ^ (2 : ℕ))).re
        =
        (transformed_num t ht0).re / ((Δ z) ^ (2 : ℕ)).re := by
    set num : ℂ := transformed_num t ht0
    set den : ℂ := (Δ z) ^ (2 : ℕ)
    have hnorm : Complex.normSq den = den.re ^ 2 := by
      simp [Complex.normSq, hden_im, pow_two]
    have hden_im' : den.im = 0 := by
      simpa [den] using! hden_im
    have hstep :
        (num / den).re = num.re * den.re / (den.re ^ 2) := by
      simpa [hden_im', hnorm] using! (Complex.div_re num den)
    have hcancel : num.re * den.re / (den.re ^ 2) = num.re / den.re := by
      field_simp [hden_re0]
    simpa [num, den] using! (hstep.trans hcancel)
  lia

/-- Lower bound the transformed real part from a lower bound on `transformed_num t`
using `Re(Δ(it))^2 ≤ 1`. -/
public lemma transformed_re_lowerBound_of_num {t : ℝ} (ht0 : 0 < t) {L : ℝ}
    (hL : 0 ≤ L) (hnum : L ≤ (transformed_num t ht0).re) :
    L ≤ (-((t : ℂ) ^ (2 : ℕ)) * varphi (it t ht0)
          + Complex.I * (t : ℂ) * varphi₁ (it t ht0)
          + varphi₂ (it t ht0)).re := by
  have hΔsq_le_one : (Δ (it t ht0)).re ^ 2 ≤ 1 :=
    Delta_it_re_sq_le_one t ht0
  have hΔsq_pos : (0 : ℝ) < (Δ (it t ht0)).re ^ 2 := by
    have hΔpos : (0 : ℝ) < (Δ (it t ht0)).re := Delta_it_re_pos (t := t) ht0
    simpa [pow_two] using! mul_pos hΔpos hΔpos
  have hΔsq_pos' : 0 < (Δ (it t ht0)).re ^ 2 := hΔsq_pos
  have hΔsq_pos_le : 0 < (Δ (it t ht0)).re ^ 2 := hΔsq_pos'
  have hmul :
      L * (Δ (it t ht0)).re ^ 2 ≤
        (transformed_num t ht0).re * (Δ (it t ht0)).re ^ 2 :=
    mul_le_mul_of_nonneg_right hnum ( pow_nonneg (Delta_it_re_pos (t := t) ht0).le 2)
  have hmul2 : L * (Δ (it t ht0)).re ^ 2 ≤ (transformed_num t ht0).re := by
    have hΔsq_le : (Δ (it t ht0)).re ^ 2 ≤ 1 := hΔsq_le_one
    have : L * (Δ (it t ht0)).re ^ 2 ≤ L * 1 := mul_le_mul_of_nonneg_left hΔsq_le hL
    have : L * (Δ (it t ht0)).re ^ 2 ≤ L := by simpa using! this
    exact this.trans hnum
  have hdiv :
      L ≤ (transformed_num t ht0).re / (Δ (it t ht0)).re ^ 2 :=
    (le_div_iff₀ hΔsq_pos).mpr hmul2
  -- Rewrite the transformed expression using `transformed_re_eq_num_re_div_Delta_re_sq`.
  exact (transformed_re_eq_num_re_div_Delta_re_sq t ht0).symm ▸ hdiv

end SpherePacking.Dim24
