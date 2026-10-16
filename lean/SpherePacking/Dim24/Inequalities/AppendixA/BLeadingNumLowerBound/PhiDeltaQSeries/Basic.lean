-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.VarphiQSeries
import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesMul
import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesSummable


/-!
# `q`-series for `phi1_num` and `phi2_num`

This file defines the coefficient functions appearing in the Eisenstein numerators for
`phi1_num` and `phi2_num` in Appendix A, and proves the basic summability facts needed to use
`qseries_mul_cast`.

## Main definitions
* `coeffPhi2Core`
* `coeffPhi1Core`

## Main statements
* `summable_norm_qseries_coeffPhi2Core`
* `summable_norm_qseries_coeffPhi1Core`
* `E₄_cube_it_eq_qseries`, `E₆_sq_it_eq_qseries`
-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.AppendixA


/-- Coefficients of the core numerator `-49*E4^3 + 25*E6^2` (as a `q`-series). -/
@[expose] public def coeffPhi2Core : ℕ → ℚ :=
  fun n => (-49 : ℚ) * coeffE4Cube n + (25 : ℚ) * coeffE6Sq n

/-- Coefficients of the core numerator for `phi1_num` (as a `q`-series). -/
@[expose] public def coeffPhi1Core : ℕ → ℚ :=
  fun n =>
    (48 : ℚ) * conv coeffE6 coeffE4Sq n + (2 : ℚ) * conv coeffE2 coeffPhi2Core n

private def Cphi2Core : ℝ :=
  (((49 : ℝ) * ((240 * 240 : ℝ) * (240 : ℝ))) + ((25 : ℝ) * (504 * 504 : ℝ)))

private def kphi2Core : ℕ :=
  ((4 + 4 + 1) + 4 + 1)

private lemma abs_coeffPhi2Core_le (n : ℕ) :
    |(coeffPhi2Core n : ℝ)| ≤ Cphi2Core * (((n + 1 : ℕ) : ℝ) ^ kphi2Core) := by
  simpa [coeffPhi2Core, Cphi2Core, kphi2Core] using! (abs_lincomb_E4Cube_E6Sq_le (n := n))

/-- Summability of the normed `q`-series for `coeffPhi2Core` at `z = it t`. -/
public lemma summable_norm_qseries_coeffPhi2Core (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    Summable (fun n : ℕ => ‖((coeffPhi2Core n : ℂ) * qterm (it t ht0) n)‖) := by
  simpa using!
    (summable_norm_qseries_of_coeffBound (t := t) (ht0 := ht0) (ht := ht)
      (a := coeffPhi2Core)
      (C := Cphi2Core) (k := kphi2Core) abs_coeffPhi2Core_le)

/-- Summability of the normed `q`-series for `conv coeffE2 coeffPhi2Core` at `z = it t`. -/
public lemma summable_norm_qseries_conv_coeffE2_coeffPhi2Core (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    Summable (fun n : ℕ => ‖((conv coeffE2 coeffPhi2Core n : ℂ) * qterm (it t ht0) n)‖) := by
  have habs : ∀ n : ℕ,
      |(conv coeffE2 coeffPhi2Core n : ℝ)| ≤
        ((24 : ℝ) * Cphi2Core) * (((n + 1 : ℕ) : ℝ) ^ (2 + kphi2Core + 1)) := by
    intro n
    -- Convolution bound with `ka=2`, `kb=14`.
    simpa [mul_assoc, add_assoc, add_left_comm, add_comm, Cphi2Core, kphi2Core] using!
      (abs_conv_le (a := coeffE2) (b := coeffPhi2Core)
        (Ca := (24 : ℝ))
        (Cb := Cphi2Core)
        (ka := 2) (kb := kphi2Core)
        abs_coeffE2_le
        abs_coeffPhi2Core_le
        n)
  exact summable_norm_qseries_of_coeffBound t ht0 ht (conv coeffE2 coeffPhi2Core) (24 * Cphi2Core)
    (2 + kphi2Core + 1) habs

/-- Summability of the normed `q`-series for `coeffPhi1Core` at `z = it t`. -/
public lemma summable_norm_qseries_coeffPhi1Core (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    Summable (fun n : ℕ => ‖((coeffPhi1Core n : ℂ) * qterm (it t ht0) n)‖) := by
  -- Summability of each summand, via polynomial coefficient bounds.
  have hsE6E4Sq :
      Summable (fun n : ℕ => ‖((conv coeffE6 coeffE4Sq n : ℂ) * qterm (it t ht0) n)‖) := by
    have habs : ∀ n : ℕ,
        |(conv coeffE6 coeffE4Sq n : ℝ)| ≤
          ((504 : ℝ) * (240 * 240 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (6 + (4 + 4 + 1) + 1)) :=
      abs_conv_coeffE6_coeffE4Sq_le
    exact summable_norm_qseries_of_coeffBound t ht0 ht (conv coeffE6 coeffE4Sq) (504 * (240 * 240))
      (6 + (4 + 4 + 1) + 1) habs
  have hsE2Phi2 :
      Summable (fun n : ℕ => ‖((conv coeffE2 coeffPhi2Core n : ℂ) * qterm (it t ht0) n)‖) :=
    summable_norm_qseries_conv_coeffE2_coeffPhi2Core (t := t) (ht0 := ht0) (ht := ht)
  -- Scale by the small rational constants and add.
  have hs1 :
      Summable (fun n : ℕ =>
        ‖(((48 : ℚ) * conv coeffE6 coeffE4Sq n : ℂ) * qterm (it t ht0) n)‖) := by
    -- Multiply the norm by `‖48‖`.
    have := hsE6E4Sq.mul_left ‖(48 : ℂ)‖
    simpa [mul_assoc, norm_mul, Rat.cast_mul, Rat.cast_ofNat] using! this
  have hs2 :
      Summable (fun n : ℕ =>
        ‖(((2 : ℚ) * conv coeffE2 coeffPhi2Core n : ℂ) * qterm (it t ht0) n)‖) := by
    have := hsE2Phi2.mul_left ‖(2 : ℂ)‖
    simpa [mul_assoc, norm_mul, Rat.cast_mul, Rat.cast_ofNat] using! this
  -- Finally bound the sum by the sum of norms; this is enough for summability.
  have hsum :
      ∀ n : ℕ,
        ‖((coeffPhi1Core n : ℂ) * qterm (it t ht0) n)‖ ≤
          ‖(((48 : ℚ) * conv coeffE6 coeffE4Sq n : ℂ) * qterm (it t ht0) n)‖ +
            ‖(((2 : ℚ) * conv coeffE2 coeffPhi2Core n : ℂ) * qterm (it t ht0) n)‖ := by
    intro n
    -- `‖(a+b) * q‖ ≤ ‖a*q‖ + ‖b*q‖`
    have :
        ‖(((48 : ℚ) * conv coeffE6 coeffE4Sq n : ℂ) +
              ((2 : ℚ) * conv coeffE2 coeffPhi2Core n : ℂ)) *
            qterm (it t ht0) n‖ ≤
          ‖(((48 : ℚ) * conv coeffE6 coeffE4Sq n : ℂ) * qterm (it t ht0) n)‖ +
            ‖(((2 : ℚ) * conv coeffE2 coeffPhi2Core n : ℂ) * qterm (it t ht0) n)‖ := by
      simpa [mul_add, add_mul] using!
        (norm_add_le
          (((48 : ℚ) * conv coeffE6 coeffE4Sq n : ℂ) * qterm (it t ht0) n)
          (((2 : ℚ) * conv coeffE2 coeffPhi2Core n : ℂ) * qterm (it t ht0) n))
    simpa
        [coeffPhi1Core, add_mul, mul_add, mul_assoc, add_assoc, add_left_comm, add_comm]
      using! this
  -- Use majorization to conclude summability.
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hsum (hs1.add hs2)

/-- Express `E₆(it t)^2` as a `q`-series with coefficients `coeffE6Sq`. -/
public lemma E₆_sq_it_eq_qseries (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    (E₆ (it t ht0)) ^ (2 : ℕ) = qseries (fun n : ℕ => (coeffE6Sq n : ℂ)) (it t ht0) := by
  set z : ℍ := it t ht0
  have hE6 : E₆ z = qseries (fun n : ℕ => (coeffE6 n : ℂ)) z := by
    simpa [z] using! (E₆_eq_qseries (z := z))
  have hsE6 : Summable (fun n : ℕ => ‖(coeffE6 n : ℂ) * qterm z n‖) := by
    simpa [z] using! summable_norm_qseries_coeffE6 (t := t) (ht0 := ht0) (ht := ht)
  have hmul :
      qseries (fun n : ℕ => (coeffE6 n : ℂ)) z *
          qseries (fun n : ℕ => (coeffE6 n : ℂ)) z =
        qseries (fun n : ℕ => (conv coeffE6 coeffE6 n : ℂ)) z := by
    simpa using! (qseries_mul_cast (z := z) (a := coeffE6) (b := coeffE6) hsE6 hsE6)
  simpa [pow_two, hE6, coeffE6Sq, z] using! hmul

/-- Express `E₄(it t)^3` as a `q`-series with coefficients `coeffE4Cube`. -/
public lemma E₄_cube_it_eq_qseries (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    (E₄ (it t ht0)) ^ (3 : ℕ) = qseries (fun n : ℕ => (coeffE4Cube n : ℂ)) (it t ht0) := by
  set z : ℍ := it t ht0
  have hE4 : E₄ z = qseries (fun n : ℕ => (coeffE4 n : ℂ)) z := by
    simpa [z] using! (E₄_eq_qseries (z := z))
  have hE4Sq : (E₄ z) ^ (2 : ℕ) = qseries (fun n : ℕ => (coeffE4Sq n : ℂ)) z := by
    simpa [coeffE4Sq, z] using! (E₄_sq_eq_qseries_conv (t := t) (ht0 := ht0) (ht := ht))
  have hsE4Sq : Summable (fun n : ℕ => ‖(coeffE4Sq n : ℂ) * qterm z n‖) := by
    simpa [z] using! summable_norm_qseries_coeffE4Sq (t := t) (ht0 := ht0) (ht := ht)
  have hsE4 : Summable (fun n : ℕ => ‖(coeffE4 n : ℂ) * qterm z n‖) := by
    simpa [z] using! summable_norm_qseries_coeffE4 (t := t) (ht0 := ht0) (ht := ht)
  have hmul :
      qseries (fun n : ℕ => (coeffE4Sq n : ℂ)) z * qseries (fun n : ℕ => (coeffE4 n : ℂ)) z =
        qseries (fun n : ℕ => (coeffE4Cube n : ℂ)) z := by
    simpa [coeffE4Cube] using!
      (qseries_mul_cast (z := z) (a := coeffE4Sq) (b := coeffE4) hsE4Sq hsE4)
  calc
    (E₄ z) ^ (3 : ℕ) = (E₄ z) ^ (2 : ℕ) * E₄ z := by
      simpa using! (pow_succ (E₄ z) 2)
    _ = qseries (fun n : ℕ => (coeffE4Sq n : ℂ)) z * qseries (fun n : ℕ => (coeffE4 n : ℂ)) z := by
      rw [hE4Sq, hE4]
    _ = qseries (fun n : ℕ => (coeffE4Cube n : ℂ)) z := hmul
    _ = qseries (fun n : ℕ => (coeffE4Cube n : ℂ)) (it t ht0) := by simp [z]

end SpherePacking.Dim24.AppendixA
