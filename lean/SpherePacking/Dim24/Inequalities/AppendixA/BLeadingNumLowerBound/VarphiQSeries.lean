-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.QSeriesHelpers
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.Numerators
import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesMul
import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesSummable


/-!
### `varphi_num` as a `qseries`

This file proves the `qseries` identity for `varphi_num (it t)` used in the remainder estimate,
with coefficients given by `coeffVarphiNum` from `QSeriesHelpers`.
-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.AppendixA

/--
At `z = it t` (with `t ≥ 1`), `varphi_num z` equals the `qseries` with coefficients
`coeffVarphiNum`. -/
public lemma varphi_num_it_eq_qseries (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    varphi_num (it t ht0) = qseries (fun n : ℕ => (coeffVarphiNum n : ℂ)) (it t ht0) := by
  set z : ℍ := it t ht0
  let A : ℕ → ℚ := fun n => (25 : ℚ) * coeffE4Fourth n
  let B : ℕ → ℚ := fun n => (-49 : ℚ) * conv coeffE6Sq coeffE4 n
  let C : ℕ → ℚ := fun n => (48 : ℚ) * conv (conv coeffE6 coeffE4Sq) coeffE2 n
  let D : ℕ → ℚ :=
    fun n => conv (fun m => (-49 : ℚ) * coeffE4Cube m + (25 : ℚ) * coeffE6Sq m) coeffE2Sq n
  -- Summability for the Eisenstein coefficient series.
  have hsE2 : Summable (fun n : ℕ => ‖(coeffE2 n : ℂ) * qterm z n‖) := by
    simpa [z] using! summable_norm_qseries_coeffE2 (t := t) (ht0 := ht0) (ht := ht)
  have hsE4 : Summable (fun n : ℕ => ‖(coeffE4 n : ℂ) * qterm z n‖) := by
    simpa [z] using! summable_norm_qseries_coeffE4 (t := t) (ht0 := ht0) (ht := ht)
  have hsE6 : Summable (fun n : ℕ => ‖(coeffE6 n : ℂ) * qterm z n‖) := by
    simpa [z] using! summable_norm_qseries_coeffE6 (t := t) (ht0 := ht0) (ht := ht)
  have hsE2Sq : Summable (fun n : ℕ => ‖(coeffE2Sq n : ℂ) * qterm z n‖) := by
    simpa [z] using! summable_norm_qseries_coeffE2Sq (t := t) (ht0 := ht0) (ht := ht)
  have hsE4Sq : Summable (fun n : ℕ => ‖(coeffE4Sq n : ℂ) * qterm z n‖) := by
    simpa [z] using! summable_norm_qseries_coeffE4Sq (t := t) (ht0 := ht0) (ht := ht)
  have hsE6Sq : Summable (fun n : ℕ => ‖(coeffE6Sq n : ℂ) * qterm z n‖) := by
    simpa [z] using! summable_norm_qseries_coeffE6Sq (t := t) (ht0 := ht0) (ht := ht)
  have hsE4Cube : Summable (fun n : ℕ => ‖(coeffE4Cube n : ℂ) * qterm z n‖) := by
    simpa [z] using! summable_norm_qseries_coeffE4Cube (t := t) (ht0 := ht0) (ht := ht)
  have hsE4Fourth : Summable (fun n : ℕ => ‖(coeffE4Fourth n : ℂ) * qterm z n‖) := by
    simpa [z] using! summable_norm_qseries_coeffE4Fourth (t := t) (ht0 := ht0) (ht := ht)
  -- Summability for the derived conv coefficients in `B` and `C`.
  have hsConvE6SqE4 :
      Summable (fun n : ℕ => ‖(conv coeffE6Sq coeffE4 n : ℂ) * qterm z n‖) := by
    have habs : ∀ n : ℕ, |(conv coeffE6Sq coeffE4 n : ℝ)| ≤
        ((504 * 504 : ℝ) * (240 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ ((6 + 6 + 1) + 4 + 1)) :=
      abs_conv_coeffE6Sq_coeffE4_le
    exact summable_norm_qseries_of_coeffBound t ht0 ht (conv coeffE6Sq coeffE4) (504 * 504 * 240)
      (6 + 6 + 1 + 4 + 1) habs
  have hsConvE6E4SqE2 :
      Summable (fun n : ℕ =>
        ‖(conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℂ) * qterm z n‖) := by
    have habs : ∀ n : ℕ,
        |(conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℝ)| ≤
          (((504 : ℝ) * (240 * 240 : ℝ)) * (24 : ℝ)) *
            (((n + 1 : ℕ) : ℝ) ^ ((6 + (4 + 4 + 1) + 1) + 2 + 1)) :=
      abs_conv_coeffE6_coeffE4Sq_coeffE2_le
    exact summable_norm_qseries_of_coeffBound t ht0 ht (conv (conv coeffE6 coeffE4Sq) coeffE2)
      (504 * (240 * 240) * 24) (6 + (4 + 4 + 1) + 1 + 2 + 1) habs
  -- Summability for the four coefficient sequences.
  have hsA : Summable (fun n : ℕ => ‖(A n : ℂ) * qterm z n‖) := by
    have := hsE4Fourth.mul_left ‖(25 : ℂ)‖
    simpa [A, mul_assoc, norm_mul, Rat.cast_mul, Rat.cast_ofNat] using! this
  have hsB : Summable (fun n : ℕ => ‖(B n : ℂ) * qterm z n‖) := by
    have := hsConvE6SqE4.mul_left ‖(-49 : ℂ)‖
    simpa [B, mul_assoc, norm_mul, Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat] using! this
  have hsC : Summable (fun n : ℕ => ‖(C n : ℂ) * qterm z n‖) := by
    have := hsConvE6E4SqE2.mul_left ‖(48 : ℂ)‖
    simpa [C, mul_assoc, norm_mul, Rat.cast_mul, Rat.cast_ofNat] using! this
  have hsD : Summable (fun n : ℕ => ‖(D n : ℂ) * qterm z n‖) := by
    have habs : ∀ n : ℕ,
        |(D n : ℝ)| ≤
          ((((49 : ℝ) * ((240 * 240 : ℝ) * (240 : ℝ))) + ((25 : ℝ) * (504 * 504 : ℝ))) *
              (24 * 24 : ℝ)) *
            (((n + 1 : ℕ) : ℝ) ^ (((4 + 4 + 1) + 4 + 1) + (2 + 2 + 1) + 1)) := by
      intro n
      simpa [D, mul_assoc, add_assoc, add_left_comm, add_comm] using!
          (abs_conv_le
          (a := fun m => (-49 : ℚ) * coeffE4Cube m + (25 : ℚ) * coeffE6Sq m)
          (b := coeffE2Sq)
          (Ca :=
            ((49 : ℝ) * ((240 * 240 : ℝ) * (240 : ℝ))) + ((25 : ℝ) * (504 * 504 : ℝ)))
          (Cb := (24 * 24 : ℝ))
          (ka := ((4 + 4 + 1) + 4 + 1)) (kb := (2 + 2 + 1))
          abs_lincomb_E4Cube_E6Sq_le abs_coeffE2Sq_le n)
    exact
        summable_norm_qseries_of_coeffBound t ht0 ht D
          ((49 * (240 * 240 * 240) + 25 * (504 * 504)) * (24 * 24))
          (4 + 4 + 1 + 4 + 1 + (2 + 2 + 1) + 1) habs
  have hcoef :
      (fun n : ℕ => (A n : ℂ) + (B n : ℂ) + (C n : ℂ) + (D n : ℂ)) =
        fun n : ℕ => (coeffVarphiNum n : ℂ) := by
    funext n
    simp [coeffVarphiNum, A, B, C, D, sub_eq_add_neg, add_assoc]
  have hsum_coeff :
      qseries (fun n : ℕ => (A n : ℂ)) z +
            qseries (fun n : ℕ => (B n : ℂ)) z +
            qseries (fun n : ℕ => (C n : ℂ)) z +
            qseries (fun n : ℕ => (D n : ℂ)) z =
          qseries (fun n : ℕ => (coeffVarphiNum n : ℂ)) z := by
    have h :=
      qseries_add4_cast
        (t := t) (ht0 := ht0)
        (a := A) (b := B) (c := C) (d := D)
        hsA hsB hsC hsD
    simpa [z, hcoef] using! h
  -- Basic `qseries` expansions.
  have hE2 : E₂ z = qseries (fun n : ℕ => (coeffE2 n : ℂ)) z := by
    simpa [z] using! (E₂_eq_qseries (z := z))
  have hE4 : E₄ z = qseries (fun n : ℕ => (coeffE4 n : ℂ)) z := by
    simpa [z] using! (E₄_eq_qseries (z := z))
  have hE6 : E₆ z = qseries (fun n : ℕ => (coeffE6 n : ℂ)) z := by
    simpa [z] using! (E₆_eq_qseries (z := z))
  have hE2Sq : (E₂ z) ^ 2 = qseries (fun n : ℕ => (coeffE2Sq n : ℂ)) z := by
    have hmul :
        qseries (fun n : ℕ => (coeffE2 n : ℂ)) z *
            qseries (fun n : ℕ => (coeffE2 n : ℂ)) z =
          qseries (fun n : ℕ => (coeffE2Sq n : ℂ)) z := by
      simpa [z, coeffE2Sq] using!
        qseries_mul_cast (z := z) (a := coeffE2) (b := coeffE2) hsE2 hsE2
    simpa [pow_two, hE2] using! hmul
  have hE4Sq : (E₄ z) ^ 2 = qseries (fun n : ℕ => (coeffE4Sq n : ℂ)) z := by
    have hmul :
        qseries (fun n : ℕ => (coeffE4 n : ℂ)) z *
            qseries (fun n : ℕ => (coeffE4 n : ℂ)) z =
          qseries (fun n : ℕ => (coeffE4Sq n : ℂ)) z := by
      simpa [z, coeffE4Sq] using!
        qseries_mul_cast (z := z) (a := coeffE4) (b := coeffE4) hsE4 hsE4
    simpa [pow_two, hE4] using! hmul
  have hE4Fourth : (E₄ z) ^ 4 = qseries (fun n : ℕ => (coeffE4Fourth n : ℂ)) z := by
    have hmul :
        qseries (fun n : ℕ => (coeffE4Sq n : ℂ)) z *
            qseries (fun n : ℕ => (coeffE4Sq n : ℂ)) z =
          qseries (fun n : ℕ => (coeffE4Fourth n : ℂ)) z := by
      simpa [z, coeffE4Fourth] using!
        qseries_mul_cast (z := z) (a := coeffE4Sq) (b := coeffE4Sq) hsE4Sq hsE4Sq
    have : (4 : ℕ) = 2 + 2 := by decide
    calc
      (E₄ z) ^ 4 = (E₄ z) ^ (2 + 2) := by simp [this]
      _ = (E₄ z) ^ 2 * (E₄ z) ^ 2 := by
            simpa using! (pow_add (E₄ z) 2 2)
      _ =
            qseries (fun n : ℕ => (coeffE4Sq n : ℂ)) z *
              qseries (fun n : ℕ => (coeffE4Sq n : ℂ)) z := by
            simpa using! congrArg (fun x : ℂ => x * x) hE4Sq
      _ = qseries (fun n : ℕ => (coeffE4Fourth n : ℂ)) z := hmul
  have hE6Sq : (E₆ z) ^ 2 = qseries (fun n : ℕ => (coeffE6Sq n : ℂ)) z := by
    have hmul :
        qseries (fun n : ℕ => (coeffE6 n : ℂ)) z *
            qseries (fun n : ℕ => (coeffE6 n : ℂ)) z =
          qseries (fun n : ℕ => (coeffE6Sq n : ℂ)) z := by
      simpa [z, coeffE6Sq] using!
        qseries_mul_cast (z := z) (a := coeffE6) (b := coeffE6) hsE6 hsE6
    simpa [pow_two, hE6] using! hmul
  have hE6Sq_mul_E4 :
      (E₆ z) ^ 2 * (E₄ z) =
        qseries (fun n : ℕ => (conv coeffE6Sq coeffE4 n : ℂ)) z := by
    have hmul :
        qseries (fun n : ℕ => (coeffE6Sq n : ℂ)) z *
            qseries (fun n : ℕ => (coeffE4 n : ℂ)) z =
          qseries (fun n : ℕ => (conv coeffE6Sq coeffE4 n : ℂ)) z := by
      simpa [z] using! (qseries_mul_cast (z := z) (a := coeffE6Sq) (b := coeffE4) hsE6Sq hsE4)
    calc
      (E₆ z) ^ 2 * (E₄ z) =
          qseries (fun n : ℕ => (coeffE6Sq n : ℂ)) z *
            qseries (fun n : ℕ => (coeffE4 n : ℂ)) z := by
          rw [hE6Sq, hE4]
      _ = qseries (fun n : ℕ => (conv coeffE6Sq coeffE4 n : ℂ)) z := hmul
  have hsE6E4Sq : Summable (fun n : ℕ => ‖(conv coeffE6 coeffE4Sq n : ℂ) * qterm z n‖) := by
    have habs : ∀ n : ℕ,
        |(conv coeffE6 coeffE4Sq n : ℝ)| ≤ ((504 : ℝ) * (240 * 240 : ℝ)) *
          (((n + 1 : ℕ) : ℝ) ^ (6 + (4 + 4 + 1) + 1)) := abs_conv_coeffE6_coeffE4Sq_le
    exact summable_norm_qseries_of_coeffBound t ht0 ht (conv coeffE6 coeffE4Sq) (504 * (240 * 240))
      (6 + (4 + 4 + 1) + 1) habs
  have hE6E4Sq_mul_E2 :
      (E₆ z) * (E₄ z) ^ 2 * (E₂ z) =
        qseries (fun n : ℕ => (conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℂ)) z := by
    have hmul1 :
        qseries (fun n : ℕ => (coeffE6 n : ℂ)) z *
            qseries (fun n : ℕ => (coeffE4Sq n : ℂ)) z =
          qseries (fun n : ℕ => (conv coeffE6 coeffE4Sq n : ℂ)) z := by
      simpa [z] using!
        qseries_mul_cast (z := z) (a := coeffE6) (b := coeffE4Sq) hsE6 hsE4Sq
    have hmul2 :
        qseries (fun n : ℕ => (conv coeffE6 coeffE4Sq n : ℂ)) z *
            qseries (fun n : ℕ => (coeffE2 n : ℂ)) z =
          qseries (fun n : ℕ => (conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℂ)) z :=
      qseries_mul_cast z (conv coeffE6 coeffE4Sq) coeffE2 hsE6E4Sq hsE2
    have : (E₆ z) * (E₄ z) ^ 2 =
        qseries (fun n : ℕ => (conv coeffE6 coeffE4Sq n : ℂ)) z := by
      calc
        (E₆ z) * (E₄ z) ^ 2 =
            qseries (fun n : ℕ => (coeffE6 n : ℂ)) z *
              qseries (fun n : ℕ => (coeffE4Sq n : ℂ)) z := by
            rw [hE6, hE4Sq]
        _ = qseries (fun n : ℕ => (conv coeffE6 coeffE4Sq n : ℂ)) z := hmul1
    calc
      (E₆ z) * (E₄ z) ^ 2 * (E₂ z) =
          qseries (fun n : ℕ => (conv coeffE6 coeffE4Sq n : ℂ)) z *
            qseries (fun n : ℕ => (coeffE2 n : ℂ)) z := by
              rw [this, hE2]
      _ = qseries (fun n : ℕ => (conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℂ)) z := hmul2
  -- Linear combination term.
  let aLin : ℕ → ℚ := fun n => (-49 : ℚ) * coeffE4Cube n + (25 : ℚ) * coeffE6Sq n
  have hsLin : Summable (fun n : ℕ => ‖(aLin n : ℂ) * qterm z n‖) := by
    have habs : ∀ n : ℕ, |(aLin n : ℝ)| ≤
        (((49 : ℝ) * ((240 * 240 : ℝ) * (240 : ℝ))) + ((25 : ℝ) * (504 * 504 : ℝ))) *
          (((n + 1 : ℕ) : ℝ) ^ ((4 + 4 + 1) + 4 + 1)) := by
      intro n
      simpa [aLin] using! abs_lincomb_E4Cube_E6Sq_le (n := n)
    simpa [z, aLin] using!
      (summable_norm_qseries_of_coeffBound (t := t) (ht0 := ht0) (ht := ht) (a := aLin)
        (C := (((49 : ℝ) * ((240 * 240 : ℝ) * (240 : ℝ))) + ((25 : ℝ) * (504 * 504 : ℝ))))
        (k := ((4 + 4 + 1) + 4 + 1)) habs)
  have hE4Cube : (E₄ z) ^ 3 = qseries (fun n : ℕ => (coeffE4Cube n : ℂ)) z := by
    have hmul :
        qseries (fun n : ℕ => (coeffE4Sq n : ℂ)) z *
            qseries (fun n : ℕ => (coeffE4 n : ℂ)) z =
          qseries (fun n : ℕ => (coeffE4Cube n : ℂ)) z := by
      simpa [z, coeffE4Cube] using!
        qseries_mul_cast (z := z) (a := coeffE4Sq) (b := coeffE4) hsE4Sq hsE4
    have : (E₄ z) ^ 3 = (E₄ z) ^ 2 * (E₄ z) := by
      simp [pow_succ, mul_assoc]
    calc
      (E₄ z) ^ 3 = (E₄ z) ^ 2 * (E₄ z) := this
      _ =
            qseries (fun n : ℕ => (coeffE4Sq n : ℂ)) z *
              qseries (fun n : ℕ => (coeffE4 n : ℂ)) z := by
            rw [hE4Sq, hE4]
      _ = qseries (fun n : ℕ => (coeffE4Cube n : ℂ)) z := hmul
  have hsE4CubeScaled :
      Summable (fun n : ℕ =>
        ‖((((-49 : ℚ) * coeffE4Cube n : ℚ) : ℂ) * qterm z n)‖) := by
    have := hsE4Cube.mul_left ‖(-49 : ℂ)‖
    simpa [mul_assoc, Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat, norm_mul] using! this
  have hsE6SqScaled :
      Summable (fun n : ℕ =>
        ‖((((25 : ℚ) * coeffE6Sq n : ℚ) : ℂ) * qterm z n)‖) := by
    have := hsE6Sq.mul_left ‖(25 : ℂ)‖
    simpa [mul_assoc, Rat.cast_mul, Rat.cast_ofNat, norm_mul] using! this
  have hlin :
      ((-49 : ℂ) * (E₄ z) ^ 3 + (25 : ℂ) * (E₆ z) ^ 2) =
        qseries (fun n : ℕ => (aLin n : ℂ)) z := by
    have h1 :
        (-49 : ℂ) * qseries (fun n : ℕ => (coeffE4Cube n : ℂ)) z =
          qseries (fun n : ℕ => (((-49 : ℚ) * coeffE4Cube n : ℚ) : ℂ)) z := by
      simpa [z] using!
        qseries_mul_qrat (t := t) (ht0 := ht0) (c := (-49 : ℚ)) (a := coeffE4Cube)
    have h2 :
        (25 : ℂ) * qseries (fun n : ℕ => (coeffE6Sq n : ℂ)) z =
          qseries (fun n : ℕ => (((25 : ℚ) * coeffE6Sq n : ℚ) : ℂ)) z := by
      simpa [z] using! (qseries_mul_qrat (t := t) (ht0 := ht0) (c := (25 : ℚ)) (a := coeffE6Sq))
    have hadd :
        qseries (fun n : ℕ => (((-49 : ℚ) * coeffE4Cube n : ℚ) : ℂ)) z +
            qseries (fun n : ℕ => (((25 : ℚ) * coeffE6Sq n : ℚ) : ℂ)) z =
          qseries (fun n : ℕ => (aLin n : ℂ)) z :=
      qseries_add_cast t ht0
        (fun n => -49 * coeffE4Cube n) (fun n => 25 * coeffE6Sq n)
        hsE4CubeScaled hsE6SqScaled
    calc
      (-49 : ℂ) * (E₄ z) ^ 3 + (25 : ℂ) * (E₆ z) ^ 2
          = (-49 : ℂ) * qseries (fun n : ℕ => (coeffE4Cube n : ℂ)) z +
              (25 : ℂ) * qseries (fun n : ℕ => (coeffE6Sq n : ℂ)) z := by
                rw [hE4Cube, hE6Sq]
      _ = qseries (fun n : ℕ => (((-49 : ℚ) * coeffE4Cube n : ℚ) : ℂ)) z +
            qseries (fun n : ℕ => (((25 : ℚ) * coeffE6Sq n : ℚ) : ℂ)) z := by
              simp [h1, h2]
      _ = qseries (fun n : ℕ => (aLin n : ℂ)) z := hadd
  have hLin_mul_E2Sq :
      ((-49 : ℂ) * (E₄ z) ^ 3 + (25 : ℂ) * (E₆ z) ^ 2) * (E₂ z) ^ 2 =
        qseries (fun n : ℕ => (D n : ℂ)) z := by
    have hmul :
        qseries (fun n : ℕ => (aLin n : ℂ)) z *
            qseries (fun n : ℕ => (coeffE2Sq n : ℂ)) z =
          qseries (fun n : ℕ => (conv aLin coeffE2Sq n : ℂ)) z := by
      simpa [z] using!
        qseries_mul_cast (z := z) (a := aLin) (b := coeffE2Sq) hsLin hsE2Sq
    have hDcoef : (fun n : ℕ => (conv aLin coeffE2Sq n : ℂ)) = fun n => (D n : ℂ) := by
      funext n
      simp [D, aLin]
    have : ((-49 : ℂ) * (E₄ z) ^ 3 + (25 : ℂ) * (E₆ z) ^ 2) * (E₂ z) ^ 2 =
        qseries (fun n : ℕ => (conv aLin coeffE2Sq n : ℂ)) z := by
      calc
        ((-49 : ℂ) * (E₄ z) ^ 3 + (25 : ℂ) * (E₆ z) ^ 2) * (E₂ z) ^ 2 =
            qseries (fun n : ℕ => (aLin n : ℂ)) z *
              qseries (fun n : ℕ => (coeffE2Sq n : ℂ)) z := by
              rw [hlin, hE2Sq]
        _ = qseries (fun n : ℕ => (conv aLin coeffE2Sq n : ℂ)) z := hmul
    simpa [hDcoef] using! this
  -- Each term is computed by `qseries_mul_cast` and `qseries_mul_qrat`.
  have hAterm : (25 : ℂ) * (E₄ z) ^ 4 = qseries (fun n : ℕ => (A n : ℂ)) z := by
    rw [hE4Fourth]
    simpa [A, z] using! qseries_mul_qrat (t := t) (ht0 := ht0) (c := 25) (a := coeffE4Fourth)
  have hBterm :
      (-49 : ℂ) * ((E₆ z) ^ 2 * (E₄ z)) = qseries (fun n : ℕ => (B n : ℂ)) z := by
    rw [hE6Sq_mul_E4]
    simpa [B, z] using!
      qseries_mul_qrat
        (t := t) (ht0 := ht0) (c := (-49 : ℚ)) (a := fun n => conv coeffE6Sq coeffE4 n)
  have hCterm :
      (48 : ℂ) * ((E₆ z) * (E₄ z) ^ 2 * (E₂ z)) =
        qseries (fun n : ℕ => (C n : ℂ)) z := by
    rw [hE6E4Sq_mul_E2]
    simpa [C, z] using!
      qseries_mul_qrat
        (t := t) (ht0 := ht0) (c := 48)
        (a := fun n => conv (conv coeffE6 coeffE4Sq) coeffE2 n)
  have hvarphi_sum :
      varphi_num z =
          qseries (fun n : ℕ => (A n : ℂ)) z +
            qseries (fun n : ℕ => (B n : ℂ)) z +
            qseries (fun n : ℕ => (C n : ℂ)) z +
            qseries (fun n : ℕ => (D n : ℂ)) z := by
    have hfirst :
        (25 : ℂ) * (E₄ z) ^ 4 - (49 : ℂ) * (E₆ z) ^ 2 * (E₄ z) =
          qseries (fun n : ℕ => (A n : ℂ)) z + qseries (fun n : ℕ => (B n : ℂ)) z := by
      calc
        (25 : ℂ) * (E₄ z) ^ 4 - (49 : ℂ) * (E₆ z) ^ 2 * (E₄ z) =
            (25 : ℂ) * (E₄ z) ^ 4 + (-(49 : ℂ) * (E₆ z) ^ 2 * (E₄ z)) := by
              simp [sub_eq_add_neg]
        _ = (25 : ℂ) * (E₄ z) ^ 4 + ((-49 : ℂ) * ((E₆ z) ^ 2 * (E₄ z))) := by
              simp [mul_assoc]
        _ = qseries (fun n : ℕ => (A n : ℂ)) z + qseries (fun n : ℕ => (B n : ℂ)) z := by
              rw [hAterm, hBterm]
    have hsecond :
        (48 : ℂ) * (E₆ z) * (E₄ z) ^ 2 * (E₂ z) =
          qseries (fun n : ℕ => (C n : ℂ)) z := by
      simpa [mul_assoc] using! hCterm
    unfold varphi_num
    rw [hfirst, hsecond, hLin_mul_E2Sq]
  calc
    varphi_num (it t ht0) = varphi_num z := by simp [z]
    _ = qseries (fun n : ℕ => (A n : ℂ)) z +
          qseries (fun n : ℕ => (B n : ℂ)) z +
          qseries (fun n : ℕ => (C n : ℂ)) z +
          qseries (fun n : ℕ => (D n : ℂ)) z := hvarphi_sum
    _ = qseries (fun n : ℕ => (coeffVarphiNum n : ℂ)) z := hsum_coeff
    _ = qseries (fun n : ℕ => (coeffVarphiNum n : ℂ)) (it t ht0) := by simp [z]
end SpherePacking.Dim24.AppendixA
