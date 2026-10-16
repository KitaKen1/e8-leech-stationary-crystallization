/- Helper lemmas for expressing numerator terms as `qseries`. -/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.EisensteinSeriesBounds
import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesMul
import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesSummable


/-!
### `qseries` helper API and numerator coefficients

This file provides small helper lemmas for manipulating `qseries` (additivity and scalar
multiplication) and defines convolution-based coefficient functions used later for the
`varphi_num` numerator expansion. It also records polynomial coefficient bounds and summability
lemmas for these derived sequences.
-/


open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.AppendixA


/--
At `z = it t` (with `t ≥ 1`), expand `(E₄ z)^2` as a `qseries` using
convolution coefficients. -/
public lemma E₄_sq_eq_qseries_conv (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    (E₄ (it t ht0)) ^ (2 : ℕ) = qseries (fun n : ℕ => (conv coeffE4 coeffE4 n : ℂ)) (it t ht0) := by
  have ha :
      Summable (fun n : ℕ => ‖((coeffE4 n : ℂ) * qterm (it t ht0) n)‖) := by
    simpa using!
      (summable_norm_qseries_of_coeffBound (t := t) (ht0 := ht0) (ht := ht)
        (a := coeffE4) (C := (240 : ℝ)) (k := 4) abs_coeffE4_le)
  simpa [pow_two, E₄_eq_qseries (z := it t ht0)] using!
    (qseries_mul_cast (z := it t ht0) (a := coeffE4) (b := coeffE4) ha ha)

/-- Additivity of `qseries`, assuming summability of the two norm series. -/
public lemma qseries_add_of_summable (z : ℍ) (a b : ℕ → ℂ)
    (ha : Summable (fun n : ℕ => ‖a n * qterm z n‖))
    (hb : Summable (fun n : ℕ => ‖b n * qterm z n‖)) :
    qseries (fun n : ℕ => a n + b n) z = qseries a z + qseries b z := by
  have ha' : Summable (fun n : ℕ => a n * qterm z n) := Summable.of_norm ha
  have hb' : Summable (fun n : ℕ => b n * qterm z n) := Summable.of_norm hb
  simp [qseries, add_mul, ha'.tsum_add hb']

private lemma qseries_smul_of_summable (z : ℍ) (c : ℂ) (a : ℕ → ℂ) :
    qseries (fun n : ℕ => c * a n) z = c * qseries a z := by
  simp [qseries, mul_assoc, tsum_mul_left]

/-!
### `q`-series expansion of `varphi_num`

This mirrors the explicit convolution computation used in `appendix.txt`.
-/

/-- Coefficients of `(E₂)^2` as a `qseries`, computed by the Cauchy product on `coeffE2`. -/
@[expose] public def coeffE2Sq : ℕ → ℚ := fun n => conv coeffE2 coeffE2 n
/-- Coefficients of `(E₄)^2` as a `qseries`, computed by the Cauchy product on `coeffE4`. -/
@[expose] public def coeffE4Sq : ℕ → ℚ := fun n => conv coeffE4 coeffE4 n
/-- Coefficients of `(E₄)^3` as a `qseries`, computed as `conv coeffE4Sq coeffE4`. -/
@[expose] public def coeffE4Cube : ℕ → ℚ := fun n => conv coeffE4Sq coeffE4 n
/-- Coefficients of `(E₄)^4` as a `qseries`, computed as `conv coeffE4Sq coeffE4Sq`. -/
@[expose] public def coeffE4Fourth : ℕ → ℚ := fun n => conv coeffE4Sq coeffE4Sq n
/-- Coefficients of `(E₆)^2` as a `qseries`, computed by the Cauchy product on `coeffE6`. -/
@[expose] public def coeffE6Sq : ℕ → ℚ := fun n => conv coeffE6 coeffE6 n

/-- Coefficients for the numerator `varphi_num`, written as an explicit polynomial in Eisenstein
series and translated to `q`-series coefficients via convolution. -/
@[expose] public def coeffVarphiNum : ℕ → ℚ :=
  fun n =>
    (25 : ℚ) * coeffE4Fourth n
      - (49 : ℚ) * (conv coeffE6Sq coeffE4 n)
      + (48 : ℚ) * (conv (conv coeffE6 coeffE4Sq) coeffE2 n)
      + (conv (fun m => (-49 : ℚ) * coeffE4Cube m + (25 : ℚ) * coeffE6Sq m) coeffE2Sq n)

/-!
### Coefficient bounds for convolution coefficients

These are used both for summability of the corresponding `qseries` and for further convolution
bounds downstream.
-/

private lemma abs_conv_le' (a b : ℕ → ℚ) (Ca Cb : ℝ) (ka kb : ℕ)
    (ha : ∀ n : ℕ, |(a n : ℝ)| ≤ Ca * (((n + 1 : ℕ) : ℝ) ^ ka))
    (hb : ∀ n : ℕ, |(b n : ℝ)| ≤ Cb * (((n + 1 : ℕ) : ℝ) ^ kb)) (n : ℕ) :
    |(conv a b n : ℝ)| ≤ (Ca * Cb) * (((n + 1 : ℕ) : ℝ) ^ (ka + kb + 1)) := by
  simpa [mul_assoc, add_assoc, add_left_comm, add_comm] using!
    (abs_conv_le (a := a) (b := b) (Ca := Ca) (Cb := Cb) (ka := ka) (kb := kb) ha hb n)

/-- Polynomial growth bound for the convolution coefficients `coeffE2Sq`. -/
public lemma abs_coeffE2Sq_le (n : ℕ) :
    |(coeffE2Sq n : ℝ)| ≤ (24 * 24 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (2 + 2 + 1)) := by
  simpa [coeffE2Sq] using!
    abs_conv_le' coeffE2 coeffE2 (24 : ℝ) (24 : ℝ) 2 2 abs_coeffE2_le abs_coeffE2_le n

/-- Polynomial growth bound for the convolution coefficients `coeffE4Sq`. -/
public lemma abs_coeffE4Sq_le (n : ℕ) :
    |(coeffE4Sq n : ℝ)| ≤ (240 * 240 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (4 + 4 + 1)) := by
  simpa [coeffE4Sq] using!
    abs_conv_le' coeffE4 coeffE4 (240 : ℝ) (240 : ℝ) 4 4 abs_coeffE4_le abs_coeffE4_le n

/-- Polynomial growth bound for the convolution coefficients `coeffE6Sq`. -/
public lemma abs_coeffE6Sq_le (n : ℕ) :
    |(coeffE6Sq n : ℝ)| ≤ (504 * 504 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (6 + 6 + 1)) := by
  simpa [coeffE6Sq] using!
    abs_conv_le' coeffE6 coeffE6 (504 : ℝ) (504 : ℝ) 6 6 abs_coeffE6_le abs_coeffE6_le n

/-- Polynomial growth bound for the convolution coefficients `coeffE4Cube`. -/
public lemma abs_coeffE4Cube_le (n : ℕ) :
    |(coeffE4Cube n : ℝ)| ≤ ((240 * 240 : ℝ) * (240 : ℝ)) *
      (((n + 1 : ℕ) : ℝ) ^ ((4 + 4 + 1) + 4 + 1)) := by
  simpa [coeffE4Cube, mul_assoc, add_assoc, add_left_comm, add_comm] using!
    abs_conv_le' coeffE4Sq coeffE4 (240 * 240 : ℝ) (240 : ℝ) (4 + 4 + 1) 4 abs_coeffE4Sq_le
      abs_coeffE4_le n

private lemma summable_norm_qseries_of_coeffBound' (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) (a : ℕ → ℚ)
    (C : ℝ) (k : ℕ) (habs : ∀ n : ℕ, |(a n : ℝ)| ≤ C * (((n + 1 : ℕ) : ℝ) ^ k)) :
    Summable (fun n : ℕ => ‖((a n : ℂ) * qterm (it t ht0) n)‖) :=
  summable_norm_qseries_of_coeffBound t ht0 ht a C k habs

/-- Summability of the norm terms for the `qseries` with coefficients `coeffE2` at `z = it t`. -/
public lemma summable_norm_qseries_coeffE2 (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    Summable (fun n : ℕ => ‖((coeffE2 n : ℂ) * qterm (it t ht0) n)‖) := by
  simpa using!
    (summable_norm_qseries_of_coeffBound' (t := t) (ht0 := ht0) (ht := ht)
      (a := coeffE2) (C := (24 : ℝ)) (k := 2) abs_coeffE2_le)

/-- Summability of the norm terms for the `qseries` with coefficients `coeffE4` at `z = it t`. -/
public lemma summable_norm_qseries_coeffE4 (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    Summable (fun n : ℕ => ‖((coeffE4 n : ℂ) * qterm (it t ht0) n)‖) := by
  simpa using!
    (summable_norm_qseries_of_coeffBound' (t := t) (ht0 := ht0) (ht := ht)
      (a := coeffE4) (C := (240 : ℝ)) (k := 4) abs_coeffE4_le)

/-- Summability of the norm terms for the `qseries` with coefficients `coeffE6` at `z = it t`. -/
public lemma summable_norm_qseries_coeffE6 (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    Summable (fun n : ℕ => ‖((coeffE6 n : ℂ) * qterm (it t ht0) n)‖) := by
  simpa using!
    (summable_norm_qseries_of_coeffBound' (t := t) (ht0 := ht0) (ht := ht)
      (a := coeffE6) (C := (504 : ℝ)) (k := 6) abs_coeffE6_le)

/-- Summability of the norm terms for the `qseries` with coefficients `coeffE2Sq` at `z = it t`. -/
public lemma summable_norm_qseries_coeffE2Sq (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    Summable (fun n : ℕ => ‖((coeffE2Sq n : ℂ) * qterm (it t ht0) n)‖) := by
  simpa using!
    (summable_norm_qseries_of_coeffBound (t := t) (ht0 := ht0) (ht := ht)
      (a := coeffE2Sq) (C := (24 * 24 : ℝ)) (k := (2 + 2 + 1)) abs_coeffE2Sq_le)

/-- Summability of the norm terms for the `qseries` with coefficients `coeffE4Sq` at `z = it t`. -/
public lemma summable_norm_qseries_coeffE4Sq (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    Summable (fun n : ℕ => ‖((coeffE4Sq n : ℂ) * qterm (it t ht0) n)‖) := by
  simpa using!
    (summable_norm_qseries_of_coeffBound (t := t) (ht0 := ht0) (ht := ht)
      (a := coeffE4Sq) (C := (240 * 240 : ℝ)) (k := (4 + 4 + 1)) abs_coeffE4Sq_le)

/--
Summability of the norm terms for the `qseries` with coefficients `coeffE4Cube`
at `z = it t`. -/
public lemma summable_norm_qseries_coeffE4Cube (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    Summable (fun n : ℕ => ‖((coeffE4Cube n : ℂ) * qterm (it t ht0) n)‖) := by
  simpa [mul_assoc] using!
    (summable_norm_qseries_of_coeffBound (t := t) (ht0 := ht0) (ht := ht)
      (a := coeffE4Cube) (C := ((240 * 240 : ℝ) * 240)) (k := ((4 + 4 + 1) + 4 + 1))
      abs_coeffE4Cube_le)

/--
Summability of the norm terms for the `qseries` with coefficients `coeffE4Fourth`
at `z = it t`. -/
public lemma summable_norm_qseries_coeffE4Fourth (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    Summable (fun n : ℕ => ‖((coeffE4Fourth n : ℂ) * qterm (it t ht0) n)‖) := by
  have habs :
      ∀ n : ℕ,
        |(coeffE4Fourth n : ℝ)| ≤
          ((240 * 240 : ℝ) * (240 * 240 : ℝ)) *
            (((n + 1 : ℕ) : ℝ) ^ ((4 + 4 + 1) + (4 + 4 + 1) + 1)) := by
    intro n
    simpa [coeffE4Fourth] using!
      abs_conv_le' coeffE4Sq coeffE4Sq (240 * 240 : ℝ) (240 * 240 : ℝ) (4 + 4 + 1) (4 + 4 + 1)
        abs_coeffE4Sq_le abs_coeffE4Sq_le n
  exact summable_norm_qseries_of_coeffBound' t ht0 ht coeffE4Fourth (240 * 240 * (240 * 240))
    (4 + 4 + 1 + (4 + 4 + 1) + 1) habs

/-- Summability of the norm terms for the `qseries` with coefficients `coeffE6Sq` at `z = it t`. -/
public lemma summable_norm_qseries_coeffE6Sq (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    Summable (fun n : ℕ => ‖((coeffE6Sq n : ℂ) * qterm (it t ht0) n)‖) := by
  simpa using!
    (summable_norm_qseries_of_coeffBound (t := t) (ht0 := ht0) (ht := ht)
      (a := coeffE6Sq) (C := (504 * 504 : ℝ)) (k := (6 + 6 + 1)) abs_coeffE6Sq_le)

/-- Polynomial growth bound for the convolution coefficients `conv coeffE6Sq coeffE4`. -/
public lemma abs_conv_coeffE6Sq_coeffE4_le (n : ℕ) :
    |(conv coeffE6Sq coeffE4 n : ℝ)| ≤ ((504 * 504 : ℝ) * (240 : ℝ)) *
      (((n + 1 : ℕ) : ℝ) ^ ((6 + 6 + 1) + 4 + 1)) := by
  simpa using!
    abs_conv_le' coeffE6Sq coeffE4 (504 * 504 : ℝ) (240 : ℝ) (6 + 6 + 1) 4 abs_coeffE6Sq_le
      abs_coeffE4_le n

/-- Polynomial growth bound for the convolution coefficients `conv coeffE6 coeffE4Sq`. -/
public lemma abs_conv_coeffE6_coeffE4Sq_le (n : ℕ) :
    |(conv coeffE6 coeffE4Sq n : ℝ)| ≤ ((504 : ℝ) * (240 * 240 : ℝ)) *
      (((n + 1 : ℕ) : ℝ) ^ (6 + (4 + 4 + 1) + 1)) := by
  simpa using!
    abs_conv_le' coeffE6 coeffE4Sq (504 : ℝ) (240 * 240 : ℝ) 6 (4 + 4 + 1) abs_coeffE6_le
      abs_coeffE4Sq_le n

/--
Polynomial growth bound for the convolution coefficients
`conv (conv coeffE6 coeffE4Sq) coeffE2`. -/
public lemma abs_conv_coeffE6_coeffE4Sq_coeffE2_le (n : ℕ) :
    |(conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℝ)| ≤
      (((504 : ℝ) * (240 * 240 : ℝ)) * (24 : ℝ)) *
        (((n + 1 : ℕ) : ℝ) ^ ((6 + (4 + 4 + 1) + 1) + 2 + 1)) := by
  simpa using!
    abs_conv_le' (fun m => conv coeffE6 coeffE4Sq m) coeffE2 ((504 : ℝ) * (240 * 240 : ℝ))
      (24 : ℝ) (6 + (4 + 4 + 1) + 1) 2 abs_conv_coeffE6_coeffE4Sq_le abs_coeffE2_le n

/-- Polynomial growth bound for the linear combination `(-49) * coeffE4Cube + 25 * coeffE6Sq`. -/
public lemma abs_lincomb_E4Cube_E6Sq_le (n : ℕ) :
    |(((-49 : ℚ) * coeffE4Cube n + (25 : ℚ) * coeffE6Sq n : ℚ) : ℝ)| ≤
      (((49 : ℝ) * ((240 * 240 : ℝ) * (240 : ℝ))) + ((25 : ℝ) * (504 * 504 : ℝ))) *
        (((n + 1 : ℕ) : ℝ) ^ ((4 + 4 + 1) + 4 + 1)) := by
  have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hpow_le :
      (((n + 1 : ℕ) : ℝ) ^ (6 + 6 + 1)) ≤ (((n + 1 : ℕ) : ℝ) ^ ((4 + 4 + 1) + 4 + 1)) := by
    simpa using!
      (pow_le_pow_right₀ hn1
        (by decide : (6 + 6 + 1 : ℕ) ≤ (4 + 4 + 1) + 4 + 1))
  have hE4Cube := abs_coeffE4Cube_le n
  have hE6Sq' :
      |(coeffE6Sq n : ℝ)| ≤
        (504 * 504 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ ((4 + 4 + 1) + 4 + 1)) := by
    calc
      |(coeffE6Sq n : ℝ)| ≤ (504 * 504 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (6 + 6 + 1)) :=
        abs_coeffE6Sq_le n
      _ ≤ (504 * 504 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ ((4 + 4 + 1) + 4 + 1)) := by
            exact mul_le_mul_of_nonneg_left hpow_le (by positivity)
  have htriangle :
      |(((-49 : ℚ) * coeffE4Cube n + (25 : ℚ) * coeffE6Sq n : ℚ) : ℝ)| ≤
        (49 : ℝ) * |(coeffE4Cube n : ℝ)| + (25 : ℝ) * |(coeffE6Sq n : ℝ)| := by
    simpa
        [Rat.cast_add, Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat, abs_mul, mul_assoc, add_assoc,
          add_left_comm, add_comm]
      using!
        (abs_add_le ((-49 : ℝ) * (coeffE4Cube n : ℝ)) ((25 : ℝ) * (coeffE6Sq n : ℝ)))
  linarith

/-- Pull a rational scalar into a `qseries` (after casting coefficients to `ℂ`). -/
public lemma qseries_mul_qrat (t : ℝ) (ht0 : 0 < t) (c : ℚ) (a : ℕ → ℚ) :
    (c : ℂ) * qseries (fun n : ℕ => (a n : ℂ)) (it t ht0) =
      qseries (fun n : ℕ => ((c * a n : ℚ) : ℂ)) (it t ht0) := by
  simpa [Rat.cast_mul] using!
    (qseries_smul_of_summable (z := it t ht0) (c := (c : ℂ)) (a := fun n : ℕ => (a n : ℂ))).symm

/-- Add two `qseries` with rational coefficients (cast to `ℂ`), assuming summability hypotheses. -/
public lemma qseries_add_cast (t : ℝ) (ht0 : 0 < t) (a b : ℕ → ℚ)
    (ha : Summable (fun n : ℕ => ‖(a n : ℂ) * qterm (it t ht0) n‖))
    (hb : Summable (fun n : ℕ => ‖(b n : ℂ) * qterm (it t ht0) n‖)) :
    qseries (fun n : ℕ => (a n : ℂ)) (it t ht0) + qseries (fun n : ℕ => (b n : ℂ)) (it t ht0) =
      qseries (fun n : ℕ => ((a n + b n : ℚ) : ℂ)) (it t ht0) := by
  simpa [Rat.cast_add] using!
    (qseries_add_of_summable (z := it t ht0)
      (a := fun n : ℕ => (a n : ℂ)) (b := fun n : ℕ => (b n : ℂ)) ha hb).symm

/-- Combine four `qseries` with rational coefficients into a single `qseries` of their sum. -/
public lemma qseries_add4_cast (t : ℝ) (ht0 : 0 < t) (a b c d : ℕ → ℚ)
    (ha : Summable (fun n : ℕ => ‖(a n : ℂ) * qterm (it t ht0) n‖))
    (hb : Summable (fun n : ℕ => ‖(b n : ℂ) * qterm (it t ht0) n‖))
    (hc : Summable (fun n : ℕ => ‖(c n : ℂ) * qterm (it t ht0) n‖))
    (hd : Summable (fun n : ℕ => ‖(d n : ℂ) * qterm (it t ht0) n‖)) :
    qseries (fun n : ℕ => (a n : ℂ)) (it t ht0) +
          qseries (fun n : ℕ => (b n : ℂ)) (it t ht0) +
          qseries (fun n : ℕ => (c n : ℂ)) (it t ht0) +
          qseries (fun n : ℕ => (d n : ℂ)) (it t ht0) =
        qseries (fun n : ℕ => ((a n + b n + c n + d n : ℚ) : ℂ)) (it t ht0) := by
  have hab :
      Summable (fun n : ℕ => ‖((a n + b n : ℚ) : ℂ) * qterm (it t ht0) n‖) := by
    have ha' : Summable (fun n : ℕ => (a n : ℂ) * qterm (it t ht0) n) := Summable.of_norm ha
    have hb' : Summable (fun n : ℕ => (b n : ℂ) * qterm (it t ht0) n) := Summable.of_norm hb
    have hab' :
        Summable (fun n : ℕ => ((a n + b n : ℚ) : ℂ) * qterm (it t ht0) n) := by
      refine (ha'.add hb').congr ?_
      intro n
      simp [Rat.cast_add, add_mul]
    exact hab'.norm
  have hcd :
      Summable (fun n : ℕ => ‖((c n + d n : ℚ) : ℂ) * qterm (it t ht0) n‖) := by
    have hc' : Summable (fun n : ℕ => (c n : ℂ) * qterm (it t ht0) n) := Summable.of_norm hc
    have hd' : Summable (fun n : ℕ => (d n : ℂ) * qterm (it t ht0) n) := Summable.of_norm hd
    have hcd' :
        Summable (fun n : ℕ => ((c n + d n : ℚ) : ℂ) * qterm (it t ht0) n) := by
      refine (hc'.add hd').congr ?_
      intro n
      simp [Rat.cast_add, add_mul]
    exact hcd'.norm
  calc
    qseries (fun n : ℕ => (a n : ℂ)) (it t ht0) +
          qseries (fun n : ℕ => (b n : ℂ)) (it t ht0) +
          qseries (fun n : ℕ => (c n : ℂ)) (it t ht0) +
          qseries (fun n : ℕ => (d n : ℂ)) (it t ht0)
        = (qseries (fun n : ℕ => (a n : ℂ)) (it t ht0) +
            qseries (fun n : ℕ => (b n : ℂ)) (it t ht0)) +
            (qseries (fun n : ℕ => (c n : ℂ)) (it t ht0) +
              qseries (fun n : ℕ => (d n : ℂ)) (it t ht0)) :=
            add_assoc (qseries (fun n => ↑(a n)) (it t ht0) + qseries (fun n => ↑(b n)) (it t ht0))
              (qseries (fun n => ↑(c n)) (it t ht0)) (qseries (fun n => ↑(d n)) (it t ht0))
    _ = qseries (fun n : ℕ => ((a n + b n : ℚ) : ℂ)) (it t ht0) +
          qseries (fun n : ℕ => ((c n + d n : ℚ) : ℂ)) (it t ht0) := by
          simp [qseries_add_cast (t := t) (ht0 := ht0) (a := a) (b := b) ha hb,
            qseries_add_cast (t := t) (ht0 := ht0) (a := c) (b := d) hc hd]
    _ = qseries (fun n : ℕ => (((a n + b n) + (c n + d n) : ℚ) : ℂ)) (it t ht0) :=
          qseries_add_cast t ht0 (fun n => a n + b n) (fun n => c n + d n) hab hcd
    _ = qseries (fun n : ℕ => ((a n + b n + c n + d n : ℚ) : ℂ)) (it t ht0) := by
          simp [add_left_comm, add_comm]


end SpherePacking.Dim24.AppendixA
