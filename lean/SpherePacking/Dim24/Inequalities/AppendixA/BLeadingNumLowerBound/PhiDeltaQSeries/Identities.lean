-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PhiDeltaQSeries.Basic
import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesMul
import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesSummable


/-!
### `Δ` and `φ₁/φ₂` numerators as `q`-series

Appendix A uses the Eisenstein expansion `Δ = (E₄^3 - E₆^2)/1728` and works at points `z = it t`
with `t ≥ 1`. This file records the corresponding `qseries` identities for `Δ`, `Δ^2`, and the
numerators `phi1_num` and `phi2_num`.
-/


open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.AppendixA


/-! ## Coefficient functions -/

/-- Rational coefficients of the Eisenstein expansion of `Δ`.

Defined by `coeffDelta n = (1/1728) * (coeffE4Cube n - coeffE6Sq n)`. -/
@[expose] public def coeffDelta : ℕ → ℚ :=
  fun n => (1 / 1728 : ℚ) * (coeffE4Cube n - coeffE6Sq n)

/-- Coefficients of `Δ^2` as a `q`-series, obtained as the Cauchy product of `coeffDelta`. -/
@[expose] public def coeffDeltaSq : ℕ → ℚ := fun n => conv coeffDelta coeffDelta n

private lemma summable_norm_qseries_coeffDelta (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    Summable (fun n : ℕ => ‖((coeffDelta n : ℂ) * qterm (it t ht0) n)‖) := by
  have hsE4Cube :
      Summable (fun n : ℕ => ‖((coeffE4Cube n : ℂ) * qterm (it t ht0) n)‖) := by
    simpa using! summable_norm_qseries_coeffE4Cube (t := t) (ht0 := ht0) (ht := ht)
  have hsE6Sq :
      Summable (fun n : ℕ => ‖((coeffE6Sq n : ℂ) * qterm (it t ht0) n)‖) := by
    simpa using! summable_norm_qseries_coeffE6Sq (t := t) (ht0 := ht0) (ht := ht)
  have hs1 :
      Summable (fun n : ℕ => ‖(((1 / 1728 : ℚ) * coeffE4Cube n : ℂ) * qterm (it t ht0) n)‖) := by
    have hs := hsE4Cube.mul_left ‖((1 / 1728 : ℚ) : ℂ)‖
    refine hs.congr ?_
    intro n
    simp [mul_assoc, Rat.cast_ofNat]
  have hs2 :
      Summable (fun n : ℕ => ‖(((-1 / 1728 : ℚ) * coeffE6Sq n : ℂ) * qterm (it t ht0) n)‖) := by
    have hs := hsE6Sq.mul_left ‖(((-1 / 1728 : ℚ)) : ℂ)‖
    refine hs.congr ?_
    intro n
    simp [mul_assoc, Rat.cast_neg, Rat.cast_ofNat]
  have hsum :
      ∀ n : ℕ,
        ‖((coeffDelta n : ℂ) * qterm (it t ht0) n)‖ ≤
          ‖(((1 / 1728 : ℚ) * coeffE4Cube n : ℂ) * qterm (it t ht0) n)‖ +
            ‖(((-1 / 1728 : ℚ) * coeffE6Sq n : ℂ) * qterm (it t ht0) n)‖ := by
    intro n
    have hcoeff :
        (coeffDelta n : ℂ) =
          ((1 / 1728 : ℚ) * coeffE4Cube n : ℂ) + ((-1 / 1728 : ℚ) * coeffE6Sq n : ℂ) := by
      -- Expand `coeffDelta n = (1/1728) * (coeffE4Cube n - coeffE6Sq n)`.
      have hcoeffQ :
          coeffDelta n =
            (1 / 1728 : ℚ) * coeffE4Cube n + (-1 / 1728 : ℚ) * coeffE6Sq n := by
        -- `c*(x - y) = c*x + (-c)*y`.
        -- Use `ring` to avoid simp-normalizing `1/1728` into `1728⁻¹`.
        have : (1 / 1728 : ℚ) * (coeffE4Cube n - coeffE6Sq n) =
            (1 / 1728 : ℚ) * coeffE4Cube n + (-1 / 1728 : ℚ) * coeffE6Sq n := by
          ring
        simpa [coeffDelta] using! this
      -- Cast the rational identity to `ℂ`.
      have := congrArg (fun q : ℚ => (q : ℂ)) hcoeffQ
      simpa [Rat.cast_add, Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat] using! this
    -- Apply the triangle inequality after rewriting the coefficient as a sum.
    have htri :
        ‖((((1 / 1728 : ℚ) * coeffE4Cube n : ℂ) + ((-1 / 1728 : ℚ) * coeffE6Sq n : ℂ)) *
              qterm (it t ht0) n)‖ ≤
          ‖(((1 / 1728 : ℚ) * coeffE4Cube n : ℂ) * qterm (it t ht0) n)‖ +
            ‖(((-1 / 1728 : ℚ) * coeffE6Sq n : ℂ) * qterm (it t ht0) n)‖ := by
      simpa [add_mul] using!
        (norm_add_le
          (((1 / 1728 : ℚ) * coeffE4Cube n : ℂ) * qterm (it t ht0) n)
          (((-1 / 1728 : ℚ) * coeffE6Sq n : ℂ) * qterm (it t ht0) n))
    -- Rewrite `coeffDelta` without triggering `simp` on norms.
    simpa [hcoeff] using! htri
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hsum (hs1.add hs2)

lemma Delta_it_eq_qseries (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    (Δ (it t ht0) : ℂ) = qseries (fun n : ℕ => (coeffDelta n : ℂ)) (it t ht0) := by
  have hΔ : (Δ (it t ht0) : ℂ) =
        (1 / 1728 : ℂ) * ((E₄ (it t ht0)) ^ (3 : ℕ) - (E₆ (it t ht0)) ^ (2 : ℕ)) := by
    simpa using! Delta_eq_eisenstein (z := it t ht0)
  have hE4Cube :
      (E₄ (it t ht0)) ^ (3 : ℕ) = qseries (fun n : ℕ => (coeffE4Cube n : ℂ)) (it t ht0) := by
    simpa using! (E₄_cube_it_eq_qseries (t := t) (ht0 := ht0) (ht := ht))
  have hE6Sq :
      (E₆ (it t ht0)) ^ (2 : ℕ) = qseries (fun n : ℕ => (coeffE6Sq n : ℂ)) (it t ht0) := by
    simpa using! (E₆_sq_it_eq_qseries (t := t) (ht0 := ht0) (ht := ht))
  have hsE4Cube :
      Summable (fun n : ℕ => ‖((coeffE4Cube n : ℂ) * qterm (it t ht0) n)‖) := by
    simpa using! summable_norm_qseries_coeffE4Cube (t := t) (ht0 := ht0) (ht := ht)
  have hsE6Sq :
      Summable (fun n : ℕ => ‖((coeffE6Sq n : ℂ) * qterm (it t ht0) n)‖) := by
    simpa using! summable_norm_qseries_coeffE6Sq (t := t) (ht0 := ht0) (ht := ht)
  have hs1 :
      Summable (fun n : ℕ => ‖((((1 / 1728 : ℚ) * coeffE4Cube n : ℂ) * qterm (it t ht0) n))‖) := by
    have hs := hsE4Cube.mul_left ‖((1 / 1728 : ℚ) : ℂ)‖
    refine hs.congr ?_
    intro n
    simp [mul_assoc, Rat.cast_ofNat]
  have hs2 :
      Summable (fun n : ℕ => ‖((((-1 / 1728 : ℚ) * coeffE6Sq n : ℂ) * qterm (it t ht0) n))‖) := by
    have hs := hsE6Sq.mul_left ‖(((-1 / 1728 : ℚ)) : ℂ)‖
    refine hs.congr ?_
    intro n
    simp [mul_assoc, Rat.cast_neg, Rat.cast_ofNat]
  have hadd :
      qseries (fun n : ℕ => (((1 / 1728 : ℚ) * coeffE4Cube n : ℚ) : ℂ)) (it t ht0) +
          qseries (fun n : ℕ => (((-1 / 1728 : ℚ) * coeffE6Sq n : ℚ) : ℂ)) (it t ht0) =
        qseries (fun n : ℕ =>
            (((((1 / 1728 : ℚ) * coeffE4Cube n) + ((-1 / 1728 : ℚ) * coeffE6Sq n) : ℚ)) : ℂ))
          (it t ht0) := by
    simpa using!
      (qseries_add_cast (t := t) (ht0 := ht0)
        (a := fun n => (1 / 1728 : ℚ) * coeffE4Cube n)
        (b := fun n => (-1 / 1728 : ℚ) * coeffE6Sq n)
        (ha := by simpa [mul_assoc] using! hs1)
        (hb := by simpa [mul_assoc] using! hs2))
  have hcoeff :
      (fun n : ℕ =>
          (((((1 / 1728 : ℚ) * coeffE4Cube n) + ((-1 / 1728 : ℚ) * coeffE6Sq n) : ℚ)) : ℂ)) =
        fun n : ℕ => (coeffDelta n : ℂ) := by
    funext n
    -- Work in `ℚ` first, then cast.
    have hcoeffQ :
        (1 / 1728 : ℚ) * coeffE4Cube n + (-1 / 1728 : ℚ) * coeffE6Sq n = coeffDelta n := by
      have : (1 / 1728 : ℚ) * (coeffE4Cube n - coeffE6Sq n) =
          (1 / 1728 : ℚ) * coeffE4Cube n + (-1 / 1728 : ℚ) * coeffE6Sq n := by
        ring
      -- Re-orient.
      simpa [coeffDelta] using! this.symm
    -- Cast the rational identity to `ℂ`.
    have := congrArg (fun q : ℚ => (q : ℂ)) hcoeffQ
    simpa [Rat.cast_add, Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat] using! this
  have hscale1 :
      ((1 / 1728 : ℂ) * qseries (fun n : ℕ => (coeffE4Cube n : ℂ)) (it t ht0)) =
        qseries (fun n : ℕ => (((1 / 1728 : ℚ) * coeffE4Cube n : ℚ) : ℂ)) (it t ht0) := by
    simpa using! (qseries_mul_qrat (t := t) (ht0 := ht0) (c := (1 / 1728 : ℚ)) (a := coeffE4Cube))
  have hscale2 :
      ((-1 / 1728 : ℂ) * qseries (fun n : ℕ => (coeffE6Sq n : ℂ)) (it t ht0)) =
        qseries (fun n : ℕ => (((-1 / 1728 : ℚ) * coeffE6Sq n : ℚ) : ℂ)) (it t ht0) := by
    simpa using! (qseries_mul_qrat (t := t) (ht0 := ht0) (c := (-1 / 1728 : ℚ)) (a := coeffE6Sq))
  grind only

/-- At `z = it t` (with `t ≥ 1`), the square `Δ(z)^2` equals the `q`-series with
coefficients `coeffDeltaSq`. -/
public lemma Delta_sq_it_eq_qseries (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    (Δ (it t ht0)) ^ (2 : ℕ) = qseries (fun n : ℕ => (coeffDeltaSq n : ℂ)) (it t ht0) := by
  have hΔ : (Δ (it t ht0) : ℂ) = qseries (fun n : ℕ => (coeffDelta n : ℂ)) (it t ht0) := by
    simpa using! Delta_it_eq_qseries (t := t) (ht0 := ht0) (ht := ht)
  have hsΔ :
      Summable (fun n : ℕ => ‖((coeffDelta n : ℂ) * qterm (it t ht0) n)‖) := by
    simpa using! summable_norm_qseries_coeffDelta (t := t) (ht0 := ht0) (ht := ht)
  have hmul :
      qseries (fun n : ℕ => (coeffDelta n : ℂ)) (it t ht0) *
          qseries (fun n : ℕ => (coeffDelta n : ℂ)) (it t ht0) =
        qseries (fun n : ℕ => (conv coeffDelta coeffDelta n : ℂ)) (it t ht0) := by
    simpa [coeffDeltaSq] using!
      (qseries_mul_cast (z := it t ht0) (a := coeffDelta) (b := coeffDelta) hsΔ hsΔ)
  simpa [pow_two, hΔ] using! hmul

lemma phi2_core_it_eq_qseries (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    ((-49 : ℂ) * (E₄ (it t ht0)) ^ (3 : ℕ) + (25 : ℂ) * (E₆ (it t ht0)) ^ (2 : ℕ)) =
      qseries (fun n : ℕ => (coeffPhi2Core n : ℂ)) (it t ht0) := by
  have hE4Cube :
      (E₄ (it t ht0)) ^ (3 : ℕ) = qseries (fun n : ℕ => (coeffE4Cube n : ℂ)) (it t ht0) := by
    simpa using! (E₄_cube_it_eq_qseries (t := t) (ht0 := ht0) (ht := ht))
  have hE6Sq :
      (E₆ (it t ht0)) ^ (2 : ℕ) = qseries (fun n : ℕ => (coeffE6Sq n : ℂ)) (it t ht0) := by
    simpa using! (E₆_sq_it_eq_qseries (t := t) (ht0 := ht0) (ht := ht))
  have hsE4Cube :
      Summable (fun n : ℕ => ‖(coeffE4Cube n : ℂ) * qterm (it t ht0) n‖) := by
    simpa using! summable_norm_qseries_coeffE4Cube (t := t) (ht0 := ht0) (ht := ht)
  have hsE6Sq :
      Summable (fun n : ℕ => ‖(coeffE6Sq n : ℂ) * qterm (it t ht0) n‖) := by
    simpa using! summable_norm_qseries_coeffE6Sq (t := t) (ht0 := ht0) (ht := ht)
  have hscale1 :
      (-49 : ℂ) * qseries (fun n : ℕ => (coeffE4Cube n : ℂ)) (it t ht0) =
        qseries (fun n : ℕ => ((-49 : ℚ) * coeffE4Cube n : ℂ)) (it t ht0) := by
    simpa [qseries, Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat, mul_assoc] using!
      (qseries_mul_qrat (t := t) (ht0 := ht0) (c := (-49 : ℚ)) (a := coeffE4Cube))
  have hscale2 :
      (25 : ℂ) * qseries (fun n : ℕ => (coeffE6Sq n : ℂ)) (it t ht0) =
        qseries (fun n : ℕ => ((25 : ℚ) * coeffE6Sq n : ℂ)) (it t ht0) := by
    simpa [qseries, Rat.cast_mul, Rat.cast_ofNat, mul_assoc] using!
      (qseries_mul_qrat (t := t) (ht0 := ht0) (c := (25 : ℚ)) (a := coeffE6Sq))
  have hs1 :
      Summable (fun n : ℕ => ‖((( (-49 : ℚ) * coeffE4Cube n : ℂ) * qterm (it t ht0) n))‖) := by
    have hs := hsE4Cube.mul_left ‖(-49 : ℂ)‖
    refine hs.congr ?_
    intro n
    -- `‖-49‖ * ‖a*q^n‖ = ‖(-49*a) * q^n‖`.
    simp [mul_assoc, Rat.cast_neg, Rat.cast_ofNat]
  have hs2 :
      Summable (fun n : ℕ => ‖((( (25 : ℚ) * coeffE6Sq n : ℂ) * qterm (it t ht0) n))‖) := by
    have hs := hsE6Sq.mul_left ‖(25 : ℂ)‖
    refine hs.congr ?_
    intro n
    simp [mul_assoc, Rat.cast_ofNat]
  have hadd :=
    (qseries_add_of_summable (z := it t ht0)
      (a := fun n : ℕ => ((-49 : ℚ) * coeffE4Cube n : ℂ))
      (b := fun n : ℕ => ((25 : ℚ) * coeffE6Sq n : ℂ))
      (ha := by simpa [mul_assoc] using! hs1)
      (hb := by simpa [mul_assoc] using! hs2))
  calc
    (-49 : ℂ) * (E₄ (it t ht0)) ^ (3 : ℕ) + (25 : ℂ) * (E₆ (it t ht0)) ^ (2 : ℕ)
        = (-49 : ℂ) * qseries (fun n : ℕ => (coeffE4Cube n : ℂ)) (it t ht0) +
            (25 : ℂ) * qseries (fun n : ℕ => (coeffE6Sq n : ℂ)) (it t ht0) := by
            rw [hE4Cube, hE6Sq]
    _ = qseries (fun n : ℕ => ((-49 : ℚ) * coeffE4Cube n : ℂ)) (it t ht0) +
          qseries (fun n : ℕ => ((25 : ℚ) * coeffE6Sq n : ℂ)) (it t ht0) := by
            simp [hscale1, hscale2]
    _ = qseries (fun n : ℕ => (coeffPhi2Core n : ℂ)) (it t ht0) := by
          simpa [coeffPhi2Core] using! hadd.symm

/-- `phi2_num` at `z = it t` as a scalar multiple of the `q`-series with coefficients
`coeffPhi2Core`. -/
public lemma phi2_num_it_eq_qseries (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    phi2_num (it t ht0) =
      (-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ)) *
        qseries (fun n : ℕ => (coeffPhi2Core n : ℂ)) (it t ht0) := by
  have hcore := phi2_core_it_eq_qseries (t := t) (ht0 := ht0) (ht := ht)
  unfold phi2_num
  rw [hcore]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

lemma phi1_core_it_eq_qseries (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    (48 : ℂ) * (E₆ (it t ht0)) * (E₄ (it t ht0)) ^ (2 : ℕ) +
        (2 : ℂ) * (E₂ (it t ht0)) *
          ((-49 : ℂ) * (E₄ (it t ht0)) ^ (3 : ℕ) + (25 : ℂ) * (E₆ (it t ht0)) ^ (2 : ℕ)) =
      qseries (fun n : ℕ => (coeffPhi1Core n : ℂ)) (it t ht0) := by
  set z : ℍ := it t ht0
  have hE2 : E₂ z = qseries (fun n : ℕ => (coeffE2 n : ℂ)) z := by
    simpa [z] using! (E₂_eq_qseries (z := z))
  have hE6 : E₆ z = qseries (fun n : ℕ => (coeffE6 n : ℂ)) z := by
    simpa [z] using! (E₆_eq_qseries (z := z))
  have hE4Sq : (E₄ z) ^ (2 : ℕ) = qseries (fun n : ℕ => (coeffE4Sq n : ℂ)) z := by
    simpa [coeffE4Sq, z] using! (E₄_sq_eq_qseries_conv (t := t) (ht0 := ht0) (ht := ht))
  have hPhi2Core :
      ((-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ)) =
        qseries (fun n : ℕ => (coeffPhi2Core n : ℂ)) z := by
    simpa [z] using! (phi2_core_it_eq_qseries (t := t) (ht0 := ht0) (ht := ht))
  -- Cauchy product for `E6 * E4^2`.
  have hsE6 : Summable (fun n : ℕ => ‖(coeffE6 n : ℂ) * qterm z n‖) := by
    simpa [z] using! summable_norm_qseries_coeffE6 (t := t) (ht0 := ht0) (ht := ht)
  have hsE4Sq : Summable (fun n : ℕ => ‖(coeffE4Sq n : ℂ) * qterm z n‖) := by
    simpa [z] using! summable_norm_qseries_coeffE4Sq (t := t) (ht0 := ht0) (ht := ht)
  have hmulE6E4Sq :
      (E₆ z) * (E₄ z) ^ (2 : ℕ) = qseries (fun n : ℕ => (conv coeffE6 coeffE4Sq n : ℂ)) z := by
    have hmul :
        qseries (fun n : ℕ => (coeffE6 n : ℂ)) z *
            qseries (fun n : ℕ => (coeffE4Sq n : ℂ)) z =
          qseries (fun n : ℕ => (conv coeffE6 coeffE4Sq n : ℂ)) z := by
      simpa using! (qseries_mul_cast (z := z) (a := coeffE6) (b := coeffE4Sq) hsE6 hsE4Sq)
    rw [hE6, hE4Sq]
    exact hmul
  -- Cauchy product for `E2 * Phi2Core`.
  have hsE2 : Summable (fun n : ℕ => ‖(coeffE2 n : ℂ) * qterm z n‖) := by
    simpa [z] using! summable_norm_qseries_coeffE2 (t := t) (ht0 := ht0) (ht := ht)
  have hsPhi2 :
      Summable (fun n : ℕ => ‖(coeffPhi2Core n : ℂ) * qterm z n‖) := by
    simpa [z] using! summable_norm_qseries_coeffPhi2Core (t := t) (ht0 := ht0) (ht := ht)
  have hmulE2Phi2 :
      (E₂ z) * ((-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ)) =
        qseries (fun n : ℕ => (conv coeffE2 coeffPhi2Core n : ℂ)) z := by
    have hmul :
        qseries (fun n : ℕ => (coeffE2 n : ℂ)) z *
            qseries (fun n : ℕ => (coeffPhi2Core n : ℂ)) z =
          qseries (fun n : ℕ => (conv coeffE2 coeffPhi2Core n : ℂ)) z := by
      simpa using! (qseries_mul_cast (z := z) (a := coeffE2) (b := coeffPhi2Core) hsE2 hsPhi2)
    rw [hE2, hPhi2Core]
    exact hmul
  -- Now scale both products by rationals.
  have hscale1 :
      (48 : ℂ) * qseries (fun n : ℕ => (conv coeffE6 coeffE4Sq n : ℂ)) (it t ht0) =
        qseries (fun n : ℕ => ((48 : ℚ) * conv coeffE6 coeffE4Sq n : ℂ)) (it t ht0) := by
    simpa [qseries, Rat.cast_mul, Rat.cast_ofNat, mul_assoc] using!
      qseries_mul_qrat
        (t := t) (ht0 := ht0) (c := (48 : ℚ)) (a := fun n => conv coeffE6 coeffE4Sq n)
  have hscale2 :
      (2 : ℂ) * qseries (fun n : ℕ => (conv coeffE2 coeffPhi2Core n : ℂ)) (it t ht0) =
        qseries (fun n : ℕ => ((2 : ℚ) * conv coeffE2 coeffPhi2Core n : ℂ)) (it t ht0) := by
    simpa [qseries, Rat.cast_mul, Rat.cast_ofNat, mul_assoc] using!
      qseries_mul_qrat
        (t := t) (ht0 := ht0) (c := (2 : ℚ)) (a := fun n => conv coeffE2 coeffPhi2Core n)
  have hsConv1 :
      Summable (fun n : ℕ => ‖((conv coeffE6 coeffE4Sq n : ℂ) * qterm z n)‖) := by
    have habs : ∀ n : ℕ,
        |(conv coeffE6 coeffE4Sq n : ℝ)| ≤
          ((504 : ℝ) * (240 * 240 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (6 + (4 + 4 + 1) + 1)) :=
      abs_conv_coeffE6_coeffE4Sq_le
    exact summable_norm_qseries_of_coeffBound t ht0 ht (conv coeffE6 coeffE4Sq) (504 * (240 * 240))
      (6 + (4 + 4 + 1) + 1) habs
  have hsConv2 :
      Summable (fun n : ℕ => ‖((conv coeffE2 coeffPhi2Core n : ℂ) * qterm z n)‖) :=
    summable_norm_qseries_conv_coeffE2_coeffPhi2Core (t := t) (ht0 := ht0) (ht := ht)
  have hs1 :
      Summable (fun n : ℕ => ‖(((48 : ℚ) * conv coeffE6 coeffE4Sq n : ℂ) * qterm z n)‖) := by
    have hs := hsConv1.mul_left ‖(48 : ℂ)‖
    refine hs.congr ?_
    intro n
    simp [mul_assoc, Rat.cast_ofNat]
  have hs2 :
      Summable (fun n : ℕ => ‖(((2 : ℚ) * conv coeffE2 coeffPhi2Core n : ℂ) * qterm z n)‖) := by
    have hs := hsConv2.mul_left ‖(2 : ℂ)‖
    refine hs.congr ?_
    intro n
    simp [mul_assoc, Rat.cast_ofNat]
  have hadd :=
    (qseries_add_of_summable (z := z)
      (a := fun n : ℕ => ((48 : ℚ) * conv coeffE6 coeffE4Sq n : ℂ))
      (b := fun n : ℕ => ((2 : ℚ) * conv coeffE2 coeffPhi2Core n : ℂ))
      (ha := by simpa [mul_assoc] using! hs1)
      (hb := by simpa [mul_assoc] using! hs2))
  -- Assemble.
  calc
    (48 : ℂ) * (E₆ z) * (E₄ z) ^ (2 : ℕ) +
        (2 : ℂ) * (E₂ z) * ((-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ))
        = (48 : ℂ) * (E₆ z * (E₄ z) ^ (2 : ℕ)) +
            (2 : ℂ) * (E₂ z * ((-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ))) := by
            ring_nf
    _ = (48 : ℂ) * qseries (fun n : ℕ => (conv coeffE6 coeffE4Sq n : ℂ)) z +
            (2 : ℂ) * qseries (fun n : ℕ => (conv coeffE2 coeffPhi2Core n : ℂ)) z := by
          rw [hmulE6E4Sq, hmulE2Phi2]
    _ = qseries (fun n : ℕ => ((48 : ℚ) * conv coeffE6 coeffE4Sq n : ℂ)) z +
            qseries (fun n : ℕ => ((2 : ℚ) * conv coeffE2 coeffPhi2Core n : ℂ)) z := by
          lia
    _ = qseries (fun n : ℕ => (coeffPhi1Core n : ℂ)) z := by
          simpa [coeffPhi1Core] using! hadd.symm
    _ = qseries (fun n : ℕ => (coeffPhi1Core n : ℂ)) (it t ht0) := by simp [z]

/-- `phi1_num` at `z = it t` as a scalar multiple of the `q`-series with coefficients
`coeffPhi1Core`. -/
public lemma phi1_num_it_eq_qseries (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    phi1_num (it t ht0) =
      ((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
        qseries (fun n : ℕ => (coeffPhi1Core n : ℂ)) (it t ht0) := by
  have hcore := phi1_core_it_eq_qseries (t := t) (ht0 := ht0) (ht := ht)
  -- Multiply the core identity by the scalar `((1/π)*(-6))`.
  have h :=
    congrArg (fun w : ℂ => ((1 / (Real.pi : ℂ)) * (-6 : ℂ)) * w) hcore
  simpa [phi1_num, mul_assoc, mul_left_comm, mul_comm] using! h


end SpherePacking.Dim24.AppendixA
