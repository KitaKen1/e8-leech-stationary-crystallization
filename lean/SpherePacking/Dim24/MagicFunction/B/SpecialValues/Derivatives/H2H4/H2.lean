-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.Theta2Trunc


/-!
# Cusp expansion for `H₂`

This file proves the `qHalf`-expansion estimate for `H₂ = Θ₂^4` used in the cusp-coefficient
computation for `ψI`.

## Main statements
* `tendsto_qHalf_sq_atImInfty`
* `tendsto_H₂_div_qHalf_sub_const_div_qHalf_sq`
-/


open scoped Real
open scoped Topology
open scoped UpperHalfPlane

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesAux

section EvenU

open Filter UpperHalfPlane

namespace Deriv

/-- As `Im z → ∞`, the parameter `qHalf(z)^2` tends to `0`. -/
public lemma tendsto_qHalf_sq_atImInfty :
    Tendsto (fun z : ℍ => (qHalf z) ^ (2 : ℕ)) atImInfty (𝓝 (0 : ℂ)) := by
  simpa using! (tendsto_qHalf_atImInfty.pow 2)

lemma tendsto_t_err :
    Tendsto
        (fun z : ℍ =>
          (Θ₂ z / qQuarter z - ((2 : ℂ) + (2 : ℂ) * (qHalf z) ^ (2 : ℕ))) / (qHalf z) ^ (2 : ℕ))
        atImInfty (𝓝 (0 : ℂ)) := by
  -- Divide the `Θ₂` truncation lemma by `qQuarter`.
  have h0 := tendsto_Θ₂_sub_trunc_div_qQuarter_mul_q
  refine h0.congr' ?_
  refine Filter.Eventually.of_forall ?_
  intro z
  have hq0 : qQuarter z ≠ 0 := qQuarter_ne_zero z
  have hq2 : (qHalf z) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 (qHalf_ne_zero z)
  field_simp [hq0, hq2]
  -- `field_simp` already clears denominators and closes this goal.

lemma tendsto_t_atImInfty :
    Tendsto (fun z : ℍ => Θ₂ z / qQuarter z) atImInfty (𝓝 (2 : ℂ)) := by
  -- `t = (2 + 2 q) + q * ((t - (2 + 2 q))/q)` with `q = qHalf^2`.
  have hEq :
      (fun z : ℍ => Θ₂ z / qQuarter z) =
        fun z : ℍ =>
          (2 : ℂ) + (2 : ℂ) * (qHalf z) ^ (2 : ℕ) +
            (qHalf z) ^ (2 : ℕ) *
              ((Θ₂ z / qQuarter z - ((2 : ℂ) + (2 : ℂ) * (qHalf z) ^ (2 : ℕ))) /
                (qHalf z) ^ (2 : ℕ)) := by
    funext z
    have hq0 : qHalf z ≠ 0 := qHalf_ne_zero z
    have hq2z : (qHalf z) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hq0
    field_simp [hq0, hq2z]
    ring_nf
  have h2 : Tendsto (fun _ : ℍ => (2 : ℂ)) atImInfty (𝓝 (2 : ℂ)) := tendsto_const_nhds
  have h2mul : Tendsto (fun z : ℍ => (2 : ℂ) * (qHalf z) ^ (2 : ℕ)) atImInfty (𝓝 (0 : ℂ)) :=
    by
      simpa [mul_zero] using!
        ( (tendsto_const_nhds : Tendsto (fun _ : ℍ => (2 : ℂ)) atImInfty (𝓝 (2 : ℂ))).mul
          tendsto_qHalf_sq_atImInfty )
  have hrest :
      Tendsto
          (fun z : ℍ =>
            (qHalf z) ^ (2 : ℕ) *
              ((Θ₂ z / qQuarter z - ((2 : ℂ) + (2 : ℂ) * (qHalf z) ^ (2 : ℕ))) /
                (qHalf z) ^ (2 : ℕ)))
          atImInfty (𝓝 (0 : ℂ)) := by
    simpa [mul_zero] using! (tendsto_qHalf_sq_atImInfty.mul tendsto_t_err)
  have :
      Tendsto
          (fun z : ℍ =>
            (2 : ℂ) + (2 : ℂ) * (qHalf z) ^ (2 : ℕ) +
              (qHalf z) ^ (2 : ℕ) *
                ((Θ₂ z / qQuarter z - ((2 : ℂ) + (2 : ℂ) * (qHalf z) ^ (2 : ℕ))) /
                  (qHalf z) ^ (2 : ℕ)))
          atImInfty (𝓝 ((2 : ℂ) + 0 + 0)) :=
    (h2.add h2mul).add hrest
  simpa [hEq, add_assoc] using! this

lemma tendsto_t4_sub_trunc_div_qHalf_sq :
    Tendsto
        (fun z : ℍ =>
          (((Θ₂ z / qQuarter z) ^ (4 : ℕ) - ((2 : ℂ) + (2 : ℂ) * (qHalf z) ^ (2 : ℕ)) ^ (4 : ℕ)) /
            (qHalf z) ^ (2 : ℕ)))
        atImInfty (𝓝 (0 : ℂ)) := by
  -- `a^4 - b^4 = (a-b) * (a^3 + a^2 b + a b^2 + b^3)`.
  let t : ℍ → ℂ := fun z : ℍ => Θ₂ z / qQuarter z
  let b : ℍ → ℂ := fun z : ℍ => (2 : ℂ) + (2 : ℂ) * (qHalf z) ^ (2 : ℕ)
  have hfac :
      ∀ z : ℍ,
        (t z) ^ (4 : ℕ) - (b z) ^ (4 : ℕ) =
          (t z - b z) *
            ((t z) ^ (3 : ℕ) +
              (t z) ^ (2 : ℕ) * (b z) +
              (t z) * (b z) ^ (2 : ℕ) +
              (b z) ^ (3 : ℕ)) := by
    intro z
    ring
  have ht : Tendsto t atImInfty (𝓝 (2 : ℂ)) := by
    simpa [t] using! tendsto_t_atImInfty
  have hb : Tendsto b atImInfty (𝓝 (2 : ℂ)) := by
    have : Tendsto (fun z : ℍ => (2 : ℂ) * (qHalf z) ^ (2 : ℕ)) atImInfty (𝓝 (0 : ℂ)) :=
      by
        simpa [mul_zero] using!
          ((tendsto_const_nhds : Tendsto (fun _ : ℍ => (2 : ℂ)) atImInfty (𝓝 (2 : ℂ))).mul
            tendsto_qHalf_sq_atImInfty)
    simpa [b] using! (tendsto_const_nhds.add this)
  have hsum :
      Tendsto
          (fun z : ℍ =>
            (t z) ^ (3 : ℕ) + (t z) ^ (2 : ℕ) * (b z) + t z * (b z) ^ (2 : ℕ) + (b z) ^ (3 : ℕ))
          atImInfty
          (𝓝
            ((2 : ℂ) ^ (3 : ℕ) + (2 : ℂ) ^ (2 : ℕ) * (2 : ℂ) + (2 : ℂ) * (2 : ℂ) ^ (2 : ℕ) +
              (2 : ℂ) ^ (3 : ℕ))) := by
    have h1 : Tendsto (fun z : ℍ => (t z) ^ (3 : ℕ)) atImInfty (𝓝 ((2 : ℂ) ^ (3 : ℕ))) := ht.pow 3
    have h2 :
        Tendsto (fun z : ℍ => (t z) ^ (2 : ℕ) * (b z))
          atImInfty (𝓝 (((2 : ℂ) ^ (2 : ℕ)) * (2 : ℂ))) :=
      (ht.pow 2).mul hb
    have h3 :
        Tendsto (fun z : ℍ => t z * (b z) ^ (2 : ℕ))
          atImInfty (𝓝 ((2 : ℂ) * ((2 : ℂ) ^ (2 : ℕ)))) :=
      ht.mul (hb.pow 2)
    have h4 : Tendsto (fun z : ℍ => (b z) ^ (3 : ℕ)) atImInfty (𝓝 ((2 : ℂ) ^ (3 : ℕ))) := hb.pow 3
    have := (h1.add h2).add (h3.add h4)
    simpa [add_assoc, add_left_comm, add_comm] using! this
  have hsum' :
      Tendsto
        (fun z : ℍ =>
          (t z) ^ (3 : ℕ) + (t z) ^ (2 : ℕ) * (b z) + t z * (b z) ^ (2 : ℕ) + (b z) ^ (3 : ℕ))
        atImInfty (𝓝 (32 : ℂ)) := by
    -- The limit is `4 * 2^3 = 32`.
    convert (postTransparency := .instances) hsum using 1
    norm_num
  have hEq :
      (fun z : ℍ =>
          ((t z) ^ (4 : ℕ) - (b z) ^ (4 : ℕ)) / (qHalf z) ^ (2 : ℕ)) =
        fun z : ℍ =>
          ((t z - b z) / (qHalf z) ^ (2 : ℕ)) *
            ((t z) ^ (3 : ℕ) +
              (t z) ^ (2 : ℕ) * (b z) +
              t z * (b z) ^ (2 : ℕ) +
              (b z) ^ (3 : ℕ)) := by
    funext z
    have hq2z : (qHalf z) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 (qHalf_ne_zero z)
    field_simp [hq2z, hfac z]
    ring
  have hmain :
      Tendsto (fun z : ℍ =>
          ((t z - b z) / (qHalf z) ^ (2 : ℕ)) *
            ((t z) ^ (3 : ℕ) +
              (t z) ^ (2 : ℕ) * (b z) +
              t z * (b z) ^ (2 : ℕ) +
              (b z) ^ (3 : ℕ)))
        atImInfty (𝓝 ((0 : ℂ) * (32 : ℂ))) := by
    have ht0 :
        Tendsto (fun z : ℍ => (t z - b z) / (qHalf z) ^ (2 : ℕ)) atImInfty (𝓝 (0 : ℂ)) := by
      -- `t - b` is exactly the error term from `tendsto_t_err`.
      simpa [t, b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using! tendsto_t_err
    simpa [mul_zero] using! (ht0.mul hsum')
  lia

lemma tendsto_poly4_trunc :
    Tendsto
        (fun z : ℍ =>
          (((2 : ℂ) + (2 : ℂ) * (qHalf z) ^ (2 : ℕ)) ^ (4 : ℕ) -
              ((16 : ℂ) + (64 : ℂ) * (qHalf z) ^ (2 : ℕ))) /
            (qHalf z) ^ (2 : ℕ))
        atImInfty (𝓝 (0 : ℂ)) := by
  -- Expand and observe that only terms of order `qHalf^2` and higher remain after cancellation.
  have hEq :
      ∀ z : ℍ,
        (((2 : ℂ) + (2 : ℂ) * (qHalf z) ^ (2 : ℕ)) ^ (4 : ℕ) -
              ((16 : ℂ) + (64 : ℂ) * (qHalf z) ^ (2 : ℕ))) /
            (qHalf z) ^ (2 : ℕ) =
          (96 : ℂ) * (qHalf z) ^ (2 : ℕ) +
            (64 : ℂ) * (qHalf z) ^ (4 : ℕ) +
            (16 : ℂ) * (qHalf z) ^ (6 : ℕ) := by
    intro z
    have hq0 : qHalf z ≠ 0 := qHalf_ne_zero z
    have hq2z : (qHalf z) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hq0
    field_simp [hq2z]
    ring_nf
  have hq4 : Tendsto (fun z : ℍ => (qHalf z) ^ (4 : ℕ)) atImInfty (𝓝 (0 : ℂ)) := by
    simpa using! (tendsto_qHalf_atImInfty.pow 4)
  have hq6 : Tendsto (fun z : ℍ => (qHalf z) ^ (6 : ℕ)) atImInfty (𝓝 (0 : ℂ)) := by
    simpa using! (tendsto_qHalf_atImInfty.pow 6)
  have h1 :
      Tendsto (fun z : ℍ => (96 : ℂ) * (qHalf z) ^ (2 : ℕ)) atImInfty (𝓝 (0 : ℂ)) := by
    simpa [mul_zero] using!
      ((tendsto_const_nhds : Tendsto (fun _ : ℍ => (96 : ℂ)) atImInfty (𝓝 (96 : ℂ))).mul
        tendsto_qHalf_sq_atImInfty)
  have h2 :
      Tendsto (fun z : ℍ => (64 : ℂ) * (qHalf z) ^ (4 : ℕ)) atImInfty (𝓝 (0 : ℂ)) := by
    simpa [mul_zero] using!
      ((tendsto_const_nhds : Tendsto (fun _ : ℍ => (64 : ℂ)) atImInfty (𝓝 (64 : ℂ))).mul hq4)
  have h3 :
      Tendsto (fun z : ℍ => (16 : ℂ) * (qHalf z) ^ (6 : ℕ)) atImInfty (𝓝 (0 : ℂ)) := by
    simpa [mul_zero] using!
      ((tendsto_const_nhds : Tendsto (fun _ : ℍ => (16 : ℂ)) atImInfty (𝓝 (16 : ℂ))).mul hq6)
  have :
      Tendsto
        (fun z : ℍ =>
          (96 : ℂ) * (qHalf z) ^ (2 : ℕ) + (64 : ℂ) * (qHalf z) ^ (4 : ℕ) +
            (16 : ℂ) * (qHalf z) ^ (6 : ℕ))
        atImInfty (𝓝 (0 : ℂ)) := by
    simpa [add_assoc] using! (h1.add (h2.add h3))
  refine this.congr' ?_
  exact Filter.Eventually.of_forall (by intro z; simp [hEq z, add_assoc])

/-- As `Im z → ∞`, the normalized error `(H₂ z / qHalf z - 16) / qHalf(z)^2` tends to `64`. -/
public lemma tendsto_H₂_div_qHalf_sub_const_div_qHalf_sq :
    Tendsto (fun z : ℍ => (H₂ z / qHalf z - (16 : ℂ)) / (qHalf z) ^ (2 : ℕ))
      atImInfty (𝓝 (64 : ℂ)) := by
  -- Let `t = Θ₂ / qQuarter`, so `H₂ / qHalf = t^4`.
  have hq : ∀ z : ℍ, (qQuarter z) ^ (4 : ℕ) = qHalf z := qQuarter_pow_four
  let t : ℍ → ℂ := fun z : ℍ => Θ₂ z / qQuarter z
  have ht4 :
      Tendsto
        (fun z : ℍ =>
          ((t z) ^ (4 : ℕ) - ((2 : ℂ) + (2 : ℂ) * (qHalf z) ^ (2 : ℕ)) ^ (4 : ℕ)) /
            (qHalf z) ^ (2 : ℕ))
        atImInfty (𝓝 (0 : ℂ)) := by
    simpa [t] using! tendsto_t4_sub_trunc_div_qHalf_sq
  -- The polynomial truncation gives the `b^4` contribution.
  have hb4 :
      Tendsto
          (fun z : ℍ =>
            (((2 : ℂ) + (2 : ℂ) * (qHalf z) ^ (2 : ℕ)) ^ (4 : ℕ) - (16 : ℂ)) /
              (qHalf z) ^ (2 : ℕ))
          atImInfty (𝓝 (64 : ℂ)) := by
    have htrunc := tendsto_poly4_trunc
    have hEq :
        (fun z : ℍ =>
            (((2 : ℂ) + (2 : ℂ) * (qHalf z) ^ (2 : ℕ)) ^ (4 : ℕ) - (16 : ℂ)) /
              (qHalf z) ^ (2 : ℕ)) =
          fun z : ℍ =>
            (64 : ℂ) +
              (((2 : ℂ) + (2 : ℂ) * (qHalf z) ^ (2 : ℕ)) ^ (4 : ℕ) -
                  ((16 : ℂ) + (64 : ℂ) * (qHalf z) ^ (2 : ℕ))) /
                (qHalf z) ^ (2 : ℕ) := by
      funext z
      have hq2z : (qHalf z) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 (qHalf_ne_zero z)
      -- Expand `b^4 - 16 = (b^4 - (16 + 64 q^2)) + 64 q^2` and divide by `q^2`.
      grind only
    have : Tendsto (fun z : ℍ =>
        (64 : ℂ) +
          (((2 : ℂ) + (2 : ℂ) * (qHalf z) ^ (2 : ℕ)) ^ (4 : ℕ) -
                ((16 : ℂ) + (64 : ℂ) * (qHalf z) ^ (2 : ℕ))) /
            (qHalf z) ^ (2 : ℕ)) atImInfty (𝓝 ((64 : ℂ) + 0)) :=
      tendsto_const_nhds.add htrunc
    simpa [hEq] using! this
  have hmain :
      Tendsto (fun z : ℍ => ((t z) ^ (4 : ℕ) - (16 : ℂ)) / (qHalf z) ^ (2 : ℕ))
        atImInfty (𝓝 (64 : ℂ)) := by
    have hEq :
        (fun z : ℍ => ((t z) ^ (4 : ℕ) - (16 : ℂ)) / (qHalf z) ^ (2 : ℕ)) =
          fun z : ℍ =>
            ((t z) ^ (4 : ℕ) - ((2 : ℂ) + (2 : ℂ) * (qHalf z) ^ (2 : ℕ)) ^ (4 : ℕ)) /
                (qHalf z) ^ (2 : ℕ) +
              (((2 : ℂ) + (2 : ℂ) * (qHalf z) ^ (2 : ℕ)) ^ (4 : ℕ) - (16 : ℂ)) /
                (qHalf z) ^ (2 : ℕ) := by
      funext z
      ring
    have : Tendsto
        (fun z : ℍ =>
            ((t z) ^ (4 : ℕ) - ((2 : ℂ) + (2 : ℂ) * (qHalf z) ^ (2 : ℕ)) ^ (4 : ℕ)) /
                  (qHalf z) ^ (2 : ℕ) +
                (((2 : ℂ) + (2 : ℂ) * (qHalf z) ^ (2 : ℕ)) ^ (4 : ℕ) - (16 : ℂ)) /
                  (qHalf z) ^ (2 : ℕ))
        atImInfty (𝓝 (0 + 64 : ℂ)) := ht4.add hb4
    simpa [hEq] using! this
  -- Finally, rewrite `(t^4 - 16) / q^2` as `(H₂ / qHalf - 16) / q^2`.
  have hEqH2 : (fun z : ℍ => H₂ z / qHalf z) = fun z : ℍ => (t z) ^ (4 : ℕ) := by
    funext z
    -- `H₂ = Θ₂^4`, and `t^4 = (Θ₂^4) / (qQuarter^4)`, with `qQuarter^4 = qHalf`.
    simp [H₂, t, div_pow, hq z]
  have hEqH2pt : ∀ z : ℍ, (t z) ^ (4 : ℕ) = H₂ z / qHalf z := by
    intro z
    simpa using! congrArg (fun f : ℍ → ℂ => f z) hEqH2.symm
  have hmain' :
      Tendsto (fun z : ℍ => (H₂ z / qHalf z - (16 : ℂ)) / (qHalf z) ^ (2 : ℕ))
        atImInfty (𝓝 (64 : ℂ)) := by
    refine hmain.congr' (Filter.Eventually.of_forall ?_)
    intro z
    simp [hEqH2pt z]
  simpa using! hmain'

end SpecialValuesAux.EvenU.Deriv
end

end SpherePacking.Dim24
