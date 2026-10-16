-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.Theta2Trunc


/-!
# Cusp expansion for `H₄`

This file proves the `qHalf`-expansion estimates for `H₄ = Θ₄^4` used in the cusp-coefficient
computation for `ψI`.

## Main statements
* `tendsto_H₄_sub_trunc_div_qHalf_sq`
* `tendsto_H₄_sub_one_div_qHalf`
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

/-- The difference between `H₄` and its quadratic truncation is `o(qHalf^2)` at the cusp. -/
public lemma tendsto_H₄_sub_trunc_div_qHalf_sq :
    Tendsto
        (fun z : ℍ =>
          (H₄ z -
              ((1 : ℂ) - (8 : ℂ) * qHalf z + (24 : ℂ) * (qHalf z) ^ (2 : ℕ))) /
            (qHalf z) ^ (2 : ℕ))
        atImInfty (𝓝 (0 : ℂ)) := by
  -- Lift the `Θ₄` truncation to `H₄ = Θ₄^4`.
  let a : ℍ → ℂ := fun z : ℍ => Θ₄ z
  let b : ℍ → ℂ := fun z : ℍ => (1 : ℂ) - (2 : ℂ) * qHalf z
  have hb4 :
      ∀ z : ℍ,
        (b z) ^ (4 : ℕ) =
          ((1 : ℂ) - (8 : ℂ) * qHalf z + (24 : ℂ) * (qHalf z) ^ (2 : ℕ)) +
            (qHalf z) ^ (3 : ℕ) * (-(32 : ℂ) + (16 : ℂ) * qHalf z) := by
    intro z
    ring
  have hΘ4err : Tendsto (fun z : ℍ => (a z - b z) / (qHalf z) ^ (2 : ℕ)) atImInfty (𝓝 (0 : ℂ)) := by
    simpa [a, b, sub_eq_add_neg, add_left_comm, add_comm] using!
      tendsto_Θ₄_sub_trunc_div_qHalf_sq
  have ha : Tendsto a atImInfty (𝓝 (1 : ℂ)) := by
    simpa [a] using! (Θ₄_tendsto_atImInfty : Tendsto Θ₄ atImInfty (𝓝 (1 : ℂ)))
  have hb : Tendsto b atImInfty (𝓝 (1 : ℂ)) := by
    have : Tendsto (fun z : ℍ => (2 : ℂ) * qHalf z) atImInfty (𝓝 (0 : ℂ)) := by
      simpa using! (tendsto_const_nhds.mul tendsto_qHalf_atImInfty)
    have :
        Tendsto (fun z : ℍ => (1 : ℂ) - (2 : ℂ) * qHalf z) atImInfty (𝓝 ((1 : ℂ) - 0)) :=
      tendsto_const_nhds.sub this
    simpa [b] using! this
  have hfac :
      ∀ z : ℍ,
        (a z) ^ (4 : ℕ) - (b z) ^ (4 : ℕ) =
          (a z - b z) *
            ((a z) ^ (3 : ℕ) + (a z) ^ (2 : ℕ) * (b z) + (a z) * (b z) ^ (2 : ℕ) +
              (b z) ^ (3 : ℕ)) := by
    intro z
    ring
  have hsum :
      Tendsto
          (fun z : ℍ =>
            ((a z) ^ (3 : ℕ) + (a z) ^ (2 : ℕ) * (b z) + (a z) * (b z) ^ (2 : ℕ) +
              (b z) ^ (3 : ℕ)))
          atImInfty (𝓝 (4 : ℂ)) := by
    have ha2 := ha.pow 2
    have ha3 := ha.pow 3
    have hb2 := hb.pow 2
    have hb3 := hb.pow 3
    have h1 : Tendsto (fun z : ℍ => (a z) ^ (3 : ℕ)) atImInfty (𝓝 (1 : ℂ)) := by
      simpa using! ha3
    have h2 :
        Tendsto (fun z : ℍ => (a z) ^ (2 : ℕ) * (b z)) atImInfty (𝓝 (1 : ℂ)) := by
      simpa using! ha2.mul hb
    have h3 :
        Tendsto (fun z : ℍ => (a z) * (b z) ^ (2 : ℕ)) atImInfty (𝓝 (1 : ℂ)) := by
      simpa using! ha.mul hb2
    have h4 : Tendsto (fun z : ℍ => (b z) ^ (3 : ℕ)) atImInfty (𝓝 (1 : ℂ)) := by
      simpa using! hb3
    have hsum' := (h1.add h2).add (h3.add h4)
    have hsum'' :
        Tendsto
            (fun z : ℍ =>
              (a z) ^ (3 : ℕ) + (a z) ^ (2 : ℕ) * (b z) + (a z) * (b z) ^ (2 : ℕ) +
                (b z) ^ (3 : ℕ))
          atImInfty (𝓝 ((1 : ℂ) + (1 : ℂ) + ((1 : ℂ) + (1 : ℂ)))) := by
      simpa [add_assoc] using! hsum'
    -- `1 + 1 + 1 + 1 = 4`.
    convert (postTransparency := .instances) hsum'' using 1
    norm_num
  have hmain :
      Tendsto (fun z : ℍ => ((a z) ^ (4 : ℕ) - (b z) ^ (4 : ℕ)) / (qHalf z) ^ (2 : ℕ)) atImInfty
        (𝓝 (0 : ℂ)) := by
    have hEq :
        (fun z : ℍ => ((a z) ^ (4 : ℕ) - (b z) ^ (4 : ℕ)) / (qHalf z) ^ (2 : ℕ)) =
          fun z : ℍ =>
            ((a z - b z) / (qHalf z) ^ (2 : ℕ)) *
              ((a z) ^ (3 : ℕ) + (a z) ^ (2 : ℕ) * (b z) + a z * (b z) ^ (2 : ℕ) +
                (b z) ^ (3 : ℕ)) := by
      funext z
      ring
    have : Tendsto (fun z : ℍ =>
        ((a z - b z) / (qHalf z) ^ (2 : ℕ)) *
          ((a z) ^ (3 : ℕ) + (a z) ^ (2 : ℕ) * (b z) + a z * (b z) ^ (2 : ℕ) +
            (b z) ^ (3 : ℕ)))
        atImInfty (𝓝 ((0 : ℂ) * (4 : ℂ))) := (hΘ4err.mul hsum)
    simpa [hEq] using! this
  -- `H₄ - trunc = (a^4 - b^4) + (b^4 - trunc)`.
  -- The second term is `o(q^2)` since it is `O(q^3)`.
  let trunc : ℍ → ℂ := fun z : ℍ => (1 : ℂ) - (8 : ℂ) * qHalf z + (24 : ℂ) * (qHalf z) ^ (2 : ℕ)
  have hb_trunc :
      Tendsto (fun z : ℍ => ((b z) ^ (4 : ℕ) - trunc z) / (qHalf z) ^ (2 : ℕ)) atImInfty
        (𝓝 (0 : ℂ)) := by
    have hEq :
        (fun z : ℍ => ((b z) ^ (4 : ℕ) - trunc z) / (qHalf z) ^ (2 : ℕ)) =
          fun z : ℍ => qHalf z * (-(32 : ℂ) + (16 : ℂ) * qHalf z) := by
      grind only
    have hlin :
        Tendsto (fun z : ℍ => (-(32 : ℂ) + (16 : ℂ) * qHalf z)) atImInfty (𝓝 (-(32 : ℂ) + 0)) := by
      simpa using!
        tendsto_const_nhds.add
          ((tendsto_const_nhds : Tendsto (fun _ : ℍ => (16 : ℂ)) atImInfty (𝓝 (16 : ℂ))).mul
            tendsto_qHalf_atImInfty)
    have :
        Tendsto
            (fun z : ℍ => qHalf z * (-(32 : ℂ) + (16 : ℂ) * qHalf z))
            atImInfty (𝓝 ((0 : ℂ) * (-(32 : ℂ) + 0))) :=
      tendsto_qHalf_atImInfty.mul hlin
    simpa [hEq, mul_zero] using! this
  have hEqMain :
      (fun z : ℍ => (H₄ z - trunc z) / (qHalf z) ^ (2 : ℕ)) =
        fun z : ℍ =>
          ((a z) ^ (4 : ℕ) - (b z) ^ (4 : ℕ)) / (qHalf z) ^ (2 : ℕ) +
            ((b z) ^ (4 : ℕ) - trunc z) / (qHalf z) ^ (2 : ℕ) := by
    funext z
    -- This is the identity `(H₄ - trunc) = (H₄ - b^4) + (b^4 - trunc)` multiplied by `(qHalf z)⁻²`.
    -- No nonvanishing hypotheses are needed.
    simp [a, H₄, trunc, div_eq_mul_inv, sub_eq_add_neg, add_left_comm, add_comm, mul_comm]
    ring_nf
  have :
      Tendsto
          (fun z : ℍ =>
            ((a z) ^ (4 : ℕ) - (b z) ^ (4 : ℕ)) / (qHalf z) ^ (2 : ℕ) +
              ((b z) ^ (4 : ℕ) - trunc z) / (qHalf z) ^ (2 : ℕ))
          atImInfty (𝓝 ((0 : ℂ) + 0)) := hmain.add hb_trunc
  simpa [hEqMain, trunc] using! this

/-- As `Im z → ∞`, the normalized error `(H₄ z - 1) / qHalf z` tends to `-8`. -/
public lemma tendsto_H₄_sub_one_div_qHalf :
    Tendsto (fun z : ℍ => (H₄ z - (1 : ℂ)) / qHalf z) atImInfty (𝓝 (-8 : ℂ)) := by
  have h0 := tendsto_H₄_sub_trunc_div_qHalf_sq
  have hEq :
      (fun z : ℍ => (H₄ z - (1 : ℂ)) / qHalf z) =
        fun z : ℍ =>
          (-8 : ℂ) +
            (qHalf z) *
              ((24 : ℂ) +
                (H₄ z -
                    ((1 : ℂ) - (8 : ℂ) * qHalf z + (24 : ℂ) * (qHalf z) ^ (2 : ℕ))) /
                  (qHalf z) ^ (2 : ℕ)) := by
    funext z
    have hq0 : qHalf z ≠ 0 := qHalf_ne_zero z
    have hq2z : (qHalf z) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hq0
    field_simp [hq0, hq2z]
    ring
  have hinner :
      Tendsto
          (fun z : ℍ =>
            (24 : ℂ) +
              (H₄ z -
                  ((1 : ℂ) - (8 : ℂ) * qHalf z + (24 : ℂ) * (qHalf z) ^ (2 : ℕ))) /
                (qHalf z) ^ (2 : ℕ))
          atImInfty (𝓝 ((24 : ℂ) + 0)) := tendsto_const_nhds.add h0
  have hrest :
      Tendsto
          (fun z : ℍ =>
            (qHalf z) *
              ((24 : ℂ) +
                (H₄ z -
                    ((1 : ℂ) - (8 : ℂ) * qHalf z + (24 : ℂ) * (qHalf z) ^ (2 : ℕ))) /
                  (qHalf z) ^ (2 : ℕ)))
          atImInfty (𝓝 (0 : ℂ)) := by
    simpa [mul_zero] using! (tendsto_qHalf_atImInfty.mul hinner)
  have :
      Tendsto
          (fun z : ℍ =>
            (-8 : ℂ) +
              (qHalf z) *
                ((24 : ℂ) +
                  (H₄ z -
                      ((1 : ℂ) - (8 : ℂ) * qHalf z + (24 : ℂ) * (qHalf z) ^ (2 : ℕ))) /
                    (qHalf z) ^ (2 : ℕ)))
          atImInfty (𝓝 ((-8 : ℂ) + 0)) := tendsto_const_nhds.add hrest
  simpa [hEq] using! this

end SpecialValuesAux.EvenU.Deriv
end

end SpherePacking.Dim24
