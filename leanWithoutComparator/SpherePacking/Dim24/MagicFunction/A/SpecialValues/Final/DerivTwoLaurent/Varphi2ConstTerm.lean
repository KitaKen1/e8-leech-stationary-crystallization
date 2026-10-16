-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import
  SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.Varphi2ConstCoeff
import SpherePacking.ModularForms.DimensionFormulas

/-!
# Second coefficient for `Δ / q` at `i∞`

This file packages algebraic rewrites for `E₄` and `E₆` and proves the limit statement for the
second `q`-coefficient of `Δ / q` (after subtracting the `q^{-1}` coefficient). This input is used
when computing the constant term of `varphi₂`.

## Main statements
* `tendsto_Delta_div_q_sub_one_div_q_coeff_two`
-/

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesVarphi₁Limits

open scoped Real Topology
open Filter Complex UpperHalfPlane

def A4 (z : ℍ) : ℂ := (E₄ z - (1 : ℂ)) / q (z : ℂ)
def B4 (z : ℍ) : ℂ := (A4 z - (240 : ℂ)) / q (z : ℂ)
def C4 (z : ℍ) : ℂ := (B4 z - (2160 : ℂ)) / q (z : ℂ)

def A6 (z : ℍ) : ℂ := (E₆ z - (1 : ℂ)) / q (z : ℂ)
def B6 (z : ℍ) : ℂ := (A6 z - (-(504 : ℂ))) / q (z : ℂ)
def C6 (z : ℍ) : ℂ := (B6 z - (-(16632 : ℂ))) / q (z : ℂ)

lemma sub_add_mul_div (X c y : ℂ) (hy : y ≠ 0) : X = c + y * ((X - c) / y) := by
  grind only

lemma A4_eq (z : ℍ) : E₄ z = (1 : ℂ) + q (z : ℂ) * A4 z := by
  have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
  simpa [A4, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using!
    (sub_add_mul_div (X := E₄ z) (c := (1 : ℂ)) (y := q (z : ℂ)) hzq)

lemma A6_eq (z : ℍ) : E₆ z = (1 : ℂ) + q (z : ℂ) * A6 z := by
  have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
  simpa [A6, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using!
    (sub_add_mul_div (X := E₆ z) (c := (1 : ℂ)) (y := q (z : ℂ)) hzq)

lemma B4_eq (z : ℍ) : A4 z = (240 : ℂ) + q (z : ℂ) * B4 z := by
  have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
  simpa [B4, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using!
    (sub_add_mul_div (X := A4 z) (c := (240 : ℂ)) (y := q (z : ℂ)) hzq)

lemma C4_eq (z : ℍ) : B4 z = (2160 : ℂ) + q (z : ℂ) * C4 z := by
  have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
  simpa [C4, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using!
    (sub_add_mul_div (X := B4 z) (c := (2160 : ℂ)) (y := q (z : ℂ)) hzq)

lemma B6_eq (z : ℍ) : A6 z = (-(504 : ℂ)) + q (z : ℂ) * B6 z := by
  have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
  simpa [B6, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using!
    (sub_add_mul_div (X := A6 z) (c := (-(504 : ℂ))) (y := q (z : ℂ)) hzq)

lemma C6_eq (z : ℍ) : B6 z = (-(16632 : ℂ)) + q (z : ℂ) * C6 z := by
  have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
  simpa [C6, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc] using!
    (sub_add_mul_div (X := B6 z) (c := (-(16632 : ℂ))) (y := q (z : ℂ)) hzq)

lemma tendsto_A4 : Tendsto A4 atImInfty (𝓝 (240 : ℂ)) := by
  simpa [A4] using!
    (tendsto_E₄_sub_one_div_q :
      Tendsto (fun z : ℍ => (E₄ z - (1 : ℂ)) / q (z : ℂ)) atImInfty (𝓝 (240 : ℂ)))

lemma tendsto_B4 : Tendsto B4 atImInfty (𝓝 (2160 : ℂ)) := by
  simpa [B4, A4] using! (tendsto_E₄_coeff_two :
    Tendsto (fun z : ℍ => ((E₄ z - (1 : ℂ)) / q (z : ℂ) - (240 : ℂ)) / q (z : ℂ)) atImInfty
      (𝓝 (2160 : ℂ)))

lemma tendsto_C4 : Tendsto C4 atImInfty (𝓝 (6720 : ℂ)) := by
  simpa [C4, B4, A4] using! (tendsto_E₄_coeff_three :
    Tendsto (fun z : ℍ =>
      ((((E₄ z - (1 : ℂ)) / q (z : ℂ) - (240 : ℂ)) / q (z : ℂ)) - (2160 : ℂ)) / q (z : ℂ))
      atImInfty (𝓝 (6720 : ℂ)))

lemma tendsto_A6 : Tendsto A6 atImInfty (𝓝 (-(504 : ℂ))) := by
  simpa [A6] using! (tendsto_E₆_sub_one_div_q :
    Tendsto (fun z : ℍ => (E₆ z - (1 : ℂ)) / q (z : ℂ)) atImInfty (𝓝 (-(504 : ℂ))))

lemma tendsto_B6 : Tendsto B6 atImInfty (𝓝 (-(16632 : ℂ))) := by
  change
      Tendsto
          (fun z : ℍ => ((E₆ z - (1 : ℂ)) / q (z : ℂ) - (-(504 : ℂ))) / q (z : ℂ))
          atImInfty (𝓝 (-(16632 : ℂ)))
  exact tendsto_E₆_coeff_two

lemma tendsto_C6 : Tendsto C6 atImInfty (𝓝 (-(122976 : ℂ))) := by
  change
      Tendsto
          (fun z : ℍ =>
            ((((E₆ z - (1 : ℂ)) / q (z : ℂ) - (-(504 : ℂ))) / q (z : ℂ)) - (-(16632 : ℂ))) /
              q (z : ℂ))
          atImInfty (𝓝 (-(122976 : ℂ)))
  exact tendsto_E₆_coeff_three

lemma Delta_div_q_eq (z : ℍ) :
    (Δ z : ℂ) / q (z : ℂ) =
      (1 / 1728 : ℂ) *
        ((3 : ℂ) * A4 z - (2 : ℂ) * A6 z
          + (q (z : ℂ)) * ((3 : ℂ) * (A4 z) ^ (2 : ℕ) - (A6 z) ^ (2 : ℕ))
          + (q (z : ℂ)) ^ (2 : ℕ) * (A4 z) ^ (3 : ℕ)) := by
  have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
  have hΔ : (Δ z : ℂ) = (1 / 1728 : ℂ) * ((E₄ z) ^ (3 : ℕ) - (E₆ z) ^ (2 : ℕ)) := by
    simpa [Delta_apply] using!
      (Delta_apply_eq_one_div_1728_mul_E4_pow_three_sub_E6_sq (z := z))
  have hE4 : (E₄ z : ℂ) = (1 : ℂ) + q (z : ℂ) * A4 z := A4_eq z
  have hE6 : (E₆ z : ℂ) = (1 : ℂ) + q (z : ℂ) * A6 z := A6_eq z
  -- Reduce to a pure algebra identity.
  grind only

/-- Second `q`-coefficient for `Δ / q` after subtracting the principal part `-24/q`. -/
public lemma tendsto_Delta_div_q_sub_one_div_q_coeff_two :
    Tendsto
      (fun z : ℍ =>
        (((((Δ z : ℂ) / q (z : ℂ)) - (1 : ℂ)) / q (z : ℂ)) - (-(24 : ℂ))) / q (z : ℂ))
      atImInfty (𝓝 (252 : ℂ)) := by
  -- Use the exact algebraic expansion from `Delta_div_q_eq` and plug in the coefficient limits.
  have hq : Tendsto (fun z : ℍ => q (z : ℂ)) atImInfty (𝓝 (0 : ℂ)) := tendsto_q_atImInfty
  have hA4 : Tendsto A4 atImInfty (𝓝 (240 : ℂ)) := tendsto_A4
  have hB4 : Tendsto B4 atImInfty (𝓝 (2160 : ℂ)) := tendsto_B4
  have hC4 : Tendsto C4 atImInfty (𝓝 (6720 : ℂ)) := tendsto_C4
  have hA6 : Tendsto A6 atImInfty (𝓝 (-(504 : ℂ))) := tendsto_A6
  have hB6 : Tendsto B6 atImInfty (𝓝 (-(16632 : ℂ))) := tendsto_B6
  have hC6 : Tendsto C6 atImInfty (𝓝 (-(122976 : ℂ))) := tendsto_C6
  -- Rewrite everything in terms of `A4,B4,C4,A6,B6,C6`.
  -- The final formula for the second coefficient is:
  --   (1/1728) * ((3*C4 - 2*C6) + (1440*B4 + 1008*B6) + q*(3*B4^2 - B6^2) + A4^3)
  -- and we evaluate the limit term-by-term.
  have hEq : ∀ z : ℍ,
      (((((Δ z : ℂ) / q (z : ℂ)) - (1 : ℂ)) / q (z : ℂ)) - (-(24 : ℂ))) / q (z : ℂ) =
        (1 / 1728 : ℂ) *
          ((3 : ℂ) * C4 z - (2 : ℂ) * C6 z +
            (1440 : ℂ) * B4 z + (1008 : ℂ) * B6 z +
            (q (z : ℂ)) * ((3 : ℂ) * (B4 z) ^ (2 : ℕ) - (B6 z) ^ (2 : ℕ)) +
            (A4 z) ^ (3 : ℕ)) := by
    intro z
    have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
    -- Expand `Δ/q` using `Delta_div_q_eq`, and then use the identities relating `A4,A6` to `B4,B6`
    -- and `B4,B6` to `C4,C6`.
    -- Everything is an identity in `ℂ`, so `field_simp`+`ring_nf` works well.
    have hΔ := Delta_div_q_eq (z := z)
    have hA4' : A4 z = (240 : ℂ) + q (z : ℂ) * B4 z := B4_eq z
    have hA6' : A6 z = (-(504 : ℂ)) + q (z : ℂ) * B6 z := B6_eq z
    have hB4' : B4 z = (2160 : ℂ) + q (z : ℂ) * C4 z := C4_eq z
    have hB6' : B6 z = (-(16632 : ℂ)) + q (z : ℂ) * C6 z := C6_eq z
    -- Now normalize.
    -- `simp` can be expensive here; we rely on `field_simp` and `ring_nf`.
    -- The constants `-24` and `252` are hard-coded by the coefficient computation.
    -- First eliminate `Δ/q` using the exact expansion `hΔ`.
    grind only
  have hlim :
      Tendsto
          (fun z : ℍ =>
            (1 / 1728 : ℂ) *
              ((3 : ℂ) * C4 z - (2 : ℂ) * C6 z +
                (1440 : ℂ) * B4 z + (1008 : ℂ) * B6 z +
                (q (z : ℂ)) * ((3 : ℂ) * (B4 z) ^ (2 : ℕ) - (B6 z) ^ (2 : ℕ)) +
                (A4 z) ^ (3 : ℕ)))
          atImInfty (𝓝 (252 : ℂ)) := by
    -- Compute the limit of each component.
    have hCpart :
        Tendsto (fun z : ℍ => (3 : ℂ) * C4 z - (2 : ℂ) * C6 z) atImInfty
          (𝓝 ((3 : ℂ) * (6720 : ℂ) - (2 : ℂ) * (-(122976 : ℂ)))) :=
      (tendsto_const_nhds.mul hC4).sub (tendsto_const_nhds.mul hC6)
    have hBpart :
        Tendsto (fun z : ℍ => (1440 : ℂ) * B4 z + (1008 : ℂ) * B6 z) atImInfty
          (𝓝 ((1440 : ℂ) * (2160 : ℂ) + (1008 : ℂ) * (-(16632 : ℂ)))) :=
      (tendsto_const_nhds.mul hB4).add (tendsto_const_nhds.mul hB6)
    have hqpart :
        Tendsto
            (fun z : ℍ => (q (z : ℂ)) * ((3 : ℂ) * (B4 z) ^ (2 : ℕ) - (B6 z) ^ (2 : ℕ)))
            atImInfty
              (𝓝
                ((0 : ℂ) * ((3 : ℂ) * (2160 : ℂ) ^ (2 : ℕ) - (-(16632 : ℂ)) ^ (2 : ℕ)))) := by
      have hinner :
          Tendsto (fun z : ℍ => (3 : ℂ) * (B4 z) ^ (2 : ℕ) - (B6 z) ^ (2 : ℕ)) atImInfty
            (𝓝 ((3 : ℂ) * (2160 : ℂ) ^ (2 : ℕ) - (-(16632 : ℂ)) ^ (2 : ℕ))) :=
        (tendsto_const_nhds.mul (hB4.pow 2)).sub (hB6.pow 2)
      exact hq.mul hinner
    have hA4pow :
        Tendsto (fun z : ℍ => (A4 z) ^ (3 : ℕ)) atImInfty (𝓝 ((240 : ℂ) ^ (3 : ℕ))) :=
      hA4.pow 3
    have hsum0 :
        Tendsto
            (fun z : ℍ =>
              ((3 : ℂ) * C4 z - (2 : ℂ) * C6 z +
                ((1440 : ℂ) * B4 z + (1008 : ℂ) * B6 z) +
                (q (z : ℂ)) * ((3 : ℂ) * (B4 z) ^ (2 : ℕ) - (B6 z) ^ (2 : ℕ)) +
                (A4 z) ^ (3 : ℕ)))
            atImInfty
            (𝓝
              (((3 : ℂ) * (6720 : ℂ) - (2 : ℂ) * (-(122976 : ℂ))) +
                ((1440 : ℂ) * (2160 : ℂ) + (1008 : ℂ) * (-(16632 : ℂ))) +
                ((0 : ℂ) * ((3 : ℂ) * (2160 : ℂ) ^ (2 : ℕ) - (-(16632 : ℂ)) ^ (2 : ℕ))) +
                ((240 : ℂ) ^ (3 : ℕ)))) :=
      ((hCpart.add hBpart).add hqpart).add hA4pow
    -- Re-associate the sums to match the ungrouped expression used in the statement.
    have hsum :
        Tendsto
            (fun z : ℍ =>
              ((3 : ℂ) * C4 z - (2 : ℂ) * C6 z +
                (1440 : ℂ) * B4 z + (1008 : ℂ) * B6 z +
                (q (z : ℂ)) * ((3 : ℂ) * (B4 z) ^ (2 : ℕ) - (B6 z) ^ (2 : ℕ)) +
                (A4 z) ^ (3 : ℕ)))
            atImInfty
            (𝓝
              (((3 : ℂ) * (6720 : ℂ) - (2 : ℂ) * (-(122976 : ℂ))) +
                ((1440 : ℂ) * (2160 : ℂ) + (1008 : ℂ) * (-(16632 : ℂ))) +
                ((0 : ℂ) * ((3 : ℂ) * (2160 : ℂ) ^ (2 : ℕ) - (-(16632 : ℂ)) ^ (2 : ℕ))) +
                ((240 : ℂ) ^ (3 : ℕ)))) := by
      refine Tendsto.congr' (Filter.Eventually.of_forall ?_) hsum0
      intro z
      ring_nf
    have hsum' :
        Tendsto
            (fun z : ℍ =>
              ((3 : ℂ) * C4 z - (2 : ℂ) * C6 z +
                (1440 : ℂ) * B4 z + (1008 : ℂ) * B6 z +
                (q (z : ℂ)) * ((3 : ℂ) * (B4 z) ^ (2 : ℕ) - (B6 z) ^ (2 : ℕ)) +
                (A4 z) ^ (3 : ℕ)))
            atImInfty (𝓝 (435456 : ℂ)) := by
      have hsum'' :
          Tendsto
              (fun z : ℍ =>
                ((3 : ℂ) * C4 z - (2 : ℂ) * C6 z +
                  (1440 : ℂ) * B4 z + (1008 : ℂ) * B6 z +
                  (q (z : ℂ)) * ((3 : ℂ) * (B4 z) ^ (2 : ℕ) - (B6 z) ^ (2 : ℕ)) +
                  (A4 z) ^ (3 : ℕ)))
              atImInfty
              (𝓝
                ((3 : ℂ) * (6720 : ℂ) + (2 : ℂ) * (122976 : ℂ) +
                  ((1440 : ℂ) * (2160 : ℂ) + -((1008 : ℂ) * (16632 : ℂ))) +
                  ((240 : ℂ) ^ (3 : ℕ)))) := by
        simpa using! hsum
      have hconst :
          ((3 : ℂ) * (6720 : ℂ) + (2 : ℂ) * (122976 : ℂ) +
              ((1440 : ℂ) * (2160 : ℂ) + -((1008 : ℂ) * (16632 : ℂ))) +
              ((240 : ℂ) ^ (3 : ℕ))) =
            (435456 : ℂ) := by
        norm_num
      simpa [hconst] using! hsum''
    have hmul :
        Tendsto
            (fun z : ℍ =>
              (1 / 1728 : ℂ) *
                ((3 : ℂ) * C4 z - (2 : ℂ) * C6 z +
                  (1440 : ℂ) * B4 z + (1008 : ℂ) * B6 z +
                  (q (z : ℂ)) * ((3 : ℂ) * (B4 z) ^ (2 : ℕ) - (B6 z) ^ (2 : ℕ)) +
                  (A4 z) ^ (3 : ℕ)))
            atImInfty (𝓝 ((1 / 1728 : ℂ) * (435456 : ℂ))) :=
      tendsto_const_nhds.mul hsum'
    have hmul' :
        Tendsto
            (fun z : ℍ =>
              (1 / 1728 : ℂ) *
                ((3 : ℂ) * C4 z - (2 : ℂ) * C6 z +
                  (1440 : ℂ) * B4 z + (1008 : ℂ) * B6 z +
                  (q (z : ℂ)) * ((3 : ℂ) * (B4 z) ^ (2 : ℕ) - (B6 z) ^ (2 : ℕ)) +
                  (A4 z) ^ (3 : ℕ)))
            atImInfty (𝓝 (((1728 : ℂ)⁻¹) * (435456 : ℂ))) := by
      simpa [one_div] using! hmul
    have : ((1728 : ℂ)⁻¹) * (435456 : ℂ) = (252 : ℂ) := by norm_num
    simpa [this] using! hmul'
  refine Tendsto.congr' (Filter.Eventually.of_forall (fun z => (hEq z).symm)) hlim

end SpecialValuesVarphi₁Limits

end

end SpherePacking.Dim24
