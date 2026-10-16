-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import
  SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.Varphi2ConstTerm
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Varphi2

/-!
# Constant term of `varphi₂` at `i∞`

The file `SpherePacking/Dim24/MagicFunction/A/SpecialValues/Varphi2.lean` proves the `q^{-2}` and
`q^{-1}` principal parts of `varphi₂`. Here we compute the next coefficient, giving the constant
term after subtracting these principal parts. This is the input used in the periodic
exponential-decay argument in `AvaluesRemainderLargeBound`.

## Main statements
* `tendsto_varphi₂_sub_c864_div_q_sq_sub_l_div_q`
-/

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesVarphi₂Limits

open scoped Real Topology
open Filter Complex UpperHalfPlane

open SpecialValuesVarphi₁Limits

def A4 (z : ℍ) : ℂ := (E₄ z - (1 : ℂ)) / q (z : ℂ)
def B4 (z : ℍ) : ℂ := ((E₄ z - (1 : ℂ)) / q (z : ℂ) - (240 : ℂ)) / q (z : ℂ)

def A6 (z : ℍ) : ℂ := (E₆ z - (1 : ℂ)) / q (z : ℂ)
def B6 (z : ℍ) : ℂ := ((E₆ z - (1 : ℂ)) / q (z : ℂ) + (504 : ℂ)) / q (z : ℂ)

def Cfun (z : ℍ) : ℂ :=
  (-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ)

def Zfun (z : ℍ) : ℂ := (q (z : ℂ) / Δ z) ^ (2 : ℕ)

def C1 (z : ℍ) : ℂ := (Cfun z + (24 : ℂ)) / q (z : ℂ)
def C2 (z : ℍ) : ℂ := (C1 z - (-(60480 : ℂ))) / q (z : ℂ)

def Z1 (z : ℍ) : ℂ := (Zfun z - (1 : ℂ)) / q (z : ℂ)
def Z2 (z : ℍ) : ℂ := (Z1 z - (48 : ℂ)) / q (z : ℂ)

lemma C1_coeff2_eq (z : ℍ) :
    C2 z =
      (50 : ℂ) * B6 z - (147 : ℂ) * B4 z +
        ((25 : ℂ) * (A6 z) ^ (2 : ℕ) - (147 : ℂ) * (A4 z) ^ (2 : ℕ)) +
        q (z : ℂ) * ((-49 : ℂ) * (A4 z) ^ (3 : ℕ)) := by
  have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
  have hA4 : E₄ z = (1 : ℂ) + q (z : ℂ) * A4 z := by
    dsimp [A4]
    field_simp [hzq]
    ring
  have hA6 : E₆ z = (1 : ℂ) + q (z : ℂ) * A6 z := by
    dsimp [A6]
    field_simp [hzq]
    ring
  -- Expand `Cfun` using `E₄ = 1 + q*A4` and `E₆ = 1 + q*A6`, then isolate the second coefficient.
  dsimp [C2, C1, Cfun, B4, B6, A4, A6]
  -- Clear the denominators coming from `/ q`.
  field_simp [hzq, pow_two, pow_three]
  ring_nf

lemma tendsto_C_sub_const_div_q_coeff_two :
    Tendsto (fun z : ℍ => C2 z) atImInfty (𝓝 (-(3265920 : ℂ))) := by
  have hq : Tendsto (fun z : ℍ => q (z : ℂ)) atImInfty (𝓝 (0 : ℂ)) := tendsto_q_atImInfty
  have hA4 : Tendsto A4 atImInfty (𝓝 (240 : ℂ)) := by
    simpa [A4] using!
      (tendsto_E₄_sub_one_div_q :
        Tendsto (fun z : ℍ => (E₄ z - (1 : ℂ)) / q (z : ℂ)) atImInfty (𝓝 (240 : ℂ)))
  have hA6 : Tendsto A6 atImInfty (𝓝 (-(504 : ℂ))) := by
    simpa [A6] using!
      (tendsto_E₆_sub_one_div_q :
        Tendsto (fun z : ℍ => (E₆ z - (1 : ℂ)) / q (z : ℂ)) atImInfty (𝓝 (-(504 : ℂ))))
  have hB4 : Tendsto B4 atImInfty (𝓝 (2160 : ℂ)) := by
    simpa [B4] using! (SpecialValuesVarphi₁Limits.tendsto_E₄_coeff_two :
      Tendsto (fun z : ℍ => ((E₄ z - (1 : ℂ)) / q (z : ℂ) - (240 : ℂ)) / q (z : ℂ)) atImInfty _)
  have hB6 : Tendsto B6 atImInfty (𝓝 (-(16632 : ℂ))) := by
    simpa [B6] using! (SpecialValuesVarphi₁Limits.tendsto_E₆_coeff_two :
      Tendsto (fun z : ℍ => ((E₆ z - (1 : ℂ)) / q (z : ℂ) - (-(504 : ℂ))) / q (z : ℂ)) atImInfty _)
  have hlim0 :
      Tendsto
          (fun z : ℍ =>
            (50 : ℂ) * B6 z - (147 : ℂ) * B4 z +
              ((25 : ℂ) * (A6 z) ^ (2 : ℕ) - (147 : ℂ) * (A4 z) ^ (2 : ℕ)) +
              q (z : ℂ) * ((-49 : ℂ) * (A4 z) ^ (3 : ℕ)))
          atImInfty
          (𝓝
            ((50 : ℂ) * (-(16632 : ℂ)) - (147 : ℂ) * (2160 : ℂ) +
              ((25 : ℂ) * ((-(504 : ℂ)) ^ (2 : ℕ)) - (147 : ℂ) * ((240 : ℂ) ^ (2 : ℕ))) +
              (0 : ℂ) * ((-49 : ℂ) * ((240 : ℂ) ^ (3 : ℕ))))) := by
    have h1 : Tendsto (fun z : ℍ => (50 : ℂ) * B6 z - (147 : ℂ) * B4 z) atImInfty
        (𝓝 ((50 : ℂ) * (-(16632 : ℂ)) - (147 : ℂ) * (2160 : ℂ))) :=
      (tendsto_const_nhds.mul hB6).sub (tendsto_const_nhds.mul hB4)
    have h2 :
        Tendsto
            (fun z : ℍ => (25 : ℂ) * (A6 z) ^ (2 : ℕ) - (147 : ℂ) * (A4 z) ^ (2 : ℕ))
            atImInfty
              (𝓝 ((25 : ℂ) * ((-(504 : ℂ)) ^ (2 : ℕ)) - (147 : ℂ) * ((240 : ℂ) ^ (2 : ℕ)))) :=
      (tendsto_const_nhds.mul (hA6.pow 2)).sub (tendsto_const_nhds.mul (hA4.pow 2))
    have h3 : Tendsto (fun z : ℍ => q (z : ℂ) * ((-49 : ℂ) * (A4 z) ^ (3 : ℕ))) atImInfty
        (𝓝 ((0 : ℂ) * ((-49 : ℂ) * ((240 : ℂ) ^ (3 : ℕ))))) :=
      hq.mul (tendsto_const_nhds.mul (hA4.pow 3))
    exact (h1.add h2).add h3
  have hlim0' :
      Tendsto (fun z : ℍ =>
        (50 : ℂ) * B6 z - (147 : ℂ) * B4 z +
          ((25 : ℂ) * (A6 z) ^ (2 : ℕ) - (147 : ℂ) * (A4 z) ^ (2 : ℕ)) +
          q (z : ℂ) * ((-49 : ℂ) * (A4 z) ^ (3 : ℕ)))
      atImInfty (𝓝 (-(50 : ℂ) * (16632 : ℂ) - (147 : ℂ) * (2160 : ℂ) +
        ((25 : ℂ) * ((504 : ℂ) ^ (2 : ℕ)) - (147 : ℂ) * ((240 : ℂ) ^ (2 : ℕ))))) := by
    -- Normalize the target constant.
    simp_all
  have hlim :
      Tendsto (fun z : ℍ =>
        (50 : ℂ) * B6 z - (147 : ℂ) * B4 z +
          ((25 : ℂ) * (A6 z) ^ (2 : ℕ) - (147 : ℂ) * (A4 z) ^ (2 : ℕ)) +
          q (z : ℂ) * ((-49 : ℂ) * (A4 z) ^ (3 : ℕ)))
      atImInfty (𝓝 (-(3265920 : ℂ))) := by
    -- Normalize the limit constant by computation.
    convert (postTransparency := .instances) hlim0' using 1
    norm_num
  refine Tendsto.congr' (Filter.Eventually.of_forall (fun z => by simp [C1_coeff2_eq])) hlim

lemma C1_eq_expansion (z : ℍ) :
    C1 z =
      (50 : ℂ) * (A6 z) - (147 : ℂ) * (A4 z) +
        q (z : ℂ) * ((25 : ℂ) * (A6 z) ^ (2 : ℕ) - (147 : ℂ) * (A4 z) ^ (2 : ℕ)) +
        (q (z : ℂ)) ^ (2 : ℕ) * ((-49 : ℂ) * (A4 z) ^ (3 : ℕ)) := by
  have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
  dsimp [C1, Cfun, A4, A6]
  field_simp [hzq, pow_two, pow_three]
  ring_nf

lemma tendsto_C_sub_const_div_q' :
    Tendsto (fun z : ℍ => C1 z) atImInfty (𝓝 (-(60480 : ℂ))) := by
  have hq : Tendsto (fun z : ℍ => q (z : ℂ)) atImInfty (𝓝 (0 : ℂ)) := tendsto_q_atImInfty
  have hq2 : Tendsto (fun z : ℍ => (q (z : ℂ)) ^ (2 : ℕ)) atImInfty (𝓝 ((0 : ℂ) ^ (2 : ℕ))) :=
    hq.pow 2
  have hA4 : Tendsto A4 atImInfty (𝓝 (240 : ℂ)) := by
    simpa [A4] using!
      (tendsto_E₄_sub_one_div_q :
        Tendsto (fun z : ℍ => (E₄ z - (1 : ℂ)) / q (z : ℂ)) atImInfty (𝓝 (240 : ℂ)))
  have hA6 : Tendsto A6 atImInfty (𝓝 (-(504 : ℂ))) := by
    simpa [A6] using!
      (tendsto_E₆_sub_one_div_q :
        Tendsto (fun z : ℍ => (E₆ z - (1 : ℂ)) / q (z : ℂ)) atImInfty (𝓝 (-(504 : ℂ))))
  have hlim0 :
      Tendsto
          (fun z : ℍ =>
            (50 : ℂ) * (A6 z) - (147 : ℂ) * (A4 z) +
              q (z : ℂ) * ((25 : ℂ) * (A6 z) ^ (2 : ℕ) - (147 : ℂ) * (A4 z) ^ (2 : ℕ)) +
              (q (z : ℂ)) ^ (2 : ℕ) * ((-49 : ℂ) * (A4 z) ^ (3 : ℕ)))
          atImInfty
          (𝓝
            ((50 : ℂ) * (-(504 : ℂ)) - (147 : ℂ) * (240 : ℂ) +
              (0 : ℂ) * ((25 : ℂ) * ((-(504 : ℂ)) ^ (2 : ℕ)) - (147 : ℂ) * ((240 : ℂ) ^ (2 : ℕ))) +
              ((0 : ℂ) ^ (2 : ℕ)) * ((-49 : ℂ) * ((240 : ℂ) ^ (3 : ℕ))))) := by
    have h1 :
        Tendsto (fun z : ℍ => (50 : ℂ) * (A6 z) - (147 : ℂ) * (A4 z)) atImInfty
          (𝓝 ((50 : ℂ) * (-(504 : ℂ)) - (147 : ℂ) * (240 : ℂ))) :=
      (tendsto_const_nhds.mul hA6).sub (tendsto_const_nhds.mul hA4)
    have h2 :
        Tendsto
            (fun z : ℍ =>
              q (z : ℂ) * ((25 : ℂ) * (A6 z) ^ (2 : ℕ) - (147 : ℂ) * (A4 z) ^ (2 : ℕ)))
            atImInfty
            (𝓝
              ((0 : ℂ) *
                ((25 : ℂ) * ((-(504 : ℂ)) ^ (2 : ℕ)) - (147 : ℂ) * ((240 : ℂ) ^ (2 : ℕ))))) :=
      hq.mul ((tendsto_const_nhds.mul (hA6.pow 2)).sub (tendsto_const_nhds.mul (hA4.pow 2)))
    have h3 :
        Tendsto (fun z : ℍ => (q (z : ℂ)) ^ (2 : ℕ) * ((-49 : ℂ) * (A4 z) ^ (3 : ℕ))) atImInfty
          (𝓝 (((0 : ℂ) ^ (2 : ℕ)) * ((-49 : ℂ) * ((240 : ℂ) ^ (3 : ℕ))))) :=
      hq2.mul (tendsto_const_nhds.mul (hA4.pow 3))
    exact (h1.add h2).add h3
  have hlim0' :
      Tendsto
          (fun z : ℍ =>
            (50 : ℂ) * (A6 z) - (147 : ℂ) * (A4 z) +
              q (z : ℂ) * ((25 : ℂ) * (A6 z) ^ (2 : ℕ) - (147 : ℂ) * (A4 z) ^ (2 : ℕ)) +
              (q (z : ℂ)) ^ (2 : ℕ) * ((-49 : ℂ) * (A4 z) ^ (3 : ℕ)))
          atImInfty (𝓝 (-(50 : ℂ) * (504 : ℂ) - (147 : ℂ) * (240 : ℂ))) := by
    -- Drop the terms killed by `q → 0`.
    simp_all
  have hlim :
      Tendsto
          (fun z : ℍ =>
            (50 : ℂ) * (A6 z) - (147 : ℂ) * (A4 z) +
              q (z : ℂ) * ((25 : ℂ) * (A6 z) ^ (2 : ℕ) - (147 : ℂ) * (A4 z) ^ (2 : ℕ)) +
              (q (z : ℂ)) ^ (2 : ℕ) * ((-49 : ℂ) * (A4 z) ^ (3 : ℕ)))
          atImInfty (𝓝 (-(60480 : ℂ))) := by
    convert (postTransparency := .instances) hlim0' using 1
    norm_num
  refine Tendsto.congr' (Filter.Eventually.of_forall (fun z => by simp [C1_eq_expansion])) hlim

lemma tendsto_q_div_Delta_sub_one_div_q_coeff_two :
    Tendsto
        (fun z : ℍ =>
          ((((q (z : ℂ) / Δ z - (1 : ℂ)) / q (z : ℂ)) - (24 : ℂ)) / q (z : ℂ)))
        atImInfty (𝓝 (324 : ℂ)) := by
  -- Write the second coefficient of `q/Δ` in terms of the coefficients for `Δ/q`.
  have hD : Tendsto (fun z : ℍ => (Δ z : ℂ) / q (z : ℂ)) atImInfty (𝓝 (1 : ℂ)) :=
    SpecialValuesVarphi₁Limits.tendsto_Delta_div_q
  have hA : Tendsto (fun z : ℍ => (((Δ z : ℂ) / q (z : ℂ)) - (1 : ℂ)) / q (z : ℂ)) atImInfty
      (𝓝 (-(24 : ℂ))) :=
    SpecialValuesVarphi₁Limits.tendsto_Delta_div_q_sub_one_div_q
  have hB : Tendsto (fun z : ℍ =>
        (((((Δ z : ℂ) / q (z : ℂ) - (1 : ℂ)) / q (z : ℂ)) - (-(24 : ℂ))) / q (z : ℂ)))
      atImInfty (𝓝 (252 : ℂ)) :=
    SpecialValuesVarphi₁Limits.tendsto_Delta_div_q_sub_one_div_q_coeff_two
  -- The identity:
  --   (((q/Δ - 1)/q - 24)/q) = (-(B + 24*A)) / (Δ/q)
  have hEq : ∀ z : ℍ,
      ((((q (z : ℂ) / Δ z - (1 : ℂ)) / q (z : ℂ)) - (24 : ℂ)) / q (z : ℂ)) =
        (-( (((( (Δ z : ℂ) / q (z : ℂ) - (1 : ℂ)) / q (z : ℂ)) - (-(24 : ℂ))) / q (z : ℂ)) +
              (24 : ℂ) * (((Δ z : ℂ) / q (z : ℂ) - (1 : ℂ)) / q (z : ℂ)) )) /
          ((Δ z : ℂ) / q (z : ℂ)) := by
    intro z
    have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
    have hzΔ : (Δ z : ℂ) ≠ 0 := Δ_ne_zero z
    field_simp [hzq, hzΔ]
    ring_nf
  have hnum :
      Tendsto
          (fun z : ℍ =>
            -(
              (((( (Δ z : ℂ) / q (z : ℂ) - (1 : ℂ)) / q (z : ℂ)) - (-(24 : ℂ))) / q (z : ℂ)) +
                (24 : ℂ) * (((Δ z : ℂ) / q (z : ℂ) - (1 : ℂ)) / q (z : ℂ))))
          atImInfty (𝓝 (-( (252 : ℂ) + (24 : ℂ) * (-(24 : ℂ)) ))) := by
    have h24 : Tendsto (fun _z : ℍ => (24 : ℂ)) atImInfty (𝓝 (24 : ℂ)) := tendsto_const_nhds
    exact Tendsto.neg (hB.add (h24.mul hA))
  have hdiv :
      Tendsto
          (fun z : ℍ =>
            -(
                ((((Δ z : ℂ) / q (z : ℂ) - (1 : ℂ)) / q (z : ℂ)) - (-(24 : ℂ))) / q (z : ℂ) +
                  (24 : ℂ) * (((Δ z : ℂ) / q (z : ℂ) - (1 : ℂ)) / q (z : ℂ))) /
              ((Δ z : ℂ) / q (z : ℂ)))
          atImInfty (𝓝 (-( (252 : ℂ) + (24 : ℂ) * (-(24 : ℂ)) ) / (1 : ℂ))) := by
    exact hnum.div hD (by norm_num)
  have hdiv' :
      Tendsto
          (fun z : ℍ =>
            -(
                ((((Δ z : ℂ) / q (z : ℂ) - (1 : ℂ)) / q (z : ℂ)) - (-(24 : ℂ))) / q (z : ℂ) +
                  (24 : ℂ) * (((Δ z : ℂ) / q (z : ℂ) - (1 : ℂ)) / q (z : ℂ))) /
              ((Δ z : ℂ) / q (z : ℂ)))
          atImInfty (𝓝 (324 : ℂ)) := by
    convert (postTransparency := .instances) hdiv using 1
    norm_num
  refine Tendsto.congr' (Filter.Eventually.of_forall (fun z => (hEq z).symm)) hdiv'

lemma tendsto_q_div_Delta_sq_sub_one_div_q_coeff_two :
    Tendsto (fun z : ℍ => Z2 z) atImInfty (𝓝 (1224 : ℂ)) := by
  -- Use `((q/Δ)^2 - 1) = (q/Δ - 1) * (q/Δ + 1)` and expand the second-order difference quotient.
  let U : ℍ → ℂ := fun z => (q (z : ℂ) / Δ z - (1 : ℂ)) / q (z : ℂ)
  let U2 : ℍ → ℂ := fun z => (U z - (24 : ℂ)) / q (z : ℂ)
  let V : ℍ → ℂ := fun z => q (z : ℂ) / Δ z + (1 : ℂ)
  have hU : Tendsto U atImInfty (𝓝 (24 : ℂ)) := by
    simpa [U] using! (SpecialValuesVarphi₁Limits.tendsto_q_div_Delta_sub_one_div_q :
      Tendsto (fun z : ℍ => (q (z : ℂ) / Δ z - (1 : ℂ)) / q (z : ℂ)) atImInfty _)
  have hU2 : Tendsto U2 atImInfty (𝓝 (324 : ℂ)) := by
    simpa [U2, U] using! tendsto_q_div_Delta_sub_one_div_q_coeff_two
  have hV : Tendsto V atImInfty (𝓝 ((1 : ℂ) + 1)) := by
    simpa [V] using! (SpecialValuesVarphi₁Limits.tendsto_q_div_Delta.add tendsto_const_nhds :
      Tendsto (fun z : ℍ => q (z : ℂ) / Δ z + (1 : ℂ)) atImInfty _)
  have hEqZ1 : ∀ z : ℍ, Z1 z = U z * V z := by
    intro z
    have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
    have hzΔ : (Δ z : ℂ) ≠ 0 := Δ_ne_zero z
    dsimp [Z1, Zfun, U, V]
    field_simp [hzq, hzΔ]
    ring_nf
  have hEqZ2 : ∀ z : ℍ, Z2 z = U2 z * V z + (24 : ℂ) * U z := by
    intro z
    have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
    have hzΔ : (Δ z : ℂ) ≠ 0 := Δ_ne_zero z
    have hZ1 : Z1 z = U z * V z := hEqZ1 z
    -- `Z2 = ((U*V) - 48)/q = ((U-24)/q)*V + 24*U`.
    dsimp [Z2, U2]
    grind only
  have hlim0 :
      Tendsto (fun z : ℍ => U2 z * V z + (24 : ℂ) * U z) atImInfty
        (𝓝 ((324 : ℂ) * ((1 : ℂ) + 1) + (24 : ℂ) * (24 : ℂ))) :=
    (hU2.mul hV).add ((tendsto_const_nhds : Tendsto (fun _z : ℍ => (24 : ℂ)) atImInfty _).mul hU)
  have hconst : (324 : ℂ) * ((1 : ℂ) + 1) + (24 : ℂ) * (24 : ℂ) = (1224 : ℂ) := by
    norm_num
  have hlim : Tendsto (fun z : ℍ => U2 z * V z + (24 : ℂ) * U z) atImInfty (𝓝 (1224 : ℂ)) := by
    simpa [hconst] using! hlim0
  refine Tendsto.congr' (Filter.Eventually.of_forall (fun z => by simp [hEqZ2 z])) hlim

/--
Constant-term limit for `varphi₂`: after subtracting the `q^{-2}` and `q^{-1}` principal parts,
the remainder tends to the explicit constant `223140096 / π^2` at `i∞`.
-/
public lemma tendsto_varphi₂_sub_c864_div_q_sq_sub_l_div_q :
    Tendsto
        (fun z : ℍ =>
          Dim24.varphi₂ z - ((864 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) / (q (z : ℂ)) ^ (2 : ℕ) -
            ((2218752 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) / q (z : ℂ))
        atImInfty (𝓝 ((223140096 : ℂ) / ((π : ℂ) ^ (2 : ℕ)))) := by
  -- Reduce to the second coefficient of `(varphi₂*q^2 - c864)/q`.
  let K : ℂ := (-36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))
  have hKc864 : K * (-24 : ℂ) = (864 : ℂ) / ((π : ℂ) ^ (2 : ℕ)) := by
    dsimp [K]
    ring_nf
  have hKl : K * (-(61632 : ℂ)) = (2218752 : ℂ) / ((π : ℂ) ^ (2 : ℕ)) := by
    dsimp [K]
    ring_nf
  have hKc0 : K * (-(6198336 : ℂ)) = (223140096 : ℂ) / ((π : ℂ) ^ (2 : ℕ)) := by
    dsimp [K]
    ring_nf
  have hEqMain : ∀ z : ℍ,
      Dim24.varphi₂ z - (K * (-24 : ℂ)) / (q (z : ℂ)) ^ (2 : ℕ) - (K * (-(61632 : ℂ))) / q (z : ℂ) =
        K *
          (C2 z + (C1 z) * (Z1 z) + (-24 : ℂ) * (Z2 z)) := by
    intro z
    have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
    have hzΔ : (Δ z : ℂ) ≠ 0 := Δ_ne_zero z
    -- Rewrite `varphi₂` as `K * Cfun * Zfun / q^2`.
    have hvarphi :
        Dim24.varphi₂ z =
          K * (Cfun z * Zfun z) / (q (z : ℂ)) ^ (2 : ℕ) := by
      have hπ : ((π : ℂ) ^ (2 : ℕ)) ≠ 0 := pow_ne_zero 2 (by exact_mod_cast Real.pi_ne_zero)
      have hΔ2 : (Δ z : ℂ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hzΔ
      -- Pure algebra from the definition of `varphi₂`.
      unfold Dim24.varphi₂ K Cfun Zfun
      field_simp
        [hπ, hzq, hzΔ, hΔ2, pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    -- Now isolate the second coefficient using `C1,C2,Z1,Z2`.
    -- Everything is an identity in the field `ℂ`.
    rw [hvarphi]
    dsimp [C2, C1, Z2, Z1, Zfun]
    field_simp [hzq, hzΔ, pow_two, pow_three, hKc864, hKl]
    ring_nf
  -- Take limits term-by-term.
  have hC1 : Tendsto C1 atImInfty (𝓝 (-(60480 : ℂ))) := by
    simpa using! (tendsto_C_sub_const_div_q' : Tendsto (fun z : ℍ => C1 z) atImInfty _)
  have hZ1 : Tendsto Z1 atImInfty (𝓝 (48 : ℂ)) := by
    simpa [Z1, Zfun] using! (SpecialValuesVarphi₁Limits.tendsto_q_div_Delta_sq_sub_one_div_q :
      Tendsto (fun z : ℍ => ((q (z : ℂ) / Δ z) ^ (2 : ℕ) - (1 : ℂ)) / q (z : ℂ)) atImInfty _)
  have hC2 : Tendsto C2 atImInfty (𝓝 (-(3265920 : ℂ))) := tendsto_C_sub_const_div_q_coeff_two
  have hZ2 : Tendsto Z2 atImInfty (𝓝 (1224 : ℂ)) :=
    tendsto_q_div_Delta_sq_sub_one_div_q_coeff_two
  have hinside :
      Tendsto (fun z : ℍ => C2 z + (C1 z) * (Z1 z) + (-24 : ℂ) * (Z2 z)) atImInfty
        (𝓝 (-(3265920 : ℂ) + (-(60480 : ℂ)) * (48 : ℂ) + (-24 : ℂ) * (1224 : ℂ))) := by
    have hmul := hC1.mul hZ1
    have hlin := (tendsto_const_nhds : Tendsto (fun _z : ℍ => (-24 : ℂ)) atImInfty _).mul hZ2
    exact (hC2.add hmul).add hlin
  have hconst :
      (-(3265920 : ℂ) + (-(60480 : ℂ)) * (48 : ℂ) + (-24 : ℂ) * (1224 : ℂ)) =
        (-(6198336 : ℂ)) := by
    norm_num
  have hmain :
      Tendsto (fun z : ℍ => K * (C2 z + (C1 z) * (Z1 z) + (-24 : ℂ) * (Z2 z))) atImInfty
        (𝓝 ((223140096 : ℂ) / ((π : ℂ) ^ (2 : ℕ)))) := by
    have hinside' : Tendsto (fun z : ℍ => C2 z + (C1 z) * (Z1 z) + (-24 : ℂ) * (Z2 z)) atImInfty
        (𝓝 (-(6198336 : ℂ))) := by
      convert (postTransparency := .instances) hinside using 1
      simpa using! hconst.symm
    have h := (tendsto_const_nhds : Tendsto (fun _z : ℍ => K) atImInfty _).mul hinside'
    simpa [hKc0] using! h
  refine
    Tendsto.congr'
      (Filter.Eventually.of_forall (fun z => by
        simpa [hKc864, hKl] using! (hEqMain z).symm)) hmain

end SpecialValuesVarphi₂Limits

end

end SpherePacking.Dim24
