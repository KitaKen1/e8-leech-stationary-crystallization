-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Varphi1C
import SpherePacking.ModularForms.Lv1Lv2Identities


/-!
# Leading `q`-expansion coefficients for `varphi₂` at `i∞`

This file records the first two coefficients in the `q`-expansion of `varphi₂` at `i∞`, packaged
as `atImInfty` limits. These limits are used later to evaluate derivatives of the profile at
`u = 4` (and `u = 2`).

## Main statements
* `SpecialValuesVarphi₂Limits.tendsto_varphi₂_mul_q_sq`
* `SpecialValuesVarphi₂Limits.tendsto_varphi₂_mul_q_sq_sub_const_div_q`
-/

namespace SpherePacking.Dim24

noncomputable section


namespace SpecialValuesVarphi₂Limits

open scoped Real Topology
open Filter Complex UpperHalfPlane

open SpecialValuesVarphi₁Limits

lemma tendsto_E₄_pow_three_sub_one_div_q :
    Tendsto (fun z : ℍ => ((E₄ z) ^ (3 : ℕ) - (1 : ℂ)) / q (z : ℂ)) atImInfty (𝓝 (720 : ℂ)) := by
  have hE4 : Tendsto (fun z : ℍ => E₄ z) atImInfty (𝓝 (1 : ℂ)) :=
    SpherePacking.ModularForms.tendsto_E₄_atImInfty
  have hE4lin :
      Tendsto (fun z : ℍ => (E₄ z - (1 : ℂ)) / q (z : ℂ)) atImInfty (𝓝 (240 : ℂ)) :=
    SpecialValuesVarphi₁Limits.tendsto_E₄_sub_one_div_q
  have hEq :
      (fun z : ℍ => ((E₄ z) ^ (3 : ℕ) - (1 : ℂ)) / q (z : ℂ)) =
        fun z : ℍ => ((E₄ z - (1 : ℂ)) / q (z : ℂ)) * ((E₄ z) ^ (2 : ℕ) + (E₄ z) + (1 : ℂ)) := by
    funext z
    ring
  have hpoly :
      Tendsto (fun z : ℍ => (E₄ z) ^ (2 : ℕ) + (E₄ z) + (1 : ℂ)) atImInfty
        (𝓝 ((1 : ℂ) ^ (2 : ℕ) + (1 : ℂ) + (1 : ℂ))) := by
    have hpow : Tendsto (fun z : ℍ => (E₄ z) ^ (2 : ℕ)) atImInfty (𝓝 ((1 : ℂ) ^ (2 : ℕ))) :=
      hE4.pow 2
    exact (hpow.add hE4).add tendsto_const_nhds
  have hmul := hE4lin.mul hpoly
  have hconst : (240 : ℂ) * ((1 : ℂ) + (1 : ℂ) + (1 : ℂ)) = (720 : ℂ) := by norm_num
  have hmul' := (Tendsto.congr (fun z => (congrArg (fun f : ℍ → ℂ => f z) hEq).symm) hmul)
  simpa [hconst] using! hmul'

lemma tendsto_E₆_sq_sub_one_div_q :
    Tendsto (fun z : ℍ => ((E₆ z) ^ (2 : ℕ) - (1 : ℂ)) / q (z : ℂ)) atImInfty
      (𝓝 (-(1008 : ℂ))) := by
  have hE6 : Tendsto (fun z : ℍ => E₆ z) atImInfty (𝓝 (1 : ℂ)) :=
    SpherePacking.ModularForms.tendsto_E₆_atImInfty
  have hE6lin :
      Tendsto (fun z : ℍ => (E₆ z - (1 : ℂ)) / q (z : ℂ)) atImInfty (𝓝 (-(504 : ℂ))) :=
    SpecialValuesVarphi₁Limits.tendsto_E₆_sub_one_div_q
  have hEq :
      (fun z : ℍ => ((E₆ z) ^ (2 : ℕ) - (1 : ℂ)) / q (z : ℂ)) =
        fun z : ℍ => ((E₆ z - (1 : ℂ)) / q (z : ℂ)) * ((E₆ z) + (1 : ℂ)) := by
    funext z
    ring
  have hplus :
      Tendsto (fun z : ℍ => (E₆ z) + (1 : ℂ)) atImInfty (𝓝 ((1 : ℂ) + (1 : ℂ))) :=
    hE6.add tendsto_const_nhds
  have hmul := hE6lin.mul hplus
  have hconst : (-(504 : ℂ)) * ((1 : ℂ) + (1 : ℂ)) = (-(1008 : ℂ)) := by norm_num
  have hmul' := (Tendsto.congr (fun z => (congrArg (fun f : ℍ → ℂ => f z) hEq).symm) hmul)
  simpa [hconst] using! hmul'

lemma tendsto_C_sub_const_div_q :
    Tendsto
        (fun z : ℍ =>
          ((((-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ)) + (24 : ℂ)) / q (z : ℂ)))
        atImInfty (𝓝 (-(60480 : ℂ))) := by
  have hE4 := tendsto_E₄_pow_three_sub_one_div_q
  have hE6 := tendsto_E₆_sq_sub_one_div_q
  have hEq :
      (fun z : ℍ =>
          ((((-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ)) + (24 : ℂ)) / q (z : ℂ))) =
        fun z : ℍ =>
          (-49 : ℂ) * (((E₄ z) ^ (3 : ℕ) - (1 : ℂ)) / q (z : ℂ)) +
            (25 : ℂ) * (((E₆ z) ^ (2 : ℕ) - (1 : ℂ)) / q (z : ℂ)) := by
    funext z
    ring
  have hlim1 :
      Tendsto (fun z : ℍ => (-49 : ℂ) * (((E₄ z) ^ (3 : ℕ) - (1 : ℂ)) / q (z : ℂ))) atImInfty
        (𝓝 ((-49 : ℂ) * (720 : ℂ))) :=
    hE4.const_mul (-49 : ℂ)
  have hlim2 :
      Tendsto (fun z : ℍ => (25 : ℂ) * (((E₆ z) ^ (2 : ℕ) - (1 : ℂ)) / q (z : ℂ))) atImInfty
        (𝓝 ((25 : ℂ) * (-(1008 : ℂ)))) :=
    hE6.const_mul (25 : ℂ)
  let c : ℂ := (-49 : ℂ) * (720 : ℂ) + (25 : ℂ) * (-(1008 : ℂ))
  have hlimc :
      Tendsto
          (fun z : ℍ =>
            (-49 : ℂ) * (((E₄ z) ^ (3 : ℕ) - (1 : ℂ)) / q (z : ℂ)) +
              (25 : ℂ) * (((E₆ z) ^ (2 : ℕ) - (1 : ℂ)) / q (z : ℂ)))
          atImInfty (𝓝 c) :=
    hlim1.add hlim2
  have hc : c = (-(60480 : ℂ)) := by
    dsimp [c]
    norm_num
  lia

/-- Leading `q`-asymptotic for `varphi₂`: `varphi₂ z * q(z)^2 → 864 / π^2` as `z → i∞`. -/
public lemma tendsto_varphi₂_mul_q_sq :
    Tendsto (fun z : ℍ => Dim24.varphi₂ z * (q (z : ℂ)) ^ (2 : ℕ)) atImInfty
      (𝓝 ((864 : ℂ) / ((π : ℂ) ^ (2 : ℕ)))) := by
  have hE4 : Tendsto (fun z : ℍ => E₄ z) atImInfty (𝓝 (1 : ℂ)) :=
    SpherePacking.ModularForms.tendsto_E₄_atImInfty
  have hE6 : Tendsto (fun z : ℍ => E₆ z) atImInfty (𝓝 (1 : ℂ)) :=
    SpherePacking.ModularForms.tendsto_E₆_atImInfty
  have hqΔ : Tendsto (fun z : ℍ => q (z : ℂ) / (Δ z)) atImInfty (𝓝 (1 : ℂ)) := tendsto_q_div_Delta
  have hqΔ2 : Tendsto (fun z : ℍ => (q (z : ℂ) / (Δ z)) ^ (2 : ℕ)) atImInfty (𝓝 (1 : ℂ)) := by
    simpa using! (hqΔ.pow 2)
  have hC : Tendsto (fun z : ℍ => ((-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ)))
      atImInfty (𝓝 ((-24 : ℂ))) := by
    have hE4_3 :
        Tendsto (fun z : ℍ => (E₄ z) ^ (3 : ℕ)) atImInfty (𝓝 ((1 : ℂ) ^ (3 : ℕ))) :=
      hE4.pow 3
    have hE6_2 :
        Tendsto (fun z : ℍ => (E₆ z) ^ (2 : ℕ)) atImInfty (𝓝 ((1 : ℂ) ^ (2 : ℕ))) :=
      hE6.pow 2
    have hlin1 :
        Tendsto (fun z : ℍ => (-49 : ℂ) * (E₄ z) ^ (3 : ℕ)) atImInfty
          (𝓝 ((-49 : ℂ) * ((1 : ℂ) ^ (3 : ℕ)))) :=
      hE4_3.const_mul (-49 : ℂ)
    have hlin2 :
        Tendsto (fun z : ℍ => (25 : ℂ) * (E₆ z) ^ (2 : ℕ)) atImInfty
          (𝓝 ((25 : ℂ) * ((1 : ℂ) ^ (2 : ℕ)))) :=
      hE6_2.const_mul (25 : ℂ)
    have hlin := hlin1.add hlin2
    have hconst : (-49 : ℂ) + (25 : ℂ) = (-24 : ℂ) := by norm_num
    simpa [hconst] using! hlin
  have hrew :
      (fun z : ℍ => Dim24.varphi₂ z * (q (z : ℂ)) ^ (2 : ℕ)) =
        fun z : ℍ =>
          ((-36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) *
              (((-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ)) *
                (q (z : ℂ) / (Δ z)) ^ (2 : ℕ)) := by
    funext z
    have hπ : ((π : ℂ) ^ (2 : ℕ)) ≠ 0 :=
      pow_ne_zero 2 (by exact_mod_cast Real.pi_ne_zero)
    have hΔ : (Δ z : ℂ) ≠ 0 := Δ_ne_zero z
    have hΔ2 : (Δ z : ℂ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hΔ
    -- Pure algebra.
    unfold Dim24.varphi₂
    field_simp [hπ, hΔ, hΔ2, pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hprod :=
    (hC.mul hqΔ2).const_mul ((-36 : ℂ) / ((π : ℂ) ^ (2 : ℕ)))
  grind only

/-- The next `q`-coefficient of `varphi₂` after subtracting the leading constant term. -/
public lemma tendsto_varphi₂_mul_q_sq_sub_const_div_q :
    Tendsto
        (fun z : ℍ =>
          ((Dim24.varphi₂ z * (q (z : ℂ)) ^ (2 : ℕ)) - ((864 : ℂ) / ((π : ℂ) ^ (2 : ℕ)))) /
            q (z : ℂ))
        atImInfty (𝓝 ((2218752 : ℂ) / ((π : ℂ) ^ (2 : ℕ)))) := by
  have hqΔ : Tendsto (fun z : ℍ => q (z : ℂ) / (Δ z)) atImInfty (𝓝 (1 : ℂ)) := tendsto_q_div_Delta
  have hqΔ2 : Tendsto (fun z : ℍ => (q (z : ℂ) / (Δ z)) ^ (2 : ℕ)) atImInfty (𝓝 (1 : ℂ)) := by
    simpa using! (hqΔ.pow 2)
  have hZlin :
      Tendsto (fun z : ℍ => ((q (z : ℂ) / Δ z) ^ (2 : ℕ) - (1 : ℂ)) / q (z : ℂ)) atImInfty
        (𝓝 (48 : ℂ)) :=
    tendsto_q_div_Delta_sq_sub_one_div_q
  have hC1 :
      Tendsto
          (fun z : ℍ =>
            ((((-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ)) + (24 : ℂ)) / q (z : ℂ)))
          atImInfty (𝓝 (-(60480 : ℂ))) :=
    tendsto_C_sub_const_div_q
  let K : ℂ := (-36 : ℂ) / ((π : ℂ) ^ (2 : ℕ))
  let C : ℍ → ℂ := fun z : ℍ => (-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ)
  let Z : ℍ → ℂ := fun z : ℍ => (q (z : ℂ) / (Δ z)) ^ (2 : ℕ)
  have hEq :
      (fun z : ℍ =>
          ((Dim24.varphi₂ z * (q (z : ℂ)) ^ (2 : ℕ)) - (K * (-24 : ℂ))) / q (z : ℂ)) =
        fun z : ℍ =>
          K *
            (((C z + (24 : ℂ)) / q (z : ℂ)) * Z z +
              (-24 : ℂ) * ((Z z - (1 : ℂ)) / q (z : ℂ))) := by
    funext z
    have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
    have hzΔ : (Δ z : ℂ) ≠ 0 := Δ_ne_zero z
    have hπ : ((π : ℂ) ^ (2 : ℕ)) ≠ 0 := pow_ne_zero 2 (by exact_mod_cast Real.pi_ne_zero)
    have hΔ2 : (Δ z : ℂ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hzΔ
    have hrew :
        Dim24.varphi₂ z * (q (z : ℂ)) ^ (2 : ℕ) = K * (C z * Z z) := by
      unfold Dim24.varphi₂ K C Z
      field_simp [hπ, hzq, hzΔ, hΔ2, pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    -- Expand and regroup: everything is an identity in the field `ℂ`.
    rw [hrew]
    field_simp [hzq]
    ring_nf
  have hCZ0 : Tendsto (fun z : ℍ => Z z) atImInfty (𝓝 (1 : ℂ)) := by
    simpa [Z] using! hqΔ2
  have hinside :
      Tendsto
          (fun z : ℍ =>
            ((C z + (24 : ℂ)) / q (z : ℂ)) * Z z +
              (-24 : ℂ) * ((Z z - (1 : ℂ)) / q (z : ℂ)))
          atImInfty (𝓝 ((-(60480 : ℂ)) * (1 : ℂ) + (-24 : ℂ) * (48 : ℂ))) := by
    have h1 := hC1.mul hCZ0
    have h2 := hZlin.const_mul (-24 : ℂ)
    exact h1.add h2
  have hmain :
      Tendsto
          (fun z : ℍ =>
            K *
              (((C z + (24 : ℂ)) / q (z : ℂ)) * Z z +
                (-24 : ℂ) * ((Z z - (1 : ℂ)) / q (z : ℂ))))
          atImInfty (𝓝 (K * ((-(60480 : ℂ)) * (1 : ℂ) + (-24 : ℂ) * (48 : ℂ)))) :=
    hinside.const_mul K
  have hmain' :
      Tendsto
          (fun z : ℍ =>
            ((Dim24.varphi₂ z * (q (z : ℂ)) ^ (2 : ℕ)) - (K * (-24 : ℂ))) / q (z : ℂ))
          atImInfty (𝓝 (K * ((-(60480 : ℂ)) * (1 : ℂ) + (-24 : ℂ) * (48 : ℂ)))) := by
    exact (tendsto_congr (congrFun (id (Eq.symm hEq)))).mp hmain
  have hconstK : K * (-24 : ℂ) = (864 : ℂ) / ((π : ℂ) ^ (2 : ℕ)) := by
    unfold K
    ring_nf
  have hconstK' : (864 : ℂ) / ((π : ℂ) ^ (2 : ℕ)) = K * (-24 : ℂ) := by
    simpa using! hconstK.symm
  have hconst :
      K * (-(60480 : ℂ) + -((24 : ℂ) * (48 : ℂ))) = (2218752 : ℂ) / ((π : ℂ) ^ (2 : ℕ)) := by
    unfold K
    ring_nf
  have hEq' :
      (fun z : ℍ =>
          ((Dim24.varphi₂ z * (q (z : ℂ)) ^ (2 : ℕ)) - ((864 : ℂ) / ((π : ℂ) ^ (2 : ℕ)))) /
            q (z : ℂ)) =ᶠ[atImInfty]
        fun z : ℍ =>
          ((Dim24.varphi₂ z * (q (z : ℂ)) ^ (2 : ℕ)) - (K * (-24 : ℂ))) / q (z : ℂ) := by
    refine Filter.Eventually.of_forall ?_
    intro z
    simp [hconstK']
  have hfinal0 := Tendsto.congr' hEq'.symm hmain'
  simpa [hconst] using! hfinal0

end SpecialValuesVarphi₂Limits

end

end SpherePacking.Dim24
