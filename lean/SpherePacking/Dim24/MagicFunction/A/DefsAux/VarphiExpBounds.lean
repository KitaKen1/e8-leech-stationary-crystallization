-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.Prelude
public import SpherePacking.ForMathlib.BoundsOnIcc


/-!
# Exponential bounds for `varphi` on the imaginary axis

We extract a concrete bound on `‖varphi(it)‖` for `t ≥ 1` from the `atImInfty` Big-O estimate in
`VarphiBounds`. This is used to dominate the tail integral `I₆'` (the only integral over `Ici 1`).

## Main statement
* `exists_bound_norm_varphi_resToImagAxis_exp_Ici_one`
-/

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

noncomputable section


namespace VarphiExpBounds

open scoped UpperHalfPlane
open Filter Asymptotics UpperHalfPlane

open VarphiBounds

/-- Continuity of the modular form `varphi`. -/
public lemma continuous_varphi : Continuous (varphi : ℍ → ℂ) := by
  simpa using! (varphi_holo'.continuous : Continuous (varphi : ℍ → ℂ))

/-- Continuity of the restriction `t ↦ varphi(it)` on `t ≥ 1`. -/
public lemma continuousOn_varphi_resToImagAxis_Ici_one :
    ContinuousOn (fun t : ℝ => varphi.resToImagAxis t) (Set.Ici (1 : ℝ)) := by
  simpa using!
    (Function.continuousOn_resToImagAxis_Ici_one_of (F := varphi) continuous_varphi)

/-- An explicit exponential decay bound for `‖varphi(it)‖` on `t ≥ 1`. -/
public lemma exists_bound_norm_varphi_resToImagAxis_exp_Ici_one :
    ∃ C, ∀ t : ℝ, 1 ≤ t → ‖varphi.resToImagAxis t‖ ≤ C * Real.exp (-(2 * Real.pi) * t) := by
  -- Unpack the `atImInfty` Big-O bound.
  rcases (varphi_isBigO_exp_neg_two_pi : (varphi : ℍ → ℂ) =O[atImInfty]
      fun z : ℍ => Real.exp (-(2 * Real.pi) * z.im)).exists_pos with ⟨C, hCpos, hC⟩
  have hC' : ∀ᶠ z : ℍ in atImInfty,
      ‖varphi z‖ ≤ C * ‖Real.exp (-(2 * Real.pi) * z.im)‖ := hC.bound
  rcases (Filter.eventually_atImInfty).1 hC' with ⟨A0, hA0⟩
  let A : ℝ := max A0 1
  have hA_ge_one : 1 ≤ A := le_max_right _ _
  -- Bound on the compact interval `t ∈ [1,A]` (after multiplying by `exp(2π t)`).
  have hcont_axis :
      ContinuousOn
        (fun t : ℝ => ‖varphi.resToImagAxis t‖ * Real.exp (2 * Real.pi * t))
        (Set.Icc 1 A) := by
    have hvarphi : ContinuousOn (fun t : ℝ => varphi.resToImagAxis t) (Set.Icc 1 A) :=
      (continuousOn_varphi_resToImagAxis_Ici_one).mono fun _ ht => ht.1
    fun_prop
  have hApos : 1 ≤ A := hA_ge_one
  rcases
      SpherePacking.ForMathlib.exists_upper_bound_on_Icc
        (g := fun t : ℝ => ‖varphi.resToImagAxis t‖ * Real.exp (2 * Real.pi * t))
        (a := 1) (b := A) hApos hcont_axis with
    ⟨Cmid, hCmid⟩
  -- Use the tail bound for `t ≥ A`.
  refine ⟨max C Cmid, ?_⟩
  intro t ht
  by_cases htA : A ≤ t
  · -- Tail: apply the `atImInfty` bound at `z = it`.
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    let z : ℍ := ⟨Complex.I * (t : ℂ), by simpa using! ht0⟩
    have hzIm : A0 ≤ z.im := by
      have : A0 ≤ A := le_max_left _ _
      have : A0 ≤ t := this.trans htA
      simpa [z, UpperHalfPlane.im] using! this
    have hz := hA0 z hzIm
    have hres : ResToImagAxis varphi t = varphi z := by
      simp [ResToImagAxis, z, ht0]
    have hzexp : Real.exp (-(2 * Real.pi * z.im)) = Real.exp (-(2 * Real.pi * t)) := by
      simp [z, UpperHalfPlane.im, mul_assoc]
    -- `max C Cmid` dominates `C`.
    have hC_le : C ≤ max C Cmid := le_max_left _ _
    -- Simplify `‖Real.exp _‖`.
    have hnonneg : 0 ≤ Real.exp (-(2 * Real.pi) * t) := (Real.exp_pos _).le
    have hz' : ‖varphi z‖ ≤ (max C Cmid) * Real.exp (-(2 * Real.pi) * t) := by
      -- from `hz : ‖varphi z‖ ≤ C * ‖exp ...‖`
      have := hz.trans (by
        -- replace `C` by `max C Cmid` and remove the norm on the RHS.
        have hle :
            C * ‖Real.exp (-(2 * Real.pi) * z.im)‖ ≤
              (max C Cmid) * ‖Real.exp (-(2 * Real.pi) * z.im)‖ :=
          mul_le_mul_of_nonneg_right hC_le (norm_nonneg _)
        exact hle)
      -- Rewrite the exponent using `z.im = t`.
      simpa [hzexp, Real.norm_of_nonneg hnonneg] using! this
    simpa [Function.resToImagAxis_eq_resToImagAxis, hres] using! hz'
  · -- Compact part: use the maximum bound on `‖varphi(it)‖ * exp(2π t)`.
    have htIcc : t ∈ Set.Icc (1 : ℝ) A := by
      refine ⟨ht, ?_⟩
      exact le_of_not_ge htA
    have hCmid' : ‖varphi.resToImagAxis t‖ * Real.exp (2 * Real.pi * t) ≤ Cmid :=
      hCmid t htIcc
    have hpos : 0 < Real.exp (2 * Real.pi * t) := Real.exp_pos _
    have :
        ‖varphi.resToImagAxis t‖ ≤ Cmid * Real.exp (-(2 * Real.pi) * t) := by
      -- Divide by `exp(2π t)` and rewrite as multiplication by `exp(-2π t)`.
      have hdiv := (le_div_iff₀ hpos).2 (by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using! hCmid')
      -- `1 / exp(2π t) = exp(-2π t)`.
      simpa [Real.exp_neg, one_div] using! hdiv
    have hCmid_le : Cmid ≤ max C Cmid := le_max_right _ _
    exact this.trans (by
      have hnonneg : 0 ≤ Real.exp (-(2 * Real.pi) * t) := (Real.exp_pos _).le
      exact (mul_le_mul_of_nonneg_right hCmid_le hnonneg))

end VarphiExpBounds

end

end SpherePacking.Dim24
