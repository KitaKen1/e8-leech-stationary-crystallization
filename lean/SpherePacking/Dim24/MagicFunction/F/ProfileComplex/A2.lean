-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.ProfileComplex.A1

/-!
# Differentiability of the bounded pieces of `aPrimeC`

This file proves differentiability in the complex parameter for the bounded-interval contour
pieces in the definition of `ProfileComplex.A.aPrimeC` (the pieces `I₂'`-`I₅'`).
-/

namespace SpherePacking.Dim24

noncomputable section

open scoped Interval Topology UpperHalfPlane

open Complex Real MeasureTheory
open MagicFunction.Parametrisations intervalIntegral

namespace ProfileComplex

/-! ### Basic measurability -/

namespace A

open scoped Interval

/-! ### Uniform bounds for the path parametrisations -/

/-- Uniform bound on the path parametrization `z₂'` on `Ι 0 1`. -/
public lemma norm_z₂'_le (t : ℝ) : ‖z₂' t‖ ≤ (2 : ℝ) :=
  norm_z₂'_le_two t

/-- Uniform bound on the path parametrization `z₃'` on `Ι 0 1`. -/
public lemma norm_z₃'_le (t : ℝ) (ht : t ∈ Ι (0 : ℝ) 1) : ‖z₃' t‖ ≤ (2 : ℝ) := by
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := mem_Icc_of_mem_Ι ht
  have hz : z₃' t = (1 : ℂ) + Complex.I * (t : ℂ) := by
    simp [MagicFunction.Parametrisations.z₃'_eq_of_mem (t := t) htIcc, add_comm]
  have ht0 : 0 ≤ t := htIcc.1
  have ht1 : t ≤ 1 := htIcc.2
  have ht_abs : ‖Complex.I * (t : ℂ)‖ ≤ (1 : ℝ) := by
    have : ‖(t : ℂ)‖ ≤ 1 := by
      simpa [Complex.norm_real, abs_of_nonneg ht0] using! ht1
    simpa [norm_mul] using! this
  calc
    ‖z₃' t‖ = ‖(1 : ℂ) + Complex.I * (t : ℂ)‖ := by simp [hz]
    _ ≤ ‖(1 : ℂ)‖ + ‖Complex.I * (t : ℂ)‖ := norm_add_le _ _
    _ ≤ 1 + 1 := by
      exact add_le_add (by simp) ht_abs
    _ = (2 : ℝ) := by norm_num

/-- Uniform bound on the path parametrization `z₄'` on `Ι 0 1`. -/
public lemma norm_z₄'_le (t : ℝ) : ‖z₄' t‖ ≤ (2 : ℝ) :=
  norm_z₄'_le_two t

/-- Uniform bound on the path parametrization `z₅'` on `Ι 0 1`. -/
public lemma norm_z₅'_le (t : ℝ) : ‖z₅' t‖ ≤ (1 : ℝ) :=
  norm_z₅'_le_one t

/-! ### Compactness bounds for `varphi'` along continuous curves -/

lemma exists_bound_norm_varphi'_comp_Icc
    (w : ℝ → ℂ) (hw : ContinuousOn w (Set.Icc (0 : ℝ) 1))
    (him : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < (w t).im) :
    ∃ M : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖varphi' (w t)‖ ≤ M := by
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  have him' : ∀ t ∈ s, 0 < (w t).im := by
    simpa [s] using! him
  have hw' : Continuous fun t : s => w (t : ℝ) := by
    -- `ContinuousOn` on `s` is equivalent to continuity of the restriction to the subtype.
    simpa [s] using! (continuousOn_iff_continuous_restrict.1 (by simpa [s] using! hw))
  let g : s → ℍ := fun t =>
    (⟨w (t : ℝ), him' (t : ℝ) t.property⟩ : ℍ)
  have hg : Continuous g := by
    simpa [g] using!
      Continuous.upperHalfPlaneMk hw' (fun t => (him' (t : ℝ) t.property))
  have hvar : Continuous fun t : s => varphi (g t) :=
    (VarphiExpBounds.continuous_varphi).comp hg
  have hEq :
      (fun t : s => varphi' (w (t : ℝ))) = fun t : s => varphi (g t) := by
    funext t
    have ht : t.1 ∈ s := t.2
    simp [g, Dim24.varphi'_def (z := w t.1) (him' t.1 ht)]
  have hcont : Continuous fun t : s => varphi' (w (t : ℝ)) := by
    simpa [hEq] using! hvar
  have hcont_norm : Continuous fun t : s => ‖varphi' (w (t : ℝ))‖ := hcont.norm
  have hcontOn_norm : ContinuousOn (fun t : ℝ => ‖varphi' (w t)‖) s := by
    simpa [s] using! (continuousOn_iff_continuous_restrict.2 hcont_norm)
  have hs : IsCompact s := isCompact_Icc
  have hne : s.Nonempty := by
    refine ⟨0, ?_⟩
    simp [s]
  obtain ⟨t0, ht0, ht0max⟩ := hs.exists_isMaxOn hne hcontOn_norm
  refine ⟨‖varphi' (w t0)‖, ?_⟩
  intro t ht
  exact ht0max ht

/-! ### Exponential bounds near the cusps (segments `z₃'` and `z₅'`) -/

lemma bound_base_I₃' :
    ∃ C : ℝ,
      ∀ t ∈ Ι (0 : ℝ) 1,
        ‖(Complex.I : ℂ) * (varphi' (-1 / (z₃' t - 1)) * (z₃' t - 1) ^ (10 : ℕ))‖ ≤ C := by
  rcases VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one with ⟨C0, hC0⟩
  have hC0nonneg : 0 ≤ C0 := by
    have h := hC0 1 (le_rfl : (1 : ℝ) ≤ 1)
    have hexp_pos : 0 < Real.exp (-(2 * Real.pi) * (1 : ℝ)) := by positivity
    exact
      ForMathlib.nonneg_of_nonneg_le_mul (ha := norm_nonneg (varphi.resToImagAxis (1 : ℝ)))
        (hb := hexp_pos) (h := by simpa using! h)
  refine ⟨C0, ?_⟩
  intro t ht
  have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := mem_Ioc_of_mem_Ι ht
  have ht0 : 0 < t := htIoc.1
  have ht1 : t ≤ 1 := htIoc.2
  have hone : (1 : ℝ) ≤ 1 / t := by simpa using! (one_le_one_div ht0 ht1)
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc_of_Ioc htIoc
  have hz1 : z₃' t - 1 = Complex.I * (t : ℂ) := by
    have hz : z₃' t = 1 + Complex.I * (t : ℂ) := by
      simp [MagicFunction.Parametrisations.z₃'_eq_of_mem (t := t) htIcc]
    simp [hz, sub_eq_add_neg, add_assoc, add_comm]
  have hvar :
      ‖varphi' (-1 / (z₃' t - 1))‖ ≤ C0 := by
    have hEq :
        varphi' (-1 / (z₃' t - 1)) = varphi.resToImagAxis (1 / t) := by
      have harg : (-1 / (z₃' t - 1) : ℂ) = (Complex.I : ℂ) * ((1 / t : ℝ) : ℂ) := by
        calc
          (-1 / (z₃' t - 1) : ℂ) = (-1 : ℂ) / ((Complex.I : ℂ) * (t : ℂ)) := by simp [hz1]
          _ = ((-1 : ℂ) / (Complex.I : ℂ)) / (t : ℂ) := by simp [div_mul_eq_div_div]
          _ = (Complex.I : ℂ) / (t : ℂ) := by simp
          _ = (Complex.I : ℂ) * ((1 / t : ℝ) : ℂ) := by
            simp [div_eq_mul_inv, Complex.ofReal_inv]
      have him' : 0 < ((Complex.I : ℂ) * ((1 / t : ℝ) : ℂ)).im := by
        simpa using! (one_div_pos.2 ht0)
      simp [harg, Function.resToImagAxis, ResToImagAxis, ht0]
    have h0 := hC0 (1 / t) hone
    have hexp_le : Real.exp (-(2 * Real.pi) * (1 / t)) ≤ 1 := by
      have : (-(2 * Real.pi) * (1 / t) : ℝ) ≤ 0 := by
        have : 0 ≤ (1 / t : ℝ) := (one_div_pos.2 ht0).le
        nlinarith [Real.pi_pos, this]
      simpa using! (Real.exp_le_one_iff.2 this)
    have hle : C0 * Real.exp (-(2 * Real.pi) * (1 / t)) ≤ C0 :=
      (mul_le_mul_of_nonneg_left hexp_le hC0nonneg).trans (by simp)
    exact (le_trans (by simpa [hEq] using! h0) hle)
  have hpow : ‖(z₃' t - 1) ^ (10 : ℕ)‖ ≤ 1 := by
    have ht_abs' : ‖(t : ℂ)‖ ≤ 1 := by
      have ht0' : 0 ≤ t := le_of_lt ht0
      simpa [Complex.norm_real, abs_of_nonneg ht0'] using! ht1
    have ht_le_one : ‖z₃' t - 1‖ ≤ 1 := by simpa [hz1, norm_mul] using! ht_abs'
    have := pow_le_pow_left₀ (norm_nonneg (z₃' t - 1)) ht_le_one 10
    simpa [norm_pow] using! this
  calc
    ‖(Complex.I : ℂ) * (varphi' (-1 / (z₃' t - 1)) * (z₃' t - 1) ^ (10 : ℕ))‖
        = ‖varphi' (-1 / (z₃' t - 1)) * (z₃' t - 1) ^ (10 : ℕ)‖ := by
            simp
    _ ≤ ‖varphi' (-1 / (z₃' t - 1))‖ * ‖(z₃' t - 1) ^ (10 : ℕ)‖ := norm_mul_le _ _
    _ ≤ C0 * 1 := by gcongr
    _ = C0 := by simp

lemma bound_base_I₅' :
    ∃ C : ℝ,
      ∀ t ∈ Ι (0 : ℝ) 1,
        ‖(Complex.I : ℂ) * (varphi' (-1 / z₅' t) * (z₅' t) ^ (10 : ℕ))‖ ≤ C := by
  rcases VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one with ⟨C0, hC0⟩
  have hC0nonneg : 0 ≤ C0 := by
    have h := hC0 1 (le_rfl : (1 : ℝ) ≤ 1)
    have hexp_pos : 0 < Real.exp (-(2 * Real.pi) * (1 : ℝ)) := by positivity
    exact
      ForMathlib.nonneg_of_nonneg_le_mul (ha := norm_nonneg (varphi.resToImagAxis (1 : ℝ)))
        (hb := hexp_pos) (h := by simpa using! h)
  refine ⟨C0, ?_⟩
  intro t ht
  have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := mem_Ioc_of_mem_Ι ht
  have ht0 : 0 < t := htIoc.1
  have ht1 : t ≤ 1 := htIoc.2
  have hone : (1 : ℝ) ≤ 1 / t := by simpa using! (one_le_one_div ht0 ht1)
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc_of_Ioc htIoc
  have hz : z₅' t = Complex.I * (t : ℂ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using! (z₅'_eq_of_mem (t := t) htIcc)
  have hvar :
      ‖varphi' (-1 / z₅' t)‖ ≤ C0 := by
    have hEq :
        varphi' (-1 / z₅' t) = varphi.resToImagAxis (1 / t) := by
        have harg : (-1 / z₅' t : ℂ) = (Complex.I : ℂ) * ((1 / t : ℝ) : ℂ) := by
          calc
            (-1 / z₅' t : ℂ) = (-1 : ℂ) / ((Complex.I : ℂ) * (t : ℂ)) := by simp [hz]
            _ = ((-1 : ℂ) / (Complex.I : ℂ)) / (t : ℂ) := by simp [div_mul_eq_div_div]
            _ = (Complex.I : ℂ) / (t : ℂ) := by simp
            _ = (Complex.I : ℂ) * ((1 / t : ℝ) : ℂ) := by
              simp [div_eq_mul_inv, Complex.ofReal_inv]
        have him' : 0 < ((Complex.I : ℂ) * ((1 / t : ℝ) : ℂ)).im := by
          simpa using! (one_div_pos.2 ht0)
        simp [harg, Function.resToImagAxis, ResToImagAxis, ht0]
    have h0 := hC0 (1 / t) hone
    have hexp_le : Real.exp (-(2 * Real.pi) * (1 / t)) ≤ 1 := by
      have : (-(2 * Real.pi) * (1 / t) : ℝ) ≤ 0 := by
        have : 0 ≤ (1 / t : ℝ) := (one_div_pos.2 ht0).le
        nlinarith [Real.pi_pos, this]
      simpa using! (Real.exp_le_one_iff.2 this)
    have hle : C0 * Real.exp (-(2 * Real.pi) * (1 / t)) ≤ C0 :=
      (mul_le_mul_of_nonneg_left hexp_le hC0nonneg).trans (by simp)
    exact (le_trans (by simpa [hEq] using! h0) hle)
  have hpow : ‖(z₅' t) ^ (10 : ℕ)‖ ≤ 1 := by
    have ht_abs' : ‖(t : ℂ)‖ ≤ 1 := by
      have ht0' : 0 ≤ t := le_of_lt ht0
      simpa [Complex.norm_real, abs_of_nonneg ht0'] using! ht1
    have ht_le_one : ‖z₅' t‖ ≤ 1 := by simpa [hz, norm_mul] using! ht_abs'
    have := pow_le_pow_left₀ (norm_nonneg (z₅' t)) ht_le_one 10
    simpa [norm_pow] using! this
  calc
    ‖(Complex.I : ℂ) * (varphi' (-1 / z₅' t) * (z₅' t) ^ (10 : ℕ))‖
          = ‖varphi' (-1 / z₅' t) * (z₅' t) ^ (10 : ℕ)‖ := by simp
    _ ≤ ‖varphi' (-1 / z₅' t)‖ * ‖(z₅' t) ^ (10 : ℕ)‖ := norm_mul_le _ _
    _ ≤ C0 * 1 := by gcongr
    _ = C0 := by simp

/-! ### Differentiability of the finite pieces -/

/-- Differentiability of the contour piece `I₂'` in the complex parameter. -/
public lemma differentiableAt_I₂' (u0 : ℂ) : DifferentiableAt ℂ I₂' u0 := by
  let base : ℝ → ℂ :=
    fun t : ℝ => varphi' (-1 / (z₂' t + 1)) * (z₂' t + 1) ^ (10 : ℕ)
  let z : ℝ → ℂ := fun t : ℝ => z₂' t
  have hz : Continuous z := by
    fun_prop [MagicFunction.Parametrisations.z₂', MagicFunction.Parametrisations.z₂]
  have hbase : Measurable base := by
    have hz_meas : Measurable z := hz.measurable
    have hvar : Measurable fun t : ℝ => varphi' (-1 / (z t + 1)) :=
      measurable_varphi'.comp (measurable_const.div (hz_meas.add measurable_const))
    have hpow : Measurable fun t : ℝ => (z t + 1) ^ (10 : ℕ) :=
      (hz_meas.add measurable_const).pow_const _
    simpa [base, mul_assoc] using! hvar.mul hpow
  have hz_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖z t‖ ≤ (2 : ℝ) := fun t _ => A.norm_z₂'_le t
  -- Bound `‖varphi' (-1/(z₂' t + 1))‖` on `Icc 0 1` by compactness.
  have hvarphi_bound :
      ∃ M : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖varphi' (-1 / (z₂' t + 1))‖ ≤ M := by
    let w : ℝ → ℂ := fun t => (-1 : ℂ) / (z₂' t + 1)
    have hw : ContinuousOn w (Set.Icc (0 : ℝ) 1) := by
      have hz : Continuous fun t : ℝ => z₂' t := by
        fun_prop [MagicFunction.Parametrisations.z₂', MagicFunction.Parametrisations.z₂]
      have hden : Continuous fun t : ℝ => z₂' t + 1 := hz.add continuous_const
      have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, z₂' t + 1 ≠ 0 := by
        intro t ht
        have hz2 : z₂' t + 1 = (t : ℂ) + Complex.I := by
            simp [MagicFunction.Parametrisations.z₂'_eq_of_mem (t := t) ht, add_left_comm, add_comm]
        intro hEq
        have hEq' : ((t : ℂ) + Complex.I) = 0 := by simpa [hz2] using! hEq
        have : ((t : ℂ) + Complex.I).im = (0 : ℂ).im := congrArg Complex.im hEq'
        simp at this
      have hnum : ContinuousOn (fun _t : ℝ => (-1 : ℂ)) (Set.Icc (0 : ℝ) 1) := continuousOn_const
      have hdenOn : ContinuousOn (fun t : ℝ => z₂' t + 1) (Set.Icc (0 : ℝ) 1) := hden.continuousOn
      simpa [w] using! hnum.div hdenOn hne
    have him : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < (w t).im := by
      intro t ht
      have hz2 : z₂' t + 1 = (t : ℂ) + Complex.I := by
          simp [MagicFunction.Parametrisations.z₂'_eq_of_mem (t := t) ht, add_left_comm, add_comm]
      have hden_ne : (t : ℂ) + Complex.I ≠ 0 := by
        intro hEq
        have : ((t : ℂ) + Complex.I).im = (0 : ℂ).im := congrArg Complex.im hEq
        simp at this
      have hnormSq_pos : 0 < Complex.normSq ((t : ℂ) + Complex.I) :=
        (Complex.normSq_pos).2 hden_ne
      have him' :
          ((-1 : ℂ) / ((t : ℂ) + Complex.I)).im =
            (1 : ℝ) / Complex.normSq ((t : ℂ) + Complex.I) := by
        simp [div_eq_mul_inv, Complex.inv_im]
      have : 0 < (1 : ℝ) / Complex.normSq ((t : ℂ) + Complex.I) := one_div_pos.2 hnormSq_pos
      simpa [w, hz2, him'] using! this
    -- Apply the compactness helper.
    simpa [w] using! (exists_bound_norm_varphi'_comp_Icc (w := w) hw him)
  rcases hvarphi_bound with ⟨Mφ, hMφ⟩
  have hMφ0 : 0 ≤ Mφ := by
    have h := hMφ 0 (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    exact (norm_nonneg _).trans h
  let Cbase : ℝ := Mφ * (1024 : ℝ)
  have hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base t‖ ≤ Cbase := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := mem_Icc_of_mem_Ι ht
    have hvar : ‖varphi' (-1 / (z₂' t + 1))‖ ≤ Mφ := hMφ t htIcc
    have hz2 : z₂' t + 1 = (t : ℂ) + Complex.I := by
      simp [MagicFunction.Parametrisations.z₂'_eq_of_mem (t := t) htIcc, add_left_comm, add_comm]
    have ht0 : 0 ≤ t := htIcc.1
    have ht1 : t ≤ 1 := htIcc.2
    have hz_norm : ‖(t : ℂ) + Complex.I‖ ≤ (2 : ℝ) := by
      have ht_abs : ‖(t : ℂ)‖ ≤ 1 := by simpa [Complex.norm_real, abs_of_nonneg ht0] using! ht1
      have htri : ‖(t : ℂ) + Complex.I‖ ≤ ‖(t : ℂ)‖ + ‖(Complex.I : ℂ)‖ := norm_add_le _ _
      have hle : ‖(t : ℂ) + Complex.I‖ ≤ (1 : ℝ) + 1 :=
        le_trans htri (add_le_add ht_abs (by simp))
      simpa [show (1 : ℝ) + 1 = 2 by norm_num] using! hle
    have hpow : ‖(z₂' t + 1) ^ (10 : ℕ)‖ ≤ (1024 : ℝ) := by
      have hpow' : ‖((t : ℂ) + Complex.I) ^ (10 : ℕ)‖ ≤ (2 : ℝ) ^ (10 : ℕ) := by
        simpa [norm_pow] using! pow_le_pow_left₀ (norm_nonneg _) hz_norm 10
      simpa [hz2] using! (le_trans hpow' (by norm_num))
    exact norm_mul_le_of_le (hMφ t htIcc) hpow
  refine
    differentiableAt_intervalIntegral_mul_expU_of_eq_of_measurable
      (base := base) (z := z) u0 Cbase (2 : ℝ) hbase hz hbase_bound hz_bound ?_
  funext u
  simp [I₂', Φ₂, Φ₂', Φ₁', base, z, mul_assoc, mul_comm]

/-- Differentiability of the contour piece `I₃'` in the complex parameter. -/
public lemma differentiableAt_I₃' (u0 : ℂ) : DifferentiableAt ℂ I₃' u0 := by
  let base : ℝ → ℂ :=
    fun t : ℝ => (Complex.I : ℂ) * (varphi' (-1 / (z₃' t - 1)) * (z₃' t - 1) ^ (10 : ℕ))
  let z : ℝ → ℂ := fun t : ℝ => z₃' t
  have hz : Continuous z := by
    fun_prop [MagicFunction.Parametrisations.z₃', MagicFunction.Parametrisations.z₃]
  have hbase : Measurable base := by
    have hz_meas : Measurable z := hz.measurable
    have hvar : Measurable fun t : ℝ => varphi' (-1 / (z t - 1)) :=
      measurable_varphi'.comp (measurable_const.div (hz_meas.sub measurable_const))
    have hpow : Measurable fun t : ℝ => (z t - 1) ^ (10 : ℕ) :=
      (hz_meas.sub measurable_const).pow_const _
    have hmul : Measurable fun t : ℝ =>
        varphi' (-1 / (z t - 1)) * (z t - 1) ^ (10 : ℕ) :=
      hvar.mul hpow
    dsimp [base]
    exact measurable_const.mul hmul
  rcases bound_base_I₃' with ⟨Cbase, hCbase⟩
  have hz_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖z t‖ ≤ (2 : ℝ) := A.norm_z₃'_le
  have hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base t‖ ≤ Cbase := by
    intro t ht; simpa [base] using! hCbase t ht
  refine
    differentiableAt_intervalIntegral_mul_expU_of_eq_of_measurable
      (base := base) (z := z) u0 Cbase (2 : ℝ) hbase hz hbase_bound hz_bound ?_
  funext u
  simp [I₃', Φ₃, Φ₃', base, z, mul_assoc, mul_comm]

/-- Differentiability of the contour piece `I₄'` in the complex parameter. -/
public lemma differentiableAt_I₄' (u0 : ℂ) : DifferentiableAt ℂ I₄' u0 := by
  let base : ℝ → ℂ :=
    fun t : ℝ => (-1 : ℂ) * (varphi' (-1 / (z₄' t - 1)) * (z₄' t - 1) ^ (10 : ℕ))
  let z : ℝ → ℂ := fun t : ℝ => z₄' t
  have hz : Continuous z := by
    fun_prop [MagicFunction.Parametrisations.z₄', MagicFunction.Parametrisations.z₄]
  have hbase : Measurable base := by
    have hz_meas : Measurable z := hz.measurable
    have hvar : Measurable fun t : ℝ => varphi' (-1 / (z t - 1)) :=
      measurable_varphi'.comp (measurable_const.div (hz_meas.sub measurable_const))
    have hpow : Measurable fun t : ℝ => (z t - 1) ^ (10 : ℕ) :=
      (hz_meas.sub measurable_const).pow_const _
    have hmul : Measurable fun t : ℝ =>
        varphi' (-1 / (z t - 1)) * (z t - 1) ^ (10 : ℕ) :=
      hvar.mul hpow
    dsimp [base]
    exact measurable_const.mul hmul
  have hz_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖z t‖ ≤ (2 : ℝ) := fun t _ => A.norm_z₄'_le t
  have hvarphi_bound :
      ∃ M : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖varphi' (-1 / (z₄' t - 1))‖ ≤ M := by
    let w : ℝ → ℂ := fun t => (-1 : ℂ) / (z₄' t - 1)
    have hw : ContinuousOn w (Set.Icc (0 : ℝ) 1) := by
      have hz : Continuous fun t : ℝ => z₄' t := by
        fun_prop [MagicFunction.Parametrisations.z₄', MagicFunction.Parametrisations.z₄]
      have hden : Continuous fun t : ℝ => z₄' t - 1 := hz.sub continuous_const
      have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, z₄' t - 1 ≠ 0 := by
        intro t ht
        have hz4 : z₄' t - 1 = (-(t : ℂ)) + Complex.I := by
          simp [
            MagicFunction.Parametrisations.z₄'_eq_of_mem (t := t) ht,
            sub_eq_add_neg,
            add_assoc,
            add_comm
          ]
        intro hEq
        have hEq' : ((-(t : ℂ)) + Complex.I) = 0 := by simpa [hz4] using! hEq
        have : ((-(t : ℂ)) + Complex.I).im = (0 : ℂ).im := congrArg Complex.im hEq'
        simp at this
      have hnum : ContinuousOn (fun _t : ℝ => (-1 : ℂ)) (Set.Icc (0 : ℝ) 1) := continuousOn_const
      have hdenOn : ContinuousOn (fun t : ℝ => z₄' t - 1) (Set.Icc (0 : ℝ) 1) := hden.continuousOn
      simpa [w] using! hnum.div hdenOn hne
    have him : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < (w t).im := by
      intro t ht
      have hz4 : z₄' t - 1 = (-(t : ℂ)) + Complex.I := by
        simp [
          MagicFunction.Parametrisations.z₄'_eq_of_mem (t := t) ht,
          sub_eq_add_neg,
          add_assoc,
          add_comm
        ]
      have hden_ne : (-(t : ℂ)) + Complex.I ≠ 0 := by
        intro hEq
        have : ((-(t : ℂ)) + Complex.I).im = (0 : ℂ).im := congrArg Complex.im hEq
        simp at this
      have hnormSq_pos : 0 < Complex.normSq ((-(t : ℂ)) + Complex.I) :=
        (Complex.normSq_pos).2 hden_ne
      have him' :
          ((-1 : ℂ) / ((-(t : ℂ)) + Complex.I)).im =
            (1 : ℝ) / Complex.normSq ((-(t : ℂ)) + Complex.I) := by
        simp [div_eq_mul_inv, Complex.inv_im]
      have : 0 < (1 : ℝ) / Complex.normSq ((-(t : ℂ)) + Complex.I) := one_div_pos.2 hnormSq_pos
      simpa [w, hz4, him'] using! this
    simpa [w] using! (exists_bound_norm_varphi'_comp_Icc (w := w) hw him)
  rcases hvarphi_bound with ⟨Mφ, hMφ⟩
  have hMφ0 : 0 ≤ Mφ := by
    have h := hMφ 0 (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    exact (norm_nonneg _).trans h
  let Cbase : ℝ := Mφ * (1024 : ℝ)
  have hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base t‖ ≤ Cbase := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := mem_Icc_of_mem_Ι ht
    have hvar : ‖varphi' (-1 / (z₄' t - 1))‖ ≤ Mφ := hMφ t htIcc
    have hz4 : z₄' t - 1 = (-(t : ℂ)) + Complex.I := by
      simp [
        MagicFunction.Parametrisations.z₄'_eq_of_mem (t := t) htIcc,
        sub_eq_add_neg,
        add_assoc,
        add_comm
      ]
    have ht0 : 0 ≤ t := htIcc.1
    have ht1 : t ≤ 1 := htIcc.2
    have hz_norm : ‖(-(t : ℂ)) + Complex.I‖ ≤ (2 : ℝ) := by
      have ht_abs : ‖(t : ℂ)‖ ≤ 1 := by simpa [Complex.norm_real, abs_of_nonneg ht0] using! ht1
      have htri : ‖(-(t : ℂ)) + Complex.I‖ ≤ ‖-(t : ℂ)‖ + ‖(Complex.I : ℂ)‖ := norm_add_le _ _
      have ht_abs' : ‖-(t : ℂ)‖ ≤ 1 := by simpa [norm_neg] using! ht_abs
      have hle : ‖(-(t : ℂ)) + Complex.I‖ ≤ (1 : ℝ) + 1 :=
        le_trans htri (add_le_add ht_abs' (by simp))
      simpa [show (1 : ℝ) + 1 = 2 by norm_num] using! hle
    have hpow : ‖(z₄' t - 1) ^ (10 : ℕ)‖ ≤ (1024 : ℝ) := by
      have hpow' : ‖((-(t : ℂ)) + Complex.I) ^ (10 : ℕ)‖ ≤ (2 : ℝ) ^ (10 : ℕ) := by
        simpa [norm_pow] using! pow_le_pow_left₀ (norm_nonneg _) hz_norm 10
      simpa [hz4] using! (le_trans hpow' (by norm_num))
    calc
      ‖base t‖ ≤ ‖varphi' (-1 / (z₄' t - 1))‖ * ‖(z₄' t - 1) ^ (10 : ℕ)‖ := by
        simp [base]
      _ ≤ Mφ * (1024 : ℝ) :=
        mul_le_mul hvar hpow (by positivity) hMφ0
      _ = Cbase := by simp [Cbase]
  refine
    differentiableAt_intervalIntegral_mul_expU_of_eq_of_measurable
      (base := base) (z := z) u0 Cbase (2 : ℝ) hbase hz hbase_bound hz_bound ?_
  funext u
  simp [I₄', Φ₄, Φ₄', Φ₃', base, z, mul_assoc, mul_comm]

/-- Differentiability of the contour piece `I₅'` in the complex parameter. -/
public lemma differentiableAt_I₅' (u0 : ℂ) : DifferentiableAt ℂ I₅' u0 := by
  let base : ℝ → ℂ :=
    fun t : ℝ => (Complex.I : ℂ) * (varphi' (-1 / z₅' t) * (z₅' t) ^ (10 : ℕ))
  let z : ℝ → ℂ := fun t : ℝ => z₅' t
  have hz : Continuous z := by
    fun_prop [MagicFunction.Parametrisations.z₅', MagicFunction.Parametrisations.z₅]
  have hbase : Measurable base := by
    have hz_meas : Measurable z := hz.measurable
    have hvar : Measurable fun t : ℝ => varphi' (-1 / z t) :=
      measurable_varphi'.comp (measurable_const.div hz_meas)
    have hpow : Measurable fun t : ℝ => (z t) ^ (10 : ℕ) := hz_meas.pow_const _
    have hmul : Measurable fun t : ℝ => varphi' (-1 / z t) * (z t) ^ (10 : ℕ) := hvar.mul hpow
    simpa [base, mul_assoc] using! measurable_const.mul hmul
  rcases bound_base_I₅' with ⟨Cbase0, hCbase0⟩
  have hz_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖z t‖ ≤ (1 : ℝ) := fun t _ => A.norm_z₅'_le t
  have hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base t‖ ≤ Cbase0 := by
    intro t ht; simpa [base] using! hCbase0 t ht
  have hdiffΦ : DifferentiableAt ℂ (fun u : ℂ => ∫ t in (0 : ℝ)..1, Φ₅ u t) u0 := by
    refine
      differentiableAt_intervalIntegral_mul_expU_of_eq_of_measurable
        (base := base) (z := z) u0 Cbase0 (1 : ℝ) hbase hz hbase_bound hz_bound ?_
    funext u
    simp [Φ₅, Φ₅', base, z, mul_assoc, mul_comm]
  have hdiffI :
      DifferentiableAt ℂ (fun u : ℂ => (-2 : ℂ) * (∫ t in (0 : ℝ)..1, Φ₅ u t)) u0 :=
    hdiffΦ.const_mul (-2 : ℂ)
  -- Rewrite the goal with the scalar factor pulled out.
  change DifferentiableAt ℂ (fun u : ℂ => (-2 : ℂ) * (∫ t in (0 : ℝ)..1, Φ₅ u t)) u0
  exact hdiffI

end ProfileComplex.A
end

end SpherePacking.Dim24
