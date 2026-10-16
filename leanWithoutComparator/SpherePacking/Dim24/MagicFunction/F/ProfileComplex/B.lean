-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import SpherePacking.Dim24.MagicFunction.B.Defs.J5Smooth
public import SpherePacking.Dim24.MagicFunction.F.ProfileComplex.A3

/-!
# Analyticity of `bPrimeC` on the right half-plane

This file proves holomorphy of the complexified `b'` profile `ProfileComplex.B.bPrimeC` on the
right half-plane. The bounded-interval pieces `J₁'`-`J₅'` are treated by differentiating under an
interval integral, while the tail piece `J₆'` is handled separately.
-/

namespace SpherePacking.Dim24

noncomputable section

open scoped Interval Topology UpperHalfPlane

open Complex Real MeasureTheory
open MagicFunction.Parametrisations intervalIntegral

namespace ProfileComplex

/-! ### Basic measurability for `ψ*'` -/

lemma measurable_ψT' : Measurable (ψT' : ℂ → ℂ) := by
  let s : Set ℂ := {z : ℂ | 0 < z.im}
  have hs : MeasurableSet s := by
    simpa [s] using!
      (isOpen_lt
          (continuous_const : Continuous fun _ : ℂ => (0 : ℝ))
          Complex.continuous_im).measurableSet
  have hcont_mk : Continuous fun z : s => (⟨(z : ℂ), z.property⟩ : ℍ) :=
    by
      simpa using! Continuous.upperHalfPlaneMk continuous_subtype_val (fun z => z.property)
  have hf : Measurable fun z : s => ψT (⟨(z : ℂ), z.property⟩ : ℍ) :=
    ((SpherePacking.Dim24.continuous_ψT).comp hcont_mk).measurable
  have hg : Measurable fun _z : (sᶜ : Set ℂ) => (0 : ℂ) := measurable_const
  simpa [ψT', s] using! (Measurable.dite (s := s) hf hg hs)

lemma measurable_ψI' : Measurable (ψI' : ℂ → ℂ) := by
  let s : Set ℂ := {z : ℂ | 0 < z.im}
  have hs : MeasurableSet s := by
    simpa [s] using!
      (isOpen_lt
          (continuous_const : Continuous fun _ : ℂ => (0 : ℝ))
          Complex.continuous_im).measurableSet
  have hcont_mk : Continuous fun z : s => (⟨(z : ℂ), z.property⟩ : ℍ) :=
    by
      simpa using! Continuous.upperHalfPlaneMk continuous_subtype_val (fun z => z.property)
  have hf : Measurable fun z : s => ψI (⟨(z : ℂ), z.property⟩ : ℍ) := by
    exact ((SpherePacking.Dim24.continuous_ψI).comp hcont_mk).measurable
  have hg : Measurable fun _z : (sᶜ : Set ℂ) => (0 : ℂ) := measurable_const
  simpa [ψI', s] using! (Measurable.dite (s := s) hf hg hs)

namespace B

open scoped Interval
open SpecialValuesAux

/-! ### Uniform bound for `ψI'(z₅' t)` on `Ι 0 1` -/

noncomputable def Cψ : ℝ :=
  Classical.choose PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_Ici_one

lemma hCψ (t : ℝ) (ht : 1 ≤ t) : ‖ψS.resToImagAxis t‖ ≤ Cψ :=
  (Classical.choose_spec PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_Ici_one) t ht

lemma Cψ_nonneg : 0 ≤ Cψ := by
  have h := hCψ (t := (1 : ℝ)) (le_rfl : (1 : ℝ) ≤ 1)
  exact (norm_nonneg _).trans h

lemma norm_ψI'_z₅'_le (t : ℝ) (ht : t ∈ Ι (0 : ℝ) 1) : ‖ψI' (z₅' t)‖ ≤ Cψ := by
  have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := mem_Ioc_of_mem_Ι ht
  have ht0 : 0 < t := htIoc.1
  have ht1 : t ≤ 1 := htIoc.2
  have hone : (1 : ℝ) ≤ 1 / t := by simpa using! (one_le_one_div ht0 ht1)
  have hEq := Schwartz.J5Smooth.ψI'_z₅'_eq (t := t) htIoc
  -- Bound `ψS.resToImagAxis (1/t)` and the power factor.
  have hψS : ‖ψS.resToImagAxis (1 / t)‖ ≤ Cψ := hCψ (t := 1 / t) hone
  have ht0' : 0 ≤ t := le_of_lt ht0
  have hpow : ‖((Complex.I : ℂ) * (t : ℂ)) ^ (10 : ℕ)‖ ≤ (1 : ℝ) := by
    have ht_abs : ‖(Complex.I : ℂ) * (t : ℂ)‖ ≤ (1 : ℝ) := by
      have ht_abs' : |t| ≤ (1 : ℝ) := by simpa [abs_of_nonneg ht0'] using! ht1
      simpa [norm_mul, Complex.norm_real] using! ht_abs'
    have ht_le_one : ‖(Complex.I : ℂ) * (t : ℂ)‖ ≤ (1 : ℝ) := ht_abs
    have := pow_le_pow_left₀ (norm_nonneg ((Complex.I : ℂ) * (t : ℂ))) ht_le_one 10
    simpa [norm_pow] using! this
  -- Combine.
  have : ‖ψI' (z₅' t)‖ ≤ Cψ := by
    calc
      ‖ψI' (z₅' t)‖ = ‖ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (10 : ℕ)‖ := by
          simp [hEq]
      _ ≤ ‖ψS.resToImagAxis (1 / t)‖ * ‖((Complex.I : ℂ) * (t : ℂ)) ^ (10 : ℕ)‖ := norm_mul_le _ _
      _ ≤ Cψ * 1 :=
            mul_le_mul hψS hpow (norm_nonneg _) Cψ_nonneg
      _ = Cψ := by simp
  exact this

/-! ### Boundedness of the base factors (no `expU`) -/

lemma bound_base_J₁' :
    ∃ C : ℝ, ∀ t ∈ Ι (0 : ℝ) 1, ‖(Complex.I : ℂ) * ψT' (z₁' t)‖ ≤ C := by
  refine ⟨Cψ, ?_⟩
  intro t ht
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := mem_Icc_of_mem_Ι ht
  have hψ : ψT' (z₁' t) = ψI' (z₅' t) := ψT'_z₁'_eq_ψI'_z₅' (t := t) htIcc
  have hbound : ‖ψT' (z₁' t)‖ ≤ Cψ := by simpa [hψ] using! norm_ψI'_z₅'_le (t := t) (ht := ht)
  simpa

lemma bound_base_J₃' :
    ∃ C : ℝ, ∀ t ∈ Ι (0 : ℝ) 1, ‖(Complex.I : ℂ) * ψT' (z₃' t)‖ ≤ C := by
  refine ⟨Cψ, ?_⟩
  intro t ht
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := mem_Icc_of_mem_Ι ht
  have hψ : ψT' (z₃' t) = ψI' (z₅' t) :=
    SpherePacking.Dim24.Schwartz.J3Smooth.ψT'_z₃'_eq_ψI'_z₅' (t := t) htIcc
  have hbound : ‖ψT' (z₃' t)‖ ≤ Cψ := by simpa [hψ] using! norm_ψI'_z₅'_le (t := t) (ht := ht)
  simpa

lemma bound_base_J₅_inner :
    ∃ C : ℝ, ∀ t ∈ Ι (0 : ℝ) 1, ‖(Complex.I : ℂ) * ψI' (z₅' t)‖ ≤ C := by
  refine ⟨Cψ, ?_⟩
  intro t ht
  have hbound : ‖ψI' (z₅' t)‖ ≤ Cψ := norm_ψI'_z₅'_le (t := t) ht
  simpa

/-! ### Compactness bounds for the horizontal pieces (`z₂'` and `z₄'`) -/

lemma exists_bound_norm_ψI'_add_I :
    ∃ M : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖ψI' ((t : ℂ) + Complex.I)‖ ≤ M := by
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  -- Build a continuous map into `ℍ`.
  let φ : s → ℍ := fun t =>
    (⟨((t : ℝ) : ℂ) + Complex.I, by simp⟩ : ℍ)
  have hφ : Continuous φ := by
    fun_prop
  have hEq : (fun t : s => ψI' (((t : ℝ) : ℂ) + Complex.I)) = fun t : s => ψI (φ t) := by
    funext t
    have hz : 0 < ((((t : ℝ) : ℂ) + Complex.I).im) := by simp
    simp [ψI', φ]
  have hcont : Continuous fun t : s => ψI' (((t : ℝ) : ℂ) + Complex.I) := by
    simpa [hEq] using! (SpherePacking.Dim24.continuous_ψI).comp hφ
  have hcont_norm : Continuous fun t : s => ‖ψI' (((t : ℝ) : ℂ) + Complex.I)‖ := hcont.norm
  have hcontOn :
      ContinuousOn (fun t : ℝ => ‖ψI' ((t : ℂ) + Complex.I)‖) s := by
    simpa [s] using! (continuousOn_iff_continuous_restrict.2 hcont_norm)
  have hs : IsCompact s := isCompact_Icc
  have hne : s.Nonempty := ⟨0, by simp [s]⟩
  obtain ⟨t0, ht0, ht0max⟩ := hs.exists_isMaxOn hne hcontOn
  refine ⟨‖ψI' ((t0 : ℂ) + Complex.I)‖, ?_⟩
  intro t ht
  exact ht0max ht

lemma bound_base_J₂' :
    ∃ C : ℝ, ∀ t ∈ Ι (0 : ℝ) 1, ‖ψT' (z₂' t)‖ ≤ C := by
  -- Use `ψT'(z₂' t) = ψI'(t + I)` and bound by compactness on `Icc 0 1`.
  rcases exists_bound_norm_ψI'_add_I with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro t ht
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := mem_Icc_of_mem_Ι ht
  have hψ : ψT' (z₂' t) = ψI' ((t : ℂ) + Complex.I) :=
    ψT'_z₂'_eq_ψI'_add_one (t := t) htIcc
  simpa [hψ] using! hM t htIcc

lemma bound_base_J₄' :
    ∃ C : ℝ, ∀ t ∈ Ι (0 : ℝ) 1, ‖(-1 : ℂ) * ψT' (z₄' t)‖ ≤ C := by
  -- Bound `ψT'(z₄' t)` by compactness via rewriting to `ψI'((-t)+I)` (and absorb `-1` in the norm).
  -- We use continuity/compactness directly on the function `t ↦ ψT'(z₄' t)`.
  let f : ℝ → ℝ := fun t => ‖ψT' (z₄' t)‖
  have hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    -- On `Icc 0 1`, `z₄' t` stays in the upper half-plane (`im = 1`), so `ψT'` agrees with `ψT`.
    let φ : Set.Icc (0 : ℝ) 1 → ℍ := fun t =>
      (⟨z₄' (t : ℝ), by
        exact im_z₄'_pos_all ↑t⟩ : ℍ)
    have hφ : Continuous φ := by
      have hz : Continuous fun t : Set.Icc (0 : ℝ) 1 => z₄' (t : ℝ) := by
        have : Continuous fun t : ℝ => z₄' t := by
          fun_prop [MagicFunction.Parametrisations.z₄', MagicFunction.Parametrisations.z₄]
        exact this.comp continuous_subtype_val
      fun_prop
    have hEq : (fun t : Set.Icc (0 : ℝ) 1 => ψT' (z₄' (t : ℝ))) = fun t => ψT (φ t) := by
      funext t
      have hz : 0 < (z₄' (t : ℝ)).im := by
        simp [MagicFunction.Parametrisations.z₄'_eq_of_mem (t := (t : ℝ)) t.property]
      have hsub : (⟨z₄' (t : ℝ), hz⟩ : ℍ) = φ t := by
        ext
        rfl
      simp [ψT', hz, hsub]
    have hψ : Continuous fun t : Set.Icc (0 : ℝ) 1 => ψT' (z₄' (t : ℝ)) := by
      simpa [hEq] using! (SpherePacking.Dim24.continuous_ψT).comp hφ
    -- Convert to `ContinuousOn` on `Icc` and take norms.
    simpa [f] using! (continuousOn_iff_continuous_restrict.2 hψ.norm)
  have hs : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  have hne : (Set.Icc (0 : ℝ) 1).Nonempty := ⟨0, by norm_num⟩
  obtain ⟨t0, ht0, ht0max⟩ := hs.exists_isMaxOn hne hcont
  refine ⟨‖ψT' (z₄' t0)‖, ?_⟩
  intro t ht
  have hmain : ‖ψT' (z₄' t)‖ ≤ ‖ψT' (z₄' t0)‖ :=
    ht0max (mem_Icc_of_mem_Ι ht)
  -- Multiply by `-1` does not change the norm.
  simpa [norm_mul] using! hmain

/-! ### Differentiability of the finite pieces -/

lemma differentiableAt_J₁' (u0 : ℂ) : DifferentiableAt ℂ J₁' u0 := by
  let base : ℝ → ℂ := fun t : ℝ => (Complex.I : ℂ) * ψT' (z₁' t)
  let z : ℝ → ℂ := fun t : ℝ => z₁' t
  have hz : Continuous z := by
    fun_prop [MagicFunction.Parametrisations.z₁', MagicFunction.Parametrisations.z₁]
  have hbase : Measurable base := by
    have hψ : Measurable fun t : ℝ => ψT' (z t) := measurable_ψT'.comp hz.measurable
    simpa [base, mul_assoc] using! measurable_const.mul hψ
  rcases bound_base_J₁' with ⟨Cbase, hCbase⟩
  have hz_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖z t‖ ≤ (2 : ℝ) := fun t _ => A.norm_z₁'_le t
  have hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base t‖ ≤ Cbase := by
    intro t ht; simpa [base] using! hCbase t ht
  refine
    differentiableAt_intervalIntegral_mul_expU_of_eq_of_measurable
      (base := base) (z := z) u0 Cbase (2 : ℝ) hbase hz hbase_bound hz_bound ?_
  funext u
  simp [J₁', base, z]

lemma differentiableAt_J₂' (u0 : ℂ) : DifferentiableAt ℂ J₂' u0 := by
  let base : ℝ → ℂ := fun t : ℝ => ψT' (z₂' t)
  let z : ℝ → ℂ := fun t : ℝ => z₂' t
  have hz : Continuous z := by
    fun_prop [MagicFunction.Parametrisations.z₂', MagicFunction.Parametrisations.z₂]
  have hbase : Measurable base := by
    simpa [base] using! measurable_ψT'.comp hz.measurable
  rcases bound_base_J₂' with ⟨Cbase, hCbase⟩
  have hz_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖z t‖ ≤ (2 : ℝ) := fun t _ => A.norm_z₂'_le t
  have hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base t‖ ≤ Cbase := by
    intro t ht; simpa [base] using! hCbase t ht
  refine
    differentiableAt_intervalIntegral_mul_expU_of_eq_of_measurable
      (base := base) (z := z) u0 Cbase (2 : ℝ) hbase hz hbase_bound hz_bound ?_
  funext u
  simp [J₂', base, z]

lemma differentiableAt_J₃' (u0 : ℂ) : DifferentiableAt ℂ J₃' u0 := by
  let base : ℝ → ℂ := fun t : ℝ => (Complex.I : ℂ) * ψT' (z₃' t)
  let z : ℝ → ℂ := fun t : ℝ => z₃' t
  have hz : Continuous z := by
    fun_prop [MagicFunction.Parametrisations.z₃', MagicFunction.Parametrisations.z₃]
  have hbase : Measurable base := by
    have hψ : Measurable fun t : ℝ => ψT' (z t) := measurable_ψT'.comp hz.measurable
    simpa [base, mul_assoc] using! measurable_const.mul hψ
  rcases bound_base_J₃' with ⟨Cbase, hCbase⟩
  have hz_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖z t‖ ≤ (2 : ℝ) := A.norm_z₃'_le
  have hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base t‖ ≤ Cbase := by
    intro t ht; simpa [base] using! hCbase t ht
  refine
    differentiableAt_intervalIntegral_mul_expU_of_eq_of_measurable
      (base := base) (z := z) u0 Cbase (2 : ℝ) hbase hz hbase_bound hz_bound ?_
  funext u
  simp [J₃', base, z]

lemma differentiableAt_J₄' (u0 : ℂ) : DifferentiableAt ℂ J₄' u0 := by
  let base : ℝ → ℂ := fun t : ℝ => (-1 : ℂ) * ψT' (z₄' t)
  let z : ℝ → ℂ := fun t : ℝ => z₄' t
  have hz : Continuous z := by
    fun_prop [MagicFunction.Parametrisations.z₄', MagicFunction.Parametrisations.z₄]
  have hbase : Measurable base := by
    have hψ : Measurable fun t : ℝ => ψT' (z t) := measurable_ψT'.comp hz.measurable
    dsimp [base]
    exact measurable_const.mul hψ
  rcases bound_base_J₄' with ⟨Cbase, hCbase⟩
  have hz_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖z t‖ ≤ (2 : ℝ) := fun t _ => A.norm_z₄'_le t
  have hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base t‖ ≤ Cbase := by
    intro t ht; simpa [base] using! hCbase t ht
  refine
    differentiableAt_intervalIntegral_mul_expU_of_eq_of_measurable
      (base := base) (z := z) u0 Cbase (2 : ℝ) hbase hz hbase_bound hz_bound ?_
  funext u
  simp [J₄', base, z]

lemma differentiableAt_J₅' (u0 : ℂ) : DifferentiableAt ℂ J₅' u0 := by
  let base : ℝ → ℂ := fun t : ℝ => (Complex.I : ℂ) * ψI' (z₅' t)
  let z : ℝ → ℂ := fun t : ℝ => z₅' t
  have hz : Continuous z := by
    fun_prop [MagicFunction.Parametrisations.z₅', MagicFunction.Parametrisations.z₅]
  have hbase : Measurable base := by
    have hψ : Measurable fun t : ℝ => ψI' (z t) := measurable_ψI'.comp hz.measurable
    simpa [base, mul_assoc] using! measurable_const.mul hψ
  rcases bound_base_J₅_inner with ⟨Cbase0, hCbase0⟩
  have hz_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖z t‖ ≤ (1 : ℝ) := fun t _ => A.norm_z₅'_le t
  have hbase_bound : ∀ t ∈ Ι (0 : ℝ) 1, ‖base t‖ ≤ Cbase0 := by
    intro t ht; simpa [base] using! hCbase0 t ht
  have hdiffΦ :
      DifferentiableAt ℂ
        (fun u : ℂ =>
          ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) * expU u (z₅' t)) u0 :=
    differentiableAt_intervalIntegral_mul_expU_of_eq_of_measurable u0 Cbase0 1 hbase hz hCbase0
          hz_bound rfl
  have hdiffI :
      DifferentiableAt ℂ (fun u : ℂ => (-2 : ℂ) * (∫ t in (0 : ℝ)..1,
        (Complex.I : ℂ) * ψI' (z₅' t) * expU u (z₅' t))) u0 :=
    hdiffΦ.const_mul (-2 : ℂ)
  -- `J₅'` has an outer factor `-2`.
  assumption

end ProfileComplex.B
end

end SpherePacking.Dim24
/-
Differentiability of the tail (`J₆'`) of the complexified `b'` profile.

This mirrors the argument for the complexified `a'` profile.
-/

open scoped Interval Topology UpperHalfPlane

open Complex Real MeasureTheory
open MagicFunction.Parametrisations intervalIntegral

namespace SpherePacking.Dim24

noncomputable section

namespace ProfileComplex

/-! ### Small real-analysis helpers -/

/-! ### Measurability of the imaginary-axis restriction -/

lemma measurable_ψS_resToImagAxis : Measurable (ψS.resToImagAxis : ℝ → ℂ) := by
  let s : Set ℝ := {t : ℝ | 0 < t}
  have hs : MeasurableSet s := by
    simpa [s] using!
      (isOpen_lt (continuous_const : Continuous fun _ : ℝ => (0 : ℝ)) continuous_id).measurableSet
  have hcont_mk :
      Continuous fun t : s => (⟨(Complex.I : ℂ) * ((t : ℝ) : ℂ), by
        have ht : 0 < (t : ℝ) := t.property
        simpa [Complex.mul_im] using! ht⟩ : ℍ) := by
    fun_prop
  have hf : Measurable fun t : s => ψS (⟨(Complex.I : ℂ) * ((t : ℝ) : ℂ), by
      have ht : 0 < (t : ℝ) := t.property
      simpa [Complex.mul_im] using! ht⟩ : ℍ) :=
    ((SpherePacking.Dim24.PsiRewrites.continuous_ψS).comp hcont_mk).measurable
  have hg : Measurable fun _t : (sᶜ : Set ℝ) => (0 : ℂ) := measurable_const
  simpa [Function.resToImagAxis, Function.resToImagAxis_eq_resToImagAxis, ResToImagAxis, s] using!
    (Measurable.dite (s := s) hf hg hs)

/-! ### Tail integral as a Laplace transform and differentiability -/

namespace B

open scoped Topology

noncomputable def bTailIntegrandCoreC (u : ℂ) (t : ℝ) : ℂ :=
  (Complex.I : ℂ) * ψS.resToImagAxis t * Complex.exp (-(π : ℂ) * u * (t : ℂ))

noncomputable def bTailIntegralCoreC (u : ℂ) : ℂ :=
  ∫ t in Set.Ici (1 : ℝ), bTailIntegrandCoreC u t

lemma J₆'_eq_const_mul_bTailIntegralCoreC (u : ℂ) :
    J₆' u = (-2 : ℂ) * bTailIntegralCoreC u := by
  -- Rewrite both `ψS' (z₆' t)` and `expU u (z₆' t)` on the imaginary axis.
  have hEq :
      ∀ t ∈ Set.Ici (1 : ℝ),
        (Complex.I : ℂ) * ψS' (z₆' t) * expU u (z₆' t) =
          bTailIntegrandCoreC u t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    have hz : z₆' t = (Complex.I : ℂ) * (t : ℂ) := by
      simpa [mul_assoc] using! (MagicFunction.Parametrisations.z₆'_eq_of_mem (t := t) ht)
    have hψ : ψS' (z₆' t) = ψS.resToImagAxis t := by
      have him : 0 < (z₆' t).im := by
        simp [hz, Complex.mul_im, ht0]
      simp [ψS', Function.resToImagAxis, ResToImagAxis, ht0, hz]
    have hexp : expU u (z₆' t) = Complex.exp (-(π : ℂ) * u * (t : ℂ)) :=
      expU_z₆'_eq (u := u) (t := t) ht
    simp [bTailIntegrandCoreC, hψ, hexp, mul_assoc, mul_left_comm, mul_comm]
  have hInt :
      (∫ t in Set.Ici (1 : ℝ), (Complex.I : ℂ) * ψS' (z₆' t) * expU u (z₆' t)) =
        ∫ t in Set.Ici (1 : ℝ), bTailIntegrandCoreC u t := by
    refine MeasureTheory.integral_congr_ae ?_
    refine
      (ae_restrict_iff' (μ := (volume : Measure ℝ)) (s := Set.Ici (1 : ℝ)) measurableSet_Ici).2 ?_
    exact Filter.Eventually.of_forall (fun t ht => hEq t ht)
  unfold J₆' bTailIntegralCoreC
  simp [hInt]

/-!
### Fixed exponential bound for `ψS.resToImagAxis`

We pick a single constant `CψExp` witnessing the exponential decay bound used in the dominated
differentiation argument.
-/

noncomputable def CψExp : ℝ :=
  Classical.choose PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one

lemma hCψExp (t : ℝ) (ht : 1 ≤ t) :
    ‖ψS.resToImagAxis t‖ ≤ CψExp * Real.exp (-Real.pi * t) :=
  (Classical.choose_spec PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_exp_Ici_one) t ht

lemma CψExp_nonneg : 0 ≤ CψExp := by
  have h := hCψExp (t := (1 : ℝ)) (le_rfl : (1 : ℝ) ≤ 1)
  have hexp_pos : 0 < Real.exp (-Real.pi * (1 : ℝ)) := by positivity
  exact
    ForMathlib.nonneg_of_nonneg_le_mul (ha := norm_nonneg (ψS.resToImagAxis (1 : ℝ)))
      (hb := hexp_pos) (h := h)

/-- The measure `volume` restricted to `Set.Ici 1`, used for the tail integral `J₆'`. -/
@[expose] public noncomputable def μ : Measure ℝ :=
  (volume : Measure ℝ).restrict (Set.Ici (1 : ℝ))

attribute [irreducible] μ

lemma aestronglyMeasurable_bTailIntegrandCoreC (u : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => bTailIntegrandCoreC u t) μ := by
  have hψ : AEStronglyMeasurable (fun t : ℝ => ψS.resToImagAxis t) μ :=
    (measurable_ψS_resToImagAxis.aestronglyMeasurable)
  have hexp : AEStronglyMeasurable (fun t : ℝ => Complex.exp (-(π : ℂ) * u * (t : ℂ))) μ := by
    have hcont : Continuous fun t : ℝ => Complex.exp (-(π : ℂ) * u * (t : ℂ)) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  have hψexp :
      AEStronglyMeasurable
        (fun t : ℝ => ψS.resToImagAxis t * Complex.exp (-(π : ℂ) * u * (t : ℂ))) μ := hψ.mul hexp
  have hIψexp :
      AEStronglyMeasurable
        (fun t : ℝ =>
          (Complex.I : ℂ) * (ψS.resToImagAxis t * Complex.exp (-(π : ℂ) * u * (t : ℂ)))) μ :=
    aestronglyMeasurable_const.mul hψexp
  simpa [bTailIntegrandCoreC, mul_assoc, mul_left_comm, mul_comm] using! hIψexp

lemma integrable_bTailIntegrandCoreC {u0 : ℂ} (hu0 : u0 ∈ SpherePacking.rightHalfPlane) :
    Integrable (fun t : ℝ => bTailIntegrandCoreC u0 t) μ := by
  have hu0_re : 0 < u0.re := by simpa [SpherePacking.rightHalfPlane] using! hu0
  let r : ℝ := u0.re / 2
  have hr : 0 < r := by simpa [r] using! (half_pos hu0_re)
  have hb : 0 < Real.pi * (r + 1) := mul_pos Real.pi_pos (by linarith)
  have hbound_int :
      Integrable (fun t : ℝ => CψExp * Real.exp (-(Real.pi * (r + 1)) * t)) μ := by
    have :
        Integrable (fun t : ℝ => CψExp * Real.exp (-(Real.pi * (r + 1)) * t)) (μ := μ) := by
      simpa [μ, mul_assoc, mul_left_comm, mul_comm] using!
        (integrable_bound_exp (C := CψExp) (b := (Real.pi * (r + 1))) hb)
    exact this
  have hmeas : AEStronglyMeasurable (fun t : ℝ => bTailIntegrandCoreC u0 t) μ := by
    simpa using! (aestronglyMeasurable_bTailIntegrandCoreC (u := u0))
  refine Integrable.mono' hbound_int hmeas ?_
  have h :
      ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Ici (1 : ℝ))),
        ‖bTailIntegrandCoreC u0 t‖ ≤ CψExp * Real.exp (-(Real.pi * (r + 1)) * t) := by
    refine
      (ae_restrict_iff' (μ := (volume : Measure ℝ)) (s := Set.Ici (1 : ℝ)) measurableSet_Ici).2
        (.of_forall ?_)
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := ht
    have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht1
    have hψ : ‖ψS.resToImagAxis t‖ ≤ CψExp * Real.exp (-Real.pi * t) := hCψExp t ht1
    have hexp :
        ‖Complex.exp (-(π : ℂ) * u0 * (t : ℂ))‖ ≤ Real.exp (-(Real.pi * r) * t) := by
      have hre : u0.re - r = r := by
        dsimp [r]
        ring_nf
      have hu : (u0 : ℂ) ∈ Metric.ball u0 r := Metric.mem_ball_self hr
      simpa [hre, mul_assoc, mul_left_comm, mul_comm] using!
        (norm_exp_neg_pi_mul_le_of_mem_ball (u := u0) (u0 := u0) (r := r) hu (t := t) ht0)
    have hI : ‖(Complex.I : ℂ)‖ = 1 := by simp
    have hExp :
        Real.exp (-Real.pi * t) * Real.exp (-(Real.pi * r) * t) =
          Real.exp (-(Real.pi * (r + 1)) * t) := by
      have hx :
          (-(Real.pi * (r + 1)) * t) = (-Real.pi * t) + (-(Real.pi * r) * t) := by ring
      calc
        Real.exp (-Real.pi * t) * Real.exp (-(Real.pi * r) * t) =
            Real.exp ((-Real.pi * t) + (-(Real.pi * r) * t)) := by
              simp [Real.exp_add]
        _ = Real.exp (-(Real.pi * (r + 1)) * t) := by simp [hx]
    have hmain :
        ‖bTailIntegrandCoreC u0 t‖ ≤ CψExp * Real.exp (-(Real.pi * (r + 1)) * t) := by
      calc
        ‖bTailIntegrandCoreC u0 t‖ =
            ‖(Complex.I : ℂ)‖ * ‖ψS.resToImagAxis t‖ *
              ‖Complex.exp (-(π : ℂ) * u0 * (t : ℂ))‖ := by
                simp [bTailIntegrandCoreC, mul_left_comm, mul_comm]
        _ ≤ ‖(Complex.I : ℂ)‖ * (CψExp * Real.exp (-Real.pi * t)) *
              Real.exp (-(Real.pi * r) * t) := by
                have hI0 : 0 ≤ ‖(Complex.I : ℂ)‖ := norm_nonneg _
                have hCexp0 : 0 ≤ CψExp * Real.exp (-Real.pi * t) :=
                  mul_nonneg CψExp_nonneg (Real.exp_pos _).le
                have hI_Cexp0 :
                    0 ≤ ‖(Complex.I : ℂ)‖ * (CψExp * Real.exp (-Real.pi * t)) :=
                  mul_nonneg hI0 hCexp0
                have h1 :
                    ‖(Complex.I : ℂ)‖ * ‖ψS.resToImagAxis t‖ ≤
                      ‖(Complex.I : ℂ)‖ * (CψExp * Real.exp (-Real.pi * t)) :=
                  mul_le_mul_of_nonneg_left hψ hI0
                have h2 :
                    (‖(Complex.I : ℂ)‖ * ‖ψS.resToImagAxis t‖) *
                        ‖Complex.exp (-(π : ℂ) * u0 * (t : ℂ))‖ ≤
                      (‖(Complex.I : ℂ)‖ * (CψExp * Real.exp (-Real.pi * t))) *
                        ‖Complex.exp (-(π : ℂ) * u0 * (t : ℂ))‖ :=
                  mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
                exact le_mul_of_le_mul_of_nonneg_left h2 hexp hI_Cexp0
        _ = CψExp * (Real.exp (-Real.pi * t) * Real.exp (-(Real.pi * r) * t)) := by
              rw [hI]
              ring_nf
        _ = CψExp * Real.exp (-(Real.pi * (r + 1)) * t) := by
              simpa using! congrArg (fun x : ℝ => CψExp * x) hExp
    exact hmain
  -- Change of measures: `μ` is definitionally the restricted measure.
  simpa [μ] using! h

lemma ae_bound_bTailDeriv {u0 : ℂ} (hu0 : u0 ∈ SpherePacking.rightHalfPlane) :
    ∀ᵐ (t : ℝ) ∂μ, ∀ u ∈ Metric.ball u0 (u0.re / 2),
      ‖-((t : ℂ) * ((π : ℂ) * bTailIntegrandCoreC u t))‖ ≤
        (‖(π : ℂ)‖ * CψExp) * (t * Real.exp (-(Real.pi * (u0.re / 2 + 1)) * t)) := by
  let r : ℝ := u0.re / 2
  let ε : ℝ := r
  let bound : ℝ → ℝ :=
    fun t : ℝ => (‖(π : ℂ)‖ * CψExp) * (t * Real.exp (-(Real.pi * (r + 1)) * t))
  have hu0_re : 0 < u0.re := by simpa [SpherePacking.rightHalfPlane] using! hu0
  have hr : 0 < r := by simpa [r] using! (half_pos hu0_re)
  have h :
      ∀ᵐ (t : ℝ) ∂((volume : Measure ℝ).restrict (Set.Ici (1 : ℝ))),
        ∀ u ∈ Metric.ball u0 ε,
          ‖-((t : ℂ) * ((π : ℂ) * bTailIntegrandCoreC u t))‖ ≤ bound t := by
    refine
      (ae_restrict_iff' (μ := (volume : Measure ℝ)) (s := Set.Ici (1 : ℝ)) measurableSet_Ici).2
        (.of_forall ?_)
    intro t ht u hu
    have ht1 : (1 : ℝ) ≤ t := ht
    have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht1
    have hψ : ‖ψS.resToImagAxis t‖ ≤ CψExp * Real.exp (-Real.pi * t) := hCψExp t ht1
    have hexp :
        ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ ≤ Real.exp (-(Real.pi * r) * t) := by
      have hre : u0.re - ε = r := by dsimp [ε, r]; ring_nf
      have hle := norm_exp_neg_pi_mul_le_of_mem_ball (u := u) (u0 := u0) (r := ε) hu (t := t) ht0
      simpa [hre, mul_assoc, mul_left_comm, mul_comm] using! hle
    have hI : ‖(Complex.I : ℂ)‖ = 1 := by simp
    have hExp :
        Real.exp (-Real.pi * t) * Real.exp (-(Real.pi * r) * t) =
          Real.exp (-(Real.pi * (r + 1)) * t) := by
      have hx :
          (-(Real.pi * (r + 1)) * t) = (-Real.pi * t) + (-(Real.pi * r) * t) := by ring
      calc
        Real.exp (-Real.pi * t) * Real.exp (-(Real.pi * r) * t) =
            Real.exp ((-Real.pi * t) + (-(Real.pi * r) * t)) := by
              simp [Real.exp_add]
        _ = Real.exp (-(Real.pi * (r + 1)) * t) := by simp [hx]
    have hF_le :
        ‖bTailIntegrandCoreC u t‖ ≤ CψExp * Real.exp (-(Real.pi * (r + 1)) * t) := by
      calc
        ‖bTailIntegrandCoreC u t‖ =
            ‖(Complex.I : ℂ)‖ * ‖ψS.resToImagAxis t‖ *
              ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ := by
                simp [bTailIntegrandCoreC, mul_left_comm, mul_comm]
        _ ≤ ‖(Complex.I : ℂ)‖ * (CψExp * Real.exp (-Real.pi * t)) *
              Real.exp (-(Real.pi * r) * t) := by
                have hI0 : 0 ≤ ‖(Complex.I : ℂ)‖ := norm_nonneg _
                have hCexp0 : 0 ≤ CψExp * Real.exp (-Real.pi * t) :=
                  mul_nonneg CψExp_nonneg (Real.exp_pos _).le
                have hI_Cexp0 :
                    0 ≤ ‖(Complex.I : ℂ)‖ * (CψExp * Real.exp (-Real.pi * t)) :=
                  mul_nonneg hI0 hCexp0
                have h1 :
                    ‖(Complex.I : ℂ)‖ * ‖ψS.resToImagAxis t‖ ≤
                      ‖(Complex.I : ℂ)‖ * (CψExp * Real.exp (-Real.pi * t)) :=
                  mul_le_mul_of_nonneg_left hψ hI0
                have h2 :
                    (‖(Complex.I : ℂ)‖ * ‖ψS.resToImagAxis t‖) *
                        ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ ≤
                      (‖(Complex.I : ℂ)‖ * (CψExp * Real.exp (-Real.pi * t))) *
                        ‖Complex.exp (-(π : ℂ) * u * (t : ℂ))‖ :=
                  mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
                exact le_mul_of_le_mul_of_nonneg_left h2 hexp hI_Cexp0
        _ = CψExp * (Real.exp (-Real.pi * t) * Real.exp (-(Real.pi * r) * t)) := by
              rw [hI]
              ring_nf
        _ = CψExp * Real.exp (-(Real.pi * (r + 1)) * t) := by
              simpa using! congrArg (fun x : ℝ => CψExp * x) hExp
    have hpi : ‖(π : ℂ)‖ = Real.pi := by
      simp [Complex.norm_real, abs_of_nonneg Real.pi_pos.le]
    calc
      ‖-((t : ℂ) * ((π : ℂ) * bTailIntegrandCoreC u t))‖ =
          ‖(π : ℂ)‖ * ‖(t : ℂ)‖ * ‖bTailIntegrandCoreC u t‖ := by
            simp [mul_assoc, mul_comm, norm_neg]
      _ ≤ ‖(π : ℂ)‖ * ‖(t : ℂ)‖ * (CψExp * Real.exp (-(Real.pi * (r + 1)) * t)) := by
            have hnonneg : 0 ≤ ‖(π : ℂ)‖ * ‖(t : ℂ)‖ :=
              mul_nonneg (norm_nonneg _) (norm_nonneg _)
            simpa [mul_assoc] using! mul_le_mul_of_nonneg_left hF_le hnonneg
      _ = bound t := by
            have htC : ‖(t : ℂ)‖ = t := by simp [Complex.norm_real, abs_of_nonneg ht0]
            dsimp [bound]
            rw [htC]
            ring_nf
  -- `μ` is definitionally the restricted measure.
  simpa [μ, ε, r, bound] using! h

lemma hasDerivAt_bTailIntegrandCoreC (u : ℂ) (t : ℝ) :
    HasDerivAt (fun z : ℂ => bTailIntegrandCoreC z t)
      (-((t : ℂ) * ((π : ℂ) * bTailIntegrandCoreC u t))) u := by
  simpa [bTailIntegrandCoreC, mul_assoc, mul_left_comm, mul_comm] using!
    (_root_.SpherePacking.Dim24.ProfileComplex.hasDerivAt_const_mul_exp_neg_pi_mul
      (c := (Complex.I : ℂ) * ψS.resToImagAxis t) (u := u) (t := t))

lemma differentiableAt_bTailIntegralCoreC {u0 : ℂ} (hu0 : u0 ∈ SpherePacking.rightHalfPlane) :
    DifferentiableAt ℂ bTailIntegralCoreC u0 := by
  have hu0_re : 0 < u0.re := by simpa [SpherePacking.rightHalfPlane] using! hu0
  let r : ℝ := u0.re / 2
  have hr : 0 < r := by simpa [r] using! (half_pos hu0_re)
  let ε : ℝ := r
  have hε : 0 < ε := by simpa [ε] using! hr
  have hb : 0 < Real.pi * (r + 1) := mul_pos Real.pi_pos (by linarith)
  let F (u : ℂ) (t : ℝ) : ℂ := bTailIntegrandCoreC u t
  let F' (u : ℂ) (t : ℝ) : ℂ := -((t : ℂ) * ((π : ℂ) * F u t))
  let bound : ℝ → ℝ :=
    fun t : ℝ => (‖(π : ℂ)‖ * CψExp) * (t * Real.exp (-(Real.pi * (r + 1)) * t))
  have hbound_int : Integrable bound μ := by
    simpa [μ, bound, mul_assoc, mul_left_comm, mul_comm] using!
      (integrable_bound_mul_exp (C := (‖(π : ℂ)‖ * CψExp)) (b := (Real.pi * (r + 1))) hb)
  have hF_meas :
      ∀ᶠ u in 𝓝 u0, AEStronglyMeasurable (fun t : ℝ => F u t) μ := by
    refine Filter.mem_of_superset (Filter.univ_mem : (Set.univ : Set ℂ) ∈ 𝓝 u0) ?_
    intro u _hu
    simpa [F] using! (aestronglyMeasurable_bTailIntegrandCoreC (u := u))
  have hF_int : Integrable (fun t : ℝ => F u0 t) μ := by
    simpa [F] using! (integrable_bTailIntegrandCoreC (u0 := u0) hu0)
  have hF'_meas : AEStronglyMeasurable (fun t : ℝ => F' u0 t) μ := by
    have hFmeas : AEStronglyMeasurable (fun t : ℝ => F u0 t) μ := by
      simpa [F] using! (aestronglyMeasurable_bTailIntegrandCoreC (u := u0))
    have ht : AEStronglyMeasurable (fun t : ℝ => (t : ℂ)) μ :=
      (Complex.continuous_ofReal.measurable.aestronglyMeasurable)
    have hpiF : AEStronglyMeasurable (fun t : ℝ => (π : ℂ) * F u0 t) μ :=
      aestronglyMeasurable_const.mul hFmeas
    have hmul : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) * ((π : ℂ) * F u0 t)) μ := ht.mul hpiF
    simpa [F'] using! hmul.neg
  have hbound :
      ∀ᵐ t ∂μ, ∀ u ∈ Metric.ball u0 ε, ‖F' u t‖ ≤ bound t := by
    simpa [F, F', bound, ε, r, μ, mul_assoc, mul_left_comm, mul_comm] using!
      (ae_bound_bTailDeriv (u0 := u0) hu0)
  have hdiff :
      ∀ᵐ t ∂μ, ∀ u ∈ Metric.ball u0 ε,
        HasDerivAt (fun z : ℂ => F z t) (F' u t) u := by
    refine Filter.Eventually.of_forall ?_
    exact fun x u a => hasDerivAt_bTailIntegrandCoreC u x
  have hderiv :
      HasDerivAt (fun z : ℂ => ∫ t, F z t ∂μ) (∫ t, F' u0 t ∂μ) u0 := by
    exact
      (_root_.SpherePacking.Dim24.ProfileComplex.hasDerivAt_integral_of_dominated_ball
        (μ := μ) (F := F) (F' := F')
        (u0 := u0) (ε := ε) (bound := bound) hε hF_meas hF_int hF'_meas hbound hbound_int hdiff)
  have hEq : (fun z : ℂ => ∫ t, F z t ∂μ) = bTailIntegralCoreC := by
    funext z
    simp [F, bTailIntegralCoreC, μ]
  simpa [hEq] using! hderiv.differentiableAt

lemma differentiableAt_J₆' {u0 : ℂ} (hu0 : u0 ∈ SpherePacking.rightHalfPlane) :
    DifferentiableAt ℂ J₆' u0 := by
  have hEq : J₆' = fun u : ℂ => (-2 : ℂ) * bTailIntegralCoreC u := by
    funext u
    simpa using! (J₆'_eq_const_mul_bTailIntegralCoreC (u := u))
  have hdiff : DifferentiableAt ℂ (fun u : ℂ => bTailIntegralCoreC u) u0 :=
    differentiableAt_bTailIntegralCoreC (u0 := u0) hu0
  simpa [hEq] using! hdiff.const_mul (-2 : ℂ)

end ProfileComplex.B
end

end SpherePacking.Dim24
/-
Holomorphy of the complexified `b'` profile `ProfileComplex.B.bPrimeC` on the right half-plane.

This section assembles the differentiability results proved above in this file.
-/

open scoped Topology

open Complex

namespace SpherePacking.Dim24

noncomputable section

namespace ProfileComplex.B
lemma differentiableAt_bPrimeC {u0 : ℂ} (hu0 : u0 ∈ SpherePacking.rightHalfPlane) :
    DifferentiableAt ℂ bPrimeC u0 := by
  simpa [bPrimeC] using!
    (((((differentiableAt_J₁' u0).add (differentiableAt_J₂' u0)).add (differentiableAt_J₃' u0)).add
            (differentiableAt_J₄' u0)).add (differentiableAt_J₅' u0)).add
      (differentiableAt_J₆' (u0 := u0) hu0)

lemma differentiableOn_bPrimeC :
    DifferentiableOn ℂ bPrimeC SpherePacking.rightHalfPlane := by
  intro u hu
  exact (differentiableAt_bPrimeC (u0 := u) hu).differentiableWithinAt

/-- The complexified profile `bPrimeC` is holomorphic on `SpherePacking.rightHalfPlane`. -/
public lemma analyticOnNhd_bPrimeC :
    AnalyticOnNhd ℂ bPrimeC SpherePacking.rightHalfPlane := by
  simpa [analyticOnNhd_iff_differentiableOn SpherePacking.rightHalfPlane_isOpen] using!
    differentiableOn_bPrimeC

end ProfileComplex.B
end

end SpherePacking.Dim24
