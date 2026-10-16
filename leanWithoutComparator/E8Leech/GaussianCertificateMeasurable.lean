import E8Leech.CKMRVKernelMeasurable

/-!
# Measurability of the actual E8 and Leech Gaussian certificate families

The chosen Schwartz witnesses agree with explicit measurable kernel integrals.
For E8 the displayed integral formula excludes the spatial origin; continuity
of each Schwartz function and a fixed sequence approaching zero fills it.
The families retain their existing value zero at the exceptional parameter π.
This file does not claim that this zero value is a certificate at π.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory Filter
open scoped Topology Manifold

/-- A measurable formula off the spatial origin and spatial continuity suffice jointly. -/
theorem measurable_family_of_formula_off_zero {d : ℕ}
    (v : Ambient d) (hv : v ≠ 0) (f : ℝ → Ambient d → ℂ)
    (hf : ∀ α, Continuous (f α)) (g : ℝ × Ambient d → ℂ) (hg : Measurable g)
    (heq : ∀ α x, x ≠ 0 → f α x = g (α, x)) :
    Measurable (fun p : ℝ × Ambient d => f p.1 p.2) := by
  let X : ℕ → Ambient d → Ambient d := fun n x =>
    if x = 0 then ((n : ℝ) + 1)⁻¹ • v else x
  have hm (n : ℕ) : Measurable (X n) :=
    Measurable.ite (measurableSet_eq_fun measurable_id measurable_const)
      measurable_const measurable_id
  have hne (n : ℕ) (x : Ambient d) : X n x ≠ 0 := by
    dsimp [X]
    split_ifs with hx
    · exact smul_ne_zero (inv_ne_zero (by positivity : (n : ℝ) + 1 ≠ 0)) hv
    · exact hx
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hlim (x : Ambient d) : Tendsto (fun n => X n x) atTop (𝓝 x) := by
    by_cases hx : x = 0
    · simp only [X, if_pos hx]
      simpa only [hx, zero_smul, Function.comp_def] using
        (tendsto_inv_atTop_zero.comp hnat).smul (tendsto_const_nhds (x := v))
    · simpa only [X, if_neg hx] using tendsto_const_nhds (x := x)
  apply measurable_of_tendsto_metrizable (f := fun n p => g (p.1, X n p.2))
    (fun n => hg.comp (measurable_fst.prodMk ((hm n).comp measurable_snd)))
  apply tendsto_pi_nhds.mpr
  intro p
  apply ((hf p.1).tendsto p.2 |>.comp (hlim p.2)).congr
  intro n
  exact heq p.1 (X n p.2) (hne n p.2)

theorem measurable_e8CertFamily (hP : E8KernelNonneg) :
    Measurable (fun p : ℝ × Ambient 8 => e8CertFamily hP p.1 p.2) := by
  let g : ℝ × Ambient 8 → ℂ := fun p =>
    if 0 < p.1 ∧ p.1 ≠ Real.pi then
      (gaussianKernel p.1 p.2 : ℂ) +
        ((4 * Real.sin (Real.pi * ‖p.2‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
          ∫ t in Ioi 0, ckmrvEightKernel (imagPt (p.1 / Real.pi)) (imagPt t) *
            (Real.exp (-(Real.pi * ‖p.2‖ ^ 2) * t) : ℂ)
    else 0
  have hi : Measurable (fun p : (ℝ × Ambient 8) × ℝ =>
      ckmrvEightKernel (imagPt (p.1.1 / Real.pi)) (imagPt p.2) *
        (Real.exp (-(Real.pi * ‖p.1.2‖ ^ 2) * p.2) : ℂ)) := by fun_prop
  have hI : Measurable (fun p : ℝ × Ambient 8 =>
      ∫ t in Ioi 0, ckmrvEightKernel (imagPt (p.1 / Real.pi)) (imagPt t) *
        (Real.exp (-(Real.pi * ‖p.2‖ ^ 2) * t) : ℂ)) :=
    hi.stronglyMeasurable.integral_prod_right'.measurable
  have hg : Measurable g := by
    dsimp [g]
    apply Measurable.ite
      ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_eq_fun measurable_fst measurable_const).compl) ?_ measurable_const
    unfold gaussianKernel
    fun_prop
  apply measurable_family_of_formula_off_zero e8Unit
    (by simpa using smul_e8Unit_ne_zero (by norm_num : (0 : ℝ) < 1))
    (fun α => e8CertFamily hP α) (fun α => (e8CertFamily hP α).continuous) g hg
  intro α x hx
  by_cases h : 0 < α ∧ α ≠ Real.pi
  · simpa only [g, if_pos h] using e8CertFamily_apply hP h.1 h.2 hx
  · simp [e8CertFamily, g, h]

theorem measurable_e8CertFamily_re (hP : E8KernelNonneg) :
    Measurable (fun p : ℝ × Ambient 8 => (e8CertFamily hP p.1 p.2).re) :=
  Complex.continuous_re.measurable.comp (measurable_e8CertFamily hP)

@[fun_prop] theorem measurable_modularE4 : Measurable (fun τ => ModularForm.E₄ τ) :=
  (ModularFormClass.continuous ModularForm.E₄).measurable

@[fun_prop] theorem measurable_modularE6 : Measurable (fun τ => ModularForm.E₆ τ) :=
  (ModularFormClass.continuous ModularForm.E₆).measurable

@[fun_prop] theorem measurable_leechMinusCusp (k : Fin 4) :
    Measurable (fun τ => leechMinusCusp τ k) := by
  fin_cases k <;> simp only [leechMinusCusp]
  all_goals
    simp only [leechMinusNZeroC, leechMinusGamma, leechMinusBeta, leechMinusAlpha]
    fun_prop

@[fun_prop] theorem measurable_leechPlusCusp (k : Fin 4) :
    Measurable (fun τ => leechPlusCusp τ k) := by
  fin_cases k <;> simp only [leechPlusCusp]
  all_goals
    simp only [leechPlusM1a, leechPlusM1c, leechPlusM0a, leechPlusM0c, leechPlusP2,
      leechPlusA0, leechPlusA1, leechPlusA2]
    fun_prop

@[fun_prop] theorem measurable_leechAxisCusp (s : ℂ) (k : Fin 4) :
    Measurable (fun β => leechAxisCusp s β k) := by
  unfold leechAxisCusp
  fun_prop

@[fun_prop] theorem measurable_leechAxisKernel (s : ℂ) :
    Measurable (fun p : ℝ × ℝ => leechAxisKernel s p.1 p.2) := by
  unfold leechAxisKernel
  fun_prop

@[fun_prop] theorem measurable_leechAxisProfile (s : ℂ) :
    Measurable (fun p : ℝ × ℝ => leechAxisProfile s p.1 p.2) := by
  unfold leechAxisProfile cuspProfile
  fun_prop

theorem measurable_leechAxisRadialProfile (s : ℂ) :
    Measurable (fun p : ℝ × ℝ => leechAxisRadialProfile s p.1 p.2) := by
  have hi : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      (leechAxisKernel s p.1.1 p.2 - leechAxisProfile s p.1.1 p.2) *
        (Real.exp (-p.1.2 * p.2) : ℂ)) := by fun_prop
  have hI : Measurable (fun p : ℝ × ℝ => ∫ t in Ioi 0,
      (leechAxisKernel s p.1 t - leechAxisProfile s p.1 t) *
        (Real.exp (-p.2 * t) : ℂ)) :=
    hi.stronglyMeasurable.integral_prod_right'.measurable
  have hsinc : Measurable Real.sinc := contDiff_sinc.continuous.measurable
  unfold leechAxisRadialProfile radialProfile cuspProfileSinc
  fun_prop

theorem measurable_leechCertFamily :
    Measurable (fun p : ℝ × Ambient 24 => leechCertFamily p.1 p.2) := by
  let g : ℝ × Ambient 24 → ℂ := fun p =>
    if 0 < p.1 ∧ p.1 ≠ Real.pi then
      (gaussianKernel p.1 p.2 : ℂ) + leechAxisRadialProfile 1 (p.1 / Real.pi)
        (Real.pi * ‖p.2‖ ^ 2)
    else 0
  have hg : Measurable g := by
    dsimp [g]
    apply Measurable.ite
      ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_eq_fun measurable_fst measurable_const).compl) ?_ measurable_const
    have hm := measurable_leechAxisRadialProfile (1 : ℂ)
    unfold gaussianKernel
    fun_prop
  have heq : (fun p : ℝ × Ambient 24 => leechCertFamily p.1 p.2) = g := by
    funext p
    by_cases h : 0 < p.1 ∧ p.1 ≠ Real.pi
    · simpa only [g, if_pos h] using leechCertFamily_apply h.1 h.2 p.2
    · simp [leechCertFamily, g, h]
  rwa [heq]

theorem measurable_leechCertFamily_re :
    Measurable (fun p : ℝ × Ambient 24 => (leechCertFamily p.1 p.2).re) :=
  Complex.continuous_re.measurable.comp measurable_leechCertFamily

end E8Leech
