-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Sign.Auxiliary
/-!
# Cohn-Elkies sign conditions for `f` (cutoff radius 2)

This file contains the final sign-condition theorems, and depends on `F.Sign.Aux`.

## Main statements
* `f_cohnElkies₁`
* `f_cohnElkies₂`
-/

namespace SpherePacking.Dim24

open scoped FourierTransform SchwartzMap ModularForm Topology

open Complex Filter MeasureTheory Real SchwartzMap

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ²⁴ ℂ)

private lemma mul_ofReal_re (z : ℂ) (r : ℝ) : (z * (r : ℂ)).re = z.re * r := by
  simp [Complex.mul_re]

/-- Cohn-Elkies sign condition: `f(x) ≤ 0` for `‖x‖ ≥ 2`. -/
public theorem f_cohnElkies₁ : ∀ x : ℝ²⁴, ‖x‖ ≥ 2 → (f x).re ≤ 0 := by
  /- Proof sketch (paper Section 4):
  Use the Laplace representation
  `f(x) = sin(π‖x‖^2/2)^2 * ∫ A(t) e^{-π‖x‖^2 t} dt`
  and show `A(t) ≤ 0` on `(0,∞)` using:
  - `varphi_imagAxis_neg` (Lemma A.1),
  - `ψS_imagAxis_nonpos` (theta expression gives `ψS(it) ≤ 0`). -/
  -- First prove the strict-radius case `2 < ‖x‖` from the Laplace representation.
  have hstrict : ∀ x : ℝ²⁴, 2 < ‖x‖ → (f x).re ≤ 0 := by
    intro x hx
    have hf := LaplaceTmp.f_eq_laplace_A (x := x) hx
    -- Abbreviate the integral term.
    set z : ℂ :=
      ∫ t in Set.Ioi (0 : ℝ), AKernel0 t * Real.exp (-Real.pi * (‖x‖ ^ 2) * t)
    -- Show the real part of the integral is nonpositive.
    have hz : z.re ≤ 0 := by
      -- Reduce to an integral of a nonpositive real-valued integrand.
      let g : ℝ → ℂ := fun t =>
        AKernel0 t * Real.exp (-Real.pi * (‖x‖ ^ 2) * t)
      by_cases hInt : Integrable g (volume.restrict (Set.Ioi (0 : ℝ)))
      · have hre :
            (∫ t in Set.Ioi (0 : ℝ), (g t).re) =
              (∫ t in Set.Ioi (0 : ℝ), g t).re := by
            -- `re` commutes with the integral under integrability.
            simpa using!
              (integral_re (μ := (volume.restrict (Set.Ioi (0 : ℝ)))) (f := g) hInt)
        have hnonpos :
            (∫ t in Set.Ioi (0 : ℝ), (g t).re) ≤ 0 := by
          -- Pointwise, the real part is nonpositive: `AKernel0.re ≤ 0` and `exp ≥ 0`.
          refine setIntegral_nonpos measurableSet_Ioi ?_
          intro t ht
          have ht0 : 0 < t := ht
          have hA : (Dim24.AKernel t ht0).re ≤ 0 := by
            simpa [Dim24.AKernel] using! (SignAux.AKernel_re_nonpos t ht0)
          have hA0 : (AKernel0 t).re ≤ 0 := by
            simpa [AKernel0, ht0] using! hA
          have hexp : 0 ≤ Real.exp (-Real.pi * (‖x‖ ^ 2) * t) := by positivity
          have hgre :
              (g t).re = (AKernel0 t).re * Real.exp (-Real.pi * (‖x‖ ^ 2) * t) := by
            dsimp [g]
            exact Complex.re_mul_ofReal _ _
          -- `re (a * r) = re a * r` for real `r`.
          rw [hgre]
          exact mul_nonpos_of_nonpos_of_nonneg hA0 hexp
        -- Convert back to the real part of the complex integral.
        have : (∫ t in Set.Ioi (0 : ℝ), g t).re ≤ 0 := by simpa [hre] using! hnonpos
        simpa [z, g] using! this
      · -- If the integral is undefined, it is `0`.
        have hz0 : (∫ t in Set.Ioi (0 : ℝ), g t) = 0 := by
          simpa using!
            (integral_undef (μ := (volume.restrict (Set.Ioi (0 : ℝ)))) (f := g) hInt)
        simp [z, g, hz0]
    -- Finish by taking real parts in the Laplace representation.
    set s : ℝ := (Real.sin (Real.pi * (‖x‖ ^ 2) / 2)) ^ (2 : ℕ)
    have hsin : 0 ≤ s := by
      dsimp [s]
      positivity
    -- `re ( (real : ℂ) * z ) = real * re z`.
    have hre :
        (f x).re = s * z.re := by
      rw [hf]
      simp [z, Complex.mul_re]
    rw [hre]
    exact mul_nonpos_of_nonneg_of_nonpos hsin hz
  -- Extend to the boundary `‖x‖ = 2` using continuity.
  intro x hx
  by_cases hxlt : 2 < ‖x‖
  · exact hstrict x hxlt
  · have hxEq : ‖x‖ = 2 := le_antisymm (le_of_not_gt hxlt) hx
    -- Approach `x` from outside the sphere by scaling.
    let c : ℕ → ℝ := fun n => (1 : ℝ) + 1 / ((n : ℝ) + 1)
    have hc1 : Tendsto c atTop (𝓝 (1 : ℝ)) := by
      have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
        simpa using! (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa [c] using! (tendsto_const_nhds.add h0)
    have hc_pos : ∀ n : ℕ, 0 < c n := by
      intro n
      have : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
      linarith [this]
    have hcx : Tendsto (fun n : ℕ => c n • x) atTop (𝓝 x) := by
      simpa using! (hc1.smul_const x)
    have hcont : Continuous fun x : ℝ²⁴ => (f x).re :=
      Continuous.comp Complex.continuous_re f.continuous
    have hlim :
        Tendsto (fun n : ℕ => (f (c n • x)).re) atTop (𝓝 (f x).re) :=
      (hcont.continuousAt.tendsto.comp hcx)
    have hmem : ∀ n : ℕ, (f (c n • x)).re ∈ Set.Iic (0 : ℝ) := by
      intro n
      have hc_gt1 : (1 : ℝ) < c n := by
        have : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
        have : (1 : ℝ) < (1 : ℝ) + 1 / ((n : ℝ) + 1) := by linarith
        simpa [c] using! this
      have hnorm :
          2 < ‖c n • x‖ := by
        -- Use `‖c•x‖ = |c|*‖x‖` and `‖x‖ = 2`.
        have hc0 : 0 < c n := hc_pos n
        have habs : ‖c n‖ = c n := by
          simp [Real.norm_eq_abs, abs_of_pos hc0]
        have : ‖c n • x‖ = c n * ‖x‖ := by
          simp [norm_smul, habs]
        -- Now `c n * 2 > 2`.
        rw [this, hxEq]
        nlinarith
      exact (hstrict (c n • x) hnorm)
    have hclosed : IsClosed (Set.Iic (0 : ℝ)) := isClosed_Iic
    have hxmem : (f x).re ∈ Set.Iic (0 : ℝ) :=
      hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem)
    exact hxmem

-- Helper: `re(∫ h) ≥ 0` from pointwise `re(h) ≥ 0`.
private lemma setIntegral_re_nonneg {s : Set ℝ} {h : ℝ → ℂ} (hs : MeasurableSet s)
    (hpoint : ∀ t, t ∈ s → 0 ≤ (h t).re) : 0 ≤ (∫ t in s, h t).re := by
  by_cases hInt : Integrable h (volume.restrict s)
  · have hre : (∫ t in s, (h t).re) = (∫ t in s, h t).re := by
      simpa using! (integral_re (μ := volume.restrict s) (f := h) hInt)
    have hnonneg : 0 ≤ ∫ t in s, (h t).re :=
      setIntegral_nonneg hs (by intro t ht; exact hpoint t ht)
    simpa [hre] using! hnonneg
  · have hz0 : (∫ t in s, h t) = 0 := by
      simpa using! (integral_undef (μ := volume.restrict s) (f := h) hInt)
    simp [hz0]

private theorem fourier_f_nonneg_of_sqrtTwo_lt_norm :
    ∀ y : ℝ²⁴, Real.sqrt 2 < ‖y‖ → 0 ≤ (FT f y).re := by
  intro y hy
  let g : ℝ²⁴ → ℝ := fun y => (FT f y).re
  have : 0 ≤ g y := by
    have hf := LaplaceTmp.fourier_f_eq_laplace_B (y := y) hy
    set z : ℂ :=
      ∫ t in Set.Ioi (0 : ℝ), BKernel0 t * Real.exp (-Real.pi * (‖y‖ ^ 2) * t)
    have hz : 0 ≤ z.re := by
      refine setIntegral_re_nonneg (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi ?_
      intro t ht
      have ht0 : 0 < t := ht
      have hB0 : 0 ≤ (BKernel0 t).re := by
        simp [BKernel0, ht0, SignAux.BKernel_re_nonneg t ht0]
      have hexp : 0 ≤ Real.exp (-Real.pi * (‖y‖ ^ 2) * t) := by positivity
      have hre :
          (BKernel0 t * Real.exp (-Real.pi * (‖y‖ ^ 2) * t)).re =
            (BKernel0 t).re * Real.exp (-Real.pi * (‖y‖ ^ 2) * t) := by
        let r : ℝ := Real.exp (-Real.pi * (‖y‖ ^ 2) * t)
        simpa [r] using! (mul_ofReal_re (z := BKernel0 t) (r := r))
      rw [hre]
      exact mul_nonneg hB0 hexp
    set s : ℝ := (Real.sin (Real.pi * (‖y‖ ^ 2) / 2)) ^ (2 : ℕ)
    have hsin : 0 ≤ s := by
      dsimp [s]
      positivity
    have hgy : g y = s * z.re := by
      change (FT f y).re = s * z.re
      simp_all
    rw [hgy]
    exact mul_nonneg hsin hz
  simpa [g] using! this

private theorem fourier_f_nonneg_of_norm_lt_sqrtTwo :
    ∀ y : ℝ²⁴, 0 < ‖y‖ → ‖y‖ < Real.sqrt 2 → 0 ≤ (FT f y).re := by
  intro y hy0 hy
  let g : ℝ²⁴ → ℝ := fun y => (FT f y).re
  have : 0 ≤ g y := by
    have hf := LaplaceTmp.fourier_f_eq_laplace_B_subtract_leading (y := y) hy0 hy
    set sC : ℝ := (Real.sin (Real.pi * (‖y‖ ^ 2) / 2)) ^ (2 : ℕ)
    set I1 : ℂ :=
      ∫ t in Set.Ioc (0 : ℝ) 1, BKernel0 t * Real.exp (-Real.pi * (‖y‖ ^ 2) * t)
    set I2 : ℂ :=
      ∫ t in Set.Ioi (1 : ℝ),
        (BKernel0 t -
            ((1 / 39 : ℝ) * t * Real.exp (2 * Real.pi * t)
              - (10 / (117 * Real.pi) : ℝ) * Real.exp (2 * Real.pi * t) : ℝ)) *
          Real.exp (-Real.pi * (‖y‖ ^ 2) * t)
    set I3 : ℂ := BleadingCorrection (‖y‖ ^ 2)
    have hI1 : 0 ≤ I1.re := by
      refine setIntegral_re_nonneg (s := Set.Ioc (0 : ℝ) 1) measurableSet_Ioc ?_
      intro t ht
      have ht0 : 0 < t := ht.1
      have hB0 : 0 ≤ (BKernel0 t).re := by
        simp [BKernel0, ht0, SignAux.BKernel_re_nonneg t ht0]
      have hexp : 0 ≤ Real.exp (-Real.pi * (‖y‖ ^ 2) * t) := by positivity
      have hre :
          (BKernel0 t * Real.exp (-Real.pi * (‖y‖ ^ 2) * t)).re =
            (BKernel0 t).re * Real.exp (-Real.pi * (‖y‖ ^ 2) * t) := by
        let r : ℝ := Real.exp (-Real.pi * (‖y‖ ^ 2) * t)
        simpa [r] using! (mul_ofReal_re (z := BKernel0 t) (r := r))
      rw [hre]
      exact mul_nonneg hB0 hexp
    have hI2 : 0 ≤ I2.re := by
      refine setIntegral_re_nonneg (s := Set.Ioi (1 : ℝ)) measurableSet_Ioi ?_
      intro t ht
      have ht1 : 1 ≤ t := le_of_lt ht
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht1
      set lead : ℝ :=
        (1 / 39 : ℝ) * t * Real.exp (2 * Real.pi * t)
          - (10 / (117 * Real.pi) : ℝ) * Real.exp (2 * Real.pi * t)
      have hBlead :
          (BKernel t ht0).re > lead := by
        simpa [lead] using! (B_leadingterms_bound (t := t) ht1)
      have hdiff : 0 ≤ (BKernel t ht0).re - lead := by linarith
      have hB0re : (BKernel0 t).re = (BKernel t ht0).re := by
        simp [BKernel0, ht0]
      have hdiff' : 0 ≤ (BKernel0 t - (lead : ℂ)).re := by
        have : 0 ≤ (BKernel0 t).re - lead := by simpa [hB0re] using! hdiff
        simpa [sub_eq_add_neg] using! this
      have hexp : 0 ≤ Real.exp (-Real.pi * (‖y‖ ^ 2) * t) := by positivity
      have hre :
          ((BKernel0 t - (lead : ℂ)) * Real.exp (-Real.pi * (‖y‖ ^ 2) * t)).re =
            (BKernel0 t - (lead : ℂ)).re * Real.exp (-Real.pi * (‖y‖ ^ 2) * t) := by
        let r : ℝ := Real.exp (-Real.pi * (‖y‖ ^ 2) * t)
        simpa [r] using! (mul_ofReal_re (z := BKernel0 t - (lead : ℂ)) (r := r))
      -- The integrand in `I2` is exactly `(BKernel0 - lead) * exp`.
      have hmul :
          0 ≤ ((BKernel0 t - (lead : ℂ)) * Real.exp (-Real.pi * (‖y‖ ^ 2) * t)).re := by
        rw [hre]
        exact mul_nonneg hdiff' hexp
      -- Fold the explicit leading term into `lead`.
      assumption
    have hI3 : 0 ≤ I3.re := by
      -- Use the explicit closed form and show it is nonnegative on `‖y‖^2 < 2`.
      set u : ℝ := ‖y‖ ^ (2 : ℕ)
      have hu : u < 2 := by
        have hs0 : 0 ≤ ‖y‖ := norm_nonneg y
        exact (lt_sqrt hs0).mp hy
      have hcoef : 0 ≤ (10 : ℝ) - 3 * Real.pi := by
        have hpi : Real.pi < 3.15 := Real.pi_lt_d2
        have hmul : 3 * Real.pi < 3 * 3.15 := by nlinarith
        have hmul' : 3 * Real.pi < 10 := lt_trans hmul (by norm_num)
        linarith
      have h2u : 0 ≤ 2 - u := sub_nonneg.2 hu.le
      have hnum : 0 ≤ ((10 : ℝ) - 3 * Real.pi) * (2 - u) + 3 :=
        add_nonneg (mul_nonneg hcoef h2u) (by norm_num)
      have hden : 0 ≤ (117 : ℝ) * (Real.pi ^ (2 : ℕ)) * (u - 2) ^ (2 : ℕ) := by positivity
      have hexp : 0 ≤ Real.exp (-Real.pi * (u - 2)) := by positivity
      have hreal :
          0 ≤
            (((((10 : ℝ) - 3 * Real.pi) * (2 - u) + 3) /
                    (117 * (Real.pi ^ (2 : ℕ)) * (u - 2) ^ (2 : ℕ))) *
                Real.exp (-Real.pi * (u - 2))) := by
        exact mul_nonneg (div_nonneg hnum hden) hexp
      -- Unfold `I3` and rewrite `u = ‖y‖^2`.
      assumption
    have hsin : 0 ≤ sC := by
      dsimp [sC]
      positivity
    have hgy : g y = sC * (I1.re + I2.re + I3.re) := by
      change (FT f y).re = sC * (I1.re + I2.re + I3.re)
      simp_all
    rw [hgy]
    exact mul_nonneg hsin (add_nonneg (add_nonneg hI1 hI2) hI3)
  simpa [g] using! this

/-- Cohn-Elkies sign condition: `\hat f(y) ≥ 0` for all `y` (after handling small radii). -/
public theorem f_cohnElkies₂ : ∀ y : ℝ²⁴, (FT f y).re ≥ 0 := by
  let g : ℝ²⁴ → ℝ := fun y => (FT f y).re
  have hgcont : Continuous g := by
    simpa [g] using! (Continuous.comp Complex.continuous_re (FT f).continuous)
  have hgt : ∀ y : ℝ²⁴, Real.sqrt 2 < ‖y‖ → 0 ≤ g y := by
    intro y hy
    simpa [g] using! (fourier_f_nonneg_of_sqrtTwo_lt_norm (y := y) hy)
  have hlt : ∀ y : ℝ²⁴, 0 < ‖y‖ → ‖y‖ < Real.sqrt 2 → 0 ≤ g y := by
    intro y hy0 hy
    simpa [g] using! (fourier_f_nonneg_of_norm_lt_sqrtTwo (y := y) hy0 hy)
  -- Finish by cases on `‖y‖`, using continuity at the boundary points.
  intro y
  by_cases hy0 : ‖y‖ = 0
  · have hy0' : y = 0 := by simpa [norm_eq_zero] using! hy0
    subst hy0'
    let v : ℝ²⁴ := EuclideanSpace.single (𝕜 := ℝ) (ι := Fin 24) 0 (1 : ℝ)
    have hv : ‖v‖ = 1 := by simp [v, EuclideanSpace.norm_single]
    let c : ℕ → ℝ := fun n => (1 : ℝ) / ((n : ℝ) + 1)
    have hc0 : Tendsto c atTop (𝓝 (0 : ℝ)) := by
      simpa [c] using! (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hcv : Tendsto (fun n : ℕ => c n • v) atTop (𝓝 (0 : ℝ²⁴)) := by
      simpa using! (hc0.smul_const v)
    have hseq : ∀ n : ℕ, 0 ≤ g (c n • v) := by
      intro n
      have hden0 : 0 < (n : ℝ) + 1 := by nlinarith
      have hcpos : 0 < c n := by
        dsimp [c]
        exact one_div_pos.2 hden0
      have hnorm : ‖c n • v‖ = c n := by
        have hc0 : 0 ≤ c n := le_of_lt hcpos
        simp [norm_smul, hv, Real.norm_eq_abs, abs_of_nonneg hc0]
      have hnormpos : 0 < ‖c n • v‖ := by simpa [hnorm] using! hcpos
      have hcle : c n ≤ 1 := by
        dsimp [c]
        have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by nlinarith
        exact (div_le_one₀ hden0).mpr hden
      have hnormlt : ‖c n • v‖ < Real.sqrt 2 := by
        rw [hnorm]
        exact lt_of_le_of_lt hcle Real.one_lt_sqrt_two
      exact hlt (c n • v) hnormpos hnormlt
    have hlim : Tendsto (fun n : ℕ => g (c n • v)) atTop (𝓝 (g 0)) :=
      (hgcont.continuousAt.tendsto.comp hcv)
    have hclosed : IsClosed (Set.Ici (0 : ℝ)) := isClosed_Ici
    have hmem : g 0 ∈ Set.Ici (0 : ℝ) :=
      hclosed.mem_of_tendsto hlim (Eventually.of_forall hseq)
    simpa [Set.mem_Ici] using! hmem
  · have hypos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy0)
    by_cases hylt : ‖y‖ < Real.sqrt 2
    · exact hlt y hypos hylt
    · by_cases hygt : Real.sqrt 2 < ‖y‖
      · exact hgt y hygt
      · have hyeq : ‖y‖ = Real.sqrt 2 :=
          le_antisymm (le_of_not_gt hygt) (le_of_not_gt hylt)
        -- Approach `y` from inside the sphere by scaling with `c n = 1 - (1/2)^(n+1)`.
        let c : ℕ → ℝ := fun n => 1 - (1 / 2 : ℝ) ^ (n + 1)
        have hc1 : Tendsto c atTop (𝓝 (1 : ℝ)) := by
          have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 (0 : ℝ)) := by
            have hnonneg : (0 : ℝ) ≤ (1 / 2 : ℝ) := by positivity
            have hlt1 : (1 / 2 : ℝ) < 1 := by norm_num
            exact tendsto_pow_atTop_nhds_zero_of_lt_one hnonneg hlt1
          have hpow' : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 (0 : ℝ)) := by
            simpa using! hpow.comp (tendsto_add_atTop_nat 1)
          have hc1' :
              Tendsto (fun n : ℕ => (1 : ℝ) - (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 (1 : ℝ)) := by
            simpa only [sub_zero] using! (tendsto_const_nhds.sub hpow')
          dsimp [c]
          exact hc1'
        have hcy : Tendsto (fun n : ℕ => c n • y) atTop (𝓝 ((1 : ℝ) • y)) :=
          hc1.smul_const y
        have hseq : ∀ n : ℕ, 0 ≤ g (c n • y) := by
          intro n
          have hr0 : (0 : ℝ) ≤ (1 / 2 : ℝ) := by positivity
          have hr1 : (1 / 2 : ℝ) < 1 := by norm_num
          have hpowlt : (1 / 2 : ℝ) ^ (n + 1) < 1 := by
            simpa only [one_pow] using!
              (pow_lt_pow_left₀ (a := (1 / 2 : ℝ)) (b := (1 : ℝ)) hr1 hr0 (n := n + 1)
                (Nat.succ_ne_zero n))
          have hcpos : 0 < c n := by
            dsimp [c]
            exact sub_pos.2 hpowlt
          have hcpowpos : 0 < (1 / 2 : ℝ) ^ (n + 1) := by positivity
          have hclt1 : c n < 1 := by
            dsimp [c]
            exact sub_lt_self _ hcpowpos
          have hnorm : ‖c n • y‖ = c n * ‖y‖ := by
            have hc0 : 0 ≤ c n := le_of_lt hcpos
            rw [norm_smul, Real.norm_of_nonneg hc0]
          have hnormpos : 0 < ‖c n • y‖ := by
            rw [hnorm]
            exact mul_pos hcpos hypos
          have hnormlt : ‖c n • y‖ < Real.sqrt 2 := by
            rw [hnorm, hyeq]
            have hspos : 0 < Real.sqrt 2 := by positivity
            exact (mul_lt_iff_lt_one_left hspos).mpr hclt1
          exact hlt (c n • y) hnormpos hnormlt
        have hlim : Tendsto (fun n : ℕ => g (c n • y)) atTop (𝓝 (g ((1 : ℝ) • y))) :=
          (hgcont.continuousAt.tendsto.comp hcy)
        have hclosed : IsClosed (Set.Ici (0 : ℝ)) := isClosed_Ici
        have hmem : 0 ≤ g ((1 : ℝ) • y) := by
          have hmem' : g ((1 : ℝ) • y) ∈ Set.Ici (0 : ℝ) :=
            hclosed.mem_of_tendsto hlim (Eventually.of_forall hseq)
          simpa [Set.mem_Ici] using! hmem'
        simpa [one_smul] using! hmem

end SpherePacking.Dim24
