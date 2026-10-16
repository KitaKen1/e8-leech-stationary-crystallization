-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import
SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.AvaluesRemainderIntegralDefs
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.Basic
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.Schwartz.Function
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Varphi1C
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Varphi2
import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.Varphi2ConstValue
import SpherePacking.Dim24.MagicFunction.A.DefsAux.VarphiExpBounds
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

/-!
# Large-`t` remainder bound for `eq:phip`

This file proves the estimate
`‖t^10 * varphi(i/t) - pPaper t‖ ≤ C * t^2 * exp(-2π t)` for `t ≥ 1`. The proof uses the
`S`-transform identity and bounds the `q`-expansion remainders of `varphi₁` and `varphi₂`.

## Main statements
* `exists_bound_remainder_large_proof`
-/

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesDerivTwoLaurent

open scoped Real Topology Manifold
open Filter Complex UpperHalfPlane

/-- Principal part of `varphi₁(it)` (paper: first two terms in the `q`-expansion). -/
def varphi₁Principal (t : ℝ) : ℂ :=
  ((725760 : ℂ) * Complex.I / (π : ℂ)) * (Real.exp (2 * Real.pi * t) : ℂ) +
    ((113218560 : ℂ) * Complex.I / (π : ℂ))

/-- Principal part of `varphi₂(it)` (paper: first three terms in the `q`-expansion). -/
def varphi₂Principal (t : ℝ) : ℂ :=
  ((864 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * (Real.exp (4 * Real.pi * t) : ℂ) +
    ((2218752 : ℂ) / ((π : ℂ) ^ (2 : ℕ))) * (Real.exp (2 * Real.pi * t) : ℂ) +
      ((223140096 : ℂ) / ((π : ℂ) ^ (2 : ℕ)))

lemma pPaper_eq_neg_i_mul_t_mul_varphi₁Principal_sub_varphi₂Principal (t : ℝ) :
    pPaper t = -(Complex.I : ℂ) * (t : ℂ) * varphi₁Principal t - varphi₂Principal t := by
  -- Pure algebra: unfold all definitions and normalize.
  simp [pPaper, varphi₁Principal, varphi₂Principal, mul_add, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
  ring_nf
  simp

/-!
### Periodic exponential decay helper lemmas

We use Mathlib's `Function.Periodic.exp_decay_sub_of_bounded_at_inf` on `I∞ = comap im atTop`.
-/

local notation "I∞" => comap Complex.im atTop

lemma q_add_one (z : ℂ) :
    SpecialValuesVarphi₁Limits.q (z + 1) = SpecialValuesVarphi₁Limits.q z := by
  -- `q(z) = exp(2π i z)` is `1`-periodic.
  unfold SpecialValuesVarphi₁Limits.q
  -- Expand the exponent and use `exp(2π i) = 1`.
  calc
    Complex.exp (2 * π * Complex.I * (z + 1)) =
        Complex.exp (2 * π * Complex.I * z + 2 * π * Complex.I) := by
          ring_nf
    _ = Complex.exp (2 * π * Complex.I * z) * Complex.exp (2 * π * Complex.I) := by
          simp [Complex.exp_add]
    _ = Complex.exp (2 * π * Complex.I * z) := by
          simp

lemma tendsto_I_mul_coe_atTop_Iinf :
    Tendsto (fun t : ℝ => (Complex.I : ℂ) * (t : ℂ)) atTop I∞ := by
  -- `im (I * t) = t`.
  refine (tendsto_comap_iff.2 ?_)
  have hEq : (Complex.im ∘ fun t : ℝ => (Complex.I : ℂ) * (t : ℂ)) = fun t : ℝ => t := by
    funext t
    simp [Function.comp, mul_comm]
  simpa [hEq] using! (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop)

instance : NeBot I∞ := by
  -- For any `t ∈ atTop`, pick a complex number with large enough imaginary part.
  refine Filter.comap_neBot ?_
  intro s hs
  rcases (mem_atTop_sets.1 hs) with ⟨A, hA⟩
  refine ⟨Complex.mk 0 (A + 1), ?_⟩
  -- `im (0 + i(A+1)) = A+1 ∈ Ici A ⊆ s`.
  have hmem : (Complex.mk 0 (A + 1)).im ∈ Set.Ici A := by
    simp [Set.mem_Ici]
  exact hA _ hmem

/-- `O(exp(-2π t))` control of `varphi₁(it) - varphi₁Principal(t)` for `t ≥ 1`. -/
theorem exists_bound_varphi₁_sub_principal_Ici_one :
    ∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ t : ℝ, 1 ≤ t → ∀ ht : 0 < t,
        ‖varphi₁ (it t ht) - varphi₁Principal t‖ ≤ C1 * Real.exp (-(2 * Real.pi) * t) := by
  -- Constants from the `q`-expansion.
  let c1 : ℂ := ((725760 : ℂ) * Complex.I / (π : ℂ))
  let c0 : ℂ := ((113218560 : ℂ) * Complex.I / (π : ℂ))
  -- Periodic function on `ℂ` whose `I∞`-limit is `c0`.
  let f : ℂ → ℂ := fun z =>
    if hz : 0 < z.im then
      Dim24.varphi₁ (⟨z, hz⟩ : ℍ) - c1 / SpecialValuesVarphi₁Limits.q z
    else
      0
  have hf_periodic : Function.Periodic f (1 : ℝ) := by
    intro z
    by_cases hz : 0 < z.im
    · have hz1 : 0 < (z + 1).im := by simpa using! hz
      let zH : ℍ := ⟨z, hz⟩
      let zH1 : ℍ := ⟨z + 1, hz1⟩
      have hvadd : ((1 : ℝ) +ᵥ zH : ℍ) = zH1 := by
        ext1
        simp [zH, zH1, add_comm]
      have hvar : Dim24.varphi₁ zH1 = Dim24.varphi₁ zH := by
        simpa [hvadd] using! (Dim24.varphi₁_periodic (z := zH))
      have hq : SpecialValuesVarphi₁Limits.q (z + 1) = SpecialValuesVarphi₁Limits.q z := q_add_one z
      simp [f, hz, zH, zH1, hvar, hq]
    · have hz1 : ¬0 < (z + 1).im := by simpa using! hz
      simp [f, hz]
  have hf_tendsto : Tendsto f I∞ (𝓝 c0) := by
    -- First, transfer the `atImInfty` limit through `ofComplex`.
    have hlim0 :
        Tendsto
            (fun z : ℂ =>
              Dim24.varphi₁ (UpperHalfPlane.ofComplex z) -
                c1 / SpecialValuesVarphi₁Limits.q ((UpperHalfPlane.ofComplex z : ℍ) : ℂ))
            I∞ (𝓝 c0) := by
      simpa [c1, c0] using!
        (SpecialValuesVarphi₁Limits.tendsto_varphi₁_sub_const_div_q.comp
          UpperHalfPlane.tendsto_comap_im_ofComplex)
    -- Replace `q ((ofComplex z : ℍ) : ℂ)` by `q z` (eventually, since `im z → ∞`).
    have hqEv :
        (fun z : ℂ => SpecialValuesVarphi₁Limits.q ((UpperHalfPlane.ofComplex z : ℍ) : ℂ)) =ᶠ[I∞]
          fun z : ℂ => SpecialValuesVarphi₁Limits.q z := by
      -- Eventually `0 < im z`, so `ofComplex z = ⟨z, _⟩`.
      filter_upwards [preimage_mem_comap (Ioi_mem_atTop (0 : ℝ))] with z hz
      simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    have hlim1 :
        Tendsto
            (fun z : ℂ =>
              Dim24.varphi₁ (UpperHalfPlane.ofComplex z) - c1 / SpecialValuesVarphi₁Limits.q z)
            I∞ (𝓝 c0) := by
      refine hlim0.congr' ?_
      filter_upwards [hqEv] with z hz
      simp [hz]
    -- Finally, replace the `ofComplex` version by the `if`-extension `f`.
    have hfEv :
        f =ᶠ[I∞] fun z : ℂ =>
          Dim24.varphi₁ (UpperHalfPlane.ofComplex z) - c1 / SpecialValuesVarphi₁Limits.q z := by
      filter_upwards [preimage_mem_comap (Ioi_mem_atTop (0 : ℝ))] with z hz
      have hz' : 0 < z.im := by simpa using! hz
      simp [f, hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz']
    exact hlim1.congr' hfEv.symm
  -- Holomorphy near `I∞` (enough to apply the periodic exponential-decay lemma).
  have hf_hol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z := by
    let s : Set ℂ := {z : ℂ | 0 < z.im}
    have hs_open : IsOpen s := isOpen_upperHalfPlaneSet
    have hvarphi₁ :
        DifferentiableOn ℂ (fun z : ℂ => Dim24.varphi₁ (UpperHalfPlane.ofComplex z)) s := by
      simpa [s] using! _root_.SpherePacking.Dim24.SpecialValuesAux.differentiableOn_varphi₁OfComplex
    -- `z ↦ c1 / q z` is entire (and `q z ≠ 0`).
    have hq : Differentiable ℂ (fun z : ℂ => SpecialValuesVarphi₁Limits.q z) := by
      unfold SpecialValuesVarphi₁Limits.q
      -- `q(z) = exp(2π i z)` is entire.
      have hlin : Differentiable ℂ (fun z : ℂ => (2 * (π : ℂ) * Complex.I) * z) :=
        (differentiable_id.const_mul (2 * (π : ℂ) * Complex.I))
      simpa [mul_assoc] using! (Complex.differentiable_exp.comp hlin)
    have hq_ne : ∀ z : ℂ, SpecialValuesVarphi₁Limits.q z ≠ 0 := SpecialValuesVarphi₁Limits.q_ne_zero
    have hdivq : DifferentiableOn ℂ (fun z : ℂ => c1 / SpecialValuesVarphi₁Limits.q z) s := by
      have hinv : Differentiable ℂ (fun z : ℂ => (SpecialValuesVarphi₁Limits.q z)⁻¹) :=
        (hq.fun_inv hq_ne)
      have hmul : Differentiable ℂ (fun z : ℂ => c1 * (SpecialValuesVarphi₁Limits.q z)⁻¹) :=
        hinv.const_mul c1
      simpa [div_eq_mul_inv] using! hmul.differentiableOn
    -- `DifferentiableAt` eventually along `I∞` (where `Im z > 0`).
    filter_upwards [preimage_mem_comap (Ioi_mem_atTop (0 : ℝ))] with z hz
    have hz' : 0 < z.im := by simpa using! hz
    have hzmem : z ∈ s := hz'
    have hvarphiAt :
        DifferentiableAt ℂ (fun w : ℂ => Dim24.varphi₁ (UpperHalfPlane.ofComplex w)) z :=
      (hvarphi₁ z hzmem).differentiableAt (hs_open.mem_nhds hz')
    have hdivAt :
        DifferentiableAt ℂ (fun w : ℂ => c1 / SpecialValuesVarphi₁Limits.q w) z :=
      (hdivq z hzmem).differentiableAt (hs_open.mem_nhds hz')
    have hAt :
        DifferentiableAt ℂ
          (fun w : ℂ =>
            Dim24.varphi₁ (UpperHalfPlane.ofComplex w) - c1 / SpecialValuesVarphi₁Limits.q w) z :=
      hvarphiAt.sub hdivAt
    have hEq :
        (fun w : ℂ => f w) =ᶠ[𝓝 z]
          fun w : ℂ =>
            Dim24.varphi₁ (UpperHalfPlane.ofComplex w) - c1 / SpecialValuesVarphi₁Limits.q w := by
      filter_upwards [hs_open.mem_nhds hz'] with w hw
      have hw' : 0 < w.im := by simpa [s] using! hw
      simp [f, hw', UpperHalfPlane.ofComplex_apply_of_im_pos hw']
    exact hAt.congr_of_eventuallyEq hEq
  -- Boundedness at `I∞` is implied by the existence of the limit.
  have hf_bd : Filter.BoundedAtFilter I∞ f := by
    -- `BoundedAtFilter` is `O(1)`, and any convergent function is `O(1)`.
    dsimp [Filter.BoundedAtFilter]
    exact hf_tendsto.isBigO_one ℝ
  -- Identify the cusp constant with `c0`.
  have hcusp :
      Function.Periodic.cuspFunction (h := (1 : ℝ)) f 0 = c0 := by
    have h1 :
        Tendsto f I∞ (𝓝 (Function.Periodic.cuspFunction (h := (1 : ℝ)) f 0)) := by
      exact Function.Periodic.tendsto_at_I_inf (h := (1 : ℝ)) (by norm_num : (0 : ℝ) < (1 : ℝ))
        hf_periodic hf_hol hf_bd
    exact tendsto_nhds_unique h1 hf_tendsto
  -- Exponential decay in `I∞`.
  have hdecay :
      (fun z : ℂ => f z - c0) =O[I∞] fun z : ℂ => Real.exp (-2 * Real.pi * z.im) := by
    -- Start from `exp_decay_sub_of_bounded_at_inf` and rewrite the cusp constant.
    simpa [hcusp] using!
      (Function.Periodic.exp_decay_sub_of_bounded_at_inf (h := (1 : ℝ))
        (by norm_num : (0 : ℝ) < (1 : ℝ)) hf_periodic hf_hol hf_bd)
  -- Pull back the `IsBigO` statement along `t ↦ I * t`.
  have hdecay_t :
      (fun t : ℝ => f ((Complex.I : ℂ) * (t : ℂ)) - c0) =O[atTop]
        fun t : ℝ => Real.exp (-(2 * Real.pi) * t) := by
    -- First compose, then simplify `im (I*t) = t`.
    have := hdecay.comp_tendsto tendsto_I_mul_coe_atTop_Iinf
    simpa [Function.comp_def, mul_assoc] using! this
  -- Extract an explicit `∀ t ≥ A` bound from `IsBigO`.
  rcases (Asymptotics.isBigO_iff'.1 hdecay_t) with ⟨C, hCpos, hCev⟩
  have hCev' :
      ∀ᶠ t : ℝ in atTop,
        ‖f ((Complex.I : ℂ) * (t : ℂ)) - c0‖ ≤ C * Real.exp (-(2 * Real.pi) * t) := by
    refine hCev.mono ?_
    norm_num
  rcases (Filter.eventually_atTop.1 hCev') with ⟨A, hA⟩
  -- Bound on the compact interval `[1, max A 1]`.
  let A' : ℝ := max A 1
  have hA' : 1 ≤ A' := le_max_right _ _
  -- Use a compactness bound for the numerator on `[1,A']` by restricting to the holomorphic branch
  -- of `f` (where `im (I*t) = t > 0`).
  have hcont_varphi₁ : Continuous (Dim24.varphi₁ : ℍ → ℂ) := SpecialValuesAux.continuous_varphi₁
  have hcont_q : Continuous (fun z : ℂ => SpecialValuesVarphi₁Limits.q z) := by
    -- `SpecialValuesDeriv.q` is just an alias for `SpecialValuesVarphi₁Limits.q`.
    simpa [SpecialValuesDeriv.q] using! (SpecialValuesDeriv.continuous_q)
  have hcont_c1divq : Continuous fun z : ℂ => c1 / SpecialValuesVarphi₁Limits.q z := by
    have hq_ne : ∀ z : ℂ, SpecialValuesVarphi₁Limits.q z ≠ 0 := SpecialValuesVarphi₁Limits.q_ne_zero
    have hq_inv : Continuous fun z : ℂ => (SpecialValuesVarphi₁Limits.q z)⁻¹ :=
      Continuous.inv₀ hcont_q hq_ne
    simpa [div_eq_mul_inv, mul_assoc] using! (continuous_const.mul hq_inv)
  have hcont_it :
      Continuous fun x : Set.Icc (1 : ℝ) A' => (Complex.I : ℂ) * ((x : ℝ) : ℂ) := by
    fun_prop
  let numFun : Set.Icc (1 : ℝ) A' → ℂ :=
    fun x =>
      Dim24.varphi₁.resToImagAxis (x : ℝ) -
        c1 / SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * ((x : ℝ) : ℂ)) - c0
  have hcont_num : Continuous numFun := by
    have h1 : Continuous fun x : Set.Icc (1 : ℝ) A' => Dim24.varphi₁.resToImagAxis (x : ℝ) := by
      have hcont_on : ContinuousOn Dim24.varphi₁.resToImagAxis (Set.Icc (1 : ℝ) A') :=
        (Function.continuousOn_resToImagAxis_Ici_one_of (F := Dim24.varphi₁) hcont_varphi₁).mono
          fun _ ht => ht.1
      simpa [continuousOn_iff_continuous_restrict] using! hcont_on
    have h2 :
        Continuous fun x : Set.Icc (1 : ℝ) A' =>
          c1 / SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * ((x : ℝ) : ℂ)) :=
      hcont_c1divq.comp hcont_it
    simpa [numFun] using! (h1.sub h2).sub continuous_const
  rcases (SpecialValuesDeriv.exists_bound_norm_of_continuous (f := numFun) hcont_num) with ⟨M, hM⟩
  let C1 : ℝ := max C (max (M / Real.exp (-(2 * Real.pi) * A')) 0)
  have hC1nonneg : 0 ≤ C1 :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C1, hC1nonneg, ?_⟩
  intro t ht1 ht0
  -- Relate the target expression to `f(I*t) - c0`.
  have hq_im :
      SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * (t : ℂ)) =
        (Real.exp (-2 * Real.pi * t) : ℂ) := by
    -- Direct computation: `q(z) = exp(2π i z)` and `im (i*t) = t`.
    unfold SpecialValuesVarphi₁Limits.q
    have h :
        (2 * (π : ℂ) * Complex.I * ((Complex.I : ℂ) * (t : ℂ))) = ((-2 * Real.pi * t : ℝ) : ℂ) := by
      push_cast
      ring_nf
      simp
    -- `Complex.ofReal_exp` is oriented as `(Real.exp x : ℂ) = Complex.exp x`.
    rw [h]
    simp
  have hF :
      varphi₁ (it t ht0) - varphi₁Principal t = f ((Complex.I : ℂ) * (t : ℂ)) - c0 := by
    have hz : 0 < (((Complex.I : ℂ) * (t : ℂ)) : ℂ).im := by
      -- `im (i*t) = t`.
      simpa [mul_comm, Complex.mul_I_im] using! ht0
    -- Turn `1/q` into `exp(2π t)`.
    have hq_inv :
        (SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * (t : ℂ)))⁻¹ =
          (Real.exp (2 * Real.pi * t) : ℂ) := by
      have hreal : (Real.exp (-(2 * Real.pi * t)))⁻¹ = Real.exp (2 * Real.pi * t) := by
        -- Invert `exp(-x) = (exp x)⁻¹`.
        simpa using! (congrArg Inv.inv (Real.exp_neg (2 * Real.pi * t)))
      -- Cast the real identity to `ℂ` and rewrite `hq_im` into `exp (-(2πt))`.
      have hrealC :
          ((Real.exp (-(2 * Real.pi * t))) : ℂ)⁻¹ =
            (Real.exp (2 * Real.pi * t) : ℂ) := by
        simpa using! congrArg (fun x : ℝ => (x : ℂ)) hreal
      have hneg : (-2 * Real.pi * t) = -(2 * Real.pi * t) := by ring_nf
      simpa [hq_im, hneg] using! hrealC
    have hit : (⟨(Complex.I : ℂ) * (t : ℂ), hz⟩ : ℍ) = it t ht0 := by
      ext1
      simp [Dim24.it]
    have hfval :
        f ((Complex.I : ℂ) * (t : ℂ)) =
          varphi₁ (it t ht0) - c1 / SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * (t : ℂ)) := by
      simp [f, ht0, hit]
    -- Expand `varphi₁Principal` and rewrite `c1 / q` using `hq_inv`.
    have hprin : varphi₁Principal t = c1 * (Real.exp (2 * Real.pi * t) : ℂ) + c0 := by
      simp [varphi₁Principal, c1, c0]
    calc
      varphi₁ (it t ht0) - varphi₁Principal t
          = (varphi₁ (it t ht0) - c1 * (Real.exp (2 * Real.pi * t) : ℂ)) - c0 := by
              simp [hprin, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ =
          (varphi₁ (it t ht0) - c1 * (SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * (t : ℂ)))⁻¹) -
            c0 := by
              simp [hq_inv, mul_assoc]
      _ =
          (varphi₁ (it t ht0) -
              c1 / SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * (t : ℂ))) -
            c0 := by
              simp [div_eq_mul_inv]
      _ = (f ((Complex.I : ℂ) * (t : ℂ)) - c0) := by
              simp [hfval, sub_eq_add_neg, add_assoc]
  -- Split into cases `t ≥ A'` and `t ≤ A'`.
  by_cases htA : A' ≤ t
  · have htA0 : A ≤ t := le_trans (le_max_left _ _) htA
    have hmain0 : ‖f ((Complex.I : ℂ) * (t : ℂ)) - c0‖ ≤ C * Real.exp (-(2 * Real.pi) * t) :=
      hA t htA0
    have hC1C : C ≤ C1 := le_max_left _ _
    have hmain :
        ‖varphi₁ (it t ht0) - varphi₁Principal t‖ ≤
          C1 * Real.exp (-(2 * Real.pi) * t) := by
      have hexp0 : 0 ≤ Real.exp (-(2 * Real.pi) * t) := by positivity
      have hscale : C * Real.exp (-(2 * Real.pi) * t) ≤ C1 * Real.exp (-(2 * Real.pi) * t) :=
        mul_le_mul_of_nonneg_right hC1C hexp0
      have := le_trans hmain0 hscale
      simpa [hF] using! this
    exact hmain
  · -- On `[1,A']`, bound the numerator by `M` and use `exp(-2π t) ≥ exp(-2π A')`.
    have htIcc : t ∈ Set.Icc (1 : ℝ) A' := ⟨ht1, le_of_lt (lt_of_not_ge htA)⟩
    have hnum : ‖f ((Complex.I : ℂ) * (t : ℂ)) - c0‖ ≤ M := by
      have hz : 0 < (((Complex.I : ℂ) * (t : ℂ)) : ℂ).im := by
        simpa [Complex.mul_I_im] using! ht0
      -- On `[1,A']`, `f` is in its holomorphic branch, hence matches `numFun`.
      have hEq : f ((Complex.I : ℂ) * (t : ℂ)) - c0 = numFun ⟨t, htIcc⟩ := by
        have hpt :
            (⟨(Complex.I : ℂ) * (t : ℂ), by simp [ht0]⟩ : ℍ) =
              (⟨(Complex.I : ℂ) * (t : ℂ), hz⟩ : ℍ) := by
          ext
          rfl
        simp [numFun, Function.resToImagAxis, ResToImagAxis, f, ht0, hpt]
      simpa [hEq] using! hM ⟨t, htIcc⟩
    have hexp : Real.exp (-(2 * Real.pi) * A') ≤ Real.exp (-(2 * Real.pi) * t) := by
      have ht_le : t ≤ A' := le_of_lt (lt_of_not_ge htA)
      have hneg : (-(2 * Real.pi)) ≤ 0 := by nlinarith [Real.pi_pos]
      have hmono : (-(2 * Real.pi)) * A' ≤ (-(2 * Real.pi)) * t :=
        mul_le_mul_of_nonpos_left ht_le hneg
      simpa [mul_assoc] using! (Real.exp_le_exp.2 hmono)
    have hC1M : M / Real.exp (-(2 * Real.pi) * A') ≤ C1 :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have :
        ‖f ((Complex.I : ℂ) * (t : ℂ)) - c0‖ ≤
          (M / Real.exp (-(2 * Real.pi) * A')) * Real.exp (-(2 * Real.pi) * t) := by
      have hMnonneg : 0 ≤ M := by
        let hx : Set.Icc (1 : ℝ) A' := ⟨(1 : ℝ), ⟨le_rfl, hA'⟩⟩
        exact le_trans (norm_nonneg (numFun hx)) (hM hx)
      have hcoef_nonneg : 0 ≤ M / Real.exp (-(2 * Real.pi) * A') :=
        div_nonneg hMnonneg (Real.exp_pos _).le
      have hscale :
          M ≤ (M / Real.exp (-(2 * Real.pi) * A')) * Real.exp (-(2 * Real.pi) * t) := by
        have hmul :
            (M / Real.exp (-(2 * Real.pi) * A')) * Real.exp (-(2 * Real.pi) * A') ≤
              (M / Real.exp (-(2 * Real.pi) * A')) * Real.exp (-(2 * Real.pi) * t) :=
          mul_le_mul_of_nonneg_left hexp hcoef_nonneg
        have hrepr :
            (M / Real.exp (-(2 * Real.pi) * A')) * Real.exp (-(2 * Real.pi) * A') = M := by
          field_simp [Real.exp_ne_zero (-(2 * Real.pi) * A')]
        simpa [hrepr] using! hmul
      exact le_trans hnum hscale
    have hfinal : ‖f ((Complex.I : ℂ) * (t : ℂ)) - c0‖ ≤ C1 * Real.exp (-(2 * Real.pi) * t) :=
      le_trans this (by gcongr)
    -- Finish by rewriting back to the original statement.
    simpa [hF] using! hfinal

/-- `O(exp(-2π t))` control of `varphi₂(it) - varphi₂Principal(t)` for `t ≥ 1`. -/
theorem exists_bound_varphi₂_sub_principal_Ici_one :
    ∃ C2 : ℝ, 0 ≤ C2 ∧
      ∀ t : ℝ, 1 ≤ t → ∀ ht : 0 < t,
        ‖varphi₂ (it t ht) - varphi₂Principal t‖ ≤ C2 * Real.exp (-(2 * Real.pi) * t) := by
  -- Constants from the `q`-expansion.
  let c2 : ℂ := (864 : ℂ) / ((π : ℂ) ^ (2 : ℕ))
  let c1 : ℂ := (2218752 : ℂ) / ((π : ℂ) ^ (2 : ℕ))
  let c0 : ℂ := (223140096 : ℂ) / ((π : ℂ) ^ (2 : ℕ))
  -- Periodic function on `ℂ` whose `I∞`-limit is `c0`.
  let f : ℂ → ℂ := fun z =>
    if hz : 0 < z.im then
      Dim24.varphi₂ (⟨z, hz⟩ : ℍ) - c2 / (SpecialValuesVarphi₁Limits.q z) ^ (2 : ℕ) -
        c1 / SpecialValuesVarphi₁Limits.q z
    else
      0
  have hf_periodic : Function.Periodic f (1 : ℝ) := by
    intro z
    by_cases hz : 0 < z.im
    · have hz1 : 0 < (z + 1).im := by simpa using! hz
      let zH : ℍ := ⟨z, hz⟩
      let zH1 : ℍ := ⟨z + 1, hz1⟩
      have hvadd : ((1 : ℝ) +ᵥ zH : ℍ) = zH1 := by
        ext1
        simp [zH, zH1, add_comm]
      have hvar : Dim24.varphi₂ zH1 = Dim24.varphi₂ zH := by
        simpa [hvadd] using! (Dim24.varphi₂_periodic (z := zH))
      have hq : SpecialValuesVarphi₁Limits.q (z + 1) = SpecialValuesVarphi₁Limits.q z := q_add_one z
      simp [f, hz, zH, zH1, hvar, hq]
    · have hz1 : ¬0 < (z + 1).im := by simpa using! hz
      simp [f, hz]
  have hf_tendsto : Tendsto f I∞ (𝓝 c0) := by
    have hlim0 :
        Tendsto
            (fun z : ℂ =>
              Dim24.varphi₂ (UpperHalfPlane.ofComplex z) -
                  c2 /
                      (SpecialValuesVarphi₁Limits.q ((UpperHalfPlane.ofComplex z : ℍ) : ℂ)) ^
                        (2 : ℕ) -
                c1 / SpecialValuesVarphi₁Limits.q ((UpperHalfPlane.ofComplex z : ℍ) : ℂ))
            I∞ (𝓝 c0) := by
      simpa [c2, c1, c0] using!
        (SpecialValuesVarphi₂Limits.tendsto_varphi₂_sub_c864_div_q_sq_sub_l_div_q.comp
          UpperHalfPlane.tendsto_comap_im_ofComplex)
    have hqEv :
        (fun z : ℂ => SpecialValuesVarphi₁Limits.q ((UpperHalfPlane.ofComplex z : ℍ) : ℂ)) =ᶠ[I∞]
          fun z : ℂ => SpecialValuesVarphi₁Limits.q z := by
      filter_upwards [preimage_mem_comap (Ioi_mem_atTop (0 : ℝ))] with z hz
      simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    have hqEv2 :
        (fun z : ℂ =>
              (SpecialValuesVarphi₁Limits.q ((UpperHalfPlane.ofComplex z : ℍ) : ℂ)) ^
                (2 : ℕ)) =ᶠ[I∞]
          fun z : ℂ => (SpecialValuesVarphi₁Limits.q z) ^ (2 : ℕ) := by
      filter_upwards [hqEv] with z hz
      simp [hz]
    have hlim1 :
        Tendsto
            (fun z : ℂ =>
              Dim24.varphi₂ (UpperHalfPlane.ofComplex z) -
                  c2 / (SpecialValuesVarphi₁Limits.q z) ^ (2 : ℕ) -
                c1 / SpecialValuesVarphi₁Limits.q z)
            I∞ (𝓝 c0) := by
      refine hlim0.congr' ?_
      filter_upwards [hqEv, hqEv2] with z hz1 _hz2
      simp [hz1]
    have hfEv :
        f =ᶠ[I∞]
          fun z : ℂ =>
            Dim24.varphi₂ (UpperHalfPlane.ofComplex z) -
                c2 / (SpecialValuesVarphi₁Limits.q z) ^ (2 : ℕ) -
              c1 / SpecialValuesVarphi₁Limits.q z := by
      filter_upwards [preimage_mem_comap (Ioi_mem_atTop (0 : ℝ))] with z hz
      have hz' : 0 < z.im := by simpa using! hz
      simp [f, hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz']
    exact hlim1.congr' hfEv.symm
  have hf_hol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z := by
    let s : Set ℂ := {z : ℂ | 0 < z.im}
    have hs_open : IsOpen s := isOpen_upperHalfPlaneSet
    have hE4 : DifferentiableOn ℂ ((E₄ : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) s :=
      UpperHalfPlane.mdifferentiable_iff.mp E₄.holo'
    have hE6 : DifferentiableOn ℂ ((E₆ : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) s :=
      UpperHalfPlane.mdifferentiable_iff.mp E₆.holo'
    have hΔ : DifferentiableOn ℂ (Δ ∘ UpperHalfPlane.ofComplex) s := by
      simpa [Delta_apply] using!
        (UpperHalfPlane.mdifferentiable_iff.mp
          (Delta.holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : ℍ => Delta z)))
    let E4c : ℂ → ℂ := fun z => E₄ (UpperHalfPlane.ofComplex z)
    let E6c : ℂ → ℂ := fun z => E₆ (UpperHalfPlane.ofComplex z)
    let Δc : ℂ → ℂ := fun z => Δ (UpperHalfPlane.ofComplex z)
    have hE4c : DifferentiableOn ℂ E4c s := by simpa [E4c, Function.comp_def] using! hE4
    have hE6c : DifferentiableOn ℂ E6c s := by simpa [E6c, Function.comp_def] using! hE6
    have hΔc : DifferentiableOn ℂ Δc s := by simpa [Δc, Function.comp_def] using! hΔ
    let den : ℂ → ℂ := fun z => ((π : ℂ) ^ (2 : ℕ)) * (Δc z) ^ (2 : ℕ)
    have hden : DifferentiableOn ℂ den s :=
      ((differentiableOn_const (c := ((π : ℂ) ^ (2 : ℕ))) :
          DifferentiableOn ℂ (fun _z : ℂ => ((π : ℂ) ^ (2 : ℕ))) s).mul (hΔc.pow 2))
    have hden_ne : ∀ z : ℂ, z ∈ s → den z ≠ 0 := by
      intro z hz
      have hz' : 0 < z.im := hz
      have hof : UpperHalfPlane.ofComplex z = ⟨z, hz'⟩ :=
        UpperHalfPlane.ofComplex_apply_of_im_pos hz'
      have hΔ0 : Δ (⟨z, hz'⟩ : ℍ) ≠ 0 := Δ_ne_zero (⟨z, hz'⟩ : ℍ)
      have hpi : ((π : ℂ) ^ (2 : ℕ)) ≠ 0 := pow_ne_zero 2 (by exact_mod_cast Real.pi_ne_zero)
      simpa [den, Δc, hof] using! mul_ne_zero hpi (pow_ne_zero 2 hΔ0)
    have hvarphi₂ :
        DifferentiableOn ℂ (fun z : ℂ => Dim24.varphi₂ (UpperHalfPlane.ofComplex z)) s := by
      let poly : ℂ → ℂ := fun z =>
        (-49 : ℂ) * (E4c z) ^ (3 : ℕ) + (25 : ℂ) * (E6c z) ^ (2 : ℕ)
      have hpoly : DifferentiableOn ℂ poly s :=
        ((hE4c.pow 3).const_mul (-49 : ℂ)).add ((hE6c.pow 2).const_mul (25 : ℂ))
      have hdiv : DifferentiableOn ℂ (fun z => poly z / den z) s := hpoly.div hden hden_ne
      have hmul : DifferentiableOn ℂ (fun z => (-36 : ℂ) * (poly z / den z)) s :=
        hdiv.const_mul (-36 : ℂ)
      refine hmul.congr fun z hz => ?_
      simp [Dim24.varphi₂, poly, den, E4c, E6c, Δc, div_eq_mul_inv, mul_assoc,
        mul_left_comm, mul_comm]
    have hq : Differentiable ℂ (fun z : ℂ => SpecialValuesVarphi₁Limits.q z) := by
      unfold SpecialValuesVarphi₁Limits.q
      have hlin : Differentiable ℂ (fun z : ℂ => (2 * (π : ℂ) * Complex.I) * z) :=
        (differentiable_id.const_mul (2 * (π : ℂ) * Complex.I))
      simpa [mul_assoc] using! (Complex.differentiable_exp.comp hlin)
    have hq_ne : ∀ z : ℂ, SpecialValuesVarphi₁Limits.q z ≠ 0 := SpecialValuesVarphi₁Limits.q_ne_zero
    have hq2 : Differentiable ℂ fun z : ℂ => (SpecialValuesVarphi₁Limits.q z) ^ (2 : ℕ) := hq.pow 2
    have hq2_ne : ∀ z : ℂ, (SpecialValuesVarphi₁Limits.q z) ^ (2 : ℕ) ≠ 0 := by
      intro z
      exact pow_ne_zero 2 (hq_ne z)
    have hdivq1 : DifferentiableOn ℂ (fun z : ℂ => c1 / SpecialValuesVarphi₁Limits.q z) s := by
      have hinv : Differentiable ℂ (fun z : ℂ => (SpecialValuesVarphi₁Limits.q z)⁻¹) :=
        (hq.fun_inv hq_ne)
      have hmul : Differentiable ℂ (fun z : ℂ => c1 * (SpecialValuesVarphi₁Limits.q z)⁻¹) :=
        hinv.const_mul c1
      simpa [div_eq_mul_inv] using! hmul.differentiableOn
    have hdivq2 :
        DifferentiableOn ℂ (fun z : ℂ => c2 / (SpecialValuesVarphi₁Limits.q z) ^ (2 : ℕ)) s := by
      have hinv :
          Differentiable ℂ (fun z : ℂ => ((SpecialValuesVarphi₁Limits.q z) ^ (2 : ℕ))⁻¹) :=
        (hq2.fun_inv hq2_ne)
      have hmul :
          Differentiable ℂ
            (fun z : ℂ => c2 * ((SpecialValuesVarphi₁Limits.q z) ^ (2 : ℕ))⁻¹) :=
        hinv.const_mul c2
      simpa [div_eq_mul_inv] using! hmul.differentiableOn
    filter_upwards [preimage_mem_comap (Ioi_mem_atTop (0 : ℝ))] with z hz
    have hz' : 0 < z.im := by simpa using! hz
    have hzmem : z ∈ s := hz'
    have hvarphiAt :
        DifferentiableAt ℂ (fun w : ℂ => Dim24.varphi₂ (UpperHalfPlane.ofComplex w)) z :=
      (hvarphi₂ z hzmem).differentiableAt (hs_open.mem_nhds hz')
    have hdiv1At :
        DifferentiableAt ℂ (fun w : ℂ => c2 / (SpecialValuesVarphi₁Limits.q w) ^ (2 : ℕ)) z :=
      (hdivq2 z hzmem).differentiableAt (hs_open.mem_nhds hz')
    have hdiv2At :
        DifferentiableAt ℂ (fun w : ℂ => c1 / SpecialValuesVarphi₁Limits.q w) z :=
      (hdivq1 z hzmem).differentiableAt (hs_open.mem_nhds hz')
    have hAt :
        DifferentiableAt ℂ
          (fun w : ℂ =>
            Dim24.varphi₂ (UpperHalfPlane.ofComplex w) -
                c2 / (SpecialValuesVarphi₁Limits.q w) ^ (2 : ℕ) -
              c1 / SpecialValuesVarphi₁Limits.q w) z :=
      (hvarphiAt.sub hdiv1At).sub hdiv2At
    have hEq :
        (fun w : ℂ => f w) =ᶠ[𝓝 z]
          fun w : ℂ =>
            Dim24.varphi₂ (UpperHalfPlane.ofComplex w) -
                c2 / (SpecialValuesVarphi₁Limits.q w) ^ (2 : ℕ) -
              c1 / SpecialValuesVarphi₁Limits.q w := by
      filter_upwards [hs_open.mem_nhds hz'] with w hw
      have hw' : 0 < w.im := by simpa [s] using! hw
      simp [f, hw', UpperHalfPlane.ofComplex_apply_of_im_pos hw']
    exact hAt.congr_of_eventuallyEq hEq
  have hf_bd : Filter.BoundedAtFilter I∞ f := by
    dsimp [Filter.BoundedAtFilter]
    exact hf_tendsto.isBigO_one ℝ
  have hcusp : Function.Periodic.cuspFunction (h := (1 : ℝ)) f 0 = c0 := by
    have h1 :
        Tendsto f I∞ (𝓝 (Function.Periodic.cuspFunction (h := (1 : ℝ)) f 0)) := by
      exact Function.Periodic.tendsto_at_I_inf (h := (1 : ℝ)) (by norm_num : (0 : ℝ) < (1 : ℝ))
        hf_periodic hf_hol hf_bd
    exact tendsto_nhds_unique h1 hf_tendsto
  have hdecay :
      (fun z : ℂ => f z - c0) =O[I∞] fun z : ℂ => Real.exp (-2 * Real.pi * z.im) := by
    simpa [hcusp] using!
      (Function.Periodic.exp_decay_sub_of_bounded_at_inf (h := (1 : ℝ))
        (by norm_num : (0 : ℝ) < (1 : ℝ)) hf_periodic hf_hol hf_bd)
  have hdecay_t :
      (fun t : ℝ => f ((Complex.I : ℂ) * (t : ℂ)) - c0) =O[atTop]
        fun t : ℝ => Real.exp (-(2 * Real.pi) * t) := by
    have := hdecay.comp_tendsto tendsto_I_mul_coe_atTop_Iinf
    simpa [Function.comp_def, mul_assoc] using! this
  rcases (Asymptotics.isBigO_iff'.1 hdecay_t) with ⟨C, hCpos, hCev⟩
  have hCev' :
      ∀ᶠ t : ℝ in atTop,
        ‖f ((Complex.I : ℂ) * (t : ℂ)) - c0‖ ≤ C * Real.exp (-(2 * Real.pi) * t) := by
    refine hCev.mono ?_
    intro t ht
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using! ht
  rcases (Filter.eventually_atTop.1 hCev') with ⟨A, hA⟩
  let A' : ℝ := max A 1
  have hA' : 1 ≤ A' := le_max_right _ _
  have hcont_varphi₂ : Continuous (Dim24.varphi₂ : ℍ → ℂ) := SpecialValuesDeriv.continuous_varphi₂
  have hcont_q : Continuous (fun z : ℂ => SpecialValuesVarphi₁Limits.q z) := by
    simpa [SpecialValuesDeriv.q] using! (SpecialValuesDeriv.continuous_q)
  have hcont_q2 : Continuous fun z : ℂ => (SpecialValuesVarphi₁Limits.q z) ^ (2 : ℕ) :=
    hcont_q.pow 2
  have hcont_c1divq : Continuous fun z : ℂ => c1 / SpecialValuesVarphi₁Limits.q z := by
    have hq_ne : ∀ z : ℂ, SpecialValuesVarphi₁Limits.q z ≠ 0 := SpecialValuesVarphi₁Limits.q_ne_zero
    have hq_inv : Continuous fun z : ℂ => (SpecialValuesVarphi₁Limits.q z)⁻¹ :=
      Continuous.inv₀ hcont_q hq_ne
    simpa [div_eq_mul_inv, mul_assoc] using! (continuous_const.mul hq_inv)
  have hcont_c2divq2 : Continuous fun z : ℂ => c2 / (SpecialValuesVarphi₁Limits.q z) ^ (2 : ℕ) := by
    have hq2_ne : ∀ z : ℂ, (SpecialValuesVarphi₁Limits.q z) ^ (2 : ℕ) ≠ 0 := by
      intro z
      exact pow_ne_zero 2 (SpecialValuesVarphi₁Limits.q_ne_zero z)
    have hq2_inv : Continuous fun z : ℂ => ((SpecialValuesVarphi₁Limits.q z) ^ (2 : ℕ))⁻¹ :=
      Continuous.inv₀ hcont_q2 hq2_ne
    simpa [div_eq_mul_inv, mul_assoc] using! (continuous_const.mul hq2_inv)
  let numFun : Set.Icc (1 : ℝ) A' → ℂ :=
    fun x =>
      Dim24.varphi₂.resToImagAxis (x : ℝ) -
        c2 / (SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * ((x : ℝ) : ℂ))) ^ (2 : ℕ) -
          c1 / SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * ((x : ℝ) : ℂ)) - c0
  have hcont_num : Continuous numFun := by
    have hcont_it :
        Continuous fun x : Set.Icc (1 : ℝ) A' => (Complex.I : ℂ) * ((x : ℝ) : ℂ) := by
      fun_prop
    have h1 : Continuous fun x : Set.Icc (1 : ℝ) A' => Dim24.varphi₂.resToImagAxis (x : ℝ) := by
      have hcont_on : ContinuousOn Dim24.varphi₂.resToImagAxis (Set.Icc (1 : ℝ) A') :=
        (Function.continuousOn_resToImagAxis_Ici_one_of (F := Dim24.varphi₂) hcont_varphi₂).mono
          fun _ ht => ht.1
      simpa [continuousOn_iff_continuous_restrict] using! hcont_on
    have h2 : Continuous fun x : Set.Icc (1 : ℝ) A' =>
        c2 / (SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * ((x : ℝ) : ℂ))) ^ (2 : ℕ) :=
      hcont_c2divq2.comp hcont_it
    have h3 :
        Continuous fun x : Set.Icc (1 : ℝ) A' =>
          c1 / SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * ((x : ℝ) : ℂ)) :=
      hcont_c1divq.comp hcont_it
    simpa [numFun] using! ((h1.sub h2).sub h3).sub continuous_const
  rcases (SpecialValuesDeriv.exists_bound_norm_of_continuous (f := numFun) hcont_num) with ⟨M, hM⟩
  let C2' : ℝ := max C (max (M / Real.exp (-(2 * Real.pi) * A')) 0)
  have hC2'nonneg : 0 ≤ C2' :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C2', hC2'nonneg, ?_⟩
  intro t ht1 ht0
  have hq_im :
      SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * (t : ℂ)) =
        (Real.exp (-2 * Real.pi * t) : ℂ) := by
    -- Direct computation: `q(z) = exp(2π i z)` and `i * (i*t) = -t`.
    unfold SpecialValuesVarphi₁Limits.q
    have h :
        (2 * (π : ℂ) * Complex.I * ((Complex.I : ℂ) * (t : ℂ))) = ((-2 * Real.pi * t : ℝ) : ℂ) := by
      push_cast
      ring_nf
      simp
    rw [h]
    simp
  have hq_inv :
      (SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * (t : ℂ)))⁻¹ =
        (Real.exp (2 * Real.pi * t) : ℂ) := by
    calc
      (SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * (t : ℂ)))⁻¹
          = ((Real.exp (-2 * Real.pi * t) : ℂ))⁻¹ := by simp [hq_im]
      _ = (Real.exp (2 * Real.pi * t) : ℂ) := by simp [Real.exp_neg]
  have hq2_im :
      (SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * (t : ℂ)) ^ (2 : ℕ)) =
        (Real.exp (-4 * Real.pi * t) : ℂ) := by
    -- Convert to `Complex.exp`, use `exp_nat_mul`, then convert (postTransparency := .instances) back.
    have hq_im' :
        SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * (t : ℂ)) =
          Complex.exp ((-2 * Real.pi * t : ℝ) : ℂ) := by
      calc
        SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * (t : ℂ))
            = (Real.exp (-2 * Real.pi * t) : ℂ) := hq_im
        _ = Complex.exp ((-2 * Real.pi * t : ℝ) : ℂ) := Complex.ofReal_exp (-2 * Real.pi * t)
    let a : ℂ := ((-2 * Real.pi * t : ℝ) : ℂ)
    have ha : SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * (t : ℂ)) = Complex.exp a := by
      simpa [a] using! hq_im'
    have h2a : (2 : ℂ) * a = ((-4 * Real.pi * t : ℝ) : ℂ) := by
      dsimp [a]
      have h2aR : (2 : ℝ) * (-2 * Real.pi * t) = (-4 * Real.pi * t) := by ring
      exact_mod_cast h2aR
    calc
      SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * (t : ℂ)) ^ (2 : ℕ)
          = (Complex.exp a) ^ (2 : ℕ) := by simp [ha]
      _ = Complex.exp ((2 : ℂ) * a) := by
            -- `exp (2*a) = (exp a)^2`.
            simpa [pow_two, mul_assoc] using! (Complex.exp_nat_mul a 2).symm
      _ = Complex.exp ((-4 * Real.pi * t : ℝ) : ℂ) := by simp [h2a]
      _ = (Real.exp (-4 * Real.pi * t) : ℂ) := by
            exact (Complex.ofReal_exp (-4 * Real.pi * t)).symm
  have hq2_inv :
      (SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * (t : ℂ)) ^ (2 : ℕ))⁻¹ =
        (Real.exp (4 * Real.pi * t) : ℂ) := by
    calc
      (SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * (t : ℂ)) ^ (2 : ℕ))⁻¹
          = ((Real.exp (-4 * Real.pi * t) : ℂ))⁻¹ := by simp [hq2_im]
      _ = (Real.exp (4 * Real.pi * t) : ℂ) := by simp [Real.exp_neg]
  have hF :
      f ((Complex.I : ℂ) * (t : ℂ)) - c0 = varphi₂ (it t ht0) - varphi₂Principal t := by
    have hIm : 0 < (((Complex.I : ℂ) * (t : ℂ)) : ℂ).im := by
      simpa [Complex.mul_I_im] using! ht0
    have hq1 : c1 / SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * (t : ℂ)) =
        c1 * (Real.exp (2 * Real.pi * t) : ℂ) := by
      simp [div_eq_mul_inv, hq_inv, mul_assoc]
    have hq2 : c2 / (SpecialValuesVarphi₁Limits.q ((Complex.I : ℂ) * (t : ℂ)) ^ (2 : ℕ)) =
        c2 * (Real.exp (4 * Real.pi * t) : ℂ) := by
      simp [div_eq_mul_inv, hq2_inv, mul_assoc]
    simp [f, ht0, varphi₂Principal, it, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
      mul_assoc, hq1, hq2, c0, c1, c2]
  by_cases htA : t ≥ A
  · have hbig : ‖f ((Complex.I : ℂ) * (t : ℂ)) - c0‖ ≤ C * Real.exp (-(2 * Real.pi) * t) := by
      have ht : t ∈ Set.Ici A := htA
      simpa using! hA t ht
    have hfinal : ‖f ((Complex.I : ℂ) * (t : ℂ)) - c0‖ ≤ C2' * Real.exp (-(2 * Real.pi) * t) :=
      le_trans hbig (by gcongr; exact le_max_left _ _)
    simpa [hF] using! hfinal
  · have ht_leA : t < A := lt_of_not_ge htA
    have htIcc : t ∈ Set.Icc (1 : ℝ) A' := ⟨ht1, le_trans (le_of_lt ht_leA) (le_max_left A 1)⟩
    have hnum : ‖f ((Complex.I : ℂ) * (t : ℂ)) - c0‖ ≤ M := by
      have hz : 0 < (((Complex.I : ℂ) * (t : ℂ)) : ℂ).im := by
        simpa [Complex.mul_I_im] using! ht0
      have hEq : f ((Complex.I : ℂ) * (t : ℂ)) - c0 = numFun ⟨t, htIcc⟩ := by
        have hpt :
            (⟨(Complex.I : ℂ) * (t : ℂ), by simp [ht0]⟩ : ℍ) =
              (⟨(Complex.I : ℂ) * (t : ℂ), hz⟩ : ℍ) := by
          ext
          rfl
        simp [numFun, Function.resToImagAxis, ResToImagAxis, f, ht0, hpt]
      simpa [hEq] using! hM ⟨t, htIcc⟩
    have hexp : Real.exp (-(2 * Real.pi) * A') ≤ Real.exp (-(2 * Real.pi) * t) := by
      have ht_le : t ≤ A' := le_trans (le_of_lt ht_leA) (le_max_left A 1)
      have hneg : (-(2 * Real.pi)) ≤ 0 := by nlinarith [Real.pi_pos]
      have hmono : (-(2 * Real.pi)) * A' ≤ (-(2 * Real.pi)) * t :=
        mul_le_mul_of_nonpos_left ht_le hneg
      simpa [mul_assoc] using! (Real.exp_le_exp.2 hmono)
    have hC1M : M / Real.exp (-(2 * Real.pi) * A') ≤ C2' :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have :
        ‖f ((Complex.I : ℂ) * (t : ℂ)) - c0‖ ≤
          (M / Real.exp (-(2 * Real.pi) * A')) * Real.exp (-(2 * Real.pi) * t) := by
      have hMnonneg : 0 ≤ M := by
        let hx : Set.Icc (1 : ℝ) A' := ⟨(1 : ℝ), ⟨le_rfl, hA'⟩⟩
        exact le_trans (norm_nonneg (numFun hx)) (hM hx)
      have hcoef_nonneg : 0 ≤ M / Real.exp (-(2 * Real.pi) * A') :=
        div_nonneg hMnonneg (Real.exp_pos _).le
      have hscale :
          M ≤ (M / Real.exp (-(2 * Real.pi) * A')) * Real.exp (-(2 * Real.pi) * t) := by
        have hmul :
            (M / Real.exp (-(2 * Real.pi) * A')) * Real.exp (-(2 * Real.pi) * A') ≤
              (M / Real.exp (-(2 * Real.pi) * A')) * Real.exp (-(2 * Real.pi) * t) :=
          mul_le_mul_of_nonneg_left hexp hcoef_nonneg
        have hrepr :
            (M / Real.exp (-(2 * Real.pi) * A')) * Real.exp (-(2 * Real.pi) * A') = M := by
          field_simp [Real.exp_ne_zero (-(2 * Real.pi) * A')]
        simpa [hrepr] using! hmul
      exact le_trans hnum hscale
    have hfinal : ‖f ((Complex.I : ℂ) * (t : ℂ)) - c0‖ ≤ C2' * Real.exp (-(2 * Real.pi) * t) :=
      le_trans this (by gcongr)
    simpa [hF] using! hfinal

/-- Assemble the paper's large-`t` remainder estimate from the principal-part bounds. -/
public theorem exists_bound_remainder_large_proof :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, 1 ≤ t → ∀ ht : 0 < t,
        ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht) - pPaper t‖ ≤
          C * (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t) := by
  rcases Dim24.VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one with ⟨Cφ0, hCφ0⟩
  -- Make the constant nonnegative.
  let Cφ : ℝ := max Cφ0 0
  have hCφ : ∀ t : ℝ, 1 ≤ t → ‖varphi.resToImagAxis t‖ ≤ Cφ * Real.exp (-(2 * Real.pi) * t) := by
    intro t ht
    have h := hCφ0 t ht
    have hexp0 : 0 ≤ Real.exp (-(2 * Real.pi) * t) := (Real.exp_pos _).le
    have hcoef : Cφ0 * Real.exp (-(2 * Real.pi) * t) ≤ Cφ * Real.exp (-(2 * Real.pi) * t) :=
      mul_le_mul_of_nonneg_right (le_max_left Cφ0 0) hexp0
    exact le_trans h hcoef
  have hCφnonneg : 0 ≤ Cφ := le_max_right _ _
  rcases exists_bound_varphi₁_sub_principal_Ici_one with ⟨C1, hC1nonneg, hC1⟩
  rcases exists_bound_varphi₂_sub_principal_Ici_one with ⟨C2, hC2nonneg, hC2⟩
  let C : ℝ := Cφ + C1 + C2
  have hCnonneg : 0 ≤ C := by nlinarith [hCφnonneg, hC1nonneg, hC2nonneg]
  refine ⟨C, hCnonneg, ?_⟩
  intro t ht1 ht0
  have ht0le : 0 ≤ t := le_of_lt ht0
  have ht_le_t2 : t ≤ t ^ (2 : ℕ) := by
    -- `t ≤ t^2` for `t ≥ 1`.
    nlinarith [ht1]
  have hone_le_t2 : (1 : ℝ) ≤ t ^ (2 : ℕ) := by nlinarith [ht1]
  -- S-transform identity and principal-part algebra.
  have htransform :
      (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0) =
        (t : ℂ) ^ (2 : ℕ) * varphi (it t ht0) -
          (Complex.I : ℂ) * (t : ℂ) * varphi₁ (it t ht0) - varphi₂ (it t ht0) := by
    simpa using! (Dim24.tPow10_varphi_iOverT (t := t) ht0)
  have hpPaper : pPaper t = -(Complex.I : ℂ) * (t : ℂ) * varphi₁Principal t - varphi₂Principal t :=
    pPaper_eq_neg_i_mul_t_mul_varphi₁Principal_sub_varphi₂Principal t
  have hEq :
      (t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0) - pPaper t =
        (t : ℂ) ^ (2 : ℕ) * varphi (it t ht0) -
          (Complex.I : ℂ) * (t : ℂ) * (varphi₁ (it t ht0) - varphi₁Principal t) -
            (varphi₂ (it t ht0) - varphi₂Principal t) := by
    -- Pure algebra.
    simp [htransform, hpPaper, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add,
      mul_assoc, mul_comm]
  -- Triangle inequality.
  have htri :
      ‖(t : ℂ) ^ (10 : ℕ) * varphi (iOverT t ht0) - pPaper t‖ ≤
        ‖(t : ℂ) ^ (2 : ℕ) * varphi (it t ht0)‖ +
          ‖(Complex.I : ℂ) * (t : ℂ) * (varphi₁ (it t ht0) - varphi₁Principal t)‖ +
            ‖(varphi₂ (it t ht0) - varphi₂Principal t)‖ := by
    -- Expand as a 3-term sum.
    have :
        ‖(t : ℂ) ^ (2 : ℕ) * varphi (it t ht0) -
              (Complex.I : ℂ) * (t : ℂ) * (varphi₁ (it t ht0) - varphi₁Principal t) -
                (varphi₂ (it t ht0) - varphi₂Principal t)‖ ≤
          ‖(t : ℂ) ^ (2 : ℕ) * varphi (it t ht0)‖ +
            ‖(Complex.I : ℂ) * (t : ℂ) * (varphi₁ (it t ht0) - varphi₁Principal t)‖ +
              ‖(varphi₂ (it t ht0) - varphi₂Principal t)‖ := by
      -- `‖A - B - C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖`.
      set A : ℂ := (t : ℂ) ^ (2 : ℕ) * varphi (it t ht0)
      set B : ℂ := (Complex.I : ℂ) * (t : ℂ) * (varphi₁ (it t ht0) - varphi₁Principal t)
      set C : ℂ := (varphi₂ (it t ht0) - varphi₂Principal t)
      have hAC : ‖(A + (-B)) + (-C)‖ ≤ ‖A + (-B)‖ + ‖-C‖ := by
        simpa [add_assoc] using! (norm_add_le (A + (-B)) (-C))
      have hAB : ‖A + (-B)‖ ≤ ‖A‖ + ‖-B‖ := by
        simpa using! (norm_add_le A (-B))
      have hABC : ‖(A + (-B)) + (-C)‖ ≤ (‖A‖ + ‖-B‖) + ‖-C‖ :=
        le_trans hAC (add_le_add_left hAB ‖-C‖)
      have hABC' : ‖(A + (-B)) + (-C)‖ ≤ (‖A‖ + ‖B‖) + ‖C‖ := by
        simpa [norm_neg, add_assoc, add_left_comm, add_comm] using! hABC
      simpa [A, B, C, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using! hABC'
    -- Normalize to match `hEq`.
    simpa [hEq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using! this
  refine le_trans htri ?_
  -- Bound each term by `t^2 * exp(-2π t)`.
  have hvarphi :
      ‖varphi (it t ht0)‖ ≤ Cφ * Real.exp (-(2 * Real.pi) * t) := by
    have h := hCφ t ht1
    -- Rewrite `varphi.resToImagAxis t` as `varphi (it t ht0)`.
    simpa [Function.resToImagAxis, ResToImagAxis, Dim24.it, ht0] using! h
  have hA :
      ‖(t : ℂ) ^ (2 : ℕ) * varphi (it t ht0)‖ ≤
        Cφ * (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t) := by
    have hnormt2 : ‖(t : ℂ) ^ (2 : ℕ)‖ = t ^ (2 : ℕ) := by
      have habs : |t| = t := abs_of_nonneg ht0le
      simp [norm_pow, Complex.norm_real, habs]
    calc
      ‖(t : ℂ) ^ (2 : ℕ) * varphi (it t ht0)‖
          = ‖(t : ℂ) ^ (2 : ℕ)‖ * ‖varphi (it t ht0)‖ := by
              simp
      _ ≤ (t ^ (2 : ℕ)) * (Cφ * Real.exp (-(2 * Real.pi) * t)) := by
            gcongr
            simp [hnormt2]
      _ = Cφ * (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t) := by ring
  have hB0 :
      ‖(Complex.I : ℂ) * (t : ℂ) * (varphi₁ (it t ht0) - varphi₁Principal t)‖ ≤
        C1 * t * Real.exp (-(2 * Real.pi) * t) := by
    have h1 := hC1 t ht1 ht0
    -- `‖I‖ = 1` and `‖(t:ℂ)‖ = t` since `t ≥ 0`.
    have hnormt : ‖(t : ℂ)‖ = t := by
      have habs : |t| = t := abs_of_nonneg ht0le
      simp [Complex.norm_real, habs]
    calc
      ‖(Complex.I : ℂ) * (t : ℂ) * (varphi₁ (it t ht0) - varphi₁Principal t)‖
          = ‖(Complex.I : ℂ)‖ * ‖(t : ℂ)‖ * ‖varphi₁ (it t ht0) - varphi₁Principal t‖ := by
              simp [mul_assoc]
      _ ≤ 1 * t * (C1 * Real.exp (-(2 * Real.pi) * t)) := by
            gcongr
            · simp
            · -- `‖(t:ℂ)‖ = |t| ≤ t` since `t ≥ 0`.
              simp [Complex.norm_real, abs_of_nonneg ht0le]
      _ = C1 * t * Real.exp (-(2 * Real.pi) * t) := by ring
  have hB :
      ‖(Complex.I : ℂ) * (t : ℂ) * (varphi₁ (it t ht0) - varphi₁Principal t)‖ ≤
        C1 * (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t) := by
    have h := hB0
    have hexp0 : 0 ≤ Real.exp (-(2 * Real.pi) * t) := (Real.exp_pos _).le
    have :
        C1 * t * Real.exp (-(2 * Real.pi) * t) ≤
          C1 * (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t) := by
      have ht_le' :
          t * Real.exp (-(2 * Real.pi) * t) ≤
            (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t) := by
        exact mul_le_mul_of_nonneg_right ht_le_t2 hexp0
      simpa [mul_assoc] using! (mul_le_mul_of_nonneg_left ht_le' hC1nonneg)
    exact le_trans h this
  have hCterm0 :
      ‖varphi₂ (it t ht0) - varphi₂Principal t‖ ≤ C2 * Real.exp (-(2 * Real.pi) * t) :=
    hC2 t ht1 ht0
  have hCterm :
      ‖varphi₂ (it t ht0) - varphi₂Principal t‖ ≤
        C2 * (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t) := by
    have hexp0 : 0 ≤ Real.exp (-(2 * Real.pi) * t) := (Real.exp_pos _).le
    have ht2_ge : (1 : ℝ) ≤ t ^ (2 : ℕ) := hone_le_t2
    have hscale :
        C2 * Real.exp (-(2 * Real.pi) * t) ≤
          C2 * (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t) := by
      have h' :
          Real.exp (-(2 * Real.pi) * t) ≤
            (t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t) := by
        exact le_mul_of_one_le_left hexp0 hone_le_t2
      have hmul :
          C2 * Real.exp (-(2 * Real.pi) * t) ≤
            C2 * ((t ^ (2 : ℕ)) * Real.exp (-(2 * Real.pi) * t)) :=
        mul_le_mul_of_nonneg_left h' hC2nonneg
      simpa [mul_assoc] using! hmul
    exact le_trans hCterm0 hscale
  -- Combine the three bounds.
  linarith

end SpecialValuesDerivTwoLaurent

end
end SpherePacking.Dim24
