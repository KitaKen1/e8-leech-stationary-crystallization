-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.EvenUnimodular.ThetaAnalytic
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Discriminant
public import SpherePacking.CohnElkies.PoissonSummationGeneral
public import SpherePacking.ForMathlib.RadialSchwartz.OneSided

public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Theta `S`-transform via Poisson summation

This file proves the modular `S`-transformation law for the analytic theta series of a
`ℤ`-lattice in `ℝ²⁴`.

The proof combines Poisson summation for full-rank lattices (from `SpherePacking.CohnElkies`) with
the Fourier transform of the Gaussian on real inner product spaces (Mathlib).

## Main statements
* `thetaSeries_transform_S`
-/

namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

noncomputable section

open scoped RealInnerProductSpace SchwartzMap FourierTransform
open Complex Filter MeasureTheory

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

def thetaProfile (τ : ℂ) : ℝ → ℂ :=
  fun r => Complex.exp (((Real.pi : ℂ) * Complex.I * τ) * (r : ℂ))

lemma thetaProfile_contDiff (τ : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (thetaProfile τ) := by
  have hlin :
      ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => ((Real.pi : ℂ) * Complex.I * τ) * (r : ℂ)) := by
    simpa using! (contDiff_const.mul (Complex.ofRealCLM.contDiff))
  simpa [thetaProfile] using! hlin.cexp

lemma thetaProfile_iteratedDeriv (τ : ℂ) (n : ℕ) (r : ℝ) :
    iteratedDeriv n (thetaProfile τ) r =
      (((Real.pi : ℂ) * Complex.I * τ) ^ n) * thetaProfile τ r := by
  let c : ℂ := (Real.pi : ℂ) * Complex.I * τ
  -- rewrite to a simpler statement with `c`.
  have hIH : ∀ n : ℕ, ∀ r : ℝ, iteratedDeriv n (thetaProfile τ) r = c ^ n * thetaProfile τ r := by
    intro n
    induction n with
    | zero =>
        intro r
        simp [thetaProfile, c]
    | succ n hn =>
        intro r
        have hmul : HasDerivAt (fun z : ℂ => c * z) c (r : ℂ) := by
          simpa using! (hasDerivAt_const_mul (c := c) (x := (r : ℂ)))
        have hlin : HasDerivAt (fun x : ℝ => c * (x : ℂ)) c r :=
          HasDerivAt.comp_ofReal (z := r) hmul
        have hderiv : deriv (fun x : ℝ => Complex.exp (c * (x : ℂ))) r =
            Complex.exp (c * (r : ℂ)) * c := (hlin.cexp).deriv
        have hfun :
            iteratedDeriv n (thetaProfile τ) = fun x : ℝ => c ^ n * thetaProfile τ x := by
          funext x
          exact hn x
        calc
          iteratedDeriv (n + 1) (thetaProfile τ) r
              = deriv (iteratedDeriv n (thetaProfile τ)) r := by
                  simp [iteratedDeriv_succ]
          _ = deriv (fun x : ℝ => c ^ n * thetaProfile τ x) r := by
                  simp [hfun]
          _ = c ^ n * deriv (thetaProfile τ) r := by
                  simp [deriv_const_mul_field (x := r) (u := c ^ n)
                    (v := fun x : ℝ => thetaProfile τ x)]
          _ = c ^ n * (c * thetaProfile τ r) := by
                  have hderiv' : deriv (thetaProfile τ) r = c * thetaProfile τ r := by
                    -- change to the linearized form
                    change deriv (fun x : ℝ => Complex.exp (c * (x : ℂ))) r =
                      c * Complex.exp (c * (r : ℂ))
                    calc
                      deriv (fun x : ℝ => Complex.exp (c * (x : ℂ))) r
                          = Complex.exp (c * (r : ℂ)) * c := hderiv
                      _ = c * Complex.exp (c * (r : ℂ)) := by ac_rfl
                  -- multiply both sides by `c^n`
                  simpa [mul_assoc] using! congrArg (fun z => c ^ n * z) hderiv'
          _ = c ^ (n + 1) * thetaProfile τ r := by
                  simp [pow_succ, mul_assoc]
  simpa [c] using! hIH n r

lemma exists_bound_pow_mul_exp_neg_mul_of_nonneg (k : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → x ^ k * Real.exp (-a * x) ≤ C := by
  have hlim :
      Tendsto (fun x : ℝ => x ^ k * Real.exp (-a * x)) atTop (nhds 0) := by
    simpa [Real.rpow_natCast] using!
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s := (k : ℝ)) (b := a) ha)
  have hevent : ∀ᶠ x : ℝ in atTop, x ^ k * Real.exp (-a * x) ≤ 1 :=
    (hlim.eventually (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num)))
  rcases (Filter.eventually_atTop.1 hevent) with ⟨R, hR⟩
  let R0 : ℝ := max R 0
  have hcont : Continuous fun x : ℝ => x ^ k * Real.exp (-a * x) := by
    fun_prop
  have hne : (Set.Icc (0 : ℝ) R0).Nonempty := by
    refine ⟨0, ?_⟩
    constructor
    · exact le_rfl
    · dsimp [R0]
      exact le_max_right R 0
  rcases (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) R0)).exists_isMaxOn hne hcont.continuousOn with
    ⟨x0, hx0, hxmax⟩
  refine ⟨max (x0 ^ k * Real.exp (-a * x0)) 1, ?_⟩
  intro x hx
  by_cases hxR : x ≤ R0
  · have hxIcc : x ∈ Set.Icc (0 : ℝ) R0 := ⟨hx, hxR⟩
    exact (hxmax hxIcc).trans (le_max_left _ _)
  · have hRR0 : R ≤ R0 := le_max_left R 0
    have hxR0 : R0 ≤ x := le_of_not_ge hxR
    exact (hR x (le_trans hRR0 hxR0)).trans (le_max_right _ _)

lemma thetaProfile_decay (τ : ℂ) (hτ : 0 < τ.im) :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (thetaProfile τ) x‖ ≤ C := by
  intro k n
  let c : ℂ := (Real.pi : ℂ) * Complex.I * τ
  have hc_re : c.re = -Real.pi * τ.im := by
    simp [c]
  have ha : 0 < -c.re := by
    nlinarith [hc_re, Real.pi_pos, hτ]
  rcases exists_bound_pow_mul_exp_neg_mul_of_nonneg k ha with ⟨C0, hC0⟩
  refine ⟨(‖c‖ ^ n) * C0, ?_⟩
  intro x hx
  have hxnorm : ‖x‖ = x := by simp [Real.norm_eq_abs, abs_of_nonneg hx]
  have hiter :
      ‖iteratedFDeriv ℝ n (thetaProfile τ) x‖ = ‖iteratedDeriv n (thetaProfile τ) x‖ := by
    simp [norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ) (n := n)
      (f := thetaProfile τ) (x := x)]
  have hder_le :
      ‖iteratedDeriv n (thetaProfile τ) x‖ ≤ (‖c‖ ^ n) * Real.exp (-(-c.re) * x) := by
    have hexp : ‖thetaProfile τ x‖ = Real.exp (c.re * x) := by
      simp [thetaProfile, c, Complex.norm_exp, Complex.mul_re]
    have hiter' :
        ‖iteratedDeriv n (thetaProfile τ) x‖ = ‖c ^ n‖ * ‖thetaProfile τ x‖ := by
      calc
        ‖iteratedDeriv n (thetaProfile τ) x‖
            = ‖(c ^ n) * thetaProfile τ x‖ := by
                simp [thetaProfile_iteratedDeriv (τ := τ) (n := n) (r := x), c]
        _ = ‖c ^ n‖ * ‖thetaProfile τ x‖ := by simp
    have hre : Real.exp (c.re * x) = Real.exp (-(-c.re) * x) := by simp
    have heq :
        ‖iteratedDeriv n (thetaProfile τ) x‖ =
          (‖c‖ ^ n) * Real.exp (-(-c.re) * x) := by
      calc
        ‖iteratedDeriv n (thetaProfile τ) x‖
            = ‖c ^ n‖ * Real.exp (-(-c.re) * x) := by simpa [hexp, hre] using! hiter'
        _ = (‖c‖ ^ n) * Real.exp (-(-c.re) * x) := by simp [norm_pow]
    exact le_of_eq heq
  have hxpow : 0 ≤ x ^ k := by positivity
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (thetaProfile τ) x‖
        = x ^ k * ‖iteratedDeriv n (thetaProfile τ) x‖ := by
            simp [hxnorm, hiter]
    _ ≤ x ^ k * ((‖c‖ ^ n) * Real.exp (-(-c.re) * x)) :=
            mul_le_mul_of_nonneg_left hder_le hxpow
    _ = (‖c‖ ^ n) * (x ^ k * Real.exp (-(-c.re) * x)) := by ring_nf
    _ ≤ (‖c‖ ^ n) * C0 := by
            gcongr
            exact hC0 x hx

noncomputable def thetaKernel (τ : ℂ) (hτ : 0 < τ.im) : 𝓢(ℝ²⁴, ℂ) :=
  RadialSchwartz.Bridge.schwartzMap_norm_sq_of_contDiff_decay_nonneg (F := ℝ²⁴)
    (thetaProfile τ) (thetaProfile_contDiff τ) (thetaProfile_decay (τ := τ) hτ)

@[simp] lemma thetaKernel_apply (τ : ℂ) (hτ : 0 < τ.im) (x : ℝ²⁴) :
    thetaKernel τ hτ x =
      Complex.exp ((Real.pi : ℂ) * Complex.I * τ * ((‖x‖ ^ 2 : ℝ) : ℂ)) := by
  simp [thetaKernel, thetaProfile, mul_assoc, mul_comm]

lemma neg_one_div_im_pos {τ : ℂ} (hτ : 0 < τ.im) : 0 < (-1 / τ).im := by
  have hτ0 : τ ≠ 0 := by
    intro hτ0
    have hτ' := hτ
    simp [hτ0] at hτ'
  -- `(-1/τ).im = τ.im / normSq τ`.
  have him : (-1 / τ).im = τ.im / Complex.normSq τ := by
    -- `(-1/τ) = -(τ⁻¹)` and `im (τ⁻¹) = -τ.im / normSq τ`.
    simp [div_eq_mul_inv, Complex.inv_im, Complex.neg_im]
  simp_all

/-- Poisson summation gives the theta `S`-transform in rank `24`. -/
public theorem thetaSeries_transform_S (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L] [IsZLattice ℝ L]
    {τ : ℂ} (hτ : 0 < τ.im) :
    thetaSeries L (-1 / τ) =
      (1 / ZLattice.covolume L volume) * (τ / Complex.I) ^ (12 : ℂ) *
        thetaSeries (DualLattice L) τ := by
  -- Apply Poisson summation at `τ₁ = -1/τ`.
  have hτ₁ : 0 < (-1 / τ).im := neg_one_div_im_pos (τ := τ) hτ
  let f : 𝓢(ℝ²⁴, ℂ) := thetaKernel (-1 / τ) hτ₁
  have hps :=
    (SchwartzMap.poissonSummation_lattice (d := 24) (L := L) (f := f) (v := (0 : ℝ²⁴)))
  -- Rewrite the LHS as `thetaSeries L (-1/τ)`.
  have hlhs :
      (∑' ℓ : L, f (ℓ : ℝ²⁴)) = thetaSeries L (-1 / τ) := by
    simp [thetaSeries, thetaTerm, f, thetaKernel_apply, mul_assoc, mul_left_comm, mul_comm]
  -- Compute the Fourier transform of the Gaussian kernel.
  have hfourier :
      ∀ m : DualLattice L,
        (𝓕 (fun x : ℝ²⁴ => f x) (m : ℝ²⁴)) =
          ((τ / Complex.I) ^ (12 : ℂ)) *
            Complex.exp ((Real.pi : ℂ) * Complex.I * τ * ((‖(m : ℝ²⁴)‖ ^ 2 : ℝ) : ℂ)) := by
    intro m
    -- Use the explicit Fourier transform of the Gaussian.
    let τ₁ : ℂ := -1 / τ
    let b : ℂ := (Real.pi : ℂ) * (-Complex.I * τ₁)
    have hτ0 : τ ≠ 0 := by
      intro hτ0
      have hτ' := hτ
      simp [hτ0] at hτ'
    have hb' : b = (Real.pi : ℂ) * (Complex.I / τ) := by
      simp [b, τ₁, div_eq_mul_inv, mul_left_comm, mul_comm]
    have hb : 0 < b.re := by
      -- `b.re = π * τ₁.im` and `τ₁.im > 0`.
      have : b.re = Real.pi * τ₁.im := by
        simp [b, τ₁, mul_left_comm, mul_comm]
      nlinarith [this, Real.pi_pos, hτ₁]
    have hgauss :
        𝓕 (fun x : ℝ²⁴ => Complex.exp (-b * ‖x‖ ^ 2)) (m : ℝ²⁴) =
          (Real.pi / b) ^ (Module.finrank ℝ ℝ²⁴ / 2 : ℂ) *
            Complex.exp (-Real.pi ^ 2 * ‖(m : ℝ²⁴)‖ ^ 2 / b) := by
      simpa using! (fourier_gaussian_innerProductSpace (V := ℝ²⁴) hb (m : ℝ²⁴))
    -- Identify `f` with this Gaussian.
    have hf :
        (fun x : ℝ²⁴ => f x) = fun x : ℝ²⁴ => Complex.exp (-b * ‖x‖ ^ 2) := by
      funext x
      -- `f x = exp(π i τ₁ ‖x‖²) = exp (-b ‖x‖²)`.
      simp [f, thetaKernel_apply, τ₁, b, mul_assoc, mul_left_comm, mul_comm]
    -- Now simplify the Fourier formula at `τ₁ = -1/τ`.
    -- First rewrite `π/b = τ/I`.
    have hπb : (Real.pi : ℂ) / b = τ / Complex.I := by
      -- `b = π * (I/τ)`, hence `π/b = τ/I`.
      -- cancel `π` and invert.
      calc
        (Real.pi : ℂ) / b
            = (Real.pi : ℂ) / ((Real.pi : ℂ) * (Complex.I / τ)) := by simp [hb']
        _ = 1 / (Complex.I / τ) := by
              field_simp [Real.pi_ne_zero]
        _ = τ / Complex.I := by
              field_simp [hτ0, Complex.I_ne_zero]
    -- Second rewrite the exponent `-π^2/b` into `π i τ`.
    have hexp :
        (-((Real.pi : ℂ) ^ 2) / b) = (Real.pi : ℂ) * Complex.I * τ := by
      -- From `b = π * (I/τ)` we get `-π^2/b = -π/(I/τ) = π*I*τ`.
      calc
        -((Real.pi : ℂ) ^ 2) / b
            = -((Real.pi : ℂ) ^ 2) / ((Real.pi : ℂ) * (Complex.I / τ)) := by simp [hb']
        _ = -((Real.pi : ℂ)) / (Complex.I / τ) := by
              field_simp [Real.pi_ne_zero]
        _ = (Real.pi : ℂ) * Complex.I * τ := by
              field_simp [hτ0, Complex.I_ne_zero]
              ring_nf
              simp [Complex.I_sq]
    -- Put everything together.
    -- Replace `f` by the Gaussian, apply the Fourier formula, then simplify constants.
    calc
      (𝓕 (fun x : ℝ²⁴ => f x) (m : ℝ²⁴))
          = (Real.pi / b) ^ ((Module.finrank ℝ ℝ²⁴ : ℂ) / 2) *
              Complex.exp (-Real.pi ^ 2 * ‖(m : ℝ²⁴)‖ ^ 2 / b) := by
                simpa [hf] using! hgauss
      _ = (Real.pi / b) ^ (12 : ℂ) *
              Complex.exp (-Real.pi ^ 2 * ‖(m : ℝ²⁴)‖ ^ 2 / b) := by
                have h24 : (24 / 2 : ℂ) = (12 : ℂ) := by norm_num
                -- after `simp`-reductions, the exponent becomes the numeral `24/2`
                simp [h24]
      _ = ((τ / Complex.I) ^ (12 : ℂ)) *
            Complex.exp ((Real.pi : ℂ) * Complex.I * τ * ((‖(m : ℝ²⁴)‖ ^ 2 : ℝ) : ℂ)) := by
            -- rewrite the scalar factor
            rw [hπb]
            -- rewrite the exponent using `hexp`
            have harg :
                (-Real.pi ^ 2 * ‖(m : ℝ²⁴)‖ ^ 2 / b) =
                  (Real.pi : ℂ) * Complex.I * τ * ((‖(m : ℝ²⁴)‖ ^ 2 : ℝ) : ℂ) := by
              set X : ℂ := ((‖(m : ℝ²⁴)‖ ^ 2 : ℝ) : ℂ)
              calc
                (-Real.pi ^ 2 * ‖(m : ℝ²⁴)‖ ^ 2 / b) = (-((Real.pi : ℂ) ^ 2) / b) * X := by
                  simp [X, div_eq_mul_inv, mul_assoc, mul_comm]
                _ = ((Real.pi : ℂ) * Complex.I * τ) * X := by
                  simpa [mul_assoc] using! congrArg (fun z : ℂ => z * X) hexp
                _ =
                    (Real.pi : ℂ) * Complex.I * τ * ((‖(m : ℝ²⁴)‖ ^ 2 : ℝ) : ℂ) := by
                  simp [X, mul_assoc]
            exact ext (congrArg re (congrArg (HMul.hMul ((τ / I) ^ 12)) (congrArg cexp harg)))
              (congrArg im (congrArg (HMul.hMul ((τ / I) ^ 12)) (congrArg cexp harg)))
  -- Rewrite the RHS of Poisson summation using `hfourier` and identify the dual theta series.
  have hrhs :
      (1 / ZLattice.covolume L volume) *
          ∑' m : DualLattice L,
            (𝓕 (fun x : ℝ²⁴ => f x) (m : ℝ²⁴)) *
              Complex.exp (2 * Real.pi * Complex.I * ⟪(0 : ℝ²⁴), (m : ℝ²⁴)⟫_[ℝ]) =
        (1 / ZLattice.covolume L volume) * (τ / Complex.I) ^ (12 : ℂ) *
          thetaSeries (DualLattice L) τ := by
    -- The exponential factor at `v = 0` is `1`.
    simp [thetaSeries, thetaTerm, hfourier, mul_assoc, mul_left_comm, mul_comm, tsum_mul_left]
  -- Combine Poisson summation and the Fourier computation.
  have hps' :
      thetaSeries L (-1 / τ) =
        (1 / ZLattice.covolume L volume) *
          ∑' m : DualLattice L,
            (𝓕 (fun x : ℝ²⁴ => f x) (m : ℝ²⁴)) *
              Complex.exp (2 * Real.pi * Complex.I * ⟪(0 : ℝ²⁴), (m : ℝ²⁴)⟫_[ℝ]) := by
    have hps0 :
        (∑' ℓ : L, f (ℓ : ℝ²⁴)) =
          (1 / ZLattice.covolume L volume) *
            ∑' m : DualLattice L,
              (𝓕 (fun x : ℝ²⁴ => f x) (m : ℝ²⁴)) *
                Complex.exp (2 * Real.pi * Complex.I * ⟪(0 : ℝ²⁴), (m : ℝ²⁴)⟫_[ℝ]) := by
      simpa [zero_add] using! hps
    simpa using! hlhs.symm.trans hps0
  exact hps'.trans hrhs

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
