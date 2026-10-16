-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.MvPolyEval24Deriv
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.AvgLemmas24
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.MeanZeroHarmonics24.AtZero
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.SphereAvg24Lemmas
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Harmonic
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import SpherePacking.ForMathlib.CancelDenomsCompat

/-!
# Mean-zero for harmonics on the sphere

This file provides the analytic input used in the BS81 design bridge.
The strategy is:

1. Use integration by parts against the Gaussian weight `exp (-‖x‖²)` to show the Gaussian integral
   of a harmonic homogeneous polynomial of positive degree vanishes.
2. Use polar coordinates (`homeomorphUnitSphereProd`) to factor the Gaussian integral as a product
   of a radial integral and the sphere integral.
3. Conclude the sphere integral (hence `sphereAvg24`) is `0`.
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem

noncomputable section

open scoped BigOperators RealInnerProductSpace
open scoped ENNReal

open MeasureTheory Finset

open Uniqueness.BS81.LP
open Uniqueness.BS81.Thm14
open Uniqueness.BS81.Thm14.AdditionTheorem
open Uniqueness.BS81.LP.Gegenbauer24.PSD

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- Gaussian weight on `ℝ²⁴`: `exp (-‖x‖²)`. -/
noncomputable def gaussWeight (x : ℝ²⁴) : ℝ :=
  Real.exp (-(‖x‖ ^ 2))

lemma continuous_gaussWeight : Continuous (gaussWeight : ℝ²⁴ → ℝ) := by
  -- continuity of `x ↦ exp (-‖x‖²)`
  simpa [gaussWeight] using! (Real.continuous_exp.comp (continuous_norm.pow 2).neg)

@[simp] lemma gaussWeight_pos (x : ℝ²⁴) : 0 < gaussWeight x := by
  simp [gaussWeight, Real.exp_pos]

@[simp] lemma gaussWeight_nonneg (x : ℝ²⁴) : 0 ≤ gaussWeight x := (gaussWeight_pos x).le

lemma hasFDerivAt_gaussWeight (x : ℝ²⁴) :
    HasFDerivAt gaussWeight
      (gaussWeight x • (- (2 : ℝ) • innerSL ℝ x)) x := by
  -- `gaussWeight = exp (fun x => -‖x‖²)`, then use chain rule.
  have hneg : HasFDerivAt (fun x : ℝ²⁴ => -(‖x‖ ^ 2))
      (- (2 : ℝ) • innerSL ℝ x) x := by
    simpa [neg_mul, one_mul, gaussWeight, two_smul, smul_smul] using!
      ((hasStrictFDerivAt_norm_sq (x := x)).hasFDerivAt.neg)
  simpa [gaussWeight, smul_smul] using! hneg.exp

lemma fderiv_gaussWeight_apply_e24 (x : ℝ²⁴) (i : Var) :
    fderiv ℝ gaussWeight x (e24 i) = (-2 : ℝ) * (x i) * gaussWeight x := by
  have h := (hasFDerivAt_gaussWeight (x := x)).fderiv
  -- Evaluate the derivative on `e24 i`.
  have h' := congrArg (fun L : ℝ²⁴ →L[ℝ] ℝ => L (e24 i)) h
  -- The inner product with the standard basis vector is the `i`-th coordinate.
  have hinter : ⟪x, e24 i⟫ = x i := by
    -- Compare to `EuclideanSpace.single`.
    have he : e24 i = EuclideanSpace.single i (1 : ℝ) := by
      ext j
      simp [e24, EuclideanSpace.single_apply]
    -- Use the explicit inner-product computation.
    simpa [he] using! (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) (v := x))
  -- Finish.
  -- Rewrite `innerSL` as `inner` and simplify scalar multiplications.
  simp [gaussWeight, h', hinter, smul_eq_mul, mul_assoc, mul_comm]

/-!
## Homogeneity: scaling identity for `evalPoly24`
-/

lemma evalPoly24_smul_of_isHomogeneous {k : ℕ} {p : Poly} (hp : p.IsHomogeneous k)
    (r : ℝ) (x : ℝ²⁴) :
    evalPoly24 (y := r • x) p = r ^ k * evalPoly24 (y := x) p := by
  -- Expand `eval` as a finite sum over the support.
  unfold evalPoly24
  -- Rewrite both evaluations as explicit sums, and distribute the scalar factor on the RHS.
  simp (disch := simp) only [MvPolynomial.eval_eq', PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  -- After unfolding, everything is a `Finset` sum over monomials.
  -- The key point: all monomials in the support have total degree `k`.
  have hdeg : ∀ d : Var →₀ ℕ, d ∈ p.support → (∑ i : Var, d i) = k := by
    intro d hd
    have hcoeff : MvPolynomial.coeff d p ≠ 0 := by
      simpa [MvPolynomial.mem_support_iff] using! hd
    have hddeg' : d.degree = k := by
      by_contra hne
      exact hcoeff (hp.coeff_eq_zero hne)
    -- Convert `degree` to a full sum using `Finsupp.degree_eq_sum`.
    have : (∑ i : Var, d i) = d.degree := by
      simpa using! (Finsupp.degree_eq_sum (f := d) (R := ℕ)).symm
    simpa [this] using! hddeg'
  -- Simplify each term using `mul_pow` and the fact that `∏ i, r^(d i) = r^k`.
  refine Finset.sum_congr rfl ?_
  intro d hd
  have hddeg : (∑ i : Var, d i) = k := hdeg d (by simpa using! hd)
  -- Expand `∏ i, (r * x i) ^ d i` and pull out the `r ^ k` factor.
  simp [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hddeg]
  ring

/-!
## Radial integrability
-/

lemma integrable_norm_pow_mul_gaussWeight (k : ℕ) :
    Integrable (fun x : ℝ²⁴ => (‖x‖ ^ k) * gaussWeight x) volume := by
  -- Reduce to a one-dimensional integrability statement using
  -- `MeasureTheory.integrable_fun_norm_addHaar`.
  have hIoi :
      IntegrableOn (fun y : ℝ =>
          (y ^ (23 + k)) * Real.exp (-(y ^ 2))) (Set.Ioi (0 : ℝ)) := by
    -- Use the `rpow` integrability lemma, then rewrite `rpow`-powers as Nat powers.
    have h :=
      (integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ)) (hb := by positivity)
        (s := ((23 + k : ℕ) : ℝ)) (hs := by
          have : (0 : ℝ) ≤ ((23 + k : ℕ) : ℝ) := by positivity
          linarith))
    -- Convert the integrand.
    refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
    -- Rewrite the `rpow` as a Nat power, then simplify the exponential factor.
    have hp : y ^ ((23 + k : ℕ) : ℝ) = y ^ (23 + k) := by
      simpa using! (Real.rpow_natCast y (23 + k))
    -- Avoid rewriting `((23 + k : ℕ) : ℝ)` to `23 + (k : ℝ)` before applying `hp`.
    beta_reduce
    rw [hp]
    simp
  -- Apply the polar-coordinates integrability criterion.
  have hE :
      Integrable (fun x : ℝ²⁴ =>
        (fun r : ℝ => (r ^ k) * Real.exp (-(r ^ 2))) ‖x‖) volume := by
    -- `integrable_fun_norm_addHaar` expects integrability of `y^(dim-1) * f y` on `Ioi 0`.
    have hIoi' :
        IntegrableOn (fun y : ℝ =>
            (y ^ (Module.finrank ℝ ℝ²⁴ - 1)) •
              ((y ^ k) * Real.exp (-(y ^ 2))))
          (Set.Ioi (0 : ℝ)) := by
      -- Rewrite to the form proved above.
      simpa [smul_eq_mul, pow_add, mul_assoc, mul_left_comm, mul_comm] using! hIoi
    exact (MeasureTheory.integrable_fun_norm_addHaar (μ := (volume : Measure ℝ²⁴))
      (f := fun r : ℝ => (r ^ k) * Real.exp (-(r ^ 2)))).2 hIoi'
  -- Unfold `gaussWeight`.
  simpa [gaussWeight] using! hE

/-!
## Basic measurability/continuity of polynomial evaluation
-/

lemma continuous_evalPoly24 (p : Poly) :
    Continuous (fun x : ℝ²⁴ => evalPoly24 (y := x) p) := by
  -- `evalPoly24` is `MvPolynomial.eval` with the coordinate assignment.
  have hcoords : Continuous (fun x : ℝ²⁴ => (fun i : Var => x i)) := by
    -- All coordinate projections are continuous.
    fun_prop
  simpa [evalPoly24] using! (MvPolynomial.continuous_eval (p := p)).comp hcoords

lemma aestronglyMeasurable_evalPoly24 (p : Poly) :
    AEStronglyMeasurable (fun x : ℝ²⁴ => evalPoly24 (y := x) p) volume :=
  (continuous_evalPoly24 (p := p)).aestronglyMeasurable

/-!
## A crude growth bound for homogeneous polynomials
-/

lemma abs_evalPoly24_le_coeffSum_mul_norm_pow {k : ℕ} {p : Poly} (hp : p.IsHomogeneous k) :
    ∃ C : ℝ, ∀ x : ℝ²⁴, |evalPoly24 (y := x) p| ≤ C * ‖x‖ ^ k := by
  let C : ℝ := (p.support.sum fun d => |p.coeff d|)
  refine ⟨C, ?_⟩
  intro x
  -- Expand evaluation as a sum over monomials.
  have heval :
      evalPoly24 (y := x) p =
        ∑ d ∈ p.support, p.coeff d * ∏ i : Var, (x i) ^ d i := by
    -- `eval_eq'` gives exactly this.
    simpa [evalPoly24] using! (MvPolynomial.eval_eq' (X := fun i : Var => x i) (f := p))
  -- Take absolute values and apply triangle inequality.
  have habs :
      |evalPoly24 (y := x) p| ≤
        ∑ d ∈ p.support, |p.coeff d * ∏ i : Var, (x i) ^ d i| := by
    -- `abs_sum_le_sum_abs` for a finite sum.
    simpa [heval] using!
      (abs_sum_le_sum_abs (s := p.support)
        (f := fun d => p.coeff d * ∏ i : Var, (x i) ^ d i))
  -- Bound each monomial by `‖x‖^k`.
  have hterm (d : Var →₀ ℕ) (hd : d ∈ p.support) :
      |p.coeff d * ∏ i : Var, (x i) ^ d i| ≤ |p.coeff d| * ‖x‖ ^ k := by
    have hx_le (i : Var) : |x i| ≤ ‖x‖ := by
      have : ‖x i‖ ≤ ‖x‖ :=
        PiLp.norm_apply_le (p := (2 : ℝ≥0∞)) (β := fun _ : Var => ℝ) x i
      simpa [Real.norm_eq_abs] using! this
    have hcoeff : MvPolynomial.coeff d p ≠ 0 := by
      simpa [MvPolynomial.mem_support_iff] using! hd
    have hddeg : (∑ i : Var, d i) = k := by
      have hddeg' : d.degree = k := by
        by_contra hne
        exact hcoeff (hp.coeff_eq_zero hne)
      have : (∑ i : Var, d i) = d.degree := by
        simpa using! (Finsupp.degree_eq_sum (f := d) (R := ℕ)).symm
      simpa [this] using! hddeg'
    -- Estimate the product term.
    have hprod :
        |∏ i : Var, (x i) ^ d i| ≤ ‖x‖ ^ k := by
      -- Work with `Finset.univ` to use standard `Finset` lemmas.
      let s : Finset Var := Finset.univ
      have habs_prod :
          |∏ i ∈ s, (x i) ^ d i| = ∏ i ∈ s, |(x i) ^ d i| := by
        simpa [s] using! (abs_prod (s := (Finset.univ : Finset Var)) (f := fun i => (x i) ^ d i))
      have hpow_abs : (∏ i ∈ s, |(x i) ^ d i|) = ∏ i ∈ s, |x i| ^ d i := by
        refine Finset.prod_congr rfl ?_
        intro i hi
        simp [abs_pow]
      have hle :
          (∏ i ∈ s, |x i| ^ d i) ≤ ∏ i ∈ s, ‖x‖ ^ d i := by
        refine Finset.prod_le_prod ?_ ?_
        · intro i hi
          positivity
        · intro i hi
          exact pow_le_pow_left₀ (abs_nonneg (x i)) (hx_le i) (d i)
      have hsimp :
          (∏ i ∈ s, ‖x‖ ^ d i) = ‖x‖ ^ (∑ i ∈ s, d i) := by
        exact prod_pow_eq_pow_sum s ⇑d ‖x‖
      have hsum : (∑ i ∈ s, d i) = (∑ i : Var, d i) := by
        simp [s]
      -- Assemble.
      have :
          |∏ i ∈ s, (x i) ^ d i| ≤ ‖x‖ ^ k := by
        calc
          |∏ i ∈ s, (x i) ^ d i| = ∏ i ∈ s, |(x i) ^ d i| := habs_prod
          _ = ∏ i ∈ s, |x i| ^ d i := hpow_abs
          _ ≤ ∏ i ∈ s, ‖x‖ ^ d i := hle
          _ = ‖x‖ ^ (∑ i ∈ s, d i) := hsimp
          _ = ‖x‖ ^ (∑ i : Var, d i) := by simp [hsum]
          _ = ‖x‖ ^ k := by simp [hddeg]
      simpa [s] using! this
    -- Combine.
    calc
      |p.coeff d * ∏ i : Var, (x i) ^ d i|
          = |p.coeff d| * |∏ i : Var, (x i) ^ d i| := by
              simp [abs_mul]
      _ ≤ |p.coeff d| * ‖x‖ ^ k := by
              exact mul_le_mul_of_nonneg_left hprod (by positivity)
  -- Finish by summing the termwise bounds and factoring out `‖x‖^k`.
  have hsum :
      (∑ d ∈ p.support, |p.coeff d * ∏ i : Var, (x i) ^ d i|) ≤
        (p.support.sum fun d => |p.coeff d|) * ‖x‖ ^ k := by
    -- First replace each term using `hterm`.
    have :
        (∑ d ∈ p.support, |p.coeff d * ∏ i : Var, (x i) ^ d i|) ≤
          ∑ d ∈ p.support, |p.coeff d| * ‖x‖ ^ k := by
      exact sum_le_sum hterm
    -- Then factor out `‖x‖^k`.
    refine this.trans ?_
    simp [Finset.sum_mul]
  -- Put the pieces together.
  have : |evalPoly24 (y := x) p| ≤ (p.support.sum fun d => |p.coeff d|) * ‖x‖ ^ k :=
    le_trans habs (le_trans (by simpa using! hsum) (le_rfl))
  simpa [C] using! this

lemma integrable_evalPoly24_mul_gaussWeight_of_isHomogeneous {k : ℕ} {p : Poly}
    (hp : p.IsHomogeneous k) :
    Integrable (fun x : ℝ²⁴ => evalPoly24 (y := x) p * gaussWeight x) volume := by
  rcases abs_evalPoly24_le_coeffSum_mul_norm_pow (p := p) hp with ⟨C, hC⟩
  -- Dominate by a radial integrable function.
  have hdom :
      ∀ x : ℝ²⁴, ‖evalPoly24 (y := x) p * gaussWeight x‖ ≤
        |C| * ((‖x‖ ^ k) * gaussWeight x) := by
    intro x
    have hg : 0 ≤ gaussWeight x := gaussWeight_nonneg x
    have : |evalPoly24 (y := x) p| ≤ C * ‖x‖ ^ k := hC x
    -- Use `‖a*b‖ = |a|*|b|` in `ℝ` and `|gaussWeight x| = gaussWeight x`.
    have habs :
        |evalPoly24 (y := x) p * gaussWeight x| ≤ |C| * (‖x‖ ^ k * gaussWeight x) := by
      have hgabs : |gaussWeight x| = gaussWeight x := by
        simp [abs_of_nonneg hg]
      -- Convert to absolute values.
      have h1 :
          |evalPoly24 (y := x) p * gaussWeight x| =
            |evalPoly24 (y := x) p| * gaussWeight x := by
        simp [abs_mul, hgabs]
      -- Bound `|eval|` by `|C| * ‖x‖^k`.
      have h2 : |evalPoly24 (y := x) p| ≤ |C| * ‖x‖ ^ k := by
        -- from `hC`, taking abs of the constant factor.
        exact (this.trans (by
          have : C * ‖x‖ ^ k ≤ |C| * ‖x‖ ^ k := by
            exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
          simpa using! this))
      -- Combine.
      calc
        |evalPoly24 (y := x) p * gaussWeight x|
            = |evalPoly24 (y := x) p| * gaussWeight x := h1
        _ ≤ (|C| * ‖x‖ ^ k) * gaussWeight x := by
              exact mul_le_mul_of_nonneg_right h2 hg
        _ = |C| * (‖x‖ ^ k * gaussWeight x) := by ring_nf
    simpa [Real.norm_eq_abs] using! habs
  have hrad : Integrable (fun x : ℝ²⁴ => |C| * ((‖x‖ ^ k) * gaussWeight x)) volume :=
    (integrable_norm_pow_mul_gaussWeight (k := k)).const_mul _
  refine
    Integrable.mono' hrad
      ((aestronglyMeasurable_evalPoly24 (p := p)).mul continuous_gaussWeight.aestronglyMeasurable)
      (ae_of_all _ hdom)

/-!
## Gaussian integration: harmonic ⇒ Gaussian integral `0`

We show that if `p` is homogeneous of degree `k ≥ 1` and harmonic (`Δ p = 0`), then
`∫ p(x) * exp(-‖x‖²) dx = 0`.

This uses integration by parts in each coordinate and Euler's identity.
-/

lemma differentiable_evalPoly24 (p : Poly) :
    Differentiable ℝ (fun x : ℝ²⁴ => evalPoly24 (y := x) p) := by
  intro x
  exact (hasFDerivAt_evalPoly24 (p := p) (x := x)).differentiableAt

lemma differentiable_gaussWeight : Differentiable ℝ (gaussWeight : ℝ²⁴ → ℝ) := by
  intro x
  exact (hasFDerivAt_gaussWeight (x := x)).differentiableAt

lemma integrable_evalPoly24_mul_fderiv_gaussWeight_apply_e24_of_isHomogeneous
    {k : ℕ} {p : Poly} (hp : p.IsHomogeneous k) (i : Var) :
    Integrable (fun x : ℝ²⁴ =>
      evalPoly24 (y := x) p * (fderiv ℝ gaussWeight x (e24 i))) volume := by
  -- Use the explicit formula for the derivative of the Gaussian weight and reduce to
  -- integrability of a homogeneous polynomial of degree `k + 1`.
  have hX : (MvPolynomial.X i * p).IsHomogeneous (k + 1) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using!
      (MvPolynomial.isHomogeneous_X (R := ℝ) i).mul hp
  have hInt :
      Integrable (fun x : ℝ²⁴ =>
        evalPoly24 (y := x) (MvPolynomial.X i * p) * gaussWeight x) volume :=
    integrable_evalPoly24_mul_gaussWeight_of_isHomogeneous (p := (MvPolynomial.X i * p)) hX
  -- Rewrite `evalPoly24 (X i * p)` and `fderiv gaussWeight` pointwise.
  have hcongr :
      (fun x : ℝ²⁴ =>
          evalPoly24 (y := x) p * (fderiv ℝ gaussWeight x (e24 i))) =
        fun x : ℝ²⁴ =>
          (-2 : ℝ) * (evalPoly24 (y := x) (MvPolynomial.X i * p) * gaussWeight x) := by
    funext x
    simp [fderiv_gaussWeight_apply_e24, evalPoly24, gaussWeight, mul_assoc, mul_left_comm, mul_comm]
  simpa [hcongr] using! hInt.const_mul (-2 : ℝ)

lemma integrable_fderiv_evalPoly24_mul_gaussWeight_apply_e24_of_isHomogeneous
    {k : ℕ} {p : Poly} (hp : p.IsHomogeneous k) (i : Var) :
    Integrable (fun x : ℝ²⁴ =>
      (fderiv ℝ (fun x : ℝ²⁴ => evalPoly24 (y := x) p) x (e24 i)) * gaussWeight x) volume := by
  -- Reduce to the integrability lemma for `pderiv i p`, whose degree is `k-1`.
  have hp' : (MvPolynomial.pderiv i p).IsHomogeneous (k - 1) := hp.pderiv (i := i)
  have hInt :
      Integrable (fun x : ℝ²⁴ =>
        evalPoly24 (y := x) (MvPolynomial.pderiv i p) * gaussWeight x) volume :=
    integrable_evalPoly24_mul_gaussWeight_of_isHomogeneous (p := MvPolynomial.pderiv i p) hp'
  have hcongr :
      (fun x : ℝ²⁴ =>
          (fderiv ℝ (fun x : ℝ²⁴ => evalPoly24 (y := x) p) x (e24 i)) * gaussWeight x) =
        fun x : ℝ²⁴ =>
          evalPoly24 (y := x) (MvPolynomial.pderiv i p) * gaussWeight x := by
    funext x
    simp [fderiv_evalPoly24_apply_e24]
  simpa [hcongr] using! hInt

lemma ibp_gaussWeight_evalPoly24_pderiv
    {k : ℕ} {p : Poly} (hp : p.IsHomogeneous k) (i : Var) :
    (∫ x : ℝ²⁴, (evalPoly24 (y := x) (MvPolynomial.pderiv i p)) *
        (fderiv ℝ gaussWeight x (e24 i)) ∂volume) =
      - ∫ x : ℝ²⁴,
          (fderiv ℝ (fun x : ℝ²⁴ => evalPoly24 (y := x) (MvPolynomial.pderiv i p)) x (e24 i)) *
            gaussWeight x ∂volume := by
  -- Apply integration by parts with `f = eval(pderiv i p)` and `g = gaussWeight`.
  have hf'g :
      Integrable (fun x : ℝ²⁴ =>
        (fderiv ℝ (fun x : ℝ²⁴ => evalPoly24 (y := x) (MvPolynomial.pderiv i p)) x (e24 i)) *
          gaussWeight x) volume := by
    -- `pderiv i p` is homogeneous of degree `k-1`, so its directional derivative has degree `k-2`.
    have hp1 : (MvPolynomial.pderiv i p).IsHomogeneous (k - 1) := hp.pderiv (i := i)
    exact integrable_fderiv_evalPoly24_mul_gaussWeight_apply_e24_of_isHomogeneous hp1 i
  have hfg' :
      Integrable (fun x : ℝ²⁴ =>
        (evalPoly24 (y := x) (MvPolynomial.pderiv i p)) *
          (fderiv ℝ gaussWeight x (e24 i))) volume := by
    have hp1 : (MvPolynomial.pderiv i p).IsHomogeneous (k - 1) := hp.pderiv (i := i)
    exact integrable_evalPoly24_mul_fderiv_gaussWeight_apply_e24_of_isHomogeneous hp1 i
  have hfg :
      Integrable (fun x : ℝ²⁴ =>
        (evalPoly24 (y := x) (MvPolynomial.pderiv i p)) * gaussWeight x) volume := by
    have hp1 : (MvPolynomial.pderiv i p).IsHomogeneous (k - 1) := hp.pderiv (i := i)
    exact integrable_evalPoly24_mul_gaussWeight_of_isHomogeneous (p := MvPolynomial.pderiv i p) hp1
  simpa using!
    (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure ℝ²⁴))
      (f := fun x : ℝ²⁴ => evalPoly24 (y := x) (MvPolynomial.pderiv i p))
      (g := gaussWeight) (v := e24 i) hf'g hfg' hfg
      (fun x _ => (differentiable_evalPoly24 (p := MvPolynomial.pderiv i p)) x)
      (fun x _ => differentiable_gaussWeight x))

lemma gaussIntegral_evalPoly24_eq_zero_of_isHomogeneous_of_harmonic
    {k : ℕ} (hk : 1 ≤ k) {p : Poly} (hp : p.IsHomogeneous k)
    (hharm : Uniqueness.BS81.LP.Gegenbauer24.PSD.Harmonic.laplacian p = 0) :
    (∫ x : ℝ²⁴, evalPoly24 (y := x) p * gaussWeight x ∂volume) = 0 := by
  -- Sum the integration-by-parts identities over `i`.
  have hsum_ibp :
      (∫ x : ℝ²⁴,
          (∑ i : Var,
              evalPoly24 (y := x) (MvPolynomial.pderiv i p) *
                fderiv ℝ gaussWeight x (e24 i)) ∂volume) =
        - ∫ x : ℝ²⁴,
            (∑ i : Var,
                (fderiv ℝ
                    (fun x : ℝ²⁴ =>
                      evalPoly24 (y := x) (MvPolynomial.pderiv i p)) x (e24 i)) *
                  gaussWeight x) ∂volume := by
    have hleft (i : Var) :
        Integrable (fun x : ℝ²⁴ =>
          evalPoly24 (y := x) (MvPolynomial.pderiv i p) *
            fderiv ℝ gaussWeight x (e24 i)) volume := by
      have hp1 : (MvPolynomial.pderiv i p).IsHomogeneous (k - 1) := hp.pderiv (i := i)
      exact integrable_evalPoly24_mul_fderiv_gaussWeight_apply_e24_of_isHomogeneous hp1 i
    have hright (i : Var) :
        Integrable (fun x : ℝ²⁴ =>
          (fderiv ℝ (fun x : ℝ²⁴ => evalPoly24 (y := x) (MvPolynomial.pderiv i p)) x (e24 i)) *
            gaussWeight x) volume := by
      have hp1 : (MvPolynomial.pderiv i p).IsHomogeneous (k - 1) := hp.pderiv (i := i)
      exact integrable_fderiv_evalPoly24_mul_gaussWeight_apply_e24_of_isHomogeneous hp1 i
    -- Use linearity of the integral and the pointwise IBP identity.
    have hpoint (i : Var) :
        (∫ x : ℝ²⁴,
            (evalPoly24 (y := x) (MvPolynomial.pderiv i p)) * (fderiv ℝ gaussWeight x (e24 i))
            ∂volume) =
          - ∫ x : ℝ²⁴,
              (fderiv ℝ (fun x : ℝ²⁴ => evalPoly24 (y := x) (MvPolynomial.pderiv i p)) x (e24 i)) *
                gaussWeight x ∂volume := by
      simpa using! ibp_gaussWeight_evalPoly24_pderiv (p := p) hp i
    -- Convert sums of integrals to integrals of sums.
    simp [MeasureTheory.integral_finset_sum, hleft, hright, hpoint, Finset.sum_neg_distrib] at *
  -- Rewrite both sides using the explicit derivative formulas.
  have hleft_simp :
      (∫ x : ℝ²⁴,
          (∑ i : Var, (evalPoly24 (y := x) (MvPolynomial.pderiv i p)) *
              (fderiv ℝ gaussWeight x (e24 i))) ∂volume) =
        ∫ x : ℝ²⁴, (-2 : ℝ) * (evalPoly24 (y := x)
          (∑ i : Var, MvPolynomial.X i * MvPolynomial.pderiv i p) * gaussWeight x) ∂volume := by
    -- Move the sum inside `evalPoly24` and use `fderiv_gaussWeight_apply_e24`.
    refine MeasureTheory.integral_congr_ae ?_
    refine ae_of_all _ ?_
    intro x
    simp [fderiv_gaussWeight_apply_e24, evalPoly24, gaussWeight, mul_assoc, mul_left_comm,
      Finset.mul_sum, Finset.sum_mul]
  have hright_simp :
      (∫ x : ℝ²⁴,
          (∑ i : Var,
              (fderiv ℝ
                  (fun x : ℝ²⁴ =>
                    evalPoly24 (y := x) (MvPolynomial.pderiv i p)) x (e24 i)) *
                gaussWeight x) ∂volume) =
        ∫ x : ℝ²⁴, evalPoly24 (y := x)
          (Uniqueness.BS81.LP.Gegenbauer24.PSD.Harmonic.laplacian p) * gaussWeight x ∂volume := by
    refine MeasureTheory.integral_congr_ae ?_
    refine ae_of_all _ ?_
    intro x
    -- Rewrite each directional derivative as a polynomial `pderiv` using the calculus bridge,
    -- then compare with the definition of the Laplacian.
    calc
      (∑ i : Var,
            (fderiv ℝ
                (fun x : ℝ²⁴ =>
                  evalPoly24 (y := x) (MvPolynomial.pderiv i p)) x (e24 i)) *
              gaussWeight x) =
          ∑ i : Var,
            evalPoly24 (y := x) (MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) *
              gaussWeight x := by
            simp [fderiv_evalPoly24_apply_e24]
      _ =
          (∑ i : Var, evalPoly24 (y := x) (MvPolynomial.pderiv i (MvPolynomial.pderiv i p))) *
            gaussWeight x := by
            -- Factor out `gaussWeight x` on the right.
            exact Eq.symm
              (sum_mul univ (fun i => evalPoly24 x ((MvPolynomial.pderiv i)
              ((MvPolynomial.pderiv i) p))) (gaussWeight x))
      _ = evalPoly24 (y := x)
            (Uniqueness.BS81.LP.Gegenbauer24.PSD.Harmonic.laplacian p) * gaussWeight x := by
            simp [Uniqueness.BS81.LP.Gegenbauer24.PSD.Harmonic.laplacian_apply, evalPoly24]
  -- Combine.
  set q : Poly := ∑ i : Var, MvPolynomial.X i * MvPolynomial.pderiv i p
  have hEq :
      (∫ x : ℝ²⁴, (-2 : ℝ) * (evalPoly24 (y := x) q * gaussWeight x) ∂volume) =
        - ∫ x : ℝ²⁴,
            evalPoly24 (y := x) (Uniqueness.BS81.LP.Gegenbauer24.PSD.Harmonic.laplacian p) *
              gaussWeight x ∂volume := by
    -- Start from `hsum_ibp` and rewrite.
    simpa [hleft_simp, hright_simp, q, mul_assoc] using! hsum_ibp
  -- Use harmonicity to kill the RHS.
  have hrhs :
      (∫ x : ℝ²⁴,
          evalPoly24 (y := x) (Uniqueness.BS81.LP.Gegenbauer24.PSD.Harmonic.laplacian p) *
            gaussWeight x ∂volume) = 0 := by
    simp [hharm, evalPoly24]
  have hsum0 :
      (∫ x : ℝ²⁴, (-2 : ℝ) * (evalPoly24 (y := x) q * gaussWeight x) ∂volume) = 0 := by
    calc
      (∫ x : ℝ²⁴, (-2 : ℝ) * (evalPoly24 (y := x) q * gaussWeight x) ∂volume) =
          - ∫ x : ℝ²⁴,
              evalPoly24 (y := x) (Uniqueness.BS81.LP.Gegenbauer24.PSD.Harmonic.laplacian p) *
                gaussWeight x ∂volume := hEq
      _ = 0 := by
          rw [hrhs]
          simp
  -- Euler identity to simplify the LHS to a nonzero scalar multiple of the desired integral.
  have heuler :
      q = k • p := by
    simpa [q] using! (hp.sum_X_mul_pderiv (φ := p))
  -- Extract the integral we want.
  have hk0 : (k : ℝ) ≠ 0 := by
    have : k ≠ 0 :=
      Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk)
    exact_mod_cast this
  have hlin :
      (∫ x : ℝ²⁴,
          evalPoly24 (y := x) q * gaussWeight x ∂volume) =
        (k : ℝ) * (∫ x : ℝ²⁴, evalPoly24 (y := x) p * gaussWeight x ∂volume) := by
    have hpt :
      (fun x : ℝ²⁴ =>
            evalPoly24 (y := x) q * gaussWeight x) =
          fun x : ℝ²⁴ =>
            (k : ℝ) * (evalPoly24 (y := x) p * gaussWeight x) := by
      funext x
      -- Evaluate Euler's identity at `x` and push `nsmul` through evaluation.
      simp [heuler, evalPoly24, nsmul_eq_mul, mul_assoc]
    calc
      (∫ x : ℝ²⁴,
          evalPoly24 (y := x) q * gaussWeight x ∂volume) =
          ∫ x : ℝ²⁴, (k : ℝ) * (evalPoly24 (y := x) p * gaussWeight x) ∂volume := by
            simp [hpt]
      _ = (k : ℝ) * (∫ x : ℝ²⁴, evalPoly24 (y := x) p * gaussWeight x ∂volume) :=
            integral_const_mul ↑k fun a => evalPoly24 a p * gaussWeight a
  -- Convert `hsum0` to a product equation `(-2) * (k * I) = 0` and cancel.
  have hmain :
      (-2 : ℝ) * ((k : ℝ) * (∫ x : ℝ²⁴, evalPoly24 (y := x) p * gaussWeight x ∂volume)) = 0 := by
    have hconst :
      (∫ x : ℝ²⁴, (-2 : ℝ) * (evalPoly24 (y := x)
            q * gaussWeight x) ∂volume) =
          (-2 : ℝ) * (∫ x : ℝ²⁴,
            evalPoly24 (y := x) q * gaussWeight x ∂volume) :=
      integral_const_mul (-2) fun a => evalPoly24 a q * gaussWeight a
    -- Convert `hsum0` to a product equation and substitute `hlin`.
    have hsum0_neg :
      (∫ x : ℝ²⁴, (-2 : ℝ) * (evalPoly24 (y := x)
            q * gaussWeight x) ∂volume) = 0 := by
      simpa using! hsum0
    have hmul :
      (-2 : ℝ) * (∫ x : ℝ²⁴,
          evalPoly24 (y := x) q * gaussWeight x ∂volume) = 0 := by
      calc
        (-2 : ℝ) * (∫ x : ℝ²⁴,
            evalPoly24 (y := x) q * gaussWeight x ∂volume)
            =
            (∫ x : ℝ²⁴, (-2 : ℝ) * (evalPoly24 (y := x)
                q * gaussWeight x) ∂volume) := by
              simpa using! hconst.symm
        _ = 0 := hsum0_neg
    -- Substitute the Euler-integral identity.
    exact CancelDenoms.derive_trans (id (Eq.symm hlin)) hmul
  have hki : (k : ℝ) * (∫ x : ℝ²⁴, evalPoly24 (y := x) p * gaussWeight x ∂volume) = 0 :=
    (mul_eq_zero.mp hmain).resolve_left (by norm_num)
  exact (mul_eq_zero.mp hki).resolve_left hk0

/-!
## Polar coordinates: Gaussian integral factors as sphere integral × radial integral
-/

lemma gaussIntegral_evalPoly24_eq_sphereIntegral_mul_radialIntegral
    {k : ℕ} {p : Poly} (hp : p.IsHomogeneous k) :
    (∫ x : ℝ²⁴, evalPoly24 (y := x) p * gaussWeight x ∂volume) =
      (∫ u : S23, evalPoly24 (y := u.1) p ∂sphereMeasure24) *
        (∫ r : Set.Ioi (0 : ℝ), (r.1 ^ k) * Real.exp (-(r.1 ^ (2 : ℕ)))
          ∂(Measure.volumeIoiPow 23)) := by
  -- `sphereMeasure24` is a finite measure, hence `SFinite`; this is needed for product integrals.
  haveI : MeasureTheory.IsFiniteMeasure sphereMeasure24 := ⟨
    sphereMeasure24_univ_lt_top⟩
  haveI : MeasureTheory.SFinite sphereMeasure24 := by infer_instance
  -- Reduce to the complement of `{0}` using `volume.restrict ({0}ᶜ) = volume`.
  have hrestrict : (volume.restrict ({(0 : ℝ²⁴)}ᶜ : Set ℝ²⁴)) = (volume : Measure ℝ²⁴) :=
    restrict_compl_singleton (μ := (volume : Measure ℝ²⁴)) (0 : ℝ²⁴)
  have hmeas : MeasurableSet ({(0 : ℝ²⁴)}ᶜ : Set ℝ²⁴) := (measurableSet_singleton _).compl
  -- Switch to an integral on the subtype `{0}ᶜ` with the comap measure.
  have hsub :
      (∫ x : ℝ²⁴, evalPoly24 (y := x) p * gaussWeight x ∂volume) =
        ∫ x : ({(0 : ℝ²⁴)}ᶜ : Set ℝ²⁴),
          evalPoly24 (y := (x.1 : ℝ²⁴)) p * gaussWeight (x.1 : ℝ²⁴)
            ∂(volume.comap Subtype.val) := by
    calc
      (∫ x : ℝ²⁴, evalPoly24 (y := x) p * gaussWeight x ∂volume) =
          ∫ x : ℝ²⁴, evalPoly24 (y := x) p * gaussWeight x
            ∂(volume.restrict ({(0 : ℝ²⁴)}ᶜ : Set ℝ²⁴)) := by
            simp [hrestrict]
      _ = ∫ x in ({(0 : ℝ²⁴)}ᶜ : Set ℝ²⁴), evalPoly24 (y := x) p * gaussWeight x ∂volume := rfl
      _ = ∫ x : ({(0 : ℝ²⁴)}ᶜ : Set ℝ²⁴),
                evalPoly24 (y := (x.1 : ℝ²⁴)) p * gaussWeight (x.1 : ℝ²⁴)
                  ∂(volume.comap Subtype.val) := by
            -- `integral_subtype_comap` is oriented in the other direction.
            symm
            simpa [hmeas] using!
              (MeasureTheory.integral_subtype_comap (μ := (volume : Measure ℝ²⁴))
                (s := ({(0 : ℝ²⁴)}ᶜ : Set ℝ²⁴)) (hs := hmeas)
                (f := fun x : ℝ²⁴ => evalPoly24 (y := x) p * gaussWeight x))
  -- Change variables using the polar-coordinate homeomorphism.
  have hMP :
      MeasurePreserving (homeomorphUnitSphereProd ℝ²⁴) (volume.comap Subtype.val)
        (sphereMeasure24.prod (Measure.volumeIoiPow 23)) := by
    -- This is `measurePreserving_homeomorphUnitSphereProd` specialized to `E = ℝ²⁴`.
    -- `sphereMeasure24 = volume.toSphere`.
    simpa [sphereMeasure24] using!
      ((volume : Measure ℝ²⁴).measurePreserving_homeomorphUnitSphereProd (E := ℝ²⁴))
  have hpolar :
      (∫ x : ({(0 : ℝ²⁴)}ᶜ : Set ℝ²⁴),
          evalPoly24 (y := (x.1 : ℝ²⁴)) p * gaussWeight (x.1 : ℝ²⁴) ∂(volume.comap Subtype.val)) =
        ∫ z : (S23 × Set.Ioi (0 : ℝ)),
          (evalPoly24 (y := ((homeomorphUnitSphereProd ℝ²⁴).symm z).1) p) *
            gaussWeight (((homeomorphUnitSphereProd ℝ²⁴).symm z).1)
              ∂(sphereMeasure24.prod (Measure.volumeIoiPow 23)) := by
    -- Use `MeasurePreserving.integral_comp` with `g z = F ((homeomorph).symm z)`.
    simpa using!
      (MeasurePreserving.integral_comp
        (μ := (volume.comap Subtype.val))
        (ν := (sphereMeasure24.prod (Measure.volumeIoiPow 23)))
        (f := homeomorphUnitSphereProd ℝ²⁴) hMP (Homeomorph.measurableEmbedding _)
        (fun z : (S23 × Set.Ioi (0 : ℝ)) =>
          (evalPoly24 (y := ((homeomorphUnitSphereProd ℝ²⁴).symm z).1) p) *
            gaussWeight (((homeomorphUnitSphereProd ℝ²⁴).symm z).1)))
  -- Simplify the product integral using homogeneity of `p` and the unit-sphere norm.
  have hsimp :
      (fun z : (S23 × Set.Ioi (0 : ℝ)) =>
          (evalPoly24 (y := ((homeomorphUnitSphereProd ℝ²⁴).symm z).1) p) *
            gaussWeight (((homeomorphUnitSphereProd ℝ²⁴).symm z).1)) =
        fun z : (S23 × Set.Ioi (0 : ℝ)) =>
          (evalPoly24 (y := z.1.1) p) * ((z.2.1 ^ k) * Real.exp (-(z.2.1 ^ (2 : ℕ)))) := by
    funext z
    rcases z with ⟨u, r⟩
    -- `((homeomorphUnitSphereProd _).symm (u,r)).1 = r • u`.
    have hcoe : ((homeomorphUnitSphereProd ℝ²⁴).symm (u, r)).1 = (r.1 : ℝ) • (u.1 : ℝ²⁴) := by
      -- `simps` lemma from `RadialEquiv`.
      exact homeomorphUnitSphereProd_symm_apply_coe (E := ℝ²⁴) (x := (u, r))
    -- Homogeneity gives the scaling of `evalPoly24`.
    have heval :
        evalPoly24 (y := (r.1 : ℝ) • (u.1 : ℝ²⁴)) p = (r.1 ^ k) * evalPoly24 (y := (u.1 : ℝ²⁴)) p :=
      evalPoly24_smul_of_isHomogeneous (p := p) hp (r := (r.1 : ℝ)) (x := (u.1 : ℝ²⁴))
    -- On the unit sphere, `‖u‖ = 1`, so `gaussWeight (r • u) = exp (-(r^2))`.
    have hu : ‖(u.1 : ℝ²⁴)‖ = (1 : ℝ) := by
      -- `u.2 : u.1 ∈ sphere 0 1`.
      exact norm_eq_of_mem_sphere u
    have hgauss :
        gaussWeight ((r.1 : ℝ) • (u.1 : ℝ²⁴)) = Real.exp (-(r.1 ^ (2 : ℕ))) := by
      -- `‖r • u‖ = r * ‖u‖ = r`.
      simp [gaussWeight, norm_smul, hu]
    -- Finish.
    simp [hcoe, heval, hgauss, mul_assoc, mul_left_comm, mul_comm]
  -- Factor the product integral.
  have hfactor :
      (∫ z : (S23 × Set.Ioi (0 : ℝ)),
          (evalPoly24 (y := z.1.1) p) * ((z.2.1 ^ k) * Real.exp (-(z.2.1 ^ (2 : ℕ))))
          ∂(sphereMeasure24.prod (Measure.volumeIoiPow 23))) =
        (∫ u : S23, evalPoly24 (y := u.1) p ∂sphereMeasure24) *
          (∫ r : Set.Ioi (0 : ℝ), (r.1 ^ k) * Real.exp (-(r.1 ^ (2 : ℕ)))
            ∂(Measure.volumeIoiPow 23)) := by
    -- Use `integral_prod_mul` with `f u = evalPoly24 u p` and `g r = r^k * exp(-r^2)`.
    simpa [mul_assoc, mul_left_comm, mul_comm] using!
      (MeasureTheory.integral_prod_mul (μ := sphereMeasure24) (ν := (Measure.volumeIoiPow 23))
        (fun u : S23 => evalPoly24 (y := u.1) p)
        (fun r : Set.Ioi (0 : ℝ) => (r.1 ^ k) * Real.exp (-(r.1 ^ (2 : ℕ)))))
  -- Assemble the chain.
  simp_all

lemma radialIntegral_pos (k : ℕ) :
    0 < ∫ r : Set.Ioi (0 : ℝ), (r.1 ^ k) * Real.exp (-(r.1 ^ (2 : ℕ)))
      ∂(Measure.volumeIoiPow 23) := by
  -- Use `integral_pos_iff_support_of_nonneg` with positivity everywhere.
  have hnonneg :
      ∀ r : Set.Ioi (0 : ℝ), 0 ≤ (r.1 ^ k) * Real.exp (-(r.1 ^ (2 : ℕ))) := by
    intro r
    exact mul_nonneg (pow_nonneg (le_of_lt r.2) _) (Real.exp_pos _).le
  -- Integrability (w.r.t. `volumeIoiPow`): convert to Lebesgue integrability on `(0,∞)`.
  have hint :
      Integrable (fun r : Set.Ioi (0 : ℝ) => (r.1 ^ k) * Real.exp (-(r.1 ^ (2 : ℕ))))
        (Measure.volumeIoiPow 23) := by
    let μ : Measure (Set.Ioi (0 : ℝ)) := Measure.comap Subtype.val (volume : Measure ℝ)
    have hmeas :
        Measurable (fun r : Set.Ioi (0 : ℝ) => ENNReal.ofReal (r.1 ^ (23 : ℕ))) := by
      measurability
    have hlt : ∀ᵐ r : Set.Ioi (0 : ℝ) ∂μ, (ENNReal.ofReal (r.1 ^ (23 : ℕ))) < ∞ := by
      filter_upwards [] with r
      simp
    have hIoi :
        IntegrableOn (fun y : ℝ => (y ^ (23 + k)) * Real.exp (-(y ^ (2 : ℕ))))
          (Set.Ioi (0 : ℝ)) := by
      have h :=
        (integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ)) (hb := by positivity)
          (s := ((23 + k : ℕ) : ℝ)) (hs := by
            have : (0 : ℝ) ≤ ((23 + k : ℕ) : ℝ) := by positivity
            linarith))
      refine h.congr_fun ?_ measurableSet_Ioi
      intro y hy
      -- Convert the `rpow` into a Nat power, then simplify `-1 * t` to `-t`.
      dsimp
      rw [Real.rpow_natCast y (23 + k)]
      simp [mul_comm]
    have hbase :
        Integrable (fun r : Set.Ioi (0 : ℝ) =>
          (r.1 ^ (23 + k)) * Real.exp (-(r.1 ^ (2 : ℕ)))) μ := by
      have :=
        (MeasureTheory.integrableOn_iff_comap_subtypeVal (μ := (volume : Measure ℝ))
          (f := fun y : ℝ => (y ^ (23 + k)) * Real.exp (-(y ^ (2 : ℕ))))
          (s := Set.Ioi (0 : ℝ)) (hs := measurableSet_Ioi)).1 hIoi
      simpa [μ, Function.comp] using! this
    have hweighted :
        Integrable (fun r : Set.Ioi (0 : ℝ) =>
          (ENNReal.ofReal (r.1 ^ (23 : ℕ))).toReal •
            ((r.1 ^ k) * Real.exp (-(r.1 ^ (2 : ℕ))))) μ := by
      -- This is the same integrand as `hbase`, by rewriting the `withDensity` weight.
      have hEq :
          (fun r : Set.Ioi (0 : ℝ) =>
              (ENNReal.ofReal (r.1 ^ (23 : ℕ))).toReal *
                ((r.1 ^ k) * Real.exp (-(r.1 ^ (2 : ℕ))))) =
            fun r : Set.Ioi (0 : ℝ) =>
              (r.1 ^ (23 + k)) * Real.exp (-(r.1 ^ (2 : ℕ))) := by
        funext r
        have hr : 0 ≤ r.1 ^ (23 : ℕ) := pow_nonneg (le_of_lt r.2) _
        simp [hr, pow_add, mul_assoc, mul_left_comm, mul_comm]
      simp_all
    -- Apply `integrable_withDensity_iff_integrable_smul'` and unfold `volumeIoiPow`.
    have :=
      (MeasureTheory.integrable_withDensity_iff_integrable_smul' (μ := μ) (E := ℝ) hmeas hlt
        (g := fun r : Set.Ioi (0 : ℝ) => (r.1 ^ k) * Real.exp (-(r.1 ^ (2 : ℕ))))).2 hweighted
    simpa [MeasureTheory.Measure.volumeIoiPow, μ] using! this
  -- Show the support has positive measure (e.g. `Iio 1` has positive `volumeIoiPow` measure,
  -- and the integrand is strictly positive there).
  have hsupport :
      0 < (Measure.volumeIoiPow 23)
            (Function.support fun r : Set.Ioi (0 : ℝ) =>
              (r.1 ^ k) * Real.exp (-(r.1 ^ (2 : ℕ)))) := by
    let onePos : Set.Ioi (0 : ℝ) := ⟨1, (zero_lt_one : (0 : ℝ) < 1)⟩
    have hμ : 0 < (Measure.volumeIoiPow 23) (Set.Iio onePos) := by
      have hμeq := (MeasureTheory.Measure.volumeIoiPow_apply_Iio 23 onePos)
      have hpos : 0 < (onePos.1 ^ (23 + 1) / (23 + 1) : ℝ) := by
        -- `onePos.1 = 1`, so this is `0 < 1/24`.
        simpa [onePos] using! (show (0 : ℝ) < (1 : ℝ) ^ (23 + 1) / (23 + 1) by norm_num)
      have : 0 < ENNReal.ofReal (onePos.1 ^ (23 + 1) / (23 + 1) : ℝ) :=
        ENNReal.ofReal_pos.mpr hpos
      simpa [hμeq] using! this
    have hsub : Set.Iio onePos ⊆
        Function.support (fun r : Set.Ioi (0 : ℝ) =>
          (r.1 ^ k) * Real.exp (-(r.1 ^ (2 : ℕ)))) := by
      intro r hr
      have hpos : 0 < (r.1 ^ k) * Real.exp (-(r.1 ^ (2 : ℕ))) := by
        exact mul_pos (pow_pos r.2 _) (Real.exp_pos _)
      have hne : (r.1 ^ k) * Real.exp (-(r.1 ^ (2 : ℕ))) ≠ 0 := ne_of_gt hpos
      simpa [Function.mem_support] using! hne
    exact lt_of_lt_of_le hμ (measure_mono hsub)
  exact (MeasureTheory.integral_pos_iff_support_of_nonneg hnonneg hint).2 hsupport

/-!
## Mean-zero on the sphere for harmonic `Pk`'s

This is the final statement needed by the BS81 design bridge.
-/

namespace Bridge24

open Uniqueness.BS81.LP.Gegenbauer24.PSD
open Uniqueness.BS81.LP.Gegenbauer24.PSD.Harmonic

lemma laplacian_eq_zero_of_mem_Harm {k : ℕ} (h : Harmonic.Harm k) :
    Harmonic.laplacian (h.1.1 : Poly) = 0 := by
  have hharmPk : Harmonic.laplacianPk k h.1 = 0 :=
    (Harmonic.mem_Harm_iff (k := k) (p := h.1)).1 h.2
  have hharmVal : ((Harmonic.laplacianPk k h.1 : Fischer.Pk (k - 2)) : Poly) = 0 :=
    congrArg (fun q : Fischer.Pk (k - 2) => (q : Poly)) hharmPk
  dsimp [Harmonic.laplacianPk] at hharmVal
  simpa [LinearMap.comp_apply] using! hharmVal

lemma isHomogeneous_of_mem_Pk {k : ℕ} (p : Fischer.Pk k) :
    (p.1 : Poly).IsHomogeneous k := by
  -- `Fischer.Pk k` is the homogeneous submodule.
  simpa [Fischer.Pk] using!
    (MvPolynomial.mem_homogeneousSubmodule (σ := Var) (R := ℝ) k (p := (p.1 : Poly))).1 p.2

lemma sphereIntegral_evalPoly24_eq_zero_of_isHomogeneous_of_harmonic
    {k : ℕ} (hk : 1 ≤ k) {p : Poly} (hp : p.IsHomogeneous k)
    (hharm : Harmonic.laplacian p = 0) :
    (∫ u : S23, evalPoly24 (y := u.1) p ∂sphereMeasure24) = 0 := by
  have hgauss :
      (∫ x : ℝ²⁴, evalPoly24 (y := x) p * gaussWeight x ∂volume) = 0 :=
    gaussIntegral_evalPoly24_eq_zero_of_isHomogeneous_of_harmonic (k := k) hk (p := p) hp hharm
  have hfactor :=
    gaussIntegral_evalPoly24_eq_sphereIntegral_mul_radialIntegral (k := k) (p := p) hp
  -- Rewrite the Gaussian integral using the polar-factorization identity.
  have hmul :
      (∫ u : S23, evalPoly24 (y := u.1) p ∂sphereMeasure24) *
          (∫ r : Set.Ioi (0 : ℝ), (r.1 ^ k) * Real.exp (-(r.1 ^ (2 : ℕ)))
            ∂(Measure.volumeIoiPow 23)) = 0 := by
    -- `hfactor` expresses the LHS integral as a product, and `hgauss = 0`.
    -- Rewrite `hgauss` and simplify.
    simpa [hfactor] using! hgauss
  have hrad_ne :
      (∫ r : Set.Ioi (0 : ℝ), (r.1 ^ k) * Real.exp (-(r.1 ^ (2 : ℕ)))
            ∂(Measure.volumeIoiPow 23)) ≠ 0 :=
    ne_of_gt (radialIntegral_pos (k := k))
  exact (mul_eq_zero.mp hmul).resolve_right hrad_ne

/-- Nonconstant harmonic homogeneous polynomials have mean `0` on the unit sphere (`n=24`). -/
public theorem sphereAvg24_harmonic_degree_pos_eq_zero_gauss
    (k : ℕ) (hk : 1 ≤ k)
    (h : Harmonic.Harm k) :
    sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x)
      (h : Fischer.Pk k)) = 0 := by
  -- Reduce to the statement about the unnormalized sphere integral.
  have hp : (h.1.1 : Poly).IsHomogeneous k :=
    isHomogeneous_of_mem_Pk (k := k) (p := (h : Fischer.Pk k))
  have hharm : Harmonic.laplacian (h.1.1 : Poly) = 0 :=
    laplacian_eq_zero_of_mem_Harm (k := k) h
  have hint :
      (∫ u : S23, evalPoly24 (y := u.1) (h.1.1 : Poly) ∂sphereMeasure24) = 0 :=
    sphereIntegral_evalPoly24_eq_zero_of_isHomogeneous_of_harmonic
      (k := k) hk (p := (h.1.1 : Poly)) hp hharm
  -- `sphereAvg24` is a scalar multiple of the integral; so it vanishes if the integral vanishes.
  simp [sphereAvg24, evalPk24, hint]

end Bridge24

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem
