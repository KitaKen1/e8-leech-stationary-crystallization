-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.EvenUnimodular.FiniteShells
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Analytic theta series

For a `ℤ`-lattice `L ⊆ ℝ²⁴` we define the (complex) theta series
`Θ_L(τ) = ∑' z : L, exp(π i ‖z‖^2 τ)` on the upper half-plane (`0 < im τ`).

We prove basic analytic properties: a norm formula for terms, summability for `0 < im τ`, and
the periodicity `Θ_L(τ + 1) = Θ_L(τ)` for even lattices (`EvenNormSq`).

The modular transformation `τ ↦ -1/τ` (Poisson summation / dual lattice) is a deeper input and
is handled separately.

## Main definitions
* `thetaTerm`
* `thetaSeries`

## Main statements
* `norm_thetaTerm`
* `summable_thetaTerm`
* `thetaSeries_add_one_of_even`
-/

namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

noncomputable section

open scoped RealInnerProductSpace
open Filter Asymptotics Complex Real Metric

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- The `z`-th term in the theta series at `τ`. -/
@[expose]
public noncomputable def thetaTerm (L : Submodule ℤ ℝ²⁴) (τ : ℂ) (z : L) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * ((‖(z : ℝ²⁴)‖ ^ 2 : ℝ) : ℂ) * τ)

/-- The (analytic) theta series `Θ_L(τ)` for a lattice `L`. -/
@[expose]
public noncomputable def thetaSeries (L : Submodule ℤ ℝ²⁴) (τ : ℂ) : ℂ :=
  ∑' z : L, thetaTerm L τ z

@[simp]
private lemma thetaTerm_re (L : Submodule ℤ ℝ²⁴) (τ : ℂ) (z : L) :
    (((Real.pi : ℂ) * Complex.I * ((‖(z : ℝ²⁴)‖ ^ 2 : ℝ) : ℂ) * τ).re : ℝ) =
      -Real.pi * (‖(z : ℝ²⁴)‖ ^ 2) * τ.im := by
  -- Reorder to isolate `I * τ`, and rewrite the real scalar as a single `ofReal`.
  have hcomm :
      (Real.pi : ℂ) * Complex.I * ((‖(z : ℝ²⁴)‖ ^ 2 : ℝ) : ℂ) * τ =
        ((Real.pi * ‖(z : ℝ²⁴)‖ ^ 2 : ℝ) : ℂ) * (Complex.I * τ) := by
    -- commutativity in `ℂ` lets us group factors arbitrarily
    -- and `simp` combines the two real scalars.
    calc
      (Real.pi : ℂ) * Complex.I * ((‖(z : ℝ²⁴)‖ ^ 2 : ℝ) : ℂ) * τ
          = ((Real.pi : ℂ) * ((‖(z : ℝ²⁴)‖ ^ 2 : ℝ) : ℂ)) * (Complex.I * τ) := by
              ac_rfl
      _ = ((Real.pi * ‖(z : ℝ²⁴)‖ ^ 2 : ℝ) : ℂ) * (Complex.I * τ) := by
            simp [mul_assoc]
  -- Now compute the real part using `mul_re` and `(I * τ).re = -τ.im`.
  -- Since the scalar is real, the cross-term vanishes.
  rw [hcomm]
  set a : ℂ := ((Real.pi * ‖(z : ℝ²⁴)‖ ^ 2 : ℝ) : ℂ)
  have ha_re : a.re = Real.pi * ‖(z : ℝ²⁴)‖ ^ 2 := by
    -- avoid `simp` rewriting `ofReal_mul`; unfold `Complex.ofReal` directly
    dsimp [a, Complex.ofReal]
  have ha_im : a.im = 0 := by
    dsimp [a, Complex.ofReal]
  have hb_re : (Complex.I * τ).re = -τ.im := by
    simp
  -- expand `mul_re` and simplify using `ha_im = 0`
  simp [Complex.mul_re, ha_re, ha_im, mul_assoc, mul_left_comm, mul_comm]

/-- The norm of a theta term is a real exponential involving `-π‖z‖^2 * im τ`. -/
@[simp]
public lemma norm_thetaTerm (L : Submodule ℤ ℝ²⁴) (τ : ℂ) (z : L) :
    ‖thetaTerm L τ z‖ = Real.exp (-Real.pi * (‖(z : ℝ²⁴)‖ ^ 2) * τ.im) := by
  -- `‖exp w‖ = exp (re w)` and `re w = -π‖z‖² im τ`.
  dsimp [thetaTerm]
  rw [Complex.norm_exp]
  -- rewrite the real part using `thetaTerm_re`
  have hre := thetaTerm_re (L := L) (τ := τ) (z := z)
  -- `hre` is stated in `ℝ`, so `rw` works directly.
  rw [hre]

/-- For `0 < im τ`, the theta series terms are summable over a discrete `ℤ`-lattice. -/
public theorem summable_thetaTerm (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L] [IsZLattice ℝ L]
    {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun z : L => thetaTerm L τ z := by
  -- Choose a negative exponent `r < -rank(L)` and compare to `‖z‖ ^ r`.
  let r : ℝ := -Module.finrank ℤ L - 2
  have hr : r < -Module.finrank ℤ L := by linarith
  have hSummable : Summable fun z : L => (‖z‖ : ℝ) ^ r :=
    ZLattice.summable_norm_rpow (L := L) r hr
  -- Show `‖thetaTerm‖` decays faster than any power, hence `O(‖z‖^r)` for large `‖z‖`.
  have hdecay :
      (fun x : ℝ => Real.exp (-Real.pi * τ.im * x ^ 2)) =o[atTop] fun x : ℝ => x ^ r := by
    -- This is a special case of the Gaussian decay lemma.
    have ha : (-Real.pi * τ.im) < 0 := by nlinarith [Real.pi_pos, hτ]
    -- `exp (-π im τ * x^2) = exp ((-π im τ) * x^2 + 0 * x)`.
    simpa [Real.exp_eq_exp, mul_assoc, add_zero] using!
      (rexp_neg_quadratic_isLittleO_rpow_atTop (a := (-Real.pi * τ.im)) ha (b := (0 : ℝ)) r)
  have hBigO :
      (fun x : ℝ => Real.exp (-Real.pi * τ.im * x ^ 2)) =O[atTop] fun x : ℝ => x ^ r :=
    hdecay.isBigO
  rcases hBigO.exists_pos with ⟨C, hCpos, hC⟩
  -- Unpack the eventual bound on `atTop` to a numerical threshold.
  rcases (Filter.eventually_atTop.1 hC.bound) with ⟨R, hR⟩
  -- Translate the threshold to an `∀ᶠ z ∈ cofinite` bound using finiteness of bounded lattice
  -- subsets.
  have hFinite : {z : L | ‖(z : ℝ²⁴)‖ < R}.Finite := by
    exact finite_subtype_norm_lt (L := L) (R := R)
  have hBound :
      ∀ᶠ z : L in Filter.cofinite,
        ‖thetaTerm L τ z‖ ≤ C * (‖z‖ : ℝ) ^ r := by
    refine Filter.eventually_cofinite.2 ?_
    -- The counterexample set is contained in `{‖z‖ < R}`, hence finite.
    refine (hFinite.subset ?_)
    intro z hzBad
    by_contra hzSmall
    have hzLarge : R ≤ ‖(z : ℝ²⁴)‖ := le_of_not_gt hzSmall
    -- Apply the `atTop` bound at `x = ‖z‖`.
    have hRz_norm :
        ‖Real.exp (-Real.pi * τ.im * ‖(z : ℝ²⁴)‖ ^ 2)‖ ≤
          C * ‖(‖(z : ℝ²⁴)‖ : ℝ) ^ r‖ :=
      hR _ hzLarge
    have hRz : Real.exp (-Real.pi * τ.im * ‖(z : ℝ²⁴)‖ ^ 2) ≤ C * (‖(z : ℝ²⁴)‖ : ℝ) ^ r := by
      -- simplify norms (all terms are nonnegative)
      have hpow_nonneg : 0 ≤ (‖(z : ℝ²⁴)‖ : ℝ) ^ r := by positivity
      have hexp_pos : 0 < Real.exp (-Real.pi * τ.im * ‖(z : ℝ²⁴)‖ ^ 2) := by positivity
      have hexp_nonneg : 0 ≤ Real.exp (-Real.pi * τ.im * ‖(z : ℝ²⁴)‖ ^ 2) := le_of_lt hexp_pos
      simpa [Real.norm_eq_abs, abs_of_nonneg hexp_nonneg, abs_of_nonneg hpow_nonneg] using! hRz_norm
    -- Rewrite `‖thetaTerm‖` and finish.
    have :
        ‖thetaTerm L τ z‖ ≤ C * (‖z‖ : ℝ) ^ r := by
      -- `‖z‖` in the subtype is definitional the ambient norm.
      simpa [norm_thetaTerm, mul_assoc, mul_left_comm, mul_comm] using! hRz
    exact hzBad this
  -- Conclude by eventual domination.
  refine Summable.of_norm_bounded_eventually (hSummable.mul_left C) ?_
  filter_upwards [hBound] with z hz
  simpa [norm_mul, Real.norm_eq_abs, abs_of_pos hCpos, mul_assoc] using! hz

/-- For an even lattice, the theta series is invariant under `τ ↦ τ + 1`. -/
public theorem thetaSeries_add_one_of_even (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L]
    [IsZLattice ℝ L] (hEven : EvenNormSq L) {τ : ℂ} :
    thetaSeries L (τ + 1) = thetaSeries L τ := by
  -- show termwise invariance and use `tsum_congr`.
  have hterm : ∀ z : L, thetaTerm L (τ + 1) z = thetaTerm L τ z := by
    intro z
    -- use `‖z‖^2 = 2n` and `exp (2π i n) = 1`
    have hzL : (z : ℝ²⁴) ∈ L := z.property
    rcases hEven (z : ℝ²⁴) hzL with ⟨n, hn⟩
    -- Set `A = π i ‖z‖²` and rewrite the terms as `exp (A * τ)`.
    let A : ℂ := (Real.pi : ℂ) * Complex.I * ((‖(z : ℝ²⁴)‖ ^ 2 : ℝ) : ℂ)
    have hτ1 : thetaTerm L (τ + 1) z = Complex.exp (A * (τ + 1)) := by
      simp [thetaTerm, A, mul_assoc, mul_left_comm, mul_comm]
    have hτ0 : thetaTerm L τ z = Complex.exp (A * τ) := by
      simp [thetaTerm, A, mul_assoc, mul_left_comm, mul_comm]
    -- Reduce to `exp A = 1` using `exp_add`.
    have hextra : Complex.exp A = 1 := by
      have hnC : ((‖(z : ℝ²⁴)‖ ^ 2 : ℝ) : ℂ) = (2 : ℂ) * n := by
        exact_mod_cast hn
      have hA : A = (n : ℂ) * (2 * Real.pi * Complex.I) := by
        simp [A, hnC, mul_assoc, mul_left_comm, mul_comm]
      simpa [hA, mul_assoc] using! (Complex.exp_nat_mul_two_pi_mul_I n)
    -- Final calculation.
    rw [hτ1, hτ0, mul_add, Complex.exp_add]
    simp [hextra]
  -- finish with `tsum_congr`
  have :
      (∑' z : L, thetaTerm L (τ + 1) z) = ∑' z : L, thetaTerm L τ z :=
    tsum_congr hterm
  simpa [thetaSeries] using! this

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
