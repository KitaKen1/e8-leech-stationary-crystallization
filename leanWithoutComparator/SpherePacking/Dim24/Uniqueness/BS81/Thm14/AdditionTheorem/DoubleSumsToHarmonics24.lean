-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.HarmPolyRecurrence24
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.Defs

/-!
# From Gegenbauer double sums to harmonic moments

Using the addition theorem bridge (`harmKernel24 = Gegenbauer24`), we show that vanishing of the
Gegenbauer double sums is equivalent to vanishing of all degree-`k` harmonic moment sums:

* `IsGegenbauerDesign24 t C` is defined by vanishing of the double sums
  `∑_{u,v∈C} Gegenbauer24 k (⟪u,v⟫)` for `k = 1..t`.
* Using the addition theorem bridge (`harmKernel24 = Gegenbauer24`), these double sums become Gram
  norms in a Hilbert space of degree-`k` harmonics, hence vanish iff a corresponding feature-map sum
  vanishes.
* Vanishing of the feature-map sum is equivalent to vanishing of *all* degree-`k` harmonic moment
  sums `∑_{u∈C} h(u)`.

This is a standard chain:

`Gegenbauer double sum = ⟪∑ Φ(u), ∑ Φ(u)⟫`,
so it is `0` iff `∑ Φ(u) = 0`,
and then `0 = ⟪∑ Φ(u), h⟫ = ∑ h(u)` for each harmonic basis element `h`.

-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem

noncomputable section

open scoped BigOperators RealInnerProductSpace

open Finset
open Uniqueness.BS81.LP

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

open Uniqueness.BS81.LP.Gegenbauer24.PSD.ZonalKernel
open Uniqueness.BS81.LP.Gegenbauer24.PSD

/-!
## Public evaluation helpers

We record explicit evaluation maps for polynomials and homogeneous polynomials on `ℝ²⁴`.
-/

/-- Evaluate a multivariate polynomial at `y : ℝ²⁴`. -/
@[expose] public noncomputable def evalPoly24 (y : ℝ²⁴) (p : MvPolynomial (Fin 24) ℝ) : ℝ :=
  MvPolynomial.eval (fun i : Fin 24 => y i) p

/-- Evaluate a homogeneous polynomial (packaged as `Fischer.Pk k`) at `y : ℝ²⁴`. -/
@[expose] public noncomputable def evalPk24 (k : ℕ) (y : ℝ²⁴) (p : Fischer.Pk k) : ℝ :=
  evalPoly24 (y := y) p.1

/-- A variant of `inner_Φ_eq_eval` formulated with `evalPk24`. -/
theorem inner_Φ_eq_evalPk24 (k : ℕ) (y : ℝ²⁴) (h : Harmonic.Harm k) :
    ⟪Φ k y, h⟫ = evalPk24 (k := k) (y := y) (h : Fischer.Pk k) := by
  -- This is just `ZonalKernel.inner_Φ_eq_eval`, rewriting the (private) `evalPk` as our public
  -- `evalPk24`.
  simpa [evalPk24, evalPoly24] using!
    (Uniqueness.BS81.LP.Gegenbauer24.PSD.ZonalKernel.inner_Φ_eq_eval
      (k := k) (y := y) (h := h))

/-!
## Double sums: `harmKernel24` vs `gegenbauerDoubleSum24`
-/

theorem sum_sum_harmKernel24_eq_harmKernelScalar24_mul_gegenbauerDoubleSum24
    (k : ℕ) (C : Finset ℝ²⁴) (hC : ∀ u ∈ C, ‖u‖ = (1 : ℝ)) :
    C.sum (fun u => C.sum (fun v => harmKernel24 k u v)) =
      (Uniqueness.BS81.LP.Gegenbauer24.AdditionTheorem.harmKernelScalar24 k) *
        gegenbauerDoubleSum24 k C := by
  -- Pointwise kernel identification on the unit sphere, then unfold `gegenbauerDoubleSum24`.
  -- This uses `harmKernel24_eq_gegenbauer_eval` from `HarmPolyRecurrence24.lean`.
  let s : ℝ := Uniqueness.BS81.LP.Gegenbauer24.AdditionTheorem.harmKernelScalar24 k
  unfold gegenbauerDoubleSum24
  calc
    C.sum (fun u => C.sum (fun v => harmKernel24 k u v)) =
        C.sum (fun u => C.sum (fun v => s * (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ))) := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          refine Finset.sum_congr rfl ?_
          exact fun x a => Gegenbauer24.AdditionTheorem.harmKernel24_eq_gegenbauer_eval
              k (hC u hu) (hC x a)
    _ = C.sum (fun u => s * C.sum (fun v => (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ))) := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          simp [Finset.mul_sum]
    _ = s * C.sum (fun u => C.sum (fun v => (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ))) := by
          simp [Finset.mul_sum]
    _ = s * gegenbauerDoubleSum24 k C := by rfl

/-!
## Gram form

The file `.../LP/Gegenbauer24/ZonalKernelPSD.lean` proves nonnegativity of the `harmKernel24` double
sum by rewriting it as `⟪S,S⟫` for `S = ∑ Φ(u)`.

We expose that identity as a separate lemma so we can turn `double sum = 0` into `S = 0`.
-/

theorem sum_sum_harmKernel24_eq_inner_sum_Φ
    (k : ℕ) (C : Finset ℝ²⁴) :
    C.sum (fun u => C.sum (fun v => harmKernel24 k u v)) =
      ⟪(C.sum (fun u => (Φ k u : Fischer.Pk k))), (C.sum (fun u => (Φ k u : Fischer.Pk k)))⟫ :=
  ZonalKernel.sum_sum_harmKernel24_eq_inner_sum_Φ k C

theorem sum_sum_harmKernel24_eq_zero_iff_sum_Φ_eq_zero
    (k : ℕ) (C : Finset ℝ²⁴) :
    (C.sum (fun u => C.sum (fun v => harmKernel24 k u v)) = 0) ↔
      (C.sum (fun u => (Φ k u : Fischer.Pk k)) = 0) := by
  -- Use `sum_sum_harmKernel24_eq_inner_sum_Φ` and definiteness of the Fischer inner product.
  have hGram := sum_sum_harmKernel24_eq_inner_sum_Φ (k := k) (C := C)
  simp_all

/-!
## Harmonic moment sums

We package the vanishing harmonic sums condition as a predicate, since it is the right interface
for connecting to BS81's design axiom (equation (14)).
-/

/-- Harmonic-design predicate:
every degree-`k` harmonic homogeneous polynomial sums to `0` on `C`, for degrees `k = 1..t`.

This is the standard intermediate notion between Gegenbauer double sums and spherical designs. -/
@[expose] public def IsHarmonicDesign24 (t : ℕ) (C : Finset ℝ²⁴) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ t →
    ∀ h : Uniqueness.BS81.LP.Gegenbauer24.PSD.Harmonic.Harm k,
      C.sum (fun u => evalPk24 (k := k) (y := u) (h : Fischer.Pk k)) = 0

/-!
### From Gegenbauer double sums to harmonic-sum vanishing

Sketch:
* assume `gegenbauerDoubleSum24 k C = 0`;
* rewrite as a `harmKernel24` double sum using addition theorem;
* rewrite as `⟪S,S⟫` and deduce `S = 0`;
* then for any harmonic `h`, `0 = ⟪S,h⟫ = ∑ eval h(u)`.
-/

/-- A Gegenbauer design implies vanishing of all harmonic moment sums. -/
public theorem isHarmonicDesign24_of_isGegenbauerDesign24
    (t : ℕ) (C : Finset ℝ²⁴) (hC : ∀ u ∈ C, ‖u‖ = (1 : ℝ))
    (hG : IsGegenbauerDesign24 t C) :
    IsHarmonicDesign24 t C := by
  intro k hk1 hkt h
  have hsum0 : gegenbauerDoubleSum24 k C = 0 := hG k hk1 hkt
  -- Convert the Gegenbauer double sum to the harmonic-kernel double sum.
  have hsum_harm :
      C.sum (fun u => C.sum (fun v => harmKernel24 k u v)) = 0 := by
    -- `sum_sum_harmKernel24_eq_harmKernelScalar24_mul_gegenbauerDoubleSum24` + `hsum0`.
    have heq :=
      sum_sum_harmKernel24_eq_harmKernelScalar24_mul_gegenbauerDoubleSum24
        (k := k) (C := C) (hC := hC)
    -- If the Gegenbauer double sum vanishes, then so does the harmonic-kernel double sum (the
    -- scalar factor is irrelevant in this direction).
    simp [heq, hsum0]
  -- Convert the vanishing double sum to `∑ Φ = 0`.
  have hΦ0 : C.sum (fun u => (Φ k u : Fischer.Pk k)) = 0 := by
    -- `sum_sum_harmKernel24_eq_zero_iff_sum_Φ_eq_zero`.
    exact (sum_sum_harmKernel24_eq_zero_iff_sum_Φ_eq_zero (k := k) (C := C)).1 hsum_harm
  -- Pair with `h` and use reproducing property of `Φ`.
  -- `inner_Φ_eq_evalPk24` gives `⟪Φ k u, h⟫ = evalPk24 u h`.
  have hinner0 : ⟪(C.sum (fun u => (Φ k u : Fischer.Pk k))), (h : Fischer.Pk k)⟫ = 0 := by
    simp [hΦ0]
  have hsum_inner :
      C.sum (fun u => ⟪(Φ k u : Fischer.Pk k), (h : Fischer.Pk k)⟫) = 0 := by
    have hEq :
        ⟪(C.sum (fun u => (Φ k u : Fischer.Pk k))), (h : Fischer.Pk k)⟫ =
          C.sum (fun u => ⟪(Φ k u : Fischer.Pk k), (h : Fischer.Pk k)⟫) := by
      simpa using!
        (sum_inner (s := C) (f := fun u => (Φ k u : Fischer.Pk k)) (x := (h : Fischer.Pk k)))
    simpa [hEq] using! hinner0
  -- Rewrite the inner-product sum as the evaluation sum.
  have hrewrite :
      C.sum (fun u => evalPk24 (k := k) (y := u) (h : Fischer.Pk k)) =
        C.sum (fun u => ⟪(Φ k u : Fischer.Pk k), (h : Fischer.Pk k)⟫) := by
    refine Finset.sum_congr rfl ?_
    intro u hu
    -- `Submodule.inner` is definitional, so we can use `inner_Φ_eq_evalPk24` directly.
    simpa using! (inner_Φ_eq_evalPk24 (k := k) (y := u) (h := h)).symm
  calc
    C.sum (fun u => evalPk24 (k := k) (y := u) (h : Fischer.Pk k))
        = C.sum (fun u => ⟪(Φ k u : Fischer.Pk k), (h : Fischer.Pk k)⟫) := hrewrite
    _ = 0 := hsum_inner

/-!
### Backwards: from harmonic-sum vanishing to Gegenbauer double sums

This direction is slightly more delicate:
* `IsHarmonicDesign24` gives `∑ eval h(u) = 0` for all harmonics `h`;
* picking `h = Φ k v` yields `∑ harmKernel24 k u v = 0` row-wise;
* then summing in `v` gives vanishing of the harmonic double sum;
* use the addition theorem to convert back to the Gegenbauer double sum.
-/

/-- Vanishing of harmonic moment sums implies vanishing of Gegenbauer double sums. -/
public theorem isGegenbauerDesign24_of_isHarmonicDesign24
    (t : ℕ) (C : Finset ℝ²⁴) (hC : ∀ u ∈ C, ‖u‖ = (1 : ℝ))
    (hH : IsHarmonicDesign24 t C) :
    IsGegenbauerDesign24 t C := by
  intro k hk1 hkt
  -- Apply harmonic vanishing to `h := ∑ Φ(u)` and rewrite in the ambient Fischer space.
  let S : Harmonic.Harm k := C.sum (fun u => Φ k u)
  have hS_eval : C.sum (fun u => evalPk24 (k := k) (y := u) (S : Fischer.Pk k)) = 0 :=
    hH k hk1 hkt S
  let SΦ : Fischer.Pk k := C.sum (fun u => (Φ k u : Fischer.Pk k))
  have hcoe : (S : Fischer.Pk k) = SΦ := by
    simp [S, SΦ]
  have hsum_inner : ⟪SΦ, (S : Fischer.Pk k)⟫ = 0 := by
    -- Rewrite the evaluation sum as an inner-product sum, then as an inner with the sum.
    have hrewrite :
        C.sum (fun u => evalPk24 (k := k) (y := u) (S : Fischer.Pk k)) =
          C.sum (fun u => ⟪(Φ k u : Fischer.Pk k), (S : Fischer.Pk k)⟫) := by
      refine Finset.sum_congr rfl ?_
      intro u hu
      simpa using! (inner_Φ_eq_evalPk24 (k := k) (y := u) (h := S)).symm
    have hEq :
        ⟪SΦ, (S : Fischer.Pk k)⟫ =
          C.sum (fun u => ⟪(Φ k u : Fischer.Pk k), (S : Fischer.Pk k)⟫) := by
      -- `⟪∑ Φ(u), S⟫ = ∑ ⟪Φ(u), S⟫`.
      simpa [SΦ] using!
        (sum_inner (s := C) (f := fun u => (Φ k u : Fischer.Pk k)) (x := (S : Fischer.Pk k)))
    -- Combine.
    grind only
  -- Deduce `∑ Φ = 0` from definiteness: `⟪SΦ,SΦ⟫ = 0`.
  have hΦ0 : SΦ = 0 := by
    simp_all
  have hΦ0' : C.sum (fun u => (Φ k u : Fischer.Pk k)) = 0 := by
    simpa [SΦ] using! hΦ0
  have hdouble0 :
      C.sum (fun u => C.sum (fun v => harmKernel24 k u v)) = 0 := by
    -- Double sum is `⟪∑ Φ, ∑ Φ⟫`.
    have hGram := sum_sum_harmKernel24_eq_inner_sum_Φ (k := k) (C := C)
    simp [hGram, hΦ0']
  -- Convert back to the Gegenbauer double sum.
  have heq :=
    sum_sum_harmKernel24_eq_harmKernelScalar24_mul_gegenbauerDoubleSum24
      (k := k) (C := C) (hC := hC)
  have hs :
      Uniqueness.BS81.LP.Gegenbauer24.AdditionTheorem.harmKernelScalar24 k ≠ 0 :=
    Uniqueness.BS81.LP.Gegenbauer24.AdditionTheorem.harmKernelScalar24_ne_zero (k := k)
  -- `heq : harmDoubleSum = s * gegenbauerDoubleSum`, so deduce the RHS is `0`.
  have hmul :
      (Uniqueness.BS81.LP.Gegenbauer24.AdditionTheorem.harmKernelScalar24 k) *
          gegenbauerDoubleSum24 k C = 0 := by
    simpa [heq] using! hdouble0
  -- Cancel the nonzero scalar.
  exact (mul_eq_zero.mp hmul).resolve_left hs

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem
