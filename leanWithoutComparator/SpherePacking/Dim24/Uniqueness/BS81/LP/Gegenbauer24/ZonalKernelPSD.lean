-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.FiniteDimensional
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Harmonic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Zonal harmonic kernels on `Ω₂₄`

Using the Fischer inner product, we construct a reproducing kernel for the Hilbert space of
degree-`k` harmonic polynomials and package it as a PSD Gram kernel `harmKernel24 k` on the unit
sphere. The kernel is defined via the feature map `Φ k`.

The identification `harmKernel24 = zonalKernel24` (via Gegenbauer polynomials and the addition
theorem) is proved in a separate file.

## Main definitions
* `Gegenbauer24.PSD.ZonalKernel.Φ`
* `Gegenbauer24.PSD.ZonalKernel.harmKernel24`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.ZonalKernel

noncomputable section

open scoped BigOperators RealInnerProductSpace

open Finset Finsupp MvPolynomial

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

open Fischer Harmonic

section Typeclass

/-!
## Typeclass note

The Fischer inner product was set up in `PSD/InnerProduct.lean` as an `InnerProductSpace` whose
associated norm is only *a priori* a seminorm (so the ambient space is only a pseudometric space).

For orthogonal projections we need a `NormedAddCommGroup` structure (hence `T2Space`) and
completeness. Both follow from definiteness of the Fischer inner product, which is exactly the
`definite` field in the `InnerProductSpace.Core` instance.

We introduce these instances locally, so we can use `Submodule.orthogonalProjection`.
-/

local instance (k : ℕ) : NormedAddCommGroup (Fischer.Pk k) :=
  (show InnerProductSpace.Core ℝ (Fischer.Pk k) from inferInstance).toNormedAddCommGroup

local instance (k : ℕ) : CompleteSpace (Fischer.Pk k) := by
  -- `Pk k` is finite-dimensional (see `PSD/FiniteDimensional.lean`), hence complete.
  simpa using! (FiniteDimensional.complete ℝ (Fischer.Pk k))

/-- The linear form `x ↦ ⟪x, y⟫` as a polynomial in the `x` variables. -/
@[expose] public noncomputable def lin (y : ℝ²⁴) : Poly :=
  (univ : Finset Var).sum (fun i => C (y i) * X i)

/-- The linear form `lin y` is homogeneous of degree `1`. -/
public lemma isHomogeneous_lin (y : ℝ²⁴) : (lin y).IsHomogeneous 1 := by
  -- Each summand `C (y i) * X i` is homogeneous of degree `1`.
  refine MvPolynomial.IsHomogeneous.sum (s := (univ : Finset Var))
      (φ := fun i => C (y i) * X i) (n := 1) ?_
  intro i hi
  simpa using! (MvPolynomial.isHomogeneous_C_mul_X (R := ℝ) (σ := Var) (y i) i)

/-- The (unnormalized) degree-`k` reproducing-kernel polynomial `Z_{k,y}(x) = ⟪x,y⟫^k`. -/
@[expose] public noncomputable def Z (k : ℕ) (y : ℝ²⁴) : Poly :=
  (lin y) ^ k

/-- The polynomial `Z k y` is homogeneous of degree `k`. -/
public lemma isHomogeneous_Z (k : ℕ) (y : ℝ²⁴) : (Z k y).IsHomogeneous k := by
  simpa [Z, lin] using! (isHomogeneous_lin (y := y)).pow k

/-- Package `Z k y` as an element of the degree-`k` homogeneous submodule. -/
@[expose] public noncomputable def ZPk (k : ℕ) (y : ℝ²⁴) : Fischer.Pk k :=
  ⟨Z k y, (MvPolynomial.mem_homogeneousSubmodule (σ := Var) (R := ℝ) k (p := Z k y)).2
      (isHomogeneous_Z (k := k) (y := y))⟩

lemma coeff_ZPk (k : ℕ) (y : ℝ²⁴) (d : Var →₀ ℕ) :
    MvPolynomial.coeff d (ZPk k y).1 = MvPolynomial.coeff d (Z k y) :=
  rfl

lemma lin_eq_sum_C_mul_X (y : ℝ²⁴) :
    lin y = (univ : Finset Var).sum (fun i => C (y i) * X i) :=
  rfl

lemma Z_eq_sum_pow (k : ℕ) (y : ℝ²⁴) :
    Z k y = ((univ : Finset Var).sum (fun i => C (y i) * X i)) ^ k := by
  simp [Z, lin_eq_sum_C_mul_X]

lemma prod_C_mul_X_pow_eq_monomial (y : ℝ²⁴) (g : Var → ℕ) :
    (∏ i : Var, (C (y i) * X i : Poly) ^ g i) =
      monomial (Finsupp.equivFunOnFinite.symm g) (∏ i : Var, (y i) ^ g i) := by
  let s : Var →₀ ℕ := Finsupp.equivFunOnFinite.symm g
  -- Expand each factor and collect constants/variables.
  have hpow (i : Var) :
      (C (y i) * X i : Poly) ^ g i = (C ((y i) ^ g i) : Poly) * (X i) ^ g i := by
    -- In a commutative semiring, `(a*b)^n = a^n*b^n`.
    simp [mul_pow, MvPolynomial.C_pow]
  -- Use commutativity to split the product.
  calc
    (∏ i : Var, (C (y i) * X i : Poly) ^ g i)
        = (∏ i : Var, (C ((y i) ^ g i) : Poly) * (X i) ^ g i) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            simp [hpow i]
    _ = (∏ i : Var, (C ((y i) ^ g i) : Poly)) * (∏ i : Var, (X i : Poly) ^ g i) := by
            simp [Finset.prod_mul_distrib]
    _ = (C (∏ i : Var, (y i) ^ g i) : Poly) * (∏ i : Var, (X i : Poly) ^ g i) := by
            simp [map_prod]
    _ = (C (∏ i : Var, (y i) ^ g i) : Poly) *
          (∏ i ∈ s.support, (X i : Poly) ^ s i) := by
            -- Restrict the product to the support since factors outside are `1`.
            refine congrArg (fun t => (C (∏ i : Var, (y i) ^ g i) : Poly) * t) ?_
            have hsub : s.support ⊆ (univ : Finset Var) := by
              intro i hi
              simp
            exact (Finset.prod_subset
              (s₁ := s.support)
              (s₂ := (univ : Finset Var))
              (f := fun i => (X i : Poly) ^ s i)
              hsub
              (by
                intro i hi hnot
                have : s i = 0 := Finsupp.notMem_support_iff.mp hnot
                simp [this])).symm
    _ = monomial s (∏ i : Var, (y i) ^ g i) := by
            -- Convert the support product of `X` powers to a `monomial`.
            simp [MvPolynomial.monomial_eq, mul_comm]

lemma coeff_lin_pow_of_degree (k : ℕ) (y : ℝ²⁴) (d : Var →₀ ℕ)
    (hd : d.degree = k) :
    MvPolynomial.coeff d (Z k y) =
      (Nat.multinomial (univ : Finset Var) (fun i => d i) : ℝ) *
        ∏ i : Var, (y i) ^ d i := by
  -- Expand using the multinomial theorem.
  have hZ :
      Z k y =
        ∑ g ∈ Finset.piAntidiag (univ : Finset Var) k,
          (Nat.multinomial (univ : Finset Var) g : Poly) *
            ∏ i ∈ (univ : Finset Var), (C (y i) * X i : Poly) ^ g i := by
    -- `lin y` is a sum over `univ`, and `Z k y = (lin y)^k`.
    dsimp [Z, lin]
    exact
      (Finset.sum_pow_eq_sum_piAntidiag (s := (univ : Finset Var))
        (f := fun i => (C (y i) * X i : Poly)) k)
  -- Take coefficients.
  have hcoeff :
      MvPolynomial.coeff d (Z k y) =
        ∑ g ∈ Finset.piAntidiag (univ : Finset Var) k,
          MvPolynomial.coeff d
            ((Nat.multinomial (univ : Finset Var) g : Poly) *
              ∏ i ∈ (univ : Finset Var), (C (y i) * X i : Poly) ^ g i) := by
    -- `coeff` is additive.
    simpa [MvPolynomial.coeff_sum] using! congrArg (MvPolynomial.coeff d) hZ
  -- Rewrite each summand as a monomial, so `coeff` becomes an `ite`.
  have hterm (g : Var → ℕ) :
      MvPolynomial.coeff d
          ((Nat.multinomial (univ : Finset Var) g : Poly) *
            ∏ i ∈ (univ : Finset Var), (C (y i) * X i : Poly) ^ g i) =
        ite (Finsupp.equivFunOnFinite.symm g = d)
          ((Nat.multinomial (univ : Finset Var) g : ℝ) * ∏ i : Var, (y i) ^ g i) 0 := by
    -- Put the product term in `monomial` form.
    have hprod :
        (∏ i ∈ (univ : Finset Var), (C (y i) * X i : Poly) ^ g i) =
          monomial (Finsupp.equivFunOnFinite.symm g) (∏ i : Var, (y i) ^ g i) := by
      simpa using! (prod_C_mul_X_pow_eq_monomial (y := y) (g := g))
    -- Rewrite the scalar as `C` and apply `coeff_monomial`.
    -- `Nat.cast` into `MvPolynomial` is `C`.
    have hscalar :
        (Nat.multinomial (univ : Finset Var) g : Poly) =
          (C (Nat.multinomial (univ : Finset Var) g : ℝ) : Poly) := by
      simp
    -- Compute the coefficient.
    -- `coeff d (C m * monomial e a) = if e = d then m*a else 0`.
    -- Then rewrite to our `ite` normal form.
    -- Avoid `simp` loops on associativity/commutativity: rewrite in two steps.
    rw [hscalar, hprod, MvPolynomial.C_mul_monomial]
    simp [MvPolynomial.coeff_monomial]
  -- Only `g0 i = d i` can contribute, since `coeff_monomial` is an `ite` on the exponent.
  let g0 : Var → ℕ := fun i => d i
  have hg0 : g0 ∈ Finset.piAntidiag (univ : Finset Var) k := by
    have : (∑ i : Var, d i) = k := by simpa [Finsupp.degree_eq_sum] using! hd
    simp [Finset.mem_piAntidiag, g0, this]
  have hgd0 : Finsupp.equivFunOnFinite.symm g0 = d := by
    ext i
    rfl
  have hsum :
      (∑ g ∈ Finset.piAntidiag (univ : Finset Var) k,
          ite (Finsupp.equivFunOnFinite.symm g = d)
            ((Nat.multinomial (univ : Finset Var) g : ℝ) * ∏ i : Var, (y i) ^ g i) 0) =
        (Nat.multinomial (univ : Finset Var) g0 : ℝ) * ∏ i : Var, (y i) ^ g0 i := by
    -- Reduce the `ite` sum to the unique contributing index `g0`.
    -- (Work with `Finset.sum` directly to avoid binder parsing issues.)
    set s : Finset (Var → ℕ) := Finset.piAntidiag (univ : Finset Var) k
    have hsingle :
        s.sum (fun g =>
            ite (Finsupp.equivFunOnFinite.symm g = d)
              ((Nat.multinomial (univ : Finset Var) g : ℝ) * ∏ i : Var, (y i) ^ g i) 0) =
          ite (Finsupp.equivFunOnFinite.symm g0 = d)
            ((Nat.multinomial (univ : Finset Var) g0 : ℝ) * ∏ i : Var, (y i) ^ g0 i) 0 := by
      refine (Finset.sum_eq_single_of_mem g0 (by simpa [s] using! hg0) ?_)
      intro g hg hne
      have : Finsupp.equivFunOnFinite.symm g ≠ d := by
        intro h
        apply hne
        funext i
        have := congrArg (fun (t : Var →₀ ℕ) => t i) h
        simpa [g0] using! this
      simp [this]
    -- Unfold `s` and simplify the surviving `ite` using `hgd0`.
    simpa [s, hgd0] using! hsingle
  -- Finish by rewriting `g0` back to `d`.
  grind only

end Typeclass

/-- `Fischer.Pk k` is a normed additive commutative group via the Fischer inner product. -/
public instance (k : ℕ) : NormedAddCommGroup (Fischer.Pk k) :=
  (show InnerProductSpace.Core ℝ (Fischer.Pk k) from inferInstance).toNormedAddCommGroup

/-- `Fischer.Pk k` is complete, since it is finite-dimensional. -/
public instance (k : ℕ) : CompleteSpace (Fischer.Pk k) := by
  simpa using! (FiniteDimensional.complete ℝ (Fischer.Pk k))

/-!
### Fischer reproducing identity for `ZPk`

The coefficient model of the Fischer inner product makes `Z_{k,y}(x) = ⟪x,y⟫^k`
into a reproducing kernel element (up to the factor `k!`).
-/

/-- Evaluate a polynomial `p` at the point `y : ℝ²⁴`. -/
@[expose] public noncomputable def evalPoly (y : ℝ²⁴) (p : Poly) : ℝ :=
  MvPolynomial.eval (fun i : Var => y i) p

/-- Evaluate a homogeneous polynomial `p : Pk k` at `y : ℝ²⁴`. -/
@[expose] public noncomputable def evalPk (k : ℕ) (y : ℝ²⁴) (p : Fischer.Pk k) : ℝ :=
  evalPoly (y := y) p.1

lemma support_subset_expFinset {k : ℕ} (p : Fischer.Pk k) :
    p.1.support ⊆ Fischer.expFinset k := by
  intro d hd
  -- If `d` is in the support, its coefficient is nonzero, hence its degree must be `k`.
  have hcoeff : MvPolynomial.coeff d p.1 ≠ 0 := by
    simpa [MvPolynomial.mem_support_iff] using! hd
  have hdeg : Finsupp.degree d = k := by
    by_contra hdeg'
    have hz : MvPolynomial.coeff d p.1 = 0 :=
      Fischer.Pk.coeff_eq_zero_of_degree_ne (k := k) (hp := p.2) (d := d) hdeg'
    exact hcoeff hz
  simpa [Fischer.mem_expFinset_iff] using! hdeg

lemma evalPk_eq_sum_expFinset (k : ℕ) (y : ℝ²⁴) (p : Fischer.Pk k) :
    evalPk (k := k) (y := y) p =
      (Fischer.expFinset k).sum (fun d =>
        (MvPolynomial.coeff d p.1) * ∏ i : Var, (y i) ^ d i) := by
  -- Start from `eval_eq'`, then extend the sum from `support` to `expFinset k`.
  have hsupport :
      evalPk (k := k) (y := y) p =
        p.1.support.sum (fun d => (MvPolynomial.coeff d p.1) * ∏ i : Var, (y i) ^ d i) := by
    -- `eval_eq'` already uses a `support`-sum.
    dsimp [evalPk, evalPoly]
    exact (MvPolynomial.eval_eq' (σ := Var) (R := ℝ) (X := fun i : Var => y i) (f := p.1))
  -- Replace `support` by `expFinset k` via `Finset.sum_subset` (coeffs vanish off support).
  have hsub : p.1.support ⊆ Fischer.expFinset k := support_subset_expFinset (p := p)
  have hvanish :
      ∀ d ∈ Fischer.expFinset k, d ∉ p.1.support →
        (MvPolynomial.coeff d p.1) * ∏ i : Var, (y i) ^ d i = 0 := by
    intro d hdexp hdnsupp
    have : MvPolynomial.coeff d p.1 = 0 := by
      simpa [MvPolynomial.notMem_support_iff] using! hdnsupp
    simp [this]
  -- Replace the support-sum by the expFinset-sum.
  have :=
    (Finset.sum_subset hsub (f := fun d =>
      (MvPolynomial.coeff d p.1) * ∏ i : Var, (y i) ^ d i) hvanish)
  -- `Finset.sum_subset` gives equality of the two sums.
  -- Use `hsupport` to rewrite `evalPk`.
  simpa [hsupport] using! this

lemma multiFactorial_mul_multinomial_eq_factorial (k : ℕ) (d : Var →₀ ℕ)
    (hd : d.degree = k) :
    ((Fischer.multiFactorial d : ℕ) : ℝ) *
        (Nat.multinomial (univ : Finset Var) d : ℝ) =
      (Nat.factorial k : ℝ) := by
  -- Use `Nat.multinomial_spec` and the fact that `∏ i ∈ univ, (d i)!` equals `multiFactorial d`.
  have hspec :
      (∏ i ∈ (univ : Finset Var), Nat.factorial (d i)) *
          Nat.multinomial (univ : Finset Var) d =
        Nat.factorial (∑ i ∈ (univ : Finset Var), d i) := by
    -- This is exactly `Nat.multinomial_spec`.
    simpa using! (Nat.multinomial_spec (s := (univ : Finset Var)) (f := d))
  have hprod :
      (∏ i ∈ (univ : Finset Var), Nat.factorial (d i)) = Fischer.multiFactorial d := by
    -- Outside `d.support`, `d i = 0` and the factorial is `1`.
    -- `Finset.prod_subset` compares the product over `support` with the product over `univ`.
    have hsub : d.support ⊆ (univ : Finset Var) := by
      intro i hi
      simp
    have :=
      (Finset.prod_subset (s₁ := d.support) (s₂ := (univ : Finset Var))
        (f := fun i => Nat.factorial (d i)) hsub (by
          intro i hi hnot
          have : d i = 0 := Finsupp.notMem_support_iff.mp hnot
          simp [this])).symm
    -- Unfold `multiFactorial` and rewrite.
    simpa [Fischer.multiFactorial] using! this
  have hsum : (∑ i ∈ (univ : Finset Var), d i) = k := by
    -- `d.degree = k` and on a finite type degree is the `univ` sum.
    simpa [Finsupp.degree_eq_sum] using! hd
  -- Convert the nat equality to ℝ and finish.
  have hspec' : (Fischer.multiFactorial d * Nat.multinomial (univ : Finset Var) d : ℕ) =
      Nat.factorial k := by
    -- Rewrite `hspec` with `hprod` and `hsum`.
    -- `hspec` is in `ℕ`, so transport carefully.
    -- Replace the product by `multiFactorial`, and the sum by `k`.
    simpa [hprod, hsum, Nat.mul_assoc] using! hspec
  -- Cast to `ℝ`.
  exact_mod_cast hspec'

/-- Fischer inner product with `ZPk` gives evaluation, up to the factor `k!`. -/
lemma inner_ZPk_eq_factorial_eval (k : ℕ) (y : ℝ²⁴) (p : Fischer.Pk k) :
    Fischer.inner k (ZPk k y) p = (Nat.factorial k : ℝ) * evalPk (k := k) (y := y) p := by
  -- Expand the Fischer inner product.
  unfold Fischer.inner
  -- Rewrite the coefficient of `ZPk` using the multinomial theorem.
  have hcoeffZ :
      ∀ d ∈ Fischer.expFinset k,
        ((Fischer.multiFactorial d : ℕ) : ℝ) * (MvPolynomial.coeff d (ZPk k y).1) =
          (Nat.factorial k : ℝ) * ∏ i : Var, (y i) ^ d i := by
    intro d hdexp
    have hddeg : d.degree = k := by
      simpa [Fischer.mem_expFinset_iff] using! (Fischer.mem_expFinset_iff k d).1 hdexp
    -- Use the coefficient formula.
    have hcoeff :
        MvPolynomial.coeff d (ZPk k y).1 =
          (Nat.multinomial (univ : Finset Var) (fun i : Var => d i) : ℝ) *
            ∏ i : Var, (y i) ^ d i := by
      simpa [ZPk, Z, lin] using! coeff_lin_pow_of_degree (k := k) (y := y) (d := d) hddeg
    -- Cancel factorial factors.
    have hfac :
        ((Fischer.multiFactorial d : ℕ) : ℝ) *
            (Nat.multinomial (univ : Finset Var) (fun i : Var => d i) : ℝ) =
          (Nat.factorial k : ℝ) :=
      multiFactorial_mul_multinomial_eq_factorial (k := k) (d := d) hddeg
    -- Combine.
    -- Avoid `simp` loops by rewriting and regrouping explicitly.
    grind only
  -- Use `hcoeffZ` to rewrite the inner sum.
  let S : ℝ :=
    (Fischer.expFinset k).sum (fun d => (MvPolynomial.coeff d p.1) * ∏ i : Var, (y i) ^ d i)
  have :
      (Fischer.expFinset k).sum (fun d =>
        ((Fischer.multiFactorial d : ℕ) : ℝ) * MvPolynomial.coeff d (ZPk k y).1 *
          MvPolynomial.coeff d p.1) =
        (Nat.factorial k : ℝ) *
          S := by
    -- First rewrite each summand using `hcoeffZ`, then factor out the common scalar `k!`.
    have hrewrite :
        (Fischer.expFinset k).sum (fun d =>
            ((Fischer.multiFactorial d : ℕ) : ℝ) * MvPolynomial.coeff d (ZPk k y).1 *
              MvPolynomial.coeff d p.1) =
          (Fischer.expFinset k).sum (fun d =>
            (Nat.factorial k : ℝ) * ((MvPolynomial.coeff d p.1) * ∏ i : Var, (y i) ^ d i)) := by
      refine Finset.sum_congr rfl ?_
      grind only
    -- Now factor out `k!`.
    -- `Finset.mul_sum` is `a * (∑ f) = ∑ (a * f)`, so use it backwards.
    have hfactor :
        (Fischer.expFinset k).sum (fun d =>
            (Nat.factorial k : ℝ) * ((MvPolynomial.coeff d p.1) * ∏ i : Var, (y i) ^ d i)) =
          (Nat.factorial k : ℝ) * S := by
      simpa [S] using!
        (Finset.mul_sum (s := Fischer.expFinset k)
          (f := fun d => (MvPolynomial.coeff d p.1) * ∏ i : Var, (y i) ^ d i)
          (a := (Nat.factorial k : ℝ))).symm
    exact hrewrite.trans hfactor
  -- Identify the remaining sum with evaluation.
  have heval : S = evalPk (k := k) (y := y) p := by
    simpa [S] using! (evalPk_eq_sum_expFinset (k := k) (y := y) (p := p)).symm
  -- Put everything together.
  -- `this` is the transformed inner sum, and `heval` turns it into evaluation.
  simpa [evalPk, evalPoly, heval, mul_assoc, mul_left_comm, mul_comm] using! this

/-- The scaled kernel element `Z_{k,y} / k!`, so that Fischer inner product gives evaluation. -/
@[expose] public noncomputable def ZscaledPk (k : ℕ) (y : ℝ²⁴) : Fischer.Pk k :=
  ((Nat.factorial k : ℝ)⁻¹) • ZPk k y

lemma inner_ZscaledPk_eq_eval (k : ℕ) (y : ℝ²⁴) (p : Fischer.Pk k) :
    Fischer.inner k (ZscaledPk k y) p = evalPk (k := k) (y := y) p := by
  -- Expand scalars on the left and cancel `k!`.
  have hk : (Nat.factorial k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.factorial_pos k))
  -- Use the unscaled reproducing identity.
  have h := inner_ZPk_eq_factorial_eval (k := k) (y := y) (p := p)
  -- Scale the left argument.
  -- `inner_smul_left` is the defining lemma for the Fischer inner product.
  have h' :
      Fischer.inner k (ZscaledPk k y) p =
        ((Nat.factorial k : ℝ)⁻¹) * Fischer.inner k (ZPk k y) p := by
    simpa [ZscaledPk] using! (Fischer.inner_smul_left (k := k) (r := (Nat.factorial k : ℝ)⁻¹)
      (p := ZPk k y) (q := p))
  -- Substitute and simplify.
  simp_all

local instance (k : ℕ) : NormedAddCommGroup (Fischer.Pk k) :=
  (show InnerProductSpace.Core ℝ (Fischer.Pk k) from inferInstance).toNormedAddCommGroup

local instance (k : ℕ) : CompleteSpace (Fischer.Pk k) := by
  simpa using! (FiniteDimensional.complete ℝ (Fischer.Pk k))

/-!
### The harmonic feature map and Gram PSD kernel

Let `Harm k` be the harmonic subspace (kernel of the Laplacian) inside `Pk k`. We define the
feature map `Φ k y` as the orthogonal projection of `ZscaledPk k y` onto `Harm k`. This yields
the Gram kernel `harmKernel24 k`.
-/

/-- The harmonic feature map `Φ_k : ℝ²⁴ → Harm k`. -/
@[expose] public noncomputable def Φ (k : ℕ) (y : ℝ²⁴) : Harmonic.Harm k :=
  (Harmonic.Harm k).orthogonalProjection (ZscaledPk k y)

/-- Reproducing property: pairing with `Φ k y` evaluates a harmonic polynomial at `y`. -/
public lemma inner_Φ_eq_eval (k : ℕ) (y : ℝ²⁴) (h : Harmonic.Harm k) :
    ⟪Φ k y, h⟫ = evalPk (k := k) (y := y) (h : Fischer.Pk k) := by
  -- Use the defining property of orthogonal projection, then the reproducing identity.
  simpa [Φ] using!
    (Submodule.inner_orthogonalProjection_eq_of_mem_right (K := Harmonic.Harm k)
      (u := h) (v := ZscaledPk k y)).trans
      (inner_ZscaledPk_eq_eval (k := k) (y := y) (p := (h : Fischer.Pk k)))

/-- The harmonic Gram kernel (PSD by construction). -/
@[expose] public noncomputable def harmKernel24 (k : ℕ) (u v : ℝ²⁴) : ℝ :=
  ⟪(Φ k u : Fischer.Pk k), (Φ k v : Fischer.Pk k)⟫

/-- Gram identity for the feature map `Φ`: double sums of `harmKernel24` are inner products. -/
public lemma sum_sum_harmKernel24_eq_inner_sum_Φ (k : ℕ) (C : Finset ℝ²⁴) :
    C.sum (fun u => C.sum (fun v => harmKernel24 k u v)) =
      ⟪(C.sum (fun u => (Φ k u : Fischer.Pk k))), (C.sum (fun u => (Φ k u : Fischer.Pk k)))⟫ := by
  -- Gram form: `∑_{u,v} ⟪Φ u, Φ v⟫ = ⟪∑ Φ u, ∑ Φ v⟫`.
  let S : Fischer.Pk k := C.sum (fun u => (Φ k u : Fischer.Pk k))
  have hS :
      ⟪S, S⟫ =
        C.sum (fun u => C.sum (fun v => harmKernel24 k u v)) := by
    dsimp [S, harmKernel24]
    rw [inner_sum]
    simp only [sum_inner]
    exact
      (Finset.sum_comm (s := C) (t := C)
        (f := fun v u => ⟪(Φ k u : Fischer.Pk k), (Φ k v : Fischer.Pk k)⟫))
  simpa [S] using! hS.symm

/-- The Gram sum `∑_{u,v ∈ C} harmKernel24 k u v` is nonnegative. -/
public lemma sum_sum_harmKernel24_nonneg (k : ℕ) (C : Finset ℝ²⁴) :
    0 ≤ C.sum (fun u => C.sum (fun v => harmKernel24 k u v)) := by
  rw [sum_sum_harmKernel24_eq_inner_sum_Φ]
  exact real_inner_self_nonneg

end

end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.ZonalKernel
