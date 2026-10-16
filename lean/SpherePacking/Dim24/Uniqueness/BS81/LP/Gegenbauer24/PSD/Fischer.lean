-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Fischer inner product on homogeneous polynomials (24 variables)

This is an auxiliary development for proving PSD of zonal Gegenbauer kernels. We work in the
degree-`k` homogeneous piece `Pk k` of `MvPolynomial (Fin 24) ℝ` and define the Fischer inner
product by declaring the monomial basis orthogonal with weights `d! = ∏ i, (d i)!`.

## Main definitions
* `Pk`
* `inner`

## Main statements
* `inner_self_eq_zero_iff`
* `instInnerProductSpace`
-/
namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD
noncomputable section

open scoped BigOperators

open Finset

/-- The variable type for multivariate polynomials in 24 variables. -/
public abbrev Var : Type := Fin 24

/-- The polynomial ring `MvPolynomial (Fin 24) ℝ`. -/
public abbrev Poly : Type := MvPolynomial Var ℝ

namespace Fischer

open Finsupp MvPolynomial

/-- The set of exponent vectors of total degree `k`. -/
@[expose]
public def expSet (k : ℕ) : Set (Var →₀ ℕ) := {d | Finsupp.degree d = k}

/-- The set `expSet k` is finite. -/
public lemma expSet_finite (k : ℕ) : (expSet k).Finite := by
  -- `degree = k` is a subset of `degree ≤ k`, and the latter is finite for finite `Var`.
  have hle : expSet k ⊆ {d : Var →₀ ℕ | Finsupp.degree d ≤ k} := by
    intro d hd
    exact le_of_eq hd
  exact (Finsupp.finite_of_degree_le (σ := Var) k).subset hle

/-- A canonical finset enumerating all exponent vectors of total degree `k`. -/
@[expose]
public def expFinset (k : ℕ) : Finset (Var →₀ ℕ) :=
  (expSet_finite k).toFinset

/-- Membership in `expFinset k` is equivalent to having total degree `k`. -/
@[simp] public lemma mem_expFinset_iff (k : ℕ) (d : Var →₀ ℕ) :
    d ∈ expFinset k ↔ Finsupp.degree d = k := by
  simp [expFinset, expSet]

attribute [grind =] mem_expFinset_iff

/-- Multi-index factorial `d! := ∏ᵢ (d i)!`. -/
@[expose]
public def multiFactorial (d : Var →₀ ℕ) : ℕ :=
  d.support.prod fun i => Nat.factorial (d i)

private lemma multiFactorial_pos (d : Var →₀ ℕ) : 0 < multiFactorial d := by
  unfold multiFactorial
  -- Every factor is positive.
  positivity

private lemma multiFactorial_ne_zero (d : Var →₀ ℕ) : (multiFactorial d : ℝ) ≠ 0 := by
  have : multiFactorial d ≠ 0 :=
    Nat.ne_of_gt (multiFactorial_pos d)
  exact_mod_cast this

/-!
### Degree-`k` homogeneous component and Fischer inner product
-/

/-- The degree-`k` homogeneous submodule. -/
public abbrev Pk (k : ℕ) : Submodule ℝ Poly :=
  MvPolynomial.homogeneousSubmodule Var ℝ k

namespace Pk

variable {k : ℕ}

/-- Coefficients outside degree `k` vanish for `p ∈ Pk k`. -/
public lemma coeff_eq_zero_of_degree_ne {p : Poly} (hp : p ∈ Pk k) {d : Var →₀ ℕ}
    (hd : Finsupp.degree d ≠ k) :
    MvPolynomial.coeff d p = 0 := by
  -- `IsHomogeneous.coeff_eq_zero` is the key lemma.
  have hh : MvPolynomial.IsHomogeneous p k := by simpa [Pk] using! hp
  exact hh.coeff_eq_zero hd

end Pk

/-- Fischer inner product on `Pk k`. -/
@[expose]
public def inner (k : ℕ) (p q : Pk k) : ℝ :=
  (expFinset k).sum (fun d =>
    ((multiFactorial d : ℕ) : ℝ) * (MvPolynomial.coeff d p.1) * (MvPolynomial.coeff d q.1))

/-- Symmetry of the Fischer inner product. -/
public lemma inner_symm (k : ℕ) (p q : Pk k) : inner k p q = inner k q p := by
  simp [inner, mul_left_comm, mul_comm]

/-- Additivity of the Fischer inner product in the left argument. -/
public lemma inner_add_left (k : ℕ) (p₁ p₂ q : Pk k) :
    inner k (p₁ + p₂) q = inner k p₁ q + inner k p₂ q := by
  -- Expand coefficients and distribute the sum.
  simp [inner, Finset.sum_add_distrib, mul_add, add_mul, mul_left_comm, mul_comm]

/-- Homogeneity of the Fischer inner product in the left argument. -/
public lemma inner_smul_left (k : ℕ) (r : ℝ) (p q : Pk k) :
    inner k (r • p) q = r * inner k p q := by
  -- Expand coefficients of `r • p` and pull `r` out of the sum.
  unfold inner
  -- `simp` turns coefficients of scalar multiples into scalar multiples.
  -- Then use `Finset.mul_sum` (in reverse) to factor out the common scalar.
  simp [mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]

/-- Nonnegativity of `inner k p p`. -/
public lemma inner_self_nonneg (k : ℕ) (p : Pk k) :
    0 ≤ inner k p p := by
  -- Each summand is a nonnegative multiple of a square.
  refine Finset.sum_nonneg ?_
  intro d hd
  have hw : 0 ≤ ((multiFactorial d : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have hs : 0 ≤ (MvPolynomial.coeff d p.1) * (MvPolynomial.coeff d p.1) :=
    mul_self_nonneg (MvPolynomial.coeff d p.1)
  -- Put into a `mul_nonneg`.
  -- Rewrite `w * a * a` as `w * (a * a)`.
  simpa [inner, mul_assoc, mul_left_comm, mul_comm] using! mul_nonneg hw hs

/-- Definiteness: `inner k p p = 0` if and only if `p = 0`. -/
public lemma inner_self_eq_zero_iff (k : ℕ) (p : Pk k) :
    inner k p p = 0 ↔ p = 0 := by
  constructor
  · intro h
    -- From the sum of nonnegative terms being `0`, each term is `0`.
    have hnonnegTerm (d : Var →₀ ℕ) :
        0 ≤
          ((multiFactorial d : ℕ) : ℝ) *
            (MvPolynomial.coeff d p.1) * (MvPolynomial.coeff d p.1) := by
      have hw : 0 ≤ ((multiFactorial d : ℕ) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      have hs : 0 ≤ (MvPolynomial.coeff d p.1) * (MvPolynomial.coeff d p.1) :=
        mul_self_nonneg (MvPolynomial.coeff d p.1)
      simpa [mul_assoc] using! mul_nonneg hw hs
    have hterm :
        ∀ d ∈ expFinset k,
          ((multiFactorial d : ℕ) : ℝ) *
              (MvPolynomial.coeff d p.1) * (MvPolynomial.coeff d p.1) = 0 := by
      intro d hd
      -- Use `sum_eq_zero_iff_of_nonneg` on the defining sum.
      have hsum :
          (expFinset k).sum (fun d =>
              ((multiFactorial d : ℕ) : ℝ) *
                (MvPolynomial.coeff d p.1) * (MvPolynomial.coeff d p.1)) = 0 := by
        simpa [inner, mul_assoc, mul_left_comm, mul_comm] using! h
      have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun d _ => hnonnegTerm d)).1 hsum
      exact hall d hd
    -- Now show `p = 0` by ext on coefficients.
    ext d
    by_cases hddeg : Finsupp.degree d = k
    · have hdmem : d ∈ expFinset k := by
        simpa [mem_expFinset_iff] using! hddeg
      have h0 := hterm d hdmem
      -- Use weight ≠ 0 to conclude coefficient = 0.
      have hw : ((multiFactorial d : ℕ) : ℝ) ≠ 0 := multiFactorial_ne_zero d
      -- `w * a * a = 0` implies `a = 0` over `ℝ`.
      have hmul : (MvPolynomial.coeff d p.1) * (MvPolynomial.coeff d p.1) = 0 := by
        have :
            ((multiFactorial d : ℕ) : ℝ) *
              ((MvPolynomial.coeff d p.1) * (MvPolynomial.coeff d p.1)) = 0 := by
          simpa [mul_assoc] using! h0
        exact (mul_eq_zero.mp this).resolve_left hw
      have : MvPolynomial.coeff d p.1 = 0 := by
        simpa [mul_self_eq_zero] using! hmul
      simp [this]
    · -- Coefficient is zero since `p` is homogeneous of degree `k`.
      have hp : p.1 ∈ Pk k := p.2
      have : MvPolynomial.coeff d p.1 = 0 :=
        Pk.coeff_eq_zero_of_degree_ne (k := k) (hp := hp) (d := d) (by simpa using! hddeg)
      simp [this]
  · intro hp
    subst hp
    simp [inner]

section InnerCore

open ComplexConjugate

private lemma conj_eq_id (r : ℝ) : conj r = r := by simp

/-- Positive-definite `InnerProductSpace.Core` structure on `Pk k` induced by the Fischer inner
product. -/
public noncomputable instance instInnerCore (k : ℕ) : InnerProductSpace.Core ℝ (Pk k) where
  inner := inner k
  conj_inner_symm x y := by
    simpa [conj_eq_id] using! (inner_symm (k := k) (p := y) (q := x))
  re_inner_nonneg x := by
    simpa using! (inner_self_nonneg (k := k) (p := x))
  add_left x y z := by
    simpa using! (inner_add_left (k := k) (p₁ := x) (p₂ := y) (q := z))
  smul_left x y r := by
    simpa [conj_eq_id, mul_assoc] using! (inner_smul_left (k := k) (r := r) (p := x) (q := y))
  definite x hx :=
    (inner_self_eq_zero_iff (k := k) (p := x)).1 hx

end InnerCore

/-- `SeminormedAddCommGroup` structure on `Pk k` coming from the Fischer inner product. -/
public noncomputable instance instSeminormedAddCommGroup (k : ℕ) : SeminormedAddCommGroup (Pk k) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ) (F := Pk k)

/-- `NormedSpace` structure on `Pk k` coming from the Fischer inner product. -/
public noncomputable instance instNormedSpace (k : ℕ) : NormedSpace ℝ (Pk k) :=
  InnerProductSpace.Core.toNormedSpace (𝕜 := ℝ) (F := Pk k)

/-- `InnerProductSpace` structure on `Pk k` coming from the Fischer inner product. -/
public noncomputable instance instInnerProductSpace (k : ℕ) : InnerProductSpace ℝ (Pk k) :=
  InnerProductSpace.ofCore (𝕜 := ℝ) (F := Pk k) (cd := inferInstance)

end Fischer

end

end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD
