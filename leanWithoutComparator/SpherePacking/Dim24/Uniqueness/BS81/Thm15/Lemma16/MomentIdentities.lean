-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Package
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16.SphereAvgMoments24.Inner
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.NormNum

/-!
# Moment identities for BS81 Lemma 16

We apply the spherical-design identity (BS81 equation (14)) to the homogeneous polynomials
`x ↦ (⟪x, v⟫ : ℝ) ^ k` for `k = 2,4`. Using the explicit spherical averages on `Ω₂₄`, this yields
numerical identities for the corresponding sums over an equality-case code `C` of size `196560`.

## Main statements
* `sum_inner_sq_eq_8190`
* `sum_inner_pow_four_eq_945`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16

noncomputable section

open scoped RealInnerProductSpace BigOperators

open Polynomial MvPolynomial

open Uniqueness.BS81.Thm14

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
We specialize the BS81 design axiom (equation (14)) to the homogeneous polynomials
`p_k(x) = (∑ i, vᵢ Xᵢ)^k`, whose evaluation is `x ↦ (⟪x,v⟫)^k`.
-/

def innerLinearPoly (v : ℝ²⁴) : MvPolynomial (Fin 24) ℝ :=
  ∑ i : Fin 24, (MvPolynomial.C (v i)) * (MvPolynomial.X i)

lemma innerLinearPoly_isHomogeneous (v : ℝ²⁴) : (innerLinearPoly v).IsHomogeneous 1 := by
  -- A sum of degree-1 monomials is homogeneous of degree 1.
  simpa [innerLinearPoly] using!
    (MvPolynomial.IsHomogeneous.sum (s := (Finset.univ : Finset (Fin 24)))
      (φ := fun i : Fin 24 => (MvPolynomial.C (v i)) * (MvPolynomial.X i)) (n := 1)
      (fun i a => isHomogeneous_C_mul_X (v.ofLp i) i))

lemma mvPolyEval24_innerLinearPoly (v x : ℝ²⁴) :
    mvPolyEval24 (innerLinearPoly v) x = (⟪x, v⟫ : ℝ) := by
  -- `eval` turns `C (v i) * X i` into `v i * x i`, which is the coordinate sum for `⟪x,v⟫`.
  simp [mvPolyEval24, innerLinearPoly, PiLp.inner_apply, mul_comm]

lemma mvPolyEval24_innerLinearPoly_pow_apply (v x : ℝ²⁴) (k : ℕ) :
    mvPolyEval24 (innerLinearPoly v ^ k) x = (⟪x, v⟫ : ℝ) ^ k := by
  -- `MvPolynomial.eval` is a ring hom, so evaluation commutes with powers.
  simpa [mvPolyEval24_innerLinearPoly] using!
    (by simp [mvPolyEval24, map_pow] :
      mvPolyEval24 (innerLinearPoly v ^ k) x = (mvPolyEval24 (innerLinearPoly v) x) ^ k)

lemma mvPolyEval24_innerLinearPoly_pow (v : ℝ²⁴) (k : ℕ) :
    mvPolyEval24 (innerLinearPoly v ^ k) = fun x : ℝ²⁴ => (⟪x, v⟫ : ℝ) ^ k := by
  funext x
  simpa using! (mvPolyEval24_innerLinearPoly_pow_apply (v := v) (x := x) (k := k))

private lemma sum_eq_card_mul_of_finsetAvg_eq (Cfin : Finset ℝ²⁴) (g : ℝ²⁴ → ℝ) (c : ℝ)
    (havg : finsetAvg Cfin g = c) : Cfin.sum g = (Cfin.card : ℝ) * c := by
  by_cases hC0 : Cfin.card = 0
  · have hCfin : Cfin = ∅ := Finset.card_eq_zero.mp hC0
    simp [hCfin]
  · have hcardR : (Cfin.card : ℝ) ≠ 0 := by exact_mod_cast hC0
    have hmul := congrArg (fun t : ℝ => (Cfin.card : ℝ) * t) (by
      simpa [finsetAvg] using! havg)
    simpa [mul_assoc, hcardR] using! hmul

private lemma sum_inner_pow_of_design11_aux (C : Set ℝ²⁴)
    (h : Uniqueness.BS81.Thm14.EqCase24Pkg C) (v : ℝ²⁴) (k : ℕ) (hk : k ≤ 11)
    (rhs : ℝ) (hsphere : sphereAvg24 (fun x : ℝ²⁴ => (⟪x, v⟫ : ℝ) ^ k) = rhs) :
    (h.code.finite.toFinset.sum fun u => (⟪u, v⟫ : ℝ) ^ k) =
      (h.code.finite.toFinset.card : ℝ) * rhs := by
  let Cfin : Finset ℝ²⁴ := h.code.finite.toFinset
  have hD : IsBS81SphericalDesign24 11 Cfin := h.design11
  have hhom : (innerLinearPoly v ^ k).IsHomogeneous k := by
    simpa [Nat.one_mul] using! (innerLinearPoly_isHomogeneous (v := v)).pow k
  have havg :
      finsetAvg Cfin (fun u : ℝ²⁴ => (⟪u, v⟫ : ℝ) ^ k) =
        sphereAvg24 (fun x : ℝ²⁴ => (⟪x, v⟫ : ℝ) ^ k) := by
    have h' := hD.2 k (innerLinearPoly v ^ k) hk hhom
    simpa [mvPolyEval24_innerLinearPoly_pow] using! h'
  have hsum :
      Cfin.sum (fun u : ℝ²⁴ => (⟪u, v⟫ : ℝ) ^ k) = (Cfin.card : ℝ) * rhs :=
    sum_eq_card_mul_of_finsetAvg_eq (Cfin := Cfin) (g := fun u : ℝ²⁴ => (⟪u, v⟫ : ℝ) ^ k)
      (c := rhs) (havg.trans hsphere)
  simpa [Cfin] using! hsum

theorem sum_inner_sq_of_design11
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (v : ℝ²⁴) :
    (h.code.finite.toFinset.sum fun u => (⟪u, v⟫ : ℝ) ^ 2) =
      ((h.code.finite.toFinset.card : ℝ) / 24) * ‖v‖ ^ 2 := by
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using!
    (sum_inner_pow_of_design11_aux (C := C) (h := h) (v := v) (k := 2) (hk := by decide)
      (rhs := (1 / 24 : ℝ) * ‖v‖ ^ 2)
      (SphereAvgMoments24.sphereAvg24_inner_pow_two (v := v)))

theorem sum_inner_pow_four_of_design11
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (v : ℝ²⁴) :
    (h.code.finite.toFinset.sum fun u => (⟪u, v⟫ : ℝ) ^ 4) =
      ((h.code.finite.toFinset.card : ℝ) / 208) * ‖v‖ ^ 4 := by
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using!
    (sum_inner_pow_of_design11_aux (C := C) (h := h) (v := v) (k := 4) (hk := by decide)
      (rhs := (1 / 208 : ℝ) * ‖v‖ ^ 4)
      (SphereAvgMoments24.sphereAvg24_inner_pow_four (v := v)))

/-- The design identity for `k = 2`, specialized to `|C| = 196560`, yields the constant `8190`. -/
public theorem sum_inner_sq_eq_8190
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (hcard : h.code.finite.toFinset.card = 196560)
    (v : ℝ²⁴) :
    (h.code.finite.toFinset.sum fun u => (⟪u, v⟫ : ℝ) ^ 2) = (8190 : ℝ) * ‖v‖ ^ 2 := by
  have hmain := sum_inner_sq_of_design11 (C := C) h v
  -- `196560 / 24 = 8190`.
  have hdiv : ((196560 : ℝ) / 24) = (8190 : ℝ) := by norm_num
  simpa [hcard, hdiv] using! hmain

/-- The design identity for `k = 4`, specialized to `|C| = 196560`, yields the constant `945`. -/
public theorem sum_inner_pow_four_eq_945
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (hcard : h.code.finite.toFinset.card = 196560)
    (v : ℝ²⁴) :
    (h.code.finite.toFinset.sum fun u => (⟪u, v⟫ : ℝ) ^ 4) = (945 : ℝ) * ‖v‖ ^ 4 := by
  have hmain := sum_inner_pow_four_of_design11 (C := C) h v
  -- `196560 / 208 = 945`.
  have hdiv : ((196560 : ℝ) / 208) = (945 : ℝ) := by norm_num
  simpa [hcard, hdiv] using! hmain

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16
