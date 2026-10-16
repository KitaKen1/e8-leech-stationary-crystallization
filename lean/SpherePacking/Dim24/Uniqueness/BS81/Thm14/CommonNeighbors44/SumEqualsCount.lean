-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44.IndPoly
import SpherePacking.Dim24.Uniqueness.BS81.EqCase24Support

/-!
# Rewrite the common-neighbor count as a sum

The core claim is:

`Set.ncard {w ∈ C | ⟪u,w⟫=1/2 ∧ ⟪v,w⟫=1/2}
   = ∑_{w∈C} indPoly(⟪u,w⟫) * indPoly(⟪v,w⟫)`.

This uses only:
- the equality-case support restriction `⟪u,w⟫ ∈ {1, -1, ±1/2, ±1/4, 0}`,
- and the special values of `indPoly` on that finite set.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44Steps

noncomputable section

open scoped RealInnerProductSpace BigOperators

open Set
open Uniqueness.BS81
open Uniqueness.BS81.Thm14
open CommonNeighbors44Aux

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
Indicator behavior of `CommonNeighbors44Aux.indPoly` on the BS81 equality-case support set.

On the support set `{1, -1, ±1/2, ±1/4, 0}`, the polynomial `indPoly` equals:
- `1` at `t = 1/2`,
- `0` at `t ∈ {-1, -1/2, -1/4, 0, 1/4}`.

The value at `t = 1` is irrelevant for the common-neighbor sum because it is multiplied by
`indPoly (⟪v,u⟫) = indPoly 0 = 0` in the situation `⟪u,v⟫ = 0`.
-/

/-- If `⟪u,w⟫ = 1/2`, then `indPoly (⟪u,w⟫) = 1`. -/
public theorem indPoly_eq_one_of_inner_eq_half
    {u w : ℝ²⁴} (hinner : (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ)) :
    indPoly (⟪u, w⟫ : ℝ) = 1 := by
  simpa [hinner] using! (indPoly_half : indPoly (1 / 2 : ℝ) = 1)

/-- `indPoly` vanishes on the non-`1/2` values in the BS81 equality-case support set. -/
public theorem indPoly_eq_zero_of_inner_eq_support
    {t : ℝ}
    (ht : t = (-1 : ℝ) ∨ t = (-1 / 2 : ℝ) ∨ t = (-1 / 4 : ℝ) ∨ t = (0 : ℝ) ∨ t = (1 / 4 : ℝ)) :
    indPoly t = 0 := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · simpa using! (indPoly_neg_one : indPoly (-1 : ℝ) = 0)
  · simpa using! (indPoly_neg_half : indPoly (-1 / 2 : ℝ) = 0)
  · simpa using! (indPoly_neg_quarter : indPoly (-1 / 4 : ℝ) = 0)
  · simpa using! (indPoly_zero : indPoly (0 : ℝ) = 0)
  · simpa using! (indPoly_quarter : indPoly (1 / 4 : ℝ) = 0)

open scoped Classical in
/-- Rewrite the sum of indicator products as the common-neighbor count. -/
public theorem sum_indPoly_mul_indPoly_eq_commonNeighbors_card
    (C : Set ℝ²⁴) (h : EqCase24Pkg C)
    {u v : ℝ²⁴} (hu : u ∈ C) (hv : v ∈ C) (hinner : (⟪u, v⟫ : ℝ) = 0) :
    (h.code.finite.toFinset.sum fun w =>
        indPoly (⟪u, w⟫ : ℝ) * indPoly (⟪v, w⟫ : ℝ)) =
      (Set.ncard
          {w : ℝ²⁴ |
            w ∈ C ∧ (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ) ∧ (⟪v, w⟫ : ℝ) = (1 / 2 : ℝ)} : ℝ) := by
  let Cfin : Finset ℝ²⁴ := h.code.finite.toFinset
  let Q : ℝ²⁴ → Prop :=
    fun w : ℝ²⁴ => (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ) ∧ (⟪v, w⟫ : ℝ) = (1 / 2 : ℝ)
  let S : Set ℝ²⁴ := {w : ℝ²⁴ | w ∈ C ∧ Q w}
  have hEq : Uniqueness.BS81.EqCase24 C := EqCase24Pkg.toEqCase24 (C := C) h
  have hu1 : ‖u‖ = (1 : ℝ) := h.code.norm_one hu
  have hv1 : ‖v‖ = (1 : ℝ) := h.code.norm_one hv
  have inner_support {x y : ℝ²⁴} (hx : x ∈ C) (hy : y ∈ C) :=
    inner_eq_one_or_eq_neg_one_or_eq_half_or_eq_neg_half_or_eq_quarter_or_eq_neg_quarter_or_eq_zero
      (C := C) hEq (u := x) (v := y) hx hy
  have hterm (w : ℝ²⁴) (hwC : w ∈ C) :
      indPoly (⟪u, w⟫ : ℝ) * indPoly (⟪v, w⟫ : ℝ) = (if Q w then (1 : ℝ) else 0) := by
    have hw1 : ‖w‖ = (1 : ℝ) := h.code.norm_one hwC
    by_cases hQ : Q w
    · have hPu : indPoly (⟪u, w⟫ : ℝ) = 1 :=
        indPoly_eq_one_of_inner_eq_half (u := u) (w := w) hQ.1
      have hPv : indPoly (⟪v, w⟫ : ℝ) = 1 :=
        indPoly_eq_one_of_inner_eq_half (u := v) (w := w) hQ.2
      simp [hQ, hPu, hPv]
    · have hUsupp :=
        inner_support (x := u) (y := w) hu hwC
      have hVsupp :=
        inner_support (x := v) (y := w) hv hwC
      have hprod0 : indPoly (⟪u, w⟫ : ℝ) * indPoly (⟪v, w⟫ : ℝ) = 0 := by
        by_cases huHalf : (⟪u, w⟫ : ℝ) = (1 / 2 : ℝ)
        · have hvHalf : (⟪v, w⟫ : ℝ) ≠ (1 / 2 : ℝ) := by
            intro hvHalf
            exact hQ ⟨huHalf, hvHalf⟩
          have hPu : indPoly (⟪u, w⟫ : ℝ) = 1 :=
            indPoly_eq_one_of_inner_eq_half (u := u) (w := w) huHalf
          have hPv0 : indPoly (⟪v, w⟫ : ℝ) = 0 := by
            refine indPoly_eq_zero_of_inner_eq_support (t := (⟪v, w⟫ : ℝ)) ?_
            rcases hVsupp with hvEq1 | hvRest
            · have hwv : v = w := (inner_eq_one_iff_of_norm_eq_one hv1 hw1).1 hvEq1
              simp_all
            -- exclude `t = 1/2` using `hvHalf`, then pick the remaining support value
            · rcases hvRest with h | h | h | h | h | h
              · exact Or.inl h
              · exact absurd h hvHalf
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
              · exact Or.inr (Or.inr (Or.inl h))
              · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
          simp [hPu, hPv0]
        · by_cases huEq1 : (⟪u, w⟫ : ℝ) = (1 : ℝ)
          · have huw : u = w := (inner_eq_one_iff_of_norm_eq_one hu1 hw1).1 huEq1
            have hvw0 : (⟪v, w⟫ : ℝ) = (0 : ℝ) := by
              have : (⟪v, u⟫ : ℝ) = 0 := by simpa [real_inner_comm] using! hinner
              simpa [huw] using! this
            have hv0 : indPoly (⟪v, w⟫ : ℝ) = 0 := by
              simpa [hvw0] using! (indPoly_zero : indPoly (0 : ℝ) = 0)
            simp [hv0]
          · have hPu0 : indPoly (⟪u, w⟫ : ℝ) = 0 := by
              refine indPoly_eq_zero_of_inner_eq_support (t := (⟪u, w⟫ : ℝ)) ?_
              -- exclude `t = 1/2` and `t = 1`, then use the remaining support value
              rcases hUsupp with h | h | h | h | h | h | h
              · exact absurd h huEq1
              · exact Or.inl h
              · exact absurd h huHalf
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
              · exact Or.inr (Or.inr (Or.inl h))
              · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
            simp [hPu0]
      simpa [hQ] using! hprod0
  have hsum_rewrite :
      (Cfin.sum fun w => indPoly (⟪u, w⟫ : ℝ) * indPoly (⟪v, w⟫ : ℝ)) =
        Cfin.sum fun w => (if Q w then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro w hw
    have hwC : w ∈ C := by simpa [Cfin] using! hw
    simpa using! hterm w hwC
  have hsum_card :
      (Cfin.sum fun w => (if Q w then (1 : ℝ) else 0)) = ((Cfin.filter Q).card : ℝ) :=
    Finset.sum_boole Q Cfin
  have hSfin : S.Finite := by
    refine h.code.finite.subset ?_
    intro w hw
    exact hw.1
  have hSto :
      hSfin.toFinset = Cfin.filter Q := by
    ext w
    simp [S, Cfin, Q, and_left_comm, and_assoc, and_comm]
  have hcard_nat : Set.ncard S = (Cfin.filter Q).card := by
    simpa [hSto] using! (Set.ncard_eq_toFinset_card S hSfin)
  have hcard_real : (Set.ncard S : ℝ) = ((Cfin.filter Q).card : ℝ) := by
    exact_mod_cast hcard_nat
  -- Put everything together.
  have : (Cfin.sum fun w => indPoly (⟪u, w⟫ : ℝ) * indPoly (⟪v, w⟫ : ℝ)) =
      (Set.ncard S : ℝ) := by
    calc
      (Cfin.sum fun w => indPoly (⟪u, w⟫ : ℝ) * indPoly (⟪v, w⟫ : ℝ)) =
          Cfin.sum fun w => (if Q w then (1 : ℝ) else 0) := hsum_rewrite
      _ = ((Cfin.filter Q).card : ℝ) := hsum_card
      _ = (Set.ncard S : ℝ) := hcard_real.symm
  simpa [Cfin, S, Q, and_assoc] using! this

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44Steps
