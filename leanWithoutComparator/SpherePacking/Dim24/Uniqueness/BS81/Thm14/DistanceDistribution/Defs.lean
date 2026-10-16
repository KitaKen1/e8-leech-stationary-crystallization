module
public import SpherePacking.Dim24.Uniqueness.BS81.Defs
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.Defs

/-!
# Distance-distribution definitions for BS81 Theorem 14

This file sets up the basic objects used to derive the BS81 distance distribution (equation (11)):
the explicit support set of admissible inner products, and the Gegenbauer "row sums" used for the
linear constraints coming from LP tightness.

## Main definitions
* `bs81Support24`
* `gegenbauerRowSum24`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14

noncomputable section

open scoped RealInnerProductSpace BigOperators

open Polynomial
open Uniqueness.BS81.LP

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
## The BS81 support set for inner products in the equality case
-/

/-- The support set `{1, -1, ±1/2, ±1/4, 0}` in the BS81 equality case. -/
@[expose] public def bs81Support24 : Finset ℝ :=
  {1, -1, (1 / 2 : ℝ), (-1 / 2 : ℝ), (1 / 4 : ℝ), (-1 / 4 : ℝ), 0}

/-- Membership in `bs81Support24`, written as an explicit disjunction. -/
public lemma mem_bs81Support24_iff (t : ℝ) :
    t ∈ bs81Support24 ↔
      t = (1 : ℝ) ∨ t = (-1 : ℝ) ∨ t = (1 / 2 : ℝ) ∨ t = (-1 / 2 : ℝ) ∨
        t = (1 / 4 : ℝ) ∨ t = (-1 / 4 : ℝ) ∨ t = (0 : ℝ) := by
  simp [bs81Support24]

attribute [grind =] mem_bs81Support24_iff

/-!
## Row sums of Gegenbauer polynomials

For a fixed `u ∈ C`, define the "row sum"
`S_k(u) = ∑_{v∈C} P_k(⟪u,v⟫)`.

In the LP equality case, these row sums vanish for degrees `k=1..t`.
-/

def gegenbauerRowSum24 (k : ℕ) (C : Finset ℝ²⁴) (u : ℝ²⁴) : ℝ :=
  C.sum (fun v => (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ))

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14
