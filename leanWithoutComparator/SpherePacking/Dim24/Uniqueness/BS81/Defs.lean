module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Set.Card

/-!
# BS81 definitions for spherical codes

This file defines the basic objects used in the BS81 discussion of spherical codes on the unit
sphere `Ωₙ`.

Source: `paper/BS81/sources.tex` (Bannai-Sloane 1981), §1 and §4.

We keep this file definition-only so later modules can import it without pulling in heavy proof
dependencies.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

noncomputable section

open scoped RealInnerProductSpace BigOperators Pointwise

/-!
### Unit sphere

BS81 writes `Ωₙ` for the unit sphere in `ℝⁿ`.
We model it as a set.
-/

/-- The unit sphere `Ωₙ` in `EuclideanSpace ℝ (Fin n)`. -/
@[expose] public def omega (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ‖x‖ = (1 : ℝ)}

/-- Membership in `omega n` is the norm-one condition. -/
@[simp] public lemma mem_omega (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ omega n ↔ ‖x‖ = (1 : ℝ) := Iff.rfl

attribute [grind =] mem_omega

/-!
### Spherical codes

BS81: an `(n, M, s)` spherical code is a subset `C ⊆ Ωₙ` of size `M` such that `(u,v) ≤ s`
for all distinct `u,v ∈ C`.

We treat `M` as `Set.ncard C` rather than a separate parameter.
-/

/-- `IsSphericalCode n C s` means `C ⊆ Ωₙ` is finite and has pairwise inner products `≤ s`. -/
public structure IsSphericalCode (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (s : ℝ) : Prop where
  finite : C.Finite
  norm_one : ∀ ⦃u⦄, u ∈ C → ‖u‖ = (1 : ℝ)
  inner_le : ∀ ⦃u v⦄, u ∈ C → v ∈ C → u ≠ v → (⟪u, v⟫ : ℝ) ≤ s

attribute [grind cases] IsSphericalCode

/-!
### Distance distribution

BS81 defines, for `u ∈ C`, the numbers `A_t(u) = |{v ∈ C : (u,v) = t}|`.

We package `A_t(u)` as a `Nat` via `Set.ncard`. Since `C` is finite, these are always finite.
-/

/-- The number of `v ∈ C` with inner product `⟪u,v⟫ = t`. -/
@[expose] public def distCount {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℕ :=
  Set.ncard {v : EuclideanSpace ℝ (Fin n) | v ∈ C ∧ (⟪u, v⟫ : ℝ) = t}

/-!
### The BS81 §4 equality-case package (Theorem 14)

In §4, BS81 prove that an optimal `(24,196560,1/2)` code is a tight spherical 11-design and has an
explicit distance distribution (equation (11)).

Rather than encoding the full spherical-design API immediately, we record the *explicit*
consequences used later in the paper as a structure.
-/

/-- The BS81 equality-case data for an optimal `(24, 196560, 1/2)` spherical code. -/
public structure EqCase24 (C : Set ℝ²⁴) : Prop where
  code : IsSphericalCode 24 C (1 / 2 : ℝ)
  card_eq : Set.ncard C = 196560
  /-- Distance distribution (equation (11) in BS81, Theorem 14(e)). -/
  distCount_eq :
    ∀ ⦃u : ℝ²⁴⦄, u ∈ C →
      distCount (n := 24) C u (1 : ℝ) = 1 ∧
      distCount (n := 24) C u (-1 : ℝ) = 1 ∧
      distCount (n := 24) C u (1 / 2 : ℝ) = 4600 ∧
      distCount (n := 24) C u (-1 / 2 : ℝ) = 4600 ∧
      distCount (n := 24) C u (1 / 4 : ℝ) = 47104 ∧
      distCount (n := 24) C u (-1 / 4 : ℝ) = 47104 ∧
      distCount (n := 24) C u (0 : ℝ) = 93150

attribute [grind cases] EqCase24

end

end SpherePacking.Dim24.Uniqueness.BS81
