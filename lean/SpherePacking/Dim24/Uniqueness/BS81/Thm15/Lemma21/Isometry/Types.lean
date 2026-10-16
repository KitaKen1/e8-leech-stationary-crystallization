module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Patterns
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma17.Shell4
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20.Defs

/-!
# Type I/II/III subsets of the shell

In the BS81 Lemma 21 counting argument, shell vectors are split into three families (`TypeI`,
`TypeII`, `TypeIII`) according to which integer coordinate pattern they realize.

This file isolates these definitions so later modules can depend on them without importing the
full counting development.

## Main definitions
* `CodeIsGolayCountFinal.TypeI`
* `CodeIsGolayCountFinal.TypeII`
* `CodeIsGolayCountFinal.TypeIII`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps

noncomputable section

open Set

open Uniqueness.BS81
open Uniqueness.BS81.Thm15.Lemma21

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace CodeIsGolayCountFinal

local notation "shell4" => Uniqueness.BS81.latticeShell4

/-!
## Pattern subclasses of the shell
-/

/-- Type I vectors: shell vectors whose integer coordinates satisfy `isPattern2`. -/
@[expose] public def TypeI (C : Set ℝ²⁴)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) : Set ℝ²⁴ :=
  {u : ℝ²⁴ | u ∈ shell4 C ∧ ∃ z : Fin 24 → ℤ,
      (∀ i : Fin 24, scaledCoord hDn.e i u = (z i : ℝ)) ∧ isPattern2 z}

/-- Type II vectors: shell vectors whose integer coordinates satisfy `isPattern1`. -/
@[expose] public def TypeII (C : Set ℝ²⁴)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) : Set ℝ²⁴ :=
  {u : ℝ²⁴ | u ∈ shell4 C ∧ ∃ z : Fin 24 → ℤ,
      (∀ i : Fin 24, scaledCoord hDn.e i u = (z i : ℝ)) ∧ isPattern1 z}

/-- Type III vectors: shell vectors whose integer coordinates satisfy `isPattern3`. -/
@[expose] public def TypeIII (C : Set ℝ²⁴)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) : Set ℝ²⁴ :=
  {u : ℝ²⁴ | u ∈ shell4 C ∧ ∃ z : Fin 24 → ℤ,
      (∀ i : Fin 24, scaledCoord hDn.e i u = (z i : ℝ)) ∧ isPattern3 z}

end CodeIsGolayCountFinal

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
