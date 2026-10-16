-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.DiscriminantPairing
import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.DualLatticeFinite
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice

/-!
# Nondegeneracy of the discriminant pairing

For a full `ℤ`-lattice `L` in `ℝ²⁴`, the double dual lattice coincides with `L`. As a
consequence, the discriminant pairing on `L*/L` is nondegenerate in the left variable.

## Main statements
* `Uniqueness.RigidityClassify.dualLattice_dualLattice_eq`
* `Uniqueness.RigidityClassify.discPair_eq_zero_forall_iff`
-/

namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

noncomputable section

open scoped RealInnerProductSpace
open Module

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)
local notation "𝕋" => AddCircle (1 : ℝ)

/-- For a full lattice `L`, the double dual lattice `L**` coincides with `L`. -/
public lemma dualLattice_dualLattice_eq (L : Submodule ℤ ℝ²⁴)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    DualLattice (DualLattice L) = L := by
  -- Choose a `ℤ`-basis of `L` and the associated `ℝ`-basis of `ℝ²⁴`.
  let bZ : Basis (Module.Free.ChooseBasisIndex ℤ L) ℤ L := Module.Free.chooseBasis ℤ L
  let bR : Basis (Module.Free.ChooseBasisIndex ℤ L) ℝ ℝ²⁴ := bZ.ofZLatticeBasis ℝ L
  have hLspan : Submodule.span ℤ (Set.range bR) = L := by
    simpa using! (bZ.ofZLatticeBasis_span (K := ℝ) (L := L))
  -- Apply `dualSubmodule_dualSubmodule_of_basis` to the `ZSpan` presentation.
  let B : LinearMap.BilinForm ℝ ℝ²⁴ := (innerₗ ℝ²⁴ : LinearMap.BilinForm ℝ ℝ²⁴)
  have hB : LinearMap.BilinForm.Nondegenerate B := by
    simpa [B] using! Uniqueness.RigidityClassify.bilinFormOfRealInner_nondegenerate ℝ²⁴
  have hSymm : B.IsSymm := by
    refine ⟨?_⟩
    intro x y
    simpa [B, innerₗ_apply_apply] using! (real_inner_comm x y).symm
  have hZspan :
      B.dualSubmodule (B.dualSubmodule (Submodule.span ℤ (Set.range bR))) =
        Submodule.span ℤ (Set.range bR) :=
    LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis B hB hSymm bR
  -- Rewrite back to `L`.
  -- `DualLattice L` is definitional `B.dualSubmodule L`.
  simpa [Uniqueness.RigidityClassify.DualLattice, hLspan, B] using! hZspan

/-- Nondegeneracy of the discriminant pairing in the left variable. -/
public theorem discPair_eq_zero_forall_iff (L : Submodule ℤ ℝ²⁴)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (a : DiscriminantGroup L) :
    (∀ b : DiscriminantGroup L, discPair (L := L) a b = 0) ↔
      a = (Zero.zero : DiscriminantGroup L) := by
  constructor
  · intro ha
    -- Reduce to representatives in the dual lattice.
    refine
      Quotient.inductionOn a
        (motive := fun a =>
          (∀ b, discPair (L := L) a b = 0) →
            a = (Zero.zero : DiscriminantGroup L))
        ?_ ha
    intro x hx
    -- `x : DualLattice L`, and `hx` says `⟪x,y⟫ ∈ ℤ` for all `y : DualLattice L`.
    have hxInt : (x : ℝ²⁴) ∈ DualLattice (DualLattice L) := by
      -- Unfold membership in the dual lattice of `DualLattice L`.
      intro y hy
      -- Use `hx` with `b = mk ⟨y,hy⟩`.
      let y' : DualLattice L := ⟨y, hy⟩
      have hxy0 : discPair (L := L) (Submodule.Quotient.mk x) (Submodule.Quotient.mk y') = 0 :=
        hx (Submodule.Quotient.mk y')
      -- Convert to a statement about the inner product modulo `ℤ`.
      have hcoe0 : (((⟪(x : ℝ²⁴), (y' : ℝ²⁴)⟫ : ℝ) : 𝕋)) = 0 := by
        simpa [discPair_mk_mk, dualLatticePair_apply, y'] using! hxy0
      -- `((t : ℝ) : AddCircle (1:ℝ)) = 0` iff `t` is an integer.
      rcases
          (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))
              (x := (⟪(x : ℝ²⁴), (y' : ℝ²⁴)⟫ : ℝ))).1 hcoe0 with
        ⟨n, hn⟩
      exact Submodule.mem_one.mpr ⟨n, by simpa using! hn⟩
    -- Now use `L** = L` to conclude `x ∈ L`, hence `mk x = 0` in the discriminant group.
    have hxL : (x : ℝ²⁴) ∈ L := by
      have : (x : ℝ²⁴) ∈ DualLattice (DualLattice L) := hxInt
      -- Rewrite the double dual.
      simpa [dualLattice_dualLattice_eq (L := L)] using! this
    -- Finish in the quotient.
    exact
      (Submodule.Quotient.mk_eq_zero (p := latticeInDual L) (x := x)).2
        (by simpa [mem_latticeInDual_iff] using! hxL)
  · intro ha
    subst ha
    intro b
    -- `discPair` is linear in the left argument.
    have h0 :
        discPair (L := L) (Zero.zero : DiscriminantGroup L) =
          (Zero.zero : DiscriminantGroup L →ₗ[ℤ] 𝕋) :=
      (discPair (L := L)).map_zero
    simpa using! congrArg (fun f => f b) h0

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
