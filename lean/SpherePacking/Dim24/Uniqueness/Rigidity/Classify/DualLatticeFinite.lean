-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Discriminant
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

/-!
# Finiteness of discriminant groups

This file records a basic lattice-theoretic fact used in the rigidity/classification step:
for a full lattice `L`, if `L` is integral (`L ≤ L*`) then the discriminant group `L*/L` is
finite.

Along the way we show that the real inner-product bilinear form is nondegenerate, and we use this
to transfer `DiscreteTopology`/`IsZLattice` structures to the dual lattice.

## Main statements
* `finite_discriminantGroup_of_le_dual`
-/


namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

noncomputable section

open scoped RealInnerProductSpace
open Module

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-! ### Dual lattice as a `ℤ`-lattice -/

/-- The bilinear form associated to the real inner product is nondegenerate. -/
public lemma bilinFormOfRealInner_nondegenerate (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] :
    LinearMap.BilinForm.Nondegenerate (innerₗ E : LinearMap.BilinForm ℝ E) := by
  dsimp [LinearMap.BilinForm.Nondegenerate, LinearMap.Nondegenerate, LinearMap.SeparatingLeft,
    LinearMap.SeparatingRight]
  constructor <;> intro x hx <;>
    (have hxx : ⟪x, x⟫ = (0 : ℝ) := hx x; exact inner_self_eq_zero.mp hxx)

/-- If `L` is a discrete `ℤ`-lattice, then the dual lattice `L*` carries the discrete topology. -/
public theorem discreteTopology_dualLattice (L : Submodule ℤ ℝ²⁴)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    DiscreteTopology (DualLattice L) := by
  -- Present the dual lattice as a `ZSpan` lattice and transfer discreteness.
  let bZ : Basis (Module.Free.ChooseBasisIndex ℤ L) ℤ L := Module.Free.chooseBasis ℤ L
  let bR : Basis (Module.Free.ChooseBasisIndex ℤ L) ℝ ℝ²⁴ := bZ.ofZLatticeBasis ℝ L
  let hB : LinearMap.BilinForm.Nondegenerate (innerₗ ℝ²⁴ : LinearMap.BilinForm ℝ ℝ²⁴) :=
    bilinFormOfRealInner_nondegenerate ℝ²⁴
  have hLspan : Submodule.span ℤ (Set.range bR) = L := by
    simpa using! (bZ.ofZLatticeBasis_span (K := ℝ) (L := L))
  have hLstar :
      DualLattice L =
        Submodule.span ℤ
          (Set.range
            (LinearMap.BilinForm.dualBasis
              (B := (innerₗ ℝ²⁴ : LinearMap.BilinForm ℝ ℝ²⁴)) hB bR)) := by
    -- Expand `DualLattice` and rewrite `L` as a `ZSpan` lattice.
    simpa [Uniqueness.RigidityClassify.DualLattice, hLspan] using!
      (LinearMap.BilinForm.dualSubmodule_span_of_basis (R := ℤ)
        (B := (innerₗ ℝ²⁴ : LinearMap.BilinForm ℝ ℝ²⁴)) hB bR)
  let Lspan : Submodule ℤ ℝ²⁴ :=
    Submodule.span ℤ
      (Set.range
        (LinearMap.BilinForm.dualBasis
          (B := (innerₗ ℝ²⁴ : LinearMap.BilinForm ℝ ℝ²⁴)) hB bR))
  haveI : DiscreteTopology Lspan := inferInstance
  -- Use the identity map `DualLattice L → Lspan` (well-defined by `hLstar`) to transfer
  -- discreteness.
  let f : DualLattice L → Lspan := fun x =>
    ⟨(x : ℝ²⁴), by simpa [Lspan, hLstar] using! x.property⟩
  have hf : Continuous f :=
    (continuous_subtype_val : Continuous fun x : DualLattice L => (x : ℝ²⁴)).subtype_mk (fun x => by
      simpa [Lspan, hLstar] using! x.property)
  have hinj : Function.Injective f := by
    intro x y hxy
    refine Subtype.ext ?_
    simpa [f] using! congrArg (fun z : Lspan => (z : ℝ²⁴)) hxy
  exact DiscreteTopology.of_continuous_injective (β := Lspan) hf hinj

/-- If `L` is a `ℤ`-lattice, then its dual lattice `L*` is again a `ℤ`-lattice. -/
public theorem isZLattice_dualLattice (L : Submodule ℤ ℝ²⁴)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    @IsZLattice ℝ _ (E := ℝ²⁴) _ _ (DualLattice L) (discreteTopology_dualLattice (L := L)) := by
  letI : DiscreteTopology (DualLattice L) := discreteTopology_dualLattice (L := L)
  -- Present the dual lattice as a `ZSpan` lattice and use the `IsZLattice` instance there.
  let bZ : Basis (Module.Free.ChooseBasisIndex ℤ L) ℤ L := Module.Free.chooseBasis ℤ L
  let bR : Basis (Module.Free.ChooseBasisIndex ℤ L) ℝ ℝ²⁴ := bZ.ofZLatticeBasis ℝ L
  let hB : LinearMap.BilinForm.Nondegenerate (innerₗ ℝ²⁴ : LinearMap.BilinForm ℝ ℝ²⁴) :=
    bilinFormOfRealInner_nondegenerate ℝ²⁴
  have hLspan : Submodule.span ℤ (Set.range bR) = L := by
    simpa using! (bZ.ofZLatticeBasis_span (K := ℝ) (L := L))
  have hLstar :
      DualLattice L =
        Submodule.span ℤ
          (Set.range
            (LinearMap.BilinForm.dualBasis
              (B := (innerₗ ℝ²⁴ : LinearMap.BilinForm ℝ ℝ²⁴)) hB bR)) := by
    simpa [Uniqueness.RigidityClassify.DualLattice, hLspan] using!
      (LinearMap.BilinForm.dualSubmodule_span_of_basis (R := ℤ)
        (B := (innerₗ ℝ²⁴ : LinearMap.BilinForm ℝ ℝ²⁴)) hB bR)
  let Lspan : Submodule ℤ ℝ²⁴ :=
    Submodule.span ℤ
      (Set.range
        (LinearMap.BilinForm.dualBasis
          (B := (innerₗ ℝ²⁴ : LinearMap.BilinForm ℝ ℝ²⁴)) hB bR))
  haveI : DiscreteTopology Lspan := inferInstance
  haveI : IsZLattice ℝ Lspan := inferInstance
  refine ⟨?_⟩
  -- Transport `span_top` along the definitional equality `hLstar`.
  have hspan : Submodule.span ℝ (Lspan : Set ℝ²⁴) = ⊤ := (IsZLattice.span_top (K := ℝ) (L := Lspan))
  dsimp [Lspan] at hspan
  rw [hLstar]
  exact hspan

/-- If `L` is integral (`L ≤ L*`), then the discriminant group `L*/L` is finite. -/
public theorem finite_discriminantGroup_of_le_dual (L : Submodule ℤ ℝ²⁴)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (hLdual :
      L ≤
        LinearMap.BilinForm.dualSubmodule (B := (innerₗ ℝ²⁴ : LinearMap.BilinForm ℝ ℝ²⁴)) L) :
    Finite (DiscriminantGroup L) := by
  -- Work inside the (real) dual lattice.
  let Lstar : Submodule ℤ ℝ²⁴ := DualLattice L
  haveI : DiscreteTopology Lstar := discreteTopology_dualLattice (L := L)
  haveI : IsZLattice ℝ Lstar := isZLattice_dualLattice (L := L)
  haveI : Module.Free ℤ Lstar := ZLattice.module_free ℝ Lstar
  haveI : Module.Finite ℤ Lstar := ZLattice.module_finite ℝ Lstar
  -- `latticeInDual L` has full rank in `Lstar` since it is linearly equivalent to `L`.
  have hRank : Module.finrank ℤ (latticeInDual L) = Module.finrank ℤ Lstar := by
    -- `latticeInDual` is (definitionally) `comap` along `Lstar.subtype`, hence equivalent to `L`
    -- under `hLdual`.
    have hEq : Module.finrank ℤ (latticeInDual L) = Module.finrank ℤ L := by
      simpa [Uniqueness.RigidityClassify.latticeInDual, Lstar] using!
        (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hLdual))
    -- both `L` and `L*` have rank `24`
    have hLrank : Module.finrank ℤ L = Module.finrank ℝ ℝ²⁴ := by
      simpa using! (ZLattice.rank (K := ℝ) (L := L))
    have hLstarRank : Module.finrank ℤ Lstar = Module.finrank ℝ ℝ²⁴ := by
      simpa using! (ZLattice.rank (K := ℝ) (L := Lstar))
    -- combine
    exact hEq.trans (hLrank.trans hLstarRank.symm)
  -- Conclude finiteness of the quotient `L*/(L*/∩L)`.
  -- This is `DiscriminantGroup L` by definition.
  simpa [Uniqueness.RigidityClassify.DiscriminantGroup, Lstar] using!
    (Submodule.finiteQuotientOfFreeOfRankEq (M := Lstar) (N := latticeInDual L) hRank)

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
