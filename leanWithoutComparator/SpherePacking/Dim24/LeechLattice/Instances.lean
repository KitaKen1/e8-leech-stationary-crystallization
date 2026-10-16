-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.LeechLattice.Defs
public import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse


/-!
# Leech lattice instances

This file constructs an explicit real basis `LeechLattice.leechRBasis` and derives topological and
`IsZLattice` structure instances for `LeechLattice`.

## Main definitions
* `LeechLattice.leechRBasis`

## Main instances
* `instDiscreteLeechLattice`
* `instIsZLatticeLeechLattice`
-/


local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

open Module

namespace LeechLattice

def leechMatrixRat : Matrix (Fin 24) (Fin 24) ℚ :=
  leechGeneratorMatrixInt.map (Int.castRingHom ℚ)

def leechMatrixReal : Matrix (Fin 24) (Fin 24) ℝ :=
  leechGeneratorMatrixInt.map (Int.castRingHom ℝ)

def leechInverseRat : Matrix (Fin 24) (Fin 24) ℚ :=
  ![
    ![(1 : ℚ) / 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 : ℚ) / 8, (1 : ℚ) / 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 : ℚ) / 8, 0, (1 : ℚ) / 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 : ℚ) / 8, 0, 0, (1 : ℚ) / 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 : ℚ) / 8, 0, 0, 0, (1 : ℚ) / 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 : ℚ) / 8, 0, 0, 0, 0, (1 : ℚ) / 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 : ℚ) / 8, 0, 0, 0, 0, 0, (1 : ℚ) / 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(5 : ℚ) / 8, (-1 : ℚ) / 4, (-1 : ℚ) / 4, (-1 : ℚ) / 4, (-1 : ℚ) / 4, (-1 : ℚ) / 4,
      (-1 : ℚ) / 4, (1 : ℚ) / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 : ℚ) / 8, 0, 0, 0, 0, 0, 0, 0, (1 : ℚ) / 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0],
    ![(-1 : ℚ) / 8, 0, 0, 0, 0, 0, 0, 0, 0, (1 : ℚ) / 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0],
    ![(-1 : ℚ) / 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1 : ℚ) / 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0],
    ![(5 : ℚ) / 8, (-1 : ℚ) / 4, (-1 : ℚ) / 4, (-1 : ℚ) / 4, 0, 0, 0, 0, (-1 : ℚ) / 4,
      (-1 : ℚ) / 4, (-1 : ℚ) / 4, (1 : ℚ) / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 : ℚ) / 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1 : ℚ) / 4, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0],
    ![(5 : ℚ) / 8, (-1 : ℚ) / 4, 0, 0, (-1 : ℚ) / 4, (-1 : ℚ) / 4, 0, 0, (-1 : ℚ) / 4,
      (-1 : ℚ) / 4, 0, 0, (-1 : ℚ) / 4, (1 : ℚ) / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(5 : ℚ) / 8, 0, (-1 : ℚ) / 4, 0, (-1 : ℚ) / 4, 0, (-1 : ℚ) / 4, 0, (-1 : ℚ) / 4, 0,
      (-1 : ℚ) / 4, 0, (-1 : ℚ) / 4, 0, (1 : ℚ) / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-7 : ℚ) / 8, (1 : ℚ) / 2, (1 : ℚ) / 2, (1 : ℚ) / 4, 0, (1 : ℚ) / 4, (1 : ℚ) / 4,
      (-1 : ℚ) / 2, 0, (1 : ℚ) / 4, (1 : ℚ) / 4, (-1 : ℚ) / 2, (-1 : ℚ) / 4, 0, 0,
      (1 : ℚ) / 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![(-1 : ℚ) / 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1 : ℚ) / 4, 0, 0, 0, 0,
      0, 0, 0],
    ![(-1 : ℚ) / 8, (1 : ℚ) / 4, 0, (1 : ℚ) / 4, 0, (1 : ℚ) / 4, (1 : ℚ) / 4, (-1 : ℚ) / 2,
      (-1 : ℚ) / 4, (-1 : ℚ) / 4, 0, 0, 0, 0, 0, 0, (-1 : ℚ) / 4, (1 : ℚ) / 2, 0, 0, 0, 0,
      0, 0],
    ![(5 : ℚ) / 8, 0, 0, (-1 : ℚ) / 4, (-1 : ℚ) / 4, (-1 : ℚ) / 4, 0, 0, (-1 : ℚ) / 4, 0,
      (-1 : ℚ) / 4, 0, 0, 0, 0, 0, (-1 : ℚ) / 4, 0, (1 : ℚ) / 2, 0, 0, 0, 0, 0],
    ![(-1 : ℚ) / 8, 0, (1 : ℚ) / 4, (1 : ℚ) / 4, (-1 : ℚ) / 4, 0, (-1 : ℚ) / 4, 0, 0,
      (1 : ℚ) / 4, (1 : ℚ) / 4, (-1 : ℚ) / 2, 0, 0, 0, 0, (-1 : ℚ) / 4, 0, 0, (1 : ℚ) / 2,
      0, 0, 0, 0],
    ![(7 : ℚ) / 8, (-1 : ℚ) / 4, (-1 : ℚ) / 4, (-1 : ℚ) / 4, (-1 : ℚ) / 4, 0, 0, 0,
      (-1 : ℚ) / 4, 0, 0, 0, (-1 : ℚ) / 4, 0, 0, 0, (-1 : ℚ) / 4, 0, 0, 0, (1 : ℚ) / 2, 0,
      0, 0],
    ![(-7 : ℚ) / 8, (1 : ℚ) / 4, (1 : ℚ) / 4, 0, (1 : ℚ) / 2, 0, (-1 : ℚ) / 4, (1 : ℚ) / 2,
      (1 : ℚ) / 2, (1 : ℚ) / 4, 0, 0, (1 : ℚ) / 4, (-1 : ℚ) / 2, 0, 0, (1 : ℚ) / 4,
      (-1 : ℚ) / 2, 0, 0, (-1 : ℚ) / 2, (1 : ℚ) / 2, 0, 0],
    ![(-13 : ℚ) / 8, (1 : ℚ) / 4, (1 : ℚ) / 2, (1 : ℚ) / 2, (3 : ℚ) / 4, (1 : ℚ) / 4,
      (1 : ℚ) / 4, 0, (1 : ℚ) / 2, 0, (1 : ℚ) / 4, 0, (1 : ℚ) / 4, 0, (-1 : ℚ) / 2, 0,
      (1 : ℚ) / 4, 0, (-1 : ℚ) / 2, 0, (-1 : ℚ) / 2, 0, (1 : ℚ) / 2, 0],
    ![(11 : ℚ) / 8, (-1 : ℚ) / 2, (-3 : ℚ) / 4, (-1 : ℚ) / 2, 0, (-1 : ℚ) / 4, 0, 0,
      (1 : ℚ) / 4, (-1 : ℚ) / 4, (-1 : ℚ) / 4, (1 : ℚ) / 2, (1 : ℚ) / 4, 0, 0, (-1 : ℚ) / 2,
      (1 : ℚ) / 4, 0, 0, (-1 : ℚ) / 2, (1 : ℚ) / 2, (-1 : ℚ) / 2, (-1 : ℚ) / 2, 1]
  ]

lemma leechInverse_mul_leechMatrix_rat : leechInverseRat * leechMatrixRat = 1 := by
  decide +kernel

lemma leechMatrix_mul_leechInverse_rat : leechMatrixRat * leechInverseRat = 1 := by
  decide +kernel

lemma leechMatrixReal_eq_cast :
    leechMatrixReal = leechMatrixRat.map (Rat.castHom ℝ) := by
  ext i j
  simp [leechMatrixReal, leechMatrixRat]

lemma leechInverse_mul_leechMatrix_real :
    (leechInverseRat.map (Rat.castHom ℝ)) * leechMatrixReal = 1 := by
  have h0 :
      (leechInverseRat * leechMatrixRat).map (Rat.castHom ℝ) = 1 := by
    simpa using!
      congrArg (fun A : Matrix (Fin 24) (Fin 24) ℚ => A.map (Rat.castHom ℝ))
        leechInverse_mul_leechMatrix_rat
  have hm :
      (leechInverseRat * leechMatrixRat).map (Rat.castHom ℝ) =
        (leechInverseRat.map (Rat.castHom ℝ)) * (leechMatrixRat.map (Rat.castHom ℝ)) := by
    simpa using!
      (Matrix.map_mul (L := leechInverseRat) (M := leechMatrixRat) (f := Rat.castHom ℝ))
  have h1 := h0
  rw [hm] at h1
  simpa [leechMatrixReal_eq_cast] using! h1

lemma leechMatrix_mul_leechInverse_real :
    leechMatrixReal * (leechInverseRat.map (Rat.castHom ℝ)) = 1 := by
  have h0 : (leechMatrixRat * leechInverseRat).map (Rat.castHom ℝ) = 1 := by
    simpa using!
      congrArg (fun A : Matrix (Fin 24) (Fin 24) ℚ => A.map (Rat.castHom ℝ))
        leechMatrix_mul_leechInverse_rat
  have hm :
      (leechMatrixRat * leechInverseRat).map (Rat.castHom ℝ) =
        (leechMatrixRat.map (Rat.castHom ℝ)) * (leechInverseRat.map (Rat.castHom ℝ)) := by
    simpa using! (Matrix.map_mul (L := leechMatrixRat) (M := leechInverseRat) (f := Rat.castHom ℝ))
  have h1 := h0
  rw [hm] at h1
  simpa [leechMatrixReal_eq_cast] using! h1

lemma linearIndependent_leechMatrixReal_rows :
    LinearIndependent ℝ leechMatrixReal.row := by
  haveI : Invertible leechMatrixReal :=
    { invOf := leechInverseRat.map (Rat.castHom ℝ)
      invOf_mul_self := leechInverse_mul_leechMatrix_real
      mul_invOf_self := leechMatrix_mul_leechInverse_real }
  simpa using! Matrix.linearIndependent_rows_of_invertible (K := ℝ) leechMatrixReal

lemma linearIndependent_leechGeneratorRowsUnscaled :
    LinearIndependent ℝ leechGeneratorRowsUnscaled := by
  have hrows : LinearIndependent ℝ leechMatrixReal.row := linearIndependent_leechMatrixReal_rows
  simpa [leechGeneratorRowsUnscaled, leechMatrixReal, Function.comp,
    WithLp.coe_symm_linearEquiv] using!
    (hrows.map' (WithLp.linearEquiv 2 ℝ (Fin 24 → ℝ)).symm.toLinearMap (by simp))

lemma linearIndependent_leechGeneratorRows :
    LinearIndependent ℝ leechGeneratorRows := by
  let u : ℝˣ :=
    Units.mk0 ((Real.sqrt 8)⁻¹ : ℝ)
      (inv_ne_zero (Real.sqrt_ne_zero'.2 (by positivity : (0 : ℝ) < (8 : ℝ))))
  have hUnits := (linearIndependent_leechGeneratorRowsUnscaled).units_smul (fun _ : Fin 24 => u)
  assumption

/-- An explicit `ℝ`-basis of `ℝ²⁴` given by the generator rows of the Leech lattice. -/
public noncomputable def leechRBasis : Basis (Fin 24) ℝ ℝ²⁴ :=
  basisOfLinearIndependentOfCardEqFinrank linearIndependent_leechGeneratorRows (by simp)

/-- The basis `leechRBasis` evaluates to the generator rows. -/
@[simp] public lemma leechRBasis_apply (i : Fin 24) :
    LeechLattice.leechRBasis i = leechGeneratorRows i := by
  simp [leechRBasis]

lemma range_leechRBasis : Set.range (LeechLattice.leechRBasis : Fin 24 → ℝ²⁴) =
    Set.range leechGeneratorRows := by
  ext x
  constructor <;> rintro ⟨i, rfl⟩ <;> exact ⟨i, by simp⟩

end LeechLattice

/-- The Leech lattice is discrete in the ambient Euclidean space. -/
public instance instDiscreteLeechLattice : DiscreteTopology LeechLattice := by
  let L : Submodule ℤ ℝ²⁴ := Submodule.span ℤ (Set.range LeechLattice.leechRBasis)
  have hEq : (LeechLattice : Submodule ℤ ℝ²⁴) = L := by
    simp [LeechLattice, L, LeechLattice.range_leechRBasis]
  have hmem : ∀ x : LeechLattice, (x : ℝ²⁴) ∈ L := by
    intro x
    simpa [hEq] using! x.property
  let f : LeechLattice → L := fun x => ⟨(x : ℝ²⁴), hmem x⟩
  have hf : Continuous f := by
    -- `f` is the inclusion map, hence continuous.
    simpa [f] using! (continuous_subtype_val.subtype_mk hmem)
  have hinj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (by simpa [f] using! congrArg Subtype.val hxy)
  exact DiscreteTopology.of_continuous_injective hf hinj

/-- The Leech lattice is a `ZLattice` over `ℝ`. -/
public instance instIsZLatticeLeechLattice : IsZLattice ℝ LeechLattice := by
  refine ⟨?_⟩
  -- The ℝ-span of the Leech lattice is all of `ℝ²⁴` because it contains an ℝ-basis.
  have hbSpan : Submodule.span ℝ (Set.range LeechLattice.leechRBasis) = ⊤ :=
    LeechLattice.leechRBasis.span_eq
  have hgenSubset : Set.range leechGeneratorRows ⊆ (LeechLattice : Set ℝ²⁴) := by
    rintro _ ⟨i, rfl⟩
    change leechGeneratorRows i ∈ Submodule.span ℤ (Set.range leechGeneratorRows)
    exact Submodule.subset_span ⟨i, rfl⟩
  have hbSubset : Set.range LeechLattice.leechRBasis ⊆ (LeechLattice : Set ℝ²⁴) := by
    simpa [LeechLattice.range_leechRBasis] using! hgenSubset
  refine eq_top_iff.mpr ?_
  simpa [hbSpan] using! (Submodule.span_mono (R := ℝ) hbSubset)

end SpherePacking.Dim24
