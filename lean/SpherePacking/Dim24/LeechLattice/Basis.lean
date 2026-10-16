-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.LeechLattice.Defs
public import SpherePacking.Dim24.LeechLattice.Instances
public import SpherePacking.Dim24.LeechLattice.Norm
public import SpherePacking.ForMathlib.VolumeOfBalls
import Mathlib.Algebra.Module.ZLattice.Covolume


/-!
# Leech lattice basis

A chosen `ℤ`-basis of the Leech lattice and its covolume normalization.

This isolates algebraic lattice data needed for packing density computations.

## Main definitions
* `Leech_ℤBasis`

## Main statements
* `leech_fundamentalDomain_volume`
* `leech_covolume`
-/

open scoped BigOperators
open MeasureTheory Metric
open MeasureTheory ZSpan
open Module

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

/-
`Matrix.det` is a reducible definition; for large index types (like `Fin 24`) unfolding it can lead
to costly unfolding during rewriting. We compute determinants through a wrapper, which stays opaque
unless explicitly unfolded.
-/
namespace Matrix

def myDetLeech {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]
    (M : Matrix n n R) : R :=
  M.det

lemma myDetLeech_smul {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]
    (c : R) (M : Matrix n n R) :
    myDetLeech (c • M) = c ^ (Fintype.card n) * myDetLeech M := by
  simp [myDetLeech]

end Matrix

/-- A fixed spanning family of `24` vectors in `LeechLattice` used to build a ℤ-basis. -/
noncomputable def leechZGenerators (i : Fin 24) : LeechLattice :=
  ⟨leechGeneratorRows i, by
    change leechGeneratorRows i ∈ Submodule.span ℤ (Set.range leechGeneratorRows)
    exact Submodule.subset_span ⟨i, rfl⟩⟩

lemma linearIndependent_leechZGenerators : LinearIndependent ℤ leechZGenerators := by
  have hlinR : LinearIndependent ℝ leechGeneratorRows := by
    simpa [show (LeechLattice.leechRBasis : Fin 24 → ℝ²⁴) = leechGeneratorRows from
      funext fun i => by simp] using!
      (LeechLattice.leechRBasis.linearIndependent)
  have hlinZ : LinearIndependent ℤ leechGeneratorRows :=
    (hlinR.restrict_scalars' (R := ℤ))
  refine LinearIndependent.of_comp (f := (LeechLattice.subtype : LeechLattice →ₗ[ℤ] ℝ²⁴)) ?_
  simpa [leechZGenerators, Function.comp] using! hlinZ

lemma top_le_span_leechZGenerators :
    (⊤ : Submodule ℤ LeechLattice) ≤ Submodule.span ℤ (Set.range leechZGenerators) := by
  intro x _
  have hx : (x : ℝ²⁴) ∈ Submodule.span ℤ (Set.range leechGeneratorRows) := by
    change (x : ℝ²⁴) ∈ LeechLattice
    exact x.property
  rcases
      (Submodule.mem_span_range_iff_exists_fun
          (R := ℤ) (v := leechGeneratorRows) (x := (x : ℝ²⁴))).1 hx with
    ⟨c, hc⟩
  refine (Submodule.mem_span_range_iff_exists_fun (R := ℤ) (v := leechZGenerators) (x := x)).2 ?_
  refine ⟨c, ?_⟩
  apply Subtype.ext
  simpa [leechZGenerators, Function.comp] using! hc

/-- A fixed `ℤ`-basis of `LeechLattice` obtained from the explicit generator matrix. -/
public noncomputable def Leech_ℤBasis : Basis (Fin 24) ℤ LeechLattice :=
  Basis.mk linearIndependent_leechZGenerators top_le_span_leechZGenerators

private lemma Leech_ℤBasis_apply (i : Fin 24) : Leech_ℤBasis i = leechZGenerators i := by
  simp [Leech_ℤBasis]

/-- A crude uniform bound on the norm of the basis vectors (used to satisfy the hypotheses of
`PeriodicSpherePacking.density_eq`).

This constant is not meant to be sharp; any explicit bound works. -/
theorem leech_basis_apply_norm :
    ∃ L : ℝ, 0 < L ∧ ∀ i : Fin 24, ‖(Leech_ℤBasis i : ℝ²⁴)‖ ≤ L := by
  -- A simple explicit bound: `L := (∑ i, ‖(Leech_ℤBasis i : ℝ²⁴)‖) + 1`.
  let s : Finset (Fin 24) := Finset.univ
  let L : ℝ := (s.sum fun i => ‖(Leech_ℤBasis i : ℝ²⁴)‖) + 1
  refine ⟨L, ?_, ?_⟩
  · have : 0 ≤ s.sum (fun i => ‖(Leech_ℤBasis i : ℝ²⁴)‖) :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  · intro i
    have hle : ‖(Leech_ℤBasis i : ℝ²⁴)‖ ≤ s.sum (fun j => ‖(Leech_ℤBasis j : ℝ²⁴)‖) := by
      simpa using!
        (Finset.single_le_sum
          (s := s)
          (f := fun j : Fin 24 => ‖(Leech_ℤBasis j : ℝ²⁴)‖)
          (fun _ _ => norm_nonneg _)
          (by simp [s]))
    linarith [hle]

/-
Auxiliary facts for unimodularity (`leech_fundamentalDomain_volume`).

These are kept `private` to avoid polluting the public API.
-/
@[simp]
lemma leechGeneratorMatrixInt_aboveDiag :
    ∀ i j : Fin 24, i < j → leechGeneratorMatrixInt i j = 0 := by
  intro i
  fin_cases i <;> decide

lemma leechGeneratorMatrixInt_diag_prod :
    (∏ i : Fin 24, leechGeneratorMatrixInt i i) = (2 : ℤ) ^ (36 : ℕ) := by
  decide

noncomputable def LeechBasisFun : Basis (Fin 24) ℝ (Fin 24 → ℝ) :=
  (Leech_ℤBasis.ofZLatticeBasis ℝ LeechLattice).map (WithLp.linearEquiv 2 ℝ (Fin 24 → ℝ))

lemma leech_volume_pres (s : Set ℝ²⁴) :
    MeasureTheory.volume ((WithLp.equiv 2 (Fin 24 → ℝ)).symm ⁻¹' s) =
      MeasureTheory.volume s := by
  have h :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (ι := Fin 24)).symm
  simpa using! h.measure_preimage_equiv s

open MeasureTheory ZSpan in
lemma leech_same_domain :
    (WithLp.linearEquiv 2 ℝ (Fin 24 → ℝ)).symm ⁻¹'
        fundamentalDomain (Leech_ℤBasis.ofZLatticeBasis ℝ LeechLattice) =
      fundamentalDomain LeechBasisFun := by
  rw [← LinearEquiv.image_eq_preimage_symm, ZSpan.map_fundamentalDomain]
  simp [LeechBasisFun]

lemma leechBasisFun_matrixOf :
    (Matrix.of LeechBasisFun) =
      ((Real.sqrt 8)⁻¹ : ℝ) • (leechGeneratorMatrixInt.map fun z : ℤ => (z : ℝ)) := by
  ext i j
  simp [LeechBasisFun, Matrix.of_apply, Matrix.map_apply, smul_eq_mul, Basis.map_apply,
    Module.Basis.ofZLatticeBasis_apply, Leech_ℤBasis_apply, leechZGenerators, leechGeneratorRows,
    leechGeneratorRowsUnscaled]

lemma leechGeneratorMatrixInt_detR :
    ((leechGeneratorMatrixInt.map fun z : ℤ => (z : ℝ)).det) = (2 : ℝ) ^ (36 : ℕ) := by
  let Mℝ : Matrix (Fin 24) (Fin 24) ℝ := leechGeneratorMatrixInt.map fun z : ℤ => (z : ℝ)
  have htriR : Mℝ.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij0 : leechGeneratorMatrixInt i j = 0 :=
      leechGeneratorMatrixInt_aboveDiag i j (by simpa using! hij)
    simp [Mℝ, Matrix.map_apply, hij0]
  have hdet_diagR : Mℝ.det = ∏ i : Fin 24, Mℝ i i := by
    simpa using! (Matrix.det_of_lowerTriangular (M := Mℝ) htriR)
  have hprodR : (∏ i : Fin 24, Mℝ i i) = (2 : ℝ) ^ (36 : ℕ) := by
    have : (∏ i : Fin 24, (leechGeneratorMatrixInt i i : ℝ)) = (2 : ℝ) ^ (36 : ℕ) := by
      exact_mod_cast leechGeneratorMatrixInt_diag_prod
    simpa [Mℝ, Matrix.map_apply] using! this
  simpa [Mℝ] using! hdet_diagR.trans hprodR

lemma leechBasisFun_myDetLeech :
    (Matrix.myDetLeech (Matrix.of LeechBasisFun)) = 1 := by
  have hsqrt_pow : (Real.sqrt 8 : ℝ) ^ (24 : ℕ) = (2 : ℝ) ^ (36 : ℕ) := by
    grind only [usr Real.sq_sqrt', = max_def]
  have htwo_pow_ne : ((2 : ℝ) ^ (36 : ℕ)) ≠ 0 :=
    pow_ne_zero 36 ( two_ne_zero)
  have hdet' :
      Matrix.myDetLeech (leechGeneratorMatrixInt.map fun z : ℤ => (z : ℝ)) =
        (2 : ℝ) ^ (36 : ℕ) := by
    simp [Matrix.myDetLeech, leechGeneratorMatrixInt_detR]
  rw [leechBasisFun_matrixOf]
  rw [Matrix.myDetLeech_smul]
  simp only [Fintype.card_fin, inv_pow]
  rw [hsqrt_pow, hdet']
  exact inv_mul_cancel₀ htwo_pow_ne

open MeasureTheory ZSpan in
lemma ZSpan.volume_fundamentalDomain_myDetLeech {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ (ι → ℝ)) :
    volume (fundamentalDomain b) = ENNReal.ofReal |Matrix.myDetLeech (Matrix.of b)| :=
  volume_fundamentalDomain b

lemma leechBasisFun_volume : volume (fundamentalDomain LeechBasisFun) = 1 := by
  simpa [leechBasisFun_myDetLeech] using!
    (ZSpan.volume_fundamentalDomain_myDetLeech (b := LeechBasisFun))

/-- Unimodularity normalization: the fundamental domain of the Leech lattice has volume `1`. -/
public theorem leech_fundamentalDomain_volume :
    volume (fundamentalDomain (Leech_ℤBasis.ofZLatticeBasis ℝ LeechLattice)) = 1 := by
  rw [← leech_volume_pres (fundamentalDomain (Leech_ℤBasis.ofZLatticeBasis ℝ LeechLattice))]
  change
    volume
        ((WithLp.linearEquiv 2 ℝ (Fin 24 → ℝ)).symm ⁻¹'
          fundamentalDomain (Leech_ℤBasis.ofZLatticeBasis ℝ LeechLattice)) = 1
  erw [leech_same_domain]
  exact leechBasisFun_volume

/-- Unimodularity normalization for the Leech lattice: the covolume is `1`. -/
public theorem leech_covolume : ZLattice.covolume LeechLattice volume = 1 := by
  -- Compute `covolume` using the fundamental domain coming from the fixed ℤ-basis.
  have hCov :
      ZLattice.covolume LeechLattice volume =
        volume.real (ZSpan.fundamentalDomain (Leech_ℤBasis.ofZLatticeBasis ℝ LeechLattice)) :=
    ZLattice.covolume_eq_measure_fundamentalDomain (L := LeechLattice) (μ := volume)
      (ZLattice.isAddFundamentalDomain (L := LeechLattice) Leech_ℤBasis volume)
  -- Convert `leech_fundamentalDomain_volume` (an `ENNReal` statement) to a real statement.
  simpa [hCov, Measure.real] using! congrArg ENNReal.toReal leech_fundamentalDomain_volume

end SpherePacking.Dim24
