-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Discriminant
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.DualLatticeFinite
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Dual covolume and discriminant size

This file collects standard covolume identities for `ℤ`-lattices in a real inner product space.
In particular, for an integral lattice (`L ≤ L*`) the discriminant group `L*/L` has cardinality
`(covolume L)^2`.

The main computations are reduced to a coordinate space `ι → ℝ` via `ZLattice.covolume_comap`.
There we use the dot-product bilinear form and a determinant computation with a basis and its
bilinear dual basis.

## Main statements
* `relIndex_eq_card_discriminantGroup`
* `card_discriminantGroup_eq_covolume_sq`
-/


namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

noncomputable section

open scoped RealInnerProductSpace BigOperators
open MeasureTheory Matrix Module

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "E" => (ι → ℝ)

noncomputable def dotBilin : LinearMap.BilinForm ℝ E :=
  Matrix.toBilin' (1 : Matrix ι ι ℝ)

@[simp] lemma dotBilin_apply (x y : E) : dotBilin (ι := ι) x y = dotProduct x y := by
  simp [dotBilin, Matrix.toBilin'_apply']

lemma dotBilin_nondegenerate :
    (dotBilin (ι := ι) : LinearMap.BilinForm ℝ E).Nondegenerate := by
  refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    (B := (dotBilin (ι := ι) : LinearMap.BilinForm ℝ E)) ?_
  intro x hx
  ext i
  have h0 : dotProduct x (Pi.single i (1 : ℝ)) = 0 := by
    simpa [dotBilin_apply] using! hx (Pi.single i (1 : ℝ))
  simpa [dotProduct_single] using! h0

lemma covolume_dualSubmodule_eq_inv (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ZLattice.covolume
        ((dotBilin (ι := ι) : LinearMap.BilinForm ℝ E).dualSubmodule L)
        volume
      =
      (ZLattice.covolume L volume)⁻¹ := by
  let B : LinearMap.BilinForm ℝ E := dotBilin (ι := ι)
  let b : Basis ι ℤ L := IsZLattice.basis (L := L)
  let bR : Basis ι ℝ E := b.ofZLatticeBasis ℝ L
  have hB : B.Nondegenerate := dotBilin_nondegenerate (ι := ι)
  let wR : Basis ι ℝ E := B.dualBasis hB bR
  have hLspan : Submodule.span ℤ (Set.range bR) = L := by
    simpa using! (b.ofZLatticeBasis_span (K := ℝ) (L := L))
  have hLstar :
      B.dualSubmodule L = Submodule.span ℤ (Set.range wR) := by
    simpa [hLspan] using!
      (LinearMap.BilinForm.dualSubmodule_span_of_basis (R := ℤ) (B := B) hB bR)
  -- Work with the `ℤ`-span description of the dual submodule.
  let LstarSpan : Submodule ℤ E := Submodule.span ℤ (Set.range wR)
  have hLstar' : B.dualSubmodule L = LstarSpan := hLstar
  haveI : DiscreteTopology LstarSpan := inferInstance
  haveI : IsZLattice ℝ LstarSpan := inferInstance
  have hw_lin : LinearIndependent ℤ (fun i : ι => (wR i : E)) := by
    -- restrict scalars along `ℤ → ℝ`
    simpa using!
      (LinearIndependent.restrict_scalars' (R := ℤ) (K := ℝ) (M := E)
        (v := fun i : ι => (wR i : E)) wR.linearIndependent)
  let wZ : ι → LstarSpan := fun i =>
    ⟨(wR i : E), Submodule.subset_span (Set.mem_range_self i)⟩
  have hwZ_lin : LinearIndependent ℤ wZ := by
    simpa [LstarSpan, wZ] using! (linearIndependent_span (R := ℤ) hw_lin)
  have hwZ_span : Submodule.span ℤ (Set.range wZ) = ⊤ := by
    have hw_mem : ∀ i : ι, (wR i : E) ∈ LstarSpan := fun i =>
      Submodule.subset_span (Set.mem_range_self i)
    have hiff :=
      (Submodule.span_range_subtype_eq_top_iff (p := LstarSpan)
        (s := fun i : ι => (wR i : E)) hw_mem)
    simpa [LstarSpan, wZ] using! (hiff.2 rfl)
  have hwZ_span' : (⊤ : Submodule ℤ LstarSpan) ≤ Submodule.span ℤ (Set.range wZ) := by
    simp [hwZ_span]
  let bStarSpan : Basis ι ℤ LstarSpan := Basis.mk hwZ_lin hwZ_span'
  -- Covolume formulas as determinants.
  have hcovL : ZLattice.covolume L volume = |(Matrix.of ((↑) ∘ b)).det| := by
    simpa using! (ZLattice.covolume_eq_det (L := L) (b := b))
  have hcovLstar :
      ZLattice.covolume LstarSpan volume = |(Matrix.of ((↑) ∘ bStarSpan)).det| := by
    simpa using! (ZLattice.covolume_eq_det (L := LstarSpan) (b := bStarSpan))
  -- Matrices of the real bases.
  let W : Matrix ι ι ℝ := Matrix.of fun i => (bR i : E)
  let Wstar : Matrix ι ι ℝ := Matrix.of fun i => (wR i : E)
  have hmul : Wstar * W.transpose = (1 : Matrix ι ι ℝ) := by
    ext i j
    have hij : B (wR i) (bR j) = (if j = i then (1 : ℝ) else 0) := by
      simpa using! (LinearMap.BilinForm.apply_dualBasis_left (B := B) hB bR i j)
    have hij' : dotProduct (wR i : E) (bR j : E) = (if i = j then (1 : ℝ) else 0) := by
      simpa [B, dotBilin_apply, eq_comm] using! hij
    have hentry : (Wstar * W.transpose) i j = dotProduct (wR i : E) (bR j : E) := by
      simp [W, Wstar, Matrix.mul_apply, Matrix.of_apply, dotProduct]
    -- finish with `hij'`
    simpa [hentry, Matrix.one_apply] using! hij'
  have hdet_mul : Wstar.det * W.det = (1 : ℝ) := by
    have : (Wstar * W.transpose).det = (1 : Matrix ι ι ℝ).det := congrArg Matrix.det hmul
    simpa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, mul_assoc] using! this
  have hWdet : W.det ≠ (0 : ℝ) := by
    exact right_ne_zero_of_mul_eq_one hdet_mul
  have hdet : Wstar.det = (W.det)⁻¹ := by
    have := congrArg (fun t => t * (W.det)⁻¹) hdet_mul
    simpa [mul_assoc, hWdet] using! this
  have hW : (Matrix.of ((↑) ∘ b) : Matrix ι ι ℝ) = W := by
    ext i j
    simp [W, bR, Basis.ofZLatticeBasis_apply]
  have hWstar : (Matrix.of ((↑) ∘ bStarSpan) : Matrix ι ι ℝ) = Wstar := by
    ext i j
    simp [Wstar, bStarSpan, wZ]
  calc
    ZLattice.covolume (B.dualSubmodule L) volume
        = ZLattice.covolume LstarSpan volume := by simp [hLstar']
    _ = |(Matrix.of ((↑) ∘ bStarSpan) : Matrix ι ι ℝ).det| := hcovLstar
    _ = |Wstar.det| := by simp [hWstar]
    _ = |(W.det)⁻¹| := by simp [hdet]
    _ = |W.det|⁻¹ := by simp [abs_inv]
    _ = (ZLattice.covolume L volume)⁻¹ := by simp [hcovL, hW]

end Pi

private theorem covolume_dualLattice_eq_inv (L : Submodule ℤ ℝ²⁴)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ZLattice.covolume (DualLattice L) volume = (ZLattice.covolume L volume)⁻¹ := by
  haveI : DiscreteTopology (DualLattice L) := discreteTopology_dualLattice (L := L)
  haveI : IsZLattice ℝ (DualLattice L) := isZLattice_dualLattice (L := L)
  -- Reduce to the coordinate space `Fin 24 → ℝ` via `toLp`.
  let e : (Fin 24 → ℝ) ≃L[ℝ] ℝ²⁴ := (EuclideanSpace.equiv (Fin 24) ℝ).symm
  have he : MeasurePreserving e volume volume := by
    simpa [e, EuclideanSpace.equiv] using! (PiLp.volume_preserving_toLp (ι := Fin 24))
  let L0 : Submodule ℤ (Fin 24 → ℝ) := ZLattice.comap ℝ L e.toLinearMap
  have hcov_comap :
      ZLattice.covolume L0 volume = ZLattice.covolume L volume := by
    simpa [L0] using! (ZLattice.covolume_comap (L := L) (μ := volume) (ν := volume) he)
  have hdual :
      ZLattice.comap ℝ (DualLattice L) e.toLinearMap =
        (dotBilin (ι := Fin 24) : LinearMap.BilinForm ℝ (Fin 24 → ℝ)).dualSubmodule L0 := by
    ext x
    constructor
    · intro hx y hy
      have hy' : (e y : ℝ²⁴) ∈ L := by
        simpa [L0, ZLattice.comap] using! hy
      have hx' : (e x : ℝ²⁴) ∈ DualLattice L := hx
      have hInt : (⟪(e x : ℝ²⁴), (e y : ℝ²⁴)⟫ : ℝ) ∈ (1 : Submodule ℤ ℝ) := by
        simpa [DualLattice, innerₗ_apply_apply] using! hx' _ hy'
      have : dotProduct y x ∈ (1 : Submodule ℤ ℝ) := by
        simpa [e, EuclideanSpace.inner_toLp_toLp] using! hInt
      simpa [dotBilin_apply, dotProduct_comm] using! this
    · intro hx y hy
      rcases (e.surjective y) with ⟨y', rfl⟩
      have hy' : y' ∈ L0 := by
        simpa [L0, ZLattice.comap] using! hy
      have hInt : (dotBilin (ι := Fin 24) x y') ∈ (1 : Submodule ℤ ℝ) := hx y' hy'
      have hDot : dotProduct y' x ∈ (1 : Submodule ℤ ℝ) := by
        simpa [dotBilin_apply, dotProduct_comm] using! hInt
      assumption
  have hpi :
      ZLattice.covolume
          ((dotBilin (ι := Fin 24) : LinearMap.BilinForm ℝ (Fin 24 → ℝ)).dualSubmodule L0)
          volume
        =
        (ZLattice.covolume L0 volume)⁻¹ :=
    covolume_dualSubmodule_eq_inv (ι := Fin 24) (L := L0)
  have hcov_dual_comap :
      ZLattice.covolume (ZLattice.comap ℝ (DualLattice L) e.toLinearMap) volume =
        ZLattice.covolume (DualLattice L) volume := by
    simpa using! (ZLattice.covolume_comap (L := DualLattice L) (μ := volume) (ν := volume) he)
  simp_all

/-! ### Discriminant group size -/

/-- The index `[L* : L]` equals the cardinality of the discriminant group `L*/L`. -/
public theorem relIndex_eq_card_discriminantGroup (L : Submodule ℤ ℝ²⁴)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    L.toAddSubgroup.relIndex (DualLattice L).toAddSubgroup = Nat.card (DiscriminantGroup L) := by
  rfl

/-- For an integral lattice, the discriminant group has order `(covolume L)^2`. -/
public theorem card_discriminantGroup_eq_covolume_sq (L : Submodule ℤ ℝ²⁴)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (hLdual : L ≤ DualLattice L) :
    (Nat.card (DiscriminantGroup L) : ℝ) = (ZLattice.covolume L volume) ^ 2 := by
  haveI : DiscreteTopology (DualLattice L) := discreteTopology_dualLattice (L := L)
  haveI : IsZLattice ℝ (DualLattice L) := isZLattice_dualLattice (L := L)
  have hdual :
      ZLattice.covolume (DualLattice L) volume = (ZLattice.covolume L volume)⁻¹ :=
    covolume_dualLattice_eq_inv (L := L)
  calc
    (Nat.card (DiscriminantGroup L) : ℝ)
        = (L.toAddSubgroup.relIndex (DualLattice L).toAddSubgroup : ℝ) := by
            simp [relIndex_eq_card_discriminantGroup (L := L)]
    _ = ZLattice.covolume L volume / ZLattice.covolume (DualLattice L) volume := by
          exact Eq.symm (ZLattice.covolume_div_covolume_eq_relIndex' L (DualLattice L) hLdual)
    _ = (ZLattice.covolume L volume) ^ 2 := by
          simp [hdual, div_eq_mul_inv, pow_two]

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
