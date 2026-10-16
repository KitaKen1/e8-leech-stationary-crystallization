-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.IsZLatticeOfUnimodular
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Orthogonal decomposition for `spanR L`

For a `ℤ`-submodule `L ⊆ ℝ²⁴`, let `W = spanR L` and `K = Wᗮ`. We record the basic orthogonal
decomposition `ℝ²⁴ ≃ₗ W × K`.

## Main definitions
* `IsZLatticeOfUnimodular.W`
* `IsZLatticeOfUnimodular.K`
* `IsZLatticeOfUnimodular.decomp`

## Main statements
* `IsZLatticeOfUnimodular.isCompl_W_K`
-/


namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

noncomputable section

open scoped RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace IsZLatticeOfUnimodular

variable (L : Submodule ℤ ℝ²⁴)

/-- The real span `W = spanR L`, as an `ℝ`-subspace of `ℝ²⁴`. -/
@[expose] public abbrev W : Submodule ℝ ℝ²⁴ := spanR (L := L)
/-- The orthogonal complement `K = Wᗮ`. -/
@[expose] public abbrev K : Submodule ℝ ℝ²⁴ := (W (L := L))ᗮ

/-- Any element of `L` lies in the real span `W = spanR L`. -/
public lemma mem_W_of_mem_L {x : ℝ²⁴} (hx : x ∈ L) : x ∈ W (L := L) :=
  Submodule.subset_span hx

instance : (W (L := L)).HasOrthogonalProjection := by infer_instance

/-- The span `W` and its orthogonal complement `K` are complementary subspaces. -/
public lemma isCompl_W_K : IsCompl (W (L := L)) (K (L := L)) := by
  simpa [IsZLatticeOfUnimodular.K] using!
    (Submodule.isCompl_orthogonal_of_hasOrthogonalProjection (K := (W (L := L))))

/-- The (linear) orthogonal decomposition `ℝ²⁴ ≃ₗ W × K`. -/
@[expose]
public noncomputable def decomp : (W (L := L) × K (L := L)) ≃ₗ[ℝ] ℝ²⁴ :=
  Submodule.prodEquivOfIsCompl (W (L := L)) (K (L := L)) (isCompl_W_K (L := L))

@[simp] lemma decomp_apply (x : W (L := L) × (W (L := L))ᗮ) :
    decomp (L := L) x = x.1 + x.2 := by
  rfl

end IsZLatticeOfUnimodular

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
