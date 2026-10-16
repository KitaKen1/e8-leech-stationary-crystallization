import E8Leech.GeneralOrientationClassification

/-! # A contained full lattice with equal covolume is the entire lattice -/

noncomputable section
namespace E8Leech
open Set MeasureTheory

theorem lattice_eq_of_le_of_covolume_eq {d : ℕ}
    (L₁ L₂ : Submodule ℤ (Ambient d)) [DiscreteTopology L₁] [IsZLattice ℝ L₁]
    [DiscreteTopology L₂] [IsZLattice ℝ L₂] (hle : L₁ ≤ L₂)
    (hcov : ZLattice.covolume L₁ volume = ZLattice.covolume L₂ volume) : L₁ = L₂ := by
  have hi : L₁.toAddSubgroup.relIndex L₂.toAddSubgroup = 1 := by
    have hh := (ZLattice.covolume_div_covolume_eq_relIndex' L₁ L₂ hle).symm
    rw [hcov, div_self (ZLattice.covolume_ne_zero L₂ volume)] at hh
    exact_mod_cast hh
  exact le_antisymm hle (AddSubgroup.relIndex_eq_one.mp hi)

theorem lattice_image_eq_of_basis_mem {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (Ambient d))
    (Λ L : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    [DiscreteTopology L] [IsZLattice ℝ L]
    (hb : Λ = Submodule.span ℤ (Set.range b))
    (hcov : ZLattice.covolume Λ volume = ZLattice.covolume L volume)
    (Q : Ambient d ≃ₗᵢ[ℝ] Ambient d) (hQ : ∀ i, Q (b i) ∈ L) :
    Q '' (Λ : Set (Ambient d)) = (L : Set (Ambient d)) := by
  let e := Q.toContinuousLinearEquiv
  let L' := ZLattice.comap ℝ L e.toLinearMap
  have hle : Λ ≤ L' := by
    rw [hb]
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact hQ i
  have hpres : MeasurePreserving e volume volume := Q.measurePreserving
  have hc : ZLattice.covolume L' volume = ZLattice.covolume L volume :=
    ZLattice.covolume_comap L volume volume hpres
  have heq : Λ = L' := lattice_eq_of_le_of_covolume_eq Λ L' hle (hcov.trans hc.symm)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : y ∈ L' := heq ▸ hy
    exact this
  · intro hx
    refine ⟨Q.symm x, ?_, Q.apply_symm_apply x⟩
    rw [heq]
    change Q (Q.symm x) ∈ L
    rwa [Q.apply_symm_apply]

end E8Leech
