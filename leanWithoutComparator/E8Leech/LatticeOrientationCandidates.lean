import E8Leech.AnchoredOrientationKernel
import E8Leech.LatticeCovolumeInclusion

/-! # Exact lattices are recovered by every compatible basis orientation -/

noncomputable section
namespace E8Leech
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

variable {d : ℕ} (b : Module.Basis (Fin d) ℝ (Ambient d))
variable (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
variable (hb : Λ = Submodule.span ℤ (Set.range b))

include hb in
omit [DiscreteTopology Λ] [IsZLattice ℝ Λ] in
theorem basis_mem_reference_lattice (i : Fin d) : b i ∈ Λ := by
  rw [hb]
  exact Submodule.subset_span (Set.mem_range_self i)

omit [DiscreteTopology Λ] [IsZLattice ℝ Λ] in
theorem isometry_lattice_recenter (Φ : Ambient d ≃ᵢ Ambient d)
    {x : Ambient d} (hx : x ∈ Φ '' (Λ : Set (Ambient d))) :
    Φ '' (Λ : Set (Ambient d)) =
      (fun v => x + Φ.toRealLinearIsometryEquiv v) '' (Λ : Set (Ambient d)) := by
  obtain ⟨z₀, hz₀, rfl⟩ := hx
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z - z₀, Λ.sub_mem hz hz₀, ?_⟩
    change Φ z₀ + Φ.toRealLinearIsometryEquiv (z - z₀) = Φ z
    rw [add_comm]
    exact isometry_recenter_apply Φ z z₀
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z + z₀, Λ.add_mem hz hz₀, ?_⟩
    have he := isometry_recenter_apply Φ (z + z₀) z₀
    rw [add_sub_cancel_right] at he
    exact he.symm.trans (add_comm _ _)

include hb in
omit [DiscreteTopology Λ] [IsZLattice ℝ Λ] in
theorem orientationCandidates_nonempty_of_exact (c : Configuration (Ambient d))
    (Φ : Ambient d ≃ᵢ Ambient d) (hc : c.support = Φ '' (Λ : Set (Ambient d)))
    {x : Ambient d} (hx : x ∈ c.support) : (orientationCandidatePoints b c x).Nonempty := by
  refine ⟨⟨Φ.toRealLinearIsometryEquiv⟩, (mem_orientationCandidatePoints b c x _).mpr ?_⟩
  intro i
  rw [hc, isometry_lattice_recenter Λ Φ (hc ▸ hx)]
  exact ⟨b i, basis_mem_reference_lattice b Λ hb i, rfl⟩

include hb in
theorem orientationCandidate_recovers_lattice (c : Configuration (Ambient d))
    (Φ : Ambient d ≃ᵢ Ambient d) (hc : c.support = Φ '' (Λ : Set (Ambient d)))
    {x : Ambient d} (hx : x ∈ c.support) (Q : LatticeOrientation d)
    (hQ : BasisOrientationCandidate b c x Q) :
    c.support = (fun v => x + Q.isometry v) '' (Λ : Set (Ambient d)) := by
  have hrec := isometry_lattice_recenter Λ Φ (hc ▸ hx)
  have hmem (i : Fin d) : Φ.toRealLinearIsometryEquiv.symm (Q.isometry (b i)) ∈ Λ := by
    have hi : x + Q.isometry (b i) ∈ Φ '' (Λ : Set (Ambient d)) := hc ▸ hQ i
    rw [hrec] at hi
    obtain ⟨z, hz, he⟩ := hi
    have he' : Φ.toRealLinearIsometryEquiv z = Q.isometry (b i) := add_left_cancel he
    rw [← he', LinearIsometryEquiv.symm_apply_apply]
    exact hz
  let T := Q.isometry.trans Φ.toRealLinearIsometryEquiv.symm
  have hT : T '' (Λ : Set (Ambient d)) = (Λ : Set (Ambient d)) :=
    lattice_image_eq_of_basis_mem b Λ Λ hb rfl T hmem
  have he : Q.isometry '' (Λ : Set (Ambient d)) =
      Φ.toRealLinearIsometryEquiv '' (Λ : Set (Ambient d)) := by
    calc
      _ = Φ.toRealLinearIsometryEquiv '' (T '' (Λ : Set (Ambient d))) := by
        rw [Set.image_image]
        congr 1
        funext v
        exact (Φ.toRealLinearIsometryEquiv.apply_symm_apply (Q.isometry v)).symm
      _ = _ := by rw [hT]
  rw [hc, hrec]
  calc
    _ = (fun v => x + v) '' (Φ.toRealLinearIsometryEquiv '' (Λ : Set (Ambient d))) := by
      rw [Set.image_image]
    _ = (fun v => x + v) '' (Q.isometry '' (Λ : Set (Ambient d))) := by rw [he]
    _ = _ := by rw [Set.image_image]


include hb in
theorem orientationCandidate_iff_recovers_lattice (c : Configuration (Ambient d))
    (Φ : Ambient d ≃ᵢ Ambient d) (hc : c.support = Φ '' (Λ : Set (Ambient d)))
    {x : Ambient d} (hx : x ∈ c.support) (Q : LatticeOrientation d) :
    BasisOrientationCandidate b c x Q ↔
      c.support = (fun v => x + Q.isometry v) '' (Λ : Set (Ambient d)) := by
  refine ⟨orientationCandidate_recovers_lattice b Λ hb c Φ hc hx Q, ?_⟩
  intro h i
  rw [h]
  exact ⟨b i, basis_mem_reference_lattice b Λ hb i, rfl⟩

include hb in
theorem orientationCandidate_at_other_anchor (c : Configuration (Ambient d))
    (Φ : Ambient d ≃ᵢ Ambient d) (hc : c.support = Φ '' (Λ : Set (Ambient d)))
    {x y : Ambient d} (hx : x ∈ c.support) (hy : y ∈ c.support) (Q : LatticeOrientation d)
    (hQ : BasisOrientationCandidate b c x Q) : BasisOrientationCandidate b c y Q := by
  have he := orientationCandidate_recovers_lattice b Λ hb c Φ hc hx Q hQ
  obtain ⟨z, hz, rfl⟩ := he ▸ hy
  intro i
  rw [he]
  refine ⟨z + b i, Λ.add_mem hz (basis_mem_reference_lattice b Λ hb i), ?_⟩
  simp only [map_add, add_assoc]

include hb in
theorem orientationCandidatePoints_anchor_independent (c : Configuration (Ambient d))
    (Φ : Ambient d ≃ᵢ Ambient d) (hc : c.support = Φ '' (Λ : Set (Ambient d)))
    {x y : Ambient d} (hx : x ∈ c.support) (hy : y ∈ c.support) :
    orientationCandidatePoints b c x = orientationCandidatePoints b c y := by
  ext Q
  simp only [mem_orientationCandidatePoints]
  exact ⟨orientationCandidate_at_other_anchor b Λ hb c Φ hc hx hy Q,
    orientationCandidate_at_other_anchor b Λ hb c Φ hc hy hx Q⟩

include hb in
theorem anchoredOrientationKernel_anchor_independent (c : Configuration (Ambient d))
    (Φ : Ambient d ≃ᵢ Ambient d) (hc : c.support = Φ '' (Λ : Set (Ambient d)))
    {x y : Ambient d} (hx : x ∈ c.support) (hy : y ∈ c.support) :
    anchoredOrientationKernel b (c, x) = anchoredOrientationKernel b (c, y) := by
  rw [anchoredOrientationKernel_eq_sum, anchoredOrientationKernel_eq_sum,
    orientationCandidatePoints_anchor_independent b Λ hb c Φ hc hx hy]

include hb in
omit [DiscreteTopology Λ] [IsZLattice ℝ Λ] in
theorem anchoredOrientationKernel_univ_ne_zero_of_exact (c : Configuration (Ambient d))
    (Φ : Ambient d ≃ᵢ Ambient d) (hc : c.support = Φ '' (Λ : Set (Ambient d)))
    {x : Ambient d} (hx : x ∈ c.support) : anchoredOrientationKernel b (c, x) univ ≠ 0 := by
  obtain ⟨Q, hQ⟩ := orientationCandidates_nonempty_of_exact b Λ hb c Φ hc hx
  have ha : anchoredOrientationKernel b (c, x) {Q} = 1 := by
    rw [anchoredOrientationKernel_singleton,
      if_pos ((mem_orientationCandidatePoints b c x Q).mp hQ)]
  exact ne_of_gt (lt_of_lt_of_le (ha ▸ zero_lt_one)
    (measure_mono (Set.subset_univ {Q})))

theorem orientationCandidatePoints_translate (a : Ambient d)
    (c : Configuration (Ambient d)) (x : Ambient d) :
    orientationCandidatePoints b (translate a c) (a + x) = orientationCandidatePoints b c x := by
  ext Q
  simp only [mem_orientationCandidatePoints, BasisOrientationCandidate]
  apply forall_congr'
  intro i
  change (a + x + Q.isometry (b i) ∈ (fun y => a + y) '' c.support) ↔ _
  constructor
  · rintro ⟨y, hy, he⟩
    have he' : y = x + Q.isometry (b i) := add_left_cancel (he.trans (add_assoc _ _ _))
    exact he' ▸ hy
  · intro hi
    exact ⟨x + Q.isometry (b i), hi, (add_assoc _ _ _).symm⟩

theorem anchoredOrientationKernel_translate (a : Ambient d)
    (c : Configuration (Ambient d)) (x : Ambient d) :
    anchoredOrientationKernel b (translate a c, a + x) = anchoredOrientationKernel b (c, x) := by
  rw [anchoredOrientationKernel_eq_sum, anchoredOrientationKernel_eq_sum,
    orientationCandidatePoints_translate]

theorem e8_orientationCandidate_recovers_lattice (c : Configuration (Ambient 8))
    (Φ : Ambient 8 ≃ᵢ Ambient 8) (hc : c.support = Φ '' e8Set)
    {x : Ambient 8} (hx : x ∈ c.support) (Q : LatticeOrientation 8)
    (hQ : BasisOrientationCandidate e8EuclideanBasis c x Q) :
    c.support = (fun v => x + Q.isometry v) '' e8Set := by
  simpa only [coe_e8Lattice] using orientationCandidate_recovers_lattice e8EuclideanBasis
    e8Lattice rfl c Φ (by simpa only [coe_e8Lattice] using hc) hx Q hQ

theorem leech_orientationCandidate_recovers_lattice (c : Configuration (Ambient 24))
    (Φ : Ambient 24 ≃ᵢ Ambient 24) (hc : c.support = Φ '' leechSet)
    {x : Ambient 24} (hx : x ∈ c.support) (Q : LatticeOrientation 24)
    (hQ : BasisOrientationCandidate leechEuclideanBasis c x Q) :
    c.support = (fun v => x + Q.isometry v) '' leechSet := by
  simpa only [coe_leechLattice] using orientationCandidate_recovers_lattice leechEuclideanBasis
    leechLattice leechLattice_eq_span c Φ (by simpa only [coe_leechLattice] using hc) hx Q hQ

end E8Leech
