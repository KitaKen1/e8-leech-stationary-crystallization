import E8Leech.LeechLatticeCount
import E8Leech.LeechBasis
import E8Leech.LeechDuality
import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.CE.Rigidity
import Mathlib.Analysis.Normed.Affine.MazurUlam

/-!
# The characterization of the Leech lattice

`LeechCharacterization` says that an even lattice of covolume one in `ℝ²⁴` without vectors of
squared norm two is an isometric copy of the Leech lattice. It is proved here from the uniqueness
part of the sphere packing theorem in dimension 24 (Cohn, Kumar, Miller, Radchenko, Viazovska), as
formalized in Sphere-Packing-Lean and ported to this project
(`SpherePacking.Dim24.Uniqueness.RigidityClassify.CE.leech_rigidity_normalized`): a periodic
packing with separation two and the density of the Leech packing is isometric to the Leech packing.

Let `L` be an even lattice of covolume one without vectors of squared norm two. Distinct points of
`L` are at distance at least two, so `L` is the set of centres of a periodic packing with
separation two (`evenRootlessPacking`). It has one centre in each period and covolume one, so its
density is the volume of the unit ball, the density of the Leech packing
(`evenRootlessPacking_density`). Hence `L` is the image of the Leech lattice of Sphere-Packing-Lean
under an isometry of `ℝ²⁴` (`exists_isometryEquiv_image_eq_splLeechLattice`).

The Leech lattice of this project (`leechLattice`, defined from the Golay code) has the same three
properties, so the same statement applies to it, and the two models of the Leech lattice are
compared without their coordinates. An isometry carrying one additive subgroup onto another becomes
linear after a translation inside the target subgroup (Mazur–Ulam;
`exists_linearIsometryEquiv_image_eq_of_isometryEquiv`).
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric

/-- In an even lattice without vectors of squared norm two, nonzero vectors have norm at least
two. -/
theorem two_le_norm_of_even_of_rootless {L : Submodule ℤ (Ambient 24)}
    (heven : ∀ x ∈ L, ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k) (hroot : ∀ x ∈ L, x ≠ 0 → ‖x‖ ^ 2 ≠ 2)
    {x : Ambient 24} (hx : x ∈ L) (hne : x ≠ 0) : 2 ≤ ‖x‖ := by
  obtain ⟨k, hk⟩ := heven x hx
  have hpos : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
  have hk0 : (0 : ℝ) < k := by
    rw [hk] at hpos
    linarith
  have hk0' : (0 : ℤ) < k := by exact_mod_cast hk0
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hroot x hx hne (by rw [hk]; norm_num)
  have hk2 : (2 : ℤ) ≤ k := by omega
  have hk3 : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have h4 : 4 ≤ ‖x‖ ^ 2 := by
    rw [hk]
    linarith
  nlinarith [norm_nonneg x]

/-- The packing by unit balls centred at the points of an even lattice without vectors of squared
norm two. -/
def evenRootlessPacking (L : Submodule ℤ (Ambient 24)) [DiscreteTopology L] [IsZLattice ℝ L]
    (heven : ∀ x ∈ L, ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k) (hroot : ∀ x ∈ L, x ≠ 0 → ‖x‖ ^ 2 ≠ 2) :
    PeriodicSpherePacking 24 where
  centers := L
  separation := 2
  centers_dist := by
    intro x y hxy
    have hne : (x : Ambient 24) - y ≠ 0 := fun h => hxy (Subtype.ext (sub_eq_zero.mp h))
    have h := two_le_norm_of_even_of_rootless heven hroot (L.sub_mem x.2 y.2) hne
    simpa [Subtype.dist_eq, dist_eq_norm] using h
  lattice := L
  lattice_action := fun _ _ hx hy => L.add_mem hx hy

/-- The packing of an even lattice of covolume one without vectors of squared norm two has the
density of the Leech packing. -/
theorem evenRootlessPacking_density (L : Submodule ℤ (Ambient 24)) [DiscreteTopology L]
    [IsZLattice ℝ L] (heven : ∀ x ∈ L, ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k)
    (hroot : ∀ x ∈ L, x ≠ 0 → ‖x‖ ^ 2 ≠ 2) (hcov : ZLattice.covolume L volume = 1) :
    (evenRootlessPacking L heven hroot).density = SpherePacking.Dim24.LeechPacking.density := by
  have hnum : (evenRootlessPacking L heven hroot).numReps = 1 :=
    PeriodicSpherePacking.numReps_eq_one (S := evenRootlessPacking L heven hroot) rfl
  have hcov' : ZLattice.covolume (evenRootlessPacking L heven hroot).lattice volume = 1 := hcov
  have hsep : (evenRootlessPacking L heven hroot).separation / 2 = 1 := by
    change (2 : ℝ) / 2 = 1
    norm_num
  have hball : (evenRootlessPacking L heven hroot).density =
      volume (ball (0 : EuclideanSpace ℝ (Fin 24)) 1) := by
    rw [PeriodicSpherePacking.density_eq' _ (by norm_num), hnum, hcov', hsep]
    simp
  have hvol : volume (ball (0 : EuclideanSpace ℝ (Fin 24)) 1) =
      ENNReal.ofReal (Real.pi ^ 12 / (Nat.factorial 12 : ℝ)) := by
    simpa [finrank_euclideanSpace] using
      (InnerProductSpace.volume_ball_of_dim_even (E := EuclideanSpace ℝ (Fin 24)) (k := 12)
        (hk := by simp) (x := 0) (r := 1))
  have hfac : (0 : ℝ) < (Nat.factorial 12 : ℝ) := by exact_mod_cast Nat.factorial_pos 12
  rw [hball, SpherePacking.Dim24.LeechPacking_density, hvol, ENNReal.ofReal_div_of_pos hfac]
  simp [ENNReal.ofReal_pow Real.pi_pos.le, ENNReal.ofReal_natCast]

/-- An even lattice of covolume one in `ℝ²⁴` without vectors of squared norm two is the image of
the Leech lattice of Sphere-Packing-Lean under an isometry of `ℝ²⁴`. -/
theorem exists_isometryEquiv_image_eq_splLeechLattice (L : Submodule ℤ (Ambient 24))
    [DiscreteTopology L] [IsZLattice ℝ L] (heven : ∀ x ∈ L, ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k)
    (hcov : ZLattice.covolume L volume = 1) (hroot : ∀ x ∈ L, x ≠ 0 → ‖x‖ ^ 2 ≠ 2) :
    ∃ e : Ambient 24 ≃ᵢ Ambient 24,
      e '' (L : Set (Ambient 24)) =
        (SpherePacking.Dim24.LeechLattice : Set (Ambient 24)) := by
  obtain ⟨-, e, he⟩ :=
    SpherePacking.Dim24.Uniqueness.RigidityClassify.CE.leech_rigidity_normalized
      (evenRootlessPacking L heven hroot) rfl (evenRootlessPacking_density L heven hroot hcov)
  exact ⟨e, he⟩

/-- An isometry of a real normed space carrying an additive subgroup onto an additive subgroup can
be replaced by a linear isometry: translate the image of the origin back to the origin, inside
the target subgroup. -/
theorem exists_linearIsometryEquiv_image_eq_of_isometryEquiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (A B : AddSubgroup E) (f : E ≃ᵢ E) (hf : f '' (A : Set E) = B) :
    ∃ Φ : E ≃ₗᵢ[ℝ] E, Φ '' (A : Set E) = B := by
  have hmem : ∀ x ∈ A, f x ∈ B := by
    intro x hx
    have h : f x ∈ f '' (A : Set E) := ⟨x, hx, rfl⟩
    rwa [hf] at h
  have h0 : f 0 ∈ B := hmem 0 A.zero_mem
  let g : E ≃ᵢ E := f.trans (IsometryEquiv.subRight (f 0))
  have hg : ∀ x, g x = f x - f 0 := fun _ => rfl
  have hg0 : g 0 = 0 := by rw [hg, sub_self]
  refine ⟨g.toRealLinearIsometryEquivOfMapZero hg0, ?_⟩
  rw [IsometryEquiv.coe_toRealLinearIsometryEquivOfMapZero]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hg]
    exact B.sub_mem (hmem x hx) h0
  · intro hy
    have h : y + f 0 ∈ f '' (A : Set E) := by
      rw [hf]
      exact B.add_mem hy h0
    obtain ⟨x, hx, hxy⟩ := h
    exact ⟨x, hx, by rw [hg, hxy, add_sub_cancel_right]⟩

/-- **The characterization of the Leech lattice**: an even lattice of covolume one in `ℝ²⁴`
without vectors of squared norm two is the image of the Leech lattice under a linear isometry. -/
theorem leechCharacterization : LeechCharacterization := by
  intro L _ _ heven hcov hroot
  obtain ⟨e₁, he₁⟩ := exists_isometryEquiv_image_eq_splLeechLattice L heven hcov hroot
  obtain ⟨e₂, he₂⟩ := exists_isometryEquiv_image_eq_splLeechLattice leechLattice
    (fun x hx => leechLattice_norm_sq_even hx) leechLattice_covolume
    (fun x hx hne h2 => by
      have hx' : x ∈ leechSet := by
        rw [← coe_leechLattice]
        exact hx
      have h4 := leechSet_norm_sq_lower hx' hne
      linarith)
  have hf : (e₂.trans e₁.symm) '' (leechLattice : Set (Ambient 24)) = (L : Set (Ambient 24)) := by
    have h : (e₂.trans e₁.symm) '' (leechLattice : Set (Ambient 24)) =
        e₁.symm '' (e₂ '' (leechLattice : Set (Ambient 24))) := by
      rw [Set.image_image]
      rfl
    rw [h, he₂, ← he₁, ← Set.image_comp, IsometryEquiv.symm_comp_self, Set.image_id]
  obtain ⟨Φ, hΦ⟩ := exists_linearIsometryEquiv_image_eq_of_isometryEquiv
    leechLattice.toAddSubgroup L.toAddSubgroup (e₂.trans e₁.symm) hf
  refine ⟨Φ, ?_⟩
  rw [← coe_leechLattice]
  exact hΦ

end E8Leech
