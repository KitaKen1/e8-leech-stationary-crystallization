import E8Leech.EvenLatticeCount
import E8Leech.LeechLattice

/-!
# An even integral lattice of rank 24 with many separated points in a ball is the Leech lattice

The `E8` case (`exists_isometry_image_e8Set_eq_of_even_lattice_count`) identifies an even integral
lattice of rank eight from a count of its points, because an even unimodular lattice of rank eight
is `E8`. In rank 24 an even unimodular lattice is the Leech lattice exactly when it has no vector
of squared norm two. This characterization (Conway; it also follows from Niemeier's
classification) is not proved in this file: it is the explicit hypothesis `LeechCharacterization`
of the theorems that use it.

Let `L ⊂ ℝ²⁴` be a `ℤ`-submodule on which inner products are integers and squared norms are even
integers, containing the lattice of a basis `w`. Let `T ⊂ L` be a finite set in a ball of radius
`R'` whose points differ by vectors of squared norm more than two, with
`vol(B_{R'+2+ρ})² < 2 (#T)²`, `ρ = ∑ |wᵢ|`. Then

* the covolume of `L` is one (as in rank eight), and
* `L` has no vector `v` of squared norm two: `T` and `T + v` would be disjoint subsets of `L` in
  the ball of radius `R' + 2`, twice as many points as the covolume allows.

So `L` is an isometric copy of the Leech lattice
(`exists_isometry_image_leechSet_eq_of_even_lattice_count`).
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric
open scoped InnerProductSpace

/-- **The characterization of the Leech lattice**: an even unimodular lattice of rank 24 without
vectors of squared norm two is an isometric copy of the Leech lattice. -/
def LeechCharacterization : Prop :=
  ∀ (L : Submodule ℤ (Ambient 24)) [DiscreteTopology L] [IsZLattice ℝ L],
    (∀ x ∈ L, ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k) → ZLattice.covolume L volume = 1 →
    (∀ x ∈ L, x ≠ 0 → ‖x‖ ^ 2 ≠ 2) →
    ∃ Φ : Ambient 24 ≃ₗᵢ[ℝ] Ambient 24, Φ '' leechSet = (L : Set (Ambient 24))

/-- A `ℤ`-submodule of `ℝᵈ` with even squared norms containing the lattice of a basis is the
lattice of a basis. -/
theorem exists_basis_span_eq_of_even {d : ℕ} (L : Submodule ℤ (Ambient d))
    (heven : ∀ x ∈ L, ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k)
    (bw : Module.Basis (Fin d) ℝ (Ambient d)) (hle : Submodule.span ℤ (Set.range bw) ≤ L) :
    ∃ bR : Module.Basis (Fin d) ℝ (Ambient d), Submodule.span ℤ (Set.range bR) = L := by
  have hdisc : DiscreteTopology L := discreteTopology_of_even_norm_sq L heven
  have hlat : IsZLattice ℝ L := ⟨by
    rw [eq_top_iff, ← bw.span_eq]
    exact Submodule.span_mono fun x hx => hle (Submodule.subset_span hx)⟩
  have hrank : Module.finrank ℤ L = d := by
    rw [ZLattice.rank ℝ L]
    simp
  exact ⟨(Module.finBasisOfFinrankEq ℤ L hrank).ofZLatticeBasis ℝ L,
    (Module.finBasisOfFinrankEq ℤ L hrank).ofZLatticeBasis_span ℝ L⟩

/-- A lattice of covolume one has no nonzero vector `v` of norm at most `s` if it contains a
finite set `T` in a ball, no two points of which differ by `v`, with more than half as many
points as the volume of the ball enlarged by `s` and a fundamental domain. -/
theorem ne_of_count_translate {d : ℕ} (b : Module.Basis (Fin d) ℝ (Ambient d))
    (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hle : Submodule.span ℤ (Set.range b) ≤ Λ) (hcov : ZLattice.covolume Λ volume = 1)
    (T : Finset (Ambient d)) (hT : ∀ t ∈ T, t ∈ Λ) {c : Ambient d} {R' s : ℝ}
    (hball : ∀ t ∈ T, t ∈ closedBall c R')
    (hcount : volume.real (closedBall c (R' + s + ∑ i, ‖b i‖)) < 2 * (T.card : ℝ))
    {v : Ambient d} (hv : v ∈ Λ) (hvs : ‖v‖ ≤ s) (hv0 : v ≠ 0) :
    ∃ t ∈ T, ∃ t' ∈ T, t ≠ t' ∧ t - t' = v := by
  classical
  by_contra hcon
  have hno : ∀ t ∈ T, t + v ∉ T := by
    intro t ht htv
    refine hcon ⟨t + v, htv, t, ht, fun h => hv0 ?_, by abel⟩
    exact add_eq_left.mp h
  let f : Ambient d ↪ Ambient d := ⟨fun t => t + v, add_left_injective v⟩
  have hdisj : Disjoint T (T.map f) := by
    rw [Finset.disjoint_left]
    intro t' ht' hmap
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hmap
    exact hno t ht ht'
  have hcard : (T ∪ T.map f).card = 2 * T.card := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_map]
    ring
  have hT' : ∀ t ∈ T ∪ T.map f, t ∈ Λ := by
    intro t ht
    rcases Finset.mem_union.mp ht with h | h
    · exact hT t h
    · obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_map.mp h
      exact Λ.add_mem (hT t₀ ht₀) hv
  have hball' : ∀ t ∈ T ∪ T.map f, t ∈ closedBall c (R' + s) := by
    intro t ht
    rcases Finset.mem_union.mp ht with h | h
    · have h1 := mem_closedBall.mp (hball t h)
      rw [mem_closedBall]
      linarith [(norm_nonneg v).trans hvs]
    · obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_map.mp h
      have h1 := mem_closedBall.mp (hball t₀ ht₀)
      rw [mem_closedBall]
      have h2 : dist (t₀ + v) c ≤ dist t₀ c + ‖v‖ := by
        rw [dist_eq_norm, dist_eq_norm]
        have e : t₀ + v - c = (t₀ - c) + v := by abel
        rw [e]
        exact norm_add_le _ _
      show dist (t₀ + v) c ≤ R' + s
      linarith
  have hcnt := card_mul_covolume_le b Λ hle (T ∪ T.map f) hT' hball'
  rw [hcov, mul_one, hcard] at hcnt
  push_cast at hcnt
  linarith

/-- **An even integral lattice of rank 24 with many separated points in a ball is the Leech
lattice**, given the characterization of the Leech lattice. -/
theorem exists_isometry_image_leechSet_eq_of_even_lattice_count (hLeech : LeechCharacterization)
    (L : Submodule ℤ (Ambient 24))
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ m : ℤ, ⟪x, y⟫_ℝ = m)
    (heven : ∀ x ∈ L, ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k)
    (bw : Module.Basis (Fin 24) ℝ (Ambient 24)) (hle : Submodule.span ℤ (Set.range bw) ≤ L)
    (T : Finset (Ambient 24)) (hT : ∀ t ∈ T, t ∈ L) {c : Ambient 24} {R' : ℝ}
    (hball : ∀ t ∈ T, t ∈ closedBall c R')
    (hsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 2 < ‖t - t'‖ ^ 2)
    (hcount : volume.real (closedBall c (R' + 2 + ∑ i, ‖bw i‖)) ^ 2 < 2 * (T.card : ℝ) ^ 2) :
    ∃ Φ : Ambient 24 ≃ₗᵢ[ℝ] Ambient 24, Φ '' leechSet = (L : Set (Ambient 24)) := by
  classical
  obtain ⟨bR, hspan⟩ := exists_basis_span_eq_of_even L heven bw hle
  subst hspan
  have hmem : ∀ i, bR i ∈ Submodule.span ℤ (Set.range bR) := fun i =>
    Submodule.subset_span ⟨i, rfl⟩
  -- the integer Gram matrix of the basis; its determinant is the squared covolume
  choose M hM using fun i j => hint (bR i) (hmem i) (bR j) (hmem j)
  have hdetR : (((Matrix.of M : Matrix (Fin 24) (Fin 24) ℤ).det : ℤ) : ℝ) =
      ZLattice.covolume (Submodule.span ℤ (Set.range bR)) ^ 2 := by
    rw [covolume_sq_eq_det_gram bR]
    have e : (Matrix.of fun i j => ⟪bR i, bR j⟫_ℝ) =
        (Matrix.of M : Matrix (Fin 24) (Fin 24) ℤ).map (Int.castRingHom ℝ) := by
      ext i j
      rw [Matrix.of_apply, Matrix.map_apply, hM i j]
      rfl
    rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  have hcovpos := ZLattice.covolume_pos (Submodule.span ℤ (Set.range bR)) volume
  have hdetpos : 0 < (Matrix.of M : Matrix (Fin 24) (Fin 24) ℤ).det := by
    have h : (0 : ℝ) < (((Matrix.of M : Matrix (Fin 24) (Fin 24) ℤ).det : ℤ) : ℝ) := by
      rw [hdetR]
      positivity
    exact_mod_cast h
  have hV0 : 0 ≤ volume.real (closedBall c (R' + 2 + ∑ i, ‖bw i‖)) := measureReal_nonneg
  have hN0 : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  -- the count of lattice points gives covolume one
  have hcnt := card_mul_covolume_le bw (Submodule.span ℤ (Set.range bR)) hle T hT hball
  have hmono : volume.real (closedBall c (R' + ∑ i, ‖bw i‖)) ≤
      volume.real (closedBall c (R' + 2 + ∑ i, ‖bw i‖)) :=
    measureReal_mono (closedBall_subset_closedBall (by linarith)) measure_closedBall_lt_top.ne
  have hdet2 : (((Matrix.of M : Matrix (Fin 24) (Fin 24) ℤ).det : ℤ) : ℝ) < 2 := by
    rw [hdetR]
    exact sq_lt_two_of_count hcovpos (hcnt.trans hmono) hN0 hcount
  have hdet1 : (Matrix.of M : Matrix (Fin 24) (Fin 24) ℤ).det = 1 := by
    have h : (Matrix.of M : Matrix (Fin 24) (Fin 24) ℤ).det < 2 := by exact_mod_cast hdet2
    omega
  have hcov1 : ZLattice.covolume (Submodule.span ℤ (Set.range bR)) volume = 1 := by
    have h : ZLattice.covolume (Submodule.span ℤ (Set.range bR)) ^ 2 = 1 := by
      rw [← hdetR, hdet1]
      norm_num
    exact (pow_eq_one_iff_of_nonneg hcovpos.le two_ne_zero).mp h
  -- there is no vector of squared norm two
  have hroot : ∀ x ∈ Submodule.span ℤ (Set.range bR), x ≠ 0 → ‖x‖ ^ 2 ≠ 2 := by
    intro v hv hv0 hv2
    have hvs : ‖v‖ ≤ 2 := by nlinarith [norm_nonneg v]
    have hlt : volume.real (closedBall c (R' + 2 + ∑ i, ‖bw i‖)) < 2 * (T.card : ℝ) := by
      by_contra hge
      have h1 : (2 * (T.card : ℝ)) ^ 2 ≤
          volume.real (closedBall c (R' + 2 + ∑ i, ‖bw i‖)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (not_lt.mp hge) 2
      nlinarith [sq_nonneg (T.card : ℝ)]
    obtain ⟨t, ht, t', ht', hne, hd⟩ := ne_of_count_translate bw
      (Submodule.span ℤ (Set.range bR)) hle hcov1 T hT hball hlt hv hvs hv0
    have h := hsep t ht t' ht' hne
    rw [hd, hv2] at h
    exact lt_irrefl _ h
  exact hLeech (Submodule.span ℤ (Set.range bR)) heven hcov1 hroot

end E8Leech
