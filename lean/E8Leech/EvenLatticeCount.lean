import E8Leech.EvenUnimodularCounts
import E8Leech.LatticePointCount

/-!
# An even integral lattice of rank eight with many points in a ball is `E8`

Let `L ⊂ ℝ⁸` be a `ℤ`-submodule on which inner products are integers and squared norms are even
integers, containing the lattice of a basis `w` of `ℝ⁸`. If a finite set `T ⊂ L` in a ball of
radius `R'` satisfies `vol(B_{R'+ρ})² < 2 (#T)²`, `ρ = ∑ |wᵢ|`, then `L` is an isometric copy of
`E8` (`exists_isometry_image_e8Set_eq_of_even_lattice_count`).

The lattice is discrete because its nonzero vectors have norm at least `√2`; a `ℤ`-basis has an
integer Gram matrix with even diagonal, whose determinant is the squared covolume; the count of
lattice points (`card_mul_covolume_le`) gives covolume `< √2`, so the determinant is `1`.

* `span_int_integral_even`: integrality and evenness pass from generators to the span.
* `discreteTopology_of_even_norm_sq`.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric
open scoped InnerProductSpace

/-- Integrality and evenness pass from a generating set to its `ℤ`-span. -/
theorem span_int_integral_even {d : ℕ} {𝒢 : Set (Ambient d)}
    (hint : ∀ x ∈ 𝒢, ∀ y ∈ 𝒢, ∃ m : ℤ, ⟪x, y⟫_ℝ = m)
    (heven : ∀ x ∈ 𝒢, ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k) :
    (∀ x ∈ Submodule.span ℤ 𝒢, ∀ y ∈ Submodule.span ℤ 𝒢, ∃ m : ℤ, ⟪x, y⟫_ℝ = m) ∧
      ∀ x ∈ Submodule.span ℤ 𝒢, ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k := by
  have h1 : ∀ y ∈ 𝒢, ∀ x ∈ Submodule.span ℤ 𝒢, ∃ m : ℤ, ⟪x, y⟫_ℝ = m := by
    intro y hy x hx
    refine Submodule.span_induction (p := fun x _ => ∃ m : ℤ, ⟪x, y⟫_ℝ = m) ?_ ?_ ?_ ?_ hx
    · intro x hx
      exact hint x hx y hy
    · exact ⟨0, by simp⟩
    · rintro a b _ _ ⟨m, hm⟩ ⟨n, hn⟩
      exact ⟨m + n, by rw [inner_add_left, hm, hn]; push_cast; ring⟩
    · rintro n a _ ⟨m, hm⟩
      exact ⟨n * m, by
        rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hm]
        push_cast
        ring⟩
  have h2 : ∀ x ∈ Submodule.span ℤ 𝒢, ∀ y ∈ Submodule.span ℤ 𝒢, ∃ m : ℤ, ⟪x, y⟫_ℝ = m := by
    intro x hx y hy
    refine Submodule.span_induction (p := fun y _ => ∃ m : ℤ, ⟪x, y⟫_ℝ = m) ?_ ?_ ?_ ?_ hy
    · intro y hy
      exact h1 y hy x hx
    · exact ⟨0, by simp⟩
    · rintro a b _ _ ⟨m, hm⟩ ⟨n, hn⟩
      exact ⟨m + n, by rw [inner_add_right, hm, hn]; push_cast; ring⟩
    · rintro n a _ ⟨m, hm⟩
      exact ⟨n * m, by
        rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hm]
        push_cast
        ring⟩
  refine ⟨h2, fun x hx => ?_⟩
  refine Submodule.span_induction
    (p := fun x _ => x ∈ Submodule.span ℤ 𝒢 ∧ ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k) ?_ ?_ ?_ ?_ hx |>.2
  · intro x hx
    exact ⟨Submodule.subset_span hx, heven x hx⟩
  · exact ⟨Submodule.zero_mem _, 0, by simp⟩
  · rintro a b _ _ ⟨ha, k, hk⟩ ⟨hb, l, hl⟩
    obtain ⟨m, hm⟩ := h2 a ha b hb
    refine ⟨Submodule.add_mem _ ha hb, k + m + l, ?_⟩
    rw [norm_add_sq_real, hk, hl, hm]
    push_cast
    ring
  · rintro n a _ ⟨ha, k, hk⟩
    refine ⟨Submodule.smul_mem _ n ha, n ^ 2 * k, ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℝ, norm_smul, mul_pow, hk, Real.norm_eq_abs, sq_abs]
    push_cast
    ring

/-- A `ℤ`-submodule whose squared norms are even integers is discrete. -/
theorem discreteTopology_of_even_norm_sq {d : ℕ} (L : Submodule ℤ (Ambient d))
    (heven : ∀ x ∈ L, ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k) : DiscreteTopology L := by
  apply discreteTopology_of_isOpen_singleton_zero
  have he : ({0} : Set L) = (Subtype.val : L → Ambient d) ⁻¹' ball 0 1 := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, mem_ball, dist_zero_right]
    constructor
    · rintro rfl
      simp
    · intro hx
      obtain ⟨k, hk⟩ := heven x x.2
      have h0 : (0 : ℝ) ≤ ‖(x : Ambient d)‖ := norm_nonneg _
      have h1 : ‖(x : Ambient d)‖ ^ 2 < 1 := by nlinarith
      have h2 : (0 : ℝ) ≤ ‖(x : Ambient d)‖ ^ 2 := sq_nonneg _
      have h3 : (2 * k : ℝ) < 1 := by rw [← hk]; exact h1
      have h4 : (0 : ℝ) ≤ 2 * k := by rw [← hk]; exact h2
      have h5 : (2 * k : ℤ) < 1 := by exact_mod_cast h3
      have h6 : (0 : ℤ) ≤ 2 * k := by exact_mod_cast h4
      have hk0 : k = 0 := by omega
      rw [hk0] at hk
      have h7 : ‖(x : Ambient d)‖ ^ 2 = 0 := by rw [hk]; simp
      exact Subtype.ext (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h7))
  rw [he]
  exact isOpen_ball.preimage continuous_subtype_val

/-- If `N κ ≤ V` and `V² < 2 N²` then `κ² < 2`. -/
theorem sq_lt_two_of_count {N V κ : ℝ} (hκ : 0 < κ) (hcnt : N * κ ≤ V) (hN : 0 ≤ N)
    (hcount : V ^ 2 < 2 * N ^ 2) : κ ^ 2 < 2 := by
  have hN0 : 0 < N := by
    rcases eq_or_lt_of_le hN with h | h
    · rw [← h] at hcount
      nlinarith [sq_nonneg V]
    · exact h
  have h1 : (N * κ) ^ 2 ≤ V ^ 2 := pow_le_pow_left₀ (mul_nonneg hN hκ.le) hcnt 2
  have h2 : N ^ 2 * κ ^ 2 < N ^ 2 * 2 := by nlinarith
  exact lt_of_mul_lt_mul_left h2 (sq_nonneg N)

/-- A discrete `ℤ`-submodule of `ℝ⁸` containing the lattice of a basis is the lattice of a
basis. -/
theorem exists_basis_span_eq_of_even_lattice (L : Submodule ℤ (Ambient 8))
    (heven : ∀ x ∈ L, ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k)
    (bw : Module.Basis (Fin 8) ℝ (Ambient 8)) (hle : Submodule.span ℤ (Set.range bw) ≤ L) :
    ∃ bR : Module.Basis (Fin 8) ℝ (Ambient 8), Submodule.span ℤ (Set.range bR) = L := by
  have hdisc : DiscreteTopology L := discreteTopology_of_even_norm_sq L heven
  have hlat : IsZLattice ℝ L := ⟨by
    rw [eq_top_iff, ← bw.span_eq]
    exact Submodule.span_mono fun x hx => hle (Submodule.subset_span hx)⟩
  have hrank : Module.finrank ℤ L = 8 := by
    rw [ZLattice.rank ℝ L]
    simp
  exact ⟨(Module.finBasisOfFinrankEq ℤ L hrank).ofZLatticeBasis ℝ L,
    (Module.finBasisOfFinrankEq ℤ L hrank).ofZLatticeBasis_span ℝ L⟩

/-- **An even integral lattice of rank eight with many points in a ball is `E8`.** -/
theorem exists_isometry_image_e8Set_eq_of_even_lattice_count (L : Submodule ℤ (Ambient 8))
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ m : ℤ, ⟪x, y⟫_ℝ = m)
    (heven : ∀ x ∈ L, ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k)
    (bw : Module.Basis (Fin 8) ℝ (Ambient 8)) (hle : Submodule.span ℤ (Set.range bw) ≤ L)
    (T : Finset (Ambient 8)) (hT : ∀ t ∈ T, t ∈ L) {c : Ambient 8} {R' : ℝ}
    (hball : ∀ t ∈ T, t ∈ closedBall c R')
    (hcount : volume.real (closedBall c (R' + ∑ i, ‖bw i‖)) ^ 2 < 2 * (T.card : ℝ) ^ 2) :
    ∃ Φ : Ambient 8 ≃ₗᵢ[ℝ] Ambient 8, Φ '' e8Set = (L : Set (Ambient 8)) := by
  obtain ⟨bR, hspan⟩ := exists_basis_span_eq_of_even_lattice L heven bw hle
  have hmem : ∀ i, bR i ∈ L := fun i => by
    rw [← hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  -- the integer Gram matrix of the basis
  choose M hM using fun i j => hint (bR i) (hmem i) (bR j) (hmem j)
  have hgram : ∀ i j, ⟪bR i, bR j⟫_ℝ = ((Matrix.of M : Matrix (Fin 8) (Fin 8) ℤ) i j : ℝ) :=
    fun i j => hM i j
  have hevenM : ∀ i, (2 : ℤ) ∣ (Matrix.of M : Matrix (Fin 8) (Fin 8) ℤ) i i := by
    intro i
    obtain ⟨k, hk⟩ := heven (bR i) (hmem i)
    refine ⟨k, ?_⟩
    have e : (((Matrix.of M : Matrix (Fin 8) (Fin 8) ℤ) i i : ℤ) : ℝ) = 2 * k := by
      rw [← hgram i i, real_inner_self_eq_norm_sq, hk]
    exact_mod_cast e
  -- its determinant is the squared covolume
  have hdetR : (((Matrix.of M : Matrix (Fin 8) (Fin 8) ℤ).det : ℤ) : ℝ) =
      ZLattice.covolume (Submodule.span ℤ (Set.range bR)) ^ 2 := by
    rw [covolume_sq_eq_det_gram bR]
    have e : (Matrix.of fun i j => ⟪bR i, bR j⟫_ℝ) =
        (Matrix.of M : Matrix (Fin 8) (Fin 8) ℤ).map (Int.castRingHom ℝ) := by
      ext i j
      rw [Matrix.of_apply, Matrix.map_apply, hgram i j]
      rfl
    rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  have hcovpos := ZLattice.covolume_pos (Submodule.span ℤ (Set.range bR)) volume
  have hdetpos : 0 < (Matrix.of M : Matrix (Fin 8) (Fin 8) ℤ).det := by
    have h : (0 : ℝ) < (((Matrix.of M : Matrix (Fin 8) (Fin 8) ℤ).det : ℤ) : ℝ) := by
      rw [hdetR]
      positivity
    exact_mod_cast h
  -- the count of lattice points
  have hcnt := card_mul_covolume_le bw (Submodule.span ℤ (Set.range bR))
    (by rw [hspan]; exact hle) T (fun t ht => by rw [hspan]; exact hT t ht) hball
  have hdet2 : (((Matrix.of M : Matrix (Fin 8) (Fin 8) ℤ).det : ℤ) : ℝ) < 2 := by
    rw [hdetR]
    exact sq_lt_two_of_count hcovpos hcnt (Nat.cast_nonneg _) hcount
  have hdet1 : (Matrix.of M : Matrix (Fin 8) (Fin 8) ℤ).det = 1 := by
    have h : (Matrix.of M : Matrix (Fin 8) (Fin 8) ℤ).det < 2 := by exact_mod_cast hdet2
    omega
  have hG : EvenUnimodularGram (fun i => bR i) (Matrix.of M) := ⟨hgram, hdet1, hevenM⟩
  obtain ⟨Φ, hΦ⟩ := hG.exists_isometry_image_e8Set_eq
  refine ⟨Φ, ?_⟩
  rw [hΦ, ← hspan]
  show (AddSubgroup.closure (Set.range fun i => bR i) : Set (Ambient 8)) =
    ((Submodule.span ℤ (Set.range bR)).toAddSubgroup : Set (Ambient 8))
  rw [Submodule.span_int_eq_addSubgroupClosure]

end E8Leech
