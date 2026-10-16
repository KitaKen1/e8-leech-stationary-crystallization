import E8Leech.E8FrameIdentification
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.Pigeonhole

/-!
# A norm-four frame from the numbers of short vectors

Let `L` be an even subgroup of `ℝ⁸` spanned over `ℤ` by eight vectors, with exactly `240`
vectors of squared norm `2` and `2160` vectors of squared norm `4`. Coordinates modulo `2` give
at most `2⁸ = 256` classes, and two vectors in one class are congruent modulo `2L`. If `x ≠ ±y`
are congruent modulo `2L`, then `(x - y)/2` and `(x + y)/2` are nonzero vectors of `L`, so
`‖x‖² + ‖y‖² ≥ 8`. Hence the class of `0` contains no short vector, a class contains at most one
pair `±r` of roots and then no vector of squared norm `4`, and the vectors of squared norm `4` in
one class are pairwise opposite or orthogonal. The roots occupy at least `120` classes, so the
`2160` vectors of squared norm `4` lie in at most `135` classes and one class contains `16` of
them: eight mutually orthogonal vectors, congruent modulo `2L`.

With self-duality some vector has an odd inner product with the first frame vector, and
`E8FrameIdentification` gives an isometry onto `e8Set`.

* `two_le_norm_sq_of_even`, `eight_le_norm_sq_add_of_congr`, `inner_eq_zero_of_congr`: the
  parallelogram argument.
* `exists_orthogonal_subset`: half of a set of pairwise opposite or orthogonal vectors is
  orthogonal.
* `exists_normFourFrame_of_counts`: the frame.
* `exists_isometry_image_e8Set_eq_of_counts`: the identification with `e8Set`.
-/

noncomputable section

namespace E8Leech

open scoped InnerProductSpace
open Finset

variable {L : AddSubgroup (Ambient 8)}

/-- A nonzero vector of an even subgroup has squared norm at least two. -/
theorem two_le_norm_sq_of_even (heven : ∀ x ∈ L, ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k) {x : Ambient 8}
    (hx : x ∈ L) (hx0 : x ≠ 0) : 2 ≤ ‖x‖ ^ 2 := by
  obtain ⟨k, hk⟩ := heven x hx
  have hpos : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
  have hk0 : (0 : ℝ) < k := by linarith
  have hk1 : (1 : ℤ) ≤ k := by
    have h : (0 : ℤ) < k := by exact_mod_cast hk0
    omega
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  linarith

/-- The two halves of a congruence modulo `2L`. -/
theorem norm_sq_add_of_congr {x y y' : Ambient 8} (e : x - y = y' + y') :
    ‖x‖ ^ 2 + ‖y‖ ^ 2 = 2 * (‖y' + y‖ ^ 2 + ‖y'‖ ^ 2) := by
  have hx : x = y' + y + y' := by
    rw [← sub_add_cancel x y, e]
    abel
  have hy : y = y' + y - y' := by abel
  have h1 := norm_add_sq_real (y' + y) y'
  have h2 := norm_sub_sq_real (y' + y) y'
  rw [← hx] at h1
  rw [← hy] at h2
  linarith

/-- Vectors congruent modulo `2L` and not opposite or equal are long. -/
theorem eight_le_norm_sq_add_of_congr (heven : ∀ x ∈ L, ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k)
    {x y y' : Ambient 8} (hy : y ∈ L) (hy' : y' ∈ L) (e : x - y = y' + y') (hne : x ≠ y)
    (hne' : x ≠ -y) : 8 ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have h0 : y' ≠ 0 := by
    intro h
    rw [h, add_zero, sub_eq_zero] at e
    exact hne e
  have h1 : y' + y ≠ 0 := by
    intro h
    apply hne'
    have hy'' : y' = -y := eq_neg_of_add_eq_zero_left h
    rw [hy''] at e
    have hx : x = -y + -y + y := by rw [← e, sub_add_cancel]
    rw [hx]
    abel
  have l0 := two_le_norm_sq_of_even heven hy' h0
  have l1 := two_le_norm_sq_of_even heven (L.add_mem hy' hy) h1
  rw [norm_sq_add_of_congr e]
  linarith

/-- Two vectors of squared norm four that are congruent modulo `2L` and not opposite or equal
are orthogonal. -/
theorem inner_eq_zero_of_congr (heven : ∀ x ∈ L, ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k)
    {x y y' : Ambient 8} (hy : y ∈ L) (hy' : y' ∈ L) (e : x - y = y' + y') (hne : x ≠ y)
    (hne' : x ≠ -y) (hx4 : ‖x‖ ^ 2 = 4) (hy4 : ‖y‖ ^ 2 = 4) : ⟪x, y⟫_ℝ = 0 := by
  have h0 : y' ≠ 0 := by
    intro h
    rw [h, add_zero, sub_eq_zero] at e
    exact hne e
  have h1 : y' + y ≠ 0 := by
    intro h
    apply hne'
    have hy'' : y' = -y := eq_neg_of_add_eq_zero_left h
    rw [hy''] at e
    have hx : x = -y + -y + y := by rw [← e, sub_add_cancel]
    rw [hx]
    abel
  have l0 := two_le_norm_sq_of_even heven hy' h0
  have l1 := two_le_norm_sq_of_even heven (L.add_mem hy' hy) h1
  have hs := norm_sq_add_of_congr e
  have hd := norm_sub_sq_real x y
  have hyy : ‖y' + y'‖ ^ 2 = 4 * ‖y'‖ ^ 2 := by
    have h := norm_add_sq_real y' y'
    rw [real_inner_self_eq_norm_sq] at h
    linarith
  rw [e, hyy] at hd
  linarith

/-- Among pairwise equal, opposite or orthogonal vectors, half of them are pairwise orthogonal. -/
theorem exists_orthogonal_subset :
    ∀ (n : ℕ) (F : Finset (Ambient 8)), F.card = n →
      (∀ x ∈ F, ∀ y ∈ F, x = y ∨ x = -y ∨ ⟪x, y⟫_ℝ = 0) →
      ∃ T ⊆ F, (∀ x ∈ T, ∀ y ∈ T, x ≠ y → ⟪x, y⟫_ℝ = 0) ∧ F.card ≤ 2 * T.card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro F hn h
    rcases F.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
    · let F' := F.filter fun y => y ≠ x ∧ y ≠ -x
      have hF'sub : F' ⊆ F := Finset.filter_subset _ _
      have hxF' : x ∉ F' := by
        intro hx'
        exact (Finset.mem_filter.mp hx').2.1 rfl
      have hlt : F'.card < n := by
        rw [← hn]
        exact Finset.card_lt_card ⟨hF'sub, fun hsub => hxF' (hsub hx)⟩
      obtain ⟨T', hT'sub, hT'orth, hT'card⟩ :=
        ih F'.card hlt F' rfl fun a ha b hb => h a (hF'sub ha) b (hF'sub hb)
      have hxT' : x ∉ T' := fun hx' => hxF' (hT'sub hx')
      have horth : ∀ y ∈ T', ⟪x, y⟫_ℝ = 0 := by
        intro y hy
        have hyF' := Finset.mem_filter.mp (hT'sub hy)
        rcases h x hx y hyF'.1 with h1 | h1 | h1
        · exact absurd h1.symm hyF'.2.1
        · exact absurd (by rw [h1, neg_neg]) hyF'.2.2
        · exact h1
      refine ⟨insert x T', ?_, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with hyx | hy'
        · rw [hyx]
          exact hx
        · exact hF'sub (hT'sub hy')
      · intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with hax | ha'
        · rcases Finset.mem_insert.mp hb with hbx | hb'
          · exact absurd (hax.trans hbx.symm) hab
          · rw [hax]
            exact horth b hb'
        · rcases Finset.mem_insert.mp hb with hbx | hb'
          · rw [hbx, real_inner_comm]
            exact horth a ha'
          · exact hT'orth a ha' b hb' hab
      · have hsub : F ⊆ F' ∪ {x, -x} := by
          intro y hy
          by_cases h1 : y = x
          · exact Finset.mem_union_right _ (by simp [h1])
          · by_cases h2 : y = -x
            · exact Finset.mem_union_right _ (by simp [h2])
            · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hy, h1, h2⟩)
        have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        have hc2 : ({x, -x} : Finset (Ambient 8)).card ≤ 2 := Finset.card_le_two
        rw [Finset.card_insert_of_notMem hxT']
        omega

/-- **The frame.** An even subgroup of `ℝ⁸` spanned by eight vectors with `240` vectors of
squared norm `2` and `2160` of squared norm `4` contains eight mutually orthogonal vectors of
squared norm `4` that are congruent modulo `2L`. -/
theorem exists_normFourFrame_of_counts (heven : ∀ x ∈ L, ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k)
    (e : Fin 8 → Ambient 8) (he : ∀ i, e i ∈ L)
    (hspan : ∀ x ∈ L, ∃ a : Fin 8 → ℤ, x = ∑ i, a i • e i)
    (S₂ S₄ : Finset (Ambient 8)) (hS₂ : ∀ x, x ∈ S₂ ↔ x ∈ L ∧ ‖x‖ ^ 2 = 2)
    (hS₄ : ∀ x, x ∈ S₄ ↔ x ∈ L ∧ ‖x‖ ^ 2 = 4) (h2 : S₂.card = 240) (h4 : S₄.card = 2160) :
    ∃ v : Fin 8 → Ambient 8, (∀ i, v i ∈ L) ∧ (∀ i, ‖v i‖ ^ 2 = 4) ∧
      (∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ = 0) ∧ ∀ i j, ∃ y ∈ L, v i - v j = y + y := by
  classical
  choose! a ha using hspan
  -- the class of a vector: its coordinates modulo two
  let κ : Ambient 8 → Fin 8 → ZMod 2 := fun x i => ((a x i : ℤ) : ZMod 2)
  -- equal classes are congruent modulo `2L`
  have hcongr : ∀ x ∈ L, ∀ y ∈ L, κ x = κ y → ∃ y' ∈ L, x - y = y' + y' := by
    intro x hx y hy hκ
    have hd : ∀ i, (2 : ℤ) ∣ a x i - a y i := by
      intro i
      have h := congrFun hκ i
      have h' := (ZMod.intCast_eq_intCast_iff_dvd_sub (a y i) (a x i) 2).mp h.symm
      exact_mod_cast h'
    choose d hd' using hd
    refine ⟨∑ i, d i • e i, L.sum_mem fun i _ => L.zsmul_mem (he i) (d i), ?_⟩
    have hxy : x - y = ∑ i, (a x i - a y i) • e i := by
      have h1 := ha x hx
      have h2 := ha y hy
      calc x - y = ∑ i, a x i • e i - ∑ i, a y i • e i := by rw [← h1, ← h2]
        _ = ∑ i, (a x i - a y i) • e i := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => (sub_smul _ _ _).symm
    rw [hxy, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hd' i, two_mul, add_smul]
  -- no short vector in the class of zero
  have hzero : ∀ x ∈ L, x ≠ 0 → ‖x‖ ^ 2 < 8 → κ x ≠ κ 0 := by
    intro x hx hx0 hlt hκ
    obtain ⟨y', hy', e'⟩ := hcongr x hx 0 L.zero_mem hκ
    have h := eight_le_norm_sq_add_of_congr heven L.zero_mem hy' e' hx0 (by simpa using hx0)
    rw [norm_zero] at h
    norm_num at h
    linarith
  -- the classes of the roots
  have hI₂ : 120 ≤ (S₂.image κ).card := by
    have h := Finset.card_le_mul_card_image S₂ 2 (f := κ) (by
      intro c hc
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hc
      have hsub : S₂.filter (fun x => κ x = κ r) ⊆ {r, -r} := by
        intro x hx
        obtain ⟨hxS, hxκ⟩ := Finset.mem_filter.mp hx
        by_contra hnot
        rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        obtain ⟨y', hy', e'⟩ := hcongr x ((hS₂ x).mp hxS).1 r ((hS₂ r).mp hr).1 hxκ
        have h := eight_le_norm_sq_add_of_congr heven ((hS₂ r).mp hr).1 hy' e' hnot.1 hnot.2
        rw [((hS₂ x).mp hxS).2, ((hS₂ r).mp hr).2] at h
        norm_num at h
      exact (Finset.card_le_card hsub).trans Finset.card_le_two)
    rw [h2] at h
    omega
  -- the classes of the vectors of squared norm four avoid those of the roots and of zero
  have hdisj : Disjoint (S₂.image κ) (S₄.image κ) := by
    rw [Finset.disjoint_left]
    intro c hc2 hc4
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hc2
    obtain ⟨w, hw, hκ⟩ := Finset.mem_image.mp hc4
    obtain ⟨y', hy', e'⟩ := hcongr w ((hS₄ w).mp hw).1 r ((hS₂ r).mp hr).1 hκ
    have hne : w ≠ r := by
      intro h
      have h1 := ((hS₄ w).mp hw).2
      rw [h, ((hS₂ r).mp hr).2] at h1
      norm_num at h1
    have hne' : w ≠ -r := by
      intro h
      have h1 := ((hS₄ w).mp hw).2
      rw [h, norm_neg, ((hS₂ r).mp hr).2] at h1
      norm_num at h1
    have h := eight_le_norm_sq_add_of_congr heven ((hS₂ r).mp hr).1 hy' e' hne hne'
    rw [((hS₄ w).mp hw).2, ((hS₂ r).mp hr).2] at h
    norm_num at h
  have hκ0 : κ 0 ∉ S₂.image κ ∪ S₄.image κ := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨r, hr, hκ⟩ := Finset.mem_image.mp h
      have hr' := (hS₂ r).mp hr
      refine hzero r hr'.1 ?_ (by rw [hr'.2]; norm_num) hκ
      intro h0
      rw [h0, norm_zero] at hr'
      norm_num at hr'
    · obtain ⟨w, hw, hκ⟩ := Finset.mem_image.mp h
      have hw' := (hS₄ w).mp hw
      refine hzero w hw'.1 ?_ (by rw [hw'.2]; norm_num) hκ
      intro h0
      rw [h0, norm_zero] at hw'
      norm_num at hw'
  have hI₄ : (S₄.image κ).card ≤ 135 := by
    have hcard : Fintype.card (Fin 8 → ZMod 2) = 256 := by
      rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
      norm_num
    have h1 : (insert (κ 0) (S₂.image κ ∪ S₄.image κ)).card ≤ 256 := by
      rw [← hcard]
      exact Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem hκ0, Finset.card_union_of_disjoint hdisj] at h1
    omega
  -- a class with sixteen vectors of squared norm four
  obtain ⟨c, _, hc⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (s := S₄)
    (t := S₄.image κ) (f := κ) (n := 15) (fun x hx => Finset.mem_image_of_mem κ hx) (by
      rw [h4]
      omega)
  -- its vectors are pairwise equal, opposite or orthogonal
  have hF : ∀ x ∈ S₄.filter (fun x => κ x = c), ∀ y ∈ S₄.filter (fun x => κ x = c),
      x = y ∨ x = -y ∨ ⟪x, y⟫_ℝ = 0 := by
    intro x hx y hy
    obtain ⟨hxS, hxκ⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyS, hyκ⟩ := Finset.mem_filter.mp hy
    by_cases h1 : x = y
    · exact Or.inl h1
    · by_cases h2 : x = -y
      · exact Or.inr (Or.inl h2)
      · obtain ⟨y', hy', e'⟩ := hcongr x ((hS₄ x).mp hxS).1 y ((hS₄ y).mp hyS).1
          (hxκ.trans hyκ.symm)
        exact Or.inr (Or.inr (inner_eq_zero_of_congr heven ((hS₄ y).mp hyS).1 hy' e' h1 h2
          ((hS₄ x).mp hxS).2 ((hS₄ y).mp hyS).2))
  obtain ⟨T, hTsub, hTorth, hTcard⟩ := exists_orthogonal_subset _ _ rfl hF
  have hT8 : 8 ≤ T.card := by omega
  obtain ⟨T₈, hT₈sub, hT₈card⟩ := Finset.exists_subset_card_eq hT8
  let φ := (Finset.equivFinOfCardEq hT₈card).symm
  have hmem : ∀ i, (φ i : Ambient 8) ∈ S₄.filter (fun x => κ x = c) := fun i =>
    hTsub (hT₈sub (φ i).2)
  refine ⟨fun i => (φ i : Ambient 8), fun i => ?_, fun i => ?_, fun i j hij => ?_, fun i j => ?_⟩
  · exact ((hS₄ _).mp (Finset.mem_filter.mp (hmem i)).1).1
  · exact ((hS₄ _).mp (Finset.mem_filter.mp (hmem i)).1).2
  · refine hTorth _ (hT₈sub (φ i).2) _ (hT₈sub (φ j).2) fun h => hij ?_
    exact φ.injective (Subtype.ext h)
  · have hi := Finset.mem_filter.mp (hmem i)
    have hj := Finset.mem_filter.mp (hmem j)
    exact hcongr _ ((hS₄ _).mp hi.1).1 _ ((hS₄ _).mp hj.1).1 (hi.2.trans hj.2.symm)

/-- **`E8` from the numbers of short vectors.** An even, integral, self-dual subgroup of `ℝ⁸`
spanned by eight vectors, with `240` vectors of squared norm `2` and `2160` of squared norm `4`,
is an isometric copy of `e8Set`. -/
theorem exists_isometry_image_e8Set_eq_of_counts
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ m : ℤ, ⟪x, y⟫_ℝ = m)
    (heven : ∀ x ∈ L, ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k)
    (hdual : ∀ w : Ambient 8, (∀ x ∈ L, ∃ n : ℤ, ⟪w, x⟫_ℝ = n) → w ∈ L)
    (e : Fin 8 → Ambient 8) (he : ∀ i, e i ∈ L)
    (hspan : ∀ x ∈ L, ∃ a : Fin 8 → ℤ, x = ∑ i, a i • e i)
    (S₂ S₄ : Finset (Ambient 8)) (hS₂ : ∀ x, x ∈ S₂ ↔ x ∈ L ∧ ‖x‖ ^ 2 = 2)
    (hS₄ : ∀ x, x ∈ S₄ ↔ x ∈ L ∧ ‖x‖ ^ 2 = 4) (h2 : S₂.card = 240) (h4 : S₄.card = 2160) :
    ∃ Φ : Ambient 8 ≃ₗᵢ[ℝ] Ambient 8, Φ '' e8Set = (L : Set (Ambient 8)) := by
  obtain ⟨v, hv, hnorm, horth, hcong⟩ :=
    exists_normFourFrame_of_counts heven e he hspan S₂ S₄ hS₂ hS₄ h2 h4
  -- a vector with an odd inner product with the first frame vector
  have hhalf : ∃ x₀ ∈ L, ∃ m₀ : ℤ, ⟪v 0, x₀⟫_ℝ = m₀ ∧ ¬ (2 : ℤ) ∣ m₀ := by
    by_contra hnot
    have hall : ∀ x ∈ L, ∀ m : ℤ, ⟪v 0, x⟫_ℝ = m → (2 : ℤ) ∣ m := fun x hx m hm => by
      by_contra h
      exact hnot ⟨x, hx, m, hm, h⟩
    have hw : (1 / 2 : ℝ) • v 0 ∈ L := by
      refine hdual _ fun x hx => ?_
      obtain ⟨m, hm⟩ := hint (v 0) (hv 0) x hx
      obtain ⟨n, hn⟩ := hall x hx m hm
      refine ⟨n, ?_⟩
      rw [real_inner_smul_left, hm, hn]
      push_cast
      ring
    obtain ⟨k, hk⟩ := heven _ hw
    rw [norm_smul, mul_pow, hnorm 0] at hk
    norm_num at hk
    have h : ((1 : ℤ) : ℝ) = ((2 * k : ℤ) : ℝ) := by
      push_cast
      linarith
    have h' : (1 : ℤ) = 2 * k := by exact_mod_cast h
    omega
  obtain ⟨x₀, hx₀, m₀, hm₀, hodd⟩ := hhalf
  exact exists_isometry_image_e8Set_eq_of_frame hint heven v hv hnorm horth hcong hx₀ hm₀ hodd

end E8Leech
