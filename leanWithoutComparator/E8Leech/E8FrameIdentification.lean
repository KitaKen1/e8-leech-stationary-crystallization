import E8Leech.E8Lattice
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Identifying `E8` from an orthogonal frame of norm-four vectors

Let `L` be an even integral subgroup of `ℝ⁸`. Suppose `L` contains eight mutually orthogonal
vectors `v i` of squared norm `4` that are congruent modulo `2L`, and a vector with an odd inner
product with one of them. Then `L` is an isometric copy of the concrete set `e8Set`.

In the orthonormal frame `v i / 2` the subgroup contains the roots `±e_i ± e_j` of `D8`, every
vector has all coordinates in `ℤ` or all in `ℤ + 1/2`, and evenness forces an even coordinate sum
on the integer vectors. A vector of the second kind exists by hypothesis, so `L` is `D8` together
with one of its two half-integer cosets; changing the sign of one frame vector selects the coset
of `e8Set`. No determinant, covolume or classification of lattices is used.

* `int_two_dvd_sum_sq_iff`: a sum of integer squares is even exactly when the sum is.
* `mem_repr_symm_image_e8Set`: membership in the copy of `e8Set` in an orthonormal frame.
* `image_e8Set_eq_of_frame`: the identification for a frame with the right coset.
* `exists_isometry_image_e8Set_eq_of_frame`: the identification from the norm-four frame.
-/

noncomputable section

namespace E8Leech

open scoped InnerProductSpace
open Finset

/-- A sum of integer squares has the parity of the sum. -/
theorem int_two_dvd_sum_sq_iff {ι : Type*} (s : Finset ι) (c : ι → ℤ) :
    (2 : ℤ) ∣ ∑ i ∈ s, c i ^ 2 ↔ (2 : ℤ) ∣ ∑ i ∈ s, c i := by
  have h : (2 : ℤ) ∣ ∑ i ∈ s, (c i ^ 2 - c i) := by
    refine Finset.dvd_sum fun i _ => ?_
    have e : c i ^ 2 - c i = c i * (c i - 1) := by ring
    rw [e]
    exact (Int.even_mul_pred_self (c i)).two_dvd
  rw [Finset.sum_sub_distrib] at h
  constructor
  · intro h'
    have h'' := dvd_sub h' h
    rwa [sub_sub_cancel] at h''
  · intro h'
    have h'' := dvd_add h h'
    rwa [sub_add_cancel] at h''

/-- A vector lies in the copy of `e8Set` in the frame `b` exactly when its doubled coordinates
are admissible numerators. -/
theorem mem_repr_symm_image_e8Set (b : OrthonormalBasis (Fin 8) ℝ (Ambient 8)) (x : Ambient 8) :
    x ∈ b.repr.symm '' e8Set ↔ ∃ z ∈ e8Numerators, ∀ i, ⟪b i, x⟫_ℝ = (z i : ℝ) / 2 := by
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨z, hz, fun i => ?_⟩
    rw [← b.repr_apply_apply, LinearIsometryEquiv.apply_symm_apply]
    simp [halfCoordinates]
  · rintro ⟨z, hz, h⟩
    refine ⟨halfCoordinates z, ⟨z, hz, rfl⟩, ?_⟩
    apply b.repr.injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    ext i
    rw [b.repr_apply_apply, h i]
    simp [halfCoordinates]

/-- The squared norm in the doubled coordinates of an orthonormal frame. -/
theorem norm_sq_of_frame_coords (b : OrthonormalBasis (Fin 8) ℝ (Ambient 8)) {x : Ambient 8}
    {a : Fin 8 → ℝ} (ha : ∀ i, ⟪b i, x⟫_ℝ = a i) : ‖x‖ ^ 2 = ∑ i, a i ^ 2 := by
  have h := b.sum_inner_mul_inner x x
  rw [real_inner_self_eq_norm_sq] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : ⟪x, b i⟫_ℝ = ⟪b i, x⟫_ℝ := real_inner_comm _ _
  rw [e, ha i]
  ring

/-- **`E8` in a frame.** An even integral subgroup of `ℝ⁸` that contains the vectors
`b i ± b j` of an orthonormal frame and a vector with odd doubled coordinates of sum divisible by
four is the copy of `e8Set` in that frame. -/
theorem image_e8Set_eq_of_frame {L : AddSubgroup (Ambient 8)}
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ m : ℤ, ⟪x, y⟫_ℝ = m)
    (heven : ∀ x ∈ L, ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k)
    (b : OrthonormalBasis (Fin 8) ℝ (Ambient 8))
    (hadd : ∀ i j, i ≠ j → b i + b j ∈ L) (hsub : ∀ i j, i ≠ j → b i - b j ∈ L)
    {x₀ : Ambient 8} (hx₀ : x₀ ∈ L) {z₀ : Fin 8 → ℤ}
    (hz₀ : ∀ i, ⟪b i, x₀⟫_ℝ = (z₀ i : ℝ) / 2) (hodd : ¬ (2 : ℤ) ∣ z₀ 0)
    (hsum : (4 : ℤ) ∣ ∑ i, z₀ i) :
    b.repr.symm '' e8Set = (L : Set (Ambient 8)) := by
  -- twice a frame vector
  have h2 : ∀ i, b i + b i ∈ L := by
    intro i
    obtain ⟨j, hj⟩ := exists_ne i
    have h := L.add_mem (hadd i j hj.symm) (hsub i j hj.symm)
    have e : b i + b j + (b i - b j) = b i + b i := by abel
    rwa [e] at h
  -- differences of doubled coordinates of a lattice vector are even
  have hpar : ∀ x ∈ L, ∀ z : Fin 8 → ℤ, (∀ i, ⟪b i, x⟫_ℝ = (z i : ℝ) / 2) →
      ∀ i j, (2 : ℤ) ∣ z i - z j := by
    intro x hx z hz i j
    by_cases hij : i = j
    · subst hij
      simp
    · obtain ⟨m, hm⟩ := hint _ (hsub i j hij) x hx
      rw [inner_sub_left, hz i, hz j] at hm
      refine ⟨m, ?_⟩
      have h : ((z i - z j : ℤ) : ℝ) = ((2 * m : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast h
  -- a lattice vector with even doubled coordinates has coordinate sum divisible by four
  have hfour : ∀ x ∈ L, ∀ z : Fin 8 → ℤ, (∀ i, ⟪b i, x⟫_ℝ = (z i : ℝ) / 2) →
      (∀ i, (2 : ℤ) ∣ z i) → (4 : ℤ) ∣ ∑ i, z i := by
    intro x hx z hz hz2
    choose c hc using hz2
    obtain ⟨k, hk⟩ := heven x hx
    have hn : ‖x‖ ^ 2 = ∑ i, ((c i : ℤ) : ℝ) ^ 2 :=
      norm_sq_of_frame_coords b fun i => by
        rw [hz i, hc i]
        push_cast
        ring
    have hsq : ∑ i, c i ^ 2 = 2 * k := by
      have h : ((∑ i, c i ^ 2 : ℤ) : ℝ) = ((2 * k : ℤ) : ℝ) := by
        push_cast
        rw [← hn, hk]
      exact_mod_cast h
    obtain ⟨l, hl⟩ := (int_two_dvd_sum_sq_iff Finset.univ c).mp ⟨k, hsq⟩
    refine ⟨l, ?_⟩
    have e : ∑ i, z i = 2 * ∑ i, c i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => hc i
    rw [e, hl]
    ring
  -- vectors with integer coordinates of even sum lie in the subgroup
  have hD8 : ∀ c : Fin 8 → ℤ, (2 : ℤ) ∣ ∑ i, c i → ∑ i, c i • b i ∈ L := by
    intro c hc
    obtain ⟨k, hk⟩ := hc
    have e : ∑ i, c i • b i = ∑ i, c i • (b i - b 0) + k • (b 0 + b 0) := by
      have e1 : ∑ i, c i • (b i - b 0) = ∑ i, c i • b i - (∑ i, c i) • b 0 := by
        rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => smul_sub _ _ _
      have e2 : k • (b 0 + b 0) = (∑ i, c i) • b 0 := by
        rw [hk, smul_add, ← add_smul]
        congr 1
        ring
      rw [e1, e2, sub_add_cancel]
    rw [e]
    refine L.add_mem (L.sum_mem fun i _ => ?_) (L.zsmul_mem (h2 0) k)
    by_cases hi : i = 0
    · rw [hi, sub_self, smul_zero]
      exact L.zero_mem
    · exact L.zsmul_mem (hsub i 0 hi) (c i)
  -- a vector with integer coordinates of even sum lies in the subgroup
  have hmem : ∀ y : Ambient 8, ∀ c : Fin 8 → ℤ, (∀ i, ⟪b i, y⟫_ℝ = (c i : ℝ)) →
      (2 : ℤ) ∣ ∑ i, c i → y ∈ L := by
    intro y c hc hc2
    have e : y = ∑ i, c i • b i := by
      rw [← b.sum_repr' y]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc i, Int.cast_smul_eq_zsmul]
    rw [e]
    exact hD8 c hc2
  ext x
  rw [mem_repr_symm_image_e8Set]
  constructor
  · rintro ⟨z, hz, hx⟩
    by_cases h0 : (2 : ℤ) ∣ z 0
    · -- integer coordinates
      have hall : ∀ i, (2 : ℤ) ∣ z i := fun i => by
        have h := hz.1 i
        omega
      choose c hc using hall
      refine hmem x c (fun i => ?_) ?_
      · rw [hx i, hc i]
        push_cast
        ring
      · obtain ⟨l, hl⟩ := hz.2
        refine ⟨l, ?_⟩
        have e : ∑ i, z i = 2 * ∑ i, c i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => hc i
        rw [e] at hl
        linarith
    · -- half-integer coordinates: compare with the half vector
      have hall : ∀ i, (2 : ℤ) ∣ z i - z₀ i := fun i => by
        have h := hz.1 i
        have h' := hpar x₀ hx₀ z₀ hz₀ i 0
        have h'' := hodd
        omega
      choose c hc using hall
      have hy : x - x₀ ∈ L := by
        refine hmem (x - x₀) c (fun i => ?_) ?_
        · rw [inner_sub_right, hx i, hz₀ i]
          have h : ((z i - z₀ i : ℤ) : ℝ) = ((2 * c i : ℤ) : ℝ) := by rw [hc i]
          push_cast at h
          linarith
        · obtain ⟨l, hl⟩ := hz.2
          obtain ⟨l₀, hl₀⟩ := hsum
          refine ⟨l - l₀, ?_⟩
          have e : ∑ i, z i - ∑ i, z₀ i = 2 * ∑ i, c i := by
            rw [← Finset.sum_sub_distrib, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => hc i
          rw [hl, hl₀] at e
          linarith
      have h := L.add_mem hy hx₀
      rwa [sub_add_cancel] at h
  · intro hx
    -- integer doubled coordinates
    have hco : ∀ i, ∃ m : ℤ, ⟪b i, x⟫_ℝ = (m : ℝ) / 2 := by
      intro i
      obtain ⟨m, hm⟩ := hint _ (h2 i) x hx
      refine ⟨m, ?_⟩
      rw [inner_add_left] at hm
      linarith
    choose z hz using hco
    refine ⟨z, ⟨fun i => hpar x hx z hz i 0, ?_⟩, hz⟩
    by_cases h0 : (2 : ℤ) ∣ z 0
    · refine hfour x hx z hz fun i => ?_
      have h := hpar x hx z hz i 0
      omega
    · -- the difference with the half vector has even doubled coordinates
      have hw : ∀ i, ⟪b i, x - x₀⟫_ℝ = ((z i - z₀ i : ℤ) : ℝ) / 2 := by
        intro i
        rw [inner_sub_right, hz i, hz₀ i]
        push_cast
        ring
      have h4 := hfour (x - x₀) (L.sub_mem hx hx₀) (fun i => z i - z₀ i) hw fun i => by
        have h := hpar x hx z hz i 0
        have h' := hpar x₀ hx₀ z₀ hz₀ i 0
        have h'' := hodd
        omega
      rw [Finset.sum_sub_distrib] at h4
      have h5 := dvd_add h4 hsum
      rwa [sub_add_cancel] at h5

/-- The identification from a norm-four frame whose odd inner products with the half vector
have a sum divisible by four. -/
theorem image_e8Set_eq_of_normFourFrame {L : AddSubgroup (Ambient 8)}
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ m : ℤ, ⟪x, y⟫_ℝ = m)
    (heven : ∀ x ∈ L, ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k)
    (v : Fin 8 → Ambient 8) (hv : ∀ i, v i ∈ L) (hnorm : ∀ i, ‖v i‖ ^ 2 = 4)
    (horth : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ = 0)
    (hcong : ∀ i j, ∃ y ∈ L, v i - v j = y + y)
    {x₀ : Ambient 8} (hx₀ : x₀ ∈ L) {m : Fin 8 → ℤ} (hm : ∀ i, ⟪v i, x₀⟫_ℝ = m i)
    (hodd : ¬ (2 : ℤ) ∣ m 0) (hsum : (4 : ℤ) ∣ ∑ i, m i) :
    ∃ Φ : Ambient 8 ≃ₗᵢ[ℝ] Ambient 8, Φ '' e8Set = (L : Set (Ambient 8)) := by
  have hon : Orthonormal ℝ (fun i => (1 / 2 : ℝ) • v i) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [real_inner_smul_left, real_inner_smul_right]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, real_inner_self_eq_norm_sq, hnorm i]
      norm_num
    · rw [if_neg hij, horth i j hij]
      norm_num
  let b : OrthonormalBasis (Fin 8) ℝ (Ambient 8) :=
    (basisOfOrthonormalOfCardEqFinrank hon (by simp)).toOrthonormalBasis
      (by rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact hon)
  have hb : ∀ i, b i = (1 / 2 : ℝ) • v i := by
    intro i
    simp only [b, Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]
  refine ⟨b.repr.symm, image_e8Set_eq_of_frame hint heven b ?_ ?_ hx₀ (z₀ := m) ?_ hodd hsum⟩
  · intro i j _
    obtain ⟨y, hy, e⟩ := hcong i j
    have hvi : v i = y + y + v j := by rw [← e, sub_add_cancel]
    have h : b i + b j = y + v j := by
      rw [hb i, hb j, hvi]
      module
    rw [h]
    exact L.add_mem hy (hv j)
  · intro i j _
    obtain ⟨y, hy, e⟩ := hcong i j
    have h : b i - b j = y := by
      rw [hb i, hb j, ← smul_sub, e]
      module
    rw [h]
    exact hy
  · intro i
    rw [hb i, real_inner_smul_left, hm i]
    ring

/-- **`E8` from a norm-four frame.** An even integral subgroup of `ℝ⁸` with eight mutually
orthogonal vectors of squared norm `4`, congruent modulo `2L`, and a vector with an odd inner
product with the first of them is an isometric copy of `e8Set`. -/
theorem exists_isometry_image_e8Set_eq_of_frame {L : AddSubgroup (Ambient 8)}
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ m : ℤ, ⟪x, y⟫_ℝ = m)
    (heven : ∀ x ∈ L, ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k)
    (v : Fin 8 → Ambient 8) (hv : ∀ i, v i ∈ L) (hnorm : ∀ i, ‖v i‖ ^ 2 = 4)
    (horth : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ = 0)
    (hcong : ∀ i j, ∃ y ∈ L, v i - v j = y + y)
    {x₀ : Ambient 8} (hx₀ : x₀ ∈ L) {m₀ : ℤ} (hm₀ : ⟪v 0, x₀⟫_ℝ = m₀)
    (hodd : ¬ (2 : ℤ) ∣ m₀) :
    ∃ Φ : Ambient 8 ≃ₗᵢ[ℝ] Ambient 8, Φ '' e8Set = (L : Set (Ambient 8)) := by
  -- integer inner products with the frame
  choose m hm using fun i => hint (v i) (hv i) x₀ hx₀
  have hm0 : m 0 = m₀ := by
    have h : ((m 0 : ℤ) : ℝ) = (m₀ : ℝ) := by rw [← hm 0, hm₀]
    exact_mod_cast h
  have hodd0 : ¬ (2 : ℤ) ∣ m 0 := by rwa [hm0]
  -- all of them have the parity of the first
  have hpar : ∀ i, (2 : ℤ) ∣ m i - m 0 := by
    intro i
    obtain ⟨y, hy, e⟩ := hcong i 0
    obtain ⟨n, hn⟩ := hint y hy x₀ hx₀
    refine ⟨n, ?_⟩
    have h : ⟪v i - v 0, x₀⟫_ℝ = ⟪y + y, x₀⟫_ℝ := by rw [e]
    rw [inner_sub_left, inner_add_left, hm i, hm 0, hn] at h
    have h' : ((m i - m 0 : ℤ) : ℝ) = ((2 * n : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h'
  have hsum2 : (2 : ℤ) ∣ ∑ i, m i := by
    have e : ∑ i, m i = ∑ i, (m i - m 0) + 8 * m 0 := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    rw [e]
    exact dvd_add (Finset.dvd_sum fun i _ => hpar i) ⟨4 * m 0, by ring⟩
  by_cases h4 : (4 : ℤ) ∣ ∑ i, m i
  · exact image_e8Set_eq_of_normFourFrame hint heven v hv hnorm horth hcong hx₀ hm hodd0 h4
  · -- change the sign of the first frame vector
    obtain ⟨v', hv0, hvi⟩ : ∃ v' : Fin 8 → Ambient 8, v' 0 = -v 0 ∧ ∀ i, i ≠ 0 → v' i = v i :=
      ⟨fun i => if i = 0 then -v 0 else v i, by simp, fun i hi => by simp [hi]⟩
    obtain ⟨m', hm0', hmi⟩ : ∃ m' : Fin 8 → ℤ, m' 0 = -m 0 ∧ ∀ i, i ≠ 0 → m' i = m i :=
      ⟨fun i => if i = 0 then -m 0 else m i, by simp, fun i hi => by simp [hi]⟩
    refine image_e8Set_eq_of_normFourFrame hint heven v' ?_ ?_ ?_ ?_ hx₀ (m := m') ?_ ?_ ?_
    · intro i
      rcases eq_or_ne i 0 with rfl | hi
      · rw [hv0]
        exact L.neg_mem (hv 0)
      · rw [hvi i hi]
        exact hv i
    · intro i
      rcases eq_or_ne i 0 with rfl | hi
      · rw [hv0, norm_neg]
        exact hnorm 0
      · rw [hvi i hi]
        exact hnorm i
    · intro i j hij
      rcases eq_or_ne i 0 with rfl | hi
      · rw [hv0, hvi j hij.symm, inner_neg_left, horth 0 j hij, neg_zero]
      · rcases eq_or_ne j 0 with rfl | hj
        · rw [hv0, hvi i hi, inner_neg_right, horth i 0 hij, neg_zero]
        · rw [hvi i hi, hvi j hj]
          exact horth i j hij
    · intro i j
      rcases eq_or_ne i 0 with rfl | hi
      · rcases eq_or_ne j 0 with rfl | hj
        · exact ⟨0, L.zero_mem, by simp⟩
        · obtain ⟨y, hy, e⟩ := hcong 0 j
          refine ⟨-(y + v j), L.neg_mem (L.add_mem hy (hv j)), ?_⟩
          have h0 : v 0 = y + y + v j := by rw [← e, sub_add_cancel]
          rw [hv0, hvi j hj, h0]
          abel
      · rcases eq_or_ne j 0 with rfl | hj
        · obtain ⟨y, hy, e⟩ := hcong i 0
          refine ⟨y + v 0, L.add_mem hy (hv 0), ?_⟩
          have h0 : v i = y + y + v 0 := by rw [← e, sub_add_cancel]
          rw [hv0, hvi i hi, h0]
          abel
        · rw [hvi i hi, hvi j hj]
          exact hcong i j
    · intro i
      rcases eq_or_ne i 0 with rfl | hi
      · rw [hv0, hm0', inner_neg_left, hm 0]
        exact (Int.cast_neg _).symm
      · rw [hvi i hi, hmi i hi]
        exact hm i
    · rw [hm0', dvd_neg]
      exact hodd0
    · have e : ∑ i, m' i = ∑ i, m i - 2 * m 0 := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ (f := m), hm0']
        have h : ∀ i : Fin 7, m' i.succ = m i.succ := fun i => hmi _ (Fin.succ_ne_zero i)
        simp only [h]
        ring
      rw [e]
      omega

end E8Leech
