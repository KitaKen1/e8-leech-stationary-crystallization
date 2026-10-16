import E8Leech.E8LocalCount
import E8Leech.LeechPackingInput
import E8Leech.LeechBasis

/-!
# The number of points of a `2`-separated set in a ball of `ℝ²⁴`

The rank 24 version of `E8LocalCount`. A finite `2`-separated set `W` in a ball of radius `R` has
at most

`vol(B_{R+2+ρ}) + (2R+4)²⁴ - (2R+2-2ρ)²⁴`

points, where `ρ` is the sum of the norms of the basis vectors of the Leech lattice
(`leech_card_window_le`). The error is of relative order `1/R`.

Proof: put the ball in a cube of side `2R+2` and add all points of the Leech lattice in the cube
at distance at least `R+2` from the centre. The union is `2`-separated, so the Cohn–Elkies bound in
dimension 24 in the guard-box form (`leech_guardDensity_le_one`) bounds it by `(2R+4)²⁴`. The Leech
lattice has at least `(2R+2-2ρ)²⁴` points in the cube and at most `vol(B_{R+2+ρ})` in the ball of
radius `R+2`.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

/-- The sum of the norms of the basis vectors of the Leech lattice. -/
def leechBasisNormSum : ℝ := ∑ i, ‖leechEuclideanBasis i‖

theorem leechBasisNormSum_nonneg : 0 ≤ leechBasisNormSum :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- Points of the Leech lattice in a ball. -/
theorem card_leech_ball_le (T : Finset (Ambient 24)) (hT : ∀ t ∈ T, t ∈ leechSet)
    {c : Ambient 24} {R : ℝ} (hball : ∀ t ∈ T, t ∈ closedBall c R) :
    (T.card : ℝ) ≤ volume.real (closedBall c (R + leechBasisNormSum)) := by
  have h := card_mul_covolume_le leechEuclideanBasis leechLattice leechLattice_eq_span.ge T
    (fun t ht => by
      rw [← SetLike.mem_coe, coe_leechLattice]
      exact hT t ht) hball
  rw [leechLattice_covolume, mul_one] at h
  exact h

/-- Points of the Leech lattice in a set, from below. -/
theorem volume_le_card_leech (T : Finset (Ambient 24)) {A A' : Set (Ambient 24)}
    (hT : ∀ x ∈ leechSet, x ∈ A → x ∈ T)
    (hA : ∀ y ∈ A', closedBall y leechBasisNormSum ⊆ A) :
    volume A' ≤ (T.card : ℝ≥0∞) := by
  have h := volume_le_card_mul_volume_fundamentalDomain leechEuclideanBasis T (A := A) (A' := A')
    (fun x hx hxA => hT x (by
      rw [← coe_leechLattice, leechLattice_eq_span]
      exact hx) hxA) hA
  rwa [volume_leechFundamentalDomain, mul_one] at h

/-- **The cube bound for a finite set** in dimension 24: the Cohn–Elkies bound in guard-box
form. -/
theorem card_le_of_separated_in_leechGuardBox (T : Finset (Ambient 24)) {L : ℝ} (hL : 2 < L)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → 2 ≤ dist x y)
    (hbox : ∀ x ∈ T, x ∈ guardInnerBox 24 L 2) : (T.card : ℝ) ≤ L ^ 24 := by
  have hL0 : 0 < L := lt_trans (by norm_num) hL
  have h := leech_guardDensity_le_one
    ⟨(T : Set (Ambient 24)), fun K _ => T.finite_toSet.subset Set.inter_subset_left⟩ L hL
    (fun x hx y hy hne => hsep x hx y hy hne)
  have hcount : (⟨(T : Set (Ambient 24)),
      fun K _ => T.finite_toSet.subset Set.inter_subset_left⟩ :
      Configuration (Ambient 24)).count (guardInnerBox 24 L 2) = (T.card : ℝ≥0∞) := by
    rw [Configuration.count_eq_encard]
    have e : (T : Set (Ambient 24)) ∩ guardInnerBox 24 L 2 = (T : Set (Ambient 24)) :=
      Set.inter_eq_left.mpr fun x hx => hbox x hx
    rw [e, Set.encard_coe_eq_coe_finsetCard]
    rfl
  rw [guardDensity, hcount] at h
  have hne : ENNReal.ofReal L ^ 24 ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr hL0).ne'
  have hnt : ENNReal.ofReal L ^ 24 ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have h1 : (T.card : ℝ≥0∞) ≤ ENNReal.ofReal L ^ 24 := by
    have h2 := (ENNReal.div_le_iff hne hnt).mp h
    rwa [one_mul] at h2
  have h3 := ENNReal.toReal_mono hnt h1
  rw [ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofReal hL0.le] at h3
  exact h3

/-- **Points of a `2`-separated set in a ball of `ℝ²⁴`**, with an error of relative order
`1/R`. -/
theorem leech_card_window_le {S : Set (Ambient 24)}
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 2 ≤ dist x y) {u : Ambient 24} {R : ℝ}
    (hR : leechBasisNormSum ≤ R) (W : Finset (Ambient 24)) (hWS : ∀ x ∈ W, x ∈ S)
    (hWball : ∀ x ∈ W, x ∈ closedBall u R) :
    (W.card : ℝ) ≤
      volume.real (closedBall (0 : Ambient 24) (R + 2 + leechBasisNormSum)) +
        ((2 * R + 4) ^ 24 - (2 * R + 2 - 2 * leechBasisNormSum) ^ 24) := by
  classical
  have hρ0 := leechBasisNormSum_nonneg
  have hR0 : 0 ≤ R := hρ0.trans hR
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 2 * (R + 1) + 2 := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Ambient 24, ∀ i, c₀ i = 2 / 2 + (R + 1) :=
    ⟨WithLp.toLp 2 fun _ => 2 / 2 + (R + 1), fun _ => rfl⟩
  have hLs : 2 < L := by
    rw [hL]
    linarith
  -- a ball of radius `R` around `c₀` lies in the guard box
  have hballbox : ∀ z : Ambient 24, dist z c₀ ≤ R → z ∈ guardInnerBox 24 L 2 := by
    intro z hz i
    rw [dist_eq_norm] at hz
    have h1 := abs_le.mp ((abs_coord_sub_le z c₀ i).trans hz)
    rw [hc₀] at h1
    refine ⟨by linarith [h1.1], ?_⟩
    rw [hL]
    linarith [h1.2]
  -- the guard box is bounded
  have hboxbdd : ∀ z ∈ guardInnerBox 24 L 2, dist z c₀ ≤ 24 * (R + 1) := by
    intro z hz
    rw [dist_eq_norm]
    refine (norm_le_sum_abs_coord (z - c₀)).trans ?_
    calc ∑ i, |(z - c₀) i| ≤ ∑ _i : Fin 24, (R + 1) := Finset.sum_le_sum fun i _ => by
          have h := hz i
          rw [hL] at h
          rw [PiLp.sub_apply, hc₀, abs_le]
          exact ⟨by linarith [h.1], by linarith [h.2]⟩
      _ = 24 * (R + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
  -- the points of the Leech lattice in the guard box
  have hfinE : (leechSet ∩ closedBall c₀ (24 * (R + 1))).Finite :=
    leechSet_inter_compact_finite (isCompact_closedBall _ _)
  obtain ⟨Eall, hEall_mem⟩ : ∃ Eall : Finset (Ambient 24),
      ∀ z, z ∈ Eall ↔ z ∈ leechSet ∧ z ∈ guardInnerBox 24 L 2 := by
    refine ⟨hfinE.toFinset.filter fun z => z ∈ guardInnerBox 24 L 2, fun z => ?_⟩
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, mem_closedBall.mpr (hboxbdd z h2)⟩, h2⟩
  have hEcard : (Eall.filter fun z => R + 2 ≤ dist z c₀).card +
      (Eall.filter fun z => ¬ (R + 2 ≤ dist z c₀)).card = Eall.card :=
    Finset.card_filter_add_card_filter_not _
  -- the translated window
  have hW'card : (W.image fun x => x + (c₀ - u)).card = W.card :=
    Finset.card_image_of_injective _ (add_left_injective _)
  have hW'dist : ∀ y ∈ W.image (fun x => x + (c₀ - u)),
      ∃ x ∈ W, y = x + (c₀ - u) ∧ dist y c₀ ≤ R := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    refine ⟨x, hx, rfl, ?_⟩
    have h := hWball x hx
    rw [mem_closedBall, dist_eq_norm] at h
    rw [dist_eq_norm]
    have e : x + (c₀ - u) - c₀ = x - u := by abel
    rw [e]
    exact h
  have hdisj : Disjoint (W.image fun x => x + (c₀ - u))
      (Eall.filter fun z => R + 2 ≤ dist z c₀) := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨_, _, _, hd⟩ := hW'dist y hy
    have h2 := (Finset.mem_filter.mp hy').2
    linarith
  have hTcard : ((W.image fun x => x + (c₀ - u)) ∪
      (Eall.filter fun z => R + 2 ≤ dist z c₀)).card =
      W.card + (Eall.filter fun z => R + 2 ≤ dist z c₀).card := by
    rw [Finset.card_union_of_disjoint hdisj, hW'card]
  -- the union is separated and lies in the guard box
  have hTsep : ∀ x ∈ (W.image fun x => x + (c₀ - u)) ∪
      (Eall.filter fun z => R + 2 ≤ dist z c₀),
      ∀ y ∈ (W.image fun x => x + (c₀ - u)) ∪
        (Eall.filter fun z => R + 2 ≤ dist z c₀),
      x ≠ y → 2 ≤ dist x y := by
    intro x hx y hy hne
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨a, ha, rfl, _⟩ := hW'dist x hx
        obtain ⟨b, hb, rfl, _⟩ := hW'dist y hy
        have hab : a ≠ b := fun e => hne (by rw [e])
        rw [dist_add_right]
        exact hsep a (hWS a ha) b (hWS b hb) hab
      · obtain ⟨_, _, _, hd⟩ := hW'dist x hx
        have h2 := (Finset.mem_filter.mp hy).2
        have h3 := dist_triangle y x c₀
        rw [dist_comm y x] at h3
        linarith
    · rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨_, _, _, hd⟩ := hW'dist y hy
        have h2 := (Finset.mem_filter.mp hx).2
        have h3 := dist_triangle x y c₀
        linarith
      · exact leechSet_separated ((hEall_mem x).mp (Finset.mem_filter.mp hx).1).1
          ((hEall_mem y).mp (Finset.mem_filter.mp hy).1).1 hne
  have hTbox : ∀ x ∈ (W.image fun x => x + (c₀ - u)) ∪
      (Eall.filter fun z => R + 2 ≤ dist z c₀),
      x ∈ guardInnerBox 24 L 2 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨_, _, _, hd⟩ := hW'dist x hx
      exact hballbox x hd
    · exact ((hEall_mem x).mp (Finset.mem_filter.mp hx).1).2
  have hT := card_le_of_separated_in_leechGuardBox _ hLs hTsep hTbox
  -- the points of the Leech lattice near the centre, and all its points in the box
  have hEin_le : ((Eall.filter fun z => ¬ (R + 2 ≤ dist z c₀)).card : ℝ) ≤
      volume.real (closedBall c₀ (R + 2 + leechBasisNormSum)) := by
    refine card_leech_ball_le _ (fun t ht => ((hEall_mem t).mp (Finset.mem_filter.mp ht).1).1)
      fun t ht => ?_
    exact mem_closedBall.mpr (le_of_lt (not_le.mp (Finset.mem_filter.mp ht).2))
  have hEall_ge : (2 * R + 2 - 2 * leechBasisNormSum) ^ 24 ≤ (Eall.card : ℝ) := by
    have h := volume_le_card_leech Eall (A := guardInnerBox 24 L 2)
      (A' := coordinateBox 24 (2 / 2 + leechBasisNormSum) (L - 2 / 2 - leechBasisNormSum))
      (fun x hx hxA => (hEall_mem x).mpr ⟨hx, hxA⟩)
      (fun y hy => closedBall_subset_coordinateBox hy)
    rw [volume_coordinateBox] at h
    have hside : L - 2 / 2 - leechBasisNormSum - (2 / 2 + leechBasisNormSum) =
        2 * R + 2 - 2 * leechBasisNormSum := by
      rw [hL]
      ring
    rw [hside] at h
    have hnn : 0 ≤ 2 * R + 2 - 2 * leechBasisNormSum := by linarith
    have h2 := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) h
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hnn, ENNReal.toReal_natCast] at h2
    exact h2
  have hball0 : volume.real (closedBall c₀ (R + 2 + leechBasisNormSum)) =
      volume.real (closedBall (0 : Ambient 24) (R + 2 + leechBasisNormSum)) := by
    rw [measureReal_def, Measure.addHaar_closedBall_center, ← measureReal_def]
  rw [hTcard, hL] at hT
  have hcast : ((W.card + (Eall.filter fun z => R + 2 ≤ dist z c₀).card : ℕ) : ℝ) =
      (W.card : ℝ) + ((Eall.filter fun z => R + 2 ≤ dist z c₀).card : ℝ) := by
    push_cast
    ring
  have hEc : ((Eall.filter fun z => R + 2 ≤ dist z c₀).card : ℝ) +
      ((Eall.filter fun z => ¬ (R + 2 ≤ dist z c₀)).card : ℝ) = (Eall.card : ℝ) := by
    exact_mod_cast hEcard
  have e24 : (2 * (R + 1) + 2) ^ 24 = (2 * R + 4) ^ 24 := by ring
  rw [hcast, e24] at hT
  rw [hball0] at hEin_le
  linarith

end E8Leech
