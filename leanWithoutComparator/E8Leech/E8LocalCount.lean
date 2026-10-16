import E8Leech.LatticePointCount
import E8Leech.E8PackingInput
import E8Leech.E8Lattice
import E8Leech.E8Geometry

/-!
# The number of points of a `√2`-separated set in a ball of `ℝ⁸`

A finite `√2`-separated set `W` in a ball of radius `R` has at most

`vol(B_{R+√2+ρ}) + (2R+2+√2)⁸ - (2R+2-2ρ)⁸`

points, where `ρ` is the sum of the norms of the basis vectors of `E8` (`card_window_le`). The
error is of relative order `1/R`, which is what the lower bound for most observation centres
needs (Lemma 4.1 of Böröczky–Radchenko–Ramos gives `vol(B_{R+√2})`; their proof uses a theorem
on finite packings that is not available here).

Proof: put the ball in a cube of side `2R+2` and add all points of `E8` in the cube at distance at
least `R+√2` from the centre. The union is `√2`-separated, so Viazovska's bound in the guard-box
form (`e8_guardDensity_le_one`) bounds it by `(2R+2+√2)⁸`. The lattice `E8` has at least
`(2R+2-2ρ)⁸` points in the cube and at most `vol(B_{R+√2+ρ})` in the ball of radius `R+√2`.

* `volume_le_card_mul_volume_fundamentalDomain`: lattice points in a set, lower bound.
* `card_le_of_separated_in_guardBox`: the cube bound for a finite set.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

/-- The translates of the fundamental parallelepiped by the lattice points of a set cover the
points whose ball of radius `∑ |bᵢ|` lies in the set. -/
theorem volume_le_card_mul_volume_fundamentalDomain {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (Ambient d)) (T : Finset (Ambient d)) {A A' : Set (Ambient d)}
    (hT : ∀ x ∈ Submodule.span ℤ (Set.range b), x ∈ A → x ∈ T)
    (hA : ∀ y ∈ A', closedBall y (∑ i, ‖b i‖) ⊆ A) :
    volume A' ≤ (T.card : ℝ≥0∞) * volume (ZSpan.fundamentalDomain b) := by
  have hsub : A' ⊆ ⋃ t ∈ T, t +ᵥ ZSpan.fundamentalDomain b := by
    intro y hy
    obtain ⟨v, hv, _⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b y
    have hv' : (v : Ambient d) + y ∈ ZSpan.fundamentalDomain b := hv
    have hn : ‖(v : Ambient d) + y‖ ≤ ∑ i, ‖b i‖ := by
      have h := ZSpan.norm_fract_le (K := ℝ) b ((v : Ambient d) + y)
      rwa [ZSpan.fract_eq_self.mpr hv'] at h
    have hx : -(v : Ambient d) ∈ A := by
      apply hA y hy
      rw [mem_closedBall, dist_eq_norm]
      have e : -(v : Ambient d) - y = -((v : Ambient d) + y) := by abel
      rw [e, norm_neg]
      exact hn
    have hxT : -(v : Ambient d) ∈ T := hT _ (Submodule.neg_mem _ v.2) hx
    simp only [Set.mem_iUnion]
    refine ⟨-(v : Ambient d), hxT, (v : Ambient d) + y, hv', ?_⟩
    show -(v : Ambient d) + ((v : Ambient d) + y) = y
    abel
  calc volume A' ≤ volume (⋃ t ∈ T, t +ᵥ ZSpan.fundamentalDomain b) := measure_mono hsub
    _ ≤ ∑ t ∈ T, volume (t +ᵥ ZSpan.fundamentalDomain b) := measure_biUnion_finset_le _ _
    _ = (T.card : ℝ≥0∞) * volume (ZSpan.fundamentalDomain b) := by
        rw [Finset.sum_congr rfl fun t _ => measure_vadd volume t (ZSpan.fundamentalDomain b),
          Finset.sum_const, nsmul_eq_mul]

/-- The sum of the norms of the basis vectors of `E8`. -/
def e8BasisNormSum : ℝ := ∑ i, ‖e8EuclideanBasis i‖

theorem e8BasisNormSum_nonneg : 0 ≤ e8BasisNormSum :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- Points of `E8` in a ball. -/
theorem card_e8_ball_le (T : Finset (Ambient 8)) (hT : ∀ t ∈ T, t ∈ e8Set) {c : Ambient 8}
    {R : ℝ} (hball : ∀ t ∈ T, t ∈ closedBall c R) :
    (T.card : ℝ) ≤ volume.real (closedBall c (R + e8BasisNormSum)) := by
  have h := card_mul_covolume_le e8EuclideanBasis e8Lattice le_rfl T
    (fun t ht => by
      rw [← SetLike.mem_coe, coe_e8Lattice]
      exact hT t ht) hball
  rw [e8Lattice_covolume, mul_one] at h
  exact h

/-- Points of `E8` in a set, from below. -/
theorem volume_le_card_e8 (T : Finset (Ambient 8)) {A A' : Set (Ambient 8)}
    (hT : ∀ x ∈ e8Set, x ∈ A → x ∈ T) (hA : ∀ y ∈ A', closedBall y e8BasisNormSum ⊆ A) :
    volume A' ≤ (T.card : ℝ≥0∞) := by
  have h := volume_le_card_mul_volume_fundamentalDomain e8EuclideanBasis T (A := A) (A' := A')
    (fun x hx hxA => hT x (by
      rw [← coe_e8Lattice]
      exact hx) hxA) hA
  rwa [volume_e8FundamentalDomain, mul_one] at h

theorem norm_le_sum_abs_coord {d : ℕ} (x : Ambient d) : ‖x‖ ≤ ∑ i, |x i| := by
  have e : ∑ i, x i • EuclideanSpace.basisFun (Fin d) ℝ i = x :=
    (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x
  calc ‖x‖ = ‖∑ i, x i • EuclideanSpace.basisFun (Fin d) ℝ i‖ := by rw [e]
    _ ≤ ∑ i, ‖x i • EuclideanSpace.basisFun (Fin d) ℝ i‖ := norm_sum_le _ _
    _ = ∑ i, |x i| := Finset.sum_congr rfl fun i _ => by
        rw [norm_smul, (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.1 i, mul_one,
          Real.norm_eq_abs]

theorem abs_coord_sub_le {d : ℕ} (z y : Ambient d) (i : Fin d) : |z i - y i| ≤ ‖z - y‖ := by
  have h := PiLp.norm_apply_le (z - y) i
  rwa [PiLp.sub_apply, Real.norm_eq_abs] at h

theorem closedBall_subset_coordinateBox {d : ℕ} {lo hi ρ : ℝ} {y : Ambient d}
    (hy : y ∈ coordinateBox d (lo + ρ) (hi - ρ)) : closedBall y ρ ⊆ coordinateBox d lo hi := by
  intro z hz i
  rw [mem_closedBall, dist_eq_norm] at hz
  have h1 := abs_le.mp ((abs_coord_sub_le z y i).trans hz)
  have h2 := hy i
  exact ⟨by linarith [h2.1, h1.1], by linarith [h2.2, h1.2]⟩

/-- **The cube bound for a finite set**: Viazovska's theorem in guard-box form. -/
theorem card_le_of_separated_in_guardBox (T : Finset (Ambient 8)) {L : ℝ}
    (hL : Real.sqrt 2 < L)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → Real.sqrt 2 ≤ dist x y)
    (hbox : ∀ x ∈ T, x ∈ guardInnerBox 8 L (Real.sqrt 2)) : (T.card : ℝ) ≤ L ^ 8 := by
  have hL0 : 0 < L := lt_trans (Real.sqrt_pos.mpr (by norm_num)) hL
  have h := e8_guardDensity_le_one
    ⟨(T : Set (Ambient 8)), fun K _ => T.finite_toSet.subset Set.inter_subset_left⟩ L hL
    (fun x hx y hy hne => hsep x hx y hy hne)
  have hcount : (⟨(T : Set (Ambient 8)), fun K _ => T.finite_toSet.subset Set.inter_subset_left⟩ :
      Configuration (Ambient 8)).count (guardInnerBox 8 L (Real.sqrt 2)) = (T.card : ℝ≥0∞) := by
    rw [Configuration.count_eq_encard]
    have e : (T : Set (Ambient 8)) ∩ guardInnerBox 8 L (Real.sqrt 2) = (T : Set (Ambient 8)) :=
      Set.inter_eq_left.mpr fun x hx => hbox x hx
    rw [e, Set.encard_coe_eq_coe_finsetCard]
    rfl
  rw [guardDensity, hcount] at h
  have hne : ENNReal.ofReal L ^ 8 ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr hL0).ne'
  have hnt : ENNReal.ofReal L ^ 8 ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have h1 : (T.card : ℝ≥0∞) ≤ ENNReal.ofReal L ^ 8 := by
    have h2 := (ENNReal.div_le_iff hne hnt).mp h
    rwa [one_mul] at h2
  have h3 := ENNReal.toReal_mono hnt h1
  rw [ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofReal hL0.le] at h3
  exact h3

/-- **Points of a `√2`-separated set in a ball of `ℝ⁸`**, with an error of relative order
`1/R`. -/
theorem card_window_le {S : Set (Ambient 8)}
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Real.sqrt 2 ≤ dist x y) {u : Ambient 8} {R : ℝ}
    (hR : e8BasisNormSum ≤ R) (W : Finset (Ambient 8)) (hWS : ∀ x ∈ W, x ∈ S)
    (hWball : ∀ x ∈ W, x ∈ closedBall u R) :
    (W.card : ℝ) ≤
      volume.real (closedBall (0 : Ambient 8) (R + Real.sqrt 2 + e8BasisNormSum)) +
        ((2 * R + 2 + Real.sqrt 2) ^ 8 - (2 * R + 2 - 2 * e8BasisNormSum) ^ 8) := by
  classical
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hρ0 := e8BasisNormSum_nonneg
  have hR0 : 0 ≤ R := hρ0.trans hR
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 2 * (R + 1) + Real.sqrt 2 := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Ambient 8, ∀ i, c₀ i = Real.sqrt 2 / 2 + (R + 1) :=
    ⟨WithLp.toLp 2 fun _ => Real.sqrt 2 / 2 + (R + 1), fun _ => rfl⟩
  have hLs : Real.sqrt 2 < L := by
    rw [hL]
    linarith
  -- a ball of radius `R` around `c₀` lies in the guard box
  have hballbox : ∀ z : Ambient 8, dist z c₀ ≤ R → z ∈ guardInnerBox 8 L (Real.sqrt 2) := by
    intro z hz i
    rw [dist_eq_norm] at hz
    have h1 := abs_le.mp ((abs_coord_sub_le z c₀ i).trans hz)
    rw [hc₀] at h1
    refine ⟨by linarith [h1.1], ?_⟩
    rw [hL]
    linarith [h1.2]
  -- the guard box is bounded
  have hboxbdd : ∀ z ∈ guardInnerBox 8 L (Real.sqrt 2), dist z c₀ ≤ 8 * (R + 1) := by
    intro z hz
    rw [dist_eq_norm]
    refine (norm_le_sum_abs_coord (z - c₀)).trans ?_
    calc ∑ i, |(z - c₀) i| ≤ ∑ _i : Fin 8, (R + 1) := Finset.sum_le_sum fun i _ => by
          have h := hz i
          rw [hL] at h
          rw [PiLp.sub_apply, hc₀, abs_le]
          exact ⟨by linarith [h.1], by linarith [h.2]⟩
      _ = 8 * (R + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
  -- the points of `E8` in the guard box
  have hfinE : (e8Set ∩ closedBall c₀ (8 * (R + 1))).Finite :=
    e8Set_inter_compact_finite (isCompact_closedBall _ _)
  obtain ⟨Eall, hEall_mem⟩ : ∃ Eall : Finset (Ambient 8),
      ∀ z, z ∈ Eall ↔ z ∈ e8Set ∧ z ∈ guardInnerBox 8 L (Real.sqrt 2) := by
    refine ⟨hfinE.toFinset.filter fun z => z ∈ guardInnerBox 8 L (Real.sqrt 2), fun z => ?_⟩
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, mem_closedBall.mpr (hboxbdd z h2)⟩, h2⟩
  have hEcard : (Eall.filter fun z => R + Real.sqrt 2 ≤ dist z c₀).card +
      (Eall.filter fun z => ¬ (R + Real.sqrt 2 ≤ dist z c₀)).card = Eall.card :=
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
      (Eall.filter fun z => R + Real.sqrt 2 ≤ dist z c₀) := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨_, _, _, hd⟩ := hW'dist y hy
    have h2 := (Finset.mem_filter.mp hy').2
    linarith
  have hTcard : ((W.image fun x => x + (c₀ - u)) ∪
      (Eall.filter fun z => R + Real.sqrt 2 ≤ dist z c₀)).card =
      W.card + (Eall.filter fun z => R + Real.sqrt 2 ≤ dist z c₀).card := by
    rw [Finset.card_union_of_disjoint hdisj, hW'card]
  -- the union is separated and lies in the guard box
  have hTsep : ∀ x ∈ (W.image fun x => x + (c₀ - u)) ∪
      (Eall.filter fun z => R + Real.sqrt 2 ≤ dist z c₀),
      ∀ y ∈ (W.image fun x => x + (c₀ - u)) ∪
        (Eall.filter fun z => R + Real.sqrt 2 ≤ dist z c₀),
      x ≠ y → Real.sqrt 2 ≤ dist x y := by
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
      · exact e8Set_separated ((hEall_mem x).mp (Finset.mem_filter.mp hx).1).1
          ((hEall_mem y).mp (Finset.mem_filter.mp hy).1).1 hne
  have hTbox : ∀ x ∈ (W.image fun x => x + (c₀ - u)) ∪
      (Eall.filter fun z => R + Real.sqrt 2 ≤ dist z c₀),
      x ∈ guardInnerBox 8 L (Real.sqrt 2) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨_, _, _, hd⟩ := hW'dist x hx
      exact hballbox x hd
    · exact ((hEall_mem x).mp (Finset.mem_filter.mp hx).1).2
  have hT := card_le_of_separated_in_guardBox _ hLs hTsep hTbox
  -- the points of `E8` near the centre, and all points of `E8` in the box
  have hEin_le : ((Eall.filter fun z => ¬ (R + Real.sqrt 2 ≤ dist z c₀)).card : ℝ) ≤
      volume.real (closedBall c₀ (R + Real.sqrt 2 + e8BasisNormSum)) := by
    refine card_e8_ball_le _ (fun t ht => ((hEall_mem t).mp (Finset.mem_filter.mp ht).1).1)
      fun t ht => ?_
    exact mem_closedBall.mpr (le_of_lt (not_le.mp (Finset.mem_filter.mp ht).2))
  have hEall_ge : (2 * R + 2 - 2 * e8BasisNormSum) ^ 8 ≤ (Eall.card : ℝ) := by
    have h := volume_le_card_e8 Eall (A := guardInnerBox 8 L (Real.sqrt 2))
      (A' := coordinateBox 8 (Real.sqrt 2 / 2 + e8BasisNormSum)
        (L - Real.sqrt 2 / 2 - e8BasisNormSum))
      (fun x hx hxA => (hEall_mem x).mpr ⟨hx, hxA⟩)
      (fun y hy => closedBall_subset_coordinateBox hy)
    rw [volume_coordinateBox] at h
    have hside : L - Real.sqrt 2 / 2 - e8BasisNormSum - (Real.sqrt 2 / 2 + e8BasisNormSum) =
        2 * R + 2 - 2 * e8BasisNormSum := by
      rw [hL]
      ring
    rw [hside] at h
    have hnn : 0 ≤ 2 * R + 2 - 2 * e8BasisNormSum := by linarith
    have h2 := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) h
    rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hnn, ENNReal.toReal_natCast] at h2
    exact h2
  have hball0 : volume.real (closedBall c₀ (R + Real.sqrt 2 + e8BasisNormSum)) =
      volume.real (closedBall (0 : Ambient 8) (R + Real.sqrt 2 + e8BasisNormSum)) := by
    rw [measureReal_def, Measure.addHaar_closedBall_center, ← measureReal_def]
  rw [hTcard, hL] at hT
  have hcast : ((W.card + (Eall.filter fun z => R + Real.sqrt 2 ≤ dist z c₀).card : ℕ) : ℝ) =
      (W.card : ℝ) + ((Eall.filter fun z => R + Real.sqrt 2 ≤ dist z c₀).card : ℝ) := by
    push_cast
    ring
  have hEc : ((Eall.filter fun z => R + Real.sqrt 2 ≤ dist z c₀).card : ℝ) +
      ((Eall.filter fun z => ¬ (R + Real.sqrt 2 ≤ dist z c₀)).card : ℝ) = (Eall.card : ℝ) := by
    exact_mod_cast hEcard
  have e8 : (2 * (R + 1) + Real.sqrt 2) ^ 8 = (2 * R + 2 + Real.sqrt 2) ^ 8 := by ring
  rw [hcast, e8] at hT
  rw [hball0] at hEin_le
  linarith

end E8Leech
