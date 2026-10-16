import E8Leech.LeechLatticeCount
import E8Leech.LocalE8Lattice

/-!
# The local lattice of an almost integral point set in dimension 24 (BRR, Steps 2–3)

The rank 24 version of `LocalE8Lattice`. Let `w` be a frame of `ℝ²⁴` with an exact integer Gram
matrix `G` with even diagonal, controlled coordinates and vectors of norm at most `70`
(`LeechIntegralFrame`). Let `Y` be a finite set in a ball of radius about `R ≥ 200000` whose
points have almost integral inner products with the frame and with each other, almost even squared
norms and mutual distances at least `19/10`. If `Y` has at least `(9/10)·vol(B_R)` points, then,
given the characterization of the Leech lattice, there is a linear isometry `Φ` with every point
of `Y` within `θ` of `Φ(Λ₂₄)` (`exists_isometry_of_leechIntegralFrame`).

The construction is that of rank eight: the points are rounded to the dual lattice of `ℤw`
(`roundPoint`), inner products of the rounded points have denominator `det G ≤ 24!·4900²⁴`, and the
rounded points and the frame generate an even integral lattice. The count of its points gives
covolume one, and the separation of the rounded points excludes vectors of squared norm two
(`exists_isometry_image_leechSet_eq_of_even_lattice_count`).

* `frame24_sum_abs_le`: a frame within `4` of `64 eᵢ` has coordinates at most `|x|/8`.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric
open scoped InnerProductSpace

/-- A frame of `ℝ²⁴` within `4` of `64 eᵢ`: the coordinates are at most an eighth of the norm. -/
theorem frame24_sum_abs_le {v : Fin 24 → Ambient 24}
    (hv : ∀ i, ‖v i - (64 : ℝ) • EuclideanSpace.basisFun (Fin 24) ℝ i‖ ≤ 4)
    (a : Fin 24 → ℝ) : ∑ j, |a j| ≤ 1 / 8 * ‖∑ j, a j • v j‖ := by
  have h := scaled_basis_sum_abs_le (EuclideanSpace.basisFun (Fin 24) ℝ) (by norm_num) hv a
  have hs : Real.sqrt ((24 : ℕ) : ℝ) ≤ 5 := by
    rw [show ((24 : ℕ) : ℝ) = 24 by norm_num]
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hsum : 0 ≤ ∑ j, |a j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hn : 0 ≤ ‖∑ j, a j • v j‖ := norm_nonneg _
  have h2 : Real.sqrt ((24 : ℕ) : ℝ) * (‖∑ j, a j • v j‖ + 4 * ∑ j, |a j|) ≤
      5 * (‖∑ j, a j • v j‖ + 4 * ∑ j, |a j|) :=
    mul_le_mul_of_nonneg_right hs (by linarith)
  linarith

theorem frame24_linearIndependent {v : Fin 24 → Ambient 24}
    (hv : ∀ i, ‖v i - (64 : ℝ) • EuclideanSpace.basisFun (Fin 24) ℝ i‖ ≤ 4) :
    LinearIndependent ℝ v := by
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have h := frame24_sum_abs_le hv a
  rw [ha, norm_zero, mul_zero] at h
  have hi : |a i| ≤ ∑ j, |a j| :=
    Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  exact abs_eq_zero.mp (le_antisymm (hi.trans h) (abs_nonneg _))

theorem frame24_norm_le {v : Fin 24 → Ambient 24}
    (hv : ∀ i, ‖v i - (64 : ℝ) • EuclideanSpace.basisFun (Fin 24) ℝ i‖ ≤ 4)
    (i : Fin 24) : ‖v i‖ ≤ 68 := by
  have e : v i = (v i - (64 : ℝ) • EuclideanSpace.basisFun (Fin 24) ℝ i) +
      (64 : ℝ) • EuclideanSpace.basisFun (Fin 24) ℝ i := by abel
  have hb : ‖(64 : ℝ) • EuclideanSpace.basisFun (Fin 24) ℝ i‖ = 64 := by
    rw [norm_smul, (EuclideanSpace.basisFun (Fin 24) ℝ).orthonormal.1 i]
    norm_num
  calc ‖v i‖ ≤ ‖v i - (64 : ℝ) • EuclideanSpace.basisFun (Fin 24) ℝ i‖ +
        ‖(64 : ℝ) • EuclideanSpace.basisFun (Fin 24) ℝ i‖ := by
        conv_lhs => rw [e]
        exact norm_add_le _ _
    _ ≤ 4 + 64 := by rw [hb]; linarith [hv i]
    _ = 68 := by norm_num

/-- A frame of `ℝ²⁴` with an exact integer Gram matrix with even diagonal, coordinates controlled
by the norm, and vectors of norm at most `70`. -/
structure LeechIntegralFrame (w : Fin 24 → Ambient 24) (G : Matrix (Fin 24) (Fin 24) ℤ) :
    Prop where
  gram : ∀ i j, ⟪w i, w j⟫_ℝ = (G i j : ℝ)
  even : ∀ i, (2 : ℤ) ∣ G i i
  coord : ∀ a : Fin 24 → ℝ, ∑ j, |a j| ≤ 1 * ‖∑ j, a j • w j‖
  norm_le : ∀ i, ‖w i‖ ≤ 70

namespace LeechIntegralFrame

variable {w : Fin 24 → Ambient 24} {G : Matrix (Fin 24) (Fin 24) ℤ}

theorem linearIndependent (hF : LeechIntegralFrame w G) : LinearIndependent ℝ w := by
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have h := hF.coord a
  rw [ha, norm_zero, mul_zero] at h
  have hi : |a i| ≤ ∑ j, |a j| :=
    Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  exact abs_eq_zero.mp (le_antisymm (hi.trans h) (abs_nonneg _))

theorem span_top (hF : LeechIntegralFrame w G) : ⊤ ≤ Submodule.span ℝ (Set.range w) := by
  rw [hF.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)]

/-- The frame as a basis. -/
def basis (hF : LeechIntegralFrame w G) : Module.Basis (Fin 24) ℝ (Ambient 24) :=
  Module.Basis.mk hF.linearIndependent hF.span_top

theorem basis_apply (hF : LeechIntegralFrame w G) (i : Fin 24) : hF.basis i = w i :=
  Module.Basis.mk_apply hF.linearIndependent hF.span_top i

theorem range_basis (hF : LeechIntegralFrame w G) : Set.range hF.basis = Set.range w :=
  congrArg Set.range (funext hF.basis_apply)

theorem exists_coords (hF : LeechIntegralFrame w G) (z : Ambient 24) :
    ∃ a : Fin 24 → ℝ, z = ∑ j, a j • w j := by
  refine ⟨fun j => hF.basis.repr z j, ?_⟩
  conv_lhs => rw [← hF.basis.sum_repr z]
  exact Finset.sum_congr rfl fun j _ => by rw [hF.basis_apply]

theorem det_pos (hF : LeechIntegralFrame w G) : 0 < G.det := by
  have h1 := covolume_sq_eq_det_gram hF.basis
  have e : (Matrix.of fun i j => ⟪hF.basis i, hF.basis j⟫_ℝ) = G.map (Int.castRingHom ℝ) := by
    ext i j
    rw [Matrix.of_apply, Matrix.map_apply, hF.basis_apply, hF.basis_apply, hF.gram i j]
    rfl
  rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h1
  have hpos := ZLattice.covolume_pos (Submodule.span ℤ (Set.range hF.basis)) volume
  have h2 : (0 : ℝ) < ((G.det : ℤ) : ℝ) := by
    have h3 : (Int.castRingHom ℝ) G.det = ((G.det : ℤ) : ℝ) := rfl
    rw [← h3, ← h1]
    positivity
  exact_mod_cast h2

/-- The determinant of the Gram matrix is at most `24!·4900²⁴`. -/
theorem det_le (hF : LeechIntegralFrame w G) :
    (G.det : ℝ) ≤ 620448401733239439360000 * 4900 ^ 24 := by
  have hx : ∀ i j, (AbsoluteValue.abs : AbsoluteValue ℤ ℤ) (G i j) ≤ 4900 := by
    intro i j
    have h1 : |(G i j : ℝ)| ≤ 70 * 70 := by
      rw [← hF.gram i j]
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul (hF.norm_le i) (hF.norm_le j) (norm_nonneg _) (by norm_num))
    have h2 : (|G i j| : ℝ) ≤ 4900 := by
      rw [← Int.cast_abs] at h1
      norm_num at h1 ⊢
      exact_mod_cast h1
    have h3 : |G i j| ≤ 4900 := by exact_mod_cast h2
    exact h3
  have h := Matrix.det_le (A := G) (abv := AbsoluteValue.abs) hx
  have h4 : |G.det| ≤ 620448401733239439360000 * 4900 ^ 24 := by
    have h5 : (Fintype.card (Fin 24)).factorial • (4900 : ℤ) ^ Fintype.card (Fin 24) =
        620448401733239439360000 * 4900 ^ 24 := by
      rw [Fintype.card_fin]
      norm_num [Nat.factorial]
    rw [h5] at h
    exact h
  have h6 : G.det ≤ 620448401733239439360000 * 4900 ^ 24 := (le_abs_self _).trans h4
  exact_mod_cast h6

end LeechIntegralFrame

/-- The volume of a ball of `ℝ²⁴`. -/
theorem volume_real_closedBall_twentyFour (c : Ambient 24) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (closedBall c r) = r ^ 24 * volume.real (ball (0 : Ambient 24) 1) := by
  rw [Measure.addHaar_real_closedBall volume c hr]
  simp

theorem volume_real_unitBall_twentyFour_pos : 0 < volume.real (ball (0 : Ambient 24) 1) :=
  ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne

/-- The numerical inequality behind the unimodularity in dimension 24: for `R ≥ 200000`, a ball
of radius `R + 1683` has less than `√2 · (9/10)` times the volume of the ball of radius `R`. -/
theorem count_volume_ineq_twentyFour {R ω N : ℝ} (hR : 200000 ≤ R) (hω : 0 < ω)
    (hN : 9 / 10 * (R ^ 24 * ω) ≤ N) {V : ℝ} (hV0 : 0 ≤ V) (hV : V ≤ (R + 1683) ^ 24 * ω) :
    V ^ 2 < 2 * N ^ 2 := by
  have hR0 : (0 : ℝ) < R := by linarith
  have h1 : R + 1683 ≤ 201683 / 200000 * R := by linarith
  have h2 : (R + 1683) ^ 24 ≤ (201683 / 200000 * R) ^ 24 :=
    pow_le_pow_left₀ (by linarith) h1 24
  have hA : 0 < R ^ 24 * ω := mul_pos (pow_pos hR0 24) hω
  have h3 : V ≤ (201683 / 200000 : ℝ) ^ 24 * (R ^ 24 * ω) := by
    calc V ≤ (R + 1683) ^ 24 * ω := hV
      _ ≤ (201683 / 200000 * R) ^ 24 * ω := mul_le_mul_of_nonneg_right h2 hω.le
      _ = (201683 / 200000 : ℝ) ^ 24 * (R ^ 24 * ω) := by ring
  have h4 : V ^ 2 ≤ ((201683 / 200000 : ℝ) ^ 24 * (R ^ 24 * ω)) ^ 2 :=
    pow_le_pow_left₀ hV0 h3 2
  have h5 : (9 / 10 * (R ^ 24 * ω)) ^ 2 ≤ N ^ 2 :=
    pow_le_pow_left₀ (by positivity) hN 2
  have h6 : ((201683 / 200000 : ℝ) ^ 24) ^ 2 < 2 * (9 / 10) ^ 2 := by norm_num
  have hA2 : 0 < (R ^ 24 * ω) ^ 2 := pow_pos hA 2
  calc V ^ 2 ≤ ((201683 / 200000 : ℝ) ^ 24 * (R ^ 24 * ω)) ^ 2 := h4
    _ = ((201683 / 200000 : ℝ) ^ 24) ^ 2 * (R ^ 24 * ω) ^ 2 := by ring
    _ < 2 * (9 / 10) ^ 2 * (R ^ 24 * ω) ^ 2 := mul_lt_mul_of_pos_right h6 hA2
    _ = 2 * (9 / 10 * (R ^ 24 * ω)) ^ 2 := by ring
    _ ≤ 2 * N ^ 2 := by linarith

/-- The rounded points together with the frame: generators of the local lattice. -/
def leechLatticeGenerators (w : Fin 24 → Ambient 24) (G : Matrix (Fin 24) (Fin 24) ℤ)
    (Y : Finset (Ambient 24)) : Set (Ambient 24) :=
  (fun y => roundPoint w G y) '' (Y : Set (Ambient 24)) ∪ Set.range w

theorem roundPoint_mem_leechLatticeGenerators (w : Fin 24 → Ambient 24)
    (G : Matrix (Fin 24) (Fin 24) ℤ) {Y : Finset (Ambient 24)} {y : Ambient 24} (hy : y ∈ Y) :
    roundPoint w G y ∈ leechLatticeGenerators w G Y :=
  Or.inl ⟨y, hy, rfl⟩

theorem range_subset_leechLatticeGenerators (w : Fin 24 → Ambient 24)
    (G : Matrix (Fin 24) (Fin 24) ℤ) (Y : Finset (Ambient 24)) :
    Set.range w ⊆ leechLatticeGenerators w G Y :=
  Set.subset_union_right

namespace LeechIntegralFrame

variable {w : Fin 24 → Ambient 24} {G : Matrix (Fin 24) (Fin 24) ℤ}

theorem norm_sub_round_le (hF : LeechIntegralFrame w G) {θ : ℝ} (hθ0 : 0 ≤ θ) {y : Ambient 24}
    (hy : ∀ k, ∃ n : ℤ, |⟪y, w k⟫_ℝ - n| ≤ θ) : ‖y - roundPoint w G y‖ ≤ θ := by
  have h := norm_sub_roundPoint_le hF.gram hF.det_pos.ne' zero_le_one hθ0 hF.exists_coords
    hF.coord hy
  rwa [one_mul] at h

theorem small_mul_det (hF : LeechIntegralFrame w G) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s * (620448401733239439360000 * 4900 ^ 24) < 1) : s * (G.det : ℝ) < 1 :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_left hF.det_le hs0) hs

/-- Inner products of the generators are integers. -/
theorem generators_integral (hF : LeechIntegralFrame w G) (Y : Finset (Ambient 24)) {θ ρ σ : ℝ}
    (hθ0 : 0 ≤ θ) (hρ0 : 0 ≤ ρ) (hπ : ∀ y ∈ Y, ‖y - roundPoint w G y‖ ≤ θ)
    (hYnorm : ∀ y ∈ Y, ‖y‖ ≤ ρ)
    (hYint : ∀ y ∈ Y, ∀ y' ∈ Y, ∃ k : ℤ, |⟪y, y'⟫_ℝ - k| ≤ σ)
    (hsmall : (σ + θ * (2 * ρ + θ)) * (G.det : ℝ) < 1) :
    ∀ x ∈ leechLatticeGenerators w G Y, ∀ x' ∈ leechLatticeGenerators w G Y,
      ∃ m : ℤ, ⟪x, x'⟫_ℝ = m := by
  intro x hx x' hx'
  rcases hx with ⟨y, hy, rfl⟩ | ⟨i, rfl⟩
  · rcases hx' with ⟨y', hy', rfl⟩ | ⟨j, rfl⟩
    · obtain ⟨k, hk⟩ := hYint y hy y' hy'
      exact ⟨k, inner_roundPoint_eq_int hF.gram hF.det_pos hθ0 hρ0 (hπ y hy) (hπ y' hy')
        (hYnorm y hy) (hYnorm y' hy') hk hsmall⟩
    · exact ⟨round ⟪y, w j⟫_ℝ, inner_roundPoint_frame hF.gram hF.det_pos.ne' y j⟩
  · rcases hx' with ⟨y', hy', rfl⟩ | ⟨j, rfl⟩
    · refine ⟨round ⟪y', w i⟫_ℝ, ?_⟩
      rw [real_inner_comm]
      exact inner_roundPoint_frame hF.gram hF.det_pos.ne' y' i
    · exact ⟨G i j, hF.gram i j⟩

/-- Squared norms of the generators are even integers. -/
theorem generators_even (hF : LeechIntegralFrame w G) (Y : Finset (Ambient 24)) {θ ρ σ : ℝ}
    (hθ0 : 0 ≤ θ) (hρ0 : 0 ≤ ρ) (hπ : ∀ y ∈ Y, ‖y - roundPoint w G y‖ ≤ θ)
    (hYnorm : ∀ y ∈ Y, ‖y‖ ≤ ρ) (hYeven : ∀ y ∈ Y, ∃ k : ℤ, |‖y‖ ^ 2 - 2 * k| ≤ σ)
    (hsmall : (σ + θ * (2 * ρ + θ)) * (G.det : ℝ) < 1) :
    ∀ x ∈ leechLatticeGenerators w G Y, ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩ | ⟨i, rfl⟩
  · obtain ⟨k, hk⟩ := hYeven y hy
    refine ⟨k, ?_⟩
    have hk' : |⟪y, y⟫_ℝ - ((2 * k : ℤ) : ℝ)| ≤ σ := by
      rw [real_inner_self_eq_norm_sq]
      have e : ((2 * k : ℤ) : ℝ) = 2 * (k : ℝ) := by norm_num
      rw [e]
      exact hk
    have h := inner_roundPoint_eq_int hF.gram hF.det_pos hθ0 hρ0 (hπ y hy) (hπ y hy)
      (hYnorm y hy) (hYnorm y hy) hk' hsmall
    have h2 : ‖roundPoint w G y‖ ^ 2 = ((2 * k : ℤ) : ℝ) := by
      rw [← real_inner_self_eq_norm_sq]
      exact h
    rw [h2]
    norm_num
  · obtain ⟨k, hk⟩ := hF.even i
    refine ⟨k, ?_⟩
    rw [← real_inner_self_eq_norm_sq, hF.gram i i, hk]
    norm_num

end LeechIntegralFrame

/-- **The local lattice in dimension 24.** A finite set `Y ⊂ ℝ²⁴` with almost integral inner
products against an integral frame and among its points, almost even squared norms, mutual
distances at least `19/10` and at least `(9/10)·vol(B_R)` points in a ball of radius about `R`
lies within `θ` of an isometric copy of the Leech lattice, given the characterization of the Leech
lattice. -/
theorem exists_isometry_of_leechIntegralFrame (hLeech : LeechCharacterization)
    {w : Fin 24 → Ambient 24} {G : Matrix (Fin 24) (Fin 24) ℤ} (hF : LeechIntegralFrame w G)
    (Y : Finset (Ambient 24)) {c : Ambient 24} {R θ σ : ℝ} (hR : 200000 ≤ R) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ 1 / 8) (hσ0 : 0 ≤ σ)
    (hYball : ∀ y ∈ Y, ‖y - c‖ ≤ R + 1 / 8) (hYnorm : ∀ y ∈ Y, ‖y‖ ≤ 3 * R)
    (hYsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 19 / 10 ≤ ‖y - y'‖)
    (hYround : ∀ y ∈ Y, ∀ k, ∃ n : ℤ, |⟪y, w k⟫_ℝ - n| ≤ θ)
    (hYint : ∀ y ∈ Y, ∀ y' ∈ Y, ∃ k : ℤ, |⟪y, y'⟫_ℝ - k| ≤ σ)
    (hYeven : ∀ y ∈ Y, ∃ k : ℤ, |‖y‖ ^ 2 - 2 * k| ≤ σ)
    (hsmall : (σ + θ * (6 * R + θ)) * (620448401733239439360000 * 4900 ^ 24) < 1)
    (hcount : 9 / 10 * volume.real (closedBall (0 : Ambient 24) R) ≤ Y.card) :
    ∃ Φ : Ambient 24 ≃ₗᵢ[ℝ] Ambient 24, ∀ y ∈ Y, ∃ z ∈ leechSet, ‖y - Φ z‖ ≤ θ := by
  classical
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hρ0 : (0 : ℝ) ≤ 3 * R := by linarith
  have hπ : ∀ y ∈ Y, ‖y - roundPoint w G y‖ ≤ θ := fun y hy =>
    hF.norm_sub_round_le hθ0 (hYround y hy)
  have hs0 : 0 ≤ σ + θ * (2 * (3 * R) + θ) := by
    have h : 0 ≤ θ * (2 * (3 * R) + θ) := mul_nonneg hθ0 (by linarith)
    linarith
  have hsmall' : (σ + θ * (2 * (3 * R) + θ)) * (G.det : ℝ) < 1 := by
    refine hF.small_mul_det hs0 ?_
    have e : σ + θ * (2 * (3 * R) + θ) = σ + θ * (6 * R + θ) := by ring
    rw [e]
    exact hsmall
  have hint := hF.generators_integral Y hθ0 hρ0 hπ hYnorm hYint hsmall'
  have heven := hF.generators_even Y hθ0 hρ0 hπ hYnorm hYeven hsmall'
  obtain ⟨hLint, hLeven⟩ := span_int_integral_even hint heven
  have hle : Submodule.span ℤ (Set.range hF.basis) ≤
      Submodule.span ℤ (leechLatticeGenerators w G Y) := by
    rw [hF.range_basis]
    exact Submodule.span_mono (range_subset_leechLatticeGenerators w G Y)
  -- the rounded points are distinct and separated
  have hdist : ∀ y ∈ Y, ∀ y' ∈ Y, ‖y - y'‖ ≤ ‖roundPoint w G y - roundPoint w G y'‖ + 1 / 4 := by
    intro y hy y' hy'
    have e : y - y' = (roundPoint w G y - roundPoint w G y') +
        ((y - roundPoint w G y) - (y' - roundPoint w G y')) := by abel
    have h1 : ‖(y - roundPoint w G y) - (y' - roundPoint w G y')‖ ≤ θ + θ :=
      (norm_sub_le _ _).trans (add_le_add (hπ y hy) (hπ y' hy'))
    calc ‖y - y'‖ = ‖(roundPoint w G y - roundPoint w G y') +
          ((y - roundPoint w G y) - (y' - roundPoint w G y'))‖ := by rw [← e]
      _ ≤ ‖roundPoint w G y - roundPoint w G y'‖ +
          ‖(y - roundPoint w G y) - (y' - roundPoint w G y')‖ := norm_add_le _ _
      _ ≤ ‖roundPoint w G y - roundPoint w G y'‖ + 1 / 4 := by linarith
  have hinj : Set.InjOn (fun y => roundPoint w G y) (Y : Set (Ambient 24)) := by
    intro y hy y' hy' he
    by_contra hne
    have h1 := hYsep y hy y' hy' hne
    have he' : roundPoint w G y = roundPoint w G y' := he
    have h2 := hdist y hy y' hy'
    rw [he', sub_self, norm_zero] at h2
    linarith
  have hcard : (Y.image fun y => roundPoint w G y).card = Y.card :=
    Finset.card_image_of_injOn hinj
  have hT : ∀ t ∈ Y.image (fun y => roundPoint w G y),
      t ∈ Submodule.span ℤ (leechLatticeGenerators w G Y) := by
    intro t ht
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
    exact Submodule.subset_span (roundPoint_mem_leechLatticeGenerators w G hy)
  have hball : ∀ t ∈ Y.image (fun y => roundPoint w G y), t ∈ closedBall c (R + 1 / 4) := by
    intro t ht
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
    rw [mem_closedBall, dist_eq_norm]
    have e : roundPoint w G y - c = (y - c) - (y - roundPoint w G y) := by abel
    rw [e]
    have h := (norm_sub_le (y - c) (y - roundPoint w G y)).trans
      (add_le_add (hYball y hy) (hπ y hy))
    linarith
  have hsepT : ∀ t ∈ Y.image (fun y => roundPoint w G y),
      ∀ t' ∈ Y.image (fun y => roundPoint w G y), t ≠ t' → 2 < ‖t - t'‖ ^ 2 := by
    intro t ht t' ht' hne
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp ht'
    have hyy : y ≠ y' := fun e => hne (by rw [e])
    have h1 := hYsep y hy y' hy' hyy
    have h2 := hdist y hy y' hy'
    have h3 : (33 / 20 : ℝ) ≤ ‖roundPoint w G y - roundPoint w G y'‖ := by linarith
    nlinarith
  -- the volume inequality
  have hsum : ∑ i, ‖hF.basis i‖ ≤ 1680 := by
    calc ∑ i, ‖hF.basis i‖ ≤ ∑ _i : Fin 24, (70 : ℝ) := Finset.sum_le_sum fun i _ => by
          rw [hF.basis_apply]
          exact hF.norm_le i
      _ = 1680 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          norm_num
  have hsum0 : 0 ≤ ∑ i, ‖hF.basis i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hr0 : 0 ≤ R + 1 / 4 + 2 + ∑ i, ‖hF.basis i‖ := by linarith
  have hV : volume.real (closedBall c (R + 1 / 4 + 2 + ∑ i, ‖hF.basis i‖)) ≤
      (R + 1683) ^ 24 * volume.real (ball (0 : Ambient 24) 1) := by
    rw [volume_real_closedBall_twentyFour c hr0]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr0 (by linarith) 24)
      volume_real_unitBall_twentyFour_pos.le
  have hN : 9 / 10 * (R ^ 24 * volume.real (ball (0 : Ambient 24) 1)) ≤
      ((Y.image fun y => roundPoint w G y).card : ℝ) := by
    rw [hcard, ← volume_real_closedBall_twentyFour (0 : Ambient 24) hR0]
    exact hcount
  have hcnt := count_volume_ineq_twentyFour hR volume_real_unitBall_twentyFour_pos hN
    measureReal_nonneg hV
  obtain ⟨Φ, hΦ⟩ := exists_isometry_image_leechSet_eq_of_even_lattice_count hLeech
    (Submodule.span ℤ (leechLatticeGenerators w G Y)) hLint hLeven hF.basis hle _ hT hball hsepT
    hcnt
  refine ⟨Φ, fun y hy => ?_⟩
  have hmem : roundPoint w G y ∈
      ((Submodule.span ℤ (leechLatticeGenerators w G Y) : Submodule ℤ (Ambient 24)) :
        Set (Ambient 24)) :=
    Submodule.subset_span (roundPoint_mem_leechLatticeGenerators w G hy)
  rw [← hΦ] at hmem
  obtain ⟨z, hz, hzy⟩ := hmem
  exact ⟨z, hz, by rw [hzy]; exact hπ y hy⟩

end E8Leech
