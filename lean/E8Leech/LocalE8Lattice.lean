import E8Leech.EvenLatticeCount
import E8Leech.DualRounding
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# The local lattice of an almost integral point set (BRR, Steps 2–3)

Let `w` be a frame of `ℝ⁸` with an exact integer Gram matrix `G` with even diagonal, controlled
coordinates and vectors of norm at most `20` (`IntegralFrame`). Let `Y` be a finite set in a ball
of radius about `R` whose points have almost integral inner products with the frame and with each
other, and almost even squared norms. If `Y` has at least `(9/10)·vol(B_R)` points, then there is
a linear isometry `Φ` with every point of `Y` within `θ` of `Φ(E8)`
(`exists_isometry_of_integralFrame`).

Each point `y` is rounded to the point `π(y)` of the dual lattice of `ℤw` with integer inner
products against the frame (`roundPoint`). Inner products of the rounded points have denominator
`det G`, so they are exactly integers once the errors are small against `1 / det G`
(`inner_roundPoint_eq_int`). The rounded points and the frame generate an even integral lattice
containing `ℤw`, and the count of its points identifies it with `E8`
(`exists_isometry_image_e8Set_eq_of_even_lattice_count`). No reduced basis and no Voronoi cell is
used.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric
open scoped InnerProductSpace

/-- Rounding the inner products with a frame: the point of the dual lattice next to `y`. -/
def roundPoint {d : ℕ} (w : Fin d → Ambient d) (G : Matrix (Fin d) (Fin d) ℤ) (y : Ambient d) :
    Ambient d :=
  dualPoint w G fun k => round ⟪y, w k⟫_ℝ

theorem inner_roundPoint_frame {d : ℕ} {w : Fin d → Ambient d} {G : Matrix (Fin d) (Fin d) ℤ}
    (hG : ∀ i j, ⟪w i, w j⟫_ℝ = (G i j : ℝ)) (hdet : G.det ≠ 0) (y : Ambient d) (k : Fin d) :
    ⟪roundPoint w G y, w k⟫_ℝ = ((round ⟪y, w k⟫_ℝ : ℤ) : ℝ) :=
  inner_dualPoint_frame hG hdet _ k

theorem norm_sub_roundPoint_le {d : ℕ} {w : Fin d → Ambient d} {G : Matrix (Fin d) (Fin d) ℤ}
    (hG : ∀ i j, ⟪w i, w j⟫_ℝ = (G i j : ℝ)) (hdet : G.det ≠ 0) {K θ : ℝ} (hK0 : 0 ≤ K)
    (hθ0 : 0 ≤ θ) (hspan : ∀ z : Ambient d, ∃ a : Fin d → ℝ, z = ∑ j, a j • w j)
    (hK : ∀ a : Fin d → ℝ, ∑ j, |a j| ≤ K * ‖∑ j, a j • w j‖) {y : Ambient d}
    (hy : ∀ k, ∃ n : ℤ, |⟪y, w k⟫_ℝ - n| ≤ θ) : ‖y - roundPoint w G y‖ ≤ K * θ := by
  refine norm_le_of_inner_frame_le hK0 hθ0 hspan hK fun k => ?_
  obtain ⟨n, hn⟩ := hy k
  rw [inner_sub_left, inner_roundPoint_frame hG hdet]
  exact (round_le _ n).trans hn

/-- **Exact integrality.** The inner product of two rounded points is the integer near the inner
product of the points, once the errors are small against `1 / det G`. -/
theorem inner_roundPoint_eq_int {d : ℕ} {w : Fin d → Ambient d} {G : Matrix (Fin d) (Fin d) ℤ}
    (hG : ∀ i j, ⟪w i, w j⟫_ℝ = (G i j : ℝ)) (hdet : 0 < G.det) {θ ρ σ : ℝ} (hθ0 : 0 ≤ θ)
    (hρ0 : 0 ≤ ρ) {y y' : Ambient d} (hy : ‖y - roundPoint w G y‖ ≤ θ)
    (hy' : ‖y' - roundPoint w G y'‖ ≤ θ) (hn : ‖y‖ ≤ ρ) (hn' : ‖y'‖ ≤ ρ) {k : ℤ}
    (hk : |⟪y, y'⟫_ℝ - k| ≤ σ) (hsmall : (σ + θ * (2 * ρ + θ)) * (G.det : ℝ) < 1) :
    ⟪roundPoint w G y, roundPoint w G y'⟫_ℝ = k := by
  have hq : (G.det : ℝ) * ⟪roundPoint w G y, roundPoint w G y'⟫_ℝ =
      ((∑ j, round ⟪y, w j⟫_ℝ *
        (G.adjugate.mulVec fun k => round ⟪y', w k⟫_ℝ) j : ℤ) : ℝ) :=
    det_mul_inner_dualPoint hG hdet.ne' _ _
  refine eq_int_of_mul_int_of_near hdet hq ?_
  have hπ' : ‖roundPoint w G y'‖ ≤ ρ + θ := by
    have h := norm_sub_le y' (y' - roundPoint w G y')
    rw [sub_sub_cancel] at h
    linarith
  have h1 : |⟪roundPoint w G y, roundPoint w G y'⟫_ℝ - ⟪y, y'⟫_ℝ| ≤ θ * (2 * ρ + θ) := by
    have e : ⟪roundPoint w G y, roundPoint w G y'⟫_ℝ - ⟪y, y'⟫_ℝ =
        ⟪roundPoint w G y - y, roundPoint w G y'⟫_ℝ + ⟪y, roundPoint w G y' - y'⟫_ℝ := by
      rw [inner_sub_left, inner_sub_right]
      ring
    have ha : |⟪roundPoint w G y - y, roundPoint w G y'⟫_ℝ| ≤ θ * (ρ + θ) :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul (by rwa [norm_sub_rev]) hπ' (norm_nonneg _) hθ0)
    have hb : |⟪y, roundPoint w G y' - y'⟫_ℝ| ≤ ρ * θ :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul hn (by rwa [norm_sub_rev]) (norm_nonneg _) hρ0)
    rw [e]
    calc |⟪roundPoint w G y - y, roundPoint w G y'⟫_ℝ + ⟪y, roundPoint w G y' - y'⟫_ℝ|
        ≤ |⟪roundPoint w G y - y, roundPoint w G y'⟫_ℝ| + |⟪y, roundPoint w G y' - y'⟫_ℝ| :=
          abs_add_le _ _
      _ ≤ θ * (ρ + θ) + ρ * θ := add_le_add ha hb
      _ = θ * (2 * ρ + θ) := by ring
  have h2 : |⟪roundPoint w G y, roundPoint w G y'⟫_ℝ - k| ≤ σ + θ * (2 * ρ + θ) := by
    have e : ⟪roundPoint w G y, roundPoint w G y'⟫_ℝ - k =
        (⟪roundPoint w G y, roundPoint w G y'⟫_ℝ - ⟪y, y'⟫_ℝ) + (⟪y, y'⟫_ℝ - k) := by ring
    rw [e]
    calc _ ≤ |⟪roundPoint w G y, roundPoint w G y'⟫_ℝ - ⟪y, y'⟫_ℝ| + |⟪y, y'⟫_ℝ - k| :=
          abs_add_le _ _
      _ ≤ θ * (2 * ρ + θ) + σ := add_le_add h1 hk
      _ = σ + θ * (2 * ρ + θ) := by ring
  have hD : (0 : ℝ) < (G.det : ℝ) := by exact_mod_cast hdet
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right h2 hD.le) hsmall

/-- A frame of `ℝ⁸` with an exact integer Gram matrix with even diagonal, coordinates controlled
by the norm, and vectors of norm at most `20`. -/
structure IntegralFrame (w : Fin 8 → Ambient 8) (G : Matrix (Fin 8) (Fin 8) ℤ) : Prop where
  gram : ∀ i j, ⟪w i, w j⟫_ℝ = (G i j : ℝ)
  even : ∀ i, (2 : ℤ) ∣ G i i
  coord : ∀ a : Fin 8 → ℝ, ∑ j, |a j| ≤ 1 * ‖∑ j, a j • w j‖
  norm_le : ∀ i, ‖w i‖ ≤ 20

namespace IntegralFrame

variable {w : Fin 8 → Ambient 8} {G : Matrix (Fin 8) (Fin 8) ℤ}

theorem linearIndependent (hF : IntegralFrame w G) : LinearIndependent ℝ w := by
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have h := hF.coord a
  rw [ha, norm_zero, mul_zero] at h
  have hi : |a i| ≤ ∑ j, |a j| :=
    Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  exact abs_eq_zero.mp (le_antisymm (hi.trans h) (abs_nonneg _))

theorem span_top (hF : IntegralFrame w G) : ⊤ ≤ Submodule.span ℝ (Set.range w) := by
  rw [hF.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)]

/-- The frame as a basis. -/
def basis (hF : IntegralFrame w G) : Module.Basis (Fin 8) ℝ (Ambient 8) :=
  Module.Basis.mk hF.linearIndependent hF.span_top

theorem basis_apply (hF : IntegralFrame w G) (i : Fin 8) : hF.basis i = w i :=
  Module.Basis.mk_apply hF.linearIndependent hF.span_top i

theorem range_basis (hF : IntegralFrame w G) : Set.range hF.basis = Set.range w :=
  congrArg Set.range (funext hF.basis_apply)

theorem exists_coords (hF : IntegralFrame w G) (z : Ambient 8) :
    ∃ a : Fin 8 → ℝ, z = ∑ j, a j • w j := by
  refine ⟨fun j => hF.basis.repr z j, ?_⟩
  conv_lhs => rw [← hF.basis.sum_repr z]
  exact Finset.sum_congr rfl fun j _ => by rw [hF.basis_apply]

theorem det_pos (hF : IntegralFrame w G) : 0 < G.det := by
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

theorem det_le (hF : IntegralFrame w G) : (G.det : ℝ) ≤ 40320 * 400 ^ 8 := by
  have hx : ∀ i j, (AbsoluteValue.abs : AbsoluteValue ℤ ℤ) (G i j) ≤ 400 := by
    intro i j
    have h1 : |(G i j : ℝ)| ≤ 20 * 20 := by
      rw [← hF.gram i j]
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul (hF.norm_le i) (hF.norm_le j) (norm_nonneg _) (by norm_num))
    have h2 : (|G i j| : ℝ) ≤ 400 := by
      rw [← Int.cast_abs] at h1
      norm_num at h1 ⊢
      exact_mod_cast h1
    have h3 : |G i j| ≤ 400 := by exact_mod_cast h2
    exact h3
  have h := Matrix.det_le (A := G) (abv := AbsoluteValue.abs) hx
  have h4 : |G.det| ≤ 40320 * 400 ^ 8 := by
    have h5 : (Fintype.card (Fin 8)).factorial • (400 : ℤ) ^ Fintype.card (Fin 8) =
        40320 * 400 ^ 8 := by
      rw [Fintype.card_fin]
      norm_num [Nat.factorial]
    rw [h5] at h
    exact h
  have h6 : G.det ≤ 40320 * 400 ^ 8 := (le_abs_self _).trans h4
  exact_mod_cast h6

end IntegralFrame

/-- The volume of a ball of `ℝ⁸`. -/
theorem volume_real_closedBall_eight (c : Ambient 8) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (closedBall c r) = r ^ 8 * volume.real (ball (0 : Ambient 8) 1) := by
  rw [Measure.addHaar_real_closedBall volume c hr]
  simp

theorem volume_real_unitBall_eight_pos : 0 < volume.real (ball (0 : Ambient 8) 1) :=
  ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne

/-- The numerical inequality behind the unimodularity: for `R ≥ 6000`, a ball of radius `R + 161`
has less than `√2 · (9/10)` times the volume of the ball of radius `R`. -/
theorem count_volume_ineq {R ω N : ℝ} (hR : 6000 ≤ R) (hω : 0 < ω)
    (hN : 9 / 10 * (R ^ 8 * ω) ≤ N) {V : ℝ} (hV0 : 0 ≤ V) (hV : V ≤ (R + 161) ^ 8 * ω) :
    V ^ 2 < 2 * N ^ 2 := by
  have hR0 : (0 : ℝ) < R := by linarith
  have h1 : R + 161 ≤ 6161 / 6000 * R := by linarith
  have h2 : (R + 161) ^ 8 ≤ (6161 / 6000 * R) ^ 8 := pow_le_pow_left₀ (by linarith) h1 8
  have hA : 0 < R ^ 8 * ω := mul_pos (pow_pos hR0 8) hω
  have h3 : V ≤ (6161 / 6000 : ℝ) ^ 8 * (R ^ 8 * ω) := by
    calc V ≤ (R + 161) ^ 8 * ω := hV
      _ ≤ (6161 / 6000 * R) ^ 8 * ω := mul_le_mul_of_nonneg_right h2 hω.le
      _ = (6161 / 6000 : ℝ) ^ 8 * (R ^ 8 * ω) := by ring
  have h4 : V ^ 2 ≤ ((6161 / 6000 : ℝ) ^ 8 * (R ^ 8 * ω)) ^ 2 := pow_le_pow_left₀ hV0 h3 2
  have h5 : (9 / 10 * (R ^ 8 * ω)) ^ 2 ≤ N ^ 2 :=
    pow_le_pow_left₀ (by positivity) hN 2
  have h6 : ((6161 / 6000 : ℝ) ^ 8) ^ 2 < 2 * (9 / 10) ^ 2 := by norm_num
  have hA2 : 0 < (R ^ 8 * ω) ^ 2 := pow_pos hA 2
  calc V ^ 2 ≤ ((6161 / 6000 : ℝ) ^ 8 * (R ^ 8 * ω)) ^ 2 := h4
    _ = ((6161 / 6000 : ℝ) ^ 8) ^ 2 * (R ^ 8 * ω) ^ 2 := by ring
    _ < 2 * (9 / 10) ^ 2 * (R ^ 8 * ω) ^ 2 := mul_lt_mul_of_pos_right h6 hA2
    _ = 2 * (9 / 10 * (R ^ 8 * ω)) ^ 2 := by ring
    _ ≤ 2 * N ^ 2 := by linarith

/-- The rounded points together with the frame: generators of the local lattice. -/
def latticeGenerators (w : Fin 8 → Ambient 8) (G : Matrix (Fin 8) (Fin 8) ℤ)
    (Y : Finset (Ambient 8)) : Set (Ambient 8) :=
  (fun y => roundPoint w G y) '' (Y : Set (Ambient 8)) ∪ Set.range w

theorem roundPoint_mem_latticeGenerators (w : Fin 8 → Ambient 8) (G : Matrix (Fin 8) (Fin 8) ℤ)
    {Y : Finset (Ambient 8)} {y : Ambient 8} (hy : y ∈ Y) :
    roundPoint w G y ∈ latticeGenerators w G Y :=
  Or.inl ⟨y, hy, rfl⟩

theorem range_subset_latticeGenerators (w : Fin 8 → Ambient 8) (G : Matrix (Fin 8) (Fin 8) ℤ)
    (Y : Finset (Ambient 8)) : Set.range w ⊆ latticeGenerators w G Y :=
  Set.subset_union_right

namespace IntegralFrame

variable {w : Fin 8 → Ambient 8} {G : Matrix (Fin 8) (Fin 8) ℤ}

theorem norm_sub_round_le (hF : IntegralFrame w G) {θ : ℝ} (hθ0 : 0 ≤ θ) {y : Ambient 8}
    (hy : ∀ k, ∃ n : ℤ, |⟪y, w k⟫_ℝ - n| ≤ θ) : ‖y - roundPoint w G y‖ ≤ θ := by
  have h := norm_sub_roundPoint_le hF.gram hF.det_pos.ne' zero_le_one hθ0 hF.exists_coords
    hF.coord hy
  rwa [one_mul] at h

theorem small_mul_det (hF : IntegralFrame w G) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s * (40320 * 400 ^ 8) < 1) : s * (G.det : ℝ) < 1 :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_left hF.det_le hs0) hs

/-- Inner products of the generators are integers. -/
theorem generators_integral (hF : IntegralFrame w G) (Y : Finset (Ambient 8)) {θ ρ σ : ℝ}
    (hθ0 : 0 ≤ θ) (hρ0 : 0 ≤ ρ) (hπ : ∀ y ∈ Y, ‖y - roundPoint w G y‖ ≤ θ)
    (hYnorm : ∀ y ∈ Y, ‖y‖ ≤ ρ)
    (hYint : ∀ y ∈ Y, ∀ y' ∈ Y, ∃ k : ℤ, |⟪y, y'⟫_ℝ - k| ≤ σ)
    (hsmall : (σ + θ * (2 * ρ + θ)) * (G.det : ℝ) < 1) :
    ∀ x ∈ latticeGenerators w G Y, ∀ x' ∈ latticeGenerators w G Y,
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
theorem generators_even (hF : IntegralFrame w G) (Y : Finset (Ambient 8)) {θ ρ σ : ℝ}
    (hθ0 : 0 ≤ θ) (hρ0 : 0 ≤ ρ) (hπ : ∀ y ∈ Y, ‖y - roundPoint w G y‖ ≤ θ)
    (hYnorm : ∀ y ∈ Y, ‖y‖ ≤ ρ) (hYeven : ∀ y ∈ Y, ∃ k : ℤ, |‖y‖ ^ 2 - 2 * k| ≤ σ)
    (hsmall : (σ + θ * (2 * ρ + θ)) * (G.det : ℝ) < 1) :
    ∀ x ∈ latticeGenerators w G Y, ∃ k : ℤ, ‖x‖ ^ 2 = 2 * k := by
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

end IntegralFrame

/-- **The local lattice.** A finite set `Y ⊂ ℝ⁸` with almost integral inner products against an
integral frame and among its points, almost even squared norms, and at least `(9/10)·vol(B_R)`
points in a ball of radius about `R`, lies within `θ` of an isometric copy of `E8`. -/
theorem exists_isometry_of_integralFrame {w : Fin 8 → Ambient 8}
    {G : Matrix (Fin 8) (Fin 8) ℤ} (hF : IntegralFrame w G) (Y : Finset (Ambient 8))
    {c : Ambient 8} {R θ σ : ℝ} (hR : 6000 ≤ R) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 8) (hσ0 : 0 ≤ σ)
    (hYball : ∀ y ∈ Y, ‖y - c‖ ≤ R + 1 / 8) (hYnorm : ∀ y ∈ Y, ‖y‖ ≤ 3 * R)
    (hYsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 1 ≤ ‖y - y'‖)
    (hYround : ∀ y ∈ Y, ∀ k, ∃ n : ℤ, |⟪y, w k⟫_ℝ - n| ≤ θ)
    (hYint : ∀ y ∈ Y, ∀ y' ∈ Y, ∃ k : ℤ, |⟪y, y'⟫_ℝ - k| ≤ σ)
    (hYeven : ∀ y ∈ Y, ∃ k : ℤ, |‖y‖ ^ 2 - 2 * k| ≤ σ)
    (hsmall : (σ + θ * (6 * R + θ)) * (40320 * 400 ^ 8) < 1)
    (hcount : 9 / 10 * volume.real (closedBall (0 : Ambient 8) R) ≤ Y.card) :
    ∃ Φ : Ambient 8 ≃ₗᵢ[ℝ] Ambient 8, ∀ y ∈ Y, ∃ z ∈ e8Set, ‖y - Φ z‖ ≤ θ := by
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
      Submodule.span ℤ (latticeGenerators w G Y) := by
    rw [hF.range_basis]
    exact Submodule.span_mono (range_subset_latticeGenerators w G Y)
  -- the rounded points are distinct
  have hinj : Set.InjOn (fun y => roundPoint w G y) (Y : Set (Ambient 8)) := by
    intro y hy y' hy' he
    by_contra hne
    have h1 := hYsep y hy y' hy' hne
    have he' : roundPoint w G y = roundPoint w G y' := he
    have e : y - y' = (y - roundPoint w G y) - (y' - roundPoint w G y') := by
      rw [he']
      abel
    have h2 : ‖y - y'‖ ≤ θ + θ := by
      rw [e]
      exact (norm_sub_le _ _).trans (add_le_add (hπ y hy) (hπ y' hy'))
    linarith
  have hcard : (Y.image fun y => roundPoint w G y).card = Y.card :=
    Finset.card_image_of_injOn hinj
  have hT : ∀ t ∈ Y.image (fun y => roundPoint w G y),
      t ∈ Submodule.span ℤ (latticeGenerators w G Y) := by
    intro t ht
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
    exact Submodule.subset_span (roundPoint_mem_latticeGenerators w G hy)
  have hball : ∀ t ∈ Y.image (fun y => roundPoint w G y), t ∈ closedBall c (R + 1 / 4) := by
    intro t ht
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
    rw [mem_closedBall, dist_eq_norm]
    have e : roundPoint w G y - c = (y - c) - (y - roundPoint w G y) := by abel
    rw [e]
    have h := (norm_sub_le (y - c) (y - roundPoint w G y)).trans
      (add_le_add (hYball y hy) (hπ y hy))
    linarith
  -- the volume inequality
  have hsum : ∑ i, ‖hF.basis i‖ ≤ 160 := by
    calc ∑ i, ‖hF.basis i‖ ≤ ∑ _i : Fin 8, (20 : ℝ) := Finset.sum_le_sum fun i _ => by
          rw [hF.basis_apply]
          exact hF.norm_le i
      _ = 160 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          norm_num
  have hsum0 : 0 ≤ ∑ i, ‖hF.basis i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hr0 : 0 ≤ R + 1 / 4 + ∑ i, ‖hF.basis i‖ := by linarith
  have hV : volume.real (closedBall c (R + 1 / 4 + ∑ i, ‖hF.basis i‖)) ≤
      (R + 161) ^ 8 * volume.real (ball (0 : Ambient 8) 1) := by
    rw [volume_real_closedBall_eight c hr0]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr0 (by linarith) 8)
      volume_real_unitBall_eight_pos.le
  have hN : 9 / 10 * (R ^ 8 * volume.real (ball (0 : Ambient 8) 1)) ≤
      ((Y.image fun y => roundPoint w G y).card : ℝ) := by
    rw [hcard, ← volume_real_closedBall_eight (0 : Ambient 8) hR0]
    exact hcount
  have hcnt := count_volume_ineq hR volume_real_unitBall_eight_pos hN measureReal_nonneg hV
  obtain ⟨Φ, hΦ⟩ := exists_isometry_image_e8Set_eq_of_even_lattice_count
    (Submodule.span ℤ (latticeGenerators w G Y)) hLint hLeven hF.basis hle _ hT hball hcnt
  refine ⟨Φ, fun y hy => ?_⟩
  have hmem : roundPoint w G y ∈
      ((Submodule.span ℤ (latticeGenerators w G Y) : Submodule ℤ (Ambient 8)) :
        Set (Ambient 8)) :=
    Submodule.subset_span (roundPoint_mem_latticeGenerators w G hy)
  rw [← hΦ] at hmem
  obtain ⟨z, hz, hzy⟩ := hmem
  exact ⟨z, hz, by rw [hzy]; exact hπ y hy⟩

end E8Leech
