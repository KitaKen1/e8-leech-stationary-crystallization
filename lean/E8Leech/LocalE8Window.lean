import E8Leech.LocalE8Lattice
import E8Leech.BRRGramApproximation

/-!
# An almost integral window with a frame lies near a copy of `E8` (BRR, Steps 2–4)

Let `X ⊂ ℝ⁸` be a finite set in a ball `B(u,R)`, `R ≥ 6000`, such that

* squared distances of points of `X` are within `η` of even integers, `η R² ≤ 10⁻²⁹`,
* distinct points are at distance at least `√2`,
* `X` contains `p₀` and `p₀ + vᵢ` for a frame `v` with `|vᵢ - 16 eᵢ| ≤ 2√2`,
* `X` has at least `(9/10)·vol(B_R)` points.

Then there is a linear isometry `Φ` with every `x - p₀`, `x ∈ X`, within `46 η R` of `Φ(E8)`
(`exists_isometry_near_e8Set_of_window`).

The Gram matrix of the frame is within `(3/2)η` of an integer matrix; the Gram correction `P`
(`exists_gram_correction`) makes it exact and moves points by a relative amount `(3/8)η`. The
corrected window `P(X - p₀)` satisfies the hypotheses of `exists_isometry_of_integralFrame`.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric
open scoped InnerProductSpace

section Near

variable {d : ℕ} {P : Ambient d →ₗ[ℝ] Ambient d} {ε : ℝ}

theorem norm_map_le_of_near (hP : ∀ x, ‖P x - x‖ ≤ ε * ‖x‖) (x : Ambient d) :
    ‖P x‖ ≤ (1 + ε) * ‖x‖ := by
  have h := norm_add_le (P x - x) x
  rw [sub_add_cancel] at h
  linarith [hP x]

theorem norm_le_map_of_near (hP : ∀ x, ‖P x - x‖ ≤ ε * ‖x‖) (x : Ambient d) :
    (1 - ε) * ‖x‖ ≤ ‖P x‖ := by
  have h := norm_sub_le (P x) (P x - x)
  rw [sub_sub_cancel] at h
  linarith [hP x]

/-- A linear map close to the identity almost preserves inner products. -/
theorem abs_inner_map_sub_inner_le (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (hP : ∀ x, ‖P x - x‖ ≤ ε * ‖x‖) (a b : Ambient d) :
    |⟪P a, P b⟫_ℝ - ⟪a, b⟫_ℝ| ≤ 3 * ε * ‖a‖ * ‖b‖ := by
  have e : ⟪P a, P b⟫_ℝ - ⟪a, b⟫_ℝ = ⟪P a - a, P b⟫_ℝ + ⟪a, P b - b⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right]
    ring
  have h1 : |⟪P a - a, P b⟫_ℝ| ≤ ε * ‖a‖ * ((1 + ε) * ‖b‖) :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hP a) (norm_map_le_of_near hP b) (norm_nonneg _)
        (mul_nonneg hε0 (norm_nonneg _)))
  have h2 : |⟪a, P b - b⟫_ℝ| ≤ ‖a‖ * (ε * ‖b‖) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hP b) (norm_nonneg _))
  have hab : 0 ≤ ‖a‖ * ‖b‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [e]
  calc |⟪P a - a, P b⟫_ℝ + ⟪a, P b - b⟫_ℝ|
      ≤ |⟪P a - a, P b⟫_ℝ| + |⟪a, P b - b⟫_ℝ| := abs_add_le _ _
    _ ≤ ε * ‖a‖ * ((1 + ε) * ‖b‖) + ‖a‖ * (ε * ‖b‖) := add_le_add h1 h2
    _ = ε * (2 + ε) * (‖a‖ * ‖b‖) := by ring
    _ ≤ ε * 3 * (‖a‖ * ‖b‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hε0) hab
    _ = 3 * ε * ‖a‖ * ‖b‖ := by ring

end Near

/-- Inner products of differences in a window with almost even squared distances. -/
theorem window_inner_approx {X : Finset (Ambient 8)} {η : ℝ}
    (hpair : ∀ x ∈ X, ∀ y ∈ X, ∃ k : ℤ, |‖x - y‖ ^ 2 - 2 * k| ≤ η) {a x y : Ambient 8}
    (ha : a ∈ X) (hx : x ∈ X) (hy : y ∈ X) :
    ∃ m : ℤ, |⟪x - a, y - a⟫_ℝ - m| ≤ 3 / 2 * η := by
  have he : (x - a) - (y - a) = x - y := by abel
  exact exists_integer_inner_approx (hpair x hx a ha) (hpair y hy a ha)
    (by rw [he]; exact hpair x hx y hy)

/-- The integer Gram matrix of a frame of the window and its correction. -/
theorem exists_frame_gram_correction {X : Finset (Ambient 8)} {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 10)
    (hpair : ∀ x ∈ X, ∀ y ∈ X, ∃ k : ℤ, |‖x - y‖ ^ 2 - 2 * k| ≤ η) {p₀ : Ambient 8}
    (hp₀ : p₀ ∈ X) {v : Fin 8 → Ambient 8} (hv : ∀ i, p₀ + v i ∈ X)
    (hframe : ∀ i, ‖v i - (16 : ℝ) • EuclideanSpace.basisFun (Fin 8) ℝ i‖ ≤ 2 * Real.sqrt 2) :
    ∃ (G : Matrix (Fin 8) (Fin 8) ℤ) (P : Ambient 8 →ₗ[ℝ] Ambient 8),
      (∀ i j, ⟪P (v i), P (v j)⟫_ℝ = (G i j : ℝ)) ∧ (∀ i, (2 : ℤ) ∣ G i i) ∧
        ∀ x, ‖P x - x‖ ≤ 3 / 8 * η * ‖x‖ := by
  have hK : ∀ i j, ∃ k : ℤ, |⟪v i, v j⟫_ℝ - k| ≤ 3 / 2 * η := by
    intro i j
    have h := window_inner_approx hpair hp₀ (hv i) (hv j)
    simpa only [add_sub_cancel_left] using h
  choose K hK' using hK
  have hsmall : 3 / 2 * η < 1 / 2 := by linarith
  have hsymm : ∀ i j, K i j = K j i := integer_gram_symmetric hsmall hK'
  have heven : ∀ i, (2 : ℤ) ∣ K i i := by
    intro i
    obtain ⟨a, ha⟩ := hpair (p₀ + v i) (hv i) p₀ hp₀
    rw [add_sub_cancel_left] at ha
    refine ⟨a, ?_⟩
    have h1 : |‖v i‖ ^ 2 - ((K i i : ℤ) : ℝ)| ≤ 3 / 2 * η := by
      rw [← real_inner_self_eq_norm_sq]
      exact hK' i i
    have h2 : |‖v i‖ ^ 2 - ((2 * a : ℤ) : ℝ)| ≤ 3 / 2 * η := by
      have e : ((2 * a : ℤ) : ℝ) = 2 * (a : ℝ) := by norm_num
      rw [e]
      linarith
    exact integer_approx_unique hsmall h1 h2
  have hδ0 : (0 : ℝ) ≤ 3 / 2 * η := by linarith
  have hquad : ∀ a : Fin 8 → ℝ,
      |∑ j, ∑ k, a j * ((Matrix.of K).map (Int.cast : ℤ → ℝ)) j k * a k -
          ‖∑ j, a j • v j‖ ^ 2| ≤ 3 / 2 * η * (1 / 2) ^ 2 * ‖∑ j, a j • v j‖ ^ 2 :=
    gram_quadratic_bound _ hδ0 (fun j k => by
      rw [Matrix.map_apply, Matrix.of_apply, abs_sub_comm]
      exact hK' j k) (frame_sum_abs_le hframe)
  have hε0 : (0 : ℝ) ≤ 3 / 2 * η * (1 / 2) ^ 2 := by linarith
  have hε1 : 3 / 2 * η * (1 / 2) ^ 2 ≤ 1 := by linarith
  obtain ⟨P, hP1, hP2⟩ := exists_gram_correction (frame_linearIndependent hframe)
    ((Matrix.of K).map (Int.cast : ℤ → ℝ))
    (fun j k => by
      rw [Matrix.map_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply, hsymm j k])
    hε0 hε1 hquad
  refine ⟨Matrix.of K, P, fun i j => ?_, heven, fun x => ?_⟩
  · rw [hP1 i j, Matrix.map_apply]
  · have h := hP2 x
    have e : 3 / 2 * η * (1 / 2) ^ 2 = 3 / 8 * η := by ring
    rw [e] at h
    exact h

/-- The corrected frame is an integral frame. -/
theorem integralFrame_of_near {v : Fin 8 → Ambient 8}
    (hframe : ∀ i, ‖v i - (16 : ℝ) • EuclideanSpace.basisFun (Fin 8) ℝ i‖ ≤ 2 * Real.sqrt 2)
    {P : Ambient 8 →ₗ[ℝ] Ambient 8} {G : Matrix (Fin 8) (Fin 8) ℤ} {ε : ℝ} (hε : ε ≤ 1 / 20)
    (hP : ∀ x, ‖P x - x‖ ≤ ε * ‖x‖) (hG : ∀ i j, ⟪P (v i), P (v j)⟫_ℝ = (G i j : ℝ))
    (heven : ∀ i, (2 : ℤ) ∣ G i i) : IntegralFrame (fun i => P (v i)) G := by
  refine ⟨hG, heven, fun a => ?_, fun i => ?_⟩
  · have h1 := frame_sum_abs_le hframe a
    have h2 := norm_le_map_of_near hP (∑ j, a j • v j)
    have e : P (∑ j, a j • v j) = ∑ j, a j • P (v j) := by simp only [map_sum, map_smul]
    rw [e] at h2
    have hn : 0 ≤ ‖∑ j, a j • v j‖ := norm_nonneg _
    have h3 : 1 / 2 * ‖∑ j, a j • v j‖ ≤ (1 - ε) * ‖∑ j, a j • v j‖ :=
      mul_le_mul_of_nonneg_right (by linarith) hn
    linarith
  · have h1 := norm_map_le_of_near hP (v i)
    have h2 := frame_norm_le hframe i
    have h3 : (1 + ε) * ‖v i‖ ≤ (1 + 1 / 20) * 19 :=
      mul_le_mul (by linarith) h2 (norm_nonneg _) (by norm_num)
    have h4 : ‖P (v i)‖ ≤ (1 + 1 / 20) * 19 := h1.trans h3
    norm_num at h4 ⊢
    linarith

/-- The hypotheses on a window with a frame, after the Gram correction `P`. -/
structure CorrectedWindow (X : Finset (Ambient 8)) (u p₀ : Ambient 8) (R η : ℝ)
    (v : Fin 8 → Ambient 8) (P : Ambient 8 →ₗ[ℝ] Ambient 8) : Prop where
  radius : 6000 ≤ R
  eta_nonneg : 0 ≤ η
  eta_small : η * R ^ 2 ≤ 1 / 10 ^ 29
  ball : ∀ x ∈ X, x ∈ closedBall u R
  pair : ∀ x ∈ X, ∀ y ∈ X, ∃ k : ℤ, |‖x - y‖ ^ 2 - 2 * k| ≤ η
  sep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → Real.sqrt 2 ≤ dist x y
  base : p₀ ∈ X
  frame_mem : ∀ i, p₀ + v i ∈ X
  frame : ∀ i, ‖v i - (16 : ℝ) • EuclideanSpace.basisFun (Fin 8) ℝ i‖ ≤ 2 * Real.sqrt 2
  near : ∀ x, ‖P x - x‖ ≤ 3 / 8 * η * ‖x‖

namespace CorrectedWindow

variable {X : Finset (Ambient 8)} {u p₀ : Ambient 8} {R η : ℝ} {v : Fin 8 → Ambient 8}
  {P : Ambient 8 →ₗ[ℝ] Ambient 8}

theorem etaR_le_etaR2 (h : CorrectedWindow X u p₀ R η v P) : η * R ≤ η * R ^ 2 := by
  have hR := h.radius
  have h0 := h.eta_nonneg
  have h1 : η * R * 1 ≤ η * R * R :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg h0 (by linarith))
  nlinarith

theorem eta_le_etaR (h : CorrectedWindow X u p₀ R η v P) : η ≤ η * R := by
  have hR := h.radius
  have h0 := h.eta_nonneg
  have h1 : η * 1 ≤ η * R := mul_le_mul_of_nonneg_left (by linarith) h0
  linarith

theorem etaR_small (h : CorrectedWindow X u p₀ R η v P) : η * R ≤ 1 / 10 ^ 29 :=
  h.etaR_le_etaR2.trans h.eta_small

theorem eta_le (h : CorrectedWindow X u p₀ R η v P) : η ≤ 1 / 10 ^ 29 :=
  h.eta_le_etaR.trans h.etaR_small

theorem eps_nonneg (h : CorrectedWindow X u p₀ R η v P) : (0 : ℝ) ≤ 3 / 8 * η := by
  have h0 := h.eta_nonneg
  linarith

theorem eps_le (h : CorrectedWindow X u p₀ R η v P) : 3 / 8 * η ≤ 1 / 20 := by
  have h1 := h.eta_le
  norm_num at h1 ⊢
  linarith

theorem norm_sub_base_le (h : CorrectedWindow X u p₀ R η v P) {x : Ambient 8} (hx : x ∈ X) :
    ‖x - p₀‖ ≤ 2 * R := by
  have h1 := h.ball x hx
  have h2 := h.ball p₀ h.base
  rw [mem_closedBall, dist_eq_norm] at h1 h2
  have e : x - p₀ = (x - u) - (p₀ - u) := by abel
  rw [e]
  exact (norm_sub_le _ _).trans (by linarith)

/-- Inner products of two corrected points are almost integers. -/
theorem inner_approx (h : CorrectedWindow X u p₀ R η v P) {x x' : Ambient 8} (hx : x ∈ X)
    (hx' : x' ∈ X) : ∃ k : ℤ, |⟪P (x - p₀), P (x' - p₀)⟫_ℝ - k| ≤ 6 * η * R ^ 2 := by
  obtain ⟨k, hk⟩ := window_inner_approx h.pair h.base hx hx'
  refine ⟨k, ?_⟩
  have h1 := abs_inner_map_sub_inner_le h.eps_nonneg (by linarith [h.eps_le]) h.near
    (x - p₀) (x' - p₀)
  have hR := h.radius
  have h0 := h.eta_nonneg
  have hn := h.norm_sub_base_le hx
  have hn' := h.norm_sub_base_le hx'
  have h2 : ‖x - p₀‖ * ‖x' - p₀‖ ≤ 2 * R * (2 * R) :=
    mul_le_mul hn hn' (norm_nonneg _) (by linarith)
  have h3 : 3 * (3 / 8 * η) * ‖x - p₀‖ * ‖x' - p₀‖ ≤ 3 * (3 / 8 * η) * (2 * R * (2 * R)) := by
    have h4 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 3 * (3 / 8 * η))
    linarith
  have h5 : η ≤ η * R ^ 2 := h.eta_le_etaR.trans h.etaR_le_etaR2
  have e : ⟪P (x - p₀), P (x' - p₀)⟫_ℝ - k =
      (⟪P (x - p₀), P (x' - p₀)⟫_ℝ - ⟪x - p₀, x' - p₀⟫_ℝ) + (⟪x - p₀, x' - p₀⟫_ℝ - k) := by
    ring
  rw [e]
  calc _ ≤ |⟪P (x - p₀), P (x' - p₀)⟫_ℝ - ⟪x - p₀, x' - p₀⟫_ℝ| + |⟪x - p₀, x' - p₀⟫_ℝ - k| :=
        abs_add_le _ _
    _ ≤ 3 * (3 / 8 * η) * (2 * R * (2 * R)) + 3 / 2 * η := add_le_add (h1.trans h3) hk
    _ ≤ 6 * η * R ^ 2 := by nlinarith

/-- Squared norms of corrected points are almost even integers. -/
theorem norm_sq_approx (h : CorrectedWindow X u p₀ R η v P) {x : Ambient 8} (hx : x ∈ X) :
    ∃ k : ℤ, |‖P (x - p₀)‖ ^ 2 - 2 * k| ≤ 6 * η * R ^ 2 := by
  obtain ⟨k, hk⟩ := h.pair x hx p₀ h.base
  refine ⟨k, ?_⟩
  have h1 := abs_inner_map_sub_inner_le h.eps_nonneg (by linarith [h.eps_le]) h.near
    (x - p₀) (x - p₀)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h1
  have hR := h.radius
  have h0 := h.eta_nonneg
  have hn := h.norm_sub_base_le hx
  have h2 : ‖x - p₀‖ * ‖x - p₀‖ ≤ 2 * R * (2 * R) :=
    mul_le_mul hn hn (norm_nonneg _) (by linarith)
  have h3 : 3 * (3 / 8 * η) * ‖x - p₀‖ * ‖x - p₀‖ ≤ 3 * (3 / 8 * η) * (2 * R * (2 * R)) := by
    have h4 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 3 * (3 / 8 * η))
    linarith
  have h5 : η ≤ η * R ^ 2 := h.eta_le_etaR.trans h.etaR_le_etaR2
  have e : ‖P (x - p₀)‖ ^ 2 - 2 * k =
      (‖P (x - p₀)‖ ^ 2 - ‖x - p₀‖ ^ 2) + (‖x - p₀‖ ^ 2 - 2 * k) := by ring
  rw [e]
  calc _ ≤ |‖P (x - p₀)‖ ^ 2 - ‖x - p₀‖ ^ 2| + |‖x - p₀‖ ^ 2 - 2 * k| := abs_add_le _ _
    _ ≤ 3 * (3 / 8 * η) * (2 * R * (2 * R)) + η := add_le_add (h1.trans h3) hk
    _ ≤ 6 * η * R ^ 2 := by nlinarith

/-- Inner products of corrected points with the corrected frame are almost integers. -/
theorem frame_approx (h : CorrectedWindow X u p₀ R η v P) {x : Ambient 8} (hx : x ∈ X)
    (k : Fin 8) : ∃ n : ℤ, |⟪P (x - p₀), P (v k)⟫_ℝ - n| ≤ 45 * η * R := by
  obtain ⟨n, hn⟩ := window_inner_approx h.pair h.base hx (h.frame_mem k)
  rw [add_sub_cancel_left] at hn
  refine ⟨n, ?_⟩
  have h1 := abs_inner_map_sub_inner_le h.eps_nonneg (by linarith [h.eps_le]) h.near
    (x - p₀) (v k)
  have hR := h.radius
  have h0 := h.eta_nonneg
  have hx' := h.norm_sub_base_le hx
  have hv := frame_norm_le h.frame k
  have h2 : ‖x - p₀‖ * ‖v k‖ ≤ 2 * R * 19 := mul_le_mul hx' hv (norm_nonneg _) (by linarith)
  have h3 : 3 * (3 / 8 * η) * ‖x - p₀‖ * ‖v k‖ ≤ 3 * (3 / 8 * η) * (2 * R * 19) := by
    have h4 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 3 * (3 / 8 * η))
    linarith
  have h5 := h.eta_le_etaR
  have e : ⟪P (x - p₀), P (v k)⟫_ℝ - n =
      (⟪P (x - p₀), P (v k)⟫_ℝ - ⟪x - p₀, v k⟫_ℝ) + (⟪x - p₀, v k⟫_ℝ - n) := by ring
  rw [e]
  calc _ ≤ |⟪P (x - p₀), P (v k)⟫_ℝ - ⟪x - p₀, v k⟫_ℝ| + |⟪x - p₀, v k⟫_ℝ - n| :=
        abs_add_le _ _
    _ ≤ 3 * (3 / 8 * η) * (2 * R * 19) + 3 / 2 * η := add_le_add (h1.trans h3) hn
    _ ≤ 45 * η * R := by nlinarith

/-- The points of the corrected window are distinct. -/
theorem injOn_corrected (h : CorrectedWindow X u p₀ R η v P) :
    Set.InjOn (fun x => P (x - p₀)) (X : Set (Ambient 8)) := by
  intro x _ x' _ he
  have he' : P (x - p₀) = P (x' - p₀) := he
  have e : P (x - x') = 0 := by
    have e1 : x - x' = (x - p₀) - (x' - p₀) := by abel
    rw [e1, map_sub, he', sub_self]
  have h1 := norm_le_map_of_near h.near (x - x')
  rw [e, norm_zero] at h1
  have h2 := h.eps_le
  have hn : 0 ≤ ‖x - x'‖ := norm_nonneg _
  have h3 : ‖x - x'‖ = 0 := by nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp h3)

/-- The smallness condition of `exists_isometry_of_integralFrame` for the window. -/
theorem small (h : CorrectedWindow X u p₀ R η v P) :
    (6 * η * R ^ 2 + 45 * η * R * (6 * R + 45 * η * R)) * (40320 * 400 ^ 8) < 1 := by
  have hR := h.radius
  have h0 := h.eta_nonneg
  have hA := h.eta_small
  have hB := h.etaR_small
  have hB0 : 0 ≤ η * R := mul_nonneg h0 (by linarith)
  have hB1 : η * R ≤ 1 := hB.trans (by norm_num)
  have hBB : (η * R) * (η * R) ≤ 1 * (η * R) := mul_le_mul_of_nonneg_right hB1 hB0
  have e : 6 * η * R ^ 2 + 45 * η * R * (6 * R + 45 * η * R) =
      276 * (η * R ^ 2) + 2025 * ((η * R) * (η * R)) := by ring
  rw [e]
  have h1 : 276 * (η * R ^ 2) + 2025 * ((η * R) * (η * R)) ≤ 2301 / 10 ^ 29 := by
    have h2 : 2025 * ((η * R) * (η * R)) ≤ 2025 * (1 / 10 ^ 29) := by linarith
    have h3 : 276 * (η * R ^ 2) ≤ 276 * (1 / 10 ^ 29) := by linarith
    linarith
  calc (276 * (η * R ^ 2) + 2025 * ((η * R) * (η * R))) * (40320 * 400 ^ 8)
      ≤ 2301 / 10 ^ 29 * (40320 * 400 ^ 8) := mul_le_mul_of_nonneg_right h1 (by norm_num)
    _ < 1 := by norm_num

/-- **The window theorem after the Gram correction.** -/
theorem exists_isometry (h : CorrectedWindow X u p₀ R η v P) {G : Matrix (Fin 8) (Fin 8) ℤ}
    (hG : ∀ i j, ⟪P (v i), P (v j)⟫_ℝ = (G i j : ℝ)) (heven : ∀ i, (2 : ℤ) ∣ G i i)
    (hcount : 9 / 10 * volume.real (closedBall (0 : Ambient 8) R) ≤ X.card) :
    ∃ Φ : Ambient 8 ≃ₗᵢ[ℝ] Ambient 8, ∀ x ∈ X, ∃ z ∈ e8Set,
      ‖(x - p₀) - Φ z‖ ≤ 46 * η * R := by
  classical
  have hR := h.radius
  have h0 := h.eta_nonneg
  have hB := h.etaR_small
  have hB0 : 0 ≤ η * R := mul_nonneg h0 (by linarith)
  have hε := h.eps_le
  have hF : IntegralFrame (fun i => P (v i)) G :=
    integralFrame_of_near h.frame h.eps_le h.near hG heven
  have hθ0 : (0 : ℝ) ≤ 45 * η * R := by linarith
  have hθ : 45 * η * R ≤ 1 / 8 := by
    have h1 : 45 * (η * R) ≤ 45 * (1 / 10 ^ 29) := by linarith
    have h2 : (45 : ℝ) * (1 / 10 ^ 29) ≤ 1 / 8 := by norm_num
    linarith
  have hσ0 : (0 : ℝ) ≤ 6 * η * R ^ 2 := by
    have h1 : 0 ≤ η * R ^ 2 := mul_nonneg h0 (sq_nonneg R)
    linarith
  have hs2 : (1.4 : ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt' (by norm_num)).mpr (by norm_num)
  have hYball : ∀ y ∈ X.image (fun x => P (x - p₀)), ‖y - P (u - p₀)‖ ≤ R + 1 / 8 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have e : P (x - p₀) - P (u - p₀) = P (x - u) := by
      rw [← map_sub]
      congr 1
      abel
    rw [e]
    have h1 := norm_map_le_of_near h.near (x - u)
    have h2 := h.ball x hx
    rw [mem_closedBall, dist_eq_norm] at h2
    have h3 : (1 + 3 / 8 * η) * ‖x - u‖ ≤ (1 + 3 / 8 * η) * R :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    nlinarith
  have hYnorm : ∀ y ∈ X.image (fun x => P (x - p₀)), ‖y‖ ≤ 3 * R := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have h1 := norm_map_le_of_near h.near (x - p₀)
    have h2 := h.norm_sub_base_le hx
    have h3 : (1 + 3 / 8 * η) * ‖x - p₀‖ ≤ (1 + 1 / 20) * (2 * R) :=
      mul_le_mul (by linarith) h2 (norm_nonneg _) (by norm_num)
    linarith
  have hYsep : ∀ y ∈ X.image (fun x => P (x - p₀)), ∀ y' ∈ X.image (fun x => P (x - p₀)),
      y ≠ y' → 1 ≤ ‖y - y'‖ := by
    intro y hy y' hy' hne
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hy'
    have hxx : x ≠ x' := fun e => hne (by rw [e])
    have h1 := h.sep x hx x' hx' hxx
    rw [dist_eq_norm] at h1
    have e : P (x - p₀) - P (x' - p₀) = P (x - x') := by
      rw [← map_sub]
      congr 1
      abel
    rw [e]
    have h2 := norm_le_map_of_near h.near (x - x')
    have h3 : (1 - 1 / 20) * 1.4 ≤ (1 - 3 / 8 * η) * ‖x - x'‖ :=
      mul_le_mul (by linarith) (hs2.trans h1) (by norm_num) (by linarith)
    norm_num at h3
    linarith
  have hYround : ∀ y ∈ X.image (fun x => P (x - p₀)), ∀ k,
      ∃ n : ℤ, |⟪y, P (v k)⟫_ℝ - n| ≤ 45 * η * R := by
    intro y hy k
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact h.frame_approx hx k
  have hYint : ∀ y ∈ X.image (fun x => P (x - p₀)), ∀ y' ∈ X.image (fun x => P (x - p₀)),
      ∃ k : ℤ, |⟪y, y'⟫_ℝ - k| ≤ 6 * η * R ^ 2 := by
    intro y hy y' hy'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hy'
    exact h.inner_approx hx hx'
  have hYeven : ∀ y ∈ X.image (fun x => P (x - p₀)),
      ∃ k : ℤ, |‖y‖ ^ 2 - 2 * k| ≤ 6 * η * R ^ 2 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact h.norm_sq_approx hx
  have hcard : (X.image fun x => P (x - p₀)).card = X.card :=
    Finset.card_image_of_injOn h.injOn_corrected
  have hcount' : 9 / 10 * volume.real (closedBall (0 : Ambient 8) R) ≤
      ((X.image fun x => P (x - p₀)).card : ℝ) := by
    rw [hcard]
    exact hcount
  obtain ⟨Φ, hΦ⟩ := exists_isometry_of_integralFrame hF (X.image fun x => P (x - p₀))
    (c := P (u - p₀)) hR hθ0 hθ hσ0 hYball hYnorm hYsep hYround hYint hYeven h.small hcount'
  refine ⟨Φ, fun x hx => ?_⟩
  obtain ⟨z, hz, hzy⟩ := hΦ (P (x - p₀)) (Finset.mem_image_of_mem _ hx)
  refine ⟨z, hz, ?_⟩
  have h1 := h.near (x - p₀)
  rw [norm_sub_rev] at h1
  have h2 := h.norm_sub_base_le hx
  have h3 : 3 / 8 * η * ‖x - p₀‖ ≤ 3 / 8 * η * (2 * R) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have e : (x - p₀) - Φ z = ((x - p₀) - P (x - p₀)) + (P (x - p₀) - Φ z) := by abel
  rw [e]
  calc ‖((x - p₀) - P (x - p₀)) + (P (x - p₀) - Φ z)‖
      ≤ ‖(x - p₀) - P (x - p₀)‖ + ‖P (x - p₀) - Φ z‖ := norm_add_le _ _
    _ ≤ 3 / 8 * η * (2 * R) + 45 * η * R := add_le_add (h1.trans h3) hzy
    _ ≤ 46 * η * R := by nlinarith

end CorrectedWindow

/-- **An almost integral window with a frame lies near a copy of `E8`.** -/
theorem exists_isometry_near_e8Set_of_window {X : Finset (Ambient 8)} {u p₀ : Ambient 8}
    {R η : ℝ} {v : Fin 8 → Ambient 8} (hR : 6000 ≤ R) (hη0 : 0 ≤ η)
    (hη : η * R ^ 2 ≤ 1 / 10 ^ 29) (hball : ∀ x ∈ X, x ∈ closedBall u R)
    (hpair : ∀ x ∈ X, ∀ y ∈ X, ∃ k : ℤ, |‖x - y‖ ^ 2 - 2 * k| ≤ η)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → Real.sqrt 2 ≤ dist x y) (hp₀ : p₀ ∈ X)
    (hv : ∀ i, p₀ + v i ∈ X)
    (hframe : ∀ i, ‖v i - (16 : ℝ) • EuclideanSpace.basisFun (Fin 8) ℝ i‖ ≤ 2 * Real.sqrt 2)
    (hcount : 9 / 10 * volume.real (closedBall (0 : Ambient 8) R) ≤ X.card) :
    ∃ Φ : Ambient 8 ≃ₗᵢ[ℝ] Ambient 8, ∀ x ∈ X, ∃ z ∈ e8Set,
      ‖(x - p₀) - Φ z‖ ≤ 46 * η * R := by
  have hη1 : η ≤ 1 / 10 := by
    have h1 : η * 1 ≤ η * R ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hη0
    have h2 : (1 : ℝ) / 10 ^ 29 ≤ 1 / 10 := by norm_num
    linarith
  obtain ⟨G, P, hG, heven, hP⟩ := exists_frame_gram_correction hη0 hη1 hpair hp₀ hv hframe
  exact CorrectedWindow.exists_isometry ⟨hR, hη0, hη, hball, hpair, hsep, hp₀, hv, hframe, hP⟩
    hG heven hcount

end E8Leech
