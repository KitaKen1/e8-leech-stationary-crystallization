import E8Leech.LocalLeechLattice
import E8Leech.LocalE8Window

/-!
# An almost integral window with a frame lies near a copy of the Leech lattice (BRR, Steps 2–4)

The rank 24 version of `LocalE8Window` and `SaturatedWindow`. Let `X ⊂ ℝ²⁴` be a finite set in a
ball `B(u,R)`, `R ≥ 200000`, such that

* squared distances of points of `X` are within `η` of even integers, `η R² ≤ 10⁻¹¹⁵`,
* distinct points are at distance at least `2`,
* `X` contains `p₀` and `p₀ + vᵢ` for a frame `v` with `|vᵢ - 64 eᵢ| ≤ 4`,
* `X` has at least `(9/10)·vol(B_R)` points.

Then, given the characterization of the Leech lattice, there is a linear isometry `Φ` with every
`x - p₀`, `x ∈ X`, within `13 η R` of `Φ(Λ₂₄)` (`exists_isometry_near_leechSet_of_window`).
For a set saturated near `u` the frame exists (`exists_leechFrame_of_saturated`), which gives
`exists_isometry_near_leechSet_of_saturated`.

The Gram matrix of the frame is within `(3/2)η` of an integer matrix; the Gram correction `P`
(`exists_gram_correction`) makes it exact and moves points by a relative amount `(3/128)η`. The
corrected window `P(X - p₀)` satisfies the hypotheses of `exists_isometry_of_leechIntegralFrame`.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric
open scoped InnerProductSpace

/-- Inner products of differences in a window with almost even squared distances. -/
theorem window_inner_approx_of_pair {d : ℕ} {X : Finset (Ambient d)} {η : ℝ}
    (hpair : ∀ x ∈ X, ∀ y ∈ X, ∃ k : ℤ, |‖x - y‖ ^ 2 - 2 * k| ≤ η) {a x y : Ambient d}
    (ha : a ∈ X) (hx : x ∈ X) (hy : y ∈ X) :
    ∃ m : ℤ, |⟪x - a, y - a⟫_ℝ - m| ≤ 3 / 2 * η := by
  have he : (x - a) - (y - a) = x - y := by abel
  exact exists_integer_inner_approx (hpair x hx a ha) (hpair y hy a ha)
    (by rw [he]; exact hpair x hx y hy)

/-- The integer Gram matrix of a frame of the window and its correction. -/
theorem exists_leechFrame_gram_correction {X : Finset (Ambient 24)} {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 10)
    (hpair : ∀ x ∈ X, ∀ y ∈ X, ∃ k : ℤ, |‖x - y‖ ^ 2 - 2 * k| ≤ η) {p₀ : Ambient 24}
    (hp₀ : p₀ ∈ X) {v : Fin 24 → Ambient 24} (hv : ∀ i, p₀ + v i ∈ X)
    (hframe : ∀ i, ‖v i - (64 : ℝ) • EuclideanSpace.basisFun (Fin 24) ℝ i‖ ≤ 4) :
    ∃ (G : Matrix (Fin 24) (Fin 24) ℤ) (P : Ambient 24 →ₗ[ℝ] Ambient 24),
      (∀ i j, ⟪P (v i), P (v j)⟫_ℝ = (G i j : ℝ)) ∧ (∀ i, (2 : ℤ) ∣ G i i) ∧
        ∀ x, ‖P x - x‖ ≤ 3 / 128 * η * ‖x‖ := by
  have hK : ∀ i j, ∃ k : ℤ, |⟪v i, v j⟫_ℝ - k| ≤ 3 / 2 * η := by
    intro i j
    have h := window_inner_approx_of_pair hpair hp₀ (hv i) (hv j)
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
  have hquad : ∀ a : Fin 24 → ℝ,
      |∑ j, ∑ k, a j * ((Matrix.of K).map (Int.cast : ℤ → ℝ)) j k * a k -
          ‖∑ j, a j • v j‖ ^ 2| ≤ 3 / 2 * η * (1 / 8) ^ 2 * ‖∑ j, a j • v j‖ ^ 2 :=
    gram_quadratic_bound _ hδ0 (fun j k => by
      rw [Matrix.map_apply, Matrix.of_apply, abs_sub_comm]
      exact hK' j k) (frame24_sum_abs_le hframe)
  have hε0 : (0 : ℝ) ≤ 3 / 2 * η * (1 / 8) ^ 2 := by linarith
  have hε1 : 3 / 2 * η * (1 / 8) ^ 2 ≤ 1 := by linarith
  obtain ⟨P, hP1, hP2⟩ := exists_gram_correction (frame24_linearIndependent hframe)
    ((Matrix.of K).map (Int.cast : ℤ → ℝ))
    (fun j k => by
      rw [Matrix.map_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply, hsymm j k])
    hε0 hε1 hquad
  refine ⟨Matrix.of K, P, fun i j => ?_, heven, fun x => ?_⟩
  · rw [hP1 i j, Matrix.map_apply]
  · have h := hP2 x
    have e : 3 / 2 * η * (1 / 8) ^ 2 = 3 / 128 * η := by ring
    rw [e] at h
    exact h

/-- The corrected frame is an integral frame. -/
theorem leechIntegralFrame_of_near {v : Fin 24 → Ambient 24}
    (hframe : ∀ i, ‖v i - (64 : ℝ) • EuclideanSpace.basisFun (Fin 24) ℝ i‖ ≤ 4)
    {P : Ambient 24 →ₗ[ℝ] Ambient 24} {G : Matrix (Fin 24) (Fin 24) ℤ} {ε : ℝ}
    (hε : ε ≤ 1 / 40) (hP : ∀ x, ‖P x - x‖ ≤ ε * ‖x‖)
    (hG : ∀ i j, ⟪P (v i), P (v j)⟫_ℝ = (G i j : ℝ))
    (heven : ∀ i, (2 : ℤ) ∣ G i i) : LeechIntegralFrame (fun i => P (v i)) G := by
  refine ⟨hG, heven, fun a => ?_, fun i => ?_⟩
  · have h1 := frame24_sum_abs_le hframe a
    have h2 := norm_le_map_of_near hP (∑ j, a j • v j)
    have e : P (∑ j, a j • v j) = ∑ j, a j • P (v j) := by simp only [map_sum, map_smul]
    rw [e] at h2
    have hn : 0 ≤ ‖∑ j, a j • v j‖ := norm_nonneg _
    have h3 : 1 / 8 * ‖∑ j, a j • v j‖ ≤ (1 - ε) * ‖∑ j, a j • v j‖ :=
      mul_le_mul_of_nonneg_right (by linarith) hn
    linarith
  · have h1 := norm_map_le_of_near hP (v i)
    have h2 := frame24_norm_le hframe i
    have h3 : (1 + ε) * ‖v i‖ ≤ (1 + 1 / 40) * 68 :=
      mul_le_mul (by linarith) h2 (norm_nonneg _) (by norm_num)
    have h4 : ‖P (v i)‖ ≤ (1 + 1 / 40) * 68 := h1.trans h3
    norm_num at h4 ⊢
    linarith

/-- The hypotheses on a window with a frame in dimension 24, after the Gram correction `P`. -/
structure LeechCorrectedWindow (X : Finset (Ambient 24)) (u p₀ : Ambient 24) (R η : ℝ)
    (v : Fin 24 → Ambient 24) (P : Ambient 24 →ₗ[ℝ] Ambient 24) : Prop where
  radius : 200000 ≤ R
  eta_nonneg : 0 ≤ η
  eta_small : η * R ^ 2 ≤ 1 / 10 ^ 115
  ball : ∀ x ∈ X, x ∈ closedBall u R
  pair : ∀ x ∈ X, ∀ y ∈ X, ∃ k : ℤ, |‖x - y‖ ^ 2 - 2 * k| ≤ η
  sep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → 2 ≤ dist x y
  base : p₀ ∈ X
  frame_mem : ∀ i, p₀ + v i ∈ X
  frame : ∀ i, ‖v i - (64 : ℝ) • EuclideanSpace.basisFun (Fin 24) ℝ i‖ ≤ 4
  near : ∀ x, ‖P x - x‖ ≤ 3 / 128 * η * ‖x‖

namespace LeechCorrectedWindow

variable {X : Finset (Ambient 24)} {u p₀ : Ambient 24} {R η : ℝ} {v : Fin 24 → Ambient 24}
  {P : Ambient 24 →ₗ[ℝ] Ambient 24}

theorem etaR_le_etaR2 (h : LeechCorrectedWindow X u p₀ R η v P) : η * R ≤ η * R ^ 2 := by
  have hR := h.radius
  have h0 := h.eta_nonneg
  have h1 : η * R * 1 ≤ η * R * R :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg h0 (by linarith))
  nlinarith

theorem eta_le_etaR (h : LeechCorrectedWindow X u p₀ R η v P) : η ≤ η * R := by
  have hR := h.radius
  have h0 := h.eta_nonneg
  have h1 : η * 1 ≤ η * R := mul_le_mul_of_nonneg_left (by linarith) h0
  linarith

theorem etaR_small (h : LeechCorrectedWindow X u p₀ R η v P) : η * R ≤ 1 / 10 ^ 115 :=
  h.etaR_le_etaR2.trans h.eta_small

theorem eta_le (h : LeechCorrectedWindow X u p₀ R η v P) : η ≤ 1 / 10 ^ 115 :=
  h.eta_le_etaR.trans h.etaR_small

theorem eps_nonneg (h : LeechCorrectedWindow X u p₀ R η v P) : (0 : ℝ) ≤ 3 / 128 * η := by
  have h0 := h.eta_nonneg
  linarith

theorem eps_le (h : LeechCorrectedWindow X u p₀ R η v P) : 3 / 128 * η ≤ 1 / 40 := by
  have h1 := h.eta_le
  have h2 : (1 : ℝ) / 10 ^ 115 ≤ 1 := by norm_num
  linarith

theorem norm_sub_base_le (h : LeechCorrectedWindow X u p₀ R η v P) {x : Ambient 24}
    (hx : x ∈ X) : ‖x - p₀‖ ≤ 2 * R := by
  have h1 := h.ball x hx
  have h2 := h.ball p₀ h.base
  rw [mem_closedBall, dist_eq_norm] at h1 h2
  have e : x - p₀ = (x - u) - (p₀ - u) := by abel
  rw [e]
  exact (norm_sub_le _ _).trans (by linarith)

/-- Inner products of two corrected points are almost integers. -/
theorem inner_approx (h : LeechCorrectedWindow X u p₀ R η v P) {x x' : Ambient 24} (hx : x ∈ X)
    (hx' : x' ∈ X) : ∃ k : ℤ, |⟪P (x - p₀), P (x' - p₀)⟫_ℝ - k| ≤ 6 * η * R ^ 2 := by
  obtain ⟨k, hk⟩ := window_inner_approx_of_pair h.pair h.base hx hx'
  refine ⟨k, ?_⟩
  have h1 := abs_inner_map_sub_inner_le h.eps_nonneg (by linarith [h.eps_le]) h.near
    (x - p₀) (x' - p₀)
  have hR := h.radius
  have h0 := h.eta_nonneg
  have hn := h.norm_sub_base_le hx
  have hn' := h.norm_sub_base_le hx'
  have h2 : ‖x - p₀‖ * ‖x' - p₀‖ ≤ 2 * R * (2 * R) :=
    mul_le_mul hn hn' (norm_nonneg _) (by linarith)
  have h3 : 3 * (3 / 128 * η) * ‖x - p₀‖ * ‖x' - p₀‖ ≤ 3 * (3 / 128 * η) * (2 * R * (2 * R)) := by
    have h4 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 3 * (3 / 128 * η))
    linarith
  have h5 : η ≤ η * R ^ 2 := h.eta_le_etaR.trans h.etaR_le_etaR2
  have e : ⟪P (x - p₀), P (x' - p₀)⟫_ℝ - k =
      (⟪P (x - p₀), P (x' - p₀)⟫_ℝ - ⟪x - p₀, x' - p₀⟫_ℝ) + (⟪x - p₀, x' - p₀⟫_ℝ - k) := by
    ring
  rw [e]
  calc _ ≤ |⟪P (x - p₀), P (x' - p₀)⟫_ℝ - ⟪x - p₀, x' - p₀⟫_ℝ| + |⟪x - p₀, x' - p₀⟫_ℝ - k| :=
        abs_add_le _ _
    _ ≤ 3 * (3 / 128 * η) * (2 * R * (2 * R)) + 3 / 2 * η := add_le_add (h1.trans h3) hk
    _ ≤ 6 * η * R ^ 2 := by nlinarith

/-- Squared norms of corrected points are almost even integers. -/
theorem norm_sq_approx (h : LeechCorrectedWindow X u p₀ R η v P) {x : Ambient 24} (hx : x ∈ X) :
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
  have h3 : 3 * (3 / 128 * η) * ‖x - p₀‖ * ‖x - p₀‖ ≤ 3 * (3 / 128 * η) * (2 * R * (2 * R)) := by
    have h4 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 3 * (3 / 128 * η))
    linarith
  have h5 : η ≤ η * R ^ 2 := h.eta_le_etaR.trans h.etaR_le_etaR2
  have e : ‖P (x - p₀)‖ ^ 2 - 2 * k =
      (‖P (x - p₀)‖ ^ 2 - ‖x - p₀‖ ^ 2) + (‖x - p₀‖ ^ 2 - 2 * k) := by ring
  rw [e]
  calc _ ≤ |‖P (x - p₀)‖ ^ 2 - ‖x - p₀‖ ^ 2| + |‖x - p₀‖ ^ 2 - 2 * k| := abs_add_le _ _
    _ ≤ 3 * (3 / 128 * η) * (2 * R * (2 * R)) + η := add_le_add (h1.trans h3) hk
    _ ≤ 6 * η * R ^ 2 := by nlinarith

/-- Inner products of corrected points with the corrected frame are almost integers. -/
theorem frame_approx (h : LeechCorrectedWindow X u p₀ R η v P) {x : Ambient 24} (hx : x ∈ X)
    (k : Fin 24) : ∃ n : ℤ, |⟪P (x - p₀), P (v k)⟫_ℝ - n| ≤ 12 * η * R := by
  obtain ⟨n, hn⟩ := window_inner_approx_of_pair h.pair h.base hx (h.frame_mem k)
  rw [add_sub_cancel_left] at hn
  refine ⟨n, ?_⟩
  have h1 := abs_inner_map_sub_inner_le h.eps_nonneg (by linarith [h.eps_le]) h.near
    (x - p₀) (v k)
  have hR := h.radius
  have h0 := h.eta_nonneg
  have hx' := h.norm_sub_base_le hx
  have hv := frame24_norm_le h.frame k
  have h2 : ‖x - p₀‖ * ‖v k‖ ≤ 2 * R * 68 := mul_le_mul hx' hv (norm_nonneg _) (by linarith)
  have h3 : 3 * (3 / 128 * η) * ‖x - p₀‖ * ‖v k‖ ≤ 3 * (3 / 128 * η) * (2 * R * 68) := by
    have h4 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 3 * (3 / 128 * η))
    linarith
  have h5 := h.eta_le_etaR
  have e : ⟪P (x - p₀), P (v k)⟫_ℝ - n =
      (⟪P (x - p₀), P (v k)⟫_ℝ - ⟪x - p₀, v k⟫_ℝ) + (⟪x - p₀, v k⟫_ℝ - n) := by ring
  rw [e]
  calc _ ≤ |⟪P (x - p₀), P (v k)⟫_ℝ - ⟪x - p₀, v k⟫_ℝ| + |⟪x - p₀, v k⟫_ℝ - n| :=
        abs_add_le _ _
    _ ≤ 3 * (3 / 128 * η) * (2 * R * 68) + 3 / 2 * η := add_le_add (h1.trans h3) hn
    _ ≤ 12 * η * R := by nlinarith

/-- The points of the corrected window are distinct. -/
theorem injOn_corrected (h : LeechCorrectedWindow X u p₀ R η v P) :
    Set.InjOn (fun x => P (x - p₀)) (X : Set (Ambient 24)) := by
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

/-- The smallness condition of `exists_isometry_of_leechIntegralFrame` for the window. -/
theorem small (h : LeechCorrectedWindow X u p₀ R η v P) :
    (6 * η * R ^ 2 + 12 * η * R * (6 * R + 12 * η * R)) *
      (620448401733239439360000 * 4900 ^ 24) < 1 := by
  have hR := h.radius
  have h0 := h.eta_nonneg
  have hA := h.eta_small
  have hB := h.etaR_small
  have hB0 : 0 ≤ η * R := mul_nonneg h0 (by linarith)
  have hB1 : η * R ≤ 1 := hB.trans (by norm_num)
  have hBB : (η * R) * (η * R) ≤ 1 * (η * R) := mul_le_mul_of_nonneg_right hB1 hB0
  have e : 6 * η * R ^ 2 + 12 * η * R * (6 * R + 12 * η * R) =
      78 * (η * R ^ 2) + 144 * ((η * R) * (η * R)) := by ring
  rw [e]
  have h1 : 78 * (η * R ^ 2) + 144 * ((η * R) * (η * R)) ≤ 222 / 10 ^ 115 := by
    have h2 : 144 * ((η * R) * (η * R)) ≤ 144 * (1 / 10 ^ 115) := by linarith
    have h3 : 78 * (η * R ^ 2) ≤ 78 * (1 / 10 ^ 115) := by linarith
    linarith
  calc (78 * (η * R ^ 2) + 144 * ((η * R) * (η * R))) *
        (620448401733239439360000 * 4900 ^ 24)
      ≤ 222 / 10 ^ 115 * (620448401733239439360000 * 4900 ^ 24) :=
        mul_le_mul_of_nonneg_right h1 (by norm_num)
    _ < 1 := by norm_num

/-- **The window theorem after the Gram correction.** -/
theorem exists_isometry (hLeech : LeechCharacterization)
    (h : LeechCorrectedWindow X u p₀ R η v P) {G : Matrix (Fin 24) (Fin 24) ℤ}
    (hG : ∀ i j, ⟪P (v i), P (v j)⟫_ℝ = (G i j : ℝ)) (heven : ∀ i, (2 : ℤ) ∣ G i i)
    (hcount : 9 / 10 * volume.real (closedBall (0 : Ambient 24) R) ≤ X.card) :
    ∃ Φ : Ambient 24 ≃ₗᵢ[ℝ] Ambient 24, ∀ x ∈ X, ∃ z ∈ leechSet,
      ‖(x - p₀) - Φ z‖ ≤ 13 * η * R := by
  classical
  have hR := h.radius
  have h0 := h.eta_nonneg
  have hB := h.etaR_small
  have hB0 : 0 ≤ η * R := mul_nonneg h0 (by linarith)
  have hB8 : η * R ≤ 1 / 1000 := hB.trans (by norm_num)
  have hε := h.eps_le
  have hF : LeechIntegralFrame (fun i => P (v i)) G :=
    leechIntegralFrame_of_near h.frame h.eps_le h.near hG heven
  have hθ0 : (0 : ℝ) ≤ 12 * η * R := by linarith
  have hθ : 12 * η * R ≤ 1 / 8 := by linarith
  have hσ0 : (0 : ℝ) ≤ 6 * η * R ^ 2 := by
    have h1 : 0 ≤ η * R ^ 2 := mul_nonneg h0 (sq_nonneg R)
    linarith
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
    have h3 : (1 + 3 / 128 * η) * ‖x - u‖ ≤ (1 + 3 / 128 * η) * R :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    nlinarith
  have hYnorm : ∀ y ∈ X.image (fun x => P (x - p₀)), ‖y‖ ≤ 3 * R := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have h1 := norm_map_le_of_near h.near (x - p₀)
    have h2 := h.norm_sub_base_le hx
    have h3 : (1 + 3 / 128 * η) * ‖x - p₀‖ ≤ (1 + 1 / 40) * (2 * R) :=
      mul_le_mul (by linarith) h2 (norm_nonneg _) (by norm_num)
    linarith
  have hYsep : ∀ y ∈ X.image (fun x => P (x - p₀)), ∀ y' ∈ X.image (fun x => P (x - p₀)),
      y ≠ y' → 19 / 10 ≤ ‖y - y'‖ := by
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
    have h3 : (1 - 1 / 40) * 2 ≤ (1 - 3 / 128 * η) * ‖x - x'‖ :=
      mul_le_mul (by linarith) h1 (by norm_num) (by linarith)
    norm_num at h3
    linarith
  have hYround : ∀ y ∈ X.image (fun x => P (x - p₀)), ∀ k,
      ∃ n : ℤ, |⟪y, P (v k)⟫_ℝ - n| ≤ 12 * η * R := by
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
  have hcount' : 9 / 10 * volume.real (closedBall (0 : Ambient 24) R) ≤
      ((X.image fun x => P (x - p₀)).card : ℝ) := by
    rw [hcard]
    exact hcount
  obtain ⟨Φ, hΦ⟩ := exists_isometry_of_leechIntegralFrame hLeech hF
    (X.image fun x => P (x - p₀)) (c := P (u - p₀)) hR hθ0 hθ hσ0 hYball hYnorm hYsep hYround
    hYint hYeven h.small hcount'
  refine ⟨Φ, fun x hx => ?_⟩
  obtain ⟨z, hz, hzy⟩ := hΦ (P (x - p₀)) (Finset.mem_image_of_mem _ hx)
  refine ⟨z, hz, ?_⟩
  have h1 := h.near (x - p₀)
  rw [norm_sub_rev] at h1
  have h2 := h.norm_sub_base_le hx
  have h3 : 3 / 128 * η * ‖x - p₀‖ ≤ 3 / 128 * η * (2 * R) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have e : (x - p₀) - Φ z = ((x - p₀) - P (x - p₀)) + (P (x - p₀) - Φ z) := by abel
  rw [e]
  calc ‖((x - p₀) - P (x - p₀)) + (P (x - p₀) - Φ z)‖
      ≤ ‖(x - p₀) - P (x - p₀)‖ + ‖P (x - p₀) - Φ z‖ := norm_add_le _ _
    _ ≤ 3 / 128 * η * (2 * R) + 12 * η * R := add_le_add (h1.trans h3) hzy
    _ ≤ 13 * η * R := by nlinarith

end LeechCorrectedWindow

/-- **An almost integral window with a frame lies near a copy of the Leech lattice**, given the
characterization of the Leech lattice. -/
theorem exists_isometry_near_leechSet_of_window (hLeech : LeechCharacterization)
    {X : Finset (Ambient 24)} {u p₀ : Ambient 24} {R η : ℝ} {v : Fin 24 → Ambient 24}
    (hR : 200000 ≤ R) (hη0 : 0 ≤ η) (hη : η * R ^ 2 ≤ 1 / 10 ^ 115)
    (hball : ∀ x ∈ X, x ∈ closedBall u R)
    (hpair : ∀ x ∈ X, ∀ y ∈ X, ∃ k : ℤ, |‖x - y‖ ^ 2 - 2 * k| ≤ η)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → 2 ≤ dist x y) (hp₀ : p₀ ∈ X)
    (hv : ∀ i, p₀ + v i ∈ X)
    (hframe : ∀ i, ‖v i - (64 : ℝ) • EuclideanSpace.basisFun (Fin 24) ℝ i‖ ≤ 4)
    (hcount : 9 / 10 * volume.real (closedBall (0 : Ambient 24) R) ≤ X.card) :
    ∃ Φ : Ambient 24 ≃ₗᵢ[ℝ] Ambient 24, ∀ x ∈ X, ∃ z ∈ leechSet,
      ‖(x - p₀) - Φ z‖ ≤ 13 * η * R := by
  have hη1 : η ≤ 1 / 10 := by
    have h1 : η * 1 ≤ η * R ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hη0
    have h2 : (1 : ℝ) / 10 ^ 115 ≤ 1 / 10 := by norm_num
    linarith
  obtain ⟨G, P, hG, heven, hP⟩ := exists_leechFrame_gram_correction hη0 hη1 hpair hp₀ hv hframe
  exact LeechCorrectedWindow.exists_isometry hLeech
    ⟨hR, hη0, hη, hball, hpair, hsep, hp₀, hv, hframe, hP⟩ hG heven hcount

/-- A base point and a frame from saturation near `u`. -/
theorem exists_leechFrame_of_saturated {S : Set (Ambient 24)} {u : Ambient 24}
    (hsat : ∀ y ∈ closedBall u 64, ∃ x ∈ S, dist x y < 2) :
    ∃ p₀ ∈ S, ∃ v : Fin 24 → Ambient 24, dist p₀ u < 2 ∧ (∀ i, p₀ + v i ∈ S) ∧
      (∀ i, dist (p₀ + v i) u < 66) ∧
      ∀ i, ‖v i - (64 : ℝ) • EuclideanSpace.basisFun (Fin 24) ℝ i‖ ≤ 4 := by
  obtain ⟨p₀, hp₀, hp₀u⟩ := hsat u (mem_closedBall_self (by norm_num))
  have hnorm : ∀ i, ‖(64 : ℝ) • EuclideanSpace.basisFun (Fin 24) ℝ i‖ = 64 := fun i => by
    rw [norm_smul, (EuclideanSpace.basisFun (Fin 24) ℝ).orthonormal.1 i]
    norm_num
  have hy : ∀ i, u + (64 : ℝ) • EuclideanSpace.basisFun (Fin 24) ℝ i ∈ closedBall u 64 :=
    fun i => by rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hnorm i]
  choose c hcS hc using fun i => hsat _ (hy i)
  refine ⟨p₀, hp₀, fun i => c i - p₀, hp₀u, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · rw [add_sub_cancel]
    exact hcS i
  · rw [add_sub_cancel]
    have h1 := dist_triangle (c i) (u + (64 : ℝ) • EuclideanSpace.basisFun (Fin 24) ℝ i) u
    have h2 : dist (u + (64 : ℝ) • EuclideanSpace.basisFun (Fin 24) ℝ i) u = 64 := by
      rw [dist_eq_norm, add_sub_cancel_left, hnorm i]
    linarith [hc i]
  · have e : c i - p₀ - (64 : ℝ) • EuclideanSpace.basisFun (Fin 24) ℝ i =
        (c i - (u + (64 : ℝ) • EuclideanSpace.basisFun (Fin 24) ℝ i)) + (u - p₀) := by abel
    rw [e]
    have h1 := hc i
    rw [dist_eq_norm] at h1
    have h2 := hp₀u
    rw [dist_comm, dist_eq_norm] at h2
    exact (norm_add_le _ _).trans (by linarith)

/-- **A saturated almost integral window lies near a copy of the Leech lattice**, given the
characterization of the Leech lattice. -/
theorem exists_isometry_near_leechSet_of_saturated (hLeech : LeechCharacterization)
    {S : Set (Ambient 24)} {u : Ambient 24} {R η : ℝ}
    (hR : 200000 ≤ R) (hη0 : 0 ≤ η) (hη : η * R ^ 2 ≤ 1 / 10 ^ 115)
    (hfin : (S ∩ closedBall u R).Finite)
    (hpair : ∀ x ∈ S ∩ closedBall u R, ∀ y ∈ S ∩ closedBall u R,
      ∃ k : ℤ, |‖x - y‖ ^ 2 - 2 * k| ≤ η)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 2 ≤ dist x y)
    (hsat : ∀ y ∈ closedBall u 64, ∃ x ∈ S, dist x y < 2)
    (hcount : 9 / 10 * volume.real (closedBall (0 : Ambient 24) R) ≤ hfin.toFinset.card) :
    ∃ (Φ : Ambient 24 ≃ₗᵢ[ℝ] Ambient 24) (p₀ : Ambient 24), ∀ x ∈ S ∩ closedBall u R,
      ∃ z ∈ leechSet, ‖(x - p₀) - Φ z‖ ≤ 13 * η * R := by
  obtain ⟨p₀, hp₀, v, hp₀u, hvS, hvu, hframe⟩ := exists_leechFrame_of_saturated hsat
  have hmem : ∀ x, x ∈ hfin.toFinset ↔ x ∈ S ∩ closedBall u R := fun x => hfin.mem_toFinset
  have hp₀X : p₀ ∈ hfin.toFinset := (hmem p₀).mpr ⟨hp₀, mem_closedBall.mpr (by linarith)⟩
  have hvX : ∀ i, p₀ + v i ∈ hfin.toFinset := fun i =>
    (hmem _).mpr ⟨hvS i, mem_closedBall.mpr (by linarith [hvu i])⟩
  obtain ⟨Φ, hΦ⟩ := exists_isometry_near_leechSet_of_window hLeech (X := hfin.toFinset) (u := u)
    hR hη0 hη (fun x hx => ((hmem x).mp hx).2)
    (fun x hx y hy => hpair x ((hmem x).mp hx) y ((hmem y).mp hy))
    (fun x hx y hy hne => hsep x ((hmem x).mp hx).1 y ((hmem y).mp hy).1 hne)
    hp₀X hvX hframe hcount
  exact ⟨Φ, p₀, fun x hx => hΦ x ((hmem x).mpr hx)⟩

end E8Leech
