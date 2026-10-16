import E8Leech.LocalE8Window

/-!
# A saturated almost integral window lies near a copy of `E8`

For a set `S ⊂ ℝ⁸` whose points are at mutual distance at least `√2`, a centre `u` near which `S`
is saturated (every point of `B(u,16)` is within `√2` of `S`) gives a base point `p₀ ∈ S` and a
frame `v` with `p₀ + vᵢ ∈ S` and `|vᵢ - 16 eᵢ| < 2√2` (`exists_frame_of_saturated`). Together with
`exists_isometry_near_e8Set_of_window` this is the deterministic form of Steps 2–4 of the proof of
Theorem 1.5 of Böröczky–Radchenko–Ramos for `E8`
(`exists_isometry_near_e8Set_of_saturated`): if the squared distances in the window
`S ∩ B(u,R)` are within `η` of even integers and the window has at least `(9/10)·vol(B_R)`
points, then the window is within `46 η R` of `p₀ + Φ(E8)` for a linear isometry `Φ`.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric
open scoped InnerProductSpace

/-- A base point and a frame from saturation near `u`. -/
theorem exists_frame_of_saturated {S : Set (Ambient 8)} {u : Ambient 8}
    (hsat : ∀ y ∈ closedBall u 16, ∃ x ∈ S, dist x y < Real.sqrt 2) :
    ∃ p₀ ∈ S, ∃ v : Fin 8 → Ambient 8, dist p₀ u < Real.sqrt 2 ∧ (∀ i, p₀ + v i ∈ S) ∧
      (∀ i, dist (p₀ + v i) u < 16 + Real.sqrt 2) ∧
      ∀ i, ‖v i - (16 : ℝ) • EuclideanSpace.basisFun (Fin 8) ℝ i‖ ≤ 2 * Real.sqrt 2 := by
  obtain ⟨p₀, hp₀, hp₀u⟩ := hsat u (mem_closedBall_self (by norm_num))
  have hnorm : ∀ i, ‖(16 : ℝ) • EuclideanSpace.basisFun (Fin 8) ℝ i‖ = 16 := fun i => by
    rw [norm_smul, (EuclideanSpace.basisFun (Fin 8) ℝ).orthonormal.1 i]
    norm_num
  have hy : ∀ i, u + (16 : ℝ) • EuclideanSpace.basisFun (Fin 8) ℝ i ∈ closedBall u 16 := fun i => by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hnorm i]
  choose c hcS hc using fun i => hsat _ (hy i)
  refine ⟨p₀, hp₀, fun i => c i - p₀, hp₀u, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · rw [add_sub_cancel]
    exact hcS i
  · rw [add_sub_cancel]
    have h1 := dist_triangle (c i) (u + (16 : ℝ) • EuclideanSpace.basisFun (Fin 8) ℝ i) u
    have h2 : dist (u + (16 : ℝ) • EuclideanSpace.basisFun (Fin 8) ℝ i) u = 16 := by
      rw [dist_eq_norm, add_sub_cancel_left, hnorm i]
    linarith [hc i]
  · have e : c i - p₀ - (16 : ℝ) • EuclideanSpace.basisFun (Fin 8) ℝ i =
        (c i - (u + (16 : ℝ) • EuclideanSpace.basisFun (Fin 8) ℝ i)) + (u - p₀) := by abel
    rw [e]
    have h1 := hc i
    rw [dist_eq_norm] at h1
    have h2 := hp₀u
    rw [dist_comm, dist_eq_norm] at h2
    exact (norm_add_le _ _).trans (by linarith)

/-- **A saturated almost integral window lies near a copy of `E8`.** -/
theorem exists_isometry_near_e8Set_of_saturated {S : Set (Ambient 8)} {u : Ambient 8} {R η : ℝ}
    (hR : 6000 ≤ R) (hη0 : 0 ≤ η) (hη : η * R ^ 2 ≤ 1 / 10 ^ 29)
    (hfin : (S ∩ closedBall u R).Finite)
    (hpair : ∀ x ∈ S ∩ closedBall u R, ∀ y ∈ S ∩ closedBall u R,
      ∃ k : ℤ, |‖x - y‖ ^ 2 - 2 * k| ≤ η)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Real.sqrt 2 ≤ dist x y)
    (hsat : ∀ y ∈ closedBall u 16, ∃ x ∈ S, dist x y < Real.sqrt 2)
    (hcount : 9 / 10 * volume.real (closedBall (0 : Ambient 8) R) ≤ hfin.toFinset.card) :
    ∃ (Φ : Ambient 8 ≃ₗᵢ[ℝ] Ambient 8) (p₀ : Ambient 8), ∀ x ∈ S ∩ closedBall u R,
      ∃ z ∈ e8Set, ‖(x - p₀) - Φ z‖ ≤ 46 * η * R := by
  obtain ⟨p₀, hp₀, v, hp₀u, hvS, hvu, hframe⟩ := exists_frame_of_saturated hsat
  have hs2 : Real.sqrt 2 ≤ 2 := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have hmem : ∀ x, x ∈ hfin.toFinset ↔ x ∈ S ∩ closedBall u R := fun x => hfin.mem_toFinset
  have hp₀X : p₀ ∈ hfin.toFinset := (hmem p₀).mpr ⟨hp₀, mem_closedBall.mpr (by linarith)⟩
  have hvX : ∀ i, p₀ + v i ∈ hfin.toFinset := fun i =>
    (hmem _).mpr ⟨hvS i, mem_closedBall.mpr (by linarith [hvu i])⟩
  obtain ⟨Φ, hΦ⟩ := exists_isometry_near_e8Set_of_window (X := hfin.toFinset) (u := u) hR hη0 hη
    (fun x hx => ((hmem x).mp hx).2)
    (fun x hx y hy => hpair x ((hmem x).mp hx) y ((hmem y).mp hy))
    (fun x hx y hy hne => hsep x ((hmem x).mp hx).1 y ((hmem y).mp hy).1 hne)
    hp₀X hvX hframe hcount
  exact ⟨Φ, p₀, fun x hx => hΦ x ((hmem x).mpr hx)⟩

end E8Leech
