import E8Leech.GramPerturbation
import Mathlib.Algebra.Order.Chebyshev

/-!
# Frames near a scaled orthonormal basis and rounding to the dual lattice (BRR, Steps 2–3)

Two elementary tools for the construction of the local lattice.

* A frame `v` with `|vᵢ - T eᵢ| ≤ r` for an orthonormal basis `e` has controlled coordinates:
  `T ∑ |aⱼ| ≤ √d (|∑ aⱼ vⱼ| + r ∑ |aⱼ|)` (`scaled_basis_sum_abs_le`). For `d = 8`, `T = 16`,
  `r = 2√2` this is `∑ |aⱼ| ≤ |∑ aⱼ vⱼ| / 2` (`frame_sum_abs_le`).
* For a frame `w` with an integer Gram matrix `G` of nonzero determinant, `dualPoint w G ℓ` is the
  vector with inner products `ℓ` against the frame. Inner products of two such vectors have
  denominator `det G` (`det_mul_inner_dualPoint`), so a value that is close to an integer is an
  integer (`eq_int_of_mul_int_of_near`).
-/

noncomputable section

namespace E8Leech

open scoped InnerProductSpace
open Finset

/-- Coordinates in a frame close to a scaled orthonormal basis. -/
theorem scaled_basis_sum_abs_le {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Ambient d))
    {v : Fin d → Ambient d} {T r : ℝ} (hT : 0 ≤ T) (hv : ∀ i, ‖v i - T • b i‖ ≤ r)
    (a : Fin d → ℝ) :
    T * ∑ j, |a j| ≤ Real.sqrt d * (‖∑ j, a j • v j‖ + r * ∑ j, |a j|) := by
  have hsplit : ∑ j, a j • v j = T • ∑ j, a j • b j + ∑ j, a j • (v j - T • b j) := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_sub, smul_smul, smul_smul, mul_comm T (a j)]
    abel
  have h1 : ‖∑ j, a j • b j‖ ^ 2 = ∑ j, a j ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, b.orthonormal.inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [conj_trivial]
    ring
  have h2 : (∑ j, |a j|) ^ 2 ≤ (d : ℝ) * ∑ j, a j ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := fun j => |a j|)
    simpa only [Finset.card_univ, Fintype.card_fin, sq_abs] using h
  have h3 : ∑ j, |a j| ≤ Real.sqrt d * ‖∑ j, a j • b j‖ := by
    have hnn : 0 ≤ Real.sqrt d * ‖∑ j, a j • b j‖ :=
      mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    have hsq : (∑ j, |a j|) ^ 2 ≤ (Real.sqrt d * ‖∑ j, a j • b j‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d), h1]
      exact h2
    exact (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun j _ => abs_nonneg _) hnn two_ne_zero).mp hsq
  have h4 : ‖∑ j, a j • (v j - T • b j)‖ ≤ r * ∑ j, |a j| := by
    calc ‖∑ j, a j • (v j - T • b j)‖ ≤ ∑ j, ‖a j • (v j - T • b j)‖ := norm_sum_le _ _
      _ ≤ ∑ j, |a j| * r := Finset.sum_le_sum fun j _ => by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _)
      _ = r * ∑ j, |a j| := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have h5 : T * ‖∑ j, a j • b j‖ ≤ ‖∑ j, a j • v j‖ + r * ∑ j, |a j| := by
    have e1 : ‖T • ∑ j, a j • b j‖ = T * ‖∑ j, a j • b j‖ := by
      rw [norm_smul, Real.norm_of_nonneg hT]
    have e2 : T • ∑ j, a j • b j = ∑ j, a j • v j - ∑ j, a j • (v j - T • b j) := by
      rw [hsplit]
      abel
    calc T * ‖∑ j, a j • b j‖ = ‖∑ j, a j • v j - ∑ j, a j • (v j - T • b j)‖ := by
          rw [← e1, e2]
      _ ≤ ‖∑ j, a j • v j‖ + ‖∑ j, a j • (v j - T • b j)‖ := norm_sub_le _ _
      _ ≤ ‖∑ j, a j • v j‖ + r * ∑ j, |a j| := by linarith
  calc T * ∑ j, |a j| ≤ T * (Real.sqrt d * ‖∑ j, a j • b j‖) := mul_le_mul_of_nonneg_left h3 hT
    _ = Real.sqrt d * (T * ‖∑ j, a j • b j‖) := by ring
    _ ≤ Real.sqrt d * (‖∑ j, a j • v j‖ + r * ∑ j, |a j|) :=
        mul_le_mul_of_nonneg_left h5 (Real.sqrt_nonneg _)

theorem sqrt_eight : Real.sqrt 8 = 2 * Real.sqrt 2 := by
  have h : (8 : ℝ) = 2 ^ 2 * 2 := by norm_num
  rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]

/-- A frame of `ℝ⁸` within `2√2` of `16 eᵢ`: the coordinates are at most half the norm. -/
theorem frame_sum_abs_le {v : Fin 8 → Ambient 8}
    (hv : ∀ i, ‖v i - (16 : ℝ) • EuclideanSpace.basisFun (Fin 8) ℝ i‖ ≤ 2 * Real.sqrt 2)
    (a : Fin 8 → ℝ) : ∑ j, |a j| ≤ 1 / 2 * ‖∑ j, a j • v j‖ := by
  have h := scaled_basis_sum_abs_le (EuclideanSpace.basisFun (Fin 8) ℝ) (by norm_num) hv a
  have hs : Real.sqrt ((8 : ℕ) : ℝ) = 2 * Real.sqrt 2 := by
    rw [show ((8 : ℕ) : ℝ) = 8 by norm_num, sqrt_eight]
  rw [hs] at h
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h3 : Real.sqrt 2 ≤ 2 := by nlinarith
  have hsum : 0 ≤ ∑ j, |a j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hn : 0 ≤ ‖∑ j, a j • v j‖ := norm_nonneg _
  -- `16 Σ ≤ 2√2 ‖x‖ + 8 Σ`
  have h4 : 16 * ∑ j, |a j| ≤ 2 * Real.sqrt 2 * ‖∑ j, a j • v j‖ + 8 * ∑ j, |a j| := by
    have e : 2 * Real.sqrt 2 * (‖∑ j, a j • v j‖ + 2 * Real.sqrt 2 * ∑ j, |a j|) =
        2 * Real.sqrt 2 * ‖∑ j, a j • v j‖ + 4 * (Real.sqrt 2 * Real.sqrt 2) * ∑ j, |a j| := by
      ring
    rw [e, h2] at h
    linarith
  have h5 : 2 * Real.sqrt 2 * ‖∑ j, a j • v j‖ ≤ 4 * ‖∑ j, a j • v j‖ := by nlinarith
  linarith

theorem frame_linearIndependent {v : Fin 8 → Ambient 8}
    (hv : ∀ i, ‖v i - (16 : ℝ) • EuclideanSpace.basisFun (Fin 8) ℝ i‖ ≤ 2 * Real.sqrt 2) :
    LinearIndependent ℝ v := by
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have h := frame_sum_abs_le hv a
  rw [ha, norm_zero, mul_zero] at h
  have hi : |a i| ≤ ∑ j, |a j| :=
    Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  exact abs_eq_zero.mp (le_antisymm (hi.trans h) (abs_nonneg _))

theorem frame_norm_le {v : Fin 8 → Ambient 8}
    (hv : ∀ i, ‖v i - (16 : ℝ) • EuclideanSpace.basisFun (Fin 8) ℝ i‖ ≤ 2 * Real.sqrt 2)
    (i : Fin 8) : ‖v i‖ ≤ 19 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h3 : Real.sqrt 2 ≤ 3 / 2 := by nlinarith
  have e : v i = (v i - (16 : ℝ) • EuclideanSpace.basisFun (Fin 8) ℝ i) +
      (16 : ℝ) • EuclideanSpace.basisFun (Fin 8) ℝ i := by abel
  have hb : ‖(16 : ℝ) • EuclideanSpace.basisFun (Fin 8) ℝ i‖ = 16 := by
    rw [norm_smul, (EuclideanSpace.basisFun (Fin 8) ℝ).orthonormal.1 i]
    norm_num
  calc ‖v i‖ ≤ ‖v i - (16 : ℝ) • EuclideanSpace.basisFun (Fin 8) ℝ i‖ +
        ‖(16 : ℝ) • EuclideanSpace.basisFun (Fin 8) ℝ i‖ := by
        conv_lhs => rw [e]
        exact norm_add_le _ _
    _ ≤ 2 * Real.sqrt 2 + 16 := by rw [hb]; linarith [hv i]
    _ ≤ 19 := by linarith

/-- If the coordinates in a spanning frame are controlled by the norm, then a vector is controlled
by its inner products with the frame. -/
theorem norm_le_of_inner_frame_le {d : ℕ} {w : Fin d → Ambient d} {K θ : ℝ} (hK0 : 0 ≤ K)
    (hθ0 : 0 ≤ θ) (hspan : ∀ z : Ambient d, ∃ a : Fin d → ℝ, z = ∑ j, a j • w j)
    (hK : ∀ a : Fin d → ℝ, ∑ j, |a j| ≤ K * ‖∑ j, a j • w j‖) {z : Ambient d}
    (hz : ∀ k, |⟪z, w k⟫_ℝ| ≤ θ) : ‖z‖ ≤ K * θ := by
  obtain ⟨a, ha⟩ := hspan z
  have h1 : ‖z‖ ^ 2 = ∑ j, a j * ⟪z, w j⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => arg 2; rw [ha]
    rw [sum_inner]
    exact Finset.sum_congr rfl fun j _ => by rw [real_inner_smul_left, real_inner_comm]
  have h2 : ‖z‖ ^ 2 ≤ K * θ * ‖z‖ := by
    calc ‖z‖ ^ 2 = ∑ j, a j * ⟪z, w j⟫_ℝ := h1
      _ ≤ ∑ j, |a j| * θ := Finset.sum_le_sum fun j _ => by
          calc a j * ⟪z, w j⟫_ℝ ≤ |a j * ⟪z, w j⟫_ℝ| := le_abs_self _
            _ = |a j| * |⟪z, w j⟫_ℝ| := abs_mul _ _
            _ ≤ |a j| * θ := mul_le_mul_of_nonneg_left (hz j) (abs_nonneg _)
      _ = (∑ j, |a j|) * θ := (Finset.sum_mul _ _ _).symm
      _ ≤ K * ‖∑ j, a j • w j‖ * θ := mul_le_mul_of_nonneg_right (hK a) hθ0
      _ = K * θ * ‖z‖ := by rw [← ha]; ring
  rcases eq_or_lt_of_le (norm_nonneg z) with h0 | h0
  · rw [← h0]
    exact mul_nonneg hK0 hθ0
  · have h3 : ‖z‖ * ‖z‖ ≤ K * θ * ‖z‖ := by rw [← sq]; exact h2
    exact le_of_mul_le_mul_right h3 h0

/-- The vector with inner products `ℓ` against a frame with integer Gram matrix `G`. -/
def dualPoint {d : ℕ} (w : Fin d → Ambient d) (G : Matrix (Fin d) (Fin d) ℤ) (ℓ : Fin d → ℤ) :
    Ambient d :=
  ((G.det : ℝ)⁻¹) • ∑ j, (((G.adjugate.mulVec ℓ) j : ℤ) : ℝ) • w j

theorem inner_dualPoint_frame {d : ℕ} {w : Fin d → Ambient d} {G : Matrix (Fin d) (Fin d) ℤ}
    (hG : ∀ i j, ⟪w i, w j⟫_ℝ = (G i j : ℝ)) (hdet : G.det ≠ 0) (ℓ : Fin d → ℤ) (k : Fin d) :
    ⟪dualPoint w G ℓ, w k⟫_ℝ = (ℓ k : ℝ) := by
  have hsymm : ∀ i j, G i j = G j i := fun i j => by
    have e : (G i j : ℝ) = (G j i : ℝ) := by rw [← hG i j, ← hG j i, real_inner_comm]
    exact_mod_cast e
  have hdet' : (G.det : ℝ) ≠ 0 := by exact_mod_cast hdet
  have e1 : ∑ j, (((G.adjugate.mulVec ℓ) j : ℤ) : ℝ) * (G j k : ℝ) = (G.det : ℝ) * (ℓ k : ℝ) := by
    have h1 : (G * G.adjugate).mulVec ℓ k = G.det * ℓ k := by
      rw [Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]
    rw [← Matrix.mulVec_mulVec] at h1
    have h2 : ∑ j, (G.adjugate.mulVec ℓ) j * G j k = G.det * ℓ k := by
      rw [← h1]
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun j _ => by rw [hsymm j k, mul_comm]
    exact_mod_cast h2
  rw [dualPoint, real_inner_smul_left, sum_inner]
  simp only [real_inner_smul_left, hG]
  rw [e1]
  field_simp

/-- **Denominators.** Inner products of two dual points have denominator `det G`. -/
theorem det_mul_inner_dualPoint {d : ℕ} {w : Fin d → Ambient d} {G : Matrix (Fin d) (Fin d) ℤ}
    (hG : ∀ i j, ⟪w i, w j⟫_ℝ = (G i j : ℝ)) (hdet : G.det ≠ 0) (ℓ m : Fin d → ℤ) :
    (G.det : ℝ) * ⟪dualPoint w G ℓ, dualPoint w G m⟫_ℝ =
      ((∑ j, ℓ j * (G.adjugate.mulVec m) j : ℤ) : ℝ) := by
  have hdet' : (G.det : ℝ) ≠ 0 := by exact_mod_cast hdet
  have e : ⟪dualPoint w G ℓ, dualPoint w G m⟫_ℝ =
      (G.det : ℝ)⁻¹ * ∑ j, (((G.adjugate.mulVec m) j : ℤ) : ℝ) * (ℓ j : ℝ) := by
    conv_lhs => arg 3; rw [dualPoint]
    rw [real_inner_smul_right, inner_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right, inner_dualPoint_frame hG hdet ℓ j]
  rw [e, ← mul_assoc, mul_inv_cancel₀ hdet', one_mul]
  push_cast
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem dualPoint_add {d : ℕ} (w : Fin d → Ambient d) (G : Matrix (Fin d) (Fin d) ℤ)
    (ℓ m : Fin d → ℤ) : dualPoint w G (ℓ + m) = dualPoint w G ℓ + dualPoint w G m := by
  simp only [dualPoint, Matrix.mulVec_add, Pi.add_apply, Int.cast_add, add_smul,
    Finset.sum_add_distrib, smul_add]

theorem dualPoint_neg {d : ℕ} (w : Fin d → Ambient d) (G : Matrix (Fin d) (Fin d) ℤ)
    (ℓ : Fin d → ℤ) : dualPoint w G (-ℓ) = -dualPoint w G ℓ := by
  simp only [dualPoint, Matrix.mulVec_neg, Pi.neg_apply, Int.cast_neg, neg_smul,
    Finset.sum_neg_distrib, smul_neg]

theorem dualPoint_zero {d : ℕ} (w : Fin d → Ambient d) (G : Matrix (Fin d) (Fin d) ℤ) :
    dualPoint w G 0 = 0 := by
  simp only [dualPoint, Matrix.mulVec_zero, Pi.zero_apply, Int.cast_zero, zero_smul,
    Finset.sum_const_zero, smul_zero]

/-- A real number with denominator `D` that is close to an integer is that integer. -/
theorem eq_int_of_mul_int_of_near {D : ℤ} (hD : 0 < D) {q : ℝ} {n k : ℤ}
    (hq : (D : ℝ) * q = n) (hk : |q - k| * D < 1) : q = k := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have h1 : |((n - D * k : ℤ) : ℝ)| < 1 := by
    have e : ((n - D * k : ℤ) : ℝ) = (D : ℝ) * (q - k) := by
      push_cast
      rw [← hq]
      ring
    rw [e, abs_mul, abs_of_pos hD', mul_comm]
    exact hk
  have h2 : |n - D * k| < 1 := by exact_mod_cast h1
  have h3 : n - D * k = 0 := Int.abs_lt_one_iff.mp h2
  have h4 : (D : ℝ) * q = (D : ℝ) * k := by
    rw [hq]
    have h5 : n = D * k := by omega
    rw [h5]
    push_cast
    ring
  exact mul_left_cancel₀ hD'.ne' h4

end E8Leech
