import E8Leech.EvenUnimodularLattice
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Correcting an almost exact Gram matrix (BRR, Step 4)

Let `w` be a basis of `ℝᵈ` and `M` a symmetric matrix whose quadratic form is close to the
Euclidean one in the coordinates of `w`:

`|aᵀ M a - |∑ aⱼ wⱼ|²| ≤ ε |∑ aⱼ wⱼ|²`.

Then there is a linear map `P` with `|P x - x| ≤ ε |x|` such that the vectors `P wⱼ` have Gram
matrix exactly `M`. `P` is the positive square root of the symmetric operator of the form: in an
orthonormal eigenbasis it multiplies by `√λᵢ`, and `|√λ - 1| ≤ |λ - 1|`.

* `exists_linearMap_inner_eq_bilin`: the statement for a symmetric bilinear form.
* `exists_gram_correction`: the statement for a basis and a matrix.
* `gram_quadratic_bound`: the hypothesis from an entrywise bound on the Gram matrix and a bound
  on the coordinates.
* `exists_evenUnimodularGram_near`: an even unimodular integer matrix gives an
  `EvenUnimodularGram`.
-/

noncomputable section

namespace E8Leech

open scoped InnerProductSpace
open Finset

/-- `|√t - 1| ≤ |t - 1|` for `t ≥ 0`. -/
theorem abs_sqrt_sub_one_le {t : ℝ} (ht : 0 ≤ t) : |Real.sqrt t - 1| ≤ |t - 1| := by
  have hs := Real.sqrt_nonneg t
  have e : t - 1 = (Real.sqrt t - 1) * (Real.sqrt t + 1) := by
    linear_combination -(Real.mul_self_sqrt ht)
  have h1 : (1 : ℝ) ≤ |Real.sqrt t + 1| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  rw [e, abs_mul]
  calc |Real.sqrt t - 1| = |Real.sqrt t - 1| * 1 := (mul_one _).symm
    _ ≤ |Real.sqrt t - 1| * |Real.sqrt t + 1| := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

/-- **Isometric correction of a quadratic form.** A symmetric bilinear form whose quadratic form
is within `ε |x|²` of `|x|²` is the pull-back of the inner product by a linear map `P` with
`|P x - x| ≤ ε |x|`. -/
theorem exists_linearMap_inner_eq_bilin {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (B : LinearMap.BilinForm ℝ E)
    (hB : ∀ x y, B x y = B y x) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (hquad : ∀ x, |B x x - ‖x‖ ^ 2| ≤ ε * ‖x‖ ^ 2) :
    ∃ P : E →ₗ[ℝ] E, (∀ x y, ⟪P x, P y⟫_ℝ = B x y) ∧ ∀ x, ‖P x - x‖ ≤ ε * ‖x‖ := by
  classical
  let e := stdOrthonormalBasis ℝ E
  -- the symmetric operator of the form
  let S : E →ₗ[ℝ] E := ∑ i, (B.flip (e i)).smulRight (e i)
  have hS : ∀ x y, ⟪S x, y⟫_ℝ = B x y := by
    intro x y
    have hy : B x y = ∑ i, ⟪e i, y⟫_ℝ * B x (e i) := by
      conv_lhs => rw [← e.sum_repr' y]
      simp only [map_sum, map_smul, smul_eq_mul]
    rw [hy]
    simp only [S, LinearMap.sum_apply, LinearMap.smulRight_apply, sum_inner,
      real_inner_smul_left]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hsymm : S.IsSymmetric := fun x y => by
    rw [hS, real_inner_comm, hS]
    exact hB x y
  have hn : Module.finrank ℝ E = Module.finrank ℝ E := rfl
  let b := hsymm.eigenvectorBasis hn
  let lam := hsymm.eigenvalues hn
  have hlam : ∀ i, S (b i) = lam i • b i := fun i => hsymm.apply_eigenvectorBasis hn i
  have hb1 : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  have hBb : ∀ i, B (b i) (b i) = lam i := fun i => by
    rw [← hS, hlam, real_inner_smul_left, real_inner_self_eq_norm_sq, hb1]
    ring
  have hlam1 : ∀ i, |lam i - 1| ≤ ε := fun i => by
    have h1 := hquad (b i)
    rw [hBb, hb1] at h1
    simpa using h1
  have hlam0 : ∀ i, 0 ≤ lam i := fun i => by
    have h1 := (abs_le.mp (hlam1 i)).1
    linarith
  -- the positive square root
  let P : E →ₗ[ℝ] E := ∑ i, Real.sqrt (lam i) • (innerₗ E (b i)).smulRight (b i)
  have hP : ∀ x, P x = ∑ i, (Real.sqrt (lam i) * ⟪b i, x⟫_ℝ) • b i := by
    intro x
    simp only [P, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      innerₗ_apply_apply, smul_smul]
  refine ⟨P, fun x y => ?_, fun x => ?_⟩
  · have h1 : ⟪P x, P y⟫_ℝ = ∑ i, lam i * (⟪b i, x⟫_ℝ * ⟪b i, y⟫_ℝ) := by
      rw [hP x, hP y, b.orthonormal.inner_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [conj_trivial]
      linear_combination (⟪b i, x⟫_ℝ * ⟪b i, y⟫_ℝ) * Real.mul_self_sqrt (hlam0 i)
    have h2 : B x y = ∑ i, lam i * (⟪b i, x⟫_ℝ * ⟪b i, y⟫_ℝ) := by
      have hSx : S x = ∑ i, (⟪b i, x⟫_ℝ * lam i) • b i := by
        conv_lhs => rw [← b.sum_repr' x]
        simp only [map_sum, map_smul, hlam, smul_smul]
      rw [← hS, hSx, sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_left]
      ring
    rw [h1, h2]
  · have hdiff : P x - x = ∑ i, ((Real.sqrt (lam i) - 1) * ⟪b i, x⟫_ℝ) • b i := by
      have e1 : P x - x = (∑ i, (Real.sqrt (lam i) * ⟪b i, x⟫_ℝ) • b i) -
          ∑ i, ⟪b i, x⟫_ℝ • b i := by
        rw [← hP x, b.sum_repr' x]
      rw [e1, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_smul]
      congr 1
      ring
    have hnorm : ‖P x - x‖ ^ 2 = ∑ i, ((Real.sqrt (lam i) - 1) * ⟪b i, x⟫_ℝ) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hdiff, b.orthonormal.inner_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [conj_trivial]
      ring
    have hxn : ‖x‖ ^ 2 = ∑ i, ⟪b i, x⟫_ℝ ^ 2 := by
      rw [← b.sum_sq_norm_inner_right x]
      exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]
    have hle : ‖P x - x‖ ^ 2 ≤ (ε * ‖x‖) ^ 2 := by
      rw [hnorm, mul_pow, hxn, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 : |Real.sqrt (lam i) - 1| ≤ ε := (abs_sqrt_sub_one_le (hlam0 i)).trans (hlam1 i)
      have h2 : (Real.sqrt (lam i) - 1) ^ 2 ≤ ε ^ 2 :=
        sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hε0 (norm_nonneg _))
      two_ne_zero).mp hle

/-- **Correction of an almost exact Gram matrix.** -/
theorem exists_gram_correction {d : ℕ} {w : Fin d → Ambient d} (hw : LinearIndependent ℝ w)
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : ∀ j k, M j k = M k j) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1)
    (hquad : ∀ a : Fin d → ℝ, |∑ j, ∑ k, a j * M j k * a k - ‖∑ j, a j • w j‖ ^ 2| ≤
      ε * ‖∑ j, a j • w j‖ ^ 2) :
    ∃ P : Ambient d →ₗ[ℝ] Ambient d,
      (∀ j k, ⟪P (w j), P (w k)⟫_ℝ = M j k) ∧ ∀ x, ‖P x - x‖ ≤ ε * ‖x‖ := by
  classical
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range w) := by
    rw [hw.span_eq_top_of_card_eq_finrank' (by simp)]
  let bw : Module.Basis (Fin d) ℝ (Ambient d) := Module.Basis.mk hw hspan
  have hbw : ∀ j, bw j = w j := fun j => Module.Basis.mk_apply hw hspan j
  let B : LinearMap.BilinForm ℝ (Ambient d) := Matrix.toBilin bw M
  have hBapp : ∀ x y, B x y = ∑ j, ∑ k, bw.repr x j * M j k * bw.repr y k :=
    fun x y => Matrix.toBilin_apply bw M x y
  have hBsymm : ∀ x y, B x y = B y x := by
    intro x y
    rw [hBapp, hBapp, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hM j k]
    ring
  have hBquad : ∀ x, |B x x - ‖x‖ ^ 2| ≤ ε * ‖x‖ ^ 2 := by
    intro x
    have hx : ∑ j, bw.repr x j • w j = x := by
      conv_rhs => rw [← bw.sum_repr x]
      exact Finset.sum_congr rfl fun j _ => by rw [hbw]
    have h1 := hquad fun j => bw.repr x j
    rw [hx] at h1
    rw [hBapp]
    exact h1
  obtain ⟨P, hP1, hP2⟩ := exists_linearMap_inner_eq_bilin B hBsymm hε0 hε hBquad
  refine ⟨P, fun j k => ?_, hP2⟩
  rw [hP1, hBapp, ← hbw j, ← hbw k]
  simp [Module.Basis.repr_self, Finsupp.single_apply]

/-- The hypothesis of `exists_gram_correction` from an entrywise bound on the Gram matrix and a
bound on the coordinates. -/
theorem gram_quadratic_bound {d : ℕ} {w : Fin d → Ambient d} (M : Matrix (Fin d) (Fin d) ℝ)
    {δ K : ℝ} (hδ0 : 0 ≤ δ) (hδ : ∀ j k, |M j k - ⟪w j, w k⟫_ℝ| ≤ δ)
    (hK : ∀ a : Fin d → ℝ, ∑ j, |a j| ≤ K * ‖∑ j, a j • w j‖) (a : Fin d → ℝ) :
    |∑ j, ∑ k, a j * M j k * a k - ‖∑ j, a j • w j‖ ^ 2| ≤
      δ * K ^ 2 * ‖∑ j, a j • w j‖ ^ 2 := by
  have hnorm : ‖∑ j, a j • w j‖ ^ 2 = ∑ j, ∑ k, a j * ⟪w j, w k⟫_ℝ * a k := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  have hdiff : ∑ j, ∑ k, a j * M j k * a k - ‖∑ j, a j • w j‖ ^ 2 =
      ∑ j, ∑ k, a j * (M j k - ⟪w j, w k⟫_ℝ) * a k := by
    rw [hnorm, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hsum : |∑ j, ∑ k, a j * (M j k - ⟪w j, w k⟫_ℝ) * a k| ≤ δ * (∑ j, |a j|) ^ 2 := by
    have h1 : |∑ j, ∑ k, a j * (M j k - ⟪w j, w k⟫_ℝ) * a k| ≤
        ∑ j, ∑ k, |a j| * δ * |a k| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hδ j k) (abs_nonneg _)) (abs_nonneg _)
    have h2 : ∑ j, ∑ k, |a j| * δ * |a k| = δ * (∑ j, |a j|) ^ 2 := by
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [← h2]
    exact h1
  have hKsq : (∑ j, |a j|) ^ 2 ≤ (K * ‖∑ j, a j • w j‖) ^ 2 :=
    pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => abs_nonneg _) (hK a) 2
  rw [hdiff]
  calc |∑ j, ∑ k, a j * (M j k - ⟪w j, w k⟫_ℝ) * a k| ≤ δ * (∑ j, |a j|) ^ 2 := hsum
    _ ≤ δ * (K * ‖∑ j, a j • w j‖) ^ 2 := mul_le_mul_of_nonneg_left hKsq hδ0
    _ = δ * K ^ 2 * ‖∑ j, a j • w j‖ ^ 2 := by ring

/-- **BRR Step 4 for `E8`.** A basis whose quadratic form is within `ε` of an even unimodular
integer matrix `M` is moved by a linear map `P` with `|P x - x| ≤ ε |x|` to vectors with Gram
matrix exactly `M`. -/
theorem exists_evenUnimodularGram_near {w : Fin 8 → Ambient 8} (hw : LinearIndependent ℝ w)
    (M : Matrix (Fin 8) (Fin 8) ℤ) (hMs : ∀ j k, M j k = M k j) (hdet : M.det = 1)
    (heven : ∀ i, (2 : ℤ) ∣ M i i) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (hquad : ∀ a : Fin 8 → ℝ, |∑ j, ∑ k, a j * (M j k : ℝ) * a k - ‖∑ j, a j • w j‖ ^ 2| ≤
      ε * ‖∑ j, a j • w j‖ ^ 2) :
    ∃ P : Ambient 8 →ₗ[ℝ] Ambient 8,
      EvenUnimodularGram (fun j => P (w j)) M ∧ ∀ x, ‖P x - x‖ ≤ ε * ‖x‖ := by
  obtain ⟨P, hP1, hP2⟩ := exists_gram_correction hw (M.map (Int.cast : ℤ → ℝ))
    (fun j k => by simp only [Matrix.map_apply]; rw [hMs j k]) hε0 hε
    (fun a => by simpa only [Matrix.map_apply] using hquad a)
  exact ⟨P, ⟨fun i j => by rw [hP1 i j, Matrix.map_apply], hdet, heven⟩, hP2⟩

end E8Leech
