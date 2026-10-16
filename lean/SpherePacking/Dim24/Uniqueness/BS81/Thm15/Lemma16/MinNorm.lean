-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16.HalfInteger
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16.Solve
public import SpherePacking.Dim24.Uniqueness.BS81.LatticeLIntegral
public import Mathlib.Data.Set.Card
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# BS81 Lemma 16: minimal norm in `L`

Let `C ⊆ Ω₂₄` be an equality-case code and set `L := span_ℤ (2 • C)`.
This file shows that there is no vector of squared norm `2` in `L`, and deduces that every
nonzero vector in `L` has squared norm at least `4`.

## Main statements
* `no_norm_sq_two_vector_in_latticeL`
* `minNorm_sq_ge_four`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16

noncomputable section

open scoped RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- There is no vector of squared norm `2` in `L = span_ℤ (2 • C)`. -/
public theorem no_norm_sq_two_vector_in_latticeL
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C) :
    ¬ ∃ v : ℝ²⁴, v ∈ (latticeL C : Set ℝ²⁴) ∧ ‖v‖ ^ 2 = (2 : ℝ) := by
  intro hv
  rcases hv with ⟨v, hvL, hnormv⟩
  have hcard : h.code.finite.toFinset.card = 196560 := by
    simpa using!
      (Set.ncard_eq_toFinset_card (s := C) (hs := h.code.finite)).symm.trans h.card_eq
  have hvals :
      ∀ u ∈ h.code.finite.toFinset,
        (⟪u, v⟫ : ℝ) = 0 ∨ (⟪u, v⟫ : ℝ) = (1 / 2 : ℝ) ∨ (⟪u, v⟫ : ℝ) = (-1 / 2 : ℝ) ∨
          (⟪u, v⟫ : ℝ) = (1 : ℝ) ∨ (⟪u, v⟫ : ℝ) = (-1 : ℝ) := by
    intro u hu
    have huC : u ∈ C := by simpa using! hu
    have hnormu : ‖u‖ = (1 : ℝ) := h.code.norm_one huC
    exact inner_mem_values_of_norm_sq_two (C := C) (h := h) (hu := huC) (hv := hvL)
      (hnormu := hnormu) (hnormv := hnormv)
  have heqs :=
    beta_gamma_eqs_of_norm_sq_two (C := C) (h := h) (hcard := hcard) (v := v) (hnormv := hnormv)
      (hvals := hvals)
  refine contradiction_of_gamma_nat (γ := gamma h.code.finite.toFinset v) ?_
  exact gamma_eq_neg_210_of_eqs (β := (beta h.code.finite.toFinset v : ℝ))
    (γ := (gamma h.code.finite.toFinset v : ℝ)) heqs.1 heqs.2

/-- The squared norm of any `x ∈ L = span_ℤ (2 • C)` is an integer multiple of `2`. -/
public theorem norm_sq_eq_two_mul_int
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    {x : ℝ²⁴} (hx : x ∈ (latticeL C : Set ℝ²⁴)) :
    ∃ m : ℤ, ‖x‖ ^ 2 = (2 : ℝ) * (m : ℝ) := by
  have hEq : Uniqueness.BS81.EqCase24 C :=
    Uniqueness.BS81.Thm14.EqCase24Pkg.toEqCase24 (C := C) h
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨u, hu, rfl⟩
      have hnormu : ‖u‖ = (1 : ℝ) := h.code.norm_one hu
      refine ⟨2, ?_⟩
      have : ‖(2 : ℝ) • u‖ ^ 2 = (4 : ℝ) := by
        simp [norm_smul, hnormu, pow_two, mul_comm]
        norm_num
      calc
        ‖(2 : ℝ) • u‖ ^ 2 = (4 : ℝ) := this
        _ = (2 : ℝ) * (2 : ℝ) := by norm_num
  | zero =>
      exact ⟨0, by simp⟩
  | add x y hx hy ihx ihy =>
      rcases ihx with ⟨m, hm⟩
      rcases ihy with ⟨n, hn⟩
      rcases
          Uniqueness.BS81.inner_latticeL_int (C := C) hEq (x := x) (y := y) hx hy
        with ⟨k, hk⟩
      refine ⟨m + n + k, ?_⟩
      have hnorm : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * (⟪x, y⟫ : ℝ) + ‖y‖ ^ 2 := by
        simpa using! (norm_add_sq_real x y)
      calc
        ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * (⟪x, y⟫ : ℝ) + ‖y‖ ^ 2 := hnorm
        _ = (2 : ℝ) * (m : ℝ) + 2 * (k : ℝ) + (2 : ℝ) * (n : ℝ) := by
              simp [hm, hn, hk, add_left_comm, add_comm]
        _ = (2 : ℝ) * ((m : ℝ) + (n : ℝ) + (k : ℝ)) := by ring
        _ = (2 : ℝ) * ((m + n + k : ℤ) : ℝ) := by simp [add_assoc]
  | smul z x hx ih =>
      rcases ih with ⟨m, hm⟩
      refine ⟨z * z * m, ?_⟩
      have hz : ‖(z • x : ℝ²⁴)‖ ^ 2 = ((z : ℝ) ^ 2) * ‖x‖ ^ 2 := by
        calc
          ‖(z • x : ℝ²⁴)‖ ^ 2 = (‖(z : ℝ)‖ * ‖x‖) ^ 2 := by
            simp [norm_zsmul (𝕜 := ℝ) z x]
          _ = (‖(z : ℝ)‖ ^ 2) * ‖x‖ ^ 2 := by
            simp [mul_pow]
          _ = ((z : ℝ) ^ 2) * ‖x‖ ^ 2 := by
            simp [Real.norm_eq_abs, sq_abs]
      have hzint : (z : ℝ) ^ 2 = ((z * z : ℤ) : ℝ) := by
        rw [pow_two]
        exact (Int.cast_mul z z).symm
      calc
        ‖(z • x : ℝ²⁴)‖ ^ 2
            = ((z : ℝ) ^ 2) * ‖x‖ ^ 2 := hz
        _ = ((z * z : ℤ) : ℝ) * ((2 : ℝ) * (m : ℝ)) := by
              simp [hzint, hm, mul_assoc]
        _ = (2 : ℝ) * (((z * z : ℤ) : ℝ) * (m : ℝ)) := by ring
        _ = (2 : ℝ) * ((z * z * m : ℤ) : ℝ) := by
              simp [Int.cast_mul, mul_assoc]

/-- Minimal squared norm in `L` is at least `4`. -/
public theorem minNorm_sq_ge_four
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C) :
    ∀ v : ℝ²⁴, v ∈ (latticeL C : Set ℝ²⁴) → v ≠ 0 → (4 : ℝ) ≤ ‖v‖ ^ 2 := by
  intro v hvL hv0
  rcases norm_sq_eq_two_mul_int (C := C) h (x := v) hvL with ⟨m, hm⟩
  have hpos : (0 : ℝ) < ‖v‖ ^ 2 := by
    have : (0 : ℝ) < ‖v‖ := by simpa using! (norm_pos_iff.2 hv0)
    nlinarith
  by_contra hlt
  have hlt4 : ‖v‖ ^ 2 < (4 : ℝ) := lt_of_not_ge hlt
  have hm2 : ‖v‖ ^ 2 = (2 : ℝ) := by
    have hm_pos : (0 : ℝ) < (m : ℝ) := by nlinarith [hm, hpos]
    have hm_lt2 : (m : ℝ) < (2 : ℝ) := by nlinarith [hm, hlt4]
    have hm_int : m = 1 := by
      have hmposZ : (0 : ℤ) < m := by exact_mod_cast hm_pos
      have hm_lt2Z : m < (2 : ℤ) := by exact_mod_cast hm_lt2
      have hm_ge1 : (1 : ℤ) ≤ m := by
        simpa using! (Int.add_one_le_iff.2 hmposZ)
      have hm_le1 : m ≤ (1 : ℤ) := by
        have : m < (1 : ℤ) + 1 := by simpa using! hm_lt2Z
        exact (Int.lt_add_one_iff).1 this
      exact le_antisymm hm_le1 hm_ge1
    simpa [hm_int] using! hm
  exact no_norm_sq_two_vector_in_latticeL (C := C) h ⟨v, hvL, hm2⟩

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16
