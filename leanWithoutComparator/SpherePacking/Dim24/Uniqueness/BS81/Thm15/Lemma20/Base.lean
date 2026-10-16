-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma19.ContainsD3
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel

/-!
# Base case for BS81 Lemma 20

From the equality-case package, BS81 Lemma 19 provides three shell vectors in
`L := span_ℤ (2 • C)` generating a copy of `D₃`. This file packages that data as
`ContainsDn C 3`, providing the base case for the induction in BS81 Lemma 20.

## Main definition
* `containsD3_of_eqCase`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20

noncomputable section

open scoped RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
## Helper lemma
-/

/-- Compute `⟪a - e0, a - e0⟫` from the inner products of `a` and `e0`. -/
public lemma inner_eq_one_of_eq_sub
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {e2 a e0 : F}
    (he2 : e2 = a - e0)
    (haa : (inner ℝ a a : ℝ) = (2 : ℝ))
    (hae0 : (inner ℝ a e0 : ℝ) = (1 : ℝ))
    (he0e0 : (inner ℝ e0 e0 : ℝ) = (1 : ℝ)) :
    (⟪e2, e2⟫ : ℝ) = (1 : ℝ) := by
  -- Reduce to a scalar computation using `real_inner_sub_sub_self`.
  have hsub :
      (inner ℝ (a - e0) (a - e0) : ℝ) =
        (inner ℝ a a : ℝ) - 2 * (inner ℝ a e0 : ℝ) + (inner ℝ e0 e0 : ℝ) := by
    simpa using! (real_inner_sub_sub_self (x := a) (y := e0))
  have : (inner ℝ e2 e2 : ℝ) = (1 : ℝ) := by
    calc
      (inner ℝ e2 e2 : ℝ) = (inner ℝ (a - e0) (a - e0) : ℝ) := by simp [he2]
      _ = (inner ℝ a a : ℝ) - 2 * (inner ℝ a e0 : ℝ) + (inner ℝ e0 e0 : ℝ) := hsub
      _ = (2 : ℝ) - 2 * (1 : ℝ) + (1 : ℝ) := by rw [haa, hae0, he0e0]
      _ = (1 : ℝ) := by ring
  simpa using! this

lemma orthonormal_vec3_of_inner
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {e0 e1 e2 : F}
    (he0e0 : (⟪e0, e0⟫ : ℝ) = (1 : ℝ))
    (he1e1 : (⟪e1, e1⟫ : ℝ) = (1 : ℝ))
    (he2e2 : (⟪e2, e2⟫ : ℝ) = (1 : ℝ))
    (he0e1 : (⟪e0, e1⟫ : ℝ) = (0 : ℝ))
    (he0e2 : (⟪e0, e2⟫ : ℝ) = (0 : ℝ))
    (he1e2 : (⟪e1, e2⟫ : ℝ) = (0 : ℝ)) :
    Orthonormal ℝ (![e0, e1, e2] : Fin 3 → F) := by
  have he1e0 : (⟪e1, e0⟫ : ℝ) = (0 : ℝ) := by simpa [real_inner_comm] using! he0e1
  have he2e0 : (⟪e2, e0⟫ : ℝ) = (0 : ℝ) := by simpa [real_inner_comm] using! he0e2
  have he2e1 : (⟪e2, e1⟫ : ℝ) = (0 : ℝ) := by simpa [real_inner_comm] using! he1e2
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    first
    | exact he0e0
    | exact he0e1
    | exact he0e2
    | exact he1e0
    | exact he1e1
    | exact he1e2
    | exact he2e0
    | exact he2e1
    | exact he2e2

lemma minVec_mem_vec3_of_identities
    (C : Set ℝ²⁴) (g : Fin 3 → ℝ²⁴)
    (hgShell : ∀ i : Fin 3, g i ∈ latticeShell4 C)
    (hg2_sub_g1 : g 2 - g 1 ∈ latticeShell4 C)
    (hg0_sub_g2 : g 0 - g 2 ∈ latticeShell4 C)
    (hg0_add_g1_sub_g2 : g 0 + g 1 - g 2 ∈ latticeShell4 C)
    (e0 e1 e2 : ℝ²⁴)
    (hsqrt2_smul_e0_add_e1 : (Real.sqrt 2 : ℝ) • (e0 + e1) = g 0)
    (hsqrt2_smul_e0_sub_e1 : (Real.sqrt 2 : ℝ) • (e0 - e1) = g 1)
    (hsqrt2_smul_e0_add_e2 : (Real.sqrt 2 : ℝ) • (e0 + e2) = g 2)
    (hsqrt2_smul_e0_sub_e2 : (Real.sqrt 2 : ℝ) • (e0 - e2) = g 0 + g 1 - g 2)
    (hsqrt2_smul_e1_add_e2 : (Real.sqrt 2 : ℝ) • (e1 + e2) = g 2 - g 1)
    (hsqrt2_smul_e1_sub_e2 : (Real.sqrt 2 : ℝ) • (e1 - e2) = g 0 - g 2) :
    ∀ (i j : Fin 3), i ≠ j →
      (Real.sqrt 2 •
          ((![e0, e1, e2] : Fin 3 → ℝ²⁴) i +
            (![e0, e1, e2] : Fin 3 → ℝ²⁴) j)) ∈ latticeShell4 C ∧
        (Real.sqrt 2 •
            ((![e0, e1, e2] : Fin 3 → ℝ²⁴) i -
              (![e0, e1, e2] : Fin 3 → ℝ²⁴) j)) ∈ latticeShell4 C := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · cases hij rfl
  · refine ⟨?_, ?_⟩
    · simpa [hsqrt2_smul_e0_add_e1] using! (hgShell 0)
    · simpa [hsqrt2_smul_e0_sub_e1] using! (hgShell 1)
  · refine ⟨?_, ?_⟩
    · simpa [hsqrt2_smul_e0_add_e2] using! (hgShell 2)
    · simpa [hsqrt2_smul_e0_sub_e2] using! hg0_add_g1_sub_g2
  · refine ⟨?_, ?_⟩
    · simpa [add_comm, hsqrt2_smul_e0_add_e1] using! (hgShell 0)
    · have : (Real.sqrt 2 : ℝ) • (e1 - e0) = - g 1 := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using!
          congrArg Neg.neg hsqrt2_smul_e0_sub_e1
      simpa [this] using! latticeShell4_neg_mem (hgShell 1)
  · cases hij rfl
  · refine ⟨?_, ?_⟩
    · simpa [hsqrt2_smul_e1_add_e2] using! hg2_sub_g1
    · simpa [hsqrt2_smul_e1_sub_e2] using! hg0_sub_g2
  · refine ⟨?_, ?_⟩
    · simpa [add_comm, hsqrt2_smul_e0_add_e2] using! (hgShell 2)
    · have : (Real.sqrt 2 : ℝ) • (e2 - e0) = - (g 0 + g 1 - g 2) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using!
          congrArg Neg.neg hsqrt2_smul_e0_sub_e2
      simpa [this] using! latticeShell4_neg_mem hg0_add_g1_sub_g2
  · refine ⟨?_, ?_⟩
    · simpa [add_comm, hsqrt2_smul_e1_add_e2] using! hg2_sub_g1
    · have : (Real.sqrt 2 : ℝ) • (e2 - e1) = - (g 0 - g 2) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using!
          congrArg Neg.neg hsqrt2_smul_e1_sub_e2
      simpa [this] using! latticeShell4_neg_mem hg0_sub_g2
  · cases hij rfl

/-- Base case: construct `ContainsDn C 3` from the equality-case package. -/
public noncomputable def containsD3_of_eqCase
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C) :
    ContainsDn C 3 := by
  -- We have an existence statement in `Prop`, so we extract data using choice.
  set g : Fin 3 → ℝ²⁴ :=
    Classical.choose
      (Uniqueness.BS81.Thm15.Lemma19.lattice_contains_D3 (C := C) h) with hg
  have hg_spec :
      (∀ i : Fin 3, g i ∈ (latticeL C : Set ℝ²⁴)) ∧
        (∀ i : Fin 3, ‖g i‖ ^ 2 = (4 : ℝ)) ∧
        (⟪g 0, g 1⟫ : ℝ) = 0 ∧
        (⟪g 0, g 2⟫ : ℝ) = 2 ∧
        (⟪g 1, g 2⟫ : ℝ) = 2 :=
    by
      simpa [hg] using!
        Classical.choose_spec
          (Uniqueness.BS81.Thm15.Lemma19.lattice_contains_D3 (C := C) h)
  have hgL : ∀ i : Fin 3, g i ∈ (latticeL C : Set ℝ²⁴) := hg_spec.1
  have hgnorm : ∀ i : Fin 3, ‖g i‖ ^ 2 = (4 : ℝ) := hg_spec.2.1
  have h01 : (⟪g 0, g 1⟫ : ℝ) = 0 := hg_spec.2.2.1
  have h02 : (⟪g 0, g 2⟫ : ℝ) = 2 := hg_spec.2.2.2.1
  have h12 : (⟪g 1, g 2⟫ : ℝ) = 2 := hg_spec.2.2.2.2
  have hnormAdd : ‖g 0 + g 1‖ ^ 2 = (8 : ℝ) := by
    -- `‖g0+g1‖^2 = ‖g0‖^2 + 2⟪g0,g1⟫ + ‖g1‖^2`.
    calc
      ‖g 0 + g 1‖ ^ 2 = ‖g 0‖ ^ 2 + 2 * (⟪g 0, g 1⟫ : ℝ) + ‖g 1‖ ^ 2 := by
        simpa using! (norm_add_sq_real (g 0) (g 1))
      _ = (4 : ℝ) + 2 * 0 + (4 : ℝ) := by simp [hgnorm, h01]
      _ = (8 : ℝ) := by ring
  have hsqrt2 : (Real.sqrt 2 : ℝ) ≠ 0 := by
    have : (0 : ℝ) < 2 := by norm_num
    exact Real.sqrt_ne_zero'.2 this
  -- Define an orthonormal frame `e₀,e₁,e₂` so that the D₃ minimal vectors are ℤ-linear
  -- combinations of the given triple `g 0, g 1, g 2`.
  set k : ℝ := 1 / (2 * Real.sqrt 2) with hk
  set e0 : ℝ²⁴ := k • (g 0 + g 1) with he0
  set e1 : ℝ²⁴ := k • (g 0 - g 1) with he1
  set e2 : ℝ²⁴ := (1 / Real.sqrt 2 : ℝ) • g 2 - e0 with he2
  have hgShell : ∀ i : Fin 3, g i ∈ latticeShell4 C := fun i => ⟨hgL i, hgnorm i⟩
  have hg2_sub_g1 : g 2 - g 1 ∈ latticeShell4 C := by
    refine ⟨sub_mem (hgL 2) (hgL 1), ?_⟩
    have h21 : (⟪g 2, g 1⟫ : ℝ) = 2 := by simpa [real_inner_comm] using! h12
    have : ‖g 2 - g 1‖ ^ 2 = (4 : ℝ) := by
      calc
        ‖g 2 - g 1‖ ^ 2 = ‖g 2‖ ^ 2 - 2 * (⟪g 2, g 1⟫ : ℝ) + ‖g 1‖ ^ 2 := by
          simpa using! (norm_sub_sq_real (g 2) (g 1))
        _ = (4 : ℝ) - 2 * (2 : ℝ) + (4 : ℝ) := by simp [hgnorm, h21]
        _ = (4 : ℝ) := by ring
    simpa using! this
  have hg0_sub_g2 : g 0 - g 2 ∈ latticeShell4 C := by
    refine ⟨sub_mem (hgL 0) (hgL 2), ?_⟩
    have : ‖g 0 - g 2‖ ^ 2 = (4 : ℝ) := by
      calc
        ‖g 0 - g 2‖ ^ 2 = ‖g 0‖ ^ 2 - 2 * (⟪g 0, g 2⟫ : ℝ) + ‖g 2‖ ^ 2 := by
          simpa using! (norm_sub_sq_real (g 0) (g 2))
        _ = (4 : ℝ) - 2 * (2 : ℝ) + (4 : ℝ) := by simp [hgnorm, h02]
        _ = (4 : ℝ) := by ring
    simpa using! this
  have hg0_add_g1_sub_g2 : g 0 + g 1 - g 2 ∈ latticeShell4 C := by
    refine ⟨sub_mem (add_mem (hgL 0) (hgL 1)) (hgL 2), ?_⟩
    have hinner : (⟪g 0 + g 1, g 2⟫ : ℝ) = (4 : ℝ) := by
      calc
        (⟪g 0 + g 1, g 2⟫ : ℝ) = (⟪g 0, g 2⟫ : ℝ) + (⟪g 1, g 2⟫ : ℝ) := by
          simp [inner_add_left]
        _ = (2 : ℝ) + (2 : ℝ) := by simp [h02, h12]
        _ = (4 : ℝ) := by norm_num
    have : ‖(g 0 + g 1) - g 2‖ ^ 2 = (4 : ℝ) := by
      calc
        ‖(g 0 + g 1) - g 2‖ ^ 2 =
            ‖g 0 + g 1‖ ^ 2 - 2 * (⟪g 0 + g 1, g 2⟫ : ℝ) + ‖g 2‖ ^ 2 := by
          simpa using! (norm_sub_sq_real (g 0 + g 1) (g 2))
        _ = (8 : ℝ) - 2 * (4 : ℝ) + (4 : ℝ) := by simp [hnormAdd, hinner, hgnorm]
        _ = (4 : ℝ) := by ring
    simpa [sub_eq_add_neg, add_assoc] using! this
  have hsqrt2_mul_k : (Real.sqrt 2 : ℝ) * k = (1 / 2 : ℝ) := by
    -- `√2 * (1 / (2 * √2)) = 1/2`.
    have hden : (2 * Real.sqrt 2 : ℝ) ≠ 0 := by
      exact mul_ne_zero (by norm_num) hsqrt2
    calc
      (Real.sqrt 2 : ℝ) * k = (Real.sqrt 2 : ℝ) * (1 / (2 * Real.sqrt 2)) := by
        simp [hk]
      _ = (Real.sqrt 2 : ℝ) / (2 * Real.sqrt 2) := by simp [div_eq_mul_inv]
      _ = (1 : ℝ) / 2 := by
        field_simp [hden]
      _ = (1 / 2 : ℝ) := by ring
  have hk2 : k ^ 2 = (1 / 8 : ℝ) := by
    -- Compute directly from the definition `k = 1 / (2 * √2)`:
    -- `(1 / a)^2 = 1 / a^2` and `(2 * √2)^2 = 8`.
    have hnonneg2 : (0 : ℝ) ≤ 2 := by norm_num
    have hs : (Real.sqrt 2 : ℝ) ^ 2 = (2 : ℝ) := by
      simp [pow_two, Real.mul_self_sqrt hnonneg2]
    have hden : (2 * Real.sqrt 2 : ℝ) ^ 2 = (8 : ℝ) := by
      calc
        (2 * Real.sqrt 2 : ℝ) ^ 2 = (2 : ℝ) ^ 2 * (Real.sqrt 2 : ℝ) ^ 2 := by
          simp [mul_pow]
        _ = (4 : ℝ) * (2 : ℝ) := by
          have h2 : (2 : ℝ) ^ 2 = (4 : ℝ) := by norm_num
          simp [h2, hs]
        _ = (8 : ℝ) := by norm_num
    -- Now conclude.
    rw [hk]
    calc
      (1 / (2 * Real.sqrt 2 : ℝ)) ^ 2 = 1 / (2 * Real.sqrt 2 : ℝ) ^ 2 := by
        simpa using! (one_div_pow (2 * Real.sqrt 2 : ℝ) 2)
      _ = (1 : ℝ) / (8 : ℝ) := by simp [hden]
      _ = (1 / 8 : ℝ) := by ring
  have hsqrt2_smul_e0_add_e1 : (Real.sqrt 2 : ℝ) • (e0 + e1) = g 0 := by
    have : e0 + e1 = (2 * k : ℝ) • g 0 := by
      -- keep `k` abstract: avoid field simplification
      calc
        e0 + e1 = k • (g 0 + g 1) + k • (g 0 - g 1) := by
          simp [he0, he1]
        _ = (k • g 0 + k • g 1) + (k • g 0 - k • g 1) := by
          rw [smul_add, smul_sub]
        _ = (k • g 0 + k • g 0) + (k • g 1 - k • g 1) := by abel
        _ = (k + k) • g 0 := by
          simp [← add_smul]
        _ = (2 * k : ℝ) • g 0 := by
          have : k + k = 2 * k := by ring
          simp [this]
    calc
      (Real.sqrt 2 : ℝ) • (e0 + e1) = ((Real.sqrt 2 : ℝ) * (2 * k)) • g 0 := by
        simp [this, smul_smul]
      _ = g 0 := by
        have : (Real.sqrt 2 : ℝ) * (2 * k) = (1 : ℝ) := by
          calc
            (Real.sqrt 2 : ℝ) * (2 * k) = 2 * ((Real.sqrt 2 : ℝ) * k) := by ring
            _ = 2 * (1 / 2 : ℝ) := by simp [hsqrt2_mul_k]
            _ = (1 : ℝ) := by norm_num
        simp [this]
  have hsqrt2_smul_e0_sub_e1 : (Real.sqrt 2 : ℝ) • (e0 - e1) = g 1 := by
    have : e0 - e1 = (2 * k : ℝ) • g 1 := by
      calc
        e0 - e1 = k • (g 0 + g 1) - k • (g 0 - g 1) := by
          simp [he0, he1]
        _ = (k • g 0 + k • g 1) - (k • g 0 - k • g 1) := by
          rw [smul_add, smul_sub]
        _ = (k • g 1 + k • g 1) := by abel
        _ = (k + k) • g 1 := by simp [← add_smul]
        _ = (2 * k : ℝ) • g 1 := by
          have : k + k = 2 * k := by ring
          simp [this]
    calc
      (Real.sqrt 2 : ℝ) • (e0 - e1) = ((Real.sqrt 2 : ℝ) * (2 * k)) • g 1 := by
        simp [this, smul_smul]
      _ = g 1 := by
        have : (Real.sqrt 2 : ℝ) * (2 * k) = (1 : ℝ) := by
          calc
            (Real.sqrt 2 : ℝ) * (2 * k) = 2 * ((Real.sqrt 2 : ℝ) * k) := by ring
            _ = 2 * (1 / 2 : ℝ) := by simp [hsqrt2_mul_k]
            _ = (1 : ℝ) := by norm_num
        simp [this]
  have hsqrt2_smul_e0_add_e2 : (Real.sqrt 2 : ℝ) • (e0 + e2) = g 2 := by
    -- `e0 + e2 = (1/√2) g2`.
    have : e0 + e2 = (1 / Real.sqrt 2 : ℝ) • g 2 := by
      exact add_sub_cancel e0 ((1 / √2) • g 2)
    calc
      (Real.sqrt 2 : ℝ) • (e0 + e2) = ((Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2 : ℝ)) • g 2 := by
        simp [this, smul_smul]
      _ = g 2 := by
        have : (Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2 : ℝ) = (1 : ℝ) := by
          field_simp [hsqrt2]
        rw [this]
        simp
  -- The remaining mixed relations follow from add/sub identities in the module.
  have hsqrt2_smul_e0_sub_e2 : (Real.sqrt 2 : ℝ) • (e0 - e2) = g 0 + g 1 - g 2 := by
    have : e0 - e2 = (e0 + e1) + (e0 - e1) - (e0 + e2) := by
      -- pure additive identity
      abel
    rw [this, smul_sub]
    have hsum :
        (Real.sqrt 2 : ℝ) • ((e0 + e1) + (e0 - e1)) =
          (Real.sqrt 2 : ℝ) • (e0 + e1) + (Real.sqrt 2 : ℝ) • (e0 - e1) := by
      simpa using! (smul_add (Real.sqrt 2 : ℝ) (e0 + e1) (e0 - e1))
    rw [hsum]
    simp [hsqrt2_smul_e0_add_e1, hsqrt2_smul_e0_sub_e1, hsqrt2_smul_e0_add_e2]
  have hsqrt2_smul_e1_add_e2 : (Real.sqrt 2 : ℝ) • (e1 + e2) = g 2 - g 1 := by
    have : e1 + e2 = (e0 + e2) - (e0 - e1) := by abel
    rw [this, smul_sub]
    simp [hsqrt2_smul_e0_add_e2, hsqrt2_smul_e0_sub_e1]
  have hsqrt2_smul_e1_sub_e2 : (Real.sqrt 2 : ℝ) • (e1 - e2) = g 0 - g 2 := by
    have : e1 - e2 = (e0 + e1) - (e0 + e2) := by abel
    rw [this, smul_sub]
    simp [hsqrt2_smul_e0_add_e1, hsqrt2_smul_e0_add_e2]
  -- Inner product calculations for the orthonormality of `e0,e1,e2`.
  have he0e0 : (⟪e0, e0⟫ : ℝ) = 1 := by
    have hinner : (⟪e0, e0⟫ : ℝ) = k ^ 2 * (8 : ℝ) := by
      have hsmul :
          (⟪e0, e0⟫ : ℝ) = (k * k) * (⟪g 0 + g 1, g 0 + g 1⟫ : ℝ) := by
        rw [he0]
        rw [inner_smul_left, inner_smul_right]
        simp [mul_assoc]
      have hself : (⟪g 0 + g 1, g 0 + g 1⟫ : ℝ) = ‖g 0 + g 1‖ ^ 2 := by
        simp
      calc
        (⟪e0, e0⟫ : ℝ) = (k * k) * (⟪g 0 + g 1, g 0 + g 1⟫ : ℝ) := hsmul
        _ = (k * k) * (‖g 0 + g 1‖ ^ 2) := by simp
        _ = k ^ 2 * (8 : ℝ) := by
          simp [pow_two, hnormAdd]
    calc
      (⟪e0, e0⟫ : ℝ) = k ^ 2 * (8 : ℝ) := hinner
      _ = (1 / 8 : ℝ) * (8 : ℝ) := by simp [hk2]
      _ = (1 : ℝ) := by norm_num
  have he1e1 : (⟪e1, e1⟫ : ℝ) = 1 := by
    have hnn : ‖g 0 - g 1‖ ^ 2 = (8 : ℝ) := by
      calc
        ‖g 0 - g 1‖ ^ 2 = ‖g 0‖ ^ 2 - 2 * (⟪g 0, g 1⟫ : ℝ) + ‖g 1‖ ^ 2 := by
          simpa using! (norm_sub_sq_real (g 0) (g 1))
        _ = (4 : ℝ) - 2 * 0 + (4 : ℝ) := by simp [hgnorm, h01]
        _ = (8 : ℝ) := by ring
    have hinner : (⟪e1, e1⟫ : ℝ) = k ^ 2 * (8 : ℝ) := by
      have hsmul :
          (⟪e1, e1⟫ : ℝ) = (k * k) * (⟪g 0 - g 1, g 0 - g 1⟫ : ℝ) := by
        rw [he1]
        rw [inner_smul_left, inner_smul_right]
        simp [mul_assoc]
      have hself : (⟪g 0 - g 1, g 0 - g 1⟫ : ℝ) = ‖g 0 - g 1‖ ^ 2 := by
        simp
      calc
        (⟪e1, e1⟫ : ℝ) = (k * k) * (⟪g 0 - g 1, g 0 - g 1⟫ : ℝ) := hsmul
        _ = (k * k) * (‖g 0 - g 1‖ ^ 2) := by simp
        _ = k ^ 2 * (8 : ℝ) := by
          simp [pow_two, hnn]
    calc
      (⟪e1, e1⟫ : ℝ) = k ^ 2 * (8 : ℝ) := hinner
      _ = (1 / 8 : ℝ) * (8 : ℝ) := by simp [hk2]
      _ = (1 : ℝ) := by norm_num
  have he0e1 : (⟪e0, e1⟫ : ℝ) = 0 := by
    have hg00 : (⟪g 0, g 0⟫ : ℝ) = (4 : ℝ) := by
      calc
        (⟪g 0, g 0⟫ : ℝ) = ‖g 0‖ ^ 2 := by simp
        _ = (4 : ℝ) := hgnorm 0
    have hg11 : (⟪g 1, g 1⟫ : ℝ) = (4 : ℝ) := by
      calc
        (⟪g 1, g 1⟫ : ℝ) = ‖g 1‖ ^ 2 := by simp
        _ = (4 : ℝ) := hgnorm 1
    have h10 : (⟪g 1, g 0⟫ : ℝ) = 0 := by simpa [real_inner_comm] using! h01
    have hinner : (⟪g 0 + g 1, g 0 - g 1⟫ : ℝ) = 0 := by
      calc
        (⟪g 0 + g 1, g 0 - g 1⟫ : ℝ)
            = (⟪g 0, g 0 - g 1⟫ : ℝ) + (⟪g 1, g 0 - g 1⟫ : ℝ) := by
              simp [inner_add_left]
        _ = ((⟪g 0, g 0⟫ : ℝ) - (⟪g 0, g 1⟫ : ℝ)) + ((⟪g 1, g 0⟫ : ℝ) - (⟪g 1, g 1⟫ : ℝ)) := by
              simp [inner_sub_right]
        _ = (4 : ℝ) - 0 + (0 - (4 : ℝ)) := by
              -- Avoid rewriting `⟪x,x⟫` into `‖x‖^2`; use only the prepared equalities.
              rw [hg00, hg11, h01, h10]
        _ = 0 := by ring
    rw [he0, he1]
    rw [inner_smul_left, inner_smul_right]
    simp [hinner]
  have he0g2 : (⟪e0, g 2⟫ : ℝ) = (4 : ℝ) * k := by
    rw [he0]
    rw [inner_smul_left]
    have hsum : (⟪g 0 + g 1, g 2⟫ : ℝ) = (4 : ℝ) := by
      calc
        (⟪g 0 + g 1, g 2⟫ : ℝ) = (⟪g 0, g 2⟫ : ℝ) + (⟪g 1, g 2⟫ : ℝ) := by
          simp [inner_add_left]
        _ = (2 : ℝ) + (2 : ℝ) := by simp [h02, h12]
        _ = (4 : ℝ) := by norm_num
    -- `starRingEnd ℝ` is the identity, so this is just scalar multiplication.
    -- Reduce the inner product and commute scalars.
    have hcomm : (k : ℝ) * (4 : ℝ) = (4 : ℝ) * k := by ring
    simpa [hsum] using! hcomm
  have hscal4k : (1 / Real.sqrt 2 : ℝ) * ((4 : ℝ) * k) = (1 : ℝ) := by
    -- Expand `k = 1 / (2 * √2)` and simplify.
    rw [hk]
    have hnonneg2 : (0 : ℝ) ≤ 2 := by norm_num
    have hs : (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) = (2 : ℝ) := by
      simp [Real.mul_self_sqrt hnonneg2]
    have hden :
        (Real.sqrt 2 : ℝ) * (2 * Real.sqrt 2) =
          (2 : ℝ) * ((Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ)) := by ring
    calc
      (1 / Real.sqrt 2 : ℝ) * ((4 : ℝ) * (1 / (2 * Real.sqrt 2 : ℝ)))
          = (4 : ℝ) * ((1 / Real.sqrt 2 : ℝ) * (1 / (2 * Real.sqrt 2 : ℝ))) := by
            ring
      _ = (4 : ℝ) * (1 / ((Real.sqrt 2 : ℝ) * (2 * Real.sqrt 2))) := by
            rw [one_div_mul_one_div (a := (Real.sqrt 2 : ℝ)) (b := (2 * Real.sqrt 2 : ℝ))]
      _ = (4 : ℝ) * (1 / ((2 : ℝ) * ((Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ)))) := by
            simp [hden]
      _ = (4 : ℝ) * (1 / ((2 : ℝ) * (2 : ℝ))) := by simp [hs]
      _ = (1 : ℝ) := by norm_num
  have he0e2 : (⟪e0, e2⟫ : ℝ) = 0 := by
    -- `e2 = (1/√2) g2 - e0`.
    have hdecomp :
        (⟪e0, e2⟫ : ℝ) =
          (1 / Real.sqrt 2 : ℝ) * (⟪e0, g 2⟫ : ℝ) - (⟪e0, e0⟫ : ℝ) := by
      simp [he2, inner_sub_right, inner_smul_right]
    -- finish
    calc
      (⟪e0, e2⟫ : ℝ)
          = (1 / Real.sqrt 2 : ℝ) * (⟪e0, g 2⟫ : ℝ) - (⟪e0, e0⟫ : ℝ) := hdecomp
      _ = (1 / Real.sqrt 2 : ℝ) * ((4 : ℝ) * k) - (1 : ℝ) := by
            rw [he0g2, he0e0]
      _ = 0 := by
            rw [hscal4k]
            norm_num
  have he1g2 : (⟪e1, g 2⟫ : ℝ) = 0 := by
    have hinner : (⟪g 0 - g 1, g 2⟫ : ℝ) = 0 := by
      simp [inner_sub_left, h02, h12]
    simp [he1, inner_smul_left, hinner]
  have he1e2 : (⟪e1, e2⟫ : ℝ) = 0 := by
    have hdecomp :
        (⟪e1, e2⟫ : ℝ) =
          (1 / Real.sqrt 2 : ℝ) * (⟪e1, g 2⟫ : ℝ) - (⟪e1, e0⟫ : ℝ) := by
      simp [he2, inner_sub_right, inner_smul_right]
    have he1e0 : (⟪e1, e0⟫ : ℝ) = 0 := by
      exact inner_eq_zero_symm.mp he0e1
    -- Substitute the computed inner products.
    rw [hdecomp]
    rw [he1g2, he1e0]
    simp
  have he2e2 : (⟪e2, e2⟫ : ℝ) = 1 := by
    -- Use the representation `e2 = a - e0`, where `a = (1/√2) g2`.
    let a : ℝ²⁴ := (1 / Real.sqrt 2 : ℝ) • g 2
    have he2_def : e2 = a - e0 := by
      simpa [a] using! he2
    have hg2g2 : (⟪g 2, g 2⟫ : ℝ) = (4 : ℝ) := by
      calc
        (⟪g 2, g 2⟫ : ℝ) = ‖g 2‖ ^ 2 := by simp
        _ = (4 : ℝ) := hgnorm 2
    have hg2e0 : (⟪g 2, e0⟫ : ℝ) = (4 : ℝ) * k := by
      have hcomm : (⟪g 2, e0⟫ : ℝ) = (⟪e0, g 2⟫ : ℝ) := by
        simpa using! (real_inner_comm e0 (g 2))
      simpa [hcomm] using! he0g2
    have hsq : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2 : ℝ) = (1 / 2 : ℝ) := by
      have hnonneg2 : (0 : ℝ) ≤ 2 := by norm_num
      have hs : (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) = (2 : ℝ) := by
        simp [Real.mul_self_sqrt hnonneg2]
      calc
        (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2 : ℝ) =
            (1 / ((Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ))) := by
          simpa using!
            (one_div_mul_one_div (a := (Real.sqrt 2 : ℝ)) (b := (Real.sqrt 2 : ℝ)))
        _ = (1 / (2 : ℝ)) := by simp [hs]
        _ = (1 / 2 : ℝ) := by ring
    have haa : (⟪a, a⟫ : ℝ) = (2 : ℝ) := by
      dsimp [a]
      rw [inner_smul_left, inner_smul_right]
      -- `⟪(c•g2),(c•g2)⟫ = c*c*⟪g2,g2⟫`, and `c*c = 1/2`.
      rw [hg2g2]
      have hc : (starRingEnd ℝ) (1 / Real.sqrt 2 : ℝ) = (1 / Real.sqrt 2 : ℝ) := by simp
      rw [hc]
      -- Reassociate to use `hsq`.
      have hcc : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2 : ℝ) = (1 / 2 : ℝ) := hsq
      calc
        (1 / Real.sqrt 2 : ℝ) * ((1 / Real.sqrt 2 : ℝ) * (4 : ℝ))
            = ((1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2 : ℝ)) * (4 : ℝ) := by
                simpa using!
                  (mul_assoc (1 / Real.sqrt 2 : ℝ) (1 / Real.sqrt 2 : ℝ) (4 : ℝ)).symm
        _ = (1 / 2 : ℝ) * (4 : ℝ) := by rw [hcc]
        _ = (2 : ℝ) := by norm_num
    have hae0 : (⟪a, e0⟫ : ℝ) = (1 : ℝ) := by
      dsimp [a]
      rw [inner_smul_left]
      -- `⟪c•g2, e0⟫ = c*⟪g2,e0⟫`.
      rw [hg2e0]
      -- reduce `starRingEnd` and use `hscal4k`
      simpa [mul_assoc, mul_left_comm, mul_comm] using! hscal4k
    exact inner_eq_one_of_eq_sub (e2 := e2) (a := a) (e0 := e0) he2_def haa hae0 he0e0
  have hortho : Orthonormal ℝ (![e0, e1, e2] : Fin 3 → ℝ²⁴) := by
    exact
      (orthonormal_vec3_of_inner (e0 := e0) (e1 := e1) (e2 := e2)
        he0e0 he1e1 he2e2 he0e1 he0e2 he1e2)
  have hminVec :
      ∀ (i j : Fin 3), i ≠ j →
        (Real.sqrt 2 • ((![e0, e1, e2] : Fin 3 → ℝ²⁴) i + (![e0, e1, e2] : Fin 3 → ℝ²⁴) j)) ∈
            latticeShell4 C ∧
          (Real.sqrt 2 • ((![e0, e1, e2] : Fin 3 → ℝ²⁴) i - (![e0, e1, e2] : Fin 3 → ℝ²⁴) j)) ∈
            latticeShell4 C := by
    exact
      (minVec_mem_vec3_of_identities (C := C) (g := g) hgShell hg2_sub_g1 hg0_sub_g2
        hg0_add_g1_sub_g2 e0 e1 e2 hsqrt2_smul_e0_add_e1 hsqrt2_smul_e0_sub_e1
        hsqrt2_smul_e0_add_e2 hsqrt2_smul_e0_sub_e2 hsqrt2_smul_e1_add_e2 hsqrt2_smul_e1_sub_e2)
  exact ⟨(![e0, e1, e2] : Fin 3 → ℝ²⁴), hortho, hminVec⟩

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20
