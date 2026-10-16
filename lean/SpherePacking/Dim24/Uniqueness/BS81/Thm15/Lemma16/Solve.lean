-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16.Counts
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16.MomentIdentities
public import SpherePacking.Dim24.Uniqueness.BS81.LatticeL
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Solving the BS81 Lemma 16 counting equations

From the value restriction `⟪u,v⟫ ∈ {0, ±1/2, ±1}` and the moment identities, we obtain the two
linear equations:

1. `beta/2 + 2*gamma = 16380`
2. `beta/8 + 2*gamma = 3780`

These imply `gamma = -210`, contradicting `gamma : ℕ`.

## Main statements
* `beta_gamma_eqs_of_norm_sq_two`
* `gamma_eq_neg_210_of_eqs`
* `contradiction_of_gamma_nat`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16

noncomputable section

open scoped RealInnerProductSpace BigOperators

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- The second and fourth moment identities give two linear equations for `beta` and `gamma`. -/
public theorem beta_gamma_eqs_of_norm_sq_two
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (hcard : h.code.finite.toFinset.card = 196560)
    (v : ℝ²⁴)
    (hnormv : ‖v‖ ^ 2 = (2 : ℝ))
    (hvals : ∀ u ∈ h.code.finite.toFinset,
      (⟪u, v⟫ : ℝ) = 0 ∨ (⟪u, v⟫ : ℝ) = (1 / 2 : ℝ) ∨ (⟪u, v⟫ : ℝ) = (-1 / 2 : ℝ) ∨
        (⟪u, v⟫ : ℝ) = (1 : ℝ) ∨ (⟪u, v⟫ : ℝ) = (-1 : ℝ)) :
    (beta h.code.finite.toFinset v : ℝ) * (1 / 2 : ℝ) + (gamma h.code.finite.toFinset v : ℝ) * 2 =
        (16380 : ℝ) ∧
      (beta h.code.finite.toFinset v : ℝ) * (1 / 8 : ℝ) +
        (gamma h.code.finite.toFinset v : ℝ) * 2 =
        (3780 : ℝ) := by
  constructor
  · have hsum := sum_inner_sq_eq_beta_gamma (C := C) (h := h) (v := v) hvals
    have hmoment := sum_inner_sq_eq_8190 (C := C) (h := h) hcard v
    nlinarith [hsum, hmoment, hnormv]
  · have hsum := sum_inner_pow_four_eq_beta_gamma (C := C) (h := h) (v := v) hvals
    have hmoment := sum_inner_pow_four_eq_945 (C := C) (h := h) hcard v
    have hv4 : ‖v‖ ^ 4 = (2 : ℝ) ^ 2 := by
      simpa using! (pow_mul ‖v‖ 2 2).trans (congrArg (fun t : ℝ => t ^ 2) hnormv)
    nlinarith [hsum, hmoment, hv4]

/-- Solving the two linear equations forces `gamma = -210`. -/
public theorem gamma_eq_neg_210_of_eqs
    (β γ : ℝ)
    (h1 : β * (1 / 2 : ℝ) + γ * 2 = (16380 : ℝ))
    (h2 : β * (1 / 8 : ℝ) + γ * 2 = (3780 : ℝ)) :
    γ = (-210 : ℝ) := by
  nlinarith [h1, h2]

/-- A natural number cannot be equal to `-210`. -/
public theorem contradiction_of_gamma_nat
    (γ : ℕ) (hγ : (γ : ℝ) = (-210 : ℝ)) : False := by
  have hnonneg : (0 : ℝ) ≤ (γ : ℝ) := by exact_mod_cast (Nat.zero_le γ)
  linarith [hnonneg, hγ]

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16
