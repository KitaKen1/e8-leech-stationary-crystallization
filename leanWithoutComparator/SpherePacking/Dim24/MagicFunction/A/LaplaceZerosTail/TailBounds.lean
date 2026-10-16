-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Group.Defs
public import SpherePacking.ModularForms.Delta.ImagAxis
public import SpherePacking.ModularForms.Lv1Lv2Identities
public import SpherePacking.Dim24.ModularForms.Psi.Defs
public import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.HolomorphyHelpers

/-!
# Tail bounds at `i∞`

This file provides crude bounds for modular forms at `i∞`. These are the analytic inputs
used to control the vertical-ray integrands in the tail deformation for
`I₂' + I₄' + I₆'`.

## Main statements
* `TailBounds.exists_bound_norm_Δ_inv_mul_exp_two_pi`
* `TailBounds.exists_bound_norm_pow_ten_varphi_S`
-/

open Complex Real MeasureTheory Filter
open scoped UpperHalfPlane Topology

namespace SpherePacking.Dim24

noncomputable section

open UpperHalfPlane MatrixGroups
open MagicFunction.Parametrisations
open RealIntegrals RealIntegrals.ComplexIntegrands

namespace LaplaceZerosTail

/-!
## Basic growth bounds at `i∞` (for `Δ⁻¹`, `E₂`, `E₄`, `E₆`, `varphi₁`, `varphi₂`)

These are the only analytic inputs needed to justify:
- integrability of the vertical-ray integrands for `u > 4`, and
- vanishing of the top-edge integrals as the height tends to `∞`.
-/

namespace TailBounds

open Filter Asymptotics
open scoped UpperHalfPlane

/-- A crude growth bound for `Δ⁻¹` at `i∞`: for large `im z`,
`‖(Δ z)⁻¹‖ ≤ C * exp(2π * im z)`. -/
public lemma exists_bound_norm_Δ_inv_mul_exp_two_pi :
    ∃ C A : ℝ, 0 < C ∧ ∀ z : ℍ, A ≤ z.im → ‖(Δ z)⁻¹‖ ≤ C * Real.exp (2 * Real.pi * z.im) := by
  -- Standard estimate: `Δ z ~ exp(2π i z)` at `i∞`.
  have hBigO :
      (fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im)) =O[atImInfty] Delta := by
    simpa using! (Delta_isTheta_rexp.2)
  rw [Asymptotics.isBigO_iff''] at hBigO
  rcases hBigO with ⟨c, hcpos, hEvent⟩
  have hSet :
      {z : ℍ | c * ‖Real.exp (-2 * Real.pi * z.im)‖ ≤ ‖Delta z‖} ∈ atImInfty := by
    simpa using! hEvent
  rcases (UpperHalfPlane.atImInfty_mem _).1 hSet with ⟨A, hA⟩
  refine ⟨c⁻¹, A, inv_pos.2 hcpos, ?_⟩
  intro z hz
  have hLower0 : c * ‖Real.exp (-2 * Real.pi * z.im)‖ ≤ ‖Delta z‖ := hA z hz
  have hLower : c * Real.exp (-2 * Real.pi * z.im) ≤ ‖Δ z‖ := by
    simpa [Delta_apply] using! hLower0
  have ha : 0 < c * Real.exp (-2 * Real.pi * z.im) := mul_pos hcpos (Real.exp_pos _)
  have hΔpos : 0 < ‖Δ z‖ := by
    simpa [norm_pos_iff] using! (Δ_ne_zero z)
  have hinv : ‖Δ z‖⁻¹ ≤ (c * Real.exp (-2 * Real.pi * z.im))⁻¹ :=
    (inv_le_inv₀ hΔpos ha).2 hLower
  calc
    ‖(Δ z)⁻¹‖ = ‖Δ z‖⁻¹ := by simp [norm_inv]
    _ ≤ (c * Real.exp (-2 * Real.pi * z.im))⁻¹ := hinv
    _ = c⁻¹ * Real.exp (2 * Real.pi * z.im) := by
          simp [mul_assoc, mul_comm, Real.exp_neg]

lemma exists_bound_norm_E₂ :
    ∃ A : ℝ, ∀ z : ℍ, A ≤ z.im → ‖E₂ z‖ ≤ 2 := by
  have hE2 : Tendsto E₂ atImInfty (𝓝 (1 : ℂ)) := tendsto_E₂_atImInfty
  have hball : ∀ᶠ z : ℍ in atImInfty, ‖E₂ z - (1 : ℂ)‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using!
      (hE2.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num)))
  have hbound : ∀ᶠ z : ℍ in atImInfty, ‖E₂ z‖ ≤ 2 := by
    filter_upwards [hball] with z hz
    have : ‖E₂ z‖ ≤ ‖E₂ z - (1 : ℂ)‖ + ‖(1 : ℂ)‖ := by
      -- `E₂ z = (E₂ z - 1) + 1`.
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using!
        (norm_add_le (E₂ z - (1 : ℂ)) (1 : ℂ))
    have hz' : ‖E₂ z - (1 : ℂ)‖ ≤ 1 := le_of_lt hz
    have h1 : ‖(1 : ℂ)‖ = (1 : ℝ) := by simp
    linarith [this, hz', h1]
  rcases (Filter.eventually_atImInfty).1 hbound with ⟨A, hA⟩
  exact ⟨A, hA⟩

lemma exists_bound_norm_E₄ :
    ∃ A : ℝ, ∀ z : ℍ, A ≤ z.im → ‖E₄ z‖ ≤ 2 := by
  have hE4 : Tendsto (fun z : ℍ => E₄ z) atImInfty (𝓝 (1 : ℂ)) :=
    SpherePacking.ModularForms.tendsto_E₄_atImInfty
  have hball : ∀ᶠ z : ℍ in atImInfty, ‖E₄ z - (1 : ℂ)‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using!
      (hE4.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num)))
  have hbound : ∀ᶠ z : ℍ in atImInfty, ‖E₄ z‖ ≤ 2 := by
    filter_upwards [hball] with z hz
    have : ‖E₄ z‖ ≤ ‖E₄ z - (1 : ℂ)‖ + ‖(1 : ℂ)‖ := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using!
        (norm_add_le (E₄ z - (1 : ℂ)) (1 : ℂ))
    have hz' : ‖E₄ z - (1 : ℂ)‖ ≤ 1 := le_of_lt hz
    have h1 : ‖(1 : ℂ)‖ = (1 : ℝ) := by simp
    linarith [this, hz', h1]
  rcases (Filter.eventually_atImInfty).1 hbound with ⟨A, hA⟩
  exact ⟨A, hA⟩

lemma exists_bound_norm_E₆ :
    ∃ A : ℝ, ∀ z : ℍ, A ≤ z.im → ‖E₆ z‖ ≤ 2 := by
  have hE6 : Tendsto (fun z : ℍ => E₆ z) atImInfty (𝓝 (1 : ℂ)) :=
    SpherePacking.ModularForms.tendsto_E₆_atImInfty
  have hball : ∀ᶠ z : ℍ in atImInfty, ‖E₆ z - (1 : ℂ)‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using!
      (hE6.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num)))
  have hbound : ∀ᶠ z : ℍ in atImInfty, ‖E₆ z‖ ≤ 2 := by
    filter_upwards [hball] with z hz
    have : ‖E₆ z‖ ≤ ‖E₆ z - (1 : ℂ)‖ + ‖(1 : ℂ)‖ := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using!
        (norm_add_le (E₆ z - (1 : ℂ)) (1 : ℂ))
    have hz' : ‖E₆ z - (1 : ℂ)‖ ≤ 1 := le_of_lt hz
    have h1 : ‖(1 : ℂ)‖ = (1 : ℝ) := by simp
    linarith [this, hz', h1]
  rcases (Filter.eventually_atImInfty).1 hbound with ⟨A, hA⟩
  exact ⟨A, hA⟩

lemma exists_bound_norm_varphi₁_mul_exp_neg_four_pi :
    ∃ C A : ℝ, ∀ z : ℍ, A ≤ z.im → ‖varphi₁ z‖ ≤ C * Real.exp (4 * Real.pi * z.im) := by
  rcases exists_bound_norm_Δ_inv_mul_exp_two_pi with ⟨CΔ, AΔ, hCΔ, hΔ⟩
  rcases exists_bound_norm_E₂ with ⟨A2, hE2⟩
  rcases exists_bound_norm_E₄ with ⟨A4, hE4⟩
  rcases exists_bound_norm_E₆ with ⟨A6, hE6⟩
  let A : ℝ := max AΔ (max A2 (max A4 A6))
  have hAΔ : AΔ ≤ A := le_max_left _ _
  have hA2 : A2 ≤ A :=
    le_trans (le_max_left A2 (max A4 A6)) (le_max_right AΔ (max A2 (max A4 A6)))
  have hA4 : A4 ≤ A :=
    le_trans (le_trans (le_max_left A4 A6) (le_max_right A2 (max A4 A6)))
        (le_max_right AΔ (max A2 (max A4 A6)))
  have hA6 : A6 ≤ A :=
    le_trans (le_trans (le_max_right A4 A6) (le_max_right A2 (max A4 A6)))
        (le_max_right AΔ (max A2 (max A4 A6)))
  -- Crude bounding: on `Im z ≥ A`, the Eisenstein series are bounded by `2`,
  -- and `‖Δ⁻¹‖ ≤ CΔ * exp(2π Im z)` so `‖Δ⁻²‖ ≤ CΔ² * exp(4π Im z)`.
  refine ⟨(‖((- (6 * (Complex.I : ℂ)) / (π : ℂ)) * 48 : ℂ)‖ * ((2 : ℝ) ^ (3 : ℕ)) +
            ‖((12 : ℂ) * Complex.I / (π : ℂ) : ℂ)‖ *
              (2 *
                    (‖(-49 : ℂ)‖ * ((2 : ℝ) ^ (3 : ℕ)) +
                      ‖(25 : ℂ)‖ * ((2 : ℝ) ^ (2 : ℕ))))) *
          (CΔ ^ 2),
          A, ?_⟩
  intro z hz
  have hzΔ : AΔ ≤ z.im := le_trans hAΔ hz
  have hz2 : A2 ≤ z.im := le_trans hA2 hz
  have hz4 : A4 ≤ z.im := le_trans hA4 hz
  have hz6 : A6 ≤ z.im := le_trans hA6 hz
  have hE2z : ‖E₂ z‖ ≤ 2 := hE2 z hz2
  have hE4z : ‖E₄ z‖ ≤ 2 := hE4 z hz4
  have hE6z : ‖E₆ z‖ ≤ 2 := hE6 z hz6
  have hΔz : ‖(Δ z)⁻¹‖ ≤ CΔ * Real.exp (2 * Real.pi * z.im) := hΔ z hzΔ
  have hΔz2 :
      ‖((Δ z) ^ (2 : ℕ))⁻¹‖ ≤ (CΔ ^ 2) * Real.exp (4 * Real.pi * z.im) := by
    have hsq : ‖(Δ z)⁻¹‖ ^ (2 : ℕ) ≤ (CΔ * Real.exp (2 * Real.pi * z.im)) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (norm_nonneg _) hΔz 2
    have hnormPow : ‖((Δ z) ^ (2 : ℕ))⁻¹‖ = ‖(Δ z)⁻¹‖ ^ (2 : ℕ) := by
      simp [norm_inv, norm_pow]
    have hexp :
        (Real.exp (2 * Real.pi * z.im)) ^ (2 : ℕ) = Real.exp (4 * Real.pi * z.im) := by
      have ha : (2 * Real.pi * z.im) + (2 * Real.pi * z.im) = 4 * Real.pi * z.im := by ring
      calc
        (Real.exp (2 * Real.pi * z.im)) ^ (2 : ℕ)
            = Real.exp ((2 * Real.pi * z.im) + (2 * Real.pi * z.im)) := by
                simp [pow_two, Real.exp_add, mul_assoc, mul_comm]
        _ = Real.exp (4 * Real.pi * z.im) := by simp [ha]
    have hmul :
        (CΔ * Real.exp (2 * Real.pi * z.im)) ^ (2 : ℕ) =
          (CΔ ^ 2) * Real.exp (4 * Real.pi * z.im) := by
      -- `(CΔ * exp a)^2 = CΔ^2 * (exp a)^2`.
      calc
        (CΔ * Real.exp (2 * Real.pi * z.im)) ^ (2 : ℕ) =
            (CΔ ^ (2 : ℕ)) * (Real.exp (2 * Real.pi * z.im)) ^ (2 : ℕ) := by
              simp [mul_pow, mul_assoc, mul_comm]
        _ = (CΔ ^ (2 : ℕ)) * Real.exp (4 * Real.pi * z.im) := by
              rw [hexp]
        _ = (CΔ ^ 2) * Real.exp (4 * Real.pi * z.im) := by
              simp
    lia
  -- Bounds for the two numerator pieces.
  have hE4sq : ‖(E₄ z) ^ (2 : ℕ)‖ ≤ (2 : ℝ) ^ (2 : ℕ) := by
    simpa [norm_pow] using! pow_le_pow_left₀ (norm_nonneg _) hE4z 2
  have hE4cube : ‖(E₄ z) ^ (3 : ℕ)‖ ≤ (2 : ℝ) ^ (3 : ℕ) := by
    simpa [norm_pow] using! pow_le_pow_left₀ (norm_nonneg _) hE4z 3
  have hE6sq : ‖(E₆ z) ^ (2 : ℕ)‖ ≤ (2 : ℝ) ^ (2 : ℕ) := by
    simpa [norm_pow] using! pow_le_pow_left₀ (norm_nonneg _) hE6z 2
  have hnum1 : ‖(E₆ z) * (E₄ z) ^ (2 : ℕ)‖ ≤ (2 : ℝ) ^ (3 : ℕ) := by
    have := (norm_mul_le (E₆ z) ((E₄ z) ^ (2 : ℕ))).trans
        (mul_le_mul hE6z hE4sq (norm_nonneg _) (by linarith))
    simpa [pow_succ, pow_two, mul_assoc, mul_left_comm, mul_comm] using! this
  have hlin :
      ‖(-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ)‖ ≤
        ‖(-49 : ℂ)‖ * ((2 : ℝ) ^ (3 : ℕ)) + ‖(25 : ℂ)‖ * ((2 : ℝ) ^ (2 : ℕ)) := by
    have hA : ‖(-49 : ℂ) * (E₄ z) ^ (3 : ℕ)‖ ≤ ‖(-49 : ℂ)‖ * ((2 : ℝ) ^ (3 : ℕ)) := by
      calc
        ‖(-49 : ℂ) * (E₄ z) ^ (3 : ℕ)‖ = ‖(-49 : ℂ)‖ * ‖(E₄ z) ^ (3 : ℕ)‖ := by simp
        _ ≤ ‖(-49 : ℂ)‖ * ((2 : ℝ) ^ (3 : ℕ)) := by gcongr
    have hB : ‖(25 : ℂ) * (E₆ z) ^ (2 : ℕ)‖ ≤ ‖(25 : ℂ)‖ * ((2 : ℝ) ^ (2 : ℕ)) := by
      calc
        ‖(25 : ℂ) * (E₆ z) ^ (2 : ℕ)‖ = ‖(25 : ℂ)‖ * ‖(E₆ z) ^ (2 : ℕ)‖ := by simp
        _ ≤ ‖(25 : ℂ)‖ * ((2 : ℝ) ^ (2 : ℕ)) := by gcongr
    exact (norm_add_le _ _).trans (by linarith [hA, hB])
  have hnum2 :
      ‖E₂ z * ((-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ))‖ ≤
        2 * (‖(-49 : ℂ)‖ * ((2 : ℝ) ^ (3 : ℕ)) + ‖(25 : ℂ)‖ * ((2 : ℝ) ^ (2 : ℕ))) :=
    norm_mul_le_of_le (hE2 z hz2) hlin
  -- Put everything together.
  have hterm1 :
      ‖(- (6 * (Complex.I : ℂ)) / (π : ℂ) * 48 * ((E₆ z) * (E₄ z) ^ (2 : ℕ)) / (Δ z) ^ (2 : ℕ))‖ ≤
        (‖((- (6 * (Complex.I : ℂ)) / (π : ℂ)) * 48 : ℂ)‖ * ((2 : ℝ) ^ (3 : ℕ))) *
          ((CΔ ^ 2) * Real.exp (4 * Real.pi * z.im)) := by
    calc
      ‖(- (6 * (Complex.I : ℂ)) / (π : ℂ) * 48 * ((E₆ z) * (E₄ z) ^ (2 : ℕ)) / (Δ z) ^ (2 : ℕ))‖
          = ‖((- (6 * (Complex.I : ℂ)) / (π : ℂ)) * 48 : ℂ)‖ *
              ‖(E₆ z) * (E₄ z) ^ (2 : ℕ)‖ * ‖((Δ z) ^ (2 : ℕ))⁻¹‖ := by
              simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ (‖((- (6 * (Complex.I : ℂ)) / (π : ℂ)) * 48 : ℂ)‖ * ((2 : ℝ) ^ (3 : ℕ))) *
              ((CΔ ^ 2) * Real.exp (4 * Real.pi * z.im)) := by
              gcongr
  have hterm2 :
      ‖((12 : ℂ) * Complex.I / (π : ℂ) *
            (E₂ z * ((-49) * (E₄ z) ^ (3 : ℕ) + 25 * (E₆ z) ^ (2 : ℕ))) /
          (Δ z) ^ (2 : ℕ))‖ ≤
        (‖((12 : ℂ) * Complex.I / (π : ℂ) : ℂ)‖ *
              (2 * (‖(-49 : ℂ)‖ * ((2 : ℝ) ^ (3 : ℕ)) + ‖(25 : ℂ)‖ * ((2 : ℝ) ^ (2 : ℕ))))) *
          ((CΔ ^ 2) * Real.exp (4 * Real.pi * z.im)) := by
    calc
      ‖((12 : ℂ) * Complex.I / (π : ℂ) *
            (E₂ z * ((-49) * (E₄ z) ^ (3 : ℕ) + 25 * (E₆ z) ^ (2 : ℕ))) /
          (Δ z) ^ (2 : ℕ))‖
          = ‖((12 : ℂ) * Complex.I / (π : ℂ) : ℂ)‖ *
              ‖E₂ z * ((-49) * (E₄ z) ^ (3 : ℕ) + 25 * (E₆ z) ^ (2 : ℕ))‖ *
                ‖((Δ z) ^ (2 : ℕ))⁻¹‖ := by
              simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ (‖((12 : ℂ) * Complex.I / (π : ℂ) : ℂ)‖ *
              (2 * (‖(-49 : ℂ)‖ * ((2 : ℝ) ^ (3 : ℕ)) + ‖(25 : ℂ)‖ * ((2 : ℝ) ^ (2 : ℕ))))) *
            ((CΔ ^ 2) * Real.exp (4 * Real.pi * z.im)) := by
            gcongr
  have htri :
      ‖varphi₁ z‖ ≤
        ‖(- (6 * (Complex.I : ℂ)) / (π : ℂ) * 48 * ((E₆ z) * (E₄ z) ^ (2 : ℕ)) / (Δ z) ^ (2 : ℕ))‖ +
          ‖((12 : ℂ) * Complex.I / (π : ℂ) *
                (E₂ z * ((-49) * (E₄ z) ^ (3 : ℕ) + 25 * (E₆ z) ^ (2 : ℕ))) /
              (Δ z) ^ (2 : ℕ))‖ := by
    -- `varphi₁ = term1 - term2`, use `‖a-b‖ ≤ ‖a‖+‖b‖`.
    simpa [Dim24.varphi₁, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using!
      (norm_sub_le
        ((- (6 * (Complex.I : ℂ)) / (π : ℂ)) * 48 * ((E₆ z) * (E₄ z) ^ (2 : ℕ)) / (Δ z) ^ (2 : ℕ))
        ((12 : ℂ) * Complex.I / (π : ℂ) *
              (E₂ z * ((-49) * (E₄ z) ^ (3 : ℕ) + 25 * (E₆ z) ^ (2 : ℕ))) /
            (Δ z) ^ (2 : ℕ)))
  grind only

lemma exists_bound_norm_varphi₂_mul_exp_neg_four_pi :
    ∃ C A : ℝ, ∀ z : ℍ, A ≤ z.im → ‖varphi₂ z‖ ≤ C * Real.exp (4 * Real.pi * z.im) := by
  rcases exists_bound_norm_Δ_inv_mul_exp_two_pi with ⟨CΔ, AΔ, hCΔ, hΔ⟩
  rcases exists_bound_norm_E₄ with ⟨A4, hE4⟩
  rcases exists_bound_norm_E₆ with ⟨A6, hE6⟩
  let A : ℝ := max AΔ (max A4 A6)
  have hAΔ : AΔ ≤ A := le_max_left _ _
  have hA4 : A4 ≤ A := le_trans (le_max_left A4 A6) (le_max_right AΔ (max A4 A6))
  have hA6 : A6 ≤ A := le_trans (le_max_right A4 A6) (le_max_right AΔ (max A4 A6))
  refine ⟨(‖(-36 : ℂ)‖ * (‖(-49 : ℂ)‖ * ((2 : ℝ) ^ (3 : ℕ)) + ‖(25 : ℂ)‖ * ((2 : ℝ) ^ (2 : ℕ))) *
            ‖((π : ℂ) ^ (2 : ℕ))⁻¹‖) *
          (CΔ ^ 2), A, ?_⟩
  intro z hz
  have hzΔ : AΔ ≤ z.im := le_trans hAΔ hz
  have hz4 : A4 ≤ z.im := le_trans hA4 hz
  have hz6 : A6 ≤ z.im := le_trans hA6 hz
  have hE4z : ‖E₄ z‖ ≤ 2 := hE4 z hz4
  have hE6z : ‖E₆ z‖ ≤ 2 := hE6 z hz6
  have hΔz : ‖(Δ z)⁻¹‖ ≤ CΔ * Real.exp (2 * Real.pi * z.im) := hΔ z hzΔ
  have hΔz2 :
      ‖((Δ z) ^ (2 : ℕ))⁻¹‖ ≤ (CΔ ^ 2) * Real.exp (4 * Real.pi * z.im) := by
    have hsq : ‖(Δ z)⁻¹‖ ^ (2 : ℕ) ≤ (CΔ * Real.exp (2 * Real.pi * z.im)) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (norm_nonneg _) hΔz 2
    have hnormPow : ‖((Δ z) ^ (2 : ℕ))⁻¹‖ = ‖(Δ z)⁻¹‖ ^ (2 : ℕ) := by
      simp [norm_inv, norm_pow]
    have hexp :
        (Real.exp (2 * Real.pi * z.im)) ^ (2 : ℕ) = Real.exp (4 * Real.pi * z.im) := by
      have ha : (2 * Real.pi * z.im) + (2 * Real.pi * z.im) = 4 * Real.pi * z.im := by ring
      calc
        (Real.exp (2 * Real.pi * z.im)) ^ (2 : ℕ)
            = Real.exp ((2 * Real.pi * z.im) + (2 * Real.pi * z.im)) := by
                simp [pow_two, Real.exp_add, mul_assoc, mul_comm]
        _ = Real.exp (4 * Real.pi * z.im) := by simp [ha]
    have hmul :
        (CΔ * Real.exp (2 * Real.pi * z.im)) ^ (2 : ℕ) =
          (CΔ ^ 2) * Real.exp (4 * Real.pi * z.im) := by
      calc
        (CΔ * Real.exp (2 * Real.pi * z.im)) ^ (2 : ℕ) =
            (CΔ ^ (2 : ℕ)) * (Real.exp (2 * Real.pi * z.im)) ^ (2 : ℕ) := by
              simp [mul_pow, mul_assoc, mul_comm]
        _ = (CΔ ^ (2 : ℕ)) * Real.exp (4 * Real.pi * z.im) := by
              rw [hexp]
        _ = (CΔ ^ 2) * Real.exp (4 * Real.pi * z.im) := by
              simp
    exact (hnormPow ▸ (le_trans hsq (by simp [hmul])))
  have hE4cube : ‖(E₄ z) ^ (3 : ℕ)‖ ≤ (2 : ℝ) ^ (3 : ℕ) := by
    simpa [norm_pow] using! pow_le_pow_left₀ (norm_nonneg _) hE4z 3
  have hE6sq : ‖(E₆ z) ^ (2 : ℕ)‖ ≤ (2 : ℝ) ^ (2 : ℕ) := by
    simpa [norm_pow] using! pow_le_pow_left₀ (norm_nonneg _) hE6z 2
  have hlin :
      ‖(-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ)‖ ≤
        ‖(-49 : ℂ)‖ * ((2 : ℝ) ^ (3 : ℕ)) + ‖(25 : ℂ)‖ * ((2 : ℝ) ^ (2 : ℕ)) := by
    have hA : ‖(-49 : ℂ) * (E₄ z) ^ (3 : ℕ)‖ ≤ ‖(-49 : ℂ)‖ * ((2 : ℝ) ^ (3 : ℕ)) := by
      calc
        ‖(-49 : ℂ) * (E₄ z) ^ (3 : ℕ)‖ = ‖(-49 : ℂ)‖ * ‖(E₄ z) ^ (3 : ℕ)‖ := by simp
        _ ≤ ‖(-49 : ℂ)‖ * ((2 : ℝ) ^ (3 : ℕ)) := by gcongr
    have hB : ‖(25 : ℂ) * (E₆ z) ^ (2 : ℕ)‖ ≤ ‖(25 : ℂ)‖ * ((2 : ℝ) ^ (2 : ℕ)) := by
      calc
        ‖(25 : ℂ) * (E₆ z) ^ (2 : ℕ)‖ = ‖(25 : ℂ)‖ * ‖(E₆ z) ^ (2 : ℕ)‖ := by simp
        _ ≤ ‖(25 : ℂ)‖ * ((2 : ℝ) ^ (2 : ℕ)) := by gcongr
    exact (norm_add_le _ _).trans (by linarith [hA, hB])
  -- Unfold and bound.
  have : varphi₂ z =
      (-36 : ℂ) * ((-49) * (E₄ z) ^ (3 : ℕ) + 25 * (E₆ z) ^ (2 : ℕ)) *
        ((π : ℂ) ^ (2 : ℕ))⁻¹ * ((Δ z) ^ (2 : ℕ))⁻¹ := by
    simp [Dim24.varphi₂, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  rw [this]
  calc
    ‖(-36 : ℂ) * ((-49) * (E₄ z) ^ (3 : ℕ) + 25 * (E₆ z) ^ (2 : ℕ)) *
        ((π : ℂ) ^ (2 : ℕ))⁻¹ * ((Δ z) ^ (2 : ℕ))⁻¹‖
        ≤ ‖(-36 : ℂ)‖ * ‖(-49) * (E₄ z) ^ (3 : ℕ) + 25 * (E₆ z) ^ (2 : ℕ)‖ *
            ‖((π : ℂ) ^ (2 : ℕ))⁻¹‖ * ‖((Δ z) ^ (2 : ℕ))⁻¹‖ := by
            simp [mul_comm]
    _ ≤ (‖(-36 : ℂ)‖ * (‖(-49 : ℂ)‖ * ((2 : ℝ) ^ (3 : ℕ)) + ‖(25 : ℂ)‖ * ((2 : ℝ) ^ (2 : ℕ))) *
          ‖((π : ℂ) ^ (2 : ℕ))⁻¹‖) *
          ((CΔ ^ 2) * Real.exp (4 * Real.pi * z.im)) := by
            gcongr
    _ = ((‖(-36 : ℂ)‖ * (‖(-49 : ℂ)‖ * ((2 : ℝ) ^ (3 : ℕ)) + ‖(25 : ℂ)‖ * ((2 : ℝ) ^ (2 : ℕ))) *
          ‖((π : ℂ) ^ (2 : ℕ))⁻¹‖) *
          (CΔ ^ 2)) * Real.exp (4 * Real.pi * z.im) := by
            ring

/-!
### Bounds used in the tail deformation (`u > 4`)

The rectangle deformation `rect_deform_of_tendsto_top` requires:
- integrability of the vertical-edge restrictions on `Set.Ioi 1`, and
- `Tendsto`-vanishing of the top-edge interval integrals as the height tends to `∞`.

We keep the bounds crude: we only use that `varphi, varphi₁, varphi₂` grow at most like
`exp(4π·Im z)` at `i∞`, so multiplying by `expU u` gives exponential decay for `u > 4`.
-/

open scoped Interval Topology

lemma exists_bound_norm_varphi_mul_exp_neg_two_pi :
    ∃ C A : ℝ, 0 < C ∧ ∀ z : ℍ, A ≤ z.im → ‖varphi z‖ ≤ C * Real.exp (-(2 * Real.pi) * z.im) := by
  have hBigO :
      (varphi : ℍ → ℂ) =O[atImInfty] fun z : ℍ => Real.exp (-(2 * Real.pi) * z.im) :=
    VarphiBounds.varphi_isBigO_exp_neg_two_pi
  rw [Asymptotics.isBigO_iff''] at hBigO
  rcases hBigO with ⟨c, hcpos, hEvent⟩
  have hSet :
      {z : ℍ | c * ‖varphi z‖ ≤ ‖Real.exp (-(2 * Real.pi) * z.im)‖} ∈ atImInfty := by
    simpa using! hEvent
  rcases (UpperHalfPlane.atImInfty_mem _).1 hSet with ⟨A, hA⟩
  refine ⟨c⁻¹, A, inv_pos.2 hcpos, ?_⟩
  intro z hz
  have hz' : c * ‖varphi z‖ ≤ ‖Real.exp (-(2 * Real.pi) * z.im)‖ := hA z hz
  have hnonneg : 0 ≤ Real.exp (-(2 * Real.pi) * z.im) := (Real.exp_pos _).le
  have hz'' :
      ‖varphi z‖ ≤ c⁻¹ * ‖Real.exp (-(2 * Real.pi) * z.im)‖ := by
    exact (le_inv_mul_iff₀ hcpos).mpr hz'
  simpa [Real.norm_of_nonneg hnonneg, mul_assoc] using! hz''

lemma exists_bound_norm_varphi_mul_exp_four_pi :
    ∃ C A : ℝ, 0 < C ∧ ∀ z : ℍ, A ≤ z.im → ‖varphi z‖ ≤ C * Real.exp (4 * Real.pi * z.im) := by
  rcases exists_bound_norm_varphi_mul_exp_neg_two_pi with ⟨C, A, hCpos, hC⟩
  refine ⟨C, max A 0, hCpos, ?_⟩
  intro z hz
  have hzA : A ≤ z.im := le_trans (le_max_left _ _) hz
  have hz0 : 0 ≤ z.im := le_trans (le_max_right _ _) hz
  have hmain := hC z hzA
  have hexp :
      Real.exp (-(2 * Real.pi) * z.im) ≤ Real.exp (4 * Real.pi * z.im) := by
    have : (-(2 * Real.pi) * z.im) ≤ 4 * Real.pi * z.im := by
      nlinarith [Real.pi_pos, hz0]
    exact Real.exp_le_exp.2 this
  have hCnonneg : 0 ≤ C := hCpos.le
  exact le_trans hmain (mul_le_mul_of_nonneg_left hexp hCnonneg)

/-- A polynomial-exponential growth bound for the `S`-transform of `varphi`, packaged as an
estimate for `‖z ^ 10 * varphi (S • z)‖` in terms of `‖z‖` and `exp(4π * im z)` for large `im z`. -/
public lemma exists_bound_norm_pow_ten_varphi_S :
    ∃ K A : ℝ, 0 < K ∧ ∀ z : ℍ, A ≤ z.im →
      ‖((z : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • z)‖ ≤
        K * (‖(z : ℂ)‖ ^ (2 : ℕ) + ‖(z : ℂ)‖ + 1) * Real.exp (4 * Real.pi * z.im) := by
  rcases exists_bound_norm_varphi_mul_exp_four_pi with ⟨Cv, Av, hCvpos, hCv⟩
  rcases exists_bound_norm_varphi₁_mul_exp_neg_four_pi with ⟨C1, A1, hC1⟩
  rcases exists_bound_norm_varphi₂_mul_exp_neg_four_pi with ⟨C2, A2, hC2⟩
  -- First, `C1` and `C2` are nonnegative: otherwise their upper bounds would contradict `0 ≤ ‖·‖`.
  have hC1nonneg : 0 ≤ C1 := by
    let t : ℝ := max A1 1
    have ht : 0 < t := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    let z0 : ℍ := it t ht
    have hz0 : A1 ≤ z0.im := by
      have : A1 ≤ t := le_max_left _ _
      have hz0im : z0.im = t := by
        change (Complex.I * (t : ℂ)).im = t
        simp
      simpa [hz0im] using! this
    have h := hC1 z0 hz0
    have hexp : 0 < Real.exp (4 * Real.pi * z0.im) := Real.exp_pos _
    have : 0 ≤ C1 * Real.exp (4 * Real.pi * z0.im) := le_trans (norm_nonneg _) h
    exact (mul_nonneg_iff_of_pos_right hexp).1 this
  have hC2nonneg : 0 ≤ C2 := by
    let t : ℝ := max A2 1
    have ht : 0 < t := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    let z0 : ℍ := it t ht
    have hz0 : A2 ≤ z0.im := by
      have : A2 ≤ t := le_max_left _ _
      have hz0im : z0.im = t := by
        change (Complex.I * (t : ℂ)).im = t
        simp
      simpa [hz0im] using! this
    have h := hC2 z0 hz0
    have hexp : 0 < Real.exp (4 * Real.pi * z0.im) := Real.exp_pos _
    have : 0 ≤ C2 * Real.exp (4 * Real.pi * z0.im) := le_trans (norm_nonneg _) h
    exact (mul_nonneg_iff_of_pos_right hexp).1 this
  let A : ℝ := max Av (max A1 A2)
  let K : ℝ := max 1 (max Cv (max C1 C2))
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨K, A, hKpos, ?_⟩
  intro z hz
  have hzv : Av ≤ z.im := le_trans (le_max_left _ _) hz
  have hz1 : A1 ≤ z.im := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hz
  have hz2 : A2 ≤ z.im := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hz
  have hvar : ‖varphi z‖ ≤ Cv * Real.exp (4 * Real.pi * z.im) := hCv z hzv
  have hvar1 : ‖varphi₁ z‖ ≤ C1 * Real.exp (4 * Real.pi * z.im) := hC1 z hz1
  have hvar2 : ‖varphi₂ z‖ ≤ C2 * Real.exp (4 * Real.pi * z.im) := hC2 z hz2
  have hS : ((z : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • z) =
      (z : ℂ) ^ (2 : ℕ) * varphi z + (z : ℂ) * varphi₁ z + varphi₂ z := by
    simpa using! (varphi_S_mul_pow (z := z))
  rw [hS]
  have htri :
      ‖(z : ℂ) ^ (2 : ℕ) * varphi z + (z : ℂ) * varphi₁ z + varphi₂ z‖ ≤
        ‖(z : ℂ) ^ (2 : ℕ) * varphi z‖ + ‖(z : ℂ) * varphi₁ z‖ + ‖varphi₂ z‖ :=
    norm_add₃_le
  have hpow2 : ‖(z : ℂ) ^ (2 : ℕ)‖ = ‖(z : ℂ)‖ ^ (2 : ℕ) := by simp [norm_pow]
  have hmul1 :
      ‖(z : ℂ) ^ (2 : ℕ) * varphi z‖ ≤
        (‖(z : ℂ)‖ ^ (2 : ℕ)) * (Cv * Real.exp (4 * Real.pi * z.im)) := by
    calc
      ‖(z : ℂ) ^ (2 : ℕ) * varphi z‖ ≤ ‖(z : ℂ) ^ (2 : ℕ)‖ * ‖varphi z‖ := norm_mul_le _ _
      _ ≤ (‖(z : ℂ)‖ ^ (2 : ℕ)) * (Cv * Real.exp (4 * Real.pi * z.im)) := by
            have hnorm : ‖(z : ℂ) ^ (2 : ℕ)‖ ≤ ‖(z : ℂ)‖ ^ (2 : ℕ) :=
              le_of_eq hpow2
            exact mul_le_mul hnorm hvar (norm_nonneg _) (by positivity)
  have hmul2 :
      ‖(z : ℂ) * varphi₁ z‖ ≤ ‖(z : ℂ)‖ * (C1 * Real.exp (4 * Real.pi * z.im)) := by
    calc
      ‖(z : ℂ) * varphi₁ z‖ ≤ ‖(z : ℂ)‖ * ‖varphi₁ z‖ := norm_mul_le _ _
      _ ≤ ‖(z : ℂ)‖ * (C1 * Real.exp (4 * Real.pi * z.im)) := by gcongr
  have hCv_le : Cv ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC1_le : C1 ≤ K :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hC2_le : C2 ≤ K :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hK0 : 0 ≤ K := hKpos.le
  have hExp0 : 0 ≤ Real.exp (4 * Real.pi * z.im) := (Real.exp_pos _).le
  have hz0 : 0 ≤ ‖(z : ℂ)‖ := norm_nonneg _
  have hz2_0 : 0 ≤ ‖(z : ℂ)‖ ^ (2 : ℕ) := by positivity
  calc
    ‖(z : ℂ) ^ (2 : ℕ) * varphi z + (z : ℂ) * varphi₁ z + varphi₂ z‖
        ≤ ‖(z : ℂ) ^ (2 : ℕ) * varphi z‖ + ‖(z : ℂ) * varphi₁ z‖ + ‖varphi₂ z‖ := htri
    _ ≤ (‖(z : ℂ)‖ ^ (2 : ℕ)) * (Cv * Real.exp (4 * Real.pi * z.im)) +
          ‖(z : ℂ)‖ * (C1 * Real.exp (4 * Real.pi * z.im)) +
          (C2 * Real.exp (4 * Real.pi * z.im)) := by
          linarith [hmul1, hmul2, hvar2]
    _ ≤ (‖(z : ℂ)‖ ^ (2 : ℕ)) * (K * Real.exp (4 * Real.pi * z.im)) +
          ‖(z : ℂ)‖ * (K * Real.exp (4 * Real.pi * z.im)) +
          (K * Real.exp (4 * Real.pi * z.im)) := by
          -- Replace `Cv,C1,C2` by the common constant `K`.
          have hCv' : Cv * Real.exp (4 * Real.pi * z.im) ≤ K * Real.exp (4 * Real.pi * z.im) :=
            mul_le_mul_of_nonneg_right hCv_le hExp0
          have hC1' : C1 * Real.exp (4 * Real.pi * z.im) ≤ K * Real.exp (4 * Real.pi * z.im) :=
            mul_le_mul_of_nonneg_right hC1_le hExp0
          have hC2' : C2 * Real.exp (4 * Real.pi * z.im) ≤ K * Real.exp (4 * Real.pi * z.im) :=
            mul_le_mul_of_nonneg_right hC2_le hExp0
          have hA : (‖(z : ℂ)‖ ^ (2 : ℕ)) * (Cv * Real.exp (4 * Real.pi * z.im)) ≤
              (‖(z : ℂ)‖ ^ (2 : ℕ)) * (K * Real.exp (4 * Real.pi * z.im)) :=
            mul_le_mul_of_nonneg_left hCv' hz2_0
          have hB : ‖(z : ℂ)‖ * (C1 * Real.exp (4 * Real.pi * z.im)) ≤
              ‖(z : ℂ)‖ * (K * Real.exp (4 * Real.pi * z.im)) :=
            mul_le_mul_of_nonneg_left hC1' hz0
          exact add_le_add_three hA hB hC2'
    _ = K * (‖(z : ℂ)‖ ^ (2 : ℕ) + ‖(z : ℂ)‖ + 1) * Real.exp (4 * Real.pi * z.im) := by
          -- collect the common factors
          ring

  -- `exists_bound_norm_pow_ten_varphi_S` already provides the bound we need.


end TailBounds

end LaplaceZerosTail

end

end SpherePacking.Dim24
