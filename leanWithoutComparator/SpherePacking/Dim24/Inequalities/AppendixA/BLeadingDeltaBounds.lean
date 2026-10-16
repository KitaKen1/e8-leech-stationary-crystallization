-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.ModularForms.Psi.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic


/-!
Elementary bounds for `Δ(it)` used in Appendix A truncation arguments.

In the `Bleadingterms` proof (paper Appendix A, Lemma A.3), one works with
`(B(t) - leading) * Δ(it)^2`. To pass back to `B(t) - leading`, it is useful to know
`0 < (Δ(it)).re ≤ 1` for `t > 0`.
-/

open UpperHalfPlane
open Filter
open scoped Topology

noncomputable section

namespace SpherePacking.Dim24

/-- Along the imaginary axis, `Δ(it)` is real-valued (so its imaginary part is `0`). -/
@[simp] public lemma Delta_it_im (t : ℝ) (ht : 0 < t) : (Δ (it t ht)).im = 0 := by
  -- `Δ.resToImagAxis t` is definitionaly `Δ(it t)`.
  simpa [ResToImagAxis, ht, it] using! (Delta_imag_axis_real (t := t) ht)

/-- Positivity of the real part of `Δ(it)` for `t > 0`. -/
public lemma Delta_it_re_pos (t : ℝ) (ht : 0 < t) : 0 < (Δ (it t ht)).re := by
  simpa [ResToImagAxis, ht, it] using! (Delta_imag_axis_pos.2 t ht)

/-- Upper bound `Δ(it) ≤ 1` on the imaginary axis, stated for the real part. -/
public lemma Delta_it_re_le_one (t : ℝ) (ht : 0 < t) : (Δ (it t ht)).re ≤ 1 := by
  -- Use the product formula from `SpherePacking/ModularForms/Delta.lean`.
  have hre :
      (Δ (it t ht)).re =
        Real.exp (-2 * Real.pi * t) *
          ∏' n : ℕ, (1 - Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t))) ^ 24 := by
    simpa [ResToImagAxis, ht, it] using! (re_ResToImagAxis_Delta_eq_real_prod (t := t) ht)
  set f : ℕ → ℝ := fun n =>
    (1 - Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t))) ^ 24
  have exp_neg_le_one (n : ℕ) : Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t)) ≤ 1 := by
    have hnonneg : 0 ≤ 2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t := by positivity [Real.pi_pos, ht]
    simpa using! (Real.exp_le_one_iff.2 (neg_nonpos.2 hnonneg))
  have hbase0 (n : ℕ) : 0 ≤ 1 - Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t)) :=
    sub_nonneg.2 (exp_neg_le_one n)
  have hf0 : ∀ n, 0 ≤ f n := by
    intro n
    simpa [f] using! pow_nonneg (hbase0 n) 24
  have hf1 : ∀ n, f n ≤ 1 := by
    intro n
    have hbase1 : (1 - Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * t))) ≤ 1 := by
      -- `1 - x ≤ 1` whenever `0 ≤ x`.
      exact sub_le_self _ (Real.exp_pos _).le
    -- `0 ≤ base ≤ 1` implies `base^24 ≤ 1`.
    simpa [f] using! (pow_le_one₀ (n := 24) (hbase0 n) hbase1)
  have hprod_le_one : (∏' n : ℕ, f n) ≤ 1 := by
    by_cases hm : Multipliable f
    · have hlim :
          Tendsto (fun N : ℕ => ∏ n ∈ Finset.range N, f n) atTop (𝓝 (∏' n : ℕ, f n)) :=
        (hm.hasProd).tendsto_prod_nat
      refine (isClosed_Iic : IsClosed (Set.Iic (1 : ℝ))).mem_of_tendsto hlim ?_
      refine (eventually_atTop.2 ⟨0, fun N _ => ?_⟩)
      exact Finset.prod_le_one (fun n _hn => hf0 n) (fun n _hn => hf1 n)
    · simp [tprod_eq_one_of_not_multipliable hm]
  have hexp_le_one : Real.exp (-2 * Real.pi * t) ≤ 1 := by
    have : (-2 * Real.pi * t) ≤ 0 := by nlinarith [Real.pi_pos, ht]
    simpa using! (Real.exp_le_one_iff.2 this)
  -- `exp(-2πt) * prod ≤ exp(-2πt) ≤ 1`.
  calc
    (Δ (it t ht)).re = Real.exp (-2 * Real.pi * t) * (∏' n : ℕ, f n) := by
          simpa [f] using! hre
    _ ≤ Real.exp (-2 * Real.pi * t) * 1 :=
          mul_le_mul_of_nonneg_left hprod_le_one (Real.exp_pos _).le
    _ ≤ 1 := by simpa using! hexp_le_one

/-- Squared version of `Delta_it_re_le_one`, useful for `Δ(it)^2`. -/
public lemma Delta_it_re_sq_le_one (t : ℝ) (ht : 0 < t) : (Δ (it t ht)).re ^ 2 ≤ 1 := by
  simpa using!
    (pow_le_pow_of_le_one (Delta_it_re_pos (t := t) ht).le (Delta_it_re_le_one (t := t) ht)
      (Nat.zero_le 2))

end SpherePacking.Dim24
