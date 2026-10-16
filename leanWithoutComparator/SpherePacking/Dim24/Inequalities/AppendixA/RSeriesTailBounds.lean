-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.Constants
public import SpherePacking.Dim24.Inequalities.AppendixA.CoeffBoundConstants
public import SpherePacking.Dim24.Inequalities.AppendixA.GeometricTailBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Order


/-!
Tail bounds for `r`-series (`r = exp(-π t)`) used in Appendix A.

This file packages the geometric tail estimates that correspond to the PARI/GP
`PolynomialSum(..., 1/23, 100, ...)` checks in `appendix.txt`.
-/


open scoped BigOperators Real

namespace SpherePacking.Dim24.AppendixA

noncomputable section

/-- A convenient `≤ 1/2` bound on the geometric ratio at `r = 1/23`, `k=20`, `N=100`. -/
public lemma powGeomRatio_one_div_23_20_100_le_half :
    powGeomRatio ((1 : ℝ) / 23) 20 100 ≤ (1 : ℝ) / 2 := by
  norm_num [powGeomRatio]

/-- If `r' ≤ 1/23`, then `powGeomRatio r' 20 100 ≤ 1/2`. -/
public lemma powGeomRatio_r_le_half_of_r_le_one_div_23 {r' : ℝ}
    (hr : r' ≤ (1 : ℝ) / 23) :
    powGeomRatio r' 20 100 ≤ (1 : ℝ) / 2 := by
  exact (powGeomRatio_mono_left (q := r') (q' := (1 : ℝ) / 23) hr 20 100).trans
    powGeomRatio_one_div_23_20_100_le_half

lemma const_psi_tail_lt_eps :
    ((2 : ℚ) * ((44 : ℚ) * (16 : ℚ) * (24 : ℚ) ^ (7 : ℕ)) * (101 : ℚ) ^ (20 : ℕ) *
        ((1 : ℚ) / 23) ^ (88 : ℕ)) <
      (10 : ℚ) ^ (-50 : ℤ) := by
  -- A closed rational inequality; `norm_num` clears denominators.
  set_option maxRecDepth 6000 in
  norm_num

/-- A fully certified bound of the form `Cpsi * tail ≤ eps * r^12` at `r(t) = exp(-π t)`. -/
public theorem psi_majorant_tail_bound (t : ℝ) (ht : 1 ≤ t) :
    Cpsi * (∑' m : ℕ, powGeomTerm (r t) 20 (100 + m)) ≤ eps * (r t) ^ (12 : ℕ) := by
  have hr0 : 0 ≤ r t := r_nonneg t
  have hrle : r t ≤ (1 : ℝ) / 23 := r_le_one_div_23 (t := t) ht
  have hρ_le_half : powGeomRatio (r t) 20 100 ≤ (1 : ℝ) / 2 :=
    powGeomRatio_r_le_half_of_r_le_one_div_23 (r' := r t) hrle
  have htail_le' :
      (∑' m : ℕ, powGeomTerm (r t) 20 (100 + m)) ≤
        2 * powGeomTerm (r t) 20 100 :=
    tsum_powGeomTerm_tail_le_two_mul (q := r t) (k := 20) (N := 100) hr0 hρ_le_half
  have hmain1 :
      Cpsi * (∑' m : ℕ, powGeomTerm (r t) 20 (100 + m)) ≤
        Cpsi * (2 * powGeomTerm (r t) 20 100) :=
    mul_le_mul_of_nonneg_left htail_le' (by norm_num [Cpsi])
  have hr_pow100 : (r t) ^ (100 : ℕ) = (r t) ^ (12 : ℕ) * (r t) ^ (88 : ℕ) := by
    have : (12 + 88 : ℕ) = 100 := by decide
    simpa [this] using! (pow_add (r t) 12 88)
  have hr_pow88_le : (r t) ^ (88 : ℕ) ≤ ((1 : ℝ) / 23) ^ (88 : ℕ) :=
    pow_le_pow_left₀ hr0 hrle _
  have hconstR :
      (2 : ℝ) * (Cpsi : ℝ) * (101 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) < eps := by
    have h' :
        ((2 : ℚ) * ((44 : ℚ) * (16 : ℚ) * (24 : ℚ) ^ (7 : ℕ)) * (101 : ℚ) ^ (20 : ℕ) *
            ((1 : ℚ) / 23) ^ (88 : ℕ) : ℝ) <
          ((10 : ℚ) ^ (-50 : ℤ) : ℝ) := by
      exact_mod_cast const_psi_tail_lt_eps
    have h'' :
        (2 : ℝ) * (Cpsi : ℝ) * (101 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) <
          (10 : ℝ) ^ (-50 : ℤ) := by
      simpa [Cpsi] using! h'
    simpa [eps] using! h''
  have hconstR' :
      (2 : ℝ) * (Cpsi : ℝ) * (101 : ℝ) ^ (20 : ℕ) * (r t) ^ (88 : ℕ) ≤ eps := by
    have hle :
        (2 : ℝ) * (Cpsi : ℝ) * (101 : ℝ) ^ (20 : ℕ) * (r t) ^ (88 : ℕ) ≤
          (2 : ℝ) * (Cpsi : ℝ) * (101 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) :=
      by
        have hmul0 : 0 ≤ (2 : ℝ) * (Cpsi : ℝ) * (101 : ℝ) ^ (20 : ℕ) := by
          dsimp [Cpsi]
          positivity
        simpa [mul_assoc, mul_left_comm, mul_comm] using!
          (mul_le_mul_of_nonneg_left hr_pow88_le hmul0)
    exact le_trans hle (le_of_lt hconstR)
  have hrt12 : 0 ≤ (r t) ^ (12 : ℕ) := pow_nonneg hr0 _
  have hbound_first :
      (Cpsi : ℝ) * (2 * powGeomTerm (r t) 20 100) ≤ eps * (r t) ^ (12 : ℕ) := by
    dsimp [powGeomTerm]
    have : ((100 + 1 : ℝ) ^ (20 : ℕ)) = (101 : ℝ) ^ (20 : ℕ) := by norm_num
    rw [this]
    rw [hr_pow100]
    have hrew :
        (Cpsi : ℝ) * (2 * ((101 : ℝ) ^ (20 : ℕ) * ((r t) ^ (12 : ℕ) * (r t) ^ (88 : ℕ)))) =
          (r t) ^ (12 : ℕ) *
            ((2 : ℝ) * (Cpsi : ℝ) * (101 : ℝ) ^ (20 : ℕ) * (r t) ^ (88 : ℕ)) := by
      ring_nf
    rw [hrew]
    have := mul_le_mul_of_nonneg_left hconstR' hrt12
    simpa [mul_assoc, mul_left_comm, mul_comm] using! this
  have hfinal : Cpsi * (2 * powGeomTerm (r t) 20 100) ≤ eps * (r t) ^ (12 : ℕ) := by
    simpa [mul_assoc] using! hbound_first
  exact le_trans hmain1 hfinal
end

end SpherePacking.Dim24.AppendixA
