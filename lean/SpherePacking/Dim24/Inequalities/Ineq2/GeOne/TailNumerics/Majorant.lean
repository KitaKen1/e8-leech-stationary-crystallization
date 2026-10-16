-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.Constants
public import SpherePacking.Dim24.Inequalities.AppendixA.CoeffBoundConstants
public import SpherePacking.Dim24.Inequalities.AppendixA.GeometricTailBounds
public import Mathlib.Topology.Algebra.InfiniteSum.Order
import SpherePacking.Dim24.Inequalities.AppendixA.ExpBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.TailNumerics.ConstantsPi
import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.TailNumerics.GeomRatio

/-!
# Majorant tail bounds for `q`- and `r`-series

This file proves the numeric tail bounds used to dominate the `varphi_num` and `psiS_num` series
remainders by `(eps/2) * q(t)^6` and `(eps/2) * r(t)^12` when `1 ≤ t`.

## Main statements
* `varphi_majorant_tail_bound`
* `psi_majorant_tail_bound`
* `psi_majorant_tail_bound_cPi`
* `psi_majorant_tail_bound27`
* `psi_majorant_tail_bound_cPi27`
-/

open scoped BigOperators

noncomputable section

namespace SpherePacking.Dim24

open AppendixA

/-!
## Majorant tail bounds
-/

/-- Tail bound for the `varphi` majorant series in the `1 ≤ t` case. -/
public lemma varphi_majorant_tail_bound (t : ℝ) (ht : 1 ≤ t) :
    Cvarphi * (∑' m : ℕ, AppendixA.powGeomTerm (q t) 20 (50 + m)) ≤
      (eps / 2) * (q t) ^ (6 : ℕ) := by
  have hq0 : 0 ≤ q t := (Real.exp_pos _).le
  have hqle : q t ≤ (1 : ℝ) / 535 := by
    simpa [q, AppendixA.q, mul_assoc] using! (AppendixA.q_le_one_div_535_of_one_le (t := t) ht)
  have hρ_le_half : AppendixA.powGeomRatio (q t) 20 50 ≤ (1 : ℝ) / 2 :=
    powGeomRatio_q_le_half_of_q_le_one_div_535 (q' := q t) hqle
  have htail_le' :
      (∑' m : ℕ, AppendixA.powGeomTerm (q t) 20 (50 + m)) ≤
        2 * AppendixA.powGeomTerm (q t) 20 50 :=
    tsum_powGeomTerm_tail_le_two_mul (q := q t) (k := 20) (N := 50) hq0 hρ_le_half
  -- Now fold the constant `Cvarphi` into the bound.
  have hmain1 :
      Cvarphi * (∑' m : ℕ, AppendixA.powGeomTerm (q t) 20 (50 + m)) ≤
        Cvarphi * (2 * AppendixA.powGeomTerm (q t) 20 50) :=
    mul_le_mul_of_nonneg_left htail_le' (by norm_num [Cvarphi])
  have hpow50 : (q t) ^ (50 : ℕ) = (q t) ^ (6 : ℕ) * (q t) ^ (44 : ℕ) := by
    have : (6 + 44 : ℕ) = 50 := by decide
    simpa [this] using! (pow_add (q t) 6 44)
  have hpow44_le : (q t) ^ (44 : ℕ) ≤ ((1 : ℝ) / 535) ^ (44 : ℕ) :=
    pow_le_pow_left₀ hq0 hqle _
  have hconstR :
      (2 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 535) ^ (44 : ℕ) < eps / 2 := by
    have h' :
        ((2 : ℚ) * (513200655360 : ℚ) * (51 : ℚ) ^ (20 : ℕ) * ((1 : ℚ) / 535) ^ (44 : ℕ) : ℝ) <
          (((10 : ℚ) ^ (-50 : ℤ)) / 2 : ℝ) := by
      exact_mod_cast const_varphi_tail_lt_half_eps
    have h'' :
        (2 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 535) ^ (44 : ℕ) <
          (10 : ℝ) ^ (-50 : ℤ) / 2 := by
      simpa [Cvarphi] using! h'
    simpa [eps] using! h''
  have hconstR' :
      (2 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) * (q t) ^ (44 : ℕ) ≤ eps / 2 := by
    have hle :
        (2 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) * (q t) ^ (44 : ℕ) ≤
          (2 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 535) ^ (44 : ℕ) := by
      have hC : 0 ≤ (Cvarphi : ℝ) := by norm_num [Cvarphi]
      have h51 : 0 ≤ (51 : ℝ) ^ (20 : ℕ) := by positivity
      have h2 : 0 ≤ (2 : ℝ) := by norm_num
      have : 0 ≤ (2 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) := by
        have : 0 ≤ (2 : ℝ) * (Cvarphi : ℝ) := mul_nonneg h2 hC
        simpa [mul_assoc] using! (mul_nonneg this h51)
      exact mul_le_mul_of_nonneg_left hpow44_le (by simpa [mul_assoc] using! this)
    exact le_trans hle (le_of_lt hconstR)
  have hqt6 : 0 ≤ (q t) ^ (6 : ℕ) := pow_nonneg hq0 _
  have hbound_first :
      (Cvarphi : ℝ) * (2 * AppendixA.powGeomTerm (q t) 20 50) ≤ (eps / 2) * (q t) ^ (6 : ℕ) := by
    dsimp [AppendixA.powGeomTerm]
    have : ((50 + 1 : ℝ) ^ (20 : ℕ)) = (51 : ℝ) ^ (20 : ℕ) := by norm_num
    rw [this]
    -- `q^50 = q^6*q^44`.
    rw [hpow50]
    -- Rearrange.
    have :
        (Cvarphi : ℝ) * (2 * ((51 : ℝ) ^ (20 : ℕ) * ((q t) ^ (6 : ℕ) * (q t) ^ (44 : ℕ)))) =
          ((q t) ^ (6 : ℕ)) *
            ((2 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) * (q t) ^ (44 : ℕ)) := by
      ring_nf
    rw [this]
    have := mul_le_mul_of_nonneg_left hconstR' hqt6
    simpa [mul_assoc, mul_left_comm, mul_comm] using! this
  exact hmain1.trans (by simpa [mul_assoc] using! hbound_first)

/-- Tail bound for the `psiS_num` majorant series (exponent `20`) in the `1 ≤ t` case. -/
public lemma psi_majorant_tail_bound (t : ℝ) (ht : 1 ≤ t) :
    Cpsi * (∑' m : ℕ, AppendixA.powGeomTerm (r t) 20 (100 + m)) ≤ (eps / 2) * (r t) ^ (12 : ℕ) := by
  have hr0 : 0 ≤ r t := (Real.exp_pos _).le
  have hrle : r t ≤ (1 : ℝ) / 23 := by
    simpa [r] using! (AppendixA.r_le_one_div_23 (t := t) ht)
  have hρ_le_half : AppendixA.powGeomRatio (r t) 20 100 ≤ (1 : ℝ) / 2 :=
    powGeomRatio_r_le_half_of_r_le_one_div_23 (r' := r t) hrle
  have htail_le' :
      (∑' m : ℕ, AppendixA.powGeomTerm (r t) 20 (100 + m)) ≤
        2 * AppendixA.powGeomTerm (r t) 20 100 :=
    tsum_powGeomTerm_tail_le_two_mul (q := r t) (k := 20) (N := 100) hr0 hρ_le_half
  have hmain1 :
      Cpsi * (∑' m : ℕ, AppendixA.powGeomTerm (r t) 20 (100 + m)) ≤
        Cpsi * (2 * AppendixA.powGeomTerm (r t) 20 100) :=
    mul_le_mul_of_nonneg_left htail_le' (by norm_num [Cpsi])
  have hr_pow100 : (r t) ^ (100 : ℕ) = (r t) ^ (12 : ℕ) * (r t) ^ (88 : ℕ) := by
    have : (12 + 88 : ℕ) = 100 := by decide
    simpa [this] using! (pow_add (r t) 12 88)
  have hr_pow88_le : (r t) ^ (88 : ℕ) ≤ ((1 : ℝ) / 23) ^ (88 : ℕ) :=
    pow_le_pow_left₀ hr0 hrle _
  have hconstR :
      (2 : ℝ) * (Cpsi : ℝ) * (101 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) < eps / 2 := by
    have h' :
        ((2 : ℚ) * ((44 : ℚ) * (16 : ℚ) * (24 : ℚ) ^ (7 : ℕ)) * (101 : ℚ) ^ (20 : ℕ) *
              ((1 : ℚ) / 23) ^ (88 : ℕ) : ℝ) <
          (((10 : ℚ) ^ (-50 : ℤ)) / 2 : ℝ) := by
      exact_mod_cast const_psi_tail_lt_half_eps
    have h'' :
        (2 : ℝ) * (Cpsi : ℝ) * (101 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) <
          (10 : ℝ) ^ (-50 : ℤ) / 2 := by
      simpa [Cpsi] using! h'
    simpa [eps] using! h''
  have hconstR' :
      (2 : ℝ) * (Cpsi : ℝ) * (101 : ℝ) ^ (20 : ℕ) * (r t) ^ (88 : ℕ) ≤ eps / 2 := by
    have hle :
        (2 : ℝ) * (Cpsi : ℝ) * (101 : ℝ) ^ (20 : ℕ) * (r t) ^ (88 : ℕ) ≤
          (2 : ℝ) * (Cpsi : ℝ) * (101 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) := by
      have : 0 ≤ (2 : ℝ) * (Cpsi : ℝ) * (101 : ℝ) ^ (20 : ℕ) := by
        have h2 : 0 ≤ (2 : ℝ) := by norm_num
        have hC : 0 ≤ (Cpsi : ℝ) := by norm_num [Cpsi]
        grind only
      exact mul_le_mul_of_nonneg_left hr_pow88_le (by simpa [mul_assoc] using! this)
    exact le_trans hle (le_of_lt hconstR)
  have hrt12 : 0 ≤ (r t) ^ (12 : ℕ) := pow_nonneg hr0 _
  have hbound_first :
      (Cpsi : ℝ) * (2 * AppendixA.powGeomTerm (r t) 20 100) ≤ (eps / 2) * (r t) ^ (12 : ℕ) := by
    dsimp [AppendixA.powGeomTerm]
    have : ((100 + 1 : ℝ) ^ (20 : ℕ)) = (101 : ℝ) ^ (20 : ℕ) := by norm_num
    rw [this]
    rw [hr_pow100]
    have :
        (Cpsi : ℝ) * (2 * ((101 : ℝ) ^ (20 : ℕ) * ((r t) ^ (12 : ℕ) * (r t) ^ (88 : ℕ)))) =
          ((r t) ^ (12 : ℕ)) *
            ((2 : ℝ) * (Cpsi : ℝ) * (101 : ℝ) ^ (20 : ℕ) * (r t) ^ (88 : ℕ)) := by
      ring_nf
    rw [this]
    have := mul_le_mul_of_nonneg_left hconstR' hrt12
    simpa [mul_assoc, mul_left_comm, mul_comm] using! this
  exact hmain1.trans (by simpa [mul_assoc] using! hbound_first)

/--
Tail bound for the `psiS_num` majorant series, scaled by the constant `432/π^2 * 16 * 24^7`.

This is the scalar that appears in the numerator bound for `ineq2` in the `1 ≤ t` case.
-/
public lemma psi_majorant_tail_bound_cPi (t : ℝ) (ht : 1 ≤ t) :
    ((432 / (Real.pi ^ 2) : ℝ) * (16 : ℝ) * (24 : ℝ) ^ (7 : ℕ)) *
        (∑' m : ℕ, AppendixA.powGeomTerm (r t) 20 (100 + m))
      ≤ (eps / 2) * (r t) ^ (12 : ℕ) := by
  have hsum0 :
      0 ≤ (∑' m : ℕ, AppendixA.powGeomTerm (r t) 20 (100 + m)) := by
      have hr0 : 0 ≤ r t := (Real.exp_pos _).le
      have hterm0 : ∀ m : ℕ, 0 ≤ AppendixA.powGeomTerm (r t) 20 (100 + m) :=
        fun m => AppendixA.powGeomTerm_nonneg (q := r t) (k := 20) (n := 100 + m) hr0
      exact tsum_nonneg hterm0
  have hconst : ((432 / (Real.pi ^ 2) : ℝ) * (16 : ℝ) * (24 : ℝ) ^ (7 : ℕ)) ≤ Cpsi := by
    have hC : (432 / (Real.pi ^ 2) : ℝ) ≤ 44 := cPi_le_44
    have h0 : 0 ≤ (16 : ℝ) * (24 : ℝ) ^ (7 : ℕ) := by positivity
    have := mul_le_mul_of_nonneg_right hC h0
    -- Reassociate the product.
    simpa [Cpsi, mul_assoc, mul_left_comm, mul_comm] using! this
  have hscale :
      ((432 / (Real.pi ^ 2) : ℝ) * (16 : ℝ) * (24 : ℝ) ^ (7 : ℕ)) *
          (∑' m : ℕ, AppendixA.powGeomTerm (r t) 20 (100 + m))
        ≤ Cpsi * (∑' m : ℕ, AppendixA.powGeomTerm (r t) 20 (100 + m)) :=
    mul_le_mul_of_nonneg_right hconst hsum0
  exact le_trans hscale (psi_majorant_tail_bound (t := t) ht)

/-- Tail bound for the `psiS_num` majorant series with exponent `27` (a coarse "backup" bound). -/
public lemma psi_majorant_tail_bound27 (t : ℝ) (ht : 1 ≤ t) :
    ((44 : ℝ) * (16 : ℝ) ^ (8 : ℕ)) *
          (∑' m : ℕ, AppendixA.powGeomTerm (r t) 27 (100 + m))
      ≤ (eps / 2) * (r t) ^ (12 : ℕ) := by
  have hr0 : 0 ≤ r t := (Real.exp_pos _).le
  have hrle : r t ≤ (1 : ℝ) / 23 := by
    simpa [r] using! (AppendixA.r_le_one_div_23 (t := t) ht)
  have hρ_le_half : AppendixA.powGeomRatio (r t) 27 100 ≤ (1 : ℝ) / 2 :=
    powGeomRatio_r_le_half_of_r_le_one_div_23_27 (r' := r t) hrle
  have htail_le' :
      (∑' m : ℕ, AppendixA.powGeomTerm (r t) 27 (100 + m)) ≤
        2 * AppendixA.powGeomTerm (r t) 27 100 :=
    tsum_powGeomTerm_tail_le_two_mul (q := r t) (k := 27) (N := 100) hr0 hρ_le_half
  have hmain1 :
      ((44 : ℝ) * (16 : ℝ) ^ (8 : ℕ)) * (∑' m : ℕ, AppendixA.powGeomTerm (r t) 27 (100 + m)) ≤
        ((44 : ℝ) * (16 : ℝ) ^ (8 : ℕ)) * (2 * AppendixA.powGeomTerm (r t) 27 100) :=
    mul_le_mul_of_nonneg_left htail_le' (by positivity)
  have hr_pow100 : (r t) ^ (100 : ℕ) = (r t) ^ (12 : ℕ) * (r t) ^ (88 : ℕ) := by
    have : (12 + 88 : ℕ) = 100 := by decide
    simpa [this] using! (pow_add (r t) 12 88)
  have hr_pow88_le : (r t) ^ (88 : ℕ) ≤ ((1 : ℝ) / 23) ^ (88 : ℕ) :=
    pow_le_pow_left₀ hr0 hrle _
  have hconstR :
      (2 : ℝ) * ((44 : ℝ) * (16 : ℝ) ^ (8 : ℕ)) * (101 : ℝ) ^ (27 : ℕ) *
          ((1 : ℝ) / 23) ^ (88 : ℕ) < eps / 2 := by
    have h' :
        ((2 : ℚ) * ((44 : ℚ) * (16 : ℚ) ^ (8 : ℕ)) * (101 : ℚ) ^ (27 : ℕ) *
              ((1 : ℚ) / 23) ^ (88 : ℕ) : ℝ) <
          (((10 : ℚ) ^ (-50 : ℤ)) / 2 : ℝ) := by
      exact_mod_cast const_psi27_tail_lt_half_eps
    simpa [eps] using! h'
  have hconstR' :
      (2 : ℝ) * ((44 : ℝ) * (16 : ℝ) ^ (8 : ℕ)) * (101 : ℝ) ^ (27 : ℕ) * (r t) ^ (88 : ℕ) ≤
        eps / 2 := by
    have hle :
        (2 : ℝ) * ((44 : ℝ) * (16 : ℝ) ^ (8 : ℕ)) * (101 : ℝ) ^ (27 : ℕ) * (r t) ^ (88 : ℕ) ≤
          (2 : ℝ) * ((44 : ℝ) * (16 : ℝ) ^ (8 : ℕ)) * (101 : ℝ) ^ (27 : ℕ) *
            ((1 : ℝ) / 23) ^ (88 : ℕ) := by
      have hnonneg :
          0 ≤ (2 : ℝ) * ((44 : ℝ) * (16 : ℝ) ^ (8 : ℕ)) * (101 : ℝ) ^ (27 : ℕ) := by positivity
      exact mul_le_mul_of_nonneg_left hr_pow88_le hnonneg
    exact le_trans hle (le_of_lt hconstR)
  have hrt12 : 0 ≤ (r t) ^ (12 : ℕ) := pow_nonneg hr0 _
  have hbound_first :
      ((44 : ℝ) * (16 : ℝ) ^ (8 : ℕ)) * (2 * AppendixA.powGeomTerm (r t) 27 100) ≤
        (eps / 2) * (r t) ^ (12 : ℕ) := by
    dsimp [AppendixA.powGeomTerm]
    have : ((100 + 1 : ℝ) ^ (27 : ℕ)) = (101 : ℝ) ^ (27 : ℕ) := by norm_num
    rw [this]
    rw [hr_pow100]
    have :
        ((44 : ℝ) * (16 : ℝ) ^ (8 : ℕ)) *
              (2 * ((101 : ℝ) ^ (27 : ℕ) * ((r t) ^ (12 : ℕ) * (r t) ^ (88 : ℕ)))) =
          ((r t) ^ (12 : ℕ)) *
            ((2 : ℝ) * ((44 : ℝ) * (16 : ℝ) ^ (8 : ℕ)) * (101 : ℝ) ^ (27 : ℕ) *
                (r t) ^ (88 : ℕ)) := by
      ring_nf
    rw [this]
    have := mul_le_mul_of_nonneg_left hconstR' hrt12
    simpa [mul_assoc, mul_left_comm, mul_comm] using! this
  exact hmain1.trans (by simpa [mul_assoc] using! hbound_first)

/-- Tail bound for the `psiS_num` majorant series with exponent `27`, scaled by `432/π^2`. -/
public lemma psi_majorant_tail_bound_cPi27 (t : ℝ) (ht : 1 ≤ t) :
    ((432 / (Real.pi ^ 2) : ℝ) * (16 : ℝ) ^ (8 : ℕ)) *
        (∑' m : ℕ, AppendixA.powGeomTerm (r t) 27 (100 + m))
      ≤ (eps / 2) * (r t) ^ (12 : ℕ) := by
  have hsum0 :
      0 ≤ (∑' m : ℕ, AppendixA.powGeomTerm (r t) 27 (100 + m)) := by
    have hr0 : 0 ≤ r t := (Real.exp_pos _).le
    have hterm0 : ∀ m : ℕ, 0 ≤ AppendixA.powGeomTerm (r t) 27 (100 + m) :=
      fun m => AppendixA.powGeomTerm_nonneg (q := r t) (k := 27) (n := 100 + m) hr0
    exact tsum_nonneg hterm0
  have hconst :
      ((432 / (Real.pi ^ 2) : ℝ) * (16 : ℝ) ^ (8 : ℕ)) ≤ (44 : ℝ) * (16 : ℝ) ^ (8 : ℕ) := by
    have hC : (432 / (Real.pi ^ 2) : ℝ) ≤ 44 := cPi_le_44
    linarith
  have hscale :
      ((432 / (Real.pi ^ 2) : ℝ) * (16 : ℝ) ^ (8 : ℕ)) *
          (∑' m : ℕ, AppendixA.powGeomTerm (r t) 27 (100 + m)) ≤
        ((44 : ℝ) * (16 : ℝ) ^ (8 : ℕ)) *
          (∑' m : ℕ, AppendixA.powGeomTerm (r t) 27 (100 + m)) :=
    mul_le_mul_of_nonneg_right hconst hsum0
  exact le_trans hscale (psi_majorant_tail_bound27 (t := t) ht)


end SpherePacking.Dim24
