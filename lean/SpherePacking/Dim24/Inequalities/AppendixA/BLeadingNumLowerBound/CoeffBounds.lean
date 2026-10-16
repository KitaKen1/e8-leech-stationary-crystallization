-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.Constants
public import SpherePacking.Dim24.Inequalities.AppendixA.CoeffBoundConstants
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.QSeriesHelpers
import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesTailBounds
import SpherePacking.Dim24.Inequalities.AppendixA.PolyOfCoeffsLemmas
import SpherePacking.Dim24.Inequalities.AppendixA.ExpBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.GeometricTailBounds
import Mathlib.Topology.Algebra.InfiniteSum.Order
public import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.Basic
public import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.CoeffsBleading
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import SpherePacking.Dim24.Inequalities.AppendixA.EisensteinSeriesBounds
import SpherePacking.Dim24.Inequalities.AppendixA.QSeries

/-!
### Coefficient bounds for Eisenstein numerators

These are the analytic inputs needed for tail estimates:
we bound each relevant coefficient function by `C * (n+1)^20`.

## Main statements
* `abs_coeffVarphiNum_le`
* `Bleading_trunc_eval₂_eq_sum_range`
* `t_sq_mul_q_pow_le`, `t_mul_q_pow_le`
-/

noncomputable section

namespace SpherePacking.Dim24.AppendixA

/-!
### Geometric tail compression

For the final analytic bounds we repeatedly use the pattern:
if `powGeomRatio q k N ≤ 1/2`, then the tail `∑' m, powGeomTerm q k (N+m)` is bounded by
`2 * powGeomTerm q k N`.
-/

private lemma abs_add4_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 : |a + b + c + d| ≤ |a + b| + |c + d| := by
    simpa [add_assoc] using! abs_add_le (a + b) (c + d)
  have h2 : |a + b| + |c + d| ≤ (|a| + |b|) + (|c| + |d|) :=
    add_le_add (abs_add_le a b) (abs_add_le c d)
  have h3 : (|a| + |b|) + (|c| + |d|) = |a| + |b| + |c| + |d| := by
    ac_rfl
  exact h1.trans (h2.trans_eq h3)

private lemma abs_conv_lincomb_coeffE2Sq_le (n : ℕ) :
    |(conv (fun m => (-49 : ℚ) * coeffE4Cube m + (25 : ℚ) * coeffE6Sq m) coeffE2Sq n : ℝ)| ≤
      (Cphi2Core * (24 * 24 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) := by
  -- `ka = 14` for the linear combination, `kb = 5` for `coeffE2Sq`.
  have h :=
    abs_conv_le
      (a := fun m => (-49 : ℚ) * coeffE4Cube m + (25 : ℚ) * coeffE6Sq m)
      (b := coeffE2Sq) (Ca := Cphi2Core) (Cb := (24 * 24 : ℝ)) (ka := 14) (kb := 5)
      (fun m => by
        simpa [Cphi2Core_eq] using! (abs_lincomb_E4Cube_E6Sq_le (n := m))
      )
      (fun m => by
        simpa using! (abs_coeffE2Sq_le (n := m)))
      n
  -- `abs_conv_le` produces exponent `14 + 5 + 1 = 20` and constant `Cphi2Core * (24*24)`.
  simpa [mul_assoc, add_assoc, add_left_comm, add_comm] using! h

/-- Polynomial growth bound for `coeffVarphiNum` (used to bound the `q`-series tail). -/
public lemma abs_coeffVarphiNum_le (n : ℕ) :
    |(coeffVarphiNum n : ℝ)| ≤ Cvarphi * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) := by
  have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hpow18 :
      (((n + 1 : ℕ) : ℝ) ^ (18 : ℕ)) ≤ (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) :=
    pow_le_pow_right₀ hn1 (by decide : (18 : ℕ) ≤ 20)
  have hpow19 :
      (((n + 1 : ℕ) : ℝ) ^ (19 : ℕ)) ≤ (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) :=
    pow_le_pow_right₀ hn1 (by decide : (19 : ℕ) ≤ 20)
  -- Term A: `25 * coeffE4Fourth`.
  have hE4Fourth :
      |(coeffE4Fourth n : ℝ)| ≤
        ((240 * 240 : ℝ) * (240 * 240 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (19 : ℕ)) := by
    -- `coeffE4Fourth = conv coeffE4Sq coeffE4Sq`, with `coeffE4Sq` bounded by exponent `9`.
    have hSq := abs_coeffE4Sq_le (n := n)
    have h :=
      abs_conv_le (a := coeffE4Sq) (b := coeffE4Sq) (Ca := (240 * 240 : ℝ)) (Cb := (240 * 240 : ℝ))
        (ka := 9) (kb := 9) abs_coeffE4Sq_le abs_coeffE4Sq_le n
    -- `9 + 9 + 1 = 19`.
    simpa [coeffE4Fourth, mul_assoc, add_assoc, add_left_comm, add_comm] using! h
  have hA :
      |(((25 : ℚ) * coeffE4Fourth n : ℚ) : ℝ)| ≤
        (25 : ℝ) * ((240 * 240 : ℝ) * (240 * 240 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) := by
    have hE4Fourth' :
        |(coeffE4Fourth n : ℝ)| ≤
          ((240 * 240 : ℝ) * (240 * 240 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) :=
      hE4Fourth.trans (mul_le_mul_of_nonneg_left hpow19 (by positivity))
    calc
      |(((25 : ℚ) * coeffE4Fourth n : ℚ) : ℝ)|
          = (25 : ℝ) * |(coeffE4Fourth n : ℝ)| := by simp [Rat.cast_mul, abs_mul]
      _ ≤ (25 : ℝ) * (((240 * 240 : ℝ) * (240 * 240 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ))) := by
            exact mul_le_mul_of_nonneg_left hE4Fourth' (by positivity)
      _ = (25 : ℝ) * ((240 * 240 : ℝ) * (240 * 240 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) := by ring
  -- Term B: `(-49) * conv coeffE6Sq coeffE4`.
  have hBcore :
      |(conv coeffE6Sq coeffE4 n : ℝ)| ≤
        ((504 * 504 : ℝ) * (240 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (18 : ℕ)) := by
    simpa using! abs_conv_coeffE6Sq_coeffE4_le (n := n)
  have hB :
      |(((-49 : ℚ) * conv coeffE6Sq coeffE4 n : ℚ) : ℝ)| ≤
        (49 : ℝ) * ((504 * 504 : ℝ) * (240 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) := by
    have hBcore' :
        |(conv coeffE6Sq coeffE4 n : ℝ)| ≤
          ((504 * 504 : ℝ) * (240 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) :=
      hBcore.trans (mul_le_mul_of_nonneg_left hpow18 (by positivity))
    calc
      |(((-49 : ℚ) * conv coeffE6Sq coeffE4 n : ℚ) : ℝ)|
          = (49 : ℝ) * |(conv coeffE6Sq coeffE4 n : ℝ)| := by
              simp [Rat.cast_mul, Rat.cast_neg, abs_mul]
      _ ≤ (49 : ℝ) * (((504 * 504 : ℝ) * (240 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ))) := by
            exact mul_le_mul_of_nonneg_left hBcore' (by positivity)
      _ = (49 : ℝ) * ((504 * 504 : ℝ) * (240 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) := by ring
  -- Term C: `48 * conv (conv coeffE6 coeffE4Sq) coeffE2`.
  have hCcore :
      |(conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℝ)| ≤
        ((504 : ℝ) * (240 * 240 : ℝ) * (24 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (19 : ℕ)) := by
    -- Reuse the already packaged bound.
    simpa using! abs_conv_coeffE6_coeffE4Sq_coeffE2_le (n := n)
  have hC :
      |(((48 : ℚ) * conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℚ) : ℝ)| ≤
        (48 : ℝ) * ((504 : ℝ) * (240 * 240 : ℝ) * (24 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) := by
    have hCcore' :
        |(conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℝ)| ≤
          ((504 : ℝ) * (240 * 240 : ℝ) * (24 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) :=
      hCcore.trans (mul_le_mul_of_nonneg_left hpow19 (by positivity))
    calc
      |(((48 : ℚ) * conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℚ) : ℝ)|
          = (48 : ℝ) * |(conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℝ)| := by
              simp [Rat.cast_mul, abs_mul]
      _ ≤ (48 : ℝ) *
            (((504 : ℝ) * (240 * 240 : ℝ) * (24 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ))) := by
            exact mul_le_mul_of_nonneg_left hCcore' (by positivity)
      _ =
          (48 : ℝ) * ((504 : ℝ) * (240 * 240 : ℝ) * (24 : ℝ)) *
            (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) := by
          ring
  -- Term D: convolution of the `(-49*E4^3 + 25*E6^2)` linear combination with `E2^2`.
  have hD :
      |(conv (fun m => (-49 : ℚ) * coeffE4Cube m + (25 : ℚ) * coeffE6Sq m) coeffE2Sq n : ℝ)| ≤
        (Cphi2Core * (24 * 24 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) :=
    abs_conv_lincomb_coeffE2Sq_le (n := n)
  -- Combine by triangle inequality and fold constants into `Cvarphi`.
  have hsum :
      |(coeffVarphiNum n : ℝ)| ≤
        ((25 : ℝ) * ((240 * 240 : ℝ) * (240 * 240 : ℝ)) +
            (49 : ℝ) * ((504 * 504 : ℝ) * (240 : ℝ)) +
            (48 : ℝ) * ((504 : ℝ) * (240 * 240 : ℝ) * (24 : ℝ)) +
            (Cphi2Core * (24 * 24 : ℝ))) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) := by
    -- Expand `coeffVarphiNum` and apply `abs_add_le` repeatedly.
    have hrepr :
        (coeffVarphiNum n : ℝ) =
          (((25 : ℚ) * coeffE4Fourth n : ℚ) : ℝ) +
            (((-49 : ℚ) * conv coeffE6Sq coeffE4 n : ℚ) : ℝ) +
            (((48 : ℚ) * conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℚ) : ℝ) +
              ((conv (fun m => (-49 : ℚ) * coeffE4Cube m + (25 : ℚ) * coeffE6Sq m) coeffE2Sq n :
                ℚ) : ℝ) := by
        simp [coeffVarphiNum, sub_eq_add_neg]
    -- Apply triangle inequality.
    -- Put everything in the form `abs (a+b+c+d) ≤ abs a + abs b + abs c + abs d`.
    have htri :
        |(coeffVarphiNum n : ℝ)| ≤
          |(((25 : ℚ) * coeffE4Fourth n : ℚ) : ℝ)| +
            |(((-49 : ℚ) * conv coeffE6Sq coeffE4 n : ℚ) : ℝ)| +
            |(((48 : ℚ) * conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℚ) : ℝ)| +
              |((conv (fun m => (-49 : ℚ) * coeffE4Cube m + (25 : ℚ) * coeffE6Sq m) coeffE2Sq n :
                ℚ) : ℝ)| := by
      -- Triangle inequality for a 4-term sum.
      set a : ℝ := (((25 : ℚ) * coeffE4Fourth n : ℚ) : ℝ)
      set b : ℝ := (((-49 : ℚ) * conv coeffE6Sq coeffE4 n : ℚ) : ℝ)
      set c : ℝ := (((48 : ℚ) * conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℚ) : ℝ)
      set d : ℝ :=
        ((conv (fun m => (-49 : ℚ) * coeffE4Cube m + (25 : ℚ) * coeffE6Sq m) coeffE2Sq n : ℚ) :
          ℝ)
      simpa [hrepr, a, b, c, d, add_assoc] using! (abs_add4_le a b c d)
    -- Now majorize each absolute value by its bound and factor out `(n+1)^20`.
    have hlin :
        |(((25 : ℚ) * coeffE4Fourth n : ℚ) : ℝ)| +
            |(((-49 : ℚ) * conv coeffE6Sq coeffE4 n : ℚ) : ℝ)| +
            |(((48 : ℚ) * conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℚ) : ℝ)| +
              |((conv (fun m => (-49 : ℚ) * coeffE4Cube m + (25 : ℚ) * coeffE6Sq m) coeffE2Sq n :
                ℚ) : ℝ)|
          ≤
            (((25 : ℝ) * ((240 * 240 : ℝ) * (240 * 240 : ℝ))) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ))) +
            (((49 : ℝ) * ((504 * 504 : ℝ) * (240 : ℝ))) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ))) +
            (((48 : ℝ) * ((504 : ℝ) * (240 * 240 : ℝ) * (24 : ℝ))) *
              (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ))) +
            ((Cphi2Core * (24 * 24 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ))) :=
      add_le_add (add_le_add (add_le_add hA hB) hC) hD
    have hfactor :
        ((25 : ℝ) * ((240 * 240 : ℝ) * (240 * 240 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ))) +
            ((49 : ℝ) * ((504 * 504 : ℝ) * (240 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ))) +
            ((48 : ℝ) * ((504 : ℝ) * (240 * 240 : ℝ) * (24 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ))) +
            ((Cphi2Core * (24 * 24 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ))) =
          ((25 : ℝ) * ((240 * 240 : ℝ) * (240 * 240 : ℝ)) +
              (49 : ℝ) * ((504 * 504 : ℝ) * (240 : ℝ)) +
              (48 : ℝ) * ((504 : ℝ) * (240 * 240 : ℝ) * (24 : ℝ)) +
              (Cphi2Core * (24 * 24 : ℝ))) * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ)) := by
      ring
    exact (htri.trans (le_trans hlin (le_of_eq hfactor)))
  -- Finally, rewrite the constant as `Cvarphi`.
  have hCvarphi :
      (25 : ℝ) * ((240 * 240 : ℝ) * (240 * 240 : ℝ)) +
          (49 : ℝ) * ((504 * 504 : ℝ) * (240 : ℝ)) +
          (48 : ℝ) * ((504 : ℝ) * (240 * 240 : ℝ) * (24 : ℝ)) +
          (Cphi2Core * (24 * 24 : ℝ)) = Cvarphi := by
    -- This is exactly the constant from `appendix.txt`.
    -- `Cphi2Core` was defined to match the `(-49*E4^3+25*E6^2)` bound.
    -- The remaining arithmetic is closed.
    -- The simplifier needs the explicit value of `Cphi2Core`.
    -- `norm_num` discharges the resulting goal.
    norm_num [Cvarphi, Cphi2Core]
  simpa [hCvarphi] using! hsum

private lemma const_varphi_tail_lt_eps :
    ((2 : ℚ) * (513200655360 : ℚ) * (51 : ℚ) ^ (20 : ℕ) * ((1 : ℚ) / 535) ^ (44 : ℕ)) <
      (10 : ℚ) ^ (-50 : ℤ) := by
  -- Closed rational inequality; `norm_num` clears denominators.
  set_option maxRecDepth 6000 in
  norm_num

private lemma varphi_majorant_tail_bound (t : ℝ) (ht : 1 ≤ t) :
    Cvarphi * (∑' m : ℕ, powGeomTerm (q t) 20 (50 + m)) ≤ eps * (q t) ^ (6 : ℕ) := by
  have hq0 : 0 ≤ q t := (Real.exp_pos _).le
  have hqle : q t ≤ (1 : ℝ) / 535 := q_le_one_div_535 (t := t) ht
  have hρ_le_half : powGeomRatio (q t) 20 50 ≤ (1 : ℝ) / 2 :=
    powGeomRatio_q_le_half_of_q_le_one_div_535 (q' := q t) hqle
  have htail_le' :
      (∑' m : ℕ, powGeomTerm (q t) 20 (50 + m)) ≤
        2 * powGeomTerm (q t) 20 50 := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using!
      (tsum_powGeomTerm_tail_le_two_mul (q := q t) (k := 20) (N := 50) hq0 hρ_le_half)
  have hmain1 :
      Cvarphi * (∑' m : ℕ, powGeomTerm (q t) 20 (50 + m)) ≤
        Cvarphi * (2 * powGeomTerm (q t) 20 50) :=
    mul_le_mul_of_nonneg_left htail_le' (by norm_num [Cvarphi])
  have hpow50 : (q t) ^ (50 : ℕ) = (q t) ^ (6 : ℕ) * (q t) ^ (44 : ℕ) := by
    simpa [pow_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using! (pow_add (q t) 6 44)
  have hpow44_le : (q t) ^ (44 : ℕ) ≤ ((1 : ℝ) / 535) ^ (44 : ℕ) :=
    pow_le_pow_left₀ hq0 hqle _
  have hconstR :
      (2 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 535) ^ (44 : ℕ) < eps := by
    have h' :
        ((2 : ℚ) * (513200655360 : ℚ) * (51 : ℚ) ^ (20 : ℕ) * ((1 : ℚ) / 535) ^ (44 : ℕ) : ℝ) <
          ((10 : ℚ) ^ (-50 : ℤ) : ℝ) := by
      exact_mod_cast const_varphi_tail_lt_eps
    have h'' :
        (2 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 535) ^ (44 : ℕ) <
          (10 : ℝ) ^ (-50 : ℤ) := by
      simpa [Cvarphi] using! h'
    simpa [eps] using! h''
  have hconstR' :
      (2 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) * (q t) ^ (44 : ℕ) ≤ eps := by
    have hle :
        (2 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) * (q t) ^ (44 : ℕ) ≤
          (2 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 535) ^ (44 : ℕ) :=
      by
        have hmul0 : 0 ≤ (2 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) := by
          dsimp [Cvarphi]
          positivity
        simpa [mul_assoc, mul_left_comm, mul_comm] using! (mul_le_mul_of_nonneg_left hpow44_le hmul0)
    exact le_trans hle (le_of_lt hconstR)
  have hqt6 : 0 ≤ (q t) ^ (6 : ℕ) := pow_nonneg hq0 _
  have hbound_first : Cvarphi * (2 * powGeomTerm (q t) 20 50) ≤ eps * (q t) ^ (6 : ℕ) := by
    dsimp [powGeomTerm]
    have : ((50 + 1 : ℝ) ^ (20 : ℕ)) = (51 : ℝ) ^ (20 : ℕ) := by norm_num
    rw [this, hpow50]
    have :
        (Cvarphi : ℝ) * (2 * ((51 : ℝ) ^ (20 : ℕ) * ((q t) ^ (6 : ℕ) * (q t) ^ (44 : ℕ)))) =
          ((q t) ^ (6 : ℕ)) *
            ((2 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) * (q t) ^ (44 : ℕ)) := by
      ring_nf
    rw [this]
    have := mul_le_mul_of_nonneg_left hconstR' hqt6
    simpa [mul_assoc, mul_left_comm, mul_comm] using! this
  exact le_trans hmain1 hbound_first

private lemma varphi_majorant_tail_bound_exp (t : ℝ) (ht : 1 ≤ t) :
    Cvarphi * (∑' m : ℕ, powGeomTerm (q t) 20 (50 + m)) ≤
      (10 : ℝ) ^ (-50 : ℤ) * (Real.exp (-Real.pi * t)) ^ (12 : ℕ) := by
  have h' :
      Cvarphi * (∑' m : ℕ, powGeomTerm (q t) 20 (50 + m)) ≤ eps * (r t) ^ (12 : ℕ) := by
    simpa [q_eq_r_sq, (pow_mul (r t) 2 6).symm, mul_assoc, mul_left_comm, mul_comm] using!
      (varphi_majorant_tail_bound (t := t) ht)
  simpa [eps, r, mul_assoc, mul_left_comm, mul_comm] using! h'

private lemma q_pow_eq_r_pow (t : ℝ) (n : ℕ) : (q t) ^ n = (r t) ^ (2 * n) := by
  simpa [q_eq_r_sq] using! (pow_mul (r t) 2 n).symm

/-- Expand `Bleading_trunc.eval₂` as an explicit finite coefficient sum. -/
public lemma Bleading_trunc_eval₂_eq_sum_range (x : ℝ) :
    (Bleading_trunc.eval₂ (algebraMap ℚ ℝ) x) =
      ∑ n ∈ Finset.range Bleading_trunc_coeffs.length,
        (algebraMap ℚ ℝ) (Bleading_trunc_coeffs.getD n 0) * x ^ n := by
  simpa [Bleading_trunc] using!
    eval₂_polyOfCoeffs_eq_sum_range_getD (l := Bleading_trunc_coeffs) (x := x)

private lemma t_le_one_div_23_div_r (t : ℝ) (ht : 1 ≤ t) : t ≤ ((1 / 23 : ℝ) / r t) := by
  have hrpos : 0 < r t := Real.exp_pos _
  have htr : t * r t ≤ (1 / 23 : ℝ) := AppendixA.t_mul_r_le_one_div_23 (t := t) ht
  exact (le_div_iff₀ hrpos).2 (by simpa [div_eq_mul_inv, mul_assoc] using! htr)

/--
For `t ≥ 1` and `n ≥ 1`, bound `t^2 * q(t)^n` by a shifted power of `r(t)`.

This is a convenient way to exploit the inequality `t * r(t) ≤ 1/23`.
-/
public lemma t_sq_mul_q_pow_le (t : ℝ) (ht : 1 ≤ t) (n : ℕ) (hn : 1 ≤ n) :
    t ^ (2 : ℕ) * (q t) ^ n ≤ ((1 / 23 : ℝ) ^ (2 : ℕ)) * (r t) ^ (2 * n - 2) := by
  have hr0 : 0 ≤ r t := (Real.exp_pos _).le
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have htr : t * r t ≤ (1 / 23 : ℝ) := AppendixA.t_mul_r_le_one_div_23 (t := t) ht
  have htr0 : 0 ≤ t * r t := mul_nonneg ht0 hr0
  have h2le : 2 ≤ 2 * n := by
    have := Nat.mul_le_mul_left 2 hn
    simpa using! this
  have hpow : (r t) ^ (2 * n) = (r t) ^ (2 : ℕ) * (r t) ^ (2 * n - 2) :=
    Eq.symm (pow_mul_pow_sub (r t) h2le)
  have hmul : t ^ (2 : ℕ) * (r t) ^ (2 : ℕ) = (t * r t) ^ (2 : ℕ) := by
    simp [mul_pow]
  have htr_sq : (t * r t) ^ (2 : ℕ) ≤ (1 / 23 : ℝ) ^ (2 : ℕ) :=
    pow_le_pow_left₀ htr0 htr 2
  calc
    t ^ (2 : ℕ) * (q t) ^ n = t ^ (2 : ℕ) * (r t) ^ (2 * n) := by
      simp [q_pow_eq_r_pow]
    _ = t ^ (2 : ℕ) * ((r t) ^ (2 : ℕ) * (r t) ^ (2 * n - 2)) := by
      simp [hpow]
    _ = (t ^ (2 : ℕ) * (r t) ^ (2 : ℕ)) * (r t) ^ (2 * n - 2) := by
      simp [mul_assoc]
    _ = (t * r t) ^ (2 : ℕ) * (r t) ^ (2 * n - 2) := by
      simp [hmul]
    _ ≤ (1 / 23 : ℝ) ^ (2 : ℕ) * (r t) ^ (2 * n - 2) :=
      mul_le_mul_of_nonneg_right htr_sq (pow_nonneg hr0 _)

/--
For `t ≥ 1` and `n ≥ 1`, bound `t * q(t)^n` by a shifted power of `r(t)`.

This is the one-power analogue of `t_sq_mul_q_pow_le`.
-/
public lemma t_mul_q_pow_le (t : ℝ) (ht : 1 ≤ t) (n : ℕ) (hn : 1 ≤ n) :
    t * (q t) ^ n ≤ ((1 / 23 : ℝ)) * (r t) ^ (2 * n - 1) := by
  have hr0 : 0 ≤ r t := (Real.exp_pos _).le
  have htr : t * r t ≤ (1 / 23 : ℝ) := AppendixA.t_mul_r_le_one_div_23 (t := t) ht
  have h1le : 1 ≤ 2 * n :=
    le_trans (by decide : (1 : ℕ) ≤ 2) (Nat.mul_le_mul_left 2 hn)
  have hpow : (r t) ^ (2 * n) = (r t) ^ (2 * n - 1) * r t := by
    have hs : (2 * n - 1) + 1 = 2 * n := Nat.sub_add_cancel h1le
    calc
      (r t) ^ (2 * n) = (r t) ^ ((2 * n - 1) + 1) := by simp [hs]
      _ = (r t) ^ (2 * n - 1) * (r t) ^ (1 : ℕ) := by simp [pow_add]
      _ = (r t) ^ (2 * n - 1) * r t := by simp
  calc
    t * (q t) ^ n = t * (r t) ^ (2 * n) := by
      simp [q_pow_eq_r_pow]
    _ = t * ((r t) ^ (2 * n - 1) * r t) := by simp [hpow]
    _ = (t * r t) * (r t) ^ (2 * n - 1) := by
      simp [mul_assoc, mul_comm]
    _ ≤ (1 / 23 : ℝ) * (r t) ^ (2 * n - 1) :=
          mul_le_mul_of_nonneg_right htr (pow_nonneg hr0 _)


end SpherePacking.Dim24.AppendixA
