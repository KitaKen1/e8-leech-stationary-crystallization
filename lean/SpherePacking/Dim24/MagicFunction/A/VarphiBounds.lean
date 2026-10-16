-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.ModularForms.Varphi
import SpherePacking.ModularForms.Delta.ImagAxis
import SpherePacking.ModularForms.ResToImagAxis
import SpherePacking.Dim24.Inequalities.AppendixA.EisensteinSeriesBounds
import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesMul

public import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import SpherePacking.ForMathlib.CancelDenomsCompat


/-!
# Bounds for `varphi` needed for the `+1` eigenfunction construction

We work with the numerator `varphi_num` of the modular form `varphi`, express it as a `qseries`,
and show that its first coefficients vanish (so the Fourier expansion starts at `q^3`). From this
we deduce an exponential decay bound for `varphi` at `atImInfty`, which is used to dominate the
contour integrands.

## Main definitions
* `VarphiBounds.varphi_num`
* `VarphiBounds.coeffVarphiNum`

## Main statements
* `VarphiBounds.varphi_isBigO_exp_neg_two_pi`
* `VarphiBounds.tendsto_varphi_atImInfty`
-/

open scoped BigOperators Real UpperHalfPlane
open Filter Asymptotics UpperHalfPlane

namespace SpherePacking.Dim24

noncomputable section

namespace VarphiBounds

open AppendixA


/-- The numerator `varphi · Δ²` (called `phinum` in `appendix.txt`). -/
def varphi_num (z : ℍ) : ℂ :=
  (25 * (E₄ z) ^ 4 - 49 * (E₆ z) ^ 2 * (E₄ z))
      + 48 * (E₆ z) * (E₄ z) ^ 2 * (E₂ z)
      + ((-49) * (E₄ z) ^ 3 + 25 * (E₆ z) ^ 2) * (E₂ z) ^ 2

/-! ### Coefficient model for `varphi_num` -/

def coeffE2Sq : ℕ → ℚ := fun n => conv coeffE2 coeffE2 n
def coeffE4Sq : ℕ → ℚ := fun n => conv coeffE4 coeffE4 n
def coeffE4Cube : ℕ → ℚ := fun n => conv coeffE4Sq coeffE4 n
def coeffE4Fourth : ℕ → ℚ := fun n => conv coeffE4Sq coeffE4Sq n
def coeffE6Sq : ℕ → ℚ := fun n => conv coeffE6 coeffE6 n

/-- Coefficients for the `qseries` model of `varphi_num`. -/
def coeffVarphiNum : ℕ → ℚ :=
  fun n =>
    (25 : ℚ) * coeffE4Fourth n
      - (49 : ℚ) * (conv coeffE6Sq coeffE4 n)
      + (48 : ℚ) * (conv (conv coeffE6 coeffE4Sq) coeffE2 n)
      + (conv (fun m => (-49 : ℚ) * coeffE4Cube m + (25 : ℚ) * coeffE6Sq m) coeffE2Sq n)

/-!
## Summability helper for q-series with polynomial coefficient bounds

For fixed `z : ℍ`, `‖qterm z n‖ = exp(-2π n z.im)` is geometric, so any polynomially bounded
coefficients yield absolute convergence.
-/

lemma summable_norm_qterm_mul_of_coeffBound (z : ℍ) (a : ℕ → ℚ) (C : ℝ) (k : ℕ)
    (ha : ∀ n : ℕ, |(a n : ℝ)| ≤ C * (((n + 1 : ℕ) : ℝ) ^ k)) :
    Summable (fun n : ℕ => ‖(a n : ℂ) * qterm z n‖) := by
  -- Compare to `C * (n+1)^k * r^n` with `r = exp(-2π * im z)`.
  set r : ℝ := Real.exp (-2 * Real.pi * z.im)
  have hr_nonneg : 0 ≤ r := (Real.exp_pos _).le
  have hr_lt_one : r < 1 := by
    have : (-2 * Real.pi * z.im : ℝ) < 0 := by nlinarith [Real.pi_pos, z.im_pos]
    simpa [r] using! (Real.exp_lt_one_iff.2 this)
  have hr_norm : ‖r‖ < 1 := by simpa [Real.norm_of_nonneg hr_nonneg] using! hr_lt_one
  have hs_pow : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ k : ℝ) * r ^ n) := by
    -- Shift the standard summability lemma.
    have hs0 : Summable (fun n : ℕ => ((n : ℝ) ^ k : ℝ) * r ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) k hr_norm
    -- `n ↦ (n+1)^k * r^n` is dominated by a shift of `n ↦ n^k * r^n`.
    -- We use `summable_nat_add_iff` to shift, then pull out a factor `1/r`.
    have hs1 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ k * r ^ (n + 1)) := by
      simpa [Nat.cast_add, Nat.cast_one] using!
        (summable_nat_add_iff 1 (f := fun n : ℕ => ((n : ℝ) ^ k : ℝ) * r ^ n)).2 hs0
    have hr_pos : 0 < r := Real.exp_pos _
    have hs2 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ k * r ^ n) := by
      have hs1' :
          Summable (fun n : ℕ => (1 / r) * (((n + 1 : ℕ) : ℝ) ^ k * r ^ (n + 1))) :=
        hs1.mul_left (1 / r)
      refine hs1'.congr ?_
      intro n
      field_simp [hr_pos.ne']
      -- `field_simp` reduces to a commutative semiring identity.
      ring_nf
    exact hs2
  have hC0 : 0 ≤ C := by
    have h0 := ha 0
    have : |(a 0 : ℝ)| ≤ C := by simpa using! h0
    exact le_trans (abs_nonneg _) this
  have hs_major : Summable (fun n : ℕ => C * (((n + 1 : ℕ) : ℝ) ^ k * r ^ n)) :=
    hs_pow.mul_left C
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hs_major
  intro n
  have hnorm_q : ‖qterm z n‖ = r ^ n := by
    -- `‖exp(2π i n z)‖ = exp(-2π n im z)`.
    have hre : (2 * Real.pi * Complex.I * (n : ℂ) * (z : ℂ)).re = -2 * Real.pi * n * z.im := by
      simp [mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg]
    calc
      ‖qterm z n‖ = ‖Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (z : ℂ))‖ := by
        simp [qterm]
      _ = Real.exp ((2 * Real.pi * Complex.I * (n : ℂ) * (z : ℂ)).re) := by
        simp [Complex.norm_exp]
      _ = Real.exp (-2 * Real.pi * n * z.im) := by simp [hre]
      _ = r ^ n := by
        -- `exp(-2π n im) = (exp(-2π im))^n`.
        calc
          Real.exp (-2 * Real.pi * n * z.im)
              = Real.exp ((n : ℕ) * ((-2 * Real.pi) * z.im)) := by
                  simp [mul_assoc, mul_left_comm, mul_comm]
          _ = (Real.exp ((-2 * Real.pi) * z.im)) ^ n := by
                  simpa using! (Real.exp_nat_mul ((-2 * Real.pi) * z.im) n)
          _ = r ^ n := by simp [r]
  calc
    ‖(a n : ℂ) * qterm z n‖ = ‖(a n : ℂ)‖ * ‖qterm z n‖ := by simp
    _ = |(a n : ℝ)| * r ^ n := by simp [hnorm_q]
    _ ≤ (C * (((n + 1 : ℕ) : ℝ) ^ k)) * r ^ n := by
          have ha' := ha n
          have hpow : 0 ≤ r ^ n := pow_nonneg hr_nonneg _
          exact mul_le_mul_of_nonneg_right (by simpa [mul_assoc] using! ha') hpow
    _ = C * (((n + 1 : ℕ) : ℝ) ^ k * r ^ n) := by ring

/-!
### Linearity helpers for `qseries`

These small lemmas keep later algebraic proofs from timing out by avoiding large `simp` terms.
-/

lemma qseries_smul_of_summable (z : ℍ) (c : ℂ) (a : ℕ → ℂ) :
    qseries (fun n : ℕ => c * a n) z = c * qseries a z := by
  simp [qseries, mul_assoc, tsum_mul_left]

lemma qseries_add4_of_summable (z : ℍ) (a b c d : ℕ → ℂ)
    (ha : Summable (fun n : ℕ => ‖a n * qterm z n‖))
    (hb : Summable (fun n : ℕ => ‖b n * qterm z n‖))
    (hc : Summable (fun n : ℕ => ‖c n * qterm z n‖))
    (hd : Summable (fun n : ℕ => ‖d n * qterm z n‖)) :
    qseries (fun n : ℕ => ((a n + b n) + c n) + d n) z =
      ((qseries a z + qseries b z) + qseries c z) + qseries d z := by
  have ha' : Summable (fun n : ℕ => a n * qterm z n) := Summable.of_norm ha
  have hb' : Summable (fun n : ℕ => b n * qterm z n) := Summable.of_norm hb
  have hc' : Summable (fun n : ℕ => c n * qterm z n) := Summable.of_norm hc
  have hd' : Summable (fun n : ℕ => d n * qterm z n) := Summable.of_norm hd
  have hab : Summable (fun n : ℕ => a n * qterm z n + b n * qterm z n) := ha'.add hb'
  have habc : Summable (fun n : ℕ => (a n * qterm z n + b n * qterm z n) + c n * qterm z n) :=
    hab.add hc'
  have habcd :
      Summable (fun n : ℕ =>
        ((a n * qterm z n + b n * qterm z n) + c n * qterm z n) + d n * qterm z n) :=
    habc.add hd'
  have htsum1 :
      (∑' n : ℕ, (a n * qterm z n + b n * qterm z n)) =
        (∑' n : ℕ, a n * qterm z n) + (∑' n : ℕ, b n * qterm z n) := by
    simpa using! (ha'.tsum_add hb')
  have htsum2 :
      (∑' n : ℕ, ((a n * qterm z n + b n * qterm z n) + c n * qterm z n)) =
        (∑' n : ℕ, (a n * qterm z n + b n * qterm z n)) + (∑' n : ℕ, c n * qterm z n) := by
    simpa using! (hab.tsum_add hc')
  have htsum3 :
      (∑' n : ℕ, (((a n * qterm z n + b n * qterm z n) + c n * qterm z n) + d n * qterm z n)) =
        (∑' n : ℕ, ((a n * qterm z n + b n * qterm z n) + c n * qterm z n)) +
          (∑' n : ℕ, d n * qterm z n) := by
    simpa using! (habc.tsum_add hd')
  -- Rewrite the summand `(a+b+c+d) * qterm` and conclude.
  have hsum :
      (∑' n : ℕ, (((a n + b n) + c n) + d n) * qterm z n) =
        (∑' n : ℕ, a n * qterm z n) + (∑' n : ℕ, b n * qterm z n) +
          (∑' n : ℕ, c n * qterm z n) + (∑' n : ℕ, d n * qterm z n) := by
    -- Expand, then use `htsum1/2/3`.
    -- We keep this `simp` local to avoid a large term.
    calc
      (∑' n : ℕ, (((a n + b n) + c n) + d n) * qterm z n)
          =
            ∑' n : ℕ,
              (((a n * qterm z n + b n * qterm z n) + c n * qterm z n) + d n * qterm z n) := by
              refine tsum_congr ?_
              intro n
              ring
      _ =
          (∑' n : ℕ, ((a n * qterm z n + b n * qterm z n) + c n * qterm z n)) +
            (∑' n : ℕ, d n * qterm z n) := by
            simpa using! htsum3
      _ = ((∑' n : ℕ, (a n * qterm z n + b n * qterm z n)) + (∑' n : ℕ, c n * qterm z n)) +
            (∑' n : ℕ, d n * qterm z n) := by
            have h := congrArg (fun x => x + (∑' n : ℕ, d n * qterm z n)) htsum2
            simpa [add_assoc] using! h
      _ = (∑' n : ℕ, (a n * qterm z n + b n * qterm z n)) +
            ((∑' n : ℕ, c n * qterm z n) + (∑' n : ℕ, d n * qterm z n)) := by
            simp [add_assoc]
      _ = ((∑' n : ℕ, a n * qterm z n) + (∑' n : ℕ, b n * qterm z n)) +
            ((∑' n : ℕ, c n * qterm z n) + (∑' n : ℕ, d n * qterm z n)) := by
            simp [htsum1, add_assoc]
      _ = (∑' n : ℕ, a n * qterm z n) + (∑' n : ℕ, b n * qterm z n) +
            (∑' n : ℕ, c n * qterm z n) + (∑' n : ℕ, d n * qterm z n) := by
            simp [add_assoc]
  -- Conclude by unfolding `qseries` and reassociating sums.
  simpa [qseries, add_assoc] using! hsum

/-! ### `varphi_num` as a `qseries` -/

lemma hs_coeffE2 (z : ℍ) :
    Summable (fun n : ℕ => ‖(coeffE2 n : ℂ) * qterm z n‖) := by
  refine summable_norm_qterm_mul_of_coeffBound (z := z) (a := coeffE2) (C := 24) (k := 2) ?_
  intro n
  simpa using! (abs_coeffE2_le (n := n))

lemma hs_coeffE4 (z : ℍ) :
    Summable (fun n : ℕ => ‖(coeffE4 n : ℂ) * qterm z n‖) := by
  refine summable_norm_qterm_mul_of_coeffBound (z := z) (a := coeffE4) (C := 240) (k := 4) ?_
  intro n
  simpa using! (abs_coeffE4_le (n := n))

lemma hs_coeffE6 (z : ℍ) :
    Summable (fun n : ℕ => ‖(coeffE6 n : ℂ) * qterm z n‖) := by
  refine summable_norm_qterm_mul_of_coeffBound (z := z) (a := coeffE6) (C := 504) (k := 6) ?_
  intro n
  simpa using! (abs_coeffE6_le (n := n))

lemma hs_coeffE2Sq (z : ℍ) :
    Summable (fun n : ℕ => ‖(coeffE2Sq n : ℂ) * qterm z n‖) := by
  -- Use the generic conv bound from AppendixA.
  have hconv :
      ∀ n : ℕ, |(coeffE2Sq n : ℝ)| ≤ (24 * 24) * (((n + 1 : ℕ) : ℝ) ^ (2 + 2 + 1)) := by
    intro n
    simpa [coeffE2Sq] using!
      (abs_conv_le (a := coeffE2) (b := coeffE2) (Ca := 24) (Cb := 24) (ka := 2) (kb := 2)
        (ha := abs_coeffE2_le) (hb := abs_coeffE2_le) n)
  exact summable_norm_qterm_mul_of_coeffBound z coeffE2Sq (24 * 24) (2 + 2 + 1) hconv

lemma hs_coeffE4Sq (z : ℍ) :
    Summable (fun n : ℕ => ‖(coeffE4Sq n : ℂ) * qterm z n‖) := by
  have hconv :
      ∀ n : ℕ, |(coeffE4Sq n : ℝ)| ≤ (240 * 240) * (((n + 1 : ℕ) : ℝ) ^ (4 + 4 + 1)) := by
    intro n
    simpa [coeffE4Sq] using!
      (abs_conv_le (a := coeffE4) (b := coeffE4) (Ca := 240) (Cb := 240) (ka := 4) (kb := 4)
        (ha := abs_coeffE4_le) (hb := abs_coeffE4_le) n)
  exact summable_norm_qterm_mul_of_coeffBound z coeffE4Sq (240 * 240) (4 + 4 + 1) hconv

lemma hs_coeffE6Sq (z : ℍ) :
    Summable (fun n : ℕ => ‖(coeffE6Sq n : ℂ) * qterm z n‖) := by
  have hconv :
      ∀ n : ℕ, |(coeffE6Sq n : ℝ)| ≤ (504 * 504) * (((n + 1 : ℕ) : ℝ) ^ (6 + 6 + 1)) := by
    intro n
    simpa [coeffE6Sq] using!
      (abs_conv_le (a := coeffE6) (b := coeffE6) (Ca := 504) (Cb := 504) (ka := 6) (kb := 6)
        (ha := abs_coeffE6_le) (hb := abs_coeffE6_le) n)
  exact summable_norm_qterm_mul_of_coeffBound z coeffE6Sq (504 * 504) (6 + 6 + 1) hconv

lemma hs_coeffE4Fourth (z : ℍ) :
    Summable (fun n : ℕ => ‖(coeffE4Fourth n : ℂ) * qterm z n‖) := by
  have hE4Sq_bound :
      ∀ m : ℕ, |(coeffE4Sq m : ℝ)| ≤ (240 * 240) * (((m + 1 : ℕ) : ℝ) ^ 9) := by
    intro m
    simpa [coeffE4Sq] using!
      (abs_conv_le (a := coeffE4) (b := coeffE4) (Ca := 240) (Cb := 240) (ka := 4) (kb := 4)
        (ha := abs_coeffE4_le) (hb := abs_coeffE4_le) m)
  have hconv :
      ∀ n : ℕ,
        |(coeffE4Fourth n : ℝ)| ≤ ((240 * 240) * (240 * 240)) * (((n + 1 : ℕ) : ℝ) ^ 19) := by
    intro n
    have h :=
      abs_conv_le (a := coeffE4Sq) (b := coeffE4Sq)
        (Ca := (240 * 240)) (Cb := (240 * 240)) (ka := 9) (kb := 9)
        (ha := hE4Sq_bound) (hb := hE4Sq_bound) n
    simpa [coeffE4Fourth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using! h
  exact summable_norm_qterm_mul_of_coeffBound z coeffE4Fourth (240 * 240 * (240 * 240)) 19 hconv

lemma hs_conv_coeffE6Sq_coeffE4 (z : ℍ) :
    Summable (fun n : ℕ => ‖(conv coeffE6Sq coeffE4 n : ℂ) * qterm z n‖) := by
  have hE6Sq_bound :
      ∀ m : ℕ, |(coeffE6Sq m : ℝ)| ≤ (504 * 504) * (((m + 1 : ℕ) : ℝ) ^ 13) := by
    intro m
    simpa [coeffE6Sq] using!
      (abs_conv_le (a := coeffE6) (b := coeffE6) (Ca := 504) (Cb := 504) (ka := 6) (kb := 6)
        (ha := abs_coeffE6_le) (hb := abs_coeffE6_le) m)
  have hconv :
      ∀ n : ℕ,
        |(conv coeffE6Sq coeffE4 n : ℝ)| ≤ ((504 * 504) * 240) * (((n + 1 : ℕ) : ℝ) ^ 18) := by
    intro n
    have h :=
      abs_conv_le (a := coeffE6Sq) (b := coeffE4)
        (Ca := (504 * 504)) (Cb := 240) (ka := 13) (kb := 4)
        (ha := hE6Sq_bound) (hb := abs_coeffE4_le) n
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using! h
  exact summable_norm_qterm_mul_of_coeffBound z (conv coeffE6Sq coeffE4) (504 * 504 * 240) 18 hconv

lemma hs_conv_coeffE6_coeffE4Sq (z : ℍ) :
    Summable (fun n : ℕ => ‖(conv coeffE6 coeffE4Sq n : ℂ) * qterm z n‖) := by
  have hE4Sq_bound :
      ∀ m : ℕ, |(coeffE4Sq m : ℝ)| ≤ (240 * 240) * (((m + 1 : ℕ) : ℝ) ^ 9) := by
    intro m
    simpa [coeffE4Sq] using!
      (abs_conv_le (a := coeffE4) (b := coeffE4) (Ca := 240) (Cb := 240) (ka := 4) (kb := 4)
        (ha := abs_coeffE4_le) (hb := abs_coeffE4_le) m)
  have hconv :
      ∀ n : ℕ,
        |(conv coeffE6 coeffE4Sq n : ℝ)| ≤ (504 * (240 * 240)) * (((n + 1 : ℕ) : ℝ) ^ 16) := by
    intro n
    have h :=
      abs_conv_le (a := coeffE6) (b := coeffE4Sq)
        (Ca := 504) (Cb := (240 * 240)) (ka := 6) (kb := 9)
        (ha := abs_coeffE6_le) (hb := hE4Sq_bound) n
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using! h
  exact
    summable_norm_qterm_mul_of_coeffBound z (conv coeffE6 coeffE4Sq)
      (504 * (240 * 240)) 16 hconv

lemma hs_conv_conv_coeffE6_coeffE4Sq_coeffE2 (z : ℍ) :
    Summable (fun n : ℕ => ‖(conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℂ) * qterm z n‖) := by
  have hE6E4Sq_bound :
      ∀ m : ℕ,
        |(conv coeffE6 coeffE4Sq m : ℝ)| ≤ (504 * (240 * 240)) * (((m + 1 : ℕ) : ℝ) ^ 16) := by
    intro m
    have hE4Sq_bound :
        ∀ j : ℕ, |(coeffE4Sq j : ℝ)| ≤ (240 * 240) * (((j + 1 : ℕ) : ℝ) ^ 9) := by
      intro j
      simpa [coeffE4Sq] using!
        (abs_conv_le (a := coeffE4) (b := coeffE4) (Ca := 240) (Cb := 240) (ka := 4) (kb := 4)
          (ha := abs_coeffE4_le) (hb := abs_coeffE4_le) j)
    have h :=
      abs_conv_le (a := coeffE6) (b := coeffE4Sq)
        (Ca := 504) (Cb := (240 * 240)) (ka := 6) (kb := 9)
        (ha := abs_coeffE6_le) (hb := hE4Sq_bound) m
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using! h
  have hconv :
      ∀ n : ℕ,
        |(conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℝ)| ≤
          ((504 * (240 * 240)) * 24) * (((n + 1 : ℕ) : ℝ) ^ 19) := by
    intro n
    have h :=
      abs_conv_le (a := fun m => conv coeffE6 coeffE4Sq m) (b := coeffE2)
        (Ca := (504 * (240 * 240))) (Cb := 24) (ka := 16) (kb := 2)
        (ha := hE6E4Sq_bound) (hb := abs_coeffE2_le) n
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using! h
  exact
    summable_norm_qterm_mul_of_coeffBound z (conv (conv coeffE6 coeffE4Sq) coeffE2)
      (504 * (240 * 240) * 24) 19 hconv

lemma E2Sq_eq_qseries (z : ℍ) :
    (E₂ z) ^ 2 = qseries (fun n : ℕ => (coeffE2Sq n : ℂ)) z := by
  have hE2 : E₂ z = qseries (fun n : ℕ => (coeffE2 n : ℂ)) z := AppendixA.E₂_eq_qseries z
  have hs : Summable (fun n : ℕ => ‖(coeffE2 n : ℂ) * qterm z n‖) := hs_coeffE2 z
  have hmul :=
    AppendixA.qseries_mul_cast (z := z) (a := coeffE2) (b := coeffE2)
      (ha := by simpa using! hs) (hb := by simpa using! hs)
  -- Turn `E₂^2` into `E₂*E₂` and rewrite with `hmul`.
  simpa [pow_two, hE2, coeffE2Sq] using! hmul

lemma E4Sq_eq_qseries (z : ℍ) :
    (E₄ z) ^ 2 = qseries (fun n : ℕ => (coeffE4Sq n : ℂ)) z := by
  have hE4 : E₄ z = qseries (fun n : ℕ => (coeffE4 n : ℂ)) z := AppendixA.E₄_eq_qseries z
  have hs : Summable (fun n : ℕ => ‖(coeffE4 n : ℂ) * qterm z n‖) := hs_coeffE4 z
  have hmul :=
    AppendixA.qseries_mul_cast (z := z) (a := coeffE4) (b := coeffE4)
      (ha := by simpa using! hs) (hb := by simpa using! hs)
  simpa [pow_two, hE4, coeffE4Sq] using! hmul

lemma E4Cube_eq_qseries (z : ℍ) :
    (E₄ z) ^ 3 = qseries (fun n : ℕ => (coeffE4Cube n : ℂ)) z := by
  have hE4 : E₄ z = qseries (fun n : ℕ => (coeffE4 n : ℂ)) z := AppendixA.E₄_eq_qseries z
  have hE4Sq : (E₄ z) ^ 2 = qseries (fun n : ℕ => (coeffE4Sq n : ℂ)) z := E4Sq_eq_qseries z
  have hs4 : Summable (fun n : ℕ => ‖(coeffE4 n : ℂ) * qterm z n‖) := hs_coeffE4 z
  have hs4sq : Summable (fun n : ℕ => ‖(coeffE4Sq n : ℂ) * qterm z n‖) := hs_coeffE4Sq z
  have hmul :=
    AppendixA.qseries_mul_cast (z := z) (a := coeffE4Sq) (b := coeffE4)
      (ha := by simpa using! hs4sq) (hb := by simpa using! hs4)
  -- Avoid `simp` rewriting `x^2` into `x*x` too early.
  -- `E₄^3 = (E₄^2) * E₄`.
  rw [pow_succ]
  rw [hE4Sq, hE4]
  simpa [coeffE4Cube] using! hmul

lemma E4Fourth_eq_qseries (z : ℍ) :
    (E₄ z) ^ 4 = qseries (fun n : ℕ => (coeffE4Fourth n : ℂ)) z := by
  have hE4Sq : (E₄ z) ^ 2 = qseries (fun n : ℕ => (coeffE4Sq n : ℂ)) z := E4Sq_eq_qseries z
  have hs4sq : Summable (fun n : ℕ => ‖(coeffE4Sq n : ℂ) * qterm z n‖) := hs_coeffE4Sq z
  have hmul :=
    AppendixA.qseries_mul_cast (z := z) (a := coeffE4Sq) (b := coeffE4Sq)
      (ha := by simpa using! hs4sq) (hb := by simpa using! hs4sq)
  calc
    (E₄ z) ^ 4 = ((E₄ z) ^ 2) ^ 2 := by simpa using! (pow_mul (E₄ z) 2 2)
    _ = (E₄ z) ^ 2 * (E₄ z) ^ 2 := by simp [pow_two]
    _ =
        qseries (fun n : ℕ => (coeffE4Sq n : ℂ)) z *
          qseries (fun n : ℕ => (coeffE4Sq n : ℂ)) z := by
        simpa using! congrArg (fun t : ℂ => t * t) hE4Sq
    _ = qseries (fun n : ℕ => (coeffE4Fourth n : ℂ)) z := by
        simpa [coeffE4Fourth] using! hmul

lemma E6Sq_eq_qseries (z : ℍ) :
    (E₆ z) ^ 2 = qseries (fun n : ℕ => (coeffE6Sq n : ℂ)) z := by
  have hE6 : E₆ z = qseries (fun n : ℕ => (coeffE6 n : ℂ)) z := AppendixA.E₆_eq_qseries z
  have hs : Summable (fun n : ℕ => ‖(coeffE6 n : ℂ) * qterm z n‖) := hs_coeffE6 z
  have hmul :=
    AppendixA.qseries_mul_cast (z := z) (a := coeffE6) (b := coeffE6)
      (ha := by simpa using! hs) (hb := by simpa using! hs)
  simpa [pow_two, hE6, coeffE6Sq] using! hmul

/-!
At this stage we have enough algebraic infrastructure to express each of the terms in `varphi_num`
as a `qseries`. We state the resulting identity as a single lemma.
-/

theorem varphi_num_eq_qseries (z : ℍ) :
    varphi_num z = qseries (fun n : ℕ => (coeffVarphiNum n : ℂ)) z := by
  -- Expand `varphi_num` and rewrite each Eisenstein series by its `qseries`.
  have hE2 : E₂ z = qseries (fun n : ℕ => (coeffE2 n : ℂ)) z := AppendixA.E₂_eq_qseries z
  have hE4 : E₄ z = qseries (fun n : ℕ => (coeffE4 n : ℂ)) z := AppendixA.E₄_eq_qseries z
  have hE6 : E₆ z = qseries (fun n : ℕ => (coeffE6 n : ℂ)) z := AppendixA.E₆_eq_qseries z
  have hE2Sq : (E₂ z) ^ 2 = qseries (fun n : ℕ => (coeffE2Sq n : ℂ)) z := E2Sq_eq_qseries z
  have hE4Sq : (E₄ z) ^ 2 = qseries (fun n : ℕ => (coeffE4Sq n : ℂ)) z := E4Sq_eq_qseries z
  have hE4Cube : (E₄ z) ^ 3 = qseries (fun n : ℕ => (coeffE4Cube n : ℂ)) z := E4Cube_eq_qseries z
  have hE4Fourth :
      (E₄ z) ^ 4 = qseries (fun n : ℕ => (coeffE4Fourth n : ℂ)) z :=
    E4Fourth_eq_qseries z
  have hE6Sq : (E₆ z) ^ 2 = qseries (fun n : ℕ => (coeffE6Sq n : ℂ)) z := E6Sq_eq_qseries z
  -- Now reduce the statement to Cauchy-product identities.
  -- We keep the proof lightweight by unfolding `qseries` and using `qseries_mul_cast` repeatedly.
  -- This is the same computation as in Appendix A (`GeOne.lean`), but we only need the statement.
  -- Helper for products of `qseries`.
  have hsE2 : Summable (fun n : ℕ => ‖(coeffE2 n : ℂ) * qterm z n‖) := hs_coeffE2 z
  have hsE4 : Summable (fun n : ℕ => ‖(coeffE4 n : ℂ) * qterm z n‖) := hs_coeffE4 z
  have hsE6 : Summable (fun n : ℕ => ‖(coeffE6 n : ℂ) * qterm z n‖) := hs_coeffE6 z
  have hsE4Sq : Summable (fun n : ℕ => ‖(coeffE4Sq n : ℂ) * qterm z n‖) := hs_coeffE4Sq z
  have hsE6Sq : Summable (fun n : ℕ => ‖(coeffE6Sq n : ℂ) * qterm z n‖) := hs_coeffE6Sq z
  have hsE2Sq : Summable (fun n : ℕ => ‖(coeffE2Sq n : ℂ) * qterm z n‖) := hs_coeffE2Sq z
  -- Build the needed Cauchy products:
  -- `E6Sq * E4`:
  have hE6Sq_mul_E4 :
      (qseries (fun n : ℕ => (coeffE6Sq n : ℂ)) z) *
          (qseries (fun n : ℕ => (coeffE4 n : ℂ)) z) =
        qseries (fun n : ℕ => (conv coeffE6Sq coeffE4 n : ℂ)) z :=
    qseries_mul_cast z coeffE6Sq coeffE4 hsE6Sq hsE4
  -- `E6 * E4Sq`:
  have hE6_mul_E4Sq :
      (qseries (fun n : ℕ => (coeffE6 n : ℂ)) z) *
          (qseries (fun n : ℕ => (coeffE4Sq n : ℂ)) z) =
        qseries (fun n : ℕ => (conv coeffE6 coeffE4Sq n : ℂ)) z :=
    qseries_mul_cast z coeffE6 coeffE4Sq hsE6 hsE4Sq
  -- `(E6*E4Sq) * E2`:
  have hsE6E4Sq :
      Summable (fun n : ℕ => ‖(conv coeffE6 coeffE4Sq n : ℂ) * qterm z n‖) :=
    hs_conv_coeffE6_coeffE4Sq z
  have hE6E4Sq_mul_E2 :
      (qseries (fun n : ℕ => (conv coeffE6 coeffE4Sq n : ℂ)) z) *
          (qseries (fun n : ℕ => (coeffE2 n : ℂ)) z) =
        qseries (fun n : ℕ => (conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℂ)) z :=
    qseries_mul_cast z (conv coeffE6 coeffE4Sq) coeffE2 hsE6E4Sq hsE2
  -- `(lincomb) * E2Sq`:
  let coeffLin : ℕ → ℚ := fun m => (-49 : ℚ) * coeffE4Cube m + (25 : ℚ) * coeffE6Sq m
  have hsE4Cube : Summable (fun n : ℕ => ‖(coeffE4Cube n : ℂ) * qterm z n‖) := by
    -- Bound via `abs_conv_le` twice.
    -- (We keep constants loose.)
    have hconv :
        ∀ n : ℕ,
          |(coeffE4Cube n : ℝ)| ≤
            ((240 * 240) * 240) * (((n + 1 : ℕ) : ℝ) ^ (4 + 9 + 1)) := by
      intro n
      have hE4Sq_bound :
          ∀ m : ℕ, |(coeffE4Sq m : ℝ)| ≤ (240 * 240) * (((m + 1 : ℕ) : ℝ) ^ 9) := by
        intro m
        have hconv' :
            |(coeffE4Sq m : ℝ)| ≤ (240 * 240) * (((m + 1 : ℕ) : ℝ) ^ (4 + 4 + 1)) := by
          simpa [coeffE4Sq] using!
            (abs_conv_le (a := coeffE4) (b := coeffE4) (Ca := 240) (Cb := 240) (ka := 4) (kb := 4)
              (ha := abs_coeffE4_le) (hb := abs_coeffE4_le) m)
        simpa using! hconv'
      simpa [coeffE4Cube, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using!
        (abs_conv_le (a := coeffE4Sq) (b := coeffE4)
          (Ca := (240 * 240)) (Cb := 240) (ka := 9) (kb := 4)
          (ha := hE4Sq_bound) (hb := abs_coeffE4_le) n)
    exact summable_norm_qterm_mul_of_coeffBound z coeffE4Cube (240 * 240 * 240) (4 + 9 + 1) hconv
  have hsLin : Summable (fun n : ℕ => ‖(coeffLin n : ℂ) * qterm z n‖) := by
    -- Polynomial bounds for `coeffE4Cube` and `coeffE6Sq`.
    have hE6Sq_bound :
        ∀ n : ℕ, |(coeffE6Sq n : ℝ)| ≤ (504 * 504) * (((n + 1 : ℕ) : ℝ) ^ 13) := by
      intro n
      simpa [coeffE6Sq] using!
        (abs_conv_le (a := coeffE6) (b := coeffE6) (Ca := 504) (Cb := 504) (ka := 6) (kb := 6)
          (ha := abs_coeffE6_le) (hb := abs_coeffE6_le) n)
    have hE4Sq_bound :
        ∀ n : ℕ, |(coeffE4Sq n : ℝ)| ≤ (240 * 240) * (((n + 1 : ℕ) : ℝ) ^ 9) := by
      intro n
      simpa [coeffE4Sq] using!
        (abs_conv_le (a := coeffE4) (b := coeffE4) (Ca := 240) (Cb := 240) (ka := 4) (kb := 4)
          (ha := abs_coeffE4_le) (hb := abs_coeffE4_le) n)
    have hE4Cube_bound :
        ∀ n : ℕ, |(coeffE4Cube n : ℝ)| ≤ ((240 * 240) * 240) * (((n + 1 : ℕ) : ℝ) ^ 14) := by
      intro n
      -- `coeffE4Cube = conv coeffE4Sq coeffE4`.
      have h :=
        abs_conv_le (a := coeffE4Sq) (b := coeffE4)
          (Ca := (240 * 240)) (Cb := 240) (ka := 9) (kb := 4)
          (ha := hE4Sq_bound) (hb := abs_coeffE4_le) n
      simpa [coeffE4Cube, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using! h
    -- Promote the `^13` bound to `^14`.
    have hE6Sq_bound' :
        ∀ n : ℕ, |(coeffE6Sq n : ℝ)| ≤ (504 * 504) * (((n + 1 : ℕ) : ℝ) ^ 14) := by
      intro n
      have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
      have hn0 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
      have hpow : (((n + 1 : ℕ) : ℝ) ^ 13) ≤ (((n + 1 : ℕ) : ℝ) ^ 14) := by
        -- `x^13 ≤ x^13 * x = x^14` since `1 ≤ x`.
        have hx13 : 0 ≤ (((n + 1 : ℕ) : ℝ) ^ 13) := pow_nonneg hn0 13
        nlinarith
      exact (hE6Sq_bound n).trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    -- Bound `coeffLin`.
    have hlin_bound :
        ∀ n : ℕ,
          |(coeffLin n : ℝ)| ≤
            ((49 : ℝ) * ((240 * 240) * 240) + (25 : ℝ) * (504 * 504)) *
              (((n + 1 : ℕ) : ℝ) ^ 14) := by
      intro n
      have hA : |(((-49 : ℚ) * coeffE4Cube n : ℚ) : ℝ)| ≤
          (49 : ℝ) * (((240 * 240) * 240) * (((n + 1 : ℕ) : ℝ) ^ 14)) := by
        have h := hE4Cube_bound n
        have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ (49 : ℝ))
        simpa [Rat.cast_mul, Rat.cast_neg, abs_mul, Rat.cast_ofNat, mul_assoc] using! this
      have hB : |(((25 : ℚ) * coeffE6Sq n : ℚ) : ℝ)| ≤
          (25 : ℝ) * ((504 * 504) * (((n + 1 : ℕ) : ℝ) ^ 14)) := by
        have h := hE6Sq_bound' n
        have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ (25 : ℝ))
        simpa [Rat.cast_mul, abs_mul, Rat.cast_ofNat, mul_assoc] using! this
      have htri :
          |(coeffLin n : ℝ)| ≤
            |(((-49 : ℚ) * coeffE4Cube n : ℚ) : ℝ)| + |(((25 : ℚ) * coeffE6Sq n : ℚ) : ℝ)| := by
        -- `abs_add_le` in `ℝ`, after rewriting casts.
        simpa [coeffLin, Rat.cast_add, Rat.cast_mul, Rat.cast_neg] using!
          (abs_add_le ((-49 : ℝ) * (coeffE4Cube n : ℝ)) ((25 : ℝ) * (coeffE6Sq n : ℝ)))
      have hsum := htri.trans (add_le_add hA hB)
      have :
          (49 : ℝ) * (((240 * 240) * 240) * (((n + 1 : ℕ) : ℝ) ^ 14)) +
              (25 : ℝ) * ((504 * 504) * (((n + 1 : ℕ) : ℝ) ^ 14)) =
            ((49 : ℝ) * ((240 * 240) * 240) + (25 : ℝ) * (504 * 504)) *
              (((n + 1 : ℕ) : ℝ) ^ 14) := by
        ring
      exact hsum.trans (le_of_eq this)
    refine summable_norm_qterm_mul_of_coeffBound (z := z) (a := coeffLin)
      (C := ((49 : ℝ) * ((240 * 240) * 240) + (25 : ℝ) * (504 * 504))) (k := 14) ?_
    intro n
    simpa using! hlin_bound n
  have hlin :
      qseries (fun n : ℕ => (coeffLin n : ℂ)) z =
        (-49 : ℂ) * qseries (fun n : ℕ => (coeffE4Cube n : ℂ)) z +
          (25 : ℂ) * qseries (fun n : ℕ => (coeffE6Sq n : ℂ)) z := by
    have hsE4Cube' : Summable (fun n : ℕ => (coeffE4Cube n : ℂ) * qterm z n) :=
      (Summable.of_norm hsE4Cube)
    have hsE6Sq' : Summable (fun n : ℕ => (coeffE6Sq n : ℂ) * qterm z n) :=
      (Summable.of_norm hsE6Sq)
    have hsA :
        Summable (fun n : ℕ => (-49 : ℂ) * ((coeffE4Cube n : ℂ) * qterm z n)) :=
      hsE4Cube'.mul_left (-49 : ℂ)
    have hsB :
        Summable (fun n : ℕ => (25 : ℂ) * ((coeffE6Sq n : ℂ) * qterm z n)) :=
      hsE6Sq'.mul_left (25 : ℂ)
    calc
      qseries (fun n : ℕ => (coeffLin n : ℂ)) z
          = ∑' n : ℕ, (coeffLin n : ℂ) * qterm z n := by
              simp [qseries]
      _ =
          ∑' n : ℕ,
            (((-49 : ℂ) * (coeffE4Cube n : ℂ) + (25 : ℂ) * (coeffE6Sq n : ℂ)) * qterm z n) := by
            refine tsum_congr ?_
            intro n
            simp [coeffLin, Rat.cast_add, Rat.cast_mul, Rat.cast_neg]
      _ = ∑' n : ℕ,
            ((-49 : ℂ) * ((coeffE4Cube n : ℂ) * qterm z n) +
              (25 : ℂ) * ((coeffE6Sq n : ℂ) * qterm z n)) := by
                refine tsum_congr ?_
                intro n
                ring
      _ =
          (∑' n : ℕ, (-49 : ℂ) * ((coeffE4Cube n : ℂ) * qterm z n)) +
            ∑' n : ℕ, (25 : ℂ) * ((coeffE6Sq n : ℂ) * qterm z n) := by
            simpa using! (hsA.tsum_add hsB)
      _ = (-49 : ℂ) * qseries (fun n : ℕ => (coeffE4Cube n : ℂ)) z +
            (25 : ℂ) * qseries (fun n : ℕ => (coeffE6Sq n : ℂ)) z := by
            have h1 :
                (∑' n : ℕ, (-49 : ℂ) * ((coeffE4Cube n : ℂ) * qterm z n)) =
                  (-49 : ℂ) * qseries (fun n : ℕ => (coeffE4Cube n : ℂ)) z := by
              -- Pull out the constant factor from the `tsum`.
              simpa [qseries, mul_assoc] using! (hsE4Cube'.tsum_mul_left (-49 : ℂ))
            have h2 :
                (∑' n : ℕ, (25 : ℂ) * ((coeffE6Sq n : ℂ) * qterm z n)) =
                  (25 : ℂ) * qseries (fun n : ℕ => (coeffE6Sq n : ℂ)) z := by
              simpa [qseries, mul_assoc] using! (hsE6Sq'.tsum_mul_left (25 : ℂ))
            -- Avoid relying on `congrArg2` (not always imported).
            lia
  have hsLin' : Summable (fun n : ℕ => ‖(coeffLin n : ℂ) * qterm z n‖) := hsLin
  have hmulLinE2Sq :
      (qseries (fun n : ℕ => (coeffLin n : ℂ)) z) * (qseries (fun n : ℕ => (coeffE2Sq n : ℂ)) z) =
        qseries (fun n : ℕ => (conv coeffLin coeffE2Sq n : ℂ)) z :=
    qseries_mul_cast z coeffLin coeffE2Sq hsLin hsE2Sq
  -- Assemble the `qseries` expression termwise and then combine coefficients.
  let a : ℕ → ℂ := fun n => ((25 : ℚ) * coeffE4Fourth n : ℂ)
  let b : ℕ → ℂ := fun n => ((-49 : ℚ) * (conv coeffE6Sq coeffE4 n) : ℂ)
  let c : ℕ → ℂ := fun n => ((48 : ℚ) * (conv (conv coeffE6 coeffE4Sq) coeffE2 n) : ℂ)
  let d : ℕ → ℂ := fun n => (conv coeffLin coeffE2Sq n : ℂ)
  have hsE4Fourth :
      Summable (fun n : ℕ => ‖(coeffE4Fourth n : ℂ) * qterm z n‖) :=
    hs_coeffE4Fourth z
  have hsE6SqE4 : Summable (fun n : ℕ => ‖(conv coeffE6Sq coeffE4 n : ℂ) * qterm z n‖) :=
    hs_conv_coeffE6Sq_coeffE4 z
  have hsE6E4SqE2 :
      Summable (fun n : ℕ => ‖(conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℂ) * qterm z n‖) :=
    hs_conv_conv_coeffE6_coeffE4Sq_coeffE2 z
  have hs_a : Summable (fun n : ℕ => ‖a n * qterm z n‖) := by
    have : Summable (fun n : ℕ => ‖(25 : ℂ)‖ * ‖(coeffE4Fourth n : ℂ) * qterm z n‖) :=
      hsE4Fourth.mul_left ‖(25 : ℂ)‖
    refine this.congr ?_
    intro n
    simp [a, mul_assoc]
  have hs_b : Summable (fun n : ℕ => ‖b n * qterm z n‖) := by
    have : Summable (fun n : ℕ => ‖(-49 : ℂ)‖ * ‖(conv coeffE6Sq coeffE4 n : ℂ) * qterm z n‖) :=
      hsE6SqE4.mul_left ‖(-49 : ℂ)‖
    refine this.congr ?_
    intro n
    simp [b, mul_assoc]
  have hs_c : Summable (fun n : ℕ => ‖c n * qterm z n‖) := by
    have : Summable (fun n : ℕ =>
        ‖(48 : ℂ)‖ * ‖(conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℂ) * qterm z n‖) :=
      hsE6E4SqE2.mul_left ‖(48 : ℂ)‖
    refine this.congr ?_
    intro n
    simp [c, mul_assoc]
  -- Summability for the convolution coefficients in the final term.
  have hs_d : Summable (fun n : ℕ => ‖d n * qterm z n‖) := by
    -- Polynomial bound for `coeffLin`.
    have hE4Sq_bound :
        ∀ m : ℕ, |(coeffE4Sq m : ℝ)| ≤ (240 * 240) * (((m + 1 : ℕ) : ℝ) ^ 9) := by
      intro m
      simpa [coeffE4Sq] using!
        (abs_conv_le (a := coeffE4) (b := coeffE4) (Ca := 240) (Cb := 240) (ka := 4) (kb := 4)
          (ha := abs_coeffE4_le) (hb := abs_coeffE4_le) m)
    have hE4Cube_bound :
        ∀ m : ℕ, |(coeffE4Cube m : ℝ)| ≤ ((240 * 240) * 240) * (((m + 1 : ℕ) : ℝ) ^ 14) := by
      intro m
      have h :=
        abs_conv_le (a := coeffE4Sq) (b := coeffE4)
          (Ca := (240 * 240)) (Cb := 240) (ka := 9) (kb := 4)
          (ha := hE4Sq_bound) (hb := abs_coeffE4_le) m
      simpa [coeffE4Cube, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using! h
    have hE6Sq_bound :
        ∀ m : ℕ, |(coeffE6Sq m : ℝ)| ≤ (504 * 504) * (((m + 1 : ℕ) : ℝ) ^ 14) := by
      intro m
      have h0 :
          |(coeffE6Sq m : ℝ)| ≤ (504 * 504) * (((m + 1 : ℕ) : ℝ) ^ 13) := by
        simpa [coeffE6Sq] using!
          (abs_conv_le (a := coeffE6) (b := coeffE6) (Ca := 504) (Cb := 504) (ka := 6) (kb := 6)
            (ha := abs_coeffE6_le) (hb := abs_coeffE6_le) m)
      have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m))
      have hpow : (((m + 1 : ℕ) : ℝ) ^ 13) ≤ (((m + 1 : ℕ) : ℝ) ^ 14) :=
        pow_le_pow_right₀ hm1 (by decide : (13 : ℕ) ≤ 14)
      exact h0.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    let C_lin : ℝ := ((49 : ℝ) * ((240 * 240) * 240) + (25 : ℝ) * (504 * 504))
    have hLin_bound :
        ∀ m : ℕ, |(coeffLin m : ℝ)| ≤ C_lin * (((m + 1 : ℕ) : ℝ) ^ 14) := by
      intro m
      have hA :
          |(((-49 : ℚ) * coeffE4Cube m : ℚ) : ℝ)| ≤
            (49 : ℝ) * (((240 * 240) * 240) * (((m + 1 : ℕ) : ℝ) ^ 14)) := by
        have h := hE4Cube_bound m
        have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ (49 : ℝ))
        simpa [Rat.cast_mul, Rat.cast_neg, abs_mul, Rat.cast_ofNat, mul_assoc] using! this
      have hB :
          |(((25 : ℚ) * coeffE6Sq m : ℚ) : ℝ)| ≤
            (25 : ℝ) * ((504 * 504) * (((m + 1 : ℕ) : ℝ) ^ 14)) := by
        have h := hE6Sq_bound m
        have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ (25 : ℝ))
        simpa [Rat.cast_mul, abs_mul, Rat.cast_ofNat, mul_assoc] using! this
      have htri :
          |(coeffLin m : ℝ)| ≤
            |(((-49 : ℚ) * coeffE4Cube m : ℚ) : ℝ)| + |(((25 : ℚ) * coeffE6Sq m : ℚ) : ℝ)| := by
        simpa [coeffLin, Rat.cast_add, Rat.cast_mul, Rat.cast_neg] using!
          (abs_add_le ((-49 : ℝ) * (coeffE4Cube m : ℝ)) ((25 : ℝ) * (coeffE6Sq m : ℝ)))
      have hsum :=
        htri.trans (add_le_add hA hB)
      have :
          (49 : ℝ) * (((240 * 240) * 240) * (((m + 1 : ℕ) : ℝ) ^ 14)) +
              (25 : ℝ) * ((504 * 504) * (((m + 1 : ℕ) : ℝ) ^ 14)) =
            C_lin * (((m + 1 : ℕ) : ℝ) ^ 14) := by
        simp [C_lin]
        ring
      exact hsum.trans (le_of_eq this)
    have hE2Sq_bound :
        ∀ m : ℕ, |(coeffE2Sq m : ℝ)| ≤ (24 * 24) * (((m + 1 : ℕ) : ℝ) ^ 5) := by
      intro m
      simpa [coeffE2Sq] using!
        (abs_conv_le (a := coeffE2) (b := coeffE2) (Ca := 24) (Cb := 24) (ka := 2) (kb := 2)
          (ha := abs_coeffE2_le) (hb := abs_coeffE2_le) m)
    have hconv :
        ∀ n : ℕ,
          |(conv coeffLin coeffE2Sq n : ℝ)| ≤ (C_lin * (24 * 24)) * (((n + 1 : ℕ) : ℝ) ^ 20) := by
      intro n
      have h :=
        abs_conv_le (a := coeffLin) (b := coeffE2Sq)
          (Ca := C_lin) (Cb := (24 * 24)) (ka := 14) (kb := 5)
          (ha := hLin_bound) (hb := hE2Sq_bound) n
      simpa [d, C_lin, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using! h
    have hs :=
      summable_norm_qterm_mul_of_coeffBound (z := z) (a := fun n => conv coeffLin coeffE2Sq n)
        (C := (C_lin * (24 * 24))) (k := 20) hconv
    simpa [d] using! hs
  -- Identify each of the four qseries with the corresponding modular-form term.
  have ha_term : qseries a z = (25 : ℂ) * (E₄ z) ^ 4 := by
    have := qseries_smul_of_summable (z := z) (c := (25 : ℂ))
      (a := fun n : ℕ => (coeffE4Fourth n : ℂ))
    -- `qseries a = 25 * qseries coeffE4Fourth = 25 * E₄^4`.
    have h1 : qseries a z = (25 : ℂ) * qseries (fun n : ℕ => (coeffE4Fourth n : ℂ)) z := by
      simpa [a, mul_assoc] using! this
    exact Eq.symm (CancelDenoms.derive_trans hE4Fourth (id (Eq.symm h1)))
  have hb_term : qseries b z = (-49 : ℂ) * ((E₆ z) ^ 2 * (E₄ z)) := by
    have hconv' :
        qseries (fun n : ℕ => (conv coeffE6Sq coeffE4 n : ℂ)) z = (E₆ z) ^ 2 * (E₄ z) := by
      -- Use the Cauchy product identity and rewrite `E₆^2`, `E₄`.
      lia
    have := qseries_smul_of_summable (z := z) (c := (-49 : ℂ))
      (a := fun n : ℕ => (conv coeffE6Sq coeffE4 n : ℂ))
    -- `qseries b = (-49) * qseries conv = (-49) * (E₆^2 * E₄)`.
    simpa [b, hconv', Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat, mul_assoc] using! this
  have hc_term : qseries c z = (48 : ℂ) * ((E₆ z) * (E₄ z) ^ 2 * (E₂ z)) := by
    have hconv' :
        qseries (fun n : ℕ => (conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℂ)) z =
          (E₆ z) * (E₄ z) ^ 2 * (E₂ z) := by
      -- Rewrite `E₆*E₄^2` as a qseries and multiply by `E₂`.
      lia
    have := qseries_smul_of_summable (z := z) (c := (48 : ℂ))
      (a := fun n : ℕ => (conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℂ))
    simpa [c, hconv', Rat.cast_mul, Rat.cast_ofNat, mul_assoc] using! this
  have hd_term :
      qseries d z = ((-49 : ℂ) * (E₄ z) ^ 3 + (25 : ℂ) * (E₆ z) ^ 2) * (E₂ z) ^ 2 := by
    -- Rewrite `qseries d` as the Cauchy product `qseries coeffLin * qseries coeffE2Sq`.
    grind only
            -- `rw` already puts the goal into reflexive form.
  have hsum_terms :
      varphi_num z = qseries a z + qseries b z + qseries c z + qseries d z := by
    -- Rewrite the `qseries` terms, then close by ring-normalization.
    rw [ha_term, hb_term, hc_term, hd_term]
    -- Now this is a direct algebraic identity.
    unfold varphi_num
    ring
  have hcombine :
      qseries a z + qseries b z + qseries c z + qseries d z =
        qseries (fun n : ℕ => ((a n + b n) + c n) + d n) z :=
    Eq.symm (qseries_add4_of_summable z a b c d hs_a hs_b hs_c hs_d)
  have hcoeff :
      (fun n : ℕ => ((a n + b n) + c n) + d n) = fun n : ℕ => (coeffVarphiNum n : ℂ) := by
    funext n
    simp [a, b, c, d, coeffVarphiNum, coeffLin, sub_eq_add_neg,
      Rat.cast_add, Rat.cast_mul, Rat.cast_neg]
  calc
    varphi_num z = qseries a z + qseries b z + qseries c z + qseries d z := hsum_terms
    _ = qseries (fun n : ℕ => ((a n + b n) + c n) + d n) z := hcombine
    _ = qseries (fun n : ℕ => (coeffVarphiNum n : ℂ)) z := by simp [hcoeff]
/-!
## Vanishing of low coefficients of `varphi_num`

The paper's q-expansion implies `varphi_num` starts at `q^3`. We verify this directly on the
coefficient model `coeffVarphiNum` (a finite calculation at `n = 0,1,2`).
-/

lemma coeffVarphiNum_zero : coeffVarphiNum 0 = 0 := by
  -- Unfold and compute `conv` at `0`, where only the pair `(0,0)` contributes.
  simp [coeffVarphiNum, coeffE2Sq, coeffE4Sq, coeffE4Cube, coeffE4Fourth, coeffE6Sq, conv, coeffE2,
    coeffE4, coeffE6]
  ring

lemma coeffVarphiNum_one : coeffVarphiNum 1 = 0 := by
  have hanti : (Finset.antidiagonal 1 : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} := by
    rfl
  -- Unfold `conv` using the explicit antidiagonal.
  simp [coeffVarphiNum, coeffE2Sq, coeffE4Sq, coeffE4Cube, coeffE4Fourth, coeffE6Sq, conv,
    coeffE2, coeffE4, coeffE6, hanti]
  ring

lemma coeffVarphiNum_two : coeffVarphiNum 2 = 0 := by
  have hanti : (Finset.antidiagonal 2 : Finset (ℕ × ℕ)) = {(0, 2), (1, 1), (2, 0)} := by
    rfl
  have hanti1 : (Finset.antidiagonal 1 : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} := by
    rfl
  have hsigma1 : (ArithmeticFunction.sigma 1 2 : ℕ) = 3 := by
    have h := ArithmeticFunction.sigma_one_apply_prime_pow (p := 2) (i := 1) Nat.prime_two
    simpa [pow_one] using! (by simpa using! h)
  have hsigma3 : (ArithmeticFunction.sigma 3 2 : ℕ) = 9 := by
    have h := ArithmeticFunction.sigma_apply_prime_pow (k := 3) (p := 2) (i := 1) Nat.prime_two
    simpa [pow_one] using! (by simpa using! h)
  have hsigma5 : (ArithmeticFunction.sigma 5 2 : ℕ) = 33 := by
    have h := ArithmeticFunction.sigma_apply_prime_pow (k := 5) (p := 2) (i := 1) Nat.prime_two
    simpa [pow_one] using! (by simpa using! h)
  -- Unfold `conv` using the explicit antidiagonal and evaluate `σ k 2`.
  simp [coeffVarphiNum, coeffE2Sq, coeffE4Sq, coeffE4Cube, coeffE4Fourth, coeffE6Sq, conv,
    coeffE2, coeffE4, coeffE6, hanti, hanti1, hsigma1, hsigma3, hsigma5]
  ring

/-!
## Polynomial bounds for `coeffVarphiNum`

To use the Fourier-shift asymptotics lemma, we only need a coarse polynomial bound on
`coeffVarphiNum`. This is obtained from the standard polynomial bounds on the Eisenstein
coefficients via repeated `abs_conv_le`.
-/

def coeffLin : ℕ → ℚ := fun m => (-49 : ℚ) * coeffE4Cube m + (25 : ℚ) * coeffE6Sq m

lemma abs_coeffE2Sq_le (n : ℕ) :
    |(coeffE2Sq n : ℝ)| ≤ (24 * 24) * (((n + 1 : ℕ) : ℝ) ^ 5) := by
  simpa [coeffE2Sq] using!
    (abs_conv_le (a := coeffE2) (b := coeffE2) (Ca := 24) (Cb := 24) (ka := 2) (kb := 2)
      (ha := abs_coeffE2_le) (hb := abs_coeffE2_le) n)

lemma abs_coeffE4Sq_le (n : ℕ) :
    |(coeffE4Sq n : ℝ)| ≤ (240 * 240) * (((n + 1 : ℕ) : ℝ) ^ 9) := by
  simpa [coeffE4Sq] using!
    (abs_conv_le (a := coeffE4) (b := coeffE4) (Ca := 240) (Cb := 240) (ka := 4) (kb := 4)
      (ha := abs_coeffE4_le) (hb := abs_coeffE4_le) n)

lemma abs_coeffE4Cube_le (n : ℕ) :
    |(coeffE4Cube n : ℝ)| ≤ ((240 * 240) * 240) * (((n + 1 : ℕ) : ℝ) ^ 14) := by
  have h :=
    abs_conv_le (a := coeffE4Sq) (b := coeffE4) (Ca := (240 * 240)) (Cb := 240) (ka := 9) (kb := 4)
      (ha := abs_coeffE4Sq_le) (hb := abs_coeffE4_le) n
  simpa [coeffE4Cube, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using! h

lemma abs_coeffE4Fourth_le (n : ℕ) :
    |(coeffE4Fourth n : ℝ)| ≤ ((240 * 240) * (240 * 240)) * (((n + 1 : ℕ) : ℝ) ^ 19) := by
  have h :=
    abs_conv_le (a := coeffE4Sq) (b := coeffE4Sq) (Ca := (240 * 240)) (Cb := (240 * 240))
      (ka := 9) (kb := 9) (ha := abs_coeffE4Sq_le) (hb := abs_coeffE4Sq_le) n
  simpa [coeffE4Fourth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using! h

lemma abs_coeffE6Sq_le_pow14 (n : ℕ) :
    |(coeffE6Sq n : ℝ)| ≤ (504 * 504) * (((n + 1 : ℕ) : ℝ) ^ 14) := by
  have h0 :
      |(coeffE6Sq n : ℝ)| ≤ (504 * 504) * (((n + 1 : ℕ) : ℝ) ^ 13) := by
    simpa [coeffE6Sq] using!
      (abs_conv_le (a := coeffE6) (b := coeffE6) (Ca := 504) (Cb := 504) (ka := 6) (kb := 6)
        (ha := abs_coeffE6_le) (hb := abs_coeffE6_le) n)
  have hx : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hpow : (((n + 1 : ℕ) : ℝ) ^ 13) ≤ (((n + 1 : ℕ) : ℝ) ^ 14) :=
    pow_le_pow_right₀ hx (by decide : (13 : ℕ) ≤ 14)
  exact h0.trans (mul_le_mul_of_nonneg_left hpow (by positivity))

lemma abs_coeffLin_le (n : ℕ) :
    |(coeffLin n : ℝ)| ≤
      (((49 : ℝ) * ((240 * 240) * 240)) + ((25 : ℝ) * (504 * 504))) * (((n + 1 : ℕ) : ℝ) ^ 14) := by
  set x : ℝ := ((n + 1 : ℕ) : ℝ)
  have hE4 : |(coeffE4Cube n : ℝ)| ≤ ((240 * 240) * 240) * (x ^ 14) := by
    simpa [x] using! abs_coeffE4Cube_le n
  have hE6 : |(coeffE6Sq n : ℝ)| ≤ (504 * 504) * (x ^ 14) := by
    simpa [x] using! abs_coeffE6Sq_le_pow14 n
  have hA :
      |(((-49 : ℚ) * coeffE4Cube n : ℚ) : ℝ)| ≤ (49 : ℝ) * (((240 * 240) * 240) * (x ^ 14)) := by
    have := mul_le_mul_of_nonneg_left hE4 (by positivity : (0 : ℝ) ≤ (49 : ℝ))
    simpa [Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat, abs_mul, mul_assoc] using! this
  have hB :
      |(((25 : ℚ) * coeffE6Sq n : ℚ) : ℝ)| ≤ (25 : ℝ) * ((504 * 504) * (x ^ 14)) := by
    have := mul_le_mul_of_nonneg_left hE6 (by positivity : (0 : ℝ) ≤ (25 : ℝ))
    simpa [Rat.cast_mul, Rat.cast_ofNat, abs_mul, mul_assoc] using! this
  have htri :
      |(coeffLin n : ℝ)| ≤
        |(((-49 : ℚ) * coeffE4Cube n : ℚ) : ℝ)| + |(((25 : ℚ) * coeffE6Sq n : ℚ) : ℝ)| := by
    simpa [coeffLin, Rat.cast_add, Rat.cast_mul, Rat.cast_neg] using!
      (abs_add_le ((-49 : ℝ) * (coeffE4Cube n : ℝ)) ((25 : ℝ) * (coeffE6Sq n : ℝ)))
  linarith

lemma abs_conv_coeffLin_coeffE2Sq_le (n : ℕ) :
    |(conv coeffLin coeffE2Sq n : ℝ)| ≤
      ((((49 : ℝ) * ((240 * 240) * 240)) + ((25 : ℝ) * (504 * 504))) * (24 * 24)) *
        (((n + 1 : ℕ) : ℝ) ^ 20) := by
  have h :=
    abs_conv_le (a := coeffLin) (b := coeffE2Sq)
      (Ca := (((49 : ℝ) * ((240 * 240) * 240)) + ((25 : ℝ) * (504 * 504))))
      (Cb := (24 * 24)) (ka := 14) (kb := 5) (ha := abs_coeffLin_le) (hb := abs_coeffE2Sq_le) n
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using! h

lemma abs_coeffVarphiNum_le_pow20 (n : ℕ) :
    |(coeffVarphiNum n : ℝ)| ≤
      (((25 : ℝ) * ((240 * 240) * (240 * 240)))
            + ((49 : ℝ) * ((504 * 504) * 240))
            + ((48 : ℝ) * (((504 : ℝ) * (240 * 240)) * (24 : ℝ)))
            + ((((49 : ℝ) * ((240 * 240) * 240)) + ((25 : ℝ) * (504 * 504))) * (24 * 24))) *
        (((n + 1 : ℕ) : ℝ) ^ 20) := by
  set x : ℝ := ((n + 1 : ℕ) : ℝ)
  have hx : (1 : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hA0 : |(coeffE4Fourth n : ℝ)| ≤ ((240 * 240) * (240 * 240)) * (x ^ 19) := by
    simpa [x] using! abs_coeffE4Fourth_le n
  have hA :
      |(((25 : ℚ) * coeffE4Fourth n : ℚ) : ℝ)| ≤
        ((25 : ℝ) * ((240 * 240) * (240 * 240))) * (x ^ 20) := by
    have hpow : x ^ 19 ≤ x ^ 20 := pow_le_pow_right₀ hx (by decide : (19 : ℕ) ≤ 20)
    have hA' : |(((25 : ℚ) * coeffE4Fourth n : ℚ) : ℝ)| ≤
        (25 : ℝ) * (((240 * 240) * (240 * 240)) * (x ^ 19)) := by
      simp_all
    linarith
  have hB0 :
      |(conv coeffE6Sq coeffE4 n : ℝ)| ≤ ((504 * 504) * (240 : ℝ)) * (x ^ 18) := by
    have habs :
        |(conv coeffE6Sq coeffE4 n : ℝ)| ≤ ((504 * 504) * (240 : ℝ)) *
          (((n + 1 : ℕ) : ℝ) ^ ((6 + 6 + 1) + 4 + 1)) := by
      -- Expand `coeffE6Sq` as a convolution and apply `abs_conv_le` twice.
      have hE6Sq :
          ∀ m : ℕ, |(coeffE6Sq m : ℝ)| ≤ (504 * 504) * (((m + 1 : ℕ) : ℝ) ^ 13) := by
        intro m
        simpa [coeffE6Sq] using!
          (abs_conv_le (a := coeffE6) (b := coeffE6) (Ca := 504) (Cb := 504) (ka := 6) (kb := 6)
            (ha := abs_coeffE6_le) (hb := abs_coeffE6_le) m)
      simpa using!
        (abs_conv_le (a := coeffE6Sq) (b := coeffE4)
          (Ca := (504 * 504)) (Cb := 240) (ka := 13) (kb := 4)
          (ha := hE6Sq) (hb := abs_coeffE4_le) n)
    -- `18 = (6+6+1)+4+1`.
    simpa [x, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using! habs
  have hB :
      |(((-49 : ℚ) * (conv coeffE6Sq coeffE4 n) : ℚ) : ℝ)| ≤
        ((49 : ℝ) * ((504 * 504) * 240)) * (x ^ 20) := by
    have hpow : x ^ 18 ≤ x ^ 20 := pow_le_pow_right₀ hx (by decide : (18 : ℕ) ≤ 20)
    have hB' :=
      mul_le_mul_of_nonneg_left (hB0.trans (mul_le_mul_of_nonneg_left hpow (by positivity)))
        (by positivity : (0 : ℝ) ≤ (49 : ℝ))
    -- Rewrite `|(-49)*b|` as `49*|b|`.
    simpa [Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat, abs_mul, abs_neg,
      mul_assoc, mul_left_comm, mul_comm] using! hB'
  have hC0 :
      |(conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℝ)| ≤
        (((504 : ℝ) * (240 * 240)) * (24 : ℝ)) * (x ^ 19) := by
    have habs :
        |(conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℝ)| ≤
          (((504 : ℝ) * (240 * 240)) * (24 : ℝ)) *
            (((n + 1 : ℕ) : ℝ) ^ ((6 + (4 + 4 + 1) + 1) + 2 + 1)) := by
      have hE4Sq : ∀ m : ℕ, |(coeffE4Sq m : ℝ)| ≤ (240 * 240) * (((m + 1 : ℕ) : ℝ) ^ 9) := by
        intro m; simpa using! abs_coeffE4Sq_le m
      have hE6E4Sq :
          ∀ m : ℕ, |(conv coeffE6 coeffE4Sq m : ℝ)| ≤ ((504 : ℝ) * (240 * 240)) *
            (((m + 1 : ℕ) : ℝ) ^ (6 + (4 + 4 + 1) + 1)) := by
        intro m
        simpa using!
          (abs_conv_le (a := coeffE6) (b := coeffE4Sq)
            (Ca := 504) (Cb := (240 * 240)) (ka := 6) (kb := 9)
            (ha := abs_coeffE6_le) (hb := hE4Sq) m)
      simpa using!
        (abs_conv_le (a := fun m => conv coeffE6 coeffE4Sq m) (b := coeffE2)
          (Ca := ((504 : ℝ) * (240 * 240))) (Cb := 24) (ka := (6 + (4 + 4 + 1) + 1)) (kb := 2)
          (ha := hE6E4Sq) (hb := abs_coeffE2_le) n)
    simpa [x, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using! habs
  have hC :
      |(((48 : ℚ) * (conv (conv coeffE6 coeffE4Sq) coeffE2 n) : ℚ) : ℝ)| ≤
        ((48 : ℝ) * (((504 : ℝ) * (240 * 240)) * (24 : ℝ))) * (x ^ 20) := by
    have hpow : x ^ 19 ≤ x ^ 20 := pow_le_pow_right₀ hx (by decide : (19 : ℕ) ≤ 20)
    have hC' :=
      mul_le_mul_of_nonneg_left (hC0.trans (mul_le_mul_of_nonneg_left hpow (by positivity)))
        (by positivity : (0 : ℝ) ≤ (48 : ℝ))
    simpa [Rat.cast_mul, Rat.cast_ofNat, abs_mul, mul_assoc, mul_left_comm, mul_comm] using! hC'
  have hD :
      |(conv coeffLin coeffE2Sq n : ℝ)| ≤
        ((((49 : ℝ) * ((240 * 240) * 240)) + ((25 : ℝ) * (504 * 504))) * (24 * 24)) * (x ^ 20) := by
    simpa [x] using! abs_conv_coeffLin_coeffE2Sq_le n
  -- Triangle inequality for the four-term expression.
  have htri :
      |(coeffVarphiNum n : ℝ)| ≤
        |(((25 : ℚ) * coeffE4Fourth n : ℚ) : ℝ)|
          + |(((-49 : ℚ) * conv coeffE6Sq coeffE4 n : ℚ) : ℝ)|
          + |(((48 : ℚ) * conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℚ) : ℝ)|
          + |(conv coeffLin coeffE2Sq n : ℝ)| := by
    set A : ℝ := (((25 : ℚ) * coeffE4Fourth n : ℚ) : ℝ)
    set B : ℝ := (((-49 : ℚ) * conv coeffE6Sq coeffE4 n : ℚ) : ℝ)
    set C : ℝ := (((48 : ℚ) * conv (conv coeffE6 coeffE4Sq) coeffE2 n : ℚ) : ℝ)
    set D : ℝ := (conv coeffLin coeffE2Sq n : ℝ)
    have hdecomp : (coeffVarphiNum n : ℝ) = A + B + C + D := by
      have hconv :
          conv (fun m => -(49 * coeffE4Cube m) + 25 * coeffE6Sq m) coeffE2Sq n =
            conv coeffLin coeffE2Sq n := by
        have hfun : (fun m => -(49 * coeffE4Cube m) + 25 * coeffE6Sq m) = coeffLin := by
          funext m
          simp [coeffLin]
        simp [hfun]
      -- After unfolding, the only nontrivial identification is the last convolution term.
      simpa [
        A, B, C, D, coeffVarphiNum, sub_eq_add_neg,
        Rat.cast_add, Rat.cast_mul, Rat.cast_neg
      ] using! hconv
    have hAB : |A + B| ≤ |A| + |B| := abs_add_le _ _
    have hABC : |A + B + C| ≤ |A + B| + |C| := by
      simpa [add_assoc] using! (abs_add_le (A + B) C)
    have hABCD : |A + B + C + D| ≤ |A + B + C| + |D| := by
      simpa [add_assoc] using! (abs_add_le (A + B + C) D)
    grind only
  -- Apply the bounds and factor out `x^20`.
  linarith

/-!
## Exponential decay at infinity

From the shift-3 qseries model for `varphi_num` and `Δ =Θ exp(-2π im)`, we get
`varphi =O exp(-2π im)` at `atImInfty`.
-/

theorem varphi_num_isBigO_exp_neg_six_pi :
    varphi_num =O[atImInfty] fun z : ℍ => Real.exp (-(2 * Real.pi * (3 : ℝ)) * z.im) := by
  -- Coefficients of the shifted Fourier expansion.
  let a : ℕ → ℂ := fun m => (coeffVarphiNum (m + 3) : ℂ)
  -- Summability of `‖a m‖ · exp(-2π m)` at height `c = 1`, using a coarse polynomial bound.
  have ha_sum : Summable (fun m : ℕ => ‖a m‖ * Real.exp (-(2 * Real.pi * (1 : ℝ)) * (m : ℝ))) := by
    -- First bound `|(coeffVarphiNum (m+3) : ℝ)|` by a fixed polynomial in `m+1`.
    set C0 : ℝ :=
      ((25 : ℝ) * ((240 * 240) * (240 * 240)))
        + ((49 : ℝ) * ((504 * 504) * 240))
        + ((48 : ℝ) * (((504 : ℝ) * (240 * 240)) * (24 : ℝ)))
        + ((((49 : ℝ) * ((240 * 240) * 240)) + ((25 : ℝ) * (504 * 504))) * (24 * 24))
    have hcoeff_shift :
        ∀ m : ℕ,
          |(coeffVarphiNum (m + 3) : ℝ)| ≤
            (C0 * (4 : ℝ) ^ (20 : ℕ)) * (((m + 1 : ℕ) : ℝ) ^ 20) := by
      intro m
      have h0 := abs_coeffVarphiNum_le_pow20 (n := m + 3)
      have hle_nat : m + 4 ≤ 4 * (m + 1) := by nlinarith
      have hle : ((m + 4 : ℕ) : ℝ) ≤ (4 : ℝ) * ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hle_nat
      have hpow :
          (((m + 4 : ℕ) : ℝ) ^ 20) ≤ (((4 : ℝ) * ((m + 1 : ℕ) : ℝ)) ^ 20) :=
        pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((m + 4 : ℕ) : ℝ)) hle 20
      linarith
    -- Apply the general summability lemma at `z = i`.
    let z0 : ℍ := ⟨(Complex.I : ℂ), by simp⟩
    have hs :
        Summable (fun m : ℕ => ‖((coeffVarphiNum (m + 3) : ℂ) * qterm z0 m)‖) := by
      refine summable_norm_qterm_mul_of_coeffBound (z := z0) (a := fun m => coeffVarphiNum (m + 3))
        (C := (C0 * (4 : ℝ) ^ (20 : ℕ))) (k := 20) ?_
      intro m
      exact hcoeff_shift m
    -- Rewrite `‖(a m) * qterm i m‖` into `‖a m‖ * exp(-2π m)`.
    refine hs.congr ?_
    intro m
    have hqterm :
        ‖qterm z0 m‖ = Real.exp (-(2 * Real.pi) * (m : ℝ)) := by
      -- `qterm i m = exp(-2π m)` so its norm is `exp(-2π m)`.
      simp [AppendixA.qterm, z0, Complex.norm_exp, mul_assoc]
    -- Finish.
    simp [a, hqterm, mul_assoc]
  -- Fourier expansion with shift `3` (using vanishing of the first coefficients).
  have hF :
      ∀ z : ℍ,
        varphi_num z =
          ∑' m : ℕ, a m * Complex.exp (2 * π * (Complex.I : ℂ) * ((m + 3 : ℕ) : ℂ) * (z : ℂ)) := by
    intro z
    have hq :
        varphi_num z = qseries (fun n : ℕ => (coeffVarphiNum n : ℂ)) z :=
      varphi_num_eq_qseries z
    -- Unfold `qseries` and shift the `tsum` by `3`.
    set f : ℕ → ℂ := fun n => (coeffVarphiNum n : ℂ) * qterm z n
    have hf_norm : Summable (fun n : ℕ => ‖f n‖) := by
      refine summable_norm_qterm_mul_of_coeffBound
        (z := z) (a := coeffVarphiNum) (C := ?_) (k := 20) ?_
      · exact
          ((25 : ℝ) * ((240 * 240) * (240 * 240)))
            + ((49 : ℝ) * ((504 * 504) * 240))
            + ((48 : ℝ) * (((504 : ℝ) * (240 * 240)) * (24 : ℝ)))
            + ((((49 : ℝ) * ((240 * 240) * 240)) + ((25 : ℝ) * (504 * 504))) * (24 * 24))
      · intro n
        simpa using! abs_coeffVarphiNum_le_pow20 (n := n)
    have hf : Summable f := (Summable.of_norm hf_norm)
    have hshift := (hf.sum_add_tsum_nat_add 3).symm
    have hfin : (∑ i ∈ Finset.range 3, f i) = 0 := by
      -- `range 3 = {0,1,2}` and the corresponding coefficients vanish.
      have hf0 : f 0 = 0 := by simp [f, coeffVarphiNum_zero]
      have hf1 : f 1 = 0 := by simp [f, coeffVarphiNum_one]
      have hf2 : f 2 = 0 := by simp [f, coeffVarphiNum_two]
      -- Evaluate the finite sum over `range 3`.
      simp [Finset.range_add_one, hf0, hf1, hf2]
    have htsum : (∑' n : ℕ, f n) = ∑' m : ℕ, f (m + 3) := by
      simpa [hfin] using! hshift
    -- Put everything together.
    have hq' : varphi_num z = ∑' n : ℕ, f n := by
      simpa [qseries, f] using! hq
    have hq'' : varphi_num z = ∑' m : ℕ, f (m + 3) := by
      simpa [htsum] using! hq'
    -- `qterm` is exactly the exponential term in the Fourier expansion.
    simpa [f, a, AppendixA.qterm, add_assoc, mul_assoc, mul_left_comm, mul_comm] using! hq''
  -- Apply the Fourier-shift bound.
  have hbig :=
    isBigO_atImInfty_of_fourier_shift (F := varphi_num) (a := a) (n₀ := 3) (c := 1)
      hF ha_sum
  simpa [mul_assoc, mul_left_comm, mul_comm] using! hbig

/-- Exponential decay of `varphi` at `i∞`, stated as a Big-O bound in terms of `exp(-2π · im z)`. -/
public theorem varphi_isBigO_exp_neg_two_pi :
    varphi =O[atImInfty] fun z : ℍ => Real.exp (-(2 * Real.pi) * z.im) := by
  -- `varphi = varphi_num / Δ^2` and combine asymptotics.
  have hnum :
      varphi_num =O[atImInfty] fun z : ℍ => Real.exp (-(2 * Real.pi * (3 : ℝ)) * z.im) :=
    varphi_num_isBigO_exp_neg_six_pi
  have hΔθ : (fun z : ℍ => Δ z) =Θ[atImInfty] fun z : ℍ => Real.exp (-2 * Real.pi * z.im) := by
    simpa [Delta_apply] using!
      (Delta_isTheta_rexp :
        Delta =Θ[atImInfty] fun τ => Real.exp (-2 * Real.pi * τ.im))
  have hΔ2θ :
      (fun z : ℍ => (Δ z) ^ (2 : ℕ)) =Θ[atImInfty] fun z : ℍ =>
        (Real.exp (-2 * Real.pi * z.im)) ^ (2 : ℕ) :=
    hΔθ.pow 2
  have hΔ2invO :
      (fun z : ℍ => ((Δ z) ^ (2 : ℕ))⁻¹) =O[atImInfty] fun z : ℍ =>
        ((Real.exp (-2 * Real.pi * z.im)) ^ (2 : ℕ))⁻¹ := by
    simpa using! (hΔ2θ.inv).isBigO
  have hmul :
      (fun z : ℍ => varphi z) = fun z : ℍ => varphi_num z * ((Δ z) ^ (2 : ℕ))⁻¹ := by
    funext z
    simp [Dim24.varphi, varphi_num, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hbig :
      (fun z : ℍ => varphi_num z * ((Δ z) ^ (2 : ℕ))⁻¹) =O[atImInfty]
        fun z : ℍ =>
          Real.exp (-(2 * Real.pi * (3 : ℝ)) * z.im) *
            ((Real.exp (-2 * Real.pi * z.im)) ^ (2 : ℕ))⁻¹ :=
    hnum.mul hΔ2invO
  have hsimp :
      (fun z : ℍ =>
          Real.exp (-(2 * π * 3 * z.im)) * (Real.exp (-(2 * π * z.im)) ^ (2 : ℕ))⁻¹) =
        fun z : ℍ => Real.exp (-(2 * π * z.im)) := by
    funext z
    set x : ℝ := 2 * π * z.im
    have hx3 : Real.exp (-(2 * π * 3 * z.im)) = Real.exp (-(3 * x)) := by
      simp [x]
      ring
    have hx1 : Real.exp (-(2 * π * z.im)) = Real.exp (-x) := by
      simp [x, mul_assoc, mul_left_comm, mul_comm]
    have hx2 : (Real.exp (-x) ^ (2 : ℕ))⁻¹ = Real.exp (2 * x) := by
      have hx2' : Real.exp (-x) ^ (2 : ℕ) = Real.exp (-(2 * x)) := by
        calc
          Real.exp (-x) ^ (2 : ℕ) = Real.exp (-x) * Real.exp (-x) := by simp [pow_two]
          _ = Real.exp (-x + -x) := by simpa using! (Real.exp_add (-x) (-x)).symm
          _ = Real.exp (-(2 * x)) := by ring_nf
      have hexp : Real.exp (-(2 * x)) = (Real.exp (2 * x))⁻¹ := by
        simpa using! (Real.exp_neg (2 * x))
      have := congrArg Inv.inv hexp
      simpa [hx2', inv_inv] using! this
    calc
      Real.exp (-(2 * π * 3 * z.im)) * (Real.exp (-(2 * π * z.im)) ^ (2 : ℕ))⁻¹
          = Real.exp (-(3 * x)) * (Real.exp (-x) ^ (2 : ℕ))⁻¹ := by
              simp [hx3, hx1]
      _ = Real.exp (-(3 * x)) * Real.exp (2 * x) := by simp [hx2]
      _ = Real.exp (-(3 * x) + 2 * x) := by
            simpa using! (Real.exp_add (-(3 * x)) (2 * x)).symm
      _ = Real.exp (-x) := by ring_nf
      _ = Real.exp (-(2 * π * z.im)) := by simp [x]
  -- Return to `Real.exp`.
  simpa [hmul, hsimp] using! hbig

/-- As `z → i∞`, the modular form `varphi z` tends to `0`. -/
public lemma tendsto_varphi_atImInfty :
    Tendsto (varphi : ℍ → ℂ) atImInfty (nhds 0) := by
  have hbig :
      (varphi : ℍ → ℂ) =O[atImInfty] fun z : ℍ => Real.exp (-(2 * Real.pi) * z.im) :=
    varphi_isBigO_exp_neg_two_pi
  have him : Tendsto (fun z : ℍ => z.im) atImInfty atTop :=
    Filter.tendsto_im_atImInfty
  have hlin : Tendsto (fun x : ℝ => (-(2 * Real.pi) : ℝ) * x) atTop atBot :=
    (tendsto_id.const_mul_atTop_of_neg (by nlinarith [Real.two_pi_pos]))
  have hexp : Tendsto (fun z : ℍ => Real.exp (-(2 * Real.pi) * z.im)) atImInfty (nhds 0) :=
    (Real.tendsto_exp_atBot.comp (hlin.comp him))
  exact hbig.trans_tendsto hexp

end VarphiBounds

end

end SpherePacking.Dim24
