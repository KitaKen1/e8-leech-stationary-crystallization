-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.EvenReindex
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.SeriesSplit
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.CoeffMatchingLemmas
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.VarphiQSeries
public import SpherePacking.Dim24.Inequalities.AppendixA.PolyOfCoeffsLemmas
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeries
public import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity


/-!
Power comparisons used in the `t ≤ 1` tail bound.

These lemmas convert (postTransparency := .instances) high powers (such as `x^100`) into a product of a small power (`x^12`) and an
explicit factor `(1/23)^88` when `0 ≤ x ≤ 1/23`, and similarly handle extra factors of `t` or
`t^2` under the constraint `t * x ≤ 1/23`.
-/

namespace SpherePacking.Dim24.AppendixA

noncomputable section

namespace VarphiLeOne

open BleadingCoeffs

/-- For `0 ≤ x ≤ 1/23`, rewrite `x^100` as a bounded multiple of `x^12`. -/
public lemma pow100_le_one_div_23_pow88_mul_pow12 (x : ℝ) (hx0 : 0 ≤ x)
    (hxle : x ≤ (1 / 23 : ℝ)) :
    x ^ (100 : ℕ) ≤ (1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ) := by
  have hxpow88 : x ^ (88 : ℕ) ≤ (1 / 23 : ℝ) ^ (88 : ℕ) := pow_le_pow_left₀ hx0 hxle _
  have hx12 : 0 ≤ x ^ (12 : ℕ) := pow_nonneg hx0 _
  calc
    x ^ (100 : ℕ) = x ^ (12 : ℕ) * x ^ (88 : ℕ) := by
      simpa [show (12 : ℕ) + 88 = 100 by decide] using! (pow_add x 12 88)
    _ ≤ x ^ (12 : ℕ) * (1 / 23 : ℝ) ^ (88 : ℕ) := mul_le_mul_of_nonneg_left hxpow88 hx12
    _ = (1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ) := by ac_rfl

/-- Variant of `pow100_le_one_div_23_pow88_mul_pow12` with an extra factor of `t`. -/
public lemma t_mul_pow100_le_one_div_23_pow88_mul_pow12 (t x : ℝ) (hx0 : 0 ≤ x)
    (hxle : x ≤ (1 / 23 : ℝ)) (htxle : t * x ≤ (1 / 23 : ℝ)) (htx0 : 0 ≤ t * x) :
    t * x ^ (100 : ℕ) ≤ (1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ) := by
  have hxpow87 : x ^ (87 : ℕ) ≤ (1 / 23 : ℝ) ^ (87 : ℕ) := pow_le_pow_left₀ hx0 hxle _
  have hx12 : 0 ≤ x ^ (12 : ℕ) := pow_nonneg hx0 _
  have h23 : 0 ≤ (1 / 23 : ℝ) := by norm_num
  have hfac0 : 0 ≤ x ^ (12 : ℕ) * (1 / 23 : ℝ) ^ (87 : ℕ) :=
    mul_nonneg hx12 (pow_nonneg h23 _)
  have hx12_mul :
      x ^ (12 : ℕ) * x ^ (87 : ℕ) ≤ x ^ (12 : ℕ) * (1 / 23 : ℝ) ^ (87 : ℕ) :=
    mul_le_mul_of_nonneg_left hxpow87 hx12
  have hdecomp : t * x ^ (100 : ℕ) = (t * x) * (x ^ (12 : ℕ) * x ^ (87 : ℕ)) := by
    ring
  have hpow : (1 / 23 : ℝ) * (1 / 23 : ℝ) ^ (87 : ℕ) = (1 / 23 : ℝ) ^ (88 : ℕ) := by
    simpa [mul_comm] using! (pow_succ (1 / 23 : ℝ) 87).symm
  calc
    t * x ^ (100 : ℕ) = (t * x) * (x ^ (12 : ℕ) * x ^ (87 : ℕ)) := hdecomp
    _ ≤ (t * x) * (x ^ (12 : ℕ) * (1 / 23 : ℝ) ^ (87 : ℕ)) :=
      mul_le_mul_of_nonneg_left hx12_mul htx0
    _ ≤ (1 / 23 : ℝ) * (x ^ (12 : ℕ) * (1 / 23 : ℝ) ^ (87 : ℕ)) :=
      mul_le_mul_of_nonneg_right htxle hfac0
    _ = (1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ) := by
      ring

/-- Variant of `pow100_le_one_div_23_pow88_mul_pow12` with an extra factor of `t^2`. -/
public lemma t_sq_mul_pow100_le_one_div_23_pow88_mul_pow12 (t x : ℝ) (hx0 : 0 ≤ x)
    (hxle : x ≤ (1 / 23 : ℝ)) (htxle : t * x ≤ (1 / 23 : ℝ)) (htx0 : 0 ≤ t * x) :
    t ^ (2 : ℕ) * x ^ (100 : ℕ) ≤ (1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ) := by
  have hxpow86 : x ^ (86 : ℕ) ≤ (1 / 23 : ℝ) ^ (86 : ℕ) := pow_le_pow_left₀ hx0 hxle _
  have hx12 : 0 ≤ x ^ (12 : ℕ) := pow_nonneg hx0 _
  have hx98_le : x ^ (98 : ℕ) ≤ (1 / 23 : ℝ) ^ (86 : ℕ) * x ^ (12 : ℕ) := by
    calc
      x ^ (98 : ℕ) = x ^ (12 : ℕ) * x ^ (86 : ℕ) := by
        simpa [show (12 : ℕ) + 86 = 98 by decide] using! (pow_add x 12 86)
      _ ≤ x ^ (12 : ℕ) * (1 / 23 : ℝ) ^ (86 : ℕ) := mul_le_mul_of_nonneg_left hxpow86 hx12
      _ = (1 / 23 : ℝ) ^ (86 : ℕ) * x ^ (12 : ℕ) := by ac_rfl
  have htx_sq : (t * x) ^ (2 : ℕ) ≤ (1 / 23 : ℝ) ^ (2 : ℕ) :=
    pow_le_pow_left₀ htx0 htxle _
  have h23 : 0 ≤ (1 / 23 : ℝ) := by norm_num
  have htx2 : t ^ (2 : ℕ) * x ^ (100 : ℕ) = (t * x) ^ (2 : ℕ) * x ^ (98 : ℕ) := by
    ring
  have hpow : (1 / 23 : ℝ) ^ (2 : ℕ) * (1 / 23 : ℝ) ^ (86 : ℕ) = (1 / 23 : ℝ) ^ (88 : ℕ) := by
    simpa [show (2 : ℕ) + 86 = 88 by decide] using! (pow_add (1 / 23 : ℝ) 2 86).symm
  calc
    t ^ (2 : ℕ) * x ^ (100 : ℕ) = (t * x) ^ (2 : ℕ) * x ^ (98 : ℕ) := htx2
    _ ≤ (1 / 23 : ℝ) ^ (2 : ℕ) * x ^ (98 : ℕ) :=
      mul_le_mul_of_nonneg_right htx_sq (pow_nonneg hx0 _)
    _ ≤ (1 / 23 : ℝ) ^ (2 : ℕ) * ((1 / 23 : ℝ) ^ (86 : ℕ) * x ^ (12 : ℕ)) :=
      mul_le_mul_of_nonneg_left hx98_le (pow_nonneg h23 _)
    _ = (1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ) := by
      calc
        (1 / 23 : ℝ) ^ (2 : ℕ) * ((1 / 23 : ℝ) ^ (86 : ℕ) * x ^ (12 : ℕ)) =
            ((1 / 23 : ℝ) ^ (2 : ℕ) * (1 / 23 : ℝ) ^ (86 : ℕ)) * x ^ (12 : ℕ) := by ac_rfl
        _ = (1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ) :=
          congrArg (fun y : ℝ => y * x ^ (12 : ℕ)) hpow

end VarphiLeOne

end

end SpherePacking.Dim24.AppendixA
