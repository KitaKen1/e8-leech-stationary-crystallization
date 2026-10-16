-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.NumTailBound.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


/-!
# Triangle inequality for `ineq2_num_tail`

This file expresses `ineq2_num_tail` as the sum of its four series-tail components and applies the
triangle inequality to bound its norm by the sum of the norms of those components.

## Main statements
* `ineq2_num_tail_norm_le_sum_terms`

-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.Ineq2LeOneTruncAux

open AppendixA
open ExactTrunc
open BleadingCoeffs

namespace NumTailBound

/-- Triangle-inequality bound for `‖ineq2_num_tail t ht0‖` by the sum of the norms of its four
component tail terms. -/
public lemma ineq2_num_tail_norm_le_sum_terms (t : ℝ) (ht0 : 0 < t) :
    ‖ineq2_num_tail t ht0‖ ≤
        ‖((t : ℂ) ^ (2 : ℕ)) *
            AppendixA.qtail (fun n : ℕ => (AppendixA.coeffVarphiNum n : ℂ)) (it t ht0) QN‖
        + ‖(t : ℂ) * ((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
            AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi1Core n : ℂ)) (it t ht0) QN‖
        + ‖((36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
            AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi2Core n : ℂ)) (it t ht0) QN‖
        + ‖(432 / (Real.pi ^ 2) : ℂ) * AppendixA.rtail AppendixA.psiCoeffFun t N‖ := by
  set z : ℍ := it t ht0
  set a : ℂ :=
    ((t : ℂ) ^ (2 : ℕ)) *
      AppendixA.qtail (fun n : ℕ => (AppendixA.coeffVarphiNum n : ℂ)) z QN
  set b : ℂ :=
    (t : ℂ) * ((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
      AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi1Core n : ℂ)) z QN
  set c : ℂ :=
    ((36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
      AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi2Core n : ℂ)) z QN
  set d : ℂ := (432 / (Real.pi ^ 2) : ℂ) * AppendixA.rtail AppendixA.psiCoeffFun t N
  have hdef : ineq2_num_tail t ht0 = a + b + c + d := by
    simp [ineq2_num_tail, z, a, b, c, d]
  have hab : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have habc : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    norm_add₃_le
  have habcd : ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ := by
    simpa [add_assoc] using! (norm_add_le (a + b + c) d)
  grind only

end SpherePacking.Dim24.Ineq2LeOneTruncAux.NumTailBound
