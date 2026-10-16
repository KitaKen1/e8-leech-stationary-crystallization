-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.NumTailBound.Defs
import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.NumTailBound.TailTermBounds
import SpherePacking.Dim24.Inequalities.Ineq2.LeOne.TruncAux.NumTailBound.TailTriangle


/-!
# Norm bound for `ineq2_num_tail`

This file proves the final tail estimate for the cleared numerator:
for `t ≥ 1`, the norm of the tail part `ineq2_num_tail t ht0` is bounded by `eps * r(t)^12`.

The proof combines the triangle inequality (`TailTriangle`) with the individual term bounds
(`TailTermBounds`).

## Main statements
* `ineq2_num_tail_norm_le`

-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.Ineq2LeOneTruncAux

open AppendixA
open ExactTrunc
open BleadingCoeffs

namespace NumTailBound

/-- For `t ≥ 1`, the tail part `ineq2_num_tail t ht0` is bounded by `eps * r(t)^12` in norm. -/
public lemma ineq2_num_tail_norm_le (t : ℝ) (ht : 1 ≤ t) :
    let ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    ‖ineq2_num_tail t ht0‖ ≤ AppendixA.eps * (AppendixA.r t) ^ (12 : ℕ) := by
  intro ht0
  have htri : ‖ineq2_num_tail t ht0‖ ≤
        ‖((t : ℂ) ^ (2 : ℕ)) *
            AppendixA.qtail (fun n : ℕ => (AppendixA.coeffVarphiNum n : ℂ)) (it t ht0) QN‖
        + ‖(t : ℂ) * ((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
            AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi1Core n : ℂ)) (it t ht0) QN‖
        + ‖((36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
            AppendixA.qtail (fun n : ℕ => (AppendixA.coeffPhi2Core n : ℂ)) (it t ht0) QN‖
        + ‖(432 / (Real.pi ^ 2) : ℂ) * AppendixA.rtail AppendixA.psiCoeffFun t N‖ :=
    ineq2_num_tail_norm_le_sum_terms (t := t) ht0
  have hvarphi := varphi_term_norm_le (t := t) ht ht0
  have hphi1 := phi1_term_norm_le (t := t) ht ht0
  have hphi2 := phi2_term_norm_le (t := t) ht ht0
  have hpsi := psi_term_norm_le (t := t) ht ht0
  have hsum :
      ‖ineq2_num_tail t ht0‖ ≤
        (AppendixA.eps / 4) * (AppendixA.r t) ^ (12 : ℕ) +
        (AppendixA.eps / 4) * (AppendixA.r t) ^ (12 : ℕ) +
        (AppendixA.eps / 4) * (AppendixA.r t) ^ (12 : ℕ) +
        (AppendixA.eps / 4) * (AppendixA.r t) ^ (12 : ℕ) :=
    le_trans htri (add_le_add (add_le_add (add_le_add hvarphi hphi1) hphi2) hpsi)
  have hfour :
      (AppendixA.eps / 4) * (AppendixA.r t) ^ (12 : ℕ) +
          (AppendixA.eps / 4) * (AppendixA.r t) ^ (12 : ℕ) +
          (AppendixA.eps / 4) * (AppendixA.r t) ^ (12 : ℕ) +
          (AppendixA.eps / 4) * (AppendixA.r t) ^ (12 : ℕ) =
        AppendixA.eps * (AppendixA.r t) ^ (12 : ℕ) := by
    ring_nf
  simpa [hfour] using! hsum

end SpherePacking.Dim24.Ineq2LeOneTruncAux.NumTailBound
