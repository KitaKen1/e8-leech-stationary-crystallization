-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.VarphiTable
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.Phi1CoreTable
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.Phi2CoreTable
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.CoeffMatchingLemmas


/-!
Table-based simp lemmas for `coeffQ` on the `q`-series lists used in Appendix A.

This module is intentionally lightweight (it does not import the heavy `PsiTable` certificate),
so other developments can use the table rewrites without depending on that table.
-/

namespace SpherePacking.Dim24.AppendixA.BleadingCoeffs
/-
We expose these as `simp` lemmas with an `if` guard, so that for concrete indices the guard reduces
by computation.
-/

private lemma coeffQ_eq_zero_of_QN_le {l : List ℚ} (hlen : l.length = QN) {n : ℕ} (hn : QN ≤ n) :
    coeffQ l n = 0 := by
  have : l.length ≤ n := by simpa [hlen] using! hn
  simpa [coeffQ] using! List.getD_eq_default (l := l) (d := (0 : ℚ)) (n := n) this

/--
Rewrite `coeffQ phinumQ n` using the precomputed `varphiNumCoeffsZ_table`.

The `if n < QN` guard ensures this reduces by computation for concrete indices.
-/
@[simp] public lemma coeffQ_phinumQ_eq_table (n : ℕ) :
    coeffQ phinumQ n =
      if n < QN then (varphiNumCoeffsZ_table.getD n 0 : ℚ) else 0 := by
  by_cases hn : n < QN
  · simpa [hn] using!
      (SpherePacking.Dim24.AppendixA.coeffQ_phinumQ_eq (n := n) hn).trans
        (coeffVarphiNum_eq_table (n := n) (hn := by simpa using! hn))
  · have hlen : phinumQ.length = QN := by simp [phinumQ, addQ, QN]
    simpa [hn] using!
      coeffQ_eq_zero_of_QN_le (l := phinumQ) hlen (Nat.le_of_not_gt hn)

/--
Rewrite `coeffQ phi2CoreQ n` using the precomputed `phi2CoreCoeffsZ_table`.

The `if n < QN` guard ensures this reduces by computation for concrete indices.
-/
@[simp] public lemma coeffQ_phi2CoreQ_eq_table (n : ℕ) :
    coeffQ phi2CoreQ n =
      if n < QN then (phi2CoreCoeffsZ_table.getD n 0 : ℚ) else 0 := by
  by_cases hn : n < QN
  · simpa [hn] using!
      (SpherePacking.Dim24.AppendixA.coeffQ_phi2CoreQ_eq (n := n) hn).trans
        (coeffPhi2Core_eq_table (n := n) (hn := by simpa using! hn))
  · have hlen : phi2CoreQ.length = QN := by simp [phi2CoreQ, addQ, QN]
    simpa [hn] using!
      coeffQ_eq_zero_of_QN_le (l := phi2CoreQ) hlen (Nat.le_of_not_gt hn)

/--
Rewrite `coeffQ phi1CoreQ n` using the precomputed `phi1CoreCoeffsZ_table`.

The `if n < QN` guard ensures this reduces by computation for concrete indices.
-/
@[simp] public lemma coeffQ_phi1CoreQ_eq_table (n : ℕ) :
    coeffQ phi1CoreQ n =
      if n < QN then (phi1CoreCoeffsZ_table.getD n 0 : ℚ) else 0 := by
  by_cases hn : n < QN
  · simpa [hn] using!
      (SpherePacking.Dim24.AppendixA.coeffQ_phi1CoreQ_eq (n := n) hn).trans
        (coeffPhi1Core_eq_table (n := n) (hn := by simpa using! hn))
  · have hlen : phi1CoreQ.length = QN := by simp [phi1CoreQ, addQ, QN]
    simpa [hn] using!
      coeffQ_eq_zero_of_QN_le (l := phi1CoreQ) hlen (Nat.le_of_not_gt hn)

end SpherePacking.Dim24.AppendixA.BleadingCoeffs
