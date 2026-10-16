-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum


/-!
Reusable multiplication lemmas for Appendix A `q`-series.

This file provides a Cauchy-product lemma for `qseries` (via antidiagonals) specialized to
`ℚ`-valued coefficients, mirroring the computations in `appendix.txt` without importing any
additional helper modules.
-/


open scoped BigOperators
open UpperHalfPlane

namespace SpherePacking.Dim24.AppendixA

noncomputable section

/-- `qseries` multiplication for `ℚ`-valued coefficients, assuming absolute summability. -/
public lemma qseries_mul_cast (z : ℍ) (a b : ℕ → ℚ)
    (ha : Summable (fun n : ℕ => ‖((a n : ℂ) * qterm z n)‖))
    (hb : Summable (fun n : ℕ => ‖((b n : ℂ) * qterm z n)‖)) :
    (qseries (fun n : ℕ => (a n : ℂ)) z) * (qseries (fun n : ℕ => (b n : ℂ)) z) =
      qseries (fun m : ℕ => (conv a b m : ℂ)) z := by
  -- Apply Cauchy product on the term functions.
  let f : ℕ → ℂ := fun n => (a n : ℂ) * qterm z n
  let g : ℕ → ℂ := fun n => (b n : ℂ) * qterm z n
  have hf : Summable (fun n : ℕ => ‖f n‖) := by simpa [f] using! ha
  have hg : Summable (fun n : ℕ => ‖g n‖) := by simpa [g] using! hb
  have hprod :
      (∑' n : ℕ, f n) * (∑' n : ℕ, g n) =
        ∑' m : ℕ, ∑ p ∈ Finset.antidiagonal m, f p.1 * g p.2 := by
    simpa using! (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg)
  -- Rewrite the antidiagonal terms.
  have hanti : ∀ m : ℕ,
      (∑ p ∈ Finset.antidiagonal m, f p.1 * g p.2) =
        (conv a b m : ℂ) * qterm z m := by
    intro m
    calc
      (∑ p ∈ Finset.antidiagonal m, f p.1 * g p.2)
          = ∑ p ∈ Finset.antidiagonal m, ((a p.1 : ℂ) * (b p.2 : ℂ)) * qterm z m := by
              refine Finset.sum_congr rfl ?_
              intro p hp
              have hm : p.1 + p.2 = m := by simpa [Finset.mem_antidiagonal] using! hp
              dsimp [f, g]
              ring_nf
              simp [qterm_mul, hm, mul_assoc, mul_left_comm, mul_comm]
      _ = (∑ p ∈ Finset.antidiagonal m, (a p.1 : ℂ) * (b p.2 : ℂ)) * qterm z m := by
            simp [Finset.sum_mul, mul_assoc]
      _ = (conv a b m : ℂ) * qterm z m := by simp [conv]
  simpa [qseries, f, g, hanti] using! hprod

end

end SpherePacking.Dim24.AppendixA
