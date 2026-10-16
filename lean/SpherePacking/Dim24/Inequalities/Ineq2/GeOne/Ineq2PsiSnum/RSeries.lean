-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.RBounds
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Tactic.Ring


/-!
# `r`-series infrastructure for the `ψS_num` truncation

We view (the relevant specializations of) theta expressions on the imaginary axis as absolutely
convergent power series in `r(t) = exp(-πt)`.

## Main definitions
* `rseries`
* `convZ`

## Main statements
* `rseries_mul_cast`
-/

noncomputable section

namespace SpherePacking.Dim24


namespace Ineq2PsiSnum

open scoped BigOperators

/-- The `r`-series `∑ a_n * r(t)^n` evaluated in `ℂ`. -/
@[expose] public def rseries (a : ℕ → ℤ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, (a n : ℂ) * ((AppendixA.r t : ℂ) ^ n)

/-- Convolution of integer coefficient functions (Cauchy product coefficients). -/
@[expose] public def convZ (a b : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2

/--
Cauchy product for `rseries`: multiplication corresponds to convolution of coefficients, assuming
absolute summability of both series.
-/
public lemma rseries_mul_cast (t : ℝ) (a b : ℕ → ℤ)
    (ha : Summable (fun n : ℕ => ‖((a n : ℂ) * ((AppendixA.r t : ℂ) ^ n))‖))
    (hb : Summable (fun n : ℕ => ‖((b n : ℂ) * ((AppendixA.r t : ℂ) ^ n))‖)) :
    (rseries a t) * (rseries b t) = rseries (convZ a b) t := by
  let f : ℕ → ℂ := fun n => (a n : ℂ) * ((AppendixA.r t : ℂ) ^ n)
  let g : ℕ → ℂ := fun n => (b n : ℂ) * ((AppendixA.r t : ℂ) ^ n)
  have hf : Summable (fun n : ℕ => ‖f n‖) := by simpa [f] using! ha
  have hg : Summable (fun n : ℕ => ‖g n‖) := by simpa [g] using! hb
  have hprod :
      (∑' n : ℕ, f n) * (∑' n : ℕ, g n) =
        ∑' m : ℕ, ∑ p ∈ Finset.antidiagonal m, f p.1 * g p.2 := by
    simpa using! (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg)
  have hanti (m : ℕ) :
      (∑ p ∈ Finset.antidiagonal m, f p.1 * g p.2) =
        (convZ a b m : ℂ) * ((AppendixA.r t : ℂ) ^ m) := by
    have hmul (p : ℕ × ℕ) (hp : p ∈ Finset.antidiagonal m) :
        f p.1 * g p.2 = ((a p.1 : ℂ) * (b p.2 : ℂ)) * ((AppendixA.r t : ℂ) ^ m) := by
      have hm : p.1 + p.2 = m := by
        simpa [Finset.mem_antidiagonal] using! hp
      grind only
    calc
      (∑ p ∈ Finset.antidiagonal m, f p.1 * g p.2)
          = ∑ p ∈ Finset.antidiagonal m, ((a p.1 : ℂ) * (b p.2 : ℂ)) *
              ((AppendixA.r t : ℂ) ^ m) := by
              exact Finset.sum_congr rfl hmul
        _ =
            (∑ p ∈ Finset.antidiagonal m, (a p.1 : ℂ) * (b p.2 : ℂ)) *
              ((AppendixA.r t : ℂ) ^ m) := by
                simp [Finset.sum_mul, mul_assoc]
        _ = (convZ a b m : ℂ) * ((AppendixA.r t : ℂ) ^ m) := by
              simp [convZ]
  have hanti' :
      (fun m : ℕ => ∑ p ∈ Finset.antidiagonal m, f p.1 * g p.2) =
        fun m : ℕ => (convZ a b m : ℂ) * ((AppendixA.r t : ℂ) ^ m) := by
      funext m
      simp [hanti m]
  have hf_tsum : (∑' n : ℕ, f n) = rseries a t := by
    simp [rseries, f]
  have hg_tsum : (∑' n : ℕ, g n) = rseries b t := by
    simp [rseries, g]
  have hconv_tsum :
      (∑' m : ℕ, (convZ a b m : ℂ) * ((AppendixA.r t : ℂ) ^ m)) =
        rseries (convZ a b) t := by
    simp [rseries]
  simpa [hf_tsum, hg_tsum, hconv_tsum, hanti'] using! hprod

end SpherePacking.Dim24.Ineq2PsiSnum
