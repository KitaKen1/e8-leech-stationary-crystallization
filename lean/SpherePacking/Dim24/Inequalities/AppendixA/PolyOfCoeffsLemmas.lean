/-
Lemmas about `AppendixA.polyOfCoeffs` needed for Appendix A inequality arguments.

These are lightweight, self-contained facts used to turn coefficient lists into explicit
finite sums, and to extract coefficients.
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.Basic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset


/-!
`absBound` and the basic tail estimate for `polyOfCoeffs`.

We use the recursion `polyOfCoeffs (a :: l) = C a + X * polyOfCoeffs l`, so evaluation satisfies
`eval (a :: l) = a + x * eval l`. This makes it easy to bound `|eval|` on `|x| ≤ c`.
-/


open scoped BigOperators

namespace SpherePacking.Dim24.AppendixA

noncomputable section

/-- The coefficient of `polyOfCoeffs l` at `n` is `l.getD n 0`. -/
public lemma polyOfCoeffs_coeff_getD (l : List ℚ) (n : ℕ) :
    (polyOfCoeffs l).coeff n = l.getD n 0 := by
  induction l generalizing n with
  | nil =>
      simp [polyOfCoeffs]
  | cons a l ih =>
      cases n with
      | zero => simp [polyOfCoeffs]
      | succ n => simp [polyOfCoeffs, ih]

/-- If the head coefficient is `0`, then `polyOfCoeffs` factors out `X`. -/
public lemma polyOfCoeffs_zero_cons (l : List ℚ) :
    polyOfCoeffs (0 :: l) = Polynomial.X * polyOfCoeffs l := by
  simp [polyOfCoeffs]


/--
`absBound l c` is the explicit bound `∑ |aᵢ| * c^i` corresponding to a coefficient list `l`.

It is used to bound `|(polyOfCoeffs l).eval₂ _ x|` on `|x| ≤ c`.
-/
@[expose]
public def absBound : List ℚ → ℝ → ℝ
  | [], _ => 0
  | a :: l, c => |(algebraMap ℚ ℝ) a| + c * absBound l c

@[simp] public lemma absBound_nil (c : ℝ) : absBound [] c = 0 := rfl

@[simp] public lemma absBound_cons (a : ℚ) (l : List ℚ) (c : ℝ) :
    absBound (a :: l) c = |(algebraMap ℚ ℝ) a| + c * absBound l c := rfl

/-- `absBound` is nonnegative when `c ≥ 0`. -/
public lemma absBound_nonneg (l : List ℚ) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ absBound l c := by
  induction l with
  | nil => simp [absBound]
  | cons a l ih =>
      exact add_nonneg (abs_nonneg ((algebraMap ℚ ℝ) a)) (mul_nonneg hc ih)

/-- Evaluation recursion for `polyOfCoeffs` on a cons list. -/
public lemma eval₂_polyOfCoeffs_cons (a : ℚ) (l : List ℚ) (x : ℝ) :
    (polyOfCoeffs (a :: l)).eval₂ (algebraMap ℚ ℝ) x =
      (algebraMap ℚ ℝ) a + x * (polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) x := by
  simp [polyOfCoeffs]

/-- Expand `(polyOfCoeffs l).eval₂` as a finite sum over `l.getD n 0`. -/
public lemma eval₂_polyOfCoeffs_eq_sum_range_getD (l : List ℚ) (x : ℝ) :
    (polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) x =
      ∑ n ∈ Finset.range l.length, (algebraMap ℚ ℝ) (l.getD n 0) * x ^ n := by
  induction l with
  | nil => simp [polyOfCoeffs]
  | cons a l ih =>
      simp [polyOfCoeffs, ih, Finset.sum_range_succ', Finset.mul_sum, pow_succ, mul_assoc, mul_comm,
        add_comm]

/-- Bound `|(polyOfCoeffs l).eval₂ _ x|` by `absBound l c` when `|x| ≤ c` and `c ≥ 0`. -/
public lemma abs_eval₂_polyOfCoeffs_le_absBound (l : List ℚ) {x c : ℝ} (hc : 0 ≤ c)
    (hx : |x| ≤ c) :
    |(polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) x| ≤ absBound l c := by
  induction l with
  | nil =>
      simp [polyOfCoeffs, absBound]
  | cons a l ih =>
      have htail : |(polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) x| ≤ absBound l c := ih
      have hmul : |x| * |(polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) x| ≤ c * absBound l c :=
        mul_le_mul hx htail (abs_nonneg _) hc
      have htri :
          |(polyOfCoeffs (a :: l)).eval₂ (algebraMap ℚ ℝ) x| ≤
            |(algebraMap ℚ ℝ) a| + |x| * |(polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) x| := by
        simpa [eval₂_polyOfCoeffs_cons, abs_mul, mul_assoc] using!
          abs_add_le ((algebraMap ℚ ℝ) a) (x * (polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) x)
      have htri' :
          |(polyOfCoeffs (a :: l)).eval₂ (algebraMap ℚ ℝ) x| ≤
            |(algebraMap ℚ ℝ) a| + c * absBound l c := le_add_of_le_add_left htri hmul
      simpa [absBound, add_assoc, add_left_comm, add_comm, mul_assoc] using! htri'

/--
Lower bound for `(polyOfCoeffs (a :: l)).eval₂ _ x` on `0 ≤ x ≤ c` in terms of the head coefficient
`a` and the tail bound `absBound l c`.
-/
public lemma eval₂_polyOfCoeffs_ge_sub_absBound (a : ℚ) (l : List ℚ) {x c : ℝ} (hx0 : 0 ≤ x)
    (hc : 0 ≤ c) (hx : x ≤ c) :
    (polyOfCoeffs (a :: l)).eval₂ (algebraMap ℚ ℝ) x ≥
      (algebraMap ℚ ℝ) a - c * absBound l c := by
  have hxabs : |x| ≤ c := by simpa [abs_of_nonneg hx0] using! hx
  have htail : |(polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) x| ≤ absBound l c :=
    abs_eval₂_polyOfCoeffs_le_absBound (l := l) hc hxabs
  have hx_mul : x * |(polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) x| ≤ c * absBound l c :=
    mul_le_mul hx htail (abs_nonneg _) hc
  have hneg :
      -(x * |(polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) x|) ≤
        x * (polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) x := by
    simpa [abs_mul, abs_of_nonneg hx0, mul_assoc] using!
      (neg_abs_le (x * (polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) x))
  have hmain :
      (algebraMap ℚ ℝ) a - x * |(polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) x| ≤
        (polyOfCoeffs (a :: l)).eval₂ (algebraMap ℚ ℝ) x := by
    have := add_le_add_left hneg ((algebraMap ℚ ℝ) a)
    simpa [eval₂_polyOfCoeffs_cons, sub_eq_add_neg, add_assoc] using! this
  have hsub :
      (algebraMap ℚ ℝ) a - c * absBound l c ≤
        (algebraMap ℚ ℝ) a - x * |(polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) x| :=
    sub_le_sub_left hx_mul ((algebraMap ℚ ℝ) a)
  exact le_trans hsub hmain

/-!
### Sign lemmas for coefficient lists

These are used to replace the PARI/GP "Sturm check" steps in Appendix A by simple
monotonicity/sign arguments when all coefficients have the same sign.
-/

/-- If all coefficients are nonpositive and `x ≥ 0`, then `(polyOfCoeffs l).eval₂ _ x ≤ 0`. -/
public lemma eval₂_polyOfCoeffs_nonpos_of_forall_coeff_nonpos (l : List ℚ) {x : ℝ} (hx : 0 ≤ x)
    (hl : ∀ c ∈ l, c ≤ 0) :
    (polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) x ≤ 0 := by
  induction l with
  | nil =>
      simp [polyOfCoeffs]
  | cons c l ih =>
      have hc0 : (algebraMap ℚ ℝ c) ≤ 0 := by
        have : (c : ℝ) ≤ 0 := by exact_mod_cast (hl c (by simp) : c ≤ 0)
        simpa using! this
      have hl' : ∀ c' ∈ l, c' ≤ 0 := by
        intro c' hc'
        exact hl c' (by simp [hc'])
      have hx_mul : x * (polyOfCoeffs l).eval₂ (algebraMap ℚ ℝ) x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hx (ih hl')
      simpa [eval₂_polyOfCoeffs_cons, add_assoc, add_comm, add_left_comm, mul_assoc] using!
        add_nonpos hc0 hx_mul

end

end SpherePacking.Dim24.AppendixA
