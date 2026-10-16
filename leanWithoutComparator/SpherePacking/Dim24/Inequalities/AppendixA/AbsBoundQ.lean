module
public import SpherePacking.Dim24.Inequalities.AppendixA.PolyOfCoeffsLemmas
import Mathlib.Algebra.Algebra.Rat


/-!
`ℚ`-valued variant of `AppendixA.absBound`.

The real-valued bound `absBound` is used to control the absolute value of a truncated coefficient
list by a simple geometric-series estimate. In Appendix A we also need a rational version so that
we can transport explicit bounds produced by computation.

The definition `absBoundQ` follows the same recursion as `absBound`, and `absBoundQ_cast` relates
the two by coercion to `ℝ`.
-/


namespace SpherePacking.Dim24.AppendixA

noncomputable section

/--
Rational coefficient bound used in Appendix A.

For a list `a₀, a₁, ...` and a constant `cQ`, this returns the sum
`|a₀| + cQ * (|a₁| + cQ * (...))`.
-/
@[expose]
public def absBoundQ : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: l, cQ => |a| + cQ * absBoundQ l cQ

/-- Casting `absBoundQ` to `ℝ` agrees with the real definition `absBound`. -/
public lemma absBoundQ_cast (l : List ℚ) (cQ : ℚ) :
    (absBound l (cQ : ℝ)) = (absBoundQ l cQ : ℝ) := by
  induction l <;> simp [absBound, absBoundQ, *, Rat.cast_abs]

end

end SpherePacking.Dim24.AppendixA
