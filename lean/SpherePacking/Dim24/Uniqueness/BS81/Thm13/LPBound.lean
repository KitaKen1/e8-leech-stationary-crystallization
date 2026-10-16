-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Defs
import SpherePacking.Dim24.Uniqueness.BS81.LP.Delsarte
import SpherePacking.Dim24.Uniqueness.BS81.LP.F24
import SpherePacking.Dim24.Uniqueness.BS81.LP.Thm13Certificate

/-!
# BS81 Theorem 13: the LP bound in dimension `24`

This file proves the linear programming bound `Set.ncard C ≤ 196560` for a `(24, M, 1/2)`
spherical code `C`. The inequality step is the abstract Delsarte LP bound from `LP/Delsarte.lean`,
and the positivity/certificate input is packaged in `LP/Thm13Certificate.lean`.

The polynomial used by BS81 is
`f(t) = (t+1)(t+1/2)^2 (t+1/4)^2 t^2 (t-1/4)^2 (t-1/2)`.

## Main statements
* `thm13_card_le_196560`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81
noncomputable section

open scoped RealInnerProductSpace BigOperators

/-!
### Specialized BS81 bound (Theorem 13)
-/

/-- The BS81 LP bound for `(24, M, 1/2)` spherical codes: `Set.ncard C ≤ 196560`. -/
public theorem thm13_card_le_196560
    (C : Set (EuclideanSpace ℝ (Fin 24))) :
    IsSphericalCode 24 C (1 / 2 : ℝ) →
      Set.ncard C ≤ 196560 := by
  intro hC
  -- Apply the abstract Delsarte LP bound with `f = f24` and the certified constant `a0_24`.
  have ha0 : 0 < Uniqueness.BS81.LP.a0_24 :=
    Uniqueness.BS81.LP.a0_24_pos
  have hcert :
      IsDelsarteDual24 f24 Uniqueness.BS81.LP.a0_24 :=
    Uniqueness.BS81.LP.isDelsarteDual24_f24
  have hboundR :
      (Set.ncard C : ℝ) ≤ 196560 := by
    have hR :=
      delsarte_bound_sphere24_real (C := C) (s := (1 / 2 : ℝ)) (f := f24)
        (a0 := Uniqueness.BS81.LP.a0_24)
        hC ha0 (fun t ht => f24_eval_nonpos_of_mem_Icc t ht) hcert
    have hval : f24.eval (1 : ℝ) / Uniqueness.BS81.LP.a0_24 = (196560 : ℝ) := by
      simpa using! Uniqueness.BS81.LP.f24_eval_one_div_a0_24
    -- Rewrite the RHS.
    exact hR.trans_eq hval
  exact (Nat.cast_le (α := ℝ)).1 (by simpa using! hboundR)

end

end SpherePacking.Dim24.Uniqueness.BS81
