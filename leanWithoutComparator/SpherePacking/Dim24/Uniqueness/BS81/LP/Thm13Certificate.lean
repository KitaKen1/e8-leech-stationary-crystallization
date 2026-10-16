-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Delsarte
public import SpherePacking.Dim24.Uniqueness.BS81.LP.F24
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.F24Coefficients
import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.DualCertificate
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# BS81 Theorem 13: the dual certificate for `f24`

We define the constant `a0_24` (the `k = 0` coefficient in the normalized Gegenbauer expansion of
`f24`) and assemble the Delsarte dual certificate `IsDelsarteDual24 f24 a0_24`. We also record
the evaluation `f24(1) / a0_24 = 196560`.

## Main definitions
* `a0_24`

## Main statements
* `f24_eval_one_div_a0_24`
* `isDelsarteDual24_f24`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.LP
noncomputable section

/-!
## The constant `a0`
-/

/-- The `k = 0` coefficient in the normalized Gegenbauer expansion of `f24`. -/
@[expose] public def a0_24 : ℝ := f24GegenbauerCoeff 0

lemma a0_24_eq : a0_24 = (15 / 1490944 : ℝ) := by
  simpa [a0_24] using! f24GegenbauerCoeff_zero

/-- The constant `a0_24` is positive. -/
public lemma a0_24_pos : 0 < a0_24 := by
  -- `a0_24` is an explicit positive rational number.
  rw [a0_24_eq]
  norm_num

/-- The normalized value `f24(1) / a0_24`, equal to `196560`. -/
public lemma f24_eval_one_div_a0_24 :
    (Uniqueness.BS81.f24).eval (1 : ℝ) / a0_24 = 196560 := by
  -- Compute both sides explicitly.
  -- `f24.eval 1 = 2025/1024` (proved in `LP/F24.lean`).
  -- The ratio is `196560`.
  simp [a0_24_eq]
  norm_num

/-!
## The dual certificate
-/

/-- The Delsarte dual certificate `IsDelsarteDual24 f24 a0_24`. -/
public theorem isDelsarteDual24_f24 :
    Uniqueness.BS81.IsDelsarteDual24 (Uniqueness.BS81.f24) a0_24 := by
  have hf24 :
      (Uniqueness.BS81.f24 : Polynomial ℝ) =
        gegenbauerExpansion 10 f24GegenbauerCoeff := by
    -- `gegenbauerExpansion 10` is exactly the `range 11` sum.
    simpa [gegenbauerExpansion] using! f24_eq_sum_coeff_mul_gegenbauer24
  simpa [a0_24, hf24] using!
    (isDelsarteDual24_of_gegenbauerExpansion (N := 10) (a := f24GegenbauerCoeff)
      (fun k _hk => f24GegenbauerCoeff_nonneg k))

end

end SpherePacking.Dim24.Uniqueness.BS81.LP
