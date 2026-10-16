-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module

public import SpherePacking.MagicFunction.IntegralParametrisations

/-!
# Continuity of integral parametrisations

This file records continuity lemmas for the parametrisations `z₁`--`z₅` and their extensions
`z₁'`--`z₅'`.
-/

namespace MagicFunction.Parametrisations

noncomputable section

open scoped Topology
open Complex Real Set

private lemma continuous_coe_Icc_toComplex :
    Continuous (fun t : Icc (0 : ℝ) 1 => (t : ℂ)) :=
  Complex.continuous_ofReal.comp continuous_subtype_val

/-- The parametrisation `z₁` is continuous on `Icc (0 : ℝ) 1`. -/
public lemma continuous_z₁ : Continuous z₁ := by
  exact continuous_const.add (continuous_const.mul continuous_coe_Icc_toComplex)

/-- The extension `z₁' : ℝ → ℂ` is continuous. -/
public lemma continuous_z₁' : Continuous z₁' := by
  change Continuous (IccExtend (zero_le_one) z₁)
  exact continuous_z₁.Icc_extend'

/-- An explicit rewrite of `((pi * I) * z₁' t)` for `t ∈ Icc (0 : ℝ) 1`. -/
public lemma pi_I_mul_z₁'_eq_of_mem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ((Real.pi : ℂ) * (Complex.I : ℂ)) * z₁' t =
      (-((Real.pi : ℂ) * (Complex.I : ℂ))) - (Real.pi : ℂ) * (t : ℂ) := by
  have hmul :
      ((Real.pi : ℂ) * (Complex.I : ℂ)) * ((Complex.I : ℂ) * (t : ℂ)) =
        -(Real.pi : ℂ) * (t : ℂ) := by
    calc
      ((Real.pi : ℂ) * (Complex.I : ℂ)) * ((Complex.I : ℂ) * (t : ℂ)) =
          (Real.pi : ℂ) * ((Complex.I : ℂ) * (Complex.I : ℂ)) * (t : ℂ) := by ac_rfl
      _ = -(Real.pi : ℂ) * (t : ℂ) := by simp [Complex.I_mul_I]
  have hmain :
      ((Real.pi : ℂ) * (Complex.I : ℂ)) * z₁' t =
        (-((Real.pi : ℂ) * (Complex.I : ℂ))) + (-(Real.pi : ℂ) * (t : ℂ)) := by
    calc
      ((Real.pi : ℂ) * (Complex.I : ℂ)) * z₁' t =
          ((Real.pi : ℂ) * (Complex.I : ℂ)) * (-1 : ℂ) +
            ((Real.pi : ℂ) * (Complex.I : ℂ)) * ((Complex.I : ℂ) * (t : ℂ)) := by
              simp [z₁'_eq_of_mem (t := t) ht, mul_add, mul_assoc]
      _ = (-((Real.pi : ℂ) * (Complex.I : ℂ))) + (-(Real.pi : ℂ) * (t : ℂ)) := by simp [hmul]
  simpa [sub_eq_add_neg] using hmain

/-- The parametrisation `z₂` is continuous on `Icc (0 : ℝ) 1`. -/
public lemma continuous_z₂ : Continuous z₂ := by
  exact (continuous_const.add continuous_coe_Icc_toComplex).add continuous_const

/-- The extension `z₂' : ℝ → ℂ` is continuous. -/
public lemma continuous_z₂' : Continuous z₂' := by
  change Continuous (IccExtend (zero_le_one) z₂)
  exact continuous_z₂.Icc_extend'

/-- The parametrisation `z₃` is continuous on `Icc (0 : ℝ) 1`. -/
public lemma continuous_z₃ : Continuous z₃ := by
  exact continuous_const.add (continuous_const.mul continuous_coe_Icc_toComplex)

/-- The extension `z₃' : ℝ → ℂ` is continuous. -/
public lemma continuous_z₃' : Continuous z₃' := by
  change Continuous (IccExtend (zero_le_one) z₃)
  exact continuous_z₃.Icc_extend'

/-- The parametrisation `z₄` is continuous on `Icc (0 : ℝ) 1`. -/
public lemma continuous_z₄ : Continuous z₄ := by
  exact (continuous_const.sub continuous_coe_Icc_toComplex).add continuous_const

/-- The extension `z₄' : ℝ → ℂ` is continuous. -/
public lemma continuous_z₄' : Continuous z₄' := by
  change Continuous (IccExtend (zero_le_one : (0 : ℝ) ≤ 1) z₄)
  exact continuous_z₄.Icc_extend'

/-- The parametrisation `z₅` is continuous on `Icc (0 : ℝ) 1`. -/
public lemma continuous_z₅ : Continuous z₅ := by
  exact continuous_const.mul continuous_coe_Icc_toComplex

/-- The extension `z₅' : ℝ → ℂ` is continuous. -/
public lemma continuous_z₅' : Continuous z₅' := by
  change Continuous (IccExtend (zero_le_one : (0 : ℝ) ≤ 1) z₅)
  exact continuous_z₅.Icc_extend'

end

end MagicFunction.Parametrisations
