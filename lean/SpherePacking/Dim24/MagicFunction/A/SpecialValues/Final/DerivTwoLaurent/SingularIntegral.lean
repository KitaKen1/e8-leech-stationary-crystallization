-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Order.Filter.Defs
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivDefs
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.Basic
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.DerivTwoLaurent.AvaluesBridge

/-!
# Singular integral input near `u = 2`

This file isolates the explicit singular integral on `(1,∞)` that produces the simple pole
`B / (u - 2)` in the analytic continuation identity `eq:avalues` (paper `dim_24.tex`). This input
is used in the derivative computation at `u = 2` in `DerivTwoAtTwo.lean`.

## Main definitions
* `singIntTwo`, `tailSingTwo`

## Main statements
* `exists_laurent_aProfile_two`
-/

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesDerivTwoLaurent

open scoped Real Topology
open Filter Complex MeasureTheory Set
open RealIntegrals

/-!
### Singular integral at `u = 2`

We will isolate a term of the form `l * ∫_{t>1} exp(-π (u-2) t) dt`, which produces the `1/(u-2)`
singularity, with residue `l/π = B`.
-/

/-- Singular integral `∫_{t>1} exp(-π (u - 2) t) dt` appearing in the `u = 2` Laurent expansion. -/
def singIntTwo (u : ℝ) : ℝ :=
  ∫ t : ℝ in Set.Ioi (1 : ℝ), Real.exp (-(Real.pi * (u - 2) * t))

/-- Complex cast of `singIntTwo`. -/
def singIntTwoC (u : ℝ) : ℂ := (singIntTwo u : ℂ)

/-- As `u → 2⁺`, the product `(u - 2) * singIntTwo u` tends to `1 / π`. -/
lemma tendsto_mul_singIntTwo_nhdsGT_two :
    Tendsto (fun u : ℝ => (u - 2) * singIntTwo u) (𝓝[>] (2 : ℝ)) (𝓝 (1 / Real.pi)) := by
  -- Evaluate the integral explicitly and take the limit as `u → 2⁺`.
  have hEv :
      (fun u : ℝ => (u - 2) * singIntTwo u) =ᶠ[𝓝[>] (2 : ℝ)]
        fun u : ℝ => Real.exp (-Real.pi * (u - 2)) / Real.pi := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu' : 2 < u := hu
    have ha : (-(Real.pi * (u - 2))) < 0 := by
      have : 0 < u - 2 := sub_pos.2 hu'
      nlinarith [Real.pi_pos]
    have hIreal :
        (∫ t : ℝ in Set.Ioi (1 : ℝ), Real.exp ((-(Real.pi * (u - 2))) * t)) =
          -Real.exp ((-(Real.pi * (u - 2))) * (1 : ℝ)) / (-(Real.pi * (u - 2))) :=
      integral_exp_mul_Ioi (a := (-(Real.pi * (u - 2)))) ha (c := (1 : ℝ))
    have hI :
        singIntTwo u =
          -Real.exp ((-(Real.pi * (u - 2))) * (1 : ℝ)) / (-(Real.pi * (u - 2))) := by
      -- Align the integrands.
      simpa [singIntTwo, mul_assoc] using! hIreal
    have hpi0 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    have hsub0 : (u - 2) ≠ 0 := sub_ne_zero.2 (ne_of_gt hu')
    have ha0 : (-(Real.pi * (u - 2))) ≠ 0 := by
      exact neg_ne_zero.2 (mul_ne_zero hpi0 hsub0)
    have hexp :
        Real.exp ((-(Real.pi * (u - 2))) * (1 : ℝ)) = Real.exp (-Real.pi * (u - 2)) := by simp
    calc
      (u - 2) * singIntTwo u =
          (u - 2) *
            (-Real.exp ((-(Real.pi * (u - 2))) * (1 : ℝ)) / (-(Real.pi * (u - 2)))) := by
              simp [hI]
      _ = Real.exp (-Real.pi * (u - 2)) / Real.pi := by
            field_simp [ha0, hpi0, hsub0, hexp]
  refine (Tendsto.congr' hEv.symm ?_)
  have hsub0 : Tendsto (fun u : ℝ => u - 2) (𝓝 (2 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using! ((tendsto_id : Tendsto (fun u : ℝ => u) (𝓝 (2 : ℝ)) (𝓝 (2 : ℝ))).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ)) (𝓝 (2 : ℝ)) (𝓝 (2 : ℝ))))
  have hsub : Tendsto (fun u : ℝ => u - 2) (𝓝[>] (2 : ℝ)) (𝓝 (0 : ℝ)) :=
    hsub0.mono_left nhdsWithin_le_nhds
  have hlin : Tendsto (fun u : ℝ => (-Real.pi) * (u - 2)) (𝓝[>] (2 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using!
      ((tendsto_const_nhds :
            Tendsto (fun _ : ℝ => (-Real.pi)) (𝓝[>] (2 : ℝ)) (𝓝 (-Real.pi))).mul hsub)
  have hExp :
      Tendsto (fun u : ℝ => Real.exp (-Real.pi * (u - 2))) (𝓝[>] (2 : ℝ)) (𝓝 (Real.exp 0)) := by
    simpa [mul_assoc] using! (Real.continuous_exp.tendsto _).comp hlin
  have hExp' :
      Tendsto (fun u : ℝ => Real.exp (-Real.pi * (u - 2))) (𝓝[>] (2 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa using! hExp
  exact Tendsto.div_const hExp' π

lemma tendsto_mul_singIntTwoC_nhdsGT_two :
    Tendsto (fun u : ℝ => (((u - 2) * singIntTwo u : ℝ) : ℂ)) (𝓝[>] (2 : ℝ))
      (𝓝 ((1 / Real.pi : ℝ) : ℂ)) :=
  (Complex.continuous_ofReal.tendsto (1 / Real.pi)).comp tendsto_mul_singIntTwo_nhdsGT_two

/-- The singular term `l * singIntTwoC u`, whose residue is `B`. -/
def tailSingTwo (u : ℝ) : ℂ := l * singIntTwoC u

/-- As `u → 2⁺`, the product `(u - 2) * tailSingTwo u` tends to `B`. -/
lemma tendsto_mul_tailSingTwo_nhdsGT_two :
    Tendsto (fun u : ℝ => ((u - 2 : ℝ) : ℂ) * tailSingTwo u) (𝓝[>] (2 : ℝ)) (𝓝 B) := by
  -- This is the same cast/multiplication pattern used at `u=4` in `DerivDefs.lean`.
  have hprod :
      Tendsto (fun u : ℝ => (((u - 2) * singIntTwo u : ℝ) : ℂ)) (𝓝[>] (2 : ℝ))
        (𝓝 ((1 / Real.pi : ℝ) : ℂ)) :=
    tendsto_mul_singIntTwoC_nhdsGT_two
  have hlim :
      Tendsto (fun u : ℝ => l * (((u - 2) * singIntTwo u : ℝ) : ℂ)) (𝓝[>] (2 : ℝ))
        (𝓝 (l * (π : ℂ)⁻¹)) := by
    have hprod' :
        Tendsto (fun u : ℝ => (((u - 2) * singIntTwo u : ℝ) : ℂ)) (𝓝[>] (2 : ℝ))
          (𝓝 ((π : ℂ)⁻¹)) := by
      simpa [one_div] using! hprod
    simpa [mul_assoc] using! (tendsto_const_nhds.mul hprod')
  have hconst : l * (π : ℂ)⁻¹ = B := by
    -- `B = l / π`.
    simpa [div_eq_mul_inv] using! B_eq_l_div_pi.symm
  have hlimB :
      Tendsto (fun u : ℝ => l * (((u - 2) * singIntTwo u : ℝ) : ℂ)) (𝓝[>] (2 : ℝ)) (𝓝 B) := by
    simpa [hconst] using! hlim
  simpa [tailSingTwo, singIntTwoC, mul_assoc, mul_left_comm, mul_comm] using! hlimB

/-!
### Main Laurent expansion

This is the analytic continuation statement supplying the principal part `B/(u-2)` after factoring
out `I * coeffExp u`.  In the paper it is derived from the contour deformation / Laplace-transform
representation in the paper, using:
- the `q`-expansion limit for `varphi₂Residual` (`Varphi2.lean`),
- the singular integral asymptotic above (`tailSingTwo`),
- dominated convergence estimates for the remaining integrable remainder.
-/

/--
Laurent expansion of `aProfile` at `u = 2` on a right-neighborhood, with principal part coming
from `B / (u - 2)` after factoring `I * coeffExp u`.
-/
public theorem exists_laurent_aProfile_two :
    ∃ h : ℝ → ℂ,
      ContinuousAt h (2 : ℝ) ∧
        (fun u : ℝ => aProfile u) =ᶠ[𝓝[>] (2 : ℝ)]
          fun u : ℝ =>
            (Complex.I : ℂ) * (SpecialValuesDeriv.coeffExp u) *
              (B / ((u - 2 : ℝ) : ℂ) + h u) +
              ((725760 : ℂ) * Complex.I / (π : ℂ)) := by
  -- Delegated to the bridge lemma in `DerivTwoLaurent`.
  simpa [SpecialValuesDerivTwoLaurent.constA2_av] using!
    (SpecialValuesDerivTwoLaurent.exists_laurent_aProfile_two_bridge : _)

end SpecialValuesDerivTwoLaurent

end

end SpherePacking.Dim24
