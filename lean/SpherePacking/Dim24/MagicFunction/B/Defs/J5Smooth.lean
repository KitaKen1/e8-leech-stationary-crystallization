-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Defs.PsiExtensions
public import SpherePacking.Integration.Measure
import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSlash
import SpherePacking.Dim24.ModularForms.Psi.Relations
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.Integration.DifferentiationUnderIntegral
import SpherePacking.Integration.UpperHalfPlaneComp
import SpherePacking.MagicFunction.IntegralParametrisationsContinuity


/-!
# Smoothness and one-sided Schwartz decay for `RealIntegrals.J₅'`

This follows the dimension-8 argument, with weight `-10` in the slash action. The modular
transformation under `S` provides an extra factor `t^10` near `t = 0`, which is integrable and
yields Schwartz decay for `x ≥ 0` after an AM-GM estimate.

## Main definitions
* `Schwartz.J5Smooth.coeff`, `Schwartz.J5Smooth.g`, `Schwartz.J5Smooth.gN`

## Main statements
* `Schwartz.J5Smooth.ψI'_z₅'_eq`
* `Schwartz.J5Smooth.gN_integrable`
-/

noncomputable section

namespace SpherePacking.Dim24.Schwartz.J5Smooth

open scoped UpperHalfPlane

open Complex Real Set MeasureTheory
open UpperHalfPlane
open MagicFunction.Parametrisations
open RealIntegrals PsiExpBounds
open SpherePacking.Integration (μIoo01)


/-- Coefficient appearing in the exponential kernel of the `J₅'` integrand. -/
@[expose] public def coeff (t : ℝ) : ℂ := ((Real.pi : ℂ) * (Complex.I : ℂ)) * z₅' t

/-- The integrand defining `J₅'`, after parametrizing the contour by `t ∈ (0,1)`. -/
@[expose] public def g (x t : ℝ) : ℂ :=
  ((Complex.I : ℂ) * ψI' (z₅' t)) * cexp ((x : ℂ) * coeff t)

/-- The `n`th differentiated integrand for `J₅'`, used for differentiation under the integral. -/
@[expose] public def gN (n : ℕ) (x t : ℝ) : ℂ := (coeff t) ^ n * g x t

/-- A uniform bound on the kernel coefficient `‖coeff t‖` on the parametrizing interval. -/
public lemma coeff_norm_le (t : ℝ) : ‖coeff t‖ ≤ 2 * Real.pi := by
  have hz : ‖z₅' t‖ ≤ 2 := by
    exact (norm_z₅'_le_one t).trans (by norm_num)
  simpa [coeff, mul_assoc] using!
    (SpherePacking.ForMathlib.norm_mul_pi_I_le_two_pi (z := z₅' t) (hz := hz))

/-- Continuity of `t ↦ ψI' (z₅' t)` on `t ∈ (0,1)`. -/
public lemma continuousOn_ψI'_z₅' : ContinuousOn (fun t : ℝ => ψI' (z₅' t)) (Ioo (0 : ℝ) 1) := by
  -- This proof is by restricting to `t ∈ (0,1)` and using continuity of `ψI` on `ℍ`.
  refine (continuousOn_iff_continuous_restrict).2 ?_
  have hz : Continuous fun t : Ioo (0 : ℝ) 1 => z₅' (t : ℝ) :=
    continuous_z₅'.comp continuous_subtype_val
  have him : ∀ t : Ioo (0 : ℝ) 1, 0 < (z₅' (t : ℝ)).im := by
    intro t
    have htIoc : (t : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨t.2.1, le_of_lt t.2.2⟩
    exact im_z₅'_pos (t := (t : ℝ)) htIoc
  have hEq :
      ∀ t : Ioo (0 : ℝ) 1, ψI' (z₅' (t : ℝ)) = ψI (⟨z₅' (t : ℝ), him t⟩ : ℍ) := by
    intro t
    simp [ψI', him]
  have hcont : Continuous fun t : Ioo (0 : ℝ) 1 => ψI' (z₅' (t : ℝ)) := by
    simpa using!
      (SpherePacking.Integration.continuous_comp_upperHalfPlane_mk
        (ψT := ψI) (hψT := SpherePacking.Dim24.continuous_ψI)
        (z := fun t : Ioo (0 : ℝ) 1 => z₅' (t : ℝ)) (hz := hz) (him := him) (ψT' := ψI')
        (hEq := hEq))
  simpa [Set.restrict] using! hcont

/-- Continuity of the kernel coefficient `coeff`. -/
public lemma continuous_coeff : Continuous coeff := by
  simpa [coeff, mul_assoc] using! continuous_const.mul continuous_z₅'

lemma continuousOn_g (x : ℝ) : ContinuousOn (g x) (Ioo (0 : ℝ) 1) := by
  have hψ : ContinuousOn (fun t : ℝ => (Complex.I : ℂ) * ψI' (z₅' t)) (Ioo (0 : ℝ) 1) :=
    continuousOn_const.mul continuousOn_ψI'_z₅'
  simpa [g, SpherePacking.Integration.DifferentiationUnderIntegral.g] using!
    (SpherePacking.Integration.DifferentiationUnderIntegral.continuousOn_g_Ioo
      (coeff := coeff) (hf := fun t => (Complex.I : ℂ) * ψI' (z₅' t)) hψ continuous_coeff x)

lemma continuousOn_gN (n : ℕ) (x : ℝ) : ContinuousOn (gN n x) (Ioo (0 : ℝ) 1) := by
  have hψ : ContinuousOn (fun t : ℝ => (Complex.I : ℂ) * ψI' (z₅' t)) (Ioo (0 : ℝ) 1) :=
    continuousOn_const.mul continuousOn_ψI'_z₅'
  simpa [gN, g,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g,
    mul_assoc, mul_left_comm, mul_comm] using!
    (SpherePacking.Integration.DifferentiationUnderIntegral.continuousOn_gN_Ioo
      (coeff := coeff) (hf := fun t => (Complex.I : ℂ) * ψI' (z₅' t))
      hψ continuous_coeff n x)

/-- Measurability of the differentiated integrand `gN n x` on `t ∈ (0,1)`. -/
public lemma gN_measurable (n : ℕ) (x : ℝ) : AEStronglyMeasurable (gN n x) μIoo01 := by
  simpa [SpherePacking.Integration.μIoo01] using!
    (ContinuousOn.aestronglyMeasurable (μ := (volume : Measure ℝ))
      (continuousOn_gN (n := n) (x := x)) measurableSet_Ioo)

section Modular

open ModularGroup
open scoped MatrixGroups ModularForm

/-- Modular rewrite of `ψI' (z₅' t)` in terms of `ψS` restricted to the imaginary axis. -/
public lemma ψI'_z₅'_eq (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    ψI' (z₅' t) = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (10 : ℕ) := by
  have htIcc : t ∈ Icc (0 : ℝ) 1 := mem_Icc_of_Ioc ht
  have ht0 : 0 < t := ht.1
  have hz5 : z₅' t = (Complex.I : ℂ) * (t : ℂ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using! (z₅'_eq_of_mem (t := t) htIcc)
  have hψI' : ψI' (z₅' t) = ψI.resToImagAxis t := by
    simp [ψI', Function.resToImagAxis, ResToImagAxis, ht0, hz5]
  have hslash :
      ψI.resToImagAxis t = (ψS ∣[-10] S).resToImagAxis t := by
    -- Apply `resToImagAxis` to the identity `(ψS ∣[-10] S) = ψI`.
    simpa using! congrArg (fun F : ℍ → ℂ => F.resToImagAxis t) PsiSlash.ψS_slash_S |>.symm
  have hS :
      (ψS ∣[-10] S).resToImagAxis t =
        (Complex.I : ℂ) ^ (10 : ℤ) * t ^ (10 : ℤ) * ψS.resToImagAxis (1 / t) := by
    -- `ResToImagAxis.SlashActionS` gives the explicit restriction of a slash action under `S`.
    simpa using! (ResToImagAxis.SlashActionS (F := ψS) (k := (-10 : ℤ)) (t := t) ht0)
  -- Combine and normalize the powers.
  calc
    ψI' (z₅' t) = ψI.resToImagAxis t := hψI'
    _ = (ψS ∣[-10] S).resToImagAxis t := hslash
    _ = (Complex.I : ℂ) ^ (10 : ℤ) * t ^ (10 : ℤ) * ψS.resToImagAxis (1 / t) := hS
    _ = ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (10 : ℕ) := by
          -- Convert `zpow` with a positive exponent to `pow`, then rewrite `(I*t)^10`.
          -- Normalize the `zpow` expression into a natural power.
          simp [zpow_ofNat, mul_pow, mul_comm]

end Modular

/-- A uniform bound on `‖ψI' (z₅' t)‖` on `t ∈ (0,1)`. -/
public lemma exists_bound_norm_ψI'_z₅' :
    ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖ψI' (z₅' t)‖ ≤ M := by
  rcases PsiExpBounds.exists_bound_norm_ψS_resToImagAxis_Ici_one with ⟨M, hM⟩
  have hM0 : 0 ≤ M :=
    le_trans (norm_nonneg (ψS.resToImagAxis (1 : ℝ))) (hM 1 (le_rfl : (1 : ℝ) ≤ 1))
  refine ⟨M, ?_⟩
  intro t ht
  have htIoc : t ∈ Ioc (0 : ℝ) 1 := ⟨ht.1, le_of_lt ht.2⟩
  have ht0 : 0 < t := ht.1
  have ht0' : 0 ≤ t := le_of_lt ht0
  have ht1 : t ≤ 1 := le_of_lt ht.2
  have ht10 : t ^ (10 : ℕ) ≤ (1 : ℝ) := by
    simpa using! (pow_le_pow_left₀ ht0' ht1 10)
  have hone : (1 : ℝ) ≤ 1 / t := by
    simpa using! (one_le_one_div ht0 ht1)
  have hψS : ‖ψS.resToImagAxis (1 / t)‖ ≤ M := hM (1 / t) hone
  have hEq : ψI' (z₅' t) =
      ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (10 : ℕ) :=
    ψI'_z₅'_eq (t := t) htIoc
  have hIt : ‖(Complex.I : ℂ) * (t : ℂ)‖ = t := by
    simp [Complex.norm_real, abs_of_nonneg ht0']
  calc
    ‖ψI' (z₅' t)‖ =
        ‖ψS.resToImagAxis (1 / t) * ((Complex.I : ℂ) * (t : ℂ)) ^ (10 : ℕ)‖ := by
          simp [hEq]
    _ ≤ ‖ψS.resToImagAxis (1 / t)‖ * ‖((Complex.I : ℂ) * (t : ℂ)) ^ (10 : ℕ)‖ := by
          simp
    _ = ‖ψS.resToImagAxis (1 / t)‖ * ‖(Complex.I : ℂ) * (t : ℂ)‖ ^ (10 : ℕ) := by
          simp [norm_pow]
    _ = ‖ψS.resToImagAxis (1 / t)‖ * t ^ (10 : ℕ) := by
          exact
            ext_cauchy
              (congrArg cauchy
                (congrArg (HMul.hMul ‖Function.resToImagAxis ψS (1 / t)‖)
                  (congrFun (congrArg HPow.hPow hIt) 10)))
    _ ≤ M * t ^ (10 : ℕ) := by gcongr
    _ ≤ M * 1 := by gcongr
    _ = M := by ring

/-- Integrability of `gN n x` with respect to the measure on `t ∈ (0,1)`. -/
public lemma gN_integrable (n : ℕ) (x : ℝ) : Integrable (gN n x) μIoo01 := by
  have hψ : ContinuousOn (fun t : ℝ => (Complex.I : ℂ) * ψI' (z₅' t)) (Ioo (0 : ℝ) 1) :=
    continuousOn_const.mul continuousOn_ψI'_z₅'
  have hexists_hf :
      ∃ M, ∀ t ∈ Ioo (0 : ℝ) 1, ‖((Complex.I : ℂ) * ψI' (z₅' t))‖ ≤ M := by
    rcases exists_bound_norm_ψI'_z₅' with ⟨Mψ, hMψ⟩
    refine ⟨Mψ, ?_⟩
    intro t ht
    have h : ‖ψI' (z₅' t)‖ ≤ Mψ := hMψ t ht
    have : ‖(Complex.I : ℂ)‖ * ‖ψI' (z₅' t)‖ ≤ Mψ := by simpa using! h
    simpa [norm_mul] using! this
  simpa [SpherePacking.Integration.μIoo01, gN, g,
    SpherePacking.Integration.DifferentiationUnderIntegral.gN,
    SpherePacking.Integration.DifferentiationUnderIntegral.g,
    mul_assoc, mul_left_comm, mul_comm] using!
    (SpherePacking.Integration.DifferentiationUnderIntegral.integrable_gN_Ioo
      (coeff := coeff) (hf := fun t => (Complex.I : ℂ) * ψI' (z₅' t))
      hψ continuous_coeff hexists_hf (fun t => coeff_norm_le t) n x)

end SpherePacking.Dim24.Schwartz.J5Smooth

end
