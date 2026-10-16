-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.Schwartz.I6Preamble
import SpherePacking.Dim24.MagicFunction.A.DefsAux.VarphiExpBounds
import SpherePacking.ForMathlib.DerivHelpers
import SpherePacking.ForMathlib.IntegrablePowMulExp
import SpherePacking.ForMathlib.IteratedDeriv
import SpherePacking.Integration.SmoothIntegralIciOne


/-!
# Differentiation under the `I₆'` integral

This file provides the "differentiate under the integral sign" input for the tail integral `I₆'`.
On the open set `s = (-1, ∞)` we define
`F n x = ∫ t in Set.Ici 1, gN n x t` and show `deriv (F n) x = F (n + 1) x`.

## Main definitions
* `F`, `G`

## Main statements
* `hasDerivAt_F`
* `iteratedDeriv_G_eq`
-/

namespace SpherePacking.Dim24

noncomputable section

namespace Schwartz

open MeasureTheory Filter Topology

namespace I6Smooth

open SpherePacking.Integration (μIciOne)

/-!
### Measurability / continuity of the integrands on `Set.Ici 1`
-/

/-- Continuity of the base integrand `g x` on `t ≥ 1`. -/
public lemma g_continuousOn (x : ℝ) : ContinuousOn (g x) (Set.Ici (1 : ℝ)) := by
  have hvarphi : ContinuousOn varphi.resToImagAxis (Set.Ici (1 : ℝ)) :=
    VarphiExpBounds.continuousOn_varphi_resToImagAxis_Ici_one
  have hcoeff : Continuous fun t : ℝ => coeff t := by
    simp only [coeff, SpherePacking.Integration.SmoothIntegralIciOne.coeff]
    fun_prop
  have hexp : ContinuousOn (fun t : ℝ => Complex.exp ((x : ℂ) * coeff t)) (Set.Ici (1 : ℝ)) :=
    (Complex.continuous_exp.comp (continuous_const.mul hcoeff)).continuousOn
  simpa [g, SpherePacking.Integration.SmoothIntegralIciOne.g] using!
    (continuousOn_const.mul (hvarphi.mul hexp))

lemma gN_measurable (n : ℕ) (x : ℝ) : AEStronglyMeasurable (gN n x) μIciOne := by
  have hcoeff0 : Continuous fun t : ℝ => coeff t := by
    simp only [coeff, SpherePacking.Integration.SmoothIntegralIciOne.coeff]
    fun_prop
  have hcoeff : ContinuousOn (fun t : ℝ => (coeff t) ^ n) (Set.Ici (1 : ℝ)) :=
    (hcoeff0.pow n).continuousOn
  have hg : ContinuousOn (g x) (Set.Ici (1 : ℝ)) := g_continuousOn x
  have hcont : ContinuousOn (gN n x) (Set.Ici (1 : ℝ)) := by simpa [gN] using! hcoeff.mul hg
  simpa [μIciOne] using!
    (ContinuousOn.aestronglyMeasurable (μ := (volume : Measure ℝ)) hcont measurableSet_Ici)

/-- Integrability of `gN n x` on `t ≥ 1` for `x ∈ s = (-1, ∞)`. -/
public lemma gN_integrable (n : ℕ) (x : ℝ) (hx : x ∈ s) : Integrable (gN n x) μIciOne := by
  -- Bound `‖gN n x t‖` by a polynomial times `exp(-π * (x+2) * t)` using the
  -- exponential decay of `varphi(it)`.
  have hmeas : AEStronglyMeasurable (gN n x) μIciOne := gN_measurable (n := n) (x := x)
  rcases VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one with ⟨Cφ, hCφ⟩
  have hCφ0 : 0 ≤ Cφ := by
    refine SpherePacking.ForMathlib.nonneg_of_nonneg_le_mul (a := ‖varphi.resToImagAxis 1‖)
      (b := Real.exp (-(2 * Real.pi) * (1 : ℝ))) (C := Cφ) (norm_nonneg _) (by positivity) ?_
    simpa using! (hCφ 1 (le_rfl : (1 : ℝ) ≤ 1))
  have hx' : (-1 : ℝ) < x := by simpa [s] using! hx
  have hx2 : 0 < x + 2 := by linarith
  have hb : 0 < Real.pi * (x + 2) := mul_pos Real.pi_pos hx2
  let bound : ℝ → ℝ := fun t ↦ (Real.pi ^ n) * (t ^ n * Real.exp (-(Real.pi * (x + 2)) * t)) * Cφ
  have hbound_int : Integrable bound μIciOne := by
    have hInt :
        IntegrableOn (fun t : ℝ ↦ t ^ n * Real.exp (-(Real.pi * (x + 2)) * t)) (Set.Ici (1 : ℝ))
          volume :=
      SpherePacking.ForMathlib.integrableOn_pow_mul_exp_neg_mul_Ici
        (n := n) (b := Real.pi * (x + 2)) (by simpa [mul_assoc] using! hb)
    have : Integrable (fun t : ℝ ↦ t ^ n * Real.exp (-(Real.pi * (x + 2)) * t)) μIciOne := by
      simpa [IntegrableOn, μIciOne] using! hInt
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using!
      this.const_mul ((Real.pi ^ n) * Cφ)
  refine
      Integrable.mono' hbound_int hmeas ?_
  refine (ae_restrict_iff' (μ := (volume : Measure ℝ)) measurableSet_Ici).2 <| .of_forall ?_
  intro t ht
  have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1) ht
  have hcoeff : ‖coeff t‖ ^ n ≤ (Real.pi * t) ^ n := by
    have : ‖coeff t‖ = Real.pi * t := coeff_norm t ht
    simp [this]
  have hvarphi :
      ‖varphi.resToImagAxis t‖ ≤ Cφ * Real.exp (-(2 * Real.pi) * t) :=
    hCφ t ht
  have hg' :
      ‖g x t‖ ≤ ‖varphi.resToImagAxis t‖ * Real.exp (-Real.pi * x * t) :=
    g_norm_bound (x := x) (t := t)
  have hexp :
      Real.exp (-(2 * Real.pi) * t) *
          Real.exp (-Real.pi * x * t) =
        Real.exp (-(Real.pi * (x + 2)) * t) := by
    have harg :
        (-(Real.pi * (x + 2)) * t) = (-(2 * Real.pi) * t) + (-Real.pi * x * t) := by ring_nf
    simp [harg, Real.exp_add, mul_comm]
  calc
    ‖gN n x t‖ = ‖coeff t‖ ^ n * ‖g x t‖ := by
          simp [gN, g, coeff, SpherePacking.Integration.SmoothIntegralIciOne.gN, norm_pow]
    _ ≤ (Real.pi * t) ^ n * (‖varphi.resToImagAxis t‖ * Real.exp (-Real.pi * x * t)) := by
          gcongr
    _ ≤
        (Real.pi * t) ^ n *
          ((Cφ * Real.exp (-(2 * Real.pi) * t)) * Real.exp (-Real.pi * x * t)) := by
          gcongr
    _ = (Real.pi ^ n) * (t ^ n * Real.exp (-(Real.pi * (x + 2)) * t)) * Cφ := by
          -- normalize to match `bound`
          have hp : (Real.pi * t) ^ n = (Real.pi ^ n) * (t ^ n) := by simp [mul_pow, mul_comm]
          grind only
    _ = bound t := by
          simp [bound, mul_left_comm, mul_comm]

/-- The tail integral `F n x = ∫_{t ≥ 1} gN n x t`. -/
@[expose] public def F (n : ℕ) (x : ℝ) : ℂ := ∫ t in Set.Ici (1 : ℝ), gN n x t

/-- The normalized tail integral `G n x = 2 * F n x`, matching the constant factor in `I₆'`. -/
@[expose] public def G (n : ℕ) (x : ℝ) : ℂ := (2 : ℂ) * F n x

/-- Differentiation under the integral sign: `d/dx (F n x) = F (n + 1) x` on `s`. -/
public lemma hasDerivAt_F (n : ℕ) (x : ℝ) (hx : x ∈ s) :
    HasDerivAt (fun y : ℝ ↦ F n y) (F (n + 1) x) x := by
  have hx' : (-1 : ℝ) < x := by simpa [s] using! hx
  have hInt : Integrable (gN n x) μIciOne := gN_integrable (n := n) (x := x) hx
  have exists_bound :
      ∃ C, ∀ t : ℝ, 1 ≤ t → ‖varphi.resToImagAxis t‖ ≤
        C * Real.exp (-(Real.pi * (2 : ℝ)) * t) := by
    rcases VarphiExpBounds.exists_bound_norm_varphi_resToImagAxis_exp_Ici_one with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro t ht
    simpa [mul_assoc, mul_left_comm, mul_comm, two_mul] using! (hC t ht)
  simpa [F, gN] using!
    (Integration.SmoothIntegralIciOne.hasDerivAt_integral_gN
      (hf := varphi.resToImagAxis) (shift := (2 : ℝ)) (hshift := (by norm_num))
      (exists_bound_norm_hf := exists_bound)
      (gN_measurable := fun n x => by simpa [gN] using! (gN_measurable (n := n) (x := x)))
      (n := n) (x := x) hx' (hF_int := by simpa [gN] using! hInt))

lemma deriv_F (n : ℕ) (x : ℝ) (hx : x ∈ s) :
    deriv (F n) x = F (n + 1) x := by
  simpa using! (hasDerivAt_F (n := n) (x := x) hx).deriv

lemma deriv_G (n : ℕ) (x : ℝ) (hx : x ∈ s) :
    deriv (G n) x = G (n + 1) x := by
  have hF : HasDerivAt (fun y : ℝ ↦ F n y) (F (n + 1) x) x := hasDerivAt_F (n := n) (x := x) hx
  change deriv (fun y : ℝ ↦ (2 : ℂ) * F n y) x = (2 : ℂ) * F (n + 1) x
  simpa [G] using! (hF.const_mul (2 : ℂ)).deriv

/-- On `s`, iterated derivatives of `G m` agree with `G (n + m)`. -/
public lemma iteratedDeriv_G_eq :
    ∀ n m : ℕ, Set.EqOn (iteratedDeriv n (G m)) (G (n + m)) s := by
  simpa using!
    (SpherePacking.ForMathlib.eqOn_iteratedDeriv_eq_of_deriv_eq (hs := isOpen_s) (G := G)
      (hderiv := fun n x hx => deriv_G (n := n) (x := x) hx))


end Schwartz.I6Smooth
end

end SpherePacking.Dim24
