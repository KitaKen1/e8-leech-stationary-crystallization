-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.RootlessCase.ThetaMF
import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.FullRank.UnimodularIsZLattice
public import SpherePacking.Dim24.Uniqueness.LatticeInvariants
public import SpherePacking.ModularForms.Delta.ImagAxis
public import SpherePacking.ModularForms.DimensionFormulas
public import SpherePacking.ModularForms.QExpansionLemmas.QExpansionAlgebra
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.Compact

/-!
# Theta series equals the Leech theta series

This file is the modular-forms classification step (rank `24`, weight `12`): it shows that if
`L ⊆ ℝ²⁴` is even, unimodular, and rootless, then `thetaSeriesUHP L` agrees with the Leech lattice
theta series.

The proof identifies the theta series as a level-1 weight-12 modular form and then compares
`q`-expansion coefficients.

## Main statements
* `NiemeierRootless.thetaSeriesUHP_eq_leech_of_even_unimodular_rootless`
-/


namespace SpherePacking.Dim24.Uniqueness.RigidityClassify
noncomputable section

open scoped RealInnerProductSpace

open Complex UpperHalfPlane

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace NiemeierRootless

open MeasureTheory
open TopologicalSpace
open scoped CongruenceSubgroup MatrixGroups ModularForm
open scoped BigOperators
open ModularFormClass

variable (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The real number `1` is a strict period for the level-1 congruence subgroup. -/
public lemma one_mem_strictPeriods_Gamma1 :
    (1 : ℝ) ∈ (Γ(1) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

/-- Convenience lemma: `0 < (1 : ℝ)`. -/
public lemma zero_lt_one_real : (0 : ℝ) < (1 : ℝ) := by norm_num

/-- The point `u + I` lies in the upper half-plane for all real `u`. -/
public lemma im_add_I_pos (u : ℝ) : 0 < ((u + (Complex.I : ℂ)) : ℂ).im := by simp

/-- The `q`-parameter on the horizontal line `u + I` has constant norm `exp (-2π)`. -/
public lemma norm_qParam_add_I (u : ℝ) :
    ‖Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I)‖ = Real.exp (-2 * Real.pi) := by
  simp [Function.Periodic.norm_qParam]

omit [DiscreteTopology L] [IsZLattice ℝ L] in
/-- Along the line `u + I`, the norm of `thetaTerm` depends only on the imaginary part. -/
public lemma norm_thetaTerm_add_I (u : ℝ) (z : L) :
    ‖thetaTerm L ((u : ℂ) + Complex.I) z‖ = ‖thetaTerm L (Complex.I : ℂ) z‖ := by
  simp [norm_thetaTerm]

/-- Continuity of `qParam` on the line `u + I`. -/
public lemma continuous_qParam_add_I :
    Continuous fun u : ℝ => Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I) := by
  dsimp [Function.Periodic.qParam]
  fun_prop

/-- The `q`-parameter does not vanish on the line `u + I`. -/
public lemma qParam_ne_zero_add_I (u : ℝ) :
    Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I) ≠ 0 := by
  simp [Function.Periodic.qParam]

omit [DiscreteTopology L] [IsZLattice ℝ L] in
/-- Continuity of `thetaTerm` on the line `u + I`. -/
public lemma continuous_thetaTerm_add_I (z : L) :
    Continuous fun u : ℝ => thetaTerm L ((u : ℂ) + Complex.I) z := by
  dsimp [thetaTerm]
  fun_prop

/-- The continuous integrand `u ↦ q(u+I)^{-n} * thetaTerm L (u+I) z`. -/
public abbrev qParamPowInvMulThetaTerm (n : ℕ) (z : L) : C(ℝ, ℂ) :=
  ContinuousMap.mk
    (fun u : ℝ =>
      (Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I) ^ n)⁻¹ *
        thetaTerm L ((u : ℂ) + Complex.I) z)
    (by
      have hne_pow :
          ∀ u : ℝ,
            Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I) ^ n ≠ 0 := by
        intro u
        exact pow_ne_zero n (qParam_ne_zero_add_I (u := u))
      have hcont_pow :
          Continuous fun u : ℝ =>
            Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I) ^ n :=
        (continuous_qParam_add_I.pow _)
      have hcont_inv :
          Continuous fun u : ℝ =>
            (Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I) ^ n)⁻¹ :=
        hcont_pow.inv₀ hne_pow
      have hcont_theta : Continuous fun u : ℝ => thetaTerm L ((u : ℂ) + Complex.I) z :=
        continuous_thetaTerm_add_I (L := L) z
      simpa [mul_assoc] using! hcont_inv.mul hcont_theta)

omit [DiscreteTopology L] [IsZLattice ℝ L] in
/-- Evaluation lemma for `qParamPowInvMulThetaTerm`. -/
@[simp]
public lemma qParamPowInvMulThetaTerm_apply (n : ℕ) (z : L) (u : ℝ) :
    qParamPowInvMulThetaTerm (L := L) n z u =
      (Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I) ^ n)⁻¹ *
        thetaTerm L ((u : ℂ) + Complex.I) z :=
  rfl

omit [DiscreteTopology L] [IsZLattice ℝ L] in
/-- Rewrite `qParam^{-n} * thetaTerm` as a single complex exponential under `‖z‖^2 = 2m`. -/
public lemma qParamPowInvMulThetaTerm_fun_eq_exp (n : ℕ) (z : L) (m : ℕ)
    (hm : ‖(z : ℝ²⁴)‖ ^ 2 = (2 : ℝ) * m) :
    (fun u : ℝ =>
        (Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I) ^ n)⁻¹ *
          thetaTerm L ((u : ℂ) + Complex.I) z) =
      fun u : ℝ =>
        Complex.exp
          ((((m : ℂ) - n) * ((2 * (Real.pi : ℝ)) * Complex.I)) * ((u : ℂ) + Complex.I)) := by
  funext u
  set ξ : ℂ := (u : ℂ) + Complex.I
  have hmC : ((‖(z : ℝ²⁴)‖ ^ 2 : ℝ) : ℂ) = (2 : ℂ) * (m : ℂ) := by
    exact_mod_cast hm
  let T : ℂ := ((2 * (Real.pi : ℝ)) * Complex.I)
  have hq : Function.Periodic.qParam (1 : ℝ) ξ = Complex.exp (T * ξ) := by
    simp [Function.Periodic.qParam, T, ξ, mul_assoc, div_one]
  have hqpow : Function.Periodic.qParam (1 : ℝ) ξ ^ n = Complex.exp ((n : ℕ) * (T * ξ)) := by
    calc
      Function.Periodic.qParam (1 : ℝ) ξ ^ n = (Complex.exp (T * ξ)) ^ n := by simp [hq]
      _ = Complex.exp ((n : ℕ) * (T * ξ)) := by
        simpa using! (Complex.exp_nat_mul (T * ξ) n).symm
  have hqinv :
      (Function.Periodic.qParam (1 : ℝ) ξ ^ n)⁻¹ = Complex.exp (-((n : ℕ) * (T * ξ))) := by
    rw [hqpow]
    simpa using! (Complex.exp_neg ((n : ℕ) * (T * ξ))).symm
  have hθ : thetaTerm L ξ z = Complex.exp ((m : ℂ) * T * ξ) := by
    dsimp [thetaTerm, T]
    simp [hmC, ξ, mul_assoc, mul_left_comm, mul_comm]
  calc
    (Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I) ^ n)⁻¹ *
        thetaTerm L ((u : ℂ) + Complex.I) z
        =
        (Function.Periodic.qParam (1 : ℝ) ξ ^ n)⁻¹ * thetaTerm L ξ z := by
          simp [ξ]
    _ = Complex.exp (-((n : ℕ) * (T * ξ))) * Complex.exp ((m : ℂ) * T * ξ) := by
          simp [hqinv, hθ]
    _ = Complex.exp (-((n : ℕ) * (T * ξ)) + (m : ℂ) * T * ξ) := by
          simpa using!
            (Complex.exp_add (-((n : ℕ) * (T * ξ))) ((m : ℂ) * T * ξ)).symm
    _ = Complex.exp (((m : ℂ) - n) * T * ξ) := by
          congr 1
          ring
    _ = Complex.exp
          ((((m : ℂ) - n) * ((2 * (Real.pi : ℝ)) * Complex.I)) * ((u : ℂ) + Complex.I)) := by
          simp [ξ, T, mul_assoc]

/-- Summability of the restricted sup norms of `qParamPowInvMulThetaTerm` on `[0,1]`. -/
public lemma summable_norm_restrict_qParamPowInvMulThetaTerm (n : ℕ) :
    Summable fun z : L =>
      ‖(qParamPowInvMulThetaTerm (L := L) n z).restrict
          (⟨Set.uIcc (0 : ℝ) 1, isCompact_uIcc⟩ : Compacts ℝ)‖ := by
  have hS : Summable fun z : L => thetaTerm L (Complex.I : ℂ) z :=
    summable_thetaTerm (L := L) (τ := (Complex.I : ℂ)) (by simp)
  have hSn : Summable fun z : L => ‖thetaTerm L (Complex.I : ℂ) z‖ := hS.norm
  have hSnC :
      Summable fun z : L =>
        (Real.exp (2 * (n : ℝ) * Real.pi) : ℝ) * ‖thetaTerm L (Complex.I : ℂ) z‖ :=
    hSn.mul_left (Real.exp (2 * (n : ℝ) * Real.pi) : ℝ)
  refine hSnC.of_nonneg_of_le (fun _ => by positivity) ?_
  intro z
  have hbound :
      ‖(qParamPowInvMulThetaTerm (L := L) n z).restrict
          (⟨Set.uIcc (0 : ℝ) 1, isCompact_uIcc⟩ : Compacts ℝ)‖
        ≤ (Real.exp (2 * (n : ℝ) * Real.pi) : ℝ) * ‖thetaTerm L (Complex.I : ℂ) z‖ := by
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro u
    have hq :
        ‖(Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I) ^ n)⁻¹‖ =
          (Real.exp (2 * (n : ℝ) * Real.pi) : ℝ) := by
      have hq0 :
          ‖Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I)‖ = Real.exp (-2 * Real.pi) := by
        simpa using! (norm_qParam_add_I (u := (u : ℝ)))
      have hpow :
          (Real.exp (-2 * Real.pi) : ℝ) ^ n = Real.exp ((n : ℝ) * (-2 * Real.pi)) := by
        simpa using! (Real.exp_nat_mul (-2 * Real.pi) n).symm
      calc
        ‖(Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I) ^ n)⁻¹‖
            = (‖Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I)‖ ^ n)⁻¹ := by
                simp [norm_pow]
        _ = ((Real.exp (-2 * Real.pi)) ^ n)⁻¹ := by simp [hq0]
        _ = (Real.exp ((n : ℝ) * (-2 * Real.pi)))⁻¹ := by
            simpa using! congrArg Inv.inv hpow
        _ = Real.exp (-((n : ℝ) * (-2 * Real.pi))) := by simp [Real.exp_neg]
        _ = (Real.exp (2 * (n : ℝ) * Real.pi) : ℝ) := by
            congr 1
            ring
    simp_all
  exact hbound

/-- Swap `tsum` and interval integral for the family `qParamPowInvMulThetaTerm`. -/
public lemma intervalIntegral_tsum_intervalIntegral_qParamPowInvMulThetaTerm_eq (n : ℕ) :
    (∫ u : ℝ in (0 : ℝ)..1, ∑' z : L, qParamPowInvMulThetaTerm (L := L) n z u) =
      ∑' z : L, ∫ u : ℝ in (0 : ℝ)..1, qParamPowInvMulThetaTerm (L := L) n z u := by
  let K : Compacts ℝ := ⟨Set.uIcc (0 : ℝ) 1, isCompact_uIcc⟩
  let fz : L → C(ℝ, ℂ) := fun z => qParamPowInvMulThetaTerm (L := L) n z
  have hsum : Summable fun z : L => ‖(fz z).restrict K‖ := by
    simpa [fz, K] using! (summable_norm_restrict_qParamPowInvMulThetaTerm (L := L) (n := n))
  exact Eq.symm (intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hsum)

/-- The integral of `u ↦ exp(2π i k u)` over `[0,1]` is `1` if `k = 0` and `0` otherwise. -/
public lemma intervalIntegral_cexp_two_pi_mul_I_int (k : ℤ) :
    (∫ u : ℝ in (0 : ℝ)..1,
        Complex.exp (((k : ℂ) * ((2 * (Real.pi : ℝ)) * Complex.I)) * u)) =
      if k = 0 then (1 : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp
  · let c : ℂ := (k : ℂ) * ((2 * (Real.pi : ℝ)) * Complex.I)
    have hc : c ≠ 0 := by
      have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      have hpi : ((2 * (Real.pi : ℝ)) : ℂ) ≠ 0 := by
        norm_cast
        nlinarith [Real.pi_pos]
      have hI : (Complex.I : ℂ) ≠ 0 := by
        exact Complex.I_ne_zero
      exact mul_ne_zero hk' (mul_ne_zero hpi hI)
    have hInt := integral_exp_mul_complex (a := (0 : ℝ)) (b := 1) (c := c) hc
    have hper : Complex.exp c = 1 :=
      exp_int_mul_two_pi_mul_I k
    have : (∫ u : ℝ in (0 : ℝ)..1, Complex.exp (c * u)) = 0 := by
      simp [hInt, hper, c]
    simpa [c, hk, if_neg hk] using! this

/-- Special case of `intervalIntegral_cexp_two_pi_mul_I_int` when `k ≠ 0`. -/
public lemma intervalIntegral_cexp_two_pi_mul_I_int_eq_zero_of_ne_zero {k : ℤ} (hk : k ≠ 0) :
    (∫ u : ℝ in (0 : ℝ)..1,
        Complex.exp (((k : ℂ) * ((2 * (Real.pi : ℝ)) * Complex.I)) * u)) = 0 := by
  simpa [if_neg hk] using! (intervalIntegral_cexp_two_pi_mul_I_int (k := k))

/-- Split `exp (A * (u + I))` as `exp (A*u) * exp (A*I)`. -/
public lemma exp_mul_add_I_split (A : ℂ) :
    (fun u : ℝ => Complex.exp (A * ((u : ℂ) + Complex.I))) =
      fun u : ℝ => Complex.exp (A * (u : ℂ)) * Complex.exp (A * Complex.I) := by
  funext u
  simp [mul_add, Complex.exp_add]

/-- If `k ≠ 0`, then integrating `exp(2π i k (u + I))` over `u ∈ [0,1]` gives `0`. -/
public lemma intervalIntegral_cexp_two_pi_mul_I_int_mul_add_I_eq_zero_of_ne_zero {k : ℤ}
    (hk : k ≠ 0) :
    (∫ u : ℝ in (0 : ℝ)..1,
        Complex.exp
          (((k : ℂ) * ((2 * (Real.pi : ℝ)) * Complex.I)) * ((u : ℂ) + Complex.I))) = 0 := by
  let A : ℂ := (k : ℂ) * ((2 * (Real.pi : ℝ)) * Complex.I)
  have hint0 :
      (∫ u : ℝ in (0 : ℝ)..1,
          Complex.exp (((k : ℂ) * ((2 * (Real.pi : ℝ)) * Complex.I)) * u)) = 0 :=
    intervalIntegral_cexp_two_pi_mul_I_int_eq_zero_of_ne_zero (k := k) hk
  rw [exp_mul_add_I_split (A := A)]
  calc
    (∫ u : ℝ in (0 : ℝ)..1, Complex.exp (A * (u : ℂ)) * Complex.exp (A * Complex.I)) =
        (∫ u : ℝ in (0 : ℝ)..1,
            Complex.exp (((k : ℂ) * ((2 * (Real.pi : ℝ)) * Complex.I)) * u)) *
          Complex.exp (A * Complex.I) := by
          simp [intervalIntegral.integral_mul_const, A, mul_assoc]
    _ = 0 := by simp [hint0]

/-- The constant term of the theta series (as a modular form) is `1`. -/
public lemma qExpansion_coeff_zero_thetaSeries
    (hEven : EvenNormSq L)
    (f : ModularForm Γ(1) (12 : ℤ)) (hf : ∀ z : ℍ, f z = thetaSeriesUHP L z) :
    (qExpansion (1 : ℝ) f).coeff 0 = (1 : ℂ) := by
  have hper := one_mem_strictPeriods_Gamma1
  have h01 := zero_lt_one_real
  have hcoeff0 :=
    ModularFormClass.qExpansion_coeff_eq_intervalIntegral (f := f) (h := (1 : ℝ)) h01 hper 0 h01
  have hcoeff := by simpa using! hcoeff0
  have hτpos : ∀ u : ℝ, 0 < (u + (Complex.I : ℂ)).im := im_add_I_pos
  have hrewrite :
      (fun u : ℝ => f ⟨u + (Complex.I : ℂ), hτpos u⟩) =
        fun u : ℝ => ∑' z : L, thetaTerm L (u + (Complex.I : ℂ)) z := by
    funext u
    simp [hf, thetaSeriesUHP, thetaSeries]
  let K : Compacts ℝ := ⟨Set.uIcc (0 : ℝ) 1, isCompact_uIcc⟩
  let fz : L → C(ℝ, ℂ) := fun z =>
    ContinuousMap.mk (fun u : ℝ => thetaTerm L (u + (Complex.I : ℂ)) z) (by
      dsimp [thetaTerm]; fun_prop)
  have hsum :
      Summable fun z : L =>
        ‖(fz z).restrict K‖ := by
    have hS : Summable fun z : L => thetaTerm L (Complex.I : ℂ) z :=
      summable_thetaTerm (L := L) (τ := (Complex.I : ℂ)) (by simp)
    have hSn : Summable fun z : L => ‖thetaTerm L (Complex.I : ℂ) z‖ := hS.norm
    refine hSn.of_nonneg_of_le (fun _ => by positivity) ?_
    intro z
    have hbound :
        ‖(fz z).restrict K‖
          ≤ ‖thetaTerm L (Complex.I : ℂ) z‖ := by
      apply (ContinuousMap.norm_le _ (by positivity)).2
      intro u
      have hnorm :
          ‖thetaTerm L ((u : ℝ) + (Complex.I : ℂ)) z‖ = ‖thetaTerm L (Complex.I : ℂ) z‖ := by
        simp [norm_thetaTerm]
      have hrestrict : ‖(fz z).restrict K u‖ = ‖thetaTerm L ((u : ℝ) + (Complex.I : ℂ)) z‖ := by
        simp [fz, K]
      exact le_of_eq (hrestrict.trans hnorm)
    exact hbound
  have hswap :
      (∫ u : ℝ in (0 : ℝ)..1, ∑' z : L, thetaTerm L (u + (Complex.I : ℂ)) z) =
        ∑' z : L, ∫ u : ℝ in (0 : ℝ)..1, thetaTerm L (u + (Complex.I : ℂ)) z := by
    simpa [fz, K] using!
      (intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm (a := (0 : ℝ)) (b := 1)
        (f := fz) hsum).symm
  have : (qExpansion (1 : ℝ) f).coeff 0 =
      ∑' z : L, ∫ u : ℝ in (0 : ℝ)..1, thetaTerm L (u + (Complex.I : ℂ)) z := by
    simpa [hrewrite, hswap] using! hcoeff
  have hterm0 :
      (∫ u : ℝ in (0 : ℝ)..1, thetaTerm L (u + (Complex.I : ℂ)) (0 : L)) = (1 : ℂ) := by
    simp [thetaTerm]
  have hterm_ne (z : L) (hz : z ≠ 0) :
      (∫ u : ℝ in (0 : ℝ)..1, thetaTerm L (u + (Complex.I : ℂ)) z) = 0 := by
    rcases hEven (z : ℝ²⁴) z.property with ⟨m, hm⟩
    have hm0 : m ≠ 0 := by
      intro hm0'
      have : ‖(z : ℝ²⁴)‖ ^ 2 = 0 := by simpa [hm0'] using! hm
      have : ‖(z : ℝ²⁴)‖ = 0 := by nlinarith [this]
      exact hz (Subtype.ext (by simpa using! (norm_eq_zero.mp this)))
    have hrewrite_z :
        (fun u : ℝ => thetaTerm L (u + (Complex.I : ℂ)) z) =
          fun u : ℝ =>
            Complex.exp ((m : ℂ) * ((2 * (Real.pi : ℝ)) * Complex.I) * ((u : ℂ) + Complex.I)) := by
      -- Specialize the shared rewrite lemma to `n = 0` (i.e. no `qParam` factor).
      simpa [sub_zero, pow_zero, mul_assoc] using!
        (qParamPowInvMulThetaTerm_fun_eq_exp (L := L) (n := 0) (z := z) (m := m) hm)
    have :
        (∫ u : ℝ in (0 : ℝ)..1,
            Complex.exp
              ((m : ℂ) * ((2 * (Real.pi : ℝ)) * Complex.I) * ((u : ℂ) + Complex.I))) = 0 := by
      have hm0Z : (m : ℤ) ≠ 0 := by exact_mod_cast hm0
      simpa [mul_assoc] using!
        (intervalIntegral_cexp_two_pi_mul_I_int_mul_add_I_eq_zero_of_ne_zero (k := (m : ℤ)) hm0Z)
    simpa [hrewrite_z] using! this
  have htsum :
      (∑' z : L, ∫ u : ℝ in (0 : ℝ)..1, thetaTerm L (u + (Complex.I : ℂ)) z) = (1 : ℂ) := by
    simpa [hterm0] using!
      (tsum_eq_single (0 : L) (fun z hz => hterm_ne z hz))
  simpa [htsum] using! this

/-- For a rootless lattice, the `q` coefficient of the theta series (as a modular form) is `0`. -/
public lemma qExpansion_coeff_one_thetaSeries_of_rootless
    (hEven : EvenNormSq L) (hRootless : Rootless L)
    (f : ModularForm Γ(1) (12 : ℤ)) (hf : ∀ z : ℍ, f z = thetaSeriesUHP L z) :
    (qExpansion (1 : ℝ) f).coeff 1 = (0 : ℂ) := by
  have hper := one_mem_strictPeriods_Gamma1
  have h01 := zero_lt_one_real
  have hcoeff0 :=
    ModularFormClass.qExpansion_coeff_eq_intervalIntegral (f := f) (h := (1 : ℝ)) h01 hper 1 h01
  have hcoeff := by simpa using! hcoeff0
  have hτpos : ∀ u : ℝ, 0 < (u + (Complex.I : ℂ)).im := im_add_I_pos
  have hrewrite :
      (fun u : ℝ =>
          (Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I))⁻¹ *
            f ⟨(u : ℂ) + Complex.I, hτpos u⟩) =
        fun u : ℝ =>
          ∑' z : L,
            (Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I))⁻¹ *
              thetaTerm L ((u : ℂ) + Complex.I) z := by
    funext u
    simp only [hf, thetaSeriesUHP, thetaSeries]
    exact Eq.symm tsum_mul_left
  have hswap :
      (∫ u : ℝ in (0 : ℝ)..1,
          ∑' z : L,
            (Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I))⁻¹ *
              thetaTerm L ((u : ℂ) + Complex.I) z) =
        ∑' z : L,
          ∫ u : ℝ in (0 : ℝ)..1,
            (Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I))⁻¹ *
              thetaTerm L ((u : ℂ) + Complex.I) z := by
    simpa [qParamPowInvMulThetaTerm_apply, pow_one] using!
      (intervalIntegral_tsum_intervalIntegral_qParamPowInvMulThetaTerm_eq (L := L) (n := 1))
  have hcoeff' :
      (qExpansion (1 : ℝ) f).coeff 1 =
        ∑' z : L,
          ∫ u : ℝ in (0 : ℝ)..1,
            (Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I))⁻¹ *
              thetaTerm L ((u : ℂ) + Complex.I) z := by
    simpa [hrewrite, hswap] using! hcoeff
  have hterm : ∀ z : L,
      (∫ u : ℝ in (0 : ℝ)..1,
          (Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I))⁻¹ *
            thetaTerm L ((u : ℂ) + Complex.I) z) = (0 : ℂ) := by
    intro z
    rcases hEven (z : ℝ²⁴) z.property with ⟨m, hm⟩
    let k : ℤ := (m : ℤ) - 1
    let A : ℂ := (k : ℂ) * ((2 * (Real.pi : ℝ)) * Complex.I)
    have hk : k ≠ 0 := by
      by_cases hz : z = 0
      · subst hz
        have hm0 : m = 0 := by
          have hm0' : (2 : ℝ) * (m : ℝ) = 0 := by simpa using! hm.symm
          have hm0'' : (m : ℝ) = 0 := by nlinarith
          exact_mod_cast hm0''
        subst hm0
        simp [k]
      · intro hk0
        have hm1Z : (m : ℤ) = 1 := by
          have : (m : ℤ) - 1 = 0 := by simpa [k] using! hk0
          linarith
        have hm1 : m = 1 := by exact_mod_cast hm1Z
        have h2 : ‖(z : ℝ²⁴)‖ ^ 2 = (2 : ℝ) := by
          simpa [hm1] using! hm
        have hz0 : (z : ℝ²⁴) ≠ 0 := by
          intro hz0
          apply hz
          exact Subtype.ext hz0
        exact (hRootless (z : ℝ²⁴) z.property hz0) h2
    have hrewrite_z :
        (fun u : ℝ =>
            (Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I))⁻¹ *
              thetaTerm L ((u : ℂ) + Complex.I) z) =
          fun u : ℝ => Complex.exp (A * ((u : ℂ) + Complex.I)) := by
      have hk_cast : (k : ℂ) = (m : ℂ) - 1 := by simp [k]
      simpa [pow_one, A, hk_cast, mul_assoc] using!
        (qParamPowInvMulThetaTerm_fun_eq_exp (L := L) (n := 1) (z := z) (m := m) hm)
    have :
        (∫ u : ℝ in (0 : ℝ)..1, Complex.exp (A * ((u : ℂ) + Complex.I))) = 0 := by
      simpa [A, mul_assoc] using!
        (intervalIntegral_cexp_two_pi_mul_I_int_mul_add_I_eq_zero_of_ne_zero (k := k) hk)
    simpa [hrewrite_z] using! this
  have htsum :
      (∑' z : L,
          ∫ u : ℝ in (0 : ℝ)..1,
            (Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I))⁻¹ *
              thetaTerm L ((u : ℂ) + Complex.I) z) = (0 : ℂ) := by
    have hfun :
        (fun z : L =>
            ∫ u : ℝ in (0 : ℝ)..1,
              (Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I))⁻¹ *
                thetaTerm L ((u : ℂ) + Complex.I) z) =
          fun _ : L => (0 : ℂ) := by
      funext z
      simpa using! hterm z
    simp [hfun]
  simpa [htsum] using! hcoeff'

/-!
### Δ-scalar elimination (shared with `ThetaExtremal.lean`)
-/

/-- The `q` coefficient of `c • Δ` is `c`. -/
public lemma qExpansion_coeff_one_smul_Delta (c : ℂ) :
    (qExpansion 1 (c • Delta)).coeff 1 = c := by
  have hqs : qExpansion 1 (c • Delta) = c • qExpansion 1 Delta := by
    simpa using! ModularForm.qExpansion_smul (Γ := Γ(1)) (h := (1 : ℝ)) (k := (12 : ℤ))
      (by norm_num) (by simp [CongruenceSubgroup.strictPeriods_Gamma]) c Delta
  have hqs1 := congrArg (fun F : PowerSeries ℂ => F.coeff 1) hqs
  simpa [Delta_q_one_term] using! hqs1

/-- If `c • Δ` has vanishing `q` coefficient, then `c = 0`. -/
public lemma c_eq_zero_of_smul_Delta_eq_of_qExpansion_coeff_one_eq_zero
    {gCF : CuspForm Γ(1) (12 : ℤ)} {c : ℂ}
    (hc : c • Delta = gCF) (hq1 : (qExpansion 1 gCF).coeff 1 = 0) :
    c = 0 := by
  have hcc :
      (qExpansion 1 (c • Delta)).coeff 1 = (qExpansion 1 gCF).coeff 1 := by
    simpa using! congrArg (fun F : CuspForm Γ(1) (12 : ℤ) => (qExpansion 1 F).coeff 1) hc
  have : (qExpansion 1 (c • Delta)).coeff 1 = 0 := by
    simpa [hq1] using! hcc
  simpa [qExpansion_coeff_one_smul_Delta (c := c)] using! this

/-- A weight-12 level-1 modular form is zero if its `q^0` and `q^1` coefficients vanish. -/
public lemma modularForm_eq_zero_of_qExpansion_coeff_zero_eq_zero_of_qExpansion_coeff_one_eq_zero
    (g : ModularForm Γ(1) (12 : ℤ))
    (hg0 : (qExpansion 1 g).coeff 0 = 0) (hg1 : (qExpansion 1 g).coeff 1 = 0) :
    g = 0 := by
  have hgCusp : IsCuspForm Γ(1) (12 : ℤ) g :=
    (IsCuspForm_iff_coeffZero_eq_zero (k := (12 : ℤ)) g).2 hg0
  let gCF : CuspForm Γ(1) (12 : ℤ) := IsCuspForm_to_CuspForm Γ(1) (12 : ℤ) g hgCusp
  have hgCF_coe : (gCF : ℍ → ℂ) = g := by
    simpa [gCF] using! CuspForm_to_ModularForm_Fun_coe Γ(1) (12 : ℤ) g hgCusp
  have hr : Module.finrank ℂ (CuspForm Γ(1) (12 : ℤ)) = 1 := by
    have e := CuspForms_iso_Modforms (12 : ℤ)
    apply Module.finrank_eq_of_rank_eq
    rw [LinearEquiv.rank_eq e]
    have h0 : Module.rank ℂ (ModularForm Γ(1) 0) = 1 := by
      have key : ∀ (G : Subgroup (GL (Fin 2) ℝ)) [G.HasDetOne],
          G = (Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range →
          Module.rank ℂ (ModularForm G 0) = 1 := by
        rintro G _ rfl
        exact ModularForm.levelOne_weight_zero_rank_one
      exact key _ (by rw [CongruenceSubgroup.Gamma_one_top, MonoidHom.range_eq_map])
    simpa using! h0
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' Delta Delta_ne_zero).1 hr gCF
  have hc0 : c = 0 := by
    have hqg : qExpansion 1 gCF = qExpansion 1 g := qExpansion_ext2 gCF g hgCF_coe
    have hq1gCF : (qExpansion 1 gCF).coeff 1 = 0 := by simpa [hqg] using! hg1
    exact c_eq_zero_of_smul_Delta_eq_of_qExpansion_coeff_one_eq_zero
      (gCF := gCF) (c := c) hc hq1gCF
  have hgCF0 : gCF = 0 := by
    have : (0 : ℂ) • Delta = gCF := by simpa [hc0] using! hc
    simpa using! this.symm
  ext z
  have hz := congrArg (fun F : CuspForm Γ(1) (12 : ℤ) => F z) hgCF0
  simpa [hgCF_coe] using! hz

/-- The theta series of an even unimodular rootless lattice agrees with the Leech theta series. -/
public theorem thetaSeriesUHP_eq_leech_of_even_unimodular_rootless
    (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L] [IsZLattice ℝ L]
    (hEven : EvenNormSq L) (hUnimod : Unimodular L) (hRootless : Rootless L) :
    (∀ z : UpperHalfPlane, thetaSeriesUHP L z = thetaSeriesUHP LeechLattice z) := by
  obtain ⟨fL, hfL⟩ := thetaSeries_is_modularForm_weight12 (L := L) hEven hUnimod
  haveI : DiscreteTopology LeechLattice :=
    Uniqueness.RigidityClassify.instDiscreteTopology_of_even_rootless
      (L := LeechLattice) leech_evenNormSq leech_rootless
  haveI : IsZLattice ℝ LeechLattice :=
    IsZLatticeOfUnimodular.isZLattice_of_unimodular_work (L := LeechLattice) leech_unimodular
  obtain ⟨fLeech, hfLeech⟩ :=
    thetaSeries_is_modularForm_weight12 (L := LeechLattice) leech_evenNormSq
      leech_unimodular
  let g : ModularForm Γ(1) (12 : ℤ) := fL - fLeech
  have hg0 : (qExpansion 1 g).coeff 0 = 0 := by
    have hq := qExpansion_sub1 (f := fL) (g := fLeech)
    have h0L : (qExpansion 1 fL).coeff 0 = 1 := by
      simpa using! qExpansion_coeff_zero_thetaSeries (L := L) hEven fL hfL
    have h0Leech : (qExpansion 1 fLeech).coeff 0 = 1 := by
      simpa using!
        qExpansion_coeff_zero_thetaSeries (L := LeechLattice)
          leech_evenNormSq fLeech hfLeech
    have hq0 :=
      congrArg (fun F : PowerSeries ℂ => PowerSeries.constantCoeff F) (by simpa [g] using! hq)
    have h0L' : PowerSeries.constantCoeff (qExpansion 1 fL) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using! h0L
    have h0Leech' : PowerSeries.constantCoeff (qExpansion 1 fLeech) = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using! h0Leech
    have : PowerSeries.constantCoeff (qExpansion 1 g) = 0 := by
      simpa [g, h0L', h0Leech'] using! hq0
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using! this
  have hg1 : (qExpansion 1 g).coeff 1 = 0 := by
    have hq := qExpansion_sub1 (f := fL) (g := fLeech)
    have hq1 := congrArg (fun F : PowerSeries ℂ => F.coeff 1) (by simpa [g] using! hq)
    have h1L : (qExpansion 1 fL).coeff 1 = 0 := by
      simpa using!
        qExpansion_coeff_one_thetaSeries_of_rootless (L := L) hEven hRootless fL hfL
    have h1Leech : (qExpansion 1 fLeech).coeff 1 = 0 := by
      simpa using!
        qExpansion_coeff_one_thetaSeries_of_rootless (L := LeechLattice)
          leech_evenNormSq leech_rootless fLeech hfLeech
    simpa [g, h1L, h1Leech] using! hq1
  have hgzero : g = 0 :=
    modularForm_eq_zero_of_qExpansion_coeff_zero_eq_zero_of_qExpansion_coeff_one_eq_zero
      (g := g) hg0 hg1
  intro z
  have : fL z = fLeech z := by
    have hz := congrArg (fun F : ModularForm Γ(1) (12 : ℤ) => F z) hgzero
    have : fL z - fLeech z = 0 := by simpa [g] using! hz
    exact sub_eq_zero.mp this
  simpa [hfL, hfLeech] using! this

end NiemeierRootless

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
