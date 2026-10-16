import E8Leech.UniformCuspExpansion
import E8Leech.LeechCuspUniformBounds

/-!
# Uniform Leech kernel cusp remainders on compact parameter sets

The second-order cancellations in the Leech kernels hold uniformly in the
left variable on compact subsets of the upper half plane. This also applies
when the compact parameter set contains the self-dual point i.
-/

noncomputable section
namespace E8Leech
open Complex Filter Topology Set Asymptotics
open UpperHalfPlane hiding I
open scoped Real Manifold

theorem continuous_leechMinusAlpha : Continuous leechMinusAlpha := by
  have h4 := ModularFormClass.continuous ModularForm.E₄
  have h6 := ModularFormClass.continuous ModularForm.E₆
  have hψ₁ := (mdifferentiable_ckmrvPsiBasis 1).continuous
  have hψ₂ := (mdifferentiable_ckmrvPsiBasis 2).continuous
  unfold leechMinusAlpha
  fun_prop

theorem continuous_leechMinusBeta : Continuous leechMinusBeta := by
  have h4 := ModularFormClass.continuous ModularForm.E₄
  have h6 := ModularFormClass.continuous ModularForm.E₆
  have hΔ := mdifferentiable_modularDiscriminant.continuous
  have hψ₁ := (mdifferentiable_ckmrvPsiBasis 1).continuous
  have hψ₂ := (mdifferentiable_ckmrvPsiBasis 2).continuous
  unfold leechMinusBeta leechMinusAlpha
  fun_prop

theorem continuous_leechMinusGamma : Continuous leechMinusGamma := by
  have h4 := ModularFormClass.continuous ModularForm.E₄
  have h6 := ModularFormClass.continuous ModularForm.E₆
  have hJ := continuous_kleinModularJ
  have hψ₁ := (mdifferentiable_ckmrvPsiBasis 1).continuous
  have hψ₂ := (mdifferentiable_ckmrvPsiBasis 2).continuous
  unfold leechMinusGamma leechMinusAlpha
  fun_prop

theorem continuous_leechPlusA0 : Continuous leechPlusA0 := by
  have h4 := ModularFormClass.continuous ModularForm.E₄
  have h6 := ModularFormClass.continuous ModularForm.E₆
  have hτ : Continuous (fun τ : ℍ => (τ : ℂ)) := UpperHalfPlane.continuous_coe
  unfold leechPlusA0
  fun_prop

theorem continuous_leechPlusA1 : Continuous leechPlusA1 := by
  have hΔ := mdifferentiable_modularDiscriminant.continuous
  have hφ₁ := (mdifferentiable_ckmrvPhiBasis 1).continuous
  unfold leechPlusA1
  fun_prop

theorem continuous_leechPlusA2 : Continuous leechPlusA2 := by
  have h4 := ModularFormClass.continuous ModularForm.E₄
  have h6 := ModularFormClass.continuous ModularForm.E₆
  have hφ₂ := (mdifferentiable_ckmrvPhiBasis 2).continuous
  unfold leechPlusA2
  fun_prop

theorem continuous_leechPlusP0 : Continuous leechPlusP0 := by
  have h4 := ModularFormClass.continuous ModularForm.E₄
  have h6 := ModularFormClass.continuous ModularForm.E₆
  have hΔ := mdifferentiable_modularDiscriminant.continuous
  have hJ := continuous_kleinModularJ
  have hτ : Continuous (fun τ : ℍ => (τ : ℂ)) := UpperHalfPlane.continuous_coe
  have hφ₁ := (mdifferentiable_ckmrvPhiBasis 1).continuous
  have hφ₂ := (mdifferentiable_ckmrvPhiBasis 2).continuous
  unfold leechPlusP0 leechPlusA0 leechPlusA1 leechPlusA2
  fun_prop

theorem continuous_leechPlusP2 : Continuous leechPlusP2 := by
  have h4 := ModularFormClass.continuous ModularForm.E₄
  have h6 := ModularFormClass.continuous ModularForm.E₆
  have hΔ := mdifferentiable_modularDiscriminant.continuous
  have hJ := continuous_kleinModularJ
  have hτ : Continuous (fun τ : ℍ => (τ : ℂ)) := UpperHalfPlane.continuous_coe
  have hφ₁ := (mdifferentiable_ckmrvPhiBasis 1).continuous
  have hφ₂ := (mdifferentiable_ckmrvPhiBasis 2).continuous
  unfold leechPlusP2 leechPlusA0 leechPlusA1 leechPlusA2
  fun_prop

section Uniform
variable {K : Set ℍ} (hK : IsCompact K)
include hK

local notation "H4" => (HasUniformExp3.of_snd (K := K) hasExp3_eisensteinFour)
local notation "H6" => (HasUniformExp3.of_snd (K := K) hasExp3_eisensteinSix)
local notation "H2" => (HasUniformExp3.of_snd (K := K) hasExp3_eisensteinTwo)
local notation "H14" => (HasUniformExp3.of_snd (K := K) hasExp3_eisensteinFourteen)
local notation "H10" => (HasUniformExp3.of_snd (K := K) hasExp3_eisensteinTen)
local notation "HΔ" => (HasUniformExp3.of_snd (K := K) hasExp3_discriminant)
local notation "HW" => (HasUniformExp3.of_snd (K := K) hasExp3_thetaW)
local notation "HU" => (HasUniformExp3.of_snd (K := K) hasExp3_thetaU_sq_sub_thetaV_sq)
local notation "HL" => (HasUniformExp3.of_snd (K := K) hasExp3_ckmrvL_sub)
local notation "HP" => (HasUniformExp3.of_snd (K := K) hasExp3_discriminantCuspQuot)
local notation "HPi" => (HasUniformExp3.of_snd (K := K) hasExp3_discriminantCuspQuot_inv)

theorem hasUniformExp3_eightMinusDenZ :
    HasUniformExp3 K (fun p => eightMinusDenZ p.1 p.2) (fun _ => -1) (fun _ => 0)
      (fun p => kleinModularJ p.1 - 720) :=
  (((HΔ).mul (HasUniformExp3.of_fst_continuous hK continuous_kleinModularJ)).sub
    ((H4).pow.mul H4)).congr_fun (fun p => by simp only [eightMinusDenZ]; ring)
    |>.congr_coeff (fun p => by ring) (fun p => by ring) (fun p => by ring)

theorem hasUniformExp3_leechDenInv :
    HasUniformExp3 K (fun p => (eightMinusDenZ p.1 p.2 * discriminantCuspQuot p.2)⁻¹)
      (fun _ => -1) (fun _ => 0) (fun p => 696 - kleinModularJ p.1) :=
  (((hasUniformExp3_eightMinusDenZ hK).mul HP).inv_const (by norm_num)).congr_coeff
    (fun p => by ring) (fun p => by ring) (fun p => by ring)

theorem hasUniformExp3_leechMinusNEll_div :
    HasUniformExp3 K (fun p => leechMinusNEll p.1 p.2 *
      (eightMinusDenZ p.1 p.2 * discriminantCuspQuot p.2)⁻¹)
      (fun p => 2 * 1728 * ModularForm.discriminant p.1) (fun _ => 0)
      (fun p => -(2 * 1728) * ModularForm.discriminant p.1 * (720 - kleinModularJ p.1)) := by
  have hc : Continuous (fun τ : ℍ => -(2 * 1728) * ModularForm.discriminant τ) :=
    continuous_const.mul mdifferentiable_modularDiscriminant.continuous
  exact (((H14).fst_mul hK hc).mul (hasUniformExp3_leechDenInv hK)).congr_fun (fun p => rfl)
    |>.congr_coeff (fun p => by ring) (fun p => by ring) (fun p => by ring)

theorem hasUniformExp3_leechMinusNZero :
    HasUniformExp3 K (fun p => leechMinusNZero p.1 p.2)
      (fun p => -leechMinusBeta p.1 - leechMinusAlpha p.1) (fun _ => 0)
      (fun p => leechMinusNZeroC p.1) := by
  have hc : Continuous (fun τ : ℍ => -(2 * 1728) * ModularForm.discriminant τ) :=
    continuous_const.mul mdifferentiable_modularDiscriminant.continuous
  exact ((((((H14).mul HL).fst_mul hK hc).add
    (((HW).mul (hasUniformExp3_eightMinusDenZ hK)).mul
      (HasUniformExp3.of_fst_continuous hK continuous_leechMinusBeta))).add
    (((HΔ).mul HW).mul (HasUniformExp3.of_fst_continuous hK continuous_leechMinusGamma))).sub
    (((H10).mul HU).fst_mul hK continuous_leechMinusAlpha)).congr_fun (fun p => rfl)
    |>.congr_coeff (fun p => by ring) (fun p => by simp only [leechMinusBeta]; ring)
      (fun p => by simp only [leechMinusNZeroC]; ring)

theorem hasUniformExp3_leechMinusNZero_div :
    HasUniformExp3 K (fun p => leechMinusNZero p.1 p.2 *
      (eightMinusDenZ p.1 p.2 * discriminantCuspQuot p.2)⁻¹)
      (fun p => leechMinusBeta p.1 + leechMinusAlpha p.1) (fun _ => 0)
      (fun p => (-leechMinusBeta p.1 - leechMinusAlpha p.1) * (696 - kleinModularJ p.1) -
        leechMinusNZeroC p.1) :=
  ((hasUniformExp3_leechMinusNZero hK).mul (hasUniformExp3_leechDenInv hK)).congr_coeff
    (fun p => by ring) (fun p => by ring) (fun p => by ring)

theorem hasUniformExp3_leechPlusM2 :
    HasUniformExp3 K (fun p => leechPlusM2 p.1 p.2) (fun _ => 0) (fun _ => 0) (fun _ => 0) := by
  have hA0 : Continuous (fun τ : ℍ => 1728 * leechPlusA0 τ) :=
    continuous_const.mul continuous_leechPlusA0
  have hA1 : Continuous (fun τ : ℍ => 2 * 1728 * leechPlusA1 τ) :=
    continuous_const.mul continuous_leechPlusA1
  have hA2 : Continuous (fun τ : ℍ => 1728 * leechPlusA2 τ) :=
    continuous_const.mul continuous_leechPlusA2
  exact (((HPi).mul (((H4).fst_mul hK continuous_leechPlusP0).add
      ((H2).pow.fst_mul hK continuous_leechPlusP2))).add
    ((hasUniformExp3_leechDenInv hK).mul
      (((((H4).mul HΔ).fst_mul hK hA2).sub (((H14).mul H2).fst_mul hK hA1)).add
        (((H2).pow.mul HΔ).fst_mul hK hA0)))).congr_fun (fun p => rfl)
    |>.congr_coeff (fun p => by simp only [leechPlusP0, leechPlusP2]; ring) (fun p => by ring)
      (fun p => by simp only [leechPlusP0, leechPlusP2]; ring)

theorem hasUniformExp3_leechPlusM1 :
    HasUniformExp3 K (fun p => leechPlusM1 p.1 p.2) (fun p => leechPlusM1a p.1)
      (fun _ => 0) (fun p => leechPlusM1c p.1) := by
  have hP2 : Continuous (fun τ : ℍ => leechPlusP2 τ * (-(12 * I / (π : ℂ)))) :=
    continuous_leechPlusP2.mul continuous_const
  have hA1 : Continuous (fun τ : ℍ => 2 * 1728 * leechPlusA1 τ * (6 * I / (π : ℂ))) :=
    (continuous_const.mul continuous_leechPlusA1).mul continuous_const
  have hA0 : Continuous (fun τ : ℍ => 1728 * leechPlusA0 τ * (12 * I / (π : ℂ))) :=
    (continuous_const.mul continuous_leechPlusA0).mul continuous_const
  exact (((HPi).mul ((H2).fst_mul hK hP2)).add
    ((hasUniformExp3_leechDenInv hK).mul
      (((H14).fst_mul hK hA1).sub (((H2).mul HΔ).fst_mul hK hA0)))).congr_fun (fun p => rfl)
    |>.congr_coeff (fun p => by simp only [leechPlusM1a]; ring) (fun p => by ring)
      (fun p => by simp only [leechPlusM1c]; ring)

theorem hasUniformExp3_leechPlusM0 :
    HasUniformExp3 K (fun p => leechPlusM0 p.1 p.2) (fun p => leechPlusM0a p.1)
      (fun _ => 0) (fun p => leechPlusM0c p.1) := by
  have hP2 : Continuous (fun τ : ℍ => leechPlusP2 τ * (-(36 / (π : ℂ) ^ 2))) :=
    continuous_leechPlusP2.mul continuous_const
  have hA0 : Continuous (fun τ : ℍ => 1728 * leechPlusA0 τ * (-(36 / (π : ℂ) ^ 2))) :=
    (continuous_const.mul continuous_leechPlusA0).mul continuous_const
  exact (((HPi).mul (HasUniformExp3.of_fst_continuous hK hP2)).add
    ((hasUniformExp3_leechDenInv hK).mul ((HΔ).fst_mul hK hA0))).congr_fun (fun p => rfl)
    |>.congr_coeff (fun p => by simp only [leechPlusM0a]; ring) (fun p => by ring)
      (fun p => by simp only [leechPlusM0c]; ring)

end Uniform

/-- Multiplying a uniform third-order remainder by s⁻² leaves exponential decay. -/
theorem isBigO_cuspS_sq_inv_mul_uniform {K : Set ℍ} {f : ℍ × ℍ → ℂ} {w : ℍ × ℍ → ℝ}
    (hf : f =O[𝓟 K ×ˢ atImInfty] fun p => w p * ‖cuspS p.2‖ ^ 3) :
    (fun p => (cuspS p.2 ^ 2)⁻¹ * f p) =O[𝓟 K ×ˢ atImInfty]
      fun p => w p * Real.exp (-π * p.2.im) :=
  ((isBigO_snd_of_isBigO isBigO_cuspS_sq_inv K).mul hf).congr_right fun p => by
    rw [norm_cuspS, mul_left_comm, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 2
    push_cast
    ring

theorem isBigO_ckmrvLeechMinusKernel_sub_G_uniform {K : Set ℍ} (hK : IsCompact K) :
    (fun p : ℍ × ℍ => ckmrvLeechMinusKernel p.1 p.2 - ckmrvLeechMinusG p.1 p.2)
      =O[𝓟 K ×ˢ atImInfty] fun p => ‖(p.2 : ℂ)‖ * Real.exp (-π * p.2.im) := by
  have hsum := ((isBigO_snd_of_isBigO isBigO_ckmrvEll K).mul
    (hasUniformExp3_leechMinusNEll_div hK).remainder).add
    ((hasUniformExp3_leechMinusNZero_div hK).remainder.trans
      (isBigO_snd_of_isBigO' (isBigO_le_norm_mul (fun z : ℍ => ‖cuspS z‖ ^ 3)) K))
  have h := (isBigO_cuspS_sq_inv_mul_uniform hsum).const_mul_left ckmrvMinusScale⁻¹
  refine h.congr_left fun p => ?_
  have hu : (ModularForm.discriminant p.2)⁻¹ =
      (cuspS p.2 ^ 2)⁻¹ * (discriminantCuspQuot p.2)⁻¹ := by
    rw [discriminant_eq_cuspS_sq_mul, mul_inv]
  have hs : (cuspS p.2 ^ 2)⁻¹ * cuspS p.2 ^ 2 = 1 :=
    inv_mul_cancel₀ (pow_ne_zero 2 (cuspS_ne_zero p.2))
  rw [ckmrvLeechMinusKernel_eq_z, ckmrvLeechMinusG, hu]
  linear_combination (-(ckmrvMinusScale⁻¹ *
    (ckmrvEll p.2 * (-(2 * 1728) * ModularForm.discriminant p.1 * (720 - kleinModularJ p.1)) +
      ((-leechMinusBeta p.1 - leechMinusAlpha p.1) * (696 - kleinModularJ p.1) -
        leechMinusNZeroC p.1)))) * hs

theorem isBigO_ckmrvLeechPlusKernel_sub_G_uniform {K : Set ℍ} (hK : IsCompact K) :
    (fun p : ℍ × ℍ => ckmrvLeechPlusKernel p.1 p.2 - ckmrvLeechPlusG p.1 p.2)
      =O[𝓟 K ×ˢ atImInfty] fun p => ‖(p.2 : ℂ)‖ ^ 2 * Real.exp (-π * p.2.im) := by
  have hsum := (((isBigO_snd_of_isBigO isBigO_coe_sq K).mul
      (hasUniformExp3_leechPlusM2 hK).remainder).add
    ((isBigO_snd_of_isBigO (isBigO_coe_norm.trans isBigO_norm_coe_sq) K).mul
      (hasUniformExp3_leechPlusM1 hK).remainder)).add
    ((hasUniformExp3_leechPlusM0 hK).remainder.trans
      (isBigO_snd_of_isBigO' (isBigO_le_norm_sq_mul (fun z : ℍ => ‖cuspS z‖ ^ 3)) K))
  have h := (isBigO_cuspS_sq_inv_mul_uniform hsum).const_mul_left (1728 * ckmrvPlusScale)⁻¹
  refine h.congr_left fun p => ?_
  have hs : (cuspS p.2 ^ 2)⁻¹ * cuspS p.2 ^ 2 = 1 :=
    inv_mul_cancel₀ (pow_ne_zero 2 (cuspS_ne_zero p.2))
  rw [ckmrvLeechPlusKernel_eq_M, ckmrvLeechPlusG]
  linear_combination (-((1728 * ckmrvPlusScale)⁻¹ *
    ((p.2 : ℂ) * leechPlusM1c p.1 + leechPlusM0c p.1))) * hs

end E8Leech
