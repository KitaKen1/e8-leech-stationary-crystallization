-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Eigen.Prelude
public import SpherePacking.Basic.Domains.WedgeSet
import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSlash
import SpherePacking.Contour.PermJ12Tendsto


/-!
# Regularity for the contour deformation of `perm_J₁_J₂`

We follow the Poincaré-lemma based contour deformation from the dim-8 argument. The key analytic
input is that `Ψ₁' r` is holomorphic on the upper half-plane and tends to `0` at the cusp `1`
within `closure wedgeSet`.

## Main statements
* `differentiableOn_Ψ₁'_upper`
* `tendsto_Ψ₁'_one_within_closure_wedgeSet`
-/

namespace SpherePacking.Dim24.BFourier
open Filter
open scoped Topology UpperHalfPlane

noncomputable section


section PermJ12

/-- Holomorphy of `Ψ₁' r` on the upper half-plane. -/
public lemma differentiableOn_Ψ₁'_upper (r : ℝ) :
    DifferentiableOn ℂ (Ψ₁' r) UpperHalfPlane.upperHalfPlaneSet := by
  simpa [Ψ₁'] using!
    (SpherePacking.Contour.differentiableOn_mul_cexp_pi_I_mul_real
      (s := UpperHalfPlane.upperHalfPlaneSet) (ψ := ψT')
      (hψ := SpherePacking.Dim24.differentiableOn_ψT'_upper) (r := r))

open UpperHalfPlane Complex ModularGroup MatrixGroups ModularForm SlashAction Matrix
open scoped Real ModularForm MatrixGroups

lemma ψS_slash_STS :
    (ψS ∣[-10] (ModularGroup.S * ModularGroup.T * ModularGroup.S)) = -ψT := by
  have hmul :
      (ψS ∣[-10] (ModularGroup.S * ModularGroup.T * ModularGroup.S)) =
        (ψS ∣[-10] (ModularGroup.S * ModularGroup.T)) ∣[-10] ModularGroup.S := by
    simpa [mul_assoc] using!
      (SlashAction.slash_mul (-10 : ℤ) (ModularGroup.S * ModularGroup.T) ModularGroup.S ψS)
  calc
    (ψS ∣[-10] (ModularGroup.S * ModularGroup.T * ModularGroup.S))
        = (ψS ∣[-10] (ModularGroup.S * ModularGroup.T)) ∣[-10] ModularGroup.S := hmul
    _ = (ψT ∣[-10] ModularGroup.S) := by
        simpa using! congrArg (fun f : ℍ → ℂ => f ∣[-10] ModularGroup.S) PsiSlash.ψS_slash_ST
    _ = -ψT := by
        simpa using! (SpherePacking.Dim24.ψT_S_action)

/-- `Ψ₁' r` tends to `0` at the cusp `1` within `closure wedgeSet`. -/
public lemma tendsto_Ψ₁'_one_within_closure_wedgeSet (r : ℝ) :
    Tendsto (Ψ₁' r) (𝓝[closure wedgeSet] (1 : ℂ)) (𝓝 0) := by
  -- This is a special case of the common ForMathlib lemma.
  let g : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ModularGroup.S * ModularGroup.T * ModularGroup.S
  -- Define the action explicitly with a fixed codomain.
  let gAct : ℍ → ℍ :=
    fun zH =>
      HSMul.hSMul (α := Matrix.SpecialLinearGroup (Fin 2) ℤ) (β := ℍ) (γ := ℍ) g zH
  have hg :
      g =
        ⟨!![-1, 0; 1, -1], by
          norm_num [Matrix.det_fin_two_of]⟩ := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hψT' :
      ∀ {z : ℂ} (hz : 0 < z.im),
        ψT' z =
          -ψS (gAct (⟨z, hz⟩ : ℍ)) * (z - 1) ^ (10 : ℕ) := by
    intro z hz
    let zH : ℍ := ⟨z, hz⟩
    have hrel0 := congrArg (fun F : ℍ → ℂ => F zH) ψS_slash_STS
    have hrel : (ψS ∣[(-10 : ℤ)] g) zH = -ψT zH := by
      simpa [g] using! hrel0
    have hdenom : UpperHalfPlane.denom g zH = (z : ℂ) - 1 := by
      have hcalc : UpperHalfPlane.denom g zH = (z : ℂ) + (-1 : ℂ) := by
        have h10 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
          rw [hg]; rfl
        have h11 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = -1 := by
          rw [hg]; rfl
        rw [ModularGroup.denom_apply, h10, h11]
        simp [zH]
      simpa [sub_eq_add_neg] using! hcalc
    have h1 :
        ψS (gAct zH) * UpperHalfPlane.denom g zH ^ (10 : ℤ) = -ψT zH := by
      simpa [ModularForm.SL_slash_apply, gAct] using! hrel
    have h2 : ψT zH = -ψS (gAct zH) * UpperHalfPlane.denom g zH ^ (10 : ℤ) := by
      simpa [neg_mul, mul_assoc] using! (congrArg Neg.neg h1).symm
    calc
      ψT' z = ψT zH := by simp [ψT', hz, zH]
      _ = -ψS (gAct zH) * UpperHalfPlane.denom g zH ^ (10 : ℤ) := h2
      _ = -ψS (gAct zH) * ((z : ℂ) - 1) ^ (10 : ℤ) := by
            simp [hdenom]
      _ = -ψS (gAct zH) * (z - 1) ^ (10 : ℕ) := by
            simpa using!
              congrArg (fun t : ℂ => -ψS (gAct zH) * t) (zpow_ofNat (z - 1) 10)
  have hgAct_im :
      ∀ {z : ℂ} (hz : 0 < z.im),
        (gAct (⟨z, hz⟩ : ℍ)).im = z.im / Complex.normSq (z - 1) := by
    intro z hz
    let zH : ℍ := ⟨z, hz⟩
    have hdenom : UpperHalfPlane.denom g zH = (z : ℂ) - 1 := by
      have hcalc : UpperHalfPlane.denom g zH = (z : ℂ) + (-1 : ℂ) := by
        have h10 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
          rw [hg]; rfl
        have h11 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = -1 := by
          rw [hg]; rfl
        rw [ModularGroup.denom_apply, h10, h11]
        simp [zH]
      simpa [sub_eq_add_neg] using! hcalc
    have him :
        (gAct zH).im = z.im / Complex.normSq (UpperHalfPlane.denom g zH) := by
      simpa [gAct] using! (ModularGroup.im_smul_eq_div_normSq (g := g) (z := zH))
    simpa [hdenom] using! him
  simpa using!
    (SpherePacking.Contour.tendsto_Ψ₁'_one_within_closure_wedgeSet_of
      (h := ({
        hk := by decide
        Ψ₁'_eq := by intro r z; simp [Ψ₁']
        ψT'_one := by simp [ψT']
        tendsto_ψS_atImInfty := tendsto_ψS_atImInfty
        gAct_im := hgAct_im
        ψT'_eq_neg_ψS_mul := hψT'
        mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one :=
          mem_upperHalfPlane_of_mem_closure_wedgeSet_ne_one
        closure_wedgeSet_subset_abs_re_sub_one_le_im := by
          intro z hz
          simpa using! (closure_wedgeSet_subset_abs_re_sub_one_le_im hz)
      } : SpherePacking.Contour.TendstoPsiOneHypotheses wedgeSet ψS ψT' Ψ₁' gAct 10))
      (r := r))


end PermJ12


end
end SpherePacking.Dim24.BFourier
