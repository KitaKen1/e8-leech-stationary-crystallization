-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.ForMathlib.QExpansionCompat
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.RootlessCase.ThetaEquality
import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.RootlessCase.ExtremalCoeffTwo

/-!
# Theta series as an extremal weight-12 modular form

For an even unimodular rootless rank-24 lattice `L`, the theta series is a weight-12 modular form
with constant term `1` and vanishing `q` coefficient. In level `1`, this forces it to equal the
extremal modular form `E₄^3 - 720 • Δ`, and in particular its `q^2` coefficient is `196560`.

This file records the modular-form argument producing the `q^2` coefficient.

## Main statements
* `NiemeierRootless.qExpansion_coeff_two_thetaSeries_of_even_unimodular_rootless`
-/


namespace SpherePacking.Dim24.Uniqueness.RigidityClassify
noncomputable section

open scoped RealInnerProductSpace
open scoped CongruenceSubgroup MatrixGroups ModularForm
open SlashInvariantFormClass
open ModularFormClass
open Complex UpperHalfPlane

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace NiemeierRootless

abbrev E4cubed : ModularForm Γ(1) 12 :=
  E₄.mul (E₄.mul E₄)

abbrev DeltaMF : ModularForm Γ(1) 12 :=
  ModForm_mk Γ(1) 12 Delta

abbrev extremalWeight12 : ModularForm Γ(1) 12 :=
  E4cubed - (720 : ℂ) • DeltaMF

lemma E4_sq_q_exp_zero : (qExpansion 1 (E₄.mul E₄)).coeff 0 = 1 := by
  rw [← Nat.cast_one (R := ℝ), qExpansion_mul_coeff]
  -- constant coefficient of a product
  rw [PowerSeries.coeff_mul]
  simp [Finset.Nat.antidiagonal_zero, E4_q_exp_zero]

lemma E4_cubed_q_exp_zero :
    (qExpansion 1 (E₄.mul (E₄.mul E₄))).coeff 0 = 1 := by
  rw [← Nat.cast_one (R := ℝ), qExpansion_mul_coeff]
  rw [PowerSeries.coeff_mul]
  simp [Finset.Nat.antidiagonal_zero, E4_q_exp_zero]
  -- the remaining constant-term is the one already computed for `E₄^2`
  simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using!
    (E4_sq_q_exp_zero : (qExpansion 1 (E₄.mul E₄)).coeff 0 = 1)

lemma E4_cubed_q_exp_one :
    (qExpansion 1 (E₄.mul (E₄.mul E₄))).coeff 1 = 720 := by
  -- `(E₄) * (E₄ * E₄)` and use the already-known `q`-coefficients of `E₄`.
  rw [← Nat.cast_one (R := ℝ), qExpansion_mul_coeff]
  rw [PowerSeries.coeff_mul, antidiagonal_one]
  have h0 := E4_q_exp_zero
  have h1 := E4_q_exp_one
  have h0' : (qExpansion 1 (E₄.mul E₄)).coeff 0 = (1 : ℂ) := by
    simpa using! (E4_sq_q_exp_zero : (qExpansion 1 (E₄.mul E₄)).coeff 0 = 1)
  have h1' : (qExpansion 1 (E₄.mul E₄)).coeff 1 = 480 := by
    simpa using! (E4_sq_q_exp_one : (qExpansion 1 (E₄.mul E₄)).coeff 1 = 480)
  simp [h0, h1, h0', h1']
  ring

lemma extremal_weight12_q_exp_one :
    (qExpansion 1 extremalWeight12).coeff 1 = 0 := by
  let F : ModularForm Γ(1) 12 := E4cubed
  let G : ModularForm Γ(1) 12 := DeltaMF
  have hGq : qExpansion 1 G = qExpansion 1 Delta := by
    apply qExpansion_ext2 G Delta
    rfl
  have hG1 : (qExpansion 1 G).coeff 1 = 1 := by
    simpa [hGq] using! (Delta_q_one_term : (qExpansion 1 Delta).coeff 1 = 1)
  have hF1 : (qExpansion 1 F).coeff 1 = 720 := by
    simpa [F] using! (E4_cubed_q_exp_one : (qExpansion 1 (E₄.mul (E₄.mul E₄))).coeff 1 = 720)
  have hsub :
      qExpansion 1 (F - (720 : ℂ) • G) =
        qExpansion 1 F - qExpansion 1 ((720 : ℂ) • G) := by
    simpa using! (qExpansion_sub1 (f := F) (g := (720 : ℂ) • G))
  have hsmul : qExpansion 1 ((720 : ℂ) • G) = (720 : ℂ) • qExpansion 1 G := by
    simpa using! (qExpansion_smul2 (n := 1) (k := (12 : ℤ)) (a := (720 : ℂ)) (f := G)).symm
  have : (qExpansion 1 (F - (720 : ℂ) • G)).coeff 1 = 0 := by
    -- Take coefficient `1` after expanding subtraction and scalar multiplication.
    simp [hsub, hsmul, hF1, hG1]
  simpa [extremalWeight12, F, G] using! this

/-- For an even unimodular rootless lattice `L`, the `q^2` coefficient of its theta series is
`196560`. -/
public theorem qExpansion_coeff_two_thetaSeries_of_even_unimodular_rootless
    (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L] [IsZLattice ℝ L]
    (hEven : EvenNormSq L) (hUnimod : Unimodular L) (hRootless : Rootless L) :
    ∃ f : ModularForm Γ(1) (12 : ℤ),
      (∀ z : UpperHalfPlane, f z = thetaSeriesUHP L z) ∧ (qExpansion 1 f).coeff 2 = 196560 := by
  -- Obtain the modular form attached to the theta series.
  obtain ⟨f, hf⟩ := thetaSeries_is_modularForm_weight12 (L := L) hEven hUnimod
  refine ⟨f, hf, ?_⟩
  -- Identify the weight-12 extremal modular form.
  let ext : ModularForm Γ(1) 12 := extremalWeight12
  -- Show `f - ext` is a cusp form by vanishing constant term.
  let g : ModularForm Γ(1) 12 := f - ext
  have hg0 : (qExpansion 1 g).coeff 0 = 0 := by
    have hq := qExpansion_sub1 (f := f) (g := ext)
    have hq0 := congrArg (fun F : PowerSeries ℂ => F.coeff 0) hq
    have h0f : (qExpansion 1 f).coeff 0 = 1 := by
      simpa using! qExpansion_coeff_zero_thetaSeries (L := L) hEven f hf
    have h0ext : (qExpansion 1 ext).coeff 0 = 1 := by
      -- `ext = E₄^3 - 720Δ` has constant term `1`.
      have hF0 : (qExpansion 1 E4cubed).coeff 0 = 1 := by
        simpa [E4cubed] using!
          (E4_cubed_q_exp_zero : (qExpansion 1 (E₄.mul (E₄.mul E₄))).coeff 0 = 1)
      have hG0 : (qExpansion 1 DeltaMF).coeff 0 = 0 := by
        -- `G` is the modular form built from the cusp form `Delta`, so its constant term is `0`.
        have hh : (0 : ℝ) < (1 : ℝ) := zero_lt_one_real
        have hΓ : (1 : ℝ) ∈ (Γ(1) : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
          one_mem_strictPeriods_Gamma1
        have h0 : cuspFunction (1 : ℝ) Delta 0 = (0 : ℂ) :=
          CuspFormClass.cuspFunction_apply_zero (f := Delta) (h := (1 : ℝ)) hh hΓ
        have hval : UpperHalfPlane.valueAtInfty (Delta : ℍ → ℂ) = (0 : ℂ) :=
          (ModularFormClass.cuspFunction_apply_zero (f := Delta) (h := (1 : ℝ)) hh hΓ).symm.trans h0
        have : (qExpansion (1 : ℝ) Delta).coeff 0 = (0 : ℂ) := by
          simp [ModularFormClass.qExpansion_coeff_zero (f := Delta) (h := (1 : ℝ)) hh hΓ, hval]
        simpa [DeltaMF] using! this
      have hsub : qExpansion 1 ext = qExpansion 1 E4cubed - qExpansion 1 ((720 : ℂ) • DeltaMF) := by
        simpa [ext, extremalWeight12, E4cubed, DeltaMF] using!
          (qExpansion_sub1 (f := E4cubed) (g := (720 : ℂ) • DeltaMF))
      have hsmul0 :
          (qExpansion 1 ((720 : ℂ) • DeltaMF)).coeff 0 =
            (720 : ℂ) * (qExpansion 1 DeltaMF).coeff 0 := by
        have hqs : qExpansion 1 ((720 : ℂ) • DeltaMF) = (720 : ℂ) • qExpansion 1 DeltaMF := by
          simpa using!
            (qExpansion_smul2 (n := 1) (k := (12 : ℤ)) (a := (720 : ℂ)) (f := DeltaMF)).symm
        have := congrArg (fun P : PowerSeries ℂ => P.coeff 0) hqs
        simpa [smul_eq_mul] using! this
      -- Take coefficient 0 of `ext`.
      have : (qExpansion 1 ext).coeff 0 =
          (qExpansion 1 E4cubed).coeff 0 - (qExpansion 1 ((720 : ℂ) • DeltaMF)).coeff 0 := by
        simp [hsub]
      -- arithmetic
      simp [this, hF0, hG0, hsmul0]
    have : (qExpansion 1 f).coeff 0 - (qExpansion 1 ext).coeff 0 = 0 := by
      simp [h0f, h0ext]
    have hq0' :
        (qExpansion 1 g).coeff 0 = (qExpansion 1 f).coeff 0 - (qExpansion 1 ext).coeff 0 := by
      simpa [g] using! hq0
    simpa [h0f, h0ext] using! hq0'
  have hg1 : (qExpansion 1 g).coeff 1 = 0 := by
    -- `q^1` coefficient of `f` is `0` by rootlessness, and `ext` has `q^1` coefficient `0`.
    have hq := qExpansion_sub1 (f := f) (g := ext)
    have hq1 := congrArg (fun F : PowerSeries ℂ => F.coeff 1) (by simpa [g] using! hq)
    have h1f : (qExpansion 1 f).coeff 1 = 0 := by
      simpa using! qExpansion_coeff_one_thetaSeries_of_rootless (L := L) hEven hRootless f hf
    have h1ext : (qExpansion 1 ext).coeff 1 = 0 := by
      simpa [ext] using! (extremal_weight12_q_exp_one : (qExpansion 1 extremalWeight12).coeff 1 = 0)
    simpa [g, h1f, h1ext] using! hq1
  have hgzero : g = 0 :=
    modularForm_eq_zero_of_qExpansion_coeff_zero_eq_zero_of_qExpansion_coeff_one_eq_zero
      (g := g) hg0 hg1
  have hfext : f = ext := by
    -- `g = f - ext = 0`.
    have : f - ext = 0 := by simpa [g] using! hgzero
    exact sub_eq_zero.mp this
  -- Conclude the `q^2` coefficient from the extremal computation.
  have h2ext : (qExpansion 1 ext).coeff 2 = 196560 := by
    simpa [ext, extremalWeight12, E4cubed, DeltaMF] using!
      (extremal_weight12_q_exp_two :
        (qExpansion 1
            (let F : ModularForm Γ(1) 12 := E₄.mul (E₄.mul E₄)
             let G : ModularForm Γ(1) 12 := ModForm_mk Γ(1) 12 Delta
             F - (720 : ℂ) • G)).coeff 2 = 196560)
  simpa [hfext] using! h2ext

end NiemeierRootless

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
