-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Defs
import SpherePacking.Dim24.MagicFunction.F.Constants
import SpherePacking.Dim24.MagicFunction.F.RealValued
import SpherePacking.Dim24.MagicFunction.F.Scaled
public import SpherePacking.Dim24.Uniqueness.Defs
import SpherePacking.Dim24.Uniqueness.Scale
import SpherePacking.Dim24.Uniqueness.Rigidity.Lemmas
public import SpherePacking.CohnElkies.EqualityCaseVanishing
import SpherePacking.Basic.PeriodicPacking.Auxiliary
import SpherePacking.Basic.PeriodicPacking.Theorem22
import SpherePacking.Basic.PeriodicPacking.DensityFormula
import SpherePacking.Basic.PeriodicPacking.PeriodicConstant
import SpherePacking.Basic.PeriodicPacking.BoundaryControl

/-!
# Equality case input for dimension 24

This file packages the equality case of the Cohn-Elkies linear programming bound in dimension 24.

It produces the vanishing condition `(scaledF (x - y)).re = 0` in the `separation = 1`
normalization, and transports it back to the normalization used in the main uniqueness statement
(`separation = 2`).
-/


namespace SpherePacking.Dim24

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ²⁴ ℂ)

open scoped FourierTransform SchwartzMap
open scoped Pointwise
open scoped ENNReal

open EuclideanSpace MeasureTheory Metric Bornology
open ZSpan Module

/-- Equality case at cutoff radius `1` for the scaled auxiliary function `scaledF`.

In the tight case, **both** slack terms vanish:

1. pairwise slack: `(scaledF (x - y)).re = 0` for distinct centers,
2. Fourier slack: for every nonzero dual-lattice frequency `m`, the nonnegative quantity
   `((𝓕 scaledF) m).re * ‖expSum(m)‖^2` vanishes.
-/
public theorem optimality_sep_one_forces_scaledF_slack_vanishing (S : PeriodicSpherePacking 24)
    (hSep : S.separation = 1) (hS : S.density = LeechPacking.density) :
    (∀ x y : S.centers, x ≠ y → (scaledF ((x : ℝ²⁴) - (y : ℝ²⁴))).re = 0) ∧
      ∃ D : Set ℝ²⁴, Bornology.IsBounded D ∧
        (∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) ∧
          ∀ m : SchwartzMap.dualLattice (d := 24) S.lattice, m ≠ 0 →
            ((𝓕 (scaledF : 𝓢(ℝ²⁴, ℂ))) (m : ℝ²⁴)).re *
              (norm (SpherePacking.CohnElkies.expSum S D m) ^ 2) = 0 := by
  have hd : (0 : ℕ) < 24 := by decide
  have hNE : Nonempty S.centers := nonempty_centers_of_density_eq_leech (S := S) hS
  letI : Nonempty S.centers := hNE
  -- Choose the standard fundamental domain `D` for the lattice.
  let b : Basis (Fin 24) ℤ ↥S.lattice :=
    ((ZLattice.module_free ℝ S.lattice).chooseBasis).reindex (S.basis_index_equiv)
  let D : Set ℝ²⁴ := ZSpan.fundamentalDomain (Basis.ofZLatticeBasis ℝ S.lattice b)
  have hD_isBounded : Bornology.IsBounded D := by
    simpa [D] using! (ZSpan.fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ S.lattice b))
  have hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D := by
    simpa [D] using! (S.fundamental_domain_unique_covers b)
  -- Re-express the Leech density in the `sep=1` normalization: `2^24 * vol(B(0,1/2))`.
  have hDensity_target :
      S.density = ((2 : ENNReal) ^ (24 : ℕ)) * volume (ball (0 : ℝ²⁴) (1 / 2 : ℝ)) := by
    calc
      S.density = LeechPacking.density := hS
      _ = ENNReal.ofReal Real.pi ^ 12 / (Nat.factorial 12) := by
        simpa [Real.pi] using! LeechPacking_density
      _ = ((2 : ENNReal) ^ (24 : ℕ)) * volume (ball (0 : ℝ²⁴) (1 / 2 : ℝ)) := by
        simpa using! (twoPow24_mul_volume_ball_half).symm
  -- Extract `(S.numReps'/covolume) = 2^24` from the density formula.
  set cov : ℝ := ZLattice.covolume S.lattice (volume : Measure ℝ²⁴)
  have hcov_pos : 0 < cov := ZLattice.covolume_pos S.lattice (volume : Measure ℝ²⁴)
  have hvol_ne_zero : volume (ball (0 : ℝ²⁴) (1 / 2 : ℝ)) ≠ 0 :=
    ne_of_gt (EuclideanSpace.volume_ball_pos (0 : ℝ²⁴) (by positivity))
  have hvol_ne_top : volume (ball (0 : ℝ²⁴) (1 / 2 : ℝ)) ≠ ∞ :=
    ne_of_lt (EuclideanSpace.volume_ball_lt_top (0 : ℝ²⁴))
  have hvol_toReal_ne_zero :
      (volume (ball (0 : ℝ²⁴) (1 / 2 : ℝ))).toReal ≠ 0 :=
    (ENNReal.toReal_ne_zero).2 ⟨hvol_ne_zero, hvol_ne_top⟩
  have hDensity_formula :
      S.density =
        (S.numReps : ENNReal) * volume (ball (0 : ℝ²⁴) (1 / 2 : ℝ)) /
          (Real.toNNReal cov) := by
    -- `density_eq'` uses `ENat.toENNReal`; rewrite and simplify `separation / 2`.
    simp [cov, hSep, ENat.toENNReal_coe, S.density_eq' hd]
  have hNumReps_ratio_real :
      (S.numReps' hd hD_isBounded : ℝ) / cov = (2 : ℝ) ^ (24 : ℕ) := by
    -- Start from the equality of densities in `ENNReal` and take `toReal`.
    have hEqENN :
        (S.numReps : ENNReal) * volume (ball (0 : ℝ²⁴) (1 / 2 : ℝ)) / (Real.toNNReal cov)
          =
          ((2 : ENNReal) ^ (24 : ℕ)) * volume (ball (0 : ℝ²⁴) (1 / 2 : ℝ)) := by
      -- Replace `S.density` by the density formula and the target evaluation.
      simpa [hDensity_formula] using! hDensity_target
    have hEqReal := congrArg ENNReal.toReal hEqENN
    -- Simplify `toReal` of the algebraic expression.
    have hEqReal' :
        ((S.numReps : ℝ) * (volume (ball (0 : ℝ²⁴) (1 / 2 : ℝ))).toReal) / cov =
          ((2 : ℝ) ^ (24 : ℕ)) * (volume (ball (0 : ℝ²⁴) (1 / 2 : ℝ))).toReal := by
      -- Convert `Real.toNNReal cov` back to `cov` using positivity.
      have hcov_toNNReal : (Real.toNNReal cov : ℝ) = cov := by
        have hcov_nonneg : 0 ≤ cov := le_of_lt hcov_pos
        simp [Real.toNNReal_of_nonneg hcov_nonneg]
      -- Now unfold `toReal` on products/divisions.
      -- `ENNReal.ofNat` is nat-cast, and `toReal` respects `*` and `/`.
      simpa [hcov_toNNReal] using! hEqReal
    -- Rewrite as `((S.numReps : ℝ) / cov) * V = (2^24 : ℝ) * V` and cancel `V`.
    have hEqReal'' :
        ((S.numReps : ℝ) / cov) * (volume (ball (0 : ℝ²⁴) (1 / 2 : ℝ))).toReal =
          ((2 : ℝ) ^ (24 : ℕ)) * (volume (ball (0 : ℝ²⁴) (1 / 2 : ℝ))).toReal := by
      -- `a * V / cov = (a / cov) * V`.
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using! hEqReal'
    have hRatio_numReps : (S.numReps : ℝ) / cov = (2 : ℝ) ^ (24 : ℕ) :=
      (mul_right_cancel₀ hvol_toReal_ne_zero hEqReal'')
    -- Replace `numReps` by `numReps'` for our `D`.
    have hNum : S.numReps = S.numReps' hd hD_isBounded := by
      exact (S.numReps_eq_numReps' hd hD_isBounded hD_unique_covers)
    -- Cast to `ℝ` and rewrite.
    simpa [hNum] using! hRatio_numReps
  -- Real-valuedness of `𝓕 scaledF` (needed for the equality-case theorem).
  have scaledF_real_fourier :
      ∀ x : ℝ²⁴, (↑((𝓕 scaledF x).re : ℂ)) = (𝓕 scaledF x) := by
    intro x
    have two_ne_zero : (2 : ℝ) ≠ 0 := by norm_num
    let A : ℝ²⁴ ≃ₗ[ℝ] ℝ²⁴ :=
      LinearEquiv.smulOfNeZero (K := ℝ) (M := ℝ²⁴) (2 : ℝ) two_ne_zero
    let y0 : ℝ²⁴ :=
      (((A.symm : ℝ²⁴ ≃ₗ[ℝ] ℝ²⁴).toLinearMap).adjoint x)
    have hcoeScaled : (𝓕 scaledF x) = 𝓕 (fun y : ℝ²⁴ => scaledF y) x := by
      simpa using!
        congrArg (fun g : ℝ²⁴ → ℂ => g x) (SchwartzMap.fourier_coe (f := scaledF))
    have hcoeF : (𝓕 (fun y : ℝ²⁴ => f y) y0) = (𝓕 f y0) := by
      simpa using! congrArg (fun g : ℝ²⁴ → ℂ => g y0) (SchwartzMap.fourier_coe (f := f))
    have hscaled : (fun y : ℝ²⁴ => scaledF y) = fun y : ℝ²⁴ => f (A y) := by
      funext y
      simp [scaledF, A]
    have hfun :
        𝓕 (fun y : ℝ²⁴ => scaledF y) x =
          (abs (LinearMap.det (A : ℝ²⁴ →ₗ[ℝ] ℝ²⁴)))⁻¹ •
            𝓕 (fun y : ℝ²⁴ => f y) y0 := by
      simpa [hscaled, y0] using!
        (SpherePacking.ForMathlib.Fourier.fourier_comp_linearEquiv (A := A) (f := (⇑f)) (w := x))
    have hScaled :
        (𝓕 scaledF x) =
          (abs (LinearMap.det (A : ℝ²⁴ →ₗ[ℝ] ℝ²⁴)))⁻¹ • (𝓕 f y0) := by
      assumption
    have hImF : (𝓕 f y0).im = 0 := by
      have him : (FT f y0).im = 0 := by
        simpa using! (congrArg Complex.im (f_real_fourier (x := y0))).symm
      assumption
    have hImScaled : (𝓕 scaledF x).im = 0 := by
      have him := congrArg Complex.im hScaled
      simpa [Complex.smul_im, hImF] using! him
    apply Complex.ext <;> simp [hImScaled]
  -- Convert the scalar ratio `scaledF(0)/\widehat{scaledF}(0) = 2^24` into a real ratio.
  have hRatio_scaledF :
      (scaledF (0 : ℝ²⁴)).re / (𝓕 (scaledF : 𝓢(ℝ²⁴, ℂ)) (0 : ℝ²⁴)).re = (2 : ℝ) ^ (24 : ℕ) := by
    have hratioENN := scaledF_ratio_toNNReal
    have hratioReal := congrArg ENNReal.toReal hratioENN
    have hratioReal' :
        ((scaledF (0 : ℝ²⁴)).re.toNNReal : ℝ) /
            ((𝓕 (⇑scaledF) (0 : ℝ²⁴)).re.toNNReal : ℝ) =
          (2 : ℝ) ^ (24 : ℕ) := by
      simpa [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast] using! hratioReal
    have hnum : ((scaledF (0 : ℝ²⁴)).re.toNNReal : ℝ) = (scaledF (0 : ℝ²⁴)).re := by
      have hnonneg : 0 ≤ (scaledF (0 : ℝ²⁴)).re := by
        simp [scaledF, f_zero]
      simp [Real.toNNReal_of_nonneg hnonneg]
    have hFourier0 :
        (𝓕 (scaledF : 𝓢(ℝ²⁴, ℂ)) (0 : ℝ²⁴)) = (𝓕 (⇑scaledF) (0 : ℝ²⁴)) := by
      simpa using!
        congrArg (fun g : ℝ²⁴ → ℂ => g (0 : ℝ²⁴)) (SchwartzMap.fourier_coe (f := scaledF))
    have hFnonneg : 0 ≤ (𝓕 (scaledF : 𝓢(ℝ²⁴, ℂ)) (0 : ℝ²⁴)).re := by
      simpa using! scaledF_cohnElkies₂ (y := (0 : ℝ²⁴))
    have hden :
        ((𝓕 (⇑scaledF) (0 : ℝ²⁴)).re.toNNReal : ℝ) =
          (𝓕 (scaledF : 𝓢(ℝ²⁴, ℂ)) (0 : ℝ²⁴)).re := by
      have hEqRe :
          (𝓕 (⇑scaledF) (0 : ℝ²⁴)).re =
            (𝓕 (scaledF : 𝓢(ℝ²⁴, ℂ)) (0 : ℝ²⁴)).re := by
        simpa using! congrArg Complex.re hFourier0.symm
      have hnonneg : 0 ≤ (𝓕 (⇑scaledF) (0 : ℝ²⁴)).re := by
        simpa [hEqRe] using! hFnonneg
      have htoNN : ((𝓕 (⇑scaledF) (0 : ℝ²⁴)).re.toNNReal : ℝ) = (𝓕 (⇑scaledF) (0 : ℝ²⁴)).re := by
        simp [Real.toNNReal_of_nonneg hnonneg]
      simpa [htoNN, hEqRe]
    have h' :
        (scaledF (0 : ℝ²⁴)).re / (𝓕 (scaledF : 𝓢(ℝ²⁴, ℂ)) (0 : ℝ²⁴)).re = (2 : ℝ) ^ (24 : ℕ) := by
      simpa [hnum, hden] using! hratioReal'
    simpa using! h'
  -- Tightness equation in the real form needed by `CohnElkies.tight_forces_of_sub_re_eq_zero`.
  have hTight :
      (S.numReps' hd hD_isBounded : ℝ) * (scaledF 0).re =
        (S.numReps' hd hD_isBounded : ℝ) ^ 2 * (𝓕 (scaledF : 𝓢(ℝ²⁴, ℂ)) 0).re / cov := by
    have hb : (𝓕 (scaledF : 𝓢(ℝ²⁴, ℂ)) 0).re ≠ 0 := by
      intro hb0
      rw [hb0, div_zero] at hRatio_scaledF
      norm_num at hRatio_scaledF
    have ha := (div_eq_iff hb).1 hRatio_scaledF
    have hN := (div_eq_iff hcov_pos.ne').1 hNumReps_ratio_real
    rw [ha, hN, eq_div_iff hcov_pos.ne']
    ring
  have hCohnElkies₂' : ∀ z : ℝ²⁴, (𝓕 (scaledF : 𝓢(ℝ²⁴, ℂ)) z).re ≥ 0 := by
    intro z
    simpa using! (scaledF_cohnElkies₂ (y := z))
  refine ⟨?_, ?_⟩
  · -- Pairwise slack vanishing.
    intro x y hxy
    have := SpherePacking.CohnElkies.tight_forces_of_sub_re_eq_zero
        (P := S) (D := D) (f := (scaledF : 𝓢(ℝ²⁴, ℂ)))
        (hRealFourier := scaledF_real_fourier)
        (hCohnElkies₁ := scaledF_cohnElkies₁)
        (hCohnElkies₂ := hCohnElkies₂')
        (hP := hSep)
        (hD_unique_covers := hD_unique_covers)
        (hD_isBounded := hD_isBounded)
        (hd := hd)
        (hTight := by
          -- Match the covolume definition used in `CohnElkies`.
          simpa [cov] using! hTight)
    simpa using! this x y hxy
  · -- Fourier slack vanishing (for the same choice of `D`).
    refine ⟨D, hD_isBounded, hD_unique_covers, ?_⟩
    intro m hm
    have := SpherePacking.CohnElkies.tight_forces_fourier_re_mul_norm_expSum_sq_eq_zero_of_ne_zero
        (P := S) (D := D) (f := (scaledF : 𝓢(ℝ²⁴, ℂ)))
        (hRealFourier := scaledF_real_fourier)
        (hCohnElkies₁ := scaledF_cohnElkies₁)
        (hCohnElkies₂ := hCohnElkies₂')
        (hP := hSep)
        (hD_unique_covers := hD_unique_covers)
        (hD_isBounded := hD_isBounded)
        (hd := hd)
        (hTight := by
          simpa [cov] using! hTight)
    exact this m hm

/-- Backward-compatible wrapper: pairwise slack vanishing at cutoff radius `1`. -/
theorem optimality_sep_one_forces_scaledF_of_sub_re_eq_zero (S : PeriodicSpherePacking 24)
    (hSep : S.separation = 1) (hS : S.density = LeechPacking.density) :
    ∀ x y : S.centers, x ≠ y → (scaledF ((x : ℝ²⁴) - (y : ℝ²⁴))).re = 0 := by
  intro x y hxy
  exact (optimality_sep_one_forces_scaledF_slack_vanishing (S := S) hSep hS).1 x y hxy

/-- Equality case transported back to separation `2`: attaining the Leech density forces
`(f(x-y)).re = 0` for distinct centers. -/
public theorem optimality_normalized_forces_f_of_sub_re_eq_zero (S : PeriodicSpherePacking 24)
    (hSep : S.separation = 2) (hS : S.density = LeechPacking.density) :
    ∀ x y : S.centers, x ≠ y → (f ((x : ℝ²⁴) - (y : ℝ²⁴))).re = 0 := by
  intro x y hxy
  -- Scale `S` down by `1/2` so that the separation becomes `1`.
  set c : ℝ := (1 / 2 : ℝ)
  have hc : 0 < c := by
    dsimp [c]
    norm_num
  let S₁ : PeriodicSpherePacking 24 := PeriodicSpherePacking.scale (S := S) hc
  have hSep₁ : S₁.separation = 1 := by
    have : (PeriodicSpherePacking.scale (S := S) hc).separation = c * S.separation := by
      simp [PeriodicSpherePacking.scale, SpherePacking.scale]
    simpa [S₁, c, hSep, this, mul_assoc] using! this
  have hd : (0 : ℕ) < 24 := by decide
  have hDens₁ : S₁.density = LeechPacking.density := by
    have : S₁.density = S.density := by
      simpa [S₁] using! (PeriodicSpherePacking.scale_density (d := 24) (S := S) (hc := hc))
    simpa [this] using! hS
  -- Map `x,y` to the corresponding scaled centers in `S₁`.
  let x₁ : S₁.centers := ⟨c • (x : ℝ²⁴), by
    change c • (x : ℝ²⁴) ∈ c • S.centers
    exact ⟨(x : ℝ²⁴), x.property, rfl⟩⟩
  let y₁ : S₁.centers := ⟨c • (y : ℝ²⁴), by
    change c • (y : ℝ²⁴) ∈ c • S.centers
    exact ⟨(y : ℝ²⁴), y.property, rfl⟩⟩
  have hxy₁ : x₁ ≠ y₁ := by
    intro h
    apply hxy
    have hc0 : c ≠ 0 := ne_of_gt hc
    have hval : c • (x : ℝ²⁴) = c • (y : ℝ²⁴) := congrArg Subtype.val h
    have : (x : ℝ²⁴) = (y : ℝ²⁴) := by
      have h' := congrArg (fun z : ℝ²⁴ => c⁻¹ • z) hval
      simpa [smul_smul, inv_mul_cancel₀ hc0] using! h'
    exact Subtype.ext this
  -- Apply the separation-`1` equality-case statement for `scaledF`.
  have hScaled :
      (scaledF (((x₁ : S₁.centers) : ℝ²⁴) - ((y₁ : S₁.centers) : ℝ²⁴))).re = 0 :=
    optimality_sep_one_forces_scaledF_of_sub_re_eq_zero (S := S₁) hSep₁ hDens₁ x₁ y₁ hxy₁
  -- Unfold the scaling: `x₁ - y₁ = c • (x - y)`.
  have hsub : ((x₁ : ℝ²⁴) - (y₁ : ℝ²⁴)) = c • ((x : ℝ²⁴) - (y : ℝ²⁴)) := by
    simp [x₁, y₁, smul_sub]
  -- Unfold `scaledF(x) = f(2 • x)` (implemented as composition by a linear equiv).
  have hScaledF_apply : ∀ z : ℝ²⁴, scaledF z = f ((2 : ℝ) • z) := by
    intro z
    simp [scaledF, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  have hScaled' : (f ((2 : ℝ) • (c • ((x : ℝ²⁴) - (y : ℝ²⁴))))).re = 0 := by
    simpa [hsub, hScaledF_apply] using! hScaled
  have hc2 : (2 : ℝ) * c = 1 := by
    dsimp [c]
    norm_num
  have :
      (f ((x : ℝ²⁴) - (y : ℝ²⁴))).re = 0 := by
    have hScaled'' :
        (f (((2 : ℝ) * c) • ((x : ℝ²⁴) - (y : ℝ²⁴)))).re = 0 := by
      simpa [smul_smul] using! hScaled'
    simpa [hc2] using! hScaled''
  simpa using! this

end SpherePacking.Dim24
