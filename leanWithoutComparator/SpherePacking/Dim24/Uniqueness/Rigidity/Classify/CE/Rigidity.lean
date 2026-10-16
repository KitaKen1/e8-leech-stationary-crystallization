-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.CE.GlobalRigidity
import SpherePacking.Dim24.Uniqueness.DistanceSpectrum.Reduction
public import SpherePacking.Dim24.Uniqueness.Scale

/-!
# Entry point for the CE uniqueness route

This file provides the two main theorems for the CE Section 8 route:

1. a normalized rigidity theorem (`separation = 2`), and
2. a scale-invariant uniqueness statement matching `dim_24.tex` Theorem 1.1.

## Main statements
* `Uniqueness.RigidityClassify.CE.leech_rigidity_normalized`
* `Uniqueness.RigidityClassify.CE.leech_unique_optimal_periodic`
-/

namespace SpherePacking.Dim24.Uniqueness.RigidityClassify.CE

noncomputable section

open scoped Pointwise

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/--
Normalized rigidity (CE route): if `S.separation = 2` and `S.density` is the Leech density, then
`S` is isometric to `LeechPacking`.
-/
public theorem leech_rigidity_normalized
    (S : PeriodicSpherePacking 24)
    (hSep : S.separation = 2)
    (hDens : S.density = LeechPacking.density) :
    PeriodicSpherePacking.Isometric S LeechPacking :=
  isometric_leechPacking_of_CE (S := S) (hSep := hSep)
    (hSpec :=
      Dim24.optimal_periodic_has_leech_distance_spectrum_normalized (S := S) hSep hDens)
    (hDens := hDens)

/- Scaling: deduce the scale-invariant uniqueness statement from the normalized one. -/

theorem isometricToScaledLeech_of_scale_isometric_leech (S : PeriodicSpherePacking 24)
    {c : ℝ} (hc : 0 < c)
    (hIso : PeriodicSpherePacking.Isometric (S.scale hc) LeechPacking) :
    IsometricToScaledLeech S := by
  rcases hIso with ⟨hSep, ⟨e, he⟩⟩
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  refine ⟨?_, ?_⟩
  · -- separation
    have hcne : c ≠ 0 := ne_of_gt hc
    have hSep' : c * S.separation = 2 := by
      simpa [PeriodicSpherePacking.scale, SpherePacking.scale] using! hSep
    calc
      S.separation = c⁻¹ * (c * S.separation) := by simp [hcne]
      _ = c⁻¹ * 2 := by simp [hSep']
      _ = (LeechPacking.scale (inv_pos.mpr hc)).separation := by
        simp [PeriodicSpherePacking.scale, SpherePacking.scale, LeechPacking_separation]
  · -- centers: conjugate the witnessing isometry by scaling
    have hcne : c ≠ 0 := ne_of_gt hc
    let f : ℝ²⁴ → ℝ²⁴ := fun x => c⁻¹ • e (c • x)
    let g : ℝ²⁴ → ℝ²⁴ := fun x => c⁻¹ • e.symm (c • x)
    have hfg : ∀ x, f (g x) = x := by
      intro x
      simp [f, g, smul_smul, hcne]
    have hgf : ∀ x, g (f x) = x := by
      intro x
      simp [f, g, smul_smul, hcne]
    have hfiso : Isometry f := by
      refine Isometry.of_dist_eq ?_
      intro x y
      calc
        dist (f x) (f y)
            = ‖c⁻¹‖ * dist (e (c • x)) (e (c • y)) := by
                simp [f, dist_smul₀]
        _ = ‖c⁻¹‖ * dist (c • x) (c • y) := by
                simp [IsometryEquiv.dist_eq]
        _ = ‖c⁻¹‖ * (‖c‖ * dist x y) := by
                simp [dist_smul₀]
        _ = dist x y := by
                simp_all
    let e' : ℝ²⁴ ≃ᵢ ℝ²⁴ := IsometryEquiv.mk' f g hfg hfiso
    refine ⟨e', ?_⟩
    have hscaled_centers :
        (S.scale hc).centers = c • (S.centers : Set ℝ²⁴) := rfl
    have hscaled_leech_centers :
        (LeechPacking.scale (inv_pos.mpr hc)).centers =
          c⁻¹ • (LeechPacking.centers : Set ℝ²⁴) := rfl
    have he' : e '' (c • (S.centers : Set ℝ²⁴)) = (LeechPacking.centers : Set ℝ²⁴) := by
      simpa [hscaled_centers] using! he
    calc
      e' '' (S.centers : Set ℝ²⁴)
          = (fun x : ℝ²⁴ => c⁻¹ • e (c • x)) '' (S.centers : Set ℝ²⁴) := by rfl
      _ = (fun x : ℝ²⁴ => c⁻¹ • x) '' ((fun x : ℝ²⁴ => e (c • x)) '' (S.centers : Set ℝ²⁴)) := by
            simp [Set.image_image]
      _ =
          (fun x : ℝ²⁴ => c⁻¹ • x) '' (e '' ((fun x : ℝ²⁴ => c • x) '' (S.centers : Set ℝ²⁴))) := by
            have :
                (fun x : ℝ²⁴ => e (c • x)) '' (S.centers : Set ℝ²⁴) =
                  e '' ((fun x : ℝ²⁴ => c • x) '' (S.centers : Set ℝ²⁴)) := by
              simpa using! (Set.image_image e (fun x : ℝ²⁴ => c • x) (S.centers : Set ℝ²⁴)).symm
            simp [this]
      _ = c⁻¹ • (e '' (c • (S.centers : Set ℝ²⁴))) := by
            simp [Set.image_smul]
      _ = c⁻¹ • (LeechPacking.centers : Set ℝ²⁴) := by
            simpa using! congrArg (fun s => c⁻¹ • s) he'
      _ = (PeriodicSpherePacking.scale (S := LeechPacking) (d := 24) (inv_pos.mpr hc)).centers := by
            simp [hscaled_leech_centers]

/--
Scale-invariant uniqueness (CE route): if `S` attains the Leech density, then `S` is isometric to a
scaled copy of `LeechPacking`.
-/
public theorem leech_unique_optimal_periodic
    (S : PeriodicSpherePacking 24)
    (hDens : S.density = LeechPacking.density) :
    IsometricToScaledLeech S := by
  rcases PeriodicSpherePacking.exists_scale_separation_eq_two (S := S) with ⟨c, hc, hSep⟩
  have hDens' : (PeriodicSpherePacking.scale (S := S) hc).density = LeechPacking.density := by
    simpa [PeriodicSpherePacking.scale_density (d := 24) (S := S) (hc := hc)] using!
      hDens
  have hIsoScaled :
      PeriodicSpherePacking.Isometric (PeriodicSpherePacking.scale (S := S) hc) LeechPacking :=
    leech_rigidity_normalized (S := PeriodicSpherePacking.scale (S := S) hc) hSep hDens'
  exact isometricToScaledLeech_of_scale_isometric_leech (S := S) (hc := hc) hIsoScaled

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify.CE
