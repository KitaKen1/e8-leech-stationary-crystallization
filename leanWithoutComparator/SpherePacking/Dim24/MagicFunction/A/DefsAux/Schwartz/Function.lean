/-
Construction of the Schwartz function `aAux : 𝓢(ℝ²⁴, ℂ)` from the profile.
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.Prelude
public import SpherePacking.ForMathlib.DerivHelpers
public import SpherePacking.ForMathlib.IteratedDeriv
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.Schwartz.I1Decay
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.Schwartz.I2Smooth
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.Schwartz.I3Smooth
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.Schwartz.I4Smooth
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.Schwartz.I5Smooth
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.Schwartz.I6ContDiffDecay


/-!
# The eigenfunction `aAux`

This file defines `aAux : 𝓢(ℝ²⁴, ℂ)` from the one-variable profile `aProfile`.

We prove one-sided Schwartz decay and smoothness for `aProfile` and then apply the radial Schwartz
bridge.

## Main definitions
* `aAux`
-/

section

open scoped SchwartzMap

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

noncomputable section

/-- The auxiliary Schwartz function in dimension 24 built from the profile `aProfile`. -/
@[expose] public noncomputable def aAux : 𝓢(ℝ²⁴, ℂ) := by
  -- One-sided Schwartz decay for the full profile on `0 ≤ r`.
  have hf_decay :
      ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n aProfile x‖ ≤ C := by
    intro k n
    rcases (Schwartz.I1Smooth.decay_I₁' (k := k) (n := n)) with ⟨C1, hC1⟩
    rcases (Schwartz.I2Smooth.decay_I₂' (k := k) (n := n)) with ⟨C2, hC2⟩
    rcases (Schwartz.I3Smooth.decay_I₃' (k := k) (n := n)) with ⟨C3, hC3⟩
    rcases (Schwartz.I4Smooth.decay_I₄' (k := k) (n := n)) with ⟨C4, hC4⟩
    rcases (Schwartz.I5Smooth.decay_I₅' (k := k) (n := n)) with ⟨C5, hC5⟩
    rcases (Schwartz.I6Smooth.decay_I₆' (k := k) (n := n)) with ⟨C6, hC6⟩
    refine ⟨C1 + C2 + C3 + C4 + C5 + C6, ?_⟩
    intro x hx
    have hn : ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
      WithTop.coe_le_coe.2 (show (n : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)
    have hI1 : ContDiffAt ℝ n RealIntegrals.I₁' x :=
      (Schwartz.I1Smooth.contDiff_I₁'.contDiffAt (x := x)).of_le hn
    have hI2 : ContDiffAt ℝ n RealIntegrals.I₂' x :=
      (Schwartz.I2Smooth.contDiff_I₂'.contDiffAt (x := x)).of_le hn
    have hI3 : ContDiffAt ℝ n RealIntegrals.I₃' x :=
      (Schwartz.I3Smooth.contDiff_I₃'.contDiffAt (x := x)).of_le hn
    have hI4 : ContDiffAt ℝ n RealIntegrals.I₄' x :=
      (Schwartz.I4Smooth.contDiff_I₄'.contDiffAt (x := x)).of_le hn
    have hI5 : ContDiffAt ℝ n RealIntegrals.I₅' x :=
      (Schwartz.I5Smooth.contDiff_I₅'.contDiffAt (x := x)).of_le hn
    have hI6top : ContDiffAt ℝ (⊤ : ℕ∞) RealIntegrals.I₆' x := by
      have hxIoi : Set.Ioi (-1 : ℝ) ∈ nhds x :=
        isOpen_Ioi.mem_nhds (by
          have hneg1 : (-1 : ℝ) < 0 := by norm_num
          exact lt_of_lt_of_le hneg1 hx)
      exact (Schwartz.I6Smooth.contDiffOn_I₆'_Ioi_neg1.contDiffAt (x := x) hxIoi)
    have hI6 : ContDiffAt ℝ n RealIntegrals.I₆' x := hI6top.of_le hn
    have ha_def :
        aProfile =
          fun u : ℝ ↦
            (((((RealIntegrals.I₁' u + RealIntegrals.I₂' u) + RealIntegrals.I₃' u) +
                  RealIntegrals.I₄' u) +
                RealIntegrals.I₅' u) +
              RealIntegrals.I₆' u) := by
      funext u
      simp [aProfile, RealIntegrals.a', add_assoc]
    simpa [ha_def] using!
      (SpherePacking.ForMathlib.decay_iteratedFDeriv_add₆_of_decay (k := k) (n := n)
        (C₁ := C1) (C₂ := C2) (C₃ := C3) (C₄ := C4) (C₅ := C5) (C₆ := C6)
        (hdec₁ := hC1) (hdec₂ := hC2) (hdec₃ := hC3) (hdec₄ := hC4) (hdec₅ := hC5) (hdec₆ := hC6)
        (x := x) (hx := hx) (hf₁ := hI1) (hf₂ := hI2) (hf₃ := hI3) (hf₄ := hI4) (hf₅ := hI5)
        (hf₆ := hI6))
  -- Smoothness of the cutoff-modified profile.
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun r ↦ RadialSchwartz.cutoffC r * aProfile r) := by
    have ha_on : ContDiffOn ℝ (⊤ : ℕ∞) aProfile (Set.Ioi (-1 : ℝ)) := by
      have ha :
          (fun y : ℝ =>
              RealIntegrals.I₁' y +
                (RealIntegrals.I₂' y +
                  (RealIntegrals.I₃' y +
                    (RealIntegrals.I₄' y + (RealIntegrals.I₅' y + RealIntegrals.I₆' y))))) =
            aProfile := by
        funext y
        simp [aProfile, RealIntegrals.a', add_assoc]
      simpa [ha] using!
        (SpherePacking.ForMathlib.contDiffOn_add₆_right_of_contDiff
          (s := Set.Ioi (-1 : ℝ))
          (f₁ := RealIntegrals.I₁')
          (f₂ := RealIntegrals.I₂')
          (f₃ := RealIntegrals.I₃')
          (f₄ := RealIntegrals.I₄')
          (f₅ := RealIntegrals.I₅')
          (f₆ := RealIntegrals.I₆')
          Schwartz.I1Smooth.contDiff_I₁'
          Schwartz.I2Smooth.contDiff_I₂'
          Schwartz.I3Smooth.contDiff_I₃'
          Schwartz.I4Smooth.contDiff_I₄'
          Schwartz.I5Smooth.contDiff_I₅'
          Schwartz.I6Smooth.contDiffOn_I₆'_Ioi_neg1)
    simpa using!
      (RadialSchwartz.contDiff_cutoffC_mul_of_contDiffOn_Ioi_neg1 (f := aProfile) ha_on)
  exact
    RadialSchwartz.Bridge.schwartzMap_norm_sq_of_cutoffMul_contDiff_decay_nonneg
      (F := ℝ²⁴) aProfile hg hf_decay


end

end SpherePacking.Dim24

end
