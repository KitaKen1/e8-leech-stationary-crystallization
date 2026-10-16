-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.ForMathlib.DerivHelpers
public import SpherePacking.ForMathlib.IteratedDeriv
public import SpherePacking.Dim24.MagicFunction.B.Defs.J1SmoothIntegrals
public import SpherePacking.Dim24.MagicFunction.B.Defs.J1SmoothDecay
public import SpherePacking.Dim24.MagicFunction.B.Defs.J2Smooth
public import SpherePacking.Dim24.MagicFunction.B.Defs.J3Smooth
public import SpherePacking.Dim24.MagicFunction.B.Defs.J4Smooth
public import SpherePacking.Dim24.MagicFunction.B.Defs.J5SmoothIntegrals
public import SpherePacking.Dim24.MagicFunction.B.Defs.J6Smooth


/-!
# The `-1` eigenfunction `b : 𝓢(ℝ²⁴,ℂ)`

We define `b` by proving smoothness and one-sided Schwartz decay of `bProfile` on `0 ≤ r`, then
applying the radial Schwartz bridge to obtain a Schwartz function on `ℝ²⁴`.

## Main definitions
* `b`
-/

open scoped SchwartzMap

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

noncomputable section

/-- The `-1` eigenfunction `b` as a Schwartz function on `ℝ²⁴`, built from the profile `bProfile`.
-/
@[expose] public def b : 𝓢(ℝ²⁴, ℂ) := by
  -- One-sided Schwartz decay for the full profile on `0 ≤ r`.
  have hf_decay :
      ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n bProfile x‖ ≤ C := by
    intro k n
    rcases (Schwartz.J1Smooth.decay_J₁' (k := k) (n := n)) with ⟨C1, hC1⟩
    rcases (Schwartz.J2Smooth.decay_J₂' (k := k) (n := n)) with ⟨C2, hC2⟩
    rcases (Schwartz.J3Smooth.decay_J₃' (k := k) (n := n)) with ⟨C3, hC3⟩
    rcases (Schwartz.J4Smooth.decay_J₄' (k := k) (n := n)) with ⟨C4, hC4⟩
    rcases (Schwartz.J5Smooth.decay_J₅' (k := k) (n := n)) with ⟨C5, hC5⟩
    rcases (Schwartz.J6Smooth.decay_J₆' (k := k) (n := n)) with ⟨C6, hC6⟩
    refine ⟨C1 + C2 + C3 + C4 + C5 + C6, ?_⟩
    intro x hx
    have hn : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      simpa using! (WithTop.coe_le_coe.2 (show (n : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
    have hJ1 : ContDiffAt ℝ n RealIntegrals.J₁' x :=
      (Schwartz.J1Smooth.contDiff_J₁'.contDiffAt (x := x)).of_le hn
    have hJ2 : ContDiffAt ℝ n RealIntegrals.J₂' x :=
      (Schwartz.J2Smooth.contDiff_J₂'.contDiffAt (x := x)).of_le hn
    have hJ3 : ContDiffAt ℝ n RealIntegrals.J₃' x :=
      (Schwartz.J3Smooth.contDiff_J₃'.contDiffAt (x := x)).of_le hn
    have hJ4 : ContDiffAt ℝ n RealIntegrals.J₄' x :=
      (Schwartz.J4Smooth.contDiff_J₄'.contDiffAt (x := x)).of_le hn
    have hJ5 : ContDiffAt ℝ n RealIntegrals.J₅' x :=
      (Schwartz.J5Smooth.contDiff_J₅'.contDiffAt (x := x)).of_le hn
    have hJ6top : ContDiffAt ℝ (⊤ : ℕ∞) RealIntegrals.J₆' x := by
      have hxIoi : Set.Ioi (-1 : ℝ) ∈ nhds x :=
        isOpen_Ioi.mem_nhds <|
          lt_of_lt_of_le (by simp : (-1 : ℝ) < 0) hx
      exact (Schwartz.J6Smooth.contDiffOn_J₆'_Ioi_neg1.contDiffAt (x := x) hxIoi)
    have hJ6 : ContDiffAt ℝ n RealIntegrals.J₆' x := hJ6top.of_le hn
    have hbdef :
        bProfile =
          fun u : ℝ ↦
            (((((RealIntegrals.J₁' u + RealIntegrals.J₂' u) + RealIntegrals.J₃' u) +
                  RealIntegrals.J₄' u) +
                RealIntegrals.J₅' u) +
              RealIntegrals.J₆' u) := by
      funext u
      simp [bProfile, RealIntegrals.b', add_assoc]
    simpa [hbdef] using!
      (SpherePacking.ForMathlib.decay_iteratedFDeriv_add₆_of_decay (k := k) (n := n)
        (C₁ := C1) (C₂ := C2) (C₃ := C3) (C₄ := C4) (C₅ := C5) (C₆ := C6)
        (hdec₁ := hC1) (hdec₂ := hC2) (hdec₃ := hC3) (hdec₄ := hC4) (hdec₅ := hC5) (hdec₆ := hC6)
        (x := x) (hx := hx) (hf₁ := hJ1) (hf₂ := hJ2) (hf₃ := hJ3) (hf₄ := hJ4) (hf₅ := hJ5)
        (hf₆ := hJ6))
  -- Smoothness of the cutoff-modified profile.
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun r ↦ RadialSchwartz.cutoffC r * bProfile r) := by
    have hb_on : ContDiffOn ℝ (⊤ : ℕ∞) bProfile (Set.Ioi (-1 : ℝ)) := by
      have hb :
          (fun y : ℝ =>
              RealIntegrals.J₁' y +
                (RealIntegrals.J₂' y +
                  (RealIntegrals.J₃' y +
                    (RealIntegrals.J₄' y + (RealIntegrals.J₅' y + RealIntegrals.J₆' y))))) =
            bProfile := by
        funext y
        simp [bProfile, RealIntegrals.b', add_assoc]
      simpa [hb] using!
        (SpherePacking.ForMathlib.contDiffOn_add₆_right_of_contDiff
          (s := Set.Ioi (-1 : ℝ))
          (f₁ := RealIntegrals.J₁')
          (f₂ := RealIntegrals.J₂')
          (f₃ := RealIntegrals.J₃')
          (f₄ := RealIntegrals.J₄')
          (f₅ := RealIntegrals.J₅')
          (f₆ := RealIntegrals.J₆')
          Schwartz.J1Smooth.contDiff_J₁'
          Schwartz.J2Smooth.contDiff_J₂'
          Schwartz.J3Smooth.contDiff_J₃'
          Schwartz.J4Smooth.contDiff_J₄'
          Schwartz.J5Smooth.contDiff_J₅'
          Schwartz.J6Smooth.contDiffOn_J₆'_Ioi_neg1)
    simpa using!
      (RadialSchwartz.contDiff_cutoffC_mul_of_contDiffOn_Ioi_neg1 (f := bProfile) hb_on)
  exact
    RadialSchwartz.Bridge.schwartzMap_norm_sq_of_cutoffMul_contDiff_decay_nonneg
      (F := ℝ²⁴) bProfile hg hf_decay

end

end SpherePacking.Dim24
