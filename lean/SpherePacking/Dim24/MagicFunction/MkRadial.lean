module
public import SpherePacking.ForMathlib.RadialSchwartz.OneSided


/-!
# Radial Schwartz-map constructor (dimension 24)

This is shared by both the `a`- and `b`-eigenfunction developments.
-/

namespace SpherePacking.Dim24

open scoped SchwartzMap
open SchwartzMap

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

noncomputable section

/-- Build a radial Schwartz map on `ℝ²⁴` from a one-variable function.

The hypotheses ensure smoothness after multiplying by the cutoff function and provide
one-sided Schwartz decay on `x ≥ 0`. -/
@[expose] public def mkRadial (f : ℝ → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) (fun r ↦ RadialSchwartz.cutoffC r * f r))
    (hdec : ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    𝓢(ℝ²⁴, ℂ) :=
  RadialSchwartz.Bridge.schwartzMap_norm_sq_of_cutoffMul_contDiff_decay_nonneg
    (F := ℝ²⁴) f hg hdec

@[simp] lemma mkRadial_apply (f : ℝ → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) (fun r ↦ RadialSchwartz.cutoffC r * f r))
    (hdec : ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C)
    (x : ℝ²⁴) :
    mkRadial f hg hdec x = f (‖x‖ ^ 2) := by
  simp [mkRadial]

end

end SpherePacking.Dim24
