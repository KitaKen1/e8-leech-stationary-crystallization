-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.DoubleSumsToHarmonics24
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.AvgLemmas24
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.SphereAvg24Lemmas
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Integrability of `evalPk24` on the sphere

These lemmas show that the functions `x ↦ evalPk24 (y := x) p` are integrable over the unit
sphere, since they are continuous and `sphereMeasure24` is finite.

## Main statements
* `AdditionTheorem.Bridge24.integrable_evalPk24`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24

noncomputable section

open scoped BigOperators RealInnerProductSpace

open MeasureTheory
open Uniqueness.BS81.LP

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- The map `x ↦ evalPk24 (y := x) p` is integrable on the unit sphere. -/
public lemma integrable_evalPk24 (k : ℕ)
    (p : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk k) :
    Integrable (fun x : S23 => evalPk24 (k := k) (y := x.1) p) sphereMeasure24 := by
  have hcont₁ : Continuous fun y : ℝ²⁴ => evalPk24 (k := k) (y := y) p := by
    -- `evalPk24` is `MvPolynomial.eval` precomposed with `EuclideanSpace.ofLp`.
    have hofLp : Continuous (fun y : ℝ²⁴ => (fun i : Fin 24 => y.ofLp i)) := by
      simpa using! (PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : Fin 24 => ℝ))
    -- `MvPolynomial.eval` is continuous in the assignment.
    simpa [evalPk24, evalPoly24] using!
      (MvPolynomial.continuous_eval (p := (p.1 : MvPolynomial (Fin 24) ℝ))).comp hofLp
  have hcont : Continuous fun x : S23 => evalPk24 (k := k) (y := x.1) p :=
    hcont₁.comp continuous_subtype_val
  -- Use finiteness of `sphereMeasure24` and boundedness on the compact sphere.
  have hcomp : IsCompact (Set.univ : Set S23) := isCompact_univ
  have hnorm_cont :
      Continuous (fun x : S23 => ‖evalPk24 (k := k) (y := x.1) p‖) :=
    (hcont.norm)
  have hbdd :
      BddAbove ((fun x : S23 => ‖evalPk24 (k := k) (y := x.1) p‖) '' (Set.univ : Set S23)) :=
    (hcomp.image hnorm_cont).bddAbove
  rcases hbdd with ⟨C, hC⟩
  have hbound : ∀ x : S23, ‖evalPk24 (k := k) (y := x.1) p‖ ≤ C := by
    intro x
    have hx :
        ‖evalPk24 (k := k) (y := x.1) p‖ ∈
          ((fun x : S23 => ‖evalPk24 (k := k) (y := x.1) p‖) '' (Set.univ : Set S23)) :=
      ⟨x, by simp, rfl⟩
    exact hC hx
  haveI : MeasureTheory.IsFiniteMeasure sphereMeasure24 := ⟨
    sphereMeasure24_univ_lt_top⟩
  refine MeasureTheory.Integrable.of_bound (μ := sphereMeasure24) (f := fun x : S23 =>
      evalPk24 (k := k) (y := x.1) p)
    (hcont.aestronglyMeasurable) C ?_
  exact ae_of_all _ hbound

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24
