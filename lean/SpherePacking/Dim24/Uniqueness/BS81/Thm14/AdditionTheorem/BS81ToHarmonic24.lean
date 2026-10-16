-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.MeanZeroHarmonics24.Basic
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.AvgLemmas24
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.EvalLemmas24
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.Defs

/-!
# From the BS81 axiom to harmonic moments

This file proves the reverse direction in the bridge:
`IsBS81SphericalDesign24 t C → IsHarmonicDesign24 t C`.

The proof specializes the BS81 averaging identity to harmonic homogeneous polynomials and uses
that their sphere average is `0` in positive degree.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24

noncomputable section

open scoped BigOperators RealInnerProductSpace

open Uniqueness.BS81.LP

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

lemma bs81_unit_norm {t : ℕ} {C : Finset ℝ²⁴} (hD : IsBS81SphericalDesign24 t C) :
    ∀ u ∈ C, ‖u‖ = (1 : ℝ) :=
  hD.1

lemma bs81_avg_eq_sphereAvg
    {t : ℕ} {C : Finset ℝ²⁴} (hD : IsBS81SphericalDesign24 t C)
    (k : ℕ) (p : MvPolynomial (Fin 24) ℝ) (hk : k ≤ t) (hp : p.IsHomogeneous k) :
    finsetAvg C (mvPolyEval24 p) = sphereAvg24 (mvPolyEval24 p) :=
  hD.2 k p hk hp

lemma finsetAvg_evalPk24_eq_sphereAvg24_evalPk24_of_bs81
    (t : ℕ) (C : Finset ℝ²⁴) (hD : IsBS81SphericalDesign24 t C)
    (k : ℕ) (p : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk k)
    (hk : k ≤ t) :
    finsetAvg C (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) p) =
      sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) p) := by
  -- Apply BS81's identity to the underlying `MvPolynomial`.
  simpa [Bridge24.mvPolyEval24_eq_evalPk24_of_memPk (p := p)] using!
    bs81_avg_eq_sphereAvg (hD := hD) (k := k) (p := p.1) hk p.2

/-- BS81 equation (14) implies vanishing of all harmonic moments (dimension `24`). -/
public theorem isHarmonicDesign24_of_isBS81SphericalDesign24
    (t : ℕ) (C : Finset ℝ²⁴) (hD : IsBS81SphericalDesign24 t C) :
    IsHarmonicDesign24 t C := by
  intro k hk1 hkt h
  -- First get equality of averages from BS81 applied to the underlying polynomial.
  have havg :
      finsetAvg C
          (fun x : ℝ²⁴ =>
            evalPk24 (k := k) (y := x) (h : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk k)) =
        sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x)
          (h : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk k)) := by
    -- `h : Harm k` coerces to `Pk k`.
    exact finsetAvg_evalPk24_eq_sphereAvg24_evalPk24_of_bs81 t C hD k (↑h) hkt
  -- The sphere average is `0` for `k ≥ 1`.
  have hsph0 :
      sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x)
        (h : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk k)) = 0 :=
    Bridge24.sphereAvg24_harmonic_degree_pos_eq_zero (k := k) hk1 h
  -- Hence the finite average is `0`, so the finite sum is `0`.
  have havg0 :
      finsetAvg C (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x)
        (h : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk k)) = 0 := by
    simpa [hsph0] using! havg
  exact sum_eq_zero_of_finsetAvg_eq_zero C (fun u => evalPk24 k u ↑h) havg0

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24
