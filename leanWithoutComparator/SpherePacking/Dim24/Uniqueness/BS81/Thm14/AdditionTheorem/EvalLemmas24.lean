-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.DoubleSumsToHarmonics24
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.AvgLemmas24
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.IntegrableEvalPk24

/-!
# Evaluation and averaging lemmas for `Pk k`

These lemmas are glue steps used in the Fischer-induction proof: they record linearity of
`evalPk24` in the polynomial argument and compatibility of `finsetAvg` / `sphereAvg24` with
addition and scalar multiplication.
-/
namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24

noncomputable section

open scoped BigOperators RealInnerProductSpace

open Uniqueness.BS81.LP

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- Rewrite `mvPolyEval24` for a homogeneous polynomial packaged as `Fischer.Pk k`. -/
public lemma mvPolyEval24_eq_evalPk24_of_memPk {k : ℕ}
    (p : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk k) :
    mvPolyEval24 p.1 = fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) p := by
  rfl

lemma evalPk24_add (k : ℕ) (y : ℝ²⁴) (p q : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk k) :
    evalPk24 (k := k) (y := y) (p + q) =
      evalPk24 (k := k) (y := y) p + evalPk24 (k := k) (y := y) q := by
  -- `evalPk24` is just `MvPolynomial.eval`, hence additive.
  simp [evalPk24, evalPoly24]

lemma evalPk24_smul (k : ℕ) (y : ℝ²⁴) (a : ℝ)
    (p : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk k) :
    evalPk24 (k := k) (y := y) (a • p) = a * evalPk24 (k := k) (y := y) p := by
  simp [evalPk24, evalPoly24]

/-- `finsetAvg` respects addition in the polynomial argument of `evalPk24`. -/
public lemma finsetAvg_evalPk24_add (k : ℕ) (C : Finset ℝ²⁴)
    (p q : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk k) :
    finsetAvg C (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) (p + q)) =
      finsetAvg C (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) p) +
      finsetAvg C (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) q) := by
  -- Expand pointwise using `evalPk24_add`, then use `finsetAvg_add`.
  have hpoint : (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) (p + q)) =
      fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) p + evalPk24 (k := k) (y := x) q := by
    funext x
    simpa using! evalPk24_add (k := k) (y := x) (p := p) (q := q)
  simpa [hpoint] using!
    (Bridge24.finsetAvg_add (C := C)
      (f := fun x => evalPk24 (k := k) (y := x) p)
      (g := fun x => evalPk24 (k := k) (y := x) q))

/-- `sphereAvg24` respects addition in the polynomial argument of `evalPk24`. -/
public lemma sphereAvg24_evalPk24_add (k : ℕ)
    (p q : Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer.Pk k) :
    sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) (p + q)) =
      sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) p) +
      sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) q) := by
  have hpoint : (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) (p + q)) =
      fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) p + evalPk24 (k := k) (y := x) q := by
    funext x
    simpa using! evalPk24_add (k := k) (y := x) (p := p) (q := q)
  have hp :
      MeasureTheory.Integrable (fun x : S23 => evalPk24 (k := k) (y := x.1) p) sphereMeasure24 :=
    integrable_evalPk24 (k := k) (p := p)
  have hq :
      MeasureTheory.Integrable (fun x : S23 => evalPk24 (k := k) (y := x.1) q) sphereMeasure24 :=
    integrable_evalPk24 (k := k) (p := q)
  simpa [hpoint] using!
    (Uniqueness.BS81.Thm14.sphereAvg24_add
      (f := fun x => evalPk24 (k := k) (y := x) p)
      (g := fun x => evalPk24 (k := k) (y := x) q)
      (hf := hp) (hg := hq))

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24
