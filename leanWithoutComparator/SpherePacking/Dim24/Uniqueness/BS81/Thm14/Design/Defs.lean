module
public import SpherePacking.Dim24.Uniqueness.BS81.Defs
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.Defs
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Design-theoretic definitions for Theorem 14

This folder uses a Gegenbauer-double-sum characterization of spherical designs, since it interacts
directly with the Delsarte LP equality case (complementary slackness).

## References
* `paper/BS81/sources.tex`, §4, Theorem 14 and equation (14)
* CK06/CK09: addition theorem / zonal kernels / "sharp bound implies design"
* BDHSS15: design characterizations via harmonic/Gegenbauer sums
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14

noncomputable section

open scoped RealInnerProductSpace BigOperators

open Polynomial
open MeasureTheory

open Uniqueness.BS81.LP

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- The unit sphere `S^{23}` in `ℝ²⁴`, as a set. We use it as a type via coercion. -/
public abbrev S23 : Set ℝ²⁴ :=
  Metric.sphere (0 : ℝ²⁴) (1 : ℝ)

/-!
## Gegenbauer double sums

For a finite `C ⊆ Ω₂₄`, the (normalized) Gegenbauer polynomials `Gegenbauer24 k` define zonal
kernels `(u,v) ↦ Gegenbauer24 k (⟪u,v⟫)`. In the Delsarte method, their double sums are nonnegative.

In the equality case, the double sums for `k=1..t` vanish, which is equivalent to `C` being a
spherical `t`-design (after connecting to the addition theorem / harmonic decomposition).
-/

/-- The raw Gegenbauer double sum `∑_{u,v∈C} P_k(⟪u,v⟫)` for `Ω₂₄`. -/
@[expose] public def gegenbauerDoubleSum24 (k : ℕ) (C : Finset ℝ²⁴) : ℝ :=
  C.sum (fun u => C.sum (fun v => (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)))

/-- Gegenbauer-design predicate: all Gegenbauer double sums vanish for degrees `1..t`. -/
@[expose] public def IsGegenbauerDesign24 (t : ℕ) (C : Finset ℝ²⁴) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ t → gegenbauerDoubleSum24 k C = 0

/-!
## Bridge to BS81's equation (14)

BS81 define a spherical `t`-design via averaging *homogeneous polynomials* of degree `≤ t` over `C`
and over the sphere (equation (14)). We record this as the separate predicate
`IsBS81SphericalDesign24`.

The Gegenbauer-sum characterization `IsGegenbauerDesign24` is the form that interacts directly with
the Delsarte LP equality case, and the addition theorem provides the link between the two
descriptions.

We define BS81's design axiom using the *surface measure* on the unit sphere obtained from Haar
measure on `ℝ²⁴` via `Measure.toSphere` (`Mathlib.MeasureTheory.Constructions.HaarToSphere`).
-/

/-- Surface measure on the unit sphere `Ω₂₄` (as `Measure.toSphere volume`). -/
@[expose] public def sphereMeasure24 : Measure S23 :=
  volume.toSphere

/-- Evaluate an `MvPolynomial` in `24` variables at `x : ℝ²⁴` by plugging in the coordinates. -/
@[expose] public def mvPolyEval24 (p : MvPolynomial (Fin 24) ℝ) (x : ℝ²⁴) : ℝ :=
  p.eval x

attribute [grind =] mvPolyEval24

/-- Average of a function over a finite set (as a real number). -/
@[expose] public def finsetAvg (C : Finset ℝ²⁴) (f : ℝ²⁴ → ℝ) : ℝ :=
  (C.card : ℝ)⁻¹ * C.sum f

attribute [grind =] finsetAvg

/-- Average of a function over the unit sphere `Ω₂₄` with respect to `sphereMeasure24`. -/
@[expose] public def sphereAvg24 (f : ℝ²⁴ → ℝ) : ℝ :=
  ((sphereMeasure24 (Set.univ)).toReal)⁻¹ *
    ∫ x : S23, f x.1 ∂(sphereMeasure24)

/-- BS81's spherical-design axiom (equation (14)), specialized to `Ω₂₄`.

We quantify over homogeneous multivariate polynomials of total degree `k ≤ t` and require that the
finite average equals the spherical average.
-/
@[expose] public def IsBS81SphericalDesign24 (t : ℕ) (C : Finset ℝ²⁴) : Prop :=
  (∀ u ∈ C, ‖u‖ = (1 : ℝ)) ∧
    ∀ (k : ℕ) (p : MvPolynomial (Fin 24) ℝ),
      k ≤ t →
        p.IsHomogeneous k →
          finsetAvg C (mvPolyEval24 p) = sphereAvg24 (mvPolyEval24 p)

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14
