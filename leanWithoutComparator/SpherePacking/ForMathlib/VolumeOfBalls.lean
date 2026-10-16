-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls


/-!
# Volume of balls

This file proves results such as `EuclideanSpace.volume_ball_pos` and
`EuclideanSpace.volume_ball_lt_top`.
-/

open Metric MeasureTheory

variable {r : ℝ} {ι : Type*} [Fintype ι]

/-- The Lebesgue volume of a nontrivial Euclidean ball is positive. -/
public theorem EuclideanSpace.volume_ball_pos [Nonempty ι] (x : EuclideanSpace ℝ ι) (hr : 0 < r) :
    0 < volume (ball x r) := by
  simpa using measure_ball_pos (μ := volume) x hr

/-- The Lebesgue volume of a Euclidean ball is finite. -/
public theorem EuclideanSpace.volume_ball_lt_top
    [MeasureTheory.NullSingletonClass (volume : Measure (EuclideanSpace ℝ ι))] (x : EuclideanSpace ℝ ι) :
    volume (ball x r) < ⊤ := by
  simpa using measure_ball_lt_top (μ := volume) (x := x) (r := r)
