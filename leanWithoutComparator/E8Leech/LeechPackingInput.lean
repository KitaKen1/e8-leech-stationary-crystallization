import E8Leech.E8PackingInput
import SpherePacking.Dim24.MagicFunction.F.UpperBound

/-!
# The Leech packing input

The ported Sphere-Packing-Lean development proves the Cohn–Elkies bound in dimension twenty-four
(`SpherePacking.Dim24.SpherePackingConstant_le_leech_density`): every packing density is at most
`π¹² / 12!`, the volume of a unit ball. Combined with the guard-box periodization this proves the
`packing` field of `PeriodicStabilityInput` for `leechSet` at the minimal distance `2`. Only the
upper bound is used; the uniqueness part of the Leech theorem is not needed. The BRR event field
is left as an explicit input.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric
open scoped ENNReal

theorem volume_ball_one_twentyFour :
    volume (ball (0 : Ambient 24) 1) = ENNReal.ofReal Real.pi ^ 12 / (Nat.factorial 12) := by
  have hball : volume (ball (0 : Ambient 24) 1) =
      ENNReal.ofReal 1 ^ 24 * ENNReal.ofReal (Real.pi ^ 12 / (Nat.factorial 12)) := by
    simp [InnerProductSpace.volume_ball_of_dim_even (E := Ambient 24) (k := 12) (hk := by simp),
      finrank_euclideanSpace]
  rw [hball, ENNReal.ofReal_one, one_pow, one_mul, ENNReal.ofReal_div_of_pos (by positivity),
    ENNReal.ofReal_pow Real.pi_pos.le, ENNReal.ofReal_natCast]

/-- The Cohn–Elkies bound in guard-box form: a `2`-separated configuration in `ℝ²⁴` has guard
density at most one. -/
theorem leech_guardDensity_le_one (c : Configuration (Ambient 24)) (L : ℝ) (hL : 2 < L)
    (hs : ∀ x ∈ c.support, ∀ y ∈ c.support, x ≠ y → 2 ≤ dist x y) :
    guardDensity c L 2 ≤ 1 := by
  have h := (guard_count_mul_volume_div_le_constant (d := 24) (by norm_num) c L 2
    (by norm_num) hL hs).trans SpherePacking.Dim24.SpherePackingConstant_le_leech_density
  rw [show (2 : ℝ) / 2 = 1 by norm_num, volume_ball_one_twentyFour] at h
  have hV0 : ENNReal.ofReal Real.pi ^ 12 / (Nat.factorial 12 : ℝ≥0∞) ≠ 0 := by
    simp [ENNReal.div_eq_zero_iff, Real.pi_pos]
  have hVtop : ENNReal.ofReal Real.pi ^ 12 / (Nat.factorial 12 : ℝ≥0∞) ≠ ∞ := by
    simp [ENNReal.div_eq_top, Nat.factorial_ne_zero]
  rw [ENNReal.mul_div_right_comm] at h
  have h' : guardDensity c L 2 * (ENNReal.ofReal Real.pi ^ 12 / (Nat.factorial 12 : ℝ≥0∞)) ≤
      1 * (ENNReal.ofReal Real.pi ^ 12 / (Nat.factorial 12 : ℝ≥0∞)) := by
    simpa [guardDensity] using h
  exact (ENNReal.mul_le_mul_iff_left hV0 hVtop).1 h'

/-- The `packing` field of `PeriodicStabilityInput` for the Leech lattice, at minimal distance
`2`. -/
theorem leech_expandAfterDeletion_guardDensity_le_one (z : Configuration (Ambient 24)) (L t : ℝ)
    (hL : 2 < L) (ht : t < 1) :
    guardDensity (expandAfterDeletion z 2 t ht) L 2 ≤ 1 :=
  leech_guardDensity_le_one _ L hL (expandAfterDeletion_separated z _ t ht)

/-- For the Leech lattice only the BRR event field remains among the periodic inputs. -/
theorem leech_periodicStabilityInput_of_events {E B c η₀ : ℝ}
    (hevents : PeriodicEventInput leechSet 2 E B c η₀) :
    PeriodicStabilityInput leechSet 2 E B c η₀ :=
  ⟨fun z L t hL ht => leech_expandAfterDeletion_guardDensity_le_one z L t hL ht, hevents⟩

end E8Leech
