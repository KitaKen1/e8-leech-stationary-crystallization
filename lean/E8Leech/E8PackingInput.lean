import E8Leech.SPLPackingDensity
import E8Leech.ConditionalCrystallization
import SpherePacking.Dim8.MainTheorem

/-!
# The E8 packing input

Viazovska's theorem, as formalized in the ported Sphere-Packing-Lean development
(`SpherePacking.Dim8.MainTheorem`), bounds every packing density in dimension eight by
`π⁴ / 384`, the volume of a ball of radius `√2 / 2`. Combined with the guard-box periodization
this proves the `packing` field of `PeriodicStabilityInput` for `e8Set` at the minimal distance
`√2`. The BRR event field is left as an explicit input.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric
open scoped ENNReal

theorem volume_ball_sqrt_two_div_two :
    volume (ball (0 : Ambient 8) (Real.sqrt 2 / 2)) = ENNReal.ofReal Real.pi ^ 4 / 384 := by
  have hball : volume (ball (0 : Ambient 8) (Real.sqrt 2 / 2)) =
      ENNReal.ofReal (Real.sqrt 2 / 2) ^ 8 * ENNReal.ofReal (Real.pi ^ 4 / 24) := by
    simp [InnerProductSpace.volume_ball_of_dim_even (E := Ambient 8) (k := 4) (hk := by simp),
      finrank_euclideanSpace, Nat.factorial]
  have hsq : (Real.sqrt 2 / 2) ^ 8 = 1 / 16 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    calc (Real.sqrt 2 / 2) ^ 8 = (Real.sqrt 2 ^ 2) ^ 4 / 256 := by ring
      _ = 1 / 16 := by rw [h2]; norm_num
  rw [hball, ← ENNReal.ofReal_pow (by positivity), hsq, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_pow Real.pi_pos.le]
  have h : (1 / 16 : ℝ) * (Real.pi ^ 4 / 24) = Real.pi ^ 4 / 384 := by ring
  rw [h, ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

/-- Viazovska's bound in guard-box form: an `√2`-separated configuration has guard density
at most one. -/
theorem e8_guardDensity_le_one (c : Configuration (Ambient 8)) (L : ℝ)
    (hL : Real.sqrt 2 < L)
    (hs : ∀ x ∈ c.support, ∀ y ∈ c.support, x ≠ y → Real.sqrt 2 ≤ dist x y) :
    guardDensity c L (Real.sqrt 2) ≤ 1 := by
  have h := guard_count_mul_volume_div_le_constant (d := 8) (by norm_num) c L (Real.sqrt 2)
    (by positivity) hL hs
  rw [SpherePacking.Dim8.MainTheorem, E8Packing_density, volume_ball_sqrt_two_div_two] at h
  have hV0 : ENNReal.ofReal Real.pi ^ 4 / 384 ≠ 0 := by
    simp [ENNReal.div_eq_zero_iff, Real.pi_pos]
  have hVtop : ENNReal.ofReal Real.pi ^ 4 / 384 ≠ ∞ := by
    simp [ENNReal.div_eq_top]
  rw [ENNReal.mul_div_right_comm] at h
  have h' : guardDensity c L (Real.sqrt 2) * (ENNReal.ofReal Real.pi ^ 4 / 384) ≤
      1 * (ENNReal.ofReal Real.pi ^ 4 / 384) := by
    simpa [guardDensity] using h
  exact (ENNReal.mul_le_mul_iff_left hV0 hVtop).1 h'

/-- The `packing` field of `PeriodicStabilityInput` for `E8`, at the minimal distance `√2`. -/
theorem e8_expandAfterDeletion_guardDensity_le_one (z : Configuration (Ambient 8)) (L t : ℝ)
    (hL : Real.sqrt 2 < L) (ht : t < 1) :
    guardDensity (expandAfterDeletion z (Real.sqrt 2) t ht) L (Real.sqrt 2) ≤ 1 :=
  e8_guardDensity_le_one _ L hL (expandAfterDeletion_separated z _ t ht)

/-- The BRR event field of `PeriodicStabilityInput`, isolated as the remaining periodic input. -/
def PeriodicEventInput {d : ℕ} (Λ : Set (Ambient d)) (r E B c η₀ : ℝ) : Prop :=
  ∀ μ : Measure (Configuration (Ambient d)), IsProbabilityMeasure μ →
    ∀ (L t R η : ℝ) (hr : 0 < r) (hL : r < L) (ht : t < 1),
      0 ≤ R → r + 2 * R ≤ L → 0 < η → η < η₀ →
      0 < observationRadius η → observationRadius η ≤ R →
      2 * R ≤ (624 / 25 : ℝ) * observationRadius η →
      ∃ H S : Set (Configuration (Ambient d) × Ambient d), MeasurableSet H ∧
        (∀ z ∈ H, LocalCrystal Λ
          (translate (-z.2) (guardedExpandedConfiguration z.1 L r t hr hL ht))
          R (E * Real.exp (c * observationRadius η) * η ^ (1 / 4 : ℝ))
          (B * observationRadius η ^ (-1 / 2 : ℝ))) ∧
        Hᶜ ⊆ {z | ENNReal.ofReal η ≤ expandedGuardDeficit z.1 L r t ht} ∪ S ∧
        (μ.prod (uniformPeriodCell d L)) S ≤
          ENNReal.ofReal (B * observationRadius η ^ (-1 / 2 : ℝ))

/-- For `E8` only the BRR event field remains among the periodic inputs. -/
theorem e8_periodicStabilityInput_of_events {E B c η₀ : ℝ}
    (hevents : PeriodicEventInput e8Set (Real.sqrt 2) E B c η₀) :
    PeriodicStabilityInput e8Set (Real.sqrt 2) E B c η₀ :=
  ⟨fun z L t hL ht => e8_expandAfterDeletion_guardDensity_le_one z L t hL ht, hevents⟩

end E8Leech
