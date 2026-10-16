import E8Leech.ZeroExcessLatticeContainment
import E8Leech.LeechLatticeCount
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# A density-one subset detects every lattice difference

For a subset of a covolume-one affine lattice, the growing-ball lower bound
from Z1 forces every lattice vector to occur as a difference of two points.
The proof uses the disjoint-translate counting argument, without classifying
the rank or index of intersections of lattices.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal

theorem eventually_shifted_power_lt_twice_density (d : ℕ) (C : ℝ)
    (R loss : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (hloss : Tendsto loss atTop (𝓝 0)) :
    ∀ᶠ n in atTop, (R n + C) ^ d < 2 * (1 - loss n) * (R n) ^ d := by
  have hi : Tendsto (fun n => (R n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hR
  have hp : Tendsto (fun n => (1 + C * (R n)⁻¹) ^ d) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
      (hi.const_mul C)).pow d
  have hq : Tendsto (fun n => 2 * (1 - loss n)) atTop (𝓝 2) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
      hloss).const_mul 2
  filter_upwards [hp.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 3 / 2)),
    hq.eventually (lt_mem_nhds (by norm_num : (3 / 2 : ℝ) < 2)),
    hR.eventually (eventually_gt_atTop 0)] with n hp hq hn
  have h := mul_lt_mul_of_pos_right (hp.trans hq) (pow_pos hn d)
  have he : (1 + C * (R n)⁻¹) ^ d * (R n) ^ d = (R n + C) ^ d := by
    rw [← mul_pow]
    congr 1
    field_simp
  rwa [he] at h

theorem eventually_enlarged_ball_lt_twice_density {d : ℕ} (C : ℝ) (hC : 0 ≤ C)
    (a : Ambient d) (R loss : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (hloss : Tendsto loss atTop (𝓝 0)) :
    ∀ᶠ n in atTop, volume.real (closedBall a (R n + C)) <
      2 * (1 - loss n) * volume.real (closedBall (0 : Ambient d) (R n)) := by
  filter_upwards [eventually_shifted_power_lt_twice_density d C R loss hR hloss,
    hR.eventually (eventually_gt_atTop 0)] with n hn hRn
  rw [Measure.addHaar_real_closedBall' volume a (by linarith),
    Measure.addHaar_real_closedBall' volume 0 hRn.le]
  have hv : 0 < volume.real (closedBall (0 : Ambient d) 1) := by
    exact ENNReal.toReal_pos (measure_closedBall_pos volume 0 (by norm_num)).ne'
      (measure_closedBall_lt_top (μ := volume)).ne
  have he : Module.finrank ℝ (Ambient d) = d := by simp [Ambient]
  rw [he]
  nlinarith [mul_lt_mul_of_pos_right hn hv]

end E8Leech
