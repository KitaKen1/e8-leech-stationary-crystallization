import E8Leech.GuardedPeriodization
import E8Leech.LocalSecondMoments
import SpherePacking.Basic.PeriodicPacking.PeriodicConstant
import SpherePacking.Basic.PeriodicPacking.DensityFormula

/-!
# Guard-box densities as periodic packing densities

A separated configuration is a Sphere-Packing-Lean packing. Its points in the guard box
`[r/2, L - r/2)^d` periodize along `L ℤ^d` (Sphere-Packing-Lean's cube periodization) to a
periodic packing whose density is `count * vol(B(r/2)) / L^d`. Hence the guard-box count is
bounded by the sphere packing constant. No packing optimality is used in this file.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

/-- A separated configuration, viewed as a Sphere-Packing-Lean packing. -/
def splPacking {d : ℕ} (c : Configuration (Ambient d)) (r : ℝ) (hr : 0 < r)
    (hs : ∀ x ∈ c.support, ∀ y ∈ c.support, x ≠ y → r ≤ dist x y) : SpherePacking d where
  centers := c.support
  separation := r
  separation_pos := hr
  centers_dist := by
    intro a b hab
    exact hs a a.2 b b.2 (fun h => hab (Subtype.ext h))

set_option backward.isDefEq.respectTransparency false in
theorem covolume_cubeLattice {d : ℕ} (L : ℝ) (hL : 0 < L) :
    ZLattice.covolume (cubeLattice (d := d) L hL) volume = L ^ d := by
  have : DiscreteTopology (cubeLattice (d := d) L hL) := by dsimp [cubeLattice]; infer_instance
  have : IsZLattice ℝ (cubeLattice (d := d) L hL) := by dsimp [cubeLattice]; infer_instance
  have hfund : IsAddFundamentalDomain (cubeLattice (d := d) L hL)
      (ZSpan.fundamentalDomain (cubeBasis (d := d) L hL)) volume := by
    simpa [cubeLattice] using (ZSpan.isAddFundamentalDomain (cubeBasis (d := d) L hL) volume)
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ hfund,
    fundamentalDomain_cubeBasis_eq_coordCube, Measure.real, PeriodicConstant.volume_coordCube,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hL.le]

theorem guardInnerBox_subset_coordCubeInner {d : ℕ} (L r : ℝ) :
    guardInnerBox d L r ⊆ coordCubeInner (d := d) L (r / 2) := by
  intro x hx i
  exact Ico_subset_Icc_self (hx i)

set_option backward.isDefEq.respectTransparency false in
/-- The guard-box count, weighted by the ball volume, is a periodic packing density. -/
theorem guard_count_mul_volume_div_le_constant {d : ℕ} (hd : 0 < d)
    (c : Configuration (Ambient d)) (L r : ℝ) (hr : 0 < r) (hL : r < L)
    (hs : ∀ x ∈ c.support, ∀ y ∈ c.support, x ≠ y → r ≤ dist x y) :
    c.count (guardInnerBox d L r) * volume (ball (0 : Ambient d) (r / 2)) /
        ENNReal.ofReal L ^ d ≤ SpherePackingConstant d := by
  have hL0 : 0 < L := hr.trans hL
  let Λ : Submodule ℤ (Ambient d) := cubeLattice (d := d) L hL0
  have : DiscreteTopology Λ := by dsimp [Λ, cubeLattice]; infer_instance
  have : IsZLattice ℝ Λ := by dsimp [Λ, cubeLattice]; infer_instance
  let S : SpherePacking d := splPacking c r hr hs
  let F : Set (Ambient d) := c.support ∩ guardInnerBox d L r
  have hF_ball : ∀ x ∈ F, ball x (S.separation / 2) ⊆ coordCube (d := d) L := by
    intro x hx
    have h := PeriodicConstantApprox.ball_subset_vadd_coordCube_of_mem_vadd_inner (d := d)
      (L := L) (r := r / 2) hL0 (v := 0) (x := x)
      (by simpa using guardInnerBox_subset_coordCubeInner L r hx.2)
    have h' : ball x (r / 2) ⊆ coordCube (d := d) L := by simpa using h
    exact h'
  let P : PeriodicSpherePacking d :=
    periodize_to_periodicSpherePacking S Λ (coordCube (d := d) L) F
      (PeriodicConstant.coordCube_unique_covers (d := d) L hL0) (fun _ hx => hx.1) hF_ball
  have hF_sub : F ⊆ coordCube (d := d) L := fun x hx =>
    hF_ball x hx (mem_ball_self (half_pos hr))
  have hcenters : P.centers ∩ coordCube (d := d) L = F :=
    periodizedCenters_inter_eq_of_subset (d := d) (Λ := Λ) (D := coordCube (d := d) L)
      (F := F) hF_sub (PeriodicConstant.coordCube_unique_covers (d := d) L hL0)
  have hnum : ((P.numReps : ℕ∞) : ℝ≥0∞) = c.count (guardInnerBox d L r) := by
    rw [Configuration.count_eq_encard, ← P.encard_centers_inter_isFundamentalDomain
      (coordCube (d := d) L) (PeriodicConstant.isBounded_coordCube (d := d) L hL0)
      (PeriodicConstant.coordCube_unique_covers (d := d) L hL0) hd, hcenters]
  have hdens := P.density_eq' hd
  have hcov : (Real.toNNReal (ZLattice.covolume P.lattice) : ℝ≥0∞) = ENNReal.ofReal L ^ d := by
    change (Real.toNNReal (ZLattice.covolume (cubeLattice (d := d) L hL0)) : ℝ≥0∞) = _
    rw [covolume_cubeLattice, ← ENNReal.ofReal_pow hL0.le]
    rfl
  have hsep : P.separation = r := rfl
  rw [hcov, hnum, hsep] at hdens
  rw [← hdens]
  exact le_iSup (fun S : SpherePacking d => S.density) P.toSpherePacking

end E8Leech
