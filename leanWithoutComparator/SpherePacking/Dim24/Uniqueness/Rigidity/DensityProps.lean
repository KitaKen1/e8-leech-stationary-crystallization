-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Packing
import SpherePacking.Dim24.LeechLattice.Basis


/-!
# Density, covolume, and `numReps`

For a periodic packing at the Leech packing density (with separation `2`), we relate the covolume
of the underlying lattice to the number of centers per fundamental domain (`numReps`).

## Main statements
* `covolume_toNNReal_eq_numReps_of_density_eq_leech_normalized`
* `covolume_toNNReal_eq_numReps_nnreal_of_density_eq_leech_normalized`
* `covolume_eq_numReps_real_of_density_eq_leech_normalized`
-/

namespace SpherePacking.Dim24

open scoped ENNReal NNReal
open MeasureTheory Metric

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- For a packing at Leech density and separation `2`, `covolume` (as an `ENNReal`) equals
`numReps`. -/
public lemma covolume_toNNReal_eq_numReps_of_density_eq_leech_normalized
    (S : PeriodicSpherePacking 24)
    (hSep : S.separation = 2) (hDens : S.density = LeechPacking.density) :
    (Real.toNNReal (ZLattice.covolume S.lattice volume) : ENNReal) = (S.numReps : ENNReal) := by
  have hd : (0 : ℕ) < 24 := by decide
  have hvol_ne_zero : volume (ball (0 : ℝ²⁴) (1 : ℝ)) ≠ 0 :=
    ne_of_gt (EuclideanSpace.volume_ball_pos (x := (0 : ℝ²⁴)) (r := (1 : ℝ)) (by norm_num))
  have hvol_ne_top : volume (ball (0 : ℝ²⁴) (1 : ℝ)) ≠ ∞ :=
    (EuclideanSpace.volume_ball_lt_top (x := (0 : ℝ²⁴)) (r := (1 : ℝ))).ne
  have hLeech : LeechPacking.density = volume (ball (0 : ℝ²⁴) (1 : ℝ)) := by
    simp [PeriodicSpherePacking.density_eq' (S := LeechPacking) (d := 24) hd, LeechPacking_numReps,
      LeechPacking_separation, LeechPacking_lattice, leech_covolume]
  have hSd : S.density = volume (ball (0 : ℝ²⁴) (1 : ℝ)) := by
    simpa [hLeech] using! hDens
  have hSformula :
      S.density =
        (S.numReps : ENNReal) * volume (ball (0 : ℝ²⁴) (1 : ℝ)) /
          Real.toNNReal (ZLattice.covolume S.lattice volume) := by
    -- Rewrite `density_eq'` and normalize `S.separation / 2 = 1`.
    simp [PeriodicSpherePacking.density_eq' (S := S) (d := 24) hd, hSep]
  have hden_ne_zero :
      (Real.toNNReal (ZLattice.covolume S.lattice volume) : ENNReal) ≠ 0 := by
    have hc : 0 < ZLattice.covolume S.lattice volume := ZLattice.covolume_pos S.lattice volume
    exact ENNReal.coe_ne_zero.2 (ne_of_gt (by simpa [Real.toNNReal_pos] using! hc))
  have hden_ne_top :
      (Real.toNNReal (ZLattice.covolume S.lattice volume) : ENNReal) ≠ ∞ :=
    ENNReal.coe_ne_top
  -- Cancel the unit-ball volume from the density equality.
  have hratio :
      (S.numReps : ENNReal) / Real.toNNReal (ZLattice.covolume S.lattice volume) = 1 := by
    apply (ENNReal.mul_left_inj (c := volume (ball (0 : ℝ²⁴) (1 : ℝ))) hvol_ne_zero hvol_ne_top).1
    have hEq :
        (S.numReps : ENNReal) * volume (ball (0 : ℝ²⁴) (1 : ℝ)) /
            Real.toNNReal (ZLattice.covolume S.lattice volume)
          =
          volume (ball (0 : ℝ²⁴) (1 : ℝ)) := by
      simpa [hSformula] using! hSd
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using! hEq
  -- Turn `a / b = 1` into `a = b`.
  have hEq :
      (S.numReps : ENNReal) =
        (Real.toNNReal (ZLattice.covolume S.lattice volume) : ENNReal) := by
    exact (ENNReal.div_eq_one_iff hden_ne_zero hden_ne_top).1 hratio
  simpa [eq_comm] using! hEq

/-- `NNReal` version of `covolume_toNNReal_eq_numReps_of_density_eq_leech_normalized`. -/
public lemma covolume_toNNReal_eq_numReps_nnreal_of_density_eq_leech_normalized
    (S : PeriodicSpherePacking 24)
    (hSep : S.separation = 2) (hDens : S.density = LeechPacking.density) :
    Real.toNNReal (ZLattice.covolume S.lattice volume) = (S.numReps : ℝ≥0) := by
  exact_mod_cast covolume_toNNReal_eq_numReps_of_density_eq_leech_normalized (S := S) hSep hDens

/-- `Real` version of `covolume_toNNReal_eq_numReps_of_density_eq_leech_normalized`. -/
public lemma covolume_eq_numReps_real_of_density_eq_leech_normalized (S : PeriodicSpherePacking 24)
    (hSep : S.separation = 2) (hDens : S.density = LeechPacking.density) :
    ZLattice.covolume S.lattice volume = (S.numReps : ℝ) := by
  have hNN :
      Real.toNNReal (ZLattice.covolume S.lattice volume) = (S.numReps : ℝ≥0) :=
    covolume_toNNReal_eq_numReps_nnreal_of_density_eq_leech_normalized (S := S) hSep hDens
  have hc : 0 ≤ ZLattice.covolume S.lattice volume := (ZLattice.covolume_pos S.lattice volume).le
  have hNN' : (Real.toNNReal (ZLattice.covolume S.lattice volume) : ℝ) = (S.numReps : ℝ) := by
    simpa using! congrArg (fun t : ℝ≥0 => (t : ℝ)) hNN
  simpa [hc] using! hNN'

end SpherePacking.Dim24
