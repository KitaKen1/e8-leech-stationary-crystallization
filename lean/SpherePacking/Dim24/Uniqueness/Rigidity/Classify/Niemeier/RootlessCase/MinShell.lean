-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.RootlessCase.ThetaExtremal
public import
  SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.RootlessCase.QExpansionCoeffTwo
public import Mathlib.Data.Int.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Minimal shell consequences

This file packages elementary facts about the shell `thetaShell L 2`, i.e. lattice vectors of
squared norm `4`, for even unimodular rootless lattices in `ℝ²⁴`.

In particular, once we know the shell count `thetaCoeff L 2 = 196560`, we can treat this shell as
a well-controlled finite configuration.

## Main definitions
* `NiemeierRootless.minShell`

## Main statements
* `NiemeierRootless.thetaCoeff_two_eq_196560_of_even_unimodular_rootless`
* `NiemeierRootless.minShell_ncard_eq_196560_of_even_unimodular_rootless`
* `NiemeierRootless.norm_eq_two_of_mem_minShell`
-/


namespace SpherePacking.Dim24.Uniqueness.RigidityClassify
noncomputable section

open scoped RealInnerProductSpace CongruenceSubgroup
open Complex UpperHalfPlane ModularFormClass

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace NiemeierRootless

variable {L : Submodule ℤ ℝ²⁴}

/-- If `‖u‖² = ‖v‖² = 4` and `⟪u,v⟫ = -4`, then `u` and `v` are antipodes. -/
public lemma add_eq_zero_of_normSq_eq_four_of_inner_eq_neg_four {u v : ℝ²⁴}
    (huSq : ‖u‖ ^ 2 = (4 : ℝ)) (hvSq : ‖v‖ ^ 2 = (4 : ℝ)) (hinner : ⟪u, v⟫ = (-4 : ℝ)) :
    u + v = 0 := by
  have hadd :
      ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * ⟪u, v⟫ + ‖v‖ ^ 2 := by
    simpa using! (norm_add_sq_real u v)
  have hnormsq : ‖u + v‖ ^ 2 = (0 : ℝ) := by
    nlinarith [hadd, huSq, hvSq, hinner]
  have hnorm : ‖u + v‖ = 0 := by
    have : (‖u + v‖) ^ 2 = (0 : ℝ) := by simpa using! hnormsq
    exact (sq_eq_zero_iff).1 this
  simpa using! (norm_eq_zero.1 hnorm)

/-- For even unimodular rootless lattices in rank `24`, the `q^2` coefficient of the theta series
is `196560`. -/
public theorem thetaCoeff_two_eq_196560_of_even_unimodular_rootless
    (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L] [IsZLattice ℝ L]
    (hEven : EvenNormSq L) (hUnimod : Unimodular L) (hRootless : Rootless L) :
    thetaCoeff L 2 = 196560 := by
  -- Get the modular form representation of `thetaSeriesUHP L` with the computed `q^2` coefficient.
  rcases
      qExpansion_coeff_two_thetaSeries_of_even_unimodular_rootless
        (L := L) hEven hUnimod hRootless with
    ⟨f, hf, hq2⟩
  -- Convert the `q^2` coefficient into a shell count.
  have hθ :
      (qExpansion (1 : ℝ) f).coeff 2 = (thetaCoeff L 2 : ℂ) :=
    qExpansion_coeff_two_thetaSeries_eq_thetaCoeff (L := L) (hEven := hEven) (f := f) (hf := hf)
  exact_mod_cast (hθ.symm.trans hq2)

/-- The minimal shell in the rootless even unimodular normalization: `‖v‖² = 4`. -/
@[expose]
public def minShell (L : Submodule ℤ ℝ²⁴) : Set ℝ²⁴ :=
  thetaShell L 2

@[simp] lemma minShell_def (L : Submodule ℤ ℝ²⁴) : minShell L = thetaShell L 2 := rfl

theorem finite_minShell (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L] : (minShell L).Finite := by
  simpa [minShell] using! (finite_thetaShell (L := L) 2)

theorem ncard_minShell_eq_thetaCoeff (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L] :
    Set.ncard (minShell L) = thetaCoeff L 2 := by
  -- Both sides are `Finite.toFinset.card` by definition.
  simpa [minShell, thetaCoeff] using!
    (Set.ncard_eq_toFinset_card (thetaShell L 2) (finite_thetaShell (L := L) 2))

/-- For an even unimodular rootless lattice, the minimal shell has `196560` elements. -/
public theorem minShell_ncard_eq_196560_of_even_unimodular_rootless
    (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L] [IsZLattice ℝ L]
    (hEven : EvenNormSq L) (hUnimod : Unimodular L) (hRootless : Rootless L) :
    Set.ncard (minShell L) = 196560 := by
  have hθ : thetaCoeff L 2 = 196560 :=
    thetaCoeff_two_eq_196560_of_even_unimodular_rootless (L := L) hEven hUnimod hRootless
  calc
    Set.ncard (minShell L) = thetaCoeff L 2 := by
      simpa using! (ncard_minShell_eq_thetaCoeff (L := L))
    _ = 196560 := hθ

theorem exists_mem_minShell_of_thetaCoeff_two_pos
    (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L]
    (hpos : 0 < thetaCoeff L 2) : ∃ v : ℝ²⁴, v ∈ minShell L := by
  rcases (show (thetaShell L 2).Nonempty by simpa [thetaCoeff] using! hpos) with ⟨v, hv⟩
  exact ⟨v, by simpa [minShell] using! hv⟩

theorem exists_normSq_eq_four_of_thetaCoeff_two_pos
    (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L]
    (hpos : 0 < thetaCoeff L 2) : ∃ v : ℝ²⁴, v ∈ L ∧ ‖v‖ ^ 2 = (4 : ℝ) := by
  rcases exists_mem_minShell_of_thetaCoeff_two_pos (L := L) hpos with ⟨v, hv⟩
  refine ⟨v, hv.1, ?_⟩
  -- `hv.2 : ‖v‖² = 2 * 2`.
  calc
    ‖v‖ ^ 2 = (2 : ℝ) * (2 : ℕ) := hv.2
    _ = (4 : ℝ) := by norm_num

theorem normSq_eq_four_of_mem_minShell (L : Submodule ℤ ℝ²⁴) {v : ℝ²⁴} (hv : v ∈ minShell L) :
    ‖v‖ ^ 2 = (4 : ℝ) := by
  calc
    ‖v‖ ^ 2 = (2 : ℝ) * (2 : ℕ) := hv.2
    _ = (4 : ℝ) := by norm_num

/-- For `v ∈ minShell L`, we have `‖v‖ = 2`. -/
public theorem norm_eq_two_of_mem_minShell (L : Submodule ℤ ℝ²⁴) {v : ℝ²⁴} (hv : v ∈ minShell L) :
    ‖v‖ = (2 : ℝ) := by
  have hvSq : ‖v‖ ^ 2 = (2 : ℝ) ^ 2 := by
    calc
      ‖v‖ ^ 2 = (2 : ℝ) * (2 : ℕ) := hv.2
      _ = (4 : ℝ) := by norm_num
      _ = (2 : ℝ) ^ 2 := by norm_num
  exact (sq_eq_sq₀ (norm_nonneg v) (by norm_num : (0 : ℝ) ≤ 2)).1 hvSq

theorem minShell_closed_under_neg (L : Submodule ℤ ℝ²⁴) :
    ∀ ⦃v : ℝ²⁴⦄, v ∈ minShell L → (-v) ∈ minShell L := by
  intro v hv
  rcases hv with ⟨hvL, hvSq⟩
  refine ⟨neg_mem hvL, ?_⟩
  have hnorm : ‖(-v)‖ ^ 2 = ‖v‖ ^ 2 := by
    -- `‖-v‖ = ‖v‖`
    exact congrArg (fun r : ℝ => r ^ 2) (norm_neg v)
  -- keep the right-hand side in the `thetaShell` format
  calc
    ‖(-v)‖ ^ 2 = ‖v‖ ^ 2 := hnorm
    _ = (2 : ℝ) * (2 : ℕ) := hvSq

theorem innerProduct_int_of_even_of_mem_minShell
    (hEven : EvenNormSq L) :
    ∀ ⦃u v : ℝ²⁴⦄, u ∈ minShell L → v ∈ minShell L → ∃ m : ℤ, ⟪u, v⟫ = m := by
  intro u v hu hv
  have hInt : Integral L := integral_of_evenNormSq (L := L) hEven
  exact hInt u v hu.1 hv.1

theorem innerProduct_mem_Icc_int_of_even_of_mem_minShell
    (hEven : EvenNormSq L) :
    ∀ ⦃u v : ℝ²⁴⦄, u ∈ minShell L → v ∈ minShell L →
      ∃ m : ℤ, m ∈ Set.Icc (-4 : ℤ) 4 ∧ ⟪u, v⟫ = m := by
  intro u v hu hv
  rcases innerProduct_int_of_even_of_mem_minShell (L := L) hEven hu hv with ⟨m, hm⟩
  have hu2 : ‖u‖ = (2 : ℝ) := norm_eq_two_of_mem_minShell (L := L) hu
  have hv2 : ‖v‖ = (2 : ℝ) := norm_eq_two_of_mem_minShell (L := L) hv
  -- Cauchy-Schwarz: `|⟪u,v⟫| ≤ ‖u‖‖v‖ = 4`.
  have habs : |⟪u, v⟫| ≤ (4 : ℝ) := by
    have hcs : |⟪u, v⟫| ≤ ‖u‖ * ‖v‖ := abs_real_inner_le_norm u v
    calc
      |⟪u, v⟫| ≤ ‖u‖ * ‖v‖ := hcs
      _ = (2 : ℝ) * (2 : ℝ) := by simp [hu2, hv2]
      _ = (4 : ℝ) := by norm_num
  have hmabs : |(m : ℝ)| ≤ (4 : ℝ) := by simpa [hm] using! habs
  have hmIcc : m ∈ Set.Icc (-4 : ℤ) 4 := by
    have hle4 : (m : ℝ) ≤ 4 := (abs_le.mp hmabs).2
    have hge : (-4 : ℝ) ≤ (m : ℝ) := (abs_le.mp hmabs).1
    have hle4Z : m ≤ 4 := by exact_mod_cast hle4
    have hgeZ : (-4 : ℤ) ≤ m := by exact_mod_cast hge
    exact ⟨hgeZ, hle4Z⟩
  exact ⟨m, hmIcc, hm⟩

theorem innerProduct_ne_three_of_mem_minShell
    (hRootless : Rootless L) {u v : ℝ²⁴} (hu : u ∈ minShell L) (hv : v ∈ minShell L)
    (hne : u ≠ v) :
    ⟪u, v⟫ ≠ (3 : ℝ) := by
  have hsubL : u - v ∈ L := sub_mem hu.1 hv.1
  have hsub0 : u - v ≠ 0 := sub_ne_zero.mpr hne
  have hroot : ‖u - v‖ ^ 2 ≠ (2 : ℝ) := hRootless (u - v) hsubL hsub0
  intro hinner
  apply hroot
  have huSq : ‖u‖ ^ 2 = (4 : ℝ) := normSq_eq_four_of_mem_minShell (L := L) hu
  have hvSq : ‖v‖ ^ 2 = (4 : ℝ) := normSq_eq_four_of_mem_minShell (L := L) hv
  have hsub :
      ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * ⟪u, v⟫ + ‖v‖ ^ 2 := by
    simpa using! (norm_sub_sq_real u v)
  calc
    ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * ⟪u, v⟫ + ‖v‖ ^ 2 := hsub
    _ = (4 : ℝ) - 2 * (3 : ℝ) + (4 : ℝ) := by simp [huSq, hvSq, hinner]
    _ = (2 : ℝ) := by norm_num

theorem innerProduct_ne_neg_three_of_mem_minShell
    (hRootless : Rootless L) {u v : ℝ²⁴} (hu : u ∈ minShell L) (hv : v ∈ minShell L)
    (hne : u ≠ -v) :
    ⟪u, v⟫ ≠ (-3 : ℝ) := by
  have haddL : u + v ∈ L := add_mem hu.1 hv.1
  have hadd0 : u + v ≠ 0 := by
    intro h
    have : u = -v := eq_neg_of_add_eq_zero_left h
    exact hne this
  have hroot : ‖u + v‖ ^ 2 ≠ (2 : ℝ) := hRootless (u + v) haddL hadd0
  intro hinner
  apply hroot
  have huSq : ‖u‖ ^ 2 = (4 : ℝ) := normSq_eq_four_of_mem_minShell (L := L) hu
  have hvSq : ‖v‖ ^ 2 = (4 : ℝ) := normSq_eq_four_of_mem_minShell (L := L) hv
  have hadd :
      ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * ⟪u, v⟫ + ‖v‖ ^ 2 := by
    simpa using! (norm_add_sq_real u v)
  calc
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * ⟪u, v⟫ + ‖v‖ ^ 2 := hadd
    _ = (4 : ℝ) + 2 * (-3 : ℝ) + (4 : ℝ) := by simp [huSq, hvSq, hinner]
    _ = (2 : ℝ) := by norm_num

theorem abs_inner_le_two_of_mem_minShell_of_ne_of_ne_neg
    (hEven : EvenNormSq L) (hRootless : Rootless L) {u v : ℝ²⁴} (hu : u ∈ minShell L)
    (hv : v ∈ minShell L) (hne : u ≠ v) (hneNeg : u ≠ -v) :
    |⟪u, v⟫| ≤ (2 : ℝ) := by
  rcases innerProduct_mem_Icc_int_of_even_of_mem_minShell (L := L) hEven hu hv with ⟨m, hmIcc, hm⟩
  have hm3 : m ≠ (3 : ℤ) := by
    intro hm3
    have : (⟪u, v⟫ : ℝ) = (3 : ℝ) := by simpa [hm3] using! hm
    exact (innerProduct_ne_three_of_mem_minShell (L := L) hRootless hu hv hne) this
  have hmneg3 : m ≠ (-3 : ℤ) := by
    intro hmneg3
    have : (⟪u, v⟫ : ℝ) = (-3 : ℝ) := by
      simpa [hmneg3] using! hm
    exact (innerProduct_ne_neg_three_of_mem_minShell (L := L) hRootless hu hv hneNeg) this
  have hm4 : m ≠ (4 : ℤ) := by
    intro hm4
    have : (⟪u, v⟫ : ℝ) = (4 : ℝ) := by simpa [hm4] using! hm
    have huSq : ‖u‖ ^ 2 = (4 : ℝ) := normSq_eq_four_of_mem_minShell (L := L) hu
    have hvSq : ‖v‖ ^ 2 = (4 : ℝ) := normSq_eq_four_of_mem_minShell (L := L) hv
    have hsub :
        ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * ⟪u, v⟫ + ‖v‖ ^ 2 := by
      simpa using! (norm_sub_sq_real u v)
    have hnormsq : ‖u - v‖ ^ 2 = (0 : ℝ) := by
      -- `4 - 2*4 + 4 = 0`
      nlinarith [hsub, huSq, hvSq, this]
    have hnorm : ‖u - v‖ = 0 := by
      -- `a^2 = 0` implies `a = 0` in `ℝ`.
      have : (‖u - v‖) ^ 2 = (0 : ℝ) := by simpa using! hnormsq
      exact (sq_eq_zero_iff).1 this
    have : u - v = 0 := by simpa using! (norm_eq_zero.1 hnorm)
    exact hne (sub_eq_zero.mp this)
  have hmneg4 : m ≠ (-4 : ℤ) := by
    intro hmneg4
    have : (⟪u, v⟫ : ℝ) = (-4 : ℝ) := by
      simpa [hmneg4] using! hm
    have huSq : ‖u‖ ^ 2 = (4 : ℝ) := normSq_eq_four_of_mem_minShell (L := L) hu
    have hvSq : ‖v‖ ^ 2 = (4 : ℝ) := normSq_eq_four_of_mem_minShell (L := L) hv
    have hadd0 : u + v = 0 :=
      add_eq_zero_of_normSq_eq_four_of_inner_eq_neg_four (u := u) (v := v) huSq hvSq this
    exact hneNeg (eq_neg_of_add_eq_zero_left hadd0)
  have hmge : (-4 : ℤ) ≤ m := hmIcc.1
  have hmle : m ≤ (4 : ℤ) := hmIcc.2
  -- Now `m ∈ [-4,4] \ {±3,±4}`, so `|(m:ℝ)| ≤ 2`.
  have habs : |(m : ℝ)| ≤ (2 : ℝ) := by
    interval_cases m using hmge, hmle <;>
      first
        | exact False.elim (hmneg4 rfl)
        | exact False.elim (hmneg3 rfl)
        | exact False.elim (hm3 rfl)
        | exact False.elim (hm4 rfl)
        | norm_num
  simpa [hm] using! habs

end NiemeierRootless

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
