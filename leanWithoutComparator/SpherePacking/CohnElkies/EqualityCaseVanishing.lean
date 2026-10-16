-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import SpherePacking.CohnElkies.EqualityCaseCommute
import SpherePacking.CohnElkies.DualSubmoduleDiscrete
import SpherePacking.CohnElkies.LatticeSumBounds
public import SpherePacking.CohnElkies.LPBoundCalcLemmas
public import SpherePacking.CohnElkies.LPBoundReindex
public import SpherePacking.CohnElkies.LPBoundSummability

/-!
Equality case for the Cohn-Elkies LP bound (periodic packings).

This file provides the pointwise vanishing consequence used in the dimension-24 uniqueness
argument: under a tightness hypothesis, `(f (x - y)).re = 0` for every pair of distinct centers.
-/

open scoped FourierTransform ENNReal SchwartzMap BigOperators
open SpherePacking Metric Pointwise Filter MeasureTheory
open Complex Real ZSpan Bornology Summable Module

namespace SpherePacking.CohnElkies

variable {d : ℕ}
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)}

lemma term_eq_zero_of_tsum_eq_zero_of_nonpos {α : Type*} {g : α → ℝ}
    (hg_summable : Summable g) (hg_nonpos : ∀ a, g a ≤ 0) (a0 : α) (htsum : (∑' a, g a) = 0) :
    g a0 = 0 := by
  classical
  have htail : (∑' a : α, ite (a = a0) 0 (g a)) ≤ 0 := by
    refine tsum_nonpos fun a => ?_
    by_cases ha : a = a0 <;> simp [ha, hg_nonpos a]
  have hga0_ge : 0 ≤ g a0 := by
    have hga0 : g a0 = - (∑' a : α, ite (a = a0) 0 (g a)) := by
      refine eq_neg_of_add_eq_zero_left ?_
      simpa [hg_summable.tsum_eq_add_tsum_ite a0] using! htsum
    simpa [hga0] using! (neg_nonneg.mpr htail)
  exact le_antisymm (hg_nonpos a0) hga0_ge

section FundamentalDomain

variable {P : PeriodicSpherePacking d}
variable {D : Set (EuclideanSpace ℝ (Fin d))}

/-- Upper bound on the triple sum in the Cohn-Elkies argument. -/
lemma tripleSum_re_le_numReps'_mul_f0 (hP : P.separation = 1) (hD_isBounded : IsBounded D)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0) (hd : 0 < d) :
    (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
        (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re)
      ≤ (P.numReps' hd hD_isBounded : ℝ) * (f 0).re := by
  letI : Fintype ↑(P.centers ∩ D) := P.instFintypeNumReps' hd hD_isBounded
  simp_rw [tsum_fintype]
  have hmain :
      (∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D),
          ∑' ℓ : P.lattice,
            (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
              (ℓ : EuclideanSpace ℝ (Fin d)))).re)
        ≤
        ∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D), ite (x = y) (f 0).re 0 := by
    refine Finset.sum_le_sum ?_
    intro x hx
    refine Finset.sum_le_sum ?_
    exact fun i a => lattice_sum_re_le_ite hP hD_unique_covers hCohnElkies₁ x i
  refine hmain.trans ?_
  simp [PeriodicSpherePacking.numReps']

lemma summable_fourier_re_mul_norm_expSum_sq (hD_isBounded : IsBounded D) (hd : 0 < d) :
    Summable fun m : SchwartzMap.dualLattice (d := d) P.lattice =>
      ((𝓕 f) (m : EuclideanSpace ℝ (Fin d))).re * (norm (expSum P D m) ^ 2) := by
  have : Finite (↑(P.centers ∩ D)) := finite_centers_inter_of_isBounded P D hD_isBounded hd
  letI : Fintype (↑(P.centers ∩ D)) := Fintype.ofFinite (↑(P.centers ∩ D))
  let n : ℝ := (Fintype.card (↑(P.centers ∩ D)) : ℝ)
  have hn : 0 ≤ n := by simp [n]
  have hFourierNorm :
      Summable fun m : SchwartzMap.dualLattice (d := d) P.lattice =>
        ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖ := by
    simpa [zero_add] using!
      (SpherePacking.CohnElkies.LPBoundAux.summable_norm_comp_add_zlattice
        (Λ := SchwartzMap.dualLattice (d := d) P.lattice) (f := 𝓕 f)
        (a := (0 : EuclideanSpace ℝ (Fin d))))
  refine Summable.of_norm_bounded
    (g := fun m : SchwartzMap.dualLattice (d := d) P.lattice =>
      ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖ * (n ^ 2)) ?_ ?_
  · simpa [mul_assoc] using! hFourierNorm.mul_right (n ^ 2)
  · intro m
    have hA_le : ‖expSum P D m‖ ≤ n := by
      have hnexp (x : ↑(P.centers ∩ D)) :
          ‖Complex.exp (2 * π * Complex.I *
              ⟪(x : EuclideanSpace ℝ (Fin d)), (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])‖ = (1 : ℝ) :=
        by
          simpa [mul_assoc, mul_left_comm, mul_comm] using!
            (Complex.norm_exp_I_mul_ofReal (2 * π *
              ⟪(x : EuclideanSpace ℝ (Fin d)), (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))
      simpa [expSum, n, tsum_fintype, hnexp, Finset.sum_const_nat] using!
        (norm_sum_le (s := (Finset.univ : Finset ↑(P.centers ∩ D)))
          (f := fun x =>
            Complex.exp (2 * π * Complex.I *
              ⟪(x : EuclideanSpace ℝ (Fin d)), (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])))
    have hsq : ‖expSum P D m‖ ^ 2 ≤ n ^ 2 := by
      simpa [pow_two] using!
        (mul_le_mul hA_le hA_le (norm_nonneg _) hn)
    have hre :
        |((𝓕 f) (m : EuclideanSpace ℝ (Fin d))).re| ≤ ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖ := by
      simpa using! abs_re_le_norm ((𝓕 f) (m : EuclideanSpace ℝ (Fin d)))
    have hmul :
        ‖((𝓕 f) (m : EuclideanSpace ℝ (Fin d))).re * (norm (expSum P D m) ^ 2)‖ ≤
          ‖(𝓕 f) (m : EuclideanSpace ℝ (Fin d))‖ * (n ^ 2) := by
      -- `‖a*b‖ = |a| * |b|`, and `|b| = b` since it is a square.
      simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖expSum P D m‖)] using!
        (mul_le_mul hre hsq (sq_nonneg ‖expSum P D m‖) (norm_nonneg _))
    simpa [mul_assoc] using! hmul

lemma term0_le_tsum_fourier_re_mul_norm_expSum_sq (hD_isBounded : IsBounded D)
    (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0) (hd : 0 < d) :
    ((𝓕 f 0).re * (P.numReps' hd hD_isBounded : ℝ) ^ 2)
      ≤
      ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
        ((𝓕 f) (m : EuclideanSpace ℝ (Fin d))).re * (norm (expSum P D m) ^ 2) := by
  letI : DecidableEq (SchwartzMap.dualLattice (d := d) P.lattice) := Classical.decEq _
  let g : SchwartzMap.dualLattice (d := d) P.lattice → ℝ := fun m =>
    ((𝓕 f) (m : EuclideanSpace ℝ (Fin d))).re * (norm (expSum P D m) ^ 2)
  have hg_nonneg (m) : 0 ≤ g m := mul_nonneg (hCohnElkies₂ m) (sq_nonneg _)
  have hSummable : Summable g :=
    summable_fourier_re_mul_norm_expSum_sq (P := P) (D := D) (f := f)
      (hD_isBounded := hD_isBounded) hd
  have hge0 : g (0 : SchwartzMap.dualLattice (d := d) P.lattice) ≤ ∑' m, g m :=
    Summable.le_tsum hSummable 0 fun j a => hg_nonneg j
  have hnorm0 :
      norm (expSum P D (0 : SchwartzMap.dualLattice (d := d) P.lattice)) ^ 2 =
        (P.numReps' hd hD_isBounded : ℝ) ^ 2 := by
    simpa [expSum] using!
      (SpherePacking.CohnElkies.norm_tsum_exp_inner_zero_sq_eq_numReps_sq
        (P := P) (D := D) (hd := hd) (hD_isBounded := hD_isBounded))
  simpa [g, hnorm0] using! hge0

section Tightness

lemma tight_forces_tripleSum_re_eq_numReps'_mul_f0
    (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), (↑((𝓕 f x).re) : ℂ) = (𝓕 f x))
    (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
    (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)
    (hP : P.separation = 1)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hD_isBounded : IsBounded D) (hd : 0 < d)
    (hTight :
      (P.numReps' hd hD_isBounded : ℝ) * (f 0).re =
        (P.numReps' hd hD_isBounded : ℝ) ^ 2 * (𝓕 f 0).re /
          ZLattice.covolume P.lattice volume) :
    (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
        (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re)
      =
      (P.numReps' hd hD_isBounded : ℝ) * (f 0).re := by
  -- Set up names.
  set cov : ℝ := ZLattice.covolume P.lattice volume
  set N : ℝ := (P.numReps' hd hD_isBounded : ℝ)
  have hcov_pos : 0 < cov := by
    dsimp [cov]
    simpa using! (ZLattice.covolume_pos P.lattice volume)
  have hcov_ne : cov ≠ 0 := ne_of_gt hcov_pos
  -- Upper bound (part 1): triple sum ≤ diagonal.
  have hUpper :
      (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
          (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re)
        ≤ N * (f 0).re :=
    tripleSum_re_le_numReps'_mul_f0 hP hD_isBounded hD_unique_covers hCohnElkies₁ hd
  -- Identity: triple sum = (1/cov) * Fourier series.
  have hEq : (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
          (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re)
        = (1 / cov) *
          ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
            ((𝓕 f) (m : EuclideanSpace ℝ (Fin d))).re * (norm (expSum P D m) ^ 2) :=
    tripleSum_re_eq_one_div_covol_mul_tsum_fourier_re_mul_norm_expSum_sq
      hRealFourier hD_isBounded hd
  -- Lower bound (part 2): keep only the `m = 0` Fourier term.
  have hterm0_le :
      (𝓕 f 0).re * N ^ 2
        ≤
        ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
          ((𝓕 f) (m : EuclideanSpace ℝ (Fin d))).re * (norm (expSum P D m) ^ 2) :=
    term0_le_tsum_fourier_re_mul_norm_expSum_sq hD_isBounded hCohnElkies₂ hd
  have hLower :
      N * (f 0).re
        ≤
        (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
          (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re) := by
    -- Rewrite `N * f0` using the tightness hypothesis and the term0 lower bound.
    have hTight' : N * (f 0).re = N ^ 2 * (𝓕 f 0).re / cov := by
      simpa [N, cov] using! hTight
    -- Convert `N^2 * (𝓕 f 0).re / cov` to `(1/cov) * ((𝓕 f 0).re * N^2)`.
    have hcomm :
        (1 / cov) * ((𝓕 f 0).re * N ^ 2) = N ^ 2 * (𝓕 f 0).re / cov := by
      -- Commutative-monoid algebra.
      ring
    -- Now compare with the `m=0` lower bound and use `hEq` to go back to the triple sum.
    calc
      N * (f 0).re = N ^ 2 * (𝓕 f 0).re / cov := hTight'
      _ = (1 / cov) * ((𝓕 f 0).re * N ^ 2) := by
            simpa [hcomm] using! hcomm.symm
      _ ≤ (1 / cov) *
            ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
              ((𝓕 f) (m : EuclideanSpace ℝ (Fin d))).re * (norm (expSum P D m) ^ 2) := by
            -- multiply the term0 inequality by `1/cov` (nonnegative).
            have hcov_nonneg : 0 ≤ (1 / cov) :=
              one_div_nonneg.mpr (le_of_lt hcov_pos)
            exact mul_le_mul_of_nonneg_left hterm0_le hcov_nonneg
      _ = _ := by
            -- Use the identity `hEq` (symmetry).
            exact hEq.symm
  exact le_antisymm hUpper hLower

/-- **Fourier slack vanishing (pointwise)** in the Cohn-Elkies equality case: under tightness,
every nonzero dual-lattice frequency contributes zero to the Fourier-side nonnegative slack term.

Concretely, for `m ≠ 0` in the dual lattice, the nonnegative quantity
`((𝓕 f) m).re * ‖expSum(m)‖^2` must vanish. -/
public theorem tight_forces_fourier_re_mul_norm_expSum_sq_eq_zero_of_ne_zero
    (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), (↑((𝓕 f x).re) : ℂ) = (𝓕 f x))
    (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
    (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)
    (hP : P.separation = 1)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hD_isBounded : IsBounded D) (hd : 0 < d)
    (hTight :
      (P.numReps' hd hD_isBounded : ℝ) * (f 0).re =
        (P.numReps' hd hD_isBounded : ℝ) ^ 2 * (𝓕 f 0).re /
          ZLattice.covolume P.lattice volume) :
    ∀ m : SchwartzMap.dualLattice (d := d) P.lattice, m ≠ 0 →
      ((𝓕 f) (m : EuclideanSpace ℝ (Fin d))).re * (norm (expSum P D m) ^ 2) = 0 := by
  letI : DecidableEq (SchwartzMap.dualLattice (d := d) P.lattice) := Classical.decEq _
  -- Names.
  set cov : ℝ := ZLattice.covolume P.lattice volume
  set N : ℝ := (P.numReps' hd hD_isBounded : ℝ)
  have hcov_pos : 0 < cov := by
    dsimp [cov]
    simpa using! (ZLattice.covolume_pos P.lattice volume)
  have hcov_ne : cov ≠ 0 := ne_of_gt hcov_pos
  -- Define the nonnegative Fourier-side summand.
  let g : SchwartzMap.dualLattice (d := d) P.lattice → ℝ := fun m =>
    ((𝓕 f) (m : EuclideanSpace ℝ (Fin d))).re * (norm (expSum P D m) ^ 2)
  have hg_summable : Summable g := by
    exact summable_fourier_re_mul_norm_expSum_sq hD_isBounded hd
  have hg_nonneg : ∀ m, 0 ≤ g m := by
    intro m
    refine mul_nonneg ?_ (sq_nonneg _)
    -- `((𝓕 f) m).re ≥ 0`
    simpa using! (hCohnElkies₂ (m : EuclideanSpace ℝ (Fin d)))
  -- Tightness forces `∑ g = g 0`.
  have hTotal :
      (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
          (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re)
        =
        N * (f 0).re :=
    tight_forces_tripleSum_re_eq_numReps'_mul_f0 hRealFourier hCohnElkies₁ hCohnElkies₂ hP
      hD_unique_covers hD_isBounded hd hTight
  have hEq :
      (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
          (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re)
        =
        (1 / cov) * ∑' m, g m := by
    -- `EqualityCaseWork2` uses `ZLattice.covolume P.lattice volume` directly; rewrite to `cov`.
    exact tripleSum_re_eq_one_div_covol_mul_tsum_fourier_re_mul_norm_expSum_sq hRealFourier
      hD_isBounded hd
  have hTight' : N * (f 0).re = N ^ 2 * (𝓕 f 0).re / cov := by
    simpa [N, cov] using! hTight
  have hcomm :
      (1 / cov) * ((𝓕 f 0).re * N ^ 2) = N ^ 2 * (𝓕 f 0).re / cov := by
    ring
  have hsumg : (∑' m, g m) = ((𝓕 f 0).re * N ^ 2) := by
    -- Compare `hEq` with `hTotal` and cancel the nonzero factor `1/cov`.
    have hEq1 : (1 / cov) * (∑' m, g m) = N * (f 0).re := by
        calc
          (1 / cov) * (∑' m, g m)
              =
              (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
                  (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
                    (ℓ : EuclideanSpace ℝ (Fin d)))).re) :=
                hEq.symm
          _ = N * (f 0).re := hTotal
    have hEq2 : (1 / cov) * (∑' m, g m) = (1 / cov) * ((𝓕 f 0).re * N ^ 2) := by
      calc
        (1 / cov) * (∑' m, g m) = N * (f 0).re := hEq1
        _ = N ^ 2 * (𝓕 f 0).re / cov := hTight'
        _ = (1 / cov) * ((𝓕 f 0).re * N ^ 2) := by simpa [hcomm] using! hcomm.symm
    have hcov' : (1 / cov) ≠ 0 := one_div_ne_zero hcov_ne
    exact mul_left_cancel₀ hcov' hEq2
  -- Evaluate `g 0`.
  have hnorm0 :
      norm (expSum P D (0 : SchwartzMap.dualLattice (d := d) P.lattice)) ^ 2 = N ^ 2 := by
    simpa [N, expSum] using!
      (SpherePacking.CohnElkies.norm_tsum_exp_inner_zero_sq_eq_numReps_sq
        (P := P) (D := D) (hd := hd) (hD_isBounded := hD_isBounded))
  have hg0 : g 0 = ((𝓕 f 0).re * N ^ 2) := by
    simp [g, hnorm0]
  have htsum_tail :
      (∑' m : SchwartzMap.dualLattice (d := d) P.lattice, ite (m = 0) 0 (g m)) = 0 := by
    -- Split off the `m = 0` term in `tsum g` and use `tsum g = g 0`.
    have hsumg0 : (∑' m, g m) = g 0 := hsumg.trans hg0.symm
    have hsplit := hg_summable.tsum_eq_add_tsum_ite (0 : SchwartzMap.dualLattice (d := d) P.lattice)
    have hEq : g 0 + (∑' m, ite (m = 0) 0 (g m)) = g 0 := by
      simpa [hsplit] using! hsumg0
    exact by simpa using! congrArg (fun z : ℝ => z - g 0) hEq
  -- Now each nonzero term must be zero.
  intro m hm
  -- Apply the general "term is zero" lemma to `-tail`.
  let tail : SchwartzMap.dualLattice (d := d) P.lattice → ℝ :=
    fun m => ite (m = 0) 0 (g m)
  have htail_summable : Summable tail := by
    refine hg_summable.congr_cofinite ?_
    filter_upwards [show {m : SchwartzMap.dualLattice (d := d) P.lattice | m ≠ 0} ∈
        (Filter.cofinite : Filter (SchwartzMap.dualLattice (d := d) P.lattice)) by
        simp [Filter.mem_cofinite, Set.compl_setOf]] with m hm
    simp [tail, hm]
  have hneg_summable : Summable fun m => -tail m := htail_summable.neg
  have hneg_nonpos : ∀ m, (-tail m) ≤ 0 := by
    intro m
    have : 0 ≤ tail m := by
      by_cases hm0 : m = 0
      · simp [tail, hm0]
      · have : 0 ≤ g m := hg_nonneg m
        simp [tail, hm0, this]
    exact neg_nonpos.2 this
  have htsum_neg : (∑' m, -tail m) = 0 := by
    -- `tsum (-tail) = -tsum tail`.
    simpa [tsum_neg, htsum_tail]
  have htailm : tail m = 0 := by
    have hneg0 :
        (-tail m) = 0 :=
      term_eq_zero_of_tsum_eq_zero_of_nonpos (g := fun m => -tail m)
        hneg_summable hneg_nonpos m htsum_neg
    exact neg_eq_zero.1 hneg0
  have hm0 : m ≠ (0 : SchwartzMap.dualLattice (d := d) P.lattice) := hm
  have hgm : g m = 0 := by simpa [tail, hm0] using! htailm
  simpa [g] using! hgm

lemma tight_forces_pairwise_latticeSum_re_eq_ite
    (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), (↑((𝓕 f x).re) : ℂ) = (𝓕 f x))
    (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
    (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)
    (hP : P.separation = 1)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hD_isBounded : IsBounded D) (hd : 0 < d)
    (hTight :
      (P.numReps' hd hD_isBounded : ℝ) * (f 0).re =
        (P.numReps' hd hD_isBounded : ℝ) ^ 2 * (𝓕 f 0).re /
          ZLattice.covolume P.lattice volume) :
    ∀ x y : ↑(P.centers ∩ D),
      (∑' ℓ : P.lattice,
            (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
              (ℓ : EuclideanSpace ℝ (Fin d)))).re)
        =
        ite (x = y) (f 0).re 0 := by
  let X : Type := ↑(P.centers ∩ D)
  letI : Fintype X := P.instFintypeNumReps' hd hD_isBounded
  have hTotal :
      (∑' (x : X) (y : X) (ℓ : P.lattice),
          (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re)
        =
        (P.numReps' hd hD_isBounded : ℝ) * (f 0).re :=
    tight_forces_tripleSum_re_eq_numReps'_mul_f0 (P := P) (D := D) (f := f)
      (hRealFourier := hRealFourier) (hCohnElkies₁ := hCohnElkies₁) (hCohnElkies₂ := hCohnElkies₂)
      (hP := hP) (hD_unique_covers := hD_unique_covers) (hD_isBounded := hD_isBounded) (hd := hd)
      (hTight := hTight)
  -- Define the pointwise slack `δ(x,y) = ite - latticeSum`.
  let sxy : X → X → ℝ := fun x y =>
    ∑' ℓ : P.lattice,
      (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
        (ℓ : EuclideanSpace ℝ (Fin d)))).re
  let txy : X → X → ℝ := fun x y => ite (x = y) (f 0).re 0
  let δ : (X × X) → ℝ := fun p => txy p.1 p.2 - sxy p.1 p.2
  have hδ_nonneg : 0 ≤ δ := by
    intro p
    exact sub_nonneg.mpr (lattice_sum_re_le_ite (P := P) (D := D) (f := f)
      (hP := hP) (hD_unique_covers := hD_unique_covers) (hCohnElkies₁ := hCohnElkies₁) p.1 p.2)
  have hsum_txy :
      (∑ p : X × X, txy p.1 p.2) = (P.numReps' hd hD_isBounded : ℝ) * (f 0).re := by
    have hprod :
        (∑ p : X × X, txy p.1 p.2) = ∑ x : X, ∑ y : X, txy x y := by
      simpa using! (Fintype.sum_prod_type' (f := txy))
    have hinner : ∀ x : X, (∑ y : X, txy x y) = (f 0).re := by
      exact fun x => Fintype.sum_ite_eq x fun j => (f 0).re
    have houter :
        (∑ x : X, ∑ y : X, txy x y) = ∑ x : X, (f 0).re := by
      exact Fintype.sum_congr (fun a => ∑ y, txy a y) (fun a => (f 0).re) hinner
    calc
      (∑ p : X × X, txy p.1 p.2)
          = ∑ x : X, ∑ y : X, txy x y := hprod
      _ = ∑ x : X, (f 0).re := houter
      _ = (Fintype.card X : ℝ) * (f 0).re := by simp
      _ = (P.numReps' hd hD_isBounded : ℝ) * (f 0).re := by
            simp [PeriodicSpherePacking.numReps', X]
  have hsum_sxy :
      (∑ p : X × X, sxy p.1 p.2) =
        ∑' (x : X) (y : X) (ℓ : P.lattice),
          (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re := by
    simpa [sxy, tsum_fintype] using! (Fintype.sum_prod_type' (f := sxy))
  have hsum_δ : (∑ p : X × X, δ p) = 0 := by
    -- Use `δ = txy - sxy` and the equalities above.
    have hsub :
        (∑ p : X × X, δ p) = (∑ p : X × X, txy p.1 p.2) - (∑ p : X × X, sxy p.1 p.2) := by
      simp [δ, Finset.sum_sub_distrib]
    -- Convert the `sxy` sum to the triple `tsum`, then use `hTotal`.
    calc
      (∑ p : X × X, δ p)
          = (∑ p : X × X, txy p.1 p.2) - (∑ p : X × X, sxy p.1 p.2) := hsub
      _ = (P.numReps' hd hD_isBounded : ℝ) * (f 0).re -
            ∑' (x : X) (y : X) (ℓ : P.lattice),
              (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
                (ℓ : EuclideanSpace ℝ (Fin d)))).re := by
            rw [hsum_txy, hsum_sxy]
      _ = (P.numReps' hd hD_isBounded : ℝ) * (f 0).re -
            (P.numReps' hd hD_isBounded : ℝ) * (f 0).re := by
            rw [hTotal]
      _ = 0 := by simp
  have hδ_zero : δ = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg hδ_nonneg).1 hsum_δ
  intro x y
  have hδxy : δ (x, y) = 0 := by
    have := congrArg (fun g : X × X → ℝ => g (x, y)) hδ_zero
    simpa using! this
  -- `δ(x,y) = 0` means `txy x y = sxy x y`.
  have : txy x y = sxy x y := by
    have : txy x y - sxy x y = 0 := by simpa [δ, txy, sxy] using! hδxy
    exact sub_eq_zero.mp this
  simpa [txy, sxy] using! this.symm

lemma tight_forces_lattice_translate_re_eq_zero_of_ne
    (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), (↑((𝓕 f x).re) : ℂ) = (𝓕 f x))
    (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
    (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)
    (hP : P.separation = 1)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hD_isBounded : IsBounded D) (hd : 0 < d)
    (hTight :
      (P.numReps' hd hD_isBounded : ℝ) * (f 0).re =
        (P.numReps' hd hD_isBounded : ℝ) ^ 2 * (𝓕 f 0).re /
          ZLattice.covolume P.lattice volume) :
    ∀ x y : ↑(P.centers ∩ D),
      x ≠ y →
        ∀ ℓ : P.lattice,
          (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re = 0 := by
  have hpair :
      ∀ x y : ↑(P.centers ∩ D),
        (∑' ℓ : P.lattice,
              (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
                (ℓ : EuclideanSpace ℝ (Fin d)))).re) =
          ite (x = y) (f 0).re 0 :=
    tight_forces_pairwise_latticeSum_re_eq_ite (P := P) (D := D) (f := f)
      (hRealFourier := hRealFourier) (hCohnElkies₁ := hCohnElkies₁) (hCohnElkies₂ := hCohnElkies₂)
      (hP := hP) (hD_unique_covers := hD_unique_covers) (hD_isBounded := hD_isBounded) (hd := hd)
      (hTight := hTight)
  intro x y hxy ℓ0
  -- If `x,y ∈ D` and `x + ℓ = y`, then `ℓ = 0` by uniqueness of the cover of `y`.
  have hℓ_eq_zero_of_vadd_eq {x y : ↑(P.centers ∩ D)} {ℓ : P.lattice}
      (hxy :
        (x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)) =
          (y : EuclideanSpace ℝ (Fin d))) :
      ℓ = 0 := by
    obtain ⟨g0, hg0, hg0_unique⟩ := hD_unique_covers (y : EuclideanSpace ℝ (Fin d))
    have hy0 : (0 : P.lattice) +ᵥ (y : EuclideanSpace ℝ (Fin d)) ∈ D := by
      simpa [Submodule.vadd_def] using! y.property.2
    have hyℓ : (-ℓ : P.lattice) +ᵥ (y : EuclideanSpace ℝ (Fin d)) ∈ D := by
      have hEq :
          ((-ℓ : P.lattice) : EuclideanSpace ℝ (Fin d)) + (y : EuclideanSpace ℝ (Fin d)) =
            (x : EuclideanSpace ℝ (Fin d)) := by
        have hx : (x : EuclideanSpace ℝ (Fin d)) =
            (y : EuclideanSpace ℝ (Fin d)) - (ℓ : EuclideanSpace ℝ (Fin d)) :=
          eq_sub_of_add_eq hxy
        have hx' :
            (x : EuclideanSpace ℝ (Fin d)) =
              (y : EuclideanSpace ℝ (Fin d)) + (- (ℓ : EuclideanSpace ℝ (Fin d))) := by
          simpa [sub_eq_add_neg] using! hx
        calc
          ((-ℓ : P.lattice) : EuclideanSpace ℝ (Fin d)) + (y : EuclideanSpace ℝ (Fin d))
              =
              (y : EuclideanSpace ℝ (Fin d)) + ((-ℓ : P.lattice) : EuclideanSpace ℝ (Fin d)) := by
                simp [add_comm]
          _ = (x : EuclideanSpace ℝ (Fin d)) := by
                simpa using! hx'.symm
      simpa [Submodule.vadd_def, hEq.symm] using! x.property.2
    have hg0_zero : g0 = (0 : P.lattice) := (hg0_unique 0 hy0).symm
    have hℓ0 : (-ℓ : P.lattice) = g0 := hg0_unique (-ℓ) hyℓ
    have : (-ℓ : P.lattice) = 0 := by simpa [hg0_zero] using! hℓ0
    simpa using! neg_eq_zero.mp this
  have hg_summable :
      Summable fun ℓ : P.lattice =>
        (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using!
      (SpherePacking.CohnElkies.LPBoundSummability.summable_lattice_translate_re
        (Λ := P.lattice) (f := f)
        (a := (x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d))))
  have hg_nonpos :
      ∀ ℓ : P.lattice,
        (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re ≤ 0 := by
    intro ℓ
    have hx0 : (x : EuclideanSpace ℝ (Fin d)) ∈ P.centers := x.property.1
    have hy0 : (y : EuclideanSpace ℝ (Fin d)) ∈ P.centers := y.property.1
    have hxℓ : (ℓ : EuclideanSpace ℝ (Fin d)) + (x : EuclideanSpace ℝ (Fin d)) ∈ P.centers :=
      P.lattice_action ℓ.property hx0
    have hxℓ' :
        (x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)) ∈ P.centers := by
      simpa [add_comm] using! hxℓ
    have hneq :
        (x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)) ≠
          (y : EuclideanSpace ℝ (Fin d)) := by
      intro h
      have : ℓ = 0 := hℓ_eq_zero_of_vadd_eq (x := x) (y := y) (ℓ := ℓ) h
      subst this
      exact hxy (Subtype.ext (by simpa using! h))
    have hdist : P.separation ≤ dist
        ((x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)))
        (y : EuclideanSpace ℝ (Fin d)) :=
      P.centers_dist' _ _ hxℓ' hy0 hneq
    have hnorm : (1 : ℝ) ≤ ‖(x : EuclideanSpace ℝ (Fin d)) +
        (ℓ : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d))‖ := by
      simpa [hP, dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using! hdist
    have hle' :
        (f ((x : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re ≤ 0 := by
      apply hCohnElkies₁ ((x : EuclideanSpace ℝ (Fin d)) +
        (ℓ : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))
      simpa using! hnorm
    have hab :
        (x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)) =
          (x : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) := by
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    simpa [hab] using! hle'
  have htsum :
      (∑' ℓ : P.lattice,
            (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
              (ℓ : EuclideanSpace ℝ (Fin d)))).re) = 0 := by
    simpa [hxy] using! hpair x y
  exact
    term_eq_zero_of_tsum_eq_zero_of_nonpos (g := fun ℓ : P.lattice =>
        (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re)
      hg_summable hg_nonpos ℓ0 htsum

lemma tight_forces_lattice_re_eq_zero_of_ne_zero
    (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), (↑((𝓕 f x).re) : ℂ) = (𝓕 f x))
    (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
    (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)
    (hP : P.separation = 1)
    [Nonempty P.centers]
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hD_isBounded : IsBounded D) (hd : 0 < d)
    (hTight :
      (P.numReps' hd hD_isBounded : ℝ) * (f 0).re =
        (P.numReps' hd hD_isBounded : ℝ) ^ 2 * (𝓕 f 0).re /
          ZLattice.covolume P.lattice volume) :
    ∀ ℓ : P.lattice, ℓ ≠ 0 →
      (f ((ℓ : EuclideanSpace ℝ (Fin d)))).re = 0 := by
  -- Pick any center and move it into `D` to get a witness `x ∈ P.centers ∩ D`.
  obtain ⟨x0⟩ := (inferInstance : Nonempty P.centers)
  obtain ⟨g, hg, -⟩ := P.unique_covers_of_centers (D := D) hD_unique_covers x0
  let x : ↑(P.centers ∩ D) := ⟨(g +ᵥ (x0 : EuclideanSpace ℝ (Fin d))), hg⟩
  have hpair :
      ∀ x y : ↑(P.centers ∩ D),
        (∑' ℓ : P.lattice,
              (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
                (ℓ : EuclideanSpace ℝ (Fin d)))).re) =
          ite (x = y) (f 0).re 0 :=
    tight_forces_pairwise_latticeSum_re_eq_ite (P := P) (D := D) (f := f)
      (hRealFourier := hRealFourier) (hCohnElkies₁ := hCohnElkies₁) (hCohnElkies₂ := hCohnElkies₂)
      (hP := hP) (hD_unique_covers := hD_unique_covers) (hD_isBounded := hD_isBounded) (hd := hd)
      (hTight := hTight)
  intro ℓ0 hℓ0
  let g0 : P.lattice → ℝ := fun ℓ => (f (ℓ : EuclideanSpace ℝ (Fin d))).re
  let tail : P.lattice → ℝ := fun ℓ => ite (ℓ = (0 : P.lattice)) 0 (g0 ℓ)
  have hg0_summable : Summable g0 := by
    simpa [g0, zero_add] using!
      (SpherePacking.CohnElkies.LPBoundSummability.summable_lattice_translate_re
        (Λ := P.lattice) (f := f) (a := (0 : EuclideanSpace ℝ (Fin d))))
  have htail_summable : Summable tail := by
    -- `tail` agrees with `g0` away from `{0}`.
    refine hg0_summable.congr_cofinite ?_
    filter_upwards [show {ℓ : P.lattice | ℓ ≠ 0} ∈ (Filter.cofinite : Filter P.lattice) by
        simp [Filter.mem_cofinite, Set.compl_setOf]] with ℓ hℓ
    simp [tail, g0, hℓ]
  have htail_nonpos : ∀ ℓ : P.lattice, tail ℓ ≤ 0 := by
    intro ℓ
    by_cases hℓ : ℓ = 0
    · simp [tail, hℓ]
    · have hx0 : (x : EuclideanSpace ℝ (Fin d)) ∈ P.centers := x.property.1
      have hxℓ : (ℓ : EuclideanSpace ℝ (Fin d)) + (x : EuclideanSpace ℝ (Fin d)) ∈ P.centers :=
        P.lattice_action ℓ.property hx0
      have hxℓ' :
          (x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)) ∈ P.centers := by
        simpa [add_comm] using! hxℓ
      have hneq :
          (x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)) ≠
            (x : EuclideanSpace ℝ (Fin d)) := by
        intro h
        have : (ℓ : EuclideanSpace ℝ (Fin d)) = 0 :=
          left_eq_add.mp (id (Eq.symm h))
        have : ℓ = 0 := (Submodule.coe_eq_zero.mp this)
        exact hℓ this
      have hdist :
          P.separation ≤ dist
            ((x : EuclideanSpace ℝ (Fin d)) + (ℓ : EuclideanSpace ℝ (Fin d)))
            (x : EuclideanSpace ℝ (Fin d)) :=
        P.centers_dist' _ _ hxℓ' hx0 hneq
      have hnorm : (1 : ℝ) ≤ ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ := by
        have :
            (1 : ℝ) ≤
              ‖(x : EuclideanSpace ℝ (Fin d)) +
                  (ℓ : EuclideanSpace ℝ (Fin d)) -
                (x : EuclideanSpace ℝ (Fin d))‖ := by
          simpa [hP, dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using! hdist
        simpa [add_sub_cancel_left] using! this
      have hle : (f (ℓ : EuclideanSpace ℝ (Fin d))).re ≤ 0 := by
        apply hCohnElkies₁ (ℓ : EuclideanSpace ℝ (Fin d))
        simpa using! hnorm
      simp [tail, g0, hℓ, hle]
  have hsum0 : (∑' ℓ : P.lattice, g0 ℓ) = (f 0).re := by
    have := hpair x x
    -- `x - x + ℓ = ℓ`.
    simpa [g0, sub_self, zero_add] using! this
  have hsplit := hg0_summable.tsum_eq_add_tsum_ite (0 : P.lattice)
  have htail_tsum : (∑' ℓ : P.lattice, tail ℓ) = 0 := by
    have hsumg0 : (∑' ℓ : P.lattice, g0 ℓ) = g0 (0 : P.lattice) := by
      simpa [g0] using! hsum0
    have hEq : g0 0 + (∑' ℓ : P.lattice, tail ℓ) = g0 0 := by
      simpa [hsplit, tail] using! hsumg0
    exact by simpa using! congrArg (fun z : ℝ => z - g0 0) hEq
  have htail0 : tail ℓ0 = 0 :=
    term_eq_zero_of_tsum_eq_zero_of_nonpos (g := tail) htail_summable htail_nonpos ℓ0 htail_tsum
  have hℓ0' : ℓ0 ≠ (0 : P.lattice) := by simpa using! hℓ0
  -- For a nonzero lattice element, the tail term is the original term.
  simpa [tail, g0, hℓ0'] using! htail0

/-- Equality case for the Cohn-Elkies LP bound: tightness forces pointwise vanishing on
pairwise differences of distinct centers. -/
public theorem tight_forces_of_sub_re_eq_zero
    (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), (↑((𝓕 f x).re) : ℂ) = (𝓕 f x))
    (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
    (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)
    (hP : P.separation = 1) [Nonempty P.centers]
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hD_isBounded : IsBounded D) (hd : 0 < d)
    (hTight :
      (P.numReps' hd hD_isBounded : ℝ) * (f 0).re =
        (P.numReps' hd hD_isBounded : ℝ) ^ 2 * (𝓕 f 0).re /
          ZLattice.covolume P.lattice volume) :
    ∀ x y : P.centers,
      x ≠ y →
        (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))).re = 0 := by
  let e : (↑(P.centers ∩ D) × P.lattice) ≃ P.centers :=
    SpherePacking.CohnElkies.centersInterProdEquiv (P := P) (D := D) hD_unique_covers
  have hoff :
      ∀ x y : ↑(P.centers ∩ D),
        x ≠ y →
          ∀ ℓ : P.lattice,
            (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
              (ℓ : EuclideanSpace ℝ (Fin d)))).re = 0 :=
    tight_forces_lattice_translate_re_eq_zero_of_ne (P := P) (D := D) (f := f)
      (hRealFourier := hRealFourier) (hCohnElkies₁ := hCohnElkies₁) (hCohnElkies₂ := hCohnElkies₂)
      (hP := hP) (hD_unique_covers := hD_unique_covers) (hD_isBounded := hD_isBounded) (hd := hd)
      (hTight := hTight)
  have hdiag :
      ∀ ℓ : P.lattice, ℓ ≠ 0 → (f ((ℓ : EuclideanSpace ℝ (Fin d)))).re = 0 :=
    tight_forces_lattice_re_eq_zero_of_ne_zero (P := P) (D := D) (f := f)
      (hRealFourier := hRealFourier) (hCohnElkies₁ := hCohnElkies₁) (hCohnElkies₂ := hCohnElkies₂)
      (hP := hP) (hD_unique_covers := hD_unique_covers) (hD_isBounded := hD_isBounded) (hd := hd)
      (hTight := hTight)
  intro x y hxy
  -- Write `x` and `y` as lattice translates of representatives in `P.centers ∩ D`.
  set px : (↑(P.centers ∩ D) × P.lattice) := e.symm x
  set py : (↑(P.centers ∩ D) × P.lattice) := e.symm y
  have hx : e px = x := by simp [px]
  have hy : e py = y := by simp [py]
  -- Compute the difference `x - y` in terms of the representatives.
  have hsub :
      ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d))) =
        (px.1 : EuclideanSpace ℝ (Fin d)) - (py.1 : EuclideanSpace ℝ (Fin d)) +
          ((px.2 - py.2 : P.lattice) : EuclideanSpace ℝ (Fin d)) := by
    have he_val (p : ↑(P.centers ∩ D) × P.lattice) :
        (e p : EuclideanSpace ℝ (Fin d)) =
          (p.2 : EuclideanSpace ℝ (Fin d)) + (p.1 : EuclideanSpace ℝ (Fin d)) := by
      -- Unfolding `centersInterProdEquiv` at a single argument is fast enough; avoid global `simp`.
      simp [e, SpherePacking.CohnElkies.centersInterProdEquiv, Submodule.vadd_def, add_comm]
    have hxv :
        (x : EuclideanSpace ℝ (Fin d)) =
          (px.2 : EuclideanSpace ℝ (Fin d)) + (px.1 : EuclideanSpace ℝ (Fin d)) := by
      -- `x = e px` and `e px` is `px.2 +ᵥ px.1`.
      have : (x : EuclideanSpace ℝ (Fin d)) = (e px : EuclideanSpace ℝ (Fin d)) :=
        congrArg Subtype.val hx.symm
      simpa [he_val] using! this
    have hyv :
        (y : EuclideanSpace ℝ (Fin d)) =
          (py.2 : EuclideanSpace ℝ (Fin d)) + (py.1 : EuclideanSpace ℝ (Fin d)) := by
      have : (y : EuclideanSpace ℝ (Fin d)) = (e py : EuclideanSpace ℝ (Fin d)) :=
        congrArg Subtype.val hy.symm
      simpa [he_val] using! this
    -- Rearrange in the additive commutative group.
    -- `(ℓx + x0) - (ℓy + y0) = (x0 - y0) + (ℓx - ℓy)`.
    have hsub_lattice :
        ((px.2 - py.2 : P.lattice) : EuclideanSpace ℝ (Fin d)) =
          (px.2 : EuclideanSpace ℝ (Fin d)) - (py.2 : EuclideanSpace ℝ (Fin d)) := by
      simp
    calc
      (x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d))
          =
          ((px.2 : EuclideanSpace ℝ (Fin d)) + (px.1 : EuclideanSpace ℝ (Fin d))) -
            ((py.2 : EuclideanSpace ℝ (Fin d)) + (py.1 : EuclideanSpace ℝ (Fin d))) := by
            simp [hxv, hyv]
      _ = (px.2 : EuclideanSpace ℝ (Fin d)) - (py.2 : EuclideanSpace ℝ (Fin d)) +
            ((px.1 : EuclideanSpace ℝ (Fin d)) - (py.1 : EuclideanSpace ℝ (Fin d))) := by
            simpa using!
              (add_sub_add_comm (px.2 : EuclideanSpace ℝ (Fin d)) (px.1 : EuclideanSpace ℝ (Fin d))
                (py.2 : EuclideanSpace ℝ (Fin d)) (py.1 : EuclideanSpace ℝ (Fin d)))
      _ = (px.1 : EuclideanSpace ℝ (Fin d)) - (py.1 : EuclideanSpace ℝ (Fin d)) +
            ((px.2 : EuclideanSpace ℝ (Fin d)) - (py.2 : EuclideanSpace ℝ (Fin d))) :=
            add_comm ((px.2 : EuclideanSpace ℝ (Fin d)) - (py.2 : EuclideanSpace ℝ (Fin d)))
                ((px.1 : EuclideanSpace ℝ (Fin d)) - (py.1 : EuclideanSpace ℝ (Fin d)))
      _ = (px.1 : EuclideanSpace ℝ (Fin d)) - (py.1 : EuclideanSpace ℝ (Fin d)) +
            ((px.2 - py.2 : P.lattice) : EuclideanSpace ℝ (Fin d)) := by
            -- Rewrite the second addend using the coercion compatibility.
            rw [← hsub_lattice]
  by_cases hrep : px.1 = py.1
  · have hlne : px.2 ≠ py.2 := by
      intro hl
      apply hxy
      -- `e px = e py` by ext on the pair.
      have : px = py := Prod.ext hrep hl
      -- transport via `e`.
      have : e px = e py := congrArg e this
      simpa [hx, hy] using! this
    have hlne0 : (px.2 - py.2 : P.lattice) ≠ 0 := sub_ne_zero.mpr hlne
    -- In the equal-representative case, `x - y` is a nonzero lattice element.
    have : (f ((px.2 - py.2 : P.lattice) : EuclideanSpace ℝ (Fin d))).re = 0 :=
      hdiag (px.2 - py.2) hlne0
    -- Use `hsub` and `hrep` to reduce to the lattice case.
    have hsub' :
        ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d))) =
          ((px.2 - py.2 : P.lattice) : EuclideanSpace ℝ (Fin d)) := by
      have hrep' :
          (px.1 : EuclideanSpace ℝ (Fin d)) = (py.1 : EuclideanSpace ℝ (Fin d)) :=
        congrArg Subtype.val hrep
      calc
        (x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) =
            (px.1 : EuclideanSpace ℝ (Fin d)) - (py.1 : EuclideanSpace ℝ (Fin d)) +
              ((px.2 - py.2 : P.lattice) : EuclideanSpace ℝ (Fin d)) := hsub
        _ = 0 + ((px.2 - py.2 : P.lattice) : EuclideanSpace ℝ (Fin d)) := by
              simp [hrep']
        _ = ((px.2 - py.2 : P.lattice) : EuclideanSpace ℝ (Fin d)) := by simp
    -- Now rewrite the goal using `hsub'`.
    simpa [hsub'] using! this
  · have : (f ((px.1 : EuclideanSpace ℝ (Fin d)) - (py.1 : EuclideanSpace ℝ (Fin d)) +
        ((px.2 - py.2 : P.lattice) : EuclideanSpace ℝ (Fin d)))).re = 0 :=
      hoff px.1 py.1 hrep (px.2 - py.2)
    simpa [hsub] using! this

end SpherePacking.CohnElkies.FundamentalDomain.Tightness
