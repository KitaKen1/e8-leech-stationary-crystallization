-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module

public import SpherePacking.Basic.Domains.RightHalfPlane
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Domains for Laplace/Fourier continuation

This file defines the half-plane domains used in the analytic continuation arguments for the
Laplace and Fourier profiles. It also provides basic topological facts (openness and
preconnectedness) and a small "frequently equal" lemma used with the analytic identity theorem.

## Main definitions
* `domainTwo`
* `domainPosNeTwo`

## Main statements
* `domainTwo_isPreconnected`
* `domainPosNeTwo_isPreconnected`
* `frequently_eq_near_five`
-/

namespace SpherePacking.Dim24.LaplaceDomains

noncomputable section

open scoped Topology

open Complex
open SpherePacking

/-! ### Domains -/

/-- The half-plane `2 < Re u`. -/
@[expose] public def domainTwo : Set ℂ := {u : ℂ | 2 < u.re}

/-- `domainTwo` is an open subset of `ℂ`. -/
public lemma domainTwo_isOpen : IsOpen domainTwo := by
  simpa [domainTwo] using! isOpen_lt
    (continuous_const : Continuous fun _ : ℂ => (2 : ℝ)) Complex.continuous_re

/-- The right half-plane with the point `2` removed. -/
@[expose] public def domainPosNeTwo : Set ℂ := rightHalfPlane \ {2}

/-- `domainTwo` is preconnected (it is convex). -/
public lemma domainTwo_isPreconnected : IsPreconnected domainTwo := by
  -- `{u | 2 < Re u}` is convex, hence preconnected.
  have hconv : Convex ℝ domainTwo := by
    intro u hu v hv a b ha hb hab
    have hre : (a • u + b • v).re = a * u.re + b * v.re := by
      simp
    have hu' : 2 < u.re := hu
    have hv' : 2 < v.re := hv
    have h2 : 2 < a * u.re + b * v.re := by
      have hsum : a * 2 + b * 2 = 2 := by nlinarith [hab]
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by nlinarith [hab, ha0]
        simpa [ha0, hb1] using! hv'
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hmain : a * 2 + b * 2 < a * u.re + b * v.re := by
          have hstrict : a * 2 < a * u.re := by nlinarith [hu', ha_pos]
          have hweak : b * 2 ≤ b * v.re := by nlinarith [hv', hb]
          exact add_lt_add_of_lt_of_le hstrict hweak
        simpa [hsum] using! hmain
    simpa [domainTwo, hre] using! h2
  exact hconv.isPreconnected

/-- `domainPosNeTwo` is preconnected: removing one point from the open right half-plane does not
disconnect it. -/
public lemma domainPosNeTwo_isPreconnected : IsPreconnected domainPosNeTwo := by
  -- Build explicit joins to a base point.
  let base : ℂ := (1 : ℂ) + Complex.I
  have hbase : base ∈ domainPosNeTwo := by
    refine ⟨?_, ?_⟩
    · simp [rightHalfPlane, base]
    · intro hEq
      have : base.im = (2 : ℂ).im := congrArg Complex.im hEq
      simp [base] at this
  have hjoin_to_base : ∀ z ∈ domainPosNeTwo, JoinedIn domainPosNeTwo z base := by
    intro z hz
    have hzRe : 0 < z.re := by simpa [domainPosNeTwo, rightHalfPlane] using! hz.1
    have hzNe : z ≠ (2 : ℂ) := by simpa [domainPosNeTwo] using! hz.2
    -- If `z.re = 2` and `z.im < 0`, first shift right by `1` to avoid crossing `2` when moving up.
    let z0 : ℂ := if h : z.re = 2 ∧ z.im < 0 then z + 1 else z
    have hz0_mem : z0 ∈ domainPosNeTwo := by
      by_cases h : z.re = 2 ∧ z.im < 0
      · have hz0eq : z0 = z + 1 := by simp [z0, h]
        rw [hz0eq]
        refine ⟨?_, ?_⟩
        · have : 0 < z.re + 1 := add_pos_of_pos_of_nonneg hzRe (by positivity)
          simpa [domainPosNeTwo, rightHalfPlane] using! this
        · intro hEq
          have : (z + 1).im = (2 : ℂ).im := congrArg Complex.im hEq
          have : z.im = 0 := by simpa using! this
          exact (ne_of_lt h.2) this
      · simpa [z0, h] using! hz
    let z1 : ℂ := Complex.mk z0.re 1
    have hz1_mem : z1 ∈ domainPosNeTwo := by
      have hz0re : 0 < z0.re := by simpa [domainPosNeTwo, rightHalfPlane] using! hz0_mem.1
      refine ⟨hz0re, ?_⟩
      intro hEq
      have : z1.im = 0 := by simpa using! congrArg Complex.im hEq
      simp [z1] at this
    have hz_z0 : JoinedIn domainPosNeTwo z z0 := by
      by_cases h : z.re = 2 ∧ z.im < 0
      · have hz0eq : z0 = z + 1 := by simp [z0, h]
        rw [hz0eq]
        refine JoinedIn.of_segment_subset ?_
        intro w hw
        rw [segment_eq_image_lineMap] at hw
        rcases hw with ⟨t, ht, rfl⟩
        have ht0 : 0 ≤ t := ht.1
        have hw_re : 0 < (AffineMap.lineMap z (z + 1) t).re := by
          have hre : (AffineMap.lineMap z (z + 1) t).re = z.re + t := by
            simp [AffineMap.lineMap_apply, Complex.add_re, sub_eq_add_neg, add_left_comm, add_comm]
          have hpos : 0 < z.re + t := add_pos_of_pos_of_nonneg hzRe ht0
          simpa [hre] using! hpos
        have hw_im : (AffineMap.lineMap z (z + 1) t).im = z.im := by
          simp [AffineMap.lineMap_apply, Complex.add_im, sub_eq_add_neg, add_left_comm, add_comm]
        have hw_ne : AffineMap.lineMap z (z + 1) t ≠ (2 : ℂ) := by
          intro hEq
          have : (AffineMap.lineMap z (z + 1) t).im = (2 : ℂ).im := congrArg Complex.im hEq
          have : z.im = 0 := by simpa [hw_im] using! this
          exact (ne_of_lt h.2) this
        exact ⟨by simpa [domainPosNeTwo, rightHalfPlane] using! hw_re,
          by simpa [domainPosNeTwo] using! hw_ne⟩
      · simpa [z0, h] using! (JoinedIn.refl hz)
    have hz0_z1 : JoinedIn domainPosNeTwo z0 z1 := by
      refine JoinedIn.of_segment_subset ?_
      intro w hw
      rw [segment_eq_image_lineMap] at hw
      rcases hw with ⟨t, ht, rfl⟩
      have hz0re : 0 < z0.re := by simpa [domainPosNeTwo, rightHalfPlane] using! hz0_mem.1
      have hw_re : 0 < (AffineMap.lineMap z0 z1 t).re := by
        simpa [z1, AffineMap.lineMap_apply, Complex.add_re, Complex.smul_re] using! hz0re
      have hw_ne : AffineMap.lineMap z0 z1 t ≠ (2 : ℂ) := by
        intro hEq
        have hre : (AffineMap.lineMap z0 z1 t).re = (2 : ℂ).re := congrArg Complex.re hEq
        have hz0re2 : z0.re = 2 := by
          simpa [z1, AffineMap.lineMap_apply, Complex.add_re, Complex.smul_re] using! hre
        have hz0im_nonneg : 0 ≤ z0.im := by
          by_cases h : z.re = 2 ∧ z.im < 0
          · have hz0eq : z0 = z + 1 := by simp [z0, h]
            simp_all
          · have hz0eq : z0 = z := by simp [z0, h]
            have : ¬ z.im < 0 := by
              intro hzneg
              have hzre2 : z.re = 2 := by simpa [hz0eq] using! hz0re2
              exact h ⟨hzre2, hzneg⟩
            have : 0 ≤ z.im := le_of_not_gt this
            simpa [hz0eq] using! this
        have hw_im : (AffineMap.lineMap z0 z1 t).im = (1 - t) * z0.im + t := by
          simp [z1, AffineMap.lineMap_apply, sub_eq_add_neg]
          ring
        have ht0 : 0 ≤ t := ht.1
        have h1t0 : 0 ≤ 1 - t := by linarith [ht.2]
        have hw_im_pos : 0 < (AffineMap.lineMap z0 z1 t).im := by
          by_cases ht0' : t = 0
          · have hz0_ne2 : z0 ≠ (2 : ℂ) := by simpa [domainPosNeTwo] using! hz0_mem.2
            have hz0_im_ne : z0.im ≠ 0 := by
              intro hz0im0
              have hz0eq2 : z0 = (2 : ℂ) := by
                refine Complex.ext ?_ ?_
                · simp [hz0re2]
                · simp [hz0im0]
              exact hz0_ne2 hz0eq2
            have hz0_im_pos : 0 < z0.im := lt_of_le_of_ne hz0im_nonneg (Ne.symm hz0_im_ne)
            simpa [hw_im, ht0', AffineMap.lineMap_apply] using! hz0_im_pos
          · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht0')
            have : 0 ≤ (1 - t) * z0.im := mul_nonneg h1t0 hz0im_nonneg
            have : 0 < (1 - t) * z0.im + t := add_pos_of_nonneg_of_pos this htpos
            simpa [hw_im] using! this
        have : (AffineMap.lineMap z0 z1 t).im = (2 : ℂ).im := congrArg Complex.im hEq
        have : (AffineMap.lineMap z0 z1 t).im = 0 := by simpa using! this
        exact (ne_of_gt hw_im_pos) this
      exact ⟨by simpa [domainPosNeTwo, rightHalfPlane] using! hw_re,
        by simpa [domainPosNeTwo] using! hw_ne⟩
    have hz1_base : JoinedIn domainPosNeTwo z1 base := by
      refine JoinedIn.of_segment_subset ?_
      intro w hw
      rw [segment_eq_image_lineMap] at hw
      rcases hw with ⟨t, ht, rfl⟩
      have ht0 : 0 ≤ t := ht.1
      have hz1re : 0 < z1.re := by simpa [domainPosNeTwo, rightHalfPlane] using! hz1_mem.1
      have hbaseRe : 0 < base.re := by simp [base]
      have hw_re : 0 < (AffineMap.lineMap z1 base t).re := by
        by_cases ht0' : t = 0
        · simpa [AffineMap.lineMap_apply, ht0'] using! hz1re
        · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht0')
          have : 0 ≤ (1 - t) * z1.re := mul_nonneg (by linarith [ht.2]) hz1re.le
          have hpos : 0 < (1 - t) * z1.re + t * base.re :=
            add_pos_of_nonneg_of_pos this (mul_pos htpos hbaseRe)
          have hre :
              (AffineMap.lineMap z1 base t).re = (1 - t) * z1.re + t * base.re := by
            simp [AffineMap.lineMap_apply, sub_eq_add_neg]
            ring
          simpa [hre] using! hpos
      have hw_im : (AffineMap.lineMap z1 base t).im = 1 := by
        simp [AffineMap.lineMap_apply, z1, base, sub_eq_add_neg]
      have hw_ne : AffineMap.lineMap z1 base t ≠ (2 : ℂ) := by
        intro hEq
        have : (AffineMap.lineMap z1 base t).im = (2 : ℂ).im := congrArg Complex.im hEq
        simp [hw_im] at this
      exact ⟨by simpa [domainPosNeTwo, rightHalfPlane] using! hw_re,
        by simpa [domainPosNeTwo] using! hw_ne⟩
    exact hz_z0.trans (hz0_z1.trans hz1_base)
  have hpc : IsPathConnected domainPosNeTwo := by
    -- Path-connected: every point joins to `base`.
    refine (isPathConnected_iff.2 ?_)
    refine ⟨⟨base, hbase⟩, ?_⟩
    intro x hx y hy
    exact (hjoin_to_base x hx).trans (hjoin_to_base y hy).symm
  exact hpc.isConnected.isPreconnected

/-!
### Frequently equal packaging

To apply `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`, we need a neighborhood accumulation
point for the set where we know equality (real `u > 4` accumulating at `5`).
-/

/-- Package equality on the real ray `u > 4` as a `Frequently` equality in a punctured
neighborhood of `5`. -/
public lemma frequently_eq_near_five
    {f g : ℂ → ℂ} (hf : ∀ u : ℝ, 4 < u → f (u : ℂ) = g (u : ℂ)) :
    (∃ᶠ z in 𝓝[≠] (5 : ℂ), f z = g z) := by
  refine (Filter.frequently_iff.2 ?_)
  intro U hU
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hU with ⟨V, hVnhds, hVsub⟩
  rcases Metric.mem_nhds_iff.1 hVnhds with ⟨ε, hεpos, hball⟩
  let r : ℝ := 5 + ε / 2
  let z : ℂ := (r : ℂ)
  have hz_in_ball : z ∈ Metric.ball (5 : ℂ) ε := by
    have hdist : dist z (5 : ℂ) < ε := by
      have hdist_eq : dist z (5 : ℂ) = ‖(ε / 2 : ℝ)‖ := by
        rw [Complex.dist_eq]
        simp [z, r, norm_real, sub_eq_add_neg, add_assoc, add_comm]
      have hnorm_lt : ‖(ε / 2 : ℝ)‖ < ε := by
        simpa [Real.norm_eq_abs, abs_of_nonneg hεpos.le] using! (half_lt_self hεpos)
      simpa [hdist_eq] using! hnorm_lt
    simpa [Metric.mem_ball] using! hdist
  have hzV : z ∈ V := hball hz_in_ball
  have hz_ne : z ≠ (5 : ℂ) := by
    have hr_gt : (5 : ℝ) < r := by
      simpa [r] using! lt_add_of_pos_right (a := (5 : ℝ)) (half_pos hεpos)
    intro hEq
    have : r = (5 : ℝ) := by
      have : (z.re : ℝ) = (5 : ℂ).re := congrArg Complex.re hEq
      simpa [z] using! this
    exact (ne_of_gt hr_gt) this
  have hr4 : (4 : ℝ) < r := by
    have h5r : (5 : ℝ) < r := by
      simpa [r] using! lt_add_of_pos_right (a := (5 : ℝ)) (half_pos hεpos)
    exact lt_trans (by norm_num : (4 : ℝ) < 5) h5r
  have hfgz : f z = g z := by simpa [z] using! hf r hr4
  refine ⟨z, ?_, hfgz⟩
  refine hVsub ?_
  exact ⟨hzV, by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using! hz_ne⟩

end

end SpherePacking.Dim24.LaplaceDomains
