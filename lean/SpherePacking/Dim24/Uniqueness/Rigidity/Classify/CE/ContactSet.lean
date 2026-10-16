-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.CE.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Facts about the contact set

This file proves basic lemmas about the contact set `contactSet S x0` of a periodic packing:
it consists of the norm-`2` difference vectors around a center and is `2`-separated when
`S.separation = 2`.

These lemmas are intended as lightweight "glue" results: they just unfold definitions and use the
separation axiom, independent of the deeper CE Section 8 analysis.

## Main statements
* `Uniqueness.RigidityClassify.CE.contactSet_eq_norm2_vectors_of_centers_eq_translate`
* `Uniqueness.RigidityClassify.CE.contactSet_isKissingConfiguration_of_separation_eq_two`
-/

namespace SpherePacking.Dim24.Uniqueness.RigidityClassify.CE

noncomputable section

open scoped RealInnerProductSpace Pointwise
open Metric

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

theorem mem_contactSet_norm_eq_two {S : PeriodicSpherePacking 24} {x0 : S.centers} {v : ℝ²⁴}
    (hv : v ∈ contactSet S x0) : ‖v‖ = (2 : ℝ) := by
  rcases hv with ⟨_, _, _, hvNorm⟩
  exact hvNorm

/--
If the center set of `S` is a translate `x0 +ᵥ L'`, then `contactSet S x0` is exactly the set of
norm-`2` vectors in `L'`.
-/
public theorem contactSet_eq_norm2_vectors_of_centers_eq_translate
    (S : PeriodicSpherePacking 24)
    (L' : Submodule ℤ ℝ²⁴)
    (x0 : S.centers)
    (hCenters : (S.centers : Set ℝ²⁴) = (x0 : ℝ²⁴) +ᵥ (L' : Set ℝ²⁴)) :
    contactSet S x0 = {v : ℝ²⁴ | v ∈ (L' : Set ℝ²⁴) ∧ ‖v‖ = (2 : ℝ)} := by
  ext v
  constructor
  · rintro ⟨y, hyne, hyEq, hvNorm⟩
    have hy : (y : ℝ²⁴) ∈ (x0 : ℝ²⁴) +ᵥ (L' : Set ℝ²⁴) := by
      simpa [hCenters] using! y.property
    rcases hy with ⟨w, hw, hyw⟩
    have hwv : w = v := by
      have : (x0 : ℝ²⁴) + w - (x0 : ℝ²⁴) = v := by
        simpa [hyw.symm, vadd_eq_add] using! hyEq
      simpa [add_sub_cancel_left] using! this
    refine ⟨?_, hvNorm⟩
    simpa [hwv] using! hw
  · rintro ⟨hv, hvnorm⟩
    have hv0 : v ≠ 0 := by
      intro hv0
      subst hv0
      rw [norm_zero] at hvnorm
      have hne : (0 : ℝ) ≠ 2 := by norm_num
      exact hne hvnorm
    have hy : (x0 : ℝ²⁴) + v ∈ (S.centers : Set ℝ²⁴) := by
      have : (x0 : ℝ²⁴) +ᵥ v ∈ (x0 : ℝ²⁴) +ᵥ (L' : Set ℝ²⁴) := ⟨v, hv, rfl⟩
      simpa [hCenters, vadd_eq_add] using! this
    refine ⟨⟨(x0 : ℝ²⁴) + v, hy⟩, ?_, ?_, hvnorm⟩
    · intro hEq
      apply hv0
      have : (x0 : ℝ²⁴) + v = (x0 : ℝ²⁴) := congrArg Subtype.val hEq
      have : (x0 : ℝ²⁴) + v = (x0 : ℝ²⁴) + 0 := by simpa using! this
      exact add_left_cancel this
    · -- simplify `(x0 + v) - x0 = v`
      simp

theorem contactSet_pairwise_dist_ge_two_of_separation_eq_two
    (S : PeriodicSpherePacking 24) (hSep : S.separation = 2) (x0 : S.centers) :
    ∀ ⦃v w : ℝ²⁴⦄,
      v ∈ contactSet S x0 → w ∈ contactSet S x0 → v ≠ w →
        ‖v - w‖ ≥ (2 : ℝ) := by
  intro v w hv hw hvw
  rcases hv with ⟨y1, hy1ne, hy1Eq, _⟩
  rcases hw with ⟨y2, hy2ne, hy2Eq, _⟩
  -- Reduce to the separation bound between `y1` and `y2`.
  have hy12 : (y1 : ℝ²⁴) ≠ (y2 : ℝ²⁴) := by
    intro h
    apply hvw
    have : v = w := by
      calc
        v = (y1 : ℝ²⁴) - (x0 : ℝ²⁴) := hy1Eq.symm
        _ = (y2 : ℝ²⁴) - (x0 : ℝ²⁴) := by simp [h]
        _ = w := hy2Eq
    exact this
  have hdist : (2 : ℝ) ≤ dist (y1 : ℝ²⁴) (y2 : ℝ²⁴) := by
    -- Use the packing separation axiom (via `SpherePacking.centers_dist'`).
    simpa [hSep] using!
      S.toSpherePacking.centers_dist' (x := (y1 : ℝ²⁴)) (y := (y2 : ℝ²⁴))
        y1.property y2.property hy12
  have hdist' : (2 : ℝ) ≤ ‖(y1 : ℝ²⁴) - (y2 : ℝ²⁴)‖ := by
    simpa [dist_eq_norm] using! hdist
  have hvw' : v - w = (y1 : ℝ²⁴) - (y2 : ℝ²⁴) := by
    simp [hy1Eq.symm, hy2Eq.symm, sub_sub_sub_cancel_right]
  simpa [hvw'] using! hdist'

theorem finite_contactSet_of_separation_eq_two
    (S : PeriodicSpherePacking 24) (hSep : S.separation = 2) (x0 : S.centers) :
    (contactSet S x0).Finite := by
  -- All contact vectors lie in the closed ball of radius `2` around the origin.
  have hSub : contactSet S x0 ⊆ Metric.closedBall (0 : ℝ²⁴) (2 : ℝ) := by
    intro v hv
    have hv2 : ‖v‖ = (2 : ℝ) := mem_contactSet_norm_eq_two (hv := hv)
    -- `dist v 0 = ‖v‖`.
    simp_all
  -- Cover the compact closed ball by finitely many open balls of radius `1`.
  have hK : IsCompact (Metric.closedBall (0 : ℝ²⁴) (2 : ℝ)) := by
    simpa using! isCompact_closedBall (0 : ℝ²⁴) (2 : ℝ)
  rcases hK.finite_cover_balls (e := (1 : ℝ)) (by norm_num) with ⟨t, htSub, htFin, htCover⟩
  have hCov : contactSet S x0 ⊆ ⋃ x ∈ t, ball x (1 : ℝ) :=
    (hSub.trans (htCover))
  -- Choose, for each `v ∈ contactSet`, a covering center `x ∈ t` with `v ∈ ball x 1`.
  have hChoice :
      ∀ v : contactSet S x0, ∃ x, x ∈ t ∧ (v : ℝ²⁴) ∈ ball x (1 : ℝ) := by
    intro v
    have : (v : ℝ²⁴) ∈ ⋃ x ∈ t, ball x (1 : ℝ) := hCov v.property
    rcases Set.mem_iUnion.1 this with ⟨x, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨hxT, hxBall⟩
    exact ⟨x, hxT, hxBall⟩
  -- An `ε`-separated set meets each ball of radius `ε/2` in at most one point.
  refine Set.finite_coe_iff.mp ?_
  -- Put `t` in the codomain.
  have htFinite : (t : Set ℝ²⁴).Finite := htFin
  let f : contactSet S x0 → t :=
    fun v =>
      ⟨Classical.choose (hChoice v), (Classical.choose_spec (hChoice v)).1⟩
  have hf_inj : Function.Injective f := by
    intro v w hfw
    -- Both `v` and `w` lie in the same ball of radius `1` around `f v`.
    have hvBall : (v : ℝ²⁴) ∈ ball (f v : ℝ²⁴) (1 : ℝ) := by
      have := (Classical.choose_spec (hChoice v)).2
      simpa [f] using! this
    have hwBall : (w : ℝ²⁴) ∈ ball (f v : ℝ²⁴) (1 : ℝ) := by
      -- rewrite `f w = f v` and use the chosen witness for `w`
      have : (w : ℝ²⁴) ∈ ball (f w : ℝ²⁴) (1 : ℝ) := by
        have := (Classical.choose_spec (hChoice w)).2
        simpa [f] using! this
      simpa [hfw] using! this
    -- Hence `dist v w < 2`.
    have hv : dist (v : ℝ²⁴) (f v : ℝ²⁴) < (1 : ℝ) := by
      simpa [Metric.mem_ball] using! hvBall
    have hw : dist (w : ℝ²⁴) (f v : ℝ²⁴) < (1 : ℝ) := by
      simpa [Metric.mem_ball] using! hwBall
    have hvw_lt : dist (v : ℝ²⁴) (w : ℝ²⁴) < (2 : ℝ) := by
      have htri := dist_triangle (v : ℝ²⁴) (f v : ℝ²⁴) (w : ℝ²⁴)
      -- `dist (f v) w = dist w (f v)`
      have hw' : dist (f v : ℝ²⁴) (w : ℝ²⁴) < (1 : ℝ) := by simpa [dist_comm] using! hw
      have hlt : dist (v : ℝ²⁴) (w : ℝ²⁴) < (1 : ℝ) + 1 :=
        lt_of_le_of_lt htri (by nlinarith [hv, hw'])
      -- rewrite `1 + 1` as `2`
      nlinarith
    -- But `contactSet` is `2`-separated in norm.
    by_contra hvw
    have hvw' : (v : ℝ²⁴) ≠ (w : ℝ²⁴) := by
      intro h
      apply hvw
      exact Subtype.ext h
    have hge :
        ‖(v : ℝ²⁴) - (w : ℝ²⁴)‖ ≥ (2 : ℝ) :=
      contactSet_pairwise_dist_ge_two_of_separation_eq_two (S := S) hSep x0
        v.property w.property hvw'
    have : dist (v : ℝ²⁴) (w : ℝ²⁴) ≥ (2 : ℝ) := by
      simpa [dist_eq_norm] using! hge
    exact (not_lt_of_ge this) hvw_lt
  -- Conclude finiteness from an injection into a finite type.
  haveI : Finite t := htFinite.to_subtype
  exact Finite.of_injective f hf_inj

/-- If `S.separation = 2`, then `contactSet S x0` is a kissing configuration. -/
public theorem contactSet_isKissingConfiguration_of_separation_eq_two
    (S : PeriodicSpherePacking 24) (hSep : S.separation = 2) (x0 : S.centers) :
    IsKissingConfiguration (contactSet S x0) := by
  refine ⟨(finite_contactSet_of_separation_eq_two (S := S) hSep x0).to_subtype, ?_, ?_⟩
  · exact fun v hv => mem_contactSet_norm_eq_two (hv := hv)
  · exact fun v w hv hw hvw =>
      contactSet_pairwise_dist_ge_two_of_separation_eq_two (S := S) hSep x0 hv hw hvw

end
end SpherePacking.Dim24.Uniqueness.RigidityClassify.CE
