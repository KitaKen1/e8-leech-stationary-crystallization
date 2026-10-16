-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Package
public import SpherePacking.Dim24.Uniqueness.BS81.LatticeL
import SpherePacking.Dim24.Uniqueness.BS81.Thm13.LPBound
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma17.InnerProducts
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Applying BS81 Theorem 13 to the norm-4 shell

Let `L₄` be the set of vectors of squared norm `4` in `L = span_ℤ (2 • C)`.
Scaling by `1/2` yields a code on the unit sphere. Using Lemma 16 to exclude inner products `±3`,
we apply BS81 Theorem 13 to obtain the upper bound `|L₄| ≤ 196560`.

## Main definitions
* `normalizeShell4`

## Main statements
* `normalizeShell4_isSphericalCode`
* `ncard_latticeShell4_le_196560`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma17

noncomputable section

open scoped RealInnerProductSpace Pointwise

open Set

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- The normalized norm-`4` shell `L₄/2` as a subset of `ℝ²⁴`. -/
@[expose] public def normalizeShell4 (C : Set ℝ²⁴) : Set ℝ²⁴ :=
  (fun x : ℝ²⁴ => (1 / 2 : ℝ) • x) '' (latticeShell4 C)

lemma inner_eq_four_of_mem_latticeShell4_iff {C : Set ℝ²⁴} {u v : ℝ²⁴}
    (hu : u ∈ latticeShell4 C) (hv : v ∈ latticeShell4 C) :
    (⟪u, v⟫ : ℝ) = (4 : ℝ) ↔ u = v := by
  constructor
  · intro hinner
    have hsubsq : ‖u - v‖ ^ 2 = (0 : ℝ) := by
      have hcalc :
          ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * (⟪u, v⟫ : ℝ) + ‖v‖ ^ 2 := by
        simpa using! (norm_sub_sq_real u v)
      nlinarith [hcalc, hu.2, hv.2, hinner]
    have hsub : ‖u - v‖ = (0 : ℝ) := by
      have : ‖u - v‖ * ‖u - v‖ = (0 : ℝ) := by simpa [pow_two] using! hsubsq
      simpa using! (mul_self_eq_zero.mp this)
    exact sub_eq_zero.mp (norm_eq_zero.mp hsub)
  · intro huv
    cases huv
    calc
      (⟪u, u⟫ : ℝ) = ‖u‖ ^ 2 := by simp
      _ = (4 : ℝ) := hu.2

lemma dist_ge_one_of_norm_one_inner_le_half {x y : ℝ²⁴}
    (hx : ‖x‖ = (1 : ℝ)) (hy : ‖y‖ = (1 : ℝ)) (hxy : (⟪x, y⟫ : ℝ) ≤ (1 / 2 : ℝ)) :
    (1 : ℝ) ≤ dist x y := by
  have hsq : (1 : ℝ) ≤ ‖x - y‖ ^ 2 := by
    -- `‖x-y‖^2 = ‖x‖^2 - 2⟪x,y⟫ + ‖y‖^2 = 2 - 2⟪x,y⟫ ≥ 1`.
    have hsub : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * (⟪x, y⟫ : ℝ) + ‖y‖ ^ 2 := by
      simpa using! (norm_sub_sq_real x y)
    nlinarith [hsub, hx, hy, hxy]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (‖x - y‖ ^ 2) := (Real.one_le_sqrt).2 hsq
  -- `dist x y = ‖x-y‖` and `√(‖x-y‖^2) = ‖x-y‖`.
  simpa [dist_eq_norm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg (x - y))] using! hsqrt

lemma finite_of_totallyBounded_of_pairwise_dist_ge
    {X : Type*} [PseudoMetricSpace X] {K s : Set X} {ε : ℝ}
    (hε : 0 < ε) (hK : TotallyBounded K) (hsK : s ⊆ K)
    (hsep : s.Pairwise fun x y => ε ≤ dist x y) : s.Finite := by
  rcases (Metric.totallyBounded_iff.1 hK) (ε / 2) (by nlinarith) with ⟨t, htfin, hcover⟩
  have hcoverS : s ⊆ ⋃ y ∈ t, Metric.ball y (ε / 2) := by
    intro x hx
    exact hcover (hsK hx)
  have hex : ∀ x : s, ∃ y : X, y ∈ t ∧ (x : X) ∈ Metric.ball y (ε / 2) := by
    intro x
    have : (x : X) ∈ ⋃ y ∈ t, Metric.ball y (ε / 2) := hcoverS x.property
    rcases Set.mem_iUnion.1 this with ⟨y, hy⟩
    rcases Set.mem_iUnion.1 hy with ⟨hyt, hyb⟩
    exact ⟨y, hyt, hyb⟩
  choose f hfmem hfball using hex
  let g : s → t := fun x => ⟨f x, hfmem x⟩
  have hg_inj : Function.Injective g := by
    intro x1 x2 hg
    have hcent : f x1 = f x2 := congrArg Subtype.val hg
    by_contra hne
    have hne' : (x1 : X) ≠ (x2 : X) := by
      intro hEq
      apply hne
      ext
      exact hEq
    have hsep12 : ε ≤ dist (x1 : X) (x2 : X) := hsep x1.property x2.property hne'
    have hx1 : dist (x1 : X) (f x1) < ε / 2 := by
      simpa [Metric.mem_ball] using! hfball x1
    have hx2 : dist (x2 : X) (f x1) < ε / 2 := by
      have hx2' : dist (x2 : X) (f x2) < ε / 2 := by
        simpa [Metric.mem_ball] using! hfball x2
      simpa [hcent] using! hx2'
    have hlt : dist (x1 : X) (x2 : X) < ε := by
      have htri : dist (x1 : X) (x2 : X) ≤ dist (x1 : X) (f x1) + dist (f x1) (x2 : X) :=
        dist_triangle _ _ _
      have hsum : dist (x1 : X) (f x1) + dist (f x1) (x2 : X) < ε := by
        have : dist (x1 : X) (f x1) + dist (f x1) (x2 : X) < (ε / 2) + (ε / 2) := by
          have hx2'' : dist (f x1) (x2 : X) < ε / 2 := by simpa [dist_comm] using! hx2
          exact add_lt_add hx1 hx2''
        nlinarith
      exact lt_of_le_of_lt htri hsum
    exact (not_lt_of_ge hsep12) hlt
  haveI : Fintype t := htfin.fintype
  haveI : Fintype s := Fintype.ofInjective g hg_inj
  simpa using! (Set.toFinite s)

/-- The normalized shell `normalizeShell4 C` is a `(24, _, 1/2)` spherical code. -/
public theorem normalizeShell4_isSphericalCode
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C) :
    IsSphericalCode 24 (normalizeShell4 C) (1 / 2 : ℝ) := by
  -- First: norms and inner-product bound for the normalized shell.
  have hnorm : ∀ ⦃x⦄, x ∈ normalizeShell4 C → ‖x‖ = (1 : ℝ) := by
    intro x hx
    rcases hx with ⟨u, hu, rfl⟩
    have hu_norm : ‖u‖ = (2 : ℝ) := norm_eq_two_of_norm_sq_eq_four hu.2
    simp [norm_smul, hu_norm]
  have hinner_le : ∀ ⦃x y⦄, x ∈ normalizeShell4 C → y ∈ normalizeShell4 C → x ≠ y →
      (⟪x, y⟫ : ℝ) ≤ (1 / 2 : ℝ) := by
    intro x y hx hy hxy
    rcases hx with ⟨u, hu, rfl⟩
    rcases hy with ⟨v, hv, rfl⟩
    have huv : u ≠ v := by
      intro huv
      apply hxy
      simp [huv]
    have hinner_mem :
        (⟪u, v⟫ : ℝ) ∈ ({0, (1 : ℝ), (-1 : ℝ), (2 : ℝ), (-2 : ℝ), (4 : ℝ), (-4 : ℝ)} : Set ℝ) :=
      inner_mem_set_of_shell4 (C := C) h hu hv
    have hinner_le_two : (⟪u, v⟫ : ℝ) ≤ (2 : ℝ) := by
      have hcases :
          (⟪u, v⟫ : ℝ) = (0 : ℝ) ∨ (⟪u, v⟫ : ℝ) = (1 : ℝ) ∨ (⟪u, v⟫ : ℝ) = (-1 : ℝ) ∨
            (⟪u, v⟫ : ℝ) = (2 : ℝ) ∨ (⟪u, v⟫ : ℝ) = (-2 : ℝ) ∨ (⟪u, v⟫ : ℝ) = (4 : ℝ) ∨
              (⟪u, v⟫ : ℝ) = (-4 : ℝ) := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using! hinner_mem
      rcases hcases with h0 | h1 | hneg1 | h2 | hneg2 | h4 | hneg4 <;> try nlinarith
      exfalso
      exact huv ((inner_eq_four_of_mem_latticeShell4_iff (C := C) hu hv).1 h4)
    have hnonneg : (0 : ℝ) ≤ (1 / 4 : ℝ) := by norm_num
    have hm : (1 / 4 : ℝ) * (⟪u, v⟫ : ℝ) ≤ (1 / 4 : ℝ) * (2 : ℝ) :=
      mul_le_mul_of_nonneg_left hinner_le_two hnonneg
    calc
      (⟪(1 / 2 : ℝ) • u, (1 / 2 : ℝ) • v⟫ : ℝ) = (1 / 4 : ℝ) * (⟪u, v⟫ : ℝ) := by
        calc
          (⟪(1 / 2 : ℝ) • u, (1 / 2 : ℝ) • v⟫ : ℝ) =
              (1 / 2 : ℝ) * ((1 / 2 : ℝ) * (⟪u, v⟫ : ℝ)) := by
            simp [real_inner_smul_left, real_inner_smul_right]
          _ = (1 / 4 : ℝ) * (⟪u, v⟫ : ℝ) := by ring
      _ ≤ (1 / 4 : ℝ) * (2 : ℝ) := hm
      _ = (1 / 2 : ℝ) := by norm_num
  have hsep : (normalizeShell4 C).Pairwise fun x y => (1 : ℝ) ≤ dist x y := by
    intro x hx y hy hxy
    exact dist_ge_one_of_norm_one_inner_le_half (hnorm hx) (hnorm hy) (hinner_le hx hy hxy)
  have hsubset : normalizeShell4 C ⊆ Metric.closedBall (0 : ℝ²⁴) 1 := by
    intro x hx
    have hx_norm : ‖x‖ = (1 : ℝ) := hnorm hx
    -- `dist x 0 = ‖x‖ = 1`.
    have : dist x (0 : ℝ²⁴) ≤ (1 : ℝ) := by
      simp [dist_eq_norm, hx_norm]
    simpa [Metric.mem_closedBall] using! this
  have hK : TotallyBounded (Metric.closedBall (0 : ℝ²⁴) 1) :=
    (ProperSpace.isCompact_closedBall (α := ℝ²⁴) (0 : ℝ²⁴) 1).totallyBounded
  have hfinite : (normalizeShell4 C).Finite :=
    finite_of_totallyBounded_of_pairwise_dist_ge
      (X := ℝ²⁴) (K := Metric.closedBall (0 : ℝ²⁴) 1) (s := normalizeShell4 C) (ε := (1 : ℝ))
      (by norm_num) hK hsubset hsep
  exact ⟨hfinite, fun u hu => hnorm hu, fun u v hu hv huv => hinner_le hu hv huv⟩

/-- Cardinality bound `|L₄| ≤ 196560` for the norm-`4` shell in `L = span_ℤ (2 • C)`. -/
public theorem ncard_latticeShell4_le_196560
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C) :
    Set.ncard (latticeShell4 C) ≤ 196560 := by
  have hcode : IsSphericalCode 24 (normalizeShell4 C) (1 / 2 : ℝ) :=
    normalizeShell4_isSphericalCode (C := C) h
  have hbound : Set.ncard (normalizeShell4 C) ≤ 196560 :=
    Uniqueness.BS81.thm13_card_le_196560 (C := normalizeShell4 C) hcode
  have hinj : Function.Injective ((1 / 2 : ℝ) • · : ℝ²⁴ → ℝ²⁴) := by
    intro x y hxy
    have := congrArg (fun z : ℝ²⁴ => (2 : ℝ) • z) hxy
    simpa [smul_smul] using! this
  have hncard : Set.ncard (normalizeShell4 C) = Set.ncard (latticeShell4 C) := by
    simpa [normalizeShell4] using!
      (Set.ncard_image_of_injective (s := latticeShell4 C) (f := ((1 / 2 : ℝ) • ·)) hinj)
  simpa [hncard] using! hbound

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma17
