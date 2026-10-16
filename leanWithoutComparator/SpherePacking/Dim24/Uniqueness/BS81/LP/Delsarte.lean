-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp

/-!
# Delsarte linear programming bound in dimension 24

This file isolates the algebraic core of the Delsarte linear programming method for spherical
codes on `Ω₂₄`. A dual certificate is a polynomial `f` together with a constant `a0` giving a
uniform lower bound on `∑ u in C, ∑ v in C, f(⟪u,v⟫)` for every finite `C ⊆ Ω₂₄`. If in addition
`f.eval t ≤ 0` on `[-1, s]`, this yields the upper bound `|C| ≤ f.eval 1 / a0` for
`(24, |C|, s)` spherical codes.

The analytic input (not in this file) is constructing certificates via nonnegative
Gegenbauer/Jacobi expansions.

## Main definitions
* `IsDelsarteDual24`

## Main statements
* `delsarte_bound_sphere24_real`

## References
* BS81, §1 and §4
* CK06, §3-4
-/


namespace SpherePacking.Dim24.Uniqueness.BS81
noncomputable section

open scoped RealInnerProductSpace BigOperators

open Polynomial

/-- A Delsarte dual certificate for spherical codes on `Ω₂₄`.

This is the positivity half of the LP method: the kernel `K(u,v) = f(⟪u,v⟫)` dominates `a0`
through a uniform lower bound on the double sum over any finite subset of the unit sphere.

In classical proofs this follows from a nonnegative Gegenbauer (Jacobi) expansion.
-/
@[expose] public def IsDelsarteDual24 (f : Polynomial ℝ) (a0 : ℝ) : Prop :=
  ∀ (C : Finset (EuclideanSpace ℝ (Fin 24))),
    (∀ u ∈ C, ‖u‖ = (1 : ℝ)) →
      a0 * (C.card : ℝ) ^ 2 ≤
        C.sum (fun u => C.sum (fun v => f.eval (⟪u, v⟫ : ℝ)))

/-- Deduce the LP upper bound `|C| ≤ f.eval 1 / a0` from a dual certificate. -/
public theorem delsarte_bound_sphere24_real
    (C : Set (EuclideanSpace ℝ (Fin 24))) (s : ℝ)
    (f : Polynomial ℝ) (a0 : ℝ) :
    IsSphericalCode 24 C s →
      0 < a0 →
        (∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) s → f.eval t ≤ 0) →
          IsDelsarteDual24 f a0 →
            ((Set.ncard C : ℝ) ≤ f.eval 1 / a0) := by
  -- Proof sketch:
  -- 1) Apply the dual-certificate inequality to the finite code `C`.
  -- 2) Split the double sum into diagonal + off-diagonal terms.
  -- 3) Use the code property and `f ≤ 0` on `[-1,s]` to show off-diagonal terms are ≤ 0.
  -- 4) Conclude `a0 * |C|^2 ≤ |C| * f(1)` and divide by `a0`.
  intro hC ha0 hneg hdual
  let Cfin : Finset (EuclideanSpace ℝ (Fin 24)) := hC.finite.toFinset
  have hcard_nat : Set.ncard C = Cfin.card := by
    simpa [Cfin] using! (Set.ncard_eq_toFinset_card C hC.finite)
  have hcard : (Set.ncard C : ℝ) = (Cfin.card : ℝ) := by
    exact_mod_cast hcard_nat
  have hmemC : ∀ {u : EuclideanSpace ℝ (Fin 24)}, u ∈ Cfin → u ∈ C := by
    intro u hu
    -- Membership in the `toFinset` is membership in the set.
    simpa [Cfin] using! (hC.finite.mem_toFinset.1 hu)
  have hnorm : ∀ u ∈ Cfin, ‖u‖ = (1 : ℝ) := by
    intro u hu
    exact hC.norm_one (hmemC hu)
  have hdual' :
      a0 * (Cfin.card : ℝ) ^ 2 ≤
        Cfin.sum (fun u => Cfin.sum (fun v => f.eval (⟪u, v⟫ : ℝ))) := by
    refine hdual Cfin ?_
    exact hnorm
  have hsum_le :
      Cfin.sum (fun u => Cfin.sum (fun v => f.eval (⟪u, v⟫ : ℝ))) ≤
        (Cfin.card : ℝ) * f.eval 1 := by
    have hterm :
        ∀ u ∈ Cfin, Cfin.sum (fun v => f.eval (⟪u, v⟫ : ℝ)) ≤ f.eval 1 := by
      intro u hu
      have huC : u ∈ C := hmemC hu
      have hnormu : ‖u‖ = (1 : ℝ) := hnorm u hu
      have hsum_split :
          Cfin.sum (fun v => f.eval (⟪u, v⟫ : ℝ)) =
            f.eval (⟪u, u⟫ : ℝ) +
              (Cfin.erase u).sum (fun v => f.eval (⟪u, v⟫ : ℝ)) := by
        simpa using!
          (Finset.add_sum_erase (s := Cfin) (f := fun v => f.eval (⟪u, v⟫ : ℝ)) (a := u) hu).symm
      have hsum_erase_le :
          (Cfin.erase u).sum (fun v => f.eval (⟪u, v⟫ : ℝ)) ≤ 0 := by
        have hsum_le_zero :
            (Cfin.erase u).sum (fun v => f.eval (⟪u, v⟫ : ℝ)) ≤
              (Cfin.erase u).sum (fun _ => (0 : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro v hv
          have hv' : v ≠ u ∧ v ∈ Cfin := by
            simpa [Finset.mem_erase] using! hv
          have hvC : v ∈ C := hmemC hv'.2
          have hnormv : ‖v‖ = (1 : ℝ) := hnorm v hv'.2
          have hinner_ge : (-1 : ℝ) ≤ (⟪u, v⟫ : ℝ) :=
            neg_one_le_real_inner_of_norm_eq_one hnormu hnormv
          have hinner_le : (⟪u, v⟫ : ℝ) ≤ s :=
            hC.inner_le huC hvC (ne_comm.mp hv'.1)
          exact hneg _ ⟨hinner_ge, hinner_le⟩
        simpa using! hsum_le_zero
      calc
        Cfin.sum (fun v => f.eval (⟪u, v⟫ : ℝ)) =
            f.eval (⟪u, u⟫ : ℝ) +
              (Cfin.erase u).sum (fun v => f.eval (⟪u, v⟫ : ℝ)) := hsum_split
        _ ≤ f.eval (⟪u, u⟫ : ℝ) + 0 := by
          exact add_le_add_right hsum_erase_le _
        _ = f.eval 1 := by
          simp [hnormu]
    have hsum_le' :
        Cfin.sum (fun u => Cfin.sum (fun v => f.eval (⟪u, v⟫ : ℝ))) ≤
          Cfin.sum (fun _ => f.eval 1) :=
      Finset.sum_le_sum hterm
    simpa using! hsum_le'
  have hineq :
      a0 * (Cfin.card : ℝ) ^ 2 ≤ (Cfin.card : ℝ) * f.eval 1 := by
    exact le_trans hdual' hsum_le
  have hcard_le : (Cfin.card : ℝ) ≤ f.eval 1 / a0 := by
    -- First, show `0 ≤ f(1)` from the dual inequality applied to a 1-point code.
    -- (This is needed only to handle the degenerate `card = 0` case.)
    have hf1 : a0 ≤ f.eval 1 := by
      let u0 : EuclideanSpace ℝ (Fin 24) := EuclideanSpace.single (0 : Fin 24) (1 : ℝ)
      have hu0 : ‖u0‖ = (1 : ℝ) := by
        simp [u0]
      have hdual1 :
          a0 * (({u0} : Finset (EuclideanSpace ℝ (Fin 24))).card : ℝ) ^ 2 ≤
            ({u0} : Finset (EuclideanSpace ℝ (Fin 24))).sum
              (fun u => ({u0} : Finset (EuclideanSpace ℝ (Fin 24))).sum
                (fun v => f.eval (⟪u, v⟫ : ℝ))) := by
        refine hdual {u0} ?_
        intro u hu
        simp [Finset.mem_singleton.mp hu, hu0]
      -- Evaluate the double sum for a singleton.
      simpa [Finset.card_singleton, hu0, real_inner_self_eq_norm_sq, pow_two] using! hdual1
    have hf1_nonneg : 0 ≤ f.eval 1 := le_trans ha0.le hf1
    by_cases hcard0 : Cfin.card = 0
    · -- `C` is empty.
      have hcard0R : (Cfin.card : ℝ) = 0 := by
        exact_mod_cast hcard0
      -- RHS is nonnegative, so the inequality is trivial.
      have hRHS : (0 : ℝ) ≤ f.eval 1 / a0 := div_nonneg hf1_nonneg ha0.le
      simpa [hcard0R] using! hRHS
    · have hcardPos : 0 < (Cfin.card : ℝ) :=
        Nat.cast_pos.2 (Nat.pos_of_ne_zero hcard0)
      -- Divide `a0 * card^2 ≤ card * f(1)` by `card` and by `a0`.
      have hineq' : a0 * (Cfin.card : ℝ) ≤ f.eval 1 := by
        have hineq2 :
            (a0 * (Cfin.card : ℝ)) * (Cfin.card : ℝ) ≤ (f.eval 1) * (Cfin.card : ℝ) := by
          -- Reassociate and commute to expose a common right factor `card`.
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using! hineq
        exact le_of_mul_le_mul_right hineq2 hcardPos
      -- Now divide by `a0` (using `le_div_iff`).
      exact (le_div_iff₀' ha0).mpr hineq'
  simpa [hcard] using! hcard_le

/-!
## Equality-case helper lemmas
Step 2 (BS81 Theorem 14) needs slack-vanishing consequences of equality in the LP bound.
We state these separately from the (24,1/2) specialization.
-/
/-- If the LP bound is sharp and `f(t) < 0` strictly off the root set on `[-1,s]`, then every
off-diagonal inner product must be a root of `f`. -/
public lemma sharp_bound_forces_inner_in_rootSet
    (C : Set (EuclideanSpace ℝ (Fin 24))) (s : ℝ)
    (f : Polynomial ℝ) (a0 : ℝ)
    (hC : IsSphericalCode 24 C s)
    (ha0 : 0 < a0)
    (hneg : ∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) s → f.eval t ≤ 0)
    (hdual : IsDelsarteDual24 f a0)
    (hsharp : (Set.ncard C : ℝ) = f.eval 1 / a0) :
    ∀ ⦃u v : EuclideanSpace ℝ (Fin 24)⦄, u ∈ C → v ∈ C → u ≠ v → f.eval (⟪u, v⟫ : ℝ) = 0 := by
  -- Paper idea: in the proof of `delsarte_bound_sphere24_real`, every inequality is forced to be
  -- an equality when `|C| = f(1)/a0`. In particular, every off-diagonal term must contribute `0`.
  intro u v huC hvC huv
  -- Work with a finset version of `C`.
  let Cfin : Finset (EuclideanSpace ℝ (Fin 24)) := hC.finite.toFinset
  have hmemC : ∀ {x : EuclideanSpace ℝ (Fin 24)}, x ∈ Cfin → x ∈ C := by
    intro x hx
    simpa [Cfin] using! (hC.finite.mem_toFinset.1 hx)
  have hu : u ∈ Cfin := by simpa [Cfin] using! (hC.finite.mem_toFinset.2 huC)
  have hv : v ∈ Cfin := by simpa [Cfin] using! (hC.finite.mem_toFinset.2 hvC)
  have hnorm : ∀ x ∈ Cfin, ‖x‖ = (1 : ℝ) := by
    intro x hx
    exact hC.norm_one (hmemC hx)
  have hcard_nat : Set.ncard C = Cfin.card := by
    simpa [Cfin] using! (Set.ncard_eq_toFinset_card C hC.finite)
  have hcard : (Set.ncard C : ℝ) = (Cfin.card : ℝ) := by
    exact_mod_cast hcard_nat
  -- Let `S` be the full double sum.
  let S : ℝ := Cfin.sum (fun x => Cfin.sum (fun y => f.eval (⟪x, y⟫ : ℝ)))
  have hdual' : a0 * (Cfin.card : ℝ) ^ 2 ≤ S := by
    refine hdual Cfin ?_
    exact hnorm
  -- Row sums of the off-diagonal contributions are nonpositive.
  have hrow_nonpos :
      ∀ x ∈ Cfin, (Cfin.erase x).sum (fun y => f.eval (⟪x, y⟫ : ℝ)) ≤ 0 := by
    intro x hx
    have hxC : x ∈ C := hmemC hx
    have hnormx : ‖x‖ = (1 : ℝ) := hnorm x hx
    have hle :
        (Cfin.erase x).sum (fun y => f.eval (⟪x, y⟫ : ℝ)) ≤
          (Cfin.erase x).sum (fun _ => (0 : ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro y hy
      have hy' : y ∈ Cfin ∧ y ≠ x := by
        -- `Finset.mem_erase` returns the conjunction in the order `y ≠ x ∧ y ∈ Cfin`.
        refine ⟨(Finset.mem_erase.mp hy).2, (Finset.mem_erase.mp hy).1⟩
      have hyC : y ∈ C := hmemC hy'.1
      have hnormy : ‖y‖ = (1 : ℝ) := hnorm y hy'.1
      have hinner_ge : (-1 : ℝ) ≤ (⟪x, y⟫ : ℝ) :=
        neg_one_le_real_inner_of_norm_eq_one hnormx hnormy
      have hinner_le : (⟪x, y⟫ : ℝ) ≤ s :=
        hC.inner_le hxC hyC (ne_comm.mp hy'.2)
      exact hneg _ ⟨hinner_ge, hinner_le⟩
    simpa using! hle
  -- Express `S` as the diagonal contribution plus the sum of row off-diagonal sums.
  have hS_split :
      S =
        (Cfin.card : ℝ) * f.eval 1 +
          Cfin.sum (fun x => (Cfin.erase x).sum (fun y => f.eval (⟪x, y⟫ : ℝ))) := by
    -- First split each inner sum `∑_{y∈C} ...` into the `y=x` term plus `erase x`.
    have hinner_split :
        ∀ x ∈ Cfin,
          Cfin.sum (fun y => f.eval (⟪x, y⟫ : ℝ)) =
            f.eval 1 + (Cfin.erase x).sum (fun y => f.eval (⟪x, y⟫ : ℝ)) := by
      intro x hx
      have hxnorm : ‖x‖ = (1 : ℝ) := hnorm x hx
      -- `Finset.add_sum_erase` gives `f(x) + ∑_{y≠x} f(y) = ∑_{y} f(y)`.
      have hsum :
          f.eval (⟪x, x⟫ : ℝ) +
              (Cfin.erase x).sum (fun y => f.eval (⟪x, y⟫ : ℝ)) =
            Cfin.sum (fun y => f.eval (⟪x, y⟫ : ℝ)) := by
        simpa using!
          (Finset.add_sum_erase (s := Cfin) (f := fun y => f.eval (⟪x, y⟫ : ℝ)) (a := x) hx)
      -- Rearrange and rewrite `⟪x,x⟫ = 1`.
      have hsum' :
          Cfin.sum (fun y => f.eval (⟪x, y⟫ : ℝ)) =
            f.eval 1 + (Cfin.erase x).sum (fun y => f.eval (⟪x, y⟫ : ℝ)) := by
        have : Cfin.sum (fun y => f.eval (⟪x, y⟫ : ℝ)) =
            f.eval (‖x‖ ^ 2) + (Cfin.erase x).sum (fun y => f.eval (⟪x, y⟫ : ℝ)) := by
          simpa [add_comm, add_left_comm, add_assoc] using! hsum.symm
        simpa [hxnorm] using! this
      exact hsum'
    -- Sum the split identity over `x ∈ Cfin`.
    calc
      S =
          Cfin.sum (fun x =>
            (f.eval 1 : ℝ) + (Cfin.erase x).sum (fun y => f.eval (⟪x, y⟫ : ℝ))) :=
        Finset.sum_congr rfl hinner_split
      _ = Cfin.sum (fun _ => (f.eval 1 : ℝ)) +
            Cfin.sum (fun x => (Cfin.erase x).sum (fun y => f.eval (⟪x, y⟫ : ℝ))) := by
        simp [Finset.sum_add_distrib]
      _ = (Cfin.card : ℝ) * f.eval 1 +
            Cfin.sum (fun x => (Cfin.erase x).sum (fun y => f.eval (⟪x, y⟫ : ℝ))) := by
        simp [mul_comm]
  -- Upper bound: off-diagonal row sums are nonpositive.
  have hS_le :
      S ≤ (Cfin.card : ℝ) * f.eval 1 := by
    -- From the split expression, it suffices to show the off-diagonal contribution is ≤ 0.
    have hoff_nonpos :
        Cfin.sum (fun x => (Cfin.erase x).sum (fun y => f.eval (⟪x, y⟫ : ℝ))) ≤ 0 :=
      Finset.sum_nonpos hrow_nonpos
    -- Now read off the inequality.
    -- `S = card*f(1) + off`, so `S ≤ card*f(1)`.
    have : S ≤ (Cfin.card : ℝ) * f.eval 1 + 0 := by
      -- rewrite using `hS_split`
      -- and apply `add_le_add_left` to `hoff_nonpos`.
      have := add_le_add_left hoff_nonpos ((Cfin.card : ℝ) * f.eval 1)
      -- rewrite `+0`.
      simpa [hS_split] using! this
    simpa using! this
  -- The sharpness hypothesis gives equality of the lower and upper bounds, hence `S = card*f(1)`.
  have hsharp' : (Cfin.card : ℝ) = f.eval 1 / a0 := by
    simpa [hcard] using! hsharp
  have hcard_mul : a0 * (Cfin.card : ℝ) ^ 2 = (Cfin.card : ℝ) * f.eval 1 := by
    -- Multiply `card = f(1)/a0` by `a0` and then by `card`.
    have h1 : a0 * (Cfin.card : ℝ) = f.eval 1 := by
      -- `a0 * card = f.eval 1` from `card = f.eval 1 / a0`.
      -- Use `mul_div_cancel'` form.
      have : a0 * (f.eval 1 / a0) = f.eval 1 := by
        field_simp [ha0.ne']
      -- rewrite
      simpa [hsharp'] using! this
    -- Multiply by `card`.
    calc
      a0 * (Cfin.card : ℝ) ^ 2 = (a0 * (Cfin.card : ℝ)) * (Cfin.card : ℝ) := by
            simp [pow_two, mul_assoc]
      _ = f.eval 1 * (Cfin.card : ℝ) := by simp [h1]
      _ = (Cfin.card : ℝ) * f.eval 1 := by simp [mul_comm]
  have hS_eq : S = (Cfin.card : ℝ) * f.eval 1 := by
    -- `a0*card^2 ≤ S ≤ card*f(1)` and `a0*card^2 = card*f(1)`.
    apply le_antisymm
    · exact hS_le
    · -- lower bound rewritten using `hcard_mul`
      have : (Cfin.card : ℝ) * f.eval 1 ≤ S := by
        -- from dual bound `a0*card^2 ≤ S`
        have : a0 * (Cfin.card : ℝ) ^ 2 ≤ S := hdual'
        simpa [hcard_mul] using! this
      exact this
  -- From the split formula, the total off-diagonal contribution is `0`.
  have hoff_total :
      Cfin.sum (fun x => (Cfin.erase x).sum (fun y => f.eval (⟪x, y⟫ : ℝ))) = 0 := by
    -- `hS_split : S = card*f(1) + off`, `hS_eq : S = card*f(1)`.
    -- Compare the two right-hand sides via transitivity.
    have hcomp :
        (Cfin.card : ℝ) * f.eval 1 +
              Cfin.sum (fun x => (Cfin.erase x).sum (fun y => f.eval (⟪x, y⟫ : ℝ))) =
            (Cfin.card : ℝ) * f.eval 1 :=
      hS_split.symm.trans hS_eq
    -- Cancel the common term.
    exact left_eq_add.mp (id (Eq.symm hcomp))
  -- Each row off-diagonal sum is `0`.
  have hrow_eq_zero :
      ∀ x ∈ Cfin, (Cfin.erase x).sum (fun y => f.eval (⟪x, y⟫ : ℝ)) = 0 := by
    intro x hx
    have hnonpos :
        ∀ y ∈ Cfin, (Cfin.erase y).sum (fun z => f.eval (⟪y, z⟫ : ℝ)) ≤ 0 := by
      intro y hy
      exact hrow_nonpos y hy
    have hall :
        ∀ y ∈ Cfin, (Cfin.erase y).sum (fun z => f.eval (⟪y, z⟫ : ℝ)) = 0 := by
      -- `∑ row = 0` and each row ≤ 0.
      exact (Finset.sum_eq_zero_iff_of_nonpos hnonpos).1 hoff_total
    exact hall x hx
  -- Finally, each off-diagonal term is `0`.
  have hterm_nonpos :
      ∀ y ∈ (Cfin.erase u), f.eval (⟪u, y⟫ : ℝ) ≤ 0 := by
    intro y hy
    have hy' : y ∈ Cfin ∧ y ≠ u := by
      refine ⟨(Finset.mem_erase.mp hy).2, (Finset.mem_erase.mp hy).1⟩
    have huC : u ∈ C := hmemC hu
    have hyC : y ∈ C := hmemC hy'.1
    have hnormu : ‖u‖ = (1 : ℝ) := hnorm u hu
    have hnormy : ‖y‖ = (1 : ℝ) := hnorm y hy'.1
    have hinner_ge : (-1 : ℝ) ≤ (⟪u, y⟫ : ℝ) :=
      neg_one_le_real_inner_of_norm_eq_one hnormu hnormy
    have hinner_le : (⟪u, y⟫ : ℝ) ≤ s :=
      hC.inner_le huC hyC (ne_comm.mp hy'.2)
    exact hneg _ ⟨hinner_ge, hinner_le⟩
  -- Apply the pointwise lemma to the row sum at `u`.
  have hrowu : (Cfin.erase u).sum (fun y => f.eval (⟪u, y⟫ : ℝ)) = 0 := hrow_eq_zero u hu
  have hall_terms :
      ∀ y ∈ (Cfin.erase u), f.eval (⟪u, y⟫ : ℝ) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos hterm_nonpos).1 hrowu
  -- `v ∈ erase u` because `v ≠ u`.
  have hv_erase : v ∈ Cfin.erase u := by
    exact Finset.mem_erase.mpr ⟨Ne.symm huv, hv⟩
  exact hall_terms v hv_erase
end

end SpherePacking.Dim24.Uniqueness.BS81
