-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20.Base

import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma18.Count44
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Dn.Lemma18Count
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma17.InnerProducts
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20.StepMinVec
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


/-!
# Induction step for BS81 Lemma 20

Assume `ContainsDn C n` for `3 ≤ n ≤ 23`. This file constructs `ContainsDn C (n + 1)` by
appending a new orthonormal direction `eNew` and proving that all minimal vectors
`√2 (e i ± e j)` in the extended frame lie in the shell `latticeShell4 C`.

The key input is a shell vector `w` which is orthogonal to the old span. We obtain `w` by
combining the `44` common-neighbors count in the shell (Lemma 18(ii)) with the `2 * (n - 2)` count
in `Dₙ` (Lemma 18(iii)).

## Main definition
* `containsDn_succ_of_containsDn`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20

noncomputable section

open scoped RealInnerProductSpace
open Set

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)
lemma le_two_of_mem_shell4_innerSet {x : ℝ}
    (hx : x ∈ ({0, (1 : ℝ), (-1 : ℝ), (2 : ℝ), (-2 : ℝ), (4 : ℝ), (-4 : ℝ)} : Set ℝ))
    (hx4 : x ≠ (4 : ℝ)) :
    x ≤ (2 : ℝ) := by
  have hx' :
      x = 0 ∨ x = (1 : ℝ) ∨ x = (-1 : ℝ) ∨ x = (2 : ℝ) ∨ x = (-2 : ℝ) ∨
        x = (4 : ℝ) ∨ x = (-4 : ℝ) := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using! hx
  rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals (try norm_num)
  · cases hx4 rfl
lemma eq_of_inner_eq_four_of_norm_sq_eq_four {u v : ℝ²⁴}
    (hu : ‖u‖ ^ 2 = (4 : ℝ)) (hv : ‖v‖ ^ 2 = (4 : ℝ))
    (hinner : (⟪u, v⟫ : ℝ) = (4 : ℝ)) :
    u = v := by
  have hcalc :
      ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * (⟪u, v⟫ : ℝ) + ‖v‖ ^ 2 := by
    simpa using! (norm_sub_sq_real u v)
  have hnorm : ‖u - v‖ ^ 2 = (0 : ℝ) := by
    linarith [hcalc, hu, hv, hinner]
  have hmul : ‖u - v‖ * ‖u - v‖ = (0 : ℝ) := by
    simpa [pow_two] using! hnorm
  have hzero : ‖u - v‖ = (0 : ℝ) := by
    rcases mul_eq_zero.mp hmul with h | h <;> exact h
  have : u - v = 0 := by
    simpa using! (norm_eq_zero.mp hzero)
  exact sub_eq_zero.mp this

lemma inner_le_two_of_mem_shell4_of_ne
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C) {u v : ℝ²⁴}
    (hu : u ∈ latticeShell4 C) (hv : v ∈ latticeShell4 C) (huv : u ≠ v) :
    (⟪u, v⟫ : ℝ) ≤ (2 : ℝ) := by
  have hmem :
      (⟪u, v⟫ : ℝ) ∈
        ({0, (1 : ℝ), (-1 : ℝ), (2 : ℝ), (-2 : ℝ), (4 : ℝ), (-4 : ℝ)} : Set ℝ) :=
    Lemma17.inner_mem_set_of_shell4 C h hu hv
  have hne4 : (⟪u, v⟫ : ℝ) ≠ (4 : ℝ) := by
    intro h4
    exact huv (eq_of_inner_eq_four_of_norm_sq_eq_four hu.2 hv.2 h4)
  exact le_two_of_mem_shell4_innerSet hmem hne4

theorem exists_extension_vector
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (n : ℕ) (hn3 : 3 ≤ n) (hn23 : n ≤ 23)
    (hDn : ContainsDn C n) :
    ∃ w : ℝ²⁴,
      w ∈ latticeShell4 C ∧
      let g1 : ℝ²⁴ := Real.sqrt 2 • (hDn.e ⟨0, by
          -- `0 < n` from `3 ≤ n`.
          exact lt_of_lt_of_le (by decide : 0 < 3) hn3⟩ + hDn.e ⟨1,
            lt_of_lt_of_le (by decide : 1 < 3) hn3⟩)
      let g2 : ℝ²⁴ := Real.sqrt 2 • (hDn.e ⟨0,
          lt_of_lt_of_le (by decide : 0 < 3) hn3⟩ - hDn.e ⟨1,
            lt_of_lt_of_le (by decide : 1 < 3) hn3⟩)
      (⟪g1, w⟫ : ℝ) = 2 ∧ (⟪g2, w⟫ : ℝ) = 2 ∧
        w ∉ (Submodule.span ℝ (Set.range hDn.e) : Submodule ℝ ℝ²⁴) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn3
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 3) hn3
  have hn2 : 2 ≤ n := le_trans (by decide : 2 ≤ 3) hn3
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := by
    have : (0 : ℝ) < (2 : ℝ) := by norm_num
    exact Real.sqrt_pos.2 this
  have hsqrt2_ne : (Real.sqrt 2 : ℝ) ≠ 0 := (ne_of_gt hsqrt2_pos)
  let i0 : Fin n := ⟨0, hn0⟩
  let i1 : Fin n := ⟨1, hn1⟩
  have hi01 : (i0 : Fin n) ≠ i1 := by
    intro hEq
    have : (0 : ℕ) = 1 := by
      simpa [i0, i1] using! congrArg Fin.val hEq
    exact Nat.zero_ne_one this
  let g1 : ℝ²⁴ := Real.sqrt 2 • (hDn.e i0 + hDn.e i1)
  let g2 : ℝ²⁴ := Real.sqrt 2 • (hDn.e i0 - hDn.e i1)
  have hg1Shell : g1 ∈ latticeShell4 C := by
    have hmem := hDn.minVec_mem i0 i1 hi01
    simpa [g1] using! hmem.1
  have hg2Shell : g2 ∈ latticeShell4 C := by
    have hmem := hDn.minVec_mem i0 i1 hi01
    simpa [g2] using! hmem.2
  have hinner_g1g2 : (⟪g1, g2⟫ : ℝ) = 0 := by
    have hite :
        ∀ i j : Fin n, (⟪hDn.e i, hDn.e j⟫ : ℝ) =
          if i = j then (1 : ℝ) else (0 : ℝ) :=
      (orthonormal_iff_ite).1 hDn.ortho
    have he00 : (⟪hDn.e i0, hDn.e i0⟫ : ℝ) = 1 := by simpa using! (hite i0 i0)
    have he11 : (⟪hDn.e i1, hDn.e i1⟫ : ℝ) = 1 := by simpa using! (hite i1 i1)
    have he01 : (⟪hDn.e i0, hDn.e i1⟫ : ℝ) = 0 := by simpa [hi01] using! (hite i0 i1)
    have he10 : (⟪hDn.e i1, hDn.e i0⟫ : ℝ) = 0 := by
      simpa [real_inner_comm] using! he01
    have hbase : (⟪hDn.e i0 + hDn.e i1, hDn.e i0 - hDn.e i1⟫ : ℝ) = 0 := by
      calc
        (⟪hDn.e i0 + hDn.e i1, hDn.e i0 - hDn.e i1⟫ : ℝ)
            = (⟪hDn.e i0, hDn.e i0 - hDn.e i1⟫ : ℝ) +
                (⟪hDn.e i1, hDn.e i0 - hDn.e i1⟫ : ℝ) := by
                  simp [inner_add_left]
        _ = ((⟪hDn.e i0, hDn.e i0⟫ : ℝ) - (⟪hDn.e i0, hDn.e i1⟫ : ℝ)) +
              ((⟪hDn.e i1, hDn.e i0⟫ : ℝ) - (⟪hDn.e i1, hDn.e i1⟫ : ℝ)) := by
                simp [inner_sub_right]
        _ = (1 : ℝ) - 0 + (0 - (1 : ℝ)) := by
              rw [he00, he01, he10, he11]
        _ = 0 := by ring
    calc
      (⟪g1, g2⟫ : ℝ) =
          (Real.sqrt 2 : ℝ) * (⟪hDn.e i0 + hDn.e i1, g2⟫ : ℝ) := by
            -- Avoid `simp` expanding `smul_add` inside `g1`.
            simpa [g1] using!
              (real_inner_smul_left (hDn.e i0 + hDn.e i1) g2 (Real.sqrt 2 : ℝ))
      _ =
          (Real.sqrt 2 : ℝ) *
            ((Real.sqrt 2 : ℝ) * (⟪hDn.e i0 + hDn.e i1, hDn.e i0 - hDn.e i1⟫ : ℝ)) := by
            -- Avoid `simp` expanding `smul_sub` inside `g2`.
            have hinner' :
                (⟪hDn.e i0 + hDn.e i1, g2⟫ : ℝ) =
                  (Real.sqrt 2 : ℝ) *
                    (⟪hDn.e i0 + hDn.e i1, hDn.e i0 - hDn.e i1⟫ : ℝ) := by
              exact real_inner_smul_right (hDn.e i0 + hDn.e i1) (hDn.e i0 - hDn.e i1) √2
            simp [hinner']
      _ = (Real.sqrt 2 : ℝ) * ((Real.sqrt 2 : ℝ) * 0) := by simp [hbase]
      _ = 0 := by ring
  -- The 44 common neighbors in the shell (Lemma 18(ii)).
  let S : Set ℝ²⁴ :=
    {w : ℝ²⁴ | w ∈ latticeShell4 C ∧ (⟪g1, w⟫ : ℝ) = 2 ∧ (⟪g2, w⟫ : ℝ) = 2}
  have hS : S.ncard = 44 :=
    Lemma18.commonNeighbors44_in_shell4 C h hg1Shell hg2Shell hinner_g1g2
  -- Parameterize the `2(n-2)` minimal vectors `√2(e₀ ± e_k)` for `k = 2,3,...,n-1`.
  let shift : Fin (n - 2) → Fin n := fun k =>
    ⟨k.1 + 2, by
      have hk : k.1 + 2 < (n - 2) + 2 := Nat.add_lt_add_right k.2 2
      simpa [Nat.sub_add_cancel hn2] using! hk⟩
  let signR : Bool → ℝ := fun b => if b then (1 : ℝ) else (-1 : ℝ)
  let vec : (Fin (n - 2) × Bool) → ℝ²⁴ := fun x =>
    Real.sqrt 2 • (hDn.e i0 + signR x.2 • hDn.e (shift x.1))
  let T : Set ℝ²⁴ := Set.range vec
  have hTle : T.ncard ≤ (n - 2) * 2 := by
    -- `ncard (range vec) ≤ card (Fin (n-2) × Bool) = (n-2)*2`.
    have hle' :
        (Set.range vec).ncard ≤ (Set.univ : Set (Fin (n - 2) × Bool)).ncard := by
      simpa [Set.image_univ] using!
        (Set.ncard_image_le (f := vec) (s := (Set.univ : Set (Fin (n - 2) × Bool))))
    calc
      T.ncard = (Set.range vec).ncard := by rfl
      _ ≤ (Set.univ : Set (Fin (n - 2) × Bool)).ncard := hle'
      _ = (n - 2) * 2 := by
        simp [Set.ncard_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm]
  have hTlt : T.ncard < S.ncard := by
    have hnsub : n - 2 ≤ 21 := by
      -- `n ≤ 23` ⇒ `n-2 ≤ 21`.
      have := Nat.sub_le_sub_right hn23 2
      simpa using! this
    have h1 : (n - 2) * 2 ≤ 21 * 2 := Nat.mul_le_mul_right 2 hnsub
    have h2 : 21 * 2 < 44 := by decide
    have h3 : T.ncard < 44 := lt_of_le_of_lt (hTle.trans h1) h2
    simpa [hS] using! h3
  have hTfinite : T.Finite := by
    -- a range of a function from a finite type is finite
    simpa [T] using! (Set.finite_range vec)
  rcases Set.exists_mem_notMem_of_ncard_lt_ncard (s := T) (t := S) hTlt (hs := hTfinite) with
    ⟨w, hwS, hwT⟩
  have hwShell : w ∈ latticeShell4 C := hwS.1
  have hwg1 : (⟪g1, w⟫ : ℝ) = 2 := hwS.2.1
  have hwg2 : (⟪g2, w⟫ : ℝ) = 2 := hwS.2.2
  -- Extract the coordinates of `w` along `e₀,e₁` from the equations `⟪g₁,w⟫=⟪g₂,w⟫=2`.
  have hg1_form :
      (⟪g1, w⟫ : ℝ) =
        (Real.sqrt 2 : ℝ) * ((⟪hDn.e i0, w⟫ : ℝ) + (⟪hDn.e i1, w⟫ : ℝ)) := by
    simp [g1, real_inner_smul_left, inner_add_left, mul_add]
  have hg2_form :
      (⟪g2, w⟫ : ℝ) =
        (Real.sqrt 2 : ℝ) * ((⟪hDn.e i0, w⟫ : ℝ) - (⟪hDn.e i1, w⟫ : ℝ)) := by
    simp [g2, real_inner_smul_left, inner_sub_left, mul_sub]
  have htwo_div_sqrt2 : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 :=
    Real.div_sqrt
  have hsum : (⟪hDn.e i0, w⟫ : ℝ) + (⟪hDn.e i1, w⟫ : ℝ) = Real.sqrt 2 := by
    have : (Real.sqrt 2 : ℝ) * ((⟪hDn.e i0, w⟫ : ℝ) + (⟪hDn.e i1, w⟫ : ℝ)) = 2 := by
      simpa [hg1_form] using! hwg1
    -- divide by `√2`
    have : (⟪hDn.e i0, w⟫ : ℝ) + (⟪hDn.e i1, w⟫ : ℝ) = (2 : ℝ) / Real.sqrt 2 := by
      refine (eq_div_iff hsqrt2_ne).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using! this
    simpa [htwo_div_sqrt2] using! this
  have hdiff : (⟪hDn.e i0, w⟫ : ℝ) - (⟪hDn.e i1, w⟫ : ℝ) = Real.sqrt 2 := by
    have : (Real.sqrt 2 : ℝ) * ((⟪hDn.e i0, w⟫ : ℝ) - (⟪hDn.e i1, w⟫ : ℝ)) = 2 := by
      simpa [hg2_form] using! hwg2
    have : (⟪hDn.e i0, w⟫ : ℝ) - (⟪hDn.e i1, w⟫ : ℝ) = (2 : ℝ) / Real.sqrt 2 := by
      refine (eq_div_iff hsqrt2_ne).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using! this
    simpa [htwo_div_sqrt2] using! this
  have hw0 : (⟪hDn.e i0, w⟫ : ℝ) = Real.sqrt 2 := by linarith [hsum, hdiff]
  have hw1 : (⟪hDn.e i1, w⟫ : ℝ) = 0 := by linarith [hsum, hdiff]
  -- If `w` were in the real span of `Dₙ`,
  -- the inner-product restrictions (13) force a contradiction.
  have hw_not_span :
      w ∉ (Submodule.span ℝ (Set.range hDn.e) : Submodule ℝ ℝ²⁴) := by
    intro hwSpan
    -- First show `⟪e_k,w⟫ = 0` for all indices `k = 2,3,...,n-1`.
    have hshift_zero : ∀ k : Fin (n - 2), (⟪hDn.e (shift k), w⟫ : ℝ) = 0 := by
      intro k
      let ik : Fin n := shift k
      have hik0 : (i0 : Fin n) ≠ ik := by
        intro hEq
        have : 0 = k.1 + 2 := by simpa [i0, ik, shift] using! congrArg Fin.val hEq
        simpa
      -- The two shell vectors `u± = √2(e₀ ± e_k)` lie in the lattice shell.
      let uplus : ℝ²⁴ := Real.sqrt 2 • (hDn.e i0 + hDn.e ik)
      let uminus : ℝ²⁴ := Real.sqrt 2 • (hDn.e i0 - hDn.e ik)
      have huplus : uplus ∈ latticeShell4 C := by
        have hmem := hDn.minVec_mem i0 ik hik0
        simpa [uplus] using! hmem.1
      have huminus : uminus ∈ latticeShell4 C := by
        have hmem := hDn.minVec_mem i0 ik hik0
        simpa [uminus] using! hmem.2
      -- `w` is not one of these minimal vectors, by construction (`w ∉ range vec`).
      have hw_ne_uplus : w ≠ uplus := by
        intro hEq
        apply hwT
        refine ⟨⟨k, true⟩, ?_⟩
        simpa [T, vec, signR, uplus, ik] using! hEq.symm
      have hw_ne_uminus : w ≠ uminus := by
        intro hEq
        apply hwT
        refine ⟨⟨k, false⟩, ?_⟩
        simpa [T, vec, signR, uminus, ik, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using!
          hEq.symm
      have hle_uplus : (⟪uplus, w⟫ : ℝ) ≤ (2 : ℝ) :=
        inner_le_two_of_mem_shell4_of_ne C h huplus hwShell (Ne.symm hw_ne_uplus)
      have hle_uminus : (⟪uminus, w⟫ : ℝ) ≤ (2 : ℝ) :=
        inner_le_two_of_mem_shell4_of_ne C h huminus hwShell (Ne.symm hw_ne_uminus)
      -- Compute the two inner products as `2 ± √2 ⟪e_k,w⟫` and deduce `⟪e_k,w⟫ = 0`.
      have hform_plus :
          (⟪uplus, w⟫ : ℝ) =
            (Real.sqrt 2 : ℝ) * ((⟪hDn.e i0, w⟫ : ℝ) + (⟪hDn.e ik, w⟫ : ℝ)) := by
        simp [uplus, real_inner_smul_left, inner_add_left, mul_add]
      have hform_minus :
          (⟪uminus, w⟫ : ℝ) =
            (Real.sqrt 2 : ℝ) * ((⟪hDn.e i0, w⟫ : ℝ) - (⟪hDn.e ik, w⟫ : ℝ)) := by
        simp [uminus, real_inner_smul_left, inner_sub_left, mul_sub]
      have hle1 :
          (Real.sqrt 2 : ℝ) * ((⟪hDn.e i0, w⟫ : ℝ) + (⟪hDn.e ik, w⟫ : ℝ)) ≤ (2 : ℝ) := by
        simpa [hform_plus] using! hle_uplus
      have hle2 :
          (Real.sqrt 2 : ℝ) * ((⟪hDn.e i0, w⟫ : ℝ) - (⟪hDn.e ik, w⟫ : ℝ)) ≤ (2 : ℝ) := by
        simpa [hform_minus] using! hle_uminus
      -- Substitute `⟪e₀,w⟫ = √2` and cancel the positive factor `√2`.
      have hle1' :
          (Real.sqrt 2 : ℝ) * (Real.sqrt 2 + (⟪hDn.e ik, w⟫ : ℝ)) ≤ (2 : ℝ) := by
        simpa [hw0, add_assoc, add_comm, add_left_comm] using! hle1
      have hle2' :
          (Real.sqrt 2 : ℝ) * (Real.sqrt 2 - (⟪hDn.e ik, w⟫ : ℝ)) ≤ (2 : ℝ) := by
        simpa [hw0, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using! hle2
      have hik_le0 : (⟪hDn.e ik, w⟫ : ℝ) ≤ 0 := by
        have : (Real.sqrt 2 : ℝ) * (⟪hDn.e ik, w⟫ : ℝ) ≤ 0 := by
          -- rearrange `√2*(√2+ik) ≤ 2` to `√2*ik ≤ 0`
          have hs : (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) = (2 : ℝ) := by
            have hnonneg2 : (0 : ℝ) ≤ 2 := by norm_num
            simp [Real.mul_self_sqrt hnonneg2]
          -- `√2*(√2+ik) = 2 + √2*ik`
          have : (2 : ℝ) + (Real.sqrt 2 : ℝ) * (⟪hDn.e ik, w⟫ : ℝ) ≤ (2 : ℝ) := by
            simpa [mul_add, hs, add_assoc, add_left_comm, add_comm] using! hle1'
          linarith
        exact nonpos_of_mul_nonpos_right this hsqrt2_pos
      have hik_ge0 : 0 ≤ (⟪hDn.e ik, w⟫ : ℝ) := by
        have hs : (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) = (2 : ℝ) := by
          have hnonneg2 : (0 : ℝ) ≤ 2 := by norm_num
          simp [Real.mul_self_sqrt hnonneg2]
        have : 0 ≤ (Real.sqrt 2 : ℝ) * (⟪hDn.e ik, w⟫ : ℝ) := by
          -- from `√2*(√2-ik) ≤ 2` and `√2*√2 = 2`
          nlinarith [hle2', hs]
        exact nonneg_of_mul_nonneg_right this hsqrt2_pos
      have hik : (⟪hDn.e ik, w⟫ : ℝ) = 0 := le_antisymm hik_le0 hik_ge0
      simpa [ik] using! hik
    -- Now show `w` must equal `√2 • e₀` inside the span, contradicting `‖w‖^2 = 4`.
    let K : Submodule ℝ ℝ²⁴ := Submodule.span ℝ (Set.range hDn.e)
    have he0_mem : hDn.e i0 ∈ K :=
      Submodule.subset_span ⟨i0, rfl⟩
    have he1_mem : hDn.e i1 ∈ K :=
      Submodule.subset_span ⟨i1, rfl⟩
    let a0 : ℝ := (⟪hDn.e i0, w⟫ : ℝ)
    let d : ℝ²⁴ := w - a0 • hDn.e i0
    have hd_mem : d ∈ K := by
      refine K.sub_mem hwSpan ?_
      exact K.smul_mem a0 he0_mem
    have hite :
        ∀ i j : Fin n, (⟪hDn.e i, hDn.e j⟫ : ℝ) =
          if i = j then (1 : ℝ) else (0 : ℝ) :=
      (orthonormal_iff_ite).1 hDn.ortho
    have hcoord0 : a0 = Real.sqrt 2 := by
      simpa [a0] using! hw0
    have hcoord1 : (⟪hDn.e i1, w⟫ : ℝ) = 0 := hw1
    have hcoord_rest : ∀ i : Fin n, i ≠ i0 → i ≠ i1 → (⟪hDn.e i, w⟫ : ℝ) = 0 := by
      intro i hi0 hi1
      -- If `i ≠ 0,1` then `i.val ≥ 2`, hence `i = shift k` for `k : Fin (n-2)`.
      have hi_ge2 : 2 ≤ i.1 := by
        have hi_cases : i.1 = 0 ∨ i.1 = 1 ∨ 2 ≤ i.1 := by omega
        rcases hi_cases with h0 | h1 | hi_ge2
        · exact False.elim (hi0 (by ext; simp [i0, h0]))
        · exact False.elim (hi1 (by ext; simp [i1, h1]))
        · exact hi_ge2
      have hk_lt : i.1 - 2 < n - 2 := by
        grind
      let k : Fin (n - 2) := ⟨i.1 - 2, hk_lt⟩
      have hshift : shift k = i := by
        apply Fin.ext
        simp [shift, k, Nat.sub_add_cancel hi_ge2]
      rw [← hshift]
      exact hshift_zero k
    have hd_orth : d ∈ Kᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      -- It suffices to check on the generators `range hDn.e`.
      refine Submodule.span_induction (R := ℝ) (s := Set.range hDn.e)
        (p := fun x hx => (⟪x, d⟫ : ℝ) = 0) ?_ ?_ ?_ ?_ hu
      · intro x hx
        rcases hx with ⟨i, rfl⟩
        by_cases hi0 : i = i0
        · subst i
          -- `⟪e₀, w - a0•e₀⟫ = a0 - a0*1 = 0`.
          have hnorm : ‖hDn.e i0‖ = (1 : ℝ) := hDn.ortho.1 i0
          simp [d, a0, inner_sub_right, inner_smul_right, hnorm]
        · by_cases hi1 : i = i1
          · subst hi1
            -- `⟪e₁, w⟫ = 0` and `⟪e₁,e₀⟫ = 0`.
            have hi10 : (i1 : Fin n) ≠ i0 := hi0
            have hi_inner : (⟪hDn.e i1, hDn.e i0⟫ : ℝ) = 0 := by
              simpa [hi10] using! (hite i1 i0)
            simp [d, a0, inner_sub_right, inner_smul_right, hcoord1, hi_inner]
          · have hwi : (⟪hDn.e i, w⟫ : ℝ) = 0 := hcoord_rest i hi0 hi1
            have hi_inner : (⟪hDn.e i, hDn.e i0⟫ : ℝ) = 0 := by
              simpa [hi0] using! (hite i i0)
            simp [d, a0, inner_sub_right, inner_smul_right, hwi, hi_inner]
      · simp [d]
      · intro x y hx hy hx0 hy0
        simp [inner_add_left, hx0, hy0]
      · intro r x hx hx0
        simp [real_inner_smul_left, hx0]
    have hd_zero : d = 0 := by
      have : d ∈ (K ⊓ Kᗮ : Submodule ℝ ℝ²⁴) := ⟨hd_mem, hd_orth⟩
      have : d ∈ (⊥ : Submodule ℝ ℝ²⁴) := by
        simpa [K.inf_orthogonal_eq_bot] using! this
      simpa using! this
    have hw_eq : w = a0 • hDn.e i0 := by
      -- `d = w - a0•e₀ = 0`
      have : w - a0 • hDn.e i0 = 0 := by simpa [d] using! hd_zero
      exact sub_eq_zero.mp this
    have hnorm_w : ‖w‖ ^ 2 = (2 : ℝ) := by
      -- `w = √2•e₀` inside the span
      have he0_norm : ‖hDn.e i0‖ = (1 : ℝ) := hDn.ortho.1 i0
      calc
        ‖w‖ ^ 2 = ‖a0 • hDn.e i0‖ ^ 2 := by simp [hw_eq]
        _ = ‖a0‖ ^ 2 * ‖hDn.e i0‖ ^ 2 := by
          simp [norm_smul, mul_pow]
        _ = ‖a0‖ ^ 2 := by simp [he0_norm]
        _ = (2 : ℝ) := by
          -- `a0 = √2`
          simp [hcoord0]
    -- Contradiction with `w ∈ latticeShell4`, which forces `‖w‖^2 = 4`.
    have : (2 : ℝ) = 4 := by simpa [hnorm_w] using! hwShell.2
    norm_num at this
  -- Return the witness `w`.
  refine ⟨w, hwShell, ?_⟩
  -- Unfold the `let g1`/`let g2` binders from the statement.
  refine ⟨?_, ?_, hw_not_span⟩
  · simpa [g1, i0, i1] using! hwg1
  · simpa [g2, i0, i1] using! hwg2

/-- Induction step for BS81 Lemma 20: extend `ContainsDn C n` to `ContainsDn C (n + 1)`. -/
public def containsDn_succ_of_containsDn
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (n : ℕ) (hn3 : 3 ≤ n) (hn23 : n ≤ 23)
    (hDn : ContainsDn C n) :
    ContainsDn C (n + 1) := by
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := by
    have : (0 : ℝ) < (2 : ℝ) := by norm_num
    exact Real.sqrt_pos.2 this
  have hsqrt2_ne : (Real.sqrt 2 : ℝ) ≠ 0 := ne_of_gt hsqrt2_pos
  have hsqrt2_norm_sq : ‖(Real.sqrt 2 : ℝ)‖ ^ 2 = (2 : ℝ) := by
    norm_num
  have norm_smul_sqrt2_sq (x : ℝ²⁴) :
      ‖(Real.sqrt 2 : ℝ) • x‖ ^ 2 = (2 : ℝ) * ‖x‖ ^ 2 := by
    calc
      ‖(Real.sqrt 2 : ℝ) • x‖ ^ 2 = (‖(Real.sqrt 2 : ℝ)‖ * ‖x‖) ^ 2 := by
        simpa using! congrArg (fun t : ℝ => t ^ 2) (norm_smul (Real.sqrt 2 : ℝ) x)
      _ = ‖(Real.sqrt 2 : ℝ)‖ ^ 2 * ‖x‖ ^ 2 := by
        simp [mul_pow]
      _ = (2 : ℝ) * ‖x‖ ^ 2 := by
        simp
  let i0 : Fin n := ⟨0, lt_of_lt_of_le (by decide : 0 < 3) hn3⟩
  let i1 : Fin n := ⟨1, lt_of_lt_of_le (by decide : 1 < 3) hn3⟩
  have hi01 : (i0 : Fin n) ≠ i1 := by
    intro hEq
    have : (0 : ℕ) = 1 := by
      simpa [i0, i1] using! congrArg Fin.val hEq
    exact Nat.zero_ne_one this
  let g1 : ℝ²⁴ := Real.sqrt 2 • (hDn.e i0 + hDn.e i1)
  let g2 : ℝ²⁴ := Real.sqrt 2 • (hDn.e i0 - hDn.e i1)
  -- Choose `w` as in `exists_extension_vector`.
  have hwExists := exists_extension_vector (C := C) h n hn3 hn23 hDn
  let w : ℝ²⁴ := Classical.choose hwExists
  have hwSpec := Classical.choose_spec hwExists
  have hwShell : w ∈ latticeShell4 C := hwSpec.1
  have hw' :
      (⟪g1, w⟫ : ℝ) = 2 ∧ (⟪g2, w⟫ : ℝ) = 2 ∧
        w ∉ (Submodule.span ℝ (Set.range hDn.e) : Submodule ℝ ℝ²⁴) := by
    -- The statement of `exists_extension_vector` uses explicit `Fin` terms `⟨0, _⟩`, `⟨1, _⟩`.
    -- Reintroduce them to avoid definitional-equality issues with the bundled proofs.
    let i0' : Fin n := ⟨0, lt_of_lt_of_le (by decide : 0 < 3) hn3⟩
    let i1' : Fin n := ⟨1, lt_of_lt_of_le (by decide : 1 < 3) hn3⟩
    have hi0' : i0' = i0 := by
      apply Fin.ext
      simp [i0', i0]
    have hi1' : i1' = i1 := by
      apply Fin.ext
      simp [i1', i1]
    have hw'' :
        (⟪Real.sqrt 2 • (hDn.e i0' + hDn.e i1'), Classical.choose hwExists⟫ : ℝ) = 2 ∧
          (⟪Real.sqrt 2 • (hDn.e i0' - hDn.e i1'), Classical.choose hwExists⟫ : ℝ) = 2 ∧
            Classical.choose hwExists ∉
              (Submodule.span ℝ (Set.range hDn.e) : Submodule ℝ ℝ²⁴) := by
      simpa [i0', i1'] using! hwSpec.2
    assumption
  have hwg1 : (⟪g1, w⟫ : ℝ) = 2 := hw'.1
  have hwg2 : (⟪g2, w⟫ : ℝ) = 2 := hw'.2.1
  have hw_not_span :
      w ∉ (Submodule.span ℝ (Set.range hDn.e) : Submodule ℝ ℝ²⁴) := hw'.2.2
  -- Extract the coordinates of `w` along `e₀,e₁`.
  have hg1_form :
      (⟪g1, w⟫ : ℝ) =
        (Real.sqrt 2 : ℝ) * ((⟪hDn.e i0, w⟫ : ℝ) + (⟪hDn.e i1, w⟫ : ℝ)) := by
    simp [g1, real_inner_smul_left, inner_add_left, mul_add]
  have hg2_form :
      (⟪g2, w⟫ : ℝ) =
        (Real.sqrt 2 : ℝ) * ((⟪hDn.e i0, w⟫ : ℝ) - (⟪hDn.e i1, w⟫ : ℝ)) := by
    simp [g2, real_inner_smul_left, inner_sub_left, mul_sub]
  have h2_div_sqrt2 : (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 :=
    Real.div_sqrt
  have hsum : (⟪hDn.e i0, w⟫ : ℝ) + (⟪hDn.e i1, w⟫ : ℝ) = Real.sqrt 2 := by
    have : (Real.sqrt 2 : ℝ) *
          ((⟪hDn.e i0, w⟫ : ℝ) + (⟪hDn.e i1, w⟫ : ℝ)) = 2 := by
      simpa [hg1_form] using! hwg1
    have :
        (⟪hDn.e i0, w⟫ : ℝ) + (⟪hDn.e i1, w⟫ : ℝ) =
          (2 : ℝ) / Real.sqrt 2 := by
      refine (eq_div_iff hsqrt2_ne).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using! this
    simpa [h2_div_sqrt2] using! this
  have hdiff : (⟪hDn.e i0, w⟫ : ℝ) - (⟪hDn.e i1, w⟫ : ℝ) = Real.sqrt 2 := by
    have : (Real.sqrt 2 : ℝ) *
          ((⟪hDn.e i0, w⟫ : ℝ) - (⟪hDn.e i1, w⟫ : ℝ)) = 2 := by
      simpa [hg2_form] using! hwg2
    have :
        (⟪hDn.e i0, w⟫ : ℝ) - (⟪hDn.e i1, w⟫ : ℝ) =
          (2 : ℝ) / Real.sqrt 2 := by
      refine (eq_div_iff hsqrt2_ne).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using! this
    simpa [h2_div_sqrt2] using! this
  have hw0 : (⟪hDn.e i0, w⟫ : ℝ) = Real.sqrt 2 := by linarith [hsum, hdiff]
  have hw1 : (⟪hDn.e i1, w⟫ : ℝ) = 0 := by linarith [hsum, hdiff]
  -- Convenient shorthand: the `ℝ`-span of the embedded `Dₙ`.
  let K : Submodule ℝ ℝ²⁴ := Submodule.span ℝ (Set.range hDn.e)
  have he_mem : ∀ i : Fin n, hDn.e i ∈ K := fun i => Submodule.subset_span ⟨i, rfl⟩
  -- (13) gives strong constraints on inner products between shell vectors.
  have hw_orth : ∀ i : Fin n, i ≠ i0 → (⟪hDn.e i, w⟫ : ℝ) = 0 := by
    intro i hi0
    by_cases hi1 : i = i1
    · subst hi1
      exact hw1
    · -- Use `u± := √2(e₀ ± e_i)` and the fact that `w ∉ K` to exclude inner product `4`.
      let uplus : ℝ²⁴ := Real.sqrt 2 • (hDn.e i0 + hDn.e i)
      let uminus : ℝ²⁴ := Real.sqrt 2 • (hDn.e i0 - hDn.e i)
      have hu : uplus ∈ latticeShell4 C ∧ uminus ∈ latticeShell4 C := by
        have hmem := hDn.minVec_mem i0 i (Ne.symm hi0)
        exact ⟨by simpa [uplus] using! hmem.1, by simpa [uminus] using! hmem.2⟩
      have huplus : uplus ∈ latticeShell4 C := hu.1
      have huminus : uminus ∈ latticeShell4 C := hu.2
      have huplus_K : uplus ∈ K := by
        refine K.smul_mem (Real.sqrt 2 : ℝ) ?_
        exact K.add_mem (he_mem i0) (he_mem i)
      have huminus_K : uminus ∈ K := by
        refine K.smul_mem (Real.sqrt 2 : ℝ) ?_
        exact K.sub_mem (he_mem i0) (he_mem i)
      have hle_uplus : (⟪uplus, w⟫ : ℝ) ≤ (2 : ℝ) :=
        inner_le_two_of_mem_shell4_of_ne C h huplus hwShell (
          ne_of_mem_of_not_mem huplus_K hw_not_span)
      have hle_uminus : (⟪uminus, w⟫ : ℝ) ≤ (2 : ℝ) :=
        inner_le_two_of_mem_shell4_of_ne C h huminus hwShell (
          ne_of_mem_of_not_mem huminus_K hw_not_span)
      have hform_plus :
          (⟪uplus, w⟫ : ℝ) =
            (Real.sqrt 2 : ℝ) * ((⟪hDn.e i0, w⟫ : ℝ) + (⟪hDn.e i, w⟫ : ℝ)) := by
        simp [uplus, real_inner_smul_left, inner_add_left, mul_add]
      have hform_minus :
          (⟪uminus, w⟫ : ℝ) =
            (Real.sqrt 2 : ℝ) * ((⟪hDn.e i0, w⟫ : ℝ) - (⟪hDn.e i, w⟫ : ℝ)) := by
        simp [uminus, real_inner_smul_left, inner_sub_left, mul_sub]
      have hle1 :
          (Real.sqrt 2 : ℝ) *
              ((⟪hDn.e i0, w⟫ : ℝ) + (⟪hDn.e i, w⟫ : ℝ)) ≤ (2 : ℝ) := by
        simpa [hform_plus] using! hle_uplus
      have hle2 :
          (Real.sqrt 2 : ℝ) *
              ((⟪hDn.e i0, w⟫ : ℝ) - (⟪hDn.e i, w⟫ : ℝ)) ≤ (2 : ℝ) := by
        simpa [hform_minus] using! hle_uminus
      have hle1' :
          (Real.sqrt 2 : ℝ) * (Real.sqrt 2 + (⟪hDn.e i, w⟫ : ℝ)) ≤ (2 : ℝ) := by
        simpa [hw0, add_assoc, add_comm, add_left_comm] using! hle1
      have hle2' :
          (Real.sqrt 2 : ℝ) * (Real.sqrt 2 - (⟪hDn.e i, w⟫ : ℝ)) ≤ (2 : ℝ) := by
        simpa [hw0, add_assoc, add_comm, add_left_comm] using! hle2
      have hik_le0 : (⟪hDn.e i, w⟫ : ℝ) ≤ 0 := by
        have hs : (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) = (2 : ℝ) := by
          have hnonneg2 : (0 : ℝ) ≤ 2 := by norm_num
          simp [Real.mul_self_sqrt hnonneg2]
        have : (2 : ℝ) + (Real.sqrt 2 : ℝ) * (⟪hDn.e i, w⟫ : ℝ) ≤ (2 : ℝ) := by
          simpa [mul_add, hs, add_assoc, add_left_comm, add_comm] using! hle1'
        have : (Real.sqrt 2 : ℝ) * (⟪hDn.e i, w⟫ : ℝ) ≤ 0 := by linarith
        exact nonpos_of_mul_nonpos_right this hsqrt2_pos
      have hik_ge0 : 0 ≤ (⟪hDn.e i, w⟫ : ℝ) := by
        have hs : (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) = (2 : ℝ) := by
          have hnonneg2 : (0 : ℝ) ≤ 2 := by norm_num
          simp [Real.mul_self_sqrt hnonneg2]
        have hle' :
            (Real.sqrt 2 : ℝ) * ((Real.sqrt 2 : ℝ) - (⟪hDn.e i, w⟫ : ℝ)) ≤
              (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) := by
          simpa [hs] using! hle2'
        have hsub :
            (Real.sqrt 2 : ℝ) - (⟪hDn.e i, w⟫ : ℝ) ≤ (Real.sqrt 2 : ℝ) :=
          le_of_mul_le_mul_left hle' hsqrt2_pos
        linarith
      exact le_antisymm hik_le0 hik_ge0
  -- Define `eNew = (w / √2) - e₀`, and show that appending it preserves orthonormality.
  let r : ℝ := (1 / (Real.sqrt 2 : ℝ))
  let a : ℝ²⁴ := r • w
  let eNew : ℝ²⁴ := a - hDn.e i0
  have hw_inner_self : (⟪w, w⟫ : ℝ) = (4 : ℝ) := by
    have hself : (⟪w, w⟫ : ℝ) = ‖w‖ ^ 2 := by
      simp
    calc
      (⟪w, w⟫ : ℝ) = ‖w‖ ^ 2 := hself
      _ = (4 : ℝ) := hwShell.2
  have ha_a : (inner ℝ a a : ℝ) = (2 : ℝ) := by
    have hsqrt2_sq : (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) = (2 : ℝ) := by
      have hnonneg2 : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
      simp [Real.mul_self_sqrt hnonneg2]
    have hr_sq : r * r = (1 / 2 : ℝ) := by
      dsimp [r]
      field_simp [hsqrt2_ne]
      simp
    calc
      (inner ℝ a a : ℝ) = r * (r * (⟪w, w⟫ : ℝ)) := by
        dsimp [a]
        rw [real_inner_smul_left, real_inner_smul_right]
      _ = r * (r * (4 : ℝ)) := by
        rw [hw_inner_self]
      _ = (2 : ℝ) := by
        -- Use `r^2 = 1/2`.
        calc
          r * (r * (4 : ℝ)) = (r * r) * (4 : ℝ) := by ring
          _ = (1 / 2 : ℝ) * (4 : ℝ) := by simp [hr_sq]
          _ = (2 : ℝ) := by norm_num
  have ha_e0 : (inner ℝ a (hDn.e i0) : ℝ) = (1 : ℝ) := by
    have hw0' : (⟪w, hDn.e i0⟫ : ℝ) = Real.sqrt 2 := by
      simpa [real_inner_comm] using! hw0
    calc
      (inner ℝ a (hDn.e i0) : ℝ) = r * (⟪w, hDn.e i0⟫ : ℝ) := by
        simp [a, real_inner_smul_left]
      _ = r * (Real.sqrt 2 : ℝ) := by simp [hw0']
      _ = (1 : ℝ) := by
        simp [r, hsqrt2_ne]
  have he0_e0 : (inner ℝ (hDn.e i0) (hDn.e i0) : ℝ) = (1 : ℝ) := by
    simpa using! ((orthonormal_iff_ite).1 hDn.ortho i0 i0)
  have heNew_eNew : (⟪eNew, eNew⟫ : ℝ) = (1 : ℝ) :=
    inner_eq_one_of_eq_sub rfl ha_a ha_e0 he0_e0
  have heNew_orth_left : ∀ i : Fin n, (⟪hDn.e i, eNew⟫ : ℝ) = 0 := by
    intro i
    by_cases hi0 : i = i0
    · subst i
      -- `⟪e₀, a - e₀⟫ = 1 - 1 = 0`.
      have ha_e0' : (⟪hDn.e i0, a⟫ : ℝ) = (1 : ℝ) := by
        simpa [real_inner_comm] using! ha_e0
      calc
        (⟪hDn.e i0, eNew⟫ : ℝ) = (⟪hDn.e i0, a - hDn.e i0⟫ : ℝ) := by
          simp [eNew]
        _ = (⟪hDn.e i0, a⟫ : ℝ) - (⟪hDn.e i0, hDn.e i0⟫ : ℝ) := by
          simp [inner_sub_right]
        _ = (1 : ℝ) - (1 : ℝ) := by
          rw [ha_e0', he0_e0]
        _ = 0 := by ring
    · have hwi : (⟪hDn.e i, w⟫ : ℝ) = 0 := hw_orth i hi0
      have hite :
          ∀ i j : Fin n, (⟪hDn.e i, hDn.e j⟫ : ℝ) =
            if i = j then (1 : ℝ) else (0 : ℝ) :=
        (orthonormal_iff_ite).1 hDn.ortho
      have hei0 : (⟪hDn.e i, hDn.e i0⟫ : ℝ) = 0 := by simpa [hi0] using! (hite i i0)
      simp [eNew, a, inner_sub_right, real_inner_smul_right, hwi, hei0]
  have heNew_orth_right : ∀ i : Fin n, (⟪eNew, hDn.e i⟫ : ℝ) = 0 := by
    intro i
    rw [real_inner_comm]
    exact heNew_orth_left i
  -- The extended frame.
  let e' : Fin (n + 1) → ℝ²⁴ := Fin.snoc hDn.e eNew
  have hortho' : Orthonormal ℝ e' := by
    rw [orthonormal_iff_ite]
    intro i j
    cases i using Fin.lastCases with
    | last =>
        cases j using Fin.lastCases with
        | last =>
            -- Avoid `simp` rewriting `⟪eNew,eNew⟫` into a `norm` goal.
            dsimp [e']
            simp only [Fin.snoc_last]
            rw [if_true]
            exact heNew_eNew
        | cast j0 =>
            dsimp [e']
            simp only [Fin.snoc_last, Fin.snoc_castSucc]
            have hne : (Fin.last n : Fin (n + 1)) ≠ j0.castSucc :=
              (Fin.castSucc_ne_last j0).symm
            rw [if_neg hne]
            exact heNew_orth_right j0
    | cast i0' =>
        cases j using Fin.lastCases with
        | last =>
            dsimp [e']
            simp only [Fin.snoc_castSucc, Fin.snoc_last]
            have hne : i0'.castSucc ≠ (Fin.last n : Fin (n + 1)) :=
              Fin.castSucc_ne_last i0'
            rw [if_neg hne]
            exact heNew_orth_left i0'
        | cast j0 =>
            dsimp [e']
            simp only [Fin.snoc_castSucc]
            have hite :
                ∀ i j : Fin n, (⟪hDn.e i, hDn.e j⟫ : ℝ) =
                  if i = j then (1 : ℝ) else (0 : ℝ) :=
              (orthonormal_iff_ite).1 hDn.ortho
            by_cases hij : i0' = j0
            · subst hij
              rw [if_pos rfl]
              simpa using! (hite i0' i0')
            · have hne : i0'.castSucc ≠ j0.castSucc := by
                intro hcast
                exact hij ((Fin.castSucc_injective n) hcast)
              rw [if_neg hne]
              simpa [hij] using! (hite i0' j0)
  -- Show `w = √2(e₀ + eNew)`; this is used to express the new minimal vectors in `latticeL`.
  have hw_eq : (Real.sqrt 2 : ℝ) • (hDn.e i0 + eNew) = w := by
    have : hDn.e i0 + eNew = a := by
      simp [eNew, a]
    calc
      (Real.sqrt 2 : ℝ) • (hDn.e i0 + eNew) = (Real.sqrt 2 : ℝ) • a := by simp [this]
      _ = ((Real.sqrt 2 : ℝ) * r) • w := by
        simp [a, smul_smul]
      _ = w := by
        have : (Real.sqrt 2 : ℝ) * r = (1 : ℝ) := by
          simp [r, hsqrt2_ne]
        simp [this]
  refine ⟨e', hortho', ?_⟩
  dsimp [e']
  exact
    (minVec_mem_snoc_of_hw_eq (C := C) (n := n) (hDn := hDn) (i0 := i0) (i1 := i1)
      (hi01 := hi01) (w := w) (eNew := eNew) (hwShell := hwShell)
      (norm_smul_sqrt2_sq := fun x => norm_smul_sqrt2_sq x)
      (hw_eq := hw_eq) (heNew_eNew := heNew_eNew) (heNew_orth_left := heNew_orth_left))

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20
