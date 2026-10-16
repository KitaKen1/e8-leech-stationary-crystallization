-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOnePsiSnumOps
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOneCoeffs
public import SpherePacking.Dim24.Inequalities.Ineq2.GeOne.Ineq2PsiSnum.PsiSnumCoeffs.Bounds
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiRSeriesSetup.SparseCoeffs


/-!
# Certificate rewriting for `psiSnumCoeffFun`

This file connects the list-based certificate operations (`coeffList`, `addZ`, `mulZ`, `powZ`,
`shift1Z`, ...) to the coefficient functions used in the bounds development.

The main public output is `psiSnumCoeffs_calc_getD_eq`, identifying the computed coefficient list
`psiSnumCoeffs_calc` with `psiSnumCoeffFun` on indices `n < Ineq2GeOneCoeffs.N`.

## Main statements
* `psiSnumCoeffs_calc_getD_eq`
-/

noncomputable section

namespace SpherePacking.Dim24

open AppendixA

namespace Ineq2PsiSnum

open scoped BigOperators

private lemma getD_ofFn {α : Type} (f : Fin Ineq2GeOneCoeffs.N → α) {n : ℕ}
    (hn : n < Ineq2GeOneCoeffs.N) (d : α) :
    (List.ofFn f).getD n d = f ⟨n, hn⟩ := by
  have hnlen : n < (List.ofFn f).length :=
    lt_of_lt_of_eq hn (List.length_ofFn (f := f)).symm
  calc
    (List.ofFn f).getD n d = (List.ofFn f)[n] :=
      List.getD_eq_getElem (l := List.ofFn f) (d := d) hnlen
    _ = f ⟨n, hn⟩ := List.getElem_ofFn (f := f) (i := n) hn

lemma theta01CoeffTrunc_eq_theta01CoeffFun (n : ℕ) (hn : n < Ineq2GeOneCoeffs.N) :
    theta01CoeffTrunc n = theta01CoeffFun n := by
  -- Compare the two finite sums by showing the summand vanishes outside the cutoff range.
  have hn100 : n < 100 := by simpa [Ineq2GeOneCoeffs.N] using! hn
  let g : ℕ → ℤ := fun k =>
    if k ^ (2 : ℕ) = n then (if k = 0 then (1 : ℤ) else 2 * ((-1 : ℤ) ^ k)) else 0
  have hg_ge11 : ∀ k : ℕ, 11 ≤ k → g k = 0 := by
    intro k hk
    have hn121 : n < 121 := lt_trans hn100 (by decide : 100 < 121)
    have hk2 : (121 : ℕ) ≤ k ^ (2 : ℕ) := by
      have hmul : (11 : ℕ) * 11 ≤ k * k := Nat.mul_le_mul hk hk
      simpa [pow_two] using! hmul
    grind only
  have hg_gt : ∀ k : ℕ, n < k → g k = 0 := by
    intro k hk
    have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hk
    have hk_le : k ≤ k ^ (2 : ℕ) := by
      -- `k ≤ k*k`.
      simpa [pow_two, mul_assoc] using! (Nat.le_mul_of_pos_right k hkpos)
    grind only
  -- Now compare the two sums by subset reduction.
  by_cases h : n + 1 ≤ AppendixA.BleadingCoeffs.thetaCutoff + 1
  · -- `range (n+1) ⊆ range (thetaCutoff+1)`.
    have hsub : Finset.range (n + 1) ⊆ Finset.range (AppendixA.BleadingCoeffs.thetaCutoff + 1) :=
      Finset.range_subset_range.mpr h
    have hsum :
        (∑ k ∈ Finset.range (n + 1), g k) =
          ∑ k ∈ Finset.range (AppendixA.BleadingCoeffs.thetaCutoff + 1), g k := by
      refine Finset.sum_subset hsub ?_
      intro k hk hknot
      have hk' : ¬ k < n + 1 := by
        -- `k ∉ range (n+1)`.
        simpa [Finset.mem_range] using! hknot
      have hkgt : n < k := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_of_not_gt hk')
      exact hg_gt k hkgt
    -- rewrite both definitions in terms of `g`.
    simp [theta01CoeffTrunc, theta01CoeffFun, g, hsum]
  · -- `range (thetaCutoff+1) ⊆ range (n+1)`.
    have hsub : Finset.range (AppendixA.BleadingCoeffs.thetaCutoff + 1) ⊆ Finset.range (n + 1) := by
      intro k hk
      have hk' : k < AppendixA.BleadingCoeffs.thetaCutoff + 1 := by
        simpa [Finset.mem_range] using! hk
      have hk'' : AppendixA.BleadingCoeffs.thetaCutoff + 1 ≤ n + 1 := Nat.le_of_not_ge h
      exact (Finset.mem_range.2 (lt_of_lt_of_le hk' hk''))
    have hsum :
        (∑ k ∈ Finset.range (AppendixA.BleadingCoeffs.thetaCutoff + 1), g k) =
          ∑ k ∈ Finset.range (n + 1), g k := by
      refine Finset.sum_subset hsub ?_
      intro k hk hknot
      have hk' : ¬ k < AppendixA.BleadingCoeffs.thetaCutoff + 1 := by
        simpa [Finset.mem_range] using! hknot
      have hkge : AppendixA.BleadingCoeffs.thetaCutoff + 1 ≤ k := Nat.le_of_not_gt hk'
      -- `thetaCutoff = 10`, so the complement starts at `11`.
      have hk11 : 11 ≤ k := by simpa [AppendixA.BleadingCoeffs.thetaCutoff] using! hkge
      exact hg_ge11 k hk11
    simp [theta01CoeffTrunc, theta01CoeffFun, g, hsum]

lemma theta10CoeffTrunc_eq_theta10CoeffFun (n : ℕ) (hn : n < Ineq2GeOneCoeffs.N) :
    theta10CoeffTrunc n = theta10CoeffFun n := by
  have hn100 : n < 100 := by simpa [Ineq2GeOneCoeffs.N] using! hn
  let g : ℕ → ℤ := fun k => if k * (k + 1) = n then (2 : ℤ) else 0
  have hg_ge11 : ∀ k : ℕ, 11 ≤ k → g k = 0 := by
    intro k hk
    have hn132 : n < 132 := lt_trans hn100 (by decide : 100 < 132)
    have hk2 : (132 : ℕ) ≤ k * (k + 1) := by
      -- `11*12 ≤ k*(k+1)`.
      have hk1 : (12 : ℕ) ≤ k + 1 := Nat.succ_le_succ hk
      have hmul : (11 : ℕ) * 12 ≤ k * (k + 1) := Nat.mul_le_mul hk hk1
      simpa using! hmul
    have hne : k * (k + 1) ≠ n := ne_of_gt (lt_of_lt_of_le hn132 hk2)
    simp [g, hne]
  have hg_gt : ∀ k : ℕ, n < k → g k = 0 := by
    grind only
  by_cases h : n + 1 ≤ AppendixA.BleadingCoeffs.thetaCutoff + 1
  · have hsub : Finset.range (n + 1) ⊆ Finset.range (AppendixA.BleadingCoeffs.thetaCutoff + 1) :=
      Finset.range_subset_range.mpr h
    have hsum :
        (∑ k ∈ Finset.range (n + 1), g k) =
          ∑ k ∈ Finset.range (AppendixA.BleadingCoeffs.thetaCutoff + 1), g k := by
      refine Finset.sum_subset hsub ?_
      intro k hk hknot
      have hk' : ¬ k < n + 1 := by simpa [Finset.mem_range] using! hknot
      have hkgt : n < k := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_of_not_gt hk')
      exact hg_gt k hkgt
    simp [theta10CoeffTrunc, theta10CoeffFun, g, hsum]
  · have hsub : Finset.range (AppendixA.BleadingCoeffs.thetaCutoff + 1) ⊆ Finset.range (n + 1) := by
      intro k hk
      have hk' : k < AppendixA.BleadingCoeffs.thetaCutoff + 1 := by
        simpa [Finset.mem_range] using! hk
      have hk'' : AppendixA.BleadingCoeffs.thetaCutoff + 1 ≤ n + 1 := Nat.le_of_not_ge h
      exact (Finset.mem_range.2 (lt_of_lt_of_le hk' hk''))
    have hsum :
        (∑ k ∈ Finset.range (AppendixA.BleadingCoeffs.thetaCutoff + 1), g k) =
          ∑ k ∈ Finset.range (n + 1), g k := by
      refine Finset.sum_subset hsub ?_
      intro k hk hknot
      have hk' : ¬ k < AppendixA.BleadingCoeffs.thetaCutoff + 1 := by
        simpa [Finset.mem_range] using! hknot
      have hkge : AppendixA.BleadingCoeffs.thetaCutoff + 1 ≤ k := Nat.le_of_not_gt hk'
      have hk11 : 11 ≤ k := by simpa [AppendixA.BleadingCoeffs.thetaCutoff] using! hkge
      exact hg_ge11 k hk11
    simp [theta10CoeffTrunc, theta10CoeffFun, g, hsum]
lemma coeffList_getD (a : ℕ → ℤ) {n : ℕ} (hn : n < Ineq2GeOneCoeffs.N) :
    (coeffList a).getD n 0 = a n := by
  dsimp [coeffList]
  exact (getD_ofFn (f := fun i : Fin Ineq2GeOneCoeffs.N => a i.1) (n := n) hn (d := (0 : ℤ)))

lemma addZ_getD (a b : List ℤ) {n : ℕ} (hn : n < Ineq2GeOneCoeffs.N) :
    (addZ a b).getD n 0 = a.getD n 0 + b.getD n 0 := by
  dsimp [addZ]
  exact
    (getD_ofFn (f := fun i : Fin Ineq2GeOneCoeffs.N => a.getD i.1 0 + b.getD i.1 0)
      (n := n) hn (d := (0 : ℤ)))

lemma negZ_getD (a : List ℤ) {n : ℕ} (hn : n < Ineq2GeOneCoeffs.N) :
    (negZ a).getD n 0 = -a.getD n 0 := by
  dsimp [negZ]
  exact
    (getD_ofFn (f := fun i : Fin Ineq2GeOneCoeffs.N => -a.getD i.1 0) (n := n) hn (d := (0 : ℤ)))

lemma smulZ_getD (c : ℤ) (a : List ℤ) {n : ℕ} (hn : n < Ineq2GeOneCoeffs.N) :
    (smulZ c a).getD n 0 = c * a.getD n 0 := by
  dsimp [smulZ]
  exact
    (getD_ofFn (f := fun i : Fin Ineq2GeOneCoeffs.N => c * a.getD i.1 0) (n := n) hn (d := (0 : ℤ)))

lemma shift1Z_getD (a : List ℤ) {n : ℕ} (hn : n < Ineq2GeOneCoeffs.N) :
    (shift1Z a).getD n 0 = shift1Fun (fun k => a.getD k 0) n := by
  dsimp [shift1Z, shift1Fun]
  exact
    (getD_ofFn
      (f := fun i : Fin Ineq2GeOneCoeffs.N =>
        match i.1 with
        | 0 => 0
        | k + 1 => a.getD k 0)
      (n := n) hn (d := (0 : ℤ)))

lemma mulZ_getD (a b : List ℤ) {n : ℕ} (hn : n < Ineq2GeOneCoeffs.N) :
    (mulZ a b).getD n 0 =
      ∑ p ∈ Finset.antidiagonal n, a.getD p.1 0 * b.getD p.2 0 := by
  have h :
      (mulZ a b).getD n 0 = ∑ k ∈ Finset.range (n + 1), a.getD k 0 * b.getD (n - k) 0 := by
    dsimp [mulZ]
    exact
      (getD_ofFn
        (f := fun i : Fin Ineq2GeOneCoeffs.N =>
          let m := i.1
          ∑ k ∈ Finset.range (m + 1), a.getD k 0 * b.getD (m - k) 0)
        (n := n) hn (d := (0 : ℤ)))
  -- Convert the `range` sum to the `antidiagonal` sum.
  rw [h]
  simpa using!
    (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f := fun i j => a.getD i 0 * b.getD j 0) n).symm

lemma mulZ_getD_eq_convZ_of_eqOn (aZ bZ : List ℤ) (a b : ℕ → ℤ) {n : ℕ}
    (hn : n < Ineq2GeOneCoeffs.N)
    (ha : ∀ k ≤ n, aZ.getD k 0 = a k) (hb : ∀ k ≤ n, bZ.getD k 0 = b k) :
    (mulZ aZ bZ).getD n 0 = convZ a b n := by
  have hmulZ := mulZ_getD (a := aZ) (b := bZ) (n := n) hn
  rw [hmulZ]
  unfold convZ
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hm : p.1 + p.2 = n := by simpa [Finset.mem_antidiagonal] using! hp
  have hp1_le : p.1 ≤ n := by
    have : p.1 ≤ p.1 + p.2 := Nat.le_add_right _ _
    simpa [hm] using! this
  have hp2_le : p.2 ≤ n := by
    have : p.2 ≤ p.1 + p.2 := Nat.le_add_left _ _
    simpa [hm] using! this
  -- Avoid `simp` unfolding `getD` into `get?`.
  rw [ha p.1 hp1_le, hb p.2 hp2_le]

lemma powZ_getD_eq_powFun_of_eqOn (aZ : List ℤ) (a : ℕ → ℤ) :
    ∀ m n : ℕ,
      n < Ineq2GeOneCoeffs.N →
        (∀ k ≤ n, aZ.getD k 0 = a k) →
          (powZ aZ m).getD n 0 = (powFun a m) n := by
  intro m
  induction m with
  | zero =>
      intro n hn ha
      have h0 : (powZ aZ 0).getD n 0 = (if n = 0 then (1 : ℤ) else 0) := by
        dsimp [powZ]
        exact
          (getD_ofFn (f := fun i : Fin Ineq2GeOneCoeffs.N => if i.1 = 0 then (1 : ℤ) else 0)
            (n := n) hn (d := (0 : ℤ)))
      simpa [h0, powFun, oneFun]
  | succ m ih =>
      intro n hn ha
      have hpow : (powZ aZ (Nat.succ m)).getD n 0 =
          ∑ p ∈ Finset.antidiagonal n, aZ.getD p.1 0 * (powZ aZ m).getD p.2 0 := by
        simpa [powZ] using! (mulZ_getD (a := aZ) (b := powZ aZ m) (n := n) hn)
      rw [hpow]
      -- Rewrite the coefficients using `ha` and the induction hypothesis, valid on `p.1,p.2 ≤ n`.
      have hrewrite :
          (∑ p ∈ Finset.antidiagonal n, aZ.getD p.1 0 * (powZ aZ m).getD p.2 0) =
            ∑ p ∈ Finset.antidiagonal n, a p.1 * (powFun a m) p.2 := by
        refine Finset.sum_congr rfl ?_
        intro p hp
        have hm : p.1 + p.2 = n := by simpa [Finset.mem_antidiagonal] using! hp
        have hp1_le : p.1 ≤ n := by
          have : p.1 ≤ p.1 + p.2 := Nat.le_add_right _ _
          simpa [hm] using! this
        have hp2_le : p.2 ≤ n := by
          have : p.2 ≤ p.1 + p.2 := Nat.le_add_left _ _
          simpa [hm] using! this
        have hp2_lt : p.2 < Ineq2GeOneCoeffs.N := lt_of_le_of_lt hp2_le hn
        have hA : aZ.getD p.1 0 = a p.1 := ha p.1 hp1_le
        have hB : (powZ aZ m).getD p.2 0 = (powFun a m) p.2 := ih p.2 hp2_lt fun k hk =>
          ha k (le_trans hk hp2_le)
        -- Avoid `simp` unfolding `getD` into `get?`.
        rw [hA, hB]
      assumption

/--
Coefficientwise correctness of the computed list `psiSnumCoeffs_calc` on indices
`n < Ineq2GeOneCoeffs.N`.
-/
public lemma psiSnumCoeffs_calc_getD_eq (n : ℕ) (hn : n < Ineq2GeOneCoeffs.N) :
    psiSnumCoeffs_calc.getD n 0 = psiSnumCoeffFun n := by
  -- Reduce each coefficient list to its coefficient function on indices `≤ n`.
  have hθ01 : ∀ k ≤ n, (coeffList theta01CoeffTrunc).getD k 0 = theta01CoeffFun k := by
    intro k hk
    have hk' : k < Ineq2GeOneCoeffs.N := lt_of_le_of_lt hk hn
    have hget : (coeffList theta01CoeffTrunc).getD k 0 = theta01CoeffTrunc k := by
      simpa using! (coeffList_getD (a := theta01CoeffTrunc) (n := k) hk')
    exact hget.trans (theta01CoeffTrunc_eq_theta01CoeffFun (n := k) hk')
  have hθ10 : ∀ k ≤ n, (coeffList theta10CoeffTrunc).getD k 0 = theta10CoeffFun k := by
    intro k hk
    have hk' : k < Ineq2GeOneCoeffs.N := lt_of_le_of_lt hk hn
    have hget : (coeffList theta10CoeffTrunc).getD k 0 = theta10CoeffTrunc k := by
      simpa using! (coeffList_getD (a := theta10CoeffTrunc) (n := k) hk')
    exact hget.trans (theta10CoeffTrunc_eq_theta10CoeffFun (n := k) hk')
  set theta01Z : List ℤ := coeffList theta01CoeffTrunc
  set theta10Z : List ℤ := coeffList theta10CoeffTrunc
  set H₄Z : List ℤ := powZ theta01Z 4
  set H₂Z : List ℤ := shift1Z (powZ theta10Z 4)
  have hH4 : ∀ k ≤ n, H₄Z.getD k 0 = H4CoeffFun k := by
    intro k hk
    have hk' : k < Ineq2GeOneCoeffs.N := lt_of_le_of_lt hk hn
    have hθ01' : ∀ j ≤ k, theta01Z.getD j 0 = theta01CoeffFun j := by
      intro j hj
      exact (hθ01 j (le_trans hj hk)).trans (by rfl)
    have := powZ_getD_eq_powFun_of_eqOn (aZ := theta01Z) (a := theta01CoeffFun) (m := 4) (n :=
      k) hk' ?_
    · simpa [H₄Z, H4CoeffFun, theta01Z] using! this
    · intro j hj
      -- `theta01Z` agrees with `theta01CoeffFun` on indices `≤ k`.
      exact (hθ01 j (le_trans hj hk)).trans (by rfl)
  have hH2 : ∀ k ≤ n, H₂Z.getD k 0 = H2CoeffFun k := by
    intro k hk
    have hk' : k < Ineq2GeOneCoeffs.N := lt_of_le_of_lt hk hn
    have hpow :
        (powZ theta10Z 4).getD k 0 = (powFun theta10CoeffFun 4) k := by
      have := powZ_getD_eq_powFun_of_eqOn (aZ := theta10Z) (a := theta10CoeffFun) (m := 4) (n :=
        k) hk' ?_
      · simpa [theta10Z] using! this
      · intro j hj
        exact (hθ10 j (le_trans hj hk)).trans (by rfl)
    have hshift : (shift1Z (powZ theta10Z 4)).getD k 0 =
        shift1Fun (fun j => (powZ theta10Z 4).getD j 0) k := by
      simpa [theta10Z] using! (shift1Z_getD (a := powZ theta10Z 4) (n := k) hk')
    -- Finish by cases on `k`, using only the defining equation of `shift1Fun`.
    cases k with
    | zero =>
        rfl
    | succ k =>
        have hk0 : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
        have hk'' : k < Ineq2GeOneCoeffs.N := lt_of_le_of_lt hk0 hn
        have hpow' :
            (powZ theta10Z 4).getD k 0 = (powFun theta10CoeffFun 4) k := by
          have := powZ_getD_eq_powFun_of_eqOn (aZ := theta10Z) (a := theta10CoeffFun) (m := 4) (n :=
            k) hk'' ?_
          · simpa [theta10Z] using! this
          · intro j hj
            exact (hθ10 j (le_trans hj hk0)).trans (by rfl)
        calc
          H₂Z.getD (Nat.succ k) 0 =
              shift1Fun (fun j => (powZ theta10Z 4).getD j 0) (Nat.succ k) := by
                simpa [H₂Z] using! hshift
          _ = (powZ theta10Z 4).getD k 0 := by simp [shift1Fun]
          _ = (powFun theta10CoeffFun 4) k := hpow'
          _ = H2CoeffFun (Nat.succ k) := by simp [H2CoeffFun, shift1Fun]
  have hpowH2 (m : ℕ) : ∀ k ≤ n, (powZ H₂Z m).getD k 0 = (powFun H2CoeffFun m) k := by
    intro k hk
    have hk' : k < Ineq2GeOneCoeffs.N := lt_of_le_of_lt hk hn
    have := powZ_getD_eq_powFun_of_eqOn (aZ := H₂Z) (a := H2CoeffFun) (m := m) (n := k) hk' ?_
    · simpa using! this
    · intro j hj
      exact (hH2 j (le_trans hj hk))
  have hpowH4 (m : ℕ) : ∀ k ≤ n, (powZ H₄Z m).getD k 0 = (powFun H4CoeffFun m) k := by
    intro k hk
    have hk' : k < Ineq2GeOneCoeffs.N := lt_of_le_of_lt hk hn
    have := powZ_getD_eq_powFun_of_eqOn (aZ := H₄Z) (a := H4CoeffFun) (m := m) (n := k) hk' ?_
    · simpa using! this
    · intro j hj
      exact (hH4 j (le_trans hj hk))
  have hmul (aZ bZ : List ℤ) (a b : ℕ → ℤ) (ha : ∀ k ≤ n, aZ.getD k 0 = a k)
      (hb : ∀ k ≤ n, bZ.getD k 0 = b k) :
      (mulZ aZ bZ).getD n 0 = mulFun a b n := by
    simpa [mulFun] using!
      (mulZ_getD_eq_convZ_of_eqOn (aZ := aZ) (bZ := bZ) (a := a) (b := b) (n := n) hn ha hb)
  -- Now compute the coefficient at index `n` by rewriting each list operation into the
  -- corresponding
  -- coefficient-function operation.
  have hterm1 :
      (mulZ (powZ H₂Z 5) (powZ H₄Z 2)).getD n 0 =
        mulFun (powFun H2CoeffFun 5) (powFun H4CoeffFun 2) n := by
    refine hmul (aZ := powZ H₂Z 5) (bZ := powZ H₄Z 2) (a := powFun H2CoeffFun 5)
      (b := powFun H4CoeffFun 2) ?_ ?_
    · intro k hk; simpa using! (hpowH2 5 k hk)
    · intro k hk; simpa using! (hpowH4 2 k hk)
  have hterm2 :
      (mulZ (powZ H₂Z 6) H₄Z).getD n 0 =
        mulFun (powFun H2CoeffFun 6) H4CoeffFun n := by
    refine hmul (aZ := powZ H₂Z 6) (bZ := H₄Z) (a := powFun H2CoeffFun 6) (b := H4CoeffFun) ?_ ?_
    · intro k hk; simpa using! (hpowH2 6 k hk)
    · intro k hk; simpa using! (hH4 k hk)
  have hterm3 :
      (powZ H₂Z 7).getD n 0 = (powFun H2CoeffFun 7) n := by
    simpa using! (hpowH2 7 n (le_rfl))
  -- Expand the coefficient list at index `n`.
  have hcalc :
      psiSnumCoeffs_calc.getD n 0 =
        -(((7 : ℤ) * mulFun (powFun H2CoeffFun 5) (powFun H4CoeffFun 2) n +
            (7 : ℤ) * mulFun (powFun H2CoeffFun 6) H4CoeffFun n) +
          (2 : ℤ) * (powFun H2CoeffFun 7) n) := by
    -- Unfold the list construction and rewrite `getD` componentwise.
    dsimp [psiSnumCoeffs_calc, theta01Z, theta10Z, H₄Z, H₂Z]
    -- `getD` through `negZ` and the nested `addZ`.
    have hneg :
        (negZ
              (addZ
                (addZ
                  (smulZ 7 (mulZ (powZ H₂Z 5) (powZ H₄Z 2)))
                  (smulZ 7 (mulZ (powZ H₂Z 6) H₄Z)))
                (smulZ 2 (powZ H₂Z 7)))).getD n 0 =
          -((addZ
                (addZ
                  (smulZ 7 (mulZ (powZ H₂Z 5) (powZ H₄Z 2)))
                  (smulZ 7 (mulZ (powZ H₂Z 6) H₄Z)))
                (smulZ 2 (powZ H₂Z 7))).getD n 0) := by
      simpa using! (negZ_getD (a :=
        addZ
          (addZ
            (smulZ 7 (mulZ (powZ H₂Z 5) (powZ H₄Z 2)))
            (smulZ 7 (mulZ (powZ H₂Z 6) H₄Z)))
          (smulZ 2 (powZ H₂Z 7))) (n := n) hn)
    rw [hneg]
    have hadd1 :
        (addZ
              (addZ
                (smulZ 7 (mulZ (powZ H₂Z 5) (powZ H₄Z 2)))
                (smulZ 7 (mulZ (powZ H₂Z 6) H₄Z)))
              (smulZ 2 (powZ H₂Z 7))).getD n 0 =
          (addZ
                (smulZ 7 (mulZ (powZ H₂Z 5) (powZ H₄Z 2)))
                (smulZ 7 (mulZ (powZ H₂Z 6) H₄Z))).getD n 0 +
            (smulZ 2 (powZ H₂Z 7)).getD n 0 := by
      simpa using! (addZ_getD
        (a := addZ
          (smulZ 7 (mulZ (powZ H₂Z 5) (powZ H₄Z 2)))
          (smulZ 7 (mulZ (powZ H₂Z 6) H₄Z)))
        (b := smulZ 2 (powZ H₂Z 7)) (n := n) hn)
    rw [hadd1]
    have hadd2 :
        (addZ
              (smulZ 7 (mulZ (powZ H₂Z 5) (powZ H₄Z 2)))
              (smulZ 7 (mulZ (powZ H₂Z 6) H₄Z))).getD n 0 =
          (smulZ 7 (mulZ (powZ H₂Z 5) (powZ H₄Z 2))).getD n 0 +
            (smulZ 7 (mulZ (powZ H₂Z 6) H₄Z)).getD n 0 :=
      addZ_getD (smulZ 7 (mulZ (powZ H₂Z 5) (powZ H₄Z 2))) (smulZ 7 (mulZ (powZ H₂Z 6) H₄Z)) hn
    rw [hadd2]
    -- Push `getD` through the scalar multiplications.
    have hsmul1 :
        (smulZ 7 (mulZ (powZ H₂Z 5) (powZ H₄Z 2))).getD n 0 =
          (7 : ℤ) * (mulZ (powZ H₂Z 5) (powZ H₄Z 2)).getD n 0 := by
      simpa using! (smulZ_getD (c := 7) (a := mulZ (powZ H₂Z 5) (powZ H₄Z 2)) (n := n) hn)
    have hsmul2 :
        (smulZ 7 (mulZ (powZ H₂Z 6) H₄Z)).getD n 0 =
          (7 : ℤ) * (mulZ (powZ H₂Z 6) H₄Z).getD n 0 := by
      simpa using! (smulZ_getD (c := 7) (a := mulZ (powZ H₂Z 6) H₄Z) (n := n) hn)
    have hsmul3 :
        (smulZ 2 (powZ H₂Z 7)).getD n 0 =
          (2 : ℤ) * (powZ H₂Z 7).getD n 0 := by
      simpa using! (smulZ_getD (c := 2) (a := powZ H₂Z 7) (n := n) hn)
    rw [hsmul1, hsmul2, hsmul3]
    -- Substitute the identified coefficients.
    rw [hterm1, hterm2, hterm3]
    -- Goal is now definitional.
  -- Unfold the coefficient-function definition at `n`.
  -- The only nontrivial parts are the `mulFun`/`powFun` terms, already identified above.
  simpa [psiSnumCoeffFun, negFun, addFun, smulFun, mulFun, add_assoc] using! hcalc
end SpherePacking.Dim24.Ineq2PsiSnum
