/- Matching `psiCoeffFun` against the truncated coefficient list. -/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingCoeffs
public import
SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiCoeffFunAndTail.PsiCoeffFun
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiRSeriesSetup.SparseCoeffs

/-!
### Matching `psiCoeffFun` against `BleadingCoeffs.psiInumCoeffs`

`Bleading_exact_trunc` uses the integer list `BleadingCoeffs.psiInumCoeffs` coming from the PARI/GP
truncation procedure. To connect it to the analytic `r`-series expansion of `ψI_num`, we show that
our convolution-built dense coefficient function `psiCoeffFun` agrees with `getD` of that list on
indices `< N = 100`.
-/

open scoped BigOperators

noncomputable section

namespace SpherePacking.Dim24.AppendixA


lemma convZ_congr_left_of_eq_on_le (a a' b : ℕ → ℤ) (n : ℕ)
    (h : ∀ m ≤ n, a m = a' m) :
    convZ a b n = convZ a' b n := by
  dsimp [convZ]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  simp [h _ (Nat.le_of_lt_succ (Finset.Nat.antidiagonal.fst_lt hp))]

lemma convZ_congr_right_of_eq_on_le (a b b' : ℕ → ℤ) (n : ℕ)
    (h : ∀ m ≤ n, b m = b' m) :
    convZ a b n = convZ a b' n := by
  dsimp [convZ]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  simp [h _ (Nat.le_of_lt_succ (Finset.Nat.antidiagonal.snd_lt hp))]

lemma powConvZ_congr_of_eq_on_le (a a' : ℕ → ℤ) :
    ∀ k n : ℕ, (∀ m ≤ n, a m = a' m) → powConvZ a k n = powConvZ a' k n
  | 0, n, _h => by simp [powConvZ]
  | Nat.succ k, n, h => by
      dsimp [powConvZ]
      refine (convZ_congr_left_of_eq_on_le (a := a) (a' := a') (b := powConvZ a k) n h).trans ?_
      refine convZ_congr_right_of_eq_on_le (a := a') (b := powConvZ a k) (b' := powConvZ a' k) n ?_
      intro m hm
      exact powConvZ_congr_of_eq_on_le a a' k m (fun j hj => h j (le_trans hj hm))

lemma coeffZ_ofFn (f : Fin BleadingCoeffs.N → ℤ) (i : Fin BleadingCoeffs.N) :
    BleadingCoeffs.coeffZ (List.ofFn f) i.1 = f i := by
  dsimp [BleadingCoeffs.coeffZ]
  have hpos : i.1 < (List.ofFn f).length :=
    lt_of_lt_of_eq i.2 (Eq.symm (List.length_ofFn (f := f)))
  rw [List.getD_eq_getElem (l := List.ofFn f) (d := (0 : ℤ)) hpos]
  exact List.getElem_ofFn hpos

lemma coeffZ_ofFn_lt (f : Fin BleadingCoeffs.N → ℤ) (n : ℕ) (hn : n < BleadingCoeffs.N) :
    BleadingCoeffs.coeffZ (List.ofFn f) n = f ⟨n, hn⟩ := by
  exact coeffZ_ofFn (f := f) ⟨n, hn⟩

lemma coeffZ_addZ_lt (a b : List ℤ) (n : ℕ) (hn : n < BleadingCoeffs.N) :
    BleadingCoeffs.coeffZ (BleadingCoeffs.addZ a b) n =
      BleadingCoeffs.coeffZ a n + BleadingCoeffs.coeffZ b n := by
  unfold BleadingCoeffs.addZ
  exact
    coeffZ_ofFn
      (f := fun i : Fin BleadingCoeffs.N =>
        BleadingCoeffs.coeffZ a i.1 + BleadingCoeffs.coeffZ b i.1)
      ⟨n, hn⟩

lemma coeffZ_negZ_lt (a : List ℤ) (n : ℕ) (hn : n < BleadingCoeffs.N) :
    BleadingCoeffs.coeffZ (BleadingCoeffs.negZ a) n = -BleadingCoeffs.coeffZ a n := by
  unfold BleadingCoeffs.negZ
  exact coeffZ_ofFn (f := fun i : Fin BleadingCoeffs.N => -BleadingCoeffs.coeffZ a i.1) ⟨n, hn⟩

lemma coeffZ_smulZ_lt (c : ℤ) (a : List ℤ) (n : ℕ) (hn : n < BleadingCoeffs.N) :
    BleadingCoeffs.coeffZ (BleadingCoeffs.smulZ c a) n = c * BleadingCoeffs.coeffZ a n := by
  unfold BleadingCoeffs.smulZ
  exact coeffZ_ofFn (f := fun i : Fin BleadingCoeffs.N => c * BleadingCoeffs.coeffZ a i.1) ⟨n, hn⟩

lemma coeffZ_mulZ_lt (a b : List ℤ) (n : ℕ) (hn : n < BleadingCoeffs.N) :
    BleadingCoeffs.coeffZ (BleadingCoeffs.mulZ a b) n =
      Finset.sum (Finset.range (n + 1)) fun j =>
        BleadingCoeffs.coeffZ a j * BleadingCoeffs.coeffZ b (n - j) := by
  unfold BleadingCoeffs.mulZ
  exact
    coeffZ_ofFn_lt
      (f := fun i : Fin BleadingCoeffs.N =>
        Finset.sum (Finset.range (i.1 + 1)) fun j =>
          BleadingCoeffs.coeffZ a j * BleadingCoeffs.coeffZ b (i.1 - j))
      (n := n) hn

lemma coeffZ_mulZ_lt_convZ (a b : List ℤ) (n : ℕ) (hn : n < BleadingCoeffs.N) :
    BleadingCoeffs.coeffZ (BleadingCoeffs.mulZ a b) n =
      convZ (fun k => BleadingCoeffs.coeffZ a k) (fun k => BleadingCoeffs.coeffZ b k) n := by
  rw [coeffZ_mulZ_lt (a := a) (b := b) (n := n) hn]
  symm
  simpa [convZ, Finset.Nat.sum_antidiagonal_eq_sum_range_succ, Nat.succ_eq_add_one] using!
    (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun i j => BleadingCoeffs.coeffZ a i * BleadingCoeffs.coeffZ b j) n)

lemma coeffZ_shift1Z_lt (a : List ℤ) (n : ℕ) (hn : n < BleadingCoeffs.N) :
    BleadingCoeffs.coeffZ (BleadingCoeffs.shift1Z a) n =
      match n with
      | 0 => 0
      | m + 1 => BleadingCoeffs.coeffZ a m := by
  let f : Fin BleadingCoeffs.N → ℤ := fun i =>
    match i.1 with
    | 0 => 0
    | m + 1 => BleadingCoeffs.coeffZ a m
  cases n with
  | zero =>
      unfold BleadingCoeffs.shift1Z
      exact coeffZ_ofFn_lt (f := f) (n := 0) hn
  | succ n =>
      unfold BleadingCoeffs.shift1Z
      exact coeffZ_ofFn_lt (f := f) (n := Nat.succ n) hn

lemma coeffZ_powZ_lt (a : List ℤ) :
    ∀ k : ℕ, ∀ n : ℕ, n < BleadingCoeffs.N →
      BleadingCoeffs.coeffZ (BleadingCoeffs.powZ a k) n =
        powConvZ (fun i => BleadingCoeffs.coeffZ a i) k n
  | 0, n, hn => by
      simpa [BleadingCoeffs.powZ, powConvZ, oneCoeffFun] using!
        (coeffZ_ofFn_lt
          (f := fun i : Fin BleadingCoeffs.N => if i.1 = 0 then (1 : ℤ) else 0)
          (n := n) hn)
  | Nat.succ k, n, hn => by
      have hmul :
          BleadingCoeffs.coeffZ (BleadingCoeffs.powZ a (Nat.succ k)) n =
            convZ
              (fun i => BleadingCoeffs.coeffZ a i)
              (fun i => BleadingCoeffs.coeffZ (BleadingCoeffs.powZ a k) i)
              n := by
        simpa [BleadingCoeffs.powZ] using!
          (coeffZ_mulZ_lt_convZ (a := a) (b := BleadingCoeffs.powZ a k) (n := n) hn)
      have hEq :
          ∀ m ≤ n,
            BleadingCoeffs.coeffZ (BleadingCoeffs.powZ a k) m =
              powConvZ (fun i => BleadingCoeffs.coeffZ a i) k m := by
        intro m hm
        have hm' : m < BleadingCoeffs.N := lt_of_le_of_lt hm hn
        simpa using! (coeffZ_powZ_lt a k m hm')
      have hconv :=
        convZ_congr_right_of_eq_on_le
          (a := fun i => BleadingCoeffs.coeffZ a i)
          (b := fun i => BleadingCoeffs.coeffZ (BleadingCoeffs.powZ a k) i)
          (b' := fun i => powConvZ (fun j => BleadingCoeffs.coeffZ a j) k i)
          n hEq
      simpa [powConvZ] using! (hmul.trans hconv)

private lemma sum_range_eq_sum_range_of_forall_ge_min_eq_zero (f : ℕ → ℤ) (n m : ℕ)
    (h : ∀ k, Nat.min n m ≤ k → f k = 0) :
    Finset.sum (Finset.range n) f = Finset.sum (Finset.range m) f := by
  cases le_total n m with
  | inl hnm =>
      have hsub : Finset.range n ⊆ Finset.range m := (Finset.range_subset_range).2 hnm
      refine Finset.sum_subset hsub ?_
      intro k hk hknot
      have hnle : n ≤ k := le_of_not_gt (by simpa [Finset.mem_range] using! hknot)
      have : Nat.min n m ≤ k := by simpa [Nat.min_eq_left hnm] using! hnle
      exact h k this
  | inr hmn =>
      have hsub : Finset.range m ⊆ Finset.range n := (Finset.range_subset_range).2 hmn
      have hsum :
          Finset.sum (Finset.range m) f = Finset.sum (Finset.range n) f := by
        refine Finset.sum_subset hsub ?_
        intro k hk hknot
        have hmle : m ≤ k := le_of_not_gt (by simpa [Finset.mem_range] using! hknot)
        have : Nat.min n m ≤ k := by simpa [Nat.min_eq_right hmn] using! hmle
        exact h k this
      simpa using! hsum.symm

lemma theta01CoeffFun_eq_theta01Coeff_cutoff (n : ℕ) (hn : n < BleadingCoeffs.N) :
    theta01CoeffFun n = BleadingCoeffs.theta01Coeff BleadingCoeffs.thetaCutoff n := by
  -- For `n < 100`, only indices `k ≤ 10` can contribute (`11^2 > 99`).
  set f : ℕ → ℤ := fun k =>
    if k ^ (2 : ℕ) = n then (if k = 0 then (1 : ℤ) else 2 * ((-1 : ℤ) ^ k)) else 0
  have hf_large : ∀ k : ℕ, 11 ≤ k → f k = 0 := by
    intro k hk
    have hk2 : n < k ^ (2 : ℕ) := by
      have h121 : (121 : ℕ) ≤ k ^ (2 : ℕ) := by
        have : (11 : ℕ) ^ (2 : ℕ) ≤ k ^ (2 : ℕ) :=
          pow_le_pow_left' hk 2
        simpa using! this
      have hn121 : n < (121 : ℕ) := lt_trans hn (by decide)
      exact lt_of_lt_of_le hn121 h121
    have : k ^ (2 : ℕ) ≠ n := ne_of_gt hk2
    simp [f, this]
  have hf_n : ∀ k : ℕ, n + 1 ≤ k → f k = 0 := by
    intro k hk
    have hkn : n < k := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hk
    have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le n) hkn
    have hk2 : n < k ^ (2 : ℕ) := by
      have hk_le : k ≤ k ^ (2 : ℕ) := by
        simpa [pow_two] using! (Nat.le_mul_of_pos_right k hkpos)
      exact lt_of_lt_of_le hkn hk_le
    have : k ^ (2 : ℕ) ≠ n := ne_of_gt hk2
    simp [f, this]
  have hcut : BleadingCoeffs.thetaCutoff + 1 = 11 := by
    norm_num [BleadingCoeffs.thetaCutoff]
  have hf_min : ∀ k : ℕ, Nat.min (n + 1) (BleadingCoeffs.thetaCutoff + 1) ≤ k → f k = 0 := by
    intro k hk
    cases le_total (n + 1) (BleadingCoeffs.thetaCutoff + 1) with
    | inl h =>
        have : n + 1 ≤ k := by simpa [Nat.min_eq_left h] using! hk
        exact hf_n k this
    | inr h =>
        have : BleadingCoeffs.thetaCutoff + 1 ≤ k := by simpa [Nat.min_eq_right h] using! hk
        have : 11 ≤ k := by simpa [hcut] using! this
        exact hf_large k this
  have hsum :
      (∑ k ∈ Finset.range (n + 1), f k) =
        ∑ k ∈ Finset.range (BleadingCoeffs.thetaCutoff + 1), f k := by
    simpa using!
      (sum_range_eq_sum_range_of_forall_ge_min_eq_zero f (n + 1) (BleadingCoeffs.thetaCutoff + 1)
        hf_min)
  simpa [theta01CoeffFun, BleadingCoeffs.theta01Coeff, f] using! hsum

lemma theta10CoeffFun_eq_theta10Coeff_cutoff (n : ℕ) (hn : n < BleadingCoeffs.N) :
    theta10CoeffFun n = BleadingCoeffs.theta10Coeff BleadingCoeffs.thetaCutoff n := by
  set f : ℕ → ℤ := fun k => if k * (k + 1) = n then (2 : ℤ) else 0
  have hf_large : ∀ k : ℕ, 11 ≤ k → f k = 0 := by
    intro k hk
    have hk2 : n < k * (k + 1) := by
      have h132 : (132 : ℕ) ≤ k * (k + 1) := by
        have hk' : (11 : ℕ) ≤ k := hk
        have hk1' : (12 : ℕ) ≤ k + 1 := Nat.succ_le_succ hk'
        have : (11 : ℕ) * (12 : ℕ) ≤ k * (k + 1) := Nat.mul_le_mul hk' hk1'
        simpa using! this
      have hn132 : n < (132 : ℕ) := lt_trans hn (by decide)
      exact lt_of_lt_of_le hn132 h132
    have : k * (k + 1) ≠ n := ne_of_gt hk2
    simp [f, this]
  have hf_n : ∀ k : ℕ, n + 1 ≤ k → f k = 0 := by
    intro k hk
    have hkn : n < k := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hk
    have hkprod : n < k * (k + 1) := by
      have hkpos : 0 < k + 1 := Nat.succ_pos k
      exact lt_of_lt_of_le hkn (Nat.le_mul_of_pos_right k hkpos)
    have : k * (k + 1) ≠ n := ne_of_gt hkprod
    simp [f, this]
  have hcut : BleadingCoeffs.thetaCutoff + 1 = 11 := by
    norm_num [BleadingCoeffs.thetaCutoff]
  have hf_min : ∀ k : ℕ, Nat.min (n + 1) (BleadingCoeffs.thetaCutoff + 1) ≤ k → f k = 0 := by
    intro k hk
    cases le_total (n + 1) (BleadingCoeffs.thetaCutoff + 1) with
    | inl h =>
        have : n + 1 ≤ k := by simpa [Nat.min_eq_left h] using! hk
        exact hf_n k this
    | inr h =>
        have : BleadingCoeffs.thetaCutoff + 1 ≤ k := by simpa [Nat.min_eq_right h] using! hk
        have : 11 ≤ k := by simpa [hcut] using! this
        exact hf_large k this
  have hsum :
      (∑ k ∈ Finset.range (n + 1), f k) =
        ∑ k ∈ Finset.range (BleadingCoeffs.thetaCutoff + 1), f k := by
    simpa using!
      (sum_range_eq_sum_range_of_forall_ge_min_eq_zero f (n + 1) (BleadingCoeffs.thetaCutoff + 1)
        hf_min)
  simpa [theta10CoeffFun, BleadingCoeffs.theta10Coeff, f] using! hsum

/-- For `n < N`, the dense coefficient function `psiCoeffFun` matches
`BleadingCoeffs.psiInumCoeffs.getD n 0`. -/
public lemma psiCoeffFun_eq_psiInumCoeffs_getD (n : ℕ) (hn : n < BleadingCoeffs.N) :
    psiCoeffFun n = BleadingCoeffs.psiInumCoeffs.getD n 0 := by
  -- Work with the cutoff `M = 10`.
  set M : ℕ := BleadingCoeffs.thetaCutoff
  -- Coefficient functions extracted from the truncated lists.
  let a01 : ℕ → ℤ := fun m => BleadingCoeffs.coeffZ (BleadingCoeffs.theta01Z M) m
  let a10 : ℕ → ℤ := fun m => BleadingCoeffs.coeffZ (BleadingCoeffs.theta10Z M) m
  have ha01 : ∀ m ≤ n, a01 m = theta01CoeffFun m := by
    intro m hm
    have hm' : m < BleadingCoeffs.N := lt_of_le_of_lt hm hn
    have hlist :
        BleadingCoeffs.coeffZ (BleadingCoeffs.theta01Z M) m = BleadingCoeffs.theta01Coeff M m := by
      unfold BleadingCoeffs.theta01Z
      exact
        coeffZ_ofFn_lt
          (f := fun i : Fin BleadingCoeffs.N => BleadingCoeffs.theta01Coeff M i.1)
          (n := m) hm'
    have hfun : theta01CoeffFun m = BleadingCoeffs.theta01Coeff M m :=
      theta01CoeffFun_eq_theta01Coeff_cutoff (n := m) (hn := hm')
    simpa [a01] using! (hlist.trans hfun.symm)
  have ha10 : ∀ m ≤ n, a10 m = theta10CoeffFun m := by
    intro m hm
    have hm' : m < BleadingCoeffs.N := lt_of_le_of_lt hm hn
    have hlist :
        BleadingCoeffs.coeffZ (BleadingCoeffs.theta10Z M) m = BleadingCoeffs.theta10Coeff M m := by
      unfold BleadingCoeffs.theta10Z
      exact
        coeffZ_ofFn_lt
          (f := fun i : Fin BleadingCoeffs.N => BleadingCoeffs.theta10Coeff M i.1)
          (n := m) hm'
    have hfun : theta10CoeffFun m = BleadingCoeffs.theta10Coeff M m :=
      theta10CoeffFun_eq_theta10Coeff_cutoff (n := m) (hn := hm')
    simpa [a10] using! (hlist.trans hfun.symm)
  -- Compare the list-side `H₄Z/H₂Z` coefficient functions to the dense
  -- `powConvZ/shift1Fun` ones.
  have hH4 :
      BleadingCoeffs.coeffZ (BleadingCoeffs.H₄Z M) n = powConvZ theta01CoeffFun 4 n := by
    have hpow :
        BleadingCoeffs.coeffZ (BleadingCoeffs.H₄Z M) n = powConvZ a01 4 n := by
      -- `H₄Z M = powZ (theta01Z M) 4`.
      simpa [BleadingCoeffs.H₄Z, a01, M] using!
        (coeffZ_powZ_lt (a := BleadingCoeffs.theta01Z M) 4 n hn)
    have hcongr :
        powConvZ a01 4 n = powConvZ theta01CoeffFun 4 n :=
      powConvZ_congr_of_eq_on_le a01 theta01CoeffFun 4 n ha01
    simpa [a01] using! hpow.trans hcongr
  have hH2 :
      BleadingCoeffs.coeffZ (BleadingCoeffs.H₂Z M) n =
        shift1Fun (powConvZ theta10CoeffFun 4) n := by
    cases n with
    | zero =>
        -- `H₂Z` is `shift1Z ...`, so the `0`-th coefficient is `0`.
        rfl
    | succ n =>
        have hn0 : n < BleadingCoeffs.N := Nat.lt_of_succ_lt hn
        have hshift :
            BleadingCoeffs.coeffZ (BleadingCoeffs.H₂Z M) (Nat.succ n) =
              BleadingCoeffs.coeffZ (BleadingCoeffs.powZ (BleadingCoeffs.theta10Z M) 4) n := by
          simpa [BleadingCoeffs.H₂Z, M] using!
            (coeffZ_shift1Z_lt
              (a := BleadingCoeffs.powZ (BleadingCoeffs.theta10Z M) 4)
              (Nat.succ n)
              (by simpa using! hn))
        have hpow :
            BleadingCoeffs.coeffZ (BleadingCoeffs.powZ (BleadingCoeffs.theta10Z M) 4) n =
              powConvZ a10 4 n := by
          simpa [a10] using! (coeffZ_powZ_lt (a := BleadingCoeffs.theta10Z M) 4 n hn0)
        have hcongr :
            powConvZ a10 4 n = powConvZ theta10CoeffFun 4 n :=
          powConvZ_congr_of_eq_on_le a10 theta10CoeffFun 4 n (fun m hm =>
            ha10 m (le_trans hm (Nat.le_succ n)))
        simpa [shift1Fun, hpow.trans hcongr] using! hshift
  -- Now expand the list-side expression for `psiInumZ` at coefficient `n`.
  have hpsiList :
      BleadingCoeffs.coeffZ (BleadingCoeffs.psiInumCoeffs) n = psiCoeffFun n := by
    -- Unfold `psiInumCoeffs = psiInumZ thetaCutoff` and push `coeffZ` through the list operations.
    -- Each step is justified on indices `< N` by the lemmas above.
    have hn' : n < BleadingCoeffs.N := hn
    -- Local abbreviations matching the definition of `psiCoeffFun`.
    let h4 : ℕ → ℤ := powConvZ theta01CoeffFun 4
    let h2base : ℕ → ℤ := powConvZ theta10CoeffFun 4
    let h2 : ℕ → ℤ := shift1Fun h2base
    -- Replace the `H₄Z/H₂Z` coefficient functions by `h4/h2` on indices `≤ n`.
    have hH4fun :
        ∀ m ≤ n, BleadingCoeffs.coeffZ (BleadingCoeffs.H₄Z M) m = h4 m := by
      intro m hm
      have hm' : m < BleadingCoeffs.N := lt_of_le_of_lt hm hn
      have hH4m :
          BleadingCoeffs.coeffZ (BleadingCoeffs.H₄Z M) m = powConvZ theta01CoeffFun 4 m := by
        have hpowm :
            BleadingCoeffs.coeffZ (BleadingCoeffs.H₄Z M) m = powConvZ a01 4 m := by
          simpa [BleadingCoeffs.H₄Z, a01, M] using!
            (coeffZ_powZ_lt (a := BleadingCoeffs.theta01Z M) 4 m hm')
        have hcongrm :
            powConvZ a01 4 m = powConvZ theta01CoeffFun 4 m :=
          powConvZ_congr_of_eq_on_le a01 theta01CoeffFun 4 m (fun j hj =>
            ha01 j (le_trans hj hm))
        simpa [h4, a01] using! hpowm.trans hcongrm
      simpa [h4] using! hH4m
    have hH2fun :
        ∀ m ≤ n, BleadingCoeffs.coeffZ (BleadingCoeffs.H₂Z M) m = h2 m := by
      intro m hm
      have hm' : m < BleadingCoeffs.N := lt_of_le_of_lt hm hn
      cases m with
      | zero =>
          rfl
      | succ m =>
          have hm0 : m < BleadingCoeffs.N := Nat.lt_of_succ_lt hm'
          have hshift :
              BleadingCoeffs.coeffZ (BleadingCoeffs.H₂Z M) (Nat.succ m) =
                BleadingCoeffs.coeffZ (BleadingCoeffs.powZ (BleadingCoeffs.theta10Z M) 4) m := by
            simpa [BleadingCoeffs.H₂Z, M] using!
              (coeffZ_shift1Z_lt
                (a := BleadingCoeffs.powZ (BleadingCoeffs.theta10Z M) 4)
                (Nat.succ m)
                (by simpa using! hm'))
          have hpow :
              BleadingCoeffs.coeffZ (BleadingCoeffs.powZ (BleadingCoeffs.theta10Z M) 4) m =
                powConvZ a10 4 m := by
            simpa [a10] using! (coeffZ_powZ_lt (a := BleadingCoeffs.theta10Z M) 4 m hm0)
          have hcongr :
              powConvZ a10 4 m = powConvZ theta10CoeffFun 4 m :=
            powConvZ_congr_of_eq_on_le a10 theta10CoeffFun 4 m (fun j hj =>
              ha10 j (le_trans hj (le_trans (Nat.le_succ m) hm)))
          have : BleadingCoeffs.coeffZ (BleadingCoeffs.H₂Z M) (Nat.succ m) =
              shift1Fun (powConvZ theta10CoeffFun 4) (Nat.succ m) := by
            -- `shift1Fun` drops the index by one.
            have :
                BleadingCoeffs.coeffZ (BleadingCoeffs.H₂Z M) (Nat.succ m) =
                  powConvZ theta10CoeffFun 4 m :=
              hshift.trans (hpow.trans hcongr)
            simpa [shift1Fun] using! this
          simpa [h2, h2base] using! this
    -- Turn `powZ` into `powConvZ` and then use the congruence lemma to rewrite the base functions.
    have hpowH4fun (k : ℕ) :
        ∀ m ≤ n,
          BleadingCoeffs.coeffZ (BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) k) m =
            powConvZ h4 k m := by
      intro m hm
      have hm' : m < BleadingCoeffs.N := lt_of_le_of_lt hm hn
      have h0 := coeffZ_powZ_lt (a := (BleadingCoeffs.H₄Z M)) k m hm'
      have hcongr :=
        powConvZ_congr_of_eq_on_le
          (fun j => BleadingCoeffs.coeffZ (BleadingCoeffs.H₄Z M) j)
          h4 k m
          (fun j hj => hH4fun j (le_trans hj hm))
      exact h0.trans hcongr
    have hpowH2fun (k : ℕ) :
        ∀ m ≤ n,
          BleadingCoeffs.coeffZ (BleadingCoeffs.powZ (BleadingCoeffs.H₂Z M) k) m =
            powConvZ h2 k m := by
      intro m hm
      have hm' : m < BleadingCoeffs.N := lt_of_le_of_lt hm hn
      have h0 := coeffZ_powZ_lt (a := (BleadingCoeffs.H₂Z M)) k m hm'
      have hcongr :=
        powConvZ_congr_of_eq_on_le
          (fun j => BleadingCoeffs.coeffZ (BleadingCoeffs.H₂Z M) j)
          h2 k m
          (fun j hj => hH2fun j (le_trans hj hm))
      exact h0.trans hcongr
    -- Finally, compute the coefficient using the `addZ/smulZ/mulZ` lemmas.
    have hmul1 :
        BleadingCoeffs.coeffZ
            (BleadingCoeffs.mulZ
              (BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 5)
              (BleadingCoeffs.powZ (BleadingCoeffs.H₂Z M) 2))
            n
          =
          convZ (powConvZ h4 5) (powConvZ h2 2) n := by
      -- Convert `mulZ` to `convZ`, then rewrite the two factors to `powConvZ`.
      have hmul :=
        (coeffZ_mulZ_lt_convZ (a := BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 5)
          (b := BleadingCoeffs.powZ (BleadingCoeffs.H₂Z M) 2) (n := n) hn')
      -- Rewrite both coefficient functions on indices `≤ n`.
      have hA : ∀ m ≤ n,
          BleadingCoeffs.coeffZ (BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 5) m =
            powConvZ h4 5 m := by
        intro m hm
        exact hpowH4fun 5 m hm
      have hB : ∀ m ≤ n,
          BleadingCoeffs.coeffZ (BleadingCoeffs.powZ (BleadingCoeffs.H₂Z M) 2) m =
            powConvZ h2 2 m := by
        intro m hm
        exact hpowH2fun 2 m hm
      -- Apply `convZ` congruence on both sides.
      have hconvA :
          convZ (fun k => BleadingCoeffs.coeffZ (BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 5) k)
              (fun k => BleadingCoeffs.coeffZ (BleadingCoeffs.powZ (BleadingCoeffs.H₂Z M) 2) k)
              n =
            convZ (powConvZ h4 5)
              (fun k => BleadingCoeffs.coeffZ (BleadingCoeffs.powZ (BleadingCoeffs.H₂Z M) 2) k)
              n :=
        convZ_congr_left_of_eq_on_le _ _ _ n hA
      have hconvB :
          convZ (powConvZ h4 5)
              (fun k => BleadingCoeffs.coeffZ (BleadingCoeffs.powZ (BleadingCoeffs.H₂Z M) 2) k)
              n =
            convZ (powConvZ h4 5) (powConvZ h2 2) n :=
        convZ_congr_right_of_eq_on_le _ _ _ n hB
      simpa using! (hmul.trans (hconvA.trans hconvB))
    have hmul2 :
        BleadingCoeffs.coeffZ
            (BleadingCoeffs.mulZ
              (BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 6)
              (BleadingCoeffs.H₂Z M))
            n
          =
          convZ (powConvZ h4 6) (powConvZ h2 1) n := by
      have hmul :=
        (coeffZ_mulZ_lt_convZ (a := BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 6)
          (b := BleadingCoeffs.H₂Z M) (n := n) hn')
      have hA : ∀ m ≤ n,
          BleadingCoeffs.coeffZ (BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 6) m =
            powConvZ h4 6 m := by
        intro m hm
        exact hpowH4fun 6 m hm
      have hB : ∀ m ≤ n, BleadingCoeffs.coeffZ (BleadingCoeffs.H₂Z M) m = h2 m := hH2fun
      have hconvA :
          convZ (fun k => BleadingCoeffs.coeffZ (BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 6) k)
              (fun k => BleadingCoeffs.coeffZ (BleadingCoeffs.H₂Z M) k) n =
            convZ (powConvZ h4 6) (fun k => BleadingCoeffs.coeffZ (BleadingCoeffs.H₂Z M) k) n :=
        convZ_congr_left_of_eq_on_le _ _ _ n hA
      have hconvB :
          convZ (powConvZ h4 6) (fun k => BleadingCoeffs.coeffZ (BleadingCoeffs.H₂Z M) k) n =
            convZ (powConvZ h4 6) h2 n :=
        convZ_congr_right_of_eq_on_le _ _ _ n hB
      -- `powConvZ h2 1 = h2`.
      simpa [powConvZ_one (a := h2)] using! (hmul.trans (hconvA.trans hconvB))
    have hpow7 :
        BleadingCoeffs.coeffZ (BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 7) n =
          powConvZ h4 7 n := by
      simpa using! (hpowH4fun 7 n le_rfl)
    -- Assemble `psiInumZ` at coefficient `n`.
    have hpsi :
        BleadingCoeffs.coeffZ (BleadingCoeffs.psiInumZ M) n = psiCoeffFun n := by
      -- Expand the list expression coefficientwise.
      have hadd1 :=
        coeffZ_addZ_lt
          (a := BleadingCoeffs.addZ
            (BleadingCoeffs.smulZ 7
              (BleadingCoeffs.mulZ
                (BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 5)
                (BleadingCoeffs.powZ (BleadingCoeffs.H₂Z M) 2)))
            (BleadingCoeffs.smulZ 7
              (BleadingCoeffs.mulZ
                (BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 6)
                (BleadingCoeffs.H₂Z M))))
          (b := BleadingCoeffs.smulZ 2 (BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 7))
          (n := n) hn'
      have hadd2 :=
        coeffZ_addZ_lt
          (a := BleadingCoeffs.smulZ 7
            (BleadingCoeffs.mulZ
              (BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 5)
              (BleadingCoeffs.powZ (BleadingCoeffs.H₂Z M) 2)))
          (b := BleadingCoeffs.smulZ 7
            (BleadingCoeffs.mulZ
              (BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 6)
              (BleadingCoeffs.H₂Z M)))
          (n := n) hn'
      have hsmul1 :=
        coeffZ_smulZ_lt (c := (7 : ℤ))
          (a := BleadingCoeffs.mulZ
            (BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 5)
            (BleadingCoeffs.powZ (BleadingCoeffs.H₂Z M) 2))
          (n := n) hn'
      have hsmul2 :=
        coeffZ_smulZ_lt (c := (7 : ℤ))
          (a := BleadingCoeffs.mulZ
            (BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 6)
            (BleadingCoeffs.H₂Z M))
          (n := n) hn'
      have hsmul3 :=
        coeffZ_smulZ_lt (c := (2 : ℤ))
          (a := BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 7)
          (n := n) hn'
      -- Put everything together and rewrite into `psiCoeffFun`.
      -- We keep the rewriting local to avoid a large `simp` normalization.
      calc
        BleadingCoeffs.coeffZ (BleadingCoeffs.psiInumZ M) n
            =
              BleadingCoeffs.coeffZ
                (BleadingCoeffs.addZ
                  (BleadingCoeffs.addZ
                    (BleadingCoeffs.smulZ 7
                      (BleadingCoeffs.mulZ
                        (BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 5)
                        (BleadingCoeffs.powZ (BleadingCoeffs.H₂Z M) 2)))
                    (BleadingCoeffs.smulZ 7
                      (BleadingCoeffs.mulZ
                        (BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 6)
                        (BleadingCoeffs.H₂Z M))))
                  (BleadingCoeffs.smulZ 2 (BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 7)))
                n := by
              rfl
        _ =
            (7 * BleadingCoeffs.coeffZ
                (BleadingCoeffs.mulZ
                  (BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 5)
                  (BleadingCoeffs.powZ (BleadingCoeffs.H₂Z M) 2))
                n +
              (7 * BleadingCoeffs.coeffZ
                  (BleadingCoeffs.mulZ
                    (BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 6)
                    (BleadingCoeffs.H₂Z M))
                  n)) +
              (2 * BleadingCoeffs.coeffZ (BleadingCoeffs.powZ (BleadingCoeffs.H₄Z M) 7) n) := by
              -- Use the coefficient lemmas for `addZ` and `smulZ`.
              -- The internal associativity is handled by `simp`.
              simp [hadd1, hadd2, hsmul1, hsmul2, hsmul3, add_assoc]
        _ =
            (7 * convZ (powConvZ h4 5) (powConvZ h2 2) n +
                (7 * convZ (powConvZ h4 6) (powConvZ h2 1) n)) +
              (2 * powConvZ h4 7 n) := by
              -- Rewrite the inner coefficients via `hmul1/hmul2/hpow7`.
              simp [hmul1, hmul2, hpow7]
        _ = psiCoeffFun n := by
              simp [psiCoeffFun, h4, h2, h2base]
    -- `psiInumCoeffs = psiInumZ thetaCutoff`.
    simpa [BleadingCoeffs.psiInumCoeffs, M] using! hpsi
  -- `coeffZ` is `getD`, so `hpsiList` is exactly the desired statement.
  simpa [BleadingCoeffs.coeffZ] using! hpsiList.symm


end SpherePacking.Dim24.AppendixA
