-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Dn.Basic

/-!
# BS81 Lemma 18(iii) in the root lattice `Dₙ`

We count minimal vectors `w ∈ minVecDn` satisfying `⟪g1, w⟫ = 2` and `⟪g2, w⟫ = 2`, where
`g1,g2` are the two special vectors from BS81 (equation (15)).

Solutions are exactly `√2 e_0 ± √2 e_k` with `k ∈ {2,3,...,n-1}`, giving `2 * (n - 2) = 2 * n - 4`.

## Main definitions
* `g1`
* `g2`

## Main statement
* `ncard_minVecDn_inner_g1_g2_eq_two`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Dn
noncomputable section

open scoped RealInnerProductSpace

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- A concrete choice of the two special vectors `g1,g2` in BS81 (equation (15)). -/
public def g1 (hn : 2 ≤ n) : ℝⁿ :=
  Real.sqrt 2 • (eStd (n := n) ⟨0, by
    -- `0 < n` follows from `2 ≤ n`.
    exact lt_of_lt_of_le Nat.zero_lt_two hn⟩ +
    eStd (n := n) ⟨1, by
      -- `1 < n` follows from `1 < 2 ≤ n`.
      exact lt_of_lt_of_le (by decide : 1 < 2) hn⟩)

/-- The second special vector `g2` from BS81 (equation (15)). -/
public def g2 (hn : 2 ≤ n) : ℝⁿ :=
  Real.sqrt 2 • (eStd (n := n) ⟨0,
    lt_of_lt_of_le Nat.zero_lt_two hn⟩ -
    eStd (n := n) ⟨1,
      lt_of_lt_of_le (by decide : 1 < 2) hn⟩)

/-- The BS81 Lemma 18(iii) count `2 * n - 4` for the constraints `⟪g1,w⟫ = ⟪g2,w⟫ = 2`. -/
public theorem ncard_minVecDn_inner_g1_g2_eq_two
    (hn : 3 ≤ n) :
    Set.ncard {w : ℝⁿ |
        w ∈ minVecDn (n := n) ∧
          (⟪g1 (n := n) (le_trans (by decide : 2 ≤ 3) hn), w⟫ : ℝ) = 2 ∧
          (⟪g2 (n := n) (le_trans (by decide : 2 ≤ 3) hn), w⟫ : ℝ) = 2} =
      2 * n - 4 := by
  have hn2 : 2 ≤ n := le_trans (by decide : 2 ≤ 3) hn
  -- Indices `0,1 : Fin n` matching the definitions of `g1,g2`.
  let i0 : Fin n := ⟨0,
    lt_of_lt_of_le Nat.zero_lt_two hn2⟩
  let i1 : Fin n := ⟨1,
    lt_of_lt_of_le (by decide : 1 < 2) hn2⟩
  have i1_ne_i0 : i1 ≠ i0 := by
    lia
  have hsqrt : (Real.sqrt 2 : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (2 : ℝ) := by norm_num
    exact Real.sqrt_ne_zero'.2 this
  have hsqrt2 : (Real.sqrt 2 : ℝ) * Real.sqrt 2 = 2 := by
    have h : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
    exact Real.mul_self_sqrt h
  have inner_eStd (a b : Fin n) :
      (⟪eStd (n := n) a, eStd (n := n) b⟫ : ℝ) = if a = b then 1 else 0 := by
    by_cases h : a = b
    · subst h
      simp [eStd]
    · simp [eStd, EuclideanSpace.inner_single_left, h]
  -- Encode sign choices `{+1,-1}` via `Bool`.
  let signZ : Bool → ℤ := fun b => if b then (1 : ℤ) else (-1 : ℤ)
  have signZ_mem : ∀ b, signZ b ∈ Sign := by
    intro b
    cases b <;> simp [signZ, Sign]
  have signZ_inj : Function.Injective signZ := by
    intro b c hbc
    cases b <;> cases c <;> simp [signZ] at hbc <;> simp
  -- Shift indices `k : Fin (n-2)` to `k+2 : Fin n` so that we range over `{2,3,...,n-1}`.
  let shift : Fin (n - 2) → Fin n := fun k =>
    ⟨k.1 + 2, by
      have hk : k.1 + 2 < (n - 2) + 2 := Nat.add_lt_add_right k.2 2
      simpa [Nat.sub_add_cancel hn2] using! hk⟩
  have shift_inj : Function.Injective shift := by
    intro k k' h
    apply Fin.ext
    have hval : k.1 + 2 = k'.1 + 2 := by
      simpa [shift] using! congrArg Fin.val h
    exact Nat.add_right_cancel hval
  have shift_ne_i0 : ∀ k, shift k ≠ i0 := by
    intro k hk
    have : k.1 + 2 = 0 := by simpa [shift, i0] using! congrArg Fin.val hk
    exact (Nat.succ_ne_zero (k.1 + 1)) this
  have shift_ne_i1 : ∀ k, shift k ≠ i1 := by
    intro k hk
    have hval : k.1 + 2 = 1 := by simpa [shift, i1] using! congrArg Fin.val hk
    have hge : 2 ≤ k.1 + 2 := Nat.le_add_left 2 k.1
    have : (2 : ℕ) ≤ 1 := by
      exact (hval ▸ hge)
    exact (by decide : ¬ (2 : ℕ) ≤ 1) this
  -- The explicit parametrization of the solutions: `√2 e₀ ± √2 e_k` with `k ≥ 2`.
  let vec : (Fin (n - 2) × Bool) → ℝⁿ := fun x =>
    (Real.sqrt 2) • ((1 : ℝ) • eStd (n := n) i0) +
      (Real.sqrt 2) • (((signZ x.2 : ℤ) : ℝ) • eStd (n := n) (shift x.1))
  let S : Set ℝⁿ :=
    {w : ℝⁿ |
      w ∈ minVecDn (n := n) ∧
        (⟪g1 (n := n) hn2, w⟫ : ℝ) = 2 ∧
          (⟪g2 (n := n) hn2, w⟫ : ℝ) = 2}
  have hvec_mem : ∀ x, vec x ∈ S := by
    rintro ⟨k, b⟩
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨i0, shift k, ?_, 1, signZ b, ?_, signZ_mem b, ?_⟩
      · intro hEq
        exact shift_ne_i0 k hEq.symm
      · simp [Sign]
      · simp [vec, smul_smul]
    · have hi0 : i0 ≠ shift k := by
        intro hEq; exact shift_ne_i0 k hEq.symm
      have hi1 : i1 ≠ shift k := by
        intro hEq; exact shift_ne_i1 k hEq.symm
      have hI0 : (⟪eStd (n := n) i0, vec ⟨k, b⟩⟫ : ℝ) = Real.sqrt 2 := by
        simp [vec, eStd, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, hi0]
      have hI1 : (⟪eStd (n := n) i1, vec ⟨k, b⟩⟫ : ℝ) = 0 := by
        simp [vec, eStd, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, hi1,
          i1_ne_i0]
      calc
        (⟪g1 (n := n) hn2, vec ⟨k, b⟩⟫ : ℝ)
            = (Real.sqrt 2) *
                ((⟪eStd (n := n) i0, vec ⟨k, b⟩⟫ : ℝ) +
                  (⟪eStd (n := n) i1, vec ⟨k, b⟩⟫ : ℝ)) := by
              simp [g1, i0, i1, real_inner_smul_left, inner_add_left, mul_add]
        _ = (Real.sqrt 2) * (Real.sqrt 2) := by simp [hI0, hI1]
        _ = 2 := hsqrt2
    · have hi0 : i0 ≠ shift k := by
        intro hEq; exact shift_ne_i0 k hEq.symm
      have hi1 : i1 ≠ shift k := by
        intro hEq; exact shift_ne_i1 k hEq.symm
      have hI0 : (⟪eStd (n := n) i0, vec ⟨k, b⟩⟫ : ℝ) = Real.sqrt 2 := by
        simp [vec, eStd, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, hi0]
      have hI1 : (⟪eStd (n := n) i1, vec ⟨k, b⟩⟫ : ℝ) = 0 := by
        simp [vec, eStd, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, hi1,
          i1_ne_i0]
      calc
        (⟪g2 (n := n) hn2, vec ⟨k, b⟩⟫ : ℝ)
            = (Real.sqrt 2) *
                ((⟪eStd (n := n) i0, vec ⟨k, b⟩⟫ : ℝ) -
                  (⟪eStd (n := n) i1, vec ⟨k, b⟩⟫ : ℝ)) := by
              simp [g2, i0, i1, real_inner_smul_left, inner_sub_left, mul_sub]
        _ = (Real.sqrt 2) * (Real.sqrt 2) := by simp [hI0, hI1]
        _ = 2 := hsqrt2
  have hrange : Set.range vec = S := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact hvec_mem x
    · intro hw
      rcases hw with ⟨hwMin, hg1, hg2⟩
      rcases hwMin with ⟨i, j, hij, s, t, hs, ht, rfl⟩
      have hs' : s = 1 ∨ s = -1 := by simpa [Sign] using! hs
      have ht' : t = 1 ∨ t = -1 := by simpa [Sign] using! ht
      -- Let `a0 = ⟪e₀,w⟫` and `a1 = ⟪e₁,w⟫`. From `⟪g1,w⟫=⟪g2,w⟫=2` we get `a0=√2` and `a1=0`.
      let w : ℝⁿ :=
        (Real.sqrt 2) • ((s : ℝ) • eStd (n := n) i) + (Real.sqrt 2) • ((t : ℝ) • eStd (n := n) j)
      let a0 : ℝ := (⟪eStd (n := n) i0, w⟫ : ℝ)
      let a1 : ℝ := (⟪eStd (n := n) i1, w⟫ : ℝ)
      have hg1_form :
          (⟪g1 (n := n) hn2,
              w⟫ : ℝ) =
            (Real.sqrt 2) * (a0 + a1) := by
        simp [a0, a1, w, g1, i0, i1, real_inner_smul_left, inner_add_left, mul_add]
      have hg2_form :
          (⟪g2 (n := n) hn2,
              w⟫ : ℝ) =
            (Real.sqrt 2) * (a0 - a1) := by
        simp [a0, a1, w, g2, i0, i1, real_inner_smul_left, inner_sub_left, mul_sub]
      have hg1' : (Real.sqrt 2) * (a0 + a1) = 2 := by simpa [w, hg1_form] using! hg1
      have hg2' : (Real.sqrt 2) * (a0 - a1) = 2 := by simpa [w, hg2_form] using! hg2
      have hsum : a0 + a1 = Real.sqrt 2 := by
        have hmul : (2 : ℝ) * (a0 + a1) = (2 : ℝ) * (Real.sqrt 2) := by
          -- multiply `hg1'` by `√2` and rewrite `√2*√2` to `2`.
          calc
            (2 : ℝ) * (a0 + a1) = (Real.sqrt 2) * ((Real.sqrt 2) * (a0 + a1)) := by
              -- rewrite `2` as `√2*√2`
              rw [← hsqrt2]
              simpa using! (mul_assoc (Real.sqrt 2) (Real.sqrt 2) (a0 + a1))
            _ = (Real.sqrt 2) * 2 := by simpa [mul_assoc] using! congrArg ((Real.sqrt 2) * ·) hg1'
            _ = (2 : ℝ) * (Real.sqrt 2) := by ring
        have h2 : (2 : ℝ) ≠ 0 := by norm_num
        exact mul_left_cancel₀ h2 hmul
      have hdiff : a0 - a1 = Real.sqrt 2 := by
        have hmul : (2 : ℝ) * (a0 - a1) = (2 : ℝ) * (Real.sqrt 2) := by
          calc
            (2 : ℝ) * (a0 - a1) = (Real.sqrt 2) * ((Real.sqrt 2) * (a0 - a1)) := by
              rw [← hsqrt2]
              simpa using! (mul_assoc (Real.sqrt 2) (Real.sqrt 2) (a0 - a1))
            _ = (Real.sqrt 2) * 2 := by
              simpa [mul_assoc] using! congrArg (fun z : ℝ => (Real.sqrt 2) * z) hg2'
            _ = (2 : ℝ) * (Real.sqrt 2) := by ring
        have h2 : (2 : ℝ) ≠ 0 := by norm_num
        exact mul_left_cancel₀ h2 hmul
      have ha0 : a0 = Real.sqrt 2 := by linarith
      have ha1 : a1 = 0 := by linarith
      -- From `a1=0` we conclude that neither index equals `i1`.
      have hi_ne_i1 : i ≠ i1 := by
        intro hi
        subst hi
        have hj : j ≠ i1 :=
          Ne.symm hij
        have hj' : i1 ≠ j := by
          intro hEq
          exact hj hEq.symm
        have : a1 = (Real.sqrt 2) * (s : ℝ) := by
          simp [a1, w, eStd, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, hj']
        -- `s = ±1`, so `√2*s ≠ 0`.
        rcases hs' with rfl | rfl <;> (simp [this, hsqrt] at ha1)
      have hj_ne_i1 : j ≠ i1 := by
        intro hj
        subst hj
        have hi' : i ≠ i1 := by
          assumption
        have hi'' : i1 ≠ i := by
          intro hEq
          exact hi' hEq.symm
        have : a1 = (Real.sqrt 2) * (t : ℝ) := by
          simp [a1, w, eStd, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, hi'']
        rcases ht' with rfl | rfl <;> (simp [this, hsqrt] at ha1)
      -- From `a0=√2` we conclude that one index equals `i0` with sign `+1`.
      by_cases hi0 : i = i0
      · subst hi0
        have hj0 : j ≠ i0 := hij.symm
        have hj0' : i0 ≠ j := by
          intro hEq
          exact hj0 hEq.symm
        have : a0 = (Real.sqrt 2) * (s : ℝ) := by
          simp [a0, w, eStd, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, hj0']
        have hs1 : s = 1 := by
          simp_all
        subst hs1
        -- choose `b` for `t`
        obtain ⟨b, hb⟩ : ∃ b : Bool, signZ b = t := by
          rcases ht' with rfl | rfl
          · exact ⟨true, by simp [signZ]⟩
          · exact ⟨false, by simp [signZ]⟩
        -- build `k` from `j`
        have hjval_ge2 : 2 ≤ j.1 := by
          have hjval_ne0 : j.1 ≠ 0 := by
            intro h0
            apply hj0
            apply Fin.ext
            simp [i0, h0]
          have hjval_ne1 : j.1 ≠ 1 := by
            intro h1
            apply hj_ne_i1
            apply Fin.ext
            simp [i1, h1]
          have hnot : ¬ j.1 < 2 := by
            intro hlt
            have hle1 : j.1 ≤ 1 := (Nat.lt_succ_iff).1 hlt
            rcases (Nat.le_one_iff_eq_zero_or_eq_one).1 hle1 with h0 | h1
            · exact hjval_ne0 h0
            · exact hjval_ne1 h1
          exact le_of_not_gt hnot
        let k : Fin (n - 2) := ⟨j.1 - 2, Nat.sub_lt_sub_right hjval_ge2 j.2⟩
        have hk : shift k = j := by
          apply Fin.ext
          have : (j.1 - 2) + 2 = j.1 := Nat.sub_add_cancel hjval_ge2
          simp [shift, k, this]
        refine ⟨⟨k, b⟩, ?_⟩
        subst hb
        simp [vec, hk, smul_smul]
      · -- `i ≠ i0`
        have hj0 : j = i0 := by
          by_contra hj0
          have hi0' : i0 ≠ i := by
            intro hEq
            exact hi0 hEq.symm
          have hj0' : i0 ≠ j := by
            intro hEq
            exact hj0 hEq.symm
          have : a0 = 0 := by
            simp [a0, w, inner_add_right, real_inner_smul_right, inner_eStd, hi0', hj0']
          exact (by nlinarith [ha0, this] : False).elim
        subst hj0
        have hi0' : i ≠ i0 := hi0
        have hi0'' : i0 ≠ i := by
          intro hEq
          exact hi0' hEq.symm
        have : a0 = (Real.sqrt 2) * (t : ℝ) := by
          simp [a0, w, eStd, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, hi0'']
        have ht1 : t = 1 := by
          simp_all
        subst ht1
        -- choose `b` for `s`
        obtain ⟨b, hb⟩ : ∃ b : Bool, signZ b = s := by
          rcases hs' with rfl | rfl
          · exact ⟨true, by simp [signZ]⟩
          · exact ⟨false, by simp [signZ]⟩
        -- build `k` from `i`
        have hival_ge2 : 2 ≤ i.1 := by
          have hival_ne0 : i.1 ≠ 0 := by
            intro h0
            apply hi0'
            apply Fin.ext
            simp [i0, h0]
          have hival_ne1 : i.1 ≠ 1 := by
            intro h1
            apply hi_ne_i1
            apply Fin.ext
            simp [i1, h1]
          have hnot : ¬ i.1 < 2 := by
            intro hlt
            have hle1 : i.1 ≤ 1 := (Nat.lt_succ_iff).1 hlt
            rcases (Nat.le_one_iff_eq_zero_or_eq_one).1 hle1 with h0 | h1
            · exact hival_ne0 h0
            · exact hival_ne1 h1
          exact le_of_not_gt hnot
        let k : Fin (n - 2) := ⟨i.1 - 2, Nat.sub_lt_sub_right hival_ge2 i.2⟩
        have hk : shift k = i := by
          apply Fin.ext
          have : (i.1 - 2) + 2 = i.1 := Nat.sub_add_cancel hival_ge2
          simp [shift, k, this]
        refine ⟨⟨k, b⟩, ?_⟩
        subst hb
        simp [vec, hk, smul_smul, add_comm]
  have hinj : Function.Injective vec := by
    rintro ⟨k, b⟩ ⟨k', b'⟩ h
    have hk : k = k' := by
      by_contra hne
      have hneq : shift k ≠ shift k' := by
        intro heq
        exact hne (shift_inj heq)
      -- inner with `e_(shift k)` distinguishes `k`.
      have hinner :
          (⟪eStd (n := n) (shift k), vec ⟨k, b⟩⟫ : ℝ) =
            (⟪eStd (n := n) (shift k), vec ⟨k', b'⟩⟫ : ℝ) := by
        simpa using! congrArg (fun v : ℝⁿ => (⟪eStd (n := n) (shift k), v⟫ : ℝ)) h
      have hL : (⟪eStd (n := n) (shift k), vec ⟨k, b⟩⟫ : ℝ) =
          (Real.sqrt 2) * ((signZ b : ℤ) : ℝ) := by
        have hi0' : shift k ≠ i0 := shift_ne_i0 k
        simp [vec, eStd, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, hi0']
      have hR : (⟪eStd (n := n) (shift k), vec ⟨k', b'⟩⟫ : ℝ) = 0 := by
        have hi0' : shift k ≠ i0 := shift_ne_i0 k
        simp [vec, eStd, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, hi0', hneq]
      -- `√2 * signZ b ≠ 0`.
      have hNz : (Real.sqrt 2) * ((signZ b : ℤ) : ℝ) ≠ 0 := by
        have : ((signZ b : ℤ) : ℝ) ≠ 0 := by
          cases b <;> simp [signZ]
        exact mul_ne_zero hsqrt this
      exact hNz (by simpa [hL, hR] using! hinner)
    subst hk
    -- compare the `shift k` inner product to identify the sign
    have hinner :
        (⟪eStd (n := n) (shift k), vec ⟨k, b⟩⟫ : ℝ) =
          (⟪eStd (n := n) (shift k), vec ⟨k, b'⟩⟫ : ℝ) := by
      simpa using! congrArg (fun v : ℝⁿ => (⟪eStd (n := n) (shift k), v⟫ : ℝ)) h
    have hEq :
        (Real.sqrt 2) * ((signZ b : ℤ) : ℝ) = (Real.sqrt 2) * ((signZ b' : ℤ) : ℝ) := by
      have hi0' : shift k ≠ i0 := shift_ne_i0 k
      simpa [vec, eStd, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, hi0'] using!
        hinner
    have hEq' : ((signZ b : ℤ) : ℝ) = ((signZ b' : ℤ) : ℝ) := mul_left_cancel₀ hsqrt hEq
    have : signZ b = signZ b' := by exact_mod_cast hEq'
    have : b = b' := signZ_inj this
    subst this
    rfl
  have hncard : Set.ncard S = Fintype.card (Fin (n - 2) × Bool) := by
    simpa [hrange] using! (Set.ncard_range_of_injective (f := vec) hinj)
  have hcard : Fintype.card (Fin (n - 2) × Bool) = 2 * n - 4 := by
    simp [Fintype.card_prod, Nat.mul_sub_left_distrib, Nat.mul_comm]
  -- Unfold `S` back to the original goal.
  change Set.ncard S = 2 * n - 4
  exact hncard.trans hcard
end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Dn
