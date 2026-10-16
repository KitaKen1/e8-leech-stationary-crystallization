-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Dn.MinVec
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Sym.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.ByContra

/-!
# Basic facts about `Dₙ`

This file records elementary properties of the minimal-vector set `minVecDn` used in
BS81 Lemma 18(iii): an explicit membership characterization, a norm computation, and the
cardinality formula.

## Main statements
* `mem_minVecDn_iff`
* `norm_sq_minVecDn_eq_four`
* `ncard_minVecDn_eq`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Dn
noncomputable section

open scoped RealInnerProductSpace

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- Unfolding lemma for membership in `minVecDn`. -/
public theorem mem_minVecDn_iff
    (x : ℝⁿ) :
    x ∈ minVecDn (n := n) ↔
      ∃ i j : Fin n,
        i ≠ j ∧
          ∃ s t : ℤ,
            s ∈ Sign ∧ t ∈ Sign ∧
              x =
                (Real.sqrt 2) • ((s : ℝ) • eStd (n := n) i) +
                  (Real.sqrt 2) • ((t : ℝ) • eStd (n := n) j) :=
  Iff.rfl

/-- Every minimal vector of `Dₙ` has squared norm `4`. -/
public theorem norm_sq_minVecDn_eq_four
    {x : ℝⁿ} (hx : x ∈ minVecDn (n := n)) :
    ‖x‖ ^ 2 = (4 : ℝ) := by
  rcases hx with ⟨i, j, hij, s, t, hs, ht, rfl⟩
  have hs' : s = 1 ∨ s = -1 := by simpa [Sign] using! hs
  have ht' : t = 1 ∨ t = -1 := by simpa [Sign] using! ht
  let u : ℝⁿ := (Real.sqrt 2) • ((s : ℝ) • eStd (n := n) i)
  let v : ℝⁿ := (Real.sqrt 2) • ((t : ℝ) • eStd (n := n) j)
  have huv : ⟪u, v⟫ = (0 : ℝ) := by
    have hij' : i ≠ j := hij
    have : (⟪eStd (n := n) i, eStd (n := n) j⟫ : ℝ) = 0 := by
      simp [eStd, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, hij']
    -- reduce to the orthogonality computation above
    simp [u, v, real_inner_smul_left, real_inner_smul_right, this]
  have hnorm : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    simpa [pow_two] using! (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u v huv)
  have hu2 : ‖u‖ ^ 2 = (2 : ℝ) := by
    rcases hs' with rfl | rfl <;>
      simp [u, eStd, EuclideanSpace.norm_single, norm_smul, abs_of_nonneg (Real.sqrt_nonneg 2)]
  have hv2 : ‖v‖ ^ 2 = (2 : ℝ) := by
    rcases ht' with rfl | rfl <;>
      simp [v, eStd, EuclideanSpace.norm_single, norm_smul, abs_of_nonneg (Real.sqrt_nonneg 2)]
  have hcalc : ‖u + v‖ ^ 2 = (4 : ℝ) := by
    nlinarith [hnorm, hu2, hv2]
  simpa [u, v] using! hcalc

/-- The set `minVecDn` has cardinality `2 * n * (n - 1)` for `2 ≤ n`. -/
public theorem ncard_minVecDn_eq : Set.ncard (minVecDn (n := n)) = 2 * n * (n - 1) := by
  -- Encode the sign set `{+1,-1}` via `Bool` (ℤ-level, for `Sign` membership).
  let signZ : Bool → ℤ := fun b => if b then (1 : ℤ) else (-1 : ℤ)
  have signZ_mem : ∀ b, signZ b ∈ Sign := by
    intro b
    cases b <;> simp [signZ, Sign]
  -- Real-level sign used in the actual vector formula.
  let signR : Bool → ℝ := fun b => if b then (1 : ℝ) else (-1 : ℝ)
  have signZ_cast (b : Bool) : (signZ b : ℝ) = signR b := by
    cases b <;> simp [signZ, signR]
  have signR_ne_zero : ∀ b, signR b ≠ (0 : ℝ) := by
    intro b
    cases b <;> simp [signR]
  -- Use strictly-ordered pairs `(i,j)` with `i<j` to avoid double counting.
  let PairLt : Type := {p : Fin n × Fin n // p.1 < p.2}
  let Param : Type := PairLt × Bool × Bool
  let vecOf : Param → ℝⁿ
    | (⟨⟨i, j⟩, hij⟩, bs, bt) =>
        (Real.sqrt 2) • (signR bs • eStd (n := n) i) +
          (Real.sqrt 2) • (signR bt • eStd (n := n) j)
  -- Inner products of standard basis vectors.
  have inner_eStd (a b : Fin n) :
      (⟪eStd (n := n) a, eStd (n := n) b⟫ : ℝ) = if a = b then 1 else 0 := by
    by_cases h : a = b
    · subst h
      simp [eStd]
    · simp [eStd, EuclideanSpace.inner_single_left, h]
  have hrange : Set.range vecOf = minVecDn (n := n) := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      rcases p with ⟨⟨⟨i, j⟩, hij⟩, bs, bt⟩
      refine ⟨i, j, ne_of_lt hij, signZ bs, signZ bt, signZ_mem bs, signZ_mem bt, ?_⟩
      -- rewrite `vecOf` into the `minVecDn` normal form
      simp [vecOf, signZ_cast, smul_smul, mul_comm]
    · intro hx
      rcases hx with ⟨i, j, hij, s, t, hs, ht, rfl⟩
      have hs' : s = 1 ∨ s = -1 := by simpa [Sign] using! hs
      have ht' : t = 1 ∨ t = -1 := by simpa [Sign] using! ht
      obtain ⟨bs, hbs⟩ : ∃ bs : Bool, signZ bs = s := by
        rcases hs' with rfl | rfl
        · exact ⟨true, by simp [signZ]⟩
        · exact ⟨false, by simp [signZ]⟩
      obtain ⟨bt, hbt⟩ : ∃ bt : Bool, signZ bt = t := by
        rcases ht' with rfl | rfl
        · exact ⟨true, by simp [signZ]⟩
        · exact ⟨false, by simp [signZ]⟩
      have hne : i ≠ j := hij
      rcases lt_or_gt_of_ne hne with hijlt | hijgt
      · refine ⟨(⟨⟨i, j⟩, hijlt⟩, bs, bt), ?_⟩
        subst hbs; subst hbt
        simp [vecOf, signZ_cast, smul_smul, mul_comm]
      · refine ⟨(⟨⟨j, i⟩, hijgt⟩, bt, bs), ?_⟩
        subst hbs; subst hbt
        simp [vecOf, signZ_cast, smul_smul, add_comm]
  have hinj : Function.Injective vecOf := by
    have hsqrt : (Real.sqrt 2 : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (2 : ℝ) := by norm_num
      exact Real.sqrt_ne_zero'.2 this
    have norm_sq_eStd (a : Fin n) : ‖eStd (n := n) a‖ ^ 2 = (1 : ℝ) := by
      simp [eStd, EuclideanSpace.norm_single]
    rintro ⟨⟨⟨i, j⟩, hij⟩, bs, bt⟩ ⟨⟨⟨i', j'⟩, hij'⟩, bs', bt'⟩ h
    have hijne : i ≠ j := ne_of_lt hij
    have hijne' : i' ≠ j' := ne_of_lt hij'
    -- Step 1: `i = i'`.
    have eqi := congrArg (fun v : ℝⁿ => (⟪eStd (n := n) i, v⟫ : ℝ)) h
    have eqi' :
        signR bs * (Real.sqrt 2) =
          (if i = i' then signR bs' * (Real.sqrt 2) else 0) +
            (if i = j' then signR bt' * (Real.sqrt 2) else 0) := by
      -- expand using bilinearity, then simplify (keeping scalars as scalars)
      -- `simp` produces a factor `‖eStd i‖^2`; reduce it using `norm_sq_eStd`.
      have := eqi
      -- Use commutativity of multiplication to match the chosen normal form.
      simpa [vecOf, inner_add_right, real_inner_smul_right, inner_eStd, hijne, hijne', smul_smul,
        mul_assoc, mul_left_comm, mul_comm, norm_sq_eStd] using! this
    have hnonzero_i : signR bs * (Real.sqrt 2) ≠ (0 : ℝ) := mul_ne_zero (signR_ne_zero bs) hsqrt
    have hii' : i = i' := by
      by_contra hne
      have hne' : i ≠ i' := hne
      -- then RHS must come from the `j'` term, so `i = j'`
      have hijEq : i = j' := by
        by_cases hji : i = j'
        · exact hji
        · have : signR bs * (Real.sqrt 2) = 0 := by
            simpa [hne', hji] using! eqi'
          exact (hnonzero_i this).elim
      have hi'lt : i' < i := by simpa [hijEq] using! hij'
      -- now look at inner product with `eStd i'`
      have eqi2 := congrArg (fun v : ℝⁿ => (⟪eStd (n := n) i', v⟫ : ℝ)) h
      have hL0 :
          (⟪eStd (n := n) i', vecOf (⟨⟨i, j⟩, hij⟩, bs, bt)⟫ : ℝ) = 0 := by
        have hi'ne_i : i' ≠ i := ne_of_lt hi'lt
        have hi'ne_j : i' ≠ j := by
          intro hEq
          have : i' < i' := by simpa [hEq] using! lt_trans hi'lt hij
          exact (lt_irrefl i') this
        -- expand; both basis inner products vanish
        simp [vecOf, inner_add_right, real_inner_smul_right, inner_eStd,
          hi'ne_i, hi'ne_j, smul_smul, mul_comm]
      have hRnz :
          (⟪eStd (n := n) i', vecOf (⟨⟨i', j'⟩, hij'⟩, bs', bt')⟫ : ℝ) ≠ 0 := by
        have : signR bs' * (Real.sqrt 2) ≠ (0 : ℝ) := mul_ne_zero (signR_ne_zero bs') hsqrt
        -- the `j'` term vanishes since `i' ≠ j'`
        -- (inner simplifies to `signR bs' * √2`)
        simpa [vecOf, inner_add_right, real_inner_smul_right, inner_eStd, hijne', smul_smul,
          mul_assoc, mul_left_comm, mul_comm, norm_sq_eStd] using! this
      have : (0 : ℝ) = (⟪eStd (n := n) i', vecOf (⟨⟨i', j'⟩, hij'⟩, bs', bt')⟫ : ℝ) := by
        simpa [hL0] using! eqi2
      exact (hRnz this.symm).elim
    subst hii'
    -- Step 2: `j = j'`.
    have eqj := congrArg (fun v : ℝⁿ => (⟪eStd (n := n) j, v⟫ : ℝ)) h
    have eqj' :
        signR bt * (Real.sqrt 2) = if j = j' then signR bt' * (Real.sqrt 2) else 0 := by
      -- after `i=i'`, the `i'`-term is orthogonal to `eStd j`
      simpa [vecOf, inner_add_right, real_inner_smul_right, inner_eStd,
        hijne, hijne', hijne.symm, smul_smul, mul_assoc, mul_left_comm, mul_comm, norm_sq_eStd]
        using! eqj
    have hnonzero_j : signR bt * (Real.sqrt 2) ≠ (0 : ℝ) := mul_ne_zero (signR_ne_zero bt) hsqrt
    have hjj' : j = j' := by
      by_contra hne
      have hne' : j ≠ j' := hne
      have : signR bt * (Real.sqrt 2) = 0 := by simpa [hne'] using! eqj'
      exact (hnonzero_j this).elim
    subst hjj'
    -- Step 3: signs are determined by the inner products with `eStd i` and `eStd j`.
    have hbsR : signR bs * (Real.sqrt 2) = signR bs' * (Real.sqrt 2) := by
      -- with `i=i'` and `i≠j` (since `i<j`), `eqi'` reduces to this.
      simpa [hijne] using! eqi'
    have hbsR' : signR bs = signR bs' := mul_right_cancel₀ hsqrt hbsR
    have hbtR : signR bt = signR bt' := by
      have : signR bt * (Real.sqrt 2) = signR bt' * (Real.sqrt 2) := by simpa using! eqj'
      exact mul_right_cancel₀ hsqrt this
    have signR_inj : Function.Injective signR := by
      intro a b hab
      cases a <;> cases b
      · rfl
      · exfalso
        have hne : (-1 : ℝ) ≠ 1 := by norm_num
        exact hne (by simpa [signR] using! hab)
      · exfalso
        have hne : (1 : ℝ) ≠ -1 := by norm_num
        exact hne (by simpa [signR] using! hab)
      · rfl
    have hbs : bs = bs' := signR_inj hbsR'
    have hbt : bt = bt' := signR_inj hbtR
    subst hbs; subst hbt
    rfl
  have hncard : Set.ncard (minVecDn (n := n)) = Nat.card Param := by
    simpa [hrange] using! (Set.ncard_range_of_injective (f := vecOf) hinj)
  -- Cardinalities.
  have hPairLt : Nat.card PairLt = n.choose 2 := by
    let f : PairLt → {a : Sym2 (Fin n) // ¬a.IsDiag} := fun p =>
      ⟨s(p.1.1, p.1.2), by
        have : (p.1.1 : Fin n) ≠ p.1.2 := ne_of_lt p.2
        simpa [Sym2.mk_isDiag_iff] using! this⟩
    have hf : Function.Bijective f := by
      constructor
      · rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
        have hpq' : s(p.1, p.2) = s(q.1, q.2) := congrArg Subtype.val hpq
        have hcases : p = q ∨ p = q.swap := Sym2.mk_eq_mk_iff.1 hpq'
        rcases hcases with hcases | hcases
        · subst hcases
          rfl
        · have : q.2 < q.1 := by simpa [hcases] using! hp
          exact (lt_asymm hq this).elim
      · intro z
        obtain ⟨a, b, hz⟩ : ∃ a b : Fin n, s(a, b) = z.1 :=
          Sym2.ind (f := fun i => ∃ a b : Fin n, s(a, b) = i) (fun x y => ⟨x, y, rfl⟩) z.1
        have hne : a ≠ b := by
          intro hEq
          apply z.2
          rw [← hz]
          exact Sym2.mk_isDiag_iff.2 hEq
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · refine ⟨⟨(a, b), hlt⟩, ?_⟩
          apply Subtype.ext
          exact hz
        · refine ⟨⟨(b, a), hgt⟩, ?_⟩
          apply Subtype.ext
          show s(b, a) = z.1
          rw [Sym2.eq_swap]
          exact hz
    have hcard :
        Nat.card PairLt = Nat.card {a : Sym2 (Fin n) // ¬a.IsDiag} := by
      simpa using! Nat.card_congr (Equiv.ofBijective f hf)
    have hsym2 :
        Nat.card {a : Sym2 (Fin n) // ¬a.IsDiag} = n.choose 2 := by
      -- avoid simp rewriting the subtype cardinality into a subtraction
      have h' :
          Fintype.card {a : Sym2 (Fin n) // ¬a.IsDiag} = (Fintype.card (Fin n)).choose 2 :=
        Sym2.card_subtype_not_diag (α := Fin n)
      have hnfin : Fintype.card (Fin n) = n := by simp
      have h'' : (Fintype.card (Fin n)).choose 2 = n.choose 2 := by simp [hnfin]
      have hcardF : Fintype.card {a : Sym2 (Fin n) // ¬a.IsDiag} = n.choose 2 := h'.trans h''
      -- convert `Nat.card` to `Fintype.card` without `simp` rewriting the subtype cardinality
      rw [Nat.card_eq_fintype_card]
      exact hcardF
    exact hcard.trans hsym2
  have hParam : Nat.card Param = 4 * (n.choose 2) := by
    -- `Param = PairLt × Bool × Bool`, so `card = card PairLt * 2 * 2`.
    calc
      Nat.card Param = Nat.card PairLt * Nat.card (Bool × Bool) := by
        simp [Param]
      _ = Nat.card PairLt * (Nat.card Bool * Nat.card Bool) := by
        simp
      _ = Nat.card PairLt * 4 := by simp
      _ = 4 * (n.choose 2) := by
        calc
          Nat.card PairLt * 4 = (n.choose 2) * 4 := by
            exact congrArg (fun m : ℕ => m * 4) hPairLt
          _ = 4 * (n.choose 2) := by simp [Nat.mul_comm]
  have hdiv : 2 ∣ n * (n - 1) := by
    exact Nat.two_dvd_mul_sub_one n
  have hmul : 4 * (n.choose 2) = 2 * n * (n - 1) := by
    -- Expand `choose n 2` and cancel `/ 2`.
    rw [Nat.choose_two_right]
    have hcancel : 2 * (n * (n - 1) / 2) = n * (n - 1) := Nat.mul_div_cancel' hdiv
    calc
      4 * (n * (n - 1) / 2) = 2 * (2 * (n * (n - 1) / 2)) := by
        simpa using! (Nat.mul_assoc 2 2 (n * (n - 1) / 2))
      _ = 2 * (n * (n - 1)) := by
        simpa [Nat.mul_assoc] using! congrArg (fun t : ℕ => 2 * t) hcancel
      _ = 2 * n * (n - 1) := by simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  calc
    Set.ncard (minVecDn (n := n)) = Nat.card Param := hncard
    _ = 4 * (n.choose 2) := hParam
    _ = 2 * n * (n - 1) := hmul
end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Dn
