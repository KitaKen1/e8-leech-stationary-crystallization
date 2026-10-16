/- Coefficient matching lemmas for `BleadingCoeffs` lists. -/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import
SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.ThetaRSeriesSpecialize
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.ConvolutionAlgebra
public import
SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PhiDeltaQSeries.Identities

/-!
# Coefficient matching for `BleadingCoeffs`

The file `BLeadingCoeffs.lean` defines explicit coefficient lists using truncated list
arithmetic. For the Appendix A truncation argument we also use coefficient functions defined via
the Cauchy convolution `conv`.

This file proves that the two presentations agree up to the cutoff `QN = 50`.

## Main statements
* `coeffQ_phi2CoreQ_eq`, `coeffQ_phi1CoreQ_eq`
* `coeffQ_phinumQ_eq`, `coeffQ_DeltaSqQ_eq`
-/

noncomputable section

namespace SpherePacking.Dim24.AppendixA
lemma coeffQ_addQ_lt (a b : List ℚ) (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    BleadingCoeffs.coeffQ (BleadingCoeffs.addQ a b) n =
      BleadingCoeffs.coeffQ a n + BleadingCoeffs.coeffQ b n := by
  simpa [BleadingCoeffs.addQ] using!
    (coeffQ_ofFn_lt
      (f := fun i : Fin BleadingCoeffs.QN =>
        BleadingCoeffs.coeffQ a i.1 + BleadingCoeffs.coeffQ b i.1)
      (n := n) hn)

lemma coeffQ_negQ_lt (a : List ℚ) (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    BleadingCoeffs.coeffQ (BleadingCoeffs.negQ a) n = -BleadingCoeffs.coeffQ a n := by
  simpa [BleadingCoeffs.negQ] using!
    (coeffQ_ofFn_lt
      (f := fun i : Fin BleadingCoeffs.QN => -BleadingCoeffs.coeffQ a i.1)
      (n := n) hn)

lemma coeffQ_subQ_lt (a b : List ℚ) (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    BleadingCoeffs.coeffQ (BleadingCoeffs.subQ a b) n =
      BleadingCoeffs.coeffQ a n - BleadingCoeffs.coeffQ b n :=
  by simp [BleadingCoeffs.subQ, coeffQ_addQ_lt, coeffQ_negQ_lt, hn, sub_eq_add_neg]

lemma coeffQ_smulQ_lt (c : ℚ) (a : List ℚ) (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    BleadingCoeffs.coeffQ (BleadingCoeffs.smulQ c a) n = c * BleadingCoeffs.coeffQ a n := by
  simpa [BleadingCoeffs.smulQ] using!
    (coeffQ_ofFn_lt
      (f := fun i : Fin BleadingCoeffs.QN => c * BleadingCoeffs.coeffQ a i.1)
      (n := n) hn)

lemma coeffQ_mulQ_lt (a b : List ℚ) (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    BleadingCoeffs.coeffQ (BleadingCoeffs.mulQ a b) n =
      Finset.sum (Finset.range (n + 1)) fun j =>
        BleadingCoeffs.coeffQ a j * BleadingCoeffs.coeffQ b (n - j) := by
  simpa [BleadingCoeffs.mulQ] using!
    (coeffQ_ofFn_lt
      (f := fun i : Fin BleadingCoeffs.QN =>
        Finset.sum (Finset.range (i.1 + 1)) fun j =>
          BleadingCoeffs.coeffQ a j * BleadingCoeffs.coeffQ b (i.1 - j))
      (n := n) hn)

lemma coeffQ_mulQ_lt_conv (a b : List ℚ) (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    BleadingCoeffs.coeffQ (BleadingCoeffs.mulQ a b) n =
      conv (fun k => BleadingCoeffs.coeffQ a k) (fun k => BleadingCoeffs.coeffQ b k) n := by
  have hanti :
      conv (fun k => BleadingCoeffs.coeffQ a k) (fun k => BleadingCoeffs.coeffQ b k) n =
        Finset.sum (Finset.range (n + 1)) fun j =>
          BleadingCoeffs.coeffQ a j * BleadingCoeffs.coeffQ b (n - j) := by
    simpa [conv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ, Nat.succ_eq_add_one] using!
      (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (f := fun i j => BleadingCoeffs.coeffQ a i * BleadingCoeffs.coeffQ b j) n)
  exact (coeffQ_mulQ_lt (a := a) (b := b) (n := n) hn).trans hanti.symm

lemma conv_congr_left_of_eq_on_le (a a' b : ℕ → ℚ) (n : ℕ)
    (h : ∀ m ≤ n, a m = a' m) :
    conv a b n = conv a' b n := by
  dsimp [conv]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hp1le : p.1 ≤ n := by
    refine le_trans (Nat.le_add_right p.1 p.2) (le_of_eq ?_)
    simpa [Finset.mem_antidiagonal] using! hp
  simp [h _ hp1le]

lemma conv_congr_right_of_eq_on_le (a b b' : ℕ → ℚ) (n : ℕ)
    (h : ∀ m ≤ n, b m = b' m) :
    conv a b n = conv a b' n := by
  dsimp [conv]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hp2le : p.2 ≤ n := by
    refine le_trans (Nat.le_add_left p.2 p.1) (le_of_eq ?_)
    simpa [Finset.mem_antidiagonal] using! hp
  simp [h _ hp2le]

lemma conv_congr_of_eq_on_le (a a' b b' : ℕ → ℚ) (n : ℕ)
    (ha : ∀ m ≤ n, a m = a' m) (hb : ∀ m ≤ n, b m = b' m) :
    conv a b n = conv a' b' n :=
  (conv_congr_left_of_eq_on_le (a := a) (a' := a') (b := b) n ha).trans
    (conv_congr_right_of_eq_on_le (a := a') (b := b) (b' := b') n hb)

lemma coeffQ_mulQ_lt_conv_of_eq_on_le (a b : List ℚ) (a' b' : ℕ → ℚ) (n : ℕ)
    (hn : n < BleadingCoeffs.QN) (ha : ∀ m ≤ n, BleadingCoeffs.coeffQ a m = a' m)
    (hb : ∀ m ≤ n, BleadingCoeffs.coeffQ b m = b' m) :
    BleadingCoeffs.coeffQ (BleadingCoeffs.mulQ a b) n = conv a' b' n := by
  refine (coeffQ_mulQ_lt_conv (a := a) (b := b) (n := n) hn).trans ?_
  refine conv_congr_of_eq_on_le
    (a := fun k => BleadingCoeffs.coeffQ a k) (a' := a')
    (b := fun k => BleadingCoeffs.coeffQ b k) (b' := b') n ha hb

def deltaQ : ℕ → ℚ := fun n => if n = 0 then 1 else 0

lemma conv_deltaQ_right (a : ℕ → ℚ) (n : ℕ) : conv a deltaQ n = a n := by
  dsimp [conv, deltaQ]
  let p0 : ℕ × ℕ := (n, 0)
  have hp0 : p0 ∈ Finset.antidiagonal n := by
    simp [p0, Finset.mem_antidiagonal]
  refine (Finset.sum_eq_single_of_mem (s := Finset.antidiagonal n)
    (f := fun p => a p.1 * if p.2 = 0 then (1 : ℚ) else 0) (a := p0) hp0 ?_).trans ?_
  · intro p hp hne
    have hpn : p.1 + p.2 = n := by simpa [Finset.mem_antidiagonal] using! hp
    have hp2 : p.2 ≠ 0 := by
      intro hp2
      have hp1 : p.1 = n := by simpa [hp2] using! hpn
      exact hne (by ext <;> simp [p0, hp1, hp2])
    simp [hp2]
  · simp [p0]

lemma conv_deltaQ_left (a : ℕ → ℚ) (n : ℕ) : conv deltaQ a n = a n := by
  simpa [conv_comm] using! (conv_deltaQ_right (a := a) (n := n))

def powConv (a : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0 => deltaQ
  | Nat.succ k => fun n => conv a (powConv a k) n

lemma powConv_one (a : ℕ → ℚ) (n : ℕ) : powConv a 1 n = a n := by
  simpa [powConv] using! (conv_deltaQ_right (a := a) (n := n))

lemma powConv_two (a : ℕ → ℚ) (n : ℕ) : powConv a 2 n = conv a a n := by
  have h1 : powConv a 1 = a := by
    funext m
    simpa [powConv] using! (conv_deltaQ_right (a := a) (n := m))
  change conv a (powConv a 1) n = conv a a n
  exact congrArg (fun b => conv a b n) h1

lemma coeffQ_powQ_lt (a : List ℚ) :
    ∀ k : ℕ, ∀ n : ℕ, n < BleadingCoeffs.QN →
      BleadingCoeffs.coeffQ (BleadingCoeffs.powQ a k) n =
        powConv (fun i => BleadingCoeffs.coeffQ a i) k n
  | 0, n, hn => by
      have :=
        (coeffQ_ofFn_lt
          (f := fun i : Fin BleadingCoeffs.QN => if i.1 = 0 then (1 : ℚ) else 0)
          (n := n) hn)
      simpa [BleadingCoeffs.powQ, powConv, deltaQ] using! this
  | Nat.succ k, n, hn => by
      have hb : ∀ m ≤ n, BleadingCoeffs.coeffQ (BleadingCoeffs.powQ a k) m =
          powConv (fun i => BleadingCoeffs.coeffQ a i) k m := by
        intro m hm
        exact coeffQ_powQ_lt (a := a) k m (lt_of_le_of_lt hm hn)
      have h :=
        coeffQ_mulQ_lt_conv_of_eq_on_le
          (a := a) (b := BleadingCoeffs.powQ a k)
          (a' := fun i => BleadingCoeffs.coeffQ a i)
          (b' := fun i => powConv (fun j => BleadingCoeffs.coeffQ a j) k i)
          (n := n) hn
          (fun _ _ => rfl) hb
      simpa [BleadingCoeffs.powQ, powConv] using! h

private lemma coeffQ_powQ_two_lt_conv (a : List ℚ) (coeff : ℕ → ℚ) (n : ℕ)
    (hn : n < BleadingCoeffs.QN) (hcoeff : ∀ m ≤ n, BleadingCoeffs.coeffQ a m = coeff m) :
    BleadingCoeffs.coeffQ (BleadingCoeffs.powQ a 2) n = conv coeff coeff n := by
  have hpow := coeffQ_powQ_lt (a := a) 2 n hn
  have hpow2 :
      powConv (fun i => BleadingCoeffs.coeffQ a i) 2 n =
        conv (fun i => BleadingCoeffs.coeffQ a i) (fun i => BleadingCoeffs.coeffQ a i) n := by
    simpa using! (powConv_two (a := fun i => BleadingCoeffs.coeffQ a i) (n := n))
  have hconv :
      conv (fun i => BleadingCoeffs.coeffQ a i) (fun i => BleadingCoeffs.coeffQ a i) n =
        conv coeff coeff n :=
    conv_congr_of_eq_on_le
      (a := fun i => BleadingCoeffs.coeffQ a i) (a' := coeff)
      (b := fun i => BleadingCoeffs.coeffQ a i) (b' := coeff) n hcoeff hcoeff
  exact hpow.trans (hpow2.trans hconv)

lemma coeffQ_E2Q_lt (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    BleadingCoeffs.coeffQ BleadingCoeffs.E2Q n = coeffE2 n := by
  simpa [BleadingCoeffs.E2Q, BleadingCoeffs.coeffE2Q, coeffE2] using!
    (coeffQ_ofFn_lt (f := fun i : Fin BleadingCoeffs.QN => BleadingCoeffs.coeffE2Q i.1) (n := n) hn)

lemma coeffQ_E4Q_lt (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    BleadingCoeffs.coeffQ BleadingCoeffs.E4Q n = coeffE4 n := by
  simpa [BleadingCoeffs.E4Q, BleadingCoeffs.coeffE4Q, coeffE4] using!
    (coeffQ_ofFn_lt (f := fun i : Fin BleadingCoeffs.QN => BleadingCoeffs.coeffE4Q i.1) (n := n) hn)

lemma coeffQ_E6Q_lt (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    BleadingCoeffs.coeffQ BleadingCoeffs.E6Q n = coeffE6 n := by
  simpa [BleadingCoeffs.E6Q, BleadingCoeffs.coeffE6Q, coeffE6] using!
    (coeffQ_ofFn_lt (f := fun i : Fin BleadingCoeffs.QN => BleadingCoeffs.coeffE6Q i.1) (n := n) hn)

lemma coeffQ_E2SqQ_lt (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    BleadingCoeffs.coeffQ BleadingCoeffs.E2SqQ n = coeffE2Sq n := by
  have hEq : ∀ m ≤ n, BleadingCoeffs.coeffQ BleadingCoeffs.E2Q m = coeffE2 m :=
    fun m hm => coeffQ_E2Q_lt m (lt_of_le_of_lt hm hn)
  have h :=
    coeffQ_powQ_two_lt_conv (a := BleadingCoeffs.E2Q) (coeff := coeffE2) (n := n) hn hEq
  simpa [BleadingCoeffs.E2SqQ, coeffE2Sq] using! h

lemma coeffQ_E4SqQ_lt (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    BleadingCoeffs.coeffQ BleadingCoeffs.E4SqQ n = coeffE4Sq n := by
  have hEq : ∀ m ≤ n, BleadingCoeffs.coeffQ BleadingCoeffs.E4Q m = coeffE4 m :=
    fun m hm => coeffQ_E4Q_lt m (lt_of_le_of_lt hm hn)
  have h :=
    coeffQ_powQ_two_lt_conv (a := BleadingCoeffs.E4Q) (coeff := coeffE4) (n := n) hn hEq
  simpa [BleadingCoeffs.E4SqQ, coeffE4Sq] using! h

lemma coeffQ_E6SqQ_lt (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    BleadingCoeffs.coeffQ BleadingCoeffs.E6SqQ n = coeffE6Sq n := by
  have hEq : ∀ m ≤ n, BleadingCoeffs.coeffQ BleadingCoeffs.E6Q m = coeffE6 m :=
    fun m hm => coeffQ_E6Q_lt m (lt_of_le_of_lt hm hn)
  have h :=
    coeffQ_powQ_two_lt_conv (a := BleadingCoeffs.E6Q) (coeff := coeffE6) (n := n) hn hEq
  simpa [BleadingCoeffs.E6SqQ, coeffE6Sq] using! h

lemma coeffQ_E4CubeQ_lt (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    BleadingCoeffs.coeffQ BleadingCoeffs.E4CubeQ n = coeffE4Cube n := by
  have hpow := coeffQ_powQ_lt (a := BleadingCoeffs.E4Q) 3 n hn
  -- Expand `powConv 3` at index `n`.
  have hEq2 : ∀ m ≤ n,
      powConv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) 2 m =
        conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
          (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) m := by
    intro m hm
    simpa using! (powConv_two (a := fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) (n := m))
  have hpow3 :
      powConv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) 3 n =
        conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
          (fun m => conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
            (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) m) n := by
    -- Rewrite the second argument of `conv` using `hEq2`.
    simpa [powConv] using!
      (conv_congr_right_of_eq_on_le
        (a := fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
        (b := fun m => powConv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) 2 m)
        (b' := fun m => conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
          (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) m)
        n hEq2)
  -- Replace the base coefficient function by `coeffE4` on indices `≤ n`.
  have hEq : ∀ m ≤ n, BleadingCoeffs.coeffQ BleadingCoeffs.E4Q m = coeffE4 m := by
    intro m hm
    have hm' : m < BleadingCoeffs.QN := lt_of_le_of_lt hm hn
    simpa using! coeffQ_E4Q_lt m hm'
  have hconvAA :
      conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
          (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) n =
        conv coeffE4 coeffE4 n :=
    conv_congr_of_eq_on_le (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) coeffE4
      (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) coeffE4 n hEq hEq
  -- Now commute to match the file's definition `coeffE4Cube = conv coeffE4Sq coeffE4`.
  have :
      BleadingCoeffs.coeffQ BleadingCoeffs.E4CubeQ n =
        conv (conv coeffE4 coeffE4) coeffE4 n := by
    -- `powConv 3` is `conv coeffE4 (conv coeffE4 coeffE4)`, then commute.
    have hpow' : BleadingCoeffs.coeffQ BleadingCoeffs.E4CubeQ n =
        conv coeffE4 (conv coeffE4 coeffE4) n := by
      -- Rewrite `hpow` and `hpow3`, then use `hEq` to change the base coefficient function.
      -- (We only need agreement on `≤ n`.)
      have hbase_left :
          conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
              (fun m => conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
                (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) m) n =
            conv coeffE4
              (fun m => conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
                (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) m) n :=
        conv_congr_left_of_eq_on_le
          (a := fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) (a' := coeffE4)
          (b := fun m => conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
            (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) m) n hEq
      have hbase_right :
          conv coeffE4
              (fun m => conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
                (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) m) n =
            conv coeffE4 (fun m => conv coeffE4 coeffE4 m) n := by
        refine conv_congr_right_of_eq_on_le
          (a := coeffE4)
          (b := fun m => conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
                (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) m)
          (b' := fun m => conv coeffE4 coeffE4 m) n ?_
        intro m hm
        have hEqm : ∀ j ≤ m, BleadingCoeffs.coeffQ BleadingCoeffs.E4Q j = coeffE4 j := by
          intro j hj
          exact hEq j (le_trans hj hm)
        exact conv_congr_of_eq_on_le (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) coeffE4
          (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) coeffE4 m hEqm hEqm
      -- Put everything together (avoid global `funext` equalities).
      have hstart :
          BleadingCoeffs.coeffQ BleadingCoeffs.E4CubeQ n =
            conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
              (fun m => conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
                (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) m) n := by
        simpa [BleadingCoeffs.E4CubeQ] using! (hpow.trans hpow3)
      exact hstart.trans (hbase_left.trans hbase_right)
    -- Commute the convolution to match `coeffE4Cube`.
    simpa [coeffE4Cube, coeffE4Sq] using! (hpow'.trans (conv_comm coeffE4 (conv coeffE4 coeffE4) n))
  simpa [coeffE4Cube, coeffE4Sq] using! this

lemma coeffQ_E4FourthQ_lt (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    BleadingCoeffs.coeffQ BleadingCoeffs.E4FourthQ n = coeffE4Fourth n := by
  have hpow := coeffQ_powQ_lt (a := BleadingCoeffs.E4Q) 4 n hn
  -- Replace the base coefficients by `coeffE4` on indices `≤ n`.
  have hEq : ∀ m ≤ n, BleadingCoeffs.coeffQ BleadingCoeffs.E4Q m = coeffE4 m := by
    intro m hm
    have hm' : m < BleadingCoeffs.QN := lt_of_le_of_lt hm hn
    simpa using! coeffQ_E4Q_lt m hm'
  -- `powConv 4` is `conv f (conv f (conv f f))`.
  -- Rewrite to `conv (conv f f) (conv f f)` by associativity.
  have hEq2 : ∀ m ≤ n,
      powConv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) 2 m =
        conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
          (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) m := by
    intro m hm
    simpa using! (powConv_two (a := fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) (n := m))
  have hEq3 :
      ∀ m ≤ n,
        powConv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) 3 m =
          conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
            (fun j => conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
              (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) j) m := by
    intro m hm
    have :=
      conv_congr_right_of_eq_on_le
        (a := fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
        (b := fun j => powConv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) 2 j)
        (b' := fun j => conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
          (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) j)
        m (fun j hj => hEq2 j (le_trans hj hm))
    simpa [powConv] using! this
  -- Now `powConv 4` can be rewritten via `conv_assoc`.
  have hpow4' :
      powConv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) 4 n =
        conv (fun j => conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
              (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) j)
          (fun j => conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
              (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) j) n := by
    -- Rewrite `powConv 4` using `hEq3`, then rebracket via `conv_assoc`.
    let f : ℕ → ℚ := fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i
    have hb : ∀ m ≤ n, powConv f 3 m = conv f (fun j => conv f f j) m := by
      intro m hm
      simpa [f] using! (hEq3 m hm)
    calc
      powConv f 4 n = conv f (powConv f 3) n := by rfl
      _ = conv f (fun m => conv f (fun j => conv f f j) m) n := by
            simpa using!
              (conv_congr_right_of_eq_on_le (a := f) (b := fun m => powConv f 3 m)
                (b' := fun m => conv f (fun j => conv f f j) m) n hb)
      _ = conv (fun j => conv f f j) (fun j => conv f f j) n := by
            simpa using! (conv_assoc f f (conv f f) n).symm
  -- Replace `coeffQ E4FourthQ n` using `hpow` and then rewrite `conv` factors to `coeffE4`.
  have : BleadingCoeffs.coeffQ BleadingCoeffs.E4FourthQ n = coeffE4Fourth n := by
    -- First rewrite the coefficient list power as `powConv`.
    have hmain : BleadingCoeffs.coeffQ BleadingCoeffs.E4FourthQ n =
        powConv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) 4 n := by
      simpa [BleadingCoeffs.E4FourthQ] using! hpow
    -- Replace base coefficients by `coeffE4` in both `conv` factors.
    -- This is safe since each `conv` at index `n` only uses indices `≤ n`.
    have hEq' : ∀ m ≤ n, conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
            (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) m = conv coeffE4 coeffE4 m := by
      intro m hm
      have hEqm : ∀ j ≤ m, BleadingCoeffs.coeffQ BleadingCoeffs.E4Q j = coeffE4 j := by
        intro j hj
        exact hEq j (le_trans hj hm)
      exact conv_congr_of_eq_on_le (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) coeffE4
        (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) coeffE4 m hEqm hEqm
    -- Evaluate `powConv 4` at `n` in the symmetric bracketing, then swap to `coeffE4`.
    have hconv :
        powConv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) 4 n =
          conv (fun j => conv coeffE4 coeffE4 j) (fun j => conv coeffE4 coeffE4 j) n := by
      -- Use `conv_assoc` (symmetric bracketing), then change the inner `conv` via `hEq'`.
      have hsymm :
          powConv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) 4 n =
            conv (fun j => conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
                    (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) j)
              (fun j => conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
                    (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) j) n :=
        hpow4'
      -- Replace inner convs.
      -- Rewrite both `conv` factors pointwise on indices `≤ n`.
      let A : ℕ → ℚ :=
        fun j =>
          conv (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i)
            (fun i => BleadingCoeffs.coeffQ BleadingCoeffs.E4Q i) j
      let A' : ℕ → ℚ := fun j => conv coeffE4 coeffE4 j
      have hA_le : ∀ m ≤ n, A m = A' m := by
        intro m hm
        simpa [A, A'] using! hEq' m hm
      have hconv1 := conv_congr_left_of_eq_on_le (a := A) (a' := A') (b := A) n hA_le
      have hconv2 := conv_congr_right_of_eq_on_le (a := A') (b := A) (b' := A') n hA_le
      have hconvAA : conv A A n = conv A' A' n := hconv1.trans hconv2
      -- Apply this to `hsymm`.
      exact (hsymm.trans hconvAA)
    -- Conclude.
    simpa [coeffE4Fourth, coeffE4Sq] using! (hmain.trans hconv)
  exact this

/-- Match `phi2CoreQ` list coefficients with `coeffPhi2Core` for `n < QN`. -/
public lemma coeffQ_phi2CoreQ_eq (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    BleadingCoeffs.coeffQ BleadingCoeffs.phi2CoreQ n = coeffPhi2Core n := by
  -- Expand `phi2CoreQ` coefficientwise using the `addQ/smulQ` lemmas.
  have hE4Cube : BleadingCoeffs.coeffQ BleadingCoeffs.E4CubeQ n = coeffE4Cube n :=
    coeffQ_E4CubeQ_lt n hn
  have hE6Sq : BleadingCoeffs.coeffQ BleadingCoeffs.E6SqQ n = coeffE6Sq n :=
    coeffQ_E6SqQ_lt n hn
  simp [BleadingCoeffs.phi2CoreQ, coeffPhi2Core, coeffQ_addQ_lt, coeffQ_smulQ_lt, hE4Cube, hE6Sq,
    hn]

/-- Match `phi1CoreQ` list coefficients with `coeffPhi1Core` for `n < QN`. -/
public lemma coeffQ_phi1CoreQ_eq (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    BleadingCoeffs.coeffQ BleadingCoeffs.phi1CoreQ n = coeffPhi1Core n := by
  have hmul1 :
      BleadingCoeffs.coeffQ (BleadingCoeffs.mulQ BleadingCoeffs.E6Q BleadingCoeffs.E4SqQ) n =
        conv coeffE6 coeffE4Sq n :=
    coeffQ_mulQ_lt_conv_of_eq_on_le (a := BleadingCoeffs.E6Q) (b := BleadingCoeffs.E4SqQ)
      (a' := coeffE6) (b' := coeffE4Sq) (n := n) hn
      (fun m hm => coeffQ_E6Q_lt m (lt_of_le_of_lt hm hn))
      (fun m hm => coeffQ_E4SqQ_lt m (lt_of_le_of_lt hm hn))
  have hmul2 :
      BleadingCoeffs.coeffQ (BleadingCoeffs.mulQ BleadingCoeffs.E2Q BleadingCoeffs.phi2CoreQ) n =
        conv coeffE2 coeffPhi2Core n :=
    coeffQ_mulQ_lt_conv_of_eq_on_le (a := BleadingCoeffs.E2Q) (b := BleadingCoeffs.phi2CoreQ)
      (a' := coeffE2) (b' := coeffPhi2Core) (n := n) hn
      (fun m hm => coeffQ_E2Q_lt m (lt_of_le_of_lt hm hn))
      (fun m hm => coeffQ_phi2CoreQ_eq m (lt_of_le_of_lt hm hn))
  simp [BleadingCoeffs.phi1CoreQ, coeffPhi1Core, coeffQ_addQ_lt, coeffQ_smulQ_lt, hmul1, hmul2, hn]

lemma coeffQ_DeltaQ_eq (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    BleadingCoeffs.coeffQ BleadingCoeffs.DeltaQ n = coeffDelta n := by
  simp [BleadingCoeffs.DeltaQ, coeffDelta, coeffQ_smulQ_lt, coeffQ_subQ_lt, coeffQ_E4CubeQ_lt,
    coeffQ_E6SqQ_lt, hn]

/-- Match `DeltaSqQ` list coefficients with `coeffDeltaSq` for `n < QN`. -/
public lemma coeffQ_DeltaSqQ_eq (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    BleadingCoeffs.coeffQ BleadingCoeffs.DeltaSqQ n = coeffDeltaSq n := by
  have hDelta_le : ∀ m ≤ n, BleadingCoeffs.coeffQ BleadingCoeffs.DeltaQ m = coeffDelta m := by
    intro m hm
    have hm' : m < BleadingCoeffs.QN := lt_of_le_of_lt hm hn
    simpa using! coeffQ_DeltaQ_eq m hm'
  have h :=
    coeffQ_powQ_two_lt_conv (a := BleadingCoeffs.DeltaQ) (coeff := coeffDelta) (n := n) hn hDelta_le
  simpa [BleadingCoeffs.DeltaSqQ, coeffDeltaSq] using! h

/-- Match `phinumQ` list coefficients with `coeffVarphiNum` for `n < QN`. -/
public lemma coeffQ_phinumQ_eq (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    BleadingCoeffs.coeffQ BleadingCoeffs.phinumQ n = coeffVarphiNum n := by
  have hE4Fourth : BleadingCoeffs.coeffQ BleadingCoeffs.E4FourthQ n = coeffE4Fourth n :=
    coeffQ_E4FourthQ_lt n hn
  have hE6SqE4 :
      BleadingCoeffs.coeffQ (BleadingCoeffs.mulQ BleadingCoeffs.E6SqQ BleadingCoeffs.E4Q) n =
        conv coeffE6Sq coeffE4 n :=
    coeffQ_mulQ_lt_conv_of_eq_on_le (a := BleadingCoeffs.E6SqQ) (b := BleadingCoeffs.E4Q)
      (a' := coeffE6Sq) (b' := coeffE4) (n := n) hn
      (fun m hm => coeffQ_E6SqQ_lt m (lt_of_le_of_lt hm hn))
      (fun m hm => coeffQ_E4Q_lt m (lt_of_le_of_lt hm hn))
  have hE6E4Sq_le : ∀ m ≤ n,
      BleadingCoeffs.coeffQ (BleadingCoeffs.mulQ BleadingCoeffs.E6Q BleadingCoeffs.E4SqQ) m =
        conv coeffE6 coeffE4Sq m := by
    intro m hm
    have hm' : m < BleadingCoeffs.QN := lt_of_le_of_lt hm hn
    exact coeffQ_mulQ_lt_conv_of_eq_on_le (a := BleadingCoeffs.E6Q) (b := BleadingCoeffs.E4SqQ)
      (a' := coeffE6) (b' := coeffE4Sq) (n := m) hm'
      (fun j hj => coeffQ_E6Q_lt j (lt_of_le_of_lt (le_trans hj hm) hn))
      (fun j hj => coeffQ_E4SqQ_lt j (lt_of_le_of_lt (le_trans hj hm) hn))
  have hE6E4SqE2 :
      BleadingCoeffs.coeffQ
          (BleadingCoeffs.mulQ
            (BleadingCoeffs.mulQ BleadingCoeffs.E6Q BleadingCoeffs.E4SqQ)
            BleadingCoeffs.E2Q) n =
        conv (conv coeffE6 coeffE4Sq) coeffE2 n :=
    coeffQ_mulQ_lt_conv_of_eq_on_le
      (a := BleadingCoeffs.mulQ BleadingCoeffs.E6Q BleadingCoeffs.E4SqQ) (b := BleadingCoeffs.E2Q)
      (a' := fun m => conv coeffE6 coeffE4Sq m) (b' := coeffE2) (n := n) hn
      hE6E4Sq_le
      (fun m hm => coeffQ_E2Q_lt m (lt_of_le_of_lt hm hn))
  have hphi2E2Sq :
      BleadingCoeffs.coeffQ (BleadingCoeffs.mulQ BleadingCoeffs.phi2CoreQ BleadingCoeffs.E2SqQ) n =
        conv coeffPhi2Core coeffE2Sq n :=
    coeffQ_mulQ_lt_conv_of_eq_on_le (a := BleadingCoeffs.phi2CoreQ) (b := BleadingCoeffs.E2SqQ)
      (a' := coeffPhi2Core) (b' := coeffE2Sq) (n := n) hn
      (fun m hm => coeffQ_phi2CoreQ_eq m (lt_of_le_of_lt hm hn))
      (fun m hm => coeffQ_E2SqQ_lt m (lt_of_le_of_lt hm hn))
  -- Assemble the coefficient formula for `phinumQ`.
  have hPhi2Core :
      coeffPhi2Core = fun m => (-(49 * coeffE4Cube m)) + (25 : ℚ) * coeffE6Sq m := by
    funext m
    simp [coeffPhi2Core]
  simp [BleadingCoeffs.phinumQ, coeffVarphiNum, coeffQ_addQ_lt, coeffQ_subQ_lt, coeffQ_smulQ_lt,
    hE4Fourth, hE6SqE4, hE6E4SqE2, hphi2E2Sq, hPhi2Core, hn]

/-!
### Convenience lemmas for `coeffQ` at small indices
-/

/-- Zero-th coefficient of a list Cauchy product. -/
public lemma coeffQ_mulQ_zero (a b : List ℚ) :
    BleadingCoeffs.coeffQ (BleadingCoeffs.mulQ a b) 0 =
      BleadingCoeffs.coeffQ a 0 * BleadingCoeffs.coeffQ b 0 := by
  simpa using! (coeffQ_mulQ_lt (a := a) (b := b) (n := 0) (hn := by decide))

/-- First coefficient of a list Cauchy product. -/
public lemma coeffQ_mulQ_one (a b : List ℚ) :
    BleadingCoeffs.coeffQ (BleadingCoeffs.mulQ a b) 1 =
      BleadingCoeffs.coeffQ a 0 * BleadingCoeffs.coeffQ b 1 +
        BleadingCoeffs.coeffQ a 1 * BleadingCoeffs.coeffQ b 0 := by
  simpa [Finset.sum_range_succ] using!
    (coeffQ_mulQ_lt (a := a) (b := b) (n := 1) (hn := by decide))

/-- Constant coefficient of a list power: `coeffQ (powQ a k) 0 = (coeffQ a 0)^k`. -/
public lemma coeffQ_powQ_zero (a : List ℚ) : ∀ k : ℕ,
    BleadingCoeffs.coeffQ (BleadingCoeffs.powQ a k) 0 = (BleadingCoeffs.coeffQ a 0) ^ k
  | 0 => by
      -- `powQ a 0` is the constant series `1`.
      simp [BleadingCoeffs.powQ, BleadingCoeffs.coeffQ, BleadingCoeffs.QN]
  | Nat.succ k => by
      -- `powQ a (k+1) = mulQ a (powQ a k)`.
      simp [BleadingCoeffs.powQ, coeffQ_mulQ_zero, coeffQ_powQ_zero a k, pow_succ, mul_comm]

/-- Zero-th coefficient of `addQ`. -/
public lemma coeffQ_addQ_zero (a b : List ℚ) :
    BleadingCoeffs.coeffQ (BleadingCoeffs.addQ a b) 0 =
      BleadingCoeffs.coeffQ a 0 + BleadingCoeffs.coeffQ b 0 := by
  simpa using! (coeffQ_addQ_lt (a := a) (b := b) (n := 0) (hn := by decide))

/-- Zero-th coefficient of `smulQ`. -/
public lemma coeffQ_smulQ_zero (c : ℚ) (a : List ℚ) :
    BleadingCoeffs.coeffQ (BleadingCoeffs.smulQ c a) 0 = c * BleadingCoeffs.coeffQ a 0 := by
  simpa using! (coeffQ_smulQ_lt (c := c) (a := a) (n := 0) (hn := by decide))

/-- Zero-th coefficient of `negQ`. -/
public lemma coeffQ_negQ_zero (a : List ℚ) :
    BleadingCoeffs.coeffQ (BleadingCoeffs.negQ a) 0 = -BleadingCoeffs.coeffQ a 0 := by
  simpa using! (coeffQ_negQ_lt (a := a) (n := 0) (hn := by decide))

/-- Zero-th coefficient of `subQ`. -/
public lemma coeffQ_subQ_zero (a b : List ℚ) :
    BleadingCoeffs.coeffQ (BleadingCoeffs.subQ a b) 0 =
      BleadingCoeffs.coeffQ a 0 - BleadingCoeffs.coeffQ b 0 := by
  simpa using! (coeffQ_subQ_lt (a := a) (b := b) (n := 0) (hn := by decide))

/-- Constant coefficient of the truncated `E₂` list. -/
public lemma coeffQ_E2Q_zero : BleadingCoeffs.coeffQ BleadingCoeffs.E2Q 0 = 1 := by
  simpa [coeffE2] using! (coeffQ_E2Q_lt (n := 0) (hn := by decide))

/-- Constant coefficient of the truncated `E₄` list. -/
public lemma coeffQ_E4Q_zero : BleadingCoeffs.coeffQ BleadingCoeffs.E4Q 0 = 1 := by
  simpa [coeffE4] using! (coeffQ_E4Q_lt (n := 0) (hn := by decide))

/-- Constant coefficient of the truncated `E₆` list. -/
public lemma coeffQ_E6Q_zero : BleadingCoeffs.coeffQ BleadingCoeffs.E6Q 0 = 1 := by
  simpa [coeffE6] using! (coeffQ_E6Q_lt (n := 0) (hn := by decide))

end SpherePacking.Dim24.AppendixA
