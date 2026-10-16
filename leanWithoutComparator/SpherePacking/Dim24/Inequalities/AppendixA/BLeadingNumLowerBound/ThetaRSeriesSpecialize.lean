/- Specializing `Θ₄(it)` and `Θ₂(it)` as `r`-series. -/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import
SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiRSeriesSetup.SparseCoeffs
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.Numerators

/-!
#### Specializing `Θ₄(it)` and `Θ₂(it)` as `r`-series

These are the standard theta identities on the imaginary axis, rewritten using `r(t)=exp(-π t)`.
-/

open scoped Real
open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.AppendixA


lemma cexp_pi_I_mul_sq_mul_it (t : ℝ) (ht0 : 0 < t) (n : ℕ) :
    Complex.exp ((Real.pi : ℂ) * (Complex.I : ℂ) * (n : ℂ) ^ (2 : ℕ) * (it t ht0 : ℂ)) =
      (rC t) ^ (n ^ (2 : ℕ)) := by
  have hit : (it t ht0 : ℂ) = (Complex.I : ℂ) * (t : ℂ) := rfl
  have harg :
      ((Real.pi : ℂ) * (Complex.I : ℂ) * (n : ℂ) ^ (2 : ℕ) * (it t ht0 : ℂ)) =
        (n ^ (2 : ℕ)) * ((-Real.pi * t : ℝ) : ℂ) := by
    -- `π * I * n^2 * (I*t) = (n^2) * (-π*t)`.
    -- Start by pulling out `it` and re-associating.
    simp [hit, pow_two, mul_assoc, mul_left_comm, mul_comm]
    ring_nf
    simp [pow_two, Complex.I_mul_I, mul_assoc]
  rw [harg]
  simpa [rC, r] using! (Complex.exp_nat_mul ((-Real.pi * t : ℝ) : ℂ) (n ^ (2 : ℕ)))

lemma cexp_pi_I_mul_sq_mul_it' (t : ℝ) (ht0 : 0 < t) (n : ℕ) :
    Complex.exp ((Real.pi : ℂ) * ((Complex.I : ℂ) * ((n : ℂ) ^ (2 : ℕ) * (it t ht0 : ℂ)))) =
      (rC t) ^ (n ^ (2 : ℕ)) := by
  -- Same statement as `cexp_pi_I_mul_sq_mul_it`, with a different parenthesization.
  simpa [mul_assoc] using! (cexp_pi_I_mul_sq_mul_it (t := t) ht0 n)

lemma cexp_I_mul_pi_mul_sq_mul_it (t : ℝ) (ht0 : 0 < t) (n : ℕ) :
    Complex.exp ((Complex.I : ℂ) * ((Real.pi : ℂ) * ((n : ℂ) ^ (2 : ℕ) * (it t ht0 : ℂ)))) =
      (rC t) ^ (n ^ (2 : ℕ)) := by
  -- Same statement again, matching the parenthesization produced by `simp [Θ₄_term]`.
  simpa [mul_assoc, mul_left_comm, mul_comm] using! (cexp_pi_I_mul_sq_mul_it (t := t) ht0 n)

/-- Summability of the theta term defining `Θ₄(it t)` as a `tsum` over `ℤ`. -/
public lemma summable_theta4_term_it (t : ℝ) (ht0 : 0 < t) :
    Summable (fun z : ℤ => Θ₄_term z (it t ht0)) := by
  -- Reduce to summability of `jacobiTheta₂_term` (Mathlib), using `Θ₄_term_as_jacobiTheta₂_term`.
  have hsJac :
      Summable (fun n : ℤ => jacobiTheta₂_term n (1 / 2 : ℂ) (it t ht0 : ℂ)) := by
    have hIm : 0 < (it t ht0 : ℂ).im := by
      -- `it t = I*t` has imaginary part `t`.
      simpa [it, mul_assoc] using! ht0
    exact (summable_jacobiTheta₂_term_iff (z := (1 / 2 : ℂ)) (τ := (it t ht0 : ℂ))).2 hIm
  have hterm : (fun n : ℤ => Θ₄_term n (it t ht0)) =
      fun n : ℤ => jacobiTheta₂_term n (1 / 2 : ℂ) (it t ht0 : ℂ) := by
    funext n
    simpa using! (Θ₄_term_as_jacobiTheta₂_term (τ := it t ht0) n)
  simpa [hterm] using! hsJac


/-- Specialize `Θ₄(it t)` as the `rseries` of `theta01CoeffFun` for `t ≥ 1`. -/
public lemma Theta4_it_eq_rseries_theta01CoeffFun (t : ℝ) (ht : 1 ≤ t) :
    Θ₄ (it t (lt_of_lt_of_le (by simp : (0 : ℝ) < 1) ht)) = rseries theta01CoeffFun t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by simp : (0 : ℝ) < 1) ht
  set τ : ℍ := it t ht0
  -- Rewrite the target `rseries` as the standard square-indexed `Θ₄` expansion.
  rw [rseries_theta01_eq_tsum_squares (t := t) ht]
  -- Split the ℤ-sum defining `Θ₄` into nonnegative and negative terms.
  have hs : Summable (fun z : ℤ => Θ₄_term z τ) := summable_theta4_term_it (t := t) ht0
  have hsplit :=
    (tsum_int_eq_tsum_nat_add_tsum_negSucc (f := fun z : ℤ => Θ₄_term z τ) hs)
  -- Define `g n = (-1)^n * r^{n^2}`.
  let g : ℕ → ℂ := fun n => ((-1 : ℂ) ^ n) * (rC t) ^ (n ^ (2 : ℕ))
  have hpos : (∑' n : ℕ, Θ₄_term (n : ℤ) τ) = ∑' n : ℕ, g n := by
    refine tsum_congr ?_
    intro n
    simp
      [Θ₄_term, τ, g, cexp_I_mul_pi_mul_sq_mul_it (t := t) ht0 n, mul_assoc, mul_comm]
  have hneg : (∑' n : ℕ, Θ₄_term (Int.negSucc n) τ) = ∑' n : ℕ, g (n + 1) := by
    refine tsum_congr ?_
    intro n
    have hsign : ((-1 : ℂ) ^ (Int.negSucc n)) = ((-1 : ℂ) ^ (n + 1)) := by
      have heven : Even (Int.negSucc n) ↔ Even (n + 1) := by
        grind only [= Int.even_iff, = Nat.even_iff]
      by_cases h : Even (n + 1) <;> simp [neg_one_pow_eq_ite, h]
    have hexp :
        Complex.exp (π * (Complex.I : ℂ) * (Int.negSucc n : ℂ) ^ (2 : ℕ) * (it t ht0 : ℂ)) =
          (rC t) ^ ((n + 1) ^ (2 : ℕ)) := by
      have hsquare : (Int.negSucc n : ℂ) ^ (2 : ℕ) = ((n + 1 : ℕ) : ℂ) ^ (2 : ℕ) := by
        have hcast : (Int.negSucc n : ℂ) = -((n + 1 : ℕ) : ℂ) := by
          simp
        calc
          (Int.negSucc n : ℂ) ^ (2 : ℕ) = (-((n + 1 : ℕ) : ℂ)) ^ (2 : ℕ) := by
            simp [hcast]
          _ = ((n + 1 : ℕ) : ℂ) ^ (2 : ℕ) := by
            simp [pow_two]
            ring_nf
      rw [hsquare]
      simpa [mul_assoc, mul_left_comm, mul_comm] using!
        (cexp_pi_I_mul_sq_mul_it (t := t) ht0 (n + 1))
    dsimp [Θ₄_term, g]
    have hexpτ :
        Complex.exp (π * (Complex.I : ℂ) * (Int.negSucc n : ℂ) ^ (2 : ℕ) * (τ : ℂ)) =
          (rC t) ^ ((n + 1) ^ (2 : ℕ)) := by
      simpa [τ, mul_assoc, mul_left_comm, mul_comm] using! hexp
    -- Now rewrite both factors.
    rw [hsign, hexpτ]
  have hTheta :
      Θ₄ τ = (∑' n : ℕ, g n) + (∑' n : ℕ, g (n + 1)) := by
    simpa [Θ₄, hpos, hneg, τ] using! hsplit
  -- Summability of `g`, dominated by a geometric series since `‖rC t‖ < 1` and `n^2 ≥ n`.
  have hsG : Summable g := by
    have hr0 : 0 ≤ r t := (Real.exp_pos _).le
    have hrle : r t ≤ (1 : ℝ) / 23 := r_le_one_div_23 (t := t) ht
    have hr1 : r t < 1 := lt_of_le_of_lt hrle (by norm_num)
    have hrnorm : ‖rC t‖ < 1 := by
      simpa [rC, Real.norm_eq_abs, abs_of_nonneg hr0] using! hr1
    have hdom : ∀ n : ℕ, ‖g n‖ ≤ ‖(rC t) ^ n‖ := by
      intro n
      have hpow : n ≤ n ^ (2 : ℕ) := by
        simpa [pow_two] using! Nat.le_mul_self n
      have h0 : ‖(rC t)‖ ≤ 1 := le_of_lt hrnorm
      have hpow' : ‖(rC t)‖ ^ (n ^ (2 : ℕ)) ≤ ‖(rC t)‖ ^ n :=
        pow_le_pow_of_le_one (norm_nonneg _) h0 hpow
      have hnorm_pow :
          ‖(rC t) ^ (n ^ (2 : ℕ))‖ ≤ ‖(rC t) ^ n‖ := by
        simpa [norm_pow] using! hpow'
      calc
        ‖g n‖ = ‖((-1 : ℂ) ^ n)‖ * ‖(rC t) ^ (n ^ (2 : ℕ))‖ := by
          simp [g]
        _ = ‖(rC t) ^ (n ^ (2 : ℕ))‖ := by simp
        _ ≤ ‖(rC t) ^ n‖ := hnorm_pow
    have hsGeom : Summable (fun n : ℕ => (rC t) ^ n) := summable_geometric_of_norm_lt_one hrnorm
    exact
      Summable.of_norm_bounded (g := fun n : ℕ => ‖(rC t) ^ n‖)
        (hsGeom.norm) (by intro n; simpa using! hdom n)
  have hsplitNat : (∑' n : ℕ, g n) = g 0 + ∑' n : ℕ, g (n + 1) := by
    simpa using! (hsG.sum_add_tsum_nat_add 1).symm
  have hTheta' : Θ₄ τ = g 0 + (2 : ℂ) * (∑' n : ℕ, g (n + 1)) := by
    rw [hTheta, hsplitNat]
    ring
  have hg0 : g 0 = (1 : ℂ) := by simp [g]
  -- Identify the square-indexed coefficient sum with `g 0 + 2 * ∑ g(n+1)`.
  have hsq :
      (∑' k : ℕ,
          ((if k = 0 then (1 : ℤ) else 2 * ((-1 : ℤ) ^ k) : ℤ) : ℂ) * (rC t) ^ (k ^ (2 : ℕ))) =
        g 0 + (2 : ℂ) * (∑' n : ℕ, g (n + 1)) := by
    have hsummand :
        (fun k : ℕ =>
            ((if k = 0 then (1 : ℤ) else 2 * ((-1 : ℤ) ^ k) : ℤ) : ℂ) * (rC t) ^ (k ^ (2 : ℕ))) =
          fun k : ℕ => if k = 0 then g 0 else (2 : ℂ) * g k := by
      funext k
      by_cases hk : k = 0
      · subst hk
        simp [hg0, g]
      · simp [hk, g, mul_assoc, mul_left_comm, mul_comm]
    let F : ℕ → ℂ := fun k => if k = 0 then g 0 else (2 : ℂ) * g k
    have hsF : Summable F := by
      refine
        Summable.of_norm_bounded (g := fun k : ℕ => (2 : ℝ) * ‖g k‖)
          ((hsG.norm).mul_left (2 : ℝ)) ?_
      intro k
      by_cases hk : k = 0
      · subst hk
        have hk0 : (0 : ℝ) ≤ ‖g 0‖ := norm_nonneg _
        have h12 : (1 : ℝ) ≤ 2 := by norm_num
        simpa [one_mul] using! (mul_le_mul_of_nonneg_right h12 hk0)
      · simp [F, hk]
    have hsplit0 : (∑' k : ℕ, F k) = F 0 + ∑' k : ℕ, ite (k = 0) 0 (F k) := by
      simpa using! (hsF.tsum_eq_add_tsum_ite 0)
    have htail :
        (∑' k : ℕ, ite (k = 0) 0 (F k)) = ∑' n : ℕ, (2 : ℂ) * g (n + 1) := by
      let f0 : ℕ → ℂ := fun k => ite (k = 0) 0 (F k)
      have hf0 : Summable f0 := by
        refine
          Summable.of_norm_bounded (g := fun k : ℕ => (2 : ℝ) * ‖g k‖)
            ((hsG.norm).mul_left (2 : ℝ)) ?_
        intro k
        by_cases hk : k = 0
        · subst hk
          simp [f0, F]
        · simp [f0, F, hk]
      have hzero : ∀ k : ℕ, k ∉ Set.range Nat.succ → f0 k = 0 := by
        intro k hk
        have hk0 : k = 0 := by
          by_contra hk0
          have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
          exact hk (Nat.mem_range_succ k |>.2 hkpos)
        subst hk0
        simp [f0]
      have hreindex : (∑' k : ℕ, f0 k) = ∑' n : ℕ, f0 (Nat.succ n) :=
        tsum_eq_tsum_comp_of_eq_zero_off_range
          (f := f0) hf0 (g := Nat.succ) Nat.succ_injective hzero
      assumption
    have hF0 : F 0 = g 0 := by simp [F]
    have hpull : (∑' n : ℕ, (2 : ℂ) * g (n + 1)) = (2 : ℂ) * (∑' n : ℕ, g (n + 1)) := by
      simp [tsum_mul_left]
    lia
  grind only

/-!
#### Specializing `Θ₂(it)` as an `r`-series

On the imaginary axis, `Θ₂(it)` has the classical expansion
`Θ₂(it) = exp(-π t / 4) * (2 * ∑_{k ≥ 0} r^{k(k+1)})` with `r = exp(-π t)`.

The inner series is `rseries theta10CoeffFun t`.
-/

/-- Symmetry of the `Θ₂` term under `m ↦ -m-1` (used to pair positive/negative terms). -/
public lemma Theta2_term_negSucc (m : ℕ) (τ : ℍ) :
    Θ₂_term (Int.negSucc m) τ = Θ₂_term (m : ℤ) τ := by
  -- `Int.negSucc m = -(m+1)`, and `(-m-1/2)^2 = (m+1/2)^2`.
  have hm : (Int.negSucc m : ℂ) + (1 / 2 : ℂ) = (-(m : ℂ) - 1 + (2 : ℂ)⁻¹) := by
    simp [Int.cast_negSucc, one_div]
    ring_nf
  have hp : (m : ℂ) + (1 / 2 : ℂ) = (m : ℂ) + (2 : ℂ)⁻¹ := by simp [one_div]
  have hs :
      (-(m : ℂ) - 1 + (2 : ℂ)⁻¹) ^ (2 : ℕ) = ((m : ℂ) + (2 : ℂ)⁻¹) ^ (2 : ℕ) := by
    ring
  have hsquare :
      ((Int.negSucc m : ℂ) + (1 / 2 : ℂ)) ^ (2 : ℕ) = ((m : ℂ) + (1 / 2 : ℂ)) ^ (2 : ℕ) := by
    lia
  dsimp [Θ₂_term]
  simp_all

/-- Summability of the theta term defining `Θ₂(it t)` as a `tsum` over `ℤ`. -/
public lemma summable_theta2_term_it (t : ℝ) (ht0 : 0 < t) :
    Summable (fun z : ℤ => Θ₂_term z (it t ht0)) := by
  -- Reduce to summability of `jacobiTheta₂_term` (Mathlib), using `Θ₂_term_as_jacobiTheta₂_term`.
  have hsJac :
      Summable (fun n : ℤ =>
        jacobiTheta₂_term n (((it t ht0 : ℍ) : ℂ) / 2) (it t ht0 : ℂ)) := by
    have hIm : 0 < (it t ht0 : ℂ).im := by
      simp [it, ht0]
    exact (summable_jacobiTheta₂_term_iff (z := ((it t ht0 : ℂ) / 2)) (τ := (it t ht0 : ℂ))).2 hIm
  refine (hsJac.mul_left (Complex.exp (π * (Complex.I : ℂ) * (it t ht0 : ℂ) / 4))).congr ?_
  intro n
  simp [Θ₂_term_as_jacobiTheta₂_term]

/-- Specialize `Θ₂(it t)` as `exp(-pi t / 4) * rseries theta10CoeffFun t` for `t ≥ 1`. -/
public lemma Theta2_it_eq_rseries_theta10CoeffFun (t : ℝ) (ht : 1 ≤ t) :
    Θ₂ (it t (lt_of_lt_of_le (by simp : (0 : ℝ) < 1) ht)) =
      ((Real.exp (-Real.pi * t / 4) : ℝ) : ℂ) * rseries theta10CoeffFun t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by simp : (0 : ℝ) < 1) ht
  set τ : ℍ := it t ht0
  have hs : Summable (fun z : ℤ => Θ₂_term z τ) := summable_theta2_term_it (t := t) ht0
  have hsplit :=
    (tsum_int_eq_tsum_nat_add_tsum_negSucc (f := fun z : ℤ => Θ₂_term z τ) hs)
  have hneg :
      (∑' n : ℕ, Θ₂_term (Int.negSucc n) τ) = ∑' n : ℕ, Θ₂_term (n : ℤ) τ := by
    refine tsum_congr ?_
    intro n
    simpa using! (Theta2_term_negSucc (m := n) (τ := τ))
  have hsum :
      Θ₂ τ = (2 : ℂ) * ∑' n : ℕ, Θ₂_term (n : ℤ) τ := by
    have :
        (∑' z : ℤ, Θ₂_term z τ) =
          (∑' n : ℕ, Θ₂_term (n : ℤ) τ) + (∑' n : ℕ, Θ₂_term (Int.negSucc n) τ) := by
      simpa using! hsplit
    calc
      Θ₂ τ = (∑' z : ℤ, Θ₂_term z τ) := rfl
      _ =
          (∑' n : ℕ, Θ₂_term (n : ℤ) τ) + (∑' n : ℕ, Θ₂_term (Int.negSucc n) τ) := this
      _ = (∑' n : ℕ, Θ₂_term (n : ℤ) τ) + (∑' n : ℕ, Θ₂_term (n : ℤ) τ) := by simp [hneg]
      _ = (2 : ℂ) * ∑' n : ℕ, Θ₂_term (n : ℤ) τ := by ring
  have hpos :
      ∑' n : ℕ, Θ₂_term (n : ℤ) τ =
        Complex.exp ((-Real.pi * t / 4 : ℝ) : ℂ) * ∑' n : ℕ, (rC t) ^ triangular n := by
    have hit : (τ : ℂ) = (Complex.I : ℂ) * (t : ℂ) := by
      simp [τ, it]
    have htsum :
        (∑' n : ℕ, Θ₂_term (n : ℤ) τ) =
          ∑' n : ℕ, Complex.exp ((-Real.pi * t / 4 : ℝ) : ℂ) * (rC t) ^ triangular n := by
      refine tsum_congr ?_
      intro n
      have hsquare :
          (((n : ℤ) : ℂ) + (1 / 2 : ℂ)) ^ (2 : ℕ) = (triangular n : ℂ) + (1 / 4 : ℂ) := by
        dsimp [triangular]
        simp [Nat.cast_mul, Nat.cast_add]
        ring
      dsimp [Θ₂_term]
      have harg :
          (π * (Complex.I : ℂ) * (((n : ℤ) : ℂ) + (1 / 2 : ℂ)) ^ (2 : ℕ) * (τ : ℂ)) =
            ((-Real.pi * t / 4 : ℝ) : ℂ) + (triangular n) * ((-Real.pi * t : ℝ) : ℂ) := by
        -- Reduce using `τ = I * t`, `I^2 = -1`, and the square expansion.
        rw [hsquare]
        simp [hit, mul_assoc, mul_left_comm, mul_comm, triangular, Nat.cast_mul, Nat.cast_add]
        grind only [= I_mul_I_mul]
      rw [harg, Complex.exp_add]
      rw [Complex.exp_nat_mul ((-Real.pi * t : ℝ) : ℂ) (triangular n)]
      have hbase : Complex.exp ((-Real.pi * t : ℝ) : ℂ) = rC t := by
        simp [rC, r]
      -- Raise the base identity to `triangular n`.
      simpa using! congrArg (fun z : ℂ => z ^ triangular n) hbase
    have hmul :
        (∑' n : ℕ, Complex.exp ((-Real.pi * t / 4 : ℝ) : ℂ) * (rC t) ^ triangular n) =
          Complex.exp ((-Real.pi * t / 4 : ℝ) : ℂ) * (∑' n : ℕ, (rC t) ^ triangular n) :=
          tsum_mul_left
    exact htsum.trans hmul
  have hT10 :
      ∑' n : ℕ, ((2 : ℤ) : ℂ) * (rC t) ^ triangular n = rseries theta10CoeffFun t := by
    simpa [two_mul, mul_assoc] using! (rseries_theta10_eq_tsum_triangular (t := t) ht).symm
  have hfac :
      Complex.exp ((-Real.pi * t / 4 : ℝ) : ℂ) = ((Real.exp (-Real.pi * t / 4) : ℝ) : ℂ) := by
    simp
  calc
    Θ₂ τ
        = (2 : ℂ) * (∑' n : ℕ, Θ₂_term (n : ℤ) τ) := hsum
    _ =
        (2 : ℂ) * (Complex.exp ((-Real.pi * t / 4 : ℝ) : ℂ) * ∑' n : ℕ, (rC t) ^ triangular n) := by
          simp [hpos]
    _ =
        Complex.exp ((-Real.pi * t / 4 : ℝ) : ℂ) *
          (∑' n : ℕ, ((2 : ℤ) : ℂ) * (rC t) ^ triangular n) := by
          have hmul :
              (2 : ℂ) * (∑' n : ℕ, (rC t) ^ triangular n) =
                ∑' n : ℕ, ((2 : ℤ) : ℂ) * (rC t) ^ triangular n := by
            simpa [mul_assoc] using!
              (tsum_mul_left (a := (2 : ℂ)) (f := fun n : ℕ => (rC t) ^ triangular n)).symm
          -- Pull out `cexp` and rewrite the remaining factor using `hmul`.
          calc
            (2 : ℂ) *
                (Complex.exp ((-Real.pi * t / 4 : ℝ) : ℂ) * ∑' n : ℕ, (rC t) ^ triangular n) =
                Complex.exp ((-Real.pi * t / 4 : ℝ) : ℂ) *
                  ((2 : ℂ) * (∑' n : ℕ, (rC t) ^ triangular n)) := by ring
            _ = Complex.exp ((-Real.pi * t / 4 : ℝ) : ℂ) *
                  (∑' n : ℕ, ((2 : ℤ) : ℂ) * (rC t) ^ triangular n) := by simp [hmul]
    _ = ((Real.exp (-Real.pi * t / 4) : ℝ) : ℂ) * rseries theta10CoeffFun t := by
          simpa [hT10, hfac]

/-- Rewrite `psiI_num` as a polynomial expression in `H₂` and `H₄`. -/
public lemma psiI_num_eq_H (z : ℍ) :
    psiI_num z =
      7 * (H₄ z) ^ (5 : ℕ) * (H₂ z) ^ (2 : ℕ) +
        7 * (H₄ z) ^ (6 : ℕ) * (H₂ z) +
          2 * (H₄ z) ^ (7 : ℕ) := by
  -- Rewrite all theta powers in terms of `H₂ = Θ₂^4` and `H₄ = Θ₄^4`.
  have h8 : (Θ₂ z) ^ (8 : ℕ) = (H₂ z) ^ (2 : ℕ) := by
    -- `(Θ₂^4)^2 = Θ₂^8`.
    simpa [H₂, pow_mul, show (4 * 2 : ℕ) = 8 by decide] using! (pow_mul (Θ₂ z) 4 2)
  have h20 : (Θ₄ z) ^ (20 : ℕ) = (H₄ z) ^ (5 : ℕ) := by
    simpa [H₄, pow_mul, show (4 * 5 : ℕ) = 20 by decide] using! (pow_mul (Θ₄ z) 4 5)
  have h24 : (Θ₄ z) ^ (24 : ℕ) = (H₄ z) ^ (6 : ℕ) := by
    simpa [H₄, pow_mul, show (4 * 6 : ℕ) = 24 by decide] using! (pow_mul (Θ₄ z) 4 6)
  have h28 : (Θ₄ z) ^ (28 : ℕ) = (H₄ z) ^ (7 : ℕ) := by
    simpa [H₄, pow_mul, show (4 * 7 : ℕ) = 28 by decide] using! (pow_mul (Θ₄ z) 4 7)
  have h4 : (Θ₂ z) ^ (4 : ℕ) = H₂ z := by simp [H₂]
  -- Assemble.
  simp [psiI_num, h20, h24, h28, h8, h4, mul_left_comm, mul_comm, add_assoc]


end SpherePacking.Dim24.AppendixA
