-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import
SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiCoeffFunAndTail.Basic
public import
SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.ThetaRSeriesSpecialize

/-!
### Coefficients for the `ψI` numerator

We define the dense integer coefficient function `psiCoeffFun : ℕ → ℤ` built from theta
coefficients via `convZ` and `powConvZ`. For `t ≥ 1` we show that `psiI_num (it t)` equals the
corresponding `rseries`, and we record a polynomial growth bound for `psiCoeffFun`.
-/

open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.AppendixA

/-- Dense integer coefficient function for the `r`-series expansion of `psiI_num`. -/
@[expose] public def psiCoeffFun : ℕ → ℤ :=
  let h4 : ℕ → ℤ := powConvZ theta01CoeffFun 4
  let h2base : ℕ → ℤ := powConvZ theta10CoeffFun 4
  let h2 : ℕ → ℤ := shift1Fun h2base
  fun n =>
    7 * convZ (powConvZ h4 5) (powConvZ h2 2) n +
      7 * convZ (powConvZ h4 6) (powConvZ h2 1) n +
        2 * powConvZ h4 7 n

lemma abs_theta01CoeffFun_le_two_real (n : ℕ) :
    |(theta01CoeffFun n : ℝ)| ≤ (2 : ℝ) :=
  by exact_mod_cast abs_theta01CoeffFun_le_two n

lemma abs_theta10CoeffFun_le_two_real (n : ℕ) :
    |(theta10CoeffFun n : ℝ)| ≤ (2 : ℝ) :=
  by exact_mod_cast abs_theta10CoeffFun_le_two n

lemma H4_it_eq_rseries_powConvZ_theta01 (t : ℝ) (ht : 1 ≤ t) :
    let ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    H₄ (it t ht0) = rseries (powConvZ theta01CoeffFun 4) t := by
  intro ht0
  have hpow4 :
      rseries (powConvZ theta01CoeffFun 4) t = (rseries theta01CoeffFun t) ^ (4 : ℕ) :=
    rseries_powConvZ_eq_pow (t := t) (ht0 := ht0) (a := theta01CoeffFun)
      (C := (2 : ℝ)) (k := 0)
      (fun n => by simpa [pow_zero] using! abs_theta01CoeffFun_le_two_real n) 4
  calc
    H₄ (it t ht0) = (Θ₄ (it t ht0)) ^ (4 : ℕ) := by simp [H₄]
    _ = (rseries theta01CoeffFun t) ^ (4 : ℕ) := by
          simpa using! congrArg (fun z => z ^ (4 : ℕ))
            (Theta4_it_eq_rseries_theta01CoeffFun (t := t) ht)
    _ = rseries (powConvZ theta01CoeffFun 4) t := by simpa using! hpow4.symm

lemma H2_it_eq_rseries_shift1_powConvZ_theta10 (t : ℝ) (ht : 1 ≤ t) :
    let ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    H₂ (it t ht0) = rseries (shift1Fun (powConvZ theta10CoeffFun 4)) t := by
  intro ht0
  have hTheta2 :
      Θ₂ (it t ht0) =
        ((Real.exp (-Real.pi * t / 4) : ℝ) : ℂ) * rseries theta10CoeffFun t := by
    simpa using! (Theta2_it_eq_rseries_theta10CoeffFun (t := t) ht)
  have hpow4 :
      rseries (powConvZ theta10CoeffFun 4) t = (rseries theta10CoeffFun t) ^ (4 : ℕ) :=
    rseries_powConvZ_eq_pow (t := t) (ht0 := ht0) (a := theta10CoeffFun)
      (C := (2 : ℝ)) (k := 0)
      (fun n => by simpa [pow_zero] using! abs_theta10CoeffFun_le_two_real n) 4
  have hexp : (((Real.exp (-Real.pi * t / 4) : ℝ) : ℂ) ^ (4 : ℕ)) = rC t := by
    have h4 : (4 : ℝ) ≠ 0 := by norm_num
    have hmul : (4 : ℝ) * (-(Real.pi * t) / 4) = -Real.pi * t := by
      linarith
    have hfacR : (Real.exp (-Real.pi * t / 4)) ^ (4 : ℕ) = Real.exp (-Real.pi * t) := by
      simpa [hmul] using! (Real.exp_nat_mul (-Real.pi * t / 4) 4).symm
    have := congrArg (fun x : ℝ => (x : ℂ)) hfacR
    simpa [rC, r] using! this
  have hshift :
      rseries (shift1Fun (powConvZ theta10CoeffFun 4)) t =
        (rC t) * rseries (powConvZ theta10CoeffFun 4) t := by
    -- Use the generic shift lemma with the coefficient bound for `powConvZ theta10CoeffFun 4`.
    have hb4 :
        ∀ n : ℕ,
          |((powConvZ theta10CoeffFun 4) n : ℝ)| ≤
            (16 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (3 : ℕ)) := by
      intro n
      have h :=
        abs_powConvZ_le (a := theta10CoeffFun) (C := (2 : ℝ)) (k := 0)
          (fun n => by simpa [pow_zero] using! abs_theta10CoeffFun_le_two_real n) 4 n
      have hpow2 : (2 : ℝ) ^ (4 : ℕ) = 16 := by norm_num
      simpa [powConvZ, pow_zero, Nat.mul_zero, Nat.zero_add, Nat.succ_sub_one, hpow2] using! h
    exact rseries_shift1Fun_eq_mul t ht0 (powConvZ theta10CoeffFun 4) 16 3 hb4
  calc
    H₂ (it t ht0) = (Θ₂ (it t ht0)) ^ (4 : ℕ) := by simp [H₂]
    _ =
        (((Real.exp (-Real.pi * t / 4) : ℝ) : ℂ) * rseries theta10CoeffFun t) ^ (4 : ℕ) := by
          simp [hTheta2]
    _ =
        (((Real.exp (-Real.pi * t / 4) : ℝ) : ℂ) ^ (4 : ℕ)) *
          (rseries theta10CoeffFun t) ^ (4 : ℕ) := by
          simp [mul_pow]
    _ = (rC t) * rseries (powConvZ theta10CoeffFun 4) t := by
          rw [hexp, ← hpow4]
    _ = rseries (shift1Fun (powConvZ theta10CoeffFun 4)) t := by
          simpa using! hshift.symm

/-- For `t ≥ 1`, the numerator `psiI_num (it t)` equals `rseries psiCoeffFun t`. -/
public lemma psiI_num_it_eq_rseries_psiCoeffFun (t : ℝ) (ht : 1 ≤ t) :
    let ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    psiI_num (it t ht0) = rseries psiCoeffFun t := by
  intro ht0
  -- Abbreviations matching `psiCoeffFun`.
  let h4 : ℕ → ℤ := powConvZ theta01CoeffFun 4
  let h2 : ℕ → ℤ := shift1Fun (powConvZ theta10CoeffFun 4)
  have hH4 : H₄ (it t ht0) = rseries h4 t := by
    simpa [h4] using! (H4_it_eq_rseries_powConvZ_theta01 (t := t) ht)
  have hH2 : H₂ (it t ht0) = rseries h2 t := by
    simpa [h2] using! (H2_it_eq_rseries_shift1_powConvZ_theta10 (t := t) ht)
  -- Coefficient bounds for `h4` and `h2` (both behave like `16*(n+1)^3`).
  have hh4 : ∀ n : ℕ, |(h4 n : ℝ)| ≤ (16 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (3 : ℕ)) := by
    intro n
    have h :=
      abs_powConvZ_le (a := theta01CoeffFun) (C := (2 : ℝ)) (k := 0)
        (fun n => by simpa [pow_zero] using! abs_theta01CoeffFun_le_two_real n) 4 n
    have hpow2 : (2 : ℝ) ^ (4 : ℕ) = 16 := by norm_num
    simpa [h4, powConvZ, pow_zero, Nat.mul_zero, Nat.zero_add, Nat.succ_sub_one, hpow2] using! h
  have hh2 : ∀ n : ℕ, |(h2 n : ℝ)| ≤ (16 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (3 : ℕ)) := by
    intro n
    cases n with
    | zero =>
        simp [h2, shift1Fun]
    | succ n =>
        -- Shift does not worsen the bound.
        have h :=
          abs_powConvZ_le (a := theta10CoeffFun) (C := (2 : ℝ)) (k := 0)
            (fun n => by simpa [pow_zero] using! abs_theta10CoeffFun_le_two_real n) 4 n
        have hpow2 : (2 : ℝ) ^ (4 : ℕ) = 16 := by norm_num
        have h16 :
            |((powConvZ theta10CoeffFun 4) n : ℝ)| ≤
              (16 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (3 : ℕ)) := by
          simpa [powConvZ, pow_zero, Nat.mul_zero, Nat.zero_add, Nat.succ_sub_one, hpow2] using! h
        have hmono :
            (((n + 1 : ℕ) : ℝ) ^ (3 : ℕ)) ≤ (((n + 2 : ℕ) : ℝ) ^ (3 : ℕ)) := by
          have : ((n + 1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
            exact_mod_cast (Nat.succ_le_succ (Nat.le_succ n))
          exact pow_le_pow_left₀ (by positivity) this _
        have h' :
            |((powConvZ theta10CoeffFun 4) n : ℝ)| ≤
              (16 : ℝ) * (((n + 2 : ℕ) : ℝ) ^ (3 : ℕ)) := by
          linarith
        simpa [h2, shift1Fun, Nat.add_assoc] using! h'
  -- Summability for the three coefficient functions appearing in `psiCoeffFun`.
  have hs_pow (h : ℕ → ℤ)
      (hh : ∀ n : ℕ, |(h n : ℝ)| ≤ (16 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (3 : ℕ))) (m : ℕ) :
      Summable (fun n : ℕ => ‖(((powConvZ h m) n : ℂ) * (rC t) ^ n)‖) := by
    have hbound :
        ∀ n : ℕ,
          |((powConvZ h m n : ℤ) : ℝ)| ≤
            (16 : ℝ) ^ m * (((n + 1 : ℕ) : ℝ) ^ (m * 3 + (m - 1))) := by
      intro n
      simpa using! (abs_powConvZ_le (a := h) (C := (16 : ℝ)) (k := 3) hh m n)
    exact summable_norm_rseries_of_coeffBound (t := t) (ht0 := ht0)
      (a := powConvZ h m) (C := (16 : ℝ) ^ m) (k := m * 3 + (m - 1)) hbound
  have hs_powH4 (m : ℕ) :
      Summable (fun n : ℕ => ‖(((powConvZ h4 m) n : ℂ) * (rC t) ^ n)‖) :=
    hs_pow h4 hh4 m
  have hs_powH2 (m : ℕ) :
      Summable (fun n : ℕ => ‖(((powConvZ h2 m) n : ℂ) * (rC t) ^ n)‖) :=
    hs_pow h2 hh2 m
  have hs_conv1 :
      Summable
        (fun n : ℕ =>
          ‖((convZ (powConvZ h4 5) (powConvZ h2 2) n : ℂ) * (rC t) ^ n)‖) := by
    -- Coefficient bound: convolution adds exponents and multiplies constants.
    have ha5 :
        ∀ n : ℕ,
          |((powConvZ h4 5) n : ℝ)| ≤
            (16 : ℝ) ^ (5 : ℕ) * (((n + 1 : ℕ) : ℝ) ^ (19 : ℕ)) := by
      intro n
      simpa using! (abs_powConvZ_le (a := h4) (C := (16 : ℝ)) (k := 3) hh4 5 n)
    have hb2 :
        ∀ n : ℕ,
          |((powConvZ h2 2) n : ℝ)| ≤
            (16 : ℝ) ^ (2 : ℕ) * (((n + 1 : ℕ) : ℝ) ^ (7 : ℕ)) := by
      intro n
      simpa using! (abs_powConvZ_le (a := h2) (C := (16 : ℝ)) (k := 3) hh2 2 n)
    have habs :
        ∀ n : ℕ,
          |((convZ (powConvZ h4 5) (powConvZ h2 2) n : ℤ) : ℝ)| ≤
            ((16 : ℝ) ^ (5 : ℕ) * (16 : ℝ) ^ (2 : ℕ)) *
              (((n + 1 : ℕ) : ℝ) ^ (19 + 7 + 1)) := by
      intro n
      exact abs_convZ_le (powConvZ h4 5) (powConvZ h2 2) (16 ^ 5) (16 ^ 2) 19 7 ha5 hb2 n
    exact summable_norm_rseries_of_coeffBound t ht0 (convZ (powConvZ h4 5) (powConvZ h2 2))
      (16 ^ 5 * 16 ^ 2) (19 + 7 + 1) habs
  have hs_conv2 :
      Summable
        (fun n : ℕ =>
          ‖((convZ (powConvZ h4 6) (powConvZ h2 1) n : ℂ) * (rC t) ^ n)‖) := by
    have ha6 :
        ∀ n : ℕ,
          |((powConvZ h4 6) n : ℝ)| ≤
            (16 : ℝ) ^ (6 : ℕ) * (((n + 1 : ℕ) : ℝ) ^ (23 : ℕ)) := by
      intro n
      simpa using! (abs_powConvZ_le (a := h4) (C := (16 : ℝ)) (k := 3) hh4 6 n)
    have hb1 :
        ∀ n : ℕ,
          |((powConvZ h2 1) n : ℝ)| ≤ (16 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (3 : ℕ)) := by
      intro n
      -- `powConvZ _ 1 = _`.
      simpa [powConvZ_one] using! hh2 n
    have habs :
        ∀ n : ℕ,
          |((convZ (powConvZ h4 6) (powConvZ h2 1) n : ℤ) : ℝ)| ≤
            ((16 : ℝ) ^ (6 : ℕ) * (16 : ℝ)) * (((n + 1 : ℕ) : ℝ) ^ (23 + 3 + 1)) := by
      intro n
      exact abs_convZ_le (powConvZ h4 6) (powConvZ h2 1) (16 ^ 6) 16 23 3 ha6 hb1 n
    exact
        summable_norm_rseries_of_coeffBound t ht0 (convZ (powConvZ h4 6) (powConvZ h2 1))
          (16 ^ 6 * 16) (23 + 3 + 1) habs
  have hs_pow7 :
      Summable (fun n : ℕ => ‖(((powConvZ h4 7) n : ℂ) * (rC t) ^ n)‖) :=
    hs_powH4 7
  -- Expand `rseries psiCoeffFun` using the `rseries_add`/`rseries_smul` lemmas.
  let a1 : ℕ → ℤ := fun n => (7 : ℤ) * convZ (powConvZ h4 5) (powConvZ h2 2) n
  let a2 : ℕ → ℤ := fun n => (7 : ℤ) * convZ (powConvZ h4 6) (powConvZ h2 1) n
  let a3 : ℕ → ℤ := fun n => (2 : ℤ) * powConvZ h4 7 n
  have hs_a1 : Summable (fun n : ℕ => ‖((a1 n : ℂ) * (rC t) ^ n)‖) := by
    have hs' :
        Summable
          (fun n : ℕ =>
            ‖(7 : ℂ)‖ *
              ‖((convZ (powConvZ h4 5) (powConvZ h2 2) n : ℂ) * (rC t) ^ n)‖) :=
      (hs_conv1.mul_left ‖(7 : ℂ)‖)
    refine hs'.congr ?_
    intro n
    simp [a1, mul_left_comm, mul_comm]
  have hs_a2 : Summable (fun n : ℕ => ‖((a2 n : ℂ) * (rC t) ^ n)‖) := by
    have hs' :
        Summable
          (fun n : ℕ =>
            ‖(7 : ℂ)‖ *
              ‖((convZ (powConvZ h4 6) (powConvZ h2 1) n : ℂ) * (rC t) ^ n)‖) :=
      (hs_conv2.mul_left ‖(7 : ℂ)‖)
    refine hs'.congr ?_
    intro n
    simp [a2, mul_left_comm, mul_comm]
  have hs_a3 : Summable (fun n : ℕ => ‖((a3 n : ℂ) * (rC t) ^ n)‖) := by
    have hs' :
        Summable
          (fun n : ℕ => ‖(2 : ℂ)‖ * ‖(((powConvZ h4 7) n : ℂ) * (rC t) ^ n)‖) :=
      (hs_pow7.mul_left ‖(2 : ℂ)‖)
    refine hs'.congr ?_
    intro n
    simp [a3, mul_assoc]
  have hs_a12 : Summable (fun n : ℕ => ‖(((a1 n + a2 n : ℤ) : ℂ) * (rC t) ^ n)‖) := by
    -- Compare to the termwise sum of norms.
    have hs_add :
        Summable
          (fun n : ℕ =>
            ‖((a1 n : ℂ) * (rC t) ^ n)‖ + ‖((a2 n : ℂ) * (rC t) ^ n)‖) :=
      hs_a1.add hs_a2
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hs_add
    intro n
    have := norm_add_le ((a1 n : ℂ) * (rC t) ^ n) ((a2 n : ℂ) * (rC t) ^ n)
    simpa [add_mul] using! this
  have hpsi_series :
      rseries psiCoeffFun t =
        (7 : ℂ) * rseries (fun n => convZ (powConvZ h4 5) (powConvZ h2 2) n) t +
          (7 : ℂ) * rseries (fun n => convZ (powConvZ h4 6) (powConvZ h2 1) n) t +
            (2 : ℂ) * rseries (powConvZ h4 7) t := by
    have hsplit123 :
        rseries psiCoeffFun t =
          rseries (fun n => a1 n + a2 n) t + rseries a3 t := by
      -- `psiCoeffFun = (a1+a2)+a3`.
      have : (fun n : ℕ => psiCoeffFun n) = fun n : ℕ => (a1 n + a2 n) + a3 n := by
        funext n
        simp [psiCoeffFun, a1, a2, a3, h4, h2, add_assoc]
      -- apply `rseries_add_of_summable`
      simpa [this, add_assoc] using!
        (rseries_add_of_summable (t := t) (a := fun n => a1 n + a2 n) (b := a3) hs_a12 hs_a3)
    have hsplit12 :
        rseries (fun n => a1 n + a2 n) t = rseries a1 t + rseries a2 t := by
      simpa using! (rseries_add_of_summable (t := t) (a := a1) (b := a2) hs_a1 hs_a2)
    -- Pull out integer scalars.
    have hsmul1 :
        rseries a1 t =
          (7 : ℂ) * rseries (fun n => convZ (powConvZ h4 5) (powConvZ h2 2) n) t := by
      simpa [a1] using!
        (rseries_smul_int_of_summable (t := t) (c := (7 : ℤ))
          (a := fun n => convZ (powConvZ h4 5) (powConvZ h2 2) n) hs_conv1)
    have hsmul2 :
        rseries a2 t =
          (7 : ℂ) * rseries (fun n => convZ (powConvZ h4 6) (powConvZ h2 1) n) t := by
      simpa [a2] using!
        (rseries_smul_int_of_summable (t := t) (c := (7 : ℤ))
          (a := fun n => convZ (powConvZ h4 6) (powConvZ h2 1) n) hs_conv2)
    have hsmul3 :
        rseries a3 t = (2 : ℂ) * rseries (powConvZ h4 7) t := by
      simpa [a3] using!
        (rseries_smul_int_of_summable (t := t) (c := (2 : ℤ)) (a := powConvZ h4 7) hs_pow7)
    -- Assemble.
    calc
      rseries psiCoeffFun t
          = rseries (fun n => a1 n + a2 n) t + rseries a3 t := hsplit123
      _ = (rseries a1 t + rseries a2 t) + rseries a3 t := by simp [hsplit12, add_assoc]
      _ =
          (7 : ℂ) * rseries (fun n => convZ (powConvZ h4 5) (powConvZ h2 2) n) t +
            (7 : ℂ) * rseries (fun n => convZ (powConvZ h4 6) (powConvZ h2 1) n) t +
              (2 : ℂ) * rseries (powConvZ h4 7) t := by
            simp [hsmul1, hsmul2, hsmul3]
  -- Finally, compute each `rseries` term as a product/power and match `psiI_num_eq_H`.
  have hpow_h4 :
      ∀ m : ℕ, rseries (powConvZ h4 m) t = (H₄ (it t ht0)) ^ m := by
    intro m
    have hpow :=
      rseries_powConvZ_eq_pow (t := t) (ht0 := ht0) (a := h4)
        (C := (16 : ℝ)) (k := 3) hh4 m
    -- `H₄ = rseries h4`.
    simpa [hH4] using! hpow
  have hpow_h2 :
      ∀ m : ℕ, rseries (powConvZ h2 m) t = (H₂ (it t ht0)) ^ m := by
    intro m
    have hpow :=
      rseries_powConvZ_eq_pow (t := t) (ht0 := ht0) (a := h2)
        (C := (16 : ℝ)) (k := 3) hh2 m
    simpa [hH2] using! hpow
  have hmul1 :
      rseries (fun n => convZ (powConvZ h4 5) (powConvZ h2 2) n) t =
        (H₄ (it t ht0)) ^ (5 : ℕ) * (H₂ (it t ht0)) ^ (2 : ℕ) := by
    have hmul :=
      (rseries_mul_cast
        (t := t)
        (a := powConvZ h4 5)
        (b := powConvZ h2 2)
        (hs_powH4 5)
        (hs_powH2 2))
    -- rewrite the LHS using the rseries multiplication lemma, then powers
    calc
      rseries (fun n => convZ (powConvZ h4 5) (powConvZ h2 2) n) t
          = rseries (convZ (powConvZ h4 5) (powConvZ h2 2)) t := by
              rfl
      _ = rseries (powConvZ h4 5) t * rseries (powConvZ h2 2) t := by
            simpa using! hmul.symm
      _ = (H₄ (it t ht0)) ^ (5 : ℕ) * (H₂ (it t ht0)) ^ (2 : ℕ) := by
            simp [hpow_h4, hpow_h2]
  have hmul2 :
      rseries (fun n => convZ (powConvZ h4 6) (powConvZ h2 1) n) t =
        (H₄ (it t ht0)) ^ (6 : ℕ) * (H₂ (it t ht0)) := by
    have hmul :=
      (rseries_mul_cast
        (t := t)
        (a := powConvZ h4 6)
        (b := powConvZ h2 1)
        (hs_powH4 6)
        (hs_powH2 1))
    calc
      rseries (fun n => convZ (powConvZ h4 6) (powConvZ h2 1) n) t
          = rseries (convZ (powConvZ h4 6) (powConvZ h2 1)) t := by
              rfl
      _ = rseries (powConvZ h4 6) t * rseries (powConvZ h2 1) t := by
            simpa using! hmul.symm
      _ = (H₄ (it t ht0)) ^ (6 : ℕ) * (H₂ (it t ht0)) := by
            simp [hpow_h4, hpow_h2]
  have hpow7 : rseries (powConvZ h4 7) t = (H₄ (it t ht0)) ^ (7 : ℕ) := by
    simpa using! (hpow_h4 7)
  -- Put the pieces together.
  have hpsiH := psiI_num_eq_H (z := it t ht0)
  -- Rewrite `psiI_num` using the rseries expression.
  calc
    psiI_num (it t ht0)
        = 7 * (H₄ (it t ht0)) ^ (5 : ℕ) * (H₂ (it t ht0)) ^ (2 : ℕ) +
            7 * (H₄ (it t ht0)) ^ (6 : ℕ) * (H₂ (it t ht0)) +
              2 * (H₄ (it t ht0)) ^ (7 : ℕ) := by
              simpa using! hpsiH
    _ =
        (7 : ℂ) * rseries (fun n => convZ (powConvZ h4 5) (powConvZ h2 2) n) t +
          (7 : ℂ) * rseries (fun n => convZ (powConvZ h4 6) (powConvZ h2 1) n) t +
            (2 : ℂ) * rseries (powConvZ h4 7) t := by
          -- rewrite each term using `hmul1/hmul2/hpow7`
          simp [hmul1, hmul2, hpow7, mul_assoc]
      _ = rseries psiCoeffFun t := by
          -- use the earlier expansion of `rseries psiCoeffFun`
          simp [hpsi_series]

end SpherePacking.Dim24.AppendixA
open scoped Real
open Complex UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.AppendixA

/-- A polynomial growth bound for `psiCoeffFun`, used to justify summability of its `rseries`. -/
public lemma abs_psiCoeffFun_le (n : ℕ) :
    |(psiCoeffFun n : ℝ)| ≤ (16 : ℝ) ^ (8 : ℕ) * (((n + 1 : ℕ) : ℝ) ^ (27 : ℕ)) := by
  let a4 : ℕ → ℤ := powConvZ theta01CoeffFun 4
  let b4 : ℕ → ℤ := powConvZ theta10CoeffFun 4
  let b4s : ℕ → ℤ := shift1Fun b4
  have hpow2 : (2 : ℝ) ^ (4 : ℕ) = 16 := by norm_num
  have ha4 :
      ∀ n : ℕ, |(a4 n : ℝ)| ≤ (16 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (3 : ℕ)) := by
    intro n
    simpa [a4, powConvZ, pow_zero, Nat.mul_zero, Nat.zero_add, Nat.succ_sub_one, hpow2] using!
      (abs_powConvZ_le (a := theta01CoeffFun) (C := (2 : ℝ)) (k := 0)
        (fun n => by simpa [pow_zero] using! abs_theta01CoeffFun_le_two_real n) 4 n)
  have hb4 :
      ∀ n : ℕ, |(b4 n : ℝ)| ≤ (16 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (3 : ℕ)) := by
    intro n
    simpa [b4, powConvZ, pow_zero, Nat.mul_zero, Nat.zero_add, Nat.succ_sub_one, hpow2] using!
      (abs_powConvZ_le (a := theta10CoeffFun) (C := (2 : ℝ)) (k := 0)
        (fun n => by simpa [pow_zero] using! abs_theta10CoeffFun_le_two_real n) 4 n)
  have hb4s :
      ∀ n : ℕ, |(b4s n : ℝ)| ≤ (16 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (3 : ℕ)) := by
    intro n
    cases n with
    | zero => simp [b4s, shift1Fun]
    | succ n =>
        have hmono :
            (((n + 1 : ℕ) : ℝ) ^ (3 : ℕ)) ≤ (((n + 2 : ℕ) : ℝ) ^ (3 : ℕ)) := by
          have : ((n + 1 : ℕ) : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
            exact_mod_cast (Nat.succ_le_succ (Nat.le_succ n))
          exact pow_le_pow_left₀ (by positivity) this _
        have h' : |(b4 n : ℝ)| ≤ (16 : ℝ) * (((n + 2 : ℕ) : ℝ) ^ (3 : ℕ)) :=
          (hb4 n).trans <| by
            have :=
              mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ (16 : ℝ))
            simpa [mul_assoc] using! this
        simpa [b4s, shift1Fun, Nat.add_assoc] using! h'
  have haPow (m : ℕ) :
      ∀ n : ℕ,
        |(powConvZ a4 m n : ℝ)| ≤
          (16 : ℝ) ^ m * (((n + 1 : ℕ) : ℝ) ^ (m * 3 + (m - 1))) :=
    fun n => abs_powConvZ_le (a := a4) (C := (16 : ℝ)) (k := 3) ha4 m n
  have hbPow (m : ℕ) :
      ∀ n : ℕ,
        |(powConvZ b4s m n : ℝ)| ≤
          (16 : ℝ) ^ m * (((n + 1 : ℕ) : ℝ) ^ (m * 3 + (m - 1))) :=
    fun n => abs_powConvZ_le (a := b4s) (C := (16 : ℝ)) (k := 3) hb4s m n
  have hconv1 :
      |(convZ (powConvZ a4 5) (powConvZ b4s 2) n : ℝ)| ≤
        (16 : ℝ) ^ (7 : ℕ) * (((n + 1 : ℕ) : ℝ) ^ (27 : ℕ)) := by
    have h :=
      abs_convZ_le (a := powConvZ a4 5) (b := powConvZ b4s 2)
        (Ca := (16 : ℝ) ^ (5 : ℕ)) (Cb := (16 : ℝ) ^ (2 : ℕ))
        (ka := (5 * 3 + 4)) (kb := (2 * 3 + 1))
        (haPow 5) (hbPow 2) n
    have hC :
        (16 : ℝ) ^ (5 : ℕ) * (16 : ℝ) ^ (2 : ℕ) = (16 : ℝ) ^ (7 : ℕ) := by
      simpa [pow_add] using! (pow_add (16 : ℝ) 5 2).symm
    have hexp : (5 * 3 + 4) + (2 * 3 + 1) + 1 = (27 : ℕ) := by decide
    simpa [hC, hexp, mul_assoc] using! h
  have hb1 :
      ∀ n : ℕ,
        |(powConvZ b4s 1 n : ℝ)| ≤ (16 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (3 : ℕ)) := by
    intro n
    simpa [powConvZ_one] using! hb4s n
  have hconv2 :
      |(convZ (powConvZ a4 6) (powConvZ b4s 1) n : ℝ)| ≤
        (16 : ℝ) ^ (7 : ℕ) * (((n + 1 : ℕ) : ℝ) ^ (27 : ℕ)) := by
    have h :=
      abs_convZ_le (a := powConvZ a4 6) (b := powConvZ b4s 1)
        (Ca := (16 : ℝ) ^ (6 : ℕ)) (Cb := (16 : ℝ))
        (ka := (6 * 3 + 5)) (kb := 3)
        (haPow 6) hb1 n
    simpa [pow_add, pow_succ, mul_assoc,
      show ((6 * 3 + 5) + 3 + 1 : ℕ) = 27 by decide] using! h
  have hpow7 :
      |(powConvZ a4 7 n : ℝ)| ≤ (16 : ℝ) ^ (7 : ℕ) * (((n + 1 : ℕ) : ℝ) ^ (27 : ℕ)) := by
    simpa [show (7 * 3 + 6 : ℕ) = 27 by decide] using! (haPow 7 n)
  have hpsi :
      (psiCoeffFun n : ℝ) =
        (7 : ℝ) * (convZ (powConvZ a4 5) (powConvZ b4s 2) n : ℝ) +
          ((7 : ℝ) * (convZ (powConvZ a4 6) (powConvZ b4s 1) n : ℝ) +
            (2 : ℝ) * (powConvZ a4 7 n : ℝ)) := by
    simp [psiCoeffFun, a4, b4, b4s, add_assoc, add_comm]
  have htri :
      |(psiCoeffFun n : ℝ)| ≤
        |((7 : ℝ) * (convZ (powConvZ a4 5) (powConvZ b4s 2) n : ℝ))| +
          |((7 : ℝ) * (convZ (powConvZ a4 6) (powConvZ b4s 1) n : ℝ))| +
            |((2 : ℝ) * (powConvZ a4 7 n : ℝ))| := by
    calc
      |(psiCoeffFun n : ℝ)| = |(7 * (convZ (powConvZ a4 5) (powConvZ b4s 2) n : ℝ)) +
          ((7 * (convZ (powConvZ a4 6) (powConvZ b4s 1) n : ℝ)) +
            (2 * (powConvZ a4 7 n : ℝ)))| := by
            simp [hpsi]
      _ ≤
          |(7 * (convZ (powConvZ a4 5) (powConvZ b4s 2) n : ℝ))| +
            |(7 * (convZ (powConvZ a4 6) (powConvZ b4s 1) n : ℝ)) +
              (2 * (powConvZ a4 7 n : ℝ))| := by
            simpa using!
              (abs_add_le (7 * (convZ (powConvZ a4 5) (powConvZ b4s 2) n : ℝ))
                ((7 * (convZ (powConvZ a4 6) (powConvZ b4s 1) n : ℝ)) +
                  (2 * (powConvZ a4 7 n : ℝ))))
      _ ≤
          |(7 * (convZ (powConvZ a4 5) (powConvZ b4s 2) n : ℝ))| +
            (|(7 * (convZ (powConvZ a4 6) (powConvZ b4s 1) n : ℝ))| +
              |(2 * (powConvZ a4 7 n : ℝ))|) := by
            gcongr
            exact abs_add_le _ _
      _ =
          |(7 * (convZ (powConvZ a4 5) (powConvZ b4s 2) n : ℝ))| +
            |(7 * (convZ (powConvZ a4 6) (powConvZ b4s 1) n : ℝ))| +
              |(2 * (powConvZ a4 7 n : ℝ))| := by ring
  have hx :
      |((7 : ℝ) * (convZ (powConvZ a4 5) (powConvZ b4s 2) n : ℝ))| ≤
        (7 : ℝ) * ((16 : ℝ) ^ (7 : ℕ) * (((n + 1 : ℕ) : ℝ) ^ (27 : ℕ))) := by
    simpa [abs_mul, mul_assoc] using!
      (mul_le_mul_of_nonneg_left hconv1 (by norm_num : (0 : ℝ) ≤ 7))
  have hy :
      |((7 : ℝ) * (convZ (powConvZ a4 6) (powConvZ b4s 1) n : ℝ))| ≤
        (7 : ℝ) * ((16 : ℝ) ^ (7 : ℕ) * (((n + 1 : ℕ) : ℝ) ^ (27 : ℕ))) := by
    simpa [abs_mul, mul_assoc] using!
      (mul_le_mul_of_nonneg_left hconv2 (by norm_num : (0 : ℝ) ≤ 7))
  have hz :
      |((2 : ℝ) * (powConvZ a4 7 n : ℝ))| ≤
        (2 : ℝ) * ((16 : ℝ) ^ (7 : ℕ) * (((n + 1 : ℕ) : ℝ) ^ (27 : ℕ))) := by
    simpa [abs_mul, mul_assoc] using!
      (mul_le_mul_of_nonneg_left hpow7 (by norm_num : (0 : ℝ) ≤ 2))
  linarith


end SpherePacking.Dim24.AppendixA
