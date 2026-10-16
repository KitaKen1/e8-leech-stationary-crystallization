-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Laplace.B.SubLeadingBounds.ExactTruncBound


/-!
# Subleading bound for `BKernel` on the tail

This file proves a polynomial growth bound for `BKernel(it t) - BleadingLeadingTerm t` on `t ≥ 1`.
It is the final analytic estimate needed to show absolute integrability of the subtracted tail
integral for all `0 < Re u`.

## Main statement
* `norm_BKernel_sub_leading_le_poly`
-/

namespace SpherePacking.Dim24.LaplaceBSubLeadingBounds

noncomputable section

open scoped BigOperators Real Topology
open Complex Filter UpperHalfPlane

open AppendixA

/-- Polynomial growth bound for `BKernel(it t) - BleadingLeadingTerm(t)` for `t ≥ 1`. -/
public theorem norm_BKernel_sub_leading_le_poly (t : ℝ) (ht : 1 ≤ t) :
    let ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    ‖BKernel t ht0 - (BleadingLeadingTerm t : ℂ)‖ ≤
      (((((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Acoeff i : ℝ)|) *
                  Real.pi * t ^ (2 : ℕ)) +
                  ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Bcoeff i : ℝ)|) * t)) +
                ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Ccoeff i : ℝ)|) *
                  (1 / Real.pi))) +
              eps) /
        (Classical.choose exists_lower_bound_norm_resToImagAxis_Ici_one) ^ 2 := by
  intro ht0
  -- Lower bound on `‖Δ / q‖` along the imaginary axis, hence on `‖Δ‖`.
  let cΔ : ℝ := Classical.choose exists_lower_bound_norm_resToImagAxis_Ici_one
  have hcΔpos : 0 < cΔ := (Classical.choose_spec exists_lower_bound_norm_resToImagAxis_Ici_one).1
  have hcΔ : ∀ t : ℝ, 1 ≤ t → cΔ ≤ ‖(fun z : ℍ => (Δ z) / q (z : ℂ)).resToImagAxis t‖ :=
    (Classical.choose_spec exists_lower_bound_norm_resToImagAxis_Ici_one).2
  have hcΔ' : cΔ ≤ ‖(fun z : ℍ => (Δ z) / q (z : ℂ)).resToImagAxis t‖ := hcΔ t ht
  have htq : ‖q ((it t ht0 : ℍ) : ℂ)‖ = Real.exp (-2 * Real.pi * t) := by
    have hexp :
        (2 * (Real.pi : ℂ) * Complex.I) * ((it t ht0 : ℍ) : ℂ) =
          (-(2 * Real.pi * t) : ℂ) := by
      -- `2π i * (i t) = -2π t`.
      have hII : (Complex.I : ℂ) * ((Complex.I : ℂ) * (t : ℂ)) = -(t : ℂ) := by
        exact I_mul_I_mul ↑t
      calc
        (2 * (Real.pi : ℂ) * Complex.I) * ((it t ht0 : ℍ) : ℂ)
            = (2 * (Real.pi : ℂ) * Complex.I) * ((Complex.I : ℂ) * (t : ℂ)) := by
                rfl
        _ = (2 * (Real.pi : ℂ)) * ((Complex.I : ℂ) * ((Complex.I : ℂ) * (t : ℂ))) := by
                simp [mul_assoc, mul_left_comm, mul_comm]
        _ = (2 * (Real.pi : ℂ)) * (-(t : ℂ)) := by
                simp [hII]
        _ = (-(2 * Real.pi * t) : ℂ) := by
                ring_nf
    calc
      ‖q ((it t ht0 : ℍ) : ℂ)‖ = ‖cexp (-(2 * Real.pi * t) : ℂ)‖ := by
            simp [q, hexp]
      _ = Real.exp (-(2 * Real.pi * t)) := by
            simpa using! (Complex.norm_exp_ofReal (-(2 * Real.pi * t)))
      _ = Real.exp (-2 * Real.pi * t) := by ring_nf
  have hΔnorm :
      ‖Δ (it t ht0)‖ =
        ‖q ((it t ht0 : ℍ) : ℂ)‖ * ‖(fun z : ℍ => (Δ z) / q (z : ℂ)).resToImagAxis t‖ := by
    -- `Δ = q * (Δ/q)`.
    have hqne : q ((it t ht0 : ℍ) : ℂ) ≠ 0 := by
      simp [q]
    have :
        Δ (it t ht0) =
          q ((it t ht0 : ℍ) : ℂ) * (Δ (it t ht0) / q ((it t ht0 : ℍ) : ℂ)) := by
      field_simp [hqne]
    -- Identify `(Δ/q)` with the `resToImagAxis` value.
    have hres :
        ((Δ (it t ht0)) / q ((it t ht0 : ℍ) : ℂ)) =
          (fun z : ℍ => (Δ z) / q (z : ℂ)).resToImagAxis t := by
      simp [Function.resToImagAxis, ResToImagAxis, it, ht0]
    -- Take norms.
    simp_all
  have hΔlb :
      (cΔ * Real.exp (-2 * Real.pi * t)) ≤ ‖(Δ (it t ht0))‖ := by
    have :
        cΔ * Real.exp (-2 * Real.pi * t) ≤
          ‖q ((it t ht0 : ℍ) : ℂ)‖ *
            ‖(fun z : ℍ => (Δ z) / q (z : ℂ)).resToImagAxis t‖ := by
      have hqpos : 0 ≤ ‖q ((it t ht0 : ℍ) : ℂ)‖ := by positivity
      -- `cΔ ≤ ‖Δ/q‖` and multiply by `‖q‖ = exp(-2πt)`.
      nlinarith
    simpa [hΔnorm] using! this
  -- We will only need lower bounds for `‖Δ(it·)‖`, not an identification of `re` with the norm.
  -- Bound `‖BleadingNum‖` using the truncation + remainder estimate.
  have hsub :
      ‖BleadingNum t ht0 - (Bleading_exact_trunc t : ℂ)‖ ≤ eps * (r t) ^ (12 : ℕ) :=
    AppendixA.norm_BleadingNum_sub_exact_trunc_le (t := t) ht
  have hNum :
      ‖BleadingNum t ht0‖ ≤
        |Bleading_exact_trunc t| + eps * (r t) ^ (12 : ℕ) := by
    have h1 :
        ‖BleadingNum t ht0‖ ≤
          ‖BleadingNum t ht0 - (Bleading_exact_trunc t : ℂ)‖ + ‖(Bleading_exact_trunc t : ℂ)‖ := by
      -- Triangle inequality after rewriting `x = (x - y) + y`.
      exact norm_le_norm_sub_add (BleadingNum t ht0) ↑(Bleading_exact_trunc t)
    have h2 :
        ‖BleadingNum t ht0 - (Bleading_exact_trunc t : ℂ)‖ + ‖(Bleading_exact_trunc t : ℂ)‖ ≤
          eps * (r t) ^ (12 : ℕ) + |Bleading_exact_trunc t| := by
      refine add_le_add hsub ?_
      -- `‖(x : ℂ)‖ = |x|` for real `x`.
      exact le_of_eq (by simp)
    have : ‖BleadingNum t ht0‖ ≤ eps * (r t) ^ (12 : ℕ) + |Bleading_exact_trunc t| :=
      le_trans h1 h2
    simpa [add_comm, add_left_comm, add_assoc] using! this
  have hExact :
      |Bleading_exact_trunc t| ≤
        ((((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Acoeff i : ℝ)|) *
                Real.pi * t ^ (2 : ℕ)) +
                ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Bcoeff i : ℝ)|) * t)) +
              ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Ccoeff i : ℝ)|) *
                (1 / Real.pi))) *
            (r t) ^ (4 : ℕ) :=
    abs_Bleading_exact_trunc_le (t := t) ht
  have hpow : (r t) ^ (12 : ℕ) ≤ (r t) ^ (4 : ℕ) := by
    have hr0 : 0 ≤ r t := (Real.exp_pos _).le
    have hr1 : r t ≤ 1 := by
      have ht' : 0 ≤ t := le_trans (by norm_num) ht
      have : (-Real.pi * t) ≤ 0 := by nlinarith [Real.pi_pos, ht']
      simpa [r] using! (Real.exp_le_one_iff.2 this)
    simpa using! (pow_le_pow_of_le_one hr0 hr1 (by decide : (4 : ℕ) ≤ 12))
  have hNum' :
      ‖BleadingNum t ht0‖ ≤
        (((((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Acoeff i : ℝ)|) *
                  Real.pi * t ^ (2 : ℕ)) +
                  ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Bcoeff i : ℝ)|) * t)) +
                ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Ccoeff i : ℝ)|) *
                  (1 / Real.pi))) +
              eps) *
          (r t) ^ (4 : ℕ) := by
    have h1 :
        |Bleading_exact_trunc t| + eps * (r t) ^ (12 : ℕ) ≤
          ((((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Acoeff i : ℝ)|) *
                  Real.pi * t ^ (2 : ℕ)) +
                  ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Bcoeff i : ℝ)|) * t)) +
                ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Ccoeff i : ℝ)|) *
                  (1 / Real.pi))) *
              (r t) ^ (4 : ℕ) + eps * (r t) ^ (4 : ℕ) := by
      refine add_le_add hExact ?_
      have heps : 0 ≤ eps := by dsimp [eps]; positivity
      exact mul_le_mul_of_nonneg_left hpow heps
    have h2 :
        ((((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Acoeff i : ℝ)|) *
                  Real.pi * t ^ (2 : ℕ)) +
                  ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Bcoeff i : ℝ)|) * t)) +
                ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Ccoeff i : ℝ)|) *
                  (1 / Real.pi))) *
              (r t) ^ (4 : ℕ) + eps * (r t) ^ (4 : ℕ) =
          (((((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Acoeff i : ℝ)|) *
                    Real.pi * t ^ (2 : ℕ)) +
                    ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Bcoeff i : ℝ)|) * t)) +
                  ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Ccoeff i : ℝ)|) *
                    (1 / Real.pi))) +
                eps) *
            (r t) ^ (4 : ℕ) := by ring
    exact le_trans hNum (le_trans h1 (le_of_eq h2))
  -- Convert the `Δ` lower bound into a lower bound on `‖Δ^2‖`.
  have hΔpos : 0 < ‖Δ (it t ht0)‖ := by
    have : Δ (it t ht0) ≠ 0 := Δ_ne_zero (it t ht0)
    simpa using! norm_pos_iff.2 this
  have hΔ2lb : (cΔ ^ 2) * (r t) ^ (4 : ℕ) ≤ ‖(Δ (it t ht0)) ^ (2 : ℕ)‖ := by
    -- `‖Δ^2‖ = ‖Δ‖^2` and `‖Δ‖ ≥ cΔ * exp(-2π t) = cΔ * (r t)^2`.
    have hΔlb' : cΔ * (r t) ^ (2 : ℕ) ≤ ‖Δ (it t ht0)‖ := by
      -- rewrite `exp(-2π t)` as `(r t)^2`.
      have hexp : Real.exp (-2 * Real.pi * t) = (r t) ^ (2 : ℕ) := by
        have hlin : (-2 * Real.pi * t) = (-Real.pi * t) + (-Real.pi * t) := by ring_nf
        calc
          Real.exp (-2 * Real.pi * t)
              = Real.exp ((-Real.pi * t) + (-Real.pi * t)) := by
                    exact congrArg Real.exp hlin
          _ = Real.exp (-Real.pi * t) * Real.exp (-Real.pi * t) := by
                simpa using! (Real.exp_add (-Real.pi * t) (-Real.pi * t))
          _ = (r t) * (r t) := by simp [r]
          _ = (r t) ^ (2 : ℕ) := by simp [pow_two]
      exact le_of_eq_of_le (congrArg (HMul.hMul cΔ) (id (Eq.symm hexp))) hΔlb
    have hmul :
        (cΔ * (r t) ^ (2 : ℕ)) * (cΔ * (r t) ^ (2 : ℕ)) ≤
          ‖Δ (it t ht0)‖ * ‖Δ (it t ht0)‖ := by
      have h0 : 0 ≤ cΔ * (r t) ^ (2 : ℕ) := by
        have : 0 ≤ (r t) ^ (2 : ℕ) := by positivity
        nlinarith [hcΔpos.le]
      have h0' : 0 ≤ ‖Δ (it t ht0)‖ := by positivity
      exact mul_le_mul hΔlb' hΔlb' h0 h0'
    have hrpow : (r t) ^ (4 : ℕ) = (r t) ^ (2 : ℕ) * (r t) ^ (2 : ℕ) := by
      simpa using! (pow_add (r t) (2 : ℕ) (2 : ℕ))
    have hlhs :
        (cΔ * (r t) ^ (2 : ℕ)) * (cΔ * (r t) ^ (2 : ℕ)) =
          (cΔ ^ 2) * (r t) ^ (4 : ℕ) := by
      -- Expand and use `hrpow`.
      simp [pow_two, hrpow, mul_assoc, mul_left_comm, mul_comm]
    have hnormpow : ‖(Δ (it t ht0)) ^ (2 : ℕ)‖ = (‖Δ (it t ht0)‖) ^ (2 : ℕ) := by
      simp [norm_pow]
    -- Rewrite `‖Δ‖ * ‖Δ‖` as `‖Δ^2‖` and finish.
    have : (cΔ ^ 2) * (r t) ^ (4 : ℕ) ≤ ‖Δ (it t ht0)‖ ^ (2 : ℕ) := by
      have hmul' : (cΔ ^ 2) * (r t) ^ (4 : ℕ) ≤ ‖Δ (it t ht0)‖ * ‖Δ (it t ht0)‖ := by
        simpa [hlhs] using! hmul
      simpa [pow_two] using! hmul'
    simpa [hnormpow] using! this
  -- Express `BKernel - leading` as `BleadingNum / Δ^2` and bound using the lower bound.
  have hΔ2ne : (Δ (it t ht0)) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 (Δ_ne_zero (it t ht0))
  have hEq :
      BKernel t ht0 - (BleadingLeadingTerm t : ℂ) =
        (BleadingNum t ht0) * ((Δ (it t ht0)) ^ (2 : ℕ))⁻¹ := by
    -- `BleadingNum = (BKernel - leading) * Δ^2`, so divide by `Δ^2`.
    have hone : (1 : ℂ) = (Δ (it t ht0)) ^ (2 : ℕ) * ((Δ (it t ht0)) ^ (2 : ℕ))⁻¹ := by
      symm
      simp [hΔ2ne]
    dsimp [BleadingNum]
    exact (eq_mul_inv_iff_mul_eq₀ hΔ2ne).mpr rfl
  have hnorm :
      ‖BKernel t ht0 - (BleadingLeadingTerm t : ℂ)‖ =
        ‖BleadingNum t ht0‖ * ‖((Δ (it t ht0)) ^ (2 : ℕ))⁻¹‖ := by
    simp [hEq]
  have hInv :
      ‖((Δ (it t ht0)) ^ (2 : ℕ))⁻¹‖ ≤ 1 / ((cΔ ^ 2) * (r t) ^ (4 : ℕ)) := by
    have hpos : 0 < (cΔ ^ 2) * (r t) ^ (4 : ℕ) := by
      have : 0 < (r t) ^ (4 : ℕ) := pow_pos (Real.exp_pos _) 4
      have : 0 < cΔ ^ 2 := sq_pos_of_pos hcΔpos
      positivity
    have hΔ2pos : 0 < ‖(Δ (it t ht0)) ^ (2 : ℕ)‖ := by
      have : (Δ (it t ht0)) ^ (2 : ℕ) ≠ 0 := hΔ2ne
      simpa using! norm_pos_iff.2 this
    have hle : (cΔ ^ 2) * (r t) ^ (4 : ℕ) ≤ ‖(Δ (it t ht0)) ^ (2 : ℕ)‖ := hΔ2lb
    -- Invert a positive inequality.
    have := one_div_le_one_div_of_le hpos hle
    simpa [one_div, norm_inv] using! this
  have hfinal :
      ‖BKernel t ht0 - (BleadingLeadingTerm t : ℂ)‖ ≤
        ((((((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Acoeff i : ℝ)|) *
                    Real.pi * t ^ (2 : ℕ)) +
                    ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Bcoeff i : ℝ)|) * t)) +
                  ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Ccoeff i : ℝ)|) *
                    (1 / Real.pi))) +
                eps) /
          (cΔ ^ 2)) := by
    -- Combine `hnorm` with bounds on `‖BleadingNum‖` and `‖(Δ^2)⁻¹‖`, and cancel `(r t)^4`.
    set P : ℝ :=
      (((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Acoeff i : ℝ)|) *
              Real.pi * t ^ (2 : ℕ)) +
              ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Bcoeff i : ℝ)|) * t) +
            ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Ccoeff i : ℝ)|) *
              (1 / Real.pi))) +
          eps
    have hmain :
        ‖BKernel t ht0 - (BleadingLeadingTerm t : ℂ)‖ ≤
          ‖BleadingNum t ht0‖ * (1 / ((cΔ ^ 2) * (r t) ^ (4 : ℕ))) := by
      calc
        ‖BKernel t ht0 - (BleadingLeadingTerm t : ℂ)‖
            = ‖BleadingNum t ht0‖ * ‖((Δ (it t ht0)) ^ (2 : ℕ))⁻¹‖ := by
                simp [hnorm]
        _ ≤ ‖BleadingNum t ht0‖ * (1 / ((cΔ ^ 2) * (r t) ^ (4 : ℕ))) := by
              gcongr
    have hNum'' : ‖BleadingNum t ht0‖ ≤ P * (r t) ^ (4 : ℕ) := by
      simpa [P, add_assoc, add_left_comm, add_comm] using! hNum'
    have hdenpos : 0 < (cΔ ^ 2) * (r t) ^ (4 : ℕ) := by
      have : 0 < (r t) ^ (4 : ℕ) := pow_pos (Real.exp_pos _) 4
      have : 0 < cΔ ^ 2 := sq_pos_of_pos hcΔpos
      positivity
    have hscale :
        ‖BleadingNum t ht0‖ * (1 / ((cΔ ^ 2) * (r t) ^ (4 : ℕ))) ≤
          (P * (r t) ^ (4 : ℕ)) * (1 / ((cΔ ^ 2) * (r t) ^ (4 : ℕ))) := by
      have hnonneg : 0 ≤ (1 / ((cΔ ^ 2) * (r t) ^ (4 : ℕ))) :=
        one_div_nonneg.2 hdenpos.le
      exact mul_le_mul_of_nonneg_right hNum'' hnonneg
    have hcancel :
        (P * (r t) ^ (4 : ℕ)) * (1 / ((cΔ ^ 2) * (r t) ^ (4 : ℕ))) = P / (cΔ ^ 2) := by
      have hr4ne : (r t) ^ (4 : ℕ) ≠ 0 := ne_of_gt (pow_pos (Real.exp_pos _) 4)
      calc
        (P * (r t) ^ (4 : ℕ)) * (1 / ((cΔ ^ 2) * (r t) ^ (4 : ℕ)))
            = (P * (r t) ^ (4 : ℕ)) / ((cΔ ^ 2) * (r t) ^ (4 : ℕ)) := by
                simp [div_eq_mul_inv]
        _ = P / (cΔ ^ 2) := by
              simpa using! (mul_div_mul_right P (cΔ ^ 2) hr4ne)
    have : ‖BKernel t ht0 - (BleadingLeadingTerm t : ℂ)‖ ≤ P / (cΔ ^ 2) :=
      le_trans hmain (le_trans hscale (le_of_eq hcancel))
    simpa [P, div_eq_mul_inv] using! this
  simpa [cΔ] using! hfinal

end

end SpherePacking.Dim24.LaplaceBSubLeadingBounds
