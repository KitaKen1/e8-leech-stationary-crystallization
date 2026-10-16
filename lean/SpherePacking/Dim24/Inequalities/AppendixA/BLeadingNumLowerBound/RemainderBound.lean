/- Bounding `‖BleadingNumRemainder‖`. -/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.BleadingNumDecomp
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PowerBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.ConstBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.TailBounds
public import Mathlib.Analysis.Real.Pi.Bounds


/-!
### Bounding `‖BleadingNumRemainder‖`

We combine the tail bounds from `TailBounds` with the decomposition from `BleadingNumDecomp` to
prove the global remainder estimate
`‖BleadingNumRemainder‖ ≤ eps * (r t)^12`.
-/


open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.AppendixA


lemma inv_pi_le_one_local : (1 / Real.pi) ≤ (1 : ℝ) := by
  simpa using!
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (le_trans (by norm_num) (le_of_lt Real.pi_gt_three)))

lemma two_div_pi_le_one : (2 / Real.pi) ≤ (1 : ℝ) := by
  have hpi : (2 : ℝ) ≤ Real.pi := le_trans (by norm_num) (le_of_lt Real.pi_gt_three)
  exact (div_le_iff₀ Real.pi_pos).2 (by simpa using! hpi)

/--
Helper bound for the constant part of the missing `Δ^2` term.

Split off as a separate lemma to avoid exhausting the heartbeat budget inside the global remainder
estimate. -/
lemma BleadingNumRemainder_missing_c_norm_le (t : ℝ) (ht : 1 ≤ t) (ht0 : 0 < t)
    (hmissing :
      ‖(coeffDeltaSq 50 : ℂ) * qterm (it t ht0) 49‖ ≤
        CdeltaSq * (51 : ℝ) ^ (29 : ℕ) * (r t) ^ (98 : ℕ)) :
    ‖((10 / 117 : ℂ) * (1 / (Real.pi : ℂ))) * ((coeffDeltaSq 50 : ℂ) * qterm (it t ht0) 49)‖
      ≤ eps * (r t) ^ (12 : ℕ) / 20 := by
  set δ : ℝ := eps * (r t) ^ (12 : ℕ)
  have hr_nonneg : 0 ≤ r t := (Real.exp_pos _).le
  have hr12_nonneg : 0 ≤ (r t) ^ (12 : ℕ) := pow_nonneg hr_nonneg _
  have hr98_r12 :
      (r t) ^ (98 : ℕ) ≤ (2 : ℝ) ^ (29 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) :=
    rpow98_le_twoPow29_oneDiv23Pow88_rpow12 (t := t) (ht := ht)
  have hcoef' :
      ((10 : ℝ) * (CdeltaSq : ℝ) * (2 : ℝ) ^ (29 : ℕ) * (51 : ℝ) ^ (29 : ℕ) *
            ((1 : ℝ) / 23) ^ (88 : ℕ)) / 117 ≤ eps / 20 := by
    have hpos : (0 : ℝ) < 117 := by positivity
    exact (div_le_iff₀ hpos).2 <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using! const_delta_c_div20
  have hinv : ‖(1 / (Real.pi : ℂ))‖ ≤ (1 : ℝ) := by
    have hpiabs : |Real.pi|⁻¹ ≤ (1 : ℝ) := by
      simpa [abs_of_nonneg (le_of_lt Real.pi_pos), one_div] using! inv_pi_le_one_local
    simpa [div_eq_mul_inv, one_div, Complex.norm_real] using! hpiabs
  have hbound1 :
      ‖((10 / 117 : ℂ) * (1 / (Real.pi : ℂ))) * ((coeffDeltaSq 50 : ℂ) * qterm (it t ht0) 49)‖ ≤
        (10 / 117 : ℝ) * (CdeltaSq * (51 : ℝ) ^ (29 : ℕ) * (r t) ^ (98 : ℕ)) := by
    calc
      ‖((10 / 117 : ℂ) * (1 / (Real.pi : ℂ))) * ((coeffDeltaSq 50 : ℂ) * qterm (it t ht0) 49)‖
          = (10 / 117 : ℝ) * ‖(1 / (Real.pi : ℂ))‖ *
              ‖(coeffDeltaSq 50 : ℂ) * qterm (it t ht0) 49‖ := by
            simp [mul_assoc]
      _ ≤ (10 / 117 : ℝ) * (1 : ℝ) * (CdeltaSq * (51 : ℝ) ^ (29 : ℕ) * (r t) ^ (98 : ℕ)) := by
            gcongr
      _ = (10 / 117 : ℝ) * (CdeltaSq * (51 : ℝ) ^ (29 : ℕ) * (r t) ^ (98 : ℕ)) := by ring_nf
  have hstep :
      (10 / 117 : ℝ) * (CdeltaSq * (51 : ℝ) ^ (29 : ℕ) * (r t) ^ (98 : ℕ)) ≤ δ / 20 := by
    have hKnonneg : 0 ≤ ((10 : ℝ) * (CdeltaSq : ℝ) * (51 : ℝ) ^ (29 : ℕ)) / 117 := by
      dsimp [CdeltaSq, Cdelta]
      positivity
    calc
      (10 / 117 : ℝ) * (CdeltaSq * (51 : ℝ) ^ (29 : ℕ) * (r t) ^ (98 : ℕ))
          = (((10 : ℝ) * (CdeltaSq : ℝ) * (51 : ℝ) ^ (29 : ℕ)) / 117) *
              (r t) ^ (98 : ℕ) := by ring_nf
      _ ≤ (((10 : ℝ) * (CdeltaSq : ℝ) * (51 : ℝ) ^ (29 : ℕ)) / 117) *
            ((2 : ℝ) ^ (29 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ)) := by
              exact mul_le_mul_of_nonneg_left hr98_r12 hKnonneg
      _ =
          (((10 : ℝ) * (CdeltaSq : ℝ) * (2 : ℝ) ^ (29 : ℕ) * (51 : ℝ) ^ (29 : ℕ) *
                ((1 : ℝ) / 23) ^ (88 : ℕ)) / 117) *
            (r t) ^ (12 : ℕ) := by ring_nf
      _ ≤ (eps / 20) * (r t) ^ (12 : ℕ) := by
            exact mul_le_mul_of_nonneg_right hcoef' hr12_nonneg
      _ = δ / 20 := by simp [δ, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
  exact
    Std.IsPreorder.le_trans
      ‖10 / 117 * (1 / ↑Real.pi) * (↑(coeffDeltaSq 50) * qterm (it t ht0) 49)‖
      (10 / 117 * (CdeltaSq * 51 ^ 29 * r t ^ 98)) (δ / 20) hbound1 hstep

lemma norm_add3_le (a b c : ℂ) :
    ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  simpa using! (norm_add₃_le (a := a) (b := b) (c := c))

lemma BleadingNumRemainder_bigPi_norm_le_of_bounds (t : ℝ) (z : ℍ) (δ : ℝ)
    (h_varphi :
      ‖((Real.pi : ℂ) / (28304640 : ℂ)) *
            ((t : ℂ) ^ (2 : ℕ) *
              qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN)‖ ≤
        δ / 10)
    (h_phi1 :
      ‖((Real.pi : ℂ) / (28304640 : ℂ)) *
            ((t : ℂ) * (((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
              qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN))‖ ≤
        δ / 10)
    (h_phi2 :
      ‖((Real.pi : ℂ) / (28304640 : ℂ)) *
            (-((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ)) *
              qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN))‖ ≤
        δ / 10) :
    ‖((Real.pi : ℂ) / (28304640 : ℂ)) *
          ((t : ℂ) ^ (2 : ℕ) * qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN +
            (t : ℂ) * (((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
              qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN) -
              ((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ)) *
                qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN))‖
      ≤ δ / 10 + δ / 10 + δ / 10 := by
  set a : ℂ :=
    ((Real.pi : ℂ) / (28304640 : ℂ)) *
      ((t : ℂ) ^ (2 : ℕ) * qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN)
  set b : ℂ :=
    ((Real.pi : ℂ) / (28304640 : ℂ)) *
      ((t : ℂ) * (((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
        qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN))
  set c : ℂ :=
    ((Real.pi : ℂ) / (28304640 : ℂ)) *
      (-((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ)) *
        qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN))
  have hrewrite :
      ((Real.pi : ℂ) / (28304640 : ℂ)) *
            ((t : ℂ) ^ (2 : ℕ) * qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN +
              (t : ℂ) * (((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
                qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN) -
                ((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ)) *
                  qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN))
        = a + b + c := by
    simp [a, b, c, mul_add, sub_eq_add_neg, add_assoc]
  have htri : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := norm_add3_le a b c
  grind only

lemma BleadingNumRemainder_norm_le_of_bounds (R A B C D : ℂ) (δ : ℝ)
    (hR : R = A + B + C + D)
    (hA : ‖A‖ ≤ δ / 10 + δ / 10 + δ / 10)
    (hB : ‖B‖ ≤ δ / 10)
    (hC : ‖C‖ ≤ δ / 20 + δ / 20)
    (hD : ‖D‖ ≤ δ / 20 + δ / 20)
    (hδ : 0 ≤ δ) :
    ‖R‖ ≤ δ := by
  have hsum :
      (δ / 10 + δ / 10 + δ / 10) + (δ / 10) + (δ / 20 + δ / 20) + (δ / 20 + δ / 20) ≤ δ := by
    nlinarith [hδ]
  have hsubs :
      ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ ≤
        (δ / 10 + δ / 10 + δ / 10) + (δ / 10) + (δ / 20 + δ / 20) + (δ / 20 + δ / 20) := by
    nlinarith [hA, hB, hC, hD]
  calc
    ‖R‖ = ‖A + B + C + D‖ := by simp [hR]
    _ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
          simpa using! (norm_add₄_le (a := A) (b := B) (c := C) (d := D))
    _ ≤ (δ / 10 + δ / 10 + δ / 10) + (δ / 10) + (δ / 20 + δ / 20) + (δ / 20 + δ / 20) := hsubs
    _ ≤ δ := hsum

lemma leadingScale_mul_norm_le (t : ℝ) (X : ℂ) (δ : ℝ)
    (h_t : ‖(-(1 / 39 : ℂ) * (t : ℂ)) * X‖ ≤ δ / 20)
    (h_c : ‖((10 / (117 : ℂ)) * (1 / (Real.pi : ℂ))) * X‖ ≤ δ / 20) :
    ‖(leadingScale t) * X‖ ≤ δ / 20 + δ / 20 := by
  have htri :
      ‖(leadingScale t) * X‖ ≤
        ‖(-(1 / 39 : ℂ) * (t : ℂ)) * X‖ + ‖((10 / (117 : ℂ)) * (1 / (Real.pi : ℂ))) * X‖ := by
    simpa [leadingScale, add_mul, mul_assoc] using!
      (norm_add_le ((-(1 / 39 : ℂ) * (t : ℂ)) * X) (((10 / (117 : ℂ)) * (1 / (Real.pi : ℂ))) * X))
  exact htri.trans (add_le_add h_t h_c)

lemma BleadingNumRemainder_bigPi_norm_le (t : ℝ) (ht : 1 ≤ t) (ht0 : 0 < t) :
    let z : ℍ := it t ht0
    let δ : ℝ := eps * (r t) ^ (12 : ℕ)
    ‖((Real.pi : ℂ) / (28304640 : ℂ)) *
          ((t : ℂ) ^ (2 : ℕ) * qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN +
            (t : ℂ) * (((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
              qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN) -
              ((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ)) *
                qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN))‖
      ≤ δ / 10 + δ / 10 + δ / 10 := by
  intro z δ
  have ht_nonneg : 0 ≤ t := ht0.le
  have hr_nonneg : 0 ≤ r t := (Real.exp_pos _).le
  have hr12_nonneg : 0 ≤ (r t) ^ (12 : ℕ) := pow_nonneg hr_nonneg _
  -- Tail bounds.
  have hvarphiTail :
      ‖qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN‖ ≤
        Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * (r t) ^ (100 : ℕ))) := by
    simpa [z] using! qtail_varphi_le_Cvarphi_rpow100 (t := t) (ht0 := ht0) (ht := ht)
  have hphi1Tail :
      ‖qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN‖ ≤
        Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * (r t) ^ (100 : ℕ))) := by
    simpa [z] using! qtail_phi1_le_Cvarphi_rpow100 (t := t) (ht0 := ht0) (ht := ht)
  have hphi2Tail :
      ‖qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN‖ ≤
        Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * (r t) ^ (100 : ℕ))) := by
    simpa [z] using! qtail_phi2_le_Cvarphi_rpow100 (t := t) (ht0 := ht0) (ht := ht)
  -- Converting `r^100` into `r^12`.
  have ht2_r100 : t ^ (2 : ℕ) * (r t) ^ (100 : ℕ) ≤ ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) :=
    t_sq_mul_rpow100_le (t := t) (ht := ht)
  have ht_r100 : t * (r t) ^ (100 : ℕ) ≤ ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) :=
    t_mul_rpow100_le (t := t) (ht := ht)
  have hr100_r12 : (r t) ^ (100 : ℕ) ≤ ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) :=
    rpow100_le_oneDiv23Pow88_rpow12 (t := t) (ht := ht)
  have hpi_le_four : (Real.pi : ℝ) ≤ 4 := (Real.pi_lt_four).le
  have h_varphi :
      ‖((Real.pi : ℂ) / (28304640 : ℂ)) *
            ((t : ℂ) ^ (2 : ℕ) * qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN)‖
        ≤ δ / 10 := by
    have hcoef : ‖(Real.pi : ℂ) / (28304640 : ℂ)‖ ≤ (4 : ℝ) / 28304640 := by
      have hpi_nonneg : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
      have habs : |Real.pi| ≤ (4 : ℝ) := by
        simpa [abs_of_nonneg hpi_nonneg] using! hpi_le_four
      have h' : |Real.pi| / 28304640 ≤ (4 : ℝ) / 28304640 :=
        div_le_div_of_nonneg_right habs (by positivity : (0 : ℝ) ≤ (28304640 : ℝ))
      have : (‖(Real.pi : ℂ) / (28304640 : ℂ)‖ : ℝ) = |Real.pi| / 28304640 := by
        simp [div_eq_mul_inv]
      simpa [this] using! h'
    have ht2norm : ‖(t : ℂ) ^ (2 : ℕ)‖ = t ^ (2 : ℕ) := by
      simp [Complex.norm_real, Real.norm_of_nonneg ht_nonneg]
    have hbound1 :
        ‖((Real.pi : ℂ) / (28304640 : ℂ)) *
              ((t : ℂ) ^ (2 : ℕ) *
                qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN)‖
          ≤ (4 / 28304640 : ℝ) * (t ^ (2 : ℕ)) *
              (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * (r t) ^ (100 : ℕ)))) := by
      calc
        ‖((Real.pi : ℂ) / (28304640 : ℂ)) *
              ((t : ℂ) ^ (2 : ℕ) *
                qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN)‖
            = ‖(Real.pi : ℂ) / (28304640 : ℂ)‖ * (t ^ (2 : ℕ)) *
                ‖qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN‖ := by
                  simp [mul_assoc, ht2norm]
        _ ≤ (4 / 28304640 : ℝ) * (t ^ (2 : ℕ)) *
              (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * (r t) ^ (100 : ℕ)))) := by
                  gcongr
    have hcoef' :
        ((8 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ)) / 28304640 ≤
          eps / 10 := by
      have hpos : (0 : ℝ) < 28304640 := by positivity
      exact (div_le_iff₀ hpos).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using! const_varphi_div10
    have hstep :
        (4 / 28304640 : ℝ) * (t ^ (2 : ℕ)) *
            (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * (r t) ^ (100 : ℕ))))
          ≤ δ / 10 := by
      have htr :
          (t ^ (2 : ℕ)) * (r t) ^ (100 : ℕ) ≤
            ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) :=
        ht2_r100
      have hKnonneg : 0 ≤ ((8 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ)) / 28304640 := by
        dsimp [Cvarphi]
        positivity
      calc
        (4 / 28304640 : ℝ) * (t ^ (2 : ℕ)) *
            (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * (r t) ^ (100 : ℕ))))
            = (((8 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ)) / 28304640) *
                ((t ^ (2 : ℕ)) * (r t) ^ (100 : ℕ)) := by ring_nf
        _ ≤ (((8 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ)) / 28304640) *
              (((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left htr hKnonneg
        _ =
            (((8 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) *
                  ((1 : ℝ) / 23) ^ (88 : ℕ)) / 28304640) *
              (r t) ^ (12 : ℕ) := by ring_nf
        _ ≤ (eps / 10) * (r t) ^ (12 : ℕ) := by
              exact mul_le_mul_of_nonneg_right hcoef' hr12_nonneg
        _ = δ / 10 := by simp [δ, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
    exact le_trans hbound1 hstep
  have h_phi1 :
      ‖((Real.pi : ℂ) / (28304640 : ℂ)) *
            ((t : ℂ) * (((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
              qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN))‖
        ≤ δ / 10 := by
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hrepl :
        ((Real.pi : ℂ) / (28304640 : ℂ)) *
              ((t : ℂ) * (((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
                qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN))
            =
          ((-6 : ℂ) / (28304640 : ℂ)) *
              ((t : ℂ) * qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN) := by
      field_simp [hπ]
    have hcoef' :
        ((2 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ)) / 4717440 ≤
          eps / 10 := by
      have hpos : (0 : ℝ) < 4717440 := by positivity
      exact (div_le_iff₀ hpos).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using! const_phi1_div10
    have hKnonneg : 0 ≤ ((2 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ)) / 4717440 := by
      dsimp [Cvarphi]
      positivity
    have htr : t * (r t) ^ (100 : ℕ) ≤ ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) := ht_r100
    have hmain :
        ‖((-6 : ℂ) / (28304640 : ℂ)) *
              ((t : ℂ) * qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN)‖
          ≤ δ / 10 := by
      have h6 : (‖((-6 : ℂ) / (28304640 : ℂ))‖ : ℝ) = (1 : ℝ) / 4717440 := by
        norm_num [div_eq_mul_inv]
      have ht_norm : ‖(t : ℂ)‖ = t := by simp [Complex.norm_real, Real.norm_of_nonneg ht_nonneg]
      have hbound1 :
          ‖((-6 : ℂ) / (28304640 : ℂ)) *
                ((t : ℂ) *
                  qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN)‖
            ≤ (1 / 4717440 : ℝ) * t *
                (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * (r t) ^ (100 : ℕ)))) := by
        have hA_nonneg : 0 ≤ (1 / 4717440 : ℝ) * t := by
          have : 0 ≤ (1 / 4717440 : ℝ) := by positivity
          exact mul_nonneg this ht_nonneg
        calc
          ‖((-6 : ℂ) / (28304640 : ℂ)) *
                ((t : ℂ) *
                  qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN)‖
              = ((1 / 4717440 : ℝ) * t) *
                  ‖qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z
                      BleadingCoeffs.QN‖ := by
                  calc
                    ‖((-6 : ℂ) / (28304640 : ℂ)) *
                          ((t : ℂ) *
                            qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN)‖
                        = (‖((-6 : ℂ) / (28304640 : ℂ))‖ : ℝ) *
                            ‖(t : ℂ) * qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z
                                BleadingCoeffs.QN‖ := by
                            simp
                    _ = (1 / 4717440 : ℝ) *
                            (‖(t : ℂ) * qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z
                                BleadingCoeffs.QN‖) := by
                            norm_num
                    _ = (1 / 4717440 : ℝ) *
                            (‖(t : ℂ)‖ *
                              ‖qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z
                                  BleadingCoeffs.QN‖) := by
                            simp
                    _ = ((1 / 4717440 : ℝ) * t) *
                            ‖qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z
                                BleadingCoeffs.QN‖ := by
                            rw [ht_norm]
                            ring_nf
          _ ≤ ((1 / 4717440 : ℝ) * t) *
                  (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * (r t) ^ (100 : ℕ)))) := by
                  exact mul_le_mul_of_nonneg_left hphi1Tail hA_nonneg
          _ = (1 / 4717440 : ℝ) * t *
                  (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * (r t) ^ (100 : ℕ)))) := by
                  ring_nf
      have hstep :
          (1 / 4717440 : ℝ) * t * (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * (r t) ^ (100 : ℕ))))
            ≤ δ / 10 := by
        calc
          (1 / 4717440 : ℝ) * t * (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * (r t) ^ (100 : ℕ))))
              = (((2 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ)) / 4717440) *
                  (t * (r t) ^ (100 : ℕ)) := by ring_nf
          _ ≤ (((2 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ)) / 4717440) *
                  (((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ)) := by
                exact mul_le_mul_of_nonneg_left htr hKnonneg
          _ =
              (((2 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) *
                    ((1 : ℝ) / 23) ^ (88 : ℕ)) / 4717440) *
                (r t) ^ (12 : ℕ) := by ring_nf
          _ ≤ (eps / 10) * (r t) ^ (12 : ℕ) := by
                exact mul_le_mul_of_nonneg_right hcoef' hr12_nonneg
          _ = δ / 10 := by simp [δ, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
      exact le_trans hbound1 hstep
    exact le_of_eq_of_le (congrArg norm hrepl) hmain
  have h_phi2 :
      ‖((Real.pi : ℂ) / (28304640 : ℂ)) *
            (-((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ)) *
              qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN))‖
        ≤ δ / 10 := by
    have hcoef' :
        ((72 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) *
              ((1 : ℝ) / 23) ^ (88 : ℕ)) / 28304640 ≤ eps / 10 := by
      have hpos : (0 : ℝ) < 28304640 := by positivity
      exact (div_le_iff₀ hpos).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using! const_phi2_div10
    have hKnonneg : 0 ≤ ((72 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ)) / 28304640 := by
      dsimp [Cvarphi]
      positivity
    have hbound1 :
        ‖((Real.pi : ℂ) / (28304640 : ℂ)) *
              (-((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ)) *
                qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN))‖
          ≤ (72 / 28304640 : ℝ) * (Cvarphi * (51 ^ (20 : ℕ) * (r t) ^ (100 : ℕ))) := by
      have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hinv : ‖(1 / (Real.pi : ℂ))‖ ≤ (1 : ℝ) := by
        have hpi_nonneg : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
        have hnorm : (‖(1 / (Real.pi : ℂ))‖ : ℝ) = (1 / Real.pi) := by
          simp [div_eq_mul_inv, abs_of_nonneg hpi_nonneg]
        rw [hnorm]
        exact inv_pi_le_one_local
      have h36le : ‖(36 : ℂ) / (28304640 : ℂ)‖ ≤ (36 / 28304640 : ℝ) := by
        norm_num [div_eq_mul_inv]
      calc
        ‖((Real.pi : ℂ) / (28304640 : ℂ)) *
              (-((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ)) *
                qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN))‖
            = ‖(36 : ℂ) / (28304640 : ℂ) * (1 / (Real.pi : ℂ)) *
                qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN‖ := by
                  field_simp [hπ]
        _ ≤ ‖(36 : ℂ) / (28304640 : ℂ)‖ * ‖(1 / (Real.pi : ℂ))‖ *
                ‖qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN‖ := by
                  simp [mul_assoc]
        _ ≤ (36 / 28304640 : ℝ) * (1 : ℝ) *
                (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * (r t) ^ (100 : ℕ)))) := by
                  gcongr
        _ = (72 / 28304640 : ℝ) * (Cvarphi * (51 ^ (20 : ℕ) * (r t) ^ (100 : ℕ))) := by ring_nf
    have hstep :
        (72 / 28304640 : ℝ) * (Cvarphi * (51 ^ (20 : ℕ) * (r t) ^ (100 : ℕ))) ≤ δ / 10 := by
      have htr : (r t) ^ (100 : ℕ) ≤ ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) := hr100_r12
      calc
        (72 / 28304640 : ℝ) * (Cvarphi * (51 ^ (20 : ℕ) * (r t) ^ (100 : ℕ)))
            = (((72 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ)) / 28304640) *
                (r t) ^ (100 : ℕ) := by
                ring_nf
        _ ≤ (((72 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ)) / 28304640) *
              (((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ)) := by
                exact mul_le_mul_of_nonneg_left htr hKnonneg
        _ =
            (((72 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) *
                  ((1 : ℝ) / 23) ^ (88 : ℕ)) / 28304640) *
              (r t) ^ (12 : ℕ) := by ring_nf
        _ ≤ (eps / 10) * (r t) ^ (12 : ℕ) := by
              exact mul_le_mul_of_nonneg_right hcoef' hr12_nonneg
        _ = δ / 10 := by simp [δ, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
    exact le_trans hbound1 hstep
  exact
    BleadingNumRemainder_bigPi_norm_le_of_bounds (t := t) (z := z) (δ := δ) h_varphi h_phi1 h_phi2

/--
Main remainder estimate: for `t ≥ 1`, `BleadingNumRemainder` is `O((r t)^12)`
with constant `eps`. -/
public lemma BleadingNumRemainder_norm_le (t : ℝ) (ht : 1 ≤ t) (ht0 : 0 < t) :
    ‖BleadingNumRemainder t ht‖ ≤ eps * (r t) ^ (12 : ℕ) := by
  set z : ℍ := it t ht0
  set δ : ℝ := eps * (r t) ^ (12 : ℕ)
  have ht_nonneg : 0 ≤ t := ht0.le
  have hr_nonneg : 0 ≤ r t := (Real.exp_pos _).le
  have hr12_nonneg : 0 ≤ (r t) ^ (12 : ℕ) := pow_nonneg hr_nonneg _
  have hδ_nonneg : 0 ≤ δ := by dsimp [δ, eps]; positivity
  -- Tail bounds.
  have hpsiTail :
      ‖rtail psiCoeffFun t BleadingCoeffs.N‖ ≤
        ((16 : ℝ) ^ (8 : ℕ)) * (2 * ((101 : ℝ) ^ (27 : ℕ) * (r t) ^ (100 : ℕ))) := by
    simpa using! rtail_psi_le_rpow100 (t := t) (ht0 := ht0) (ht := ht)
  have hdeltaTail :
      ‖qtail (fun n : ℕ => (coeffDeltaSqShift n)) z BleadingCoeffs.QN‖ ≤
        (CdeltaSq * (2 : ℝ) ^ (29 : ℕ)) * (2 * ((51 : ℝ) ^ (29 : ℕ) * (r t) ^ (100 : ℕ))) := by
    simpa [coeffDeltaSqShift, z] using!
      qtail_deltaShift_le_Cdelta_rpow100 (t := t) (ht0 := ht0) (ht := ht)
  have hmissing :
      ‖(coeffDeltaSq 50 : ℂ) * qterm z 49‖ ≤
        CdeltaSq * (51 : ℝ) ^ (29 : ℕ) * (r t) ^ (98 : ℕ) := by
    simpa [z] using! norm_missingDeltaTerm_le (t := t) (ht0 := ht0)
  -- Converting `r^100` and `r^98` into `r^12`.
  have ht_r100 : t * (r t) ^ (100 : ℕ) ≤ ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) :=
    t_mul_rpow100_le (t := t) (ht := ht)
  have hr100_r12 : (r t) ^ (100 : ℕ) ≤ ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) :=
    rpow100_le_oneDiv23Pow88_rpow12 (t := t) (ht := ht)
  have hr98_r12 :
      (r t) ^ (98 : ℕ) ≤ (2 : ℝ) ^ (29 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) :=
    rpow98_le_twoPow29_oneDiv23Pow88_rpow12 (t := t) (ht := ht)
  have h_bigPi :
      ‖((Real.pi : ℂ) / (28304640 : ℂ)) *
            ((t : ℂ) ^ (2 : ℕ) * qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN +
              (t : ℂ) * (((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
                qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN) -
                ((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ)) *
                  qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN))‖
        ≤ δ / 10 + δ / 10 + δ / 10 := by
    simpa [z, δ] using! BleadingNumRemainder_bigPi_norm_le (t := t) (ht := ht) (ht0 := ht0)
  -- Psi tail term.
  have h_psi :
      ‖(1 / ((65520 : ℂ) * Real.pi)) * rtail psiCoeffFun t BleadingCoeffs.N‖ ≤ δ / 10 := by
    have hcoef' :
        ((2 : ℝ) * ((16 : ℝ) ^ (8 : ℕ)) * (101 : ℝ) ^ (27 : ℕ) *
              ((1 : ℝ) / 23) ^ (88 : ℕ)) / 65520 ≤
          eps / 10 := by
      have hpos : (0 : ℝ) < 65520 := by positivity
      exact (div_le_iff₀ hpos).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using! const_psi_div10
    have hKnonneg :
        0 ≤ ((2 : ℝ) * ((16 : ℝ) ^ (8 : ℕ)) * (101 : ℝ) ^ (27 : ℕ)) / 65520 := by positivity
    have hbound1 :
        ‖(1 / ((65520 : ℂ) * Real.pi)) * rtail psiCoeffFun t BleadingCoeffs.N‖
          ≤ (1 / 65520 : ℝ) *
              (((16 : ℝ) ^ (8 : ℕ)) *
                (2 * ((101 : ℝ) ^ (27 : ℕ) * (r t) ^ (100 : ℕ)))) := by
      have : ‖(1 / ((65520 : ℂ) * Real.pi))‖ ≤ (1 : ℝ) / 65520 := by
        have hpi : (1 / Real.pi) ≤ (1 : ℝ) := inv_pi_le_one_local
        have hpi_nonneg : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
        have : (‖(1 / ((65520 : ℂ) * Real.pi))‖ : ℝ) = (1 / 65520) * (1 / Real.pi) := by
          simp [div_eq_mul_inv, mul_left_comm, mul_comm, abs_of_nonneg hpi_nonneg]
        grind only
      exact norm_mul_le_of_le this hpsiTail
    have hstep :
        (1 / 65520 : ℝ) *
            (((16 : ℝ) ^ (8 : ℕ)) *
              (2 * ((101 : ℝ) ^ (27 : ℕ) * (r t) ^ (100 : ℕ)))) ≤
          δ / 10 := by
      have htr : (r t) ^ (100 : ℕ) ≤ ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) := hr100_r12
      calc
        (1 / 65520 : ℝ) *
            (((16 : ℝ) ^ (8 : ℕ)) *
              (2 * ((101 : ℝ) ^ (27 : ℕ) * (r t) ^ (100 : ℕ))))
            = (((2 : ℝ) * ((16 : ℝ) ^ (8 : ℕ)) * (101 : ℝ) ^ (27 : ℕ)) / 65520) *
                (r t) ^ (100 : ℕ) := by
                ring_nf
        _ ≤ (((2 : ℝ) * ((16 : ℝ) ^ (8 : ℕ)) * (101 : ℝ) ^ (27 : ℕ)) / 65520) *
              (((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ)) := by
                exact mul_le_mul_of_nonneg_left htr hKnonneg
        _ =
            (((2 : ℝ) * ((16 : ℝ) ^ (8 : ℕ)) * (101 : ℝ) ^ (27 : ℕ) *
                  ((1 : ℝ) / 23) ^ (88 : ℕ)) / 65520) *
              (r t) ^ (12 : ℕ) := by ring_nf
        _ ≤ (eps / 10) * (r t) ^ (12 : ℕ) := by
              exact mul_le_mul_of_nonneg_right hcoef' hr12_nonneg
        _ = δ / 10 := by simp [δ, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
    exact le_trans hbound1 hstep
  -- Delta tail (split `leadingScale` into `t` and constant parts).
  have h_delta_t :
      ‖(-(1 / 39 : ℂ) * (t : ℂ)) *
            qtail (fun n : ℕ => (coeffDeltaSqShift n)) z BleadingCoeffs.QN‖
        ≤ δ / 20 := by
    have hcoef' :
        ((2 : ℝ) * (CdeltaSq : ℝ) * (2 : ℝ) ^ (29 : ℕ) * (51 : ℝ) ^ (29 : ℕ) *
              ((1 : ℝ) / 23) ^ (88 : ℕ)) / 39 ≤
          eps / 20 := by
      have hpos : (0 : ℝ) < 39 := by positivity
      exact (div_le_iff₀ hpos).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using! const_delta_t_div20
    have hKnonneg :
        0 ≤ ((2 : ℝ) * (CdeltaSq : ℝ) * (2 : ℝ) ^ (29 : ℕ) * (51 : ℝ) ^ (29 : ℕ)) / 39 := by
      dsimp [CdeltaSq, Cdelta]
      positivity
    have hbound1 :
        ‖(-(1 / 39 : ℂ) * (t : ℂ)) *
              qtail (fun n : ℕ => (coeffDeltaSqShift n)) z BleadingCoeffs.QN‖
          ≤ (1 / 39 : ℝ) * t *
              ((CdeltaSq * (2 : ℝ) ^ (29 : ℕ)) *
                (2 * ((51 : ℝ) ^ (29 : ℕ) * (r t) ^ (100 : ℕ)))) := by
      have ht_norm : ‖(t : ℂ)‖ = t := by simp [Complex.norm_real, Real.norm_of_nonneg ht_nonneg]
      have h39_norm : (‖(1 / 39 : ℂ)‖ : ℝ) = (1 / 39 : ℝ) := by
        norm_num [div_eq_mul_inv]
      have hA_nonneg : 0 ≤ (1 / 39 : ℝ) * t := by
        have : 0 ≤ (1 / 39 : ℝ) := by positivity
        exact mul_nonneg this ht_nonneg
      calc
        ‖(-(1 / 39 : ℂ) * (t : ℂ)) *
              qtail (fun n : ℕ => (coeffDeltaSqShift n)) z BleadingCoeffs.QN‖
            = ‖(1 / 39 : ℂ)‖ * ‖(t : ℂ)‖ *
                ‖qtail (fun n : ℕ => (coeffDeltaSqShift n)) z BleadingCoeffs.QN‖ := by
                  simp [mul_assoc]
        _ = ((1 / 39 : ℝ) * t) *
                ‖qtail (fun n : ℕ => (coeffDeltaSqShift n)) z BleadingCoeffs.QN‖ := by
                  lia
        _ ≤ ((1 / 39 : ℝ) * t) *
              ((CdeltaSq * (2 : ℝ) ^ (29 : ℕ)) *
                (2 * ((51 : ℝ) ^ (29 : ℕ) * (r t) ^ (100 : ℕ)))) := by
                  exact mul_le_mul_of_nonneg_left hdeltaTail hA_nonneg
        _ = (1 / 39 : ℝ) * t *
              ((CdeltaSq * (2 : ℝ) ^ (29 : ℕ)) *
                (2 * ((51 : ℝ) ^ (29 : ℕ) * (r t) ^ (100 : ℕ)))) := by
                  ring_nf
    have hstep :
        (1 / 39 : ℝ) * t *
            ((CdeltaSq * (2 : ℝ) ^ (29 : ℕ)) *
              (2 * ((51 : ℝ) ^ (29 : ℕ) * (r t) ^ (100 : ℕ))))
          ≤ δ / 20 := by
      have htr : t * (r t) ^ (100 : ℕ) ≤ ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) := ht_r100
      calc
        (1 / 39 : ℝ) * t *
            ((CdeltaSq * (2 : ℝ) ^ (29 : ℕ)) * (2 * ((51 : ℝ) ^ (29 : ℕ) * (r t) ^ (100 : ℕ))))
            = (((2 : ℝ) * (CdeltaSq : ℝ) * (2 : ℝ) ^ (29 : ℕ) * (51 : ℝ) ^ (29 : ℕ)) / 39) *
                (t * (r t) ^ (100 : ℕ)) := by ring_nf
        _ ≤ (((2 : ℝ) * (CdeltaSq : ℝ) * (2 : ℝ) ^ (29 : ℕ) * (51 : ℝ) ^ (29 : ℕ)) / 39) *
              (((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ)) := by
                exact mul_le_mul_of_nonneg_left htr hKnonneg
        _ =
            (((2 : ℝ) * (CdeltaSq : ℝ) * (2 : ℝ) ^ (29 : ℕ) * (51 : ℝ) ^ (29 : ℕ) *
                  ((1 : ℝ) / 23) ^ (88 : ℕ)) / 39) *
              (r t) ^ (12 : ℕ) := by ring_nf
        _ ≤ (eps / 20) * (r t) ^ (12 : ℕ) := by
              exact mul_le_mul_of_nonneg_right hcoef' hr12_nonneg
        _ = δ / 20 := by simp [δ, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
    exact le_trans hbound1 hstep
  have h_delta_c :
      ‖((10 / 117 : ℂ) * (1 / (Real.pi : ℂ))) *
            qtail (fun n : ℕ => (coeffDeltaSqShift n)) z BleadingCoeffs.QN‖
        ≤ δ / 20 := by
    have hcoef' :
        ((10 : ℝ) * (CdeltaSq : ℝ) * (2 : ℝ) ^ (29 : ℕ) * (51 : ℝ) ^ (29 : ℕ) *
              ((1 : ℝ) / 23) ^ (88 : ℕ)) / 117 ≤
          eps / 20 := by
      have hpos : (0 : ℝ) < 117 := by positivity
      exact (div_le_iff₀ hpos).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using! const_delta_c_div20
    have hKnonneg :
        0 ≤ ((10 : ℝ) * (CdeltaSq : ℝ) * (2 : ℝ) ^ (29 : ℕ) * (51 : ℝ) ^ (29 : ℕ)) / 117 := by
      dsimp [CdeltaSq, Cdelta]
      positivity
    have hbound1 :
        ‖((10 / 117 : ℂ) * (1 / (Real.pi : ℂ))) *
              qtail (fun n : ℕ => (coeffDeltaSqShift n)) z BleadingCoeffs.QN‖
          ≤ (10 / 117 : ℝ) *
              ((CdeltaSq * (2 : ℝ) ^ (29 : ℕ)) * ((51 : ℝ) ^ (29 : ℕ) * (r t) ^ (100 : ℕ))) := by
      have hinv : ‖(2 / (Real.pi : ℂ))‖ ≤ (1 : ℝ) := by
        have hpi_nonneg : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
        have hnorm' : (‖(2 / (Real.pi : ℂ))‖ : ℝ) = 2 / Real.pi := by
          simp [div_eq_mul_inv, abs_of_nonneg hpi_nonneg]
        -- rewrite the norm into the scalar expression `2/π`.
        have : (‖(2 / (Real.pi : ℂ))‖ : ℝ) ≤ 1 := by
          -- `rw` avoids extra simp-rewriting through `|π|`.
          rw [hnorm']
          exact two_div_pi_le_one
        simpa using! this
      have hhalf :
          (‖(1 / (Real.pi : ℂ))‖ : ℝ) = (‖(2 / (Real.pi : ℂ))‖ : ℝ) / 2 := by
        -- `1/π = (1/2) * (2/π)` and `‖1/2‖ = 1/2`.
        have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        have hrew : (1 / (Real.pi : ℂ)) = (1 / (2 : ℂ)) * (2 / (Real.pi : ℂ)) := by
          field_simp [hπ]
        calc
          (‖(1 / (Real.pi : ℂ))‖ : ℝ) = ‖(1 / (2 : ℂ)) * (2 / (Real.pi : ℂ))‖ := by
              simp [hrew]
          _ = (‖(1 / (2 : ℂ))‖ : ℝ) * ‖(2 / (Real.pi : ℂ))‖ := by
              simp
          _ = (1 / 2 : ℝ) * ‖(2 / (Real.pi : ℂ))‖ := by
              norm_num [div_eq_mul_inv]
          _ = (‖(2 / (Real.pi : ℂ))‖ : ℝ) / 2 := by ring_nf
      calc
        ‖((10 / 117 : ℂ) * (1 / (Real.pi : ℂ))) *
              qtail (fun n : ℕ => (coeffDeltaSqShift n)) z BleadingCoeffs.QN‖
            = (10 / 117 : ℝ) * (‖(1 / (Real.pi : ℂ))‖ : ℝ) *
                ‖qtail (fun n : ℕ => (coeffDeltaSqShift n)) z BleadingCoeffs.QN‖ := by
                  simp [mul_assoc]
        _ = (10 / 117 : ℝ) * ((‖(2 / (Real.pi : ℂ))‖ : ℝ) / 2) *
                ‖qtail (fun n : ℕ => (coeffDeltaSqShift n)) z BleadingCoeffs.QN‖ := by
                  lia
        _ ≤ (10 / 117 : ℝ) * ((‖(2 / (Real.pi : ℂ))‖ : ℝ) / 2) *
              ((CdeltaSq * (2 : ℝ) ^ (29 : ℕ)) *
                (2 * ((51 : ℝ) ^ (29 : ℕ) * (r t) ^ (100 : ℕ)))) := by
                  have hA_nonneg :
                      0 ≤ (10 / 117 : ℝ) * ((‖(2 / (Real.pi : ℂ))‖ : ℝ) / 2) := by positivity
                  -- apply the delta tail bound and multiply by a nonnegative scalar.
                  simpa [mul_assoc] using!
                    (mul_le_mul_of_nonneg_left hdeltaTail hA_nonneg)
        _ = (10 / 117 : ℝ) * ‖(2 / (Real.pi : ℂ))‖ *
              ((CdeltaSq * (2 : ℝ) ^ (29 : ℕ)) * ((51 : ℝ) ^ (29 : ℕ) * (r t) ^ (100 : ℕ))) := by
                  ring_nf
        _ ≤ (10 / 117 : ℝ) * 1 *
              ((CdeltaSq * (2 : ℝ) ^ (29 : ℕ)) * ((51 : ℝ) ^ (29 : ℕ) * (r t) ^ (100 : ℕ))) := by
                  have hX_nonneg :
                      0 ≤
                        ((CdeltaSq * (2 : ℝ) ^ (29 : ℕ)) *
                          ((51 : ℝ) ^ (29 : ℕ) * (r t) ^ (100 : ℕ))) := by
                        have hc : 0 ≤ (CdeltaSq : ℝ) := by
                          dsimp [CdeltaSq, Cdelta]
                          positivity
                        have h2 : 0 ≤ (2 : ℝ) ^ (29 : ℕ) := by positivity
                        have h51 : 0 ≤ (51 : ℝ) ^ (29 : ℕ) := by positivity
                        have hr100 : 0 ≤ (r t) ^ (100 : ℕ) := pow_nonneg hr_nonneg _
                        exact
                          mul_nonneg (mul_nonneg hc h2)
                            (mul_nonneg h51 hr100)
                  have hAX_nonneg :
                      0 ≤ (10 / 117 : ℝ) *
                          ((CdeltaSq * (2 : ℝ) ^ (29 : ℕ)) *
                            ((51 : ℝ) ^ (29 : ℕ) * (r t) ^ (100 : ℕ))) := by
                        have : 0 ≤ (10 / 117 : ℝ) := by positivity
                        exact mul_nonneg this hX_nonneg
                  have hmul : ((10 / 117 : ℝ) *
                        ((CdeltaSq * (2 : ℝ) ^ (29 : ℕ)) *
                          ((51 : ℝ) ^ (29 : ℕ) * (r t) ^ (100 : ℕ)))) *
                          ‖(2 / (Real.pi : ℂ))‖
                        ≤ ((10 / 117 : ℝ) *
                          ((CdeltaSq * (2 : ℝ) ^ (29 : ℕ)) *
                            ((51 : ℝ) ^ (29 : ℕ) * (r t) ^ (100 : ℕ)))) * 1 :=
                    mul_le_mul_of_nonneg_left hinv hAX_nonneg
                  -- Reassociate into the displayed form.
                  simpa [mul_assoc, mul_left_comm, mul_comm] using! hmul
        _ = (10 / 117 : ℝ) *
              ((CdeltaSq * (2 : ℝ) ^ (29 : ℕ)) * ((51 : ℝ) ^ (29 : ℕ) * (r t) ^ (100 : ℕ))) := by
                  ring_nf
    have hstep :
        (10 / 117 : ℝ) *
            ((CdeltaSq * (2 : ℝ) ^ (29 : ℕ)) * ((51 : ℝ) ^ (29 : ℕ) * (r t) ^ (100 : ℕ)))
          ≤ δ / 20 := by
      have htr : (r t) ^ (100 : ℕ) ≤ ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) := hr100_r12
      calc
        (10 / 117 : ℝ) *
            ((CdeltaSq * (2 : ℝ) ^ (29 : ℕ)) * ((51 : ℝ) ^ (29 : ℕ) * (r t) ^ (100 : ℕ)))
            = (((10 : ℝ) * (CdeltaSq : ℝ) * (2 : ℝ) ^ (29 : ℕ) * (51 : ℝ) ^ (29 : ℕ)) / 117) *
                (r t) ^ (100 : ℕ) := by ring_nf
        _ ≤ (((10 : ℝ) * (CdeltaSq : ℝ) * (2 : ℝ) ^ (29 : ℕ) * (51 : ℝ) ^ (29 : ℕ)) / 117) *
              (((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ)) := by
                exact mul_le_mul_of_nonneg_left htr hKnonneg
        _ =
            (((10 : ℝ) * (CdeltaSq : ℝ) * (2 : ℝ) ^ (29 : ℕ) * (51 : ℝ) ^ (29 : ℕ) *
                  ((1 : ℝ) / 23) ^ (88 : ℕ)) / 117) *
              (r t) ^ (12 : ℕ) := by ring_nf
        _ ≤ (eps / 20) * (r t) ^ (12 : ℕ) := by
              exact mul_le_mul_of_nonneg_right hcoef' hr12_nonneg
        _ = δ / 20 := by simp [δ, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
    exact le_trans hbound1 hstep
  -- Missing Δ² term (use `r^98 → r^12` conversion).
  have h_missing_t :
      ‖(-(1 / 39 : ℂ) * (t : ℂ)) * ((coeffDeltaSq 50 : ℂ) * qterm z 49)‖ ≤ δ / 20 := by
    have hcoef' :
        ((2 : ℝ) * (CdeltaSq : ℝ) * (2 : ℝ) ^ (29 : ℕ) * (51 : ℝ) ^ (29 : ℕ) *
              ((1 : ℝ) / 23) ^ (88 : ℕ)) / 39 ≤
          eps / 20 := by
      have hpos : (0 : ℝ) < 39 := by positivity
      exact (div_le_iff₀ hpos).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using! const_delta_t_div20
    have hKnonneg :
        0 ≤ ((2 : ℝ) * (CdeltaSq : ℝ) * (2 : ℝ) ^ (29 : ℕ) * (51 : ℝ) ^ (29 : ℕ)) / 39 := by
      dsimp [CdeltaSq, Cdelta]
      positivity
    have hbound1 :
        ‖(-(1 / 39 : ℂ) * (t : ℂ)) * ((coeffDeltaSq 50 : ℂ) * qterm z 49)‖ ≤
          (1 / 39 : ℝ) * t * (CdeltaSq * (51 : ℝ) ^ (29 : ℕ) * (r t) ^ (98 : ℕ)) := by
      have h39 : (0 : ℝ) ≤ (1 / 39 : ℝ) := by positivity
      calc
        ‖(-(1 / 39 : ℂ) * (t : ℂ)) * ((coeffDeltaSq 50 : ℂ) * qterm z 49)‖
            = (1 / 39 : ℝ) * t * ‖(coeffDeltaSq 50 : ℂ) * qterm z 49‖ := by
                simp [mul_assoc, Complex.norm_real, Real.norm_of_nonneg ht_nonneg]
        _ ≤ (1 / 39 : ℝ) * t * (CdeltaSq * (51 : ℝ) ^ (29 : ℕ) * (r t) ^ (98 : ℕ)) := by
              gcongr
    have hstep :
        (1 / 39 : ℝ) * t * (CdeltaSq * (51 : ℝ) ^ (29 : ℕ) * (r t) ^ (98 : ℕ)) ≤ δ / 20 := by
      have htr' :
          t * (r t) ^ (98 : ℕ) ≤
            (2 : ℝ) ^ (29 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) * (r t) ^ (12 : ℕ) :=
        t_mul_rpow98_le_twoPow29_oneDiv23Pow88_rpow12 (t := t) (ht := ht)
      nlinarith
    exact le_trans hbound1 hstep
  have h_missing_c :
      ‖((10 / 117 : ℂ) * (1 / (Real.pi : ℂ))) *
            ((coeffDeltaSq 50 : ℂ) * qterm z 49)‖ ≤ δ / 20 :=
    BleadingNumRemainder_missing_c_norm_le t ht ht0 hmissing
  -- Split the delta tail and missing terms via `leadingScale`.
  have h_delta :
      ‖(leadingScale t) *
            qtail (fun n : ℕ => (coeffDeltaSqShift n)) z BleadingCoeffs.QN‖ ≤
          δ / 20 + δ / 20 :=
    leadingScale_mul_norm_le t (qtail (fun n => coeffDeltaSqShift n) z BleadingCoeffs.QN) δ
      h_delta_t h_delta_c
  have h_missing :
      ‖(leadingScale t) * ((coeffDeltaSq 50 : ℂ) * qterm z 49)‖ ≤ δ / 20 + δ / 20 :=
    leadingScale_mul_norm_le (t := t) (X := (coeffDeltaSq 50 : ℂ) * qterm z 49) (δ := δ)
        h_missing_t h_missing_c
  -- Final bound for the whole remainder: use the decomposition into four pieces.
  set A : ℂ :=
    ((Real.pi : ℂ) / (28304640 : ℂ)) *
      ((t : ℂ) ^ (2 : ℕ) * qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN +
        (t : ℂ) * (((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
          qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN) -
          ((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ)) *
            qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN))
  set B : ℂ := (1 / ((65520 : ℂ) * Real.pi)) * rtail psiCoeffFun t BleadingCoeffs.N
  set C : ℂ := (leadingScale t) * qtail (fun n : ℕ => (coeffDeltaSqShift n)) z BleadingCoeffs.QN
  set D : ℂ := (leadingScale t) * ((coeffDeltaSq 50 : ℂ) * qterm z 49)
  have hR : BleadingNumRemainder t ht = A + B + C + D := by
    simp [BleadingNumRemainder, A, B, C, D, z, coeffDeltaSqShift, sub_eq_add_neg, add_assoc]
  exact
    BleadingNumRemainder_norm_le_of_bounds (BleadingNumRemainder t ht) A B C D δ hR h_bigPi h_psi
      h_delta h_missing hδ_nonneg

/--
Bound the difference between `BleadingNum` and the exact truncation
by the remainder estimate. -/
public lemma norm_BleadingNum_sub_exact_trunc_le (t : ℝ) (ht : 1 ≤ t) :
    let ht0 : 0 < t := lt_of_lt_of_le (show (0 : ℝ) < 1 from zero_lt_one) ht
    ‖BleadingNum t ht0 - (Bleading_exact_trunc t : ℂ)‖ ≤ eps * (r t) ^ (12 : ℕ) := by
  intro ht0
  have hEq :
      BleadingNum t ht0 - (Bleading_exact_trunc t : ℂ) = BleadingNumRemainder t ht := by
    simpa using! (BleadingNum_sub_exact_trunc_eq_remainder (t := t) (ht := ht))
  simpa [hEq] using! (BleadingNumRemainder_norm_le (t := t) (ht := ht) (ht0 := ht0))

end SpherePacking.Dim24.AppendixA
