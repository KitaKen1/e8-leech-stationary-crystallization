/- Tail bounds for the numerator `r`-series. -/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingCoeffs
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeriesTailBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.CoeffBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.DeltaCoeffBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.SeriesSplit
public import
SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.QSeriesTailAndCoeffBounds.TailBound
public import
SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiCoeffFunAndTail.PsiCoeffFun
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PhiCoeffBounds

/-!
### Tail bounds at the truncation points (`QN=50`, `N=100`)

We bound the `q`-tails (starting at `q^50`) and the `r`-tail of `psiCoeffFun` (starting at `r^100`)
by explicit multiples of `(r t)^12`.
-/

open scoped BigOperators
open UpperHalfPlane

noncomputable section

namespace SpherePacking.Dim24.AppendixA

private lemma q_pow_50_eq_r_pow_100 (t : ℝ) : (q t) ^ (50 : ℕ) = (r t) ^ (100 : ℕ) := by
  simpa [q_eq_r_sq] using! (pow_mul (r t) 2 50).symm

private lemma Cvarphi_nonneg : (0 : ℝ) ≤ Cvarphi := by
  norm_num [Cvarphi]

private lemma powGeomRatio_le_powGeomRatio_of_le {q q₀ : ℝ} {k N : ℕ} (hq : q ≤ q₀) :
    powGeomRatio q k N ≤ powGeomRatio q₀ k N := by
  have hbase0 : 0 ≤ (((N + 2 : ℝ) / (N + 1 : ℝ)) ^ k) := by positivity
  simpa [powGeomRatio] using! mul_le_mul_of_nonneg_right hq hbase0

private lemma powGeomRatio_q_29_50_le_half (t : ℝ) (ht : 1 ≤ t) :
    powGeomRatio (q t) 29 50 ≤ (1 : ℝ) / 2 := by
  refine
    (powGeomRatio_le_powGeomRatio_of_le (k := 29) (N := 50) (q := q t)
        (q₀ := (1 : ℝ) / 535) ?_).trans ?_
  · exact q_le_one_div_535 (t := t) ht
  · norm_num [powGeomRatio]

private lemma powGeomRatio_r_27_100_le_half (t : ℝ) (ht : 1 ≤ t) :
    powGeomRatio (r t) 27 100 ≤ (1 : ℝ) / 2 := by
  refine
    (powGeomRatio_le_powGeomRatio_of_le (k := 27) (N := 100) (q := r t)
        (q₀ := (1 : ℝ) / 23) ?_).trans ?_
  · exact r_le_one_div_23 (t := t) ht
  · norm_num [powGeomRatio]

private lemma powGeomTerm_q_QN_eq (t : ℝ) (k : ℕ) :
    powGeomTerm (q t) k BleadingCoeffs.QN = (51 : ℝ) ^ k * (r t) ^ (100 : ℕ) := by
  simp [powGeomTerm, BleadingCoeffs.QN, q_pow_50_eq_r_pow_100 (t := t),
    show (50 + 1 : ℝ) = 51 by norm_num]

private lemma powGeomTerm_r_N_eq (t : ℝ) (k : ℕ) :
    powGeomTerm (r t) k BleadingCoeffs.N = (101 : ℝ) ^ k * (r t) ^ (100 : ℕ) := by
  simp [powGeomTerm, BleadingCoeffs.N, show (100 + 1 : ℝ) = 101 by norm_num]

private lemma qtail_le_Cvarphi_rpow100 (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t)
    (a : ℕ → ℚ) (ha : ∀ n : ℕ, |(a n : ℝ)| ≤ Cvarphi * (((n + 1 : ℕ) : ℝ) ^ (20 : ℕ))) :
    ‖∑' m : ℕ, (a (BleadingCoeffs.QN + m) : ℂ) * qterm (it t ht0) (BleadingCoeffs.QN + m)‖ ≤
      Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * (r t) ^ (100 : ℕ))) := by
  have htail0 :
      ‖∑' m : ℕ, (a (BleadingCoeffs.QN + m) : ℂ) * qterm (it t ht0) (BleadingCoeffs.QN + m)‖ ≤
        Cvarphi * (∑' m : ℕ, powGeomTerm (q t) 20 (BleadingCoeffs.QN + m)) :=
    norm_qseries_tail_le_of_coeffBound (t := t) (ht0 := ht0) (ht := ht)
      (a := a) (C := Cvarphi) (k := 20) (N := BleadingCoeffs.QN) ha
  have hsum :
      (∑' m : ℕ, powGeomTerm (q t) 20 (BleadingCoeffs.QN + m)) ≤
        2 * powGeomTerm (q t) 20 BleadingCoeffs.QN := by
    have hρ : powGeomRatio (q t) 20 BleadingCoeffs.QN ≤ (1 : ℝ) / 2 :=
      powGeomRatio_q_le_half_of_q_le_one_div_535 (q' := q t) (q_le_one_div_535 (t := t) ht)
    simpa using!
      (tsum_powGeomTerm_tail_le_two_mul (q := q t) (k := 20) (N := BleadingCoeffs.QN)
        (q_nonneg t) hρ)
  have hmain :
      Cvarphi * (∑' m : ℕ, powGeomTerm (q t) 20 (BleadingCoeffs.QN + m)) ≤
        Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * (r t) ^ (100 : ℕ))) := by
    have := mul_le_mul_of_nonneg_left hsum Cvarphi_nonneg
    simpa [powGeomTerm_q_QN_eq (t := t) (k := 20), mul_assoc, mul_left_comm, mul_comm] using! this
  exact htail0.trans hmain

/-- Tail bound for the `qseries` coefficients of `varphi_num`, starting at `QN = 50`. -/
public lemma qtail_varphi_le_Cvarphi_rpow100 (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    ‖qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) (it t ht0) BleadingCoeffs.QN‖ ≤
      Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * (r t) ^ (100 : ℕ))) := by
  simpa [qtail] using! qtail_le_Cvarphi_rpow100 (t := t) (ht0 := ht0) (ht := ht)
    (a := coeffVarphiNum) (ha := abs_coeffVarphiNum_le)

/-- Tail bound for the `qseries` coefficients `coeffPhi1Core`, starting at `QN = 50`. -/
public lemma qtail_phi1_le_Cvarphi_rpow100 (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    ‖qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) (it t ht0) BleadingCoeffs.QN‖ ≤
      Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * (r t) ^ (100 : ℕ))) := by
  simpa [qtail] using! qtail_le_Cvarphi_rpow100 (t := t) (ht0 := ht0) (ht := ht)
    (a := coeffPhi1Core) (ha := abs_coeffPhi1Core_le_Cvarphi)

/-- Tail bound for the `qseries` coefficients `coeffPhi2Core`, starting at `QN = 50`. -/
public lemma qtail_phi2_le_Cvarphi_rpow100 (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    ‖qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) (it t ht0) BleadingCoeffs.QN‖ ≤
      Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * (r t) ^ (100 : ℕ))) := by
  simpa [qtail] using! qtail_le_Cvarphi_rpow100 (t := t) (ht0 := ht0) (ht := ht)
    (a := coeffPhi2Core) (ha := abs_coeffPhi2Core_le_Cvarphi)

/--
Tail bound for the shifted `Δ^2` coefficients used in the remainder term,
starting at `QN = 50`. -/
public lemma qtail_deltaShift_le_Cdelta_rpow100 (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    ‖qtail (fun n : ℕ => (coeffDeltaSq (n + 1) : ℂ)) (it t ht0) BleadingCoeffs.QN‖ ≤
      (CdeltaSq * (2 : ℝ) ^ (29 : ℕ)) * (2 * ((51 : ℝ) ^ (29 : ℕ) * (r t) ^ (100 : ℕ))) := by
  set Cshift : ℝ := (CdeltaSq * (2 : ℝ) ^ (29 : ℕ))
  have hC0 : (0 : ℝ) ≤ Cshift := by
    dsimp [Cshift, CdeltaSq, Cdelta]
    positivity
  have ha : ∀ n : ℕ, |(coeffDeltaSq (n + 1) : ℝ)| ≤ Cshift * (((n + 1 : ℕ) : ℝ) ^ (29 : ℕ)) := by
    intro n
    simpa [Cshift, mul_assoc] using! (abs_coeffDeltaSq_shift_le (n := n))
  have htail0 :
      ‖qtail (fun n : ℕ => (coeffDeltaSq (n + 1) : ℂ)) (it t ht0) BleadingCoeffs.QN‖ ≤
        Cshift * (∑' m : ℕ, powGeomTerm (q t) 29 (BleadingCoeffs.QN + m)) := by
    -- Apply the generic `qseries` tail bound and rewrite into `qtail`.
    simpa [qtail, BleadingCoeffs.QN] using!
      (norm_qseries_tail_le_of_coeffBound (t := t) (ht0 := ht0) (ht := ht)
        (a := fun n : ℕ => coeffDeltaSq (n + 1))
        (C := Cshift) (k := 29) (N := BleadingCoeffs.QN) ha)
  have hsum :
      (∑' m : ℕ, powGeomTerm (q t) 29 (BleadingCoeffs.QN + m)) ≤
        2 * powGeomTerm (q t) 29 BleadingCoeffs.QN := by
    have hρ : powGeomRatio (q t) 29 BleadingCoeffs.QN ≤ (1 : ℝ) / 2 :=
      by simpa [BleadingCoeffs.QN] using! powGeomRatio_q_29_50_le_half (t := t) ht
    simpa using!
      (tsum_powGeomTerm_tail_le_two_mul (q := q t) (k := 29) (N := BleadingCoeffs.QN)
        (q_nonneg t) hρ)
  have hmain :
      Cshift * (∑' m : ℕ, powGeomTerm (q t) 29 (BleadingCoeffs.QN + m)) ≤
        Cshift * (2 * ((51 : ℝ) ^ (29 : ℕ) * (r t) ^ (100 : ℕ))) := by
    have := mul_le_mul_of_nonneg_left hsum hC0
    simpa [powGeomTerm_q_QN_eq (t := t) (k := 29), mul_assoc, mul_left_comm, mul_comm] using! this
  exact htail0.trans hmain

/-- Tail bound for the `rseries` of `psiCoeffFun`, starting at `N = 100`. -/
public lemma rtail_psi_le_rpow100 (t : ℝ) (ht0 : 0 < t) (ht : 1 ≤ t) :
    ‖rtail psiCoeffFun t BleadingCoeffs.N‖ ≤
      ((16 : ℝ) ^ (8 : ℕ)) * (2 * ((101 : ℝ) ^ (27 : ℕ) * (r t) ^ (100 : ℕ))) := by
  have htail0 :
      ‖rtail psiCoeffFun t BleadingCoeffs.N‖ ≤
        (16 : ℝ) ^ (8 : ℕ) * (∑' m : ℕ, powGeomTerm (r t) 27 (BleadingCoeffs.N + m)) := by
    simpa [rtail, Nat.add_assoc] using!
      (norm_rseries_tail_le_of_coeffBound (t := t) (ht0 := ht0)
        (a := psiCoeffFun) (C := (16 : ℝ) ^ (8 : ℕ)) (k := 27) (N := BleadingCoeffs.N)
        (fun n => abs_psiCoeffFun_le (n := n)))
  have hsum :
      (∑' m : ℕ, powGeomTerm (r t) 27 (BleadingCoeffs.N + m)) ≤
        2 * powGeomTerm (r t) 27 BleadingCoeffs.N := by
    have hρ : powGeomRatio (r t) 27 BleadingCoeffs.N ≤ (1 : ℝ) / 2 :=
      by simpa [BleadingCoeffs.N] using! powGeomRatio_r_27_100_le_half (t := t) ht
    simpa using!
      (tsum_powGeomTerm_tail_le_two_mul (q := r t) (k := 27) (N := BleadingCoeffs.N)
        (r_nonneg t) hρ)
  have hmain :
      (16 : ℝ) ^ (8 : ℕ) * (∑' m : ℕ, powGeomTerm (r t) 27 (BleadingCoeffs.N + m)) ≤
        ((16 : ℝ) ^ (8 : ℕ)) * (2 * ((101 : ℝ) ^ (27 : ℕ) * (r t) ^ (100 : ℕ))) := by
    have := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ (16 : ℝ) ^ (8 : ℕ))
    simpa [powGeomTerm_r_N_eq (t := t) (k := 27)] using! this
  exact htail0.trans hmain

/-!
### Certified constant comparisons against `eps`

We keep these as small standalone arithmetic lemmas (on `ℚ`) so that proofs only need simple
`exact_mod_cast` steps.
-/

/-- Arithmetic certificate comparing the `varphi` tail constant against `eps`. -/
public lemma const_varphi_scaled_lt :
    (80 : ℚ) * (513200655360 : ℚ) * (51 : ℚ) ^ (20 : ℕ) * ((1 : ℚ) / 23) ^ (88 : ℕ) <
      (28304640 : ℚ) * (10 : ℚ) ^ (-50 : ℤ) := by
  set_option maxRecDepth 6000 in
  norm_num

/-- Arithmetic certificate comparing the `phi1` tail constant against `eps`. -/
public lemma const_phi1_scaled_lt :
    (20 : ℚ) * (513200655360 : ℚ) * (51 : ℚ) ^ (20 : ℕ) * ((1 : ℚ) / 23) ^ (88 : ℕ) <
      (4717440 : ℚ) * (10 : ℚ) ^ (-50 : ℤ) := by
  set_option maxRecDepth 6000 in
  norm_num

/-- Arithmetic certificate comparing the `phi2` tail constant against `eps`. -/
public lemma const_phi2_scaled_lt :
    (720 : ℚ) * (513200655360 : ℚ) * (51 : ℚ) ^ (20 : ℕ) * ((1 : ℚ) / 23) ^ (88 : ℕ) <
      (28304640 : ℚ) * (10 : ℚ) ^ (-50 : ℤ) := by
  set_option maxRecDepth 6000 in
  norm_num

/-- Arithmetic certificate comparing the `psi` tail constant against `eps`. -/
public lemma const_psi_scaled_lt :
    (20 : ℚ) * ((16 : ℚ) ^ (8 : ℕ)) * (101 : ℚ) ^ (27 : ℕ) * ((1 : ℚ) / 23) ^ (88 : ℕ) <
      (65520 : ℚ) * (10 : ℚ) ^ (-50 : ℤ) := by
  set_option maxRecDepth 6000 in
  norm_num

/-- Arithmetic certificate comparing the `Δ^2` tail (t-scaling part) constant against `eps`. -/
public lemma const_delta_t_scaled_lt :
    (40 : ℚ) * (((1 / 1728 : ℚ) *
        (((240 * 240 : ℚ) * (240 : ℚ)) + (504 * 504 : ℚ))) *
        ((1 / 1728 : ℚ) *
          (((240 * 240 : ℚ) * (240 : ℚ)) + (504 * 504 : ℚ)))) *
        (2 : ℚ) ^ (29 : ℕ) * (51 : ℚ) ^ (29 : ℕ) * ((1 : ℚ) / 23) ^ (88 : ℕ) <
      (39 : ℚ) * (10 : ℚ) ^ (-50 : ℤ) := by
  set_option maxRecDepth 7000 in
  norm_num

/-- Arithmetic certificate comparing the `Δ^2` tail (constant part) constant against `eps`. -/
public lemma const_delta_c_scaled_lt :
    (400 : ℚ) * (((1 / 1728 : ℚ) *
        (((240 * 240 : ℚ) * (240 : ℚ)) + (504 * 504 : ℚ))) *
        ((1 / 1728 : ℚ) *
          (((240 * 240 : ℚ) * (240 : ℚ)) + (504 * 504 : ℚ)))) *
        (2 : ℚ) ^ (29 : ℕ) * (51 : ℚ) ^ (29 : ℕ) * ((1 : ℚ) / 23) ^ (88 : ℕ) <
      (117 : ℚ) * (10 : ℚ) ^ (-50 : ℤ) := by
  set_option maxRecDepth 7000 in
  norm_num

end SpherePacking.Dim24.AppendixA
