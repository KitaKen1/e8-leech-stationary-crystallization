/- Constant bounds used in the remainder estimate. -/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.TailBounds


/-!
### Certified constants, repackaged

`Part13E_TailBounds` supplies rational strict inequalities against `eps`. We repackage them as
weak `≤` inequalities on `ℝ`, in the exact shapes needed in the analytic remainder bound.
-/

noncomputable section

namespace SpherePacking.Dim24.AppendixA

private def Avarphi : ℝ :=
  (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ)

private def Apsi : ℝ :=
  ((16 : ℝ) ^ (8 : ℕ)) * (101 : ℝ) ^ (27 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ)

private def Adelta : ℝ :=
  (CdeltaSq : ℝ) * (2 : ℝ) ^ (29 : ℕ) * (51 : ℝ) ^ (29 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ)

private lemma Adelta_nonneg : 0 ≤ Adelta := by
  dsimp [Adelta, CdeltaSq, Cdelta]
  positivity

/-- Bound the `varphi` tail constant by `(28304640) * (eps / 10)`. -/
public lemma const_varphi_div10 :
    (8 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) ≤
      (28304640 : ℝ) * (eps / 10) := by
  have hQ :
      ((80 : ℚ) * (513200655360 : ℚ) * (51 : ℚ) ^ (20 : ℕ) * ((1 : ℚ) / 23) ^ (88 : ℕ) : ℝ) <
        ((28304640 : ℚ) * (10 : ℚ) ^ (-50 : ℤ) : ℝ) := by
    exact_mod_cast const_varphi_scaled_lt
  have h80 : (80 : ℝ) * Avarphi ≤ (28304640 : ℝ) * eps := by
    have : (80 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) ≤
        (28304640 : ℝ) * eps :=
      le_of_lt (by simpa [Cvarphi, eps] using! hQ)
    simpa [Avarphi, mul_assoc, mul_left_comm, mul_comm] using! this
  have h8 : (8 : ℝ) * Avarphi ≤ (28304640 : ℝ) * (eps / 10) := by nlinarith [h80]
  simpa [Avarphi, mul_assoc, mul_left_comm, mul_comm] using! h8

/-- Bound the `phi1` tail constant by `(4717440) * (eps / 10)`. -/
public lemma const_phi1_div10 :
    (2 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) ≤
      (4717440 : ℝ) * (eps / 10) := by
  have hQ :
      ((20 : ℚ) * (513200655360 : ℚ) * (51 : ℚ) ^ (20 : ℕ) * ((1 : ℚ) / 23) ^ (88 : ℕ) : ℝ) <
        ((4717440 : ℚ) * (10 : ℚ) ^ (-50 : ℤ) : ℝ) := by
    exact_mod_cast const_phi1_scaled_lt
  have h20 : (20 : ℝ) * Avarphi ≤ (4717440 : ℝ) * eps := by
    have : (20 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) ≤
        (4717440 : ℝ) * eps :=
      le_of_lt (by simpa [Cvarphi, eps] using! hQ)
    simpa [Avarphi, mul_assoc, mul_left_comm, mul_comm] using! this
  have h2 : (2 : ℝ) * Avarphi ≤ (4717440 : ℝ) * (eps / 10) := by nlinarith [h20]
  simpa [Avarphi, mul_assoc, mul_left_comm, mul_comm] using! h2

/-- Bound the `phi2` tail constant by `(28304640) * (eps / 10)`. -/
public lemma const_phi2_div10 :
    (72 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) ≤
      (28304640 : ℝ) * (eps / 10) := by
  have hQ :
      ((720 : ℚ) * (513200655360 : ℚ) * (51 : ℚ) ^ (20 : ℕ) * ((1 : ℚ) / 23) ^ (88 : ℕ) : ℝ) <
        ((28304640 : ℚ) * (10 : ℚ) ^ (-50 : ℤ) : ℝ) := by
    exact_mod_cast const_phi2_scaled_lt
  have h720 : (720 : ℝ) * Avarphi ≤ (28304640 : ℝ) * eps := by
    have : (720 : ℝ) * (Cvarphi : ℝ) * (51 : ℝ) ^ (20 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) ≤
        (28304640 : ℝ) * eps :=
      le_of_lt (by simpa [Cvarphi, eps] using! hQ)
    simpa [Avarphi, mul_assoc, mul_left_comm, mul_comm] using! this
  have h72 : (72 : ℝ) * Avarphi ≤ (28304640 : ℝ) * (eps / 10) := by nlinarith [h720]
  simpa [Avarphi, mul_assoc, mul_left_comm, mul_comm] using! h72

/-- Bound the `psiI` tail constant by `(65520) * (eps / 10)`. -/
public lemma const_psi_div10 :
    (2 : ℝ) * ((16 : ℝ) ^ (8 : ℕ)) * (101 : ℝ) ^ (27 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) ≤
      (65520 : ℝ) * (eps / 10) := by
  have hQ :
      ((20 : ℚ) * ((16 : ℚ) ^ (8 : ℕ)) * (101 : ℚ) ^ (27 : ℕ) * ((1 : ℚ) / 23) ^ (88 : ℕ) : ℝ) <
        ((65520 : ℚ) * (10 : ℚ) ^ (-50 : ℤ) : ℝ) := by
    exact_mod_cast const_psi_scaled_lt
  have h20 : (20 : ℝ) * Apsi ≤ (65520 : ℝ) * eps := by
    have :
        (20 : ℝ) * ((16 : ℝ) ^ (8 : ℕ)) * (101 : ℝ) ^ (27 : ℕ) * ((1 : ℝ) / 23) ^ (88 : ℕ) ≤
          (65520 : ℝ) * eps :=
      le_of_lt (by simpa [eps] using! hQ)
    simpa [Apsi, mul_assoc, mul_left_comm, mul_comm] using! this
  have h2 : (2 : ℝ) * Apsi ≤ (65520 : ℝ) * (eps / 10) := by nlinarith [h20]
  simpa [Apsi, mul_assoc, mul_left_comm, mul_comm] using! h2

/-- Bound the `Δ^2` tail constant in the `t`-term by `(39) * (eps / 20)`. -/
public lemma const_delta_t_div20 :
    (2 : ℝ) * (CdeltaSq : ℝ) * (2 : ℝ) ^ 29 * (51 : ℝ) ^ 29 * ((1 : ℝ) / 23) ^ 88 ≤
      (39 : ℝ) * (eps / 20) := by
  have hQ :
      ((40 : ℚ) *
            (((1 / 1728 : ℚ) * (((240 * 240 : ℚ) * (240 : ℚ)) + (504 * 504 : ℚ))) *
              ((1 / 1728 : ℚ) * (((240 * 240 : ℚ) * (240 : ℚ)) + (504 * 504 : ℚ)))) *
            (2 : ℚ) ^ (29 : ℕ) * (51 : ℚ) ^ (29 : ℕ) * ((1 : ℚ) / 23) ^ (88 : ℕ) : ℝ) <
        ((39 : ℚ) * (10 : ℚ) ^ (-50 : ℤ) : ℝ) := by
    exact_mod_cast const_delta_t_scaled_lt
  have h' :
      (40 : ℝ) * (CdeltaSq : ℝ) * (2 : ℝ) ^ 29 * (51 : ℝ) ^ 29 * ((1 : ℝ) / 23) ^ 88 <
        (39 : ℝ) * eps := by
    simpa [CdeltaSq, Cdelta, eps] using! hQ
  linarith

/-- Bound the `Δ^2` tail constant in the `1/pi`-term by `(117) * (eps / 20)`. -/
public lemma const_delta_c_div20 :
    (10 : ℝ) * (CdeltaSq : ℝ) * (2 : ℝ) ^ 29 * (51 : ℝ) ^ 29 * ((1 : ℝ) / 23) ^ 88 ≤
      (117 : ℝ) * (eps / 20) := by
  have hQ :
      ((400 : ℚ) *
            (((1 / 1728 : ℚ) * (((240 * 240 : ℚ) * (240 : ℚ)) + (504 * 504 : ℚ))) *
              ((1 / 1728 : ℚ) * (((240 * 240 : ℚ) * (240 : ℚ)) + (504 * 504 : ℚ)))) *
            (2 : ℚ) ^ (29 : ℕ) * (51 : ℚ) ^ (29 : ℕ) * ((1 : ℚ) / 23) ^ (88 : ℕ) : ℝ) <
        ((117 : ℚ) * (10 : ℚ) ^ (-50 : ℤ) : ℝ) := by
    exact_mod_cast const_delta_c_scaled_lt
  have h' :
      (400 : ℝ) * (CdeltaSq : ℝ) * (2 : ℝ) ^ 29 * (51 : ℝ) ^ 29 * ((1 : ℝ) / 23) ^ 88 <
        (117 : ℝ) * eps := by
    simpa [CdeltaSq, Cdelta, eps] using! hQ
  have h : (400 : ℝ) * Adelta ≤ (117 : ℝ) * eps := by
    simpa [Adelta, mul_assoc, mul_left_comm, mul_comm] using! (le_of_lt h')
  have : (10 : ℝ) * Adelta ≤ (117 : ℝ) * (eps / 20) := by
    nlinarith [h, Adelta_nonneg]
  simpa [Adelta, mul_assoc, mul_left_comm, mul_comm] using! this

end SpherePacking.Dim24.AppendixA
