import E8Leech.CKMRVKernelRoundedPhiNegative
import Mathlib.Tactic.FinCases

/-! Verified endpoint and logarithm data for a candidate below ut=1.
No numerator sign or kernel positivity is claimed in this module. -/

namespace E8Leech.Taylor

set_option maxHeartbeats 0
set_option maxRecDepth 32768

def roundedNegativeCandidateBox : Box :=
  ⟨(295729543 / 5000000000), (295915681 / 5000000000), (9230139 / 250000000), (184719 / 5000000),
    (8999 / 10000), (9001 / 10000), (10499 / 10000), (10501 / 10000),
    (392699 / 125000), (3141593 / 1000000), (69 / 100), (7 / 10)⟩

def roundedNegativeCandidate : KernelRectangleCandidate :=
  ⟨roundedNegativeCandidateBox, (295915681 / 5000000000), 2, 12, 4, 4, 4, 10⟩

set_option cbv.warning false
set_option cbv.maxSteps 2000000

theorem roundedNegativeCandidate_nome : NomeOK roundedNegativeCandidate.box roundedNegativeCandidate.M := by
  exact ⟨by norm_num [Box.Valid, roundedNegativeCandidate, roundedNegativeCandidateBox],
    by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem roundedNegativeCandidate_logarithms :
    LogarithmOK roundedNegativeCandidate.box roundedNegativeCandidate.M 2 12 4 := by
  have h : ∀ j : Fin 3,
      TM.absBound roundedNegativeCandidate.box
        ((generatorDD roundedNegativeCandidate.box roundedNegativeCandidate.M 2 (logarithmIndex j)).A.sub (TM.const 1)) < 1 ∧
      TM.absBound roundedNegativeCandidate.box
        ((generatorDD roundedNegativeCandidate.box roundedNegativeCandidate.M 2 (logarithmIndex j)).B.sub (TM.const 1)) < 1 ∧
      TM.absBound roundedNegativeCandidate.box
        (DD.logZ roundedNegativeCandidate.box 12 4
          (generatorDD roundedNegativeCandidate.box roundedNegativeCandidate.M 2 (logarithmIndex j))) < 1 := by
    intro j
    fin_cases j <;> decide_cbv
  exact ⟨fun j => (h j).1, fun j => (h j).2.1, fun j => (h j).2.2⟩

theorem roundedNegativeCandidate_endpoints : kernelPhiRectangleEndpointChecks roundedNegativeCandidate := by
  decide_cbv

theorem roundedNegativeCandidate_product : roundedNegativeCandidate.box.uhi * roundedNegativeCandidate.box.thi < 1 := by
  decide +kernel

theorem roundedNegativeCandidate_mem_axis {u t : ℝ}
    (hu : (roundedNegativeCandidate.box.ulo : ℝ) ≤ u ∧ u ≤ roundedNegativeCandidate.box.uhi)
    (ht : (roundedNegativeCandidate.box.tlo : ℝ) ≤ t ∧ t ≤ roundedNegativeCandidate.box.thi) :
    roundedNegativeCandidate.box.Mem (axisEnv u t) :=
  roundedNegativeCandidate_endpoints.mem_axis roundedNegativeCandidate_nome.valid hu ht

theorem roundedNegativeCandidate_regular_point :
    ((roundedNegativeCandidate.box.ulo : ℝ) ≤ 9 / 10 ∧ (9 / 10 : ℝ) ≤ roundedNegativeCandidate.box.uhi) ∧
    ((roundedNegativeCandidate.box.tlo : ℝ) ≤ 21 / 20 ∧ (21 / 20 : ℝ) ≤ roundedNegativeCandidate.box.thi) ∧
    (9 / 10 : ℝ) ≠ 21 / 20 ∧ (9 / 10 : ℝ) * (21 / 20) < 1 := by
  norm_num [roundedNegativeCandidate, roundedNegativeCandidateBox]

theorem roundedNegativeCandidate_denominator_neg {u t : ℝ}
    (hu : (roundedNegativeCandidate.box.ulo : ℝ) ≤ u ∧ u ≤ roundedNegativeCandidate.box.uhi)
    (ht : (roundedNegativeCandidate.box.tlo : ℝ) ≤ t ∧ t ≤ roundedNegativeCandidate.box.thi)
    (hut : u ≠ t) :
    axNu (axV u) (axW u) (axV t) (axW t) /
      (Real.exp (-Real.pi * t) - Real.exp (-Real.pi * u)) < 0 := by
  have hu0 : 0 < u := by
    have h : (0 : ℝ) < roundedNegativeCandidate.box.ulo := by
      exact_mod_cast roundedNegativeCandidate_nome.valid.2.2.1
    exact h.trans_le hu.1
  have ht0 : 0 < t := by
    have h : (0 : ℝ) < roundedNegativeCandidate.box.tlo := by
      exact_mod_cast roundedNegativeCandidate_nome.valid.2.2.2.1
    exact h.trans_le ht.1
  have hp : (roundedNegativeCandidate.box.uhi : ℝ) * roundedNegativeCandidate.box.thi < 1 := by
    exact_mod_cast roundedNegativeCandidate_product
  have hprod := (mul_le_mul hu.2 ht.2 ht0.le (hu0.le.trans hu.2)).trans_lt hp
  exact ckmrvAxisDividedDenominator_neg hu0 ht0 hut hprod

end E8Leech.Taylor
