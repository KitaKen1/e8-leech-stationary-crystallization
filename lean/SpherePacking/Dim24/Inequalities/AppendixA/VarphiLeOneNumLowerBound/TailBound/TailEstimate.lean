-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import
  SpherePacking.Dim24.Inequalities.AppendixA.VarphiLeOneNumLowerBound.TailBound.NormRemainder
import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.BleadingNumDecomp
public import SpherePacking.Dim24.Inequalities.AppendixA.VarphiLeOneNumLowerBound.HeadIdentification


/-!
Tail estimate and final lower bound for the `t ≤ 1` case.
-/

open UpperHalfPlane

namespace SpherePacking.Dim24.AppendixA

noncomputable section

namespace VarphiLeOne

open BleadingCoeffs

/-- The tail estimate used in the `t ≤ 1` case: the exact truncation differs from the true
numerator real part by at most `eps * r(t)^12`. -/
public theorem exactTrunc_sub_eps_le_num_re (t : ℝ) (ht : 1 ≤ t) :
    let ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    exactTrunc t - eps * (r t) ^ (12 : ℕ)
      ≤
        (-((t : ℂ) ^ (2 : ℕ)) * varphi_num (it t ht0) - (t : ℂ) * phi1_num (it t ht0) +
              phi2_num (it t ht0)).re := by
  intro ht0
  -- Decompose each `qseries` into head + tail.
  have hsVarphi : Summable (fun n : ℕ => (coeffVarphiNum n : ℂ) * qterm (it t ht0) n) := by
    simpa using! (summable_coeffVarphiNum (t := t) (ht := ht))
  have hsPhi1 : Summable (fun n : ℕ => (coeffPhi1Core n : ℂ) * qterm (it t ht0) n) := by
    simpa using! (summable_coeffPhi1Core (t := t) (ht := ht))
  have hsPhi2 : Summable (fun n : ℕ => (coeffPhi2Core n : ℂ) * qterm (it t ht0) n) := by
    simpa using! (summable_coeffPhi2Core (t := t) (ht := ht))
  have hqVarphi :=
    qseries_eq_qhead_add_qtail (a := fun n : ℕ => (coeffVarphiNum n : ℂ)) (z := it t ht0)
      (N := BleadingCoeffs.QN) hsVarphi
  have hqPhi1 :=
    qseries_eq_qhead_add_qtail (a := fun n : ℕ => (coeffPhi1Core n : ℂ)) (z := it t ht0)
      (N := BleadingCoeffs.QN) hsPhi1
  have hqPhi2 :=
    qseries_eq_qhead_add_qtail (a := fun n : ℕ => (coeffPhi2Core n : ℂ)) (z := it t ht0)
      (N := BleadingCoeffs.QN) hsPhi2
  -- Rewrite the numerator in `qseries` form.
  have hvarphi := varphi_num_it_eq_qseries (t := t) (ht0 := ht0) ht
  have hphi1 := phi1_num_it_eq_qseries (t := t) (ht0 := ht0) ht
  have hphi2 := phi2_num_it_eq_qseries (t := t) (ht0 := ht0) ht
  -- Define the `qhead`-based head part and show it equals `exactTrunc`.
  have hhead_eq : headS t ht0 = (exactTrunc t : ℂ) := headS_eq_exactTrunc (t := t) ht0
  -- Replace coefficient-function heads by the list-based heads used in `headS`.
  have hqVarphiHead :
      qhead (fun n : ℕ => (coeffVarphiNum n : ℂ)) (it t ht0) BleadingCoeffs.QN =
        qhead (fun n : ℕ => (aA n : ℂ)) (it t ht0) BleadingCoeffs.QN :=
    qhead_coeffVarphiNum_eq (t := t) (ht0 := ht0)
  have hqPhi1Head :
      qhead (fun n : ℕ => (coeffPhi1Core n : ℂ)) (it t ht0) BleadingCoeffs.QN =
        qhead (fun n : ℕ => (aB n : ℂ)) (it t ht0) BleadingCoeffs.QN :=
    qhead_coeffPhi1Core_eq (t := t) (ht0 := ht0)
  have hqPhi2Head :
      qhead (fun n : ℕ => (coeffPhi2Core n : ℂ)) (it t ht0) BleadingCoeffs.QN =
        qhead (fun n : ℕ => (aC n : ℂ)) (it t ht0) BleadingCoeffs.QN :=
    qhead_coeffPhi2Core_eq (t := t) (ht0 := ht0)
  -- Assemble: numerator = head + tail, so numerator - exactTrunc = tail.
  have hEq :
      (-((t : ℂ) ^ (2 : ℕ)) * varphi_num (it t ht0) - (t : ℂ) * phi1_num (it t ht0) +
              phi2_num (it t ht0)) -
          (exactTrunc t : ℂ) =
        (-((t : ℂ) ^ (2 : ℕ))) *
            qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) (it t ht0) BleadingCoeffs.QN +
          (t : ℂ) * ((6 : ℂ) * (1 / (Real.pi : ℂ))) *
              qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) (it t ht0) BleadingCoeffs.QN +
            ((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
              qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) (it t ht0) BleadingCoeffs.QN := by
    -- Expand each numerator piece into `qhead + qtail`.
    have hvarphi' :
        varphi_num (it t ht0) =
          qhead (fun n : ℕ => (coeffVarphiNum n : ℂ)) (it t ht0) BleadingCoeffs.QN +
            qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) (it t ht0) BleadingCoeffs.QN := by
      simpa [hvarphi] using! hqVarphi
    have hphi1' :
        phi1_num (it t ht0) =
          ((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
              qhead (fun n : ℕ => (coeffPhi1Core n : ℂ)) (it t ht0) BleadingCoeffs.QN +
            ((1 / (Real.pi : ℂ)) * (-6 : ℂ)) *
              qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) (it t ht0) BleadingCoeffs.QN := by
      have := congrArg (fun w : ℂ => ((1 / (Real.pi : ℂ)) * (-6 : ℂ)) * w) hqPhi1
      simpa [hphi1, mul_add, mul_assoc] using! this
    have hphi2' :
        phi2_num (it t ht0) =
          ((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
              qhead (fun n : ℕ => (coeffPhi2Core n : ℂ)) (it t ht0) BleadingCoeffs.QN +
            ((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
              qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) (it t ht0) BleadingCoeffs.QN := by
      have := congrArg (fun w : ℂ => ((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) * w) hqPhi2
      simpa [hphi2, mul_add, mul_assoc] using! this
    calc
      (-((t : ℂ) ^ (2 : ℕ)) * varphi_num (it t ht0) - (t : ℂ) * phi1_num (it t ht0) +
              phi2_num (it t ht0)) -
          (exactTrunc t : ℂ)
          =
        (headS t ht0 +
          (-((t : ℂ) ^ (2 : ℕ))) *
              qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) (it t ht0) BleadingCoeffs.QN +
            (t : ℂ) * ((6 : ℂ) * (1 / (Real.pi : ℂ))) *
                qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) (it t ht0) BleadingCoeffs.QN +
              ((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
                qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) (it t ht0) BleadingCoeffs.QN) -
            (exactTrunc t : ℂ) := by
              simp [
                hvarphi',
                hphi1',
                hphi2',
                headS,
                hqVarphiHead,
                hqPhi1Head,
                hqPhi2Head,
                sub_eq_add_neg,
                mul_add,
                add_assoc,
                add_left_comm,
                add_comm,
                mul_assoc,
                mul_comm
              ]
      _ =
        (-((t : ℂ) ^ (2 : ℕ))) *
            qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) (it t ht0) BleadingCoeffs.QN +
          (t : ℂ) * ((6 : ℂ) * (1 / (Real.pi : ℂ))) *
              qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) (it t ht0) BleadingCoeffs.QN +
            ((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
              qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) (it t ht0) BleadingCoeffs.QN := by
              simp [hhead_eq, sub_eq_add_neg, add_left_comm, add_comm]
  have hnorm :
      ‖(-((t : ℂ) ^ (2 : ℕ)) * varphi_num (it t ht0) - (t : ℂ) * phi1_num (it t ht0) +
              phi2_num (it t ht0)) -
          (exactTrunc t : ℂ)‖ ≤
        eps * (r t) ^ (12 : ℕ) := by
    rw [hEq]
    simpa using! (norm_remainder_le (t := t) (ht := ht))
  set z : ℂ :=
    (-((t : ℂ) ^ (2 : ℕ)) * varphi_num (it t ht0) - (t : ℂ) * phi1_num (it t ht0) +
        phi2_num (it t ht0))
  have habs : |z.re - exactTrunc t| ≤ eps * (r t) ^ (12 : ℕ) := by
    have : |(z - (exactTrunc t : ℂ)).re| ≤ eps * (r t) ^ (12 : ℕ) :=
      (Complex.abs_re_le_norm (z - (exactTrunc t : ℂ))).trans hnorm
    simpa [z] using! this
  exact sub_le_of_abs_sub_le_left habs

/--
Final inequality for the `t ≤ 1` case: truncation polynomial minus tail bound is below the true
numerator real part.
-/
public theorem varphiNum_lower_bound_leOne (t : ℝ) (ht : 1 ≤ t) :
    let ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    ((-varphi_trunc_leOne).eval₂ (algebraMap ℚ ℝ) (r t)) - eps * (r t) ^ (12 : ℕ)
      ≤
        (-((t : ℂ) ^ (2 : ℕ)) * varphi_num (it t ht0) - (t : ℂ) * phi1_num (it t ht0) +
              phi2_num (it t ht0)).re := by
  intro ht0
  refine (sub_le_sub_right (trunc_eval₂_le_exactTrunc (t := t) ht) _).trans ?_
  simpa using! (exactTrunc_sub_eps_le_num_re (t := t) (ht := ht))


end VarphiLeOne

end

end SpherePacking.Dim24.AppendixA
