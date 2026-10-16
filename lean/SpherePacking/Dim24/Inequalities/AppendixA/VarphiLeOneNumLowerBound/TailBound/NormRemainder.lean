-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.VarphiLeOneNumLowerBound.HeadIdentification
import SpherePacking.Dim24.Inequalities.AppendixA.VarphiLeOneNumLowerBound.TailBound.PowComparisons
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PhiCoeffBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.TailBounds


/-!
Norm bound for the remainder (tail) term in the `t ≤ 1` case.
-/

open UpperHalfPlane

namespace SpherePacking.Dim24.AppendixA

noncomputable section

namespace VarphiLeOne

open BleadingCoeffs

lemma const_tail_scaled_lt_eps :
    (86 : ℚ) * (513200655360 : ℚ) * (2 : ℚ) * (51 : ℚ) ^ (20 : ℕ) * ((1 : ℚ) / 23) ^ (88 : ℕ) <
      (10 : ℚ) ^ (-50 : ℤ) := by
  norm_num

/--
Norm bound for the combined tail terms in the `t ≤ 1` case.

This estimates the norm of the `qtail` contributions in
`-t^2 * varphi_num - t * phi1_num + phi2_num` by `eps * r(t)^12`.
-/
public lemma norm_remainder_le (t : ℝ) (ht : 1 ≤ t) :
    let ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
    let z : ℍ := it t ht0
    ‖(-((t : ℂ) ^ (2 : ℕ))) * qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN +
          (t : ℂ) * ((6 : ℂ) * (1 / (Real.pi : ℂ))) *
              qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN +
            ((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
              qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN‖
      ≤ eps * (r t) ^ (12 : ℕ) := by
  intro ht0 z
  set x : ℝ := r t
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hxle : x ≤ (1 / 23 : ℝ) := r_le_one_div_23 (t := t) ht
  have htxle : t * x ≤ (1 / 23 : ℝ) := t_mul_r_le_one_div_23 (t := t) ht
  have ht0' : 0 ≤ t := le_trans (by norm_num) ht
  have htx0 : 0 ≤ t * x := mul_nonneg ht0' hx0
  -- Bound `1/π` and `1/π^2` by `1`.
  have hinvPi_le_one : (1 / Real.pi) ≤ (1 : ℝ) := by
    have hpi1 : (1 : ℝ) < Real.pi := lt_trans (by norm_num) Real.pi_gt_three
    have hpos : 0 < Real.pi := Real.pi_pos
    have := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hpi1
    exact le_of_lt (by simpa using! this)
  have hinvPiSq_le_one : (1 / (Real.pi ^ 2)) ≤ (1 : ℝ) := by
    have hpi0 : 0 ≤ (1 / Real.pi) := by positivity [Real.pi_pos.le]
    have := pow_le_pow_left₀ hpi0 hinvPi_le_one 2
    -- `(1/pi)^2 = 1/pi^2`.
    simpa [pow_two, one_div, mul_assoc] using! this
  -- Tail bounds from `Part13E_TailBounds`.
  have htailVarphi :
      ‖qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN‖ ≤
        Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * x ^ (100 : ℕ))) := by
    simpa [x] using! qtail_varphi_le_Cvarphi_rpow100 (t := t) (ht0 := ht0) ht
  have htailPhi1 :
      ‖qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN‖ ≤
        Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * x ^ (100 : ℕ))) := by
    simpa [x] using! qtail_phi1_le_Cvarphi_rpow100 (t := t) (ht0 := ht0) ht
  have htailPhi2 :
      ‖qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN‖ ≤
        Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * x ^ (100 : ℕ))) := by
    simpa [x] using! qtail_phi2_le_Cvarphi_rpow100 (t := t) (ht0 := ht0) ht
  -- Convert `x^100` into `(1/23)^88 * x^12`.
  have hxpow100_le : x ^ (100 : ℕ) ≤ (1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ) :=
    pow100_le_one_div_23_pow88_mul_pow12 (x := x) hx0 hxle
  have htxpow100_le : t * x ^ (100 : ℕ) ≤ (1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ) :=
    t_mul_pow100_le_one_div_23_pow88_mul_pow12 (t := t) (x := x) hx0 hxle htxle htx0
  have ht2xpow100_le : t ^ (2 : ℕ) * x ^ (100 : ℕ) ≤ (1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ) :=
    t_sq_mul_pow100_le_one_div_23_pow88_mul_pow12 (t := t) (x := x) hx0 hxle htxle htx0
  -- Bound each scaled tail by `const * (1/23)^88 * x^12`.
  have h1 :
      ‖(-((t : ℂ) ^ (2 : ℕ))) * qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN‖ ≤
        Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * ((1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ)))) := by
    have ht2 : ‖(t : ℂ) ^ (2 : ℕ)‖ = t ^ (2 : ℕ) := by
      have ht1 : ‖(t : ℂ)‖ = t := by
        simp [Real.norm_of_nonneg ht0']
      simp
    have hmul :
        ‖(-((t : ℂ) ^ (2 : ℕ))) * qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN‖ =
          (t ^ (2 : ℕ)) * ‖qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN‖ := by
      simp [ht2]
    -- Apply the tail bound and the power comparison.
    have htail_scaled :
        t ^ (2 : ℕ) * ‖qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN‖ ≤
          t ^ (2 : ℕ) * (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * x ^ (100 : ℕ)))) := by
      have ht2n0 : 0 ≤ t ^ (2 : ℕ) := by positivity
      exact mul_le_mul_of_nonneg_left htailVarphi ht2n0
    have htx : t ^ (2 : ℕ) * x ^ (100 : ℕ) ≤ (1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ) := ht2xpow100_le
    have hK0 : 0 ≤ Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ))) := by
      dsimp [Cvarphi]
      positivity
    have htx' :
        (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ)))) * (t ^ (2 : ℕ) * x ^ (100 : ℕ)) ≤
          (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ)))) * ((1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ)) :=
      mul_le_mul_of_nonneg_left htx hK0
    linarith
  -- (For the remaining two terms we use the weaker bounds `t * x^100` and `x^100`.)
  have h2 :
      ‖(t : ℂ) * ((6 : ℂ) * (1 / (Real.pi : ℂ))) *
            qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN‖ ≤
        (6 : ℝ) *
          (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * ((1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ))))) := by
    have ht1 : ‖(t : ℂ)‖ = t := by
      simp [Real.norm_of_nonneg ht0']
    have hpi : ‖(1 / (Real.pi : ℂ))‖ = (1 / Real.pi) := by
      have hpi0 : 0 ≤ (1 / Real.pi) := by positivity [Real.pi_pos.le]
      calc
        ‖(1 / (Real.pi : ℂ))‖ = ‖((1 / Real.pi) : ℂ)‖ := by simp
        _ = ‖(1 / Real.pi)‖ := by simp
        _ = (1 / Real.pi) := by simpa using! (Real.norm_of_nonneg hpi0)
    have h6 : ‖(6 : ℂ)‖ = (6 : ℝ) := by norm_num
    have hmul :
        ‖(t : ℂ) * ((6 : ℂ) * (1 / (Real.pi : ℂ))) *
            qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN‖ ≤
          (t * 6) * ‖qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN‖ := by
      -- `‖a*b*c‖ = ‖a‖*‖b‖*‖c‖` and use `‖1/π‖ ≤ 1`.
      have hpi_le : ‖(1 / (Real.pi : ℂ))‖ ≤ (1 : ℝ) := by
        -- Avoid `simp` normalizing `1/π` to `|π|⁻¹`.
        rw [hpi]
        exact hinvPi_le_one
      calc
        ‖(t : ℂ) * ((6 : ℂ) * (1 / (Real.pi : ℂ))) *
              qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN‖
            =
            ‖(t : ℂ)‖ * (‖(6 : ℂ)‖ * ‖(1 / (Real.pi : ℂ))‖) *
              ‖qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN‖ := by
              simp [mul_assoc]
        _ ≤ ‖(t : ℂ)‖ * (‖(6 : ℂ)‖ * (1 : ℝ)) *
                ‖qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN‖ := by
                have htail0 :
                    0 ≤ ‖qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN‖ := by
                  positivity
                have h6n0 : 0 ≤ ‖(6 : ℂ)‖ := by positivity
                have ht0'' : 0 ≤ ‖(t : ℂ)‖ := by
                  -- `‖(t : ℂ)‖ = t` and `0 ≤ t`.
                  rw [ht1]
                  exact ht0'
                -- multiply `hpi_le` by the nonnegative factors
                have := mul_le_mul_of_nonneg_left hpi_le h6n0
                have := mul_le_mul_of_nonneg_left this ht0''
                have := mul_le_mul_of_nonneg_right this htail0
                simpa [mul_assoc] using! this
        _ = (t * 6) * ‖qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN‖ := by
                -- Pure reassociation after rewriting `‖t‖ = t` and `‖6‖ = 6`.
                -- Use `rw` (not `simp`) to avoid rewriting `‖t‖` into `|t|`.
                rw [ht1, h6]
                ring_nf
    -- Apply the tail bound and the power comparison.
    have htx : t * x ^ (100 : ℕ) ≤ (1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ) := htxpow100_le
    have hK0 : 0 ≤ Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ))) := by
      dsimp [Cvarphi]
      positivity
    have hmul_tail :
        (t * 6) * ‖qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN‖ ≤
          (6 : ℝ) *
            (Cvarphi *
              (2 * ((51 : ℝ) ^ (20 : ℕ) * ((1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ))))) := by
      -- First use the tail bound `‖tail‖ ≤ C * 2 * (51^20 * x^100)`.
      have htail' := mul_le_mul_of_nonneg_left htailPhi1 (by positivity : 0 ≤ (t * 6 : ℝ))
      -- Now replace `t* x^100` by the bound.
      have htx' : (t * 6) * (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * x ^ (100 : ℕ)))) ≤
          (6 : ℝ) *
            (Cvarphi *
              (2 * ((51 : ℝ) ^ (20 : ℕ) * ((1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ))))) := by
        -- Factor out the common nonnegative constant `6*Cvarphi*2*51^20`.
        have hK0' : 0 ≤ (6 : ℝ) * (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ)))) := by
          dsimp [Cvarphi]
          positivity
        have := mul_le_mul_of_nonneg_left htx hK0'
        -- Normalize.
        simpa [mul_assoc, mul_left_comm, mul_comm, left_distrib, right_distrib] using! this
      linarith
    exact le_trans hmul hmul_tail
  have h3 :
      ‖(((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
            qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN)‖ ≤
        (36 : ℝ) *
          (Cvarphi *
            (2 * ((51 : ℝ) ^ (20 : ℕ) * ((1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ))))) := by
    -- Bound `1/pi^2 ≤ 1` and apply the tail bound.
    have hpi2 : ‖(1 / ((Real.pi : ℂ) ^ (2 : ℕ)))‖ = (1 / (Real.pi ^ 2)) := by
      norm_num
    have h36 : ‖(-36 : ℂ)‖ = (36 : ℝ) := by norm_num
    have hmul :
        ‖((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
            qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN‖ ≤
          (36 : ℝ) * ‖qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN‖ := by
      have : ‖((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ)))‖ ≤ (36 : ℝ) := by
        -- `‖-36‖ * ‖1/pi^2‖ ≤ 36` since `1/pi^2 ≤ 1`.
        have hpi2le : (1 / (Real.pi ^ 2)) ≤ 1 := hinvPiSq_le_one
        have := mul_le_mul_of_nonneg_left hpi2le (by positivity : 0 ≤ (36 : ℝ))
        -- normalize
        simpa [norm_mul, h36, hpi2, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using! this
      -- Multiply by the tail norm.
      have htail0 :
          0 ≤ ‖qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN‖ := by
        positivity
      have := mul_le_mul_of_nonneg_right this htail0
      simpa [norm_mul, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using! this
    -- Apply the tail bound and the `x^100` comparison, then combine by transitivity.
    have htail36 :
        (36 : ℝ) * ‖qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN‖ ≤
          (36 : ℝ) * (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * x ^ (100 : ℕ)))) :=
      mul_le_mul_of_nonneg_left htailPhi2 (by positivity : 0 ≤ (36 : ℝ))
    have hscale :
        (36 : ℝ) * (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * x ^ (100 : ℕ)))) ≤
          (36 : ℝ) *
            (Cvarphi *
              (2 * ((51 : ℝ) ^ (20 : ℕ) * ((1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ))))) := by
      have hK0 : 0 ≤ (36 : ℝ) * (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ)))) := by
        dsimp [Cvarphi]
        positivity
      have h' :
          ((36 : ℝ) * (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ))))) * x ^ (100 : ℕ) ≤
            ((36 : ℝ) * (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ))))) *
              ((1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ)) :=
        mul_le_mul_of_nonneg_left hxpow100_le hK0
      convert (postTransparency := .instances) h' using 1 <;> ring_nf
    exact le_trans hmul (le_trans htail36 hscale)
  -- Combine the three bounds and absorb constants into `eps`.
  have hsum :
      ‖(-((t : ℂ) ^ (2 : ℕ))) * qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN +
          (t : ℂ) * ((6 : ℂ) * (1 / (Real.pi : ℂ))) *
              qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN +
            ((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
              qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN‖
        ≤
          (86 : ℝ) *
            (Cvarphi *
              (2 * ((51 : ℝ) ^ (20 : ℕ) * ((1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ))))) := by
    set B : ℝ :=
      Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * ((1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ))))
    have hB0 : 0 ≤ B := by
      dsimp [B]
      have hC : 0 ≤ Cvarphi := by
        dsimp [Cvarphi]
        positivity
      have hx12 : 0 ≤ x ^ (12 : ℕ) := pow_nonneg hx0 _
      have h51 : 0 ≤ (51 : ℝ) ^ (20 : ℕ) := by positivity
      have h23 : 0 ≤ (1 / 23 : ℝ) ^ (88 : ℕ) := by
        have : 0 ≤ (1 / 23 : ℝ) := by norm_num
        exact pow_nonneg this _
      have hrest : 0 ≤ 2 * ((51 : ℝ) ^ (20 : ℕ) * ((1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ))) := by
        have : 0 ≤ (51 : ℝ) ^ (20 : ℕ) * ((1 / 23 : ℝ) ^ (88 : ℕ) * x ^ (12 : ℕ)) :=
          mul_nonneg h51 (mul_nonneg h23 hx12)
        exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) this
      exact mul_nonneg hC hrest
    set a : ℂ :=
      (-((t : ℂ) ^ (2 : ℕ))) * qtail (fun n : ℕ => (coeffVarphiNum n : ℂ)) z BleadingCoeffs.QN
    set b : ℂ :=
      (t : ℂ) * ((6 : ℂ) * (1 / (Real.pi : ℂ))) *
        qtail (fun n : ℕ => (coeffPhi1Core n : ℂ)) z BleadingCoeffs.QN
    set c : ℂ :=
      ((-36 : ℂ) / ((Real.pi : ℂ) ^ (2 : ℕ))) *
        qtail (fun n : ℕ => (coeffPhi2Core n : ℂ)) z BleadingCoeffs.QN
    have htri : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
      norm_add₃_le
    -- Substitute the three bounds, regroup, and use `43 ≤ 86`.
    linarith
  -- Convert the constant inequality (over `ℚ`) and finish.
  have hconst :
      (86 : ℝ) *
          (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * ((1 / 23 : ℝ) ^ (88 : ℕ))))) ≤
        eps := by
    have hQ :
        ((86 : ℚ) *
              (513200655360 : ℚ) *
              (2 : ℚ) *
              (51 : ℚ) ^ (20 : ℕ) *
              ((1 : ℚ) / 23) ^ (88 : ℕ) : ℚ) <
          (10 : ℚ) ^ (-50 : ℤ) := const_tail_scaled_lt_eps
    have hR :
        ((86 : ℚ) *
              (513200655360 : ℚ) *
              (2 : ℚ) *
              (51 : ℚ) ^ (20 : ℕ) *
              ((1 : ℚ) / 23) ^ (88 : ℕ) : ℝ) <
          (10 : ℚ) ^ (-50 : ℤ) := by
      exact_mod_cast hQ
    -- Normalize the casted statement into the constant form we need.
    have :
        (86 : ℝ) *
            (Cvarphi * (2 * ((51 : ℝ) ^ (20 : ℕ) * ((1 / 23 : ℝ) ^ (88 : ℕ))))) <
          eps := by
      have hR' :
          (86 : ℝ) *
                (513200655360 : ℝ) *
                (2 : ℝ) *
                (51 : ℝ) ^ (20 : ℕ) *
                (1 / 23 : ℝ) ^ (88 : ℕ) <
              eps := by
        simpa [eps] using! hR
      -- Reassociate the LHS to match the goal.
      have hgoal :
          (86 : ℝ) *
                ((513200655360 : ℝ) *
                  (2 * ((51 : ℝ) ^ (20 : ℕ) * (1 / 23 : ℝ) ^ (88 : ℕ)))) <
              eps := by
        convert (postTransparency := .instances) hR' using 1
        ring_nf
      simpa [Cvarphi] using! hgoal
    exact le_of_lt this
  -- Multiply by the nonnegative factor `x^12`.
  have hx12 : 0 ≤ x ^ (12 : ℕ) := by positivity
  have := mul_le_mul_of_nonneg_right hconst hx12
  -- Normalize the RHS and conclude using `hsum`.
  linarith


end VarphiLeOne

end

end SpherePacking.Dim24.AppendixA
