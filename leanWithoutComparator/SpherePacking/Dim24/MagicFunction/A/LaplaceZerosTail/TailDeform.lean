-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import Mathlib.Data.Complex.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailBounds
public import SpherePacking.ForMathlib.CancelDenomsCompat

/-!
# Tail deformation for `I₂' + I₄' + I₆'`

Using the crude bounds from `TailBounds`, we justify a Cauchy-Goursat deformation of the
bottom-edge integrals `I₂'` and `I₄'` onto vertical rays when `u > 4`. The main outcome is a
factorization of `I₂' + I₄' + I₆'` as an integral of `Φ₅'` along the imaginary axis.

## Main statements
* `TailDeform.norm_cexp_pi_I_mul_u_mul`
* `TailDeform.integrable_imag_axis_Φ₅'`
* `TailDeform.I₂'_add_I₄'_add_I₆'_eq_imag_axis`
-/

open Complex Real MeasureTheory Filter intervalIntegral
open scoped UpperHalfPlane Interval Topology

namespace SpherePacking.Dim24

noncomputable section

open UpperHalfPlane MatrixGroups
open MagicFunction.Parametrisations
open RealIntegrals RealIntegrals.ComplexIntegrands

namespace LaplaceZerosTail

namespace TailDeform

open scoped UpperHalfPlane Interval Topology
open MeasureTheory Filter

/-- The norm of the exponential weight `cexp (π i u z)`, expressed in terms of `im z`. -/
public lemma norm_cexp_pi_I_mul_u_mul (u : ℝ) (z : ℂ) :
    ‖cexp (Real.pi * Complex.I * (u : ℂ) * z)‖ = Real.exp (-Real.pi * u * z.im) := by
  -- Use `‖exp w‖ = exp(Re w)` and compute the real part.
  have hre : ((Real.pi : ℂ) * Complex.I * (u : ℂ) * z).re = -Real.pi * u * z.im := by
    -- Pull out the real scalar `(π*u)` and use `re (I*z) = - im z`.
    simp
  simp [Complex.norm_exp, hre]

open Filter Asymptotics
open scoped Real

lemma im_coe_vadd_it (a t : ℝ) (ht : 0 < t) :
    ((a +ᵥ it t ht : ℍ) : ℂ).im = t := by
  simp [it, add_im]

lemma norm_coe_vadd_it_le (a t : ℝ) (ht : 0 < t) :
    ‖((a +ᵥ it t ht : ℍ) : ℂ)‖ ≤ ‖(a : ℂ)‖ + ‖((it t ht : ℍ) : ℂ)‖ := by
  have hcoe : ((a +ᵥ it t ht : ℍ) : ℂ) = (a : ℂ) + ((it t ht : ℍ) : ℂ) :=
    UpperHalfPlane.coe_vadd (x := a) (z := (it t ht : ℍ))
  simpa [hcoe] using! (norm_add_le (a : ℂ) ((it t ht : ℍ) : ℂ))

lemma norm_it (t : ℝ) (ht : 0 < t) : ‖((it t ht : ℍ) : ℂ)‖ = t := by
  -- `it t` is `I * t` and `‖I‖ = 1`.
  have : ((it t ht : ℍ) : ℂ) = (Complex.I : ℂ) * (t : ℂ) := by rfl
  simp [this, abs_of_pos ht]

@[simp] lemma im_it (t : ℝ) (ht : 0 < t) : (it t ht : ℍ).im = t := by
  -- `it t` is definitionally `I * t` (as a complex number).
  have : (((it t ht : ℍ) : ℂ).im) = t := by
    simp [it]
  simpa using! this

lemma norm_coe_vadd_it_le_add (a t : ℝ) (ht : 0 < t) :
    ‖((a +ᵥ it t ht : ℍ) : ℂ)‖ ≤ |a| + t := by
  have h := norm_coe_vadd_it_le (a := a) (t := t) ht
  have ha : ‖(a : ℂ)‖ = |a| := by simp
  have ht' : ‖((it t ht : ℍ) : ℂ)‖ = t := norm_it (t := t) ht
  simpa [ha, ht'] using! h

lemma norm_coe_vadd_it_le_succ (a t : ℝ) (ht : 0 < t) (ha : |a| ≤ 1) :
    ‖((a +ᵥ it t ht : ℍ) : ℂ)‖ ≤ t + 1 := by
  have h := norm_coe_vadd_it_le_add (a := a) (t := t) ht
  have : |a| + t ≤ t + 1 := by linarith
  exact le_trans h this

lemma pow_two_le_pow_two_of_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ (2 : ℕ) ≤ y ^ (2 : ℕ) := by
  -- Use monotonicity of multiplication on `ℝ`.
  simpa [pow_two] using! (mul_le_mul hxy hxy hx (le_trans hx hxy))

lemma poly_bound_of_norm_le (t : ℝ) (ht : 1 ≤ t) {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ t + 1) :
    r ^ (2 : ℕ) + r + 1 ≤ 4 * (t ^ (2 : ℕ) + t + 1) := by
  nlinarith

lemma tendsto_poly_mul_exp_neg_mul_atTop (b : ℝ) (hb : 0 < b) :
    Tendsto (fun t : ℝ => (t ^ (2 : ℕ) + t + 1) * Real.exp (-b * t)) atTop (𝓝 0) := by
  -- Split into three terms and use `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`.
  have h2 :
      Tendsto (fun t : ℝ => (t ^ (2 : ℕ)) * Real.exp (-b * t)) atTop (𝓝 0) := by
    -- Convert `t^2` to `t^(2:ℝ)` and apply the standard lemma.
    have h :=
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s := (2 : ℝ)) (b := b) hb)
    -- `t ^ (2:ℝ) = t ^ (2:ℕ)`.
    simpa [Real.rpow_natCast] using! h
  have h1 :
      Tendsto (fun t : ℝ => t * Real.exp (-b * t)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s := (1 : ℝ)) (b := b) hb)
    simpa using! h
  have h0 :
      Tendsto (fun t : ℝ => (1 : ℝ) * Real.exp (-b * t)) atTop (𝓝 0) := by
    have hbt : Tendsto (fun t : ℝ => b * t) atTop atTop :=
      Tendsto.const_mul_atTop hb tendsto_id
    simpa
  -- Put the three limits together.
  have hsum :
      Tendsto
          (fun t : ℝ =>
            (t ^ (2 : ℕ)) * Real.exp (-b * t) + t * Real.exp (-b * t) +
              (1 : ℝ) * Real.exp (-b * t)) atTop (𝓝 0) := by
    simpa [add_assoc] using! ((h2.add h1).add h0)
  -- Rewrite the target to match `hsum`.
  have hEq :
      ∀ t : ℝ,
        (t ^ (2 : ℕ) + t + 1) * Real.exp (-b * t) =
          (t ^ (2 : ℕ)) * Real.exp (-b * t) +
            t * Real.exp (-b * t) +
            (1 : ℝ) * Real.exp (-b * t) := by
    intro t
    ring
  exact (tendsto_congr hEq).mpr hsum

lemma eventually_poly_le_exp (b : ℝ) (hb : 0 < b) :
    ∀ᶠ t : ℝ in atTop, t ^ (2 : ℕ) + t + 1 ≤ Real.exp (b * t) := by
  have hT : Tendsto (fun t : ℝ => (t ^ (2 : ℕ) + t + 1) * Real.exp (-b * t)) atTop (𝓝 0) :=
    tendsto_poly_mul_exp_neg_mul_atTop (b := b) hb
  have hsmall : ∀ᶠ t : ℝ in atTop, ‖(t ^ (2 : ℕ) + t + 1) * Real.exp (-b * t)‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using!
      (hT.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num)))
  have hpos : ∀ᶠ t : ℝ in atTop, 0 ≤ (t ^ (2 : ℕ) + t + 1) * Real.exp (-b * t) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht0
    have hpoly : 0 ≤ t ^ (2 : ℕ) + t + 1 := by
      have : 0 ≤ t ^ (2 : ℕ) := pow_nonneg ht0 _
      linarith
    exact mul_nonneg hpoly (Real.exp_pos _).le
  filter_upwards [hsmall, hpos] with t ht1 ht0
  have ht1' : (t ^ (2 : ℕ) + t + 1) * Real.exp (-b * t) ≤ 1 := by
    have hnorm : ‖(t ^ (2 : ℕ) + t + 1) * Real.exp (-b * t)‖ ≤ 1 := le_of_lt ht1
    -- Since the product is nonnegative, we can drop the norm.
    calc
      (t ^ (2 : ℕ) + t + 1) * Real.exp (-b * t) =
          ‖(t ^ (2 : ℕ) + t + 1) * Real.exp (-b * t)‖ := by
            simpa using! (Real.norm_of_nonneg ht0).symm
      _ ≤ 1 := hnorm
  -- Multiply by `exp(b*t)` (positive) to clear the factor.
  have hExpPos : 0 < Real.exp (b * t) := Real.exp_pos _
  have :
      (t ^ (2 : ℕ) + t + 1) ≤ Real.exp (b * t) := by
    -- `a * exp(-b t) ≤ 1` implies `a ≤ exp(b t)`.
    -- Multiply by `exp (b*t)` and simplify `exp(b*t)*exp(-b*t)=1`.
    have hmul := (mul_le_mul_of_nonneg_right ht1' hExpPos.le)
    -- Simplify `exp(-b*t) * exp(b*t) = 1`.
    have hcancel : Real.exp (-(b * t)) * Real.exp (b * t) = 1 := by
      have hs : (-(b * t)) + (b * t) = 0 := by ring
      have hmul' : Real.exp (-(b * t)) * Real.exp (b * t) = Real.exp ((-(b * t)) + (b * t)) :=
        (Real.exp_add (-(b * t)) (b * t)).symm
      simpa [hs, Real.exp_zero] using! hmul'
    -- Now finish.
    -- Left side: `(poly * exp(-b*t)) * exp(b*t) = poly`.
    have hLeft :
        ((t ^ (2 : ℕ) + t + 1) * Real.exp (-(b * t))) * Real.exp (b * t) =
          (t ^ (2 : ℕ) + t + 1) := by
      calc
        ((t ^ (2 : ℕ) + t + 1) * Real.exp (-(b * t))) * Real.exp (b * t) =
            (t ^ (2 : ℕ) + t + 1) * (Real.exp (-(b * t)) * Real.exp (b * t)) := by
              simp [mul_assoc]
        _ = (t ^ (2 : ℕ) + t + 1) := by simp [hcancel]
    -- Rewrite `exp(-b*t)` to `exp (-(b*t))` in `hmul`.
    have hmul' :
        ((t ^ (2 : ℕ) + t + 1) * Real.exp (-(b * t))) * Real.exp (b * t) ≤
          (1 : ℝ) * Real.exp (b * t) := by
      simpa [neg_mul, mul_assoc] using! hmul
    simpa [hLeft, one_mul] using! hmul'
  exact this

lemma norm_pow_ten_varphi_S_le (K A : ℝ) (hK : 0 < K)
    (hbound :
      ∀ z : ℍ, A ≤ z.im →
        ‖((z : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • z)‖ ≤
          K * (‖(z : ℂ)‖ ^ (2 : ℕ) + ‖(z : ℂ)‖ + 1) * Real.exp (4 * Real.pi * z.im))
    (a t : ℝ) (ht : 0 < t) (ht1 : 1 ≤ t) (ha : |a| ≤ 1) (hA : A ≤ t) :
    ‖((a +ᵥ it t ht : ℍ) : ℂ) ^ (10 : ℕ) * varphi (ModularGroup.S • (a +ᵥ it t ht : ℍ))‖ ≤
      (4 * K) * (t ^ (2 : ℕ) + t + 1) * Real.exp (4 * Real.pi * t) := by
  have hzIm : (a +ᵥ it t ht : ℍ).im = t := by
    change (((a +ᵥ it t ht : ℍ) : ℂ).im) = t
    exact im_coe_vadd_it (a := a) (t := t) ht
  have hIm : A ≤ (a +ᵥ it t ht : ℍ).im := by simpa [hzIm] using! hA
  have h0 := hbound (z := (a +ᵥ it t ht : ℍ)) hIm
  have hnorm : ‖((a +ᵥ it t ht : ℍ) : ℂ)‖ ≤ t + 1 := by
    simpa using! (norm_coe_vadd_it_le_succ (a := a) (t := t) ht ha)
  have hpoly :
      ‖((a +ᵥ it t ht : ℍ) : ℂ)‖ ^ (2 : ℕ) + ‖((a +ᵥ it t ht : ℍ) : ℂ)‖ + 1 ≤
        4 * (t ^ (2 : ℕ) + t + 1) := by
    have hr0 : 0 ≤ ‖((a +ᵥ it t ht : ℍ) : ℂ)‖ := norm_nonneg _
    exact poly_bound_of_norm_le (t := t) ht1 hr0 hnorm
  -- Replace `z.im` by `t` and dominate the polynomial factor.
  calc
    ‖((a +ᵥ it t ht : ℍ) : ℂ) ^ (10 : ℕ) * varphi (ModularGroup.S • (a +ᵥ it t ht : ℍ))‖
        ≤ K * (‖((a +ᵥ it t ht : ℍ) : ℂ)‖ ^ (2 : ℕ) + ‖((a +ᵥ it t ht : ℍ) : ℂ)‖ + 1) *
              Real.exp (4 * Real.pi * (a +ᵥ it t ht : ℍ).im) := by
          simpa using! h0
    _ ≤ K * (4 * (t ^ (2 : ℕ) + t + 1)) * Real.exp (4 * Real.pi * t) := by
          have hexp :
              Real.exp (4 * Real.pi * (a +ᵥ it t ht : ℍ).im) = Real.exp (4 * Real.pi * t) := by
            simp [hzIm]
          -- First enlarge the polynomial factor, then rewrite the exponential factor using `hexp`.
          have hpoly' :
              K *
                    (‖((a +ᵥ it t ht : ℍ) : ℂ)‖ ^ (2 : ℕ) + ‖((a +ᵥ it t ht : ℍ) : ℂ)‖ + 1) ≤
                  K * (4 * (t ^ (2 : ℕ) + t + 1)) := by
            exact mul_le_mul_of_nonneg_left hpoly (le_of_lt hK)
          have :=
            mul_le_mul_of_nonneg_right hpoly'
              (Real.exp_pos (4 * Real.pi * (a +ᵥ it t ht : ℍ).im)).le
          -- Reassociate to match the goal.
          simpa [mul_assoc, hexp] using! this
    _ = (4 * K) * (t ^ (2 : ℕ) + t + 1) * Real.exp (4 * Real.pi * t) := by
          ring

lemma norm_Φ₂'_vadd_it_le (u a : ℝ) (ha : |a + 1| ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t' : ℝ in atTop,
      ‖Φ₂' u (((a : ℂ) + (t' : ℂ) * Complex.I))‖ ≤
        C * (t' ^ (2 : ℕ) + t' + 1) * Real.exp (-Real.pi * (u - 4) * t') := by
  rcases TailBounds.exists_bound_norm_pow_ten_varphi_S with ⟨K, A, hK, hbound⟩
  refine ⟨4 * K, by nlinarith [hK], ?_⟩
  filter_upwards [eventually_ge_atTop (max A 1)] with t' ht'
  have htpos : 0 < t' := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) ht')
  set z : ℍ := a +ᵥ it t' htpos
  have hz : (z : ℂ) = (a : ℂ) + (t' : ℂ) * Complex.I := by
    -- `↑(a +ᵥ it t') = a + I*t'`.
    simp [z, it, mul_comm]
  have hterm := (Φ₂'_term_eq (u := u) (z := z))
  -- `Φ₂'(z)` uses `w := 1+ᵥ z`.
  set w : ℍ := (1 : ℝ) +ᵥ z
  have hwim : w.im = t' := by
    have hw : w = (a + 1) +ᵥ it t' htpos := by
      ext; simp [w, z, add_assoc, add_left_comm]
    change ((w : ℂ).im) = t'
    rw [hw]
    exact im_coe_vadd_it (a := a + 1) (t := t') htpos
  have hA' : A ≤ t' := le_trans (le_max_left _ _) ht'
  have ht1 : 1 ≤ t' := le_trans (le_max_right _ _) ht'
  have ha' : |(a + 1)| ≤ 1 := ha
  have hwbound :
      ‖((w : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • w)‖ ≤
        (4 * K) * (t' ^ (2 : ℕ) + t' + 1) * Real.exp (4 * Real.pi * t') := by
    -- `w = (a+1) +ᵥ it t'`.
    have hw : w = (a + 1) +ᵥ it t' htpos := by
      ext; simp [w, z, add_assoc, add_left_comm]
    simpa [hw] using!
      (norm_pow_ten_varphi_S_le (K := K) (A := A) hK hbound
        (a := a + 1) (t := t') htpos ht1 ha' hA')
  have hexp :
      ‖cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ))‖ = Real.exp (-Real.pi * u * t') := by
    -- `Im(z) = t'`.
    have hzIm : (z : ℂ).im = t' := by
      simp [z, it]
    have h := norm_cexp_pi_I_mul_u_mul (u := u) (z := (z : ℂ))
    -- Rewrite the imaginary part explicitly.
    rw [hzIm] at h
    simpa using! h
  -- Combine the bounds.
  -- `exp(4π t) * exp(-π u t) = exp(-π (u-4) t)`.
  have hExp :
      Real.exp (4 * Real.pi * t') * Real.exp (-Real.pi * u * t') =
        Real.exp (-Real.pi * (u - 4) * t') := by
    have : (4 * Real.pi * t') + (-(Real.pi * u * t')) = -(Real.pi * (u - 4) * t') := by ring
    calc
      Real.exp (4 * Real.pi * t') * Real.exp (-Real.pi * u * t') =
          Real.exp ((4 * Real.pi * t') + (-(Real.pi * u * t'))) := by
            simp [Real.exp_add, neg_mul, mul_assoc]
      _ = Real.exp (-(Real.pi * (u - 4) * t')) := by simp [this]
      _ = Real.exp (-Real.pi * (u - 4) * t') := by simp [mul_assoc, neg_mul]
  -- Use `hterm` to rewrite `Φ₂'` and take norms.
  have hEq : Φ₂' u (z : ℂ) = ((w : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • w) *
        cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ)) := by
    -- `hterm` has the LHS in this exact order.
    simpa [w] using! hterm.symm
  -- Finally, translate from `z` to the concrete complex point `a + it'`.
  calc
    ‖Φ₂' u ((a : ℂ) + (t' : ℂ) * Complex.I)‖ = ‖Φ₂' u (z : ℂ)‖ := by simp [hz]
    _ = ‖((w : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • w) *
          cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ))‖ := by simp [hEq]
    _ = ‖((w : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • w)‖ *
          ‖cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ))‖ := by
          simp [mul_assoc]
    _ ≤ ((4 * K) * (t' ^ (2 : ℕ) + t' + 1) * Real.exp (4 * Real.pi * t')) *
          Real.exp (-Real.pi * u * t') := by
          -- Bound the two factors separately.
          have hE :
              ‖cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ))‖ ≤
                Real.exp (-Real.pi * u * t') :=
            le_of_eq hexp
          have hA : ‖((w : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • w)‖ ≤
              (4 * K) * (t' ^ (2 : ℕ) + t' + 1) * Real.exp (4 * Real.pi * t') := hwbound
          exact mul_le_mul hA hE (by positivity) (by positivity)
    _ = (4 * K) * (t' ^ (2 : ℕ) + t' + 1) * Real.exp (-Real.pi * (u - 4) * t') := by
          -- reassociate and use `hExp`.
          have :
              ((4 * K) * (t' ^ (2 : ℕ) + t' + 1) * Real.exp (4 * Real.pi * t')) *
                  Real.exp (-Real.pi * u * t') =
                (4 * K) * (t' ^ (2 : ℕ) + t' + 1) *
                  (Real.exp (4 * Real.pi * t') * Real.exp (-Real.pi * u * t')) := by
            simp [mul_assoc]
          exact Eq.symm (CancelDenoms.derive_trans (id (Eq.symm hExp)) (id (Eq.symm this)))

lemma norm_Φ₄'_vadd_it_le (u a : ℝ) (ha : |a - 1| ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t' : ℝ in atTop,
      ‖Φ₄' u (((a : ℂ) + (t' : ℂ) * Complex.I))‖ ≤
        C * (t' ^ (2 : ℕ) + t' + 1) * Real.exp (-Real.pi * (u - 4) * t') := by
  rcases TailBounds.exists_bound_norm_pow_ten_varphi_S with ⟨K, A, hK, hbound⟩
  refine ⟨4 * K, by nlinarith [hK], ?_⟩
  filter_upwards [eventually_ge_atTop (max A 1)] with t' ht'
  have htpos : 0 < t' := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) ht')
  set z : ℍ := a +ᵥ it t' htpos
  have hz : (z : ℂ) = (a : ℂ) + (t' : ℂ) * Complex.I := by
    simp [z, it, mul_comm]
  have hterm := (Φ₄'_term_eq (u := u) (z := z))
  -- `Φ₄'(z)` uses `w := (-1)+ᵥ z`.
  set w : ℍ := (-1 : ℝ) +ᵥ z
  have hA' : A ≤ t' := le_trans (le_max_left _ _) ht'
  have ht1 : 1 ≤ t' := le_trans (le_max_right _ _) ht'
  have ha' : |(a - 1)| ≤ 1 := ha
  have hwbound :
      ‖((w : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • w)‖ ≤
        (4 * K) * (t' ^ (2 : ℕ) + t' + 1) * Real.exp (4 * Real.pi * t') := by
    -- `w = (a-1) +ᵥ it t'`.
    have hw : w = (a - 1) +ᵥ it t' htpos := by
      ext; simp [w, z, sub_eq_add_neg, add_assoc, add_left_comm]
    simpa [hw] using!
      (norm_pow_ten_varphi_S_le (K := K) (A := A) hK hbound
        (a := a - 1) (t := t') htpos ht1 ha' hA')
  have hexp :
      ‖cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ))‖ = Real.exp (-Real.pi * u * t') := by
    have hzIm : (z : ℂ).im = t' := by
      simp [z, it]
    have h := norm_cexp_pi_I_mul_u_mul (u := u) (z := (z : ℂ))
    rw [hzIm] at h
    simpa using! h
  have hExp :
      Real.exp (4 * Real.pi * t') * Real.exp (-Real.pi * u * t') =
        Real.exp (-Real.pi * (u - 4) * t') := by
    have : (4 * Real.pi * t') + (-(Real.pi * u * t')) = -(Real.pi * (u - 4) * t') := by ring
    calc
      Real.exp (4 * Real.pi * t') * Real.exp (-Real.pi * u * t') =
          Real.exp ((4 * Real.pi * t') + (-(Real.pi * u * t'))) := by
            simp [Real.exp_add, neg_mul, mul_assoc]
      _ = Real.exp (-(Real.pi * (u - 4) * t')) := by simp [this]
      _ = Real.exp (-Real.pi * (u - 4) * t') := by simp [mul_assoc, neg_mul]
  have hEq : Φ₄' u (z : ℂ) = ((w : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • w) *
        cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ)) := by
    simpa [w] using! hterm.symm
  calc
    ‖Φ₄' u ((a : ℂ) + (t' : ℂ) * Complex.I)‖ = ‖Φ₄' u (z : ℂ)‖ := by simp [hz]
    _ = ‖((w : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • w) *
          cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ))‖ := by simp [hEq]
    _ = ‖((w : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • w)‖ *
          ‖cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ))‖ := by
          simp [mul_assoc]
    _ ≤ ((4 * K) * (t' ^ (2 : ℕ) + t' + 1) * Real.exp (4 * Real.pi * t')) *
          Real.exp (-Real.pi * u * t') := by
          have hE :
              ‖cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ))‖ ≤
                Real.exp (-Real.pi * u * t') := by
            exact le_of_eq hexp
          have hA : ‖((w : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • w)‖ ≤
              (4 * K) * (t' ^ (2 : ℕ) + t' + 1) * Real.exp (4 * Real.pi * t') := hwbound
          exact mul_le_mul hA hE (by positivity) (by positivity)
    _ = (4 * K) * (t' ^ (2 : ℕ) + t' + 1) * Real.exp (-Real.pi * (u - 4) * t') := by
          have :
              ((4 * K) * (t' ^ (2 : ℕ) + t' + 1) * Real.exp (4 * Real.pi * t')) *
                  Real.exp (-Real.pi * u * t') =
                (4 * K) * (t' ^ (2 : ℕ) + t' + 1) *
                  (Real.exp (4 * Real.pi * t') * Real.exp (-Real.pi * u * t')) := by
            simp [mul_assoc]
          exact Eq.symm (CancelDenoms.derive_trans (id (Eq.symm hExp)) (id (Eq.symm this)))

/-!
### Deformation prerequisites (`u > 4`)

We prepare continuity, differentiability, and integrability statements needed to apply the
finite-rectangle deformation lemma `rect_deform_of_tendsto_top`.
-/

open scoped Interval
open MeasureTheory Filter Asymptotics Set intervalIntegral

lemma differentiableOn_Φ₂' (u : ℝ) :
    DifferentiableOn ℂ (Φ₂' u) upperHalfPlaneSet := by
  intro z hz
  exact (differentiableAt_Φ₂' (u := u) (z := z) hz).differentiableWithinAt

lemma continuousOn_Φ₂' (u : ℝ) :
    ContinuousOn (Φ₂' u) upperHalfPlaneSet :=
  (differentiableOn_Φ₂' (u := u)).continuousOn

lemma differentiableOn_Φ₄' (u : ℝ) :
    DifferentiableOn ℂ (Φ₄' u) upperHalfPlaneSet := by
  intro z hz
  exact (differentiableAt_Φ₄' (u := u) (z := z) hz).differentiableWithinAt

lemma continuousOn_Φ₄' (u : ℝ) :
    ContinuousOn (Φ₄' u) upperHalfPlaneSet :=
  (differentiableOn_Φ₄' (u := u)).continuousOn

lemma im_real_add_mul_I (x t : ℝ) : ((x : ℂ) + (t : ℂ) * Complex.I).im = t := by
  -- This is `Complex.im_of_real_add_real_mul_I`.
  exact Complex.im_of_real_add_real_mul_I x t

lemma mapsTo_real_add_mul_I_upper (x : ℝ) :
    MapsTo (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) (Set.Ici (1 : ℝ)) upperHalfPlaneSet := by
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  simpa

lemma continuousOn_real_add_mul_I (x : ℝ) :
    ContinuousOn (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) (Set.Ici (1 : ℝ)) := by
  -- A polynomial map in `t`.
  fun_prop

lemma continuousOn_vertical_Φ₂' (u x : ℝ) :
    ContinuousOn (fun t : ℝ => Φ₂' u ((x : ℂ) + (t : ℂ) * Complex.I)) (Set.Ici (1 : ℝ)) := by
  have hcomp :=
    (continuousOn_Φ₂' (u := u)).comp (continuousOn_real_add_mul_I (x := x))
      (mapsTo_real_add_mul_I_upper (x := x))
  simpa [Function.comp] using! hcomp

lemma continuousOn_vertical_Φ₄' (u x : ℝ) :
    ContinuousOn (fun t : ℝ => Φ₄' u ((x : ℂ) + (t : ℂ) * Complex.I)) (Set.Ici (1 : ℝ)) := by
  have hcomp :=
    (continuousOn_Φ₄' (u := u)).comp (continuousOn_real_add_mul_I (x := x))
      (mapsTo_real_add_mul_I_upper (x := x))
  simpa [Function.comp] using! hcomp

lemma integrableOn_vertical_Φ₂' (u x : ℝ) (hu : 4 < u) (hx : |x + 1| ≤ 1) :
    IntegrableOn (fun t : ℝ => Φ₂' u ((x : ℂ) + (t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) volume := by
  -- We first show the norm is integrable, using exponential decay.
  rcases norm_Φ₂'_vadd_it_le (u := u) (a := x) hx with ⟨C, hCpos, hCbound⟩
  set b : ℝ := Real.pi * (u - 4) / 2
  have hb : 0 < b := by
    have hu4 : 0 < u - 4 := sub_pos.2 hu
    have hnum : 0 < Real.pi * (u - 4) := mul_pos Real.pi_pos hu4
    have : 0 < Real.pi * (u - 4) / 2 := div_pos hnum (by norm_num)
    simpa [b] using! this
  have hpoly : ∀ᶠ t : ℝ in atTop, t ^ (2 : ℕ) + t + 1 ≤ Real.exp (b * t) :=
    eventually_poly_le_exp (b := b) hb
  have hdecay : ∀ᶠ t : ℝ in atTop,
      ‖Φ₂' u ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * Real.exp (-b * t) := by
    filter_upwards [hCbound, hpoly] with t ht hpoly
    have hb2 : Real.pi * (u - 4) = 2 * b := by
      dsimp [b]
      ring_nf
    -- Combine `poly ≤ exp(b*t)` with `exp(-(π(u-4))t) = exp(-(2b)t)`.
    have hpoly' :
        (t ^ (2 : ℕ) + t + 1) * Real.exp (-Real.pi * (u - 4) * t) ≤ Real.exp (-b * t) := by
      have hmul1 :
          (t ^ (2 : ℕ) + t + 1) * Real.exp (-Real.pi * (u - 4) * t) ≤
            Real.exp (b * t) * Real.exp (-Real.pi * (u - 4) * t) := by
        have := mul_le_mul_of_nonneg_right hpoly (Real.exp_pos (-Real.pi * (u - 4) * t)).le
        simpa [mul_assoc, mul_left_comm, mul_comm] using! this
      have hmul2 :
          Real.exp (b * t) * Real.exp (-Real.pi * (u - 4) * t) = Real.exp (-b * t) := by
        have hb2t : Real.pi * (u - 4) * t = 2 * b * t := by
          simpa [mul_assoc] using! congrArg (fun s : ℝ => s * t) hb2
        have hsum : (b * t) + (-Real.pi * (u - 4) * t) = -(b * t) := by
          -- Replace `π (u-4) * t` with `2 * b * t`, then simplify.
          ring
        have hnegMul : -(b * t) = -b * t := by
          -- `-(b*t) = (-b)*t`.
          exact (neg_mul b t).symm
        calc
          Real.exp (b * t) * Real.exp (-Real.pi * (u - 4) * t) =
              Real.exp ((b * t) + (-Real.pi * (u - 4) * t)) := by
                simp [Real.exp_add]
          _ = Real.exp (-(b * t)) := by rw [hsum]
          _ = Real.exp (-b * t) := by rw [hnegMul]
      exact (hmul1.trans_eq hmul2)
    nlinarith
  have hBigO :
      (fun t : ℝ => ‖Φ₂' u ((x : ℂ) + (t : ℂ) * Complex.I)‖) =O[atTop]
        fun t : ℝ => Real.exp (-b * t) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨C, ?_⟩
    filter_upwards [hdecay] with t ht
    simpa using! ht
  have hcontNorm :
      ContinuousOn (fun t : ℝ => ‖Φ₂' u ((x : ℂ) + (t : ℂ) * Complex.I)‖) (Set.Ici (1 : ℝ)) :=
    (continuousOn_vertical_Φ₂' (u := u) (x := x)).norm
  have hIntNorm :
      IntegrableOn
        (fun t : ℝ => ‖Φ₂' u ((x : ℂ) + (t : ℂ) * Complex.I)‖)
        (Set.Ioi (1 : ℝ)) volume :=
    integrable_of_isBigO_exp_neg (a := (1 : ℝ)) (b := b) hb hcontNorm (by simpa using! hBigO)
  -- Now upgrade from integrability of the norm to integrability of the complex-valued function.
  let μ : Measure ℝ := volume.restrict (Set.Ioi (1 : ℝ))
  have hmeas :
      AEStronglyMeasurable (fun t : ℝ => Φ₂' u ((x : ℂ) + (t : ℂ) * Complex.I)) μ := by
    have hcontIoi :
        ContinuousOn (fun t : ℝ => Φ₂' u ((x : ℂ) + (t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) :=
      (continuousOn_vertical_Φ₂' (u := u) (x := x)).mono (Set.Ioi_subset_Ici_self)
    exact hcontIoi.aestronglyMeasurable measurableSet_Ioi
  have hfiNorm :
      MeasureTheory.HasFiniteIntegral
        (fun t : ℝ => ‖Φ₂' u ((x : ℂ) + (t : ℂ) * Complex.I)‖) μ := by
    have hIntNormμ :
        Integrable (fun t : ℝ => ‖Φ₂' u ((x : ℂ) + (t : ℂ) * Complex.I)‖) μ := by
      simpa [MeasureTheory.IntegrableOn, μ] using! hIntNorm
    exact hIntNormμ.hasFiniteIntegral
  have hfi :
      MeasureTheory.HasFiniteIntegral (fun t : ℝ => Φ₂' u ((x : ℂ) + (t : ℂ) * Complex.I)) μ :=
    (MeasureTheory.hasFiniteIntegral_iff_norm (f := fun t : ℝ =>
        Φ₂' u ((x : ℂ) + (t : ℂ) * Complex.I)) (μ := μ)).2 <|
      (by
        -- Reduce to the finite integral of the norm, which follows from `hfiNorm`.
        exact IntegrableOn.setLIntegral_lt_top hIntNorm)
  exact ⟨hmeas, hfi⟩

lemma integrableOn_vertical_Φ₄' (u x : ℝ) (hu : 4 < u) (hx : |x - 1| ≤ 1) :
    IntegrableOn (fun t : ℝ => Φ₄' u ((x : ℂ) + (t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) volume := by
  -- Same proof as `integrableOn_vertical_Φ₂'`, using the crude bound for `Φ₄'`.
  rcases norm_Φ₄'_vadd_it_le (u := u) (a := x) hx with ⟨C, hCpos, hCbound⟩
  set b : ℝ := Real.pi * (u - 4) / 2
  have hb : 0 < b := by
    have hu4 : 0 < u - 4 := sub_pos.2 hu
    have hnum : 0 < Real.pi * (u - 4) := mul_pos Real.pi_pos hu4
    have : 0 < Real.pi * (u - 4) / 2 := div_pos hnum (by norm_num)
    simpa [b] using! this
  have hpoly : ∀ᶠ t : ℝ in atTop, t ^ (2 : ℕ) + t + 1 ≤ Real.exp (b * t) :=
    eventually_poly_le_exp (b := b) hb
  have hdecay : ∀ᶠ t : ℝ in atTop,
      ‖Φ₄' u ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * Real.exp (-b * t) := by
    filter_upwards [hCbound, hpoly] with t ht hpoly
    have hb2 : Real.pi * (u - 4) = 2 * b := by
      dsimp [b]
      ring_nf
    have hpoly' :
        (t ^ (2 : ℕ) + t + 1) * Real.exp (-Real.pi * (u - 4) * t) ≤ Real.exp (-b * t) := by
      have hmul1 :
          (t ^ (2 : ℕ) + t + 1) * Real.exp (-Real.pi * (u - 4) * t) ≤
            Real.exp (b * t) * Real.exp (-Real.pi * (u - 4) * t) := by
        have := mul_le_mul_of_nonneg_right hpoly (Real.exp_pos (-Real.pi * (u - 4) * t)).le
        simpa [mul_assoc, mul_left_comm, mul_comm] using! this
      have hmul2 :
          Real.exp (b * t) * Real.exp (-Real.pi * (u - 4) * t) = Real.exp (-b * t) := by
        have hb2t : Real.pi * (u - 4) * t = 2 * b * t := by
          simpa [mul_assoc] using! congrArg (fun s : ℝ => s * t) hb2
        have hsum : (b * t) + (-Real.pi * (u - 4) * t) = -(b * t) := by
          ring
        have hnegMul : -(b * t) = -b * t :=
          (neg_mul b t).symm
        calc
          Real.exp (b * t) * Real.exp (-Real.pi * (u - 4) * t) =
              Real.exp ((b * t) + (-Real.pi * (u - 4) * t)) := by
                simp [Real.exp_add]
          _ = Real.exp (-(b * t)) := by rw [hsum]
          _ = Real.exp (-b * t) := by rw [hnegMul]
      exact (hmul1.trans_eq hmul2)
    nlinarith
  have hBigO :
      (fun t : ℝ => ‖Φ₄' u ((x : ℂ) + (t : ℂ) * Complex.I)‖) =O[atTop]
        fun t : ℝ => Real.exp (-b * t) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨C, ?_⟩
    filter_upwards [hdecay] with t ht
    simpa using! ht
  have hcontNorm :
      ContinuousOn (fun t : ℝ => ‖Φ₄' u ((x : ℂ) + (t : ℂ) * Complex.I)‖) (Set.Ici (1 : ℝ)) :=
    (continuousOn_vertical_Φ₄' (u := u) (x := x)).norm
  have hIntNorm :
      IntegrableOn
        (fun t : ℝ => ‖Φ₄' u ((x : ℂ) + (t : ℂ) * Complex.I)‖)
        (Set.Ioi (1 : ℝ)) volume :=
    integrable_of_isBigO_exp_neg (a := (1 : ℝ)) (b := b) hb hcontNorm (by simpa using! hBigO)
  let μ : Measure ℝ := volume.restrict (Set.Ioi (1 : ℝ))
  have hmeas :
      AEStronglyMeasurable (fun t : ℝ => Φ₄' u ((x : ℂ) + (t : ℂ) * Complex.I)) μ := by
    have hcontIoi :
        ContinuousOn (fun t : ℝ => Φ₄' u ((x : ℂ) + (t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) :=
      (continuousOn_vertical_Φ₄' (u := u) (x := x)).mono (Set.Ioi_subset_Ici_self)
    exact hcontIoi.aestronglyMeasurable measurableSet_Ioi
  have hfiNorm :
      MeasureTheory.HasFiniteIntegral
        (fun t : ℝ => ‖Φ₄' u ((x : ℂ) + (t : ℂ) * Complex.I)‖) μ := by
    have hIntNormμ :
        Integrable (fun t : ℝ => ‖Φ₄' u ((x : ℂ) + (t : ℂ) * Complex.I)‖) μ := by
      simpa [MeasureTheory.IntegrableOn, μ] using! hIntNorm
    exact hIntNormμ.hasFiniteIntegral
  have hfi :
      MeasureTheory.HasFiniteIntegral (fun t : ℝ => Φ₄' u ((x : ℂ) + (t : ℂ) * Complex.I)) μ :=
    (MeasureTheory.hasFiniteIntegral_iff_norm (f := fun t : ℝ =>
        Φ₄' u ((x : ℂ) + (t : ℂ) * Complex.I)) (μ := μ)).2 <|
      (by
        exact IntegrableOn.setLIntegral_lt_top hIntNorm)
  exact ⟨hmeas, hfi⟩

/-!
### Top-edge decay (`u > 4`)

We need the horizontal "top" integrals to tend to `0` as the height tends to `∞`, in order to
apply `rect_deform_of_tendsto_top`.
-/

lemma abs_add_one_le_one_of_mem_Ioc_neg_one_zero {x : ℝ} (hx : x ∈ Set.Ioc (-1 : ℝ) 0) :
    |x + 1| ≤ 1 := by
  grind only [= mem_Ioc, = abs.eq_1, = max_def]

lemma abs_sub_one_le_one_of_mem_Ioc_zero_one {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    |x - 1| ≤ 1 := by
  have hle : x ≤ 1 := hx.2
  have hgt : 0 < x := hx.1
  -- `|x-1| ≤ 1` is the same as `-1 ≤ x-1 ≤ 1`.
  refine abs_le.2 ?_
  constructor
  · linarith [hgt]
  · linarith [hle]

lemma tendsto_top_edge_I₂' (u : ℝ) (hu : 4 < u) :
    Tendsto (fun m : ℝ => ∫ x in (-1 : ℝ)..0, Φ₂' u ((x : ℂ) + (m : ℂ) * Complex.I)) atTop
      (𝓝 0) := by
  -- Use the `Φ₂'` crude bound to dominate the interval integral by `poly(m) * exp(-π(u-4)m)`.
  rcases TailBounds.exists_bound_norm_pow_ten_varphi_S with ⟨K, A, hK, hbound⟩
  have hpiu : 0 < Real.pi * (u - 4) := mul_pos Real.pi_pos (sub_pos.2 hu)
  let C0 : ℝ := 4 * K
  let T : ℝ := max A 1
  have hC0pos : 0 < C0 := by dsimp [C0]; nlinarith [hK]
  -- Pointwise bound for all `x ∈ Ι (-1) 0` once `m ≥ T`.
  have hboundPoint :
      ∀ᶠ m : ℝ in atTop, ∀ x ∈ (Ι (-1 : ℝ) 0), ‖Φ₂' u ((x : ℂ) + (m : ℂ) * Complex.I)‖ ≤
        C0 * (m ^ (2 : ℕ) + m + 1) * Real.exp (-Real.pi * (u - 4) * m) := by
    filter_upwards [eventually_ge_atTop T] with m hm x hx
    -- Convert `x ∈ Ι (-1) 0` to `x ∈ Ioc (-1) 0`.
    have hx' : x ∈ Set.Ioc (-1 : ℝ) 0 := by
      simpa [Set.uIoc_of_le (show (-1 : ℝ) ≤ 0 by norm_num)] using! hx
    have hxabs : |x + 1| ≤ 1 := abs_add_one_le_one_of_mem_Ioc_neg_one_zero hx'
    have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
    have hmA : A ≤ m := le_trans (le_max_left _ _) hm
    have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm1
    -- Run the same computation as `norm_Φ₂'_vadd_it_le`, but at a fixed height `m`.
    set z : ℍ := x +ᵥ it m hmpos
    have hz : (z : ℂ) = (x : ℂ) + (m : ℂ) * Complex.I := by
      simp [z, it, mul_comm]
    have hterm := (Φ₂'_term_eq (u := u) (z := z))
    set w : ℍ := (1 : ℝ) +ᵥ z
    have hwbound :
          ‖((w : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • w)‖ ≤
            C0 * (m ^ (2 : ℕ) + m + 1) * Real.exp (4 * Real.pi * m) := by
      have hw : w = (x + 1) +ᵥ it m hmpos := by
        ext; simp [w, z, add_assoc, add_left_comm]
      simpa [C0, hw] using!
        (norm_pow_ten_varphi_S_le (K := K) (A := A) hK hbound
          (a := x + 1) (t := m) hmpos hm1 hxabs hmA)
    have hexp :
        ‖cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ))‖ = Real.exp (-Real.pi * u * m) := by
      have hzIm : (z : ℂ).im = m := by
        dsimp [z]
        exact im_coe_vadd_it (a := x) (t := m) hmpos
      have h := norm_cexp_pi_I_mul_u_mul (u := u) (z := (z : ℂ))
      rw [hzIm] at h
      simpa using! h
    have hExp :
        Real.exp (4 * Real.pi * m) * Real.exp (-Real.pi * u * m) =
          Real.exp (-Real.pi * (u - 4) * m) := by
      have : (4 * Real.pi * m) + (-(Real.pi * u * m)) = -(Real.pi * (u - 4) * m) := by ring
      calc
        Real.exp (4 * Real.pi * m) * Real.exp (-Real.pi * u * m) =
            Real.exp ((4 * Real.pi * m) + (-(Real.pi * u * m))) := by
              simp [Real.exp_add, neg_mul, mul_assoc]
        _ = Real.exp (-(Real.pi * (u - 4) * m)) := by simp [this]
        _ = Real.exp (-Real.pi * (u - 4) * m) := by simp [mul_assoc, neg_mul]
    have hEq : Φ₂' u (z : ℂ) = ((w : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • w) *
          cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ)) := by
      simpa [w] using! hterm.symm
    calc
      ‖Φ₂' u ((x : ℂ) + (m : ℂ) * Complex.I)‖ = ‖Φ₂' u (z : ℂ)‖ := by simp [hz]
      _ = ‖((w : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • w) *
            cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ))‖ := by simp [hEq]
      _ = ‖((w : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • w)‖ *
            ‖cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ))‖ := by
            simp [mul_assoc]
      _ ≤ (C0 * (m ^ (2 : ℕ) + m + 1) * Real.exp (4 * Real.pi * m)) *
            Real.exp (-Real.pi * u * m) := by
            have hE :
                ‖cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ))‖ ≤ Real.exp (-Real.pi * u * m) :=
              le_of_eq hexp
            exact mul_le_mul hwbound hE (by positivity) (by positivity)
      _ = C0 * (m ^ (2 : ℕ) + m + 1) * Real.exp (-Real.pi * (u - 4) * m) := by
            have :
                (C0 * (m ^ (2 : ℕ) + m + 1) * Real.exp (4 * Real.pi * m)) *
                    Real.exp (-Real.pi * u * m) =
                  C0 * (m ^ (2 : ℕ) + m + 1) *
                    (Real.exp (4 * Real.pi * m) * Real.exp (-Real.pi * u * m)) := by
              simp [mul_assoc]
            exact Eq.symm (CancelDenoms.derive_trans (id (Eq.symm hExp)) (id (Eq.symm this)))
  -- Convert to a norm estimate on the interval integral.
  have hle :
      ∀ᶠ m : ℝ in atTop,
        ‖∫ x in (-1 : ℝ)..0, Φ₂' u ((x : ℂ) + (m : ℂ) * Complex.I)‖ ≤
          C0 * (m ^ (2 : ℕ) + m + 1) * Real.exp (-Real.pi * (u - 4) * m) := by
    filter_upwards [hboundPoint] with m hm
    have h :=
      (intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := (0 : ℝ))
        (C := C0 * (m ^ (2 : ℕ) + m + 1) * Real.exp (-Real.pi * (u - 4) * m))
        (f := fun x : ℝ => Φ₂' u ((x : ℂ) + (m : ℂ) * Complex.I))) ?_
    · simpa [abs_of_pos (show (0 : ℝ) < 1 by norm_num), C0, mul_assoc] using! h
    · intro x hx
      exact hm x hx
  -- The dominating scalar tends to `0`.
  have hdom :
      Tendsto (fun m : ℝ =>
          C0 * ((m ^ (2 : ℕ) + m + 1) * Real.exp (-Real.pi * (u - 4) * m))) atTop (𝓝 0) := by
    have hT := tendsto_poly_mul_exp_neg_mul_atTop (b := Real.pi * (u - 4)) hpiu
    have hT' :
        Tendsto
          (fun m : ℝ => (m ^ (2 : ℕ) + m + 1) * Real.exp (-Real.pi * (u - 4) * m))
          atTop (𝓝 0) := by
      simpa [mul_assoc] using! hT
    simpa [mul_assoc] using! (tendsto_const_nhds.mul hT')
  -- Finish by squeezing the norms.
  refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hle ?_
  -- Rewrite the bound to match `hdom`.
  simpa [mul_assoc] using! hdom

lemma tendsto_top_edge_I₄' (u : ℝ) (hu : 4 < u) :
    Tendsto (fun m : ℝ => ∫ x in (1 : ℝ)..0, Φ₄' u ((x : ℂ) + (m : ℂ) * Complex.I)) atTop
      (𝓝 0) := by
  rcases TailBounds.exists_bound_norm_pow_ten_varphi_S with ⟨K, A, hK, hbound⟩
  have hpiu : 0 < Real.pi * (u - 4) := mul_pos Real.pi_pos (sub_pos.2 hu)
  let C0 : ℝ := 4 * K
  let T : ℝ := max A 1
  have hC0pos : 0 < C0 := by dsimp [C0]; nlinarith [hK]
  have hboundPoint :
      ∀ᶠ m : ℝ in atTop, ∀ x ∈ (Ι (1 : ℝ) 0), ‖Φ₄' u ((x : ℂ) + (m : ℂ) * Complex.I)‖ ≤
        C0 * (m ^ (2 : ℕ) + m + 1) * Real.exp (-Real.pi * (u - 4) * m) := by
    filter_upwards [eventually_ge_atTop T] with m hm x hx
    have hx' : x ∈ Set.Ioc (0 : ℝ) 1 := by
      -- `Ι 1 0 = Ioc 0 1`.
      simpa [Set.uIoc_of_ge (show (0 : ℝ) ≤ 1 by norm_num)] using! hx
    have hxabs : |x - 1| ≤ 1 := abs_sub_one_le_one_of_mem_Ioc_zero_one hx'
    have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
    have hmA : A ≤ m := le_trans (le_max_left _ _) hm
    have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm1
    set z : ℍ := x +ᵥ it m hmpos
    have hz : (z : ℂ) = (x : ℂ) + (m : ℂ) * Complex.I := by
      simp [z, it, mul_comm]
    have hterm := (Φ₄'_term_eq (u := u) (z := z))
    set w : ℍ := (-1 : ℝ) +ᵥ z
    have hwbound :
          ‖((w : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • w)‖ ≤
            C0 * (m ^ (2 : ℕ) + m + 1) * Real.exp (4 * Real.pi * m) := by
      have hw : w = (x - 1) +ᵥ it m hmpos := by
        ext; simp [w, z, sub_eq_add_neg, add_assoc, add_left_comm]
      simpa [C0, hw] using!
        (norm_pow_ten_varphi_S_le (K := K) (A := A) hK hbound
          (a := x - 1) (t := m) hmpos hm1 hxabs hmA)
    have hexp :
        ‖cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ))‖ = Real.exp (-Real.pi * u * m) := by
      have hzIm : (z : ℂ).im = m := by
        dsimp [z]
        exact im_coe_vadd_it (a := x) (t := m) hmpos
      have h := norm_cexp_pi_I_mul_u_mul (u := u) (z := (z : ℂ))
      rw [hzIm] at h
      simpa using! h
    have hExp :
        Real.exp (4 * Real.pi * m) * Real.exp (-Real.pi * u * m) =
          Real.exp (-Real.pi * (u - 4) * m) := by
      have : (4 * Real.pi * m) + (-(Real.pi * u * m)) = -(Real.pi * (u - 4) * m) := by ring
      calc
        Real.exp (4 * Real.pi * m) * Real.exp (-Real.pi * u * m) =
            Real.exp ((4 * Real.pi * m) + (-(Real.pi * u * m))) := by
              simp [Real.exp_add, neg_mul, mul_assoc]
        _ = Real.exp (-(Real.pi * (u - 4) * m)) := by simp [this]
        _ = Real.exp (-Real.pi * (u - 4) * m) := by simp [mul_assoc, neg_mul]
    have hEq : Φ₄' u (z : ℂ) = ((w : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • w) *
          cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ)) := by
      simpa [w] using! hterm.symm
    calc
      ‖Φ₄' u ((x : ℂ) + (m : ℂ) * Complex.I)‖ = ‖Φ₄' u (z : ℂ)‖ := by simp [hz]
      _ = ‖((w : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • w) *
            cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ))‖ := by simp [hEq]
      _ = ‖((w : ℂ) ^ (10 : ℕ)) * varphi (ModularGroup.S • w)‖ *
            ‖cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ))‖ := by
            simp [mul_assoc]
      _ ≤ (C0 * (m ^ (2 : ℕ) + m + 1) * Real.exp (4 * Real.pi * m)) *
            Real.exp (-Real.pi * u * m) := by
            have hE :
                ‖cexp (Real.pi * Complex.I * (u : ℂ) * (z : ℂ))‖ ≤ Real.exp (-Real.pi * u * m) :=
              le_of_eq hexp
            exact mul_le_mul hwbound hE (by positivity) (by positivity)
      _ = C0 * (m ^ (2 : ℕ) + m + 1) * Real.exp (-Real.pi * (u - 4) * m) := by
            have :
                (C0 * (m ^ (2 : ℕ) + m + 1) * Real.exp (4 * Real.pi * m)) *
                    Real.exp (-Real.pi * u * m) =
                  C0 * (m ^ (2 : ℕ) + m + 1) *
                    (Real.exp (4 * Real.pi * m) * Real.exp (-Real.pi * u * m)) := by
              simp [mul_assoc]
            exact Eq.symm (CancelDenoms.derive_trans (id (Eq.symm hExp)) (id (Eq.symm this)))
  have hle :
      ∀ᶠ m : ℝ in atTop,
        ‖∫ x in (1 : ℝ)..0, Φ₄' u ((x : ℂ) + (m : ℂ) * Complex.I)‖ ≤
          C0 * (m ^ (2 : ℕ) + m + 1) * Real.exp (-Real.pi * (u - 4) * m) := by
    filter_upwards [hboundPoint] with m hm
    have h :=
      (intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 : ℝ)) (b := (0 : ℝ))
        (C := C0 * (m ^ (2 : ℕ) + m + 1) * Real.exp (-Real.pi * (u - 4) * m))
        (f := fun x : ℝ => Φ₄' u ((x : ℂ) + (m : ℂ) * Complex.I))) ?_
    · -- `|0 - 1| = 1`.
      simpa [abs_of_neg (show (-1 : ℝ) < 0 by norm_num), C0, mul_assoc] using! h
    · intro x hx
      exact hm x hx
  have hdom :
      Tendsto (fun m : ℝ =>
          C0 * ((m ^ (2 : ℕ) + m + 1) * Real.exp (-Real.pi * (u - 4) * m))) atTop (𝓝 0) := by
    have hT := tendsto_poly_mul_exp_neg_mul_atTop (b := Real.pi * (u - 4)) hpiu
    have hT' :
        Tendsto
          (fun m : ℝ => (m ^ (2 : ℕ) + m + 1) * Real.exp (-Real.pi * (u - 4) * m))
          atTop (𝓝 0) := by
      simpa [mul_assoc] using! hT
    simpa [mul_assoc] using! (tendsto_const_nhds.mul hT')
  refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hle ?_
  simpa [mul_assoc] using! hdom

/-!
### Deforming `I₂'` and `I₄'` onto vertical rays (`u > 4`)
-/

lemma continuousOn_rect_Φ₂' (u : ℝ) :
    ContinuousOn (Φ₂' u) (Set.uIcc (-1 : ℝ) 0 ×ℂ Set.Ici (1 : ℝ)) := by
  refine (continuousOn_Φ₂' (u := u)).mono ?_
  intro z hz
  rw [mem_reProdIm] at hz
  have hzIm : (1 : ℝ) ≤ z.im := hz.2
  have : 0 < z.im := lt_of_lt_of_le (by norm_num) hzIm
  simpa [upperHalfPlaneSet] using! this

lemma differentiableAt_rect_Φ₂' (u : ℝ) :
    ∀ z ∈ (Set.Ioo (min (-1 : ℝ) 0) (max (-1 : ℝ) 0) ×ℂ Set.Ioi (1 : ℝ)),
      DifferentiableAt ℂ (Φ₂' u) z := by
  intro z hz
  rw [mem_reProdIm] at hz
  have hzIm : (1 : ℝ) < z.im := hz.2
  have : 0 < z.im := lt_trans (by norm_num) hzIm
  exact differentiableAt_Φ₂' (u := u) (z := z) (by simpa [upperHalfPlaneSet] using! this)

lemma continuousOn_rect_Φ₄' (u : ℝ) :
    ContinuousOn (Φ₄' u) (Set.uIcc (1 : ℝ) 0 ×ℂ Set.Ici (1 : ℝ)) := by
  refine (continuousOn_Φ₄' (u := u)).mono ?_
  intro z hz
  rw [mem_reProdIm] at hz
  have hzIm : (1 : ℝ) ≤ z.im := hz.2
  have : 0 < z.im := lt_of_lt_of_le (by norm_num) hzIm
  simpa [upperHalfPlaneSet] using! this

lemma differentiableAt_rect_Φ₄' (u : ℝ) :
    ∀ z ∈ (Set.Ioo (min (1 : ℝ) 0) (max (1 : ℝ) 0) ×ℂ Set.Ioi (1 : ℝ)),
      DifferentiableAt ℂ (Φ₄' u) z := by
  intro z hz
  rw [mem_reProdIm] at hz
  have hzIm : (1 : ℝ) < z.im := hz.2
  have : 0 < z.im := lt_trans (by norm_num) hzIm
  exact differentiableAt_Φ₄' (u := u) (z := z) (by simpa [upperHalfPlaneSet] using! this)

lemma I₂'_eq_vertical (u : ℝ) (hu : 4 < u) :
    RealIntegrals.I₂' u =
      (Complex.I : ℂ) • (∫ t in Set.Ioi (1 : ℝ),
            Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I)) -
        (Complex.I : ℂ) • (∫ t in Set.Ioi (1 : ℝ),
            Φ₂' u ((0 : ℂ) + (t : ℂ) * Complex.I)) := by
  have hrect :=
    Complex.rect_deform_of_tendsto_top (f := Φ₂' u) (x₁ := (-1 : ℝ)) (x₂ := (0 : ℝ))
      (y := (1 : ℝ))
      (hcont := continuousOn_rect_Φ₂' (u := u)) (hdiff := differentiableAt_rect_Φ₂' (u := u))
      (hint₁ := integrableOn_vertical_Φ₂' (u := u) (x := (-1 : ℝ)) hu (by norm_num))
      (hint₂ := integrableOn_vertical_Φ₂' (u := u) (x := (0 : ℝ)) hu (by norm_num))
      (htop := tendsto_top_edge_I₂' (u := u) hu)
  -- Rearrange the deformation identity to solve for the bottom edge.
  have hbottom :
      (∫ x in (-1 : ℝ)..0, Φ₂' u ((x : ℂ) + Complex.I)) =
        (Complex.I : ℂ) • (∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I)) -
          (Complex.I : ℂ) • (∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((0 : ℂ) + (t : ℂ) * Complex.I)) := by
    refine eq_sub_of_add_sub_eq_zero ?_
    simpa [mul_assoc] using! hrect
  -- Convert the bottom edge to `I₂'`.
  calc
    RealIntegrals.I₂' u = ∫ x in (-1 : ℝ)..0, Φ₂' u ((x : ℂ) + Complex.I) :=
      (I₂'_eq_intervalIntegral_bottom (u := u))
    _ = (Complex.I : ℂ) • (∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I)) -
          (Complex.I : ℂ) • (∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((0 : ℂ) + (t : ℂ) * Complex.I)) :=
      hbottom

lemma I₄'_eq_vertical (u : ℝ) (hu : 4 < u) :
    RealIntegrals.I₄' u =
      (Complex.I : ℂ) • (∫ t in Set.Ioi (1 : ℝ),
            Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) -
        (Complex.I : ℂ) • (∫ t in Set.Ioi (1 : ℝ),
            Φ₄' u ((0 : ℂ) + (t : ℂ) * Complex.I)) := by
  have hrect :=
    Complex.rect_deform_of_tendsto_top (f := Φ₄' u) (x₁ := (1 : ℝ)) (x₂ := (0 : ℝ))
      (y := (1 : ℝ))
      (hcont := continuousOn_rect_Φ₄' (u := u)) (hdiff := differentiableAt_rect_Φ₄' (u := u))
      (hint₁ := integrableOn_vertical_Φ₄' (u := u) (x := (1 : ℝ)) hu (by norm_num))
      (hint₂ := integrableOn_vertical_Φ₄' (u := u) (x := (0 : ℝ)) hu (by norm_num))
      (htop := tendsto_top_edge_I₄' (u := u) hu)
  have hbottom :
      (∫ x in (1 : ℝ)..0, Φ₄' u ((x : ℂ) + Complex.I)) =
        (Complex.I : ℂ) • (∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) -
          (Complex.I : ℂ) • (∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((0 : ℂ) + (t : ℂ) * Complex.I)) := by
    refine eq_sub_of_add_sub_eq_zero ?_
    simpa [mul_assoc] using! hrect
  calc
    RealIntegrals.I₄' u = ∫ x in (1 : ℝ)..0, Φ₄' u ((x : ℂ) + Complex.I) :=
      (I₄'_eq_intervalIntegral_bottom (u := u))
    _ = (Complex.I : ℂ) • (∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) -
          (Complex.I : ℂ) • (∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((0 : ℂ) + (t : ℂ) * Complex.I)) :=
      hbottom

lemma I₆'_eq_two_mul_I_mul_integral_Φ₆' (u : ℝ) :
    RealIntegrals.I₆' u =
      (2 : ℂ) * (Complex.I : ℂ) * (∫ t in Set.Ioi (1 : ℝ), Φ₆' u ((t : ℂ) * Complex.I)) := by
  -- Remove the endpoint `t = 1` (measure zero).
  have hIci :
      (∫ t in Set.Ici (1 : ℝ), RealIntegrands.Φ₆ u t) =
        ∫ t in Set.Ioi (1 : ℝ), RealIntegrands.Φ₆ u t := by
    exact integral_Ici_eq_integral_Ioi
  -- Rewrite the parametrization `z₆' t = i t` almost everywhere on `Ioi 1`.
  have hcongr :
      (∫ t in Set.Ioi (1 : ℝ), RealIntegrands.Φ₆ u t) =
        ∫ t in Set.Ioi (1 : ℝ), (Complex.I : ℂ) * Φ₆' u ((t : ℂ) * Complex.I) := by
    -- Argue under the restricted measure.
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : t ∈ Set.Ici (1 : ℝ) := le_of_lt (by simpa [Set.mem_Ioi] using! ht)
    have hz : z₆' t = (Complex.I : ℂ) * t := z₆'_eq_of_mem ht'
    have hz' : z₆' t = (t : ℂ) * Complex.I := by
      simpa [mul_comm] using! hz
    -- Unfold `Φ₆` and rewrite `z₆' t`.
    simp [RealIntegrands.Φ₆, hz']
  -- Assemble `I₆'`.
  rw [RealIntegrals.I₆', hIci, hcongr]
  -- Pull out the constant `I`.
  simp [MeasureTheory.integral_const_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Integrability of the primed integrand `Φ₅'` along the imaginary axis on `(1,∞)` for `u > 4`.

Here the prime indicates the complex-valued contour integrand (as opposed to a real-parametrized
version). -/
public lemma integrable_imag_axis_Φ₅' (u : ℝ) (hu : 4 < u) :
    Integrable (fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)) (volume.restrict (Set.Ioi (1 : ℝ))) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi (1 : ℝ))
  -- Start from integrability of the shifted `Φ₄'` at `x=1`.
  have hIntRight :
      IntegrableOn (fun t : ℝ => Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) volume :=
    integrableOn_vertical_Φ₄' (u := u) (x := (1 : ℝ)) hu (by simp)
  have hIntRight' :
      Integrable (fun t : ℝ => Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) μ := by
    simpa [MeasureTheory.IntegrableOn, μ] using! hIntRight
  set c : ℂ := Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I)
  have hc0 : c ≠ 0 := by
    simp [c]
  have hcf :
      (fun t : ℝ => Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) =
        fun t : ℝ => c * Φ₅' u ((t : ℂ) * Complex.I) := by
    funext t
    dsimp [c]
    simpa using! (Φ₄'_shift_right (u := u) (t := t))
  have hIntCf : Integrable (fun t : ℝ => c * Φ₅' u ((t : ℂ) * Complex.I)) μ := by
    simpa [hcf] using! hIntRight'
  have : Integrable (fun t : ℝ => c⁻¹ * (c * Φ₅' u ((t : ℂ) * Complex.I))) μ :=
    hIntCf.const_mul c⁻¹
  have hmul :
      (fun t : ℝ => c⁻¹ * (c * Φ₅' u ((t : ℂ) * Complex.I))) =
        fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I) := by
    funext t
    simp [hc0]
  simpa [μ, hmul] using! this

/-- Tail factorization on the vertical ray: for `u > 4`, the tail sum `I₂' + I₄' + I₆'` is a scalar
multiple of the imaginary-axis integral of `Φ₅'` over `(1,∞)`. -/
public theorem I₂'_add_I₄'_add_I₆'_eq_imag_axis (u : ℝ) (hu : 4 < u) :
    RealIntegrals.I₂' u + RealIntegrals.I₄' u + RealIntegrals.I₆' u =
      (Complex.I : ℂ) *
        ((Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) +
              Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ)) *
            (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I))) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi (1 : ℝ))
  let V : ℂ := ∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)
  have hV : V = ∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I) := rfl
  -- Deform `I₂'` and `I₄'` to vertical rays.
  have hI2 := I₂'_eq_vertical (u := u) hu
  have hI4 := I₄'_eq_vertical (u := u) hu
  -- Rewrite the shifted vertical integrals using the shift identities.
  have hshift2 :
      (∫ t in Set.Ioi (1 : ℝ), Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I)) =
        Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) * V := by
    have hfun :
        (fun t : ℝ => Φ₂' u ((-1 : ℂ) + (t : ℂ) * Complex.I)) =
          fun t : ℝ =>
            Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) * Φ₅' u ((t : ℂ) * Complex.I) := by
      funext t
      simpa using! (Φ₂'_shift_left (u := u) (t := t))
    -- Rewrite the integrand and pull out the constant factor.
    simp [hfun, V, MeasureTheory.integral_const_mul, mul_assoc]
  have hshift4 :
      (∫ t in Set.Ioi (1 : ℝ), Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) =
        Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) * V := by
    have hfun :
        (fun t : ℝ => Φ₄' u ((1 : ℂ) + (t : ℂ) * Complex.I)) =
          fun t : ℝ =>
            Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) * Φ₅' u ((t : ℂ) * Complex.I) := by
      funext t
      simpa using! (Φ₄'_shift_right (u := u) (t := t))
    simp [hfun, V, MeasureTheory.integral_const_mul, mul_assoc]
  -- Abbreviate the imaginary-axis integrands at `x=0`.
  let f2 : ℝ → ℂ := fun t : ℝ => Φ₂' u ((t : ℂ) * Complex.I)
  let f4 : ℝ → ℂ := fun t : ℝ => Φ₄' u ((t : ℂ) * Complex.I)
  let f5 : ℝ → ℂ := fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)
  let f6 : ℝ → ℂ := fun t : ℝ => Φ₆' u ((t : ℂ) * Complex.I)
  have hInt2 : Integrable f2 μ := by
    have :
        IntegrableOn (fun t : ℝ => Φ₂' u ((0 : ℂ) + (t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ))
          volume :=
      integrableOn_vertical_Φ₂' (u := u) (x := (0 : ℝ)) hu (by norm_num)
    simpa [MeasureTheory.IntegrableOn, μ, f2, add_zero] using! this
  have hInt4 : Integrable f4 μ := by
    have :
        IntegrableOn (fun t : ℝ => Φ₄' u ((0 : ℂ) + (t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ))
          volume :=
      integrableOn_vertical_Φ₄' (u := u) (x := (0 : ℝ)) hu (by norm_num)
    simpa [MeasureTheory.IntegrableOn, μ, f4, add_zero] using! this
  have hInt5 : Integrable f5 μ := by
    simpa [μ, f5] using! (integrable_imag_axis_Φ₅' (u := u) hu)
  -- Use the finite-difference identity to relate `f2+f4` to `f5+f6` almost everywhere.
  have hEq :
      (fun t : ℝ => f2 t + f4 t) =ᵐ[μ] fun t : ℝ => (2 : ℂ) * f5 t + (2 : ℂ) * f6 t := by
    have hmem : ∀ᵐ t ∂μ, t ∈ Set.Ioi (1 : ℝ) := ae_restrict_mem measurableSet_Ioi
    filter_upwards [hmem] with t ht
    have ht0 : 0 < t := lt_trans (by norm_num) ht
    have hfd :=
      Φ₂'_sub_two_mul_Φ₅'_add_Φ₄'_eq_two_mul_Φ₆' (u := u) (t := t) ht0
    have hfd' : f2 t - (2 : ℂ) * f5 t + f4 t = (2 : ℂ) * f6 t := by
      simpa [f2, f4, f5, f6] using! hfd
    calc
      f2 t + f4 t = (f2 t - (2 : ℂ) * f5 t + f4 t) + (2 : ℂ) * f5 t := by ring
      _ = (2 : ℂ) * f6 t + (2 : ℂ) * f5 t := by simp [hfd']
      _ = (2 : ℂ) * f5 t + (2 : ℂ) * f6 t := by ac_rfl
  -- Extract integrability of `f6` from integrability of `f2+f4` and `f5` via the relation `hEq`.
  have hIntSum : Integrable (fun t : ℝ => f2 t + f4 t) μ := hInt2.add hInt4
  have hIntRhs : Integrable (fun t : ℝ => (2 : ℂ) * f5 t + (2 : ℂ) * f6 t) μ :=
    hIntSum.congr hEq
  have hInt2F5 : Integrable (fun t : ℝ => (2 : ℂ) * f5 t) μ := hInt5.const_mul (2 : ℂ)
  have hInt2F6 : Integrable (fun t : ℝ => (2 : ℂ) * f6 t) μ :=
    (integrable_add_iff_integrable_right' hInt2F5).mp hIntRhs
  have hInt6 : Integrable f6 μ := by
    have : Integrable (fun t : ℝ => (1 / (2 : ℂ)) * ((2 : ℂ) * f6 t)) μ :=
      hInt2F6.const_mul (1 / (2 : ℂ))
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    have hmul : (fun t : ℝ => (1 / (2 : ℂ)) * ((2 : ℂ) * f6 t)) = f6 := by
      funext t
      simp [div_eq_mul_inv, h2]
    simpa [hmul] using! this
  -- Rewrite `I₆'` as the vertical integral of `f6`.
  have hI6 :
      RealIntegrals.I₆' u = (2 : ℂ) * (Complex.I : ℂ) * (∫ t in Set.Ioi (1 : ℝ), f6 t) := by
    simpa [f6] using! (I₆'_eq_two_mul_I_mul_integral_Φ₆' (u := u))
  -- Rewrite `I₂'` and `I₄'` using `hshift2`, `hshift4` and the `x=0` integrals `f2`, `f4`.
  have hI2' :
      RealIntegrals.I₂' u =
        (Complex.I : ℂ) • (Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) * V) -
          (Complex.I : ℂ) • (∫ t in Set.Ioi (1 : ℝ), f2 t) := by
    simpa [hshift2, f2, add_zero, sub_eq_add_neg, hV, mul_assoc] using! hI2
  have hI4' :
      RealIntegrals.I₄' u =
        (Complex.I : ℂ) • (Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) * V) -
          (Complex.I : ℂ) • (∫ t in Set.Ioi (1 : ℝ), f4 t) := by
    simpa [hshift4, f4, add_zero, sub_eq_add_neg, hV, mul_assoc] using! hI4
  -- Turn `I•X - I•Y` into `I*(X - Y)` to simplify the final algebra.
  have hI2mul :
      RealIntegrals.I₂' u =
        (Complex.I : ℂ) *
          (Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) * V -
            (∫ t in Set.Ioi (1 : ℝ), f2 t)) := by
    have h' :
        RealIntegrals.I₂' u =
          (Complex.I : ℂ) * (Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) * V) -
            (Complex.I : ℂ) * (∫ t in Set.Ioi (1 : ℝ), f2 t) := by
      simpa [smul_eq_mul] using! hI2'
    calc
      RealIntegrals.I₂' u =
          (Complex.I : ℂ) * (Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) * V) -
            (Complex.I : ℂ) * (∫ t in Set.Ioi (1 : ℝ), f2 t) := h'
      _ =
          (Complex.I : ℂ) *
            (Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) * V -
              (∫ t in Set.Ioi (1 : ℝ), f2 t)) := by
          ring
  have hI4mul :
      RealIntegrals.I₄' u =
        (Complex.I : ℂ) *
          (Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) * V -
            (∫ t in Set.Ioi (1 : ℝ), f4 t)) := by
    have h' :
        RealIntegrals.I₄' u =
          (Complex.I : ℂ) * (Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) * V) -
            (Complex.I : ℂ) * (∫ t in Set.Ioi (1 : ℝ), f4 t) := by
      simpa [smul_eq_mul] using! hI4'
    calc
      RealIntegrals.I₄' u =
          (Complex.I : ℂ) * (Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) * V) -
            (Complex.I : ℂ) * (∫ t in Set.Ioi (1 : ℝ), f4 t) := h'
      _ =
          (Complex.I : ℂ) *
            (Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) * V -
              (∫ t in Set.Ioi (1 : ℝ), f4 t)) := by
          ring
  have hI6mul :
      RealIntegrals.I₆' u =
        (Complex.I : ℂ) * ((2 : ℂ) * (∫ t in Set.Ioi (1 : ℝ), f6 t)) := by
    -- Commute factors to pull out `I`.
    simpa [mul_assoc, mul_left_comm, mul_comm] using! hI6
  -- Integral identity: `∫ f2 + ∫ f4 = 2*V + 2*∫ f6`.
  have hIntegral :
      (∫ t in Set.Ioi (1 : ℝ), f2 t) + (∫ t in Set.Ioi (1 : ℝ), f4 t) =
        (2 : ℂ) * V + (2 : ℂ) * (∫ t in Set.Ioi (1 : ℝ), f6 t) := by
    have hcongr :
        (∫ t, (f2 t + f4 t) ∂μ) = ∫ t, ((2 : ℂ) * f5 t + (2 : ℂ) * f6 t) ∂μ := by
      refine MeasureTheory.integral_congr_ae ?_
      exact hEq
    have hL :
        (∫ t, (f2 t + f4 t) ∂μ) = (∫ t, f2 t ∂μ) + (∫ t, f4 t ∂μ) := by
      simpa using! (MeasureTheory.integral_add hInt2 hInt4)
    have hR :
        (∫ t, ((2 : ℂ) * f5 t + (2 : ℂ) * f6 t) ∂μ) =
          (∫ t, (2 : ℂ) * f5 t ∂μ) + (∫ t, (2 : ℂ) * f6 t ∂μ) := by
      simpa using! (MeasureTheory.integral_add hInt2F5 hInt2F6)
    have hcongr' := hcongr
    rw [hL, hR] at hcongr'
    have hVμ : (∫ t, f5 t ∂μ) = V := by simp [μ, V, f5]
    have hFinal :
        (∫ t, f2 t ∂μ) + (∫ t, f4 t ∂μ) =
          (2 : ℂ) * V + (2 : ℂ) * (∫ t, f6 t ∂μ) := by
      calc
        (∫ t, f2 t ∂μ) + (∫ t, f4 t ∂μ) =
            (∫ t, (2 : ℂ) * f5 t ∂μ) + (∫ t, (2 : ℂ) * f6 t ∂μ) := hcongr'
        _ =
            (2 : ℂ) * (∫ t, f5 t ∂μ) + (2 : ℂ) * (∫ t, f6 t ∂μ) := by
            simp [MeasureTheory.integral_const_mul]
        _ = (2 : ℂ) * V + (2 : ℂ) * (∫ t, f6 t ∂μ) := by simp [hVμ]
    simpa [μ] using! hFinal
  grind only

end LaplaceZerosTail.TailDeform
end

end SpherePacking.Dim24
