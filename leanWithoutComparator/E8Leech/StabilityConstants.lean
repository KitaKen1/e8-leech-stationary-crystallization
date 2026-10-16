import E8Leech.GuardedPeriodicPacking

/-!
# Elementary estimates for the constants of the periodic stability input

Real-variable inequalities used to turn `e8_periodic_window_structure` into the periodic
stability input with the error `E·exp(c·R_η)·η^{1/4}` and the loss `B·R_η^{-1/2}`, where
`R_η = log(1/η) / log log(1/η)` is the observation radius.

* `rpow_quarter_le_exp_neg`: `η^{1/4} ≤ exp(-κ R_η)` once `log log(1/η) ≥ 4κ`.
* `le_observationRadius`: `R_η ≥ R₀` once `log(1/η) ≥ 4R₀²`.
* `pow_eight_sub_le`: `x⁸ - y⁸ ≤ 8(x-y)x⁷`.
* `windowBound_sub_volume_le`: `windowBound R - vol(B_R) ≤ K R⁷` and `vol(B_R) ≤ windowBound R`.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric

theorem le_exp_self (x : ℝ) : x ≤ Real.exp x := by
  linarith [Real.add_one_le_exp x]

theorem pow_le_exp_mul {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : x ^ n ≤ Real.exp (n * x) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ hx (le_exp_self x) n

theorem exp_neg_le_inv {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 1 / x := by
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ hx (le_exp_self x)

/-- `η^{1/4} ≤ exp(-κ R_η)` once `log log(1/η) ≥ 4κ`. -/
theorem rpow_quarter_le_exp_neg {η κ : ℝ} (hη0 : 0 < η) (hκ : 0 < κ)
    (hx : Real.exp (4 * κ) ≤ Real.log (1 / η)) :
    η ^ (1 / 4 : ℝ) ≤ Real.exp (-(κ * observationRadius η)) := by
  unfold observationRadius
  have hlog : Real.log η = -Real.log (1 / η) := by
    rw [one_div, Real.log_inv, neg_neg]
  have hx0 : 0 < Real.log (1 / η) := lt_of_lt_of_le (Real.exp_pos _) hx
  have hy : 4 * κ ≤ Real.log (Real.log (1 / η)) := by
    have h := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at h
  have hy0 : 0 < Real.log (Real.log (1 / η)) := by linarith
  rw [Real.rpow_def_of_pos hη0, hlog, Real.exp_le_exp]
  have h1 : κ * (Real.log (1 / η) / Real.log (Real.log (1 / η))) ≤ Real.log (1 / η) / 4 := by
    rw [← mul_div_assoc, div_le_div_iff₀ hy0 (by norm_num)]
    nlinarith
  linarith

/-- `R_η ≥ R₀` once `log(1/η) ≥ 4R₀²`. -/
theorem le_observationRadius {η R₀ : ℝ} (hR₀ : 1 ≤ R₀)
    (hx : 4 * R₀ ^ 2 ≤ Real.log (1 / η)) : R₀ ≤ observationRadius η := by
  unfold observationRadius
  have hx4 : 4 ≤ Real.log (1 / η) := by nlinarith
  have hx0 : 0 < Real.log (1 / η) := by linarith
  have hs : 0 < Real.sqrt (Real.log (1 / η)) := Real.sqrt_pos.mpr hx0
  have hlog : Real.log (Real.log (1 / η)) ≤ 2 * Real.sqrt (Real.log (1 / η)) := by
    have h1 := Real.log_le_sub_one_of_pos hs
    rw [Real.log_sqrt hx0.le] at h1
    linarith
  have hlog0 : 0 < Real.log (Real.log (1 / η)) := Real.log_pos (by linarith)
  have hsq : Real.sqrt (Real.log (1 / η)) * Real.sqrt (Real.log (1 / η)) = Real.log (1 / η) :=
    Real.mul_self_sqrt hx0.le
  have h2 : 2 * R₀ ≤ Real.sqrt (Real.log (1 / η)) := by
    have h3 : Real.sqrt ((2 * R₀) ^ 2) ≤ Real.sqrt (Real.log (1 / η)) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at h3
  rw [le_div_iff₀ hlog0]
  nlinarith

/-- `x⁸ - y⁸ ≤ 8 (x - y) x⁷` for `0 ≤ y ≤ x`. -/
theorem pow_eight_sub_le {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) :
    x ^ 8 - y ^ 8 ≤ 8 * (x - y) * x ^ 7 := by
  have hx : 0 ≤ x := hy.trans hxy
  have hk : ∀ a b : ℕ, a + b = 7 → x ^ a * y ^ b ≤ x ^ 7 := by
    intro a b hab
    calc x ^ a * y ^ b ≤ x ^ a * x ^ b :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hxy b) (pow_nonneg hx a)
      _ = x ^ 7 := by rw [← pow_add, hab]
  have e : x ^ 8 - y ^ 8 = (x - y) * (x ^ 7 * y ^ 0 + x ^ 6 * y ^ 1 + x ^ 5 * y ^ 2 +
      x ^ 4 * y ^ 3 + x ^ 3 * y ^ 4 + x ^ 2 * y ^ 5 + x ^ 1 * y ^ 6 + x ^ 0 * y ^ 7) := by ring
  have hsum : x ^ 7 * y ^ 0 + x ^ 6 * y ^ 1 + x ^ 5 * y ^ 2 + x ^ 4 * y ^ 3 + x ^ 3 * y ^ 4 +
      x ^ 2 * y ^ 5 + x ^ 1 * y ^ 6 + x ^ 0 * y ^ 7 ≤ 8 * x ^ 7 := by
    linarith [hk 7 0 rfl, hk 6 1 rfl, hk 5 2 rfl, hk 4 3 rfl, hk 3 4 rfl, hk 2 5 rfl,
      hk 1 6 rfl, hk 0 7 rfl]
  rw [e]
  calc (x - y) * (x ^ 7 * y ^ 0 + x ^ 6 * y ^ 1 + x ^ 5 * y ^ 2 + x ^ 4 * y ^ 3 + x ^ 3 * y ^ 4 +
        x ^ 2 * y ^ 5 + x ^ 1 * y ^ 6 + x ^ 0 * y ^ 7) ≤ (x - y) * (8 * x ^ 7) :=
        mul_le_mul_of_nonneg_left hsum (by linarith)
    _ = 8 * (x - y) * x ^ 7 := by ring

/-- The constant of the local count: `windowBound R - vol(B_R) ≤ stabilityK · R⁷`. -/
def stabilityK : ℝ :=
  8 * (Real.sqrt 2 + e8BasisNormSum) * 2 ^ 7 * volume.real (ball (0 : Ambient 8) 1) +
    8 * (Real.sqrt 2 + 2 * e8BasisNormSum) * 3 ^ 7

theorem stabilityK_nonneg : 0 ≤ stabilityK := by
  have h1 := e8BasisNormSum_nonneg
  have h2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h3 := volume_real_unitBall_eight_pos.le
  unfold stabilityK
  positivity

theorem windowBound_sub_volume_le {R : ℝ} (hR : e8BasisNormSum + 4 ≤ R) :
    windowBound R - volume.real (closedBall (0 : Ambient 8) R) ≤ stabilityK * R ^ 7 ∧
      volume.real (closedBall (0 : Ambient 8) R) ≤ windowBound R := by
  have hρ := e8BasisNormSum_nonneg
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 ≤ 2 := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    nlinarith
  have hω := volume_real_unitBall_eight_pos.le
  have hR0 : 0 ≤ R := by linarith
  have hball : volume.real (closedBall (0 : Ambient 8) R) =
      R ^ 8 * volume.real (ball (0 : Ambient 8) 1) := volume_real_closedBall_eight 0 hR0
  have hball' : volume.real (closedBall (0 : Ambient 8) (R + Real.sqrt 2 + e8BasisNormSum)) =
      (R + Real.sqrt 2 + e8BasisNormSum) ^ 8 * volume.real (ball (0 : Ambient 8) 1) :=
    volume_real_closedBall_eight 0 (by linarith)
  -- the two differences of eighth powers
  have h1 := pow_eight_sub_le hR0 (show R ≤ R + Real.sqrt 2 + e8BasisNormSum by linarith)
  have h2 := pow_eight_sub_le (show 0 ≤ 2 * R + 2 - 2 * e8BasisNormSum by linarith)
    (show 2 * R + 2 - 2 * e8BasisNormSum ≤ 2 * R + 2 + Real.sqrt 2 by linarith)
  have h3 : (R + Real.sqrt 2 + e8BasisNormSum) ^ 7 ≤ (2 * R) ^ 7 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 7
  have h4 : (2 * R + 2 + Real.sqrt 2) ^ 7 ≤ (3 * R) ^ 7 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 7
  have h5 : (R + Real.sqrt 2 + e8BasisNormSum) ^ 8 - R ^ 8 ≤
      8 * (Real.sqrt 2 + e8BasisNormSum) * (2 * R) ^ 7 := by
    have e : R + Real.sqrt 2 + e8BasisNormSum - R = Real.sqrt 2 + e8BasisNormSum := by ring
    rw [e] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
  have h6 : (2 * R + 2 + Real.sqrt 2) ^ 8 - (2 * R + 2 - 2 * e8BasisNormSum) ^ 8 ≤
      8 * (Real.sqrt 2 + 2 * e8BasisNormSum) * (3 * R) ^ 7 := by
    have e : 2 * R + 2 + Real.sqrt 2 - (2 * R + 2 - 2 * e8BasisNormSum) =
        Real.sqrt 2 + 2 * e8BasisNormSum := by ring
    rw [e] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left h4 (by positivity))
  have h7 : 0 ≤ (R + Real.sqrt 2 + e8BasisNormSum) ^ 8 - R ^ 8 :=
    sub_nonneg.mpr (pow_le_pow_left₀ hR0 (by linarith) 8)
  have h8 : 0 ≤ (2 * R + 2 + Real.sqrt 2) ^ 8 - (2 * R + 2 - 2 * e8BasisNormSum) ^ 8 :=
    sub_nonneg.mpr (pow_le_pow_left₀ (by linarith) (by linarith) 8)
  unfold windowBound
  rw [hball, hball']
  constructor
  · have h9 : ((R + Real.sqrt 2 + e8BasisNormSum) ^ 8 - R ^ 8) *
        volume.real (ball (0 : Ambient 8) 1) ≤
        8 * (Real.sqrt 2 + e8BasisNormSum) * (2 * R) ^ 7 * volume.real (ball (0 : Ambient 8) 1) :=
      mul_le_mul_of_nonneg_right h5 hω
    have e : stabilityK * R ^ 7 =
        8 * (Real.sqrt 2 + e8BasisNormSum) * (2 * R) ^ 7 * volume.real (ball (0 : Ambient 8) 1) +
          8 * (Real.sqrt 2 + 2 * e8BasisNormSum) * (3 * R) ^ 7 := by
      unfold stabilityK
      ring
    rw [e]
    linarith
  · have h9 : 0 ≤ ((R + Real.sqrt 2 + e8BasisNormSum) ^ 8 - R ^ 8) *
        volume.real (ball (0 : Ambient 8) 1) := mul_nonneg h7 hω
    linarith

/-- The constant of the even shells is at most exponential in the radius. -/
theorem alpha_le_exp {ρ R α : ℝ} (hρ : 0 < ρ) (hR : 1 ≤ R)
    (hα : α ≤ ρ * (2 * R) ^ (3 / 2 : ℝ) * Real.exp (5 * Real.pi * (2 * R) / 4)) :
    α ≤ 4 * ρ * Real.exp (12 * R) := by
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have h1 : (2 * R) ^ (3 / 2 : ℝ) ≤ (2 * R) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h2 : (2 * R) ^ (2 : ℝ) = (2 * R) ^ 2 := Real.rpow_two _
  have h3 : (2 * R) ^ 2 ≤ 4 * Real.exp (2 * R) := by
    have h := pow_le_exp_mul hR0 2
    have e : ((2 : ℕ) : ℝ) * R = 2 * R := by norm_num
    rw [e] at h
    nlinarith
  have h4 : Real.exp (5 * Real.pi * (2 * R) / 4) ≤ Real.exp (10 * R) := by
    apply Real.exp_le_exp.mpr
    have hpi := Real.pi_le_four
    nlinarith
  have h5 : (2 * R) ^ (3 / 2 : ℝ) ≤ 4 * Real.exp (2 * R) := h1.trans (h2.le.trans h3)
  calc α ≤ ρ * (2 * R) ^ (3 / 2 : ℝ) * Real.exp (5 * Real.pi * (2 * R) / 4) := hα
    _ ≤ ρ * (4 * Real.exp (2 * R)) * Real.exp (10 * R) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h5 hρ.le) h4 (Real.exp_pos _).le
          (mul_nonneg hρ.le (by positivity))
    _ = 4 * ρ * Real.exp (12 * R) := by
        rw [show (12 : ℝ) * R = 2 * R + 10 * R by ring, Real.exp_add]
        ring

section Exponents

variable {Rη R q : ℝ}

theorem stability_small (hRη : 1 ≤ Rη) (hR : Rη ≤ R) (hR13 : R ≤ 13 * Rη) (hq0 : 0 ≤ q)
    (hq : q ≤ Real.exp (-(200 * Rη))) : Real.exp (12 * R) * q * R ^ 2 ≤ 1 / Rη := by
  have hR0 : 0 ≤ R := by linarith
  have h1 : R ^ 2 ≤ Real.exp (2 * R) := by
    have h := pow_le_exp_mul hR0 2
    have e : ((2 : ℕ) : ℝ) * R = 2 * R := by norm_num
    rwa [e] at h
  have h2 : Real.exp (12 * R) * R ^ 2 ≤ Real.exp (182 * Rη) := by
    calc Real.exp (12 * R) * R ^ 2 ≤ Real.exp (12 * R) * Real.exp (2 * R) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = Real.exp (14 * R) := by
          rw [← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (182 * Rη) := Real.exp_le_exp.mpr (by linarith)
  calc Real.exp (12 * R) * q * R ^ 2 = (Real.exp (12 * R) * R ^ 2) * q := by ring
    _ ≤ Real.exp (182 * Rη) * Real.exp (-(200 * Rη)) :=
        mul_le_mul h2 hq hq0 (Real.exp_pos _).le
    _ = Real.exp (-(18 * Rη)) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (-Rη) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ 1 / Rη := exp_neg_le_inv (by linarith)

theorem stability_error (hRη : 1 ≤ Rη) (hR : Rη ≤ R) (hR13 : R ≤ 13 * Rη) :
    Real.exp (12 * R) * R ≤ Real.exp (169 * Rη) := by
  have hR0 : 0 ≤ R := by linarith
  calc Real.exp (12 * R) * R ≤ Real.exp (12 * R) * Real.exp R :=
        mul_le_mul_of_nonneg_left (le_exp_self R) (Real.exp_pos _).le
    _ = Real.exp (13 * R) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (169 * Rη) := Real.exp_le_exp.mpr (by linarith)

theorem stability_sq (hRη : 1 ≤ Rη) (hR : Rη ≤ R) (hR13 : R ≤ 13 * Rη) (hq0 : 0 ≤ q)
    (hq : q ≤ Real.exp (-(200 * Rη))) : q ^ 2 * R ^ 8 ≤ 1 / (Rη * Rη) := by
  have hR0 : 0 ≤ R := by linarith
  have hRη0 : 0 < Rη := by linarith
  have h1 : R ^ 8 ≤ Real.exp (104 * Rη) := by
    have h := pow_le_exp_mul hR0 8
    have e : ((8 : ℕ) : ℝ) * R = 8 * R := by norm_num
    rw [e] at h
    exact h.trans (Real.exp_le_exp.mpr (by linarith))
  have h2 : q ^ 2 ≤ Real.exp (-(400 * Rη)) := by
    have h := pow_le_pow_left₀ hq0 hq 2
    rw [← Real.exp_nat_mul] at h
    have e : ((2 : ℕ) : ℝ) * -(200 * Rη) = -(400 * Rη) := by norm_num; ring
    rwa [e] at h
  have h3 : Real.exp (-Rη) ≤ 1 / Rη := exp_neg_le_inv hRη0
  have h4 : (0 : ℝ) ≤ Real.exp (-Rη) := (Real.exp_pos _).le
  calc q ^ 2 * R ^ 8 ≤ Real.exp (-(400 * Rη)) * Real.exp (104 * Rη) :=
        mul_le_mul h2 h1 (by positivity) (Real.exp_pos _).le
    _ = Real.exp (-(296 * Rη)) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (-Rη + -Rη) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-Rη) * Real.exp (-Rη) := Real.exp_add _ _
    _ ≤ 1 / Rη * (1 / Rη) := mul_le_mul h3 h3 h4 (by positivity)
    _ = 1 / (Rη * Rη) := by
        field_simp

theorem stability_fourth (hRη : 1 ≤ Rη) (hq0 : 0 ≤ q) (hq : q ≤ Real.exp (-(200 * Rη))) :
    q ^ 4 ≤ 1 / Rη := by
  have hRη0 : 0 < Rη := by linarith
  have h := pow_le_pow_left₀ hq0 hq 4
  rw [← Real.exp_nat_mul] at h
  exact h.trans ((Real.exp_le_exp.mpr (by push_cast; linarith)).trans (exp_neg_le_inv hRη0))

end Exponents

/-- **The probability estimate of the periodic stability input**, in real variables. -/
theorem stability_measure_bound {ω K B Rη R lam V U η s : ℝ} (hω : 0 < ω) (hK : 0 ≤ K)
    (hB : B = K / ω + 2) (hRη1 : 1 ≤ Rη) (hRηω : 3 * ω ≤ Rη) (hR : Rη ≤ R) (hlam0 : 0 < lam)
    (hlam : lam * lam = 1 / Rη) (hV : V = R ^ 8 * ω) (hUV : U - V ≤ K * R ^ 7) (hVU : V ≤ U)
    (hsη : η ≤ s) (hsR : s * R ^ 8 ≤ 1 / (Rη * Rη)) (hηR : η ≤ 1 / Rη) :
    2 * s * V + η * V + (U - (1 - η) * V) / (U - (1 - B * lam) * V) ≤ B * lam := by
  have hRη0 : 0 < Rη := by linarith
  have hR0 : 0 < R := by linarith
  have hKω : 0 ≤ K / ω := div_nonneg hK hω.le
  have hB2 : 2 ≤ B := by rw [hB]; linarith
  have hR8 : 0 < R ^ 8 := pow_pos hR0 8
  have hV0 : 0 < V := by rw [hV]; exact mul_pos hR8 hω
  have hll : lam * lam ≤ 1 := by
    rw [hlam, div_le_one hRη0]
    exact hRη1
  have hlam1 : lam ≤ 1 := by nlinarith
  have hll2 : lam * lam ≤ lam := by nlinarith
  -- the first two terms
  have h1 : 2 * s * V + η * V ≤ lam := by
    have h2 : 2 * s * V + η * V ≤ 3 * (s * R ^ 8) * ω := by
      rw [hV]
      have h3 : η * (R ^ 8 * ω) ≤ s * (R ^ 8 * ω) :=
        mul_le_mul_of_nonneg_right hsη (mul_pos hR8 hω).le
      nlinarith
    have h4 : 3 * (s * R ^ 8) * ω ≤ 3 * (1 / (Rη * Rη)) * ω := by
      have h5 := mul_le_mul_of_nonneg_right hsR hω.le
      nlinarith
    have h6 : 3 * (1 / (Rη * Rη)) * ω = (3 * ω / Rη) * (lam * lam) := by
      rw [hlam]
      field_simp
    have h7 : 3 * ω / Rη ≤ 1 := by
      rw [div_le_one hRη0]
      exact hRηω
    have h8 : (3 * ω / Rη) * (lam * lam) ≤ 1 * (lam * lam) :=
      mul_le_mul_of_nonneg_right h7 (mul_self_nonneg lam)
    linarith
  -- the ratio
  have hR7 : R ^ 7 ≤ lam * lam * R ^ 8 := by
    rw [hlam]
    have h2 : (1 : ℝ) ≤ R / Rη := (one_le_div hRη0).mpr hR
    have h3 : 1 / Rη * R ^ 8 = R ^ 7 * (R / Rη) := by
      field_simp
    rw [h3]
    nlinarith [pow_pos hR0 7]
  have hnum : U - (1 - η) * V ≤ lam * lam * (R ^ 8 * (K + ω)) := by
    have h2 : η * V ≤ lam * lam * V := by
      rw [hlam]
      exact mul_le_mul_of_nonneg_right hηR hV0.le
    have h3 : K * R ^ 7 ≤ K * (lam * lam * R ^ 8) := mul_le_mul_of_nonneg_left hR7 hK
    rw [hV] at h2
    have e : U - (1 - η) * V = (U - V) + η * V := by ring
    rw [e, hV]
    rw [hV] at hUV
    nlinarith
  have hden : B * lam * (R ^ 8 * ω) ≤ U - (1 - B * lam) * V := by
    have e : U - (1 - B * lam) * V = (U - V) + B * lam * V := by ring
    rw [e, hV]
    rw [hV] at hVU
    linarith
  have hBV : 0 < B * lam * (R ^ 8 * ω) := by positivity
  have hden0 : 0 < U - (1 - B * lam) * V := lt_of_lt_of_le hBV hden
  have h2 : (U - (1 - η) * V) / (U - (1 - B * lam) * V) ≤ lam * (B - 1) := by
    rw [div_le_iff₀ hden0]
    have hωB : ω * (B - 1) = K + ω := by
      rw [hB]
      field_simp
      ring
    have h3 : lam * (B - 1) * (B * lam * (R ^ 8 * ω)) ≤
        lam * (B - 1) * (U - (1 - B * lam) * V) :=
      mul_le_mul_of_nonneg_left hden (by nlinarith)
    have h4 : lam * (B - 1) * (B * lam * (R ^ 8 * ω)) = B * (lam * lam * (R ^ 8 * (K + ω))) := by
      rw [← hωB]
      ring
    have h5 : lam * lam * (R ^ 8 * (K + ω)) ≤ B * (lam * lam * (R ^ 8 * (K + ω))) := by
      have h6 : 0 ≤ lam * lam * (R ^ 8 * (K + ω)) := by positivity
      nlinarith
    linarith
  nlinarith

end E8Leech
