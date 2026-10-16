import E8Leech.StabilityConstants
import E8Leech.LeechCountProbability
import E8Leech.LocalLeechLattice

/-!
# Elementary estimates for the constants of the periodic stability input in dimension 24

The rank 24 version of `StabilityConstants`: real-variable inequalities used to turn
`leech_periodic_window_structure` into the periodic stability input with the error
`E·exp(c·R_η)·η^{1/4}` and the loss `B·R_η^{-1/2}`.

* `pow_succ_sub_pow_succ_le`: `x^(n+1) - y^(n+1) ≤ (n+1)(x-y)xⁿ`.
* `leechWindowBound_sub_volume_le`: `leechWindowBound R - vol(B_R) ≤ K R²³` and
  `vol(B_R) ≤ leechWindowBound R`.
* `leech_alpha_le_exp`: the constant of the even shells is at most `64 ρ exp(16 R)`.
* `stability_measure_bound_pow`: the probability estimate in a general dimension.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric

/-- `x^(n+1) - y^(n+1) ≤ (n+1) (x - y) xⁿ` for `0 ≤ y ≤ x`. -/
theorem pow_succ_sub_pow_succ_le {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (n : ℕ) :
    x ^ (n + 1) - y ^ (n + 1) ≤ ((n + 1 : ℕ) : ℝ) * (x - y) * x ^ n := by
  have hx : 0 ≤ x := hy.trans hxy
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : y ^ (n + 1) ≤ x ^ (n + 1) := pow_le_pow_left₀ hy hxy _
    have e : x ^ (n + 1 + 1) - y ^ (n + 1 + 1) =
        x * (x ^ (n + 1) - y ^ (n + 1)) + (x - y) * y ^ (n + 1) := by ring
    have h2 : x * (x ^ (n + 1) - y ^ (n + 1)) ≤ x * (((n + 1 : ℕ) : ℝ) * (x - y) * x ^ n) :=
      mul_le_mul_of_nonneg_left ih hx
    have h3 : (x - y) * y ^ (n + 1) ≤ (x - y) * x ^ (n + 1) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    rw [e]
    calc x * (x ^ (n + 1) - y ^ (n + 1)) + (x - y) * y ^ (n + 1)
        ≤ x * (((n + 1 : ℕ) : ℝ) * (x - y) * x ^ n) + (x - y) * x ^ (n + 1) := add_le_add h2 h3
      _ = ((n + 1 + 1 : ℕ) : ℝ) * (x - y) * x ^ (n + 1) := by
          push_cast
          ring

/-- `x²⁴ - y²⁴ ≤ 24 (x - y) x²³` for `0 ≤ y ≤ x`. -/
theorem pow_twentyFour_sub_le {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) :
    x ^ 24 - y ^ 24 ≤ 24 * (x - y) * x ^ 23 := by
  have h := pow_succ_sub_pow_succ_le hy hxy 23
  norm_num at h
  linarith

/-- The constant of the local count in dimension 24:
`leechWindowBound R - vol(B_R) ≤ leechStabilityK · R²³`. -/
def leechStabilityK : ℝ :=
  24 * (2 + leechBasisNormSum) * 2 ^ 23 * volume.real (ball (0 : Ambient 24) 1) +
    24 * (2 + 2 * leechBasisNormSum) * 3 ^ 23

theorem leechStabilityK_nonneg : 0 ≤ leechStabilityK := by
  have h1 := leechBasisNormSum_nonneg
  have h3 := volume_real_unitBall_twentyFour_pos.le
  unfold leechStabilityK
  positivity

/-- The linear arithmetic of `leechWindowBound_sub_volume_le`, with the powers as variables. -/
theorem windowBound_arith {a b c d ω X Y : ℝ} (h5 : a - b ≤ X) (h6 : c - d ≤ Y)
    (h7 : 0 ≤ a - b) (h8 : 0 ≤ c - d) (hω : 0 ≤ ω) :
    a * ω + (c - d) - b * ω ≤ X * ω + Y ∧ b * ω ≤ a * ω + (c - d) := by
  have h9 : (a - b) * ω ≤ X * ω := mul_le_mul_of_nonneg_right h5 hω
  have h10 : 0 ≤ (a - b) * ω := mul_nonneg h7 hω
  constructor <;> linarith

theorem leechWindowBound_sub_volume_le {R : ℝ} (hR : leechBasisNormSum + 4 ≤ R) :
    leechWindowBound R - volume.real (closedBall (0 : Ambient 24) R) ≤
        leechStabilityK * R ^ 23 ∧
      volume.real (closedBall (0 : Ambient 24) R) ≤ leechWindowBound R := by
  have hρ := leechBasisNormSum_nonneg
  have hω := volume_real_unitBall_twentyFour_pos.le
  -- the linear facts, before any power enters the context
  have hR0 : 0 ≤ R := by linarith
  have ha0 : 0 ≤ R + 2 + leechBasisNormSum := by linarith
  have hab : R ≤ R + 2 + leechBasisNormSum := by linarith
  have ha2 : R + 2 + leechBasisNormSum ≤ 2 * R := by linarith
  have hd0 : 0 ≤ 2 * R + 2 - 2 * leechBasisNormSum := by linarith
  have hdc : 2 * R + 2 - 2 * leechBasisNormSum ≤ 2 * R + 4 := by linarith
  have hc0 : 0 ≤ 2 * R + 4 := by linarith
  have hc3 : 2 * R + 4 ≤ 3 * R := by linarith
  have hk1 : 0 ≤ 24 * (2 + leechBasisNormSum) := by linarith
  have hk2 : 0 ≤ 24 * (2 + 2 * leechBasisNormSum) := by linarith
  have e1 : R + 2 + leechBasisNormSum - R = 2 + leechBasisNormSum := by ring
  have e2 : 2 * R + 4 - (2 * R + 2 - 2 * leechBasisNormSum) = 2 + 2 * leechBasisNormSum := by
    ring
  have hball : volume.real (closedBall (0 : Ambient 24) R) =
      R ^ 24 * volume.real (ball (0 : Ambient 24) 1) := volume_real_closedBall_twentyFour 0 hR0
  have hball' : volume.real (closedBall (0 : Ambient 24) (R + 2 + leechBasisNormSum)) =
      (R + 2 + leechBasisNormSum) ^ 24 * volume.real (ball (0 : Ambient 24) 1) :=
    volume_real_closedBall_twentyFour 0 ha0
  -- the two differences of 24th powers
  have h5 : (R + 2 + leechBasisNormSum) ^ 24 - R ^ 24 ≤
      24 * (2 + leechBasisNormSum) * (2 * R) ^ 23 := by
    have h1 := pow_twentyFour_sub_le hR0 hab
    rw [e1] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha0 ha2 23) hk1)
  have h6 : (2 * R + 4) ^ 24 - (2 * R + 2 - 2 * leechBasisNormSum) ^ 24 ≤
      24 * (2 + 2 * leechBasisNormSum) * (3 * R) ^ 23 := by
    have h2 := pow_twentyFour_sub_le hd0 hdc
    rw [e2] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc0 hc3 23) hk2)
  have h7 : 0 ≤ (R + 2 + leechBasisNormSum) ^ 24 - R ^ 24 :=
    sub_nonneg.mpr (pow_le_pow_left₀ hR0 hab 24)
  have h8 : 0 ≤ (2 * R + 4) ^ 24 - (2 * R + 2 - 2 * leechBasisNormSum) ^ 24 :=
    sub_nonneg.mpr (pow_le_pow_left₀ hd0 hdc 24)
  obtain ⟨hA, hB⟩ := windowBound_arith h5 h6 h7 h8 hω
  have e : leechStabilityK * R ^ 23 =
      24 * (2 + leechBasisNormSum) * (2 * R) ^ 23 * volume.real (ball (0 : Ambient 24) 1) +
        24 * (2 + 2 * leechBasisNormSum) * (3 * R) ^ 23 := by
    unfold leechStabilityK
    ring
  unfold leechWindowBound
  rw [hball, hball', e]
  exact ⟨hA, hB⟩

/-- The constant of the even shells in dimension 24 is at most exponential in the radius. -/
theorem leech_alpha_le_exp {ρ R α : ℝ} (hρ : 0 < ρ) (hR : 1 ≤ R)
    (hα : α ≤ ρ * (2 * R) ^ (11 / 2 : ℝ) * Real.exp (5 * Real.pi * (2 * R) / 4)) :
    α ≤ 64 * ρ * Real.exp (16 * R) := by
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have h1 : (2 * R) ^ (11 / 2 : ℝ) ≤ (2 * R) ^ (6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h2 : (2 * R) ^ (6 : ℝ) = (2 * R) ^ 6 := by
    exact_mod_cast Real.rpow_natCast (2 * R) 6
  have h3 : (2 * R) ^ 6 ≤ 64 * Real.exp (6 * R) := by
    have h := pow_le_exp_mul hR0 6
    have e : ((6 : ℕ) : ℝ) * R = 6 * R := by norm_num
    rw [e] at h
    have e2 : (2 * R) ^ 6 = 64 * R ^ 6 := by ring
    rw [e2]
    linarith
  have h4 : Real.exp (5 * Real.pi * (2 * R) / 4) ≤ Real.exp (10 * R) := by
    apply Real.exp_le_exp.mpr
    have hpi := Real.pi_le_four
    nlinarith
  have h5 : (2 * R) ^ (11 / 2 : ℝ) ≤ 64 * Real.exp (6 * R) := h1.trans (h2.le.trans h3)
  calc α ≤ ρ * (2 * R) ^ (11 / 2 : ℝ) * Real.exp (5 * Real.pi * (2 * R) / 4) := hα
    _ ≤ ρ * (64 * Real.exp (6 * R)) * Real.exp (10 * R) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h5 hρ.le) h4 (Real.exp_pos _).le
          (mul_nonneg hρ.le (by positivity))
    _ = 64 * ρ * Real.exp (16 * R) := by
        rw [show (16 : ℝ) * R = 6 * R + 10 * R by ring, Real.exp_add]
        ring

section LeechExponents

variable {Rη R q : ℝ}

theorem leech_stability_small (hRη : 1 ≤ Rη) (hR : Rη ≤ R) (hR13 : R ≤ 13 * Rη) (hq0 : 0 ≤ q)
    (hq : q ≤ Real.exp (-(400 * Rη))) : Real.exp (16 * R) * q * R ^ 2 ≤ 1 / Rη := by
  have hR0 : 0 ≤ R := by linarith
  have h1 : R ^ 2 ≤ Real.exp (2 * R) := by
    have h := pow_le_exp_mul hR0 2
    have e : ((2 : ℕ) : ℝ) * R = 2 * R := by norm_num
    rwa [e] at h
  have h2 : Real.exp (16 * R) * R ^ 2 ≤ Real.exp (234 * Rη) := by
    calc Real.exp (16 * R) * R ^ 2 ≤ Real.exp (16 * R) * Real.exp (2 * R) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = Real.exp (18 * R) := by
          rw [← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (234 * Rη) := Real.exp_le_exp.mpr (by linarith)
  calc Real.exp (16 * R) * q * R ^ 2 = (Real.exp (16 * R) * R ^ 2) * q := by ring
    _ ≤ Real.exp (234 * Rη) * Real.exp (-(400 * Rη)) :=
        mul_le_mul h2 hq hq0 (Real.exp_pos _).le
    _ = Real.exp (-(166 * Rη)) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (-Rη) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ 1 / Rη := exp_neg_le_inv (by linarith)

theorem leech_stability_error (hRη : 1 ≤ Rη) (hR : Rη ≤ R) (hR13 : R ≤ 13 * Rη) :
    Real.exp (16 * R) * R ≤ Real.exp (221 * Rη) := by
  have hR0 : 0 ≤ R := by linarith
  calc Real.exp (16 * R) * R ≤ Real.exp (16 * R) * Real.exp R :=
        mul_le_mul_of_nonneg_left (le_exp_self R) (Real.exp_pos _).le
    _ = Real.exp (17 * R) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (221 * Rη) := Real.exp_le_exp.mpr (by linarith)

theorem leech_stability_sq (hRη : 1 ≤ Rη) (hR : Rη ≤ R) (hR13 : R ≤ 13 * Rη) (hq0 : 0 ≤ q)
    (hq : q ≤ Real.exp (-(400 * Rη))) : q ^ 2 * R ^ 24 ≤ 1 / (Rη * Rη) := by
  have hR0 : 0 ≤ R := by linarith
  have hRη0 : 0 < Rη := by linarith
  have h1 : R ^ 24 ≤ Real.exp (312 * Rη) := by
    have h := pow_le_exp_mul hR0 24
    have e : ((24 : ℕ) : ℝ) * R = 24 * R := by norm_num
    rw [e] at h
    exact h.trans (Real.exp_le_exp.mpr (by linarith))
  have h2 : q ^ 2 ≤ Real.exp (-(800 * Rη)) := by
    have h := pow_le_pow_left₀ hq0 hq 2
    rw [← Real.exp_nat_mul] at h
    have e : ((2 : ℕ) : ℝ) * -(400 * Rη) = -(800 * Rη) := by norm_num; ring
    rwa [e] at h
  have h3 : Real.exp (-Rη) ≤ 1 / Rη := exp_neg_le_inv hRη0
  have h4 : (0 : ℝ) ≤ Real.exp (-Rη) := (Real.exp_pos _).le
  calc q ^ 2 * R ^ 24 ≤ Real.exp (-(800 * Rη)) * Real.exp (312 * Rη) :=
        mul_le_mul h2 h1 (by positivity) (Real.exp_pos _).le
    _ = Real.exp (-(488 * Rη)) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (-Rη + -Rη) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-Rη) * Real.exp (-Rη) := Real.exp_add _ _
    _ ≤ 1 / Rη * (1 / Rη) := mul_le_mul h3 h3 h4 (by positivity)
    _ = 1 / (Rη * Rη) := by
        field_simp

theorem leech_stability_fourth (hRη : 1 ≤ Rη) (hq0 : 0 ≤ q)
    (hq : q ≤ Real.exp (-(400 * Rη))) : q ^ 4 ≤ 1 / Rη := by
  have hRη0 : 0 < Rη := by linarith
  have h := pow_le_pow_left₀ hq0 hq 4
  rw [← Real.exp_nat_mul] at h
  exact h.trans ((Real.exp_le_exp.mpr (by push_cast; linarith)).trans (exp_neg_le_inv hRη0))

end LeechExponents

/-- **The probability estimate of the periodic stability input**, in real variables, for a
general dimension `n + 1`. -/
theorem stability_measure_bound_pow (n : ℕ) {ω K B Rη R lam V U η s : ℝ} (hω : 0 < ω) (hK : 0 ≤ K)
    (hB : B = K / ω + 2) (hRη1 : 1 ≤ Rη) (hRηω : 3 * ω ≤ Rη) (hR : Rη ≤ R) (hlam0 : 0 < lam)
    (hlam : lam * lam = 1 / Rη) (hV : V = R ^ (n + 1) * ω) (hUV : U - V ≤ K * R ^ n) (hVU : V ≤ U)
    (hsη : η ≤ s) (hsR : s * R ^ (n + 1) ≤ 1 / (Rη * Rη)) (hηR : η ≤ 1 / Rη) :
    2 * s * V + η * V + (U - (1 - η) * V) / (U - (1 - B * lam) * V) ≤ B * lam := by
  have hRη0 : 0 < Rη := by linarith
  have hR0 : 0 < R := by linarith
  have hKω : 0 ≤ K / ω := div_nonneg hK hω.le
  have hB2 : 2 ≤ B := by rw [hB]; linarith
  have hR8 : 0 < R ^ (n + 1) := pow_pos hR0 (n + 1)
  have hV0 : 0 < V := by rw [hV]; exact mul_pos hR8 hω
  have hll : lam * lam ≤ 1 := by
    rw [hlam, div_le_one hRη0]
    exact hRη1
  have hlam1 : lam ≤ 1 := by nlinarith
  have hll2 : lam * lam ≤ lam := by nlinarith
  -- the first two terms
  have h1 : 2 * s * V + η * V ≤ lam := by
    have h2 : 2 * s * V + η * V ≤ 3 * (s * R ^ (n + 1)) * ω := by
      rw [hV]
      have h3 : η * (R ^ (n + 1) * ω) ≤ s * (R ^ (n + 1) * ω) :=
        mul_le_mul_of_nonneg_right hsη (mul_pos hR8 hω).le
      nlinarith
    have h4 : 3 * (s * R ^ (n + 1)) * ω ≤ 3 * (1 / (Rη * Rη)) * ω := by
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
  have hR7 : R ^ n ≤ lam * lam * R ^ (n + 1) := by
    rw [hlam]
    have h2 : (1 : ℝ) ≤ R / Rη := (one_le_div hRη0).mpr hR
    have h3 : 1 / Rη * R ^ (n + 1) = R ^ n * (R / Rη) := by ring
    rw [h3]
    nlinarith [pow_pos hR0 n]
  have hnum : U - (1 - η) * V ≤ lam * lam * (R ^ (n + 1) * (K + ω)) := by
    have h2 : η * V ≤ lam * lam * V := by
      rw [hlam]
      exact mul_le_mul_of_nonneg_right hηR hV0.le
    have h3 : K * R ^ n ≤ K * (lam * lam * R ^ (n + 1)) := mul_le_mul_of_nonneg_left hR7 hK
    rw [hV] at h2
    have e : U - (1 - η) * V = (U - V) + η * V := by ring
    rw [e, hV]
    rw [hV] at hUV
    nlinarith
  have hden : B * lam * (R ^ (n + 1) * ω) ≤ U - (1 - B * lam) * V := by
    have e : U - (1 - B * lam) * V = (U - V) + B * lam * V := by ring
    rw [e, hV]
    rw [hV] at hVU
    linarith
  have hBV : 0 < B * lam * (R ^ (n + 1) * ω) := by positivity
  have hden0 : 0 < U - (1 - B * lam) * V := lt_of_lt_of_le hBV hden
  have h2 : (U - (1 - η) * V) / (U - (1 - B * lam) * V) ≤ lam * (B - 1) := by
    rw [div_le_iff₀ hden0]
    have hωB : ω * (B - 1) = K + ω := by
      rw [hB]
      field_simp
      ring
    have h3 : lam * (B - 1) * (B * lam * (R ^ (n + 1) * ω)) ≤
        lam * (B - 1) * (U - (1 - B * lam) * V) :=
      mul_le_mul_of_nonneg_left hden (by nlinarith)
    have h4 : lam * (B - 1) * (B * lam * (R ^ (n + 1) * ω)) =
        B * (lam * lam * (R ^ (n + 1) * (K + ω))) := by
      rw [← hωB]
      ring
    have h5 : lam * lam * (R ^ (n + 1) * (K + ω)) ≤ B * (lam * lam * (R ^ (n + 1) * (K + ω))) := by
      have h6 : 0 ≤ lam * lam * (R ^ (n + 1) * (K + ω)) := by positivity
      nlinarith
    linarith
  nlinarith

end E8Leech
