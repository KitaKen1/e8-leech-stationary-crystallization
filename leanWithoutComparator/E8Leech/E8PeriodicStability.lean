import E8Leech.StabilityConstants
import E8Leech.SectionwiseBRR
import E8Leech.E8KernelPositivity
import E8Leech.E8MagicExponentialBounds
import E8Leech.LatticeDistance

/-!
# The periodic stability input for `E8` and the unconditional `E8` crystallization theorem

`e8_sectionwisePeriodicStabilityInput` proves the periodic stability input for `E8` (Theorem 1.5
of Böröczky–Radchenko–Ramos in the form used by this development): for a configuration whose
guarded periodization has density deficit `η < η₀`, outside a set of observation centres of
probability at most `B R_η^{-1/2}` the periodization is a local crystal of `E8` on the ball of
radius `R`, with error `E exp(c R_η) η^{1/4}` and loss `B R_η^{-1/2}`.

Together with the analytic input for `E8` (`e8_analyticUnitCostInput`) this gives the stationary
crystallization target for `E8` without hypotheses: `e8CrystallizationTarget_holds`.

* `e8_centres_of_window`: from `e8_periodic_window_structure` to `LocalCrystal` and the bound for
  the exceptional set, with the numerical conditions as hypotheses.
* `e8_sectionwisePeriodicStabilityInput`: the constants `E = 184ρ`, `c = 169`,
  `B = K/ω + 2` and `η₀ = exp(-(exp 800 + 4R₀²))`.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric Set SpherePacking
open scoped ENNReal

/-- The count of a configuration in a ball is the count of the centres of a periodic packing with
the same support. -/
theorem count_closedBall_eq_periodicCentreCount {d : ℕ} (P : PeriodicSpherePacking d)
    (cfg : Configuration (Ambient d)) (hsupp : cfg.support = P.centers) (u : Ambient d) (R : ℝ) :
    cfg.count (closedBall u R) = periodicCentreCount P R u := by
  have hfin := finite_centers_inter_closedBall P u R
  rw [periodicCentreCount_eq_card P R u hfin.toFinset (fun x => hfin.mem_toFinset),
    Configuration.count_eq_encard, hsupp, hfin.encard_eq_coe_toFinset_card]
  rfl

/-- From the periodic local structure to `LocalCrystal`, with the numerical conditions as
hypotheses. -/
theorem e8_centres_of_window {P : PeriodicSpherePacking 8} (cfg : Configuration (Ambient 8))
    (hsupp : cfg.support = P.centers) {L : ℝ} (hP : Real.sqrt 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ periodCell 8 L) {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hε : 1 - η ≤ (P.numReps' (by norm_num) (isBounded_periodCell 8 L) : ℝ) /
      ZLattice.covolume P.lattice volume)
    {R α loss err bound : ℝ} (hR : 6000 ≤ R) (hRρ : e8BasisNormSum ≤ R) (hα0 : 0 ≤ α)
    (hshell : ∀ x : Ambient 8, Real.sqrt 2 ≤ ‖x‖ → ‖x‖ ≤ 2 * R →
      ∃ k : ℤ, 1 ≤ k ∧ |‖x‖ ^ 2 - 2 * k| ≤ α * Real.sqrt |(_root_.g x).re|)
    (hsmall : α * η ^ (1 / 4 : ℝ) * R ^ 2 ≤ 1 / 10 ^ 29) (hloss : loss ≤ 1 / 10)
    (hVU : volume.real (closedBall (0 : Ambient 8) R) ≤ windowBound R)
    (htU : (1 - loss) * volume.real (closedBall (0 : Ambient 8) R) < windowBound R)
    (herr : 46 * (α * η ^ (1 / 4 : ℝ)) * R ≤ err)
    (hbound : 2 * Real.sqrt η * volume.real (closedBall (0 : Ambient 8) R) +
      η * volume.real (closedBall (0 : Ambient 8) R) +
      (windowBound R - (1 - η) * volume.real (closedBall (0 : Ambient 8) R)) /
        (windowBound R - (1 - loss) * volume.real (closedBall (0 : Ambient 8) R)) ≤ bound) :
    ∃ S : Set (Ambient 8),
      (∀ u, u ∉ S → LocalCrystal e8Set (translate (-u) cfg) R err loss) ∧
        uniformPeriodCell 8 L S ≤ ENNReal.ofReal bound := by
  have hV0 : 0 ≤ volume.real (closedBall (0 : Ambient 8) R) := measureReal_nonneg
  -- the packing is not empty
  have hne : P.centers.Nonempty := by
    by_contra hcon
    have hempty : P.centers = ∅ := Set.not_nonempty_iff_eq_empty.mp hcon
    have h0 : P.numReps' (by norm_num) (isBounded_periodCell 8 L) = 0 := by
      rw [numReps'_eq_ncard, hempty, Set.empty_inter, Set.ncard_empty]
    rw [h0] at hε
    norm_num at hε
    linarith
  have ht9 : 9 / 10 * volume.real (closedBall (0 : Ambient 8) R) ≤
      (1 - loss) * volume.real (closedBall (0 : Ambient 8) R) :=
    mul_le_mul_of_nonneg_right (by linarith) hV0
  obtain ⟨S, hSm, hS⟩ := e8_periodic_window_structure (isBounded_periodCell 8 L)
    (measurable_periodCell 8 L) hP hD hne hη hη1.le hε hR hRρ hα0 hshell hsmall ht9 htU
  have hvol : volume (closedBall (0 : Ambient 8) R) =
      ENNReal.ofReal (volume.real (closedBall (0 : Ambient 8) R)) :=
    (ENNReal.ofReal_toReal measure_closedBall_lt_top.ne).symm
  refine ⟨S, fun u hu => ?_, ?_⟩
  · obtain ⟨⟨Φ, p₀, hnear⟩, hcnt⟩ := hS u hu
    refine localCrystal_translate_of_window cfg u Φ p₀ (fun x hx => ?_) ?_
    · rw [hsupp] at hx
      obtain ⟨z', hz', hd⟩ := hnear x hx
      exact ⟨z', hz', hd.trans herr⟩
    · rw [count_closedBall_eq_periodicCentreCount P cfg hsupp u R]
      refine le_trans (le_of_eq ?_) hcnt
      rw [ENNReal.ofReal_mul (by linarith), ← hvol]
  · have hratio0 : 0 ≤ (windowBound R - (1 - η) * volume.real (closedBall (0 : Ambient 8) R)) /
        (windowBound R - (1 - loss) * volume.real (closedBall (0 : Ambient 8) R)) := by
      apply div_nonneg
      · have h1 : (1 - η) * volume.real (closedBall (0 : Ambient 8) R) ≤
            1 * volume.real (closedBall (0 : Ambient 8) R) :=
          mul_le_mul_of_nonneg_right (by linarith) hV0
        linarith
      · linarith
    have h1 : (0 : ℝ) ≤ 2 * Real.sqrt η * volume.real (closedBall (0 : Ambient 8) R) :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hV0
    have h2 : (0 : ℝ) ≤ η * volume.real (closedBall (0 : Ambient 8) R) := mul_nonneg hη.le hV0
    show uniformFundamentalDomain (periodCell 8 L) S ≤ ENNReal.ofReal bound
    refine hSm.trans ?_
    rw [hvol, ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)),
      ← ENNReal.ofReal_mul hη.le, ← ENNReal.ofReal_add h1 h2,
      ← ENNReal.ofReal_add (add_nonneg h1 h2) hratio0]
    exact ENNReal.ofReal_le_ofReal hbound

/-- The size of `η` below the threshold: `η^{1/4} ≤ exp(-200 R_η)` and `R_η ≥ R₀`. -/
theorem stability_eta_facts {R₀ η : ℝ} (hR₀ : 1 ≤ R₀) (hη : 0 < η)
    (hηη₀ : η < Real.exp (-(Real.exp 800 + 4 * R₀ ^ 2))) :
    η < 1 ∧ η ^ (1 / 4 : ℝ) ≤ Real.exp (-(200 * observationRadius η)) ∧
      R₀ ≤ observationRadius η := by
  have he800 : (0 : ℝ) < Real.exp 800 := Real.exp_pos _
  have hsqR₀ : 0 ≤ 4 * R₀ ^ 2 := by positivity
  have hη₀1 : Real.exp (-(Real.exp 800 + 4 * R₀ ^ 2)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hlogη : Real.exp 800 + 4 * R₀ ^ 2 < Real.log (1 / η) := by
    have h1 := Real.log_lt_log hη hηη₀
    rw [Real.log_exp] at h1
    rw [one_div, Real.log_inv]
    linarith
  refine ⟨hηη₀.trans hη₀1, ?_, ?_⟩
  · exact rpow_quarter_le_exp_neg hη (by norm_num : (0 : ℝ) < 200)
      (by rw [show (4 : ℝ) * 200 = 800 by norm_num]; linarith)
  · exact le_observationRadius hR₀ (by linarith)

/-- The smallness of the even-shell error and the size of the final error. -/
theorem stability_small_err {ρ Rη R q α : ℝ} (hρ : 0 < ρ) (hRη1 : 1 ≤ Rη) (hRηR : Rη ≤ R)
    (hR13 : R ≤ 13 * Rη) (hRηρ : 4 * ρ * 10 ^ 29 ≤ Rη) (hq0 : 0 ≤ q)
    (hq : q ≤ Real.exp (-(200 * Rη))) (hα' : α ≤ 4 * ρ * Real.exp (12 * R)) :
    α * q * R ^ 2 ≤ 1 / 10 ^ 29 ∧ 46 * (α * q) * R ≤ 184 * ρ * Real.exp (169 * Rη) * q := by
  have hRη0 : 0 < Rη := by linarith
  have hR0 : 0 ≤ R := by linarith
  constructor
  · have h1 := stability_small hRη1 hRηR hR13 hq0 hq
    have h2 : α * (q * R ^ 2) ≤ 4 * ρ * Real.exp (12 * R) * (q * R ^ 2) :=
      mul_le_mul_of_nonneg_right hα' (mul_nonneg hq0 (sq_nonneg R))
    have h3 : 4 * ρ * (1 / Rη) ≤ 1 / 10 ^ 29 := by
      rw [mul_one_div, div_le_div_iff₀ hRη0 (by positivity)]
      linarith
    calc α * q * R ^ 2 = α * (q * R ^ 2) := by ring
      _ ≤ 4 * ρ * Real.exp (12 * R) * (q * R ^ 2) := h2
      _ = 4 * ρ * (Real.exp (12 * R) * q * R ^ 2) := by ring
      _ ≤ 4 * ρ * (1 / Rη) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 1 / 10 ^ 29 := h3
  · have h1 := stability_error hRη1 hRηR hR13
    have h2 : α * R ≤ 4 * ρ * Real.exp (12 * R) * R := mul_le_mul_of_nonneg_right hα' hR0
    have h3 : 4 * ρ * Real.exp (12 * R) * R ≤ 4 * ρ * Real.exp (169 * Rη) := by
      calc 4 * ρ * Real.exp (12 * R) * R = 4 * ρ * (Real.exp (12 * R) * R) := by ring
        _ ≤ 4 * ρ * Real.exp (169 * Rη) := mul_le_mul_of_nonneg_left h1 (by positivity)
    calc 46 * (α * q) * R = 46 * q * (α * R) := by ring
      _ ≤ 46 * q * (4 * ρ * Real.exp (169 * Rη)) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) (mul_nonneg (by norm_num) hq0)
      _ = 184 * ρ * Real.exp (169 * Rη) * q := by ring

/-- The loss is at most `1/10`, the window bound exceeds the threshold, and the exceptional
probability is at most the loss. -/
theorem stability_loss_bound {B Rη R η q lam : ℝ}
    (hBdef : B = stabilityK / volume.real (ball (0 : Ambient 8) 1) + 2) (hRη1 : 1 ≤ Rη)
    (hRηR : Rη ≤ R) (hR13 : R ≤ 13 * Rη) (hRρ : e8BasisNormSum + 4 ≤ R)
    (hRηω : 3 * volume.real (ball (0 : Ambient 8) 1) ≤ Rη) (hRηB : 100 * B ^ 2 ≤ Rη)
    (hq0 : 0 ≤ q) (hq : q ≤ Real.exp (-(200 * Rη))) (hsq : Real.sqrt η = q ^ 2)
    (hfour : η = q ^ 4) (hlam0 : 0 < lam) (hlam : lam * lam = 1 / Rη) :
    B * lam ≤ 1 / 10 ∧ volume.real (closedBall (0 : Ambient 8) R) ≤ windowBound R ∧
      (1 - B * lam) * volume.real (closedBall (0 : Ambient 8) R) < windowBound R ∧
      2 * Real.sqrt η * volume.real (closedBall (0 : Ambient 8) R) +
        η * volume.real (closedBall (0 : Ambient 8) R) +
        (windowBound R - (1 - η) * volume.real (closedBall (0 : Ambient 8) R)) /
          (windowBound R - (1 - B * lam) * volume.real (closedBall (0 : Ambient 8) R)) ≤
        B * lam := by
  have hω := volume_real_unitBall_eight_pos
  have hK := stabilityK_nonneg
  have hRη0 : 0 < Rη := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hB2 : 2 ≤ B := by
    have h := div_nonneg hK hω.le
    rw [hBdef]
    linarith
  have hB0 : 0 ≤ B := by linarith
  have hV : volume.real (closedBall (0 : Ambient 8) R) =
      R ^ 8 * volume.real (ball (0 : Ambient 8) 1) := volume_real_closedBall_eight 0 hR0
  obtain ⟨hUV, hVU⟩ := windowBound_sub_volume_le hRρ
  have hV0 : 0 < volume.real (closedBall (0 : Ambient 8) R) := by
    rw [hV]
    exact mul_pos (pow_pos (by linarith) 8) hω
  have hloss : B * lam ≤ 1 / 10 := by
    have h1 : (B * lam) ^ 2 ≤ (1 / 10 : ℝ) ^ 2 := by
      have e : (B * lam) ^ 2 = B ^ 2 * (lam * lam) := by ring
      rw [e, hlam, mul_one_div, div_le_iff₀ hRη0]
      linarith
    exact (pow_le_pow_iff_left₀ (mul_nonneg hB0 hlam0.le) (by norm_num) two_ne_zero).mp h1
  have hBlamV : 0 < B * lam * volume.real (closedBall (0 : Ambient 8) R) :=
    mul_pos (mul_pos (by linarith) hlam0) hV0
  have htU : (1 - B * lam) * volume.real (closedBall (0 : Ambient 8) R) < windowBound R := by
    have e : (1 - B * lam) * volume.real (closedBall (0 : Ambient 8) R) =
        volume.real (closedBall (0 : Ambient 8) R) -
          B * lam * volume.real (closedBall (0 : Ambient 8) R) := by ring
    rw [e]
    linarith
  have hq1 : q ≤ 1 := hq.trans (by rw [Real.exp_le_one_iff]; linarith)
  have hq2 : q ^ 2 ≤ 1 := pow_le_one₀ hq0 hq1
  have hsη : η ≤ Real.sqrt η := by
    rw [hsq]
    have e : η = q ^ 2 * q ^ 2 := by
      rw [← pow_add]
      exact hfour
    rw [e]
    nlinarith [sq_nonneg q]
  have hsR : Real.sqrt η * R ^ 8 ≤ 1 / (Rη * Rη) := by
    rw [hsq]
    exact stability_sq hRη1 hRηR hR13 hq0 hq
  have hηR : η ≤ 1 / Rη := by
    have h1 := stability_fourth hRη1 hq0 hq
    rwa [← hfour] at h1
  exact ⟨hloss, hVU, htU, stability_measure_bound hω hK hBdef hRη1 hRηω hRηR hlam0 hlam hV hUV
    hVU hsη hsR hηR⟩

/-- **The periodic stability input for `E8`.** -/
theorem e8_sectionwisePeriodicStabilityInput :
    ∃ E B c η₀ : ℝ, 0 ≤ E ∧ 0 ≤ B ∧ 0 ≤ c ∧ 0 < η₀ ∧
      SectionwisePeriodicStabilityInput e8Set (Real.sqrt 2) E B c η₀ := by
  obtain ⟨ρ, hρ, hshellbound⟩ := e8_magic_even_shell_exponential_bound
  have hω := volume_real_unitBall_eight_pos
  have hK := stabilityK_nonneg
  have hρ8 := e8BasisNormSum_nonneg
  -- the constants
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = stabilityK / volume.real (ball (0 : Ambient 8) 1) + 2 :=
    ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    have h := div_nonneg hK hω.le
    rw [hBdef]
    linarith
  obtain ⟨R₀, hR₀def⟩ : ∃ R₀ : ℝ, R₀ = 6000 + e8BasisNormSum + 4 + 4 * ρ * 10 ^ 29 +
      3 * volume.real (ball (0 : Ambient 8) 1) + 100 * B ^ 2 := ⟨_, rfl⟩
  have h4ρ : 0 ≤ 4 * ρ * 10 ^ 29 := by positivity
  have h100 : 0 ≤ 100 * B ^ 2 := by positivity
  have hR₀a : 6000 ≤ R₀ := by rw [hR₀def]; linarith
  have hR₀b : e8BasisNormSum + 4 ≤ R₀ := by rw [hR₀def]; linarith
  have hR₀c : 4 * ρ * 10 ^ 29 ≤ R₀ := by rw [hR₀def]; linarith
  have hR₀d : 3 * volume.real (ball (0 : Ambient 8) 1) ≤ R₀ := by rw [hR₀def]; linarith
  have hR₀e : 100 * B ^ 2 ≤ R₀ := by rw [hR₀def]; linarith
  refine ⟨184 * ρ, B, 169, Real.exp (-(Real.exp 800 + 4 * R₀ ^ 2)), by positivity, hB0,
    by norm_num, Real.exp_pos _, ?_, ?_⟩
  · intro z L t hL ht
    exact e8_expandAfterDeletion_guardDensity_le_one z L t hL ht
  · intro L t R η hr hL ht hR0 hLR hη hηη₀ hRη0 hRηR hRR z hdef
    obtain ⟨hη1, hq, hRη⟩ := stability_eta_facts (by linarith : (1 : ℝ) ≤ R₀) hη hηη₀
    have hRη1 : (1 : ℝ) ≤ observationRadius η := by linarith
    have hR13 : R ≤ 13 * observationRadius η := by linarith
    have hR1 : (1 : ℝ) ≤ R := by linarith
    have hq0 : 0 ≤ η ^ (1 / 4 : ℝ) := Real.rpow_nonneg hη.le _
    have hsq : Real.sqrt η = (η ^ (1 / 4 : ℝ)) ^ 2 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hη.le]
      norm_num
    have hfour : η = (η ^ (1 / 4 : ℝ)) ^ 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]
      norm_num
    have hlam0 : 0 < observationRadius η ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hRη0 _
    have hlam : observationRadius η ^ (-1 / 2 : ℝ) * observationRadius η ^ (-1 / 2 : ℝ) =
        1 / observationRadius η := by
      rw [← Real.rpow_add hRη0, show (-1 / 2 : ℝ) + -1 / 2 = -1 by norm_num, Real.rpow_neg_one,
        one_div]
    -- the shells
    obtain ⟨α, hα1, hαb, hshell⟩ := hshellbound (2 * R) (by linarith)
    have hα' := alpha_le_exp hρ hR1 hαb
    have hα0 : 0 ≤ α := by linarith
    obtain ⟨hsmall, herr⟩ := stability_small_err hρ hRη1 hRηR hR13 (by linarith) hq0 hq hα'
    obtain ⟨hloss, hVU, htU, hbound⟩ := stability_loss_bound hBdef hRη1 hRηR hR13
      (by linarith) (by linarith) (by linarith) hq0 hq hsq hfour hlam0 hlam
    -- the periodic packing of the periodization
    have hs := expandAfterDeletion_separated z (Real.sqrt 2) t ht
    have hε := guardedPacking_density_ge (by norm_num : 0 < 8)
      (expandAfterDeletion z (Real.sqrt 2) t ht) L (Real.sqrt 2) hr hL hs hdef
    exact e8_centres_of_window
      (P := guardedPacking (expandAfterDeletion z (Real.sqrt 2) t ht) L (Real.sqrt 2) hr hL hs)
      (guardedExpandedConfiguration z L (Real.sqrt 2) t hr hL ht) rfl le_rfl
      (guardedPacking_unique_covers _ L (Real.sqrt 2) hr hL hs) hη hη1 hε (by linarith)
      (by linarith) hα0 hshell hsmall hloss hVU htU herr hbound

/-- **The stationary crystallization theorem for `E8`**, without hypotheses. -/
theorem e8CrystallizationTarget_holds : e8CrystallizationTarget := by
  obtain ⟨E, B, c, η₀, hE, hB, hc, hη₀, h⟩ := e8_sectionwisePeriodicStabilityInput
  exact e8_stationaryCrystallization_of_periodic (by linarith) hB hc hη₀
    (periodicStabilityInput_of_sectionwise isClosed_e8Set ⟨0, zero_mem_e8⟩ (Real.sqrt 2) E B c η₀
      h)

end E8Leech
