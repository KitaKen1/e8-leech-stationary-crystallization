import E8Leech.E8PeriodicStability
import E8Leech.LeechStabilityConstants
import E8Leech.LeechPeriodicStructure
import E8Leech.LeechMagicExponentialBounds

/-!
# The periodic stability input for the Leech lattice

`leech_sectionwisePeriodicStabilityInput` proves the periodic stability input for the Leech
lattice (Theorem 1.5 of Böröczky–Radchenko–Ramos in dimension 24, in the form used by this
development), **given the characterization of the Leech lattice** (`LeechCharacterization`: an even
unimodular lattice of rank 24 without vectors of squared norm two is an isometric copy of the
Leech lattice). For a configuration whose guarded periodization has density deficit `η < η₀`,
outside a set of observation centres of probability at most `B R_η^{-1/2}` the periodization is a
local crystal of the Leech lattice on the ball of radius `R`, with error `E exp(c R_η) η^{1/4}`
and loss `B R_η^{-1/2}`.

`leech_stationaryCrystallization_of_inputs` states what remains for the Leech crystallization
target: the characterization of the Leech lattice and the analytic unit-cost input of the Leech
lattice. Neither is proved in this development at this point.

* `leech_centres_of_window`: from `leech_periodic_window_structure` to `LocalCrystal` and the
  bound for the exceptional set, with the numerical conditions as hypotheses.
* `leech_sectionwisePeriodicStabilityInput`: the constants `E = 832ρ`, `c = 221`,
  `B = K/ω + 2` and `η₀ = exp(-(exp 1600 + 4R₀²))`.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric Set SpherePacking
open scoped ENNReal

/-- From the periodic local structure to `LocalCrystal` in dimension 24, with the numerical
conditions as hypotheses. -/
theorem leech_centres_of_window (hLeech : LeechCharacterization)
    {P : PeriodicSpherePacking 24} (cfg : Configuration (Ambient 24))
    (hsupp : cfg.support = P.centers) {L : ℝ} (hP : 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ periodCell 24 L) {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hε : 1 - η ≤ (P.numReps' (by norm_num) (isBounded_periodCell 24 L) : ℝ) /
      ZLattice.covolume P.lattice volume)
    {R α loss err bound : ℝ} (hR : 200000 ≤ R) (hRρ : leechBasisNormSum ≤ R) (hα0 : 0 ≤ α)
    (hshell : ∀ x : Ambient 24, 2 ≤ ‖x‖ → ‖x‖ ≤ 2 * R →
      ∃ k : ℤ, 2 ≤ k ∧ |‖x‖ ^ 2 - 2 * k| ≤ α * Real.sqrt |(Dim24.f x).re|)
    (hsmall : α * η ^ (1 / 4 : ℝ) * R ^ 2 ≤ 1 / 10 ^ 115) (hloss : loss ≤ 1 / 10)
    (hVU : volume.real (closedBall (0 : Ambient 24) R) ≤ leechWindowBound R)
    (htU : (1 - loss) * volume.real (closedBall (0 : Ambient 24) R) < leechWindowBound R)
    (herr : 13 * (α * η ^ (1 / 4 : ℝ)) * R ≤ err)
    (hbound : 2 * Real.sqrt η * volume.real (closedBall (0 : Ambient 24) R) +
      η * volume.real (closedBall (0 : Ambient 24) R) +
      (leechWindowBound R - (1 - η) * volume.real (closedBall (0 : Ambient 24) R)) /
        (leechWindowBound R - (1 - loss) * volume.real (closedBall (0 : Ambient 24) R)) ≤
        bound) :
    ∃ S : Set (Ambient 24),
      (∀ u, u ∉ S → LocalCrystal leechSet (translate (-u) cfg) R err loss) ∧
        uniformPeriodCell 24 L S ≤ ENNReal.ofReal bound := by
  have hV0 : 0 ≤ volume.real (closedBall (0 : Ambient 24) R) := measureReal_nonneg
  -- the packing is not empty
  have hne : P.centers.Nonempty := by
    by_contra hcon
    have hempty : P.centers = ∅ := Set.not_nonempty_iff_eq_empty.mp hcon
    have h0 : P.numReps' (by norm_num) (isBounded_periodCell 24 L) = 0 := by
      rw [numReps'_eq_ncard, hempty, Set.empty_inter, Set.ncard_empty]
    rw [h0] at hε
    norm_num at hε
    linarith
  have ht9 : 9 / 10 * volume.real (closedBall (0 : Ambient 24) R) ≤
      (1 - loss) * volume.real (closedBall (0 : Ambient 24) R) :=
    mul_le_mul_of_nonneg_right (by linarith) hV0
  obtain ⟨S, hSm, hS⟩ := leech_periodic_window_structure hLeech (isBounded_periodCell 24 L)
    (measurable_periodCell 24 L) hP hD hne hη hη1.le hε hR hRρ hα0 hshell hsmall ht9 htU
  have hvol : volume (closedBall (0 : Ambient 24) R) =
      ENNReal.ofReal (volume.real (closedBall (0 : Ambient 24) R)) :=
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
  · have hratio0 : 0 ≤
        (leechWindowBound R - (1 - η) * volume.real (closedBall (0 : Ambient 24) R)) /
        (leechWindowBound R - (1 - loss) * volume.real (closedBall (0 : Ambient 24) R)) := by
      apply div_nonneg
      · have h1 : (1 - η) * volume.real (closedBall (0 : Ambient 24) R) ≤
            1 * volume.real (closedBall (0 : Ambient 24) R) :=
          mul_le_mul_of_nonneg_right (by linarith) hV0
        linarith
      · linarith
    have h1 : (0 : ℝ) ≤ 2 * Real.sqrt η * volume.real (closedBall (0 : Ambient 24) R) :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hV0
    have h2 : (0 : ℝ) ≤ η * volume.real (closedBall (0 : Ambient 24) R) := mul_nonneg hη.le hV0
    show uniformFundamentalDomain (periodCell 24 L) S ≤ ENNReal.ofReal bound
    refine hSm.trans ?_
    rw [hvol, ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)),
      ← ENNReal.ofReal_mul hη.le, ← ENNReal.ofReal_add h1 h2,
      ← ENNReal.ofReal_add (add_nonneg h1 h2) hratio0]
    exact ENNReal.ofReal_le_ofReal hbound

/-- The size of `η` below the threshold: `η^{1/4} ≤ exp(-400 R_η)` and `R_η ≥ R₀`. -/
theorem leech_stability_eta_facts {R₀ η : ℝ} (hR₀ : 1 ≤ R₀) (hη : 0 < η)
    (hηη₀ : η < Real.exp (-(Real.exp 1600 + 4 * R₀ ^ 2))) :
    η < 1 ∧ η ^ (1 / 4 : ℝ) ≤ Real.exp (-(400 * observationRadius η)) ∧
      R₀ ≤ observationRadius η := by
  have he : (0 : ℝ) < Real.exp 1600 := Real.exp_pos _
  have hsqR₀ : 0 ≤ 4 * R₀ ^ 2 := by positivity
  have hη₀1 : Real.exp (-(Real.exp 1600 + 4 * R₀ ^ 2)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hlogη : Real.exp 1600 + 4 * R₀ ^ 2 < Real.log (1 / η) := by
    have h1 := Real.log_lt_log hη hηη₀
    rw [Real.log_exp] at h1
    rw [one_div, Real.log_inv]
    linarith
  refine ⟨hηη₀.trans hη₀1, ?_, ?_⟩
  · exact rpow_quarter_le_exp_neg hη (by norm_num : (0 : ℝ) < 400)
      (by rw [show (4 : ℝ) * 400 = 1600 by norm_num]; linarith)
  · exact le_observationRadius hR₀ (by linarith)

/-- The smallness of the even-shell error and the size of the final error in dimension 24. -/
theorem leech_stability_small_err {ρ Rη R q α : ℝ} (hρ : 0 < ρ) (hRη1 : 1 ≤ Rη)
    (hRηR : Rη ≤ R) (hR13 : R ≤ 13 * Rη) (hRηρ : 64 * ρ * 10 ^ 115 ≤ Rη) (hq0 : 0 ≤ q)
    (hq : q ≤ Real.exp (-(400 * Rη))) (hα' : α ≤ 64 * ρ * Real.exp (16 * R)) :
    α * q * R ^ 2 ≤ 1 / 10 ^ 115 ∧
      13 * (α * q) * R ≤ 832 * ρ * Real.exp (221 * Rη) * q := by
  have hRη0 : 0 < Rη := by linarith
  have hR0 : 0 ≤ R := by linarith
  constructor
  · have h1 := leech_stability_small hRη1 hRηR hR13 hq0 hq
    have h2 : α * (q * R ^ 2) ≤ 64 * ρ * Real.exp (16 * R) * (q * R ^ 2) :=
      mul_le_mul_of_nonneg_right hα' (mul_nonneg hq0 (sq_nonneg R))
    have h3 : 64 * ρ * (1 / Rη) ≤ 1 / 10 ^ 115 := by
      rw [mul_one_div, div_le_div_iff₀ hRη0 (by positivity)]
      linarith
    calc α * q * R ^ 2 = α * (q * R ^ 2) := by ring
      _ ≤ 64 * ρ * Real.exp (16 * R) * (q * R ^ 2) := h2
      _ = 64 * ρ * (Real.exp (16 * R) * q * R ^ 2) := by ring
      _ ≤ 64 * ρ * (1 / Rη) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 1 / 10 ^ 115 := h3
  · have h1 := leech_stability_error hRη1 hRηR hR13
    have h2 : α * R ≤ 64 * ρ * Real.exp (16 * R) * R := mul_le_mul_of_nonneg_right hα' hR0
    have h3 : 64 * ρ * Real.exp (16 * R) * R ≤ 64 * ρ * Real.exp (221 * Rη) := by
      calc 64 * ρ * Real.exp (16 * R) * R = 64 * ρ * (Real.exp (16 * R) * R) := by ring
        _ ≤ 64 * ρ * Real.exp (221 * Rη) := mul_le_mul_of_nonneg_left h1 (by positivity)
    calc 13 * (α * q) * R = 13 * q * (α * R) := by ring
      _ ≤ 13 * q * (64 * ρ * Real.exp (221 * Rη)) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) (mul_nonneg (by norm_num) hq0)
      _ = 832 * ρ * Real.exp (221 * Rη) * q := by ring

/-- The loss is at most `1/10`, the window bound exceeds the threshold, and the exceptional
probability is at most the loss (dimension 24). -/
theorem leech_stability_loss_bound {B Rη R η q lam : ℝ}
    (hBdef : B = leechStabilityK / volume.real (ball (0 : Ambient 24) 1) + 2) (hRη1 : 1 ≤ Rη)
    (hRηR : Rη ≤ R) (hR13 : R ≤ 13 * Rη) (hRρ : leechBasisNormSum + 4 ≤ R)
    (hRηω : 3 * volume.real (ball (0 : Ambient 24) 1) ≤ Rη) (hRηB : 100 * B ^ 2 ≤ Rη)
    (hq0 : 0 ≤ q) (hq : q ≤ Real.exp (-(400 * Rη))) (hsq : Real.sqrt η = q ^ 2)
    (hfour : η = q ^ 4) (hlam0 : 0 < lam) (hlam : lam * lam = 1 / Rη) :
    B * lam ≤ 1 / 10 ∧ volume.real (closedBall (0 : Ambient 24) R) ≤ leechWindowBound R ∧
      (1 - B * lam) * volume.real (closedBall (0 : Ambient 24) R) < leechWindowBound R ∧
      2 * Real.sqrt η * volume.real (closedBall (0 : Ambient 24) R) +
        η * volume.real (closedBall (0 : Ambient 24) R) +
        (leechWindowBound R - (1 - η) * volume.real (closedBall (0 : Ambient 24) R)) /
          (leechWindowBound R -
            (1 - B * lam) * volume.real (closedBall (0 : Ambient 24) R)) ≤
        B * lam := by
  have hω := volume_real_unitBall_twentyFour_pos
  have hK := leechStabilityK_nonneg
  have hRη0 : 0 < Rη := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hB2 : 2 ≤ B := by
    have h := div_nonneg hK hω.le
    rw [hBdef]
    linarith
  have hB0 : 0 ≤ B := by linarith
  have hV : volume.real (closedBall (0 : Ambient 24) R) =
      R ^ 24 * volume.real (ball (0 : Ambient 24) 1) := volume_real_closedBall_twentyFour 0 hR0
  obtain ⟨hUV, hVU⟩ := leechWindowBound_sub_volume_le hRρ
  have hV0 : 0 < volume.real (closedBall (0 : Ambient 24) R) := by
    rw [hV]
    exact mul_pos (pow_pos (by linarith) 24) hω
  have hloss : B * lam ≤ 1 / 10 := by
    have h1 : (B * lam) ^ 2 ≤ (1 / 10 : ℝ) ^ 2 := by
      have e : (B * lam) ^ 2 = B ^ 2 * (lam * lam) := by ring
      rw [e, hlam, mul_one_div, div_le_iff₀ hRη0]
      linarith
    exact (pow_le_pow_iff_left₀ (mul_nonneg hB0 hlam0.le) (by norm_num) two_ne_zero).mp h1
  have hBlamV : 0 < B * lam * volume.real (closedBall (0 : Ambient 24) R) :=
    mul_pos (mul_pos (by linarith) hlam0) hV0
  have htU : (1 - B * lam) * volume.real (closedBall (0 : Ambient 24) R) <
      leechWindowBound R := by
    have e : (1 - B * lam) * volume.real (closedBall (0 : Ambient 24) R) =
        volume.real (closedBall (0 : Ambient 24) R) -
          B * lam * volume.real (closedBall (0 : Ambient 24) R) := by ring
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
  have hsR : Real.sqrt η * R ^ 24 ≤ 1 / (Rη * Rη) := by
    rw [hsq]
    exact leech_stability_sq hRη1 hRηR hR13 hq0 hq
  have hηR : η ≤ 1 / Rη := by
    have h1 := leech_stability_fourth hRη1 hq0 hq
    rwa [← hfour] at h1
  exact ⟨hloss, hVU, htU, stability_measure_bound_pow 23 hω hK hBdef hRη1 hRηω hRηR hlam0 hlam
    hV hUV hVU hsη hsR hηR⟩

/-- **The periodic stability input for the Leech lattice**, given the characterization of the
Leech lattice. -/
theorem leech_sectionwisePeriodicStabilityInput (hLeech : LeechCharacterization) :
    ∃ E B c η₀ : ℝ, 0 ≤ E ∧ 0 ≤ B ∧ 0 ≤ c ∧ 0 < η₀ ∧
      SectionwisePeriodicStabilityInput leechSet 2 E B c η₀ := by
  obtain ⟨ρ, hρ, hshellbound⟩ := leech_magic_even_shell_exponential_bound
  have hω := volume_real_unitBall_twentyFour_pos
  have hK := leechStabilityK_nonneg
  have hρ24 := leechBasisNormSum_nonneg
  -- the constants
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ,
      B = leechStabilityK / volume.real (ball (0 : Ambient 24) 1) + 2 := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    have h := div_nonneg hK hω.le
    rw [hBdef]
    linarith
  obtain ⟨R₀, hR₀def⟩ : ∃ R₀ : ℝ, R₀ = 200000 + leechBasisNormSum + 4 + 64 * ρ * 10 ^ 115 +
      3 * volume.real (ball (0 : Ambient 24) 1) + 100 * B ^ 2 := ⟨_, rfl⟩
  have h64ρ : 0 ≤ 64 * ρ * 10 ^ 115 := by positivity
  have h100 : 0 ≤ 100 * B ^ 2 := by positivity
  have hR₀a : 200000 ≤ R₀ := by rw [hR₀def]; linarith
  have hR₀b : leechBasisNormSum + 4 ≤ R₀ := by rw [hR₀def]; linarith
  have hR₀c : 64 * ρ * 10 ^ 115 ≤ R₀ := by rw [hR₀def]; linarith
  have hR₀d : 3 * volume.real (ball (0 : Ambient 24) 1) ≤ R₀ := by rw [hR₀def]; linarith
  have hR₀e : 100 * B ^ 2 ≤ R₀ := by rw [hR₀def]; linarith
  refine ⟨832 * ρ, B, 221, Real.exp (-(Real.exp 1600 + 4 * R₀ ^ 2)), by positivity, hB0,
    by norm_num, Real.exp_pos _, ?_, ?_⟩
  · intro z L t hL ht
    exact leech_expandAfterDeletion_guardDensity_le_one z L t hL ht
  · intro L t R η hr hL ht hR0 hLR hη hηη₀ hRη0 hRηR hRR z hdef
    obtain ⟨hη1, hq, hRη⟩ := leech_stability_eta_facts (by linarith : (1 : ℝ) ≤ R₀) hη hηη₀
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
    have hα' := leech_alpha_le_exp hρ hR1 hαb
    have hα0 : 0 ≤ α := by linarith
    obtain ⟨hsmall, herr⟩ :=
      leech_stability_small_err hρ hRη1 hRηR hR13 (by linarith) hq0 hq hα'
    obtain ⟨hloss, hVU, htU, hbound⟩ := leech_stability_loss_bound hBdef hRη1 hRηR hR13
      (by linarith) (by linarith) (by linarith) hq0 hq hsq hfour hlam0 hlam
    -- the periodic packing of the periodization
    have hs := expandAfterDeletion_separated z (2 : ℝ) t ht
    have hε := guardedPacking_density_ge (by norm_num : 0 < 24)
      (expandAfterDeletion z 2 t ht) L 2 hr hL hs hdef
    exact leech_centres_of_window hLeech
      (P := guardedPacking (expandAfterDeletion z 2 t ht) L 2 hr hL hs)
      (guardedExpandedConfiguration z L 2 t hr hL ht) rfl le_rfl
      (guardedPacking_unique_covers _ L 2 hr hL hs) hη hη1 hε (by linarith)
      (by linarith) hα0 hshell hsmall hloss hVU htU herr hbound

/-- **What remains for the Leech lattice.** The stationary crystallization target for the Leech
lattice follows from the characterization of the Leech lattice and the analytic unit-cost input
of the Leech lattice. -/
theorem leech_stationaryCrystallization_of_inputs (hLeech : LeechCharacterization)
    (hanalytic : ∀ s : ℝ, ((24 : ℕ) : ℝ) < s → ∃ A δA : ℝ,
      0 ≤ A ∧ 0 < δA ∧ AnalyticUnitCostInput leechSet s 2 A δA) :
    leechCrystallizationTarget := by
  obtain ⟨E, B, c, η₀, hE, hB, hc, hη₀, h⟩ := leech_sectionwisePeriodicStabilityInput hLeech
  exact stationaryCrystallizationFor_of_inputs leechSet (fun _ hx _ hy => leechSet_sub hx hy)
    2 (E + 1) B c η₀ (by norm_num) (by linarith) hB hc hη₀
    (periodicStabilityInput_of_sectionwise isClosed_leechSet ⟨0, zero_mem_leechSet⟩ 2 E B c η₀ h)
    hanalytic

end E8Leech
