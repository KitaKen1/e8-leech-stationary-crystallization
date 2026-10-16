import E8Leech.GaussianBaseline
import E8Leech.OriginSlack

/-!
# Actual Gaussian slack duality, including the spatial origin

The contour identities determine the Fourier transforms of the chosen CKMRV
families off zero. Spatial continuity extends Gaussian duality to zero, where
Fourier positivity and lattice calibration give a strictly positive slack.
The exceptional parameter π is still excluded from these certificate families.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal Real FourierTransform SchwartzMap

theorem gaussian_dual_parameter_ne_pi {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π) :
    π ^ 2 / α ≠ π := by
  intro h
  rw [div_eq_iff hα.ne'] at h
  exact hαπ (mul_left_cancel₀ Real.pi_ne_zero (by rw [← h, sq])).symm

theorem fourier_e8CertFamily_apply (hP : E8KernelNonneg) {α : ℝ}
    (hα : 0 < α) (hαπ : α ≠ π) {x : Ambient 8} (hx : x ≠ 0) :
    (𝓕 (e8CertFamily hP α) : 𝓢(Ambient 8, ℂ)) x =
      ((4 * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
        ∫ t in Ioi 0, ckmrvEightHatKernel (imagPt (α / π)) (imagPt t) *
          (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ) := by
  rw [e8CertFamily, dif_pos ⟨hα, hαπ⟩, FourierAdd.fourier_add]
  change (𝓕 (gaussianSchwartz hα) : 𝓢(Ambient 8, ℂ)) x +
    (𝓕 (e8_exists_gaussianSchwartzCertificate' hα hαπ hP).choose :
      𝓢(Ambient 8, ℂ)) x = _
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe,
    fourier_gaussianSchwartz_eight hα,
    fourier_ckmrvEightKernel_axis (div_pi_pos hα) (div_pi_ne_one hαπ)
      (e8_exists_gaussianSchwartzCertificate' hα hαπ hP).choose_spec.1]
  have h := ckmrv_contour_identity (div_pi_pos hα) (div_pi_ne_one hαπ)
    (norm_ne_zero_iff.mpr hx)
  rw [inv_div, show π / (α / π) = π ^ 2 / α by field_simp] at h
  simpa only [gaussianKernel, add_comm] using h

theorem fourier_leechCertFamily_apply {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π)
    {x : Ambient 24} (hx : x ≠ 0) :
    (𝓕 (leechCertFamily α) : 𝓢(Ambient 24, ℂ)) x =
      leechAxisRadialProfile (-1) (α / π) (π * ‖x‖ ^ 2) := by
  rw [leechCertFamily, dif_pos ⟨hα, hαπ⟩, FourierAdd.fourier_add]
  change (𝓕 (gaussianSchwartz hα) : 𝓢(Ambient 24, ℂ)) x +
    (𝓕 (exists_schwartz_leechAxisRadialProfile (Ambient 24) 1
      (div_pi_pos hα) (div_pi_ne_one hαπ)).choose : 𝓢(Ambient 24, ℂ)) x = _
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe,
    fourier_gaussianSchwartz_twentyFour hα, add_comm]
  exact leechFourierIdentities α hα hαπ _
    (exists_schwartz_leechAxisRadialProfile (Ambient 24) 1
      (div_pi_pos hα) (div_pi_ne_one hαπ)).choose_spec.1 x hx

theorem e8_gaussian_slack_duality (hP : E8KernelNonneg) {α : ℝ}
    (hα : 0 < α) (hαπ : α ≠ π) (x : Ambient 8) :
    gaussianKernel α x - (e8CertFamily hP α x).re =
      (π / α) ^ 4 * (𝓕 (e8CertFamily hP (π ^ 2 / α)) x).re := by
  have hβ : 0 < π ^ 2 / α := by positivity
  have hβπ := gaussian_dual_parameter_ne_pi hα hαπ
  have hp : π ^ 2 / α / π = π / α := by field_simp
  have hf : Continuous (fun x : Ambient 8 =>
      gaussianKernel α x - (e8CertFamily hP α x).re) := by
    unfold gaussianKernel
    fun_prop
  have hg : Continuous (fun x : Ambient 8 =>
      (π / α) ^ 4 * (𝓕 (e8CertFamily hP (π ^ 2 / α)) x).re) := by fun_prop
  apply congrFun (Continuous.ext_on (dense_compl_singleton (0 : Ambient 8)) hf hg ?_) x
  intro v hv
  have hv0 : v ≠ 0 := hv
  dsimp only
  rw [← e8SlackProfile_norm hP α v,
    e8SlackProfile_eq hP hα hαπ (norm_pos_iff.mpr hv0),
    fourier_e8CertFamily_apply hP hβ hβπ hv0, hp, Complex.re_ofReal_mul]
  congr 2
  have hi := integrableOn_ckmrvEightHatKernel_laplace (div_pos Real.pi_pos hα)
    (fun h => hαπ ((div_eq_one_iff_eq hα.ne').mp h).symm)
    (norm_ne_zero_iff.mpr hv0)
  rw [← RCLike.re_to_complex, ← integral_re hi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [Complex.re_mul_ofReal, RCLike.re_to_complex, e8DualKernel]
  congr 2
  ring

theorem leech_gaussian_slack_duality {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π)
    (x : Ambient 24) :
    gaussianKernel α x - (leechCertFamily α x).re =
      (π / α) ^ 12 * (𝓕 (leechCertFamily (π ^ 2 / α)) x).re := by
  have hβ : 0 < π ^ 2 / α := by positivity
  have hβπ := gaussian_dual_parameter_ne_pi hα hαπ
  have hp : π ^ 2 / α / π = π / α := by field_simp
  have hf : Continuous (fun x : Ambient 24 =>
      gaussianKernel α x - (leechCertFamily α x).re) := by
    unfold gaussianKernel
    fun_prop
  have hg : Continuous (fun x : Ambient 24 =>
      (π / α) ^ 12 * (𝓕 (leechCertFamily (π ^ 2 / α)) x).re) := by fun_prop
  apply congrFun (Continuous.ext_on (dense_compl_singleton (0 : Ambient 24)) hf hg ?_) x
  intro v hv
  dsimp only
  rw [← leechSlackProfile_norm α v, leechSlackProfile_eq hα hαπ (norm_nonneg v),
    fourier_leechCertFamily_apply hβ hβπ hv, hp]

theorem e8_gaussian_slack_origin_lower (hP : E8KernelNonneg) {α : ℝ}
    (hα : 0 < α) (hαπ : α ≠ π) :
    (π / α) ^ 4 * (latticePotentialEnergy e8Set (gaussianPotential (π ^ 2 / α))).toReal ≤
      gaussianKernel α (0 : Ambient 8) - (e8CertFamily hP α 0).re := by
  have hc := e8CertFamily_cert hP (by positivity : 0 < π ^ 2 / α)
    (gaussian_dual_parameter_ne_pi hα hαπ)
  exact origin_slack_lower_of_duality_calibration _ hc.fourierReal hc.fourierNonneg
    hc.calibration.symm (by positivity) (e8_gaussian_slack_duality hP hα hαπ 0)

theorem leech_gaussian_slack_origin_lower {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π) :
    (π / α) ^ 12 * (latticePotentialEnergy leechSet (gaussianPotential (π ^ 2 / α))).toReal ≤
      gaussianKernel α (0 : Ambient 24) - (leechCertFamily α 0).re := by
  have hc := leechCertFamily_cert leechKernelInequalities leechFourierIdentities
    (by positivity : 0 < π ^ 2 / α) (gaussian_dual_parameter_ne_pi hα hαπ)
  exact origin_slack_lower_of_duality_calibration _ hc.fourierReal hc.fourierNonneg
    hc.calibration.symm (by positivity) (leech_gaussian_slack_duality hα hαπ 0)

theorem e8_gaussian_slack_origin_pos (hP : E8KernelNonneg) {α : ℝ}
    (hα : 0 < α) (hαπ : α ≠ π) :
    0 < gaussianKernel α (0 : Ambient 8) - (e8CertFamily hP α 0).re := by
  obtain ⟨z, hz, hne, -⟩ := e8Set_minimum_attained
  have hβ : 0 < π ^ 2 / α := by positivity
  have hL := gaussian_lattice_single_vector_lower hz hne (e8_gaussian_lattice_energy_ne_top hβ)
  have hpos : 0 < (latticePotentialEnergy e8Set (gaussianPotential (π ^ 2 / α))).toReal :=
    (Real.exp_pos _).trans_le hL
  exact (mul_pos (by positivity) hpos).trans_le (e8_gaussian_slack_origin_lower hP hα hαπ)

theorem leech_gaussian_slack_origin_pos {α : ℝ} (hα : 0 < α) (hαπ : α ≠ π) :
    0 < gaussianKernel α (0 : Ambient 24) - (leechCertFamily α 0).re := by
  obtain ⟨z, hz, hne, -⟩ := leechSet_minimum_attained
  have hβ : 0 < π ^ 2 / α := by positivity
  have hL := gaussian_lattice_single_vector_lower hz hne (leech_gaussian_lattice_energy_ne_top hβ)
  have hpos : 0 < (latticePotentialEnergy leechSet (gaussianPotential (π ^ 2 / α))).toReal :=
    (Real.exp_pos _).trans_le hL
  exact (mul_pos (by positivity) hpos).trans_le (leech_gaussian_slack_origin_lower hα hαπ)

theorem gaussian_lattice_dual_compact_lower {d : ℕ} {Λ : Set (Ambient d)}
    {a b α r : ℝ} (ha : 0 < a) (hα : α ∈ Icc a b) {z : Ambient d}
    (hz : z ∈ Λ) (hne : z ≠ 0) (hnorm : ‖z‖ = r)
    (hfinite : latticePotentialEnergy Λ (gaussianPotential (π ^ 2 / α)) ≠ ∞) :
    Real.exp (-(π ^ 2 / a) * r ^ 2) ≤
      (latticePotentialEnergy Λ (gaussianPotential (π ^ 2 / α))).toReal := by
  apply le_trans _ (gaussian_lattice_single_vector_lower hz hne hfinite)
  unfold gaussianKernel
  rw [hnorm]
  apply Real.exp_le_exp.mpr
  have hp := div_le_div_of_nonneg_left (sq_nonneg π) ha hα.1
  nlinarith only [mul_le_mul_of_nonneg_right hp (sq_nonneg r)]

/-- The positive origin bound is uniform up to π from both sides. -/
theorem e8_gaussian_slack_origin_compact_lower (hP : E8KernelNonneg)
    {a b α : ℝ} (ha : 0 < a) (hα : α ∈ Icc a b) (hαπ : α ≠ π) :
    (π / b) ^ 4 * Real.exp (-(π ^ 2 / a) * 2) ≤
      gaussianKernel α (0 : Ambient 8) - (e8CertFamily hP α 0).re := by
  have hα0 : 0 < α := ha.trans_le hα.1
  have hb : 0 < b := hα0.trans_le hα.2
  obtain ⟨z, hz, hne, hnorm⟩ := e8Set_minimum_attained
  have hL := gaussian_lattice_dual_compact_lower ha hα hz hne hnorm
    (e8_gaussian_lattice_energy_ne_top (by positivity : 0 < π ^ 2 / α))
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hL
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ π / b)
    (div_le_div_of_nonneg_left Real.pi_pos.le hα0 hα.2) 4
  exact (mul_le_mul hp hL (Real.exp_pos _).le (by positivity)).trans
    (e8_gaussian_slack_origin_lower hP hα0 hαπ)

/-- The positive origin bound is uniform up to π from both sides. -/
theorem leech_gaussian_slack_origin_compact_lower {a b α : ℝ}
    (ha : 0 < a) (hα : α ∈ Icc a b) (hαπ : α ≠ π) :
    (π / b) ^ 12 * Real.exp (-(π ^ 2 / a) * 4) ≤
      gaussianKernel α (0 : Ambient 24) - (leechCertFamily α 0).re := by
  have hα0 : 0 < α := ha.trans_le hα.1
  have hb : 0 < b := hα0.trans_le hα.2
  obtain ⟨z, hz, hne, hnorm⟩ := leechSet_minimum_attained
  have hL := gaussian_lattice_dual_compact_lower ha hα hz hne hnorm
    (leech_gaussian_lattice_energy_ne_top (by positivity : 0 < π ^ 2 / α))
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hL
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ π / b)
    (div_le_div_of_nonneg_left Real.pi_pos.le hα0 hα.2) 12
  exact (mul_le_mul hp hL (Real.exp_pos _).le (by positivity)).trans
    (leech_gaussian_slack_origin_lower hα0 hαπ)

end E8Leech
