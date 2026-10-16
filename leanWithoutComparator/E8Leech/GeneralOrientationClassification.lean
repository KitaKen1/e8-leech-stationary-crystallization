import E8Leech.RotatingPhaseWindow
import E8Leech.InvariantDensityAveraging

/-!
# Arbitrary orientation mixtures from a measurable invariant orientation map

A measurable translation-invariant orientation map allows rotating the phase
averaging window with the configuration. Its pushforward is exactly the mixing
distribution, even when non-atomic. The joint integral identity identifies the
uniform phase at each orientation without conditional measures or countability.
The orientation map and its agreement with the configurations remain explicit
inputs; their existence for every exact lattice law is not proved here.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {d : ℕ} (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem lintegral_joint_orientation_of_invariant_map {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hDm : MeasurableSet D)
    (hcov : ZLattice.covolume Λ volume = 1)
    (μ : Measure (Configuration (Ambient d))) [SFinite μ] (hμ : IsStationary μ)
    (q : Configuration (Ambient d) → LatticeOrientation d) (hq : Measurable q)
    (hinv : ∀ a c, q (translate a c) = q c)
    (hgood : ∀ᵐ c ∂μ, ∃ u : Ambient d, c = rotatedLatticeShift Λ (q c) u)
    (G : LatticeOrientation d × Configuration (Ambient d) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ c, G (q c, c) ∂μ) =
      ∫⁻ Q, (∫⁻ c, G (Q, c) ∂rotatedLatticeShiftLaw Λ D Q) ∂μ.map q := by
  let κ : Kernel (LatticeOrientation d) (Configuration (Ambient d)) :=
    ⟨rotatedLatticeShiftLaw Λ D, measurable_rotatedLatticeShiftLaw Λ D⟩
  have hκ (Q : LatticeOrientation d) : IsFiniteMeasure (κ Q) := by
    let := isProbabilityMeasure_rotatedLatticeShiftLaw Λ hD hcov Q
    change IsFiniteMeasure (rotatedLatticeShiftLaw Λ D Q)
    infer_instance
  have hJ : Measurable (fun Q : LatticeOrientation d =>
      ∫⁻ c, G (Q, c) ∂rotatedLatticeShiftLaw Λ D Q) :=
    measurable_lintegral_of_finite_fibers κ hκ hG
  rw [lintegral_map hJ hq]
  let w : Configuration (Ambient d) × Ambient d → ℝ≥0∞ :=
    fun p => orientationPhaseDensity D (q p.1) p.2
  have hw : Measurable w := (measurable_orientationPhaseDensity hDm).comp
    ((hq.comp measurable_fst).prodMk measurable_snd)
  have hwi (a : Ambient d) (c : Configuration (Ambient d)) :
      w (translate a c, a) = w (c, a) := by
    change orientationPhaseDensity D (q (translate a c)) a = _
    rw [hinv]
  have hwn : ∀ᵐ c ∂μ, (∫⁻ a, w (c, a)) = 1 := ae_of_all _ fun c => by
    exact (lintegral_orientationPhaseDensity hDm (q c)).trans
      (volume_fundamentalDomain_eq_one Λ hD hcov)
  let F : Configuration (Ambient d) → ℝ≥0∞ := fun c => G (q c, c)
  have hF : Measurable F := hG.comp (hq.prodMk measurable_id)
  have havg := stationary_lintegral_invariant_density_average μ hμ w hw hwi hwn F hF
  calc
    _ = ∫⁻ c, (∫⁻ a, w (c, a) * F (translate a c) ∂volume) ∂μ := havg.symm
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hgood] with c hc
      obtain ⟨u, hu⟩ := hc
      have hGc : Measurable (fun c' => G (q c, c')) :=
        hG.comp (measurable_const.prodMk measurable_id)
      calc
        _ = ∫⁻ a, orientationPhaseDensity D (q c) a * G (q c, translate a c) := by
          apply lintegral_congr
          intro a
          change orientationPhaseDensity D (q c) a * G (q (translate a c), translate a c) = _
          rw [hinv]
        _ = ∫⁻ a, orientationPhaseDensity D (q c) a *
            G (q c, translate a (rotatedLatticeShift Λ (q c) u)) :=
          congrArg (fun c' : Configuration (Ambient d) =>
            ∫⁻ a, orientationPhaseDensity D (q c) a * G (q c, translate a c')) hu
        _ = _ := lintegral_phaseDensity_translate_rotatedLatticeShift Λ hD hDm (q c) u _ hGc

theorem eq_orientationMixtureLaw_of_invariant_map_measurable_domain {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hDm : MeasurableSet D)
    (hcov : ZLattice.covolume Λ volume = 1)
    (μ : Measure (Configuration (Ambient d))) [SFinite μ] (hμ : IsStationary μ)
    (q : Configuration (Ambient d) → LatticeOrientation d) (hq : Measurable q)
    (hinv : ∀ a c, q (translate a c) = q c)
    (hgood : ∀ᵐ c ∂μ, ∃ u : Ambient d, c = rotatedLatticeShift Λ (q c) u) :
    μ = orientationMixtureLaw Λ D (μ.map q) := by
  apply Measure.ext
  intro A hA
  rw [orientationMixtureLaw, Measure.bind_apply hA
    (measurable_rotatedLatticeShiftLaw Λ D).aemeasurable]
  have hG : Measurable (fun p : LatticeOrientation d × Configuration (Ambient d) =>
      A.indicator (fun _ => (1 : ℝ≥0∞)) p.2) :=
    (measurable_const.indicator hA).comp measurable_snd
  have hh := lintegral_joint_orientation_of_invariant_map Λ hD hDm hcov μ hμ q hq hinv hgood _ hG
  simpa only [lintegral_indicator hA, setLIntegral_const, one_mul] using hh

theorem eq_orientationMixtureLaw_of_invariant_map {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hcov : ZLattice.covolume Λ volume = 1)
    (μ : Measure (Configuration (Ambient d))) [SFinite μ] (hμ : IsStationary μ)
    (q : Configuration (Ambient d) → LatticeOrientation d) (hq : Measurable q)
    (hinv : ∀ a c, q (translate a c) = q c)
    (hgood : ∀ᵐ c ∂μ, ∃ u : Ambient d, c = rotatedLatticeShift Λ (q c) u) :
    μ = orientationMixtureLaw Λ D (μ.map q) := by
  let b := (Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ
  have hE : IsAddFundamentalDomain Λ (ZSpan.fundamentalDomain b) volume :=
    ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ Λ) volume
  calc
    _ = orientationMixtureLaw Λ (ZSpan.fundamentalDomain b) (μ.map q) :=
      eq_orientationMixtureLaw_of_invariant_map_measurable_domain Λ hE
        (ZSpan.fundamentalDomain_measurableSet b) hcov μ hμ q hq hinv hgood
    _ = _ := orientationMixtureLaw_eq_of_fundamentalDomains Λ hE hD (μ.map q)

theorem exists_orientationMixtureLaw_of_invariant_map {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hcov : ZLattice.covolume Λ volume = 1)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (q : Configuration (Ambient d) → LatticeOrientation d) (hq : Measurable q)
    (hinv : ∀ a c, q (translate a c) = q c)
    (hgood : ∀ᵐ c ∂μ, ∃ u : Ambient d, c = rotatedLatticeShift Λ (q c) u) :
    ∃ σ : Measure (LatticeOrientation d), IsProbabilityMeasure σ ∧ μ = orientationMixtureLaw Λ D σ :=
  ⟨μ.map q, Measure.isProbabilityMeasure_map hq.aemeasurable,
    eq_orientationMixtureLaw_of_invariant_map Λ hD hcov μ hμ q hq hinv hgood⟩

theorem hasIntensity_one_of_invariant_orientation_map {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hcov : ZLattice.covolume Λ volume = 1)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (q : Configuration (Ambient d) → LatticeOrientation d) (hq : Measurable q)
    (hinv : ∀ a c, q (translate a c) = q c)
    (hgood : ∀ᵐ c ∂μ, ∃ u : Ambient d, c = rotatedLatticeShift Λ (q c) u) : HasIntensity μ 1 := by
  have : IsProbabilityMeasure (μ.map q) := Measure.isProbabilityMeasure_map hq.aemeasurable
  rw [eq_orientationMixtureLaw_of_invariant_map Λ hD hcov μ hμ q hq hinv hgood]
  exact hasIntensity_orientationMixtureLaw Λ hD (μ.map q)

theorem potentialEnergy_of_invariant_orientation_map {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hcov : ZLattice.covolume Λ volume = 1)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (q : Configuration (Ambient d) → LatticeOrientation d) (hq : Measurable q)
    (hinv : ∀ a c, q (translate a c) = q c)
    (hgood : ∀ᵐ c ∂μ, ∃ u : Ambient d, c = rotatedLatticeShift Λ (q c) u)
    (P : Ambient d → Ambient d → ℝ≥0∞) (hP : IsometryInvariantPotential P)
    (hPm : Measurable (Function.uncurry P)) : potentialEnergy P μ = latticePotentialEnergy (Λ : Set (Ambient d)) P := by
  have : IsProbabilityMeasure (μ.map q) := Measure.isProbabilityMeasure_map hq.aemeasurable
  rw [eq_orientationMixtureLaw_of_invariant_map Λ hD hcov μ hμ q hq hinv hgood]
  exact potentialEnergy_orientationMixtureLaw Λ hD (μ.map q) P hP hPm

omit Λ [DiscreteTopology Λ] [IsZLattice ℝ Λ] in
theorem e8_eq_orientationMixtureLaw_of_invariant_map
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (q : Configuration (Ambient 8) → LatticeOrientation 8) (hq : Measurable q)
    (hinv : ∀ a c, q (translate a c) = q c)
    (hgood : ∀ᵐ c ∂μ, ∃ u : Ambient 8, c = rotatedLatticeShift e8Lattice (q c) u) :
    μ = e8OrientationMixtureLaw (μ.map q) :=
  eq_orientationMixtureLaw_of_invariant_map e8Lattice
    (ZSpan.isAddFundamentalDomain e8EuclideanBasis volume) e8Lattice_covolume μ hμ q hq hinv hgood

omit Λ [DiscreteTopology Λ] [IsZLattice ℝ Λ] in
theorem leech_eq_orientationMixtureLaw_of_invariant_map
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (q : Configuration (Ambient 24) → LatticeOrientation 24) (hq : Measurable q)
    (hinv : ∀ a c, q (translate a c) = q c)
    (hgood : ∀ᵐ c ∂μ, ∃ u : Ambient 24, c = rotatedLatticeShift leechLattice (q c) u) :
    μ = leechOrientationMixtureLaw (μ.map q) := by
  have hD : IsAddFundamentalDomain leechLattice
      (ZSpan.fundamentalDomain leechEuclideanBasis) volume := by
    rw [leechLattice_eq_span]
    exact ZSpan.isAddFundamentalDomain leechEuclideanBasis volume
  exact eq_orientationMixtureLaw_of_invariant_map leechLattice hD leechLattice_covolume μ hμ q hq hinv hgood

end E8Leech
