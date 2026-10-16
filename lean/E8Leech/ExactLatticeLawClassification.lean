import E8Leech.GlobalOrientationKernel
import E8Leech.KernelPhaseAveraging

/-! # Every stationary exact lattice law is an orientation mixture with uniform phase

The orientation distribution is explicitly obtained by binding the constructed
probability kernel. No invariant orientation map or point selection is an input.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {d : ℕ} (b : Module.Basis (Fin d) ℝ (Ambient d))
variable (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem eq_orientationMixtureLaw_of_ae_isometric_lattice
    (hb : Λ = Submodule.span ℤ (Set.range b))
    {D : Set (Ambient d)} (hD : IsAddFundamentalDomain Λ D volume)
    (hcov : ZLattice.covolume Λ volume = 1)
    (μ : Measure (Configuration (Ambient d))) [SFinite μ] (hμ : IsStationary μ)
    (hgood : ∀ᵐ c ∂μ, ∃ Φ : Ambient d ≃ᵢ Ambient d, c.support = Φ '' (Λ : Set (Ambient d))) :
    μ = orientationMixtureLaw Λ D (μ.bind (globalOrientationKernel b)) := by
  apply eq_orientationMixtureLaw_of_invariant_kernel Λ hD hcov μ hμ (globalOrientationKernel b)
  · intro a
    filter_upwards [hgood] with c hc
    obtain ⟨Φ, hΦ⟩ := hc
    exact globalOrientationKernel_translate_of_exact b Λ hb c Φ hΦ a
  · filter_upwards [hgood] with c hc
    obtain ⟨Φ, hΦ⟩ := hc
    exact globalOrientationKernel_ae_recovers_lattice b Λ hb c Φ hΦ

theorem exists_orientationMixtureLaw_of_ae_isometric_lattice
    (hb : Λ = Submodule.span ℤ (Set.range b))
    {D : Set (Ambient d)} (hD : IsAddFundamentalDomain Λ D volume)
    (hcov : ZLattice.covolume Λ volume = 1)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (hgood : ∀ᵐ c ∂μ, ∃ Φ : Ambient d ≃ᵢ Ambient d, c.support = Φ '' (Λ : Set (Ambient d))) :
    ∃ σ : Measure (LatticeOrientation d), IsProbabilityMeasure σ ∧ μ = orientationMixtureLaw Λ D σ :=
  ⟨μ.bind (globalOrientationKernel b), globalOrientationKernel_mixing_isProbability b μ,
    eq_orientationMixtureLaw_of_ae_isometric_lattice b Λ hb hD hcov μ hμ hgood⟩

theorem hasIntensity_one_of_stationary_ae_isometric_lattice
    (hb : Λ = Submodule.span ℤ (Set.range b))
    {D : Set (Ambient d)} (hD : IsAddFundamentalDomain Λ D volume)
    (hcov : ZLattice.covolume Λ volume = 1)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (hgood : ∀ᵐ c ∂μ, ∃ Φ : Ambient d ≃ᵢ Ambient d, c.support = Φ '' (Λ : Set (Ambient d))) :
    HasIntensity μ 1 := by
  let := globalOrientationKernel_mixing_isProbability b μ
  rw [eq_orientationMixtureLaw_of_ae_isometric_lattice b Λ hb hD hcov μ hμ hgood]
  exact hasIntensity_orientationMixtureLaw Λ hD _

omit b Λ [DiscreteTopology Λ] [IsZLattice ℝ Λ] in
theorem e8_eq_orientationMixtureLaw_of_ae_isometric_lattice
    (μ : Measure (Configuration (Ambient 8))) [SFinite μ] (hμ : IsStationary μ)
    (hgood : ∀ᵐ c ∂μ, ∃ Φ : Ambient 8 ≃ᵢ Ambient 8, c.support = Φ '' e8Set) :
    μ = e8OrientationMixtureLaw (μ.bind (globalOrientationKernel e8EuclideanBasis)) := by
  apply eq_orientationMixtureLaw_of_ae_isometric_lattice e8EuclideanBasis e8Lattice rfl
    (ZSpan.isAddFundamentalDomain e8EuclideanBasis volume) e8Lattice_covolume μ hμ
  simpa only [coe_e8Lattice] using hgood

omit b Λ [DiscreteTopology Λ] [IsZLattice ℝ Λ] in
theorem leech_eq_orientationMixtureLaw_of_ae_isometric_lattice
    (μ : Measure (Configuration (Ambient 24))) [SFinite μ] (hμ : IsStationary μ)
    (hgood : ∀ᵐ c ∂μ, ∃ Φ : Ambient 24 ≃ᵢ Ambient 24, c.support = Φ '' leechSet) :
    μ = leechOrientationMixtureLaw (μ.bind (globalOrientationKernel leechEuclideanBasis)) := by
  have hD : IsAddFundamentalDomain leechLattice
      (ZSpan.fundamentalDomain leechEuclideanBasis) volume := by
    rw [leechLattice_eq_span]
    exact ZSpan.isAddFundamentalDomain leechEuclideanBasis volume
  apply eq_orientationMixtureLaw_of_ae_isometric_lattice leechEuclideanBasis leechLattice
    leechLattice_eq_span hD leechLattice_covolume μ hμ
  simpa only [coe_leechLattice] using hgood

omit b Λ [DiscreteTopology Λ] [IsZLattice ℝ Λ] in
theorem e8_exists_orientationMixtureLaw_of_ae_isometric_lattice
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (hgood : ∀ᵐ c ∂μ, ∃ Φ : Ambient 8 ≃ᵢ Ambient 8, c.support = Φ '' e8Set) :
    ∃ σ : Measure (LatticeOrientation 8), IsProbabilityMeasure σ ∧ μ = e8OrientationMixtureLaw σ :=
  ⟨μ.bind (globalOrientationKernel e8EuclideanBasis),
    globalOrientationKernel_mixing_isProbability e8EuclideanBasis μ,
    e8_eq_orientationMixtureLaw_of_ae_isometric_lattice μ hμ hgood⟩

omit b Λ [DiscreteTopology Λ] [IsZLattice ℝ Λ] in
theorem leech_exists_orientationMixtureLaw_of_ae_isometric_lattice
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (hgood : ∀ᵐ c ∂μ, ∃ Φ : Ambient 24 ≃ᵢ Ambient 24, c.support = Φ '' leechSet) :
    ∃ σ : Measure (LatticeOrientation 24), IsProbabilityMeasure σ ∧ μ = leechOrientationMixtureLaw σ :=
  ⟨μ.bind (globalOrientationKernel leechEuclideanBasis),
    globalOrientationKernel_mixing_isProbability leechEuclideanBasis μ,
    leech_eq_orientationMixtureLaw_of_ae_isometric_lattice μ hμ hgood⟩

end E8Leech
