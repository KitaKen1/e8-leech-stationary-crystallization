import E8Leech.LatticePhaseLawUniqueness

/-!
# Forward law classification from a countable invariant orientation label

Restricting a stationary law to a measurable translation-invariant event
preserves stationarity. The fixed-orientation uniqueness theorem identifies
each component. A countable invariant measurable partition therefore gives
an explicit orientation mixture, with weights equal to the component masses.
The existence of such a countable label is an explicit hypothesis; arbitrary
orientation distributions still require a measurable quotient construction.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal

theorem isStationary_restrict_invariant {d : ℕ}
    (μ : Measure (Configuration (Ambient d))) (hμ : IsStationary μ)
    {S : Set (Configuration (Ambient d))} (hS : MeasurableSet S)
    (hinv : ∀ a : Ambient d, translate a ⁻¹' S = S) : IsStationary (μ.restrict S) := by
  intro a
  have hh := (hμ a).restrict_preimage hS
  rwa [hinv a] at hh

theorem eq_sum_restrict_of_ae_partition {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (μ : Measure X) (S : ι → Set X) (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, S i) :
    μ = Measure.sum (fun i => μ.restrict (S i)) :=
  (Measure.restrict_eq_self_of_ae_mem hcover).symm.trans (Measure.restrict_iUnion hd hS)

def countableOrientationDistribution {d : ℕ} {ι : Type*}
    (Q : ι → LatticeOrientation d) (w : ι → ℝ≥0∞) : Measure (LatticeOrientation d) :=
  Measure.sum (fun i => w i • Measure.dirac (Q i))

theorem isProbabilityMeasure_countableOrientationDistribution {d : ℕ} {ι : Type*}
    (Q : ι → LatticeOrientation d) (w : ι → ℝ≥0∞) (hw : ∑' i, w i = 1) :
    IsProbabilityMeasure (countableOrientationDistribution Q w) := by
  constructor
  simpa only [countableOrientationDistribution, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one] using hw

theorem orientationMixtureLaw_countableOrientationDistribution {d : ℕ} {ι : Type*}
    (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (D : Set (Ambient d)) (Q : ι → LatticeOrientation d) (w : ι → ℝ≥0∞) :
    orientationMixtureLaw Λ D (countableOrientationDistribution Q w) =
      Measure.sum (fun i => w i • rotatedLatticeShiftLaw Λ D (Q i)) := by
  apply Measure.ext
  intro A hA
  rw [orientationMixtureLaw, Measure.bind_apply hA
    (measurable_rotatedLatticeShiftLaw Λ D).aemeasurable,
    countableOrientationDistribution, lintegral_sum_measure, Measure.sum_apply _ hA]
  apply tsum_congr
  intro i
  have hmA : Measurable (fun R : LatticeOrientation d => (rotatedLatticeShiftLaw Λ D R) A) :=
    (Measure.measurable_coe hA).comp (measurable_rotatedLatticeShiftLaw Λ D)
  rw [lintegral_smul_measure,
    lintegral_dirac' (Q i) hmA,
    Measure.smul_apply, smul_eq_mul]

theorem eq_orientationMixtureLaw_of_invariant_partition {d : ℕ} {ι : Type*} [Countable ι]
    (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {D : Set (Ambient d)} (hD : IsAddFundamentalDomain Λ D volume)
    (hcov : ZLattice.covolume Λ volume = 1)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (Q : ι → LatticeOrientation d) (S : ι → Set (Configuration (Ambient d)))
    (hS : ∀ i, MeasurableSet (S i)) (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hcover : ∀ᵐ c ∂μ, c ∈ ⋃ i, S i)
    (hinv : ∀ i (a : Ambient d), translate a ⁻¹' S i = S i)
    (hgood : ∀ i, ∀ᵐ c ∂μ.restrict (S i), ∃ u : Ambient d, c = rotatedLatticeShift Λ (Q i) u) :
    IsProbabilityMeasure (countableOrientationDistribution Q (fun i => μ (S i))) ∧
      μ = orientationMixtureLaw Λ D (countableOrientationDistribution Q (fun i => μ (S i))) := by
  have hdecomp := eq_sum_restrict_of_ae_partition μ S hS hd hcover
  have hsum : ∑' i, μ (S i) = 1 := by
    have hh := congrArg (fun ν : Measure (Configuration (Ambient d)) => ν univ) hdecomp
    simpa only [Measure.sum_apply _ MeasurableSet.univ, Measure.restrict_apply_univ,
      measure_univ] using hh.symm
  refine ⟨isProbabilityMeasure_countableOrientationDistribution Q _ hsum, ?_⟩
  have hi (i : ι) : μ.restrict (S i) = μ (S i) • rotatedLatticeShiftLaw Λ D (Q i) := by
    have hh := eq_smul_rotatedLatticeShiftLaw_of_ae Λ hD hcov (Q i) (μ.restrict (S i))
      (isStationary_restrict_invariant μ hμ (hS i) (hinv i)) (hgood i)
    simpa only [Measure.restrict_apply_univ] using hh
  rw [orientationMixtureLaw_countableOrientationDistribution]
  exact hdecomp.trans (congrArg Measure.sum (funext hi))

theorem exists_orientationMixtureLaw_of_countable_invariant_label
    {d : ℕ} {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
    (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {D : Set (Ambient d)} (hD : IsAddFundamentalDomain Λ D volume)
    (hcov : ZLattice.covolume Λ volume = 1)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (q : Configuration (Ambient d) → ι) (hq : Measurable q) (Q : ι → LatticeOrientation d)
    (hinv : ∀ a c, q (translate a c) = q c)
    (hgood : ∀ᵐ c ∂μ, ∃ u : Ambient d, c = rotatedLatticeShift Λ (Q (q c)) u) :
    ∃ σ : Measure (LatticeOrientation d), IsProbabilityMeasure σ ∧ μ = orientationMixtureLaw Λ D σ := by
  let S : ι → Set (Configuration (Ambient d)) := fun i => q ⁻¹' {i}
  have hS (i : ι) : MeasurableSet (S i) := hq (measurableSet_singleton i)
  have hd : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    apply disjoint_left.mpr
    intro c hci hcj
    have hi : q c = i := hci
    have hj : q c = j := hcj
    exact hij (hi.symm.trans hj)
  have hcover : ∀ᵐ c ∂μ, c ∈ ⋃ i, S i := ae_of_all _ fun c => mem_iUnion.mpr ⟨q c, rfl⟩
  have hSi (i : ι) (a : Ambient d) : translate a ⁻¹' S i = S i := by
    ext c
    change q (translate a c) = i ↔ q c = i
    rw [hinv]
  have hgoodi (i : ι) : ∀ᵐ c ∂μ.restrict (S i),
      ∃ u : Ambient d, c = rotatedLatticeShift Λ (Q i) u := by
    filter_upwards [ae_restrict_of_ae hgood, ae_restrict_mem (hS i)] with c hc hci
    have hqi : q c = i := hci
    simpa only [hqi] using hc
  exact ⟨_, eq_orientationMixtureLaw_of_invariant_partition Λ hD hcov μ hμ Q S hS hd hcover hSi hgoodi⟩

theorem e8_exists_orientationMixture_of_countable_invariant_label
    {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (q : Configuration (Ambient 8) → ι) (hq : Measurable q) (Q : ι → LatticeOrientation 8)
    (hinv : ∀ a c, q (translate a c) = q c)
    (hgood : ∀ᵐ c ∂μ, ∃ u : Ambient 8, c = rotatedLatticeShift e8Lattice (Q (q c)) u) :
    ∃ σ : Measure (LatticeOrientation 8), IsProbabilityMeasure σ ∧ μ = e8OrientationMixtureLaw σ :=
  exists_orientationMixtureLaw_of_countable_invariant_label e8Lattice
    (ZSpan.isAddFundamentalDomain e8EuclideanBasis volume) e8Lattice_covolume μ hμ q hq Q hinv hgood

theorem leech_exists_orientationMixture_of_countable_invariant_label
    {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (q : Configuration (Ambient 24) → ι) (hq : Measurable q) (Q : ι → LatticeOrientation 24)
    (hinv : ∀ a c, q (translate a c) = q c)
    (hgood : ∀ᵐ c ∂μ, ∃ u : Ambient 24, c = rotatedLatticeShift leechLattice (Q (q c)) u) :
    ∃ σ : Measure (LatticeOrientation 24), IsProbabilityMeasure σ ∧ μ = leechOrientationMixtureLaw σ := by
  have hD : IsAddFundamentalDomain leechLattice
      (ZSpan.fundamentalDomain leechEuclideanBasis) volume := by
    rw [leechLattice_eq_span]
    exact ZSpan.isAddFundamentalDomain leechEuclideanBasis volume
  exact exists_orientationMixtureLaw_of_countable_invariant_label leechLattice hD
    leechLattice_covolume μ hμ q hq Q hinv hgood

end E8Leech
