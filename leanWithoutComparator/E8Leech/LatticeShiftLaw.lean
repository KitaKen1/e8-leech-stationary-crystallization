import E8Leech.WindowNormalization
import E8Leech.LatticeDistance
import E8Leech.LatticeEnergy
import E8Leech.LeechBasis
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The uniformly shifted lattice: a law that satisfies the hypotheses of the main theorem

For a lattice `Λ` of covolume one in `ℝ^d`, the law of `u + Λ` with `u` distributed by Lebesgue
measure on a fundamental domain is a stationary point process of intensity one, and its Riesz
energy is the lattice energy `∑_{z ∈ Λ, z ≠ 0} |z|^{-s}` for every `s`
(`exists_stationary_law_latticeRieszEnergy`).

So the hypotheses of the crystallization theorems (`Target`, `LeechCrystallization`) are satisfied
by one law for all `s > d` and all `δ > 0` (`e8_hypotheses_satisfiable`,
`leech_hypotheses_satisfiable`): the theorems are not vacuous, and the energy bound in the
hypothesis is attained with excess zero.

* `latticeShift Λ u`: the configuration `u + Λ`.
* `latticeShiftLaw Λ D`: its law for `u` in a fundamental domain `D`.
* `lintegral_lattice_unfold`: `∫_D ∑_{ℓ ∈ Λ} f(u + ℓ) du = ∫ f`.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Pointwise Classical

/-- The ordered energy with the points of the configuration indexed by a bijection, and with
indicator functions in place of the case distinctions. -/
theorem orderedWindowEnergy_eq_tsum_equiv {X ι : Type*} [TopologicalSpace X]
    (V : X → X → ℝ≥0∞) (c : Configuration X) (W : Set X) (e : ι ≃ c.support) :
    orderedWindowEnergy V c W =
      ∑' i : ι, W.indicator
        (fun p => ∑' j : ι, ({p}ᶜ : Set X).indicator (V p) (e j : X)) (e i : X) := by
  unfold orderedWindowEnergy
  rw [← e.tsum_eq]
  refine tsum_congr fun i => ?_
  by_cases h : (e i : X) ∈ W
  · rw [if_pos h, Set.indicator_of_mem h, ← e.tsum_eq]
    refine tsum_congr fun j => ?_
    by_cases hj : (e j : X) = (e i : X)
    · rw [if_pos hj, Set.indicator_of_notMem]
      simp [hj]
    · rw [if_neg hj, Set.indicator_of_mem]
      simpa using hj
  · rw [if_neg h, Set.indicator_of_notMem h]

section Shift

variable {d : ℕ} (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ]

/-- The lattice as a configuration. -/
def latticeConfiguration : Configuration (Ambient d) where
  support := (Λ : Set (Ambient d))
  finite_on_compacts K hK := by
    have h : (K ∩ (Λ.toAddSubgroup : Set (Ambient d))).Finite := by
      have : DiscreteTopology Λ.toAddSubgroup := (inferInstance : DiscreteTopology Λ)
      exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hK.isBounded
        AddSubgroup.isClosed_of_discrete
    rw [Set.inter_comm]
    exact h

/-- The lattice shifted by `u`. -/
def latticeShift (u : Ambient d) : Configuration (Ambient d) :=
  translate u (latticeConfiguration Λ)

theorem latticeShift_support (u : Ambient d) :
    (latticeShift Λ u).support = (fun x => u + x) '' (Λ : Set (Ambient d)) := rfl

theorem mem_latticeShift {u x : Ambient d} : x ∈ (latticeShift Λ u).support ↔ x - u ∈ Λ := by
  rw [latticeShift_support]
  constructor
  · rintro ⟨ℓ, hℓ, rfl⟩
    simpa using hℓ
  · intro h
    exact ⟨x - u, h, by simp⟩

/-- The points of the shifted lattice, indexed by the lattice. -/
def latticeShiftEquiv (u : Ambient d) : Λ ≃ (latticeShift Λ u).support where
  toFun ℓ := ⟨u + ℓ, ⟨ℓ, ℓ.2, rfl⟩⟩
  invFun x := ⟨x - u, (mem_latticeShift Λ).mp x.2⟩
  left_inv ℓ := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)

theorem latticeShiftEquiv_apply (u : Ambient d) (ℓ : Λ) :
    ((latticeShiftEquiv Λ u ℓ : (latticeShift Λ u).support) : Ambient d) = u + ℓ := rfl

theorem tsum_latticeShift (u : Ambient d) (f : Ambient d → ℝ≥0∞) :
    ∑' x : (latticeShift Λ u).support, f x = ∑' ℓ : Λ, f (u + ℓ) :=
  ((latticeShiftEquiv Λ u).tsum_eq (fun x : (latticeShift Λ u).support => f x)).symm

theorem count_latticeShift (u : Ambient d) {W : Set (Ambient d)} (hW : MeasurableSet W) :
    (latticeShift Λ u).count W = ∑' ℓ : Λ, W.indicator (1 : Ambient d → ℝ≥0∞) (u + ℓ) := by
  have h1 : (latticeShift Λ u).count W = countingKernel d (latticeShift Λ u) W :=
    (countingKernel_apply _ hW).symm
  have h2 : countingKernel d (latticeShift Λ u) W =
      ∫⁻ x, W.indicator (1 : Ambient d → ℝ≥0∞) x ∂countingKernel d (latticeShift Λ u) :=
    (lintegral_indicator_one hW).symm
  rw [h1, h2, countingKernel_lintegral_eq_tsum, tsum_latticeShift]

theorem translate_latticeShift (a u : Ambient d) :
    translate a (latticeShift Λ u) = latticeShift Λ (a + u) := by
  apply Configuration.ext
  show (fun x => a + x) '' ((fun x => u + x) '' (Λ : Set (Ambient d))) =
    (fun x => a + u + x) '' (Λ : Set (Ambient d))
  rw [Set.image_image]
  simp only [add_assoc]

theorem latticeShift_add_lattice (u : Ambient d) (ℓ : Λ) :
    latticeShift Λ ((ℓ : Ambient d) + u) = latticeShift Λ u := by
  apply Configuration.ext
  ext x
  rw [mem_latticeShift, mem_latticeShift]
  have hx : x - ((ℓ : Ambient d) + u) = x - u - ℓ := by abel
  rw [hx]
  exact ⟨fun h => by simpa using Λ.add_mem h ℓ.2, fun h => Λ.sub_mem h ℓ.2⟩

omit [DiscreteTopology Λ] in
/-- The lattice energy as a sum over the lattice, with an indicator function. -/
theorem latticeRieszEnergy_coe (s : ℝ) :
    latticeRieszEnergy (Λ : Set (Ambient d)) s =
      ∑' k : Λ, ({0}ᶜ : Set (Ambient d)).indicator (rieszPotential s 0) (k : Ambient d) := by
  unfold latticeRieszEnergy
  refine tsum_congr fun k => ?_
  by_cases h : (k : Ambient d) = 0
  · rw [if_pos h, Set.indicator_of_notMem]
    simp [h]
  · rw [if_neg h, Set.indicator_of_mem]
    simpa using h

omit [DiscreteTopology Λ] in
/-- The energy seen from a point of the shifted lattice is the lattice energy. -/
theorem tsum_riesz_latticeShift (s : ℝ) (u : Ambient d) (ℓ : Λ) :
    ∑' m : Λ, ({u + (ℓ : Ambient d)}ᶜ : Set (Ambient d)).indicator
        (rieszPotential s (u + ℓ)) (u + m) =
      latticeRieszEnergy (Λ : Set (Ambient d)) s := by
  rw [latticeRieszEnergy_coe]
  refine Eq.trans ?_ ((Equiv.subRight ℓ).tsum_eq _)
  refine tsum_congr fun m => ?_
  show _ = ({0}ᶜ : Set (Ambient d)).indicator (rieszPotential s 0) ((m - ℓ : Λ) : Ambient d)
  by_cases hm : m = ℓ
  · subst hm
    rw [Set.indicator_of_notMem (by simp), Set.indicator_of_notMem (by simp)]
  · have h1 : u + (m : Ambient d) ∈ ({u + (ℓ : Ambient d)}ᶜ : Set (Ambient d)) := by
      simpa using hm
    have h2 : ((m - ℓ : Λ) : Ambient d) ∈ ({0}ᶜ : Set (Ambient d)) := by
      simpa [sub_eq_zero] using hm
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
    unfold rieszPotential
    rw [dist_add_left, dist_zero_left, Submodule.coe_sub, ← dist_eq_norm, dist_comm]

theorem orderedWindowEnergy_latticeShift (s : ℝ) (u : Ambient d) (W : Set (Ambient d)) :
    orderedWindowEnergy (rieszPotential s) (latticeShift Λ u) W =
      ∑' ℓ : Λ, W.indicator (fun _ => latticeRieszEnergy (Λ : Set (Ambient d)) s)
        (u + (ℓ : Ambient d)) := by
  rw [orderedWindowEnergy_eq_tsum_equiv _ _ _ (latticeShiftEquiv Λ u)]
  refine tsum_congr fun ℓ => ?_
  show W.indicator (fun p => ∑' m : Λ, ({p}ᶜ : Set (Ambient d)).indicator (rieszPotential s p)
      (u + (m : Ambient d))) (u + (ℓ : Ambient d)) = _
  by_cases h : u + (ℓ : Ambient d) ∈ W
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, tsum_riesz_latticeShift]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]

end Shift

section Law

variable {d : ℕ} (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

theorem measurable_latticeShift : Measurable (latticeShift Λ) := by
  refine Configuration.measurable_of_counts fun W hW => ?_
  simp_rw [count_latticeShift Λ _ hW]
  exact Measurable.tsum fun ℓ =>
    (measurable_one.indicator hW).comp (measurable_add_const (ℓ : Ambient d))

/-- **Unfolding**: the integral over a fundamental domain of the sum over the lattice. -/
theorem lintegral_lattice_unfold {D : Set (Ambient d)} (hD : IsAddFundamentalDomain Λ D volume)
    {f : Ambient d → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ u in D, ∑' ℓ : Λ, f (u + ℓ) = ∫⁻ x, f x := by
  have : VAddInvariantMeasure Λ (Ambient d) volume :=
    inferInstanceAs (VAddInvariantMeasure Λ.toAddSubgroup (Ambient d) volume)
  rw [lintegral_tsum (f := fun (ℓ : Λ) (u : Ambient d) => f (u + ℓ))
      fun ℓ => (hf.comp (measurable_add_const (ℓ : Ambient d))).aemeasurable,
    hD.lintegral_eq_tsum'' f]
  refine tsum_congr fun ℓ => ?_
  simp only [Submodule.vadd_def, vadd_eq_add, add_comm]

/-- The law of the lattice shifted by a point of `D`, distributed by Lebesgue measure. -/
def latticeShiftLaw (D : Set (Ambient d)) : Measure (Configuration (Ambient d)) :=
  (volume.restrict D).map (latticeShift Λ)

theorem isProbabilityMeasure_latticeShiftLaw {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (hcov : ZLattice.covolume Λ volume = 1) :
    IsProbabilityMeasure (latticeShiftLaw Λ D) := by
  constructor
  rw [latticeShiftLaw, Measure.map_apply (measurable_latticeShift Λ) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]
  rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hD, Measure.real] at hcov
  exact (ENNReal.toReal_eq_one_iff _).mp hcov

theorem isStationary_latticeShiftLaw {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) : IsStationary (latticeShiftLaw Λ D) := by
  intro a
  have hS := measurable_latticeShift Λ
  refine ⟨measurable_translate a, Measure.ext fun A hA => ?_⟩
  have hB : MeasurableSet (latticeShift Λ ⁻¹' A) := hS hA
  have : VAddInvariantMeasure Λ (Ambient d) volume :=
    inferInstanceAs (VAddInvariantMeasure Λ.toAddSubgroup (Ambient d) volume)
  have : VAddCommClass (Ambient d) Λ (Ambient d) := ⟨fun b ℓ x => by
    simp only [Submodule.vadd_def, vadd_eq_add]
    exact add_left_comm _ _ _⟩
  have hinv : ∀ g : Λ, (fun x : Ambient d => g +ᵥ x) ⁻¹' (latticeShift Λ ⁻¹' A) =
      latticeShift Λ ⁻¹' A := by
    intro g
    ext x
    show latticeShift Λ (g +ᵥ x) ∈ A ↔ latticeShift Λ x ∈ A
    rw [Submodule.vadd_def, vadd_eq_add, latticeShift_add_lattice]
  have hpre : latticeShift Λ ⁻¹' (translate a ⁻¹' A) ∩ D =
      (fun x => a + x) ⁻¹' (latticeShift Λ ⁻¹' A ∩ (a +ᵥ D)) := by
    ext x
    constructor
    · rintro ⟨hx, hxD⟩
      have hx' : translate a (latticeShift Λ x) ∈ A := hx
      rw [translate_latticeShift] at hx'
      exact ⟨hx', Set.vadd_mem_vadd_set hxD⟩
    · rintro ⟨hx, hxD⟩
      have hx' : latticeShift Λ (a + x) ∈ A := hx
      rw [← translate_latticeShift] at hx'
      obtain ⟨y, hy, hyx⟩ := Set.mem_vadd_set.mp hxD
      have hyx' : y = x := add_left_cancel (a := a) (by simpa using hyx)
      exact ⟨hx', hyx' ▸ hy⟩
  rw [Measure.map_apply (measurable_translate a) hA, latticeShiftLaw,
    Measure.map_apply hS (measurable_translate a hA), Measure.map_apply hS hA,
    Measure.restrict_apply (hS (measurable_translate a hA)), Measure.restrict_apply hB, hpre,
    measure_preimage_add]
  exact (hD.vadd_of_comm a).measure_set_eq hD hB hinv

theorem hasIntensity_latticeShiftLaw {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) : HasIntensity (latticeShiftLaw Λ D) 1 := by
  intro W hW
  rw [latticeShiftLaw, lintegral_map (Configuration.measurable_count hW)
    (measurable_latticeShift Λ)]
  simp_rw [count_latticeShift Λ _ hW]
  rw [lintegral_lattice_unfold Λ hD (measurable_one.indicator hW), lintegral_indicator_one hW,
    one_mul]

theorem rieszEnergy_latticeShiftLaw {D : Set (Ambient d)}
    (hD : IsAddFundamentalDomain Λ D volume) (s : ℝ) :
    rieszEnergy s (latticeShiftLaw Λ D) = latticeRieszEnergy (Λ : Set (Ambient d)) s := by
  rw [rieszEnergy, latticeShiftLaw, lintegral_map (measurable_rieszWindowEnergy s)
    (measurable_latticeShift Λ)]
  simp_rw [orderedWindowEnergy_latticeShift]
  rw [lintegral_lattice_unfold Λ hD (measurable_const.indicator (measurable_unitWindow d)),
    lintegral_indicator_const (measurable_unitWindow d), volume_unitWindow, mul_one]

/-- **The uniformly shifted lattice.** For a lattice of covolume one there is a stationary law of
intensity one whose Riesz energy is the lattice energy, for every exponent. -/
theorem exists_stationary_law_latticeRieszEnergy (hcov : ZLattice.covolume Λ volume = 1) :
    ∃ μ : Measure (Configuration (Ambient d)), IsProbabilityMeasure μ ∧ IsStationary μ ∧
      HasIntensity μ 1 ∧
        ∀ s : ℝ, rieszEnergy s μ = latticeRieszEnergy (Λ : Set (Ambient d)) s := by
  have hD : IsAddFundamentalDomain Λ
      (ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ)) volume :=
    ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ Λ) volume
  exact ⟨latticeShiftLaw Λ _, isProbabilityMeasure_latticeShiftLaw Λ hD hcov,
    isStationary_latticeShiftLaw Λ hD, hasIntensity_latticeShiftLaw Λ hD,
    fun s => rieszEnergy_latticeShiftLaw Λ hD s⟩

end Law

/-- The shifted `E8` lattice: a stationary law of intensity one with the `E8` energy. -/
theorem e8_exists_stationary_law :
    ∃ μ : Measure (Configuration (Ambient 8)), IsProbabilityMeasure μ ∧ IsStationary μ ∧
      HasIntensity μ 1 ∧ ∀ s : ℝ, rieszEnergy s μ = latticeRieszEnergy e8Set s := by
  have h := exists_stationary_law_latticeRieszEnergy e8Lattice e8Lattice_covolume
  rwa [coe_e8Lattice] at h

/-- The shifted Leech lattice: a stationary law of intensity one with the Leech energy. -/
theorem leech_exists_stationary_law :
    ∃ μ : Measure (Configuration (Ambient 24)), IsProbabilityMeasure μ ∧ IsStationary μ ∧
      HasIntensity μ 1 ∧ ∀ s : ℝ, rieszEnergy s μ = latticeRieszEnergy leechSet s := by
  have h := exists_stationary_law_latticeRieszEnergy leechLattice leechLattice_covolume
  rwa [coe_leechLattice] at h

/-- **The hypotheses of the `E8` crystallization theorem are satisfiable**: one law satisfies them
for every `s > 8` and every `δ > 0`, with excess zero. -/
theorem e8_hypotheses_satisfiable :
    ∃ μ : Measure (Configuration (Ambient 8)), IsProbabilityMeasure μ ∧ IsStationary μ ∧
      HasIntensity μ 1 ∧ ∀ s : ℝ, (8 : ℝ) < s →
        rieszEnergy s μ = latticeRieszEnergy e8Set s ∧ ∀ δ : ℝ, 0 < δ →
          HasRieszExcessAtMost s μ (latticeRieszEnergy e8Set s) (ENNReal.ofReal δ) := by
  obtain ⟨μ, hp, hst, hi, he⟩ := e8_exists_stationary_law
  refine ⟨μ, hp, hst, hi, fun s hs => ⟨he s, fun δ _ => ⟨e8_latticeRieszEnergy_ne_top hs, ?_⟩⟩⟩
  rw [he s]
  exact le_self_add

/-- **The hypotheses of the Leech crystallization theorem are satisfiable**: one law satisfies
them for every `s > 24` and every `δ > 0`, with excess zero. -/
theorem leech_hypotheses_satisfiable :
    ∃ μ : Measure (Configuration (Ambient 24)), IsProbabilityMeasure μ ∧ IsStationary μ ∧
      HasIntensity μ 1 ∧ ∀ s : ℝ, (24 : ℝ) < s →
        rieszEnergy s μ = latticeRieszEnergy leechSet s ∧ ∀ δ : ℝ, 0 < δ →
          HasRieszExcessAtMost s μ (latticeRieszEnergy leechSet s) (ENNReal.ofReal δ) := by
  obtain ⟨μ, hp, hst, hi, he⟩ := leech_exists_stationary_law
  refine ⟨μ, hp, hst, hi, fun s hs =>
    ⟨he s, fun δ _ => ⟨leech_latticeRieszEnergy_ne_top hs, ?_⟩⟩⟩
  rw [he s]
  exact le_self_add

end E8Leech
