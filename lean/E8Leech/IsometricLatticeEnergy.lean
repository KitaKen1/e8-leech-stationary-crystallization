import E8Leech.ZeroExcessExactLattice

/-!
# Exact energy on arbitrary isometric lattice configurations

For an isometry-invariant potential, every point of an affine lattice sees
the same full lattice energy. Averaging a unit-window count of intensity one
therefore gives zero excess. No potential measurability or finite energy is
needed for this extended-nonnegative equality.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal Classical

def IsometryInvariantPotential {d : ℕ} (P : Ambient d → Ambient d → ℝ≥0∞) : Prop :=
  ∀ Φ : Ambient d ≃ᵢ Ambient d, ∀ x y, P (Φ x) (Φ y) = P x y

theorem rieszPotential_isometryInvariant {d : ℕ} (s : ℝ) :
    IsometryInvariantPotential (rieszPotential (d := d) s) := by
  intro Φ x y
  simp only [rieszPotential, Φ.dist_eq]

theorem gaussianPotential_isometryInvariant {d : ℕ} (α : ℝ) :
    IsometryInvariantPotential (gaussianPotential (d := d) α) := by
  intro Φ x y
  simp only [gaussianPotential, gaussianKernel, ← dist_eq_norm, Φ.dist_eq]

theorem positiveGaussianMixturePotential_isometryInvariant {d : ℕ} (ν : Measure ℝ) :
    IsometryInvariantPotential (positiveGaussianMixturePotential (d := d) ν) := by
  intro Φ x y
  unfold positiveGaussianMixturePotential potentialMixture
  exact lintegral_congr fun α => gaussianPotential_isometryInvariant α Φ x y

def latticeIsometryConfiguration {d : ℕ} (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ]
    (Φ : Ambient d ≃ᵢ Ambient d) : Configuration (Ambient d) :=
  (latticeConfiguration Λ).mapHomeomorph Φ.toHomeomorph

def latticeIsometryEquiv {d : ℕ} (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ]
    (Φ : Ambient d ≃ᵢ Ambient d) : Λ ≃ (latticeIsometryConfiguration Λ Φ).support where
  toFun z := ⟨Φ z, ⟨z, z.2, rfl⟩⟩
  invFun x := ⟨Φ.symm x, by
    obtain ⟨z, hz, he⟩ := x.2
    rw [← he]
    change Φ.symm (Φ z) ∈ Λ
    rw [Φ.symm_apply_apply]
    exact hz⟩
  left_inv z := Subtype.ext (Φ.symm_apply_apply z)
  right_inv x := Subtype.ext (Φ.apply_symm_apply x)

theorem tsum_isometric_lattice_potential {d : ℕ} (Λ : Submodule ℤ (Ambient d))
    (P : Ambient d → Ambient d → ℝ≥0∞) (hP : IsometryInvariantPotential P)
    (Φ : Ambient d ≃ᵢ Ambient d) (z : Λ) :
    (∑' m : Λ, if Φ m = Φ z then 0 else P (Φ z) (Φ m)) =
      latticePotentialEnergy (Λ : Set (Ambient d)) P := by
  unfold latticePotentialEnergy
  refine Eq.trans ?_ ((Equiv.subRight z).tsum_eq _)
  apply tsum_congr
  intro m
  change (if Φ m = Φ z then 0 else P (Φ z) (Φ m)) =
    if ((m - z : Λ) : Ambient d) = 0 then 0 else P 0 (m - z)
  by_cases hm : m = z
  · subst m
    simp
  · have hΦ : Φ m ≠ Φ z := fun h => hm (Subtype.ext (Φ.injective h))
    have hm0 : ((m - z : Λ) : Ambient d) ≠ 0 := by
      intro h
      exact hm (sub_eq_zero.mp (Subtype.ext h))
    rw [if_neg hΦ, if_neg hm0, hP Φ]
    have hh := hP (IsometryEquiv.addRight (-(z : Ambient d))) z m
    simpa only [IsometryEquiv.addRight_apply, add_neg_cancel, ← sub_eq_add_neg,
      Submodule.coe_sub] using hh.symm

theorem count_eq_tsum_indicator {d : ℕ} (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : MeasurableSet W) :
    c.count W = ∑' x : c.support, if (x : Ambient d) ∈ W then 1 else 0 := by
  rw [← countingKernel_apply c hW, ← lintegral_indicator_one hW,
    countingKernel_lintegral_eq_tsum]
  rfl

theorem orderedWindowEnergy_eq_lattice_mul_count {d : ℕ}
    (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ]
    (P : Ambient d → Ambient d → ℝ≥0∞) (hP : IsometryInvariantPotential P)
    (c : Configuration (Ambient d)) (Φ : Ambient d ≃ᵢ Ambient d)
    (hc : c.support = Φ '' (Λ : Set (Ambient d))) {W : Set (Ambient d)} (hW : MeasurableSet W) :
    orderedWindowEnergy P c W = latticePotentialEnergy (Λ : Set (Ambient d)) P * c.count W := by
  have he : c = latticeIsometryConfiguration Λ Φ := Configuration.ext hc
  subst c
  let e := latticeIsometryEquiv Λ Φ
  have he_apply (z : Λ) : ((e z : (latticeIsometryConfiguration Λ Φ).support) : Ambient d) = Φ z := rfl
  have hlocal (x : (latticeIsometryConfiguration Λ Φ).support) :
      (∑' y : (latticeIsometryConfiguration Λ Φ).support,
        if (y : Ambient d) = x then 0 else P x y) = latticePotentialEnergy (Λ : Set (Ambient d)) P := by
    rw [← e.tsum_eq]
    have hh := tsum_isometric_lattice_potential Λ P hP Φ (e.symm x)
    have hx : Φ (e.symm x) = x := congrArg Subtype.val (e.apply_symm_apply x)
    simpa only [he_apply, hx] using hh
  rw [count_eq_tsum_indicator _ hW, ← ENNReal.tsum_mul_left]
  unfold orderedWindowEnergy
  apply tsum_congr
  intro x
  by_cases hx : (x : Ambient d) ∈ W
  · simp only [if_pos hx, mul_one]
    convert hlocal x using 1
    apply tsum_congr
    intro y
    by_cases hy : (y : Ambient d) = x <;> simp [hy]
  · simp [hx]

theorem potentialEnergy_eq_lattice_of_ae_isometric_lattice {d : ℕ}
    (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ]
    (P : Ambient d → Ambient d → ℝ≥0∞) (hP : IsometryInvariantPotential P)
    (μ : Measure (Configuration (Ambient d))) (hρ : HasIntensity μ 1)
    (hgood : ∀ᵐ c ∂μ, ∃ Φ : Ambient d ≃ᵢ Ambient d, c.support = Φ '' (Λ : Set (Ambient d))) :
    potentialEnergy P μ = latticePotentialEnergy (Λ : Set (Ambient d)) P := by
  unfold potentialEnergy
  calc
    _ = ∫⁻ c, latticePotentialEnergy (Λ : Set (Ambient d)) P * c.count (unitWindow d) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hgood] with c hc
      obtain ⟨Φ, hΦ⟩ := hc
      exact orderedWindowEnergy_eq_lattice_mul_count Λ P hP c Φ hΦ (measurable_unitWindow d)
    _ = _ := by
      rw [lintegral_const_mul _ (Configuration.measurable_count (measurable_unitWindow d)),
        expected_count_unitWindow μ 1 hρ, mul_one]

end E8Leech
