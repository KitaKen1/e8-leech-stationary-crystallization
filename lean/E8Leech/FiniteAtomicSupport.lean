import E8Leech.CountingKernel

/-!
# Counting the distinct atoms of a finite atomic kernel

Weight each atom by the inverse of its mass. Each distinct atom then contributes
one, independently of its multiplicity. This constructs measurable finite-image
counts without choosing a measurable enumeration or discarding duplicate images.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem count_finite_support_eq_lintegral {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ : Measure X) [IsFiniteMeasure μ]
    (S : Finset X) (hzero : μ (S : Set X)ᶜ = 0)
    (hpos : ∀ x ∈ S, μ {x} ≠ 0) (W : Set X) :
    Measure.count ((S : Set X) ∩ W) =
      ∫⁻ x, W.indicator (fun x => (μ {x})⁻¹) x ∂μ := by
  classical
  have hr : μ.restrict (S : Set X) = μ :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hzero)
  have hs : (S : Set X) ∩ W = (S.filter (fun x => x ∈ W) : Set X) := by
    ext x
    simp
  calc
    Measure.count ((S : Set X) ∩ W) = ∑ x ∈ S, if x ∈ W then (1 : ℝ≥0∞) else 0 := by
      rw [hs, Measure.count_apply_finset]
      simp
    _ = ∫⁻ x in (S : Set X), W.indicator (fun x => (μ {x})⁻¹) x ∂μ := by
      rw [lintegral_finset]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : x ∈ W
      · simp only [h, if_true, Set.indicator_of_mem]
        exact (ENNReal.inv_mul_cancel (hpos x hx) (measure_ne_top μ {x})).symm
      · simp [h]
    _ = ∫⁻ x, W.indicator (fun x => (μ {x})⁻¹) x ∂μ := by rw [hr]

theorem measurable_atom_mass_of_finite_fibers {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
    (κ : Kernel Ω X) (hκ : ∀ ω, IsFiniteMeasure (κ ω))
    (hdiag : MeasurableSet {p : X × X | p.1 = p.2}) :
    Measurable (fun p : Ω × X => κ p.1 {p.2}) := by
  let η : Kernel (Ω × X) X := ⟨fun p => κ p.1, κ.measurable.comp measurable_fst⟩
  have hm := Kernel.measurable_kernel_prodMk_left_of_finite
    (κ := η) (hdiag.preimage (measurable_fst.snd.prodMk measurable_snd))
    (fun p => hκ p.1)
  convert hm using 1
  ext p
  congr 1
  ext x
  simp

theorem measurable_lintegral_finite_fibers_param {Ω A X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace X]
    (κ : Kernel Ω X) (hκ : ∀ ω, IsFiniteMeasure (κ ω))
    (g : A → Ω) (hg : Measurable g) {f : A × X → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun a => ∫⁻ x, f (a, x) ∂κ (g a)) := by
  let η : Kernel A X := ⟨fun a => κ (g a), κ.measurable.comp hg⟩
  exact measurable_lintegral_of_finite_fibers η (fun a => hκ (g a)) hf

theorem measurable_count_finite_atomic_support {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
    (κ : Kernel Ω X) (hκ : ∀ ω, IsFiniteMeasure (κ ω))
    (hdiag : MeasurableSet {p : X × X | p.1 = p.2})
    (S : Ω → Finset X) (hzero : ∀ ω, κ ω (S ω : Set X)ᶜ = 0)
    (hpos : ∀ ω x, x ∈ S ω → κ ω {x} ≠ 0) {W : Set X} (hW : MeasurableSet W) :
    Measurable (fun ω => Measure.count ((S ω : Set X) ∩ W)) := by
  have hm := measurable_lintegral_of_finite_fibers κ hκ
    (((measurable_atom_mass_of_finite_fibers κ hκ hdiag).inv).indicator
      (hW.preimage measurable_snd))
  have he : (fun ω => Measure.count ((S ω : Set X) ∩ W)) =
      fun ω => ∫⁻ x, W.indicator (fun x => (κ ω {x})⁻¹) x ∂κ ω := by
    funext ω
    let := hκ ω
    exact count_finite_support_eq_lintegral (κ ω) (S ω) (hzero ω) (hpos ω) W
  rw [he]
  exact hm

end E8Leech
