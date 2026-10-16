import E8Leech.FiniteAtomicSupport
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Finite products of kernels with pointwise finite fibers -/

noncomputable section
namespace E8Leech
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

theorem measurable_pi_measure_of_finite_fibers
    (κ : ∀ i, Kernel Ω (X i)) (hκ : ∀ i ω, IsFiniteMeasure (κ i ω)) :
    Measurable (fun ω => Measure.pi (fun i => κ i ω)) := by
  have hbox (s : ∀ i, Set (X i)) :
      (fun ω => Measure.pi (fun i => κ i ω) (Set.pi univ s)) =
        fun ω => ∏ i, κ i ω (s i) := by
    funext ω
    let inst (i : ι) : IsFiniteMeasure (κ i ω) := hκ i ω
    exact Measure.pi_pi _ _
  have huniv : (fun ω => Measure.pi (fun i => κ i ω) univ) =
      fun ω => ∏ i, κ i ω univ := by
    funext ω
    let inst (i : ι) : IsFiniteMeasure (κ i ω) := hκ i ω
    exact Measure.pi_univ _
  apply Measurable.measure_of_isPiSystem generateFrom_pi.symm isPiSystem_pi _
  · rw [huniv]
    exact Finset.measurable_prod _ fun i _ =>
      (Measure.measurable_coe MeasurableSet.univ).comp (κ i).measurable
  · rintro _ ⟨s, hs, rfl⟩
    rw [hbox]
    exact Finset.measurable_prod _ fun i _ =>
      (Measure.measurable_coe (hs i (mem_univ i))).comp (κ i).measurable

def finitePiKernel (κ : ∀ i, Kernel Ω (X i)) (hκ : ∀ i ω, IsFiniteMeasure (κ i ω)) :
    Kernel Ω (∀ i, X i) where
  toFun ω := Measure.pi (fun i => κ i ω)
  measurable' := measurable_pi_measure_of_finite_fibers κ hκ

theorem finitePiKernel_finite (κ : ∀ i, Kernel Ω (X i)) (hκ : ∀ i ω, IsFiniteMeasure (κ i ω))
    (ω : Ω) : IsFiniteMeasure (finitePiKernel κ hκ ω) := by
  let inst (i : ι) : IsFiniteMeasure (κ i ω) := hκ i ω
  change IsFiniteMeasure (Measure.pi (fun i => κ i ω))
  infer_instance

theorem finitePiKernel_singleton [∀ i, MeasurableSingletonClass (X i)]
    (κ : ∀ i, Kernel Ω (X i)) (hκ : ∀ i ω, IsFiniteMeasure (κ i ω)) (ω : Ω) (v : ∀ i, X i) :
    finitePiKernel κ hκ ω {v} = ∏ i, κ i ω {v i} := by
  let inst (i : ι) : IsFiniteMeasure (κ i ω) := hκ i ω
  exact Measure.pi_singleton _ v

theorem finitePiKernel_atom_ne_zero [∀ i, MeasurableSingletonClass (X i)]
    (κ : ∀ i, Kernel Ω (X i)) (hκ : ∀ i ω, IsFiniteMeasure (κ i ω)) (ω : Ω) (v : ∀ i, X i)
    (hv : ∀ i, κ i ω {v i} ≠ 0) : finitePiKernel κ hκ ω {v} ≠ 0 := by
  rw [finitePiKernel_singleton]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hv i)

theorem finitePiKernel_compl_pi_eq_zero
    (κ : ∀ i, Kernel Ω (X i)) (hκ : ∀ i ω, IsFiniteMeasure (κ i ω)) (ω : Ω)
    (S : ∀ i, Set (X i)) (hS : ∀ i, MeasurableSet (S i))
    (hz : ∀ i, κ i ω (S i)ᶜ = 0) :
    finitePiKernel κ hκ ω (Set.pi univ S)ᶜ = 0 := by
  let inst (i : ι) : IsFiniteMeasure (κ i ω) := hκ i ω
  let := finitePiKernel_finite κ hκ ω
  have hm : MeasurableSet (Set.pi univ S) := MeasurableSet.pi (Set.to_countable _) fun i _ => hS i
  rw [measure_compl hm (measure_ne_top _ _)]
  change Measure.pi (fun i => κ i ω) univ - Measure.pi (fun i => κ i ω) (Set.pi univ S) = 0
  rw [Measure.pi_univ, Measure.pi_pi]
  have he : ∀ i, κ i ω (S i) = κ i ω univ := fun i => measure_of_measure_compl_eq_zero (hz i)
  simp_rw [he]
  exact tsub_self _

end E8Leech
