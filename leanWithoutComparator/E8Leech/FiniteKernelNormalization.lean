import E8Leech.FiniteAtomicSupport
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! # Probability normalization for kernels with pointwise finite fibers -/

noncomputable section
namespace E8Leech
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

def normalizedFiniteKernel (κ : Kernel Ω X) (x₀ : X) : Kernel Ω X where
  toFun ω := if κ ω univ = 0 then Measure.dirac x₀ else (κ ω univ)⁻¹ • κ ω
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    change Measurable (fun ω =>
      (if κ ω univ = 0 then Measure.dirac x₀ else (κ ω univ)⁻¹ • κ ω) S)
    have he : (fun ω => (if κ ω univ = 0 then Measure.dirac x₀ else
        (κ ω univ)⁻¹ • κ ω) S) =
        fun ω => if κ ω univ = 0 then Measure.dirac x₀ S else (κ ω univ)⁻¹ * κ ω S := by
      funext ω
      split_ifs <;> rfl
    rw [he]
    exact Measurable.ite
      (measurableSet_eq_fun (κ.measurable_coe MeasurableSet.univ) measurable_const)
      measurable_const ((κ.measurable_coe MeasurableSet.univ).inv.mul (κ.measurable_coe hS))

theorem normalizedFiniteKernel_apply_of_ne (κ : Kernel Ω X) (x₀ : X) (ω : Ω)
    (hω : κ ω univ ≠ 0) : normalizedFiniteKernel κ x₀ ω = (κ ω univ)⁻¹ • κ ω := by
  change (if κ ω univ = 0 then _ else _) = _
  rw [if_neg hω]

theorem normalizedFiniteKernel_apply_of_zero (κ : Kernel Ω X) (x₀ : X) (ω : Ω)
    (hω : κ ω univ = 0) : normalizedFiniteKernel κ x₀ ω = Measure.dirac x₀ := by
  change (if κ ω univ = 0 then _ else _) = _
  rw [if_pos hω]

theorem normalizedFiniteKernel_isMarkov (κ : Kernel Ω X)
    (hκ : ∀ ω, IsFiniteMeasure (κ ω)) (x₀ : X) :
    IsMarkovKernel (normalizedFiniteKernel κ x₀) := by
  constructor
  intro ω
  constructor
  by_cases hω : κ ω univ = 0
  · rw [normalizedFiniteKernel_apply_of_zero κ x₀ ω hω]
    exact Measure.dirac_apply_of_mem (Set.mem_univ x₀)
  · let := hκ ω
    rw [normalizedFiniteKernel_apply_of_ne κ x₀ ω hω, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hω (measure_ne_top _ _)

theorem normalizedFiniteKernel_eq_of_fiber_eq (κ : Kernel Ω X) (x₀ : X)
    {ω ω' : Ω} (h : κ ω = κ ω') :
    normalizedFiniteKernel κ x₀ ω = normalizedFiniteKernel κ x₀ ω' := by
  change (if κ ω univ = 0 then _ else _) = (if κ ω' univ = 0 then _ else _)
  rw [h]

theorem normalizedFiniteKernel_null_of_ne (κ : Kernel Ω X) (x₀ : X) (ω : Ω)
    (hω : κ ω univ ≠ 0) {S : Set X} (hS : κ ω S = 0) :
    normalizedFiniteKernel κ x₀ ω S = 0 := by
  rw [normalizedFiniteKernel_apply_of_ne κ x₀ ω hω, Measure.smul_apply, hS, smul_zero]

end E8Leech
