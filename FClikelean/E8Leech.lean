import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace


/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

variable {X : Type*} [TopologicalSpace X]
structure Configuration (X : Type*) [TopologicalSpace X] where
  support : Set X
  finite_on_compacts : ∀ K : Set X, IsCompact K → (support ∩ K).Finite

namespace Configuration
instance : Coe (Configuration X) (Set X) := ⟨Configuration.support⟩

def mapHomeomorph (e : X ≃ₜ X) (c : Configuration X) : Configuration X where
  support := e '' c.support
  finite_on_compacts K hK := by
    have hpre : IsCompact (e ⁻¹' K) := by
      have heq : e ⁻¹' K = e.symm '' K := by
        ext x
        constructor
        · intro hx
          exact ⟨e x, hx, e.symm_apply_apply x⟩
        · rintro ⟨y, hy, rfl⟩
          simpa using hy
      rw [heq]
      exact hK.image e.symm.continuous
    have hfinite := (c.finite_on_compacts (e ⁻¹' K) hpre).image e
    have heq : e '' (c.support ∩ e ⁻¹' K) = e '' c.support ∩ K := by
      exact Set.image_inter_preimage e c.support K
    rwa [heq] at hfinite

section
variable [MeasurableSpace X] [MeasurableSingletonClass X]
def count (c : Configuration X) (A : Set X) : ℝ≥0∞ :=
  Measure.count (c.support ∩ A)

instance : MeasurableSpace (Configuration X) :=
  ⨆ A : {A : Set X // MeasurableSet A},
    MeasurableSpace.comap (fun c : Configuration X => c.count A.1) inferInstance
end
end Configuration
end E8Leech

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)

def translate {d : ℕ} (a : Ambient d) : Configuration (Ambient d) → Configuration (Ambient d) :=
  Configuration.mapHomeomorph (Homeomorph.addLeft a)

def IsStationary {d : ℕ} (μ : Measure (Configuration (Ambient d))) : Prop :=
  ∀ a : Ambient d, MeasurePreserving (translate a) μ μ

def HasIntensity {d : ℕ} (μ : Measure (Configuration (Ambient d))) (ρ : ℝ≥0∞) : Prop :=
  ∀ W : Set (Ambient d), MeasurableSet W →
    (∫⁻ c, c.count W ∂μ) = ρ * volume W

end E8Leech

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

def orderedWindowEnergy {X : Type*} [TopologicalSpace X]
    (V : X → X → ℝ≥0∞) (c : Configuration X) (W : Set X) : ℝ≥0∞ :=
  ∑' x : c.support, if (x : X) ∈ W then
    ∑' y : c.support, if (y : X) = (x : X) then 0 else V x y
    else 0

def rieszPotential {d : ℕ} (s : ℝ) (x y : Ambient d) : ℝ≥0∞ :=
  ENNReal.ofReal (dist x y) ^ (-s)

def unitWindow (d : ℕ) : Set (Ambient d) :=
  {x | ∀ i, x i ∈ Set.Ico (0 : ℝ) 1}

def rieszEnergy {d : ℕ} (s : ℝ) (μ : Measure (Configuration (Ambient d))) : ℝ≥0∞ :=
  ∫⁻ c, orderedWindowEnergy (rieszPotential s) c (unitWindow d) ∂μ

def HasRieszExcessAtMost {d : ℕ} (s : ℝ)
    (μ : Measure (Configuration (Ambient d))) (latticeEnergy δ : ℝ≥0∞) : Prop :=
  latticeEnergy ≠ ∞ ∧ rieszEnergy s μ ≤ latticeEnergy + δ

end E8Leech

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

def e8Numerators : Set (Fin 8 → ℤ) :=
  {z | (∀ i, (2 : ℤ) ∣ z i - z 0) ∧ (4 : ℤ) ∣ ∑ i, z i}

def halfCoordinates (z : Fin 8 → ℤ) : Ambient 8 :=
  WithLp.toLp 2 (fun i => (z i : ℝ) / 2)

def e8Set : Set (Ambient 8) := halfCoordinates '' e8Numerators

end E8Leech

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

def golayBlock : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  !![0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1;
     1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0;
     1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1;
     1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1;
     1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0;
     1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1;
     1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1;
     1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1;
     1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0;
     1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0;
     1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0;
     1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1]

def golayEncode (a : Fin 12 → ZMod 2) : Fin 24 → ZMod 2 :=
  Fin.append a (a ᵥ* golayBlock)

def golayEncoderLinear : (Fin 12 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun := golayEncode
  map_add' a b := by
    ext j
    refine Fin.addCases (m := 12) (n := 12) (fun i => ?_) (fun i => ?_) j
    · simp [golayEncode]
    · simp [golayEncode, add_vecMul, -Fin.natAdd_eq_addNat]
  map_smul' k a := by
    ext j
    refine Fin.addCases (m := 12) (n := 12) (fun i => ?_) (fun i => ?_) j
    · simp [golayEncode]
    · simp [golayEncode, smul_vecMul, -Fin.natAdd_eq_addNat]

def golayCode : Submodule (ZMod 2) (Fin 24 → ZMod 2) := LinearMap.range golayEncoderLinear

end E8Leech

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

def leechResidue (z : Fin 24 → ℤ) (m : ℤ) : Fin 24 → ZMod 2 :=
  fun i => ((z i - m) / 2 : ℤ)

def leechNumerators : Set (Fin 24 → ℤ) :=
  {z | ∃ m : ℤ, (∀ i, (2 : ℤ) ∣ z i - m) ∧
    (8 : ℤ) ∣ (∑ i, z i) - 4 * m ∧ leechResidue z m ∈ golayCode}

def leechCoordinates (z : Fin 24 → ℤ) : Ambient 24 :=
  WithLp.toLp 2 (fun i => (z i : ℝ) / Real.sqrt 8)

def leechSet : Set (Ambient 24) := leechCoordinates '' leechNumerators

end E8Leech

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

def observationRadius (δ : ℝ) : ℝ :=
  Real.log (1 / δ) / Real.log (Real.log (1 / δ))

def latticeRieszEnergy {d : ℕ} (Λ : Set (Ambient d)) (s : ℝ) : ℝ≥0∞ :=
  ∑' y : Λ, if (y : Ambient d) = 0 then 0 else rieszPotential s 0 (y : Ambient d)

def LocalCrystal {d : ℕ} (Λ : Set (Ambient d))
    (c : Configuration (Ambient d)) (R error loss : ℝ) : Prop :=
  (∃ Φ : Ambient d ≃ᵢ Ambient d, ∃ Z : Finset (Ambient d),
    (↑Z : Set (Ambient d)) ⊆ Λ ∧
    (∀ x ∈ c.support ∩ Metric.closedBall 0 R, ∃ z ∈ Z, dist x (Φ z) ≤ error) ∧
    (∀ z ∈ Z, ∃ x ∈ c.support ∩ Metric.closedBall 0 R, dist (Φ z) x ≤ error)) ∧
  ENNReal.ofReal (1 - loss) * volume (Metric.closedBall (0 : Ambient d) R) ≤
    c.count (Metric.closedBall 0 R)

end E8Leech

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

def potentialMixture {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (ν : Measure Θ) (V : Θ → Ambient d → Ambient d → ℝ≥0∞)
    (x y : Ambient d) : ℝ≥0∞ := ∫⁻ θ, V θ x y ∂ν

def latticePotentialEnergy {d : ℕ} (Λ : Set (Ambient d))
    (V : Ambient d → Ambient d → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' y : Λ, if (y : Ambient d) = 0 then 0 else V 0 y

end E8Leech

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

def gaussianKernel {d : ℕ} (α : ℝ) (x : Ambient d) : ℝ :=
  Real.exp (-α * ‖x‖ ^ 2)

end E8Leech

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

def gaussianPotential {d : ℕ} (α : ℝ) (x y : Ambient d) : ℝ≥0∞ :=
  ENNReal.ofReal (gaussianKernel α (x - y))

def positiveGaussianMixturePotential {d : ℕ} (ν : Measure ℝ)
    (x y : Ambient d) : ℝ≥0∞ :=
  potentialMixture (ν.restrict (Ioi 0)) (gaussianPotential (d := d)) x y

end E8Leech

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

def potentialEnergy {d : ℕ} (P : Ambient d → Ambient d → ℝ≥0∞)
    (μ : Measure (Configuration (Ambient d))) : ℝ≥0∞ :=
  ∫⁻ z, orderedWindowEnergy P z (unitWindow d) ∂μ

def HasPotentialExcessAtMost {d : ℕ} (P : Ambient d → Ambient d → ℝ≥0∞)
    (μ : Measure (Configuration (Ambient d))) (L δ : ℝ≥0∞) : Prop :=
  L ≠ ∞ ∧ potentialEnergy P μ ≤ L + δ

end E8Leech

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

def PotentialCrystallizationTargetForExponent {d : ℕ} (Λ : Set (Ambient d))
    (P : Ambient d → Ambient d → ℝ≥0∞) (γ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
    ∀ μ : Measure (Configuration (Ambient d)),
      IsProbabilityMeasure μ → IsStationary μ → HasIntensity μ 1 →
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        HasPotentialExcessAtMost P μ (latticePotentialEnergy Λ P) (ENNReal.ofReal δ) →
        ∃ G : Set (Configuration (Ambient d)), MeasurableSet G ∧
          G ⊆ {z | LocalCrystal Λ z (observationRadius δ)
            (C * δ ^ γ) (C * observationRadius δ ^ (-1 / 2 : ℝ))} ∧
          ENNReal.ofReal (1 - C * observationRadius δ ^ (-1 / 2 : ℝ)) ≤ μ G

end E8Leech

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

section
variable {d : ℕ} (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ]
def latticeConfiguration : Configuration (Ambient d) where
  support := (Λ : Set (Ambient d))
  finite_on_compacts K hK := by
    have h : (K ∩ (Λ.toAddSubgroup : Set (Ambient d))).Finite := by
      have : DiscreteTopology Λ.toAddSubgroup := (inferInstance : DiscreteTopology Λ)
      exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hK.isBounded
        AddSubgroup.isClosed_of_discrete
    rw [Set.inter_comm]
    exact h

def latticeShift (u : Ambient d) : Configuration (Ambient d) :=
  translate u (latticeConfiguration Λ)

variable [IsZLattice ℝ Λ]

def latticeShiftLaw (D : Set (Ambient d)) : Measure (Configuration (Ambient d)) :=
  (volume.restrict D).map (latticeShift Λ)

end
end E8Leech

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

structure LatticeOrientation (d : ℕ) where
  isometry : Ambient d ≃ₗᵢ[ℝ] Ambient d

instance {d : ℕ} : TopologicalSpace (LatticeOrientation d) :=
  TopologicalSpace.induced (fun Q : LatticeOrientation d => Q.isometry.toContinuousLinearMap)
    inferInstance

instance {d : ℕ} : SecondCountableTopology (LatticeOrientation d) :=
  TopologicalSpace.secondCountableTopology_induced _ _ _

instance {d : ℕ} : MeasurableSpace (LatticeOrientation d) := borel _

instance {d : ℕ} : BorelSpace (LatticeOrientation d) := ⟨rfl⟩

def rotateConfiguration {d : ℕ} (Q : Ambient d ≃ₗᵢ[ℝ] Ambient d)
    (c : Configuration (Ambient d)) : Configuration (Ambient d) :=
  c.mapHomeomorph Q.toHomeomorph

def rotatedLatticeShift {d : ℕ} (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ]
    (Q : LatticeOrientation d) (u : Ambient d) : Configuration (Ambient d) :=
  rotateConfiguration Q.isometry (latticeShift Λ u)

def rotatedLatticeShiftLaw {d : ℕ} (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ]
    (D : Set (Ambient d)) (Q : LatticeOrientation d) : Measure (Configuration (Ambient d)) :=
  (latticeShiftLaw Λ D).map (rotateConfiguration Q.isometry)

end E8Leech

/-! Trusted mathematical definition copies; no crystallization proofs.
Module boundaries preserve the proof sources' module-local auxiliary-proof naming.
Coordinate/Golay attribution: THIRD_PARTY.txt and original source headers. -/
noncomputable section
namespace E8Leech
open Set MeasureTheory Matrix
open scoped ENNReal Classical

def orientationMixtureLaw {d : ℕ} (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ]
    (D : Set (Ambient d)) (σ : Measure (LatticeOrientation d)) :
    Measure (Configuration (Ambient d)) := σ.bind (rotatedLatticeShiftLaw Λ D)

end E8Leech

noncomputable section
namespace E8LeechFC
open E8Leech Set MeasureTheory
open scoped ENNReal

theorem e8_quantitative_crystallization {s γ : ℝ} (hs : (8 : ℝ) < s) (hγ : 0 < γ) (hγlt : γ < 1 / 12) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
      ∀ μ : Measure (Configuration (Ambient 8)),
        IsProbabilityMeasure μ → IsStationary μ → HasIntensity μ 1 →
        ∀ δ : ℝ, 0 < δ → δ < δ₀ →
          rieszEnergy s μ ≤ latticeRieszEnergy e8Set s + ENNReal.ofReal δ →
          ∃ G : Set (Configuration (Ambient 8)), MeasurableSet G ∧
            G ⊆ {c | LocalCrystal e8Set c (observationRadius δ)
              (C * δ ^ γ) (C * observationRadius δ ^ (-1 / 2 : ℝ))} ∧
            ENNReal.ofReal (1 - C * observationRadius δ ^ (-1 / 2 : ℝ)) ≤ μ G := by
  sorry

theorem e8_gaussian_crystallization {α γ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hγlt : γ < 1 / 12) :
    PotentialCrystallizationTargetForExponent e8Set (gaussianPotential α) γ := by
  sorry

theorem e8_positiveGaussianMixture_crystallization (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞)
    {γ : ℝ} (hγ : 0 < γ) (hγlt : γ < 1 / 12) :
    PotentialCrystallizationTargetForExponent e8Set (positiveGaussianMixturePotential ν) γ := by
  sorry

theorem e8_riesz_zero_excess_iff_ae_isometric_lattice {s : ℝ} (hs : (8 : ℝ) < s)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    rieszEnergy s μ = latticeRieszEnergy e8Set s ↔
      ∀ᵐ c ∂μ, ∃ Φ : Ambient 8 ≃ᵢ Ambient 8, c.support = Φ '' e8Set := by
  sorry

theorem e8_gaussian_zero_excess_iff_ae_isometric_lattice {α : ℝ} (hα : 0 < α)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    potentialEnergy (gaussianPotential α) μ = latticePotentialEnergy e8Set (gaussianPotential α) ↔
      ∀ᵐ c ∂μ, ∃ Φ : Ambient 8 ≃ᵢ Ambient 8, c.support = Φ '' e8Set := by
  sorry

theorem e8_positiveGaussianMixture_zero_excess_iff_ae_isometric_lattice
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient 8))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    potentialEnergy (positiveGaussianMixturePotential ν) μ =
      latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ↔
      ∀ᵐ c ∂μ, ∃ Φ : Ambient 8 ≃ᵢ Ambient 8, c.support = Φ '' e8Set := by
  sorry

theorem leech_quantitative_crystallization {s γ : ℝ} (hs : (24 : ℝ) < s) (hγ : 0 < γ) (hγlt : γ < 1 / 12) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
      ∀ μ : Measure (Configuration (Ambient 24)),
        IsProbabilityMeasure μ → IsStationary μ → HasIntensity μ 1 →
        ∀ δ : ℝ, 0 < δ → δ < δ₀ →
          rieszEnergy s μ ≤ latticeRieszEnergy leechSet s + ENNReal.ofReal δ →
          ∃ G : Set (Configuration (Ambient 24)), MeasurableSet G ∧
            G ⊆ {c | LocalCrystal leechSet c (observationRadius δ)
              (C * δ ^ γ) (C * observationRadius δ ^ (-1 / 2 : ℝ))} ∧
            ENNReal.ofReal (1 - C * observationRadius δ ^ (-1 / 2 : ℝ)) ≤ μ G := by
  sorry

theorem leech_gaussian_crystallization {α γ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hγlt : γ < 1 / 12) :
    PotentialCrystallizationTargetForExponent leechSet (gaussianPotential α) γ := by
  sorry

theorem leech_positiveGaussianMixture_crystallization (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞)
    {γ : ℝ} (hγ : 0 < γ) (hγlt : γ < 1 / 12) :
    PotentialCrystallizationTargetForExponent leechSet (positiveGaussianMixturePotential ν) γ := by
  sorry

theorem leech_riesz_zero_excess_iff_ae_isometric_lattice {s : ℝ} (hs : (24 : ℝ) < s)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    rieszEnergy s μ = latticeRieszEnergy leechSet s ↔
      ∀ᵐ c ∂μ, ∃ Φ : Ambient 24 ≃ᵢ Ambient 24, c.support = Φ '' leechSet := by
  sorry

theorem leech_gaussian_zero_excess_iff_ae_isometric_lattice {α : ℝ} (hα : 0 < α)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    potentialEnergy (gaussianPotential α) μ = latticePotentialEnergy leechSet (gaussianPotential α) ↔
      ∀ᵐ c ∂μ, ∃ Φ : Ambient 24 ≃ᵢ Ambient 24, c.support = Φ '' leechSet := by
  sorry

theorem leech_positiveGaussianMixture_zero_excess_iff_ae_isometric_lattice
    (ν : Measure ℝ) (hν : ν (Ioi 0) ≠ 0)
    (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞)
    (μ : Measure (Configuration (Ambient 24))) [IsProbabilityMeasure μ]
    (hμ : IsStationary μ) (hρ : HasIntensity μ 1) :
    potentialEnergy (positiveGaussianMixturePotential ν) μ =
      latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ↔
      ∀ᵐ c ∂μ, ∃ Φ : Ambient 24 ≃ᵢ Ambient 24, c.support = Φ '' leechSet := by
  sorry

theorem stationary_exact_lattice_law {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (Ambient d))
    (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hb : Λ = Submodule.span ℤ (Set.range b))
    {D : Set (Ambient d)} (hD : IsAddFundamentalDomain Λ D volume)
    (hcov : ZLattice.covolume Λ volume = 1)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (hgood : ∀ᵐ c ∂μ, ∃ Φ : Ambient d ≃ᵢ Ambient d, c.support = Φ '' (Λ : Set (Ambient d))) :
    ∃ σ : Measure (LatticeOrientation d), IsProbabilityMeasure σ ∧ μ = orientationMixtureLaw Λ D σ := by
  sorry

end E8LeechFC
