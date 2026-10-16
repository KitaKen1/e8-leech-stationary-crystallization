import E8Leech.IsometricLatticeEnergy
import E8Leech.PositiveMixtureMoments

/-!
# Finite lattice mixture energy makes the positive parameter measure sigma-finite

One nonzero lattice vector supplies a strictly positive Gaussian lower bound
on every parameter half-line. This recovers measurability of the mixture from
finite lattice energy, without assuming the entire parameter measure s-finite.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal

theorem e8_measurable_positiveGaussianMixturePotential_of_finite_lattice_energy
    (ν : Measure ℝ) (hbase : latticePotentialEnergy e8Set (positiveGaussianMixturePotential ν) ≠ ∞) :
    Measurable (Function.uncurry (positiveGaussianMixturePotential (d := 8) ν)) := by
  have hz : e8EuclideanBasis 0 ∈ e8Set := by
    rw [← coe_e8Lattice]
    exact Submodule.subset_span ⟨0, rfl⟩
  exact measurable_positiveGaussianMixturePotential_of_lattice ν hz
    (e8EuclideanBasis.ne_zero 0) hbase

theorem leech_measurable_positiveGaussianMixturePotential_of_finite_lattice_energy
    (ν : Measure ℝ) (hbase : latticePotentialEnergy leechSet (positiveGaussianMixturePotential ν) ≠ ∞) :
    Measurable (Function.uncurry (positiveGaussianMixturePotential (d := 24) ν)) := by
  have hz : leechEuclideanBasis 0 ∈ leechSet := by
    rw [← coe_leechLattice, leechLattice_eq_span]
    exact Submodule.subset_span ⟨0, rfl⟩
  exact measurable_positiveGaussianMixturePotential_of_lattice ν hz
    (leechEuclideanBasis.ne_zero 0) hbase

end E8Leech
