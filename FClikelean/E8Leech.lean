module

public import FormalConjecturesUtil

/-!
# Quantitative stationary crystallization for $E_8$ and Leech

A small ordered Riesz-energy excess gives local lattice matching, with constants
chosen before the stationary intensity-one law. We state the measurable-subevent form.

*Reference:* K. Kitamura, *Quantitative stationary crystallization for the E8 and Leech lattices*,
[Sections 1 and 7](https://github.com/KitaKen1/e8-leech-stationary-crystallization/blob/57cd06a0056a7d9c83e16ef6153fdad469160100/PDF/e8-leech-stationary-crystallization.pdf).
-/

@[expose] public section

noncomputable section
namespace E8LeechFC
open PointProcess Set MeasureTheory Matrix
open scoped ENNReal

/-- The covolume-one E₈ lattice. -/
def e8Set : Set (Ambient 8) :=
  (fun z : Fin 8 → ℤ => WithLp.toLp 2 (fun i => (z i : ℝ) / 2)) ''
    {z | (∀ i, (2 : ℤ) ∣ z i - z 0) ∧ (4 : ℤ) ∣ ∑ i, z i}

/-- The binary Golay generator block in the coordinate model below. -/
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

/-- The covolume-one Leech lattice, using the extended binary Golay code. -/
def leechSet : Set (Ambient 24) :=
  (fun z : Fin 24 → ℤ => WithLp.toLp 2 (fun i => (z i : ℝ) / Real.sqrt 8)) ''
    {z | ∃ m : ℤ, (∀ i, (2 : ℤ) ∣ z i - m) ∧ (8 : ℤ) ∣ (∑ i, z i) - 4 * m ∧
      ∃ a : Fin 12 → ZMod 2, Fin.append a (a ᵥ* golayBlock) =
        (fun i => (((z i - m) / 2 : ℤ) : ZMod 2))}

/-- Position error $C\delta^\gamma$ and probability and count losses $CR^{-1/2}$,
where $R=\log(1/\delta)/\log\log(1/\delta)$. -/
def QuantitativeCrystallization {d : ℕ} (Λ : Set (Ambient d)) (s γ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
    ∀ μ : Measure (Configuration (Ambient d)),
      IsProbabilityMeasure μ → IsStationary μ → HasIntensity μ 1 →
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        rieszEnergy s μ ≤ latticeRieszEnergy Λ s + ENNReal.ofReal δ →
        let R := Real.log (1 / δ) / Real.log (Real.log (1 / δ))
        ∃ G : Set (Configuration (Ambient d)), MeasurableSet G ∧
          G ⊆ {c | LocalCrystal Λ c R (C * δ ^ γ) (C * R ^ (-1 / 2 : ℝ))} ∧
          ENNReal.ofReal (1 - C * R ^ (-1 / 2 : ℝ)) ≤ μ G

/-- Quantitative stationary crystallization for $E_8$, for every $0<\gamma<1/12$. -/
@[category research solved, AMS 52 60]
theorem e8_quantitative_crystallization {s γ : ℝ} (hs : (8 : ℝ) < s)
    (hγ : 0 < γ) (hγlt : γ < 1 / 12) :
    QuantitativeCrystallization e8Set s γ := by
  sorry

/-- Quantitative stationary crystallization for Leech, for every $0<\gamma<1/12$. -/
@[category research solved, AMS 52 60]
theorem leech_quantitative_crystallization {s γ : ℝ} (hs : (24 : ℝ) < s)
    (hγ : 0 < γ) (hγlt : γ < 1 / 12) :
    QuantitativeCrystallization leechSet s γ := by
  sorry

/-- The coordinate model of $E_8$ contains the origin. -/
@[category test, AMS 52]
theorem zero_mem_e8Set : (0 : Ambient 8) ∈ e8Set := by
  refine ⟨0, ?_, ?_⟩
  · simp
  · ext i
    simp

/-- The coordinate model of Leech contains the origin. -/
@[category test, AMS 52]
theorem zero_mem_leechSet : (0 : Ambient 24) ∈ leechSet := by
  refine ⟨0, ⟨0, ?_, ?_, ?_⟩, ?_⟩
  · simp
  · simp
  · refine ⟨0, ?_⟩
    ext i
    simp [Fin.append, Fin.addCases]
  · ext i
    simp

end E8LeechFC
