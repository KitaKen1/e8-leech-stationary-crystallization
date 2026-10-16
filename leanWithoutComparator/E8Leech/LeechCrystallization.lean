import E8Leech.LeechFourierIdentityProof
import E8Leech.LeechBlockBoundsProof
import E8Leech.E8PeriodicStability

/-!
# The Leech case, and the main theorem for `E8` and the Leech lattice

The three analytic inputs of the Leech case are proved: the kernel inequalities (6.4)
(`leechKernelInequalities`), the block bounds (`leechBlockBounds`) and the Fourier identities (**)
(`leechFourierIdentities`). Hence `leechCrystallizationTarget` holds without hypotheses, and with
`e8CrystallizationTarget_holds` this is the main theorem `e8LeechCrystallizationTarget`.

The last two theorems state the result as in the manuscript: the hypothesis is the energy inequality
`𝓔_s(μ) ≤ L_s + δ` alone (the finiteness of the lattice energy `L_s` for `s > d`, which is part of
`HasRieszExcessAtMost`, is a theorem).
-/

namespace E8Leech

open MeasureTheory

/-- **The Leech case of the main theorem**: stationary crystallization for the Leech lattice. -/
theorem leechCrystallizationTarget_holds : leechCrystallizationTarget :=
  leech_stationaryCrystallization_of_fourierIdentities leechFourierIdentities

/-- **The main theorem**: stationary crystallization for `E8` and for the Leech lattice. -/
theorem e8LeechCrystallizationTarget_holds : e8LeechCrystallizationTarget :=
  ⟨e8CrystallizationTarget_holds, leechCrystallizationTarget_holds⟩

/-- **The `E8` theorem in the form of the manuscript.** For `s > 8` there are `C > 0` and
`0 < δ₀ < e^{−e}`, chosen before the law, such that every stationary simple point process of
intensity one with `𝓔_s(μ) ≤ L_s + δ`, `0 < δ < δ₀`, is locally `Cδ^{1/13}`-close to an isometric
copy of `E8` in the ball of radius `R = log(1/δ)/log log(1/δ)`, with at least
`(1 − CR^{−1/2}) vol(B_R)` points, on a measurable event of probability at least `1 − CR^{−1/2}`. -/
theorem e8_crystallization_of_energy_le {s : ℝ} (hs : (8 : ℝ) < s) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
      ∀ μ : Measure (Configuration (Ambient 8)),
        IsProbabilityMeasure μ → IsStationary μ → HasIntensity μ 1 →
        ∀ δ : ℝ, 0 < δ → δ < δ₀ →
          rieszEnergy s μ ≤ latticeRieszEnergy e8Set s + ENNReal.ofReal δ →
          ∃ G : Set (Configuration (Ambient 8)), MeasurableSet G ∧
            G ⊆ {c | LocalCrystal e8Set c (observationRadius δ)
              (C * δ ^ (1 / 13 : ℝ)) (C * observationRadius δ ^ (-1 / 2 : ℝ))} ∧
            ENNReal.ofReal (1 - C * observationRadius δ ^ (-1 / 2 : ℝ)) ≤ μ G := by
  obtain ⟨C, hC, δ₀, hδ₀, hδ₀e, h⟩ := e8CrystallizationTarget_holds s (by exact_mod_cast hs)
  exact ⟨C, hC, δ₀, hδ₀, hδ₀e, fun μ hP hS hI δ hδ hδ' hE =>
    h μ hP hS hI δ hδ hδ' ⟨e8_latticeRieszEnergy_ne_top hs, hE⟩⟩

/-- **The Leech theorem in the form of the manuscript** (`s > 24`; see
`e8_crystallization_of_energy_le`). -/
theorem leech_crystallization_of_energy_le {s : ℝ} (hs : (24 : ℝ) < s) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
      ∀ μ : Measure (Configuration (Ambient 24)),
        IsProbabilityMeasure μ → IsStationary μ → HasIntensity μ 1 →
        ∀ δ : ℝ, 0 < δ → δ < δ₀ →
          rieszEnergy s μ ≤ latticeRieszEnergy leechSet s + ENNReal.ofReal δ →
          ∃ G : Set (Configuration (Ambient 24)), MeasurableSet G ∧
            G ⊆ {c | LocalCrystal leechSet c (observationRadius δ)
              (C * δ ^ (1 / 13 : ℝ)) (C * observationRadius δ ^ (-1 / 2 : ℝ))} ∧
            ENNReal.ofReal (1 - C * observationRadius δ ^ (-1 / 2 : ℝ)) ≤ μ G := by
  obtain ⟨C, hC, δ₀, hδ₀, hδ₀e, h⟩ := leechCrystallizationTarget_holds s (by exact_mod_cast hs)
  exact ⟨C, hC, δ₀, hδ₀, hδ₀e, fun μ hP hS hI δ hδ hδ' hE =>
    h μ hP hS hI δ hδ hδ' ⟨leech_latticeRieszEnergy_ne_top hs, hE⟩⟩

end E8Leech
