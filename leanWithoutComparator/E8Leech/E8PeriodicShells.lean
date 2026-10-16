import E8Leech.E8PeriodicDeficit

/-!
# BRR square-root deletion and quarter-power shell scales for E8

The actual periodic Poisson budget is specialized to the threshold sqrt(epsilon).
This supplies good representatives, before the geometric good-centre estimates.
-/
noncomputable section
namespace E8Leech
open SpherePacking MeasureTheory

theorem e8_periodic_good_representatives_quarter_shells {P : PeriodicSpherePacking 8}
    {D : Set (EuclideanSpace ℝ (Fin 8))} (hDb : Bornology.IsBounded D)
    (hP : Real.sqrt 2 ≤ P.separation)
    (hD : ∀ v, ∃! ℓ : P.lattice, ℓ +ᵥ v ∈ D) {ε : ℝ} (hεpos : 0 < ε)
    (hε : 1 - ε ≤ (P.numReps' (by norm_num) hDb : ℝ) /
      ZLattice.covolume P.lattice volume) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ R : ℝ, 2 < R →
      ∃ α : ℝ, 1 < α ∧ α ≤ ρ * R ^ (3 / 2 : ℝ) * Real.exp (5 * Real.pi * R / 4) ∧
        ∃ good : Finset (PeriodicReps P D),
          (P.numReps' (by norm_num) hDb : ℝ) -
              2 * (P.numReps' (by norm_num) hDb : ℝ) * Real.sqrt ε ≤ (good.card : ℝ) ∧
          ∀ x ∈ good, ∀ y : PeriodicReps P D, ∀ ℓ : P.lattice,
            (x : EuclideanSpace ℝ (Fin 8)) - y + ℓ ≠ 0 →
            ‖(x : EuclideanSpace ℝ (Fin 8)) - y + ℓ‖ ≤ R →
            ∃ k : ℤ, 1 ≤ k ∧
              |‖(x : EuclideanSpace ℝ (Fin 8)) - y + ℓ‖ ^ 2 - 2 * k| ≤
                α * ε ^ (1 / 4 : ℝ) := by
  have hτ : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hεpos
  have hdiv : ε / Real.sqrt ε = Real.sqrt ε := by
    apply (div_eq_iff hτ.ne').mpr
    simpa only [pow_two] using (Real.sq_sqrt hεpos.le).symm
  have hquarter : Real.sqrt (Real.sqrt ε) = ε ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hεpos.le]
    norm_num
  obtain ⟨ρ, hρ, hbound⟩ := e8_periodic_good_representatives_shells hDb hP hD hτ hε
  refine ⟨ρ, hρ, ?_⟩
  intro R hR
  obtain ⟨α, hα, hαb, good, hc, hs⟩ := hbound R hR
  refine ⟨α, hα, hαb, good, ?_, ?_⟩
  · simpa only [mul_div_assoc, hdiv] using hc
  · simpa only [hquarter] using hs
end E8Leech
