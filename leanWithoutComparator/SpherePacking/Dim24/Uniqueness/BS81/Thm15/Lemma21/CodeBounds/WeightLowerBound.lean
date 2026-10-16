-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.CodeBounds.ReducedWitness
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16.MinNorm


/-!
# Weight lower bound for `codeFromLattice`

Using the reduced-witness lemma (`CodeFromLattice.exists_reduced_witness`) and the minimum-norm
bound from Lemma 16, we show that every nonzero word in `codeFromLattice` has Hamming weight at
least `8`.

## Main statement
* `CodeFromLattice.weight_ge_eight_of_mem_codeFromLattice`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21

noncomputable section

open scoped RealInnerProductSpace BigOperators

open Set

open Uniqueness.BS81.CodingTheory

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace CodeFromLattice


/-- Nonzero codewords in the extracted code have weight at least `8`. -/
public theorem weight_ge_eight_of_mem_codeFromLattice
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24)
    {c : BinWord 24} (hc : c ∈ codeFromLattice (C := C) hDn) (hc0 : c ≠ 0) :
    8 ≤ weight c := by
  rcases exists_reduced_witness (C := C) (hDn := hDn) hc hc0 with
    ⟨x, hxL, z, hzCoord, hzVals, hcZ⟩
  have he : Orthonormal ℝ hDn.e := hDn.ortho
  -- Compute `‖x‖^2` from the reduced coordinates.
  have hnorm :
      ‖x‖ ^ 2 = (weight c : ℝ) / 2 := by
    -- `‖x‖^2 = (1/8) * Σ z_i^2`, and for reduced `z_i` this equals `weight/2`.
    have hnorm' :
        ‖x‖ ^ 2 = (1 / 8 : ℝ) * ∑ i : Fin 24, (scaledCoord hDn.e i x) ^ 2 :=
      norm_sq_eq_sum_scaledCoord_sq_div8 (e := hDn.e) he x
    -- Replace `scaledCoord` by `z`.
    have hsum :
        ∑ i : Fin 24, (scaledCoord hDn.e i x) ^ 2 = ∑ i : Fin 24, ((z i : ℝ) ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      simp [hzCoord i]
    -- Now compute `∑ z_i^2 = 4 * weight c`.
    have hsq :
        ∑ i : Fin 24, ((z i : ℝ) ^ 2) = (4 : ℝ) * weight c := by
      have hz_sq : ∀ i : Fin 24, ((z i : ℝ) ^ 2) = (if c i = 1 then (4 : ℝ) else 0) := by
        intro i
        rcases hzVals i with hz | hz | hz
        · -- `z i = 0` hence `c i = 0`
          have hc0i : c i = 0 := by simp [hz, hcZ i]
          simp [hz, hc0i]
        · -- `z i = 2` hence `c i = 1`
          have hc1i : c i = 1 := by simp [hz, hcZ i]
          simp [hz, hc1i]
          norm_num
        · -- `z i = -2` hence `c i = 1` (since `(-1 : ZMod 2) = 1`)
          have hc1i : c i = 1 := by simp [hz, hcZ i]
          simp [hz, hc1i]
          norm_num
      calc
        ∑ i : Fin 24, ((z i : ℝ) ^ 2)
            = ∑ i : Fin 24, (if c i = 1 then (4 : ℝ) else 0) := by
                refine Finset.sum_congr rfl ?_
                intro i _hi
                exact hz_sq i
        _ = (4 : ℝ) * weight c := by
              simpa [weight, mul_comm, mul_left_comm, mul_assoc] using!
                (Finset.sum_filter (s := (Finset.univ : Finset (Fin 24)))
                  (p := fun i : Fin 24 => c i = 1) (f := fun _ => (4 : ℝ))).symm
    -- finish
    calc
      ‖x‖ ^ 2 = (1 / 8 : ℝ) * ∑ i : Fin 24, (scaledCoord hDn.e i x) ^ 2 := hnorm'
      _ = (1 / 8 : ℝ) * ∑ i : Fin 24, ((z i : ℝ) ^ 2) := by simp [hsum]
      _ = (1 / 8 : ℝ) * ((4 : ℝ) * weight c) := by simp [hsq]
      _ = (weight c : ℝ) / 2 := by ring
  -- `x ≠ 0` since some coordinate is nonzero (as `c ≠ 0`).
  have hx0 : x ≠ 0 := by
    rcases exists_idx_one_of_ne_zero (c := c) hc0 with ⟨i, hi⟩
    have hz_ne0 : z i ≠ 0 := by
      rcases hzVals i with hz | hz | hz
      · -- `z i = 0` forces `c i = 0`, contradicting `c i = 1`
        have hc0i : c i = 0 := by simp [hz, hcZ i]
        have : False := by
          have hi' := hi
          rw [hc0i] at hi'
          exact (zero_ne_one (α := ZMod 2)) hi'
        exact this.elim
      · -- `z i = 2`
        simp [hz]
      · -- `z i = -2`
        simp [hz]
    intro hx
    apply hz_ne0
    have : scaledCoord hDn.e i x = 0 := by simp [hx, scaledCoord, coord]
    simpa [hzCoord i] using! this
  -- Apply Lemma 16 to `x`.
  have hmin :
      (4 : ℝ) ≤ ‖x‖ ^ 2 :=
    Uniqueness.BS81.Thm15.Lemma16.minNorm_sq_ge_four (C := C) h x hxL hx0
  -- Convert to a bound on the weight.
  have : (8 : ℝ) ≤ (weight c : ℝ) := by nlinarith [hmin, hnorm]
  exact_mod_cast this

end CodeFromLattice

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21
