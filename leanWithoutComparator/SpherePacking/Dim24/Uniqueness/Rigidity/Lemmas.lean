-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Defs
public import SpherePacking.Basic.PeriodicPacking.Auxiliary
public import SpherePacking.Basic.PeriodicPacking.Theorem22
public import SpherePacking.Basic.PeriodicPacking.DensityFormula
public import SpherePacking.Basic.PeriodicPacking.PeriodicConstant
public import SpherePacking.Basic.PeriodicPacking.BoundaryControl
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Auxiliary lemmas for rigidity

These lemmas extract basic metric and arithmetic consequences of `HasLeechDistanceSpectrum` and are
used in the proof of `leech_rigidity_normalized`.

## Main statements
* `nonempty_centers_of_density_eq_leech`
* `HasLeechDistanceSpectrum.two_le_norm_sub`
* `HasLeechDistanceSpectrum.inner_lattice_eq_int`
-/


namespace SpherePacking.Dim24

open scoped ENNReal Real RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- The Leech packing has positive density. -/
public lemma leechPacking_density_ne_zero : LeechPacking.density ≠ 0 := by
  rw [LeechPacking_density]
  intro h
  rcases (ENNReal.div_eq_zero_iff).1 h with h0 | htop
  · exact (pow_ne_zero 12 ((ENNReal.ofReal_ne_zero_iff).2 Real.pi_pos)) h0
  · simp at htop

/-- If a periodic packing has Leech packing density, then it has at least one center. -/
public lemma nonempty_centers_of_density_eq_leech (S : PeriodicSpherePacking 24)
    (hS : S.density = LeechPacking.density) : Nonempty S.centers := by
  rcases isEmpty_or_nonempty S.centers with hE | hNE
  · haveI : IsEmpty S.centers := hE
    have hd : (0 : ℕ) < 24 := by decide
    have : LeechPacking.density = 0 := by
      simpa [hS] using! PeriodicSpherePacking.density_of_centers_empty (S := S) hd
    exact (leechPacking_density_ne_zero this).elim
  · exact hNE

/-- Under `HasLeechDistanceSpectrum`, distinct centers are separated by distance at least `2`. -/
public lemma HasLeechDistanceSpectrum.two_le_norm_sub (S : PeriodicSpherePacking 24)
    (hSpec : HasLeechDistanceSpectrum S) (x y : S.centers) (hxy : x ≠ y) :
    (2 : ℝ) ≤ ‖(x : ℝ²⁴) - (y : ℝ²⁴)‖ := by
  rcases hSpec x y hxy with ⟨k, hk, hnorm⟩
  have hsq : (2 : ℝ) ^ 2 ≤ ‖(x : ℝ²⁴) - (y : ℝ²⁴)‖ ^ 2 := by
    -- `‖x-y‖^2 = 2*k ≥ 2*2 = 4 = 2^2`.
    nlinarith [hnorm, (show (2 : ℝ) ≤ (k : ℝ) from by exact_mod_cast hk)]
  exact (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg _)).1 hsq

/-- If `v ∈ S.lattice` is nonzero, then `‖v‖^2 = 2k` for some `k ≥ 2`. -/
public lemma HasLeechDistanceSpectrum.norm_sq_eq_two_mul_of_lattice (S : PeriodicSpherePacking 24)
    (hSpec : HasLeechDistanceSpectrum S) (x0 : S.centers) (v : ℝ²⁴)
    (hv : v ∈ S.lattice) (hv0 : v ≠ 0) :
    ∃ k : ℕ, 2 ≤ k ∧ ‖v‖ ^ 2 = (2 : ℝ) * k := by
  let y0 : S.centers := ⟨v + (x0 : ℝ²⁴), S.lattice_action hv x0.property⟩
  have hy0 : y0 ≠ x0 := by
    intro h
    apply hv0
    exact add_right_cancel (b := (x0 : ℝ²⁴)) (by simpa [y0] using! congrArg Subtype.val h)
  rcases hSpec y0 x0 hy0 with ⟨k, hk, hkEq⟩
  refine ⟨k, hk, ?_⟩
  simpa [y0] using! hkEq

/-- If `v ∈ S.lattice`, then `‖v‖^2 = 2k` for some `k : ℕ` (allowing `k = 0`). -/
public lemma HasLeechDistanceSpectrum.norm_sq_eq_two_mul_of_lattice' (S : PeriodicSpherePacking 24)
    (hSpec : HasLeechDistanceSpectrum S) (x0 : S.centers) (v : ℝ²⁴)
    (hv : v ∈ S.lattice) :
    ∃ k : ℕ, ‖v‖ ^ 2 = (2 : ℝ) * k := by
  by_cases hv0 : v = 0
  · subst hv0
    exact ⟨0, by simp⟩
  · rcases
        HasLeechDistanceSpectrum.norm_sq_eq_two_mul_of_lattice (S := S) (hSpec := hSpec) (x0 := x0)
          (v := v) hv hv0 with
      ⟨k, _, hkEq⟩
    exact ⟨k, hkEq⟩

/-- If `u, v ∈ S.lattice`, then `⟪u, v⟫` is an integer. -/
public lemma HasLeechDistanceSpectrum.inner_lattice_eq_int (S : PeriodicSpherePacking 24)
    (hSpec : HasLeechDistanceSpectrum S) (x0 : S.centers) (u v : ℝ²⁴)
    (hu : u ∈ S.lattice) (hv : v ∈ S.lattice) :
    ∃ m : ℤ, ⟪u, v⟫ = (m : ℝ) := by
  rcases
        HasLeechDistanceSpectrum.norm_sq_eq_two_mul_of_lattice' (S := S) (hSpec := hSpec) (x0 := x0)
          (v := u) hu with
      ⟨nu, hnu⟩
  rcases
        HasLeechDistanceSpectrum.norm_sq_eq_two_mul_of_lattice' (S := S) (hSpec := hSpec) (x0 := x0)
          (v := v) hv with
      ⟨nv, hnv⟩
  have huv : u + v ∈ S.lattice := add_mem hu hv
  rcases
        HasLeechDistanceSpectrum.norm_sq_eq_two_mul_of_lattice' (S := S) (hSpec := hSpec) (x0 := x0)
          (v := u + v) huv with
      ⟨nuv, hnuv⟩
  have hInner : (2 : ℝ) * ⟪u, v⟫ = ‖u + v‖ ^ 2 - ‖u‖ ^ 2 - ‖v‖ ^ 2 := by
    have hadd : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * ⟪u, v⟫ + ‖v‖ ^ 2 := norm_add_sq_real u v
    linarith
  have hInner' : (2 : ℝ) * ⟪u, v⟫ = (2 : ℝ) * ((nuv : ℝ) - (nu : ℝ) - (nv : ℝ)) := by
    have h0 := hInner
    rw [hnuv, hnu, hnv] at h0
    nlinarith
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hInner'' : ⟪u, v⟫ = (nuv : ℝ) - (nu : ℝ) - (nv : ℝ) := by
    nlinarith [hInner', h2]
  refine ⟨(nuv : ℤ) - (nu : ℤ) - (nv : ℤ), ?_⟩
  have hcast :
      ((nuv : ℤ) - (nu : ℤ) - (nv : ℤ) : ℝ) =
        (nuv : ℝ) - (nu : ℝ) - (nv : ℝ) := by
    norm_cast
  simpa [hcast] using! hInner''

end SpherePacking.Dim24
