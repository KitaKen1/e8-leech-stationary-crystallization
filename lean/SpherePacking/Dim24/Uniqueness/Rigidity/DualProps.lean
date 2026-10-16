-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Lemmas
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice

/-!
# Dual lattice consequences of the Leech spectrum

We record basic integrality statements implied by `HasLeechDistanceSpectrum`:

* the lattice `S.lattice` is integral (hence contained in its dual lattice) once `S.centers` is
  nonempty;
* every center difference `x - x0` lies in the dual lattice of `S.lattice`.

## Main statements
* `LinearMap.BilinForm.HasLeechDistanceSpectrum.lattice_le_dual`
* `LinearMap.BilinForm.HasLeechDistanceSpectrum.center_sub_mem_dual`
-/


namespace SpherePacking.Dim24

open scoped RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace LinearMap.BilinForm

/-- If `S` has the Leech distance spectrum and has a center, then the lattice is integral:
`S.lattice ≤ (S.lattice)*` (as a dual submodule for `innerₗ`). -/
public lemma HasLeechDistanceSpectrum.lattice_le_dual_of_nonempty (S : PeriodicSpherePacking 24)
    (hSpec : HasLeechDistanceSpectrum S) [Nonempty S.centers] :
    S.lattice ≤
      LinearMap.BilinForm.dualSubmodule
        (B := (innerₗ ℝ²⁴ : LinearMap.BilinForm ℝ ℝ²⁴)) S.lattice := by
  intro u hu v hv
  rcases
        HasLeechDistanceSpectrum.inner_lattice_eq_int (S := S) (hSpec := hSpec)
          (x0 := Classical.choice (inferInstance : Nonempty S.centers)) (u := u) (v := v) hu hv with
      ⟨m, hm⟩
  exact Submodule.mem_one.mpr ⟨m, by simpa using! hm.symm⟩

/-- If `S` has the Leech distance spectrum and has Leech density, then the lattice is integral. -/
public lemma HasLeechDistanceSpectrum.lattice_le_dual (S : PeriodicSpherePacking 24)
    (hSpec : HasLeechDistanceSpectrum S) (hDens : S.density = LeechPacking.density) :
    S.lattice ≤
      LinearMap.BilinForm.dualSubmodule
        (B := (innerₗ ℝ²⁴ : LinearMap.BilinForm ℝ ℝ²⁴)) S.lattice := by
  haveI : Nonempty S.centers := nonempty_centers_of_density_eq_leech (S := S) hDens
  exact HasLeechDistanceSpectrum.lattice_le_dual_of_nonempty (S := S) hSpec

/-- If `S` has the Leech distance spectrum and has a center, then every center difference lies in
the dual lattice of `S.lattice`. -/
public lemma HasLeechDistanceSpectrum.center_sub_mem_dual_of_nonempty (S : PeriodicSpherePacking 24)
    (hSpec : HasLeechDistanceSpectrum S) [Nonempty S.centers] (x0 x : S.centers) :
    ((x : ℝ²⁴) - (x0 : ℝ²⁴)) ∈
      LinearMap.BilinForm.dualSubmodule
        (B := (innerₗ ℝ²⁴ : LinearMap.BilinForm ℝ ℝ²⁴)) S.lattice := by
  -- Membership means all pairings against lattice vectors are integral.
  intro v hv
  by_cases hx : x = x0
  · subst hx
    simp_all
  -- First, `‖x-x0‖^2 = 2*k` is an even integer.
  rcases hSpec x x0 hx with ⟨k0, hk0, hk0Eq⟩
  -- For a given lattice vector `v`, compare `‖(x-x0) - v‖^2`.
  let y : S.centers := ⟨(v : ℝ²⁴) + (x0 : ℝ²⁴), S.lattice_action hv x0.property⟩
  -- Use the spectrum on `v` (a lattice vector) to get `‖v‖^2 = 2*n`.
  rcases HasLeechDistanceSpectrum.norm_sq_eq_two_mul_of_lattice' (S := S) (hSpec := hSpec)
      (x0 := x0) (v := (v : ℝ²⁴)) hv with ⟨nv, hnv⟩
  -- For `w - v`, we can use the spectrum on centers `x` and `y`; if they coincide then the norm
  -- is `0`, which is also of the form `2*0`.
  have hwv :
      ∃ nwv : ℕ, ‖((x : ℝ²⁴) - (x0 : ℝ²⁴)) - (v : ℝ²⁴)‖ ^ 2 = (2 : ℝ) * nwv := by
    by_cases hxy' : x = y
    · subst hxy'
      exact ⟨0, by simp [y]⟩
    · rcases hSpec x y hxy' with ⟨nwv, hnwv, hnwvEq⟩
      refine ⟨nwv, ?_⟩
      -- rewrite `x - y` into `((x-x0) - v)`
      simpa [y, sub_eq_add_neg, add_left_comm, add_comm, add_assoc] using! hnwvEq
  rcases hwv with ⟨nwv, hnwv⟩
  -- Now use `‖w - v‖^2 = ‖w‖^2 + ‖v‖^2 - 2⟪w,v⟫` to solve for `⟪w,v⟫`.
  set w : ℝ²⁴ := (x : ℝ²⁴) - (x0 : ℝ²⁴)
  have hinner :
      (2 : ℝ) * ⟪w, v⟫ = ‖w‖ ^ 2 + ‖(v : ℝ²⁴)‖ ^ 2 - ‖w - (v : ℝ²⁴)‖ ^ 2 := by
    -- Expand `‖w - v‖^2`.
    have h' : ‖w - (v : ℝ²⁴)‖ ^ 2 = ‖w‖ ^ 2 + ‖(v : ℝ²⁴)‖ ^ 2 - 2 * ⟪w, v⟫ := by
      -- `norm_sub_sq` is `‖u-v‖^2 = ‖u‖^2 + ‖v‖^2 - 2⟪u,v⟫`.
      simpa [w, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using!
        (@norm_sub_sq ℝ _ _ _ _ w (v : ℝ²⁴))
    linarith
  have hinner' :
      (2 : ℝ) * ⟪w, v⟫ = (2 : ℝ) * ((k0 : ℝ) + (nv : ℝ) - (nwv : ℝ)) := by
    -- Replace the norm-squared terms by `2*Nat` expressions.
    have hw : ‖w‖ ^ 2 = (2 : ℝ) * k0 := by
      simpa [w] using! hk0Eq
    have hv' : ‖(v : ℝ²⁴)‖ ^ 2 = (2 : ℝ) * nv := by
      simpa using! hnv
    have hwv' : ‖w - (v : ℝ²⁴)‖ ^ 2 = (2 : ℝ) * nwv := by
      simpa [w] using! hnwv
    -- Plug into the expression for `2*⟪w,v⟫`.
    rw [hw, hv', hwv'] at hinner
    nlinarith
  have hinner'' : ⟪w, v⟫ = (k0 : ℝ) + (nv : ℝ) - (nwv : ℝ) := by
    nlinarith [hinner']
  -- Finish by exhibiting an integer equal to the RHS.
  refine Submodule.mem_one.mpr ?_
  refine ⟨(k0 : ℤ) + (nv : ℤ) - (nwv : ℤ), ?_⟩
  simp_all

/-- If `S` has the Leech distance spectrum and has Leech density, then every center difference lies
in the dual lattice of `S.lattice`. -/
public lemma HasLeechDistanceSpectrum.center_sub_mem_dual (S : PeriodicSpherePacking 24)
    (hSpec : HasLeechDistanceSpectrum S) (hDens : S.density = LeechPacking.density)
    (x0 x : S.centers) :
    ((x : ℝ²⁴) - (x0 : ℝ²⁴)) ∈
      LinearMap.BilinForm.dualSubmodule
        (B := (innerₗ ℝ²⁴ : LinearMap.BilinForm ℝ ℝ²⁴)) S.lattice := by
  haveI : Nonempty S.centers := nonempty_centers_of_density_eq_leech (S := S) hDens
  exact HasLeechDistanceSpectrum.center_sub_mem_dual_of_nonempty (S := S) hSpec x0 x

end LinearMap.BilinForm

end SpherePacking.Dim24
