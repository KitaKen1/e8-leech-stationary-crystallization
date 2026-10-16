-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Defs
public import SpherePacking.Dim24.Uniqueness.Rigidity.Lemmas

/-!
# Integrality of center-difference inner products

From the Leech distance spectrum hypothesis, squared distances between centers are of the form
`2 * k`. Using the polarization identity for the norm, this implies that inner products between
center differences are integers.

## Main statement
* `HasLeechDistanceSpectrum.inner_centerDiff_eq_int`
-/


namespace SpherePacking.Dim24

open scoped RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/--
Under `HasLeechDistanceSpectrum`, the inner product of two center differences based at `x0` is an
integer.
-/
public lemma HasLeechDistanceSpectrum.inner_centerDiff_eq_int (S : PeriodicSpherePacking 24)
    (hSpec : HasLeechDistanceSpectrum S) (x0 x y : S.centers) :
    ∃ m : ℤ, ⟪(x : ℝ²⁴) - (x0 : ℝ²⁴), (y : ℝ²⁴) - (x0 : ℝ²⁴)⟫ = m := by
  set u : ℝ²⁴ := (x : ℝ²⁴) - (x0 : ℝ²⁴)
  set v : ℝ²⁴ := (y : ℝ²⁴) - (x0 : ℝ²⁴)
  have hnorm (x y : S.centers) : ∃ n : ℕ, ‖(x : ℝ²⁴) - (y : ℝ²⁴)‖ ^ 2 = (2 : ℝ) * n := by
    by_cases hxy : x = y
    · subst hxy
      exact ⟨0, by simp⟩
    · rcases hSpec x y hxy with ⟨k, -, hk⟩
      exact ⟨k, hk⟩
  rcases hnorm x x0 with ⟨nu, hnu⟩
  rcases hnorm y x0 with ⟨nv, hnv⟩
  rcases hnorm x y with ⟨nuv, hnuv⟩
  have hnu' : ‖u‖ ^ 2 = (2 : ℝ) * nu := by simpa [u] using! hnu
  have hnv' : ‖v‖ ^ 2 = (2 : ℝ) * nv := by simpa [v] using! hnv
  have hnuv' : ‖u - v‖ ^ 2 = (2 : ℝ) * nuv := by
    have : u - v = (x : ℝ²⁴) - (y : ℝ²⁴) := by
      simp [u, v, sub_sub_sub_cancel_right]
    simpa [this] using! hnuv
  -- `‖u - v‖^2 = ‖u‖^2 + ‖v‖^2 - 2⟪u,v⟫`
  have hpol :
      ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * ⟪u, v⟫ + ‖v‖ ^ 2 := by
    simpa using! (norm_sub_sq_real u v)
  -- Solve for `⟪u,v⟫` and exhibit an integer.
  refine ⟨(nu : ℤ) + (nv : ℤ) - (nuv : ℤ), ?_⟩
  have hcalc : (2 : ℝ) * ⟪u, v⟫ = (2 : ℝ) * ((nu : ℝ) + (nv : ℝ) - (nuv : ℝ)) := by
    -- Substitute the `2*Nat` expressions and rearrange.
    rw [hnu', hnv', hnuv'] at hpol
    nlinarith [hpol]
  simp_all

end SpherePacking.Dim24
