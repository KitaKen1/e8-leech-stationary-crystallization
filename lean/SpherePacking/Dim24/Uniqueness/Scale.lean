-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Defs

/-!
# Scaling periodic packings

This file records basic lemmas about scaling a periodic packing: scaling preserves density, and
every periodic packing can be rescaled to have separation `2`.

## Main statements
* `PeriodicSpherePacking.scale_density`
* `PeriodicSpherePacking.exists_scale_separation_eq_two`
-/

namespace SpherePacking.Dim24

open scoped Real

/-- Scaling a periodic packing does not change its density. -/
@[simp] public theorem PeriodicSpherePacking.scale_density {d : ℕ} (S : PeriodicSpherePacking d)
    {c : ℝ}
    (hc : 0 < c) :
    (PeriodicSpherePacking.scale (S := S) hc).density = S.density := by
  -- `PeriodicSpherePacking.scale` is defined via `SpherePacking.scale`.
  simpa using! SpherePacking.scale_density (S := S.toSpherePacking) (hc := hc)

/-- Every periodic packing can be rescaled to have separation `2`. -/
public theorem PeriodicSpherePacking.exists_scale_separation_eq_two {d : ℕ}
    (S : PeriodicSpherePacking d) :
    ∃ c : ℝ, ∃ hc : 0 < c, (PeriodicSpherePacking.scale (S := S) hc).separation = 2 := by
  refine ⟨2 / S.separation, div_pos two_pos S.separation_pos, by
    simp [PeriodicSpherePacking.scale, SpherePacking.scale, S.separation_pos.ne']⟩

end SpherePacking.Dim24
