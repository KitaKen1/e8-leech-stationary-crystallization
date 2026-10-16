-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Overlattice.Basic

/-!
# Isotropy of `centersSubgroup`

We show that the submodule `centersSubgroup` of the discriminant group is isotropic for the
discriminant pairing `discPair`.

Concretely, the pairing vanishes on the orbit cosets, and hence on their `ℤ`-span.

## Main statements
* `orbitCoset_discPair_eq_zero`
* `discPair_eq_zero_of_mem_centersSubgroup`
-/

namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

noncomputable section

open scoped Pointwise RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)
local notation "𝕋" => AddCircle (1 : ℝ)

/-- The discriminant pairing vanishes on any two orbit cosets. -/
public theorem orbitCoset_discPair_eq_zero (S : PeriodicSpherePacking 24)
    (hSpec : HasLeechDistanceSpectrum S) (hDens : S.density = LeechPacking.density)
    (x0 : S.centers) (q1 q2 : Quotient S.addAction.orbitRel) :
    discPair (L := S.lattice)
        (orbitCoset (S := S) hSpec hDens x0 q1)
        (orbitCoset (S := S) hSpec hDens x0 q2) = 0 := by
  refine Quotient.inductionOn₂ q1 q2 ?_
  intro x y
  rcases HasLeechDistanceSpectrum.inner_centerDiff_eq_int (S := S) hSpec x0 x y with ⟨m, hm⟩
  have hm0 : ((m : ℝ) : 𝕋) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (p := (1 : ℝ)) (x := (m : ℝ))).2
    exact ⟨m, by simp⟩
  have hinner :
      (⟪(centerDiffDual (S := S) hSpec hDens x0 x : ℝ²⁴),
          (centerDiffDual (S := S) hSpec hDens x0 y : ℝ²⁴)⟫ : ℝ) = (m : ℝ) := by
    simpa [centerDiffDual] using! hm
  simp [orbitCoset, centerCoset, discPair_mk_mk, dualLatticePair_apply, hinner, hm0]

/-- The discriminant pairing vanishes on `centersSubgroup`. -/
public theorem discPair_eq_zero_of_mem_centersSubgroup (S : PeriodicSpherePacking 24)
    (hSpec : HasLeechDistanceSpectrum S) (hDens : S.density = LeechPacking.density)
    (x0 : S.centers) {a b : DiscriminantGroup S.lattice}
    (ha : a ∈ centersSubgroup (S := S) hSpec hDens x0)
    (hb : b ∈ centersSubgroup (S := S) hSpec hDens x0) :
    discPair (L := S.lattice) a b = 0 := by
  let f : Quotient S.addAction.orbitRel → DiscriminantGroup S.lattice :=
    orbitCoset (S := S) hSpec hDens x0
  let s : Set (DiscriminantGroup S.lattice) := Set.range f
  have ha' : a ∈ Submodule.span ℤ s := by
    simpa [centersSubgroup, s, f] using! ha
  have hb' : b ∈ Submodule.span ℤ s := by
    simpa [centersSubgroup, s, f] using! hb
  -- span induction on the left argument
  have haP :
      (∀ b ∈ Submodule.span ℤ s, discPair (L := S.lattice) a b = 0) :=
    Submodule.span_induction (s := s)
      (p := fun a _ => ∀ b ∈ Submodule.span ℤ s, discPair (L := S.lattice) a b = 0)
      (mem := by
        intro a haRange
        rcases haRange with ⟨q1, rfl⟩
        intro b hbSpan
        -- span induction on the right argument
        refine Submodule.span_induction (s := s)
          (p := fun b _ =>
            discPair (L := S.lattice) (f q1) b = 0)
          (mem := by
            intro b hbRange
            rcases hbRange with ⟨q2, rfl⟩
            exact orbitCoset_discPair_eq_zero S hSpec hDens x0 q1 q2)
          (zero := by simp)
          (add := by
            simp_all)
          (smul := by
            simp_all)
          hbSpan)
      (zero := by simp)
      (add := by
        simp_all)
      (smul := by
        simp_all)
      ha'
  exact haP b hb'

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
