-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.DualProps
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Discriminant

/-!
# Center cosets in the discriminant group

Under the Leech distance spectrum and optimal density hypotheses, each center difference `x - x0`
lies in the dual lattice `S.lattice*`. Modulo `S.lattice`, this yields a map from centers to the
discriminant group `S.lattice*/S.lattice`.

In subsequent arguments, this map descends to the finite orbit quotient of centers (`S.numReps`)
and its image forms a subgroup of the discriminant group.

## Main definitions
* `Uniqueness.RigidityClassify.centerDiffDual`
* `Uniqueness.RigidityClassify.centerCoset`
* `Uniqueness.RigidityClassify.orbitCoset`

## Main statement
* `Uniqueness.RigidityClassify.orbitCoset_injective`
-/

namespace SpherePacking.Dim24.LinearMap.BilinForm

open scoped RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- A helper lemma: center differences lie in the dual lattice, with swapped arguments. -/
public lemma HasLeechDistanceSpectrum.center_sub_mem_dual₂ (S : PeriodicSpherePacking 24)
    (hSpec : HasLeechDistanceSpectrum S) (hDens : S.density = LeechPacking.density)
    (x y : S.centers) :
    ((x : ℝ²⁴) - (y : ℝ²⁴)) ∈
      LinearMap.BilinForm.dualSubmodule (B := (innerₗ ℝ²⁴ : LinearMap.BilinForm ℝ ℝ²⁴))
        S.lattice :=
  HasLeechDistanceSpectrum.center_sub_mem_dual (S := S) hSpec hDens y x

end SpherePacking.Dim24.LinearMap.BilinForm

namespace SpherePacking.Dim24.Uniqueness.RigidityClassify
open scoped Pointwise RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/--
The center difference `x - x0`, regarded as an element of the dual lattice `DualLattice S.lattice`.
-/
@[expose] public noncomputable def centerDiffDual (S : PeriodicSpherePacking 24)
    (hSpec : HasLeechDistanceSpectrum S) (hDens : S.density = LeechPacking.density)
    (x0 x : S.centers) : DualLattice S.lattice :=
  ⟨(x : ℝ²⁴) - (x0 : ℝ²⁴),
      LinearMap.BilinForm.HasLeechDistanceSpectrum.center_sub_mem_dual₂ S hSpec hDens x x0⟩

/-- The discriminant-group element attached to a center `x`, relative to a base center `x0`. -/
@[expose] public noncomputable def centerCoset (S : PeriodicSpherePacking 24)
    (hSpec : HasLeechDistanceSpectrum S) (hDens : S.density = LeechPacking.density)
    (x0 : S.centers) : S.centers → DiscriminantGroup S.lattice :=
  fun x => Submodule.Quotient.mk (centerDiffDual (S := S) hSpec hDens x0 x)

/-- `centerCoset` is invariant under translating the input center by a lattice vector. -/
public lemma centerCoset_vadd_eq (S : PeriodicSpherePacking 24)
    (hSpec : HasLeechDistanceSpectrum S) (hDens : S.density = LeechPacking.density)
    (x0 : S.centers)
    (v : ℝ²⁴) (hv : v ∈ S.lattice) (x : S.centers) :
    centerCoset (S := S) hSpec hDens x0
        ⟨v + (x : ℝ²⁴), S.lattice_action hv x.property⟩
      =
      centerCoset (S := S) hSpec hDens x0 x := by
  -- Work in the quotient by `latticeInDual S.lattice`.
  -- Reduce equality in the quotient to membership of the difference.
  refine
    (mk_eq_mk_iff_sub_mem (L := S.lattice)
        (centerDiffDual (S := S) hSpec hDens x0 ⟨v + (x : ℝ²⁴), S.lattice_action hv x.property⟩)
        (centerDiffDual (S := S) hSpec hDens x0 x)).2 ?_
  -- Membership in `latticeInDual` is membership in `S.lattice` after coercion to `ℝ²⁴`.
  change
    ((centerDiffDual (S := S) hSpec hDens x0 ⟨v + (x : ℝ²⁴), S.lattice_action hv x.property⟩ -
            centerDiffDual (S := S) hSpec hDens x0 x : DualLattice S.lattice) : ℝ²⁴) ∈
      S.lattice
  simpa [centerDiffDual, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using! hv

/-- The coset map descends to the orbit quotient of centers. -/
@[expose] public noncomputable def orbitCoset (S : PeriodicSpherePacking 24)
    (hSpec : HasLeechDistanceSpectrum S) (hDens : S.density = LeechPacking.density)
    (x0 : S.centers) :
    Quotient S.addAction.orbitRel → DiscriminantGroup S.lattice :=
by
  refine Quotient.lift (fun x : S.centers => centerCoset (S := S) hSpec hDens x0 x) ?_
  intro a b hab
  -- `hab` says `b` is a lattice translate of `a`.
  change (S.addAction.orbitRel).r _ _ at hab
  rw [AddAction.orbitRel_apply, AddAction.orbit, Set.mem_range] at hab
  rcases hab with ⟨g, rfl⟩
  -- Unfold the action `g +ᵥ a` and apply the translation invariance lemma.
  simpa [PeriodicSpherePacking.addAction_vadd, Submodule.vadd_def] using!
    (centerCoset_vadd_eq (S := S) (hSpec := hSpec) (hDens := hDens) (x0 := x0)
      (v := (g : ℝ²⁴)) (hv := g.property) (x := b))

/-- Distinct orbits of centers map to distinct discriminant-group elements under `orbitCoset`. -/
public theorem orbitCoset_injective (S : PeriodicSpherePacking 24)
    (hSpec : HasLeechDistanceSpectrum S) (hDens : S.density = LeechPacking.density)
    (x0 : S.centers) :
    Function.Injective (orbitCoset (S := S) hSpec hDens x0) := by
  intro q1 q2 hq
  -- Reduce to representatives in `S.centers`.
  refine
    (Quotient.inductionOn₂
        (motive := fun q1 q2 =>
          orbitCoset (S := S) hSpec hDens x0 q1 = orbitCoset (S := S) hSpec hDens x0 q2 →
            q1 = q2)
        q1 q2 ?_) hq
  intro x y hxy
  -- unfold `orbitCoset` on representatives: `orbitCoset ⟦x⟧ = centerCoset x`
  have hcos :
      centerCoset (S := S) hSpec hDens x0 x =
        centerCoset (S := S) hSpec hDens x0 y := by
    -- `simp` knows how `Quotient.lift` acts on `Quotient.mk`.
    simpa [orbitCoset] using! hxy
  -- unpack equality in the discriminant group: it means `x - y ∈ S.lattice`.
  have hmem :
      (centerDiffDual (S := S) hSpec hDens x0 x -
            centerDiffDual (S := S) hSpec hDens x0 y : DualLattice S.lattice) ∈
        latticeInDual S.lattice := by
    -- `mk_eq_mk_iff_sub_mem` is the characterization of equality in the quotient.
    exact
      (mk_eq_mk_iff_sub_mem (L := S.lattice)
          (centerDiffDual (S := S) hSpec hDens x0 x)
          (centerDiffDual (S := S) hSpec hDens x0 y)).1
        (by simpa [centerCoset] using! hcos)
  have hxyLat : ((x : ℝ²⁴) - (y : ℝ²⁴)) ∈ S.lattice := by
    -- membership in `latticeInDual` is membership in `S.lattice` after coercion
    have hcoe :
        ((centerDiffDual (S := S) hSpec hDens x0 x -
              centerDiffDual (S := S) hSpec hDens x0 y : DualLattice S.lattice) : ℝ²⁴) ∈
          S.lattice := by
      simpa [Uniqueness.RigidityClassify.mem_latticeInDual_iff] using! hmem
    have hdiff :
        ((centerDiffDual (S := S) hSpec hDens x0 x -
              centerDiffDual (S := S) hSpec hDens x0 y : DualLattice S.lattice) : ℝ²⁴)
          =
          ((x : ℝ²⁴) - (y : ℝ²⁴)) := by
      -- Expand and cancel `x0` terms.
      simp [centerDiffDual, sub_eq_add_neg, add_assoc, add_left_comm]
      abel
    simpa [hdiff] using! hcoe
  -- Conclude `⟦x⟧ = ⟦y⟧` by showing `x` and `y` are in the same lattice orbit.
  apply Quotient.sound
  change (S.addAction.orbitRel).r x y
  rw [AddAction.orbitRel_apply, AddAction.orbit, Set.mem_range]
  -- `orbitRel x y` means `x ∈ orbit y`, i.e. `∃ g, g +ᵥ y = x`.
  refine ⟨⟨(x : ℝ²⁴) - (y : ℝ²⁴), hxyLat⟩, ?_⟩
  apply Subtype.ext
  simp [PeriodicSpherePacking.addAction_vadd, sub_eq_add_neg, add_left_comm, add_comm]

end SpherePacking.Dim24.Uniqueness.RigidityClassify
