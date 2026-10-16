-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.CE.ContactSet
public import SpherePacking.Dim24.Uniqueness.LatticeInvariants
import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.CE.EqualityCase
import SpherePacking.Dim24.Uniqueness.BS81.KissingUniqueness
import SpherePacking.Dim24.Uniqueness.Rigidity.DensityProps
import SpherePacking.Dim24.Uniqueness.Rigidity.DualProps
import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Overlattice.IndexCovolume
import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.EvenUnimodular.Discrete
import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.RootlessCase.MinShell
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Local rigidity for the CE route

This file proves the local rigidity step in the CE Section 8 approach: in the normalized equality
case, the contact set around any center is isometric to the Leech kissing configuration.

In particular, it implies `Set.ncard (contactSet S x0) = 196560`.

## Main statements
* `Uniqueness.RigidityClassify.CE.centers_eq_translate_of_fullRankLattice_of_CE`
* `Uniqueness.RigidityClassify.CE.contactSet_is_leech_kissing_of_CE`
-/

namespace SpherePacking.Dim24.Uniqueness.RigidityClassify.CE

noncomputable section

open scoped FourierTransform RealInnerProductSpace Pointwise
open Uniqueness.RigidityClassify.NiemeierRootless

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
### Structural claim: equality case ⇒ centers are a single lattice coset

In the CE §8 equality case, multiple cosets should be ruled out (otherwise one typically obtains
extra allowed distances / extra roots). We record the lattice-coset structure as a reusable lemma.
-/

/--
In the normalized equality case, the set of centers of `S` is a single lattice coset `x0 +ᵥ L'`,
where `L'` is a unimodular `ℤ`-lattice.
-/
public theorem centers_eq_translate_of_fullRankLattice_of_CE
    (S : PeriodicSpherePacking 24)
    (hSep : S.separation = 2)
    (hSpec : HasLeechDistanceSpectrum S)
    (hDens : S.density = LeechPacking.density)
    (x0c : S.centers) :
    ∃ (x0 : ℝ²⁴) (L' : Submodule ℤ ℝ²⁴),
      ∃ _ : DiscreteTopology L',
        IsZLattice ℝ L' ∧ Unimodular L' ∧ (S.centers : Set ℝ²⁴) = x0 +ᵥ (L' : Set ℝ²⁴) := by
  -- First, compute the covolume/`numReps` identity forced by the sharp density value.
  have hCovol : ZLattice.covolume S.lattice MeasureTheory.volume = (S.numReps : ℝ) :=
    Dim24.covolume_eq_numReps_real_of_density_eq_leech_normalized (S := S) hSep hDens
  -- Next, show `S.lattice ≤ dualSubmodule(S.lattice)` from the distance-spectrum constraint.
  have hLdual :
      S.lattice ≤
        LinearMap.BilinForm.dualSubmodule (B := (innerₗ ℝ²⁴ : LinearMap.BilinForm ℝ ℝ²⁴))
          S.lattice :=
    LinearMap.BilinForm.HasLeechDistanceSpectrum.lattice_le_dual (S := S) hSpec hDens
  -- Apply the existing overlattice construction: centers form one coset of an overlattice `L'`.
  rcases
      Uniqueness.RigidityClassify.covolume_eq_one_of_covolume_eq_numReps_and_subgroup_card (S := S)
        (hCovol := hCovol) (hSpec := hSpec) (hDens := hDens) (x0 := x0c) (hLdual := hLdual) with
    ⟨L', hLL', hCovol', x0, hCenters⟩
  -- `DiscreteTopology L'` follows from the uniform lower bound `‖v‖ ≥ 2` for `v ∈ L' \ {0}`.
  have hmin : ∀ v : ℝ²⁴, v ∈ L' → v ≠ 0 → (2 : ℝ) ≤ ‖v‖ := by
    intro v hv hv0
    have hx0 : x0 ∈ (S.centers : Set ℝ²⁴) := by
      have : x0 ∈ x0 +ᵥ (L' : Set ℝ²⁴) := by
        refine ⟨0, ?_, by simp⟩
        simp
      simpa [hCenters] using! this
    have hxv : x0 + v ∈ (S.centers : Set ℝ²⁴) := by
      have : x0 + v ∈ x0 +ᵥ (L' : Set ℝ²⁴) := by
        refine ⟨v, hv, by simp⟩
      simpa [hCenters] using! this
    have hxne : x0 + v ≠ x0 :=
      add_ne_left.mpr hv0
    have hdist : (2 : ℝ) ≤ dist (x0 + v) x0 := by
      simpa [hSep] using!
        S.toSpherePacking.centers_dist' (x := x0 + v) (y := x0) hxv hx0 hxne
    -- `dist (x0+v) x0 = ‖v‖`
    have : dist (x0 + v) x0 = ‖v‖ := by simp [dist_eq_norm]
    simpa [this] using! hdist
  let disc : DiscreteTopology L' :=
    Dim24.Uniqueness.RigidityClassify.discreteTopology_of_two_le_norm (L := L') hmin
  letI : DiscreteTopology L' := disc
  -- `IsZLattice` follows from `S.lattice ≤ L'` since `S.lattice` has full real span.
  have hZ : IsZLattice ℝ L' :=
    SpherePacking.Dim24.Uniqueness.RigidityClassify.isZLattice_of_le_of_isZLattice
      (L := S.lattice) (L' := L') hLL'
  have hUnimod : Unimodular L' := by
    simpa [Unimodular] using! hCovol'
  refine ⟨x0, L', ⟨disc, ⟨hZ, ⟨hUnimod, hCenters⟩⟩⟩⟩

theorem contactSet_ncard_eq_196560_of_CE
    (S : PeriodicSpherePacking 24)
    (hSep : S.separation = 2)
    (hSpec : HasLeechDistanceSpectrum S)
  (hDens : S.density = LeechPacking.density)
  (x0 : S.centers) :
  Set.ncard (contactSet S x0) = 196560 := by
  -- From the sharp density and the distance-spectrum constraint, the centers form a single coset
  -- `xB +ᵥ L'` of a unimodular overlattice `L'`, which is even and rootless. The shell `‖v‖ = 2` in
  -- `L'` then has cardinality `196560`.
  rcases
      centers_eq_translate_of_fullRankLattice_of_CE (S := S) (hSep := hSep) (hSpec := hSpec)
        (hDens := hDens) (x0c := x0) with
    ⟨xB, L', hDisc, hZ, hUnimod', hCentersB⟩
  letI : DiscreteTopology L' := hDisc
  letI : IsZLattice ℝ L' := hZ
  have hxB : xB ∈ (S.centers : Set ℝ²⁴) := by
    have : xB ∈ xB +ᵥ (L' : Set ℝ²⁴) := by
      refine ⟨0, ?_, by simp⟩
      simp
    simpa [hCentersB] using! this
  let xBc : S.centers := ⟨xB, hxB⟩
  -- Transfer the coset description to the chosen basepoint `x0`.
  have hCenters :
      (S.centers : Set ℝ²⁴) = (x0 : ℝ²⁴) +ᵥ (L' : Set ℝ²⁴) := by
    have hx0 : (x0 : ℝ²⁴) ∈ xB +ᵥ (L' : Set ℝ²⁴) := by
      simpa [hCentersB] using! x0.property
    rcases hx0 with ⟨w0, hw0, hx0Eq⟩
    have hx0Eq' : (x0 : ℝ²⁴) = xB + w0 := by
      simpa [vadd_eq_add] using! hx0Eq.symm
    ext y
    constructor
    · intro hy
      rcases (show y ∈ xB +ᵥ (L' : Set ℝ²⁴) by simpa [hCentersB] using! hy) with ⟨w, hw, rfl⟩
      refine ⟨w - w0, sub_mem hw hw0, ?_⟩
      simp [hx0Eq', vadd_eq_add, add_assoc]
    · rintro ⟨w, hw, rfl⟩
      have : xB +ᵥ (w0 + w) ∈ xB +ᵥ (L' : Set ℝ²⁴) := ⟨w0 + w, add_mem hw0 hw, rfl⟩
      have : (x0 : ℝ²⁴) + w ∈ xB +ᵥ (L' : Set ℝ²⁴) := by
        simpa [hx0Eq', vadd_eq_add, add_assoc] using! this
      simpa [hCentersB] using! this
  -- Rewrite the contact set as the norm-2 shell in `L'`.
  have hContact :
      contactSet S x0 = {v : ℝ²⁴ | v ∈ (L' : Set ℝ²⁴) ∧ ‖v‖ = (2 : ℝ)} := by
    exact contactSet_eq_norm2_vectors_of_centers_eq_translate S L' x0 hCenters
  -- Evenness + rootlessness of `L'` come from the distance spectrum for center differences.
  have hEven' : EvenNormSq L' := by
    intro v hv
    by_cases hv0 : v = 0
    · subst hv0
      refine ⟨0, by simp⟩
    · have hxv : xB + v ∈ (S.centers : Set ℝ²⁴) := by
        have : xB + v ∈ xB +ᵥ (L' : Set ℝ²⁴) := by
          refine ⟨v, hv, by simp⟩
        simpa [hCentersB] using! this
      have hxne : (⟨xB + v, hxv⟩ : S.centers) ≠ xBc := by
        intro h
        apply hv0
        have : xB + v = xB := congrArg Subtype.val h
        have : xB + v = xB + 0 := by simpa using! this
        exact add_left_cancel this
      rcases hSpec ⟨xB + v, hxv⟩ xBc hxne with ⟨k, _hk, hkEq⟩
      refine ⟨k, ?_⟩
      -- simplify `(xB + v) - xB = v`
      have hsub : ((xB + v) - xB) = v := by
        simp
      simpa [hsub, xBc] using! hkEq
  have hRootless' : Rootless L' := by
    intro v hv hv0
    have hxv : xB + v ∈ (S.centers : Set ℝ²⁴) := by
      have : xB + v ∈ xB +ᵥ (L' : Set ℝ²⁴) := by
        refine ⟨v, hv, by simp⟩
      simpa [hCentersB] using! this
    have hxne : (⟨xB + v, hxv⟩ : S.centers) ≠ xBc := by
      intro h
      apply hv0
      have : xB + v = xB := congrArg Subtype.val h
      have : xB + v = xB + 0 := by simpa using! this
      exact add_left_cancel this
    rcases hSpec ⟨xB + v, hxv⟩ xBc hxne with ⟨k, hk, hkEq⟩
    have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hkEq' : ‖v‖ ^ 2 = (2 : ℝ) * (k : ℕ) := by
      have hsub : ((xB + v) - xB) = v := by
        simp
      simpa [hsub, xBc] using! hkEq
    intro h
    have : (4 : ℝ) ≤ (2 : ℝ) := by
      have : (4 : ℝ) ≤ ‖v‖ ^ 2 := by nlinarith [hkEq', hk']
      simpa [h] using! this
    nlinarith
  -- The norm-2 shell equals the `minShell` of `L'`.
  have hShell :
      {v : ℝ²⁴ | v ∈ (L' : Set ℝ²⁴) ∧ ‖v‖ = (2 : ℝ)} =
        minShell L' := by
    ext v
    constructor
    · rintro ⟨hvL, hvNorm⟩
      refine ⟨hvL, ?_⟩
      -- `‖v‖ = 2` implies `‖v‖^2 = 4 = 2*2`.
      calc
        ‖v‖ ^ 2 = (2 : ℝ) ^ 2 := by simp [hvNorm]
        _ = (2 : ℝ) * (2 : ℕ) := by norm_num
    · intro hv
      refine ⟨hv.1, ?_⟩
      exact norm_eq_two_of_mem_minShell (L := L') hv
  have hMinShell :
      Set.ncard (minShell L') = 196560 :=
    minShell_ncard_eq_196560_of_even_unimodular_rootless
      (L := L') (hEven := hEven') (hUnimod := hUnimod') (hRootless := hRootless')
  -- Conclude.
  calc
    Set.ncard (contactSet S x0)
        = Set.ncard {v : ℝ²⁴ | v ∈ (L' : Set ℝ²⁴) ∧ ‖v‖ = (2 : ℝ)} := by
            simp [hContact]
    _ = Set.ncard (minShell L') := by
            simpa using! congrArg Set.ncard hShell
    _ = 196560 := hMinShell

/--
Local rigidity (CE route): in the normalized equality case, `contactSet S x0` is isometric to
`leechKissingVectors`.
-/
public theorem contactSet_is_leech_kissing_of_CE
    (S : PeriodicSpherePacking 24)
    (hSep : S.separation = 2)
    (hSpec : HasLeechDistanceSpectrum S)
    (hDens : S.density = LeechPacking.density)
    (x0 : S.centers) :
    ∃ e : ℝ²⁴ ≃ᵢ ℝ²⁴, e '' (contactSet S x0) = leechKissingVectors := by
  have hKiss : IsKissingConfiguration (contactSet S x0) :=
    contactSet_isKissingConfiguration_of_separation_eq_two (S := S) hSep x0
  have hCard : Set.ncard (contactSet S x0) = 196560 :=
    contactSet_ncard_eq_196560_of_CE (S := S) (hSep := hSep) (hSpec := hSpec) (hDens := hDens) x0
  exact Uniqueness.BS81.kissing_configuration_unique_24_bs81 (X := contactSet S x0) hKiss hCard

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify.CE
