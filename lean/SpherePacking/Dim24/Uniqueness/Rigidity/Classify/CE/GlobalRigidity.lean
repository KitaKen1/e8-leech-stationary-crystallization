-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Packing
public import SpherePacking.Dim24.Uniqueness.Defs
import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.CE.LocalRigidity
import SpherePacking.Dim24.Uniqueness.Rigidity.DensityProps
import SpherePacking.Dim24.Uniqueness.Rigidity.DualProps
import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Overlattice.IndexCovolume
import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.EvenUnimodular.Discrete
import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.RootlessCase.MinShell
import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.RootlessCase.LeechMinShellSpan
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Global rigidity for the CE route

This file upgrades the local statement "the contact configuration around a center is Leech" to the
global statement "the entire periodic packing is isometric to the Leech packing", in the CE
Section 8 approach.

## Main statement
* `Uniqueness.RigidityClassify.CE.isometric_leechPacking_of_CE`
-/

namespace SpherePacking.Dim24.Uniqueness.RigidityClassify.CE

noncomputable section

open scoped RealInnerProductSpace Pointwise
open Uniqueness.RigidityClassify Uniqueness.RigidityClassify.NiemeierRootless

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
### 2. From contact-set identification to lattice identification

Once centers are a lattice coset `x0 + L'`, the contact set at `x0` is essentially the set of
norm-2 vectors in `L'`. If it is isometric to the Leech kissing configuration, then `L'` should be
isometric to the Leech lattice itself.
-/

theorem lattice_isometric_leech_of_contactSet_is_leech
    {L' : Submodule ℤ ℝ²⁴}
    [DiscreteTopology L']
    (hZ : IsZLattice ℝ L')
    (hUnimod : Unimodular L')
    (hKiss : ∃ e : ℝ²⁴ ≃ᵢ ℝ²⁴, e '' {v : ℝ²⁴ | v ∈ (L' : Set ℝ²⁴) ∧ ‖v‖ = (2 : ℝ)} =
      leechKissingVectors) :
    ∃ e : ℝ²⁴ ≃ᵢ ℝ²⁴, e '' (L' : Set ℝ²⁴) = (LeechLattice : Set ℝ²⁴) := by
  -- Abbreviations.
  let shell : Set ℝ²⁴ := {v : ℝ²⁴ | v ∈ (L' : Set ℝ²⁴) ∧ ‖v‖ = (2 : ℝ)}
  -- A helper: in `ℝ²⁴`, if `‖u‖=‖v‖=2` and `‖u-v‖=4`, then `v = -u`.
  have eq_neg_of_norm_eq_two_of_norm_sub_eq_four {u v : ℝ²⁴}
      (hu : ‖u‖ = (2 : ℝ)) (hv : ‖v‖ = (2 : ℝ)) (hsub : ‖u - v‖ = (4 : ℝ)) :
      v = -u := by
    have hinner : ⟪u, v⟫ = (-4 : ℝ) := by
      have hsubSq :
          ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * ⟪u, v⟫ + ‖v‖ ^ 2 := by
        simpa using! (norm_sub_sq_real u v)
      have : (4 : ℝ) ^ 2 = ‖u‖ ^ 2 - 2 * ⟪u, v⟫ + ‖v‖ ^ 2 := by
        simpa [hsub] using! hsubSq
      nlinarith [this, hu, hv]
    have huSq : ‖u‖ ^ 2 = (4 : ℝ) := by nlinarith [hu]
    have hvSq : ‖v‖ ^ 2 = (4 : ℝ) := by nlinarith [hv]
    have hadd0 : u + v = 0 :=
      add_eq_zero_of_normSq_eq_four_of_inner_eq_neg_four (u := u) (v := v) huSq hvSq hinner
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using! hadd0)
  rcases hKiss with ⟨e, he⟩
  have heShell : e '' shell = leechKissingVectors := by simpa [shell] using! he
  -- First show `e 0 = 0` using antipodes.
  have he0 : e 0 = 0 := by
    -- Produce a concrete Leech minimal vector and pull it back via `e`.
    let y : ℝ²⁴ := Dim24.leechGeneratorRows (⟨1, by decide⟩ : Fin 24)
    have hyMin : y ∈ minShell LeechLattice :=
      leechGeneratorRows_mem_minShell_of_ne_zero
        (i := (⟨1, by decide⟩ : Fin 24)) (by decide)
    have hyK : y ∈ leechKissingVectors :=
      ⟨hyMin.1, norm_eq_two_of_mem_minShell (L := LeechLattice) hyMin⟩
    have hyImg : y ∈ e '' shell := by
      -- Rewrite the goal via `e '' shell = leechKissingVectors`.
      rw [heShell]
      exact hyK
    rcases hyImg with ⟨x, hx, -⟩
    have hxneg : (-x) ∈ shell := by
      refine ⟨neg_mem hx.1, ?_⟩
      calc
        ‖-x‖ = ‖x‖ := norm_neg x
        _ = (2 : ℝ) := hx.2
    have hxImg : e x ∈ leechKissingVectors := by
      have hx' : e x ∈ e '' shell := ⟨x, hx, rfl⟩
      -- Convert membership in `e '' shell` to membership in `leechKissingVectors`.
      have hx'' : e x ∈ leechKissingVectors := by
        -- Avoid `simp` (which unfolds `Set.mem_image`) by rewriting the set directly.
        simpa [heShell] using! hx'
      exact hx''
    have hxnegImg : e (-x) ∈ leechKissingVectors := by
      have hx' : e (-x) ∈ e '' shell := ⟨-x, hxneg, rfl⟩
      have hx'' : e (-x) ∈ leechKissingVectors := by
        simpa [heShell] using! hx'
      exact hx''
    have hdist : ‖(e x) - (e (-x))‖ = (4 : ℝ) := by
      have hdist' : dist (e x) (e (-x)) = dist x (-x) := by simpa using! (e.dist_eq x (-x))
      have hxnorm : ‖x‖ = (2 : ℝ) := hx.2
      have hdistx : dist x (-x) = (4 : ℝ) := by
        -- `dist x (-x) = ‖x - (-x)‖ = ‖x + x‖ = ‖(2:ℝ) • x‖ = 4`.
        have hxx : ‖x + x‖ = (4 : ℝ) := by
          calc
            ‖x + x‖ = ‖(2 : ℝ) • x‖ := by simp [two_smul]
            _ = ‖(2 : ℝ)‖ * ‖x‖ := by simp [norm_smul]
            _ = (2 : ℝ) * (2 : ℝ) := by simp [hxnorm]
            _ = (4 : ℝ) := by norm_num
        simpa [dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using! hxx
      have : dist (e x) (e (-x)) = (4 : ℝ) := by simpa [hdistx] using! hdist'
      simpa [dist_eq_norm] using! this
    have hanti : e (-x) = -(e x) :=
      eq_neg_of_norm_eq_two_of_norm_sub_eq_four (hu := (hxImg.2))
        (hv := (hxnegImg.2)) hdist
    have hm : e (midpoint ℝ x (-x)) = midpoint ℝ (e x) (e (-x)) :=
      IsometryEquiv.map_midpoint e x (-x)
    -- `midpoint x (-x) = 0` and similarly on the image.
    simpa [midpoint_eq_smul_add, hanti] using! hm
  -- Mazur-Ulam: an isometry with `e 0 = 0` is linear.
  let eLin : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴ := e.toRealLinearIsometryEquivOfMapZero he0
  have heShellLin : (eLin : ℝ²⁴ → ℝ²⁴) '' shell = leechKissingVectors := by
    simpa [eLin, shell] using! he
  -- Let `M` be the ℤ-span of the shell.
  let M : Submodule ℤ ℝ²⁴ := Submodule.span ℤ shell
  have hML : M ≤ L' := by
    refine Submodule.span_le.2 ?_
    intro v hv
    exact hv.1
  -- `LeechLattice` is generated (over `ℤ`) by its minimal shell.
  have hspanLeech :
      Submodule.span ℤ leechKissingVectors = (LeechLattice : Submodule ℤ ℝ²⁴) := by
    -- Convert from `minShell = thetaShell 2` and apply the repo lemma.
    have hminShell :
        Submodule.span ℤ (thetaShell LeechLattice 2 : Set ℝ²⁴) =
          (LeechLattice : Submodule ℤ ℝ²⁴) := by
      simpa [minShell] using!
        (spanZ_minShell_eq_leechLattice :
          Submodule.span ℤ (minShell LeechLattice : Set ℝ²⁴) =
            (LeechLattice : Submodule ℤ ℝ²⁴))
    -- `thetaShell 2` equals `{v ∈ LeechLattice | ‖v‖ = 2}`.
    have hEqShell :
        (thetaShell LeechLattice 2 : Set ℝ²⁴) = leechKissingVectors := by
      ext v
      constructor
      · intro hv
        refine ⟨hv.1, ?_⟩
        have hvMin : v ∈ minShell LeechLattice := by simpa [minShell] using! hv
        exact norm_eq_two_of_mem_minShell (L := LeechLattice) hvMin
      · rintro ⟨hvL, hvNorm⟩
        refine ⟨hvL, ?_⟩
        -- `‖v‖ = 2` implies `‖v‖^2 = 2*2`.
        calc
          ‖v‖ ^ 2 = (2 : ℝ) ^ 2 := by simp [hvNorm]
          _ = (2 : ℝ) * (2 : ℕ) := by norm_num
    simpa [hEqShell] using! hminShell
  -- `eLin` maps `M` onto `LeechLattice`.
  let eZ := eLin.toLinearEquiv.toLinearMap.restrictScalars ℤ
  have hmapM :
      Submodule.map eZ M = LeechLattice := by
    calc
      Submodule.map eZ (Submodule.span ℤ shell)
          = Submodule.span ℤ ((eLin : ℝ²⁴ → ℝ²⁴) '' shell) := by
              simpa [M, eZ] using! (Submodule.map_span eZ shell)
      _ = Submodule.span ℤ leechKissingVectors := by simp [heShellLin]
      _ = LeechLattice := by simpa using! hspanLeech
  -- Identify `M` as the pullback of `LeechLattice` along `eLin`.
  have hcomap :
      M = ZLattice.comap ℝ LeechLattice eLin.toContinuousLinearEquiv.toLinearMap := by
    ext v
    constructor
    · intro hv
      have : (eLin v) ∈ (LeechLattice : Set ℝ²⁴) := by
        have : eLin v ∈ (Submodule.map eZ M : Set ℝ²⁴) :=
          ⟨v, hv, rfl⟩
        simpa [hmapM] using! this
      simpa [ZLattice.coe_comap] using! this
    · intro hv
      have : eLin v ∈ (LeechLattice : Set ℝ²⁴) := by
        simpa [ZLattice.coe_comap] using! hv
      have : eLin v ∈ (Submodule.map eZ M : Set ℝ²⁴) := by
        simpa [hmapM] using! this
      rcases this with ⟨w, hw, hwe⟩
      have : w = v := eLin.injective (by simpa [eZ] using! hwe)
      simpa [this] using! hw
  -- Work with `N := comap ...`, which carries `ZLattice` instances by construction.
  let N : Submodule ℤ ℝ²⁴ :=
    ZLattice.comap ℝ LeechLattice eLin.toContinuousLinearEquiv.toLinearMap
  have hMN : M = N := hcomap
  have hNL : N ≤ L' := by
    exact le_of_eq_of_le (id (Eq.symm hcomap)) hML
  haveI : DiscreteTopology N := by
    dsimp [N]
    infer_instance
  haveI : IsZLattice ℝ N := by
    dsimp [N]
    infer_instance
  -- Compute covolume of `N` using `covolume_comap` (measure-preserving linear isometry).
  have hcovN : ZLattice.covolume N MeasureTheory.volume = 1 := by
    have hcovLeech : ZLattice.covolume LeechLattice MeasureTheory.volume = 1 := by
      simpa [Unimodular] using! Dim24.leech_unimodular
    have hcov :
        ZLattice.covolume N
            MeasureTheory.volume =
          ZLattice.covolume LeechLattice MeasureTheory.volume := by
      -- unfold `N`
      simpa [N] using!
        (ZLattice.covolume_comap (L := LeechLattice) (μ := MeasureTheory.volume)
          (ν := MeasureTheory.volume) (e := eLin.toContinuousLinearEquiv)
          (he := by simpa using! (LinearIsometryEquiv.measurePreserving eLin)))
    simpa [hcovLeech] using! hcov
  -- Compare covolumes to show `N = L'` (index 1).
  have hcovL : ZLattice.covolume L' MeasureTheory.volume = 1 := by
    simpa [Unimodular] using! hUnimod
  have hratio :
      ZLattice.covolume N MeasureTheory.volume /
        ZLattice.covolume L' MeasureTheory.volume =
          (N.toAddSubgroup.relIndex L'.toAddSubgroup : ℝ) := by
    simpa using!
      (ZLattice.covolume_div_covolume_eq_relIndex' (L₁ := N) (L₂ := L') (h := hNL))
  have hrelIndex_one : N.toAddSubgroup.relIndex L'.toAddSubgroup = 1 := by
    have : (N.toAddSubgroup.relIndex L'.toAddSubgroup : ℝ) = 1 := by
      have : ZLattice.covolume N MeasureTheory.volume /
          ZLattice.covolume L' MeasureTheory.volume = (1 : ℝ) := by
        simp [hcovN, hcovL]
      simpa [hratio] using! this
    exact_mod_cast this
  have hLle : L' ≤ N := by
    simpa using! (AddSubgroup.relIndex_eq_one.mp hrelIndex_one)
  have hEq : (L' : Set ℝ²⁴) = (N : Set ℝ²⁴) := by
    ext v
    exact ⟨fun hv => hLle hv, fun hv => hNL hv⟩
  have hImgN : (eLin : ℝ²⁴ → ℝ²⁴) '' (N : Set ℝ²⁴) = (LeechLattice : Set ℝ²⁴) := by
    ext z
    constructor
    · rintro ⟨x, hxN, rfl⟩
      assumption
    · intro hz
      refine ⟨eLin.symm z, ?_, by simp⟩
      have : eLin (eLin.symm z) ∈ (LeechLattice : Set ℝ²⁴) := by simpa using! hz
      assumption
  -- Conclude: `eLin` sends `L'` to `LeechLattice`.
  refine ⟨eLin.toIsometryEquiv, ?_⟩
  simpa [hEq] using! hImgN

/-!
### 3. Conclude isometry of periodic packings

This is the final "global" statement needed by `dim_24.tex` after normalization.
-/

/--
Global rigidity (CE route): in the normalized equality case, an optimal periodic packing is
isometric to the Leech packing.
-/
public theorem isometric_leechPacking_of_CE
    (S : PeriodicSpherePacking 24)
    (hSep : S.separation = 2)
    (hSpec : HasLeechDistanceSpectrum S)
    (hDens : S.density = LeechPacking.density) :
    PeriodicSpherePacking.Isometric S LeechPacking := by
  -- Step 1: show centers are a lattice coset `x0 + L'`.
  have hNonempty : Nonempty S.centers :=
    Dim24.nonempty_centers_of_density_eq_leech (S := S) hDens
  let u0 : S.centers := Classical.choice hNonempty
  rcases
      centers_eq_translate_of_fullRankLattice_of_CE (S := S) (hSep := hSep) (hSpec := hSpec)
        (hDens := hDens) (x0c := u0) with
    ⟨x0, L', hDisc, hZ, hUnimod, hCenters⟩
  letI : DiscreteTopology L' := hDisc
  -- Step 2: local rigidity gives the Leech kissing configuration at the lattice basepoint `x0`.
  have hx0 : x0 ∈ (S.centers : Set ℝ²⁴) := by
    have : x0 ∈ x0 +ᵥ (L' : Set ℝ²⁴) := by
      refine ⟨0, ?_, by simp⟩
      simp
    simpa [hCenters] using! this
  let x0c : S.centers := ⟨x0, hx0⟩
  rcases
      contactSet_is_leech_kissing_of_CE (S := S) (hSep := hSep) (hSpec := hSpec) (hDens := hDens)
        (x0 := x0c) with
    ⟨eK, heK⟩
  -- Step 3: upgrade to a lattice isometry, then to a packing isometry.
  have hCenters' : (S.centers : Set ℝ²⁴) = (x0c : ℝ²⁴) +ᵥ (L' : Set ℝ²⁴) := by
    simpa [x0c] using! hCenters
  have hKiss :
      ∃ e : ℝ²⁴ ≃ᵢ ℝ²⁴,
        e '' {v : ℝ²⁴ | v ∈ (L' : Set ℝ²⁴) ∧ ‖v‖ = (2 : ℝ)} = leechKissingVectors := by
    refine ⟨eK, ?_⟩
    simpa [contactSet_eq_norm2_vectors_of_centers_eq_translate
      (S := S) (L' := L') (x0 := x0c) (hCenters := hCenters')] using! heK
  rcases lattice_isometric_leech_of_contactSet_is_leech (L' := L') (hZ := hZ) (hUnimod := hUnimod)
      hKiss with
    ⟨eL, heL⟩
  -- Use translation to recenter the lattice packing.
  -- `t` is the translation by `-x0`, i.e. `t y = y - x0`.
  let t : ℝ²⁴ ≃ᵢ ℝ²⁴ := (IsometryEquiv.vaddConst x0).symm
  let e : ℝ²⁴ ≃ᵢ ℝ²⁴ := t.trans eL
  have heCenters : e '' (S.centers : Set ℝ²⁴) = (LeechPacking.centers : Set ℝ²⁴) := by
    -- First translate `S.centers = x0 +ᵥ L'` back to `L'`.
    have ht : t '' (S.centers : Set ℝ²⁴) = (L' : Set ℝ²⁴) := by
      ext v
      constructor
      · rintro ⟨y, hy, rfl⟩
        rcases (show (y : ℝ²⁴) ∈ x0 +ᵥ (L' : Set ℝ²⁴) by simpa [hCenters] using! hy) with
          ⟨w, hw, rfl⟩
        simpa [t]
      · intro hv
        refine ⟨x0 + v, ?_, ?_⟩
        · have : x0 + v ∈ x0 +ᵥ (L' : Set ℝ²⁴) := by
            refine ⟨v, ?_, by simp⟩
            simpa using! hv
          simpa [hCenters] using! this
        · simp [t]
    -- Now apply the Leech-lattice identification and rewrite `LeechPacking.centers`.
    calc
      e '' (S.centers : Set ℝ²⁴) = eL '' (t '' (S.centers : Set ℝ²⁴)) := by
        rw [Set.image_image]
        rfl
      _ = eL '' (L' : Set ℝ²⁴) := by simp [ht]
      _ = (LeechPacking.centers : Set ℝ²⁴) := by
        simpa [LeechPacking] using! heL
  refine ⟨?_, ?_⟩
  · -- separation
    simpa [LeechPacking] using! hSep
  · exact ⟨e, by simpa using! heCenters⟩

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify.CE
