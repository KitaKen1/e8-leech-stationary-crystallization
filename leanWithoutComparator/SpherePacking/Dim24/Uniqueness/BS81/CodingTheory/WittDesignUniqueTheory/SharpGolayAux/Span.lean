-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import
SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.SharpGolayAux.Extraction
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.EvenBasisSpan

/-!
# Spanning by the extracted generators

For `E : Extraction C hC`, we show that the code `C` is spanned by the distinguished dodecad word
`E.u` together with the pinned lifts `E.v i`. This corresponds to Proposition `gen_matrix`
(part (1)) in the in-repo note `paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace GolayUniquenessSteps.WittDesignUniqueTheory.SharpGolayUniqueFromBiplaneAux.Extraction

noncomputable section

open scoped BigOperators symmDiff
open GolayBounds
open GolayUniquenessSteps.CodeFromOctadsAux
open PunctureEven
open BiplaneFromSharp

local notation "Word" => BinWord 24

/-- If `d ∈ C` is pinned at `p` and vanishes after erasing `support u`, then `d = 0`. -/
public lemma eraseCoords_eq_zero_of_mem_of_p0
    {C : Code 24} {hC : IsSharpBS81GolayInput C} (E : Extraction C hC)
    {d : Word} (hdC : d ∈ C) (hdp0 : d E.p = 0)
    (hErase : eraseCoords (support E.u) d = 0) :
    d = 0 := by
  by_contra hd0
  have hdwt_ge : 8 ≤ weight d :=
    PunctureEven.weight_ge_minDist_of_mem (C := C) hC.minDist_ge hC.linear.1 hdC hd0
  -- `eraseCoords S d = 0` forces `supp d ⊆ S`.
  have hsupp : support d ⊆ support E.u :=
    (PunctureEven.eraseCoords_eq_zero_iff_support_subset (S := support E.u) (w := d)).1 hErase
  have hu_p : E.u E.p = 1 := (GolayBounds.mem_support (w := E.u) E.p).1 E.hp
  have hdu : d ≠ E.u := by
    grind only
  let z : Word := E.u + d
  have hzC : z ∈ C := hC.linear.2 E.u d E.huC hdC
  have hz0 : z ≠ 0 := by
    intro hz0
    have hz_p : z E.p = 1 := by simp [z, Pi.add_apply, hu_p, hdp0]
    simp [hz0] at hz_p
  have hzwt_ge : 8 ≤ weight z :=
    PunctureEven.weight_ge_minDist_of_mem (C := C) hC.minDist_ge hC.linear.1 hzC hz0
  have hzwt_le : weight z ≤ 4 := by
    simpa [z] using!
      PunctureEven.weight_add_le_four_of_support_subset (u := E.u) (x := d) hsupp E.hwt hdwt_ge
  exact (not_lt_of_ge hzwt_ge (lt_of_le_of_lt hzwt_le (by decide : (4 : ℕ) < 8)))

/-- The complement set `T` is `{t0} ∪ range t` in the extracted enumeration. -/
public lemma insert_t0_image_t_eq_T
    {C : Code 24} {hC : IsSharpBS81GolayInput C} (E : Extraction C hC) :
    insert E.t0 ((Finset.univ : Finset (Fin 11)).image E.t) = E.T := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · simp
    · rcases Finset.mem_image.1 hx with ⟨i, _, rfl⟩
      simp
  · intro hxT
    have hxImg : x ∈ Finset.image E.fT (Finset.univ : Finset (Fin 12)) := by
      -- `Finset.image E.fT univ = E.T`
      simpa using! (show x ∈ E.T from hxT)
    rcases Finset.mem_image.1 hxImg with ⟨k, _, rfl⟩
    cases k using Fin.cases with
    | zero =>
        simp
    | succ i =>
        refine Finset.mem_insert.2 (Or.inr ?_)
        refine Finset.mem_image.2 ⟨i, by simp, ?_⟩
        simp

/-- The even-basis span lies in the image of the span of the pinned lifts under `eraseLinear`. -/
public lemma mem_map_eraseLinear_span_v
    {C : Code 24} {hC : IsSharpBS81GolayInput C} (E : Extraction C hC) :
    Submodule.span (ZMod 2) (Set.range (evenBasisFamily E.t0 E.t)) ≤
      Submodule.map (PunctureEven.eraseLinear (support E.u))
        (Submodule.span (ZMod 2) (Set.range E.v)) := by
  refine Submodule.span_le.2 ?_
  intro w hw
  rcases hw with ⟨i, rfl⟩
  refine Submodule.mem_map.2 ?_
  refine ⟨E.v i, ?_, ?_⟩
  · exact Submodule.subset_span ⟨i, rfl⟩
  · -- `eraseLinear` is `eraseCoords`
    simpa [PunctureEven.eraseLinear] using! (E.hverase i)

/-- Any codeword pinned at `p` lies in the span of the pinned lifts `v i`. -/
public lemma mem_span_v_of_mem_of_p0
    {C : Code 24} {hC : IsSharpBS81GolayInput C} (E : Extraction C hC)
    {c : Word} (hcC : c ∈ C) (hcp0 : c E.p = 0) :
    c ∈ Submodule.span (ZMod 2) (Set.range E.v) := by
  let S : Finset (Fin 24) := support E.u
  have hw_even : eraseCoords S c ∈ evenWeightCode S := by
    have hw_erase : eraseCoords S c ∈ eraseCode S C := ⟨c, hcC, rfl⟩
    have : eraseCode S C ⊆ evenWeightCode S :=
      eraseCode_subset_evenWeightCode_of_sharp (C := C) hC E.huC
    exact this hw_erase
  have hsupp :
      support (eraseCoords S c) ⊆ insert E.t0 ((Finset.univ : Finset (Fin 11)).image E.t) := by
    have hT : insert E.t0 ((Finset.univ : Finset (Fin 11)).image E.t) = E.T :=
      insert_t0_image_t_eq_T E
    intro x hx
    rw [hT]
    have hxS : x ∉ S :=
      (Finset.mem_sdiff.1 (by simpa [PunctureEven.support_eraseCoords] using! hx)).2
    exact (mem_T_iff_not_mem_support E x).mpr hxS
  have hspan_erase :
      eraseCoords S c ∈ Submodule.span (ZMod 2) (Set.range (evenBasisFamily E.t0 E.t)) := by
    have hEven : Even (weight (eraseCoords S c)) := hw_even.2
    exact EvenBasisSpan.mem_span_evenBasisFamily_of_support_subset_of_even
      (t0 := E.t0) (t := E.t) E.htinj (by simpa using! E.hne) hsupp hEven
  have hmap :
      eraseCoords S c ∈ Submodule.map (PunctureEven.eraseLinear S)
        (Submodule.span (ZMod 2) (Set.range E.v)) :=
    (mem_map_eraseLinear_span_v E) hspan_erase
  rcases Submodule.mem_map.1 hmap with ⟨x, hxspan, hxEq⟩
  -- show `c = x` by the "pinned kernel is trivial" argument
  have hxC : x ∈ C := by
    -- span of `v` lies in the linear submodule of `C`
    have hspan_le :
        Submodule.span (ZMod 2) (Set.range E.v) ≤
          LinearCode.submodule (n := 24) C hC.linear := by
      refine Submodule.span_le.2 ?_
      intro w hw
      rcases hw with ⟨i, rfl⟩
      exact E.hvC i
    exact hspan_le hxspan
  have hxp0 : x E.p = 0 := by
    have hspan_le :
        Submodule.span (ZMod 2) (Set.range E.v) ≤
          LinearMap.ker (LinearMap.proj E.p) := by
      refine Submodule.span_le.2 ?_
      intro w hw
      rcases hw with ⟨i, rfl⟩
      -- `proj p (v i) = v i p`
      change (E.v i) E.p = 0
      simpa using! E.hvp0 i
    have : (LinearMap.proj E.p : Word →ₗ[ZMod 2] ZMod 2) x = 0 := hspan_le hxspan
    simpa [LinearMap.proj] using! this
  have hxEq' : eraseCoords S x = eraseCoords S c := by
    simpa [PunctureEven.eraseLinear, S] using! hxEq
  have hdiff_erase : eraseCoords S (c - x) = 0 := by
    simpa [PunctureEven.eraseLinear, S, hxEq'] using! (PunctureEven.eraseLinear S).map_sub c x
  have hdiff_p0 : (c - x) E.p = 0 := by
    simp [hcp0, hxp0]
  have hdiffC : c - x ∈ C := by
    simpa [sub_eq_add_neg] using! hC.linear.2 c x hcC hxC
  have hdiff0 : c - x = 0 := by
    simpa [S] using! eraseCoords_eq_zero_of_mem_of_p0 E hdiffC hdiff_p0 hdiff_erase
  have : c = x := sub_eq_zero.mp hdiff0
  simpa [this] using! hxspan

/-- Every codeword lies in the span of `u` together with the pinned lifts `v i`. -/
public lemma mem_span_u_v_of_mem
    {C : Code 24} {hC : IsSharpBS81GolayInput C} (E : Extraction C hC)
    {c : Word} (hcC : c ∈ C) :
    c ∈ Submodule.span (ZMod 2) (Set.insert E.u (Set.range E.v)) := by
  rcases GolayBounds.zmod2_eq_zero_or_eq_one (c E.p) with h0 | h1
  · -- pinned case
    have hc : c ∈ Submodule.span (ZMod 2) (Set.range E.v) :=
      mem_span_v_of_mem_of_p0 E hcC (by simpa using! h0)
    have hmono : (Set.range E.v) ⊆ Set.insert E.u (Set.range E.v) := by
      intro w hw
      exact Set.mem_insert_of_mem _ hw
    exact (Submodule.span_mono hmono) hc
  · -- add `u` to pin coordinate
    let c' : Word := c + E.u
    have hc'C : c' ∈ C := hC.linear.2 c E.u hcC E.huC
    have hcp0 : c' E.p = 0 := by
      have hu_p : E.u E.p = 1 := (GolayBounds.mem_support (w := E.u) E.p).1 E.hp
      simp [c', Pi.add_apply, h1, hu_p, GolayBounds.zmod2_add_self]
    have hc' : c' ∈ Submodule.span (ZMod 2) (Set.range E.v) :=
      mem_span_v_of_mem_of_p0 E hc'C hcp0
    have hu : E.u ∈ Submodule.span (ZMod 2) (Set.insert E.u (Set.range E.v)) :=
      Submodule.subset_span (Set.mem_insert _ _)
    have hc'big :
        c' ∈ Submodule.span (ZMod 2) (Set.insert E.u (Set.range E.v)) :=
      Submodule.span_mono (by
        intro w hw
        exact Set.mem_insert_of_mem _ hw) hc'
    -- `c = c' + u`
    have : c = c' + E.u := by
      funext i
      simp [c', Pi.add_apply, add_assoc, GolayBounds.zmod2_add_self]
    simpa [this] using! (Submodule.add_mem _ hc'big hu)

end

end GolayUniquenessSteps.WittDesignUniqueTheory.SharpGolayUniqueFromBiplaneAux.Extraction

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
