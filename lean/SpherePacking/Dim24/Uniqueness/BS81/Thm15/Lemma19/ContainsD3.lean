-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma18.Count44
public import SpherePacking.Dim24.Uniqueness.BS81.LatticeL

/-!
# BS81 Lemma 19: a copy of `D₃` in `L`

Let `L := span_ℤ (2 • C)` and let `L₄` be the norm-`4` shell.
Using the `44` common-neighbors count from BS81 Lemma 18(ii), we find vectors `u,v,w ∈ L₄` with
`⟪u, v⟫ = 0` and `⟪u, w⟫ = ⟪v, w⟫ = 2`. These vectors generate a sublattice isometric to `D₃`.

## Main statement
* `lattice_contains_D3`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma19

noncomputable section

open scoped RealInnerProductSpace

open Set

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- Existence of three shell vectors with the inner products needed to generate `D₃`. -/
theorem exists_D3_generators_in_shell4
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C) :
    ∃ u v w : ℝ²⁴,
      u ∈ latticeShell4 C ∧
      v ∈ latticeShell4 C ∧
      w ∈ latticeShell4 C ∧
      (⟪u, v⟫ : ℝ) = 0 ∧
      (⟪u, w⟫ : ℝ) = 2 ∧
      (⟪v, w⟫ : ℝ) = 2 := by
  -- Pick `u₀ ∈ C`, then choose `v₀ ∈ C` with `⟪u₀,v₀⟫ = 0` using `A₀(u₀)=93150`.
  have hCpos : (0 : ℕ) < Set.ncard C := by
    simp [h.card_eq]
  have hCnonempty : C.Nonempty :=
    (Set.ncard_pos (s := C) (hs := h.code.finite)).1 hCpos
  rcases hCnonempty with ⟨u₀, hu₀⟩
  rcases h.distCount_eq (u := u₀) hu₀ with
    ⟨_h1, _hneg1, _hhalf, _hneghalf, _hquarter, _hnegquarter, hzero⟩
  let S : Set ℝ²⁴ := {v : ℝ²⁴ | v ∈ C ∧ (⟪u₀, v⟫ : ℝ) = 0}
  have hSpos : (0 : ℕ) < Set.ncard S := by
    have : (0 : ℕ) < Uniqueness.BS81.distCount (n := 24) C u₀ (0 : ℝ) := by
      simp [hzero]
    simpa [Uniqueness.BS81.distCount, S] using! this
  have hSfinite : S.Finite := h.code.finite.subset (by intro v hv; exact hv.1)
  have hSnonempty : S.Nonempty := (Set.ncard_pos (s := S) (hs := hSfinite)).1 hSpos
  rcases hSnonempty with ⟨v₀, hv₀⟩
  have hv₀C : v₀ ∈ C := hv₀.1
  have hinner₀ : (⟪u₀, v₀⟫ : ℝ) = 0 := hv₀.2
  -- Move to the shell `L₄ = {v ∈ L : ‖v‖² = 4}` by scaling by `2`.
  have huShell : (2 : ℝ) • u₀ ∈ latticeShell4 C :=
    Uniqueness.BS81.smul_mem_latticeShell4_of_norm_one
      (C := C) (u := u₀) hu₀ (h.code.norm_one hu₀)
  have hvShell : (2 : ℝ) • v₀ ∈ latticeShell4 C :=
    Uniqueness.BS81.smul_mem_latticeShell4_of_norm_one
      (C := C) (u := v₀) hv₀C (h.code.norm_one hv₀C)
  have hinner : (⟪(2 : ℝ) • u₀, (2 : ℝ) • v₀⟫ : ℝ) = 0 := by
    simp [inner_smul_left, inner_smul_right, hinner₀]
  -- Apply BS81 Lemma 18(ii): there are 44 common neighbors at inner product `2`.
  let T : Set ℝ²⁴ :=
    {w : ℝ²⁴ |
      w ∈ latticeShell4 C ∧ (⟪(2 : ℝ) • u₀, w⟫ : ℝ) = 2 ∧ (⟪(2 : ℝ) • v₀, w⟫ : ℝ) = 2}
  have hTcard : Set.ncard T = 44 :=
    Lemma18.commonNeighbors44_in_shell4 C h huShell hvShell hinner
  have hTnonempty : T.Nonempty := by
    refine Set.nonempty_of_ncard_ne_zero ?_
    simp [hTcard]
  rcases hTnonempty with ⟨w, hw⟩
  refine ⟨(2 : ℝ) • u₀, (2 : ℝ) • v₀, w, huShell, hvShell, hw.1, ?_, hw.2.1, hw.2.2⟩
  exact hinner

/-- BS81 Lemma 19: the lattice `L = span_ℤ (2 • C)` contains a copy of `D₃`. -/
public theorem lattice_contains_D3
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C) :
    ∃ g : Fin 3 → ℝ²⁴,
      (∀ i : Fin 3, g i ∈ (latticeL C : Set ℝ²⁴)) ∧
      (∀ i : Fin 3, ‖g i‖ ^ 2 = (4 : ℝ)) ∧
      (⟪g 0, g 1⟫ : ℝ) = 0 ∧
      (⟪g 0, g 2⟫ : ℝ) = 2 ∧
      (⟪g 1, g 2⟫ : ℝ) = 2 := by
  rcases exists_D3_generators_in_shell4 (C := C) h with
    ⟨u, v, w, hu, hv, hw, huv, huw, hvw⟩
  refine ⟨(![u, v, w] : Fin 3 → ℝ²⁴), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [hu.1, hv.1, hw.1]
  · intro i
    fin_cases i <;> simp [hu.2, hv.2, hw.2]
  · simpa using! huv
  · simpa using! huw
  · simpa using! hvw

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma19
