-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Package
public import SpherePacking.Dim24.Uniqueness.BS81.FromKissing
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20.ContainsDn
public import SpherePacking.Dim24.Uniqueness.BS81.LatticeL

import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma17.Shell4
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma18.Count44
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma19.ContainsD3
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.LeechIsometry

/-!
# BS81 Theorem 15: uniqueness in `Ω₂₄`

This file collects the public statements used in the proof of BS81 Theorem 15: a tight spherical
11-design `C ⊆ Ω₂₄` is isometric to the Leech unit-sphere code.

We expose the intermediate lemmas as separate theorems to keep the proof graph explicit and
refactor-friendly.

## Main definitions
* `Uniqueness.BS81.leechUnitCode`

## Main statements
* `Uniqueness.BS81.lemma18_joint44_count`
* `Uniqueness.BS81.lemma19_contains_D3`
* `Uniqueness.BS81.lemma20_contains_Dn_all`
* `Uniqueness.BS81.thm15_isometry_to_leechUnitCode`

## References
* Bannai-Sloane (1981), Section 4, Theorem 15 and Lemmas 16-21.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81

noncomputable section

open scoped RealInnerProductSpace Pointwise

open Uniqueness.RigidityClassify.CE

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
### The Leech unit-sphere code `(1/2)Λ₄`

In the repo, `leechKissingVectors` is the set of Leech lattice vectors of norm `2`.
Scaling by `1/2` yields a unit-sphere code in `Ω₂₄`.
-/

/-- The unit-sphere code obtained by normalizing the Leech kissing vectors. -/
@[expose] public def leechUnitCode : Set ℝ²⁴ :=
  normalizeKissing leechKissingVectors

/-!
### Lemma 16: minimal norm is 4 (no norm-2 vectors)

BS81 prove this using the design/moment identity (14) specialized to `k=2,4` and a counting
argument on the possible inner products with a putative norm-2 vector.
-/

/-!
### Lemma 17: the norm-4 shell equals `2 • C`

BS81: the norm-4 shell `L₄` contains `2 C` by construction, and has size `≤ 196560` by the LP
bound (Theorem 13), hence `L₄ = 2 C`.
-/

/-!
### Lemmas 18-20: `Dₙ ⊆ L` for `n = 3, ..., 24`

BS81 define the root lattice `Dₙ` via explicit generators (equation (15)) and show `L` contains
copies of these lattices, bootstrapping from combinatorial "44-neighbor" counts in the
association scheme.
-/

/--
In the equality case, orthogonal shell-4 vectors have exactly `44` common neighbors with
inner product `2` to each of them.
-/
public theorem lemma18_joint44_count
    (C : Set ℝ²⁴) (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg C) :
    ∀ ⦃u v : ℝ²⁴⦄,
      u ∈ latticeShell4 C →
        v ∈ latticeShell4 C →
          (⟪u, v⟫ : ℝ) = 0 →
            Set.ncard {w : ℝ²⁴ | w ∈ latticeShell4 C ∧ (⟪u, w⟫ : ℝ) = 2 ∧ (⟪v, w⟫ : ℝ) = 2} =
              44 :=
  fun ⦃_ _⦄ a a_1 a_2 => Thm15.Lemma18.commonNeighbors44_in_shell4 C hEq a a_1 a_2

/--
The lattice `latticeL C` contains a copy of `D₃`: three norm-`4` vectors with the inner products
appearing in the standard `D₃` Gram matrix.
-/
public theorem lemma19_contains_D3
    (C : Set ℝ²⁴) (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg C) :
    ∃ g1 g2 g3 : ℝ²⁴,
      g1 ∈ (latticeL C : Set ℝ²⁴) ∧
      g2 ∈ (latticeL C : Set ℝ²⁴) ∧
      g3 ∈ (latticeL C : Set ℝ²⁴) ∧
      ‖g1‖ ^ 2 = (4 : ℝ) ∧
      ‖g2‖ ^ 2 = (4 : ℝ) ∧
      ‖g3‖ ^ 2 = (4 : ℝ) ∧
      (⟪g1, g2⟫ : ℝ) = 0 ∧
      (⟪g1, g3⟫ : ℝ) = 2 ∧
      (⟪g2, g3⟫ : ℝ) = 2 := by
  rcases Uniqueness.BS81.Thm15.Lemma19.lattice_contains_D3 (C := C) hEq with
    ⟨g, hgL, hgNorm, h01, h02, h12⟩
  refine ⟨g 0, g 1, g 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using! hgL 0
  · simpa using! hgL 1
  · simpa using! hgL 2
  · simpa using! hgNorm 0
  · simpa using! hgNorm 1
  · simpa using! hgNorm 2
  · simpa using! h01
  · simpa using! h02
  · simpa using! h12

/--
For each `n` with `3 ≤ n ≤ 24`, the lattice `latticeL C` contains a copy of the root lattice `Dₙ`.
-/
public theorem lemma20_contains_Dn_all
    (C : Set ℝ²⁴) (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg C) :
    ∀ n : ℕ, 3 ≤ n → n ≤ 24 →
      Nonempty (Uniqueness.BS81.Thm15.Lemma20.ContainsDn C n) := by
  intro n hn3 hn24
  refine ⟨Uniqueness.BS81.Thm15.Lemma20.containsDn_all (C := C) hEq n hn3 hn24⟩

/-!
### Lemma 21: identify `L` with the Leech lattice

BS81 proceed by fixing an orthonormal basis using `D₂₄ ⊆ L` and then classifying all norm-4
vectors using inner-product restrictions; the final step uses the binary Golay code.
-/

/-!
### Theorem 15 (as used in this repo)

We phrase the conclusion as: `C` is isometric to the Leech unit-sphere code `leechUnitCode`.
-/

/-- Theorem 15: any tight spherical 11-design in `Ω₂₄` is isometric to `leechUnitCode`. -/
public theorem thm15_isometry_to_leechUnitCode
    (C : Set ℝ²⁴) (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) :
    ∃ e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴, e '' C = leechUnitCode := by
  -- Step 1: identify the lattice `latticeL C` with the Leech lattice.
  rcases
      (Uniqueness.BS81.Thm15.Lemma21.latticeL_isometric_leech
        (C := C) hEq (hDn := hDn)) with ⟨e, heL⟩
  -- Step 2: transport the norm-4 shell of `latticeL C` to the norm-4 shell of the Leech lattice.
  have hShellLeech :
      e '' latticeShell4 C =
        {v : ℝ²⁴ | v ∈ (LeechLattice : Set ℝ²⁴) ∧ ‖v‖ ^ 2 = (4 : ℝ)} := by
    ext y
    constructor
    · rintro ⟨x, hxShell, rfl⟩
      rcases hxShell with ⟨hxL, hxNorm⟩
      refine ⟨?_, ?_⟩
      · -- membership in the Leech lattice
        have : e x ∈ e '' (latticeL C : Set ℝ²⁴) := ⟨x, hxL, rfl⟩
        simpa [heL] using! this
      · -- norms are preserved by the isometry
        simpa [e.norm_map x] using! hxNorm
    · rintro ⟨hyL, hyNorm⟩
      -- Pull back `y` to a vector in `latticeL C` using `heL`.
      rcases (by simpa [heL] using! hyL : y ∈ e '' (latticeL C : Set ℝ²⁴)) with ⟨x, hxL, rfl⟩
      refine ⟨x, ⟨hxL, ?_⟩, rfl⟩
      simpa [e.norm_map x] using! hyNorm
  -- Step 3: `‖v‖^2 = 4` is equivalent to `‖v‖ = 2` for the nonnegative norm, so this shell is
  -- exactly `leechKissingVectors`.
  have hLeechShell :
      {v : ℝ²⁴ | v ∈ (LeechLattice : Set ℝ²⁴) ∧ ‖v‖ ^ 2 = (4 : ℝ)} =
        Uniqueness.RigidityClassify.CE.leechKissingVectors := by
    ext v
    constructor
    · rintro ⟨hvL, hvSq⟩
      refine ⟨hvL, ?_⟩
      have hn : 0 ≤ ‖v‖ := norm_nonneg v
      nlinarith [hvSq, hn]
    · rintro ⟨hvL, hvNorm⟩
      refine ⟨hvL, ?_⟩
      -- square both sides
      nlinarith [hvNorm]
  have hShellImage : e '' latticeShell4 C = Uniqueness.RigidityClassify.CE.leechKissingVectors :=
    hShellLeech.trans hLeechShell
  -- Step 4: by Lemma 17, the norm-4 shell is exactly `2 • C`.
  have hShellEq : latticeShell4 C = twoCodeVectors C :=
    Uniqueness.BS81.Thm15.Lemma17.shell4_eq_twoCodeVectors (C := C) hEq
  have hTwoImage : e '' twoCodeVectors C = Uniqueness.RigidityClassify.CE.leechKissingVectors := by
    simpa [hShellEq] using! hShellImage
  -- Step 5: cancel the factor `2` to identify `e '' C` with the normalized Leech code.
  refine ⟨e, ?_⟩
  ext z
  constructor
  · rintro ⟨c, hcC, rfl⟩
    -- Witness in the Leech kissing set: `e (2c)`.
    refine ⟨e ((2 : ℝ) • c), ?_, ?_⟩
    · -- membership in `leechKissingVectors`
      have : e ((2 : ℝ) • c) ∈ e '' twoCodeVectors C := by
        refine ⟨(2 : ℝ) • c, ?_, rfl⟩
        exact ⟨c, hcC, rfl⟩
      simpa [hTwoImage] using! this
    · -- scaling by `1/2` cancels the factor `2`
      simp [map_smul, smul_smul]
  · rintro ⟨x, hxLeech, hxz⟩
    -- Pull back `x` as `e (2c)` for some `c ∈ C`, then `z = e c`.
    have : x ∈ e '' twoCodeVectors C := by
      simpa [hTwoImage] using! hxLeech
    rcases this with ⟨y, hyTwo, rfl⟩
    rcases hyTwo with ⟨c, hcC, rfl⟩
    refine ⟨c, hcC, ?_⟩
    -- `z = (1/2) • e (2c) = e c`
    -- and we rewrite `hxz` to close.
    simpa [map_smul, smul_smul] using! hxz
end

end SpherePacking.Dim24.Uniqueness.BS81
