-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LatticeL
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Package
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.CodeFromLattice
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechConstructionA
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechParityCode
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma17.Shell4
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.LeechKissingSpan
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4Constraints
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.CodeFromLatticeDiff
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechMembershipDefs
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechMembershipTypeI
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechMembershipTypeII
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechMembershipTypeIII
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.ScaledCoord
import Mathlib.LinearAlgebra.Dimension.Constructions
public import SpherePacking.ForMathlib.CancelDenomsCompat

/-!
# Bridge from code alignment to the Leech shell

This file isolates the step turning a code alignment
`permuteCode σ (codeFromLattice (C := Cset) hDn) = leechParityCode`
into a geometric statement: the induced ambient isometry sends `latticeShell4 Cset` into the Leech
norm-`4` shell `leechShell4`.

The main result is the subset lemma
`image_shell4_subset_leechShell4_of_code_equiv`,
which is later combined with cardinality computations to obtain equality of shells.

## Main definitions
* `leechShell4`
* `OddBasepointRowLast`
* `shell4Isometry`

## Main statement
* `image_shell4_subset_leechShell4_of_code_equiv`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps

noncomputable section

open scoped RealInnerProductSpace

open Set

open Uniqueness.BS81
open Uniqueness.BS81.CodingTheory
open Uniqueness.BS81.Thm15.Lemma21

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace Shell4IsometryAux

/-!
### Local helper: `scaledCoord` determines a vector (orthonormal coordinates).
-/

local notation "rowLast" =>
  Shell4IsometryLeechConstructionA.rowInt Shell4IsometryLeechConstructionA.last

/-- The norm-`4` shell of `LeechLattice` (as a set). -/
@[expose] public def leechShell4 : Set ℝ²⁴ :=
  {x : ℝ²⁴ | x ∈ (LeechLattice : Set ℝ²⁴) ∧ ‖x‖ ^ 2 = (4 : ℝ)}

private theorem mem_leechLattice_of_pattern
    (z : Fin 24 → ℤ)
    (hpat : isPattern1 z ∨ isPattern2 z ∨ isPattern3 z)
    (hII :
      isPattern1 z →
        Shell4IsometryLeechConstructionA.halfWord z ∈
          Shell4IsometryLeechParityCode.leechParityCode ∧
          (8 : ℤ) ∣ ∑ k : Fin 24, z k)
    (hIII :
      isPattern3 z →
        Shell4IsometryLeechConstructionA.halfWord
            (z - Shell4IsometryLeechConstructionA.rowInt Shell4IsometryLeechConstructionA.last) ∈
          Shell4IsometryLeechParityCode.leechParityCode ∧
              (8 : ℤ) ∣
                ∑ k : Fin 24,
                  (z k -
                    Shell4IsometryLeechConstructionA.rowInt
                      Shell4IsometryLeechConstructionA.last k)) :
      Shell4IsometryLeechMembership.vecOfScaledStd z ∈ (LeechLattice : Set ℝ²⁴) := by
  rcases hpat with h1 | h2 | h3
  · rcases hII h1 with ⟨hw, hsum⟩
    simpa using! (Shell4IsometryLeechMembership.mem_leechLattice_of_typeII (z := z) h1 hw hsum)
  · simpa using! (Shell4IsometryLeechMembership.mem_leechLattice_of_typeI (z := z) h2)
  · rcases hIII h3 with ⟨hw, hsum⟩
    simpa using! (Shell4IsometryLeechMembership.mem_leechLattice_of_typeIII (z := z) h3 hw hsum)

/-!
### CodeFromLattice differences (reusable helper)

If `x,y ∈ latticeL`, then the mod-2 reduction of the even coordinate difference `zx-zy` lies in
`codeFromLattice`, hence in `leechParityCode` after applying a coordinate alignment `hσ`.
-/

lemma halfWord_sub_mem_leechParityCode_of_coords
    (Cset : Set ℝ²⁴)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn Cset 24)
    (σ : Equiv (Fin 24) (Fin 24))
    (hσ :
      permuteCode (n := 24) σ (CodeFromLattice.codeFromLattice (C := Cset) hDn) =
        Shell4IsometryLeechParityCode.leechParityCode)
    {x y : ℝ²⁴}
    (hx : x ∈ (latticeL Cset : Set ℝ²⁴))
    (hy : y ∈ (latticeL Cset : Set ℝ²⁴))
    (zx zy : Fin 24 → ℤ)
    (hzx : ∀ i : Fin 24, scaledCoord hDn.e i x = (zx i : ℝ))
    (hzy : ∀ i : Fin 24, scaledCoord hDn.e i y = (zy i : ℝ))
    (hEven : ∀ i : Fin 24, Even (zx i - zy i)) :
    Shell4IsometryLeechConstructionA.halfWord (fun i : Fin 24 => zx (σ i) - zy (σ i)) ∈
      Shell4IsometryLeechParityCode.leechParityCode := by
  -- membership in the extracted code for the even difference
  have hw :
      (fun i : Fin 24 => (((zx i - zy i) / 2 : ℤ) : ZMod 2)) ∈
        CodeFromLattice.codeFromLattice (C := Cset) hDn :=
    Shell4IsometryCodeFromLatticeDiff.halfWord_sub_mem_codeFromLattice
      (C := Cset) (hDn := hDn) (x := x) (y := y) hx hy zx zy hzx hzy hEven
  -- transport along the coordinate permutation
  have hwperm :
      permuteWord (n := 24) σ (fun i : Fin 24 => (((zx i - zy i) / 2 : ℤ) : ZMod 2)) ∈
        Shell4IsometryLeechParityCode.leechParityCode := by
    have : permuteWord (n := 24) σ (fun i : Fin 24 => (((zx i - zy i) / 2 : ℤ) : ZMod 2)) ∈
        permuteCode (n := 24) σ (CodeFromLattice.codeFromLattice (C := Cset) hDn) :=
      ⟨_, hw, rfl⟩
    simpa [hσ] using! this
  simpa [Shell4IsometryLeechConstructionA.halfWord, permuteWord] using! hwperm

/-!
### Reducing the Pattern-III residue condition to a basepoint existence

The Pattern-III Leech membership proof in `Shell4IsometryLeechMembershipTypeIII.lean` is phrased
using the fixed odd Leech vector `rowInt last` (coordinates `(-3, 1, ..., 1)`).

For the shell-4 bridge, the only nontrivial "odd coset" input is that our lattice `latticeL Cset`
contains some vector whose `D₂₄`-frame integer coordinates (after permuting by `σ`) match that
specific row. Once such a basepoint exists, the required `halfWord (zσ - rowInt last)` membership
in `leechParityCode` follows formally from the extracted code definition.

This isolates where the "do not propagate assumptions" issue truly lives:
the only extra input is the existence of such a basepoint, together with the mod-8 sum constraint
derived from integrality.
-/

/-- Predicate asserting that `latticeL Cset` contains a basepoint whose permuted integer coordinates
match the fixed Leech row `rowInt last`. -/
@[expose] public def OddBasepointRowLast
    (Cset : Set ℝ²⁴)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn Cset 24)
    (σ : Equiv (Fin 24) (Fin 24)) : Prop :=
  ∃ y : ℝ²⁴,
    y ∈ (latticeL Cset : Set ℝ²⁴) ∧
      (∀ i : Fin 24,
        scaledCoord hDn.e i y =
          (rowLast (σ.symm i) : ℝ))

lemma odd_rowInt_last (k : Fin 24) :
    Odd (rowLast k) :=
  Shell4IsometryLeechConstructionA.odd_rowInt_last k

lemma odd_of_isPattern3_of_perm
    {z : Fin 24 → ℤ} {σ : Equiv (Fin 24) (Fin 24)} (hzσ : isPattern3 (fun i : Fin 24 => z (σ i)))
    (j : Fin 24) : Odd (z j) := by
  -- choose `i` with `σ i = j` and use the pattern-3 value classification
  have hvals := hzσ.2 (σ.symm j)
  rcases hvals with h1 | hN1 | h3 | hN3
  · have : z j = 1 := by simpa using! h1
    rw [this]; decide
  · have : z j = -1 := by simpa using! hN1
    rw [this]; decide
  · have : z j = 3 := by simpa using! h3
    rw [this]; decide
  · have : z j = -3 := by simpa using! hN3
    rw [this]; decide

lemma halfWord_zσ_sub_rowLast_mem_leechParityCode_of_basepoint
    (Cset : Set ℝ²⁴)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn Cset 24)
    (σ : Equiv (Fin 24) (Fin 24))
    (hσ :
      permuteCode (n := 24) σ (CodeFromLattice.codeFromLattice (C := Cset) hDn) =
        Shell4IsometryLeechParityCode.leechParityCode)
    (base : OddBasepointRowLast (Cset := Cset) hDn σ)
    {x : ℝ²⁴} (hx : x ∈ (latticeShell4 Cset))
    (zx : Fin 24 → ℤ)
    (hzx : ∀ i : Fin 24, scaledCoord hDn.e i x = (zx i : ℝ))
    (hxPat : isPattern3 (fun i : Fin 24 => zx (σ i))) :
    Shell4IsometryLeechConstructionA.halfWord
        ((fun i : Fin 24 => zx (σ i)) -
          rowLast) ∈
      Shell4IsometryLeechParityCode.leechParityCode := by
  rcases base with ⟨y, hyL, hyCoord⟩
  -- Apply the generic difference lemma with `x` and the chosen basepoint `y`.
  have hxL : x ∈ (latticeL Cset : Set ℝ²⁴) := hx.1
  -- coordinates for the basepoint `y`
  let zy : Fin 24 → ℤ :=
    fun i : Fin 24 => rowLast (σ.symm i)
  have hzy : ∀ i : Fin 24, scaledCoord hDn.e i y = (zy i : ℝ) := by
    intro i
    simpa [zy] using! hyCoord i
  -- evenness of the coordinate difference: both sides are odd
  have hEven : ∀ i : Fin 24, Even (zx i - zy i) := by
    intro i
    have hxOdd : Odd (zx i) := odd_of_isPattern3_of_perm (σ := σ) hxPat i
    have hyOdd : Odd (zy i) := by
      simpa [zy] using! odd_rowInt_last (σ.symm i)
    exact Odd.sub_odd hxOdd hyOdd
  -- invoke the reusable bridge lemma
  have hmem :=
    halfWord_sub_mem_leechParityCode_of_coords
      (Cset := Cset) (hDn := hDn) (σ := σ) (hσ := hσ)
      (x := x) (y := y) hxL hyL zx zy hzx hzy hEven
  -- rewrite the produced difference `zx(σ i) - zy(σ i)` as `zx(σ i) - rowInt last i`
  simpa [zy, Pi.sub_apply] using! hmem

/-!
### Using integrality to derive the mod-8 sum constraints

Once an odd basepoint with coordinates `rowInt last` exists inside `latticeL Cset`, integrality of
`latticeL Cset` turns inner-product integrality into divisibility of certain integer sums. For
Pattern II and the even difference in Pattern III, the special row `rowInt last` is congruent to
`1 (mod 4)` in every coordinate, so the weighted sum reduces to the plain coordinate sum
modulo `8`.
-/

lemma inner_eq_sum_coord_mul_coord
    (e : Fin 24 → ℝ²⁴) (he : Orthonormal ℝ e) (x y : ℝ²⁴) :
    (⟪x, y⟫ : ℝ) = ∑ i : Fin 24, (coord e i x) * (coord e i y) := by
  have hx :
      x = ∑ i : Fin 24, (coord e i x) • e i :=
    Uniqueness.BS81.Thm15.Lemma21.coord_eq_of_orthonormal e he x
  have hx' : (⟪x, y⟫ : ℝ) = ⟪∑ i : Fin 24, (coord e i x) • e i, y⟫ := by
    simpa using! congrArg (fun t : ℝ²⁴ => (⟪t, y⟫ : ℝ)) hx
  calc
    (⟪x, y⟫ : ℝ) = ⟪∑ i : Fin 24, (coord e i x) • e i, y⟫ := hx'
    _ = ∑ i : Fin 24, ⟪(coord e i x) • e i, y⟫ := by
          -- `inner_sum` is the linearity of `inner` in the left argument.
          exact sum_inner Finset.univ (fun i => coord e i x • e i) y
    _ = ∑ i : Fin 24, (coord e i x) * (coord e i y) := by
          simp [coord, real_inner_smul_left]

lemma eight_mul_inner_eq_sum_scaledCoord_mul_scaledCoord
    (e : Fin 24 → ℝ²⁴) (he : Orthonormal ℝ e) (x y : ℝ²⁴) :
    (8 : ℝ) * (⟪x, y⟫ : ℝ) = ∑ i : Fin 24, (scaledCoord e i x) * (scaledCoord e i y) := by
  have hinner : (⟪x, y⟫ : ℝ) = ∑ i : Fin 24, (coord e i x) * (coord e i y) :=
    inner_eq_sum_coord_mul_coord (e := e) he x y
  calc
    (8 : ℝ) * (⟪x, y⟫ : ℝ) = (8 : ℝ) * ∑ i : Fin 24, (coord e i x) * (coord e i y) := by
      simp [hinner]
    _ = ∑ i : Fin 24, (8 : ℝ) * ((coord e i x) * (coord e i y)) := by
      simpa using! (Finset.mul_sum (8 : ℝ) (s := (Finset.univ : Finset (Fin 24)))
        (f := fun i : Fin 24 => (coord e i x) * (coord e i y)))
    _ = ∑ i : Fin 24, (scaledCoord e i x) * (scaledCoord e i y) := by
      refine Finset.sum_congr rfl (fun i _hi => ?_)
      have hsqrt8_sq : (Real.sqrt 8 : ℝ) * (Real.sqrt 8 : ℝ) = (8 : ℝ) := by
        have h0 : (0 : ℝ) ≤ (8 : ℝ) := by norm_num
        exact Real.mul_self_sqrt h0
      -- `scaledCoord = √8 * coord`, so this is just regrouping factors.
      -- We keep the algebra explicit to avoid fragile `simp` traces.
      have hterm :
          (8 : ℝ) * ((coord e i x) * (coord e i y)) =
            ((Real.sqrt 8 : ℝ) * (coord e i x)) * ((Real.sqrt 8 : ℝ) * (coord e i y)) :=
        CancelDenoms.mul_subst rfl rfl hsqrt8_sq
      simpa [scaledCoord, mul_assoc, mul_left_comm, mul_comm] using! hterm

-- We keep the divisibility conversion local to `ContainsDn` coordinates.
lemma dvd8_sum_int_mul_of_basepoint
    (Cset : Set ℝ²⁴)
    (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg Cset)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn Cset 24)
    (σ : Equiv (Fin 24) (Fin 24))
    (base : OddBasepointRowLast (Cset := Cset) hDn σ)
    {u : ℝ²⁴} (hu : u ∈ (latticeL Cset : Set ℝ²⁴))
    (z : Fin 24 → ℤ) (hz : ∀ i : Fin 24, scaledCoord hDn.e i u = (z i : ℝ)) :
    (8 : ℤ) ∣ ∑ i : Fin 24,
      z i * rowLast (σ.symm i) := by
  rcases base with ⟨y, hyL, hyCoord⟩
  have hEq' : Uniqueness.BS81.EqCase24 Cset :=
    Uniqueness.BS81.Thm14.EqCase24Pkg.toEqCase24 (C := Cset) hEq
  rcases
      Uniqueness.BS81.inner_latticeL_int
        (C := Cset) hEq' (x := u) (y := y) hu hyL with
    ⟨m, hm⟩
  -- Convert integrality to a divisibility statement using the explicit coordinate formula.
  have h8 :
      (8 : ℝ) * (⟪u, y⟫ : ℝ) =
        ∑ i : Fin 24, (scaledCoord hDn.e i u) * (scaledCoord hDn.e i y) :=
    eight_mul_inner_eq_sum_scaledCoord_mul_scaledCoord (e := hDn.e) hDn.ortho u y
  have hcast :
      ((∑ i : Fin 24,
            z i * rowLast (σ.symm i) : ℤ) : ℝ) =
        ((8 * m : ℤ) : ℝ) := by
    -- rewrite the RHS with `hm` and the LHS using `hz` and `hyCoord`
    simp_all
  -- Deduce the integer divisibility.
  refine ⟨m, ?_⟩
  -- Convert the cast equality back to ℤ.
  exact_mod_cast hcast

lemma sum_rowInt_last_eq_twenty :
    (∑ k : Fin 24,
        rowLast k) = 20 := by
  decide

lemma dvd8_sum_mul_rowLastPulled_sub_sum_of_even
    (σ : Equiv (Fin 24) (Fin 24)) {a : Fin 24 → ℤ} (ha : ∀ i : Fin 24, Even (a i)) :
    (8 : ℤ) ∣
      (∑ i : Fin 24,
          a i * rowLast (σ.symm i)) -
        (∑ i : Fin 24, a i) := by
  have hrow :
      ∀ i : Fin 24,
        rowLast (σ.symm i) - 1 =
          if i = σ 0 then (-4 : ℤ) else 0 := by
    intro i
    by_cases hi : i = σ 0
    · subst hi
      simp [Shell4IsometryLeechConstructionA.row_last_apply]
    · have : σ.symm i ≠ 0 := by
        intro h0
        have : i = σ 0 := by
          simpa [Equiv.apply_symm_apply] using! congrArg σ h0
        exact hi this
      simp [Shell4IsometryLeechConstructionA.row_last_apply, this, hi]
  have :
      (∑ i : Fin 24,
            a i *
              rowLast (σ.symm i)) -
          (∑ i : Fin 24, a i) =
        ∑ i : Fin 24,
          a i *
            (rowLast (σ.symm i) - 1) := by
    simp [mul_sub, Finset.sum_sub_distrib]
  rw [this]
  have :
      (∑ i : Fin 24,
            a i *
              (rowLast (σ.symm i) - 1)) =
        a (σ 0) * (-4 : ℤ) := by
    have hterm :
        ∀ i : Fin 24,
          i ≠ σ 0 →
            a i *
              (rowLast (σ.symm i) - 1) =
              0 := by
      intro i hi
      simp [hrow i, hi]
    have hs :
        (∑ i : Fin 24,
              a i *
                (rowLast (σ.symm i) - 1)) =
          a (σ 0) *
            (rowLast (σ.symm (σ 0)) - 1) :=
      Fintype.sum_eq_single (σ 0) hterm
    simpa [Shell4IsometryLeechConstructionA.row_last_apply] using! hs
  rw [this]
  rcases ha (σ 0) with ⟨t, ht⟩
  refine ⟨-t, ?_⟩
  simp [ht]
  ring

lemma sum_dvd8_of_pattern1_of_basepoint
    (Cset : Set ℝ²⁴)
    (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg Cset)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn Cset 24)
    (σ : Equiv (Fin 24) (Fin 24))
    (base : OddBasepointRowLast (Cset := Cset) hDn σ)
    {u : ℝ²⁴} (hu : u ∈ latticeShell4 Cset)
    (z : Fin 24 → ℤ) (hz : ∀ i : Fin 24, scaledCoord hDn.e i u = (z i : ℝ))
    (hzσ : isPattern1 (fun i : Fin 24 => z (σ i))) :
    (8 : ℤ) ∣ ∑ i : Fin 24, z (σ i) := by
  -- From integrality against the basepoint we get `8 ∣ ∑ z_i * rowLast(σ⁻¹ i)`.
  have huL : u ∈ (latticeL Cset : Set ℝ²⁴) := hu.1
  have hdiv :
      (8 : ℤ) ∣ ∑ i : Fin 24,
        z i * rowLast (σ.symm i) :=
    dvd8_sum_int_mul_of_basepoint (Cset := Cset) (hEq := hEq) (hDn := hDn) (σ := σ) base huL z hz
  -- Rewrite the weighted sum as `∑ z i` modulo `8`.
  -- Only coordinate `σ 0` differs, by a multiple of `8`.
  have hzEven : ∀ i : Fin 24, Even (z i) := by
    intro i
    rcases hzσ.2 (σ.symm i) with h0 | h2 | hN2
    · have : z i = 0 := by simpa using! h0
      simp [this]
    · have : z i = 2 := by simpa using! h2
      simp [this]
    · have : z i = -2 := by simpa using! hN2
      simp [this]
  have hdiff :
      (8 : ℤ) ∣
        (∑ i : Fin 24,
            z i * rowLast (σ.symm i)) -
          (∑ i : Fin 24, z i) := by
    simpa using! dvd8_sum_mul_rowLastPulled_sub_sum_of_even (σ := σ) (a := z) hzEven
  -- Now deduce `8 ∣ ∑ z i`.
  rcases hdiv with ⟨t, ht⟩
  rcases hdiff with ⟨s, hs⟩
  refine ⟨t - s, ?_⟩
  -- `(∑ z_i) = (∑ z_i*rowLast) - ((∑ z_i*rowLast) - (∑ z_i))`
  have :
      (∑ i : Fin 24, z i) =
        (∑ i : Fin 24,
            z i * rowLast (σ.symm i)) -
          ((∑ i : Fin 24,
              z i * rowLast (σ.symm i)) -
            (∑ i : Fin 24, z i)) := by ring
  -- finish by rewriting both divisible terms
  calc
    (∑ i : Fin 24, z (σ i)) = ∑ i : Fin 24, z i := by
      -- permutation invariance of the sum
      simpa using! (Equiv.sum_comp σ (fun i : Fin 24 => z i))
    _ = 8 * (t - s) := by
      -- use the decomposition and `ht`, `hs`
      have h1 : (∑ i : Fin 24,
          z i * rowLast (σ.symm i)) = 8 * t := ht
      have h2 :
          (∑ i : Fin 24,
              z i * rowLast (σ.symm i)) -
            (∑ i : Fin 24, z i) = 8 * s := hs
      -- solve for `∑ z i`
      -- `A - (A - B) = B`
      calc
        (∑ i : Fin 24, z i)
            = (∑ i : Fin 24,
                z i * rowLast (σ.symm i)) -
              ((∑ i : Fin 24,
                  z i * rowLast (σ.symm i)) -
                (∑ i : Fin 24, z i)) := this
        _ = 8 * t - 8 * s := by
              -- rewrite the inner `(A - B)` term before rewriting `A` itself
              rw [h2, h1]
        _ = 8 * (t - s) := by ring

lemma sum_dvd8_sub_rowLast_of_pattern3_of_basepoint
    (Cset : Set ℝ²⁴)
    (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg Cset)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn Cset 24)
    (σ : Equiv (Fin 24) (Fin 24))
    (base : OddBasepointRowLast (Cset := Cset) hDn σ)
    {u : ℝ²⁴} (hu : u ∈ latticeShell4 Cset)
    (z : Fin 24 → ℤ) (hz : ∀ i : Fin 24, scaledCoord hDn.e i u = (z i : ℝ))
    (hzσ : isPattern3 (fun i : Fin 24 => z (σ i))) :
    (8 : ℤ) ∣
      ∑ i : Fin 24,
        ((fun i : Fin 24 => z (σ i)) -
            rowLast) i := by
  -- Work with the unpermuted difference `d i = z i - rowLast(σ⁻¹ i)`.
  rcases base with ⟨y, hyL, hyCoord⟩
  have huL : u ∈ (latticeL Cset : Set ℝ²⁴) := hu.1
  let zy : Fin 24 → ℤ :=
    fun i : Fin 24 => rowLast (σ.symm i)
  have hzy : ∀ i : Fin 24, scaledCoord hDn.e i y = (zy i : ℝ) := by
    intro i
    simpa [zy] using! hyCoord i
  have hEven : ∀ i : Fin 24, Even (z i - zy i) := by
    intro i
    have hzOdd : Odd (z i) := odd_of_isPattern3_of_perm (σ := σ) hzσ i
    have hyOdd : Odd (zy i) := by simpa [zy] using! odd_rowInt_last (σ.symm i)
    exact Odd.sub_odd hzOdd hyOdd
  -- Use integrality of `⟪u - y, y⟫` to get `8 ∣ ∑ (z-zy)*zy`.
  have hEq' : Uniqueness.BS81.EqCase24 Cset :=
    Uniqueness.BS81.Thm14.EqCase24Pkg.toEqCase24 (C := Cset) hEq
  have hxL : u - y ∈ (latticeL Cset : Set ℝ²⁴) := (latticeL Cset).sub_mem huL hyL
  rcases
      Uniqueness.BS81.inner_latticeL_int
        (C := Cset) hEq' (x := u - y) (y := y) hxL hyL with
    ⟨m, hm⟩
  have h8 :
      (8 : ℝ) * (⟪u - y, y⟫ : ℝ) =
        ∑ i : Fin 24, (scaledCoord hDn.e i (u - y)) * (scaledCoord hDn.e i y) :=
    eight_mul_inner_eq_sum_scaledCoord_mul_scaledCoord (e := hDn.e) hDn.ortho (u - y) y
  have hcast :
      ((∑ i : Fin 24, (z i - zy i) * zy i : ℤ) : ℝ) = ((8 * m : ℤ) : ℝ) := by
    have hsub : ∀ i : Fin 24, scaledCoord hDn.e i (u - y) = (z i - zy i : ℝ) := by
      intro i
      calc
        scaledCoord hDn.e i (u - y) = scaledCoord hDn.e i u - scaledCoord hDn.e i y := by
          simp [scaledCoord, coord, inner_sub_right, mul_sub]
        _ = (z i : ℝ) - (zy i : ℝ) := by simp [hz i, hzy i]
        _ = (z i - zy i : ℝ) := by simp
    calc
      ((∑ i : Fin 24, (z i - zy i) * zy i : ℤ) : ℝ) =
          ∑ i : Fin 24, (scaledCoord hDn.e i (u - y)) * (scaledCoord hDn.e i y) := by
            simp [hsub, hzy, zy, Int.cast_sum, Int.cast_mul]
      _ = (8 : ℝ) * (⟪u - y, y⟫ : ℝ) := h8.symm
      _ = (8 : ℝ) * (m : ℝ) := by simp [hm]
      _ = ((8 * m : ℤ) : ℝ) := by norm_cast
  have hdiv : (8 : ℤ) ∣ ∑ i : Fin 24, (z i - zy i) * zy i := by
    refine ⟨m, ?_⟩
    exact_mod_cast hcast
  -- Reduce the weighted sum to the plain sum using `Even (z-zy)`.
  have hdiff :
      (8 : ℤ) ∣ (∑ i : Fin 24, (z i - zy i) * zy i) - (∑ i : Fin 24, (z i - zy i)) := by
    -- same reasoning as Pattern II, with `a := z - zy`.
    simpa [zy] using!
      dvd8_sum_mul_rowLastPulled_sub_sum_of_even (σ := σ) (a := fun i => z i - zy i) hEven
  -- Conclude `8 ∣ ∑ (z-zy)` and translate to the permuted `zσ - rowLast` sum.
  let A : ℤ := ∑ i : Fin 24, (z i - zy i) * zy i
  let B : ℤ := ∑ i : Fin 24, (z i - zy i)
  rcases hdiv with ⟨a, ha⟩
  rcases hdiff with ⟨b, hb⟩
  refine ⟨a - b, ?_⟩
  calc
    (∑ i : Fin 24,
        ((fun i : Fin 24 => z (σ i)) -
            rowLast) i) = B := by
            -- rewrite the permuted `rowInt last` as `zy (σ i)`, then use permutation invariance
            calc
              (∑ i : Fin 24,
                  (z (σ i) -
                    rowLast i)) =
                  ∑ i : Fin 24, (z (σ i) - zy (σ i)) := by
                    refine Finset.sum_congr rfl (fun i _hi => ?_)
                    simp [zy, Equiv.symm_apply_apply]
              _ = B := by
                    simpa [B] using! (Equiv.sum_comp σ (fun i : Fin 24 => z i - zy i))
    _ = 8 * (a - b) := by
      -- solve for the plain sum from the two divisible relations
      have hA : A = 8 * a := by simpa [A] using! ha
      have hAB : A - B = 8 * b := by simpa [A, B] using! hb
      calc
        B = A - (A - B) := by ring
        _ = 8 * a - 8 * b := by rw [hAB, hA]
        _ = 8 * (a - b) := by ring

lemma leechShell4_eq_leechKissingVectors :
    leechShell4 = Uniqueness.RigidityClassify.CE.leechKissingVectors := by
  ext v
  constructor
  · rintro ⟨hvL, hvSq⟩
    refine ⟨hvL, ?_⟩
    have : ‖v‖ = (2 : ℝ) := by
      have hsqrt : Real.sqrt (‖v‖ ^ 2) = Real.sqrt (4 : ℝ) := congrArg Real.sqrt hvSq
      have hvNorm' : ‖v‖ = Real.sqrt (4 : ℝ) := by
        simpa [Real.sqrt_sq (norm_nonneg v)] using! hsqrt
      have hsqrt4 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
        have hpow : ((2 : ℝ) ^ 2) = (4 : ℝ) := by norm_num1
        simpa [hpow] using! (Real.sqrt_sq_eq_abs (2 : ℝ))
      simpa [hsqrt4] using! hvNorm'
    simpa using! this
  · rintro ⟨hvL, hvNorm⟩
    refine ⟨hvL, ?_⟩
    nlinarith [hvNorm]

open scoped Classical in
section

/-- The Leech norm-`4` shell `leechShell4` has cardinality `196560`. -/
public theorem ncard_leechShell4 :
    Set.ncard leechShell4 = 196560 := by
  simpa [leechShell4_eq_leechKissingVectors] using!
    (Uniqueness.BS81.Thm15.Lemma21.ncard_leechKissingVectors)

/-- In the equality case, the shell `latticeShell4 C` has cardinality `196560`. -/
public theorem ncard_latticeShell4_eq_196560
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C) :
    Set.ncard (latticeShell4 C) = 196560 := by
  have hshell : latticeShell4 C = twoCodeVectors C :=
    Uniqueness.BS81.Thm15.Lemma17.shell4_eq_twoCodeVectors (C := C) h
  have hncard_two : Set.ncard (twoCodeVectors C) = 196560 := by
    calc
      Set.ncard (twoCodeVectors C) = Set.ncard C :=
        Uniqueness.BS81.ncard_twoCodeVectors_eq C
      _ = 196560 := h.card_eq
  simpa [hshell] using! hncard_two

end

lemma top_le_span_of_orthonormal_fin24 (e : Fin 24 → ℝ²⁴) (he : Orthonormal ℝ e) :
    (⊤ : Submodule ℝ ℝ²⁴) ≤ Submodule.span ℝ (Set.range e) := by
  have hlin : LinearIndependent ℝ e := Orthonormal.linearIndependent he
  have hspanEq : Submodule.span ℝ (Set.range e) = (⊤ : Submodule ℝ ℝ²⁴) := by
    apply Submodule.eq_top_of_finrank_eq
    simpa [EuclideanSpace, Fintype.card_fin] using!
      (finrank_span_eq_card (R := ℝ) (M := ℝ²⁴) (b := e) hlin)
  simp [hspanEq]

noncomputable def orthonormalBasis_of_containsDn
    (C : Set ℝ²⁴) (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24) :
    OrthonormalBasis (Fin 24) ℝ ℝ²⁴ :=
  OrthonormalBasis.mk hDn.ortho
    (top_le_span_of_orthonormal_fin24 (e := hDn.e) hDn.ortho)

/-- The ambient linear isometry used for coordinate alignment: send the `D₂₄` frame to the
standard basis, then permute coordinates by `σ` (in the `permuteWord` convention). -/
public def shell4Isometry
    (C : Set ℝ²⁴)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24)
    (σ : Equiv (Fin 24) (Fin 24)) :
    ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴ :=
  let b : OrthonormalBasis (Fin 24) ℝ ℝ²⁴ := orthonormalBasis_of_containsDn (C := C) hDn
  let std : OrthonormalBasis (Fin 24) ℝ ℝ²⁴ := EuclideanSpace.basisFun (Fin 24) ℝ
  let eFrame : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴ := b.equiv std (Equiv.refl (Fin 24))
  let ePerm : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴ := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ.symm
  eFrame.trans ePerm

/-- Under the code alignment hypothesis `hσ`, the constructed ambient isometry sends the shell-4
set into the Leech shell-4 set. -/
public theorem image_shell4_subset_leechShell4_of_code_equiv
    (Cset : Set ℝ²⁴)
    (hEq : Uniqueness.BS81.Thm14.EqCase24Pkg Cset)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn Cset 24)
    (σ : Equiv (Fin 24) (Fin 24))
    (hσ :
      permuteCode (n := 24) σ (CodeFromLattice.codeFromLattice (C := Cset) hDn) =
        Shell4IsometryLeechParityCode.leechParityCode)
    (base : OddBasepointRowLast (Cset := Cset) hDn σ) :
    shell4Isometry (C := Cset) hDn σ '' (latticeShell4 Cset) ⊆ leechShell4 := by
  intro v hv
  rcases hv with ⟨u, hu, rfl⟩
  refine ⟨?_, ?_⟩
  · -- Membership in the Leech lattice, via the integer-coordinate pattern classification.
    rcases
        shell4_patterns (C := Cset) (hEq := hEq) (hDn := hDn) (u := u) hu with
      ⟨z, hz, _, _, hpat⟩
    -- Let `std` denote the standard orthonormal basis.
    let std : OrthonormalBasis (Fin 24) ℝ ℝ²⁴ := EuclideanSpace.basisFun (Fin 24) ℝ
    -- The `shell4Isometry` is `eFrame.trans ePerm`; extract them to compute coordinates.
    let b : OrthonormalBasis (Fin 24) ℝ ℝ²⁴ := orthonormalBasis_of_containsDn (C := Cset) hDn
    let eFrame : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴ := b.equiv std (Equiv.refl (Fin 24))
    let ePerm : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴ := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ.symm
    -- Coordinates after `eFrame` agree with the original `D₂₄`-frame coordinates.
    have hcoord_frame :
        ∀ i : Fin 24, coord (fun j => std j) i (eFrame u) = coord hDn.e i u := by
      intro i
      have hbasis : eFrame (b i) = std i := by
        -- `simp` knows how `OrthonormalBasis.equiv` acts on the basis.
        simp [eFrame]  -- discharges the goal via `OrthonormalBasis.equiv_apply_basis`
      -- Unfold `b` to identify `b i` with `hDn.e i`.
      have hb : (b i : ℝ²⁴) = hDn.e i := by
        simp [b, orthonormalBasis_of_containsDn, OrthonormalBasis.coe_mk]
      -- Assemble: `eFrame` sends the `D₂₄` frame to the standard basis.
      have hinner : (⟪std i, eFrame u⟫ : ℝ) = (⟪hDn.e i, u⟫ : ℝ) := by
        calc
          (⟪std i, eFrame u⟫ : ℝ) = ⟪eFrame (b i), eFrame u⟫ := by simp [hbasis]
          _ = ⟪b i, u⟫ := by simp
          _ = ⟪hDn.e i, u⟫ := by simp [hb]
      simpa [coord] using! hinner
    -- Therefore the scaled coordinates after `eFrame` are the integers `z i`.
    have hscaled_frame : ∀ i : Fin 24, scaledCoord (fun j => std j) i (eFrame u) = (z i : ℝ) := by
      intro i
      have : scaledCoord (fun j => std j) i (eFrame u) = scaledCoord hDn.e i u := by
        -- `scaledCoord` is `√8` times `coord`.
        simpa [scaledCoord] using!
          congrArg (fun t : ℝ => (Real.sqrt 8) * t) (hcoord_frame i)
      exact this.trans (hz i)
    -- `ePerm` permutes standard coordinates by `σ`.
    have hscaled_perm :
        ∀ i : Fin 24, scaledCoord (fun j => std j) i (ePerm (eFrame u)) = (z (σ i) : ℝ) := by
      intro i
      have :
          scaledCoord (fun j => std j) i (ePerm (eFrame u)) =
            scaledCoord (fun j => std j) (σ i) (eFrame u) := by
        -- `piLpCongrLeft` acts by precomposition by `σ`.
        -- `coord` in the standard basis is evaluation.
        have hcoord :
            coord (fun j => std j) i (ePerm (eFrame u)) =
              coord (fun j => std j) (σ i) (eFrame u) := by
          -- Reduce to an inner-product identity using `basisFun_inner`.
          have hinner :
              (⟪std i, ePerm (eFrame u)⟫ : ℝ) = (⟪std (σ i), eFrame u⟫ : ℝ) := by
            calc
              (⟪std i, ePerm (eFrame u)⟫ : ℝ) = (ePerm (eFrame u)) i := by
                simpa [std] using! (EuclideanSpace.basisFun_inner (ι := Fin 24) (𝕜 := ℝ)
                  (x := ePerm (eFrame u)) i)
              _ = (eFrame u) (σ i) := by
                simp [ePerm, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
              _ = (⟪std (σ i), eFrame u⟫ : ℝ) := by
                simpa [std] using!
                  (EuclideanSpace.basisFun_inner (ι := Fin 24) (𝕜 := ℝ) (x := eFrame u) (σ i)).symm
          simpa [coord] using! hinner
        simp [scaledCoord, hcoord]
      exact (this.trans (hscaled_frame (σ i)))
    -- At this point, `shell4Isometry u = ePerm (eFrame u)` has standard scaled coordinates
    -- `z (σ i)`.
    have hscaled_image :
        ∀ i : Fin 24,
          scaledCoord (fun j => std j) i (shell4Isometry (C := Cset) hDn σ u) = (z (σ i) : ℝ) := by
      assumption
    -- Reduce to the standard-coordinate vector `z ∘ σ`.
    let zσ : Fin 24 → ℤ := fun i => z (σ i)
    have halfWord_zσ_mem_leechParityCode_of_pattern1 (hzσ : isPattern1 zσ) :
        Shell4IsometryLeechConstructionA.halfWord zσ ∈
          Shell4IsometryLeechParityCode.leechParityCode := by
      -- `zσ` being Pattern I implies all coordinates of `z` are even.
      have hzEven : ∀ i : Fin 24, Even (z i) := by
        intro i
        -- pull back to `σ.symm i` and use `isPattern1 zσ`
        rcases hzσ.2 (σ.symm i) with h0 | h2 | hN2
        · have : z i = 0 := by
            simpa [zσ] using! h0
          simp [this]
        · have : z i = 2 := by
            simpa [zσ] using! h2
          simp [this]
        · have : z i = -2 := by
            simpa [zσ] using! hN2
          simp [this]
      -- Build the extracted codeword from `u` and its integer coordinates `z`.
      let w : BinWord 24 := fun i : Fin 24 => ((z i / 2 : ℤ) : ZMod 2)
      have hw : w ∈ CodeFromLattice.codeFromLattice (C := Cset) hDn := by
        refine ⟨u, hu.1, z, hz, hzEven, ?_⟩
        intro i
        rfl
      have hwperm :
          permuteWord (n := 24) σ w ∈ Shell4IsometryLeechParityCode.leechParityCode := by
        have : permuteWord (n := 24) σ w ∈
            permuteCode (n := 24) σ (CodeFromLattice.codeFromLattice (C := Cset) hDn) := by
          exact ⟨w, hw, rfl⟩
        simpa [hσ] using! this
      assumption
    -- The `isPattern` disjunction is preserved under permutation.
    have hpatσ : isPattern1 zσ ∨ isPattern2 zσ ∨ isPattern3 zσ := by
      have hzeros_eq_card :
          Fintype.card {i : Fin 24 // z (σ i) = 0} = Fintype.card {i : Fin 24 // z i = 0} := by
        let e :
            {i : Fin 24 // z (σ i) = 0} ≃ {i : Fin 24 // z i = 0} :=
          { toFun := fun i => ⟨σ i.1, i.2⟩
            invFun := fun j => ⟨σ.symm j.1, by simpa using! j.2⟩
            left_inv := by intro i; ext; simp
            right_inv := by intro j; ext; simp }
        simpa using! Fintype.card_congr e
      have hthree_eq_card :
          Fintype.card {i : Fin 24 // z (σ i) = 3 ∨ z (σ i) = -3} =
            Fintype.card {i : Fin 24 // z i = 3 ∨ z i = -3} := by
        let e :
            {i : Fin 24 // z (σ i) = 3 ∨ z (σ i) = -3} ≃
              {i : Fin 24 // z i = 3 ∨ z i = -3} :=
          { toFun := fun i => ⟨σ i.1, i.2⟩
            invFun := fun j => ⟨σ.symm j.1, by simpa using! j.2⟩
            left_inv := by intro i; ext; simp
            right_inv := by intro j; ext; simp }
        simpa using! Fintype.card_congr e
      rcases hpat with h1 | h2 | h3
      · left
        refine ⟨?_, ?_⟩
        · have h1' := h1.1
          -- rewrite `#{i | z i = 0}` into `Fintype.card {i // z i = 0}`
          rw [← Fintype.card_subtype (α := Fin 24) (p := fun i : Fin 24 => z i = 0)] at h1'
          -- rewrite the goal `#{i | zσ i = 0}` into `Fintype.card {i // zσ i = 0}`
          rw [← Fintype.card_subtype (α := Fin 24) (p := fun i : Fin 24 => zσ i = 0)]
          have :
              Fintype.card {i : Fin 24 // zσ i = 0} = 16 := by
            have :
                Fintype.card {i : Fin 24 // z (σ i) = 0} = 16 := by
              calc
                Fintype.card {i : Fin 24 // z (σ i) = 0} =
                    Fintype.card {i : Fin 24 // z i = 0} := hzeros_eq_card
                _ = 16 := h1'
            simpa [zσ] using! this
          simpa using! this
        · intro i
          simpa [zσ] using! h1.2 (σ i)
      · right; left
        refine ⟨?_, ?_⟩
        · have h2' := h2.1
          rw [← Fintype.card_subtype (α := Fin 24) (p := fun i : Fin 24 => z i = 0)] at h2'
          rw [← Fintype.card_subtype (α := Fin 24) (p := fun i : Fin 24 => zσ i = 0)]
          have :
              Fintype.card {i : Fin 24 // zσ i = 0} = 22 := by
            have :
                Fintype.card {i : Fin 24 // z (σ i) = 0} = 22 := by
              calc
                Fintype.card {i : Fin 24 // z (σ i) = 0} =
                    Fintype.card {i : Fin 24 // z i = 0} := hzeros_eq_card
                _ = 22 := h2'
            simpa [zσ] using! this
          simpa using! this
        · intro i
          simpa [zσ] using! h2.2 (σ i)
      · right; right
        refine ⟨?_, ?_⟩
        · have h3' := h3.1
          rw [← Fintype.card_subtype (α := Fin 24)
            (p := fun i : Fin 24 => z i = 3 ∨ z i = -3)] at h3'
          rw [← Fintype.card_subtype (α := Fin 24)
            (p := fun i : Fin 24 => zσ i = 3 ∨ zσ i = -3)]
          have :
              Fintype.card {i : Fin 24 // zσ i = 3 ∨ zσ i = -3} = 1 := by
            have :
                Fintype.card {i : Fin 24 // z (σ i) = 3 ∨ z (σ i) = -3} = 1 := by
              calc
                Fintype.card {i : Fin 24 // z (σ i) = 3 ∨ z (σ i) = -3} =
                    Fintype.card {i : Fin 24 // z i = 3 ∨ z i = -3} := hthree_eq_card
                _ = 1 := h3'
            simpa [zσ] using! this
          simpa using! this
        · intro i
          simpa [zσ] using! h3.2 (σ i)
    -- The image vector is uniquely determined by its `scaledCoord` values in the standard basis.
    have hv_eq :
        shell4Isometry (C := Cset) hDn σ u =
          Shell4IsometryLeechMembership.vecOfScaledStd zσ := by
      -- Expand both vectors in the standard orthonormal basis.
      apply (eq_of_scaledCoord_eq (e := fun j => (std j)) std.orthonormal)
      intro i
      -- LHS: by coordinate computation above.
      have hlhs := hscaled_image i
      -- RHS: by definition of `vecOfScaledStd`.
      have hrhs :
          scaledCoord (fun j => std j) i (Shell4IsometryLeechMembership.vecOfScaledStd zσ) =
            (zσ i : ℝ) := by
        simpa [std] using! (Shell4IsometryLeechMembership.scaledCoord_std_vecOfScaledStd zσ i)
      simpa [zσ] using! (hlhs.trans hrhs.symm)
    -- Conclude Leech lattice membership from the Construction-A (pattern) membership lemma.
    have hvL :
        Shell4IsometryLeechMembership.vecOfScaledStd zσ ∈ (LeechLattice : Set ℝ²⁴) :=
      mem_leechLattice_of_pattern (z := zσ) (hpat := hpatσ)
        (hII := by
          intro hzσ
          refine ⟨halfWord_zσ_mem_leechParityCode_of_pattern1 hzσ, ?_⟩
          exact sum_dvd8_of_pattern1_of_basepoint Cset hEq hDn σ base hu z hz hzσ)
        (hIII := by
          intro hzσ
          refine ⟨?_, ?_⟩
          · exact
              halfWord_zσ_sub_rowLast_mem_leechParityCode_of_basepoint
                (Cset := Cset) (hDn := hDn) (σ := σ) (hσ := hσ) (base := base)
                (hx := hu) (zx := z) (hzx := hz) hzσ
          · -- rewrite `zσ` back to `(fun i => z (σ i))` to match the lemma statement
            simpa [zσ, Pi.sub_apply] using!
              (sum_dvd8_sub_rowLast_of_pattern3_of_basepoint
                (Cset := Cset) (hEq := hEq) (hDn := hDn) (σ := σ) (base := base)
                (hu := hu) (z := z) (hz := hz) hzσ))
    simpa [hv_eq] using! hvL
  · -- Norm is preserved by the linear isometry.
    have hn : ‖shell4Isometry (C := Cset) hDn σ u‖ = ‖u‖ :=
      (shell4Isometry (C := Cset) hDn σ).norm_map u
    have hn2 : ‖shell4Isometry (C := Cset) hDn σ u‖ ^ 2 = ‖u‖ ^ 2 :=
      congrArg (fun t : ℝ => t ^ 2) hn
    simpa using! hn2.trans hu.2

end Shell4IsometryAux

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
