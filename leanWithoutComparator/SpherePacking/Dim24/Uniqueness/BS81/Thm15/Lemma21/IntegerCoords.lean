-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LatticeL
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Package
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Coordinates
public import Mathlib.Algebra.Group.Int.Even
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma17.InnerProducts
import SpherePacking.Dim24.Uniqueness.BS81.LatticeLIntegral

/-!
# Integer scaled coordinates on `latticeShell4`

For the `D₂₄` frame `e` coming from Lemma 20, BS81 study the `√8`-scaled coordinates
`scaledCoord e i u = √8 * ⟪e i, u⟫` of vectors `u ∈ latticeShell4 C`.

Using integrality of inner products with the vectors `√2 (e i ± e j)`, we show these scaled
coordinates are integers and satisfy a uniform parity condition.

## Main definitions
* `scaledCoord`
* `jOf`

## Main statements
* `exists_integer_coords_of_shell4`
* `sum_sq_integer_coords_eq_32`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21

noncomputable section

open scoped RealInnerProductSpace Pointwise

open Set

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- The `√8`-scaled coordinate `√8 * ⟪e i, x⟫` of `x` in the frame `e`. -/
@[expose] public def scaledCoord (e : Fin 24 → ℝ²⁴) (i : Fin 24) (x : ℝ²⁴) : ℝ :=
  (Real.sqrt 8) * coord e i x

/-! ### A deterministic choice of a distinct index -/

/-- A deterministic index distinct from `i` (used to avoid choice in several shell-to-lattice
steps). -/
@[expose] public def jOf (i : Fin 24) : Fin 24 :=
  if i = 0 then 1 else 0

/-- The index `jOf i` is always distinct from `i`. -/
public lemma i_ne_jOf (i : Fin 24) : i ≠ jOf i := by
  by_cases hi : i = 0
  · subst hi
    simp [jOf]
  · have : jOf i = 0 := by simp [jOf, hi]
    exact Ne.trans_eq hi (id (Eq.symm this))

private lemma scaledCoord_eq_inner_smul
    (e : Fin 24 → ℝ²⁴) (i : Fin 24) (x : ℝ²⁴) :
    scaledCoord e i x = (⟪(Real.sqrt 8 : ℝ) • e i, x⟫ : ℝ) := by
  simp [scaledCoord, coord, real_inner_smul_left]

/-- A convenient normalization: `Real.sqrt 8 = 2 * Real.sqrt 2`. -/
public lemma sqrt8_eq_two_mul_sqrt2 : (Real.sqrt 8 : ℝ) = (2 : ℝ) * Real.sqrt 2 := by
  have h8 : (4 : ℝ) * 2 = 8 := by norm_num
  have hx4 : (0 : ℝ) ≤ 4 := by norm_num
  have hsqrt4 : (Real.sqrt 4 : ℝ) = 2 := by
    have hx : (0 : ℝ) ≤ 4 := by norm_num
    have hy : (0 : ℝ) ≤ 2 := by norm_num
    exact (Real.sqrt_eq_iff_mul_self_eq hx hy).2 (by norm_num)
  calc
    (Real.sqrt 8 : ℝ) = Real.sqrt ((4 : ℝ) * 2) :=
      (congrArg Real.sqrt h8).symm
    _ = (Real.sqrt 4 : ℝ) * Real.sqrt 2 :=
      Real.sqrt_mul hx4 (2 : ℝ)
    _ = (2 : ℝ) * Real.sqrt 2 := by simp [hsqrt4]

/-- The sum of the two `√2` inner products with `e i ± e j` recovers the `√8` coordinate. -/
public lemma inner_sqrt2_add_sub_eq_sqrt8 (e : Fin 24 → ℝ²⁴) (i j : Fin 24) (x : ℝ²⁴) :
    (⟪(Real.sqrt 2) • (e i + e j), x⟫ : ℝ) +
        (⟪(Real.sqrt 2) • (e i - e j), x⟫ : ℝ) =
      (Real.sqrt 8 : ℝ) * (⟪e i, x⟫ : ℝ) := by
  have :
      (⟪(Real.sqrt 2) • (e i + e j), x⟫ : ℝ) +
          (⟪(Real.sqrt 2) • (e i - e j), x⟫ : ℝ) =
        ((2 : ℝ) * Real.sqrt 2) * (⟪e i, x⟫ : ℝ) := by
    simp [real_inner_smul_left, inner_add_left, inner_sub_left, mul_sub]
    ring
  simpa [sqrt8_eq_two_mul_sqrt2, mul_assoc, mul_left_comm, mul_comm] using! this

/-- Express `scaledCoord` as a sum of two `√2` inner products. -/
public lemma scaledCoord_eq_inner_sqrt2_add_sub (e : Fin 24 → ℝ²⁴) (i j : Fin 24) (x : ℝ²⁴) :
    scaledCoord e i x =
      (⟪(Real.sqrt 2) • (e i + e j), x⟫ : ℝ) +
        (⟪(Real.sqrt 2) • (e i - e j), x⟫ : ℝ) := by
  simpa [scaledCoord, coord] using!
    (inner_sqrt2_add_sub_eq_sqrt8 (e := e) (i := i) (j := j) (x := x)).symm

/-- If the two `√2` inner products are integers, then `scaledCoord` is their integer sum. -/
public lemma scaledCoord_eq_int_add_of_inner_sqrt2_add_sub
    (e : Fin 24 → ℝ²⁴) (i j : Fin 24) (x : ℝ²⁴) (mplus mminus : ℤ)
    (hmplus : (⟪(Real.sqrt 2) • (e i + e j), x⟫ : ℝ) = (mplus : ℝ))
    (hmminus : (⟪(Real.sqrt 2) • (e i - e j), x⟫ : ℝ) = (mminus : ℝ)) :
    scaledCoord e i x = ((mplus + mminus : ℤ) : ℝ) := by
  rw [scaledCoord_eq_inner_sqrt2_add_sub (e := e) (i := i) (j := j) (x := x), hmplus, hmminus]
  simp [Int.cast_add]

/-- Parity: integer scaled coordinates satisfy `Even (z i + z j)` once the relevant inner products
are integral. -/
public lemma even_z_add_z_of_scaledCoord_eq_int
    (e : Fin 24 → ℝ²⁴) (x : ℝ²⁴) (z : Fin 24 → ℤ)
    (hzCoord : ∀ i : Fin 24, scaledCoord e i x = (z i : ℝ))
    (hinner : ∀ i j : Fin 24, i ≠ j → ∃ m : ℤ,
      (⟪(Real.sqrt 2) • (e i + e j), x⟫ : ℝ) = (m : ℝ)) :
    ∀ i j : Fin 24, Even (z i + z j) := by
  intro i j
  by_cases hij : i = j
  · subst hij
    exact ⟨z i, by simp⟩
  · rcases hinner i j hij with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hsumCoord :
        scaledCoord e i x + scaledCoord e j x =
          (2 : ℝ) * (⟪(Real.sqrt 2) • (e i + e j), x⟫ : ℝ) := by
      simp [scaledCoord, coord, sqrt8_eq_two_mul_sqrt2, real_inner_smul_left, inner_add_left,
        mul_add, mul_assoc]
    have hcast :
        ((z i + z j : ℤ) : ℝ) = ((m + m : ℤ) : ℝ) := by
      calc
        ((z i + z j : ℤ) : ℝ) = (z i : ℝ) + (z j : ℝ) := by simp
        _ = scaledCoord e i x + scaledCoord e j x := by
          simp [hzCoord i, hzCoord j]
        _ = (2 : ℝ) * (⟪(Real.sqrt 2) • (e i + e j), x⟫ : ℝ) := hsumCoord
        _ = (2 : ℝ) * (m : ℝ) := by
          simpa using! congrArg (fun t : ℝ => (2 : ℝ) * t) hm
        _ = ((m + m : ℤ) : ℝ) := by
          simp [two_mul]
    exact_mod_cast hcast

private lemma sqrt8_smul_basis_mem_latticeL_of_minVec
    (C : Set ℝ²⁴) (e : Fin 24 → ℝ²⁴)
    (hmin : ∀ (i j : Fin 24), i ≠ j →
      (Real.sqrt 2 • (e i + e j)) ∈ latticeShell4 C ∧
        (Real.sqrt 2 • (e i - e j)) ∈ latticeShell4 C) :
    ∀ i : Fin 24, (Real.sqrt 8 : ℝ) • e i ∈ (latticeL C : Set ℝ²⁴) := by
  have hsqrt8 : (Real.sqrt 8 : ℝ) = (2 : ℝ) * Real.sqrt 2 := sqrt8_eq_two_mul_sqrt2
  intro i
  have hplusShell : (Real.sqrt 2 • (e i + e (jOf i))) ∈ latticeShell4 C :=
    (hmin i (jOf i) (i_ne_jOf i)).1
  have hminusShell : (Real.sqrt 2 • (e i - e (jOf i))) ∈ latticeShell4 C :=
    (hmin i (jOf i) (i_ne_jOf i)).2
  have hplusL : (Real.sqrt 2 • (e i + e (jOf i))) ∈ (latticeL C : Set ℝ²⁴) :=
    hplusShell.1
  have hminusL : (Real.sqrt 2 • (e i - e (jOf i))) ∈ (latticeL C : Set ℝ²⁴) :=
    hminusShell.1
  have hsum :
      (Real.sqrt 2 • (e i + e (jOf i))) + (Real.sqrt 2 • (e i - e (jOf i))) =
        ((2 : ℝ) * Real.sqrt 2) • e i := by
    calc
      (Real.sqrt 2 • (e i + e (jOf i))) + (Real.sqrt 2 • (e i - e (jOf i))) =
          (Real.sqrt 2 : ℝ) • ((e i + e (jOf i)) + (e i - e (jOf i))) := by
            simpa using!
              (smul_add (Real.sqrt 2 : ℝ) (e i + e (jOf i)) (e i - e (jOf i))).symm
      _ = (Real.sqrt 2 : ℝ) • ((2 : ℝ) • e i) := by
            -- cancel the `e (jOf i)` terms
            have hvec :
                (e i + e (jOf i)) + (e i - e (jOf i)) = (2 : ℝ) • e i := by
              calc
                (e i + e (jOf i)) + (e i - e (jOf i)) =
                    ((e i + e (jOf i)) + e i) - e (jOf i) := by
                      simp [sub_eq_add_neg, add_assoc]
                _ = ((e i + e i) + e (jOf i)) - e (jOf i) := by
                      simp [add_left_comm, add_comm]
                _ = e i + e i := by
                      simp
                _ = (2 : ℝ) • e i := by simp [two_smul]
            simp [hvec]
      _ = ((2 : ℝ) * Real.sqrt 2) • e i := by
            simp [smul_smul, mul_comm]
  have hmem :
      ((2 : ℝ) * Real.sqrt 2) • e i ∈ (latticeL C : Set ℝ²⁴) := by
    have hmemSum :
        (Real.sqrt 2 • (e i + e (jOf i)) + Real.sqrt 2 • (e i - e (jOf i))) ∈
          (latticeL C : Set ℝ²⁴) :=
      add_mem hplusL hminusL
    -- rewrite the goal using `hsum`
    rw [hsum.symm]
    exact hmemSum
  simpa [hsqrt8] using! hmem

open scoped Classical in
private theorem exists_integer_coords_of_mem_latticeL
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.EqCase24 C)
    (e : Fin 24 → ℝ²⁴)
    (hmin : ∀ (i j : Fin 24), i ≠ j →
      (Real.sqrt 2 • (e i + e j)) ∈ latticeShell4 C ∧
        (Real.sqrt 2 • (e i - e j)) ∈ latticeShell4 C)
    {x : ℝ²⁴} (hx : x ∈ (latticeL C : Set ℝ²⁴)) :
    ∃ z : Fin 24 → ℤ, ∀ i : Fin 24, scaledCoord e i x = (z i : ℝ) := by
  have hsqrt8e : ∀ i : Fin 24, (Real.sqrt 8 : ℝ) • e i ∈ (latticeL C : Set ℝ²⁴) :=
    sqrt8_smul_basis_mem_latticeL_of_minVec (C := C) (e := e) hmin
  refine ⟨fun i => (Uniqueness.BS81.inner_latticeL_int (C := C) h (x := (Real.sqrt 8 : ℝ) • e i)
      (y := x) (hsqrt8e i) hx).choose, ?_⟩
  intro i
  have hm :
      (⟪(Real.sqrt 8 : ℝ) • e i, x⟫ : ℝ) =
        ((Uniqueness.BS81.inner_latticeL_int (C := C) h
          (x := (Real.sqrt 8 : ℝ) • e i) (y := x) (hsqrt8e i) hx).choose : ℝ) :=
    (Uniqueness.BS81.inner_latticeL_int (C := C) h
        (x := (Real.sqrt 8 : ℝ) • e i) (y := x) (hsqrt8e i) hx).choose_spec
  simpa [scaledCoord_eq_inner_smul] using! hm

open scoped Classical in
section

/-- Integer coordinates for shell vectors: `scaledCoord` takes integer values with a uniform parity
condition. -/
public theorem exists_integer_coords_of_shell4
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (e : Fin 24 → ℝ²⁴) (he : Orthonormal ℝ e)
    (hmin : ∀ (i j : Fin 24), i ≠ j →
      (Real.sqrt 2 • (e i + e j)) ∈ latticeShell4 C ∧
        (Real.sqrt 2 • (e i - e j)) ∈ latticeShell4 C)
    {u : ℝ²⁴} (hu : u ∈ latticeShell4 C) :
    ∃ z : Fin 24 → ℤ,
      (∀ i : Fin 24, scaledCoord e i u = (z i : ℝ)) ∧
        (∀ i j : Fin 24, Even (z i + z j)) := by
  have _ : Orthonormal ℝ e := he
  have hplus : ∀ i : Fin 24, ∃ m : ℤ,
      (⟪(Real.sqrt 2) • (e i + e (jOf i)), u⟫ : ℝ) = (m : ℝ) := by
    intro i
    have hv : (Real.sqrt 2 • (e i + e (jOf i))) ∈ latticeShell4 C :=
      (hmin i (jOf i) (i_ne_jOf i)).1
    exact Lemma17.inner_mem_int_of_shell4 C h hv hu
  have hminus : ∀ i : Fin 24, ∃ m : ℤ,
      (⟪(Real.sqrt 2) • (e i - e (jOf i)), u⟫ : ℝ) = (m : ℝ) := by
    intro i
    have hv : (Real.sqrt 2 • (e i - e (jOf i))) ∈ latticeShell4 C :=
      (hmin i (jOf i) (i_ne_jOf i)).2
    exact Lemma17.inner_mem_int_of_shell4 C h hv hu
  choose mplus hmplus using hplus
  choose mminus hmminus using hminus
  let z : Fin 24 → ℤ := fun i => mplus i + mminus i
  have hzCoord : ∀ i : Fin 24, scaledCoord e i u = (z i : ℝ) :=
    fun i =>
      scaledCoord_eq_int_add_of_inner_sqrt2_add_sub
        e i (jOf i) u (mplus i) (mminus i) (hmplus i) (hmminus i)
  have hinner : ∀ i j : Fin 24, i ≠ j → ∃ m : ℤ,
      (⟪(Real.sqrt 2) • (e i + e j), u⟫ : ℝ) = (m : ℝ) := by
    intro i j hij
    have hv : (Real.sqrt 2 • (e i + e j)) ∈ latticeShell4 C := (hmin i j hij).1
    exact Lemma17.inner_mem_int_of_shell4 C h hv hu
  refine ⟨z, hzCoord, ?_⟩
  exact even_z_add_z_of_scaledCoord_eq_int (e := e) (x := u) (z := z) hzCoord hinner

end

/-- For a shell vector `u` with `‖u‖^2 = 4`, the sum of squares of the integer scaled coordinates is
`32`. -/
public theorem sum_sq_integer_coords_eq_32
    (e : Fin 24 → ℝ²⁴) (he : Orthonormal ℝ e)
    {u : ℝ²⁴} (hu : ‖u‖ ^ 2 = (4 : ℝ))
    (z : Fin 24 → ℤ) (hz : ∀ i, scaledCoord e i u = (z i : ℝ)) :
    (∑ i : Fin 24, (z i : ℝ) ^ 2) = (32 : ℝ) := by
  have hparseval : ‖u‖ ^ 2 = ∑ i : Fin 24, (coord e i u) ^ 2 :=
    norm_sq_eq_sum_coord_sq e he u
  have hsqrt8_sq : (Real.sqrt 8 : ℝ) ^ 2 = (8 : ℝ) := by
    have h0 : (0 : ℝ) ≤ (8 : ℝ) := by norm_num
    exact Real.sq_sqrt h0
  calc
    (∑ i : Fin 24, (z i : ℝ) ^ 2)
        = ∑ i : Fin 24, (scaledCoord e i u) ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simp [hz i]
    _ = ∑ i : Fin 24, ((Real.sqrt 8 : ℝ) * coord e i u) ^ 2 := by
          simp [scaledCoord]
    _ = ∑ i : Fin 24, (8 : ℝ) * (coord e i u) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro i _
          -- `(a*b)^2 = a^2*b^2` and `a^2 = 8` for `a = √8`.
          simp [mul_pow, hsqrt8_sq]
    _ = (8 : ℝ) * ∑ i : Fin 24, (coord e i u) ^ 2 := by
          -- `mul_sum` is stated for `Finset.sum`; rewrite the `Fintype` sum as a `Finset.univ` sum.
          exact Eq.symm (Finset.mul_sum Finset.univ (fun i => coord e i u ^ 2) 8)
    _ = (8 : ℝ) * ‖u‖ ^ 2 := by simp [hparseval]
    _ = (32 : ℝ) := by nlinarith [hu]

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21
