-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import
  SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheoremFixed.HarmonicProjection24

/-!
# Harmonicity of `harmApprox` (dimension 24)

Assuming `‖y‖ = 1`, the explicit correction `harmApprox k y` is harmonic. This is the first step
of the addition-theorem bridge: it provides an explicit element of `Harm k` congruent to
`ZscaledPk k y` modulo `r²`, hence equal to the Fischer orthogonal projection `Φ k y`.

## Main statements
* `isHomogeneous_harmApprox`
* `laplacian_harmApprox_eq_zero`
* `harmApproxPk`
-/
namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheoremFixed.Zonal
noncomputable section

open scoped RealInnerProductSpace

open Finset MvPolynomial

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

open PSD PSD.Harmonic PSD.LinOps

local notation "Var" => Fin 24
local notation "Poly" => MvPolynomial Var ℝ

lemma sumSq_yPoint_eq_one (y : ℝ²⁴) (hy : ‖y‖ = (1 : ℝ)) :
    PSD.ZonalProjector.sumSq (yPoint y) = 1 := by
  have hyn : ⟪y, y⟫ = (1 : ℝ) :=
    inner_self_eq_one_of_norm_eq_one hy
  have : (univ : Finset Var).sum (fun i => y i ^ (2 : ℕ)) = (1 : ℝ) := by
    have hyn' := hyn
    rw [PiLp.inner_apply] at hyn'
    simpa [pow_two] using! hyn'
  simpa [PSD.ZonalProjector.sumSq, yPoint] using! this

lemma isHomogeneous_r2 : (r2 : Poly).IsHomogeneous 2 := by
  -- `r2 = ∑ i, X i ^ 2`.
  refine MvPolynomial.IsHomogeneous.sum (s := (univ : Finset Var))
    (φ := fun i => (X i : Poly) ^ (2 : ℕ)) (n := 2) ?_
  intro i hi
  simpa using! (MvPolynomial.isHomogeneous_X_pow (R := ℝ) (σ := Var) i 2)

lemma isHomogeneous_t (y : ℝ²⁴) : (t y : Poly).IsHomogeneous 1 := by
  simpa [t, yPoint] using! (PSD.LinOps.isHomogeneous_lin (y := (yPoint y)))

/-- The explicit correction `harmApprox k y` is homogeneous of degree `k`. -/
public lemma isHomogeneous_harmApprox (k : ℕ) (y : ℝ²⁴) :
    (harmApprox k y : Poly).IsHomogeneous k := by
  -- Each term has degree `2*j + (k-2*j) = k`.
  refine MvPolynomial.IsHomogeneous.sum
      (s := Finset.range (k / 2 + 1))
      (φ := fun j => (aCoeff k j) • ((r2 : Poly) ^ j * (t y : Poly) ^ (k - 2 * j)))
      (n := k) ?_
  intro j hj
  have hr2 : ((r2 : Poly) ^ j).IsHomogeneous (2 * j) := by
    simpa using! (isHomogeneous_r2.pow j)
  have ht : ((t y : Poly) ^ (k - 2 * j)).IsHomogeneous (k - 2 * j) := by
    simpa using! (isHomogeneous_t (y := y)).pow (k - 2 * j)
  have hjle : j ≤ k / 2 := Nat.le_of_lt_succ (Finset.mem_range.1 hj)
  have h2jle : 2 * j ≤ k := by
    have h1 : 2 * j ≤ 2 * (k / 2) := Nat.mul_le_mul_left 2 hjle
    have hk' : 2 * (k / 2) ≤ k :=
      Nat.mul_div_le k 2
    exact le_trans h1 hk'
  have hmul :
      (((r2 : Poly) ^ j) * (t y : Poly) ^ (k - 2 * j)).IsHomogeneous (2 * j + (k - 2 * j)) :=
    hr2.mul ht
  have hdeg : 2 * j + (k - 2 * j) = k := Nat.add_sub_of_le h2jle
  have hmul' :
      (((r2 : Poly) ^ j) * (t y : Poly) ^ (k - 2 * j)).IsHomogeneous k := by
    simpa [hdeg] using! hmul
  -- Rewrite the scalar multiplication as multiplication by a constant polynomial.
  have hC : (C (aCoeff k j) : Poly).IsHomogeneous 0 := by
    simpa using! (MvPolynomial.isHomogeneous_C (σ := Var) (R := ℝ) (aCoeff k j))
  have hprod :
      ((C (aCoeff k j) : Poly) *
          ((r2 : Poly) ^ j * (t y : Poly) ^ (k - 2 * j))).IsHomogeneous k := by
    simpa using! (hC.mul hmul')
  simpa [MvPolynomial.smul_eq_C_mul, mul_assoc] using! hprod

/-- Package `harmApprox` as an element of the homogeneous degree-`k` piece. -/
@[expose] public noncomputable def harmApproxPk (k : ℕ) (y : ℝ²⁴) : PSD.Fischer.Pk k :=
  ⟨harmApprox k y,
    (MvPolynomial.mem_homogeneousSubmodule (σ := Var) (R := ℝ) k (p := (harmApprox k y : Poly))).2
      (isHomogeneous_harmApprox (k := k) (y := y))⟩

lemma laplacian_term_unit (k : ℕ) (y : ℝ²⁴) (hy : ‖y‖ = (1 : ℝ)) (j : ℕ) :
    PSD.Harmonic.laplacian (((r2 : Poly) ^ j) * (t y : Poly) ^ (k - 2 * j)) =
      (C ((A k j : ℕ) : ℝ) : Poly) * (r2 : Poly) ^ (j - 1) * (t y : Poly) ^ (k - 2 * j) +
        (C ((B k j : ℕ) : ℝ) : Poly) * (r2 : Poly) ^ j * (t y : Poly) ^ ((k - 2 * j) - 2) := by
  -- Start from the general Laplacian formula and specialize `sumSq y = 1`.
  have hsumSq : PSD.ZonalProjector.sumSq (yPoint y) = (1 : ℝ) :=
    sumSq_yPoint_eq_one (y := y) hy
  -- Use the lemma from `PSD/LaplacianR2PowLinPow.lean`.
  have h :=
    (PSD.ZonalProjector.laplacian_r2_pow_mul_lin_pow (y := (yPoint y)) (j := j) (m := (k - 2 * j)))
  -- Replace `sumSq` by `1` before `simp` unfolds it.
  rw [hsumSq] at h
  simpa [A, B, r2, t, yPoint, mul_assoc, mul_left_comm, mul_comm, Nat.mul_assoc, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm, Nat.sub_sub] using! h

/-- For unit `y`, the Laplacian of `harmApprox k y` vanishes. -/
public lemma laplacian_harmApprox_eq_zero (k : ℕ) (y : ℝ²⁴) (hy : ‖y‖ = (1 : ℝ)) :
    PSD.Harmonic.laplacian (harmApprox k y) = 0 := by
  let N : ℕ := k / 2
  -- Abbreviate the two Laplacian contributions.
  let fA : ℕ → Poly := fun j =>
    (aCoeff k j) •
      ((C ((A k j : ℕ) : ℝ) : Poly) * (r2 : Poly) ^ (j - 1) * (t y : Poly) ^ (k - 2 * j))
  let fB : ℕ → Poly := fun j =>
    (aCoeff k j) •
      ((C ((B k j : ℕ) : ℝ) : Poly) * (r2 : Poly) ^ j * (t y : Poly) ^ ((k - 2 * j) - 2))
  have hLap :
      PSD.Harmonic.laplacian (harmApprox k y) =
        (Finset.range (N + 1)).sum (fun j => fA j + fB j) := by
    -- Expand `harmApprox` and use termwise Laplacian.
    -- (`range (N+1)` is definitional equal to `range (k/2+1)`.)
    simp [harmApprox, N, fA, fB, map_sum, smul_add,
      laplacian_term_unit (k := k) (y := y) (hy := hy)]
  -- The `j=0` term of the `A`-sum is `0` since `A k 0 = 0`.
  have hA0 : fA 0 = (0 : Poly) := by
    simp [fA, A]
  have hsumA :
      (Finset.range (N + 1)).sum fA = (Finset.range N).sum (fun j => fA (j + 1)) := by
    simp [Finset.sum_range_succ', hA0, N]
  -- The last `B`-term (`j = N`) vanishes since `B k (k/2) = 0`.
  have hB_last : B k N = 0 := by
    -- `k - 2*(k/2) = k % 2`, hence it is `0` or `1`.
    have hk : 2 * (k / 2) + k % 2 = k := Nat.div_add_mod k 2
    have hm : k - 2 * (k / 2) = k % 2 :=
      Eq.symm Nat.mod_eq_sub_mul_div
    rcases Nat.mod_two_eq_zero_or_one k with hk0 | hk1
    · simp [B, N, hm, hk0]
    · simp [B, N, hm, hk1]
  have hB0 : fB N = (0 : Poly) := by
    simp [fB, hB_last, N]
  have hsumB :
      (Finset.range (N + 1)).sum fB = (Finset.range N).sum fB := by
    -- Split off the last term at `N`.
    simp [Finset.sum_range_succ, hB0, N]
  -- Cancellation identity for the scalar coefficients.
  have hcancel (j : ℕ) :
      (aCoeff k (j + 1)) * (A k (j + 1) : ℝ) + (aCoeff k j) * (B k j : ℝ) = 0 := by
    have hA' : A k (j + 1) ≠ 0 := by
      have h1 : 2 * (j + 1) ≠ 0 := Nat.mul_ne_zero (by decide) (Nat.succ_ne_zero j)
      have h2 : 2 * (k - 2 * (j + 1)) + 2 * (j + 1) + 22 ≠ 0 := by
        -- It is positive since it is at least `22`.
        exact Ne.symm (Nat.zero_ne_add_one (2 * (k - 2 * (j + 1)) + 2 * (j + 1) + 21))
      simp [A, h1]
    have hA : (A k (j + 1) : ℝ) ≠ 0 := by exact_mod_cast hA'
    calc
      (aCoeff k (j + 1)) * (A k (j + 1) : ℝ) + (aCoeff k j) * (B k j : ℝ)
          = (-(aCoeff k j) * (B k j : ℝ) / (A k (j + 1) : ℝ)) * (A k (j + 1) : ℝ) +
              (aCoeff k j) * (B k j : ℝ) := by
              simp [aCoeff_succ]
      _ = (-(aCoeff k j) * (B k j : ℝ)) + (aCoeff k j) * (B k j : ℝ) := by
            simp [div_eq_mul_inv, mul_assoc, hA]
      _ = 0 := by ring
  -- Align exponents: `k - 2*(j+1) = (k - 2*j) - 2`.
  have hexp (j : ℕ) : k - 2 * (j + 1) = (k - 2 * j) - 2 := by
    -- `2*(j+1) = 2*j + 2` and `a - (b + c) = (a - b) - c`.
    simp [Nat.mul_add, Nat.add_comm, Nat.sub_sub]
  -- Termwise cancellation after shifting: `fA (j+1) + fB j = 0`.
  have hcancel_term (j : ℕ) (hj : j ∈ Finset.range N) : fA (j + 1) + fB j = 0 := by
    have hexp' : (t y : Poly) ^ (k - 2 * (j + 1)) = (t y : Poly) ^ ((k - 2 * j) - 2) := by
      simp [hexp j]
    -- Put both terms over the same monomial and reduce to the scalar cancellation `hcancel j`.
    have hc : (aCoeff k (j + 1)) * (A k (j + 1) : ℝ) + (aCoeff k j) * (B k j : ℝ) = 0 :=
      hcancel j
    -- Rewrite scalar multiplication as multiplication by constant polynomials,
    -- then factor out the common monomial.
    set M : Poly := (r2 : Poly) ^ j * (t y : Poly) ^ ((k - 2 * j) - 2)
    have hA :
        fA (j + 1) =
          (C ((aCoeff k (j + 1)) * (A k (j + 1) : ℝ)) : Poly) * M := by
      -- Use `smul_eq_C_mul` and combine constants.
      dsimp [fA, M]
      -- Align the exponent.
      rw [hexp']
      -- Turn `•` into `C _ * _` and reassociate.
      simp [MvPolynomial.smul_eq_C_mul, mul_assoc, MvPolynomial.C_mul]
    have hB :
        fB j =
          (C ((aCoeff k j) * (B k j : ℝ)) : Poly) * M := by
      dsimp [fB, M]
      simp [MvPolynomial.smul_eq_C_mul, mul_assoc, MvPolynomial.C_mul]
    -- Now the cancellation is purely scalar.
    rw [hA, hB]
    rw [← add_mul]
    rw [← MvPolynomial.C_add (σ := Var) (R := ℝ)
      (a := (aCoeff k (j + 1)) * (A k (j + 1) : ℝ)) (a' := (aCoeff k j) * (B k j : ℝ))]
    simp [hc]
  -- Put the pieces together.
  -- `Δ(harmApprox) = ∑ (fA + fB)`, and after shifting/splitting it becomes a sum of `0`.
  rw [hLap]
  -- Split the big sum and rewrite `fA` and `fB`.
  have :
      (Finset.range (N + 1)).sum (fun j => fA j + fB j) =
        (Finset.range N).sum (fun j => fA (j + 1) + fB j) := by
    -- Expand and use `hsumA`/`hsumB`.
    -- Start from the RHS and unfold.
    calc
      (Finset.range (N + 1)).sum (fun j => fA j + fB j)
          = (Finset.range (N + 1)).sum fA + (Finset.range (N + 1)).sum fB := by
              simp [Finset.sum_add_distrib]
      _ = (Finset.range N).sum (fun j => fA (j + 1)) + (Finset.range N).sum fB := by
              simp [hsumA, hsumB]
      _ = (Finset.range N).sum (fun j => (fA (j + 1) + fB j)) := by
              simp [Finset.sum_add_distrib]
  rw [this]
  -- Now cancel termwise.
  refine Finset.sum_eq_zero ?_
  intro j hj
  exact hcancel_term j hj

end

end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheoremFixed.Zonal
