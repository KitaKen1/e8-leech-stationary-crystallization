-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import
  SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheoremFixed.HarmonicProjection24Harm
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The explicit correction equals the harmonic projection `Φ` (dimension 24)

For `‖y‖ = 1`, the polynomial `harmApprox k y` is harmonic (previous files) and differs from the
scaled reproducing element `ZscaledPk k y` by a multiple of `r²`. Using the Fischer decomposition
`(Harm k)ᗮ = range (mulR2Pk (k := k - 2))`, we conclude that `harmApprox` is exactly the
orthogonal projection `Φ k y`.

## Main statements
* `harmApproxPk_mem_Harm`
* `Φ_eq_harmApproxHarm`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheoremFixed.Zonal
noncomputable section

open scoped RealInnerProductSpace

open Finset MvPolynomial

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

open PSD PSD.Fischer PSD.Harmonic PSD.R2Laplacian

local notation "Var" => Fin 24
local notation "Poly" => MvPolynomial Var ℝ
local notation "Pk" => PSD.Fischer.Pk

local instance (k : ℕ) : NormedAddCommGroup (Pk k) :=
  (show InnerProductSpace.Core ℝ (Pk k) from inferInstance).toNormedAddCommGroup

local instance (k : ℕ) : CompleteSpace (Pk k) :=
  FiniteDimensional.complete ℝ (Pk k)

/-- For unit `y`, the explicit correction lies in the harmonic subspace. -/
public lemma harmApproxPk_mem_Harm (k : ℕ) (y : ℝ²⁴) (hy : ‖y‖ = (1 : ℝ)) :
    harmApproxPk k y ∈ (Harmonic.Harm k) := by
  refine (Harmonic.mem_Harm_iff (k := k) (p := harmApproxPk k y)).2 ?_
  ext d
  simp [Harmonic.laplacianPk, harmApproxPk, laplacian_harmApprox_eq_zero (k := k) (y := y) hy]

/-- `harmApprox` packaged as an element of the harmonic subspace (under `‖y‖=1`). -/
@[expose] public noncomputable def harmApproxHarm (k : ℕ) (y : ℝ²⁴) (hy : ‖y‖ = (1 : ℝ)) :
    Harmonic.Harm k :=
  ⟨harmApproxPk k y, harmApproxPk_mem_Harm (k := k) (y := y) hy⟩

lemma lin_eq_t (y : ℝ²⁴) : (PSD.ZonalKernel.lin y : Poly) = (t y : Poly) := by
  simp [PSD.ZonalKernel.lin, Zonal.t, Zonal.yPoint, PSD.LinOps.lin]

lemma ZscaledPk_val (k : ℕ) (y : ℝ²⁴) :
    (PSD.ZonalKernel.ZscaledPk k y : Pk k).1 = (aCoeff k 0) • (t y : Poly) ^ k := by
  simp [PSD.ZonalKernel.ZscaledPk, PSD.ZonalKernel.ZPk, PSD.ZonalKernel.Z, aCoeff_zero, lin_eq_t]

noncomputable def corrPoly (k : ℕ) (y : ℝ²⁴) : Poly :=
  (Finset.range (k / 2)).sum (fun j =>
    (aCoeff k (j + 1)) • ((r2 : Poly) ^ j * (t y : Poly) ^ (k - 2 * (j + 1))))

lemma isHomogeneous_corrPoly (k : ℕ) (y : ℝ²⁴) :
    (corrPoly k y : Poly).IsHomogeneous (k - 2) := by
  refine MvPolynomial.IsHomogeneous.sum (s := Finset.range (k / 2))
    (φ := fun j => (aCoeff k (j + 1)) • ((r2 : Poly) ^ j * (t y : Poly) ^ (k - 2 * (j + 1))))
    (n := k - 2) ?_
  intro j hj
  have hr2 : ((r2 : Poly) ^ j).IsHomogeneous (2 * j) := by
    have hr2' : (r2 : Poly).IsHomogeneous 2 := by
      refine MvPolynomial.IsHomogeneous.sum (s := (univ : Finset Var))
        (φ := fun i => (X i : Poly) ^ (2 : ℕ)) (n := 2) ?_
      intro i hi
      simpa using! (MvPolynomial.isHomogeneous_X_pow (R := ℝ) (σ := Var) i 2)
    simpa using! (hr2'.pow j)
  have ht : ((t y : Poly) ^ (k - 2 * (j + 1))).IsHomogeneous (k - 2 * (j + 1)) := by
    have ht1 : (t y : Poly).IsHomogeneous 1 := by
      simpa [Zonal.t, yPoint] using! (PSD.LinOps.isHomogeneous_lin (y := yPoint y))
    simpa using! (ht1.pow (k - 2 * (j + 1)))
  have hmul :
      (((r2 : Poly) ^ j) * (t y : Poly) ^ (k - 2 * (j + 1))).IsHomogeneous
        (2 * j + (k - 2 * (j + 1))) := hr2.mul ht
  have hjlt : j < k / 2 := Finset.mem_range.1 hj
  have hjle : j + 1 ≤ k / 2 := Nat.succ_le_of_lt hjlt
  have h2j1le : 2 * (j + 1) ≤ k := by
    have h1 : 2 * (j + 1) ≤ 2 * (k / 2) := Nat.mul_le_mul_left 2 hjle
    have h2 : 2 * (k / 2) ≤ k :=
      Nat.mul_div_le k 2
    exact le_trans h1 h2
  have hdeg : 2 * j + (k - 2 * (j + 1)) = k - 2 := by
    -- Rewrite `k - 2*(j+1)` as `(k-2) - 2*j`.
    have hsub : k - 2 * (j + 1) = (k - 2) - 2 * j := by
      -- Start from `(k - 2) - (2*j) = k - (2 + 2*j)`.
      have h := (Nat.sub_sub k 2 (2 * j)).symm
      -- Rewrite `2 + 2*j = 2*j + 2`.
      simpa [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using! h
    -- Now use `a + ((k-2) - a) = k-2` with `a := 2*j`.
    have h2jle' : 2 * j ≤ k - 2 := by
      -- From `2*(j+1) ≤ k` we get `2*j ≤ k-2`.
      have : 2 * j + 2 ≤ k := by
        simpa [Nat.mul_succ] using! h2j1le
      exact Nat.le_sub_of_add_le this
    exact Eq.symm ((fun {b a c} h => (Nat.sub_eq_iff_eq_add' h).mp) h2jle' (id (Eq.symm hsub)))
  have hmul' :
      (((r2 : Poly) ^ j) * (t y : Poly) ^ (k - 2 * (j + 1))).IsHomogeneous (k - 2) := by
    simpa [hdeg] using! hmul
  have hC : (C (aCoeff k (j + 1)) : Poly).IsHomogeneous 0 := by
    simpa using! (MvPolynomial.isHomogeneous_C (σ := Var) (R := ℝ) (aCoeff k (j + 1)))
  have hprod :
      ((C (aCoeff k (j + 1)) : Poly) *
          (((r2 : Poly) ^ j) * (t y : Poly) ^ (k - 2 * (j + 1)))).IsHomogeneous (k - 2) := by
    simpa using! (hC.mul hmul')
  simpa [MvPolynomial.smul_eq_C_mul, mul_assoc] using! hprod

noncomputable def corrPk (k : ℕ) (y : ℝ²⁴) : Pk (k - 2) :=
  ⟨corrPoly k y,
    (mem_homogeneousSubmodule (σ := Var) (R := ℝ) (k - 2) (p := corrPoly k y)).2
      (isHomogeneous_corrPoly (k := k) (y := y))⟩

lemma harmApprox_eq_leading_add_r2_mul_corr (k : ℕ) (y : ℝ²⁴) :
    harmApprox k y =
      (aCoeff k 0) • (t y : Poly) ^ k + (r2 : Poly) * corrPoly k y := by
  -- Split the `harmApprox` sum into `j=0` and `j≥1`.
  set N : ℕ := k / 2
  have hsplit :
      (Finset.range (N + 1)).sum (fun j =>
          (aCoeff k j) • ((r2 : Poly) ^ j * (t y : Poly) ^ (k - 2 * j))) =
        (aCoeff k 0) • ((r2 : Poly) ^ 0 * (t y : Poly) ^ (k - 0)) +
          (Finset.range N).sum (fun j =>
            (aCoeff k (j + 1)) • ((r2 : Poly) ^ (j + 1) * (t y : Poly) ^ (k - 2 * (j + 1)))) := by
    -- Use `sum_range_succ'` (which splits off the `0` term) and commute the `+`.
    have h :=
      (Finset.sum_range_succ' (f := fun j =>
        (aCoeff k j) • ((r2 : Poly) ^ j * (t y : Poly) ^ (k - 2 * j))) N)
    -- `h` splits the sum; rewrite only `f 0` to avoid simp loops.
    simpa [add_comm, add_left_comm, add_assoc, N, pow_zero, Nat.sub_zero, Nat.zero_mul] using! h
  -- Rewrite the shifted tail as `r2 * corrPoly`.
  have htail :
      (Finset.range N).sum (fun j =>
            (aCoeff k (j + 1)) • ((r2 : Poly) ^ (j + 1) * (t y : Poly) ^ (k - 2 * (j + 1)))) =
        (r2 : Poly) * corrPoly k y := by
    -- Use `r2^(j+1) = r2 * r2^j` and factor out `r2`.
    have hrepl :
        (Finset.range N).sum (fun j =>
              (aCoeff k (j + 1)) • ((r2 : Poly) ^ (j + 1) * (t y : Poly) ^ (k - 2 * (j + 1)))) =
          (Finset.range N).sum (fun j =>
              (r2 : Poly) *
                ((aCoeff k (j + 1)) •
                  ((r2 : Poly) ^ j * (t y : Poly) ^ (k - 2 * (j + 1))))) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp [pow_succ, mul_assoc, mul_comm]
    -- Factor out `r2` from the sum.
    calc
      (Finset.range N).sum (fun j =>
              (aCoeff k (j + 1)) • ((r2 : Poly) ^ (j + 1) * (t y : Poly) ^ (k - 2 * (j + 1))))
          = (Finset.range N).sum (fun j =>
              (r2 : Poly) *
                ((aCoeff k (j + 1)) •
                  ((r2 : Poly) ^ j * (t y : Poly) ^ (k - 2 * (j + 1))))) := hrepl
      _ = (r2 : Poly) * (Finset.range N).sum (fun j =>
              (aCoeff k (j + 1)) • ((r2 : Poly) ^ j * (t y : Poly) ^ (k - 2 * (j + 1)))) := by
            simp [Finset.mul_sum]
      _ = (r2 : Poly) * corrPoly k y := by
            simp [corrPoly, N]
  -- Assemble.
  have hdef :
      harmApprox k y =
        (Finset.range (N + 1)).sum (fun j =>
          (aCoeff k j) • ((r2 : Poly) ^ j * (t y : Poly) ^ (k - 2 * j))) := by
    simp [harmApprox, N]
  -- Rewrite the sum using `hsplit`, then identify the tail with `r2 * corrPoly`.
  simp_all

lemma mulXPk_val (k : ℕ) (i : Var) (p : Pk k) :
    (mulXPk (k := k) i p : Pk (k + 1)).1 = (X i : Poly) * p.1 := by
  simp [mulXPk, LinearMap.codRestrict, LinearMap.comp_apply]

lemma mulR2Pk_val (k : ℕ) (p : Pk k) :
    (mulR2Pk (k := k) p : Pk (k + 2)).1 = (r2 : Poly) * p.1 := by
  -- Expand `mulR2Pk` as `∑ i, X i * (X i * p)`.
  have :
      (mulR2Pk (k := k) p : Pk (k + 2)).1 =
        (univ : Finset Var).sum (fun i => (X i : Poly) * ((X i : Poly) * p.1)) := by
    simp [mulR2Pk, PSD.Fischer.mulR2Pk, LinearMap.sum_apply, LinearMap.comp_apply, mulXPk_val]
  -- Rewrite the RHS as `(∑ i, X i ^ 2) * p`.
  rw [this]
  have hsum :
      (univ : Finset Var).sum (fun i => (X i : Poly) * ((X i : Poly) * p.1)) =
        (univ : Finset Var).sum (fun i => ((X i : Poly) ^ (2 : ℕ)) * p.1) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [pow_two, mul_assoc]
  rw [hsum]
  -- Fold `r2` and use distributivity to factor `p.1`.
  -- `r2 * p.1 = (∑ i, X i^2) * p.1 = ∑ i, (X i^2) * p.1`.
  have hdist :
      ((univ : Finset Var).sum (fun i => (X i : Poly) ^ (2 : ℕ))) * p.1 =
        (univ : Finset Var).sum (fun i => ((X i : Poly) ^ (2 : ℕ)) * p.1) := by
    simpa [mul_assoc] using!
      (Finset.sum_mul (s := (univ : Finset Var)) (f := fun i => (X i : Poly) ^ (2 : ℕ)) (a := p.1))
  -- Conclude by rewriting `r2`.
  simpa [R2Laplacian.r2] using! hdist.symm

lemma ZscaledPk_sub_harmApproxPk_eq_mulR2_succ_succ (m : ℕ) (y : ℝ²⁴) :
    (PSD.ZonalKernel.ZscaledPk (m + 2) y : Pk (m + 2)) - harmApproxPk (m + 2) y =
      mulR2Pk (k := m) (-(corrPk (m + 2) y)) := by
  -- Compare underlying polynomials.
  apply Subtype.ext
  -- First rewrite `ZscaledPk` as the leading term.
  have hZ :
      (PSD.ZonalKernel.ZscaledPk (m + 2) y : Pk (m + 2)).1 =
        (aCoeff (m + 2) 0) • (t y : Poly) ^ (m + 2) :=
    ZscaledPk_val (k := m + 2) (y := y)
  -- Expand `harmApprox` into leading + `r2 * corr`.
  have hH : (harmApproxPk (m + 2) y).1 =
      (aCoeff (m + 2) 0) • (t y : Poly) ^ (m + 2) + (r2 : Poly) * corrPoly (m + 2) y := by
    simp [harmApproxPk, harmApprox_eq_leading_add_r2_mul_corr]
  have hmul_pos :
      (mulR2Pk (k := m) (corrPk (m + 2) y) : Pk (m + 2)).1 =
        (r2 : Poly) * (corrPoly (m + 2) y) := by
    simpa [corrPk] using! (mulR2Pk_val (k := m) (p := (corrPk (m + 2) y)))
  -- Assemble.
  simp [hZ, hH, hmul_pos, sub_eq_add_neg]

/-- For unit `y`, the harmonic projection `Φ k y` agrees with the explicit correction. -/
public lemma Φ_eq_harmApproxHarm (k : ℕ) (y : ℝ²⁴) (hy : ‖y‖ = (1 : ℝ)) :
    PSD.ZonalKernel.Φ k y = harmApproxHarm k y hy := by
  -- Use the characterization of orthogonal projection by orthogonality.
  set K : Submodule ℝ (Pk k) := Harmonic.Harm k
  have hvK : (harmApproxPk k y : Pk k) ∈ K := harmApproxPk_mem_Harm (k := k) (y := y) hy
  have horth : (PSD.ZonalKernel.ZscaledPk k y : Pk k) - (harmApproxPk k y : Pk k) ∈ Kᗮ := by
    cases k with
    | zero =>
        -- `k = 0`: no correction term, so the difference is `0`.
        have hEq : (PSD.ZonalKernel.ZscaledPk 0 y : Pk 0) = harmApproxPk 0 y := by
          apply Subtype.ext
          simp [PSD.ZonalKernel.ZscaledPk, PSD.ZonalKernel.ZPk, PSD.ZonalKernel.Z, harmApproxPk,
            harmApprox, aCoeff_zero, lin_eq_t]
        simp [hEq, K]
    | succ k1 =>
        cases k1 with
        | zero =>
            -- `k = 1`: no correction term, so the difference is `0`.
            have hEq : (PSD.ZonalKernel.ZscaledPk 1 y : Pk 1) = harmApproxPk 1 y := by
              apply Subtype.ext
              simp [PSD.ZonalKernel.ZscaledPk, PSD.ZonalKernel.ZPk, PSD.ZonalKernel.Z, harmApproxPk,
                harmApprox, aCoeff_zero, lin_eq_t]
            simp [hEq, K]
        | succ m =>
            -- `k = m + 2`: the difference lies in the `r²`-range, hence in `Kᗮ`.
            have hKorth :
                Kᗮ = LinearMap.range (mulR2Pk (k := m)) := by
              -- Fischer decomposition at index `m`.
              exact Harm_orthogonal_eq_range_mulR2Pk m
            have hrange :
                (PSD.ZonalKernel.ZscaledPk (m + 2) y : Pk (m + 2)) - harmApproxPk (m + 2) y ∈
                  LinearMap.range (mulR2Pk (k := m)) := by
              refine ⟨-(corrPk (m + 2) y), ?_⟩
              simpa using! (ZscaledPk_sub_harmApproxPk_eq_mulR2_succ_succ (m := m) (y := y)).symm
            simpa [hKorth] using! hrange
  -- Now `harmApproxPk` is the orthogonal projection of `ZscaledPk` onto `Harm k`.
  have hstar :
      K.starProjection (PSD.ZonalKernel.ZscaledPk k y : Pk k) = (harmApproxPk k y : Pk k) :=
    Submodule.eq_starProjection_of_mem_orthogonal (K := K) hvK horth
  -- Turn the ambient statement into an equality in the subtype.
  have hprojE :
      (K.orthogonalProjection (PSD.ZonalKernel.ZscaledPk k y : Pk k) : Pk k) =
        harmApproxPk k y := by
    -- Coercion to the ambient turns `orthogonalProjection` into `starProjection`.
    simpa [Submodule.coe_orthogonalProjection_apply] using! hstar
  -- Match the definitions.
  unfold PSD.ZonalKernel.Φ harmApproxHarm
  -- Both sides live in `Harm k = K`.
  refine Subtype.ext ?_
  simpa [K] using! hprojE

end
end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheoremFixed.Zonal
