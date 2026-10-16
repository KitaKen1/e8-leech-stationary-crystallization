-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.Defs
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.ZonalKernelPSD
public import
  SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheoremFixed.ZonalPolynomial24
import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheoremFixed.GegenbauerBridge24

/-!
# Zonal polynomial for the harmonic Gram kernel (dimension 24)

On the unit sphere, the harmonic Gram kernel depends only on `t = ⟪u,v⟫`. We package this by
introducing a univariate polynomial `harmPoly24 k` and a scalar `harmKernelScalar24 k` such that

`harmKernel24 k u v = (harmKernelScalar24 k) * (harmPoly24 k).eval (⟪u, v⟫ : ℝ)`.

The scalar comes from the explicit computation in `AdditionTheoremFixed/` that relates harmonic
projection to the normalized Gegenbauer kernel.

## Main definitions
* `harmPoly24`
* `harmKernelScalar24`

## Main statements
* `harmKernel24_eq_harmPoly24_eval`
* `harmKernelScalar24_ne_zero`
* `harmKernelScalar24_pos`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheorem
noncomputable section

open scoped RealInnerProductSpace

open AdditionTheoremFixed.ZonalPolynomial24
  (harmKernel24_eq_harmPoly24Raw_eval harmPoly24Raw
    harmPoly24Raw_eval_eq_inv_scale_mul_gegenbauer_eval scale24 scale24_ne_zero)

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- The univariate zonal polynomial corresponding to `harmKernel24`. -/
@[expose] public noncomputable def harmPoly24 (k : ℕ) : Polynomial ℝ :=
  Gegenbauer24 k

/-- The scalar factor relating `harmKernel24` to the normalized Gegenbauer kernel. -/
@[expose] public noncomputable def harmKernelScalar24 (k : ℕ) : ℝ :=
  (harmPoly24Raw k).eval (1 : ℝ)

lemma gegenbauer_eval_one_ne_zero (k : ℕ) :
    (gegenbauer gegenbauer24Param k).eval (1 : ℝ) ≠ 0 := by
  -- If this value were `0`, the normalization identity `(Gegenbauer24 k).eval 1 = 1` would fail.
  intro h0
  have h0' : (gegenbauer (11 : ℝ) k).eval (1 : ℝ) = 0 := by
    simpa [gegenbauer24Param] using! h0
  have h := (Uniqueness.BS81.LP.Gegenbauer24_eval_one k)
  -- Unfold `Gegenbauer24` at index `k` and evaluate at `t = 1`.
  have :
      (Uniqueness.BS81.LP.Gegenbauer24 k).eval (1 : ℝ) = 0 := by
    simp [Uniqueness.BS81.LP.Gegenbauer24, gegenbauer24Param, h0']
  -- Contradiction with `(...).eval 1 = 1`.
  have h2 := h
  rw [this] at h2
  exact (zero_ne_one (α := ℝ)) h2

/-! ### Basic properties of `harmKernelScalar24` -/

/-- The scalar `harmKernelScalar24 k` is nonzero. -/
public lemma harmKernelScalar24_ne_zero (k : ℕ) : harmKernelScalar24 k ≠ 0 := by
  have hs : scale24 k ≠ 0 := scale24_ne_zero (k := k)
  have hg : (gegenbauer gegenbauer24Param k).eval (1 : ℝ) ≠ 0 :=
    gegenbauer_eval_one_ne_zero (k := k)
  have hscalar :
    harmKernelScalar24 k =
        (scale24 k)⁻¹ * (gegenbauer gegenbauer24Param k).eval (1 : ℝ) := by
    simpa [harmKernelScalar24] using!
      harmPoly24Raw_eval_eq_inv_scale_mul_gegenbauer_eval (k := k) (t := (1 : ℝ))
  exact hscalar.symm ▸ mul_ne_zero (inv_ne_zero hs) hg

/-! ### Evaluating the harmonic Gram kernel via `harmPoly24` -/

/-- Evaluate `harmKernel24` using the zonal polynomial `harmPoly24`. -/
public theorem harmKernel24_eq_harmPoly24_eval
    (k : ℕ) {u v : ℝ²⁴} (hu : ‖u‖ = (1 : ℝ)) (hv : ‖v‖ = (1 : ℝ)) :
    PSD.ZonalKernel.harmKernel24 k u v =
      (harmKernelScalar24 k) * (harmPoly24 k).eval (⟪u, v⟫ : ℝ) := by
  -- Use the explicit polynomial extracted from harmonic projection, then the bridge to
  -- `gegenbauer 11`, and finally rewrite in terms of the normalized basis `Gegenbauer24`.
  have hraw :=
    harmKernel24_eq_harmPoly24Raw_eval (k := k) (u := u) (v := v) hu hv
  have hbridge :=
    harmPoly24Raw_eval_eq_inv_scale_mul_gegenbauer_eval (k := k) (t := (⟪u, v⟫ : ℝ))
  -- Rewrite `gegenbauer ... k).eval t` as `c_k * (Gegenbauer24 k).eval t`.
  let c : ℝ := (gegenbauer gegenbauer24Param k).eval (1 : ℝ)
  have hc : c ≠ 0 := gegenbauer_eval_one_ne_zero (k := k)
  have hnorm :
      (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ) =
        c⁻¹ * (gegenbauer gegenbauer24Param k).eval (⟪u, v⟫ : ℝ) := by
    -- Definitional: `Gegenbauer24 k = C (c⁻¹) * gegenbauer ... k`.
    simp [Gegenbauer24, c, gegenbauer24Param]
  have hgegen :
      (gegenbauer gegenbauer24Param k).eval (⟪u, v⟫ : ℝ) =
        c * (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ) :=
    (inv_mul_eq_iff_eq_mul₀ hc).mp (id (Eq.symm hnorm))
  have hscalar :
      harmKernelScalar24 k =
        (scale24 k)⁻¹ * c := by
    -- The bridge identity at `t = 1`.
    have hbridge1 :=
      harmPoly24Raw_eval_eq_inv_scale_mul_gegenbauer_eval (k := k) (t := (1 : ℝ))
    simpa [harmKernelScalar24, c] using! hbridge1
  calc
    PSD.ZonalKernel.harmKernel24 k u v =
        (harmPoly24Raw k).eval (⟪u, v⟫ : ℝ) :=
          hraw
    _ =
        (scale24 k)⁻¹ * (gegenbauer gegenbauer24Param k).eval (⟪u, v⟫ : ℝ) :=
          hbridge
    _ =
        (scale24 k)⁻¹ * (c * (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ)) := by
          simp [hgegen]
    _ = ((scale24 k)⁻¹ * c) * (Gegenbauer24 k).eval (⟪u, v⟫ : ℝ) := by
          simp [mul_assoc, mul_left_comm, mul_comm]
    _ = (harmKernelScalar24 k) * (harmPoly24 k).eval (⟪u, v⟫ : ℝ) := by
          simp [hscalar, harmPoly24, mul_assoc, mul_comm]

lemma harmKernelScalar24_nonneg (k : ℕ) : 0 ≤ harmKernelScalar24 k := by
  let u0 : ℝ²⁴ := EuclideanSpace.single (0 : Fin 24) (1 : ℝ)
  have hu0 : ‖u0‖ = (1 : ℝ) := by
    dsimp [u0]
    norm_num
  have huu : (⟪u0, u0⟫ : ℝ) = 1 := by
    simp [hu0]
  have hscalar :
      PSD.ZonalKernel.harmKernel24 k u0 u0 = harmKernelScalar24 k := by
    simpa [huu, hu0, harmPoly24, harmKernelScalar24, mul_assoc, mul_left_comm, mul_comm] using!
      harmKernel24_eq_harmPoly24_eval (k := k) (u := u0) (v := u0) hu0 hu0
  have hnonneg :
      0 ≤
        ({u0} : Finset ℝ²⁴).sum (fun u =>
          ({u0} : Finset ℝ²⁴).sum (fun v => PSD.ZonalKernel.harmKernel24 k u v)) :=
    PSD.ZonalKernel.sum_sum_harmKernel24_nonneg k {u0}
  simp_all

/-! ### Positivity of `harmKernelScalar24` -/

/-- The scalar `harmKernelScalar24 k` is positive. -/
public lemma harmKernelScalar24_pos (k : ℕ) : 0 < harmKernelScalar24 k := by
  have h0 : 0 ≤ harmKernelScalar24 k := harmKernelScalar24_nonneg (k := k)
  have hne : harmKernelScalar24 k ≠ 0 := harmKernelScalar24_ne_zero (k := k)
  exact lt_of_le_of_ne h0 (Ne.symm hne)

end

end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheorem
