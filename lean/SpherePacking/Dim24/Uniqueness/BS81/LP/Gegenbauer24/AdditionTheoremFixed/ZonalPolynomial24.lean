-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import
  SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheoremFixed.HarmonicProjection24Proj
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Zonal polynomial extracted from harmonic projection (dimension 24)

For unit vectors `u,v ∈ Ω₂₄`, the harmonic Gram kernel
`harmKernel24 k u v = ⟪Φ k u, Φ k v⟫`
can be computed by evaluating the explicit harmonic representative `harmApprox k v`. This yields a
univariate polynomial `harmPoly24Raw k` such that
`harmKernel24 k u v = (harmPoly24Raw k).eval (⟪u, v⟫ : ℝ)`.

## Main definitions
* `harmPoly24Raw`

## Main statements
* `harmKernel24_eq_harmPoly24Raw_eval`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheoremFixed.ZonalPolynomial24
noncomputable section

open scoped RealInnerProductSpace

open Finset Polynomial

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

open PSD PSD.ZonalKernel

open Gegenbauer24.AdditionTheoremFixed.Zonal

/-- Unnormalized zonal polynomial from `harmApprox`. -/
@[expose]
public noncomputable def harmPoly24Raw (k : ℕ) : Polynomial ℝ :=
  (Finset.range (k / 2 + 1)).sum (fun j => (C (aCoeff k j)) * (X ^ (k - 2 * j)))

@[simp] lemma harmPoly24Raw_eval (k : ℕ) (t : ℝ) :
    (harmPoly24Raw k).eval t =
      (Finset.range (k / 2 + 1)).sum (fun j => (aCoeff k j) * t ^ (k - 2 * j)) := by
  -- Use the ring-hom form of evaluation (stable `simp`).
  let φ : Polynomial ℝ →+* ℝ := Polynomial.eval₂RingHom (RingHom.id ℝ) t
  have hφ : (harmPoly24Raw k).eval t = φ (harmPoly24Raw k) := by rfl
  calc
    (harmPoly24Raw k).eval t = φ (harmPoly24Raw k) := hφ
    _ = (Finset.range (k / 2 + 1)).sum (fun j =>
          φ ((Polynomial.C (aCoeff k j)) * (Polynomial.X ^ (k - 2 * j)))) := by
          simp [harmPoly24Raw, φ, map_sum]
    _ = (Finset.range (k / 2 + 1)).sum (fun j => (aCoeff k j) * t ^ (k - 2 * j)) := by
          simp [φ]

/-- Evaluate the harmonic Gram kernel using the univariate polynomial `harmPoly24Raw`. -/
public theorem harmKernel24_eq_harmPoly24Raw_eval
    (k : ℕ) {u v : ℝ²⁴} (hu : ‖u‖ = (1 : ℝ)) (hv : ‖v‖ = (1 : ℝ)) :
    harmKernel24 k u v = (harmPoly24Raw k).eval (⟪u, v⟫ : ℝ) := by
  have hΦsub :
      (Φ k v : Harmonic.Harm k) =
        Gegenbauer24.AdditionTheoremFixed.Zonal.harmApproxHarm k v hv := by
    simpa using! (Gegenbauer24.AdditionTheoremFixed.Zonal.Φ_eq_harmApproxHarm (k := k) (y := v) hv)
  have hΦ : (Φ k v : Fischer.Pk k) =
      (Gegenbauer24.AdditionTheoremFixed.Zonal.harmApproxPk k v : Fischer.Pk k) := by
    simpa [Gegenbauer24.AdditionTheoremFixed.Zonal.harmApproxHarm] using!
      congrArg (fun p : Harmonic.Harm k => (p : Fischer.Pk k)) hΦsub
  have hEval :
      evalPk (k := k) (y := u) (Φ k v : Fischer.Pk k) =
        (Finset.range (k / 2 + 1)).sum (fun j =>
          (aCoeff k j) * (⟪u, v⟫ : ℝ) ^ (k - 2 * j)) := by
    have ht :
        MvPolynomial.eval (fun i : Fin 24 => u.ofLp i) (t v : MvPolynomial (Fin 24) ℝ) =
          (⟪u, v⟫ : ℝ) := by
      simp [t, yPoint, PSD.LinOps.lin, PiLp.inner_apply]
    have hr2 : MvPolynomial.eval (fun i : Fin 24 => u.ofLp i) (r2 : MvPolynomial (Fin 24) ℝ) =
        (⟪u, u⟫ : ℝ) := by
      rw [PiLp.inner_apply]
      simp [r2, PSD.R2Laplacian.r2, pow_two]
    have huSq : ‖u‖ ^ 2 = (1 : ℝ) := by
      simp [hu]
    -- Evaluate the explicit polynomial and use `‖u‖ = 1` to simplify the `r2` factor.
    simp [evalPk, hΦ, harmApproxPk, harmApprox, evalPoly, ht, hr2, huSq, MvPolynomial.smul_eq_C_mul,
      MvPolynomial.eval_mul, MvPolynomial.eval_pow]
  calc
    harmKernel24 k u v
        = evalPk (k := k) (y := u) (Φ k v : Fischer.Pk k) := by
            simpa [harmKernel24] using! (inner_Φ_eq_eval (k := k) (y := u) (h := Φ k v))
    _ = (Finset.range (k / 2 + 1)).sum (fun j =>
          (aCoeff k j) * (⟪u, v⟫ : ℝ) ^ (k - 2 * j)) := hEval
    _ = (harmPoly24Raw k).eval (⟪u, v⟫ : ℝ) := by
          simp [harmPoly24Raw_eval]

end

end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.AdditionTheoremFixed.ZonalPolynomial24
