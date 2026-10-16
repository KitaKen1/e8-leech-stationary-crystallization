-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.Defs
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.SphereAvgMoments
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.SphereAvgFourthMoment24Final

/-!
# Equivalence of design characterizations for `Ω₂₄`

BS81 define spherical designs via averaging of homogeneous polynomials (equation (14)). The
Delsarte LP method naturally produces Gegenbauer double-sum equalities. This file records the
bridge statements used in the equality case.
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14

noncomputable section

open scoped RealInnerProductSpace BigOperators

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
## Basic algebra of averages
-/

/-- Unfolding lemma for `finsetAvg`. -/
public theorem finsetAvg_def (C : Finset ℝ²⁴) (f : ℝ²⁴ → ℝ) :
    finsetAvg C f = (C.card : ℝ)⁻¹ * C.sum f := by
  rfl

/-!
## Design equivalences (core analytic input)

These are the main bridges that isolate the addition-theorem and harmonic-analysis content.
They should be proved using CK06/CK09 and BDHSS15, but we keep them specialized to `n=24`.
-/

/-!
## Concrete moment consequences (degrees 2 and 4)

BS81 Lemma 16 uses equation (14) with `f_k = ξ_1^k` for `k = 2,4`.
We isolate these as standalone lemmas for re-use in Lemma 16.
-/

/-- Degree-2 moment identity specialized to the first coordinate function. -/
public theorem bs81_moment_coord_pow_two
    (C : Finset ℝ²⁴) (hD : IsBS81SphericalDesign24 11 C) :
    finsetAvg C (fun u => (u (0 : Fin 24)) ^ 2) = (1 / 24 : ℝ) := by
  rcases hD with ⟨_hC, hEq⟩
  have h :=
    hEq 2 (MvPolynomial.X (0 : Fin 24) ^ 2) (by decide)
      (MvPolynomial.isHomogeneous_X_pow (R := ℝ) (i := (0 : Fin 24)) (n := 2))
  have heval :
      mvPolyEval24 (MvPolynomial.X (0 : Fin 24) ^ 2) =
        (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2) := by
    funext x
    simp [mvPolyEval24]
  calc
    finsetAvg C (fun u => (u (0 : Fin 24)) ^ 2) =
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2) := by
          simpa [heval] using! h
    _ = (1 / 24 : ℝ) := by
          simpa using! (sphereAvg24_coord_sq (i := (0 : Fin 24)))

/-- Degree-4 moment identity specialized to the first coordinate function. -/
public theorem bs81_moment_coord_pow_four
    (C : Finset ℝ²⁴) (hD : IsBS81SphericalDesign24 11 C) :
    finsetAvg C (fun u => (u (0 : Fin 24)) ^ 4) = (1 / 208 : ℝ) := by
  rcases hD with ⟨_hC, hEq⟩
  have h :=
    hEq 4 (MvPolynomial.X (0 : Fin 24) ^ 4) (by decide)
      (MvPolynomial.isHomogeneous_X_pow (R := ℝ) (i := (0 : Fin 24)) (n := 4))
  have heval :
      mvPolyEval24 (MvPolynomial.X (0 : Fin 24) ^ 4) =
        (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4) := by
    funext x
    simp [mvPolyEval24]
  calc
    finsetAvg C (fun u => (u (0 : Fin 24)) ^ 4) =
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4) := by
          simpa [heval] using! h
    _ = (1 / 208 : ℝ) := by
          simpa using! sphereAvg24_coord_pow_four

/-- BS81's numeric form of the `k=2` moment identity when `|C| = 196560`. -/
public theorem bs81_sum_coord_pow_two_eq_8190
    (C : Finset ℝ²⁴) (hD : IsBS81SphericalDesign24 11 C) (hcard : C.card = 196560) :
    C.sum (fun u => (u (0 : Fin 24)) ^ 2) = (8190 : ℝ) := by
  have hcard0 : (C.card : ℝ) ≠ 0 := by
    exact_mod_cast (by simp [hcard] : C.card ≠ 0)
  have hsum :
      C.sum (fun u => (u (0 : Fin 24)) ^ 2) = (C.card : ℝ) * (1 / 24 : ℝ) := by
    have hm' :
        (C.card : ℝ)⁻¹ * C.sum (fun u => (u (0 : Fin 24)) ^ 2) = (1 / 24 : ℝ) := by
      simpa [finsetAvg_def] using! bs81_moment_coord_pow_two (C := C) hD
    have := congrArg (fun z : ℝ => (C.card : ℝ) * z) hm'
    simpa [mul_assoc, hcard0] using! this
  have hsum' :
      C.sum (fun u => (u (0 : Fin 24)) ^ 2) = (196560 : ℝ) * (1 / 24 : ℝ) := by
    simpa [hcard] using! hsum
  exact hsum'.trans (by norm_num)

/-- BS81's numeric form of the `k=4` moment identity when `|C| = 196560`. -/
public theorem bs81_sum_coord_pow_four_eq_945
    (C : Finset ℝ²⁴) (hD : IsBS81SphericalDesign24 11 C) (hcard : C.card = 196560) :
    C.sum (fun u => (u (0 : Fin 24)) ^ 4) = (945 : ℝ) := by
  have hcard0 : (C.card : ℝ) ≠ 0 := by
    exact_mod_cast (by simp [hcard] : C.card ≠ 0)
  have hsum :
      C.sum (fun u => (u (0 : Fin 24)) ^ 4) = (C.card : ℝ) * (1 / 208 : ℝ) := by
    have hm' :
        (C.card : ℝ)⁻¹ * C.sum (fun u => (u (0 : Fin 24)) ^ 4) = (1 / 208 : ℝ) := by
      simpa [finsetAvg_def] using! bs81_moment_coord_pow_four (C := C) hD
    have := congrArg (fun z : ℝ => (C.card : ℝ) * z) hm'
    simpa [mul_assoc, hcard0] using! this
  have hsum' :
      C.sum (fun u => (u (0 : Fin 24)) ^ 4) = (196560 : ℝ) * (1 / 208 : ℝ) := by
    simpa [hcard] using! hsum
  exact hsum'.trans (by norm_num)

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14
