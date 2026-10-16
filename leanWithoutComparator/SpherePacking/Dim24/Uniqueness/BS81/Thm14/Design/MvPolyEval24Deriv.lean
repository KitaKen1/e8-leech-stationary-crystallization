-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.DoubleSumsToHarmonics24
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Tactic.Ring

/-!
# Directional derivatives of `evalPoly24`

This file relates the formal partial derivative `MvPolynomial.pderiv` to the analytic Fréchet
derivative `fderiv` of the polynomial evaluation map `evalPoly24` on `ℝ²⁴`.

## Main definitions
* `fderivEvalPoly24`
* `e24`

## Main statements
* `hasFDerivAt_evalPoly24`
* `fderiv_evalPoly24_apply_e24`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem

noncomputable section

open scoped BigOperators ENNReal

open Finset MvPolynomial

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- Coordinate projection as a continuous linear map on `ℝ²⁴`. -/
noncomputable def coordCLM (i : Fin 24) : ℝ²⁴ →L[ℝ] ℝ :=
  PiLp.proj (p := (2 : ℝ≥0∞)) (β := fun _ : Fin 24 => ℝ) i

/-- Standard basis vector in `ℝ²⁴`. -/
@[expose] public noncomputable def e24 (i : Fin 24) : ℝ²⁴ :=
  WithLp.toLp (p := (2 : ℝ≥0∞)) (Pi.single i (1 : ℝ) : Fin 24 → ℝ)

@[simp] lemma coordCLM_e24 (i j : Fin 24) :
    coordCLM (i := j) (e24 i) = (if j = i then (1 : ℝ) else 0) := by
  simp [e24, coordCLM]

/-- The (Fréchet) derivative of `evalPoly24 · p` at `x`, as an explicit linear form. -/
public noncomputable def fderivEvalPoly24 (p : MvPolynomial (Fin 24) ℝ) (x : ℝ²⁴) : ℝ²⁴ →L[ℝ] ℝ :=
  (Finset.univ : Finset (Fin 24)).sum (fun i =>
    (evalPoly24 (y := x) (MvPolynomial.pderiv i p)) • coordCLM (i := i))

lemma fderivEvalPoly24_C (r : ℝ) (x : ℝ²⁴) :
    fderivEvalPoly24 (p := (C r : MvPolynomial (Fin 24) ℝ)) x = 0 := by
  ext v
  simp [fderivEvalPoly24, evalPoly24]

lemma fderivEvalPoly24_add (p q : MvPolynomial (Fin 24) ℝ) (x : ℝ²⁴) :
    fderivEvalPoly24 (p := p + q) x =
      fderivEvalPoly24 (p := p) x + fderivEvalPoly24 (p := q) x := by
  ext v
  simp [fderivEvalPoly24, evalPoly24, Finset.sum_add_distrib, add_smul]

lemma fderivEvalPoly24_mul_X (p : MvPolynomial (Fin 24) ℝ) (i : Fin 24) (x : ℝ²⁴) :
    fderivEvalPoly24 (p := p * X i) x =
      (evalPoly24 (y := x) p) • coordCLM (i := i) + (x i) • fderivEvalPoly24 (p := p) x := by
  ext v
  let S : Finset (Fin 24) := Finset.univ
  have h_apply (q : MvPolynomial (Fin 24) ℝ) :
      (fderivEvalPoly24 (p := q) x) v =
        S.sum (fun j => evalPoly24 (y := x) (pderiv j q) * (coordCLM (i := j)) v) := by
    simp [fderivEvalPoly24, S, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
  have hXi : evalPoly24 (y := x) (X i : MvPolynomial (Fin 24) ℝ) = x i := by
    simp [evalPoly24]
  -- Main algebraic rearrangement.
  have h1 :
      S.sum (fun j =>
          (evalPoly24 (y := x) (pderiv j p) * x i) * (coordCLM (i := j)) v) =
        (x i) * S.sum (fun j =>
          evalPoly24 (y := x) (pderiv j p) * (coordCLM (i := j)) v) := by
    calc
      S.sum (fun j =>
          (evalPoly24 (y := x) (pderiv j p) * x i) * (coordCLM (i := j)) v) =
          S.sum (fun j =>
            (x i) * (evalPoly24 (y := x) (pderiv j p) * (coordCLM (i := j)) v)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
      _ = (x i) * S.sum (fun j =>
            evalPoly24 (y := x) (pderiv j p) * (coordCLM (i := j)) v) := by
            simp [Finset.mul_sum]
  have h2 :
      S.sum (fun j =>
          (evalPoly24 (y := x) p *
              evalPoly24 (y := x) (pderiv j (X i : MvPolynomial (Fin 24) ℝ))) *
              (coordCLM (i := j)) v) =
        evalPoly24 (y := x) p * (coordCLM (i := i)) v := by
    -- The derivative of `X i` is the Kronecker delta, so only the `i`-term survives.
    simp [S, evalPoly24, coordCLM, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ]
  -- Finish by expanding `pderiv_mul` on the LHS and rewriting the RHS.
  -- Both sides are now `ℝ`-valued expressions after applying to `v`.
  rw [h_apply]
  -- Expand `pderiv` of a product inside the sum.
  have :
      S.sum (fun j =>
          evalPoly24 (y := x) (pderiv j (p * X i)) * (coordCLM (i := j)) v) =
      S.sum (fun j =>
            ((evalPoly24 (y := x) (pderiv j p) * x i) +
                (evalPoly24 (y := x) p *
                    evalPoly24 (y := x) (pderiv j (X i : MvPolynomial (Fin 24) ℝ)))) *
              (coordCLM (i := j)) v) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, mul_eq_mul_right_iff]
    refine Or.inl ?_
    simp only [evalPoly24, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X]
    ring_nf
  -- Rewrite RHS of the main goal using `h_apply`.
  rw [this]
  -- Split the sum using distributivity and apply `h1`, `h2`.
  -- Then finish by commutativity of addition.
  have hsplit :
      S.sum (fun j =>
          ((evalPoly24 (y := x) (pderiv j p) * x i) +
                (evalPoly24 (y := x) p *
                    evalPoly24 (y := x) (pderiv j (X i : MvPolynomial (Fin 24) ℝ)))) *
              (coordCLM (i := j)) v) =
          S.sum (fun j =>
            (evalPoly24 (y := x) (pderiv j p) * x i) * (coordCLM (i := j)) v) +
          S.sum (fun j =>
            (evalPoly24 (y := x) p *
                evalPoly24 (y := x) (pderiv j (X i : MvPolynomial (Fin 24) ℝ))) *
              (coordCLM (i := j)) v) := by
    simp [add_mul, Finset.sum_add_distrib, add_mul, mul_assoc]
  -- Rewrite everything using `hsplit`, `h1`, `h2`, and `h_apply`.
  -- The only remaining difference is the order of the two addends.
  have hR :
      ((evalPoly24 (y := x) p) • coordCLM (i := i) + (x i) • fderivEvalPoly24 (p := p) x) v =
        evalPoly24 (y := x) p * (coordCLM (i := i)) v +
          (x i) * S.sum (fun j =>
            evalPoly24 (y := x) (pderiv j p) * (coordCLM (i := j)) v) := by
    simp [h_apply, S, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  -- Put the goal in the same normal form as the LHS computation.
  rw [hR, hsplit, h1, h2]
  ac_rfl

/-- The polynomial evaluation map `y ↦ evalPoly24 p` is differentiable with derivative
`fderivEvalPoly24`. -/
public theorem hasFDerivAt_evalPoly24 (p : MvPolynomial (Fin 24) ℝ) (x : ℝ²⁴) :
    HasFDerivAt (fun y : ℝ²⁴ => evalPoly24 (y := y) p) (fderivEvalPoly24 (p := p) x) x := by
  -- Induction on the polynomial.
  refine MvPolynomial.induction_on (p := p)
    (motive := fun p =>
      HasFDerivAt (fun y : ℝ²⁴ => evalPoly24 (y := y) p) (fderivEvalPoly24 (p := p) x) x)
    (C := ?_) (add := ?_) (mul_X := ?_)
  · intro r
    -- constant
    simpa [evalPoly24, fderivEvalPoly24_C (r := r) (x := x)] using! (hasFDerivAt_const x (c := r))
  · intro p q hp hq
    -- addition
    simpa [evalPoly24, fderivEvalPoly24_add (p := p) (q := q) (x := x)] using! hp.add hq
  · intro p i hp
    -- multiplication by `X i`
    have hcoord :
        HasFDerivAt (fun y : ℝ²⁴ => (y i : ℝ)) (coordCLM (i := i)) x := by
      simpa [coordCLM] using!
        (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := (2 : ℝ≥0∞)) (E := fun _ : Fin 24 => ℝ) (f := x) i)
    have hmul := hp.mul hcoord
    -- Rewrite `evalPoly24 (p * X i)` and the target derivative.
    simpa [evalPoly24, fderivEvalPoly24_mul_X (p := p) (i := i) (x := x), mul_assoc, mul_comm,
      mul_left_comm, add_comm, add_left_comm, add_assoc] using! hmul

/-- Evaluating the derivative of `evalPoly24` on the basis vector `e24 i` gives `pderiv i p`. -/
public theorem fderiv_evalPoly24_apply_e24 (p : MvPolynomial (Fin 24) ℝ) (x : ℝ²⁴) (i : Fin 24) :
    fderiv ℝ (fun y : ℝ²⁴ => evalPoly24 (y := y) p) x (e24 i) =
      evalPoly24 (y := x) (MvPolynomial.pderiv i p) := by
  -- Use the explicit `HasFDerivAt` and evaluate the resulting linear map on `Pi.single`.
  have h := (hasFDerivAt_evalPoly24 (p := p) (x := x)).fderiv
  have h' := congrArg (fun L : ℝ²⁴ →L[ℝ] ℝ => L (e24 i)) h
  -- Compute the sum: only the `i`-term survives.
  have hsum :
      (fderivEvalPoly24 (p := p) x) (e24 i) =
        evalPoly24 (y := x) (MvPolynomial.pderiv i p) := by
    -- Expand the sum and use that the coordinate projections pick out the `i`-th term.
    simp [fderivEvalPoly24, coordCLM_e24]
  simpa [hsum] using! h'

theorem fderiv_fderiv_evalPoly24_apply_e24 (p : MvPolynomial (Fin 24) ℝ) (x : ℝ²⁴) (i : Fin 24) :
    fderiv ℝ
        (fun y : ℝ²⁴ =>
          fderiv ℝ (fun z : ℝ²⁴ => evalPoly24 (y := z) p) y (e24 i)) x (e24 i) =
      evalPoly24 (y := x) (MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) := by
  -- Reduce to the previous lemma applied to the polynomial `pderiv i p`.
  simp [fderiv_evalPoly24_apply_e24]

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem
