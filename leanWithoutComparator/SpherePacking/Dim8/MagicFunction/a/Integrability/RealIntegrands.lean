/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.

module
public import SpherePacking.Dim8.MagicFunction.a.Basic
import SpherePacking.Dim8.MagicFunction.a.Integrability.ComplexIntegrands

/-!
# Smoothness of the real integrands

This file proves smoothness of the contour parametrisations `z₁'`-`z₆'` and of the real integrands
`Φ₁`-`Φ₆` used to define the auxiliary function `a`.

## Main statements
* `z₁'_contDiffOn` ... `z₆'_contDiffOn`
* `Φ₁_contDiffOn` ... `Φ₆_contDiffOn`
-/

open Real ContDiff Filter Set Complex

section Parametrisations

namespace MagicFunction.Parametrisations

private lemma contDiffOn_add_I_mul (a : ℂ) (s : Set ℝ) :
    ContDiffOn ℝ ∞ (fun y : ℝ => a + I * y) s := by
  simpa using! (contDiffOn_const.add (contDiffOn_const.mul ofRealCLM.contDiff.contDiffOn))

private lemma z₁'_rhs_contDiffOn :
    ContDiffOn ℝ ∞ (fun y : ℝ => (-1 : ℂ) + I * y) (Ioc (0 : ℝ) 1) := by
  simpa using! contDiffOn_add_I_mul (a := (-1 : ℂ)) (s := Ioc (0 : ℝ) 1)

private lemma z₁'_rhs_eq (y : ℝ) (hy : y ∈ Ioc (0 : ℝ) 1) :
    z₁' y = (-1 : ℂ) + I * y := by
  simpa using! z₁'_eq_of_mem (t := y) (mem_Icc_of_Ioc hy)

/-- Smoothness of the parametrisation `z₁'` on `Ioc (0, 1)`. -/
public theorem z₁'_contDiffOn : ContDiffOn ℝ ∞ z₁' (Ioc (0 : ℝ) 1) := by
  simpa using! z₁'_rhs_contDiffOn.congr z₁'_rhs_eq

private lemma z₂'_rhs_contDiffOn :
    ContDiffOn ℝ ∞ (fun y : ℝ => (-1 : ℂ) + y + I) (Icc (0 : ℝ) 1) := by
  simpa [add_assoc] using! (contDiffOn_const.add ofRealCLM.contDiff.contDiffOn).add contDiffOn_const

/-- Smoothness of the parametrisation `z₂'` on `Icc (0, 1)`. -/
public theorem z₂'_contDiffOn : ContDiffOn ℝ ∞ z₂' (Icc (0 : ℝ) 1) := by
  refine z₂'_rhs_contDiffOn.congr fun y hy => by simpa using! z₂'_eq_of_mem (t := y) hy

private lemma z₃'_rhs_contDiffOn :
    ContDiffOn ℝ ∞ (fun y : ℝ => (1 : ℂ) + I * y) (Ioc (0 : ℝ) 1) := by
  simpa using! contDiffOn_add_I_mul (a := (1 : ℂ)) (s := Ioc (0 : ℝ) 1)

private lemma z₃'_rhs_eq (y : ℝ) (hy : y ∈ Ioc (0 : ℝ) 1) :
    z₃' y = (1 : ℂ) + I * y := by
  simpa using! z₃'_eq_of_mem (t := y) (mem_Icc_of_Ioc hy)

/-- Smoothness of the parametrisation `z₃'` on `Ioc (0, 1)`. -/
public theorem z₃'_contDiffOn : ContDiffOn ℝ ∞ z₃' (Ioc (0 : ℝ) 1) := by
  simpa using! z₃'_rhs_contDiffOn.congr z₃'_rhs_eq

private lemma z₄'_rhs_contDiffOn :
    ContDiffOn ℝ ∞ (fun y : ℝ => (1 : ℂ) - y + I) (Icc (0 : ℝ) 1) := by
  simpa using! (contDiffOn_const.sub ofRealCLM.contDiff.contDiffOn).add contDiffOn_const

/-- Smoothness of the parametrisation `z₄'` on `Icc (0, 1)`. -/
public theorem z₄'_contDiffOn : ContDiffOn ℝ ∞ z₄' (Icc (0 : ℝ) 1) := by
  refine z₄'_rhs_contDiffOn.congr fun y hy => by simpa using! z₄'_eq_of_mem (t := y) hy

private lemma z₅'_rhs_contDiffOn : ContDiffOn ℝ ∞ (fun y : ℝ => I * y) (Ioc (0 : ℝ) 1) := by
  simpa using! (contDiffOn_const.mul ofRealCLM.contDiff.contDiffOn)

private lemma z₅'_rhs_eq (y : ℝ) (hy : y ∈ Ioc (0 : ℝ) 1) : z₅' y = I * y := by
  simpa using! z₅'_eq_of_mem (t := y) (mem_Icc_of_Ioc hy)

/-- Smoothness of the parametrisation `z₅'` on `Ioc (0, 1)`. -/
public theorem z₅'_contDiffOn : ContDiffOn ℝ ∞ z₅' (Ioc (0 : ℝ) 1) := by
  simpa using! z₅'_rhs_contDiffOn.congr z₅'_rhs_eq

private lemma z₆'_rhs_contDiffOn : ContDiffOn ℝ ∞ (fun y : ℝ => I * y) (Ici (1 : ℝ)) := by
  simpa using! (contDiffOn_const.mul ofRealCLM.contDiff.contDiffOn)

/-- Smoothness of the parametrisation `z₆'` on `Ici 1`. -/
public theorem z₆'_contDiffOn : ContDiffOn ℝ ∞ z₆' (Ici (1 : ℝ)) := by
  refine z₆'_rhs_contDiffOn.congr fun y hy => by simpa using! z₆'_eq_of_mem (t := y) hy

end MagicFunction.Parametrisations

end Parametrisations
section Integrands

open MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands
  MagicFunction.Parametrisations

variable {r : ℝ} (hr : r ≥ 0)

namespace MagicFunction.a.RealIntegrands

/-- Smoothness of the real integrand `Φ₁ r` on `Ioc (0, 1)`. -/
private lemma Φ₁_contDiffOn_core (r : ℝ) :
    ContDiffOn ℝ ∞ (fun t : ℝ => (I : ℂ) • Φ₁' r (z₁' t)) (Ioc (0 : ℝ) 1) := by
  simpa using! ((Φ₁'_contDiffOn (r := r)).comp z₁'_contDiffOn z₁'_mapsto).const_smul I

public theorem Φ₁_contDiffOn : ContDiffOn ℝ ∞ (Φ₁ r) (Ioc (0 : ℝ) 1) := by
  simpa [Φ₁_def, smul_eq_mul] using! Φ₁_contDiffOn_core (r := r)

/-- Smoothness of the real integrand `Φ₂ r` on `Icc (0, 1)`. -/
public theorem Φ₂_contDiffOn : ContDiffOn ℝ ∞ (Φ₂ r) (Icc (0 : ℝ) 1) := by
  simpa [Φ₂_def, Φ₂'] using! (Φ₁'_contDiffOn (r := r)).comp z₂'_contDiffOn z₂'_mapsto

/-- Smoothness of the real integrand `Φ₃ r` on `Ioc (0, 1)`. -/
private lemma Φ₃_contDiffOn_core (r : ℝ) :
    ContDiffOn ℝ ∞ (fun t : ℝ => (I : ℂ) • Φ₃' r (z₃' t)) (Ioc (0 : ℝ) 1) := by
  simpa using! ((Φ₃'_contDiffOn (r := r)).comp z₃'_contDiffOn z₃'_mapsto).const_smul I

public theorem Φ₃_contDiffOn : ContDiffOn ℝ ∞ (Φ₃ r) (Ioc (0 : ℝ) 1) := by
  simpa [Φ₃_def, smul_eq_mul] using! Φ₃_contDiffOn_core (r := r)

/-- Smoothness of the real integrand `Φ₄ r` on `Icc (0, 1)`. -/
private lemma Φ₄_contDiffOn_core (r : ℝ) :
    ContDiffOn ℝ ∞ (fun t : ℝ => (-1 : ℂ) • Φ₃' r (z₄' t)) (Icc (0 : ℝ) 1) := by
  simpa using! ContDiffOn.const_smul (c := (-1 : ℂ))
    ((Φ₃'_contDiffOn (r := r)).comp z₄'_contDiffOn z₄'_mapsto)

public theorem Φ₄_contDiffOn : ContDiffOn ℝ ∞ (Φ₄ r) (Icc (0 : ℝ) 1) := by
  simpa [Φ₄_def, Φ₄', smul_eq_mul] using! Φ₄_contDiffOn_core (r := r)

/-- Smoothness of the real integrand `Φ₅ r` on `Ioc (0, 1)`. -/
private lemma Φ₅_contDiffOn_core (r : ℝ) :
    ContDiffOn ℝ ∞ (fun t : ℝ => (I : ℂ) • Φ₅' r (z₅' t)) (Ioc (0 : ℝ) 1) := by
  simpa using! ((Φ₅'_contDiffOn (r := r)).comp z₅'_contDiffOn z₅'_mapsto).const_smul I

public theorem Φ₅_contDiffOn : ContDiffOn ℝ ∞ (Φ₅ r) (Ioc (0 : ℝ) 1) := by
  simpa [Φ₅_def, smul_eq_mul] using! Φ₅_contDiffOn_core (r := r)

/-- Smoothness of the real integrand `Φ₆ r` on `Ici 1`. -/
private lemma Φ₆_contDiffOn_core (r : ℝ) :
    ContDiffOn ℝ ∞ (fun t : ℝ => (I : ℂ) • Φ₆' r (z₆' t)) (Ici (1 : ℝ)) := by
  simpa using! ((Φ₆'_contDiffOn (r := r)).comp z₆'_contDiffOn z₆'_mapsto).const_smul I

public theorem Φ₆_contDiffOn : ContDiffOn ℝ ∞ (Φ₆ r) (Ici (1 : ℝ)) := by
  simpa [Φ₆_def, smul_eq_mul] using! Φ₆_contDiffOn_core (r := r)

end MagicFunction.a.RealIntegrands

end Integrands
