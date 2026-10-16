/-
Truncated list arithmetic in `ℤ` (length `50`) for certificate computations.

This module packages the shared list operations and coefficientwise lemmas used by both:
* `Dim24.Inequalities.Ineq2.GeOne.Ineq2Varphi` certificates, and
* `Dim24.Inequalities.VarphiNeg.GeOne` certificates.
-/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module

public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Truncated list arithmetic in `ℤ`

This file defines list operations on length `NVarphi` (addition, scalar multiplication, and a
truncated Cauchy product) and proves coefficientwise lemmas for the extractor `coeffZV`.

## Main definitions
* `NVarphi`, `coeffZV`, `truncZV`
* `addZV`, `smulZV`, `mulZV`, `mulFunZV`

## Main statements
* `coeffZV_mulZV_trunc`
-/

namespace SpherePacking.Dim24.CertificateZV
/-- Number of coefficients used in the certificates (`n < 50`). -/
@[expose]
public def NVarphi : ℕ := 50

/-- Coefficient extraction from a truncated `ℤ` list (default `0` out of range). -/
@[expose]
public def coeffZV (l : List ℤ) (n : ℕ) : ℤ :=
  l.getD n 0

/-- Truncate a coefficient function to a list of length `NVarphi`. -/
@[expose]
public def truncZV (a : ℕ → ℤ) : List ℤ :=
  List.ofFn fun i : Fin NVarphi => a i.1

/-- Pointwise addition of truncated `ℤ` lists (length `NVarphi`). -/
@[expose]
public def addZV (a b : List ℤ) : List ℤ :=
  List.ofFn fun i : Fin NVarphi => coeffZV a i.1 + coeffZV b i.1

/-- Pointwise scalar multiplication of a truncated `ℤ` list (length `NVarphi`). -/
@[expose]
public def smulZV (c : ℤ) (a : List ℤ) : List ℤ :=
  List.ofFn fun i : Fin NVarphi => c * coeffZV a i.1

/-- Truncated Cauchy product of `ℤ` lists (length `NVarphi`). -/
@[expose]
public def mulZV (a b : List ℤ) : List ℤ :=
  List.ofFn fun i : Fin NVarphi =>
    let n := i.1
    Finset.sum (Finset.range (n + 1)) fun j => coeffZV a j * coeffZV b (n - j)

/-- Range-sum convolution on coefficient functions (Cauchy product coefficients). -/
@[expose]
public def mulFunZV (a b : ℕ → ℤ) (n : ℕ) : ℤ :=
  Finset.sum (Finset.range (n + 1)) fun j => a j * b (n - j)

private lemma coeffZV_ofFn (f : Fin NVarphi → ℤ) (i : Fin NVarphi) :
    coeffZV (List.ofFn f) i.1 = f i := by
  unfold coeffZV
  have hpos : i.1 < (List.ofFn f).length :=
    lt_of_lt_of_eq i.2 (Eq.symm (List.length_ofFn (f := f)))
  rw [List.getD_eq_getElem (l := List.ofFn f) (d := (0 : ℤ)) hpos]
  exact List.getElem_ofFn hpos

/-- Coefficient lookup for `List.ofFn f` at indices `n < NVarphi`. -/
public lemma coeffZV_ofFn_lt (f : Fin NVarphi → ℤ) (n : ℕ) (hn : n < NVarphi) :
    coeffZV (List.ofFn f) n = f ⟨n, hn⟩ :=
  coeffZV_ofFn (f := f) ⟨n, hn⟩

/-- Truncation preserves coefficients below `NVarphi`. -/
public lemma coeffZV_trunc (a : ℕ → ℤ) (n : ℕ) (hn : n < NVarphi) :
    coeffZV (truncZV a) n = a n := by
  simpa [truncZV] using! (coeffZV_ofFn (f := fun i : Fin NVarphi => a i.1) ⟨n, hn⟩)

/-- Coefficientwise behavior of `addZV` below `NVarphi`. -/
public lemma coeffZV_addZV (a b : List ℤ) (n : ℕ) (hn : n < NVarphi) :
    coeffZV (addZV a b) n = coeffZV a n + coeffZV b n := by
  simpa [addZV] using!
    (coeffZV_ofFn (f := fun i : Fin NVarphi => coeffZV a i.1 + coeffZV b i.1) ⟨n, hn⟩)

/-- Coefficientwise behavior of `smulZV` below `NVarphi`. -/
public lemma coeffZV_smulZV (c : ℤ) (a : List ℤ) (n : ℕ) (hn : n < NVarphi) :
    coeffZV (smulZV c a) n = c * coeffZV a n := by
  simpa [smulZV] using! (coeffZV_ofFn (f := fun i : Fin NVarphi => c * coeffZV a i.1) ⟨n, hn⟩)

/-- Coefficient formula for `mulZV` below `NVarphi` (finite Cauchy product). -/
public lemma coeffZV_mulZV (a b : List ℤ) (n : ℕ) (hn : n < NVarphi) :
    coeffZV (mulZV a b) n =
      Finset.sum (Finset.range (n + 1)) (fun j => coeffZV a j * coeffZV b (n - j)) := by
  simpa [mulZV] using!
    (coeffZV_ofFn (f := fun i : Fin NVarphi =>
      let n := i.1
      Finset.sum (Finset.range (n + 1)) (fun j => coeffZV a j * coeffZV b (n - j))) ⟨n, hn⟩)

/-- Truncated list multiplication agrees with coefficient-function convolution below `NVarphi`. -/
public lemma coeffZV_mulZV_trunc (a b : ℕ → ℤ) (n : ℕ) (hn : n < NVarphi) :
    coeffZV (mulZV (truncZV a) (truncZV b)) n = mulFunZV a b n := by
  have hmul := coeffZV_mulZV (a := truncZV a) (b := truncZV b) (n := n) hn
  refine hmul.trans ?_
  rw [mulFunZV]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.1 hj)
  have hjlt : j < NVarphi := lt_of_le_of_lt hjle hn
  have hnsub : n - j ≤ n := Nat.sub_le _ _
  have hnsub_lt : n - j < NVarphi := lt_of_le_of_lt hnsub hn
  rw [coeffZV_trunc (a := a) (n := j) (hn := hjlt)]
  rw [coeffZV_trunc (a := b) (n := n - j) (hn := hnsub_lt)]

end SpherePacking.Dim24.CertificateZV
