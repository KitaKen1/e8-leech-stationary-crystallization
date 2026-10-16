-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingCoeffs
public import SpherePacking.Dim24.Inequalities.Certificate.ZVArith

/-!
Truncated list arithmetic in `ℤ` (length `BleadingCoeffs.QN`).

Several coefficient-table modules compute the first `BleadingCoeffs.QN` coefficients of various
`q`-series by rewriting into explicit `ℤ` formulas and then evaluating truncated list arithmetic.
This file provides the shared list operations and coefficientwise lemmas to avoid duplicated
definitions (and name clashes under the module system).
-/

namespace SpherePacking.Dim24.AppendixA

/-- Coefficient lookup for a truncated integer list, defaulting to `0` out of range. -/
@[expose] public def coeffZV (l : List ℤ) (n : ℕ) : ℤ :=
  CertificateZV.coeffZV l n

/-- Truncate an integer coefficient function to a list of length `BleadingCoeffs.QN`. -/
@[expose] public def truncZV (a : ℕ → ℤ) : List ℤ :=
  CertificateZV.truncZV a

/-- Coefficientwise addition on truncated integer lists. -/
@[expose] public def addZV (a b : List ℤ) : List ℤ :=
  CertificateZV.addZV a b

/-- Scalar multiplication on truncated integer lists. -/
@[expose] public def smulZV (c : ℤ) (a : List ℤ) : List ℤ :=
  CertificateZV.smulZV c a

/-- Negation on truncated integer lists (`negZV a = (-1) • a`). -/
@[expose] public def negZV (a : List ℤ) : List ℤ :=
  smulZV (-1) a

/-- Subtraction on truncated integer lists (`subZV a b = a - b`). -/
@[expose] public def subZV (a b : List ℤ) : List ℤ :=
  addZV a (negZV b)

/-- Truncated Cauchy product on integer lists, keeping coefficients up to `BleadingCoeffs.QN`. -/
@[expose] public def mulZV (a b : List ℤ) : List ℤ :=
  CertificateZV.mulZV a b

private lemma hn_cert {n : ℕ} (hn : n < BleadingCoeffs.QN) :
    n < CertificateZV.NVarphi := by
  simpa [BleadingCoeffs.QN, CertificateZV.NVarphi] using! hn

/-- Coefficient lookup for `List.ofFn f` at indices `n < BleadingCoeffs.QN`. -/
public lemma coeffZV_ofFn_lt (f : Fin BleadingCoeffs.QN → ℤ) (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffZV (List.ofFn f) n = f ⟨n, hn⟩ := by
  simpa [coeffZV, CertificateZV.NVarphi] using!
    (CertificateZV.coeffZV_ofFn_lt (f := f) (n := n) (hn := hn_cert hn))

/-- Truncation preserves coefficients below `BleadingCoeffs.QN`. -/
public lemma coeffZV_truncZV (a : ℕ → ℤ) (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffZV (truncZV a) n = a n := by
  simpa [coeffZV, truncZV] using! (CertificateZV.coeffZV_trunc (a:=a) (n:=n) (hn:=hn_cert hn))

/-- Coefficientwise behavior of `addZV` below `BleadingCoeffs.QN`. -/
public lemma coeffZV_addZV (a b : List ℤ) (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffZV (addZV a b) n = coeffZV a n + coeffZV b n := by
  simpa [coeffZV, addZV] using! (CertificateZV.coeffZV_addZV (a:=a) (b:=b) (n:=n) (hn:=hn_cert hn))

/-- Coefficientwise behavior of `smulZV` below `BleadingCoeffs.QN`. -/
public lemma coeffZV_smulZV (c : ℤ) (a : List ℤ) (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffZV (smulZV c a) n = c * coeffZV a n := by
  simpa [coeffZV, smulZV] using! (CertificateZV.coeffZV_smulZV (c:=c) (a:=a) (n:=n) (hn:=hn_cert hn))

/-- Coefficientwise behavior of `negZV` below `BleadingCoeffs.QN`. -/
public lemma coeffZV_negZV (a : List ℤ) (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffZV (negZV a) n = -coeffZV a n := by
  simpa [negZV] using! (coeffZV_smulZV (c := (-1 : ℤ)) (a := a) (n := n) hn)

/-- Coefficientwise behavior of `subZV` below `BleadingCoeffs.QN`. -/
public lemma coeffZV_subZV (a b : List ℤ) (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffZV (subZV a b) n = coeffZV a n - coeffZV b n := by
  have hadd : coeffZV (addZV a (negZV b)) n = coeffZV a n + coeffZV (negZV b) n :=
    coeffZV_addZV (a := a) (b := negZV b) (n := n) hn
  have hneg : coeffZV (negZV b) n = -coeffZV b n := coeffZV_negZV (a := b) (n := n) hn
  simp [subZV, sub_eq_add_neg, hadd, hneg]

/-- Coefficient formula for `mulZV` below `BleadingCoeffs.QN` (finite Cauchy product). -/
public lemma coeffZV_mulZV (a b : List ℤ) (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    coeffZV (mulZV a b) n =
      Finset.sum (Finset.range (n + 1)) fun j => coeffZV a j * coeffZV b (n - j) := by
  simpa [coeffZV, mulZV] using! (CertificateZV.coeffZV_mulZV (a:=a) (b:=b) (n:=n) (hn:=hn_cert hn))

end SpherePacking.Dim24.AppendixA
