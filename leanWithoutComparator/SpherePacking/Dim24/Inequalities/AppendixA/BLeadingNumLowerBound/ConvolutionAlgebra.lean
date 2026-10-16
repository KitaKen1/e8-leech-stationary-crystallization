/- Convolution algebra for `AppendixA.conv` / `qseries` bookkeeping. -/
-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingCoeffs
public import SpherePacking.Dim24.Inequalities.AppendixA.QSeries
import Mathlib.Algebra.Polynomial.Basic


/-!
### Convolution algebra for `AppendixA.conv`

We prove commutativity/associativity of the Cauchy convolution `conv` (defined via
`Finset.antidiagonal`) by reducing to commutativity/associativity of multiplication of truncated
polynomials (only finitely many coefficients are relevant at a fixed index).
-/

noncomputable section

namespace SpherePacking.Dim24.AppendixA

open scoped BigOperators


private def polyTrunc (a : ℕ → ℚ) (N : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (N + 1), Polynomial.monomial k (a k)

private lemma antidiagonal_props {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ Finset.antidiagonal n) :
    p.1 + p.2 = n ∧ p.1 ≤ n ∧ p.2 ≤ n := by
  have hpn : p.1 + p.2 = n := by simpa [Finset.mem_antidiagonal] using! hp
  refine ⟨hpn, ?_, ?_⟩
  · exact le_trans (Nat.le_add_right _ _) (le_of_eq hpn)
  · exact le_trans (Nat.le_add_left _ _) (le_of_eq hpn)

private lemma polyTrunc_coeff (a : ℕ → ℚ) (N n : ℕ) :
    (polyTrunc a N).coeff n = if n ≤ N then a n else 0 := by
  simp [polyTrunc, Polynomial.coeff_monomial, Finset.mem_range]

private lemma conv_eq_coeff_mul_polyTrunc (a b : ℕ → ℚ) (N n : ℕ) (hn : n ≤ N) :
    (polyTrunc a N * polyTrunc b N).coeff n = conv a b n := by
  rw [Polynomial.coeff_mul]
  refine Finset.sum_congr rfl ?_
  intro p hp
  rcases antidiagonal_props hp with ⟨_, hp1le, hp2le⟩
  simp [polyTrunc_coeff, le_trans hp1le hn, le_trans hp2le hn]

/-- Commutativity of the Cauchy convolution `conv`. -/
public lemma conv_comm (a b : ℕ → ℚ) (n : ℕ) : conv a b n = conv b a n := by
  have hmul :
      (polyTrunc a n * polyTrunc b n).coeff n = (polyTrunc b n * polyTrunc a n).coeff n := by
    simp [mul_comm]
  rw [← conv_eq_coeff_mul_polyTrunc (a := a) (b := b) (N := n) (n := n) le_rfl]
  rw [← conv_eq_coeff_mul_polyTrunc (a := b) (b := a) (N := n) (n := n) le_rfl]
  exact hmul

/-- Associativity of the Cauchy convolution `conv`. -/
public lemma conv_assoc (a b c : ℕ → ℚ) (n : ℕ) :
    conv (conv a b) c n = conv a (conv b c) n := by
  let Pa : Polynomial ℚ := polyTrunc a n
  let Pb : Polynomial ℚ := polyTrunc b n
  let Pc : Polynomial ℚ := polyTrunc c n
  have hleft : ((Pa * Pb) * Pc).coeff n = conv (conv a b) c n := by
    rw [Polynomial.coeff_mul]
    refine Finset.sum_congr rfl ?_
    intro p hp
    rcases antidiagonal_props hp with ⟨_, hp1le, hp2le⟩
    simp [conv, Pa, Pb, Pc, polyTrunc_coeff,
      conv_eq_coeff_mul_polyTrunc (a := a) (b := b) (N := n) (n := p.1) hp1le, hp2le]
  have hright : (Pa * (Pb * Pc)).coeff n = conv a (conv b c) n := by
    rw [Polynomial.coeff_mul]
    refine Finset.sum_congr rfl ?_
    intro p hp
    rcases antidiagonal_props hp with ⟨_, hp1le, hp2le⟩
    simp [conv, Pa, Pb, Pc, polyTrunc_coeff,
      conv_eq_coeff_mul_polyTrunc (a := b) (b := c) (N := n) (n := p.2) hp2le, hp1le]
  have hassoc : ((Pa * Pb) * Pc).coeff n = (Pa * (Pb * Pc)).coeff n := by
    simp [mul_assoc]
  exact hleft.symm.trans (hassoc.trans hright)

/-!
### Helper lemmas for `BleadingCoeffs.coeffQ`
-/

/-- `coeffQ (List.ofFn f) n = f ⟨n, hn⟩` for indices `n < QN`. -/
public lemma coeffQ_ofFn_lt (f : Fin BleadingCoeffs.QN → ℚ) (n : ℕ) (hn : n < BleadingCoeffs.QN) :
    BleadingCoeffs.coeffQ (List.ofFn f) n = f ⟨n, hn⟩ := by
  unfold BleadingCoeffs.coeffQ
  have hpos : n < (List.ofFn f).length := by simpa [List.length_ofFn] using! hn
  rw [List.getD_eq_getElem (l := List.ofFn f) (d := (0 : ℚ)) hpos]
  simpa using! (List.getElem_ofFn (f := f) (i := n) (h := hpos))

/-- `coeffQ (List.ofFn f) i = f i` (Fin-indexed form of `coeffQ_ofFn_lt`). -/
public lemma coeffQ_ofFn (f : Fin BleadingCoeffs.QN → ℚ) (i : Fin BleadingCoeffs.QN) :
    BleadingCoeffs.coeffQ (List.ofFn f) i.1 = f i := by
  simpa using! (coeffQ_ofFn_lt (f := f) (n := i.1) (hn := i.2))

/-- Special case of `coeffQ_ofFn` at index `0`. -/
public lemma coeffQ_ofFn_zero (f : Fin BleadingCoeffs.QN → ℚ) :
    BleadingCoeffs.coeffQ (List.ofFn f) 0 = f ⟨0, by simp [BleadingCoeffs.QN]⟩ := by
  simpa using! (coeffQ_ofFn (f := f) (i := ⟨0, by simp [BleadingCoeffs.QN]⟩))

/-- Special case of `coeffQ_ofFn` at index `1`. -/
public lemma coeffQ_ofFn_one (f : Fin BleadingCoeffs.QN → ℚ) :
    BleadingCoeffs.coeffQ (List.ofFn f) 1 = f ⟨1, by simp [BleadingCoeffs.QN]⟩ := by
  simpa using! (coeffQ_ofFn (f := f) (i := ⟨1, by simp [BleadingCoeffs.QN]⟩))

end SpherePacking.Dim24.AppendixA
