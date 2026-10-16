module
public import Mathlib.Data.List.GetD
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.ArithmeticFunction.Misc


/-!
Computable coefficient identities for Appendix A, Lemma A.3 (`Bleadingterms` numerator).

This module provides explicit coefficient lists and supporting lemmas used in the truncation
arguments in `SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound`.
-/

open scoped BigOperators
open scoped ArithmeticFunction.sigma


namespace SpherePacking.Dim24.AppendixA.BleadingCoeffs

/-- Truncation length for the `r`-series coefficient lists used in Appendix A. -/
@[expose] public def N : ℕ := 100

/-- We need `q`-series coefficients up to `q^49` (since `q = r^2` and we truncate at `r^99`). -/
@[expose] public def QN : ℕ := 50

/-!
### Truncated list arithmetic (`ℚ`)
-/

/-- Lookup the `n`-th coefficient of a truncated `ℚ` list, defaulting to `0` past the end. -/
@[expose] public def coeffQ (l : List ℚ) (n : ℕ) : ℚ :=
  l.getD n 0

/-- Pointwise addition of truncated `ℚ` coefficient lists (truncated to `QN`). -/
@[expose] public def addQ (a b : List ℚ) : List ℚ :=
  List.ofFn fun i : Fin QN => coeffQ a i.1 + coeffQ b i.1

/-- Pointwise negation of a truncated `ℚ` coefficient list (truncated to `QN`). -/
@[expose] public def negQ (a : List ℚ) : List ℚ :=
  List.ofFn fun i : Fin QN => -coeffQ a i.1

/-- Pointwise subtraction of truncated `ℚ` coefficient lists (truncated to `QN`). -/
@[expose] public def subQ (a b : List ℚ) : List ℚ :=
  addQ a (negQ b)

/-- Scalar multiplication of a truncated `ℚ` coefficient list (truncated to `QN`). -/
@[expose] public def smulQ (c : ℚ) (a : List ℚ) : List ℚ :=
  List.ofFn fun i : Fin QN => c * coeffQ a i.1

/-- Truncated Cauchy product of `ℚ` coefficient lists, producing coefficients up to `q^(QN-1)`. -/
@[expose] public def mulQ (a b : List ℚ) : List ℚ :=
  List.ofFn fun i : Fin QN =>
    let n := i.1
    Finset.sum (Finset.range (n + 1)) fun j => coeffQ a j * coeffQ b (n - j)

/-- Truncated power of a `ℚ` coefficient list, computed via repeated Cauchy products. -/
@[expose] public def powQ (a : List ℚ) : ℕ → List ℚ
  | 0 => List.ofFn fun i : Fin QN => if i.1 = 0 then (1 : ℚ) else 0
  | Nat.succ k => mulQ a (powQ a k)

/-!
### Eisenstein coefficient lists (up to `q^50`)
-/

/-- Rational `q^n` coefficient of the Eisenstein series `E₂`. -/
@[expose] public def coeffE2Q (n : ℕ) : ℚ :=
  if n = 0 then 1 else (-24 : ℚ) * (σ 1 n)

/-- Rational `q^n` coefficient of the Eisenstein series `E₄`. -/
@[expose] public def coeffE4Q (n : ℕ) : ℚ :=
  if n = 0 then 1 else (240 : ℚ) * (σ 3 n)

/-- Rational `q^n` coefficient of the Eisenstein series `E₆`. -/
@[expose] public def coeffE6Q (n : ℕ) : ℚ :=
  if n = 0 then 1 else (-504 : ℚ) * (σ 5 n)

/-- Truncated `q`-series coefficients of `E₂` (up to `q^(QN-1)`). -/
@[expose] public def E2Q : List ℚ := List.ofFn fun i : Fin QN => coeffE2Q i.1
/-- Truncated `q`-series coefficients of `E₄` (up to `q^(QN-1)`). -/
@[expose] public def E4Q : List ℚ := List.ofFn fun i : Fin QN => coeffE4Q i.1
/-- Truncated `q`-series coefficients of `E₆` (up to `q^(QN-1)`). -/
@[expose] public def E6Q : List ℚ := List.ofFn fun i : Fin QN => coeffE6Q i.1

/-- Truncated `q`-series coefficients of `E₂^2`. -/
@[expose] public def E2SqQ : List ℚ := powQ E2Q 2
/-- Truncated `q`-series coefficients of `E₄^2`. -/
@[expose] public def E4SqQ : List ℚ := powQ E4Q 2
/-- Truncated `q`-series coefficients of `E₄^3`. -/
@[expose] public def E4CubeQ : List ℚ := powQ E4Q 3
/-- Truncated `q`-series coefficients of `E₄^4`. -/
@[expose] public def E4FourthQ : List ℚ := powQ E4Q 4
/-- Truncated `q`-series coefficients of `E₆^2`. -/
@[expose] public def E6SqQ : List ℚ := powQ E6Q 2

/-!
### Numerator coefficient lists (`q`-series)

These correspond to `appendix.txt`:
`phinum`, `phi1num` (without the outer `(1/π)*(-6)`), and `(-49*E4^3 + 25*E6^2)`.
-/

/-- Coefficients of the `phi2` core numerator `-49*E4^3 + 25*E6^2` (truncated). -/
@[expose] public def phi2CoreQ : List ℚ :=
  addQ (smulQ (-49) E4CubeQ) (smulQ 25 E6SqQ)

/-- Coefficients of the `phi` numerator `phinum` from Appendix A (truncated). -/
@[expose] public def phinumQ : List ℚ :=
  addQ
      (addQ
        (subQ (smulQ 25 E4FourthQ) (smulQ 49 (mulQ E6SqQ E4Q)))
        (smulQ 48 (mulQ (mulQ E6Q E4SqQ) E2Q)))
      (mulQ phi2CoreQ E2SqQ)

/-- Coefficients of the `phi1` core numerator (truncated). -/
@[expose] public def phi1CoreQ : List ℚ :=
  addQ
    (smulQ 48 (mulQ E6Q E4SqQ))
    (smulQ 2 (mulQ E2Q phi2CoreQ))

/-!
### `Δ` coefficients (`q`-series) via `Δ = (E₄^3 - E₆^2)/1728`
-/

/-- Truncated `q`-series coefficients of `Δ`, defined via `Δ = (E₄^3 - E₆^2)/1728`. -/
@[expose] public def DeltaQ : List ℚ :=
  smulQ (1 / 1728) (subQ E4CubeQ E6SqQ)

/-- Truncated `q`-series coefficients of `Δ^2`. -/
@[expose] public def DeltaSqQ : List ℚ := powQ DeltaQ 2

/-!
### Truncated theta coefficient lists (`ℤ`)

We only need coefficients up to `r^99`, so it suffices to truncate:
- squares `k^2` to `k <= 10` (`11^2 = 121 > 99`),
- triangular numbers `k(k+1)` to `k <= 9` (`10*11 = 110 > 99`).
-/

/-- Lookup the `n`-th coefficient of a truncated `ℤ` list, defaulting to `0` past the end. -/
@[expose] public def coeffZ (l : List ℤ) (n : ℕ) : ℤ :=
  l.getD n 0

/-- Pointwise addition of truncated `ℤ` coefficient lists (truncated to `N`). -/
@[expose] public def addZ (a b : List ℤ) : List ℤ :=
  List.ofFn fun i : Fin N => coeffZ a i.1 + coeffZ b i.1

/-- Pointwise negation of a truncated `ℤ` coefficient list (truncated to `N`). -/
@[expose] public def negZ (a : List ℤ) : List ℤ :=
  List.ofFn fun i : Fin N => -coeffZ a i.1

/-- Scalar multiplication of a truncated `ℤ` coefficient list (truncated to `N`). -/
@[expose] public def smulZ (c : ℤ) (a : List ℤ) : List ℤ :=
  List.ofFn fun i : Fin N => c * coeffZ a i.1

/-- Truncated Cauchy product of `ℤ` coefficient lists, producing coefficients up to `r^(N-1)`. -/
@[expose] public def mulZ (a b : List ℤ) : List ℤ :=
  List.ofFn fun i : Fin N =>
    let n := i.1
    Finset.sum (Finset.range (n + 1)) fun j => coeffZ a j * coeffZ b (n - j)

/-- Truncated power of a `ℤ` coefficient list, computed via repeated Cauchy products. -/
@[expose] public def powZ (a : List ℤ) : ℕ → List ℤ
  | 0 => List.ofFn fun i : Fin N => if i.1 = 0 then (1 : ℤ) else 0
  | Nat.succ k => mulZ a (powZ a k)

/-- Shift a truncated `ℤ` coefficient list by one (corresponding to multiplication by `r`). -/
@[expose] public def shift1Z (a : List ℤ) : List ℤ :=
  List.ofFn fun i : Fin N =>
    match i.1 with
    | 0 => 0
    | n + 1 => coeffZ a n

/-- Truncated coefficient formula for the theta series `θ₀₁`, summing over `k ≤ M`. -/
@[expose] public def theta01Coeff (M : ℕ) (n : ℕ) : ℤ :=
  Finset.sum (Finset.range (M + 1)) fun k =>
    if k ^ 2 = n then (if k = 0 then (1 : ℤ) else 2 * ((-1 : ℤ) ^ k)) else 0

/-- Truncated coefficient formula for the theta series `θ₁₀`, summing over `k ≤ M`. -/
@[expose] public def theta10Coeff (M : ℕ) (n : ℕ) : ℤ :=
  Finset.sum (Finset.range (M + 1)) fun k => if k * (k + 1) = n then (2 : ℤ) else 0

/-- Truncated `r`-series coefficients of `θ₀₁`, with cutoff `M`. -/
@[expose] public def theta01Z (M : ℕ) : List ℤ :=
  List.ofFn fun i : Fin N => theta01Coeff M i.1

/-- Truncated `r`-series coefficients of `θ₁₀`, with cutoff `M`. -/
@[expose] public def theta10Z (M : ℕ) : List ℤ :=
  List.ofFn fun i : Fin N => theta10Coeff M i.1

/-- Truncated `r`-series coefficients of `H₄`, defined as `θ₀₁^4`. -/
@[expose] public def H₄Z (M : ℕ) : List ℤ :=
  powZ (theta01Z M) 4

/-- Truncated `r`-series coefficients of `H₂`, defined as `r * θ₁₀^4`. -/
@[expose] public def H₂Z (M : ℕ) : List ℤ :=
  shift1Z (powZ (theta10Z M) 4)

/-- Truncated `r`-series coefficients of the `psiI` numerator used in Appendix A. -/
@[expose] public def psiInumZ (M : ℕ) : List ℤ :=
  addZ
      (addZ
        (smulZ 7 (mulZ (powZ (H₄Z M) 5) (powZ (H₂Z M) 2)))
        (smulZ 7 (mulZ (powZ (H₄Z M) 6) (H₂Z M))))
      (smulZ 2 (powZ (H₄Z M) 7))

/-- Default theta cutoff used to compute `psiInumCoeffs`. -/
@[expose] public def thetaCutoff : ℕ := 10

/-- Coefficients of the `psiI` numerator, computed using `thetaCutoff`. -/
@[expose] public def psiInumCoeffs : List ℤ :=
  psiInumZ thetaCutoff

/-!
### Rational bounds used by PARI/GP (`10` decimal digits)
-/

/-- Lower rational bound for `π` with `10` decimal digits. -/
@[expose] public def piLower10Q : ℚ := 31415926535 / 10000000000
/-- Upper rational bound for `π` with `10` decimal digits. -/
@[expose] public def piUpper10Q : ℚ := 31415926536 / 10000000000

/-- Lower rational bound for `1/π`, derived from `piUpper10Q`. -/
@[expose] public def invPiLower10Q : ℚ := 1 / piUpper10Q
/-- Upper rational bound for `1/π`, derived from `piLower10Q`. -/
@[expose] public def invPiUpper10Q : ℚ := 1 / piLower10Q

/-- Constant `c = 1/23` used to shift negative coefficients in the truncation bound. -/
@[expose] public def cQ : ℚ := (1 : ℚ) / 23

/-!
### Lower-bound coefficient construction (monomial-wise)
-/

/-- Choose a lower/upper bound for `π` depending on the sign of a coefficient. -/
@[expose] public def choosePi (c : ℚ) : ℚ :=
  if 0 ≤ c then piLower10Q else piUpper10Q

/-- Choose a lower/upper bound for `1/π` depending on the sign of a coefficient. -/
@[expose] public def chooseInvPi (c : ℚ) : ℚ :=
  if 0 ≤ c then invPiLower10Q else invPiUpper10Q

/-- Build a coefficient list of length `N` from an index function. -/
public def mkRcoeffs (f : ℕ → ℚ) : List ℚ :=
  List.ofFn fun i : Fin N => f i.1

/-!
### Coefficients of the numerator as an `r`-series with symbolic `t, π`

For each `i < 100`, the `r^i` coefficient of the numerator can be written as:
`A i * π * t^2 + B i * t + C i / π`.
-/

/-- Normalization factor for the `π * t^2` coefficient list. -/
@[expose] public def piDiv : ℚ := (1 : ℚ) / 28304640
/-- Normalization factor for the `1/π` coefficient list. -/
@[expose] public def invPiDiv : ℚ := (1 : ℚ) / 65520
/-- Scaling factor for the `phi2` contribution to `Ccoeff`. -/
@[expose] public def phi2Scale : ℚ := (36 : ℚ) / 28304640
/-- Scaling factor for the `phi1` contribution to `Bcoeff`. -/
@[expose] public def phi1Scale : ℚ := (-6 : ℚ) / 28304640
/-- Scaling factor for the leading-term `t` contribution inside `Bcoeff`. -/
@[expose] public def leadTScale : ℚ := (-1 : ℚ) / 39
/-- Scaling factor for the leading-term `1/π` contribution inside `Ccoeff`. -/
@[expose] public def leadInvPiScale : ℚ := (10 : ℚ) / 117

/-- Boolean predicate for whether an index is even (used to map `r`-powers to `q`-powers). -/
@[expose] public def isEven (i : ℕ) : Bool := i % 2 = 0
/-- Map an `r`-series index to a `q`-series index (`q = r^2`). -/
@[expose] public def qIdx (i : ℕ) : ℕ := i / 2
/-- Index shift used when reading off `Δ^2` coefficients in the `r`-series. -/
@[expose] public def deltaIdx (i : ℕ) : ℕ := (i / 2) + 1

/-- The `A i` coefficient multiplying `π * t^2` in the `r^i` term of the numerator. -/
@[expose] public def Acoeff (i : ℕ) : ℚ :=
  if isEven i then piDiv * coeffQ phinumQ (qIdx i) else 0

/-- The `B i` coefficient multiplying `t` in the `r^i` term of the numerator. -/
@[expose] public def Bcoeff (i : ℕ) : ℚ :=
  if isEven i then
    (phi1Scale * coeffQ phi1CoreQ (qIdx i)) + (leadTScale * coeffQ DeltaSqQ (deltaIdx i))
  else 0

/-- The `C i` coefficient multiplying `1/π` in the `r^i` term of the numerator. -/
@[expose] public def Ccoeff (i : ℕ) : ℚ :=
  (if isEven i then
      (phi2Scale * coeffQ phi2CoreQ (qIdx i)) + (leadInvPiScale * coeffQ DeltaSqQ (deltaIdx i))
    else 0) +
    (invPiDiv * (psiInumCoeffs.getD i 0 : ℚ))

/-- Convenience sum `Acoeff + Bcoeff + Ccoeff`, used in bound certificates. -/
public def ycoeff (i : ℕ) : ℚ := Acoeff i + Bcoeff i + Ccoeff i

/-!
### PARI/GP-style monomial-wise choices
-/

/-- Choice of `π` bound for the `Acoeff` monomial at index `i`. -/
@[expose] public def piForA (i : ℕ) : ℚ := choosePi (Acoeff i)
/-- Choice of `1/π` bound for the `Ccoeff` monomial at index `i`. -/
@[expose] public def invPiForC (i : ℕ) : ℚ := chooseInvPi (Ccoeff i)

/-- Nonnegative contribution from the `Acoeff` monomial after choosing a `π` bound. -/
@[expose] public def Akeep (i : ℕ) : ℚ :=
  if 0 ≤ Acoeff i then (piForA i) * Acoeff i else 0

/-- Shift the negative part of `Acoeff` forward by two indices (scaled by `cQ^2`). -/
@[expose] public def Ashift (i : ℕ) : ℚ :=
  if Acoeff i < 0 then (cQ ^ (2 : ℕ)) * ((piForA i) * Acoeff i) else 0

/-- Nonnegative contribution from the `Bcoeff` monomial. -/
@[expose] public def Bkeep (i : ℕ) : ℚ :=
  if 0 ≤ Bcoeff i then Bcoeff i else 0

/-- Shift the negative part of `Bcoeff` forward by one index (scaled by `cQ`). -/
@[expose] public def Bshift (i : ℕ) : ℚ :=
  if Bcoeff i < 0 then cQ * Bcoeff i else 0

/-- Contribution from `Ccoeff` after choosing an `1/π` bound. -/
@[expose] public def Ckeep (i : ℕ) : ℚ := (invPiForC i) * Ccoeff i

/-!
Expected coefficient list for `Bleading_trunc`.
-/

/-- Coefficient list expected by the `Bleading_trunc` truncation lemma. -/
public def Bleading_trunc_coeffs_expected : List ℚ :=
  mkRcoeffs fun k =>
    Akeep k +
      (if k + 2 < N then Ashift (k + 2) else 0) +
      Bkeep k +
        (if k + 1 < N then Bshift (k + 1) else 0) +
      Ckeep k

/-!
### Computable variants (avoid `<`/`≤` on `ℚ`)

Lean's kernel reduction does not unfold `Rat.blt`, so order tests on `ℚ` do not reduce.
For small explicit computations (e.g. the `Bleading_trunc_c0Q` certificate), we provide
equivalent variants that branch on integer numerator comparisons, which *do* reduce.
-/

/-- Numerator-based variant of `choosePi` that reduces by kernel computation. -/
@[expose] public def choosePiNum (c : ℚ) : ℚ := if 0 ≤ c.num then piLower10Q else piUpper10Q

/-- Numerator-based variant of `chooseInvPi` that reduces by kernel computation. -/
@[expose] public def chooseInvPiNum (c : ℚ) : ℚ :=
  if 0 ≤ c.num then invPiLower10Q else invPiUpper10Q

/-- Numerator-based variant of `piForA`. -/
@[expose] public def piForANum (i : ℕ) : ℚ := choosePiNum (Acoeff i)
/-- Numerator-based variant of `invPiForC`. -/
@[expose] public def invPiForCNum (i : ℕ) : ℚ := chooseInvPiNum (Ccoeff i)

/-- Numerator-based variant of `Akeep`. -/
@[expose] public def AkeepNum (i : ℕ) : ℚ :=
  if 0 ≤ (Acoeff i).num then (piForANum i) * Acoeff i else 0

/-- Numerator-based variant of `Ashift`. -/
@[expose] public def AshiftNum (i : ℕ) : ℚ :=
  if (Acoeff i).num < 0 then (cQ ^ (2 : ℕ)) * ((piForANum i) * Acoeff i) else 0

/-- Numerator-based variant of `Bkeep`. -/
@[expose] public def BkeepNum (i : ℕ) : ℚ := if 0 ≤ (Bcoeff i).num then Bcoeff i else 0

/-- Numerator-based variant of `Bshift`. -/
@[expose] public def BshiftNum (i : ℕ) : ℚ := if (Bcoeff i).num < 0 then cQ * Bcoeff i else 0

/-- Numerator-based variant of `Ckeep`. -/
@[expose] public def CkeepNum (i : ℕ) : ℚ := (invPiForCNum i) * Ccoeff i

/-- Numerator-based variant of `Bleading_trunc_coeffs_expected`. -/
public def Bleading_trunc_coeffs_expected_num : List ℚ :=
  mkRcoeffs fun k =>
    AkeepNum k +
      (if k + 2 < N then AshiftNum (k + 2) else 0) +
      BkeepNum k +
        (if k + 1 < N then BshiftNum (k + 1) else 0) +
      CkeepNum k

@[simp] public lemma choosePiNum_eq_choosePi (c : ℚ) : choosePiNum c = choosePi c := by
  simp [choosePiNum, choosePi]

@[simp] public lemma chooseInvPiNum_eq_chooseInvPi (c : ℚ) : chooseInvPiNum c = chooseInvPi c := by
  simp [chooseInvPiNum, chooseInvPi]

@[simp] public lemma piForANum_eq_piForA (i : ℕ) : piForANum i = piForA i := by
  simp [piForANum, piForA, choosePiNum_eq_choosePi]

@[simp] public lemma invPiForCNum_eq_invPiForC (i : ℕ) : invPiForCNum i = invPiForC i := by
  simp [invPiForCNum, invPiForC, chooseInvPiNum_eq_chooseInvPi]

public lemma AkeepNum_eq_Akeep (i : ℕ) : AkeepNum i = Akeep i := by
  simp [AkeepNum, Akeep, piForANum_eq_piForA]

public lemma AshiftNum_eq_Ashift (i : ℕ) : AshiftNum i = Ashift i := by
  simp [AshiftNum, Ashift, piForANum_eq_piForA]

public lemma BkeepNum_eq_Bkeep (i : ℕ) : BkeepNum i = Bkeep i := by
  simp [BkeepNum, Bkeep]

public lemma BshiftNum_eq_Bshift (i : ℕ) : BshiftNum i = Bshift i := by
  simp [BshiftNum, Bshift]

public lemma CkeepNum_eq_Ckeep (i : ℕ) : CkeepNum i = Ckeep i := by
  simp [CkeepNum, Ckeep, invPiForCNum_eq_invPiForC]

public lemma Bleading_trunc_coeffs_expected_num_eq :
    Bleading_trunc_coeffs_expected_num = Bleading_trunc_coeffs_expected := by
  dsimp [Bleading_trunc_coeffs_expected_num, Bleading_trunc_coeffs_expected, mkRcoeffs]
  congr 1
  funext i
  simp [AkeepNum_eq_Akeep, AshiftNum_eq_Ashift, BkeepNum_eq_Bkeep, BshiftNum_eq_Bshift,
    CkeepNum_eq_Ckeep]

end SpherePacking.Dim24.AppendixA.BleadingCoeffs
