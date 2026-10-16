-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.F.Laplace.B.SubLeadingBounds.DeltaDivQLowerBound

/-!
# Bound for the exact truncation term

This file bounds the exact truncation term `Bleading_exact_trunc` that appears in the
subtract-leading Laplace continuation of the `BKernel` integral.

## Main statement
* `abs_Bleading_exact_trunc_le`

-/

namespace SpherePacking.Dim24.LaplaceBSubLeadingBounds

noncomputable section

open scoped BigOperators Real Topology
open Complex Filter UpperHalfPlane

open AppendixA


lemma Bleading_exact_coeff_eq_zero_of_lt4 (t : ℝ) (i : ℕ) (hi : i < 4) :
    Bleading_exact_coeff t i = 0 := by
  -- The first four coefficients are `0` by the explicit coefficient tables from Appendix A.
  -- We avoid `interval_cases` here, since it can discharge some cases immediately and then
  -- subsequent tactics may run in a no-goal state.
  revert hi
  induction i with
  | zero =>
      intro _
      simp
        [ List.getD
        , varphiNumCoeffsZ_table
        , phi1CoreCoeffsZ_table
        , phi2CoreCoeffsZ_table
        , deltaHatSqCoeffsZ_table
        , psiInumCoeffs_table
        , SpherePacking.Dim24.AppendixA.psiInumCoeffs_get?_getD_eq
        , Bleading_exact_coeff
        , BleadingCoeffs.Acoeff
        , BleadingCoeffs.Bcoeff
        , BleadingCoeffs.Ccoeff
        , BleadingCoeffs.isEven
        , BleadingCoeffs.qIdx
        , BleadingCoeffs.deltaIdx
        , BleadingCoeffs.QN
        , BleadingCoeffs.piDiv
        , BleadingCoeffs.invPiDiv
        , BleadingCoeffs.phi1Scale
        , BleadingCoeffs.phi2Scale
        , BleadingCoeffs.leadTScale
        , BleadingCoeffs.leadInvPiScale
        , BleadingCoeffs.coeffQ_phinumQ_eq_table
        , BleadingCoeffs.coeffQ_phi1CoreQ_eq_table
        , BleadingCoeffs.coeffQ_phi2CoreQ_eq_table
        , BleadingCoeffs.coeffQ_DeltaSqQ_eq_table
        ]
      all_goals ring_nf
  | succ i ih =>
      intro hi
      cases i with
      | zero =>
          simp
              [ List.getD
              , varphiNumCoeffsZ_table
              , phi1CoreCoeffsZ_table
              , phi2CoreCoeffsZ_table
              , deltaHatSqCoeffsZ_table
              , psiInumCoeffs_table
              , SpherePacking.Dim24.AppendixA.psiInumCoeffs_get?_getD_eq
              , Bleading_exact_coeff
              , BleadingCoeffs.Acoeff
              , BleadingCoeffs.Bcoeff
              , BleadingCoeffs.Ccoeff
              , BleadingCoeffs.isEven
              , BleadingCoeffs.qIdx
              , BleadingCoeffs.deltaIdx
              , BleadingCoeffs.QN
              , BleadingCoeffs.piDiv
              , BleadingCoeffs.invPiDiv
              , BleadingCoeffs.phi1Scale
              , BleadingCoeffs.phi2Scale
              , BleadingCoeffs.leadTScale
              , BleadingCoeffs.leadInvPiScale
              , BleadingCoeffs.coeffQ_phinumQ_eq_table
              , BleadingCoeffs.coeffQ_phi1CoreQ_eq_table
              , BleadingCoeffs.coeffQ_phi2CoreQ_eq_table
              , BleadingCoeffs.coeffQ_DeltaSqQ_eq_table
              ]
            at *
      | succ i =>
          cases i with
          | zero =>
              simp
                  [ List.getD
                  , varphiNumCoeffsZ_table
                  , phi1CoreCoeffsZ_table
                  , phi2CoreCoeffsZ_table
                  , deltaHatSqCoeffsZ_table
                  , psiInumCoeffs_table
                  , SpherePacking.Dim24.AppendixA.psiInumCoeffs_get?_getD_eq
                  , Bleading_exact_coeff
                  , BleadingCoeffs.Acoeff
                  , BleadingCoeffs.Bcoeff
                  , BleadingCoeffs.Ccoeff
                  , BleadingCoeffs.isEven
                  , BleadingCoeffs.qIdx
                  , BleadingCoeffs.deltaIdx
                  , BleadingCoeffs.QN
                  , BleadingCoeffs.piDiv
                  , BleadingCoeffs.invPiDiv
                  , BleadingCoeffs.phi1Scale
                  , BleadingCoeffs.phi2Scale
                  , BleadingCoeffs.leadTScale
                  , BleadingCoeffs.leadInvPiScale
                  , BleadingCoeffs.coeffQ_phinumQ_eq_table
                  , BleadingCoeffs.coeffQ_phi1CoreQ_eq_table
                  , BleadingCoeffs.coeffQ_phi2CoreQ_eq_table
                  , BleadingCoeffs.coeffQ_DeltaSqQ_eq_table
                  ]
                at *
              all_goals ring_nf
          | succ i =>
              cases i with
              | zero =>
                  simp
                      [ List.getD
                      , varphiNumCoeffsZ_table
                      , phi1CoreCoeffsZ_table
                      , phi2CoreCoeffsZ_table
                      , deltaHatSqCoeffsZ_table
                      , psiInumCoeffs_table
                      , SpherePacking.Dim24.AppendixA.psiInumCoeffs_get?_getD_eq
                      , Bleading_exact_coeff
                      , BleadingCoeffs.Acoeff
                      , BleadingCoeffs.Bcoeff
                      , BleadingCoeffs.Ccoeff
                      , BleadingCoeffs.isEven
                      , BleadingCoeffs.qIdx
                      , BleadingCoeffs.deltaIdx
                      , BleadingCoeffs.QN
                      , BleadingCoeffs.piDiv
                      , BleadingCoeffs.invPiDiv
                      , BleadingCoeffs.phi1Scale
                      , BleadingCoeffs.phi2Scale
                      , BleadingCoeffs.leadTScale
                      , BleadingCoeffs.leadInvPiScale
                      , BleadingCoeffs.coeffQ_phinumQ_eq_table
                      , BleadingCoeffs.coeffQ_phi1CoreQ_eq_table
                      , BleadingCoeffs.coeffQ_phi2CoreQ_eq_table
                      , BleadingCoeffs.coeffQ_DeltaSqQ_eq_table
                      ]
                    at *
              | succ i =>
                  have hge : 4 ≤ Nat.succ (Nat.succ (Nat.succ (Nat.succ i))) :=
                    Nat.succ_le_succ
                      (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le i))))
                  exact (False.elim (Nat.not_lt_of_ge hge hi))

/-- Bound for the exact truncation term `Bleading_exact_trunc t` on the range `t ≥ 1`. -/
public lemma abs_Bleading_exact_trunc_le (t : ℝ) (ht : 1 ≤ t) :
    |Bleading_exact_trunc t| ≤
      ((((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Acoeff i : ℝ)|) *
              Real.pi * t ^ (2 : ℕ)) +
              ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Bcoeff i : ℝ)|) * t)) +
            ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Ccoeff i : ℝ)|) *
              (1 / Real.pi))) *
          (r t) ^ (4 : ℕ) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hr_le_one : r t ≤ 1 := by
    have : (-Real.pi * t) ≤ 0 := by nlinarith [Real.pi_pos, (show 0 ≤ t from le_of_lt ht0)]
    simpa [r] using! (Real.exp_le_one_iff.2 this)
  have hr0 : 0 ≤ r t := (Real.exp_pos _).le
  -- Expand the truncation and drop the first four (zero) coefficients.
  have hsum_eq :
      Bleading_exact_trunc t =
        ∑ i ∈ Finset.range BleadingCoeffs.N,
          Bleading_exact_coeff t i * (r t) ^ i := by
    simp [Bleading_exact_trunc]
  -- Triangle inequality for finite sums.
  have htri :
      |∑ i ∈ Finset.range BleadingCoeffs.N, Bleading_exact_coeff t i * (r t) ^ i| ≤
        ∑ i ∈ Finset.range BleadingCoeffs.N, |Bleading_exact_coeff t i * (r t) ^ i| :=
    Finset.abs_sum_le_sum_abs _ _
  -- Bound each term by factoring out `(r t)^4`.
  have hterm :
      ∀ i, i ∈ Finset.range BleadingCoeffs.N →
        |Bleading_exact_coeff t i * (r t) ^ i| ≤
          (|(BleadingCoeffs.Acoeff i : ℝ)| * Real.pi * t ^ (2 : ℕ) +
                |(BleadingCoeffs.Bcoeff i : ℝ)| * t +
              |(BleadingCoeffs.Ccoeff i : ℝ)| * (1 / Real.pi)) *
            (r t) ^ (4 : ℕ) := by
    intro i hiN
    by_cases hi4 : i < 4
    · have hcoeff0 : Bleading_exact_coeff t i = 0 :=
        Bleading_exact_coeff_eq_zero_of_lt4 (t := t) (i := i) hi4
      have hnonneg :
          0 ≤
            (|(BleadingCoeffs.Acoeff i : ℝ)| * Real.pi * t ^ (2 : ℕ) +
                  |(BleadingCoeffs.Bcoeff i : ℝ)| * t +
                    |(BleadingCoeffs.Ccoeff i : ℝ)| * (1 / Real.pi)) * (r t) ^ (4 : ℕ) := by
        positivity [Real.pi_pos, (show 0 ≤ t from le_of_lt ht0)]
      simpa [hcoeff0] using! hnonneg
    · have hi4' : 4 ≤ i := le_of_not_gt hi4
      have hrpow : (r t) ^ i ≤ (r t) ^ (4 : ℕ) := by
        -- `r t ∈ [0,1]` and `4 ≤ i`.
        simpa using! (pow_le_pow_of_le_one hr0 hr_le_one hi4')
      have habs :
          |Bleading_exact_coeff t i * (r t) ^ i| =
            |Bleading_exact_coeff t i| * (r t) ^ i := by
        simp [abs_mul, abs_pow, abs_of_nonneg hr0]
      have hcoeff_le :
          |Bleading_exact_coeff t i| ≤
            |(BleadingCoeffs.Acoeff i : ℝ)| * Real.pi * t ^ (2 : ℕ) +
              |(BleadingCoeffs.Bcoeff i : ℝ)| * t +
                |(BleadingCoeffs.Ccoeff i : ℝ)| * (1 / Real.pi) := by
        -- Expand `Bleading_exact_coeff` and bound by triangle inequality.
        have hA : |(BleadingCoeffs.Acoeff i : ℝ) * Real.pi * t ^ (2 : ℕ)| =
            |(BleadingCoeffs.Acoeff i : ℝ)| * Real.pi * t ^ (2 : ℕ) := by
          simp [abs_mul, abs_of_nonneg Real.pi_pos.le,
            abs_of_nonneg (by
              positivity : (0 : ℝ) ≤ t ^ (2 : ℕ))]
        have hB : |(BleadingCoeffs.Bcoeff i : ℝ) * t| = |(BleadingCoeffs.Bcoeff i : ℝ)| * t := by
          simp [abs_mul, abs_of_nonneg (show 0 ≤ t from le_of_lt ht0)]
        have hC : |(BleadingCoeffs.Ccoeff i : ℝ) * (1 / Real.pi)| =
            |(BleadingCoeffs.Ccoeff i : ℝ)| * (1 / Real.pi) := by
          have hpiInv : (0 : ℝ) ≤ (1 / Real.pi) := by positivity [Real.pi_pos]
          calc
            |(BleadingCoeffs.Ccoeff i : ℝ) * (1 / Real.pi)| =
                |(BleadingCoeffs.Ccoeff i : ℝ)| * |(1 / Real.pi : ℝ)| := by
                  simp [abs_mul]
            _ = |(BleadingCoeffs.Ccoeff i : ℝ)| * (1 / Real.pi) := by
                  rw [abs_of_nonneg hpiInv]
        exact
          calc
            |Bleading_exact_coeff t i| =
                |(BleadingCoeffs.Acoeff i : ℝ) * Real.pi * t ^ (2 : ℕ) +
                    (BleadingCoeffs.Bcoeff i : ℝ) * t +
                      (BleadingCoeffs.Ccoeff i : ℝ) * (1 / Real.pi)| := by
                    simp [Bleading_exact_coeff, add_assoc]
            _ ≤ |(BleadingCoeffs.Acoeff i : ℝ) * Real.pi * t ^ (2 : ℕ)| +
                  |(BleadingCoeffs.Bcoeff i : ℝ) * t +
                      (BleadingCoeffs.Ccoeff i : ℝ) * (1 / Real.pi)| := by
                  simpa [add_assoc] using!
                    (abs_add_le
                      ((BleadingCoeffs.Acoeff i : ℝ) * Real.pi * t ^ (2 : ℕ))
                      ((BleadingCoeffs.Bcoeff i : ℝ) * t +
                        (BleadingCoeffs.Ccoeff i : ℝ) * (1 / Real.pi)))
            _ ≤ |(BleadingCoeffs.Acoeff i : ℝ) * Real.pi * t ^ (2 : ℕ)| +
                  (|(BleadingCoeffs.Bcoeff i : ℝ) * t| +
                    |(BleadingCoeffs.Ccoeff i : ℝ) * (1 / Real.pi)|) := by
                  -- Apply the triangle inequality to the inner sum, then rearrange.
                  have hbc :
                      |(BleadingCoeffs.Bcoeff i : ℝ) * t +
                          (BleadingCoeffs.Ccoeff i : ℝ) * (1 / Real.pi)| ≤
                        |(BleadingCoeffs.Bcoeff i : ℝ) * t| +
                          |(BleadingCoeffs.Ccoeff i : ℝ) * (1 / Real.pi)| :=
                    abs_add_le _ _
                  exact (add_le_add_iff_left |↑(BleadingCoeffs.Acoeff i) * π * t ^ 2|).mpr hbc
            _ = _ := by
                  rw [hA, hB, hC]
                  simp [add_assoc]
      have hpoly_nonneg :
          0 ≤
            (|(BleadingCoeffs.Acoeff i : ℝ)| * Real.pi * t ^ (2 : ℕ) +
                |(BleadingCoeffs.Bcoeff i : ℝ)| * t +
                  |(BleadingCoeffs.Ccoeff i : ℝ)| * (1 / Real.pi)) := by
        positivity [Real.pi_pos, (show 0 ≤ t from le_trans (by norm_num) ht)]
      have hcoeff_mul :
          |Bleading_exact_coeff t i| * (r t) ^ i ≤
            (|(BleadingCoeffs.Acoeff i : ℝ)| * Real.pi * t ^ (2 : ℕ) +
                |(BleadingCoeffs.Bcoeff i : ℝ)| * t +
                  |(BleadingCoeffs.Ccoeff i : ℝ)| * (1 / Real.pi)) *
              (r t) ^ i :=
        mul_le_mul_of_nonneg_right hcoeff_le (pow_nonneg hr0 _)
      have hpow_mul :
          (|(BleadingCoeffs.Acoeff i : ℝ)| * Real.pi * t ^ (2 : ℕ) +
                |(BleadingCoeffs.Bcoeff i : ℝ)| * t +
                  |(BleadingCoeffs.Ccoeff i : ℝ)| * (1 / Real.pi)) *
              (r t) ^ i ≤
            (|(BleadingCoeffs.Acoeff i : ℝ)| * Real.pi * t ^ (2 : ℕ) +
                |(BleadingCoeffs.Bcoeff i : ℝ)| * t +
                  |(BleadingCoeffs.Ccoeff i : ℝ)| * (1 / Real.pi)) *
              (r t) ^ (4 : ℕ) :=
        mul_le_mul_of_nonneg_left hrpow hpoly_nonneg
      have hmain :
          |Bleading_exact_coeff t i| * (r t) ^ i ≤
            (|(BleadingCoeffs.Acoeff i : ℝ)| * Real.pi * t ^ (2 : ℕ) +
                |(BleadingCoeffs.Bcoeff i : ℝ)| * t +
                  |(BleadingCoeffs.Ccoeff i : ℝ)| * (1 / Real.pi)) *
              (r t) ^ (4 : ℕ) :=
        le_trans hcoeff_mul hpow_mul
      exact le_trans (le_of_eq habs) hmain
  -- Sum the termwise bounds.
  have hsum :
      ∑ i ∈ Finset.range BleadingCoeffs.N, |Bleading_exact_coeff t i * (r t) ^ i| ≤
        ((((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Acoeff i : ℝ)|) *
                Real.pi * t ^ (2 : ℕ)) +
                ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Bcoeff i : ℝ)|) * t)) +
              ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Ccoeff i : ℝ)|) *
                (1 / Real.pi))) *
            (r t) ^ (4 : ℕ) := by
    -- Pull out `(r t)^4` and distribute sums.
    have :
        ∑ i ∈ Finset.range BleadingCoeffs.N, |Bleading_exact_coeff t i * (r t) ^ i| ≤
          ∑ i ∈ Finset.range BleadingCoeffs.N,
            (|(BleadingCoeffs.Acoeff i : ℝ)| * Real.pi * t ^ (2 : ℕ) +
                |(BleadingCoeffs.Bcoeff i : ℝ)| * t +
                  |(BleadingCoeffs.Ccoeff i : ℝ)| * (1 / Real.pi)) * (r t) ^ (4 : ℕ) :=
      Finset.sum_le_sum hterm
    -- Rewrite the RHS sum.
    have hrewrite :
          (∑ i ∈ Finset.range BleadingCoeffs.N,
              (|(BleadingCoeffs.Acoeff i : ℝ)| * Real.pi * t ^ (2 : ℕ) +
                  |(BleadingCoeffs.Bcoeff i : ℝ)| * t +
                    |(BleadingCoeffs.Ccoeff i : ℝ)| * (1 / Real.pi)) * (r t) ^ (4 : ℕ)) =
            ((((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Acoeff i : ℝ)|) *
                    Real.pi * t ^ (2 : ℕ)) +
                    ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Bcoeff i : ℝ)|) * t)) +
                  ((∑ i ∈ Finset.range BleadingCoeffs.N, |(BleadingCoeffs.Ccoeff i : ℝ)|) *
                    (1 / Real.pi))) *
                (r t) ^ (4 : ℕ) := by
      -- Factor out `(r t)^4` and use linearity of sums.
      set S : Finset ℕ := Finset.range BleadingCoeffs.N
      set rt4 : ℝ := (r t) ^ (4 : ℕ)
      set constA : ℝ := Real.pi * t ^ (2 : ℕ)
      set constB : ℝ := t
      set constC : ℝ := (1 / Real.pi)
      -- Pull `rt4` out of the sum.
      have hrt4 :
          (∑ i ∈ S,
                (|(BleadingCoeffs.Acoeff i : ℝ)| * constA +
                    |(BleadingCoeffs.Bcoeff i : ℝ)| * constB +
                      |(BleadingCoeffs.Ccoeff i : ℝ)| * constC) * rt4) =
            (∑ i ∈ S,
                (|(BleadingCoeffs.Acoeff i : ℝ)| * constA +
                    |(BleadingCoeffs.Bcoeff i : ℝ)| * constB +
                      |(BleadingCoeffs.Ccoeff i : ℝ)| * constC)) * rt4 := by
        simpa using!
          (Eq.symm
            (Finset.sum_mul (s := S)
              (f := fun i =>
                (|(BleadingCoeffs.Acoeff i : ℝ)| * constA +
                    |(BleadingCoeffs.Bcoeff i : ℝ)| * constB +
                      |(BleadingCoeffs.Ccoeff i : ℝ)| * constC))
              rt4))
      -- Split the sum into three sums.
      have hsplit :
          (∑ i ∈ S,
                (|(BleadingCoeffs.Acoeff i : ℝ)| * constA +
                    |(BleadingCoeffs.Bcoeff i : ℝ)| * constB +
                      |(BleadingCoeffs.Ccoeff i : ℝ)| * constC)) =
            (∑ i ∈ S, |(BleadingCoeffs.Acoeff i : ℝ)| * constA) +
              ((∑ i ∈ S, |(BleadingCoeffs.Bcoeff i : ℝ)| * constB) +
                (∑ i ∈ S, |(BleadingCoeffs.Ccoeff i : ℝ)| * constC)) := by
        simp [add_assoc, Finset.sum_add_distrib]
      -- Factor the constants out of each sum.
      have hA :
          (∑ i ∈ S, |(BleadingCoeffs.Acoeff i : ℝ)| * constA) =
            (∑ i ∈ S, |(BleadingCoeffs.Acoeff i : ℝ)|) * constA := by
        simpa using!
          (Eq.symm
            (Finset.sum_mul (s := S)
              (f := fun i => |(BleadingCoeffs.Acoeff i : ℝ)|) constA))
      have hB :
          (∑ i ∈ S, |(BleadingCoeffs.Bcoeff i : ℝ)| * constB) =
            (∑ i ∈ S, |(BleadingCoeffs.Bcoeff i : ℝ)|) * constB := by
        simpa using!
          (Eq.symm
            (Finset.sum_mul (s := S)
              (f := fun i => |(BleadingCoeffs.Bcoeff i : ℝ)|) constB))
      have hC :
          (∑ i ∈ S, |(BleadingCoeffs.Ccoeff i : ℝ)| * constC) =
            (∑ i ∈ S, |(BleadingCoeffs.Ccoeff i : ℝ)|) * constC := by
        simpa using!
          (Eq.symm
            (Finset.sum_mul (s := S)
              (f := fun i => |(BleadingCoeffs.Ccoeff i : ℝ)|) constC))
      have hfinal :
          (∑ i ∈ S,
                (|(BleadingCoeffs.Acoeff i : ℝ)| * constA +
                    |(BleadingCoeffs.Bcoeff i : ℝ)| * constB +
                      |(BleadingCoeffs.Ccoeff i : ℝ)| * constC) * rt4) =
            ((∑ i ∈ S, |(BleadingCoeffs.Acoeff i : ℝ)|) * constA +
                (∑ i ∈ S, |(BleadingCoeffs.Bcoeff i : ℝ)|) * constB +
                  (∑ i ∈ S, |(BleadingCoeffs.Ccoeff i : ℝ)|) * constC) *
              rt4 := by
        calc
          (∑ i ∈ S,
                (|(BleadingCoeffs.Acoeff i : ℝ)| * constA +
                    |(BleadingCoeffs.Bcoeff i : ℝ)| * constB +
                      |(BleadingCoeffs.Ccoeff i : ℝ)| * constC) * rt4) =
              (∑ i ∈ S,
                    (|(BleadingCoeffs.Acoeff i : ℝ)| * constA +
                        |(BleadingCoeffs.Bcoeff i : ℝ)| * constB +
                          |(BleadingCoeffs.Ccoeff i : ℝ)| * constC)) *
                  rt4 := hrt4
          _ =
              ((∑ i ∈ S, |(BleadingCoeffs.Acoeff i : ℝ)| * constA) +
                  ((∑ i ∈ S, |(BleadingCoeffs.Bcoeff i : ℝ)| * constB) +
                    (∑ i ∈ S, |(BleadingCoeffs.Ccoeff i : ℝ)| * constC))) *
                rt4 := by
                simp [hsplit]
          _ =
              (((∑ i ∈ S, |(BleadingCoeffs.Acoeff i : ℝ)|) * constA) +
                  (((∑ i ∈ S, |(BleadingCoeffs.Bcoeff i : ℝ)|) * constB) +
                    ((∑ i ∈ S, |(BleadingCoeffs.Ccoeff i : ℝ)|) * constC))) *
                rt4 := by
                simp [hA, hB, hC]
          _ =
              ((∑ i ∈ S, |(BleadingCoeffs.Acoeff i : ℝ)|) * constA +
                  (∑ i ∈ S, |(BleadingCoeffs.Bcoeff i : ℝ)|) * constB +
                    (∑ i ∈ S, |(BleadingCoeffs.Ccoeff i : ℝ)|) * constC) *
                rt4 := by
                simp [add_assoc]
      simpa [S, rt4, constA, constB, constC, mul_assoc, add_assoc] using! hfinal
    exact le_trans this (le_of_eq hrewrite)
  -- Combine.
  rw [hsum_eq]
  exact htri.trans hsum

end

end SpherePacking.Dim24.LaplaceBSubLeadingBounds
