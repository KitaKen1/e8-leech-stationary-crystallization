-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.DeltaQHalf.Base
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.DeltaQHalf.InvSq


/-!
# `qHalf`-expansion consequences for `H₄` at the cusp `i∞`

This file provides the limit statements for `H₄` needed by the cusp-coefficient computation for
`ψI`.

## Main statements
* `tendsto_H₄_pow6_sub_one_div_qHalf`
* `tendsto_H₄_pow7_sub_one_add_fiftysix_mul_qHalf_div_qHalf_sq`
-/

open scoped Real
open scoped Topology
open scoped UpperHalfPlane

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesAux

section EvenU

open Filter UpperHalfPlane

namespace Deriv

/-- Linear term of `H₄^6` at the cusp: `((H₄ z)^6 - 1) / qHalf z → -48`. -/
public lemma tendsto_H₄_pow6_sub_one_div_qHalf :
    Tendsto
        (fun z : ℍ => ((H₄ z) ^ (6 : ℕ) - (1 : ℂ)) / qHalf z)
        atImInfty (𝓝 (-48 : ℂ)) := by
  have hH4lin :
      Tendsto (fun z : ℍ => (H₄ z - (1 : ℂ)) / qHalf z) atImInfty (𝓝 (-8 : ℂ)) :=
    tendsto_H₄_sub_one_div_qHalf
  have hH4to : Tendsto H₄ atImInfty (𝓝 (1 : ℂ)) := by
    simpa using! (H₄_tendsto_atImInfty : Tendsto H₄ atImInfty (𝓝 (1 : ℂ)))
  have hsum :
      Tendsto
          (fun z : ℍ => Finset.sum (Finset.range 6) (fun k : ℕ => (H₄ z) ^ k))
          atImInfty (𝓝 (6 : ℂ)) := by
    have :
        Tendsto
            (fun z : ℍ => Finset.sum (Finset.range 6) (fun k : ℕ => (H₄ z) ^ k))
            atImInfty (𝓝 (Finset.sum (Finset.range 6) (fun k : ℕ => ((1 : ℂ) ^ k)))) := by
      refine tendsto_finset_sum (Finset.range 6) (fun k hk => ?_)
      simpa using! (hH4to.pow k)
    simpa using! this
  have hEq :
      (fun z : ℍ => ((H₄ z) ^ (6 : ℕ) - (1 : ℂ)) / qHalf z) =
        fun z : ℍ =>
          ((H₄ z - (1 : ℂ)) / qHalf z) *
            (Finset.sum (Finset.range 6) (fun k : ℕ => (H₄ z) ^ k)) := by
    funext z
    have hq0 : qHalf z ≠ 0 := qHalf_ne_zero z
    field_simp [hq0]
    exact Eq.symm (mul_geom_sum (H₄ z) 6)
  have :
      Tendsto
          (fun z : ℍ =>
            ((H₄ z - (1 : ℂ)) / qHalf z) *
              (Finset.sum (Finset.range 6) (fun k : ℕ => (H₄ z) ^ k)))
          atImInfty (𝓝 ((-8 : ℂ) * (6 : ℂ))) := hH4lin.mul hsum
  have hconst : ((-8 : ℂ) * (6 : ℂ)) = (-48 : ℂ) := by norm_num
  simpa [hEq, hconst] using! this

private lemma one_add_pow_seven (u : ℂ) :
    (1 + u) ^ (7 : ℕ) =
      (1 : ℂ) + (7 : ℂ) * u + (21 : ℂ) * (u ^ (2 : ℕ)) +
        (u ^ (3 : ℕ)) *
          ((35 : ℂ) + (35 : ℂ) * u + (21 : ℂ) * (u ^ (2 : ℕ)) + (7 : ℂ) * (u ^ (3 : ℕ)) +
            u ^ (4 : ℕ)) := by
  ring

/-- Quadratic term of `H₄^7` at the cusp, after canceling the linear contribution. -/
public lemma tendsto_H₄_pow7_sub_one_add_fiftysix_mul_qHalf_div_qHalf_sq :
    Tendsto
        (fun z : ℍ => ((H₄ z) ^ (7 : ℕ) - (1 : ℂ) + (56 : ℂ) * qHalf z) / (qHalf z) ^ (2 : ℕ))
        atImInfty (𝓝 (1512 : ℂ)) := by
  let q : ℍ → ℂ := qHalf
  let q2 : ℍ → ℂ := fun z : ℍ => (q z) ^ (2 : ℕ)
  have hq : Tendsto q atImInfty (𝓝 (0 : ℂ)) := tendsto_qHalf_atImInfty
  have hq2 : Tendsto q2 atImInfty (𝓝 (0 : ℂ)) := by
    simpa [q2, q] using! (hq.pow 2)
  -- Truncation error: `H₄ = 1 - 8q + 24q² + q² * e`.
  let e : ℍ → ℂ := fun z : ℍ => (H₄ z - ((1 : ℂ) - (8 : ℂ) * q z + (24 : ℂ) * q2 z)) / q2 z
  have he : Tendsto e atImInfty (𝓝 (0 : ℂ)) := by
    simpa [e, q2, q] using! tendsto_H₄_sub_trunc_div_qHalf_sq
  let v : ℍ → ℂ := fun z : ℍ => (24 : ℂ) + e z
  have hv : Tendsto v atImInfty (𝓝 (24 : ℂ)) := by
    simpa [v] using! (tendsto_const_nhds.add he)
  let u : ℍ → ℂ := fun z : ℍ => (-8 : ℂ) * q z + q2 z * v z
  have hu : Tendsto u atImInfty (𝓝 (0 : ℂ)) := by
    have h1' : Tendsto (fun z : ℍ => (-8 : ℂ) * q z) atImInfty (𝓝 ((-8 : ℂ) * 0)) :=
      tendsto_const_nhds.mul hq
    have h1 : Tendsto (fun z : ℍ => (-8 : ℂ) * q z) atImInfty (𝓝 (0 : ℂ)) := by
      simpa [mul_zero] using! h1'
    have h2 : Tendsto (fun z : ℍ => q2 z * v z) atImInfty (𝓝 (0 : ℂ)) := by
      simpa [mul_zero] using! (hq2.mul hv)
    simpa [u, add_assoc] using! h1.add h2
  have hH4u : ∀ z : ℍ, H₄ z = (1 : ℂ) + u z := by
    intro z
    have hq0 : q2 z ≠ 0 := pow_ne_zero 2 (qHalf_ne_zero z)
    have hsub :
        H₄ z - ((1 : ℂ) - (8 : ℂ) * q z + (24 : ℂ) * q2 z) = q2 z * e z :=
      Eq.symm (mul_div_cancel₀ (H₄ z - (1 - 8 * q z + 24 * q2 z)) hq0)
    have hH4 :
        H₄ z = ((1 : ℂ) - (8 : ℂ) * q z + (24 : ℂ) * q2 z) + q2 z * e z :=
      eq_add_of_sub_eq' hsub
    -- Normalize into `1 + (-8q + q²*v)`.
    have : ((1 : ℂ) - (8 : ℂ) * q z + (24 : ℂ) * q2 z) + q2 z * e z = (1 : ℂ) + u z := by
      simp [u, v, q2]
      ring
    simp [hH4, this]
  have hlin :
      Tendsto (fun z : ℍ => ((7 : ℂ) * u z + (56 : ℂ) * q z) / q2 z) atImInfty (𝓝 (168 : ℂ)) := by
    have hEq :
        (fun z : ℍ => ((7 : ℂ) * u z + (56 : ℂ) * q z) / q2 z) = fun z : ℍ => (7 : ℂ) * v z := by
      funext z
      have hq0 : q z ≠ 0 := qHalf_ne_zero z
      have hq20 : q2 z ≠ 0 := pow_ne_zero 2 hq0
      field_simp [u, q2, hq0, hq20]
      ring
    have : Tendsto (fun z : ℍ => (7 : ℂ) * v z) atImInfty (𝓝 ((7 : ℂ) * (24 : ℂ))) :=
      tendsto_const_nhds.mul hv
    have hconst : ((7 : ℂ) * (24 : ℂ)) = (168 : ℂ) := by norm_num
    simpa [hEq, hconst] using! this
  have hsq :
      Tendsto (fun z : ℍ => (u z) ^ (2 : ℕ) / q2 z) atImInfty (𝓝 (64 : ℂ)) := by
    have hdiv :
        Tendsto (fun z : ℍ => u z / q z) atImInfty (𝓝 (-8 : ℂ)) := by
      have hEq : (fun z : ℍ => u z / q z) = fun z : ℍ => (-8 : ℂ) + q z * v z := by
        funext z
        have hq0 : q z ≠ 0 := qHalf_ne_zero z
        field_simp [u, hq0]
        ring
      have : Tendsto (fun z : ℍ => (-8 : ℂ) + q z * v z) atImInfty (𝓝 ((-8 : ℂ) + 0)) :=
        by
          have hqv : Tendsto (fun z : ℍ => q z * v z) atImInfty (𝓝 (0 : ℂ)) := by
            simpa [mul_zero] using! (hq.mul hv)
          simpa using! (tendsto_const_nhds.add hqv)
      simpa [hEq] using! this
    have hdiv2 : Tendsto (fun z : ℍ => (u z / q z) ^ (2 : ℕ)) atImInfty (𝓝 ((-8 : ℂ) ^ (2 : ℕ))) :=
      hdiv.pow 2
    have hEq :
        (fun z : ℍ => (u z) ^ (2 : ℕ) / q2 z) = fun z : ℍ => (u z / q z) ^ (2 : ℕ) := by
      funext z
      exact Eq.symm (div_pow (u z) (q z) 2)
    have hconst : ((-8 : ℂ) ^ (2 : ℕ)) = (64 : ℂ) := by norm_num
    simpa [hEq, hconst] using!
      hdiv2
  have hP :
      Tendsto
          (fun z : ℍ =>
            (u z) ^ (3 : ℕ) *
              ((35 : ℂ) + (35 : ℂ) * u z + (21 : ℂ) * (u z) ^ (2 : ℕ) + (7 : ℂ) * (u z) ^ (3 : ℕ) +
                  (u z) ^ (4 : ℕ)) /
              q2 z)
          atImInfty (𝓝 (0 : ℂ)) := by
    have hpoly :
        Tendsto
            (fun z : ℍ =>
              (35 : ℂ) + (35 : ℂ) * u z + (21 : ℂ) * (u z) ^ (2 : ℕ) + (7 : ℂ) * (u z) ^ (3 : ℕ) +
                (u z) ^ (4 : ℕ))
            atImInfty (𝓝 (35 : ℂ)) := by
      have h2 : Tendsto (fun z : ℍ => (u z) ^ (2 : ℕ)) atImInfty (𝓝 (0 : ℂ)) := by
        simpa using! (hu.pow 2)
      have h3 : Tendsto (fun z : ℍ => (u z) ^ (3 : ℕ)) atImInfty (𝓝 (0 : ℂ)) := by
        simpa using! (hu.pow 3)
      have h4 : Tendsto (fun z : ℍ => (u z) ^ (4 : ℕ)) atImInfty (𝓝 (0 : ℂ)) := by
        simpa using! (hu.pow 4)
      have h35u : Tendsto (fun z : ℍ => (35 : ℂ) * u z) atImInfty (𝓝 (0 : ℂ)) := by
        simpa [mul_zero] using! (tendsto_const_nhds.mul hu)
      have h21u2 : Tendsto (fun z : ℍ => (21 : ℂ) * (u z) ^ (2 : ℕ)) atImInfty (𝓝 (0 : ℂ)) := by
        simpa [mul_zero] using! (tendsto_const_nhds.mul h2)
      have h7u3 :
          Tendsto (fun z : ℍ => (7 : ℂ) * (u z) ^ (3 : ℕ)) atImInfty (𝓝 (0 : ℂ)) := by
        simpa [mul_zero] using! (tendsto_const_nhds.mul h3)
      have :
          Tendsto
              (fun z : ℍ =>
                (35 : ℂ) +
                  ((35 : ℂ) * u z +
                    ((21 : ℂ) * (u z) ^ (2 : ℕ) + ((7 : ℂ) * (u z) ^ (3 : ℕ) + (u z) ^ (4 : ℕ)))))
              atImInfty (𝓝 ((35 : ℂ) + (0 + (0 + (0 + 0))))) := by
        exact tendsto_const_nhds.add (h35u.add (h21u2.add (h7u3.add h4)))
      simpa [add_assoc, add_left_comm, add_comm] using!
        this
    have hcore : Tendsto (fun z : ℍ => (u z) ^ (3 : ℕ) / q2 z) atImInfty (𝓝 (0 : ℂ)) := by
      have hEq :
          (fun z : ℍ => (u z) ^ (3 : ℕ) / q2 z) =
            fun z : ℍ => (u z) * ((u z) ^ (2 : ℕ) / q2 z) := by
        funext z
        have hq0 : q2 z ≠ 0 := pow_ne_zero 2 (qHalf_ne_zero z)
        field_simp [q2, hq0]
      have :
          Tendsto (fun z : ℍ => (u z) * ((u z) ^ (2 : ℕ) / q2 z)) atImInfty (𝓝 (0 * (64 : ℂ))) :=
        hu.mul hsq
      simpa [hEq, mul_zero] using! this
    have hEq :
        (fun z : ℍ =>
            (u z) ^ (3 : ℕ) *
                ((35 : ℂ) + (35 : ℂ) * u z + (21 : ℂ) * (u z) ^ (2 : ℕ) +
                    (7 : ℂ) * (u z) ^ (3 : ℕ) + (u z) ^ (4 : ℕ)) /
              q2 z) =
          fun z : ℍ =>
            ((u z) ^ (3 : ℕ) / q2 z) *
              ((35 : ℂ) + (35 : ℂ) * u z + (21 : ℂ) * (u z) ^ (2 : ℕ) +
                (7 : ℂ) * (u z) ^ (3 : ℕ) + (u z) ^ (4 : ℕ)) := by
      ring_nf
    have :
        Tendsto
            (fun z : ℍ =>
              ((u z) ^ (3 : ℕ) / q2 z) *
                ((35 : ℂ) + (35 : ℂ) * u z + (21 : ℂ) * (u z) ^ (2 : ℕ) +
                  (7 : ℂ) * (u z) ^ (3 : ℕ) + (u z) ^ (4 : ℕ)))
        atImInfty (𝓝 (0 * (35 : ℂ))) := hcore.mul hpoly
    simpa [hEq, mul_zero] using! this
  have hmain :
      Tendsto
          (fun z : ℍ => ((H₄ z) ^ (7 : ℕ) - (1 : ℂ) + (56 : ℂ) * q z) / q2 z)
          atImInfty (𝓝 ((168 : ℂ) + (21 : ℂ) * (64 : ℂ) + 0)) := by
    have hEq :
        (fun z : ℍ => ((H₄ z) ^ (7 : ℕ) - (1 : ℂ) + (56 : ℂ) * q z) / q2 z) =
          fun z : ℍ =>
            (((7 : ℂ) * u z + (56 : ℂ) * q z) / q2 z) +
              ((21 : ℂ) * (u z) ^ (2 : ℕ) / q2 z) +
                ((u z) ^ (3 : ℕ) *
                    ((35 : ℂ) + (35 : ℂ) * u z + (21 : ℂ) * (u z) ^ (2 : ℕ) +
                        (7 : ℂ) * (u z) ^ (3 : ℕ) + (u z) ^ (4 : ℕ)) /
                  q2 z) := by
      funext z
      have hq0 : q2 z ≠ 0 := pow_ne_zero 2 (qHalf_ne_zero z)
      -- Expand `(H₄ z)^7` around `1 + u z`.
      have hpow :
          ((H₄ z) ^ (7 : ℕ)) = ((1 : ℂ) + u z) ^ (7 : ℕ) := by
        simp [hH4u z]
      -- Normalize to a polynomial in `u z`.
      simp [hpow, one_add_pow_seven, q2, q]
      ring
    have h21 :
        Tendsto (fun z : ℍ => (21 : ℂ) * (u z) ^ (2 : ℕ) / q2 z) atImInfty
          (𝓝 ((21 : ℂ) * (64 : ℂ))) := by
      have hEq' :
          (fun z : ℍ => (21 : ℂ) * (u z) ^ (2 : ℕ) / q2 z) =
            fun z : ℍ => (21 : ℂ) * ((u z) ^ (2 : ℕ) / q2 z) := by
        funext z
        have hq0 : q2 z ≠ 0 := pow_ne_zero 2 (qHalf_ne_zero z)
        field_simp [hq0]
      have :
          Tendsto (fun z : ℍ => (21 : ℂ) * ((u z) ^ (2 : ℕ) / q2 z)) atImInfty
            (𝓝 ((21 : ℂ) * (64 : ℂ))) :=
        tendsto_const_nhds.mul hsq
      simpa [hEq'] using!
        this
    have :
        Tendsto
            (fun z : ℍ =>
              (((7 : ℂ) * u z + (56 : ℂ) * q z) / q2 z) + ((21 : ℂ) * (u z) ^ (2 : ℕ) / q2 z) +
                ((u z) ^ (3 : ℕ) *
                      ((35 : ℂ) + (35 : ℂ) * u z + (21 : ℂ) * (u z) ^ (2 : ℕ) +
                          (7 : ℂ) * (u z) ^ (3 : ℕ) + (u z) ^ (4 : ℕ)) /
                    q2 z))
            atImInfty (𝓝 ((168 : ℂ) + ((21 : ℂ) * (64 : ℂ)) + 0)) :=
      (hlin.add h21).add hP
    simpa [hEq, add_assoc] using! this
  have hconst : ((168 : ℂ) + (21 : ℂ) * (64 : ℂ) + 0) = (1512 : ℂ) := by norm_num
  simpa [q2, q, hconst] using! hmain

end SpecialValuesAux.EvenU.Deriv
end

end SpherePacking.Dim24
