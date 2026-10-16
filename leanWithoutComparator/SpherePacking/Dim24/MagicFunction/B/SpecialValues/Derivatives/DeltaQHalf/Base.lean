-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.H2H4.H2
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.H2H4.H4
import SpherePacking.Dim24.MagicFunction.B.Defs.PsiExtensions


/-!
# Cusp expansion of `Δ` to order `qHalf^2`

We record the first `qHalf^2` term of `Δ` at the cusp `i∞` in the normalized form
`(Δ / qHalf^2 - 1) / qHalf^2 → -24`.

## Main statements
* `tendsto_Delta_div_qHalf_sq_sub_one_div_qHalf_sq`
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

/-- As `Im z → ∞`, the normalized error `(Δ z / qHalf(z)^2 - 1) / qHalf(z)^2` tends to `-24`. -/
public lemma tendsto_Delta_div_qHalf_sq_sub_one_div_qHalf_sq :
    Tendsto (fun z : ℍ => ((Δ z) / (qHalf z) ^ (2 : ℕ) - (1 : ℂ)) / (qHalf z) ^ (2 : ℕ))
      atImInfty (𝓝 (-24 : ℂ)) := by
  -- Use `Δ = (H₂*H₃*H₄)^2 / 256` and compute the first nontrivial coefficient.
  let q2 : ℍ → ℂ := fun z : ℍ => (qHalf z) ^ (2 : ℕ)
  have hq : Tendsto q2 atImInfty (𝓝 (0 : ℂ)) := by
    simpa [q2] using! tendsto_qHalf_sq_atImInfty
  let A : ℍ → ℂ := fun z : ℍ => (H₂ z / qHalf z) / (16 : ℂ)
  let B : ℍ → ℂ := fun z : ℍ => (H₃ z) * (H₄ z)
  have hA :
      Tendsto (fun z : ℍ => (A z - (1 : ℂ)) / q2 z) atImInfty (𝓝 (4 : ℂ)) := by
    have hH2 := tendsto_H₂_div_qHalf_sub_const_div_qHalf_sq
    have hEq :
        (fun z : ℍ => (A z - (1 : ℂ)) / q2 z) =
          fun z : ℍ => ((H₂ z / qHalf z - (16 : ℂ)) / q2 z) / (16 : ℂ) := by
      funext z
      ring
      -- `field_simp` closes this goal.
    have hA' :
        Tendsto (fun z : ℍ => ((H₂ z / qHalf z - (16 : ℂ)) / q2 z) / (16 : ℂ))
          atImInfty (𝓝 ((64 : ℂ) / (16 : ℂ))) :=
      hH2.div_const (16 : ℂ)
    have hconst : (64 : ℂ) / (16 : ℂ) = (4 : ℂ) := by norm_num
    simpa [hEq, hconst] using! hA'
  have hB :
      Tendsto (fun z : ℍ => (B z - (1 : ℂ)) / q2 z) atImInfty (𝓝 (-16 : ℂ)) := by
    -- Use Jacobi identity `H₂ + H₄ = H₃` to get the matching linear terms.
    have hJac : H₂ + H₄ = H₃ := jacobi_identity
    have hH4 :
        Tendsto
            (fun z : ℍ =>
              (H₄ z - ((1 : ℂ) - (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z)) / q2 z)
            atImInfty (𝓝 (0 : ℂ)) := by
      simpa [q2] using! tendsto_H₄_sub_trunc_div_qHalf_sq
    have hH2small :
        Tendsto (fun z : ℍ => (H₂ z - (16 : ℂ) * qHalf z) / q2 z) atImInfty (𝓝 (0 : ℂ)) := by
      have hH2 := tendsto_H₂_div_qHalf_sub_const_div_qHalf_sq
      have hEq :
          (fun z : ℍ => (H₂ z - (16 : ℂ) * qHalf z) / q2 z) =
            fun z : ℍ => ((H₂ z / qHalf z - (16 : ℂ)) / q2 z) * qHalf z := by
        funext z
        have hq0 : qHalf z ≠ 0 := qHalf_ne_zero z
        have hq2z : q2 z ≠ 0 := pow_ne_zero 2 hq0
        dsimp [q2]
        field_simp [hq0, hq2z]
      have :
          Tendsto (fun z : ℍ => ((H₂ z / qHalf z - (16 : ℂ)) / q2 z) * qHalf z) atImInfty
            (𝓝 ((64 : ℂ) * 0)) :=
        hH2.mul tendsto_qHalf_atImInfty
      simpa [hEq, mul_zero] using! this
    have hH3 :
        Tendsto (fun z : ℍ => (H₃ z - ((1 : ℂ) + (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z)) / q2 z)
          atImInfty (𝓝 (0 : ℂ)) := by
      have hEqH3 : H₃ = fun z : ℍ => H₂ z + H₄ z := by
        funext z
        simpa [hJac] using! (congrArg (fun f : ℍ → ℂ => f z) hJac).symm
      have hEq' :
          ∀ z : ℍ,
            (H₂ z + H₄ z) - ((1 : ℂ) + (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z) =
              (H₂ z - (16 : ℂ) * qHalf z) +
                (H₄ z - ((1 : ℂ) - (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z)) := by
        intro z
        ring
      have hsum := hH2small.add hH4
      have hmain' :
          Tendsto
              (fun z : ℍ =>
                ((H₂ z + H₄ z) - ((1 : ℂ) + (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z)) / q2 z)
              atImInfty (𝓝 ((0 : ℂ) + (0 : ℂ))) := by
        refine hsum.congr' ?_
        refine Filter.Eventually.of_forall ?_
        intro z
        ring
      have hmain :
          Tendsto
              (fun z : ℍ =>
                ((H₂ z + H₄ z) - ((1 : ℂ) + (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z)) / q2 z)
              atImInfty (𝓝 (0 : ℂ)) := by
        simpa [add_zero] using! hmain'
      simpa [hEqH3] using! hmain
    have hH4to : Tendsto H₄ atImInfty (𝓝 (1 : ℂ)) := by
      simpa using! (H₄_tendsto_atImInfty : Tendsto H₄ atImInfty (𝓝 (1 : ℂ)))
    -- Compare `B` with the quadratic truncation.
    let B0 : ℍ → ℂ :=
      fun z : ℍ =>
        ((1 : ℂ) + (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z) *
          ((1 : ℂ) - (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z)
    have hBerr : Tendsto (fun z : ℍ => (B z - B0 z) / q2 z) atImInfty (𝓝 (0 : ℂ)) := by
      have hEq :
          ∀ z : ℍ,
            B z - B0 z =
              (H₃ z - ((1 : ℂ) + (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z)) * H₄ z +
                ((1 : ℂ) + (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z) *
                  (H₄ z - ((1 : ℂ) - (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z)) := by
        intro z
        simp [B, B0]
        ring
      have h1 :
          Tendsto
              (fun z : ℍ =>
                ((H₃ z - ((1 : ℂ) + (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z)) * H₄ z) / q2 z)
              atImInfty (𝓝 (0 : ℂ)) := by
        have ht :
            Tendsto
                (fun z : ℍ =>
                  (H₃ z - ((1 : ℂ) + (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z)) / q2 z * H₄ z)
                atImInfty (𝓝 (0 * (1 : ℂ))) := (hH3.mul hH4to)
        have hEq1 :
            (fun z : ℍ =>
                (H₃ z - ((1 : ℂ) + (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z)) / q2 z *
                  H₄ z) =ᶠ[atImInfty]
              fun z : ℍ =>
                ((H₃ z - ((1 : ℂ) + (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z)) *
                    H₄ z) /
                  q2 z := by
          refine Filter.Eventually.of_forall ?_
          exact fun x => div_mul_eq_mul_div (H₃ x - (1 + 8 * qHalf x + 24 * q2 x)) (q2 x) (H₄ x)
          -- `field_simp` closes this goal.
        have ht' := ht.congr' hEq1
        simpa [mul_zero] using! ht'
      have h2 :
          Tendsto
              (fun z : ℍ =>
                (((1 : ℂ) + (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z) *
                    (H₄ z - ((1 : ℂ) - (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z))) /
                  q2 z)
              atImInfty (𝓝 (0 : ℂ)) := by
        have hA0 :
            Tendsto (fun z : ℍ => (1 : ℂ) + (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z) atImInfty
              (𝓝 (1 : ℂ)) := by
          have h1 : Tendsto (fun _ : ℍ => (1 : ℂ)) atImInfty (𝓝 (1 : ℂ)) := tendsto_const_nhds
          have h2' : Tendsto (fun z : ℍ => (8 : ℂ) * qHalf z) atImInfty (𝓝 (0 : ℂ)) := by
            simpa [mul_zero] using! (tendsto_const_nhds.mul tendsto_qHalf_atImInfty)
          have h3' : Tendsto (fun z : ℍ => (24 : ℂ) * q2 z) atImInfty (𝓝 (0 : ℂ)) := by
            simpa [mul_zero] using! (tendsto_const_nhds.mul hq)
          simpa [q2, add_assoc] using! (h1.add (h2'.add h3'))
        have : Tendsto
            (fun z : ℍ =>
              ((H₄ z - ((1 : ℂ) - (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z)) / q2 z) *
                ((1 : ℂ) + (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z))
            atImInfty (𝓝 (0 * (1 : ℂ))) :=
          (hH4.mul hA0)
        have hEq2 :
            (fun z : ℍ =>
              ((H₄ z - ((1 : ℂ) - (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z)) / q2 z) *
                ((1 : ℂ) + (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z)) =ᶠ[atImInfty]
              fun z : ℍ =>
                (((1 : ℂ) + (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z) *
                    (H₄ z - ((1 : ℂ) - (8 : ℂ) * qHalf z + (24 : ℂ) * q2 z))) /
                  q2 z := by
          refine Filter.Eventually.of_forall ?_
          intro z
          ring
          -- `field_simp` closes this goal.
        have ht' := this.congr' hEq2
        simpa [mul_zero] using! ht'
      have hsum := h1.add h2
      have hBerr' :
          Tendsto (fun z : ℍ => (B z - B0 z) / q2 z) atImInfty (𝓝 ((0 : ℂ) + (0 : ℂ))) := by
        refine hsum.congr' ?_
        refine Filter.Eventually.of_forall ?_
        intro z
        ring
      simpa [add_zero] using! hBerr'
    have hB0 :
        Tendsto (fun z : ℍ => (B0 z - (1 : ℂ)) / q2 z) atImInfty (𝓝 (-16 : ℂ)) := by
      -- Expand the quadratic truncation exactly.
      have hEq :
          ∀ z : ℍ,
            B0 z - (1 : ℂ) = q2 z * ((-16 : ℂ) + qHalf z * (0 : ℂ) + q2 z * (576 : ℂ)) := by
        intro z
        simp [B0, q2]
        ring
      have hlim :
          Tendsto (fun z : ℍ => (-16 : ℂ) + qHalf z * (0 : ℂ) + q2 z * (576 : ℂ)) atImInfty
            (𝓝 (-16 : ℂ)) := by
        have h0 : Tendsto (fun z : ℍ => qHalf z * (0 : ℂ)) atImInfty (𝓝 (0 : ℂ)) := by
          norm_num
        have h576 : Tendsto (fun z : ℍ => q2 z * (576 : ℂ)) atImInfty (𝓝 (0 : ℂ)) := by
          simpa [mul_zero] using! (hq.mul tendsto_const_nhds)
        simpa [add_assoc] using! (tendsto_const_nhds.add (h0.add h576))
      have :
          Tendsto
              (fun z : ℍ =>
                (q2 z * ((-16 : ℂ) + qHalf z * (0 : ℂ) + q2 z * (576 : ℂ))) / q2 z)
              atImInfty (𝓝 (-16 : ℂ)) := by
        refine hlim.congr' ?_
        refine Filter.Eventually.of_forall ?_
        intro z
        have hq2z : q2 z ≠ 0 := pow_ne_zero 2 (qHalf_ne_zero z)
        field_simp [q2, hq2z, hEq z]
      simpa [hEq] using! this
    have hEqB :
        (fun z : ℍ => (B z - (1 : ℂ)) / q2 z) =
          fun z : ℍ => (B z - B0 z) / q2 z + (B0 z - (1 : ℂ)) / q2 z := by
      funext z
      ring
    have hComb :
        Tendsto
            (fun z : ℍ => (B z - B0 z) / q2 z + (B0 z - (1 : ℂ)) / q2 z)
            atImInfty (𝓝 (0 + (-16 : ℂ))) :=
      (hBerr.add hB0)
    simpa [hEqB] using! hComb
  have hΔ : ∀ z : ℍ, (Δ z : ℂ) = ((H₂ z) * (H₃ z) * (H₄ z)) ^ (2 : ℕ) / (256 : ℂ) := by
    intro z
    simpa using! (PsiRewrites.Delta_eq_H₂_H₃_H₄_apply z)
  let s : ℍ → ℂ := fun z : ℍ => A z * B z
  have hs :
      Tendsto (fun z : ℍ => (s z - (1 : ℂ)) / q2 z) atImInfty (𝓝 (-12 : ℂ)) := by
    have hEq :
        ∀ z : ℍ,
          s z - (1 : ℂ) =
            (A z - (1 : ℂ)) + (B z - (1 : ℂ)) + (A z - (1 : ℂ)) * (B z - (1 : ℂ)) := by
      intro z
      simp [s]
      ring
    have hA0 : Tendsto (fun z : ℍ => A z - (1 : ℂ)) atImInfty (𝓝 (0 : ℂ)) := by
      have hEqA :
          ∀ z : ℍ, (1 : ℂ) + q2 z * ((A z - (1 : ℂ)) / q2 z) = A z := by
        intro z
        have hq2z : q2 z ≠ 0 := by
          simpa [q2] using! (pow_ne_zero 2 (qHalf_ne_zero z))
        field_simp [A, q2, hq2z]
        ring_nf
      have hAto : Tendsto A atImInfty (𝓝 (1 : ℂ)) := by
        have hmul :
            Tendsto (fun z : ℍ => q2 z * ((A z - (1 : ℂ)) / q2 z)) atImInfty (𝓝 (0 : ℂ)) := by
          simpa [zero_mul] using! (hq.mul hA)
        have hform :
            Tendsto (fun z : ℍ => (1 : ℂ) + q2 z * ((A z - (1 : ℂ)) / q2 z)) atImInfty
              (𝓝 (1 : ℂ)) := by
          simpa [add_zero] using! (tendsto_const_nhds.add hmul)
        exact hform.congr' (Filter.Eventually.of_forall hEqA)
      have h1 : Tendsto (fun _ : ℍ => (1 : ℂ)) atImInfty (𝓝 (1 : ℂ)) := tendsto_const_nhds
      simpa using! (hAto.sub h1)
    have hB0 : Tendsto (fun z : ℍ => B z - (1 : ℂ)) atImInfty (𝓝 (0 : ℂ)) := by
      have hBto : Tendsto B atImInfty (𝓝 (1 : ℂ)) := by
        have hH4 : Tendsto H₄ atImInfty (𝓝 (1 : ℂ)) := H₄_tendsto_atImInfty
        simpa [B] using! (H₃_tendsto_atImInfty.mul hH4)
      have h1 : Tendsto (fun _ : ℍ => (1 : ℂ)) atImInfty (𝓝 (1 : ℂ)) := tendsto_const_nhds
      simpa using! (hBto.sub h1)
    have hprod :
        Tendsto
            (fun z : ℍ => ((A z - (1 : ℂ)) * (B z - (1 : ℂ))) / q2 z)
            atImInfty (𝓝 (0 : ℂ)) := by
      have hEqP :
          (fun z : ℍ => ((A z - (1 : ℂ)) * (B z - (1 : ℂ))) / q2 z) =
            fun z : ℍ => (A z - (1 : ℂ)) * ((B z - (1 : ℂ)) / q2 z) := by
        funext z
        have hq2z : q2 z ≠ 0 := pow_ne_zero 2 (qHalf_ne_zero z)
        field_simp [q2, hq2z]
        -- `field_simp` closes this goal.
      have :
          Tendsto
              (fun z : ℍ => (A z - (1 : ℂ)) * ((B z - (1 : ℂ)) / q2 z))
              atImInfty (𝓝 (0 : ℂ)) := by
        simpa [zero_mul] using! (hA0.mul hB)
      simpa [hEqP] using! this
    have hsum :
        Tendsto
            (fun z : ℍ =>
              ((A z - (1 : ℂ)) + (B z - (1 : ℂ)) + (A z - (1 : ℂ)) * (B z - (1 : ℂ))) / q2 z)
          atImInfty (𝓝 ((4 : ℂ) + (-16 : ℂ) + (0 : ℂ))) := by
      have hEqS :
          (fun z : ℍ =>
              ((A z - (1 : ℂ)) + (B z - (1 : ℂ)) + (A z - (1 : ℂ)) * (B z - (1 : ℂ))) / q2 z) =
            fun z : ℍ =>
              (A z - (1 : ℂ)) / q2 z + (B z - (1 : ℂ)) / q2 z +
                ((A z - (1 : ℂ)) * (B z - (1 : ℂ))) / q2 z := by
        funext z
        have hq2z : q2 z ≠ 0 := pow_ne_zero 2 (qHalf_ne_zero z)
        field_simp [q2, hq2z]
        -- `field_simp` closes this goal.
      have :
          Tendsto
              (fun z : ℍ =>
                (A z - (1 : ℂ)) / q2 z + (B z - (1 : ℂ)) / q2 z +
                  ((A z - (1 : ℂ)) * (B z - (1 : ℂ))) / q2 z)
              atImInfty (𝓝 ((4 : ℂ) + (-16 : ℂ) + (0 : ℂ))) :=
        (hA.add hB).add hprod
      simpa [hEqS] using! this
    have hs' :
        Tendsto
            (fun z : ℍ => (s z - (1 : ℂ)) / q2 z)
            atImInfty (𝓝 ((4 : ℂ) + (-16 : ℂ) + (0 : ℂ))) :=
      (tendsto_congr fun x => congrFun (congrArg HDiv.hDiv (hEq x)) (q2 x)).mpr hsum
    have hconst : (4 : ℂ) + (-16 : ℂ) + (0 : ℂ) = (-12 : ℂ) := by norm_num
    simpa [hconst] using! hs'
  have hsplus : Tendsto (fun z : ℍ => s z + (1 : ℂ)) atImInfty (𝓝 (2 : ℂ)) := by
    have hs_to : Tendsto s atImInfty (𝓝 (1 : ℂ)) := by
      have hEqS :
          s = fun z : ℍ => (1 : ℂ) + q2 z * ((s z - (1 : ℂ)) / q2 z) := by
        funext z
        have hq2z : q2 z ≠ 0 := pow_ne_zero 2 (qHalf_ne_zero z)
        field_simp [s, q2, hq2z]
        ring_nf
      have hmul : Tendsto (fun z : ℍ => q2 z * ((s z - (1 : ℂ)) / q2 z)) atImInfty (𝓝 (0 : ℂ)) := by
        simpa [zero_mul] using! (hq.mul hs)
      have :
          Tendsto
              (fun z : ℍ => (1 : ℂ) + q2 z * ((s z - (1 : ℂ)) / q2 z))
              atImInfty (𝓝 (1 : ℂ)) := by
        simpa [add_zero] using! (tendsto_const_nhds.add hmul)
      refine this.congr' ?_
      exact Eq.eventuallyEq (id (Eq.symm hEqS))
    have h1 : Tendsto (fun _ : ℍ => (1 : ℂ)) atImInfty (𝓝 (1 : ℂ)) := tendsto_const_nhds
    have hconst : (1 : ℂ) + (1 : ℂ) = (2 : ℂ) := by norm_num
    simpa [hconst] using! (hs_to.add h1)
  have hEqD : (fun z : ℍ => (Δ z) / q2 z) = fun z : ℍ => (s z) ^ (2 : ℕ) := by
    funext z
    have hq0 : qHalf z ≠ 0 := qHalf_ne_zero z
    have hq2z : (qHalf z) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hq0
    have hHB : (H₂ z) * (H₃ z) * (H₄ z) = (16 : ℂ) * qHalf z * s z := by
      dsimp [s, A, B]
      field_simp [hq0]
      -- `field_simp` closes this goal.
    -- Rewrite `Δ / qHalf^2` into an expression in `s = A*B` and cancel.
    dsimp [q2]
    have hHB2 :
        ((H₂ z) * (H₃ z) * (H₄ z)) ^ (2 : ℕ) =
          ((16 : ℂ) * qHalf z * s z) ^ (2 : ℕ) :=
      congrArg (fun w : ℂ => w ^ (2 : ℕ)) hHB
    -- Now clear denominators and normalize.
    rw [hΔ z, hHB2]
    field_simp [hq2z]
    ring_nf
  have hmain :
      Tendsto (fun z : ℍ => (((Δ z) / q2 z) - (1 : ℂ)) / q2 z) atImInfty (𝓝 (-24 : ℂ)) := by
    have hEq' :
        (fun z : ℍ => (((Δ z) / q2 z) - (1 : ℂ)) / q2 z) =
          fun z : ℍ => (((s z) ^ (2 : ℕ) - (1 : ℂ)) / q2 z) := by
      funext z
      have hEqDz : (Δ z) / q2 z = (s z) ^ (2 : ℕ) := by
        simpa using! congrArg (fun f : ℍ → ℂ => f z) hEqD
      simp [hEqDz]
    have hPow :
        Tendsto (fun z : ℍ => (((s z) ^ (2 : ℕ) - (1 : ℂ)) / q2 z)) atImInfty (𝓝 (-24 : ℂ)) := by
      have hEqP :
          (fun z : ℍ => (((s z) ^ (2 : ℕ) - (1 : ℂ)) / q2 z)) =
            fun z : ℍ => ((s z - (1 : ℂ)) / q2 z) * (s z + (1 : ℂ)) := by
        funext z
        ring
      have :
          Tendsto (fun z : ℍ => ((s z - (1 : ℂ)) / q2 z) * (s z + (1 : ℂ))) atImInfty
            (𝓝 ((-12 : ℂ) * (2 : ℂ))) :=
        hs.mul hsplus
      have hconst : ((-12 : ℂ) * (2 : ℂ)) = (-24 : ℂ) := by norm_num
      simpa [hEqP, hconst] using! this
    simpa [hEq', q2] using! hPow
  simpa [q2, sub_eq_add_neg, add_assoc] using! hmain

end SpecialValuesAux.EvenU.Deriv
end

end SpherePacking.Dim24
