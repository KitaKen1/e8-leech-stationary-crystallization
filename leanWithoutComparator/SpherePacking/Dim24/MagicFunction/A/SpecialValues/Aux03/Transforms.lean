-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Aux02


/-!
# Transform identities

This file packages the shift (`z ↦ z - 1`) and `S`-transform identities for `varphi'` and its
companions, and uses them to compute the finite difference `F(z) - F(z - 1)` at even `u`.

## Main statement
* `SpecialValuesAux.F_sub_F_sub_one`
-/

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesAux

open MagicFunction.Parametrisations RealIntegrals intervalIntegral Complex MeasureTheory Set Filter
open UpperHalfPlane
open scoped Topology
open scoped UpperHalfPlane

private lemma sub_one_of_periodic
    {f : UpperHalfPlane → ℂ} {f' : ℂ → ℂ}
    (hf : ∀ {z : ℂ} (hz : 0 < z.im), f' z = f ⟨z, hz⟩)
    (hper : ∀ z : UpperHalfPlane, f (((1 : ℝ) +ᵥ z) : UpperHalfPlane) = f z)
    (z : ℂ) (hz : 0 < z.im) :
    f' (z - 1) = f' z := by
  let zH' : UpperHalfPlane := ⟨z - 1, by simpa [sub_eq_add_neg, add_im] using! hz⟩
  let zH : UpperHalfPlane := ⟨z, hz⟩
  have hv : ((1 : ℝ) +ᵥ zH' : UpperHalfPlane) = zH := by
    ext1
    simp [zH', zH, sub_eq_add_neg, add_left_comm]
  have hz' : 0 < (z - 1).im := by simpa [sub_eq_add_neg, add_im] using! hz
  have hEq : f zH = f zH' := by
    simpa [hv] using! hper zH'
  calc
    f' (z - 1) = f zH' := by simpa [zH'] using! hf (z := z - 1) hz'
    _ = f zH := by simpa using! hEq.symm
    _ = f' z := by simpa [zH] using! (hf (z := z) hz).symm

lemma varphi'_sub_one (z : ℂ) (hz : 0 < z.im) : varphi' (z - 1) = varphi' z := by
  simpa using!
    sub_one_of_periodic (f := varphi) (f' := varphi') (hf := fun hz => (varphi'_def hz))
      (hper := fun z => (varphi_periodic (z := z))) z hz

lemma varphi₁'_sub_one (z : ℂ) (hz : 0 < z.im) : varphi₁' (z - 1) = varphi₁' z := by
  simpa using!
    sub_one_of_periodic (f := varphi₁) (f' := varphi₁') (hf := fun hz => (varphi₁'_def hz))
      (hper := fun z => (varphi₁_periodic (z := z))) z hz

lemma varphi₂'_sub_one (z : ℂ) (hz : 0 < z.im) : varphi₂' (z - 1) = varphi₂' z := by
  simpa using!
    sub_one_of_periodic (f := varphi₂) (f' := varphi₂') (hf := fun hz => (varphi₂'_def hz))
      (hper := fun z => (varphi₂_periodic (z := z))) z hz

lemma varphi'_neg_inv_mul_pow10 (z : ℂ) (hz : 0 < z.im) :
    varphi' (-1 / z) * z ^ (10 : ℕ) =
      z ^ (2 : ℕ) * varphi' z + z * varphi₁' z + varphi₂' z := by
  -- Apply the `S`-transformation law for `varphi` on `ℍ` and translate to the total extensions.
  let zH : UpperHalfPlane := ⟨z, hz⟩
  let zHS : UpperHalfPlane := ModularGroup.S • zH
  have hScoe : ((zHS : UpperHalfPlane) : ℂ) = (-1 : ℂ) / z := by
    -- `S • z = (-z)⁻¹ = (-1)/z`.
    have h1' :
        ((ModularGroup.S • zH : UpperHalfPlane) : ℂ) = (-(z : ℂ))⁻¹ := by
      -- Coerce `modular_S_smul` to `ℂ`.
      simpa [UpperHalfPlane.modular_S_smul, zH] using!
        congrArg (fun w : UpperHalfPlane => (w : ℂ)) (UpperHalfPlane.modular_S_smul zH)
    have h1 : ((zHS : UpperHalfPlane) : ℂ) = (-(z : ℂ))⁻¹ := by
      simpa [zHS] using! h1'
    calc
      ((zHS : UpperHalfPlane) : ℂ) = (-(z : ℂ))⁻¹ := h1
      _ = (-1 : ℂ) / z := by simp [div_eq_mul_inv]
  have hvarphiS' : varphi' ((-1 : ℂ) / z) = varphi zHS := by
    -- Use the coercion lemma for `varphi'` and rewrite the argument using `hScoe`.
    simpa [hScoe] using! (varphi'_coe_upperHalfPlane (z := zHS))
  have hmain := varphi_S_transform_mul_pow10 (z := zH)
  -- Rewrite all modular forms by the corresponding total extensions.
  have hvarphi : varphi (zH : UpperHalfPlane) = varphi' z := by
    simp [varphi', hz, zH]
  have hvarphi₁ : varphi₁ (zH : UpperHalfPlane) = varphi₁' z := by
    simp [varphi₁', hz, zH]
  have hvarphi₂ : varphi₂ (zH : UpperHalfPlane) = varphi₂' z := by
    simp [varphi₂', hz, zH]
  -- Put the pieces together.
  -- (`mul_comm` to match the `varphi' * z^10` ordering.)
  calc
    varphi' ((-1 : ℂ) / z) * z ^ (10 : ℕ) =
        (z ^ (10 : ℕ)) * varphi zHS := by
          -- Rewrite `varphi'((-1)/z)` and commute.
          simp [hvarphiS', mul_comm]
    _ =
        z ^ (2 : ℕ) * varphi (zH : UpperHalfPlane) + z * varphi₁ (zH : UpperHalfPlane) +
          varphi₂ (zH : UpperHalfPlane) := by
          simpa [zH] using! hmain
    _ = z ^ (2 : ℕ) * varphi' z + z * varphi₁' z + varphi₂' z := by
          simp [hvarphi, hvarphi₁, hvarphi₂]
 
/-- At even `u`, compute the finite difference `F u (zI x) - F u (zI x - 1)` in terms of `f0`. -/
public lemma F_sub_F_sub_one (u : ℝ) (hu : expU u 1 = 1) (x : ℝ) :
    F u (zI x) - F u (zI x - 1) =
      f0 u (zI x) + varphi₁' (zI x) * expU u (zI x) := by
  -- Work with `z = x + i`.
  let z : ℂ := zI x
  have hz : 0 < z.im := by
    simp [z, zI]
  have hz' : 0 < (z - 1).im := by
    simp [z, zI, sub_eq_add_neg, add_im]
  let E : ℂ := expU u z
  -- Rewrite `F` at `z` and `z-1` using the S-transform identity for `varphi`.
  have hFz :
      F u z =
        (z ^ (2 : ℕ) * varphi' z + z * varphi₁' z + varphi₂' z) * E := by
    unfold F
    have h := varphi'_neg_inv_mul_pow10 (z := z) hz
    simpa [E, mul_assoc, mul_left_comm, mul_comm] using! congrArg (fun w : ℂ => w * expU u z) h
  have hFz1_raw :
      F u (z - 1) =
        ((z - 1) ^ (2 : ℕ) * varphi' (z - 1) +
            (z - 1) * varphi₁' (z - 1) + varphi₂' (z - 1)) *
          expU u (z - 1) := by
    unfold F
    have h := varphi'_neg_inv_mul_pow10 (z := z - 1) hz'
    simpa [mul_assoc, mul_left_comm, mul_comm] using!
      congrArg (fun w : ℂ => w * expU u (z - 1)) h
  -- Rewrite the shifted terms using periodicity and `expU u 1 = 1`.
  have hexp : expU u (z - 1) = E := by
    have h := expU_sub_one (u := u) (z := z)
    simpa [E, hu, mul_one, inv_one] using! h
  have hperφ : varphi' (z - 1) = varphi' z := varphi'_sub_one (z := z) hz
  have hperφ1 : varphi₁' (z - 1) = varphi₁' z := varphi₁'_sub_one (z := z) hz
  have hperφ2 : varphi₂' (z - 1) = varphi₂' z := varphi₂'_sub_one (z := z) hz
  have hFz1 :
      F u (z - 1) =
        ((z - 1) ^ (2 : ℕ) * varphi' z + (z - 1) * varphi₁' z + varphi₂' z) * E := by
    -- Rewrite `hFz1_raw` using `hexp` and periodicity.
    simpa [hexp, hperφ, hperφ1, hperφ2, E, mul_assoc, add_assoc] using! hFz1_raw
  -- Now compute the finite difference.
  have hdiff :
      F u z - F u (z - 1) =
        varphi' z * (((2 : ℂ) * z) - 1) * E + varphi₁' z * E := by
    -- Expand both sides and simplify the polynomial identity in `z`.
    rw [hFz, hFz1]
    -- Reduce to an identity in the commutative ring `ℂ`.
    ring_nf
  -- Return to the original statement (in terms of `zI x`) and unpack `f0`.
  assumption

end SpecialValuesAux

end

end SpherePacking.Dim24
