-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSDecay
import SpherePacking.Dim24.ModularForms.Psi.Relations


/-!
# Slash-action identities for `ψ`-functions

We use these to relate values of `ψI, ψS, ψT` along the parametrized contours to values on the
imaginary axis.

## Main statements
* `PsiSlash.ψS_slash_S`
* `PsiSlash.ψS_slash_ST`
* `PsiSlash.ψT_slash_T`
-/

noncomputable section

namespace SpherePacking.Dim24.PsiSlash

open scoped UpperHalfPlane
open UpperHalfPlane ModularGroup MatrixGroups ModularForm SlashAction
open scoped ModularForm

private lemma even_negTen : Even (-10 : ℤ) := by decide

/-- Modular relation under `S`: `ψS ∣[-10] S = ψI`. -/
public theorem ψS_slash_S : (ψS ∣[-10] S) = ψI := by
  calc
    (ψS ∣[-10] S) = (ψI ∣[-10] S) ∣[-10] S := by simp [ψS]
    _ = ψI ∣[-10] (S * S) := by
          simpa using! (SlashAction.slash_mul (-10 : ℤ) S S ψI).symm
    _ = ψI ∣[-10] (-1 : SL(2, ℤ)) := by simp [ModularGroup.modular_S_sq]
    _ = ψI := by
          simpa using! (ModularForm.slash_neg_one' (k := (-10 : ℤ)) ψI even_negTen)

/-- Modular relation under `S*T`: `ψS ∣[-10] (S*T) = ψT`. -/
public theorem ψS_slash_ST : (ψS ∣[-10] (S * T)) = ψT := by
  calc
    (ψS ∣[-10] (S * T)) = (ψI ∣[-10] S) ∣[-10] (S * T) := by simp [ψS]
    _ = ψI ∣[-10] (S * (S * T)) := by
          simpa using! (SlashAction.slash_mul (-10 : ℤ) S (S * T) ψI).symm
    _ = ψI ∣[-10] ((S * S) * T) := by
          simpa using! congrArg (fun γ => ψI ∣[-10] γ) (mul_assoc S S T).symm
    _ = ψI ∣[-10] ((-1 : SL(2, ℤ)) * T) := by simp [ModularGroup.modular_S_sq]
    _ = (ψI ∣[-10] (-1 : SL(2, ℤ))) ∣[-10] T := by
          simpa using! (SlashAction.slash_mul (-10 : ℤ) (-1 : SL(2, ℤ)) T ψI)
    _ = (ψI ∣[-10] T) := by
          simpa using! congrArg (fun f : ℍ → ℂ => f ∣[-10] T)
            (ModularForm.slash_neg_one' (k := (-10 : ℤ)) ψI even_negTen)
    _ = ψT := by simp [ψT]

/-- Modular relation under `T`: `ψT ∣[-10] T = ψI`. -/
public theorem ψT_slash_T : (ψT ∣[-10] T) = ψI := by
  -- `ψT = ψI | T`, so `ψT | T = ψI | T^2 = ψI` (period `2`).
  have hT2 : (ψI ∣[-10] (T ^ 2)) = ψI := by
    ext z
    calc
      (ψI ∣[-10] (T ^ 2)) z = ψI (((1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ z)) : ℍ) := by
        calc
          (ψI ∣[-10] (T ^ 2)) z = (ψI ∣[-10] (T * T)) z := by simp [pow_two]
          _ = ((ψI ∣[-10] T) ∣[-10] T) z := by
                simpa using! congrFun (SlashAction.slash_mul (-10 : ℤ) T T ψI) z
          _ = ψI (((1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ z)) : ℍ) := by
                simp [modular_slash_T_apply]
      _ = ψI z := SpherePacking.Dim24.ψI_periodic_two z
  calc
    (ψT ∣[-10] T) = (ψI ∣[-10] T) ∣[-10] T := by simp [ψT]
    _ = ψI ∣[-10] (T ^ 2) := by
          -- `T * T = T^2` and `slash_mul` packages the composition.
          simpa [pow_two] using! (SlashAction.slash_mul (-10 : ℤ) T T ψI).symm
    _ = ψI := hT2

end SpherePacking.Dim24.PsiSlash

end
