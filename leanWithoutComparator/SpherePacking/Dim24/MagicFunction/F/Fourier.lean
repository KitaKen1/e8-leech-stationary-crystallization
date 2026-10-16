module
public import SpherePacking.Dim24.MagicFunction.F.Defs
import SpherePacking.Dim24.MagicFunction.A.Eigen.Eigenfunction
import SpherePacking.Dim24.MagicFunction.B.Eigen.PermJ5

/-!
# Fourier transform of `f`

We compute the Fourier transform of the auxiliary function `f` using the eigenfunction relations
`𝓕 a = a` and `𝓕 b = -b`.

## Main statement
* `fourier_f`
-/

open scoped FourierTransform

namespace SpherePacking.Dim24

noncomputable section

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ²⁴ ℂ)

/--
Fourier transform of `f`, obtained by linearity and the eigenfunction identities
`𝓕 a = a` and `𝓕 b = -b`.
-/
public theorem fourier_f :
    FT f =
      (-((Real.pi : ℂ) * Complex.I) / (113218560 : ℂ)) • a +
        (Complex.I / ((262080 : ℂ) * (Real.pi : ℂ))) • b := by
  -- `𝓕 a = a` and `𝓕 b = -b`, so the `b` coefficient flips sign.
  simp [-FourierTransform.fourierCLE_apply, Dim24.f, eig_a, eig_b]

end

end SpherePacking.Dim24
