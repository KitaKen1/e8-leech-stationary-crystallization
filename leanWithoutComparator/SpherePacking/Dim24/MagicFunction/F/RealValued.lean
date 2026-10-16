module
public import SpherePacking.Dim24.MagicFunction.F.Defs
public import SpherePacking.Dim24.MagicFunction.A.PureImag
public import SpherePacking.Dim24.MagicFunction.B.PureImag
public import SpherePacking.Dim24.MagicFunction.A.Eigen.Eigenfunction
public import SpherePacking.Dim24.MagicFunction.B.Eigen.PermJ5


/-!
# Real-valuedness of `f` and `𝓕 f`

This file shows that the magic function `f` and its Fourier transform `𝓕 f` take real values.

## Main statements
* `f_real`
* `f_real_fourier`
-/

namespace SpherePacking.Dim24

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ²⁴ ℂ)

/-- The magic function `f` is real-valued. -/
public theorem f_real : ∀ x : ℝ²⁴, (↑(f x).re : ℂ) = f x := by
  /- Proof sketch:
  Combine `a_mapsTo_pureImag` and `b_mapsTo_pureImag`:
  `f` is a linear combination of purely imaginary functions with prefactor `i`,
  hence real-valued. -/
  intro x
  have ha : (a x).re = 0 := a_mapsTo_pureImag (x := x)
  have hb : (b x).re = 0 := b_mapsTo_pureImag (x := x)
  let c₁ : ℂ := (-((Real.pi : ℂ) * Complex.I) / (113218560 : ℂ))
  let c₂ : ℂ := Complex.I / ((262080 : ℂ) * (Real.pi : ℂ))
  have hc₁ : c₁.re = 0 := by simp [c₁]
  have hc₂ : c₂.re = 0 := by simp [c₂, div_eq_mul_inv, Complex.mul_re]
  have hIm₁ : (c₁ * a x).im = 0 := by simp [Complex.mul_im, hc₁, ha]
  have hIm₂ : (c₂ * b x).im = 0 := by simp [Complex.mul_im, hc₂, hb]
  have hf : f x = c₁ * a x - c₂ * b x := by
    simp [f, c₁, c₂, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul]
  have hIm : (f x).im = 0 := by simp [hf, Complex.sub_im, hIm₁, hIm₂]
  apply Complex.ext
  · simp
  · exact hIm.symm

/-- The Fourier transform `𝓕 f` is real-valued. -/
public theorem f_real_fourier :
    ∀ x : ℝ²⁴, (↑((FT f x).re : ℂ)) = FT f x := by
  /- Proof sketch:
  Use `eig_a`/`eig_b` to rewrite `𝓕 f` as the same linear combination of `a,b` (with sign),
  then apply the same argument as `f_real`. -/
  intro x
  have ha : (a x).re = 0 := a_mapsTo_pureImag (x := x)
  have hb : (b x).re = 0 := b_mapsTo_pureImag (x := x)
  let c₁ : ℂ := (-((Real.pi : ℂ) * Complex.I) / (113218560 : ℂ))
  let c₂ : ℂ := Complex.I / ((262080 : ℂ) * (Real.pi : ℂ))
  have hc₁ : c₁.re = 0 := by simp [c₁]
  have hc₂ : c₂.re = 0 := by simp [c₂, div_eq_mul_inv, Complex.mul_re]
  have hIm₁ : (c₁ * a x).im = 0 := by simp [Complex.mul_im, hc₁, ha]
  have hIm₂ : (c₂ * b x).im = 0 := by simp [Complex.mul_im, hc₂, hb]
  have hFf : FT f = c₁ • a + c₂ • b := by
    simp [f, map_sub, map_smul, eig_a, eig_b, c₁, c₂, -FourierTransform.fourierCLE_apply]
  have hIm : (FT f x).im = 0 := by
    simp [hFf, SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul,
      Complex.add_im, hIm₁, hIm₂]
  apply Complex.ext
  · simp
  · exact hIm.symm

end SpherePacking.Dim24
