-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.Orthogonality
public import Mathlib.Algebra.Module.Pi
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Dot product as a bilinear form over `ZMod 2`

We package the dot product on binary words into a bundled `LinearMap.BilinForm`, and record
basic properties such as symmetry and nondegeneracy.

## Main definitions
* `DotBilin.dotBilinForm`

## Main statements
* `DotBilin.dotBilinForm_isSymm`
* `DotBilin.dotBilinForm_nondegenerate`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

open scoped BigOperators

namespace DotBilin

/-- The dot product on binary words is symmetric. -/
public lemma dot_comm {n : ℕ} (x y : BinWord n) : dot x y = dot y x := by
  simp [dot, mul_comm]

/-- Scalar multiplication in the right argument factors out of the dot product. -/
public lemma dot_smul_right {n : ℕ} (a : ZMod 2) (x y : BinWord n) :
    dot x (a • y) = a * dot x y := by
  simp [dot, Pi.smul_apply, Finset.mul_sum, mul_left_comm]

/-- Scalar multiplication in the left argument factors out of the dot product. -/
public lemma dot_smul_left {n : ℕ} (a : ZMod 2) (x y : BinWord n) :
    dot (a • x) y = a * dot x y := by
  simpa [dot_comm] using! (dot_smul_right (n := n) a y x)

/-- The dot product bundled as a `LinearMap.BilinForm` over `ZMod 2`. -/
@[expose] public def dotBilinForm (n : ℕ) : LinearMap.BilinForm (ZMod 2) (BinWord n) :=
  LinearMap.mk₂ (R := ZMod 2) (fun x y => dot (n := n) x y)
    (by
      intro x₁ x₂ y
      simpa using! (dot_add_left (n := n) x₁ x₂ y))
    (by
      intro a x y
      -- `LinearMap.mk₂` expects a `•`-statement; `ZMod 2` acts on itself by multiplication.
      simpa using! (dot_smul_left (n := n) a x y))
    (by
      intro x y₁ y₂
      simpa using! (dot_add_right (n := n) x y₁ y₂))
    (by
      intro a x y
      simpa using! (dot_smul_right (n := n) a x y))

/-- Evaluation lemma for `dotBilinForm`. -/
@[simp] public lemma dotBilinForm_apply {n : ℕ} (x y : BinWord n) :
    dotBilinForm (n := n) x y = dot x y := rfl

/-- The bundled dot product bilinear form is symmetric. -/
public lemma dotBilinForm_isSymm (n : ℕ) : (dotBilinForm (n := n)).IsSymm :=
  ⟨by intro x y; simp [dot_comm]⟩

lemma dot_single_right {n : ℕ} (x : BinWord n) (i : Fin n) :
    dot x (Pi.single i (1 : ZMod 2)) = x i := by
  dsimp [dot, Pi.single]
  -- A single nonzero term at `i`.
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- The dot product bilinear form is nondegenerate. -/
public lemma dotBilinForm_nondegenerate (n : ℕ) : (dotBilinForm (n := n)).Nondegenerate := by
  dsimp
    [LinearMap.BilinForm.Nondegenerate, LinearMap.Nondegenerate,
      LinearMap.SeparatingLeft, LinearMap.SeparatingRight]
  have hL : (dotBilinForm (n := n)).SeparatingLeft := by
    intro x hx; ext i; simpa [dot_single_right] using! hx (Pi.single i (1 : ZMod 2))
  refine ⟨hL, fun y hy => hL y (fun x => by simpa [dot_comm] using! hy x)⟩

end DotBilin
end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
