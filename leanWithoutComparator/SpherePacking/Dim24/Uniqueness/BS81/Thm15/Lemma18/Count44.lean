-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Package
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma17.Shell4
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44.Basic
import Mathlib.Tactic.Linarith

/-!
# BS81 Lemma 18(ii): 44 common neighbors in `L₄`

In the equality case, BS81 Lemma 17 identifies the norm-`4` shell with the scaled code
`L₄ = 2 • C`. This file proves BS81 Lemma 18(ii): if `u,v ∈ L₄` satisfy `⟪u, v⟫ = 0`, then there
are exactly `44` vectors `w ∈ L₄` such that `⟪u, w⟫ = ⟪v, w⟫ = 2`.

We reduce this to the corresponding statement in the code `C`, proved in
`SpherePacking.Dim24.Uniqueness.BS81.Thm14.CommonNeighbors44.Basic`.

## Main statement
* `commonNeighbors44_in_shell4`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma18

noncomputable section

open scoped RealInnerProductSpace Pointwise

open Set

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- BS81 Lemma 18(ii): the `44` common-neighbors count in the shell `L₄ = 2 • C`. -/
public theorem commonNeighbors44_in_shell4
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    {u v : ℝ²⁴}
    (hu : u ∈ latticeShell4 C) (hv : v ∈ latticeShell4 C)
    (hinner : (⟪u, v⟫ : ℝ) = 0) :
    Set.ncard {w : ℝ²⁴ | w ∈ latticeShell4 C ∧ (⟪u, w⟫ : ℝ) = 2 ∧ (⟪v, w⟫ : ℝ) = 2} = 44 := by
  have inner_two_smul_two_smul (x y : ℝ²⁴) :
      (⟪(2 : ℝ) • x, (2 : ℝ) • y⟫ : ℝ) = (2 : ℝ) * ((2 : ℝ) * (⟪x, y⟫ : ℝ)) := by
    simp [inner_smul_left, inner_smul_right]
  have hshell :
      latticeShell4 C = twoCodeVectors C :=
    Uniqueness.BS81.Thm15.Lemma17.shell4_eq_twoCodeVectors (C := C) h
  have hu' : u ∈ twoCodeVectors C := by
    simpa [hshell] using! hu
  rcases hu' with ⟨u₀, hu₀, rfl⟩
  have hv' : v ∈ twoCodeVectors C := by
    simpa [hshell] using! hv
  rcases hv' with ⟨v₀, hv₀, rfl⟩
  have hinner₀ : (⟪u₀, v₀⟫ : ℝ) = 0 := by
    have : 2 * (2 * ⟪u₀, v₀⟫) = 0 := by simpa [inner_two_smul_two_smul] using! hinner
    nlinarith
  have hset :
      {w : ℝ²⁴ |
          w ∈ latticeShell4 C ∧
            (⟪(2 : ℝ) • u₀, w⟫ : ℝ) = 2 ∧ (⟪(2 : ℝ) • v₀, w⟫ : ℝ) = 2} =
        (fun w₀ : ℝ²⁴ => (2 : ℝ) • w₀) ''
          {w₀ : ℝ²⁴ | w₀ ∈ C ∧ (⟪u₀, w₀⟫ : ℝ) = (1 / 2 : ℝ) ∧ (⟪v₀, w₀⟫ : ℝ) = (1 / 2 : ℝ)} := by
    ext w
    constructor
    · rintro ⟨hwShell, hwu, hwv⟩
      have hwTwo : w ∈ twoCodeVectors C := by
        simpa [hshell] using! hwShell
      rcases hwTwo with ⟨w₀, hw₀, rfl⟩
      have hwu₀ : (⟪u₀, w₀⟫ : ℝ) = (1 / 2 : ℝ) := by
        have : 2 * (2 * ⟪u₀, w₀⟫) = 2 := by simpa [inner_two_smul_two_smul] using! hwu
        nlinarith
      have hwv₀ : (⟪v₀, w₀⟫ : ℝ) = (1 / 2 : ℝ) := by
        have : 2 * (2 * ⟪v₀, w₀⟫) = 2 := by simpa [inner_two_smul_two_smul] using! hwv
        nlinarith
      refine ⟨w₀, ⟨hw₀, hwu₀, hwv₀⟩, rfl⟩
    · rintro ⟨w₀, ⟨hw₀, hwu₀, hwv₀⟩, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · have : (2 : ℝ) • w₀ ∈ twoCodeVectors C := ⟨w₀, hw₀, rfl⟩
        simpa [hshell] using! this
      · have : (2 : ℝ) * ((2 : ℝ) * (⟪u₀, w₀⟫ : ℝ)) = 2 := by nlinarith [hwu₀]
        simpa [inner_two_smul_two_smul] using! this
      · have : (2 : ℝ) * ((2 : ℝ) * (⟪v₀, w₀⟫ : ℝ)) = 2 := by nlinarith [hwv₀]
        simpa [inner_two_smul_two_smul] using! this
  have hinj : Function.Injective fun x : ℝ²⁴ => (2 : ℝ) • x := by
    intro a b hab
    have h2 : IsUnit (2 : ℝ) := (isUnit_iff_ne_zero.2 (by norm_num))
    exact (h2.smul_left_cancel).1 hab
  have hcount :
      Set.ncard
          {w₀ : ℝ²⁴ | w₀ ∈ C ∧ (⟪u₀, w₀⟫ : ℝ) = (1 / 2 : ℝ) ∧ (⟪v₀, w₀⟫ : ℝ) = (1 / 2 : ℝ)} =
        44 := by
    simpa using!
      (Uniqueness.BS81.Thm14.commonNeighbors44 (C := C) h hu₀ hv₀ hinner₀)
  -- Convert the `latticeShell4`-count to the `C`-count by the bijection `w₀ ↦ 2•w₀`.
  rw [hset]
  rw [Set.ncard_image_of_injective _ hinj]
  exact hcount

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma18
