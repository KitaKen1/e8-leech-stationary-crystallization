-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.SphereAvgMoments
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Basic lemmas for `sphereAvg24`

This file collects integrability and linearity lemmas for the spherical average `sphereAvg24`.
These are shared between the design computations and the `44` common-neighbors moment package.

## Main statements
* `integrable_coord_pow_mul_coord_pow`
* `integrable_inner_pow_mul_inner_pow`
* `sphereAvg24_congr`
* `sphereAvg24_neg`
* `sphereAvg24_finset_sum`
* `sphereAvg24_finset_sum₂`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14

noncomputable section

open scoped RealInnerProductSpace BigOperators ENNReal
open MeasureTheory Set

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

lemma coord_abs_le_one (x : S23) (i : Fin 24) : |(x.1 i : ℝ)| ≤ (1 : ℝ) := by
  have hx : ‖(x : ℝ²⁴)‖ = (1 : ℝ) :=
    mem_sphere_zero_iff_norm.mp x.2
  have hle : ‖(x : ℝ²⁴) i‖ ≤ ‖(x : ℝ²⁴)‖ := by
    simpa using! (PiLp.norm_apply_le (p := (2 : ℝ≥0∞)) (x := (x : ℝ²⁴)) i)
  simp_all

/-- A coordinate monomial `x ↦ x_i^m * x_j^n` is integrable on `S23`. -/
public lemma integrable_coord_pow_mul_coord_pow (i j : Fin 24) (m n : ℕ) :
    Integrable (fun x : S23 => (x.1 i : ℝ) ^ m * (x.1 j : ℝ) ^ n) sphereMeasure24 := by
  letI : IsFiniteMeasure sphereMeasure24 := ⟨by simpa using! sphereMeasure24_univ_lt_top⟩
  have hmeas :
      AEStronglyMeasurable (fun x : S23 => (x.1 i : ℝ) ^ m * (x.1 j : ℝ) ^ n) sphereMeasure24 := by
    have hcont : Continuous (fun x : S23 => (x.1 i : ℝ) ^ m * (x.1 j : ℝ) ^ n) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  refine Integrable.of_bound (μ := sphereMeasure24) hmeas (C := (1 : ℝ)) ?_
  filter_upwards with x
  have hi : |(x.1 i : ℝ)| ≤ (1 : ℝ) := coord_abs_le_one x i
  have hj : |(x.1 j : ℝ)| ≤ (1 : ℝ) := coord_abs_le_one x j
  have hi' : |(x.1 i : ℝ) ^ m| ≤ (1 : ℝ) := by
    have : |(x.1 i : ℝ)| ^ m ≤ (1 : ℝ) ^ m := pow_le_pow_left₀ (abs_nonneg _) hi m
    simpa [abs_pow, one_pow] using! this
  have hj' : |(x.1 j : ℝ) ^ n| ≤ (1 : ℝ) := by
    have : |(x.1 j : ℝ)| ^ n ≤ (1 : ℝ) ^ n := pow_le_pow_left₀ (abs_nonneg _) hj n
    simpa [abs_pow, one_pow] using! this
  have hmul : |(x.1 i : ℝ) ^ m * (x.1 j : ℝ) ^ n| ≤ (1 : ℝ) := by
    have : |(x.1 i : ℝ) ^ m| * |(x.1 j : ℝ) ^ n| ≤ (1 : ℝ) :=
      mul_le_one₀ hi' (abs_nonneg _) hj'
    simpa [abs_mul] using! this
  simpa [Real.norm_eq_abs] using! hmul

/-- The mixed inner-product monomial `x ↦ ⟪x,u⟫^i * ⟪x,v⟫^j` is integrable on `S23`. -/
public lemma integrable_inner_pow_mul_inner_pow
    {u v : ℝ²⁴} (hu1 : ‖u‖ = (1 : ℝ)) (hv1 : ‖v‖ = (1 : ℝ)) (i j : ℕ) :
    Integrable (fun x : S23 => (⟪x.1, u⟫ : ℝ) ^ i * (⟪x.1, v⟫ : ℝ) ^ j) sphereMeasure24 := by
  letI : IsFiniteMeasure sphereMeasure24 := ⟨by simpa using! sphereMeasure24_univ_lt_top⟩
  have hmeas :
      AEStronglyMeasurable
        (fun x : S23 => (⟪x.1, u⟫ : ℝ) ^ i * (⟪x.1, v⟫ : ℝ) ^ j) sphereMeasure24 := by
    have hcont : Continuous (fun x : S23 => (⟪x.1, u⟫ : ℝ) ^ i * (⟪x.1, v⟫ : ℝ) ^ j) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  refine Integrable.of_bound (μ := sphereMeasure24) hmeas (C := (1 : ℝ)) ?_
  filter_upwards with x
  have hx : ‖(x : ℝ²⁴)‖ = (1 : ℝ) :=
    mem_sphere_zero_iff_norm.mp x.2
  have hU : |(⟪(x : ℝ²⁴), u⟫ : ℝ)| ≤ (1 : ℝ) := by
    simpa [hx, hu1] using! (abs_real_inner_le_norm (x : ℝ²⁴) u)
  have hV : |(⟪(x : ℝ²⁴), v⟫ : ℝ)| ≤ (1 : ℝ) := by
    simpa [hx, hv1] using! (abs_real_inner_le_norm (x : ℝ²⁴) v)
  have hU' : |(⟪(x : ℝ²⁴), u⟫ : ℝ)| ^ i ≤ (1 : ℝ) := by
    simpa using! (pow_le_one₀ (abs_nonneg _) hU)
  have hV' : |(⟪(x : ℝ²⁴), v⟫ : ℝ)| ^ j ≤ (1 : ℝ) := by
    simpa using! (pow_le_one₀ (abs_nonneg _) hV)
  have hV0 : 0 ≤ |(⟪(x : ℝ²⁴), v⟫ : ℝ)| ^ j := pow_nonneg (abs_nonneg _) _
  have habs :
      |((⟪(x : ℝ²⁴), u⟫ : ℝ) ^ i) * ((⟪(x : ℝ²⁴), v⟫ : ℝ) ^ j)| ≤ (1 : ℝ) := by
    calc
      |((⟪(x : ℝ²⁴), u⟫ : ℝ) ^ i) * ((⟪(x : ℝ²⁴), v⟫ : ℝ) ^ j)|
          = |(⟪(x : ℝ²⁴), u⟫ : ℝ) ^ i| * |(⟪(x : ℝ²⁴), v⟫ : ℝ) ^ j| := by
              simp [abs_mul]
      _ = (|(⟪(x : ℝ²⁴), u⟫ : ℝ)| ^ i) * (|(⟪(x : ℝ²⁴), v⟫ : ℝ)| ^ j) := by
            simp [abs_pow]
      _ ≤ (1 : ℝ) * (1 : ℝ) :=
            mul_le_mul hU' hV' hV0 (by positivity)
      _ = (1 : ℝ) := by ring
  simpa [Real.norm_eq_abs] using! habs

/-- Congruence principle for `sphereAvg24`: pointwise equality on `S23` implies equal averages. -/
public lemma sphereAvg24_congr {f g : ℝ²⁴ → ℝ} (h : ∀ x : S23, f x.1 = g x.1) :
    sphereAvg24 f = sphereAvg24 g := by
  unfold sphereAvg24
  simp [funext h]

/-- `sphereAvg24` commutes with negation. -/
public lemma sphereAvg24_neg (f : ℝ²⁴ → ℝ) :
    sphereAvg24 (fun x => -f x) = -sphereAvg24 f := by
  unfold sphereAvg24
  simp [integral_neg]

/-- `sphereAvg24` distributes over a finite sum, assuming integrability of each summand. -/
public lemma sphereAvg24_finset_sum {α : Type*} (s : Finset α) (f : α → ℝ²⁴ → ℝ)
    (hf : ∀ a ∈ s, Integrable (fun x : S23 => f a x.1) sphereMeasure24) :
    sphereAvg24 (fun x => s.sum (fun a => f a x)) = s.sum (fun a => sphereAvg24 (f a)) := by
  unfold sphereAvg24
  have hInt :
      (∫ x : S23, s.sum (fun a => f a x.1) ∂sphereMeasure24) =
        s.sum (fun a => ∫ x : S23, f a x.1 ∂sphereMeasure24) := by
    simpa using!
      (integral_finset_sum (s := s) (f := fun a => fun x : S23 => f a x.1) (fun a ha => hf a ha))
  rw [hInt]
  simp [Finset.mul_sum]

/-- `sphereAvg24` distributes over a double finite sum, assuming integrability of each summand. -/
public lemma sphereAvg24_finset_sum₂ {α β : Type*} (s : Finset α) (t : Finset β)
    (f : α → β → ℝ²⁴ → ℝ)
    (hf : ∀ a ∈ s, ∀ b ∈ t, Integrable (fun x : S23 => f a b x.1) sphereMeasure24) :
    sphereAvg24 (fun x => s.sum (fun a => t.sum (fun b => f a b x))) =
      s.sum (fun a => t.sum (fun b => sphereAvg24 (f a b))) := by
  have hf_t :
      ∀ a ∈ s, Integrable (fun x : S23 => t.sum (fun b => f a b x.1)) sphereMeasure24 :=
    fun a a_1 => integrable_finset_sum t (hf a a_1)
  calc
    sphereAvg24 (fun x => s.sum (fun a => t.sum (fun b => f a b x))) =
        s.sum (fun a => sphereAvg24 (fun x => t.sum (fun b => f a b x))) :=
          sphereAvg24_finset_sum s (fun a x => ∑ b ∈ t, f a b x) hf_t
    _ = s.sum (fun a => t.sum (fun b => sphereAvg24 (f a b))) := by
          refine Finset.sum_congr rfl (fun a ha => ?_)
          simpa using!
            (sphereAvg24_finset_sum (s := t) (f := fun b : β => f a b) (fun b hb => hf a ha b hb))

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14
