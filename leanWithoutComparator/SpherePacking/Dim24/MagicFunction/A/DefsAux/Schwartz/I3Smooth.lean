-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.Prelude
import SpherePacking.Dim24.MagicFunction.A.DefsAux.Schwartz.I1Decay
import SpherePacking.ForMathlib.IteratedDeriv

/-!
# Smoothness and decay of `I₃'`

This file proves smoothness and one-sided Schwartz decay bounds for the integral
`RealIntegrals.I₃'`.

The integral `I₃'` is related to `I₁'` by an explicit exponential factor.

## Main statements
* `Schwartz.I3Smooth.contDiff_I₃'`
* `Schwartz.I3Smooth.decay_I₃'`
-/

section

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

noncomputable section

namespace Schwartz

open MeasureTheory Filter Topology

namespace I3Smooth

open MagicFunction.Parametrisations RealIntegrals
open Complex Real Set MeasureTheory Filter intervalIntegral
open scoped Interval Topology

private lemma z₃'_eq_z₁'_add_two (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    z₃' t = z₁' t + 2 := by
  have hz3 : z₃' t = (1 : ℂ) + (Complex.I : ℂ) * (t : ℂ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using! (z₃'_eq_of_mem (t := t) ht)
  have hz1 : z₁' t = (-1 : ℂ) + (Complex.I : ℂ) * (t : ℂ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using! (z₁'_eq_of_mem (t := t) ht)
  calc
    z₃' t = (1 : ℂ) + (Complex.I : ℂ) * (t : ℂ) := hz3
    _ = z₁' t + 2 := by
      simp [hz1]
      ring

private lemma I₃'_eq (x : ℝ) :
    RealIntegrals.I₃' x =
      RealIntegrals.I₁' x *
        cexp ((x : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)) := by
  -- Rewrite the integrand using `z₃' t = z₁' t + 2`, then pull out the constant exponential factor.
  have hEq :
      Set.EqOn (RealIntegrals.RealIntegrands.Φ₃ x)
        (fun t : ℝ =>
            RealIntegrals.RealIntegrands.Φ₁ x t *
              cexp ((x : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)))
        ([[ (0 : ℝ), 1 ]]) := by
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using! ht
    have hz : z₃' t = z₁' t + 2 := z₃'_eq_z₁'_add_two (t := t) htIcc
    have hsub : z₃' t - 1 = z₁' t + 1 := by
      calc
        z₃' t - 1 = (z₁' t + 2) - 1 := by simp [hz]
        _ = z₁' t + 1 := by ring
    have hmul :
        (Real.pi : ℂ) * Complex.I * (x : ℂ) * (z₃' t) =
          (Real.pi : ℂ) * Complex.I * (x : ℂ) * (z₁' t) +
            (x : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) := by
      -- expand `z₃' t = z₁' t + 2` and normalize
      simp [hz, mul_add, mul_assoc, mul_left_comm, mul_comm]
    have hcexp :
        cexp ((Real.pi : ℂ) * Complex.I * (x : ℂ) * (z₃' t)) =
          cexp ((Real.pi : ℂ) * Complex.I * (x : ℂ) * (z₁' t)) *
            cexp ((x : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)) := by
      simp [hmul, Complex.exp_add]
    have hcore :
        RealIntegrals.ComplexIntegrands.Φ₃' x (z₃' t) =
          RealIntegrals.ComplexIntegrands.Φ₁' x (z₁' t) *
            cexp ((x : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)) := by
      dsimp [RealIntegrals.ComplexIntegrands.Φ₃', RealIntegrals.ComplexIntegrands.Φ₁']
      simp only [hsub]
      rw [hcexp]
      ac_rfl
    calc
      RealIntegrals.RealIntegrands.Φ₃ x t =
          (Complex.I : ℂ) * RealIntegrals.ComplexIntegrands.Φ₃' x (z₃' t) := rfl
      _ =
          (Complex.I : ℂ) *
            (RealIntegrals.ComplexIntegrands.Φ₁' x (z₁' t) *
              cexp ((x : ℂ) * ((2 * Real.pi : ℂ) * Complex.I))) := by
            simp [hcore]
      _ =
          ((Complex.I : ℂ) * RealIntegrals.ComplexIntegrands.Φ₁' x (z₁' t)) *
            cexp ((x : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)) := by
            ring_nf
      _ =
          RealIntegrals.RealIntegrands.Φ₁ x t *
            cexp ((x : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)) := rfl
  have hInt :
      ∫ t in (0 : ℝ)..1, RealIntegrals.RealIntegrands.Φ₃ x t =
        ∫ t in (0 : ℝ)..1,
          RealIntegrals.RealIntegrands.Φ₁ x t *
            cexp ((x : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)) :=
    integral_congr hEq
  calc
    RealIntegrals.I₃' x =
        ∫ t in (0 : ℝ)..1, RealIntegrals.RealIntegrands.Φ₃ x t := by rfl
    _ =
        ∫ t in (0 : ℝ)..1,
          RealIntegrals.RealIntegrands.Φ₁ x t *
            cexp ((x : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)) := by
            simpa [RealIntegrals.I₃'] using! hInt
    _ =
        (∫ t in (0 : ℝ)..1, RealIntegrals.RealIntegrands.Φ₁ x t) *
          cexp ((x : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)) := by
            simp [intervalIntegral.integral_mul_const]
    _ = RealIntegrals.I₁' x * cexp ((x : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)) := by rfl

/-- Smoothness of `I₃'`. -/
public theorem contDiff_I₃' : ContDiff ℝ (⊤ : ℕ∞) RealIntegrals.I₃' := by
  have hExp :
      ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ cexp ((x : ℂ) * ((2 * Real.pi : ℂ) * Complex.I))) :=
    (ofRealCLM.contDiff.mul contDiff_const).cexp
  have hmul :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun x : ℝ ↦ RealIntegrals.I₁' x * cexp ((x : ℂ) * ((2 * Real.pi : ℂ) * Complex.I))) :=
    I1Smooth.contDiff_I₁'.mul hExp
  have hEq :
      (fun x : ℝ ↦ RealIntegrals.I₁' x * cexp ((x : ℂ) * ((2 * Real.pi : ℂ) * Complex.I))) =
        RealIntegrals.I₃' := by
    funext x
    simpa using! (I₃'_eq (x := x)).symm
  simpa [hEq] using! hmul

/-- One-sided Schwartz decay of `I₃'` on the ray `0 ≤ x`. -/
public theorem decay_I₃' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₃' x‖ ≤ C := by
  intro k n
  let c : ℂ := ((2 * Real.pi : ℝ) : ℂ) * Complex.I
  let e : ℝ → ℂ := fun x ↦ cexp ((x : ℂ) * c)
  have he_cont : ContDiff ℝ (⊤ : ℕ∞) e := by
    have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ (x : ℂ) * c) :=
      (ofRealCLM.contDiff.mul contDiff_const)
    simpa [e] using! hlin.cexp
  have hI1_cont : ContDiff ℝ (⊤ : ℕ∞) RealIntegrals.I₁' := I1Smooth.contDiff_I₁'
  have hnorm_e : ∀ x : ℝ, ‖e x‖ = 1 := by
    intro x
    have hz : (x : ℂ) * c = ((x * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      simp [c, mul_left_comm, mul_comm]
    simp [e, Complex.norm_exp, hz]
  have hc_norm : ‖c‖ = (2 * Real.pi : ℝ) := by
    have h2pi0 : 0 ≤ (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
    have hnormR : ‖((2 * Real.pi : ℝ) : ℂ)‖ = (2 * Real.pi : ℝ) :=
      Complex.norm_of_nonneg h2pi0
    calc
      ‖c‖ = ‖((2 * Real.pi : ℝ) : ℂ)‖ * ‖(Complex.I : ℂ)‖ := by
        simp [c]
      _ = ‖((2 * Real.pi : ℝ) : ℂ)‖ := by simp
      _ = (2 * Real.pi : ℝ) := hnormR
  have hiter_e : ∀ m : ℕ, iteratedDeriv m e = fun x : ℝ ↦ c ^ m * e x := by
    intro m
    simpa [e] using! (SpherePacking.ForMathlib.iteratedDeriv_cexp_mul_const (c := c) m)
  have hbound_e :
      ∀ m : ℕ, ∀ x : ℝ, ‖iteratedFDeriv ℝ m e x‖ ≤ (2 * Real.pi) ^ m := by
    intro m x
    have hnorm_iter :
        ‖iteratedFDeriv ℝ m e x‖ = ‖iteratedDeriv m e x‖ := by
      simpa using!
        (norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ) (n := m) (f := e) (x := x))
    simp_all
  have hdec1 :
      ∀ m : ℕ, ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ m RealIntegrals.I₁' x‖ ≤ C := by
    intro m
    simpa using! (I1Smooth.decay_I₁' (k := k) (n := m))
  let C1 : ℕ → ℝ := fun m ↦ Classical.choose (hdec1 m)
  let C : ℝ :=
    ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ((2 * Real.pi) ^ i) * C1 (n - i)
  refine ⟨C, ?_⟩
  intro x hx
  have hxk0 : 0 ≤ ‖x‖ ^ k := by positivity
  have hmul :
      ‖iteratedFDeriv ℝ n (fun y : ℝ ↦ e y * RealIntegrals.I₁' y) x‖ ≤
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i e x‖ *
            ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖ :=
    norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := (⊤ : ℕ∞)) he_cont hI1_cont x (n := n)
      (hn :=
        WithTop.coe_le_coe.2 (show (n : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
  have hI3fun : RealIntegrals.I₃' = fun y : ℝ ↦ e y * RealIntegrals.I₁' y := by
    funext y
    have he' : cexp ((y : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)) = e y := by
      simp [e, c, mul_left_comm, mul_comm]
    calc
      RealIntegrals.I₃' y =
          RealIntegrals.I₁' y * cexp ((y : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)) := by
            simpa using! (I₃'_eq (x := y))
      _ = RealIntegrals.I₁' y * e y := by simp [he']
      _ = e y * RealIntegrals.I₁' y := by ac_rfl
  have hmain :
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₃' x‖ ≤
        ∑ i ∈ Finset.range (n + 1),
          ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i e x‖ *
            ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖) := by
    have hmulI3 :
        ‖iteratedFDeriv ℝ n RealIntegrals.I₃' x‖ ≤
          ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i e x‖ *
              ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖ := by
      simpa [hI3fun.symm] using! hmul
    have h' := mul_le_mul_of_nonneg_left hmulI3 hxk0
    simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using! h'
  have hterm :
      ∀ i ∈ Finset.range (n + 1),
        ‖x‖ ^ k *
            ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i e x‖ *
              ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖) ≤
          (n.choose i : ℝ) * ((2 * Real.pi) ^ i) * C1 (n - i) := by
    intro i hi
    have hei : ‖iteratedFDeriv ℝ i e x‖ ≤ (2 * Real.pi) ^ i := hbound_e i x
    have hIi : ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖ ≤ C1 (n - i) := by
      simpa [C1] using! (Classical.choose_spec (hdec1 (n - i)) x hx)
    calc
      ‖x‖ ^ k *
            ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i e x‖ *
              ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖) =
          (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i e x‖ *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖) := by
              ring_nf
      _ ≤ (n.choose i : ℝ) * ((2 * Real.pi) ^ i) * C1 (n - i) := by
            gcongr
  have hsum :
      (∑ i ∈ Finset.range (n + 1),
          ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i e x‖ *
            ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖)) ≤
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((2 * Real.pi) ^ i) * C1 (n - i) :=
    Finset.sum_le_sum fun i hi => hterm i hi
  grind only

end Schwartz.I3Smooth
end

end SpherePacking.Dim24

end
