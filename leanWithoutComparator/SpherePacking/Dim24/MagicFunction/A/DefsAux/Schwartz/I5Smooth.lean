-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.Prelude
public import SpherePacking.Dim24.MagicFunction.A.DefsAux.Schwartz.I1Decay
import SpherePacking.Dim24.MagicFunction.A.DefsAux.Schwartz.I3Smooth
import SpherePacking.ForMathlib.IteratedDeriv


/-!
# Smoothness and decay of `I₅'`

This file proves smoothness and one-sided Schwartz decay bounds for the integral
`RealIntegrals.I₅'`.

The integral `I₅'` is related to `I₁'` by an explicit exponential factor.

## Main statements
* `Schwartz.I5Smooth.contDiff_I₅'`
* `Schwartz.I5Smooth.decay_I₅'`
-/

section

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

noncomputable section

namespace Schwartz

open MeasureTheory Filter Topology

namespace I5Smooth

open MagicFunction.Parametrisations RealIntegrals
open Complex Real Set MeasureTheory Filter intervalIntegral
open scoped Interval Topology

lemma z₅'_eq_z₁'_add_one (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    z₅' t = z₁' t + 1 := by
  have hz5 : z₅' t = (Complex.I : ℂ) * (t : ℂ) := by
    simpa using! (z₅'_eq_of_mem (t := t) ht)
  have hz1 : z₁' t = (-1 : ℂ) + (Complex.I : ℂ) * (t : ℂ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using! (z₁'_eq_of_mem (t := t) ht)
  rw [hz5, hz1]
  ring

lemma I₅'_eq (x : ℝ) :
    RealIntegrals.I₅' x =
      (-2 : ℂ) * (RealIntegrals.I₁' x * cexp ((x : ℂ) * ((Real.pi : ℂ) * Complex.I))) := by
  have hEq :
      Set.EqOn (RealIntegrals.RealIntegrands.Φ₅ x)
        (fun t : ℝ =>
            RealIntegrals.RealIntegrands.Φ₁ x t *
              cexp ((x : ℂ) * ((Real.pi : ℂ) * Complex.I)))
        ([[ (0 : ℝ), 1 ]]) := by
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using! ht
    have hz : z₅' t = z₁' t + 1 := z₅'_eq_z₁'_add_one (t := t) htIcc
    have hmul :
        (Real.pi : ℂ) * Complex.I * (x : ℂ) * (z₅' t) =
          (Real.pi : ℂ) * Complex.I * (x : ℂ) * (z₁' t) +
            (x : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
      simp [hz, mul_add, mul_assoc, mul_left_comm, mul_comm]
    have hcexp :
        cexp ((Real.pi : ℂ) * Complex.I * (x : ℂ) * (z₅' t)) =
          cexp ((Real.pi : ℂ) * Complex.I * (x : ℂ) * (z₁' t)) *
            cexp ((x : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
      simp [hmul, Complex.exp_add]
    have hcore :
        RealIntegrals.ComplexIntegrands.Φ₅' x (z₅' t) =
          RealIntegrals.ComplexIntegrands.Φ₁' x (z₁' t) *
            cexp ((x : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
      dsimp [RealIntegrals.ComplexIntegrands.Φ₅', RealIntegrals.ComplexIntegrands.Φ₁']
      rw [hcexp]
      simp [hz]
      ac_rfl
    calc
      RealIntegrals.RealIntegrands.Φ₅ x t =
          (Complex.I : ℂ) * RealIntegrals.ComplexIntegrands.Φ₅' x (z₅' t) := rfl
      _ =
          (Complex.I : ℂ) *
            (RealIntegrals.ComplexIntegrands.Φ₁' x (z₁' t) *
              cexp ((x : ℂ) * ((Real.pi : ℂ) * Complex.I))) := by
            simp [hcore]
      _ =
          ((Complex.I : ℂ) * RealIntegrals.ComplexIntegrands.Φ₁' x (z₁' t)) *
            cexp ((x : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
            ring_nf
      _ =
          RealIntegrals.RealIntegrands.Φ₁ x t *
            cexp ((x : ℂ) * ((Real.pi : ℂ) * Complex.I)) := rfl
  have hInt :
      ∫ t in (0 : ℝ)..1, RealIntegrals.RealIntegrands.Φ₅ x t =
        ∫ t in (0 : ℝ)..1,
          RealIntegrals.RealIntegrands.Φ₁ x t * cexp ((x : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
    exact integral_congr hEq
  calc
    RealIntegrals.I₅' x =
        (-2 : ℂ) * ∫ t in (0 : ℝ)..1, RealIntegrals.RealIntegrands.Φ₅ x t := by rfl
    _ =
        (-2 : ℂ) *
          ∫ t in (0 : ℝ)..1,
            RealIntegrals.RealIntegrands.Φ₁ x t * cexp ((x : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
          simp [hInt]
    _ =
        (-2 : ℂ) *
          ((∫ t in (0 : ℝ)..1, RealIntegrals.RealIntegrands.Φ₁ x t) *
            cexp ((x : ℂ) * ((Real.pi : ℂ) * Complex.I))) := by
          simp [intervalIntegral.integral_mul_const]
    _ = (-2 : ℂ) * (RealIntegrals.I₁' x * cexp ((x : ℂ) * ((Real.pi : ℂ) * Complex.I))) := by rfl

/-- Smoothness of `I₅'`. -/
public theorem contDiff_I₅' : ContDiff ℝ (⊤ : ℕ∞) RealIntegrals.I₅' := by
  have hExp :
      ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ cexp ((x : ℂ) * ((Real.pi : ℂ) * Complex.I))) :=
    (ofRealCLM.contDiff.mul contDiff_const).cexp
  have hmul :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun x : ℝ ↦
          -(2 *
              (RealIntegrals.I₁' x *
                cexp ((x : ℂ) * ((Real.pi : ℂ) * Complex.I))))) := by
    simpa using!
      (contDiff_const.mul (I1Smooth.contDiff_I₁'.mul hExp) :
        ContDiff ℝ (⊤ : ℕ∞)
          (fun x : ℝ ↦
            (-2 : ℂ) *
              (RealIntegrals.I₁' x *
                cexp ((x : ℂ) * ((Real.pi : ℂ) * Complex.I)))))
  have hEq :
      (fun x : ℝ ↦
          -(2 *
              (RealIntegrals.I₁' x *
                cexp ((x : ℂ) * ((Real.pi : ℂ) * Complex.I))))) =
        RealIntegrals.I₅' := by
    funext x
    simpa using! (I₅'_eq (x := x)).symm
  simpa [hEq] using! hmul

/-- One-sided Schwartz decay of `I₅'` on the ray `0 ≤ x`. -/
public theorem decay_I₅' :
    ∀ (k n : ℕ), ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₅' x‖ ≤ C := by
  intro k n
  let c : ℂ := (Real.pi : ℂ) * Complex.I
  let e : ℝ → ℂ := fun x ↦ cexp ((x : ℂ) * c)
  let f : ℝ → ℂ := fun x ↦ (-2 : ℂ) • e x
  have he_cont : ContDiff ℝ (⊤ : ℕ∞) e := by
    have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ (x : ℂ) * c) :=
      (ofRealCLM.contDiff.mul contDiff_const)
    simpa [e] using! hlin.cexp
  have hf_cont : ContDiff ℝ (⊤ : ℕ∞) f := by
    simpa [f] using! (he_cont.const_smul (-2 : ℂ))
  have hI1_cont : ContDiff ℝ (⊤ : ℕ∞) RealIntegrals.I₁' := I1Smooth.contDiff_I₁'
  have hbound_f :
      ∀ m : ℕ, ∀ x : ℝ, ‖iteratedFDeriv ℝ m f x‖ ≤ (2 : ℝ) * Real.pi ^ m := by
    intro m x
    have hf_smul :
        iteratedFDeriv ℝ m f x = (-2 : ℂ) • iteratedFDeriv ℝ m e x := by
      have hfAt : ContDiffAt ℝ m e x :=
        (he_cont.contDiffAt).of_le <|
          WithTop.coe_le_coe.2 (show (m : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)
      exact iteratedFDeriv_const_smul_apply' hfAt
    calc
      ‖iteratedFDeriv ℝ m f x‖ = ‖(-2 : ℂ) • iteratedFDeriv ℝ m e x‖ := by simp [hf_smul]
      _ = ‖(-2 : ℂ)‖ * ‖iteratedFDeriv ℝ m e x‖ := by simp [norm_smul]
      _ ≤ (2 : ℝ) * Real.pi ^ m := by
        have hnorm : ‖(-2 : ℂ)‖ = (2 : ℝ) := by norm_num
        have hiter :
            ‖iteratedFDeriv ℝ m e x‖ ≤ Real.pi ^ m := by
          simpa [e, c] using!
            (SpherePacking.ForMathlib.norm_iteratedFDeriv_cexp_mul_pi_I_le (m := m) (x := x))
        have hnorm' : 0 ≤ ‖(-2 : ℂ)‖ := norm_nonneg _
        simpa [hnorm, mul_assoc] using! (mul_le_mul_of_nonneg_left hiter hnorm')
  have hdec1 :
      ∀ m : ℕ, ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ m RealIntegrals.I₁' x‖ ≤ C := by
    intro m
    simpa using! (I1Smooth.decay_I₁' (k := k) (n := m))
  let C1 : ℕ → ℝ := fun m ↦ Classical.choose (hdec1 m)
  let C : ℝ :=
    ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ((2 : ℝ) * Real.pi ^ i) * C1 (n - i)
  refine ⟨C, ?_⟩
  intro x hx
  have hxk0 : 0 ≤ ‖x‖ ^ k := by positivity
  have hmul :
      ‖iteratedFDeriv ℝ n (fun y : ℝ ↦ f y * RealIntegrals.I₁' y) x‖ ≤
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i f x‖ *
            ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖ :=
    norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := (⊤ : ℕ∞)) hf_cont hI1_cont x (n := n)
      (hn := by
        exact WithTop.coe_le_coe.2 (show (n : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
  have hI5fun : RealIntegrals.I₅' = fun y : ℝ ↦ f y * RealIntegrals.I₁' y := by
    funext y
    have hf : f y = (-2 : ℂ) * cexp ((y : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
      simp [f, e, c, mul_left_comm, mul_comm]
    calc
      RealIntegrals.I₅' y =
          (-2 : ℂ) * (RealIntegrals.I₁' y * cexp ((y : ℂ) * ((Real.pi : ℂ) * Complex.I))) := by
            simpa using! (I₅'_eq (x := y))
      _ = f y * RealIntegrals.I₁' y := by
            simp [hf, mul_assoc, mul_left_comm, mul_comm]
  have hmain :
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.I₅' x‖ ≤
        ∑ i ∈ Finset.range (n + 1),
          ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
            ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖) := by
    have hmulI5 :
        ‖iteratedFDeriv ℝ n RealIntegrals.I₅' x‖ ≤
          ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i f x‖ *
              ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖ := by
      simpa [hI5fun.symm] using! hmul
    have h' := mul_le_mul_of_nonneg_left hmulI5 hxk0
    simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using! h'
  have hterm :
      ∀ i ∈ Finset.range (n + 1),
        ‖x‖ ^ k *
            ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
              ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖) ≤
          (n.choose i : ℝ) * ((2 : ℝ) * Real.pi ^ i) * C1 (n - i) := by
    intro i hi
    have hfi : ‖iteratedFDeriv ℝ i f x‖ ≤ (2 : ℝ) * Real.pi ^ i := hbound_f i x
    have hIi : ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖ ≤ C1 (n - i) := by
      simpa [C1] using! (Classical.choose_spec (hdec1 (n - i)) x hx)
    calc
      ‖x‖ ^ k *
            ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
              ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖) =
          (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖) := by
              ring_nf
      _ ≤ (n.choose i : ℝ) * ((2 : ℝ) * Real.pi ^ i) * C1 (n - i) := by
            gcongr
  have hsum :
      (∑ i ∈ Finset.range (n + 1),
          ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
            ‖iteratedFDeriv ℝ (n - i) RealIntegrals.I₁' x‖)) ≤
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((2 : ℝ) * Real.pi ^ i) * C1 (n - i) :=
    Finset.sum_le_sum fun i hi => hterm i hi
  grind only

end Schwartz.I5Smooth
end

end SpherePacking.Dim24

end
