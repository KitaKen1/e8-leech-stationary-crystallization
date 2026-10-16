-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.ThetaUpperHalfPlane
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.EvenUnimodular.ThetaSeries
public import SpherePacking.ModularForms.QExpansion
public import SpherePacking.ModularForms.SlashActionAuxil
public import SpherePacking.ModularForms.E2.Transform
public import SpherePacking.ForMathlib.Cusps
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import SpherePacking.Tactic.NormNumI

/-!
# Theta series as a modular form

This file shows that for an even unimodular lattice `L ⊆ ℝ²⁴`, the analytic theta series
`thetaSeriesUHP L : ℍ → ℂ` defines a weight-12 modular form for `Γ(1)`.

This is the "bridge" between:
* the analytic theta series `thetaSeries` / `thetaSeriesUHP`, and
* the repo's modular-forms framework in `SpherePacking/ModularForms/*`.

## Main statements
* `NiemeierRootless.thetaSeries_is_modularForm_weight12`
-/


namespace SpherePacking.Dim24.Uniqueness.RigidityClassify
noncomputable section

open scoped RealInnerProductSpace

open Complex UpperHalfPlane
open Filter Asymptotics

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace NiemeierRootless

open scoped Manifold ModularForm MatrixGroups

variable (L : Submodule ℤ ℝ²⁴)

private lemma neg_pi_mul_norm_sq_nonpos (v : ℝ²⁴) : -Real.pi * (‖v‖ ^ 2) ≤ 0 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hv0 : 0 ≤ ‖v‖ ^ 2 := by positivity
  nlinarith [hπ, hv0]

private lemma exp_mul_le_exp_mul_of_nonpos_left {a b c : ℝ} (hab : a ≤ b) (hc : c ≤ 0) :
    Real.exp (c * b) ≤ Real.exp (c * a) :=
  (Real.exp_le_exp).2 (mul_le_mul_of_nonpos_left hab hc)

private lemma norm_thetaTerm_le_of_le_im [DiscreteTopology L] [IsZLattice ℝ L] (x : L) (w : ℂ)
    {a : ℝ} (ha : a ≤ w.im) :
    ‖thetaTerm L w x‖ ≤ Real.exp (-Real.pi * (‖(x : ℝ²⁴)‖ ^ 2) * a) := by
  have hcoef : (-Real.pi * (‖(x : ℝ²⁴)‖ ^ 2)) ≤ 0 :=
    neg_pi_mul_norm_sq_nonpos (v := (x : ℝ²⁴))
  have hexp :
      Real.exp ((-Real.pi * (‖(x : ℝ²⁴)‖ ^ 2)) * w.im) ≤
        Real.exp ((-Real.pi * (‖(x : ℝ²⁴)‖ ^ 2)) * a) :=
    exp_mul_le_exp_mul_of_nonpos_left ha hcoef
  simpa [norm_thetaTerm, mul_assoc, mul_left_comm, mul_comm] using! hexp

lemma summable_gaussian [DiscreteTopology L] [IsZLattice ℝ L] {a : ℝ} (ha : 0 < a) :
    Summable fun x : L => Real.exp (-Real.pi * (‖(x : ℝ²⁴)‖ ^ 2) * a) := by
  have haτ : 0 < ((Complex.I : ℂ) * a).im := by simpa using! ha
  have hSumm : Summable fun x : L => thetaTerm L ((Complex.I : ℂ) * a) x :=
    summable_thetaTerm (L := L) (τ := (Complex.I : ℂ) * a) haτ
  simpa [norm_thetaTerm] using! hSumm.norm

lemma thetaSeriesUHP_isBoundedAtImInfty [DiscreteTopology L] [IsZLattice ℝ L] :
    UpperHalfPlane.IsBoundedAtImInfty (thetaSeriesUHP L) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  -- Bound `‖Θ_L(z)‖` for `1 ≤ im z` by a fixed convergent majorant.
  let g : L → ℝ := fun x => Real.exp (-Real.pi * (‖(x : ℝ²⁴)‖ ^ 2) * (1 : ℝ))
  have hg : Summable g :=
    summable_gaussian (L := L) (a := (1 : ℝ)) (by simp)
  refine ⟨∑' x : L, g x, 1, ?_⟩
  intro z hz
  have hbound :
      ‖thetaSeriesUHP L z‖ ≤ ∑' x : L, g x := by
    -- `tsum_of_norm_bounded` with the majorant `g`.
    have hg' : HasSum g (∑' x : L, g x) := hg.hasSum
    -- pointwise bound on the summand
    have hle : ∀ x : L, ‖thetaTerm L (z : ℂ) x‖ ≤ g x := by
      intro x
      -- `‖thetaTerm‖ = exp (-π ‖x‖^2 * im z) ≤ exp (-π ‖x‖^2 * 1)`.
      simpa [g] using!
        (norm_thetaTerm_le_of_le_im (L := L) (x := x) (w := (z : ℂ)) (a := (1 : ℝ))
          (by simpa using! hz))
    -- Conclude.
    simpa [thetaSeriesUHP, thetaSeries] using!
      (tsum_of_norm_bounded (hg := hg') (f := fun x : L => thetaTerm L (z : ℂ) x) hle)
  simpa using! hbound

lemma thetaSeries_is_MDifferentiable [DiscreteTopology L] [IsZLattice ℝ L] :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (thetaSeriesUHP L) := by
  -- Reduce to `Complex` differentiability on `{z | 0 < im z}`.
  rw [UpperHalfPlane.mdifferentiable_iff]
  -- Prove differentiability on the open upper half-plane set via a strip majorant.
  refine ?_
  intro z hz
  have hzIm : 0 < z.im := by simpa using! hz
  -- Work on the smaller open subset `{w | z.im/2 < w.im}` where the series is uniformly bounded.
  let a : ℝ := z.im / 2
  have ha : 0 < a := by
    dsimp [a]
    nlinarith [hzIm]
  let U : Set ℂ := {w : ℂ | a < w.im}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hzU : z ∈ U := by
    dsimp [U, a]
    nlinarith [hzIm]
  -- Majorant `u` on `U`.
  let u : L → ℝ := fun x => Real.exp (-Real.pi * (‖(x : ℝ²⁴)‖ ^ 2) * a)
  have hu : Summable u := summable_gaussian (L := L) (a := a) ha
  have hterm : ∀ x : L, DifferentiableOn ℂ (fun w : ℂ => thetaTerm L w x) U := by
    intro x
    -- `thetaTerm` is `exp (c * w)` with constant `c`.
    let c : ℂ :=
      (Real.pi : ℂ) * Complex.I * ((‖(x : ℝ²⁴)‖ ^ 2 : ℝ) : ℂ)
    have hconst : Differentiable ℂ (fun _ : ℂ => c) := by
      simp
    have hid : Differentiable ℂ (fun w : ℂ => w) := differentiable_id
    have hdiff : Differentiable ℂ (fun w : ℂ => Complex.exp (c * w)) := (hconst.mul hid).cexp
    simpa [thetaTerm, c, mul_assoc, mul_left_comm, mul_comm] using! hdiff.differentiableOn
  have hle : ∀ (x : L) (w : ℂ), w ∈ U → ‖thetaTerm L w x‖ ≤ u x := by
    intro x w hw
    have ha_le : a ≤ w.im := le_of_lt hw
    simpa [u] using! (norm_thetaTerm_le_of_le_im (L := L) (x := x) (w := w) ha_le)
  have hUdiff :
      DifferentiableOn ℂ (fun w : ℂ => ∑' x : L, thetaTerm L w x) U :=
    Complex.differentiableOn_tsum_of_summable_norm (U := U)
      (F := fun x : L => fun w : ℂ => thetaTerm L w x)
      (hu := hu) (hf := hterm) (hU := hUopen) (hF_le := hle)
  -- Get a `DifferentiableAt` statement at `z` from the open neighborhood `U`.
  have hAt : DifferentiableAt ℂ (fun w : ℂ => ∑' x : L, thetaTerm L w x) z :=
    (hUdiff z hzU).differentiableAt (hUopen.mem_nhds hzU)
  have hWithin :
      DifferentiableWithinAt ℂ (thetaSeries L) {w : ℂ | 0 < w.im} z := by
    -- `thetaSeries` is definitional the tsum.
    simpa [thetaSeries] using! (hAt.differentiableWithinAt)
  -- Convert from `thetaSeries` to `thetaSeriesUHP ∘ ofComplex` on `{im>0}`.
  have hEq :
      ∀ w ∈ {w : ℂ | 0 < w.im},
        (thetaSeriesUHP L ∘ UpperHalfPlane.ofComplex) w = thetaSeries L w := by
    intro w hw
    have hw' : 0 < w.im := by simpa using! hw
    simp [Function.comp, thetaSeriesUHP, UpperHalfPlane.ofComplex_apply_of_im_pos hw']
  exact hWithin.congr hEq (hEq z hz)

/-- For an even unimodular lattice `L`, the theta series is a modular form of weight `12`. -/
public theorem thetaSeries_is_modularForm_weight12 [DiscreteTopology L] [IsZLattice ℝ L]
    (hEven : EvenNormSq L) (hUnimod : Unimodular L) :
    ∃ f : ModularForm (CongruenceSubgroup.Gamma 1) (12 : ℤ),
      (∀ z : UpperHalfPlane, f z = thetaSeriesUHP L z) := by
  let θ : UpperHalfPlane → ℂ := thetaSeriesUHP L
  have hT : θ ∣[(12 : ℤ)] ModularGroup.T = θ := by
    ext z
    -- Slash under `T` is translation by `1`.
    simpa [modular_slash_T_apply, θ] using!
      (thetaSeriesUHP_vadd_one (L := L) hEven z)
  have hS : θ ∣[(12 : ℤ)] ModularGroup.S = θ := by
    ext z
    -- Use the explicit `S`-law from Poisson summation and simplify the weight factor.
    have hz0 : (z : ℂ) ≠ 0 := by exact ne_zero z
    have hθS :=
      thetaSeriesUHP_mk_inv_neg (L := L) hEven hUnimod z
    -- Expand the slash action under `S`.
    rw [modular_slash_S_apply (f := θ) (k := (12 : ℤ)) (z := z)]
    -- Substitute the `S`-transformation formula.
    have hθS' :
        θ (UpperHalfPlane.mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos) =
          (-(z : ℂ) * Complex.I) ^ (12 : ℂ) * θ z := by
      simpa [θ] using! hθS
    rw [hθS']
    -- Convert the complex-power `(^ (12 : ℂ))` to an ordinary power, then simplify `(-z*I)^12`.
    have hcpow :
        (-(z : ℂ) * Complex.I) ^ (12 : ℂ) = (-(z : ℂ) * Complex.I) ^ (12 : ℕ) := by
      exact Complex.cpow_natCast (-(z : ℂ) * Complex.I) 12
    have hpow : (-(z : ℂ) * Complex.I) ^ (12 : ℕ) = (z : ℂ) ^ (12 : ℕ) := by
      -- `((-z) * I) ^ 12 = (-z) ^ 12 * I ^ 12 = z ^ 12`, since `I ^ 12 = 1`.
      have hI12 : (Complex.I : ℂ) ^ (12 : ℕ) = 1 := by norm_num1
      grind only
    -- Reduce `z ^ (-12)` to an inverse and cancel.
    have hzpow : z ^ (-(12 : ℤ)) = ((z : ℂ) ^ (12 : ℕ))⁻¹ := by
      -- `z ^ (-12) = (z ^ 12)⁻¹`, and `z ^ 12` is a Nat power.
      rfl
    rw [hcpow, hpow]
    rw [hzpow]
    have hz12 : ((z : ℂ) ^ (12 : ℕ)) ≠ 0 := pow_ne_zero _ hz0
    -- rearrange using commutativity
    calc
      ((z : ℂ) ^ (12 : ℕ) * θ z) * ((z : ℂ) ^ (12 : ℕ))⁻¹
          = θ z * (((z : ℂ) ^ (12 : ℕ)) * ((z : ℂ) ^ (12 : ℕ))⁻¹) := by
              ac_rfl
      _ = θ z := by
            simp [hz12]
  -- Bundle as a `SlashInvariantForm` and then as a `ModularForm`.
  let θSIF : SlashInvariantForm (CongruenceSubgroup.Gamma 1) (12 : ℤ) :=
    { toFun := θ
      slash_action_eq' := slashaction_generators_GL2R θ 12 hS hT }
  have hθbdd : UpperHalfPlane.IsBoundedAtImInfty θ := thetaSeriesUHP_isBoundedAtImInfty (L := L)
  have hθbdd_slash :
      ∀ A ∈ 𝒮ℒ, UpperHalfPlane.IsBoundedAtImInfty (θ ∣[(12 : ℤ)] (A : GL (Fin 2) ℝ)) := by
    intro A hA
    rcases hA with ⟨A', rfl⟩
    -- Any slash by an element of `SL(2,ℤ)` is just itself, since we proved invariance under `S,T`.
    have θ_SL2Z_invariant :
        ∀ γ : SL(2, ℤ), θ ∣[(12 : ℤ)] γ = θ :=
      slashaction_generators_SL2Z θ 12 hS hT
    have θ_slash_eq (A' : SL(2, ℤ)) :
        θ ∣[(12 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ A') = θ := by
      simpa [ModularForm.SL_slash] using! θ_SL2Z_invariant A'
    rw [θ_slash_eq A']
    exact hθbdd
  let θMF : ModularForm (CongruenceSubgroup.Gamma 1) (12 : ℤ) :=
    { θSIF with
      holo' := thetaSeries_is_MDifferentiable (L := L)
      bdd_at_cusps' := fun hc =>
        bounded_at_cusps_of_bounded_at_infty (k := (12 : ℤ)) (f := θ) hc hθbdd_slash }
  refine ⟨θMF, ?_⟩
  intro z
  rfl

end NiemeierRootless

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
