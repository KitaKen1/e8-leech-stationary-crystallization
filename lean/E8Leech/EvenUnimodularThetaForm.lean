import E8Leech.EvenUnimodularTheta
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex

/-!
# The theta series of an even unimodular lattice of rank eight is a modular form of weight four

For the lattice `L` of an `EvenUnimodularGram`, the theta series

`θ(τ) = ∑_{ℓ ∈ L} e^{π i τ |ℓ|²}`

is holomorphic on the upper half plane and bounded at `i∞`. It is invariant under `τ ↦ τ + 1`
because `|ℓ|²` is even, and satisfies `θ(-1/τ) = τ⁴ θ(τ)`: on the imaginary axis this is the
inversion of the Gaussian sum (`EvenUnimodularGram.gaussianSum_inv`), and the identity theorem
extends it to the upper half plane. Hence `θ` is a modular form of weight four and level one
(`EvenUnimodularGram.thetaForm`).
-/

noncomputable section

namespace E8Leech

open Complex Filter Set MatrixGroups ModularForm SlashInvariantForm
open UpperHalfPlane hiding I
open scoped Real Topology

/-- The Gaussian decreases in its parameter. -/
theorem gaussianKernel_le_of_le {d : ℕ} {α β : ℝ} (hαβ : α ≤ β) (x : Ambient d) :
    gaussianKernel β x ≤ gaussianKernel α x := by
  unfold gaussianKernel
  apply Real.exp_le_exp.mpr
  have h1 : α * ‖x‖ ^ 2 ≤ β * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right hαβ (sq_nonneg _)
  linarith

/-- `-1/τ` lies in the upper half plane when `τ` does. -/
theorem im_neg_inv_pos {τ : ℂ} (hτ : 0 < τ.im) : 0 < (-τ⁻¹).im := by
  have hne : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  exact div_pos hτ (Complex.normSq_pos.mpr hne)

namespace EvenUnimodularGram

variable {z : Fin 8 → Ambient 8} {M : Matrix (Fin 8) (Fin 8) ℤ}

/-- A term of the theta series. -/
def thetaTerm (h : EvenUnimodularGram z M) (ℓ : h.zlattice) (τ : ℂ) : ℂ :=
  Complex.exp (π * I * τ * ((‖(ℓ : Ambient 8)‖ ^ 2 : ℝ) : ℂ))

/-- The theta series `θ(τ) = ∑_{ℓ ∈ L} e^{π i τ |ℓ|²}`, as a function on `ℂ`. -/
def theta (h : EvenUnimodularGram z M) (τ : ℂ) : ℂ :=
  ∑' ℓ : h.zlattice, h.thetaTerm ℓ τ

theorem norm_thetaTerm (h : EvenUnimodularGram z M) (ℓ : h.zlattice) (τ : ℂ) :
    ‖h.thetaTerm ℓ τ‖ = gaussianKernel (π * τ.im) (ℓ : Ambient 8) := by
  rw [thetaTerm, Complex.norm_exp, gaussianKernel]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

theorem summable_norm_thetaTerm (h : EvenUnimodularGram z M) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun ℓ : h.zlattice => ‖h.thetaTerm ℓ τ‖ :=
  (h.summable_gaussianSum hτ).congr fun ℓ => (h.norm_thetaTerm ℓ τ).symm

theorem hasSum_theta (h : EvenUnimodularGram z M) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun ℓ : h.zlattice => h.thetaTerm ℓ τ) (h.theta τ) :=
  (Summable.of_norm (h.summable_norm_thetaTerm hτ)).hasSum

/-- The theta series is holomorphic on the upper half plane. -/
theorem differentiableAt_theta (h : EvenUnimodularGram z M) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ h.theta τ := by
  have hδ : 0 < τ.im / 2 := half_pos hτ
  have hopen : IsOpen {w : ℂ | τ.im / 2 < w.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hd : DifferentiableOn ℂ (fun w => ∑' ℓ : h.zlattice, h.thetaTerm ℓ w)
      {w : ℂ | τ.im / 2 < w.im} := by
    refine differentiableOn_tsum_of_summable_norm (h.summable_gaussianSum hδ) (fun ℓ => ?_) hopen
      fun ℓ w hw => ?_
    · unfold thetaTerm
      fun_prop
    · rw [h.norm_thetaTerm]
      exact gaussianKernel_le_of_le
        (mul_le_mul_of_nonneg_left (show τ.im / 2 < w.im from hw).le Real.pi_pos.le) _
  exact (hd τ (half_lt_self hτ)).differentiableAt (hopen.mem_nhds (half_lt_self hτ))

/-- On the imaginary axis the theta series is the Gaussian sum. -/
theorem theta_I_mul (h : EvenUnimodularGram z M) (t : ℝ) :
    h.theta (I * t) = ((h.gaussianSum t : ℝ) : ℂ) := by
  rw [theta, gaussianSum, Complex.ofReal_tsum]
  refine tsum_congr fun ℓ => ?_
  rw [thetaTerm, gaussianKernel, Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination ((π : ℂ) * t * (‖(ℓ : Ambient 8)‖ : ℂ) ^ 2) * Complex.I_mul_I

/-- The inversion formula on the imaginary axis. -/
theorem theta_neg_inv_axis (h : EvenUnimodularGram z M) {t : ℝ} (ht : 0 < t) :
    h.theta (-(I * (t : ℂ))⁻¹) = (I * (t : ℂ)) ^ 4 * h.theta (I * t) := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have e1 : -(I * (t : ℂ))⁻¹ = I * ((t⁻¹ : ℝ) : ℂ) := by
    rw [mul_inv, Complex.inv_I]
    push_cast
    ring
  have e2 : (I * (t : ℂ)) ^ 4 = ((t ^ 4 : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_pow_four]
    push_cast
    ring
  rw [e1, e2, h.theta_I_mul, h.theta_I_mul, h.gaussianSum_inv ht]
  push_cast
  field_simp

/-- **The inversion formula** `θ(-1/τ) = τ⁴ θ(τ)` on the upper half plane. -/
theorem theta_neg_inv (h : EvenUnimodularGram z M) {τ : ℂ} (hτ : 0 < τ.im) :
    h.theta (-τ⁻¹) = τ ^ 4 * h.theta τ := by
  have hUo : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hne : ∀ w ∈ {w : ℂ | 0 < w.im}, w ≠ 0 := by
    rintro w hw rfl
    simp at hw
  have hf : AnalyticOnNhd ℂ (fun w => h.theta (-w⁻¹)) {w : ℂ | 0 < w.im} := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    have h1 : DifferentiableAt ℂ (fun w : ℂ => -w⁻¹) w :=
      (differentiableAt_id.inv (hne w hw)).neg
    exact ((h.differentiableAt_theta (im_neg_inv_pos hw)).comp w h1).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ (fun w => w ^ 4 * h.theta w) {w : ℂ | 0 < w.im} := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    exact ((differentiableAt_id.pow 4).mul (h.differentiableAt_theta hw)).differentiableWithinAt
  have hconn : IsPreconnected {w : ℂ | 0 < w.im} := (convex_halfSpace_im_gt 0).isPreconnected
  have hI : I ∈ {w : ℂ | 0 < w.im} := by simp
  have htend : Tendsto (fun t : ℝ => I * (t : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] I) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : Continuous fun t : ℝ => I * (t : ℂ) := by fun_prop
      have ht := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
      simpa using ht
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro e
      have e' : (t : ℂ) = 1 := mul_left_cancel₀ Complex.I_ne_zero (by rw [e, mul_one])
      exact (Set.mem_Ioi.mp ht).ne' (by exact_mod_cast e')
  have hfreq : ∃ᶠ w in 𝓝[≠] I,
      (fun w => h.theta (-w⁻¹)) w = (fun w => w ^ 4 * h.theta w) w := by
    refine htend.frequently (Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact h.theta_neg_inv_axis (lt_trans one_pos (Set.mem_Ioi.mp ht))
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hconn hI hfreq hτ

theorem thetaTerm_add_one (h : EvenUnimodularGram z M) (ℓ : h.zlattice) (τ : ℂ) :
    h.thetaTerm ℓ (τ + 1) = h.thetaTerm ℓ τ := by
  obtain ⟨k, hk⟩ := h.even_norm_sq (h.mem_zlattice.mp ℓ.2)
  unfold thetaTerm
  rw [hk]
  have e : (π : ℂ) * I * (τ + 1) * ((2 * (k : ℝ) : ℝ) : ℂ) =
      π * I * τ * ((2 * (k : ℝ) : ℝ) : ℂ) + (k : ℂ) * (2 * π * I) := by
    push_cast
    ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The theta series has period one: `|ℓ|²` is even. -/
theorem theta_add_one (h : EvenUnimodularGram z M) (τ : ℂ) : h.theta (τ + 1) = h.theta τ := by
  unfold theta
  exact tsum_congr fun ℓ => h.thetaTerm_add_one ℓ τ

/-- The theta series on the upper half plane. -/
def thetaFun (h : EvenUnimodularGram z M) (τ : ℍ) : ℂ := h.theta (τ : ℂ)

set_option backward.isDefEq.respectTransparency.types false in
theorem thetaFun_T (h : EvenUnimodularGram z M) :
    (h.thetaFun ∣[(4 : ℤ)] ModularGroup.T) = h.thetaFun := by
  ext τ
  have hco : (((1 : ℝ) +ᵥ τ : ℍ) : ℂ) = (τ : ℂ) + 1 := by
    rw [UpperHalfPlane.coe_vadd, Complex.ofReal_one, add_comm]
  rw [SL_slash_apply, denom, modular_T_smul, ModularGroup.T]
  simp [thetaFun, hco, h.theta_add_one]

set_option backward.isDefEq.respectTransparency.types false in
theorem thetaFun_S (h : EvenUnimodularGram z M) :
    (h.thetaFun ∣[(4 : ℤ)] ModularGroup.S) = h.thetaFun := by
  ext τ
  suffices h.theta (-(τ : ℂ)⁻¹) * ((τ : ℂ) ^ 4)⁻¹ = h.theta τ by
    rw [SL_slash_apply, UpperHalfPlane.modular_S_smul]
    simpa [thetaFun, denom, ModularGroup.S]
  have hpos : 0 < (τ : ℂ).im := by
    rw [UpperHalfPlane.coe_im]
    exact τ.im_pos
  rw [h.theta_neg_inv hpos, mul_comm, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 4 τ.ne_zero),
    one_mul]

/-- The theta series is bounded at `i∞`. -/
theorem isBoundedAtImInfty_thetaFun (h : EvenUnimodularGram z M) :
    IsBoundedAtImInfty h.thetaFun := by
  rw [isBoundedAtImInfty_iff]
  refine ⟨h.gaussianSum 1, 1, fun τ hτ => ?_⟩
  have hpos : 0 < (τ : ℂ).im := by
    rw [UpperHalfPlane.coe_im]
    exact τ.im_pos
  have hs := h.summable_norm_thetaTerm hpos
  have h1 : ‖h.thetaFun τ‖ ≤ ∑' ℓ : h.zlattice, ‖h.thetaTerm ℓ τ‖ :=
    norm_tsum_le_tsum_norm hs
  have h2 : ∑' ℓ : h.zlattice, ‖h.thetaTerm ℓ τ‖ ≤
      ∑' ℓ : h.zlattice, gaussianKernel (π * 1) (ℓ : Ambient 8) := by
    refine Summable.tsum_le_tsum (fun ℓ => ?_) hs (h.summable_gaussianSum one_pos)
    rw [h.norm_thetaTerm, UpperHalfPlane.coe_im]
    exact gaussianKernel_le_of_le (mul_le_mul_of_nonneg_left hτ Real.pi_pos.le) _
  exact h1.trans h2

/-- **The theta series is a modular form of weight four and level one.** -/
def thetaForm (h : EvenUnimodularGram z M) : ModularForm 𝒮ℒ 4 where
  toFun := h.thetaFun
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact slash_action_generators_SL2Z h.thetaFun_S h.thetaFun_T A
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine DifferentiableOn.congr (f := h.theta)
      (fun w hw => (h.differentiableAt_theta hw).differentiableWithinAt) fun w hw => ?_
    simp [thetaFun, ofComplex_apply_of_im_pos hw]
  bdd_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slash_action_generators_SL2Z h.thetaFun_S h.thetaFun_T]
    exact h.isBoundedAtImInfty_thetaFun

theorem thetaForm_apply (h : EvenUnimodularGram z M) (τ : ℍ) :
    h.thetaForm τ = h.theta (τ : ℂ) := rfl

end EvenUnimodularGram

end E8Leech
