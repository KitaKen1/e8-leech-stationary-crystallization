import E8Leech.EvenUnimodularThetaForm
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# An even unimodular lattice of rank eight is isometric to `E8`

The theta series of the lattice `L` of an `EvenUnimodularGram` is a modular form of weight four
and level one, and that space is spanned by the Eisenstein series `E₄`. Grouping the theta series
by the norm gives its `q`-expansion `∑ N_m q^m`, where `N_m` is the number of lattice vectors of
squared norm `2m`. Comparing with `E₄ = 1 + 240 q + 2160 q² + ⋯` gives `N₁ = 240` and
`N₂ = 2160`, which is the input of `exists_isometry_image_e8Set_eq_of_counts`.

* `EvenUnimodularGram.thetaForm_eq_E₄`
* `EvenUnimodularGram.shellCount_one`, `EvenUnimodularGram.shellCount_two`
* `EvenUnimodularGram.exists_isometry_image_e8Set_eq`: the lattice is isometric to `E8`. The
  classification of even unimodular lattices is not used.
-/

noncomputable section

namespace E8Leech

open Complex Filter Set MatrixGroups ModularForm EisensteinSeries
open UpperHalfPlane hiding I
open scoped Real Topology InnerProductSpace ArithmeticFunction.sigma

/-- The second coefficient of `E₄`. -/
theorem E₄_qExpansion_coeff_two : (qExpansion 1 E₄).coeff 2 = 2160 := by
  have hσ : σ 3 2 = 9 := by decide
  have hb : bernoulli 4 = -1 / 30 := by decide +kernel
  rw [E_qExpansion_coeff _ ⟨2, rfl⟩]
  norm_num [hσ, hb]

namespace EvenUnimodularGram

variable {z : Fin 8 → Ambient 8} {M : Matrix (Fin 8) (Fin 8) ℤ}

/-- Half the squared norm of a lattice vector, a natural number. -/
def halfNormSq (h : EvenUnimodularGram z M) (ℓ : h.zlattice) : ℕ :=
  ⌊‖(ℓ : Ambient 8)‖ ^ 2 / 2⌋₊

theorem norm_sq_eq (h : EvenUnimodularGram z M) (ℓ : h.zlattice) :
    ‖(ℓ : Ambient 8)‖ ^ 2 = 2 * (h.halfNormSq ℓ : ℝ) := by
  obtain ⟨k, hk⟩ := h.even_norm_sq (h.mem_zlattice.mp ℓ.2)
  have hk0 : 0 ≤ k := by
    have h1 : (0 : ℝ) ≤ 2 * k := by
      rw [← hk]
      positivity
    have h2 : (0 : ℝ) ≤ k := by linarith
    exact_mod_cast h2
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
  have e : h.halfNormSq ℓ = n := by
    unfold halfNormSq
    rw [hk]
    have e1 : (2 * (((n : ℕ) : ℤ) : ℝ)) / 2 = (n : ℝ) := by
      push_cast
      ring
    rw [e1, Nat.floor_natCast]
  rw [e, hk, Int.cast_natCast]

/-- A term of the theta series is a power of `q = e^{2π i τ}`. -/
theorem thetaTerm_eq_pow (h : EvenUnimodularGram z M) (ℓ : h.zlattice) (τ : ℂ) :
    h.thetaTerm ℓ τ = Complex.exp (2 * π * I * τ) ^ h.halfNormSq ℓ := by
  rw [thetaTerm, h.norm_sq_eq ℓ, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- There are finitely many lattice vectors of a given norm. -/
theorem finite_fiber (h : EvenUnimodularGram z M) (m : ℕ) :
    (h.halfNormSq ⁻¹' {m} : Set h.zlattice).Finite := by
  have ht := (h.summable_gaussianSum one_pos).tendsto_cofinite_zero
  have hε : 0 < Real.exp (-(π * 1) * (2 * (m : ℝ))) := Real.exp_pos _
  have hev : ∀ᶠ ℓ : h.zlattice in Filter.cofinite,
      gaussianKernel (π * 1) (ℓ : Ambient 8) < Real.exp (-(π * 1) * (2 * (m : ℝ))) :=
    ht.eventually (gt_mem_nhds hε)
  have hfin : {ℓ : h.zlattice | ¬ gaussianKernel (π * 1) (ℓ : Ambient 8) <
      Real.exp (-(π * 1) * (2 * (m : ℝ)))}.Finite := Filter.eventually_cofinite.mp hev
  refine hfin.subset fun ℓ hℓ => ?_
  have hℓ' : h.halfNormSq ℓ = m := hℓ
  show ¬ gaussianKernel (π * 1) (ℓ : Ambient 8) < Real.exp (-(π * 1) * (2 * (m : ℝ)))
  rw [gaussianKernel, h.norm_sq_eq ℓ, hℓ']
  exact lt_irrefl _

/-- The number of lattice vectors of squared norm `2m`. -/
def shellCount (h : EvenUnimodularGram z M) (m : ℕ) : ℕ :=
  Nat.card (h.halfNormSq ⁻¹' {m} : Set h.zlattice)

/-- **The theta series grouped by the norm.** -/
theorem hasSum_shellCount (h : EvenUnimodularGram z M) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun m : ℕ => (h.shellCount m : ℂ) * Complex.exp (2 * π * I * τ) ^ m) (h.theta τ) := by
  have hfun : (fun ℓ : h.zlattice => h.thetaTerm ℓ τ) =
      fun ℓ => Complex.exp (2 * π * I * τ) ^ h.halfNormSq ℓ :=
    funext fun ℓ => h.thetaTerm_eq_pow ℓ τ
  have hsum := h.hasSum_theta hτ
  rw [hfun] at hsum
  have hfib := hsum.tsum_fiberwise h.halfNormSq
  have hterm : (fun m : ℕ => ∑' b : (h.halfNormSq ⁻¹' {m} : Set h.zlattice),
      Complex.exp (2 * π * I * τ) ^ h.halfNormSq (b : h.zlattice)) =
      fun m : ℕ => (h.shellCount m : ℂ) * Complex.exp (2 * π * I * τ) ^ m := by
    funext m
    have e1 : ∀ b : (h.halfNormSq ⁻¹' {m} : Set h.zlattice),
        Complex.exp (2 * π * I * τ) ^ h.halfNormSq (b : h.zlattice) =
          Complex.exp (2 * π * I * τ) ^ m := fun b => by
      have hb : h.halfNormSq (b : h.zlattice) = m := b.2
      rw [hb]
    rw [tsum_congr e1, tsum_const, nsmul_eq_mul, shellCount]
  rw [hterm] at hfib
  exact hfib

/-- The `q`-expansion of the theta series. -/
theorem hasSum_qExpansion (h : EvenUnimodularGram z M) (τ : ℍ) :
    HasSum (fun m : ℕ => (h.shellCount m : ℂ) • Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (h.thetaForm τ) := by
  have hpos : 0 < (τ : ℂ).im := by
    rw [UpperHalfPlane.coe_im]
    exact τ.im_pos
  have hq : Function.Periodic.qParam 1 (τ : ℂ) = Complex.exp (2 * π * I * τ) := by
    simp [Function.Periodic.qParam]
  simp only [hq, smul_eq_mul]
  exact h.hasSum_shellCount hpos

theorem qExpansion_thetaForm_coeff (h : EvenUnimodularGram z M) (m : ℕ) :
    (qExpansion 1 h.thetaForm).coeff m = (h.shellCount m : ℂ) :=
  (ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL
    (f := h.thetaForm) h.hasSum_qExpansion m).symm

/-- Only the zero vector has norm zero. -/
theorem shellCount_zero (h : EvenUnimodularGram z M) : h.shellCount 0 = 1 := by
  have hz : ((0 : h.zlattice) : Ambient 8) = 0 := rfl
  have h0 : h.halfNormSq 0 = 0 := by
    have e := h.norm_sq_eq 0
    rw [hz, norm_zero] at e
    have e' : (h.halfNormSq 0 : ℝ) = 0 := by linarith
    exact_mod_cast e'
  have key : ∀ c : (h.halfNormSq ⁻¹' {0} : Set h.zlattice),
      ((c : h.zlattice) : Ambient 8) = 0 := by
    intro c
    have hc : h.halfNormSq (c : h.zlattice) = 0 := c.2
    have hn := h.norm_sq_eq (c : h.zlattice)
    rw [hc] at hn
    have hn' : ‖((c : h.zlattice) : Ambient 8)‖ ^ 2 = 0 := by
      rw [hn]
      simp
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hn')
  unfold shellCount
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => Subtype.ext (Subtype.ext ((key a).trans (key b).symm))⟩, ⟨⟨0, h0⟩⟩⟩

/-- **The theta series is the Eisenstein series `E₄`.** -/
theorem thetaForm_eq_E₄ (h : EvenUnimodularGram z M) : h.thetaForm = E₄ := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • E₄ = h.thetaForm :=
    (finrank_eq_one_iff_of_nonzero' E₄ (E_ne_zero _ ⟨2, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp levelOne_weight_four_rank_one) _
  have hq : c • qExpansion 1 (E₄ : ℍ → ℂ) = qExpansion 1 (h.thetaForm : ℍ → ℂ) := by
    rw [← ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c E₄,
      show (c • E₄ : ℍ → ℂ) = h.thetaForm from congrArg DFunLike.coe hc]
  have h0 := congrArg (fun p : PowerSeries ℂ => p.coeff 0) hq
  simp only [PowerSeries.coeff_smul, E_qExpansion_coeff_zero _ ⟨2, rfl⟩, smul_eq_mul, mul_one,
    h.qExpansion_thetaForm_coeff 0, h.shellCount_zero, Nat.cast_one] at h0
  rw [← hc, h0, one_smul]

/-- **An even unimodular lattice of rank eight has 240 vectors of squared norm 2.** -/
theorem shellCount_one (h : EvenUnimodularGram z M) : h.shellCount 1 = 240 := by
  have e := h.qExpansion_thetaForm_coeff 1
  rw [h.thetaForm_eq_E₄, E₄_qExpansion_coeff_one] at e
  exact_mod_cast e.symm

/-- **An even unimodular lattice of rank eight has 2160 vectors of squared norm 4.** -/
theorem shellCount_two (h : EvenUnimodularGram z M) : h.shellCount 2 = 2160 := by
  have e := h.qExpansion_thetaForm_coeff 2
  rw [h.thetaForm_eq_E₄, E₄_qExpansion_coeff_two] at e
  exact_mod_cast e.symm

/-- The lattice vectors of squared norm `2m` are the vectors of the fibre. -/
theorem coe_image_fiber (h : EvenUnimodularGram z M) (m : ℕ) :
    (fun ℓ : h.zlattice => (ℓ : Ambient 8)) '' (h.halfNormSq ⁻¹' {m}) =
      {x : Ambient 8 | x ∈ h.lattice ∧ ‖x‖ ^ 2 = 2 * (m : ℝ)} := by
  ext x
  constructor
  · rintro ⟨ℓ, hℓ, rfl⟩
    have hℓ' : h.halfNormSq ℓ = m := hℓ
    exact ⟨h.mem_zlattice.mp ℓ.2, by rw [h.norm_sq_eq ℓ, hℓ']⟩
  · rintro ⟨hx, hn⟩
    refine ⟨⟨x, h.mem_zlattice.mpr hx⟩, ?_, rfl⟩
    show h.halfNormSq ⟨x, h.mem_zlattice.mpr hx⟩ = m
    have e : ‖x‖ ^ 2 = 2 * (h.halfNormSq ⟨x, h.mem_zlattice.mpr hx⟩ : ℝ) :=
      h.norm_sq_eq ⟨x, h.mem_zlattice.mpr hx⟩
    have hn' : ‖x‖ ^ 2 = 2 * (m : ℝ) := hn
    have e' : (h.halfNormSq ⟨x, h.mem_zlattice.mpr hx⟩ : ℝ) = m := by linarith
    exact_mod_cast e'

theorem finite_shell (h : EvenUnimodularGram z M) (m : ℕ) :
    {x : Ambient 8 | x ∈ h.lattice ∧ ‖x‖ ^ 2 = 2 * (m : ℝ)}.Finite := by
  rw [← h.coe_image_fiber m]
  exact (h.finite_fiber m).image _

/-- The lattice vectors of squared norm `2m`. -/
def shell (h : EvenUnimodularGram z M) (m : ℕ) : Finset (Ambient 8) :=
  (h.finite_shell m).toFinset

theorem mem_shell (h : EvenUnimodularGram z M) {m : ℕ} {x : Ambient 8} :
    x ∈ h.shell m ↔ x ∈ h.lattice ∧ ‖x‖ ^ 2 = 2 * (m : ℝ) := by
  rw [shell, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

theorem card_shell (h : EvenUnimodularGram z M) (m : ℕ) : (h.shell m).card = h.shellCount m := by
  rw [shell, ← Set.ncard_eq_toFinset_card _ (h.finite_shell m), ← h.coe_image_fiber m,
    Set.ncard_image_of_injective _ Subtype.val_injective, shellCount, Nat.card_coe_set_eq]

/-- **An even unimodular lattice of rank eight is isometric to `E8`.** -/
theorem exists_isometry_image_e8Set_eq (h : EvenUnimodularGram z M) :
    ∃ Φ : Ambient 8 ≃ₗᵢ[ℝ] Ambient 8, Φ '' e8Set = (h.lattice : Set (Ambient 8)) := by
  refine exists_isometry_image_e8Set_eq_of_counts (fun x hx y hy => h.integral hx hy)
    (fun x hx => h.even_norm_sq hx) (fun w hw => h.selfDual hw) z h.mem_lattice
    (fun x hx => h.exists_coeffs hx) (h.shell 1) (h.shell 2) (fun x => ?_) (fun x => ?_) ?_ ?_
  · rw [h.mem_shell]
    norm_num
  · rw [h.mem_shell]
    norm_num
  · rw [h.card_shell, h.shellCount_one]
  · rw [h.card_shell, h.shellCount_two]

end EvenUnimodularGram

end E8Leech
