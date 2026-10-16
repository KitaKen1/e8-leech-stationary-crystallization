import E8Leech.EvenUnimodularLattice
import E8Leech.GaussianSchwartz
import SpherePacking.CohnElkies.PoissonSummationGeneral
import SpherePacking.CohnElkies.LPBoundAux

/-!
# The Gaussian sum of an even unimodular lattice of rank eight

For eight vectors with an even unimodular Gram matrix (`EvenUnimodularGram`), the lattice they
span has covolume one and equals its dual lattice. Poisson summation for the Gaussian then gives
the inversion formula of the Gaussian sum on the positive axis,

`Θ(t) = t⁻⁴ Θ(1/t)`,  `Θ(t) = ∑_{ℓ ∈ L} e^{-π t |ℓ|²}`.

* `EvenUnimodularGram.zlattice`: the lattice as a `ℤ`-submodule (the form of Mathlib's lattices).
* `EvenUnimodularGram.covolume_zlattice`, `EvenUnimodularGram.dualLattice_zlattice`.
* `EvenUnimodularGram.gaussianSum_inv`: the inversion formula.
-/

noncomputable section

namespace E8Leech

open MeasureTheory
open scoped InnerProductSpace FourierTransform Real

/-- A Gaussian is summable over a discrete lattice. -/
theorem summable_gaussianKernel_lattice {d : ℕ} (L : Submodule ℤ (Ambient d))
    [DiscreteTopology L] {α : ℝ} (hα : 0 < α) :
    Summable fun ℓ : L => gaussianKernel α (ℓ : Ambient d) := by
  have h := SpherePacking.CohnElkies.LPBoundAux.summable_norm_comp_add_zlattice (Λ := L)
    (gaussianSchwartz (d := d) hα) 0
  refine h.congr fun ℓ => ?_
  rw [zero_add, gaussianSchwartz_apply, Complex.norm_real,
    Real.norm_of_nonneg (gaussianKernel_pos α _).le]

namespace EvenUnimodularGram

variable {z : Fin 8 → Ambient 8} {M : Matrix (Fin 8) (Fin 8) ℤ}

/-- The lattice as a `ℤ`-submodule. -/
def zlattice (h : EvenUnimodularGram z M) : Submodule ℤ (Ambient 8) :=
  Submodule.span ℤ (Set.range h.basis)

instance (h : EvenUnimodularGram z M) : DiscreteTopology h.zlattice :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range h.basis)))

instance (h : EvenUnimodularGram z M) : IsZLattice ℝ h.zlattice :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range h.basis)))

theorem mem_zlattice (h : EvenUnimodularGram z M) {x : Ambient 8} :
    x ∈ h.zlattice ↔ x ∈ h.lattice := by
  have hr : Set.range h.basis = Set.range z := congrArg Set.range (funext h.basis_apply)
  unfold zlattice lattice
  rw [hr, ← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup]

/-- **The lattice has covolume one.** -/
theorem covolume_zlattice (h : EvenUnimodularGram z M) : ZLattice.covolume h.zlattice = 1 := by
  classical
  let b₀ : OrthonormalBasis (Fin 8) ℝ (Ambient 8) := EuclideanSpace.basisFun (Fin 8) ℝ
  let bZ : Module.Basis (Fin 8) ℤ h.zlattice := h.basis.restrictScalars ℤ
  have hbZ : ((↑) ∘ bZ : Fin 8 → Ambient 8) = z := by
    funext i
    exact (Module.Basis.restrictScalars_apply ℤ h.basis i).trans (h.basis_apply i)
  have hvol : (volume : Measure (Ambient 8)).real (ZSpan.fundamentalDomain b₀.toBasis) = 1 := by
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped b₀.toBasis volume),
      measureReal_def, OrthonormalBasis.coe_toBasis, b₀.volume_parallelepiped]
    simp
  -- the coordinate matrix of the vectors
  set B : Matrix (Fin 8) (Fin 8) ℝ := b₀.toBasis.toMatrix z with hB
  have hgram : B.transpose * B = M.map (Int.castRingHom ℝ) := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hB, Module.Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply, Matrix.map_apply,
      Int.coe_castRingHom]
    rw [← h.gram j k, ← b₀.sum_inner_mul_inner (z j) (z k)]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm (z j) (b₀ i)]
  have hdet : B.det * B.det = 1 := by
    have e := congrArg Matrix.det hgram
    rw [Matrix.det_mul, Matrix.det_transpose] at e
    rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h.det]
    simp
  have habs : |B.det| = 1 := by
    have h1 : |B.det| * |B.det| = 1 := by rw [abs_mul_abs_self, hdet]
    nlinarith [abs_nonneg B.det]
  rw [ZLattice.covolume_eq_det_mul_measureReal h.zlattice volume bZ b₀.toBasis, hbZ, hvol,
    Module.Basis.det_apply, ← hB, habs, mul_one]

/-- **The lattice is its own dual.** -/
theorem dualLattice_zlattice (h : EvenUnimodularGram z M) :
    SchwartzMap.dualLattice (d := 8) h.zlattice = h.zlattice := by
  ext w
  rw [SchwartzMap.dualLattice, LinearMap.BilinForm.mem_dualSubmodule]
  constructor
  · intro hw
    rw [h.mem_zlattice]
    refine h.selfDual fun x hx => ?_
    obtain ⟨n, hn⟩ := Submodule.mem_one.mp (hw x (h.mem_zlattice.mpr hx))
    exact ⟨n, by simpa using hn.symm⟩
  · intro hw x hx
    obtain ⟨n, hn⟩ := h.integral (h.mem_zlattice.mp hw) (h.mem_zlattice.mp hx)
    exact Submodule.mem_one.mpr ⟨n, by simpa using hn.symm⟩

/-- A sum over the dual lattice is a sum over the lattice. -/
theorem tsum_dualLattice (h : EvenUnimodularGram z M) (g : Ambient 8 → ℂ) :
    ∑' m : SchwartzMap.dualLattice (d := 8) h.zlattice, g (m : Ambient 8) =
      ∑' m : h.zlattice, g (m : Ambient 8) := by
  rw [h.dualLattice_zlattice]

/-- The Gaussian sum `Θ(t) = ∑_{ℓ ∈ L} e^{-π t |ℓ|²}`. -/
def gaussianSum (h : EvenUnimodularGram z M) (t : ℝ) : ℝ :=
  ∑' ℓ : h.zlattice, gaussianKernel (π * t) (ℓ : Ambient 8)

theorem summable_gaussianSum (h : EvenUnimodularGram z M) {t : ℝ} (ht : 0 < t) :
    Summable fun ℓ : h.zlattice => gaussianKernel (π * t) (ℓ : Ambient 8) :=
  summable_gaussianKernel_lattice h.zlattice (mul_pos Real.pi_pos ht)

/-- **Inversion of the Gaussian sum**: `Θ(t) = t⁻⁴ Θ(1/t)` (Poisson summation). -/
theorem gaussianSum_inv (h : EvenUnimodularGram z M) {t : ℝ} (ht : 0 < t) :
    h.gaussianSum t = t⁻¹ ^ 4 * h.gaussianSum t⁻¹ := by
  have ht' : t ≠ 0 := ht.ne'
  have hα : 0 < π * t := mul_pos Real.pi_pos ht
  have hP := SchwartzMap.poissonSummation_lattice (d := 8) (L := h.zlattice)
    (gaussianSchwartz (d := 8) hα) 0
  simp only [zero_add, h.covolume_zlattice, div_one, Complex.ofReal_one, one_mul,
    WithLp.ofLp_zero, RCLike.wInner_zero_left, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    mul_one] at hP
  have hL : ((h.gaussianSum t : ℝ) : ℂ) =
      ∑' ℓ : h.zlattice, gaussianSchwartz (d := 8) hα (ℓ : Ambient 8) := by
    rw [gaussianSum, Complex.ofReal_tsum]
    exact tsum_congr fun ℓ => (gaussianSchwartz_apply hα _).symm
  have hR : ∑' m : SchwartzMap.dualLattice (d := 8) h.zlattice,
      𝓕 (fun x : Ambient 8 => gaussianSchwartz (d := 8) hα x) (m : Ambient 8) =
      ((t⁻¹ ^ 4 * h.gaussianSum t⁻¹ : ℝ) : ℂ) := by
    rw [h.tsum_dualLattice
      (fun m => 𝓕 (fun x : Ambient 8 => gaussianSchwartz (d := 8) hα x) m),
      gaussianSum, ← tsum_mul_left, Complex.ofReal_tsum]
    refine tsum_congr fun ℓ => ?_
    have e := fourier_gaussianSchwartz_eight hα (ℓ : Ambient 8)
    have h1 : π / (π * t) = t⁻¹ := by field_simp
    have h2 : π ^ 2 / (π * t) = π * t⁻¹ := by field_simp
    rw [h1, h2] at e
    refine e.trans ?_
    push_cast
    ring
  have hfinal := hL.trans (hP.trans hR)
  exact_mod_cast hfinal

end EvenUnimodularGram

end E8Leech
