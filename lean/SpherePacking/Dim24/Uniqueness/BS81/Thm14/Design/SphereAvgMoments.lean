-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.Defs
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Invariance and second moments of `sphereAvg24`

This file develops basic properties of the spherical average `sphereAvg24` on `Ω₂₄`:
invariance under linear isometries and the explicit second coordinate moment.

## Main statements
* `sphereAvg24_comp_linearIsometryEquiv`
* `sphereAvg24_coord_sq`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14

noncomputable section

open scoped RealInnerProductSpace BigOperators Pointwise ENNReal
open MeasureTheory

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
## Auxiliary measurability lemma

This is the measurability fact needed to use `MeasurePreserving.measure_preimage` for the
polar-coordinate set `Ioo (0,1) • (Subtype.val '' s)`.
-/

lemma measurableSet_Ioo_smul_image_subtype_val (s : Set S23) (hs : MeasurableSet s) :
    MeasurableSet (Set.Ioo (0 : ℝ) (1 : ℝ) • ((Subtype.val : S23 → ℝ²⁴) '' s) : Set ℝ²⁴) := by
  -- This is the same set appearing in the definition of `Measure.toSphere`.
  -- We prove measurability by transporting a measurable set across `homeomorphUnitSphereProd`.
  let r : Set.Ioi (0 : ℝ) := ⟨(1 : ℝ), by simp⟩
  have hprod : MeasurableSet (s ×ˢ (Set.Iio r) : Set (S23 × Set.Ioi (0 : ℝ))) :=
    hs.prod measurableSet_Iio
  have hpre :
      MeasurableSet (homeomorphUnitSphereProd ℝ²⁴ ⁻¹' (s ×ˢ Set.Iio r) :
        Set ({(0 : ℝ²⁴)}ᶜ : Set ℝ²⁴)) :=
    (homeomorphUnitSphereProd ℝ²⁴).continuous.measurable hprod
  have hEmb : MeasurableEmbedding (Subtype.val : ({(0 : ℝ²⁴)}ᶜ : Set ℝ²⁴) → ℝ²⁴) :=
    MeasurableEmbedding.subtype_coe (by
      exact (measurableSet_singleton (0 : ℝ²⁴)).compl)
  have himg :
      MeasurableSet ((Subtype.val : ({(0 : ℝ²⁴)}ᶜ : Set ℝ²⁴) → ℝ²⁴) ''
        (homeomorphUnitSphereProd ℝ²⁴ ⁻¹' (s ×ˢ Set.Iio r))) :=
    hEmb.measurableSet_image' hpre
  -- Identify this image with the desired `Ioo`-smul set (this is the same rewriting chain as
  -- `Measure.toSphere_apply_aux` in Mathlib).
  have hset :
      ((Subtype.val : ({(0 : ℝ²⁴)}ᶜ : Set ℝ²⁴) → ℝ²⁴) ''
          (homeomorphUnitSphereProd ℝ²⁴ ⁻¹' (s ×ˢ Set.Iio r))) =
        (Set.Ioo (0 : ℝ) (r : ℝ) • ((Subtype.val : S23 → ℝ²⁴) '' s) : Set ℝ²⁴) := by
    rw [← Set.image2_smul, Set.image2_image_right, ← Homeomorph.image_symm, Set.image_image,
      ← Set.image_subtype_val_Ioi_Iio, Set.image2_image_left, Set.image2_swap, ← Set.image_prod]
    rfl
  simpa [hset, r] using! himg

/-!
## The induced action of a linear isometry on the unit sphere
-/

def sphereMap (e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴) : S23 → S23 :=
  fun x =>
    ⟨e x.1, by
      have hx : ‖x.1‖ = (1 : ℝ) :=
        mem_sphere_zero_iff_norm.mp x.2
      have : ‖e x.1‖ = (1 : ℝ) := by
        calc
          ‖e x.1‖ = ‖x.1‖ := e.norm_map x.1
          _ = (1 : ℝ) := hx
      exact mem_sphere_zero_iff_norm.mpr this⟩

@[simp] lemma sphereMap_coe (e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴) (x : S23) :
    (sphereMap e x : ℝ²⁴) = e (x : ℝ²⁴) := rfl

lemma measurable_sphereMap (e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴) : Measurable (sphereMap e) := by
  -- `sphereMap e` is continuous, hence measurable.
  have hcont : Continuous fun x : S23 => e (x : ℝ²⁴) :=
    e.continuous.comp continuous_subtype_val
  have hcont' : Continuous (sphereMap e) := by
    -- Build continuity of the subtype map.
    simpa [sphereMap] using!
      (Continuous.subtype_mk hcont (fun x => by
        have hx : ‖(x : ℝ²⁴)‖ = (1 : ℝ) := by
          exact mem_sphere_zero_iff_norm.mp x.2
        have : ‖e (x : ℝ²⁴)‖ = (1 : ℝ) := by
          calc
            ‖e (x : ℝ²⁴)‖ = ‖(x : ℝ²⁴)‖ := e.norm_map (x : ℝ²⁴)
            _ = (1 : ℝ) := hx
        exact mem_sphere_zero_iff_norm.mpr this))
  exact hcont'.measurable

lemma sphereMeasure24_preimage_sphereMap
    (e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴) (s : Set S23) (hs : MeasurableSet s) :
    sphereMeasure24 ((sphereMap e) ⁻¹' s) = sphereMeasure24 s := by
  have hs_pre : MeasurableSet ((sphereMap e) ⁻¹' s) := (measurable_sphereMap e) hs
  -- Abbreviate `A = Subtype.val '' s`.
  let A : Set ℝ²⁴ := (Subtype.val : S23 → ℝ²⁴) '' s
  -- Identify the `Subtype.val` image of the preimage as an `e.symm` image.
  have hval_pre :
      ((Subtype.val : S23 → ℝ²⁴) '' ((sphereMap e) ⁻¹' s)) = (e.symm : ℝ²⁴ → ℝ²⁴) '' A := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : sphereMap e z ∈ s := hz
      refine ⟨(sphereMap e z : ℝ²⁴), ?_, by simp [sphereMap]⟩
      exact ⟨sphereMap e z, hz', rfl⟩
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨sphereMap e.symm z, ?_, by simp [sphereMap]⟩
      have : sphereMap e (sphereMap e.symm z) = z := by
        ext
        simp [sphereMap]
      simpa [this] using! hz
  -- Scalar multiplication commutes with the linear map.
  have hsmul :
      Set.Ioo (0 : ℝ) (1 : ℝ) • ((e.symm : ℝ²⁴ → ℝ²⁴) '' A) =
        (e.symm : ℝ²⁴ → ℝ²⁴) '' (Set.Ioo (0 : ℝ) (1 : ℝ) • A) := by
    ext x
    constructor
    · rintro ⟨a, ha, y, hy, rfl⟩
      rcases hy with ⟨z, hz, rfl⟩
      refine ⟨a • z, ?_, by exact e.symm.map_smul a z⟩
      exact ⟨a, ha, z, hz, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨a, ha, z, hz, rfl⟩
      refine ⟨a, ha, e.symm z, ?_, by exact (e.symm.map_smul a z).symm⟩
      exact ⟨z, hz, rfl⟩
  have hmeas : MeasurableSet (Set.Ioo (0 : ℝ) (1 : ℝ) • A : Set ℝ²⁴) :=
    measurableSet_Ioo_smul_image_subtype_val (s := s) hs
  have hvol :
      MeasurePreserving (e : ℝ²⁴ → ℝ²⁴) (volume : Measure ℝ²⁴) (volume : Measure ℝ²⁴) := by
    simpa using! (LinearIsometryEquiv.measurePreserving (E := ℝ²⁴) (F := ℝ²⁴) e)
  have hpreimage (B : Set ℝ²⁴) :
      (e : ℝ²⁴ → ℝ²⁴) ⁻¹' B = (e.symm : ℝ²⁴ → ℝ²⁴) '' B := by
    ext x
    constructor
    · intro hx
      refine ⟨e x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using! hy
  -- Rewrite both sides using `Measure.toSphere_apply'` and compare the polar-coordinate sets.
  have hto_pre :=
    (Measure.toSphere_apply' (μ := (volume : Measure ℝ²⁴)) (s := ((sphereMap e) ⁻¹' s)) hs_pre)
  have hto := (Measure.toSphere_apply' (μ := (volume : Measure ℝ²⁴)) (s := s) hs)
  -- Now conclude.
  calc
    sphereMeasure24 ((sphereMap e) ⁻¹' s)
        = 24 * volume (Set.Ioo (0 : ℝ) (1 : ℝ) •
            ((Subtype.val : S23 → ℝ²⁴) '' ((sphereMap e) ⁻¹' s)) : Set ℝ²⁴) := by
              simpa [sphereMeasure24] using! hto_pre
    _ = 24 * volume (Set.Ioo (0 : ℝ) (1 : ℝ) • ((e.symm : ℝ²⁴ → ℝ²⁴) '' A) : Set ℝ²⁴) := by
          simp [hval_pre]
    _ = 24 * volume ((e.symm : ℝ²⁴ → ℝ²⁴) '' (Set.Ioo (0 : ℝ) (1 : ℝ) • A) : Set ℝ²⁴) := by
          simp [hsmul]
    _ = 24 * volume ((e : ℝ²⁴ → ℝ²⁴) ⁻¹' (Set.Ioo (0 : ℝ) (1 : ℝ) • A) : Set ℝ²⁴) := by
          simp [hpreimage]
    _ = 24 * volume (Set.Ioo (0 : ℝ) (1 : ℝ) • A : Set ℝ²⁴) := by
          simpa using!
            congrArg (fun t => 24 * t) (hvol.measure_preimage hmeas.nullMeasurableSet)
    _ = sphereMeasure24 s := by
          simpa [sphereMeasure24, A] using! hto.symm

/-- `sphereAvg24` is invariant under precomposition by a linear isometry of `ℝ²⁴`. -/
public theorem sphereAvg24_comp_linearIsometryEquiv (e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴) (f : ℝ²⁴ → ℝ) :
    sphereAvg24 (fun x : ℝ²⁴ => f (e x)) = sphereAvg24 f := by
  -- Build a measurable equivalence on the sphere.
  let m : S23 ≃ᵐ S23 :=
    { toEquiv :=
        { toFun := sphereMap e
          invFun := sphereMap e.symm
          left_inv := by
            intro x; ext; simp [sphereMap]
          right_inv := by
            intro x; ext; simp [sphereMap] }
      measurable_toFun := measurable_sphereMap e
      measurable_invFun := measurable_sphereMap e.symm }
  have hmp : MeasurePreserving (m : S23 → S23) sphereMeasure24 sphereMeasure24 := by
    refine ⟨m.measurable, ?_⟩
    ext s hs
    -- Use invariance of `sphereMeasure24` under `sphereMap e`.
    simpa [m, Measure.map_apply, measurable_sphereMap e, hs] using!
      (sphereMeasure24_preimage_sphereMap (e := e) (s := s) hs)
  -- Apply `MeasurePreserving.integral_comp'` to the integrand `x ↦ f x.1`.
  have hint :
      (∫ x : S23, f (e x.1) ∂sphereMeasure24) = ∫ x : S23, f x.1 ∂sphereMeasure24 := by
    have := MeasurePreserving.integral_comp' (μ := sphereMeasure24) (ν := sphereMeasure24)
      (f := m) hmp (g := fun x : S23 => f x.1)
    simpa [m, sphereMap] using! this
  -- Finish by unfolding `sphereAvg24`.
  simp [sphereAvg24, hint]

/-- The spherical measure `sphereMeasure24` is finite. -/
public lemma sphereMeasure24_univ_lt_top :
    sphereMeasure24 (Set.univ : Set S23) < (⊤ : ℝ≥0∞) := by
  have hto :
      sphereMeasure24 (Set.univ : Set S23) =
        (Module.finrank ℝ ℝ²⁴ : ℝ≥0∞) * volume (Metric.ball (0 : ℝ²⁴) (1 : ℝ)) := by
    dsimp [sphereMeasure24]
    exact Measure.toSphere_apply_univ (μ := (volume : Measure ℝ²⁴))
  have hball : volume (Metric.ball (0 : ℝ²⁴) (1 : ℝ)) < (⊤ : ℝ≥0∞) := by
    simpa using!
      (measure_ball_lt_top (μ := (volume : Measure ℝ²⁴)) (x := (0 : ℝ²⁴)) (r := (1 : ℝ)))
  have hcoeff : (Module.finrank ℝ ℝ²⁴ : ℝ≥0∞) < (⊤ : ℝ≥0∞) := by
    simp
  simpa [hto] using! (ENNReal.mul_lt_top hcoeff hball)

/-!
## Second coordinate moment
-/

lemma integrable_coord_sq (i : Fin 24) :
    Integrable (fun x : S23 => (x.1 i : ℝ) ^ 2) sphereMeasure24 := by
  -- The measure is finite, hence constants are integrable; the integrand is bounded by `1`.
  -- Use a local `IsFiniteMeasure` instance to access `integrable_const`.
  letI : IsFiniteMeasure sphereMeasure24 := ⟨by simpa using! sphereMeasure24_univ_lt_top⟩
  have hconst : Integrable (fun _ : S23 => (1 : ℝ)) sphereMeasure24 := by
    exact (integrable_const (μ := sphereMeasure24) (c := (1 : ℝ)))
  refine Integrable.mono' hconst (by fun_prop) ?_
  filter_upwards with x
  have hx : ‖(x : ℝ²⁴)‖ = (1 : ℝ) :=
    mem_sphere_zero_iff_norm.mp x.2
  have hcoord : |(x.1 i : ℝ)| ≤ 1 := by
    have : ‖(x : ℝ²⁴) i‖ ≤ ‖(x : ℝ²⁴)‖ := PiLp.norm_apply_le (p := (2 : ℝ≥0∞)) (x := (x : ℝ²⁴)) i
    simpa [Real.norm_eq_abs, hx] using! this
  simp_all

lemma sphereMeasure24_univ_toReal_ne_zero :
    (sphereMeasure24 (Set.univ : Set S23)).toReal ≠ 0 := by
  have hne : sphereMeasure24 ≠ 0 := by
    simp [sphereMeasure24]
  have huniv : sphereMeasure24 (Set.univ : Set S23) ≠ 0 := by
    -- `μ univ = 0 ↔ μ = 0`.
    exact (Measure.measure_univ_eq_zero.not).2 hne
  -- `sphereMeasure24 univ < ∞` by the explicit formula `toSphere_apply_univ`.
  have hto :
      sphereMeasure24 (Set.univ : Set S23) =
        (Module.finrank ℝ ℝ²⁴ : ℝ≥0∞) * volume (Metric.ball (0 : ℝ²⁴) (1 : ℝ)) := by
    simp [sphereMeasure24, Measure.toSphere_apply_univ]
  have hball : volume (Metric.ball (0 : ℝ²⁴) (1 : ℝ)) < (⊤ : ℝ≥0∞) := by
    simpa using!
      (measure_ball_lt_top (μ := (volume : Measure ℝ²⁴)) (x := (0 : ℝ²⁴)) (r := (1 : ℝ)))
  have hcoeff : (Module.finrank ℝ ℝ²⁴ : ℝ≥0∞) < (⊤ : ℝ≥0∞) := by
    simp
  have htop : sphereMeasure24 (Set.univ : Set S23) ≠ ∞ := by
    have : sphereMeasure24 (Set.univ : Set S23) < ∞ := by
      simpa [hto] using! (ENNReal.mul_lt_top hcoeff hball)
    exact this.ne
  exact (ENNReal.toReal_ne_zero).2 ⟨huniv, htop⟩

/-- `sphereAvg24` is additive, assuming integrability of the summands. -/
public lemma sphereAvg24_add (f g : ℝ²⁴ → ℝ)
    (hf : Integrable (fun x : S23 => f x.1) sphereMeasure24)
    (hg : Integrable (fun x : S23 => g x.1) sphereMeasure24) :
    sphereAvg24 (fun x => f x + g x) = sphereAvg24 f + sphereAvg24 g := by
  unfold sphereAvg24
  have h :
      (∫ x : S23, (f x.1 + g x.1) ∂sphereMeasure24) =
        (∫ x : S23, f x.1 ∂sphereMeasure24) + (∫ x : S23, g x.1 ∂sphereMeasure24) := by
    simpa [Pi.add_apply] using! (MeasureTheory.integral_add (μ := sphereMeasure24) hf hg)
  rw [h]
  ring

/-- `sphereAvg24` commutes with scalar multiplication. -/
public lemma sphereAvg24_smul (a : ℝ) (f : ℝ²⁴ → ℝ) :
    sphereAvg24 (fun x => a * f x) = a * sphereAvg24 f := by
  unfold sphereAvg24
  have h :
      (∫ x : S23, a * f x.1 ∂sphereMeasure24) =
        a * (∫ x : S23, f x.1 ∂sphereMeasure24) := by
    simpa using! (MeasureTheory.integral_const_mul (μ := sphereMeasure24) a (fun x : S23 => f x.1))
  rw [h]
  ring

/-- The spherical average of a constant function is that constant. -/
public lemma sphereAvg24_const (c : ℝ) :
    sphereAvg24 (fun _ : ℝ²⁴ => c) = c := by
  have hμ0 : (sphereMeasure24 (Set.univ : Set S23)).toReal ≠ 0 :=
    sphereMeasure24_univ_toReal_ne_zero
  unfold sphereAvg24
  -- `integral_const` uses `μ.real univ`, which is definitionaly `(μ univ).toReal`.
  simp [hμ0, MeasureTheory.measureReal_def, mul_comm]

/-- On `ℝ²⁴`, the sum of squared coordinates is the squared norm. -/
public lemma sum_sq_eq_norm_sq (x : ℝ²⁴) : (∑ j : Fin 24, (x j) ^ 2) = ‖x‖ ^ 2 := by
  have hnorm : ‖x‖ ^ 2 = ∑ j : Fin 24, ‖x j‖ ^ 2 := by
    simpa using! (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin 24 => ℝ) (x := x))
  simp_all

/-- The spherical average of a squared coordinate is `1/24`. -/
public theorem sphereAvg24_coord_sq (i : Fin 24) :
    sphereAvg24 (fun x : ℝ²⁴ => (x i) ^ 2) = (1 / 24 : ℝ) := by
  -- By permutation symmetry, all coordinates have the same second moment.
  have hsame : ∀ j : Fin 24,
      sphereAvg24 (fun x : ℝ²⁴ => (x j) ^ 2) = sphereAvg24 (fun x : ℝ²⁴ => (x i) ^ 2) := by
    intro j
    let σ : Fin 24 ≃ Fin 24 := Equiv.swap i j
    let e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴ :=
      LinearIsometryEquiv.piLpCongrLeft (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (E := ℝ) σ
    have hinv :
        sphereAvg24 (fun x : ℝ²⁴ => ((e x) i) ^ 2) =
          sphereAvg24 (fun x : ℝ²⁴ => (x i) ^ 2) := by
      simpa using! (sphereAvg24_comp_linearIsometryEquiv (e := e) (f := fun x => (x i) ^ 2))
    -- For the swap-isometry, `((e x) i) = x j`.
    simpa [e, σ, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'] using! hinv
  -- Take the average of `∑ x_j^2 = 1` and solve.
  have hsum_one :
      sphereAvg24 (fun x : ℝ²⁴ => ∑ j : Fin 24, (x j) ^ 2) = (1 : ℝ) := by
    -- On the sphere, `∑ x_j^2 = ‖x‖^2 = 1`.
    have hpoint : (fun x : S23 => (∑ j : Fin 24, (x.1 j) ^ 2)) = fun _ => (1 : ℝ) := by
      funext x
      have hx : ‖(x : ℝ²⁴)‖ = (1 : ℝ) := by
        exact mem_sphere_zero_iff_norm.mp x.2
      have : (∑ j : Fin 24, (x.1 j) ^ 2) = ‖(x : ℝ²⁴)‖ ^ 2 := by
        simpa using! (sum_sq_eq_norm_sq (x := (x : ℝ²⁴)))
      simpa [this, hx, pow_two]
    -- Rewrite the integrand as a constant and compute the average.
    have havg :
        sphereAvg24 (fun x : ℝ²⁴ => ∑ j : Fin 24, (x j) ^ 2) =
          sphereAvg24 (fun _ : ℝ²⁴ => (1 : ℝ)) := by
      unfold sphereAvg24
      simp [hpoint]
    simpa [sphereAvg24_const] using! havg.trans (sphereAvg24_const (c := (1 : ℝ)))
  have hsum :
      sphereAvg24 (fun x : ℝ²⁴ => ∑ j : Fin 24, (x j) ^ 2) =
        (Finset.univ.sum fun j : Fin 24 => sphereAvg24 (fun x : ℝ²⁴ => (x j) ^ 2)) := by
    -- Linearity of the integral over a finite sum.
    unfold sphereAvg24
    have hint : ∀ j : Fin 24, Integrable (fun x : S23 => (x.1 j : ℝ) ^ 2) sphereMeasure24 :=
      fun j => integrable_coord_sq (i := j)
    have hInt :
        (∫ x : S23, (Finset.univ.sum fun j : Fin 24 => (x.1 j : ℝ) ^ 2) ∂sphereMeasure24) =
          Finset.univ.sum (fun j : Fin 24 => ∫ x : S23, (x.1 j : ℝ) ^ 2 ∂sphereMeasure24) := by
      exact integral_finset_sum Finset.univ fun i a => hint i
    -- Rewrite both sides in terms of `Finset.univ.sum` (avoids `Fintype.sum`).
    -- LHS: scalar times integral of sum.
    -- RHS: sum of scalar times each integral.
    have :
        (sphereMeasure24 (Set.univ : Set S23)).toReal⁻¹ *
            ∫ x : S23, (Finset.univ.sum fun j : Fin 24 => (x.1 j : ℝ) ^ 2) ∂sphereMeasure24
          =
          Finset.univ.sum (fun j : Fin 24 =>
            (sphereMeasure24 (Set.univ : Set S23)).toReal⁻¹ *
              ∫ x : S23, (x.1 j : ℝ) ^ 2 ∂sphereMeasure24) := by
      -- distribute the scalar over the finite sum
      simp [hInt, Finset.mul_sum]
    -- The goal is exactly this equality.
    exact this
  have hconstsum :
      (Finset.univ.sum fun j : Fin 24 => sphereAvg24 (fun x : ℝ²⁴ => (x j) ^ 2)) =
        (24 : ℝ) * sphereAvg24 (fun x : ℝ²⁴ => (x i) ^ 2) := by
    -- All terms are equal by `hsame`.
    simp [hsame, Fintype.card_fin]
  have : (24 : ℝ) * sphereAvg24 (fun x : ℝ²⁴ => (x i) ^ 2) = 1 := by
    have hAB : sphereAvg24 (fun x : ℝ²⁴ => ∑ j : Fin 24, (x j) ^ 2) =
        (24 : ℝ) * sphereAvg24 (fun x : ℝ²⁴ => (x i) ^ 2) := by
      simpa using! (hsum.trans hconstsum)
    -- `A = B` and `A = 1`, so `B = 1`.
    simpa using! hAB.symm.trans hsum_one
  have h24 : (24 : ℝ) ≠ 0 := by norm_num
  nlinarith

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14
