-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.SphereAvg24Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Fourth coordinate moment for `sphereAvg24`

This file computes the fourth moment of a coordinate under the spherical average in dimension `24`:
`sphereAvg24 (x ↦ (x 0) ^ 4) = 1 / 208`.

The proof uses rotation invariance and a short linear system relating
`E[x_0 ^ 4]` and `E[x_0 ^ 2 * x_1 ^ 2]`.

## Main statements
* `exists_linearIsometryEquiv_map_unit_to_basis0`
* `sphereAvg24_coord_pow_four`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14

noncomputable section

open scoped RealInnerProductSpace BigOperators ENNReal

open MeasureTheory

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
## Linearity helpers for `sphereAvg24`
-/

/-!
## Odd mixed terms vanish by sign symmetry
-/

lemma sphereAvg24_coord_pow_three_mul_coord_eq_zero :
    sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 3 * (x (1 : Fin 24))) = (0 : ℝ) := by
  let e0 : ℝ ≃ₗᵢ[ℝ] ℝ := LinearIsometryEquiv.neg ℝ
  let e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴ :=
    LinearIsometryEquiv.piLpCongrRight (p := (2 : ℝ≥0∞))
      (fun i : Fin 24 => if i = (0 : Fin 24) then e0 else LinearIsometryEquiv.refl ℝ ℝ)
  have hinv :=
    (sphereAvg24_comp_linearIsometryEquiv (e := e)
      (f := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 3 * (x (1 : Fin 24)))).symm
  have hflip :
      (fun x : ℝ²⁴ => ((e x) (0 : Fin 24)) ^ 3 * ((e x) (1 : Fin 24))) =
        fun x : ℝ²⁴ => -((x (0 : Fin 24)) ^ 3 * (x (1 : Fin 24))) := by
    funext x
    have h0 : (e x) (0 : Fin 24) = -(x (0 : Fin 24)) := by
      simp [e, e0, LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply]
    have h1 : (e x) (1 : Fin 24) = x (1 : Fin 24) := by
      simp [e, e0, LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply]
    simp [h0, h1, pow_succ, mul_assoc, mul_comm]
  have : sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 3 * (x (1 : Fin 24))) =
      sphereAvg24 (fun x : ℝ²⁴ => -((x (0 : Fin 24)) ^ 3 * (x (1 : Fin 24)))) := by
    simpa [hflip] using! hinv
  have : sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 3 * (x (1 : Fin 24))) =
      -sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 3 * (x (1 : Fin 24))) := by
    simpa [sphereAvg24_neg] using! this
  linarith

lemma sphereAvg24_coord_mul_coord_pow_three_eq_zero :
    sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) * (x (1 : Fin 24)) ^ 3) = (0 : ℝ) := by
  let e1 : ℝ ≃ₗᵢ[ℝ] ℝ := LinearIsometryEquiv.neg ℝ
  let e : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴ :=
    LinearIsometryEquiv.piLpCongrRight (p := (2 : ℝ≥0∞))
      (fun i : Fin 24 => if i = (1 : Fin 24) then e1 else LinearIsometryEquiv.refl ℝ ℝ)
  have hinv :=
    (sphereAvg24_comp_linearIsometryEquiv (e := e)
      (f := fun x : ℝ²⁴ => (x (0 : Fin 24)) * (x (1 : Fin 24)) ^ 3)).symm
  have hflip :
      (fun x : ℝ²⁴ => ((e x) (0 : Fin 24)) * ((e x) (1 : Fin 24)) ^ 3) =
        fun x : ℝ²⁴ => -((x (0 : Fin 24)) * (x (1 : Fin 24)) ^ 3) := by
    funext x
    have h0 : (e x) (0 : Fin 24) = x (0 : Fin 24) := by
      simp [e, e1, LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply]
    have h1 : (e x) (1 : Fin 24) = -(x (1 : Fin 24)) := by
      simp [e, e1, LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply]
    simp [h0, h1, pow_succ, mul_comm]
  have : sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) * (x (1 : Fin 24)) ^ 3) =
      sphereAvg24 (fun x : ℝ²⁴ => -((x (0 : Fin 24)) * (x (1 : Fin 24)) ^ 3)) := by
    simpa [hflip] using! hinv
  have : sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) * (x (1 : Fin 24)) ^ 3) =
      -sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) * (x (1 : Fin 24)) ^ 3) := by
    simpa [sphereAvg24_neg] using! this
  linarith

/-!
## Fourth coordinate moment
-/

/-- Given a unit vector `u`, there is a linear isometry of `ℝ²⁴` sending `u` to the first basis
vector. -/
public theorem exists_linearIsometryEquiv_map_unit_to_basis0
    {u : ℝ²⁴} (hu : ‖u‖ = (1 : ℝ)) :
    ∃ E : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴, E u = (EuclideanSpace.single (0 : Fin 24) (1 : ℝ) : ℝ²⁴) := by
  have hcard : Module.finrank ℝ ℝ²⁴ = Fintype.card (Fin 24) :=
    finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin 24)
  let s : Set (Fin 24) := ({0} : Set (Fin 24))
  let v : Fin 24 → ℝ²⁴ := fun i => if i = (0 : Fin 24) then u else 0
  have hv : Orthonormal ℝ (s.restrict v) := by
    -- `↥s` is a subsingleton since `s = {0}`.
    haveI : Subsingleton (↥s) :=
      (Set.subsingleton_coe s).2 (by simp [s])
    refine ⟨?_, ?_⟩
    · -- Reduce to the distinguished element `⟨0, _⟩ : ↥s`.
      let i0 : (↥s) := ⟨(0 : Fin 24), by
        -- `0 ∈ {0}`.
        dsimp [s]
        rfl⟩
      intro i
      have hi : i = i0 := Subsingleton.elim i i0
      subst hi
      -- Now `s.restrict v i0 = u`.
      simp [i0, Set.restrict, v, hu]
    · exact
        (Subsingleton.pairwise (r := fun i j : (↥s) => (⟪s.restrict v i, s.restrict v j⟫ : ℝ) = 0))
  obtain ⟨b', hb'⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ) (E := ℝ²⁴) hcard
      (v := v) (s := s) hv
  have hb0 : b' (0 : Fin 24) = u := by
    simpa [v] using! hb' (0 : Fin 24) (by simp [s])
  let bstd : OrthonormalBasis (Fin 24) ℝ ℝ²⁴ := EuclideanSpace.basisFun (Fin 24) ℝ
  let E : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴ := b'.equiv bstd (Equiv.refl _)
  refine ⟨E, ?_⟩
  have : E (b' (0 : Fin 24)) = bstd (0 : Fin 24) := by
    simp [E]
  simpa [hb0] using! this.trans (by simp [bstd])

/-- The fourth moment of a coordinate on the unit sphere in `ℝ²⁴` is `1 / 208`. -/
public theorem sphereAvg24_coord_pow_four :
    sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4) = (1 / 208 : ℝ) := by
  set a : ℝ := sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4)
  set b : ℝ := sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ 2)
  -- Build a unit vector `u = (e0+e1)/√2`.
  let bstd : OrthonormalBasis (Fin 24) ℝ ℝ²⁴ := EuclideanSpace.basisFun (Fin 24) ℝ
  let e0 : ℝ²⁴ := bstd (0 : Fin 24)
  let e1 : ℝ²⁴ := bstd (1 : Fin 24)
  let u : ℝ²⁴ := (Real.sqrt 2)⁻¹ • (e0 + e1)
  have hsqrt2 : (Real.sqrt 2 : ℝ) ≠ 0 := by
    positivity
  have hu_norm : ‖u‖ = (1 : ℝ) := by
    have horth01 : (⟪e0, e1⟫ : ℝ) = 0 := by
      have hne : (0 : Fin 24) ≠ (1 : Fin 24) := by decide
      exact OrthonormalBasis.inner_eq_zero bstd hne
    have hnorm_e0 : ‖e0‖ = (1 : ℝ) := by
      dsimp [e0]
      exact bstd.norm_eq_one (0 : Fin 24)
    have hnorm_e1 : ‖e1‖ = (1 : ℝ) := by
      dsimp [e1]
      exact bstd.norm_eq_one (1 : Fin 24)
    have hnorm_add : ‖e0 + e1‖ ^ 2 = (2 : ℝ) := by
      have : ‖e0 + e1‖ ^ 2 = ‖e0‖ ^ 2 + ‖e1‖ ^ 2 := by
        simpa [real_inner_self_eq_norm_sq, pow_two, inner_add_left, inner_add_right, horth01,
          add_assoc, add_left_comm, add_comm] using!
          (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x := e0) (y := e1)
            (by simpa using! horth01))
      have : ‖e0 + e1‖ ^ 2 = (1 : ℝ) + 1 := by
        simpa [hnorm_e0, hnorm_e1] using! this
      nlinarith
    have : ‖u‖ ^ 2 = (Real.sqrt 2)⁻¹ ^ 2 * ‖e0 + e1‖ ^ 2 := by
      have ha : ‖(Real.sqrt 2 : ℝ)⁻¹‖ = (Real.sqrt 2 : ℝ)⁻¹ := by
        have hnonneg : (0 : ℝ) ≤ (Real.sqrt 2 : ℝ)⁻¹ :=
          inv_nonneg.2 (Real.sqrt_nonneg (2 : ℝ))
        exact Real.norm_of_nonneg hnonneg
      calc
        ‖u‖ ^ 2 = (‖(Real.sqrt 2 : ℝ)⁻¹‖ * ‖e0 + e1‖) ^ 2 := by
          -- Avoid `simp`: it may rewrite `a • (e0+e1)` as `a•e0 + a•e1` under the norm.
          dsimp [u]
          rw [norm_smul]
          rfl
        _ = (Real.sqrt 2 : ℝ)⁻¹ ^ 2 * ‖e0 + e1‖ ^ 2 := by
          -- expand and remove the `‖ · ‖` on the scalar (it is nonnegative)
          simp [ha, pow_two, mul_assoc, mul_left_comm, mul_comm]
    have hs : (Real.sqrt 2)⁻¹ ^ 2 * (2 : ℝ) = 1 := by
      field_simp [hsqrt2]
      simp [Real.sq_sqrt (zero_le_two : (0 : ℝ) ≤ (2 : ℝ))]
    have : ‖u‖ ^ 2 = (1 : ℝ) := by simpa [hnorm_add, hs] using! this
    have hnonneg : 0 ≤ ‖u‖ := norm_nonneg _
    nlinarith
  -- Choose an isometry sending `u` to `e0`.
  obtain ⟨E, hEu⟩ := exists_linearIsometryEquiv_map_unit_to_basis0 (u := u) hu_norm
  have hEu0 : E u = e0 := by
    -- `e0 = basisFun 0 = single 0 1`.
    simpa [e0, bstd] using! hEu
  -- Relate `((E x) 0)` to `⟪x,u⟫`.
  have hinner_coord0 : ∀ x : ℝ²⁴, (E x) (0 : Fin 24) = (⟪x, u⟫ : ℝ) := by
    intro x
    have hx0 : (E x) (0 : Fin 24) = (⟪E x, e0⟫ : ℝ) := by
      -- `⟪x, e0⟫ = x0`
      simpa [e0, bstd] using!
        (EuclideanSpace.inner_basisFun_real (ι := Fin 24) (x := (E x)) (i := (0 : Fin 24))).symm
    have hx1 : (⟪E x, e0⟫ : ℝ) = (⟪E x, E u⟫ : ℝ) := by simp [hEu0]
    have hx2 : (⟪E x, E u⟫ : ℝ) = (⟪x, u⟫ : ℝ) :=
      LinearIsometryEquiv.inner_map_map E x u
    exact hx0.trans (hx1.trans hx2)
  -- Symmetry: `E[x₁^4] = a`.
  have hswap4 : sphereAvg24 (fun x : ℝ²⁴ => (x (1 : Fin 24)) ^ 4) = a := by
    let σ : Fin 24 ≃ Fin 24 := Equiv.swap (0 : Fin 24) (1 : Fin 24)
    let eσ : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴ :=
      LinearIsometryEquiv.piLpCongrLeft (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (E := ℝ) σ
    have hinv :=
      sphereAvg24_comp_linearIsometryEquiv (e := eσ) (f := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4)
    simpa [a, eσ, σ, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'] using! hinv
  -- First relation: `a = 3 b`.
  have hab : a = 3 * b := by
    -- Invariance under `E` turns `x ↦ x0^4` into `x ↦ ⟪x,u⟫^4`.
    have hinv :=
      (sphereAvg24_comp_linearIsometryEquiv (e := E)
          (f := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4)).symm
    have ha_inner :
        a = sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ 4) := by
      have :
          sphereAvg24 (fun x : ℝ²⁴ => ((E x) (0 : Fin 24)) ^ 4) =
            sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ 4) := by
        exact sphereAvg24_congr fun x => congrFun (congrArg HPow.hPow (hinner_coord0 ↑x)) 4
      simpa [a] using! hinv.trans this
    have hinner : ∀ x : ℝ²⁴,
        (⟪x, u⟫ : ℝ) = (Real.sqrt 2)⁻¹ * (x (0 : Fin 24) + x (1 : Fin 24)) := by
      intro x
      have hx0 : (⟪x, e0⟫ : ℝ) = x (0 : Fin 24) := by
        simpa [e0, bstd] using!
          (EuclideanSpace.inner_basisFun_real (ι := Fin 24) (x := x) (i := (0 : Fin 24)))
      have hx1 : (⟪x, e1⟫ : ℝ) = x (1 : Fin 24) := by
        simpa [e1, bstd] using!
          (EuclideanSpace.inner_basisFun_real (ι := Fin 24) (x := x) (i := (1 : Fin 24)))
      calc
        (⟪x, u⟫ : ℝ) = (Real.sqrt 2)⁻¹ * (⟪x, e0⟫ + ⟪x, e1⟫) := by
          simp [u, e0, e1, inner_smul_right, inner_add_right, mul_add]
        _ = (Real.sqrt 2)⁻¹ * (x (0 : Fin 24) + x (1 : Fin 24)) := by
          simp [hx0, hx1, mul_add]
    have hscale :
        sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ 4) =
          (Real.sqrt 2)⁻¹ ^ 4 *
            sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24) + x (1 : Fin 24)) ^ 4) := by
      -- pointwise: `((c * t)^4) = c^4 * t^4`
      have hcongr :
          sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ 4) =
            sphereAvg24 (fun x : ℝ²⁴ =>
              ((Real.sqrt 2)⁻¹ * (x (0 : Fin 24) + x (1 : Fin 24))) ^ 4) := by
        exact sphereAvg24_congr fun x => congrFun (congrArg HPow.hPow (hinner ↑x)) 4
      have :
          sphereAvg24 (fun x : ℝ²⁴ =>
              ((Real.sqrt 2)⁻¹ * (x (0 : Fin 24) + x (1 : Fin 24))) ^ 4) =
            (Real.sqrt 2)⁻¹ ^ 4 *
              sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24) + x (1 : Fin 24)) ^ 4) := by
        calc
          sphereAvg24 (fun x : ℝ²⁴ =>
              ((Real.sqrt 2)⁻¹ * (x (0 : Fin 24) + x (1 : Fin 24))) ^ 4) =
              sphereAvg24 (fun x : ℝ²⁴ =>
                (Real.sqrt 2)⁻¹ ^ 4 * (x (0 : Fin 24) + x (1 : Fin 24)) ^ 4) := by
                refine sphereAvg24_congr ?_
                intro x
                ring
          _ = (Real.sqrt 2)⁻¹ ^ 4 *
                sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24) + x (1 : Fin 24)) ^ 4) := by
                exact sphereAvg24_smul ((√2)⁻¹ ^ 4) fun x => (x.ofLp 0 + x.ofLp 1) ^ 4
      exact hcongr.trans this
    -- Expand `(x0+x1)^4` and take averages.
    have hpoly : ∀ x : ℝ²⁴,
        (x (0 : Fin 24) + x (1 : Fin 24)) ^ 4 =
          (x (0 : Fin 24)) ^ 4 +
            4 * ((x (0 : Fin 24)) ^ 3 * (x (1 : Fin 24))) +
              (6 * ((x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ 2) +
                (4 * (x (0 : Fin 24) * (x (1 : Fin 24)) ^ 3) +
                  (x (1 : Fin 24)) ^ 4)) := by
      intro x
      ring
    have hI0 : Integrable (fun x : S23 => (x.1 (0 : Fin 24) : ℝ) ^ 4) sphereMeasure24 := by
      simpa [mul_one] using!
        integrable_coord_pow_mul_coord_pow (i := (0 : Fin 24)) (j := (0 : Fin 24)) (m := 4) (n := 0)
    have hI31 :
        Integrable
          (fun x : S23 => (x.1 (0 : Fin 24) : ℝ) ^ 3 * (x.1 (1 : Fin 24) : ℝ))
          sphereMeasure24 := by
      simpa using!
        integrable_coord_pow_mul_coord_pow (i := (0 : Fin 24)) (j := (1 : Fin 24)) (m := 3) (n := 1)
    have hI22 :
        Integrable
          (fun x : S23 =>
            (x.1 (0 : Fin 24) : ℝ) ^ 2 * (x.1 (1 : Fin 24) : ℝ) ^ 2)
          sphereMeasure24 := by
      simpa using!
        integrable_coord_pow_mul_coord_pow (i := (0 : Fin 24)) (j := (1 : Fin 24)) (m := 2) (n := 2)
    have hI13 :
        Integrable
          (fun x : S23 => (x.1 (0 : Fin 24) : ℝ) * (x.1 (1 : Fin 24) : ℝ) ^ 3)
          sphereMeasure24 := by
      simpa using!
        integrable_coord_pow_mul_coord_pow (i := (0 : Fin 24)) (j := (1 : Fin 24)) (m := 1) (n := 3)
    have hI4 : Integrable (fun x : S23 => (x.1 (1 : Fin 24) : ℝ) ^ 4) sphereMeasure24 := by
      simpa [mul_one] using!
        integrable_coord_pow_mul_coord_pow (i := (1 : Fin 24)) (j := (1 : Fin 24)) (m := 4) (n := 0)
    have havg :
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24) + x (1 : Fin 24)) ^ 4) = 2 * a + 6 * b := by
      -- Apply `sphereAvg24` to the pointwise identity and simplify term-by-term.
      have hcongr :
          sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24) + x (1 : Fin 24)) ^ 4) =
            sphereAvg24 (fun x : ℝ²⁴ =>
              (x (0 : Fin 24)) ^ 4 +
                4 * ((x (0 : Fin 24)) ^ 3 * (x (1 : Fin 24))) +
                  (6 * ((x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ 2) +
                    (4 * (x (0 : Fin 24) * (x (1 : Fin 24)) ^ 3) +
                      (x (1 : Fin 24)) ^ 4))) := by
        exact sphereAvg24_congr fun x => hpoly ↑x
      -- linearity chain for five terms
      have h1 :=
        sphereAvg24_add
          (f := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4)
          (g := fun x : ℝ²⁴ =>
            4 * ((x (0 : Fin 24)) ^ 3 * (x (1 : Fin 24))) +
              (6 * ((x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ 2) +
                (4 * (x (0 : Fin 24) * (x (1 : Fin 24)) ^ 3) +
                  (x (1 : Fin 24)) ^ 4)))
          (hf := hI0)
          (hg := by
            refine (hI31.const_mul 4).add ?_
            refine (hI22.const_mul 6).add ?_
            exact (hI13.const_mul 4).add hI4)
      have h2 :=
        sphereAvg24_add
          (f := fun x : ℝ²⁴ => 4 * ((x (0 : Fin 24)) ^ 3 * (x (1 : Fin 24))))
          (g := fun x : ℝ²⁴ =>
            6 * ((x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ 2) +
              (4 * (x (0 : Fin 24) * (x (1 : Fin 24)) ^ 3) +
                (x (1 : Fin 24)) ^ 4))
          (hf := (hI31.const_mul 4))
          (hg := by
            refine (hI22.const_mul 6).add ?_
            exact (hI13.const_mul 4).add hI4)
      have h3 :=
        sphereAvg24_add
          (f := fun x : ℝ²⁴ => 6 * ((x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ 2))
          (g := fun x : ℝ²⁴ => 4 * (x (0 : Fin 24) * (x (1 : Fin 24)) ^ 3) + (x (1 : Fin 24)) ^ 4)
          (hf := (hI22.const_mul 6))
          (hg := (hI13.const_mul 4).add hI4)
      have h4 :=
        sphereAvg24_add
          (f := fun x : ℝ²⁴ => 4 * (x (0 : Fin 24) * (x (1 : Fin 24)) ^ 3))
          (g := fun x : ℝ²⁴ => (x (1 : Fin 24)) ^ 4)
          (hf := (hI13.const_mul 4))
          (hg := hI4)
      -- Put the chain together and simplify using vanishing odd moments and symmetry.
      have hx31 :
          sphereAvg24 (fun x : ℝ²⁴ => 4 * ((x (0 : Fin 24)) ^ 3 * (x (1 : Fin 24)))) = 0 := by
        have h0 : sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 3 * (x (1 : Fin 24))) = 0 :=
          sphereAvg24_coord_pow_three_mul_coord_eq_zero
        simp [sphereAvg24_smul, h0]
      have hx13 :
          sphereAvg24 (fun x : ℝ²⁴ => 4 * (x (0 : Fin 24) * (x (1 : Fin 24)) ^ 3)) = 0 := by
        have h0 : sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) * (x (1 : Fin 24)) ^ 3) = 0 :=
          sphereAvg24_coord_mul_coord_pow_three_eq_zero
        simp [sphereAvg24_smul, h0]
      have hx22 :
          sphereAvg24
              (fun x : ℝ²⁴ => 6 * ((x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ 2)) =
            6 * b := by
        exact sphereAvg24_smul 6 fun x => x.ofLp 0 ^ 2 * x.ofLp 1 ^ 2
      have hx04 : sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4) = a := by simp [a]
      have hx14 : sphereAvg24 (fun x : ℝ²⁴ => (x (1 : Fin 24)) ^ 4) = a := by simp [hswap4]
      -- Rewrite the linearity equalities into the final form.
      -- (We keep the final arithmetic step in `nlinarith` to avoid brittle rewriting.)
      have :
          sphereAvg24 (fun x : ℝ²⁴ =>
              (x (0 : Fin 24)) ^ 4 +
                4 * ((x (0 : Fin 24)) ^ 3 * (x (1 : Fin 24))) +
                  (6 * ((x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ 2) +
                    (4 * (x (0 : Fin 24) * (x (1 : Fin 24)) ^ 3) +
                      (x (1 : Fin 24)) ^ 4))) =
            sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4) +
              sphereAvg24 (fun x : ℝ²⁴ => 4 * ((x (0 : Fin 24)) ^ 3 * (x (1 : Fin 24)))) +
                sphereAvg24 (fun x : ℝ²⁴ => 6 * ((x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ 2)) +
                  sphereAvg24 (fun x : ℝ²⁴ => 4 * (x (0 : Fin 24) * (x (1 : Fin 24)) ^ 3)) +
                    sphereAvg24 (fun x : ℝ²⁴ => (x (1 : Fin 24)) ^ 4) := by
        -- `simp` with the linearity lemmas, keeping associativity explicit.
        -- `h1`..`h4` split the sum right-associated.
        -- Use `ring` to reassociate when needed.
        have := h1
        -- expand the nested sums using `h2`..`h4`
        -- (manual reassociation is robust here)
        simpa [h2, h3, h4, add_assoc] using! this
      -- Combine.
      have htotal :
          sphereAvg24 (fun x : ℝ²⁴ =>
              (x (0 : Fin 24)) ^ 4 +
                4 * ((x (0 : Fin 24)) ^ 3 * (x (1 : Fin 24))) +
                  (6 * ((x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ 2) +
                    (4 * (x (0 : Fin 24) * (x (1 : Fin 24)) ^ 3) +
                      (x (1 : Fin 24)) ^ 4))) = 2 * a + 6 * b := by
        -- substitute the evaluated terms
        -- note: `2*a` is `a + a`
        -- avoid `nlinarith`: rewrite and finish by `ring`
        rw [this, hx04, hx31, hx22, hx13, hx14]
        ring
      exact hcongr.trans htotal
    -- Now solve `a = 3 b`.
    have hsqrt4 : (Real.sqrt 2)⁻¹ ^ 4 = (1 / 4 : ℝ) := by
      -- `(1/√2)^4 = 1/4`.
      have : (Real.sqrt 2) ^ 4 = (4 : ℝ) := by
        calc
          (Real.sqrt 2) ^ 4 = ((Real.sqrt 2) ^ 2) ^ 2 := by ring
          _ = (2 : ℝ) ^ 2 := by
                simp [pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          _ = (4 : ℝ) := by norm_num
      simpa
    have : a = (1 / 4 : ℝ) * (2 * a + 6 * b) := by
      -- `a = E[⟪x,u⟫^4] = (1/4) * E[(x0+x1)^4] = (1/4) * (2a + 6b)`.
      calc
        a = sphereAvg24 (fun x : ℝ²⁴ => (⟪x, u⟫ : ℝ) ^ 4) := ha_inner
        _ =
            (Real.sqrt 2)⁻¹ ^ 4 *
              sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24) + x (1 : Fin 24)) ^ 4) := hscale
        _ = (1 / 4 : ℝ) * (2 * a + 6 * b) := by simp [hsqrt4, havg]
    nlinarith [this]
  -- Second relation: `a + 23 b = 1/24`.
  have hab2 : a + (23 : ℝ) * b = (1 / 24 : ℝ) := by
    -- For each `j ≠ 0`, `E[x0^2 xj^2] = b` by swapping `1` and `j` (fixing `0`).
    have hpair : ∀ j : Fin 24, j ≠ (0 : Fin 24) →
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2 * (x j) ^ 2) = b := by
      intro j hj0
      by_cases hj1 : j = (1 : Fin 24)
      · subst hj1; simp [b]
      · let σ : Fin 24 ≃ Fin 24 := Equiv.swap (1 : Fin 24) j
        let eσ : ℝ²⁴ ≃ₗᵢ[ℝ] ℝ²⁴ :=
          LinearIsometryEquiv.piLpCongrLeft (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (E := ℝ) σ
        have hσ0 : σ (0 : Fin 24) = (0 : Fin 24) := by
          have hj0' : (0 : Fin 24) ≠ j :=
            fun h => hj0 h.symm
          simp [σ, Equiv.swap_apply_def, hj0']
        have hσ1 : σ (1 : Fin 24) = j := by
          simp [σ]
        have hσsymm : σ.symm = σ := by
          simp [σ]
        -- Invariance of the spherical average under the permutation isometry.
        have hinv :
            sphereAvg24 (fun x : ℝ²⁴ =>
                ((eσ x) (0 : Fin 24)) ^ 2 * ((eσ x) (1 : Fin 24)) ^ 2) =
              sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ 2) := by
          simpa using!
            (sphereAvg24_comp_linearIsometryEquiv (e := eσ)
              (f := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ 2))
        -- Read off the permuted coordinates.
        have hcoords :
            (fun x : ℝ²⁴ =>
                ((eσ x) (0 : Fin 24)) ^ 2 * ((eσ x) (1 : Fin 24)) ^ 2) =
              fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2 * (x j) ^ 2 := by
          funext x
          have hσsymm0 : σ.symm (0 : Fin 24) = (0 : Fin 24) := by
            simpa [hσsymm] using! congrArg σ.symm hσ0
          have hσsymm1 : σ.symm (1 : Fin 24) = j := by
            simpa [hσsymm] using! congrArg σ.symm hσ1
          -- expand `eσ` on coordinates
          have h0 : (eσ x) (0 : Fin 24) = x (0 : Fin 24) := by
            simp [eσ, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', hσsymm0]
          have h1 : (eσ x) (1 : Fin 24) = x j := by
            simp [eσ, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', hσsymm1]
          simp [h0, h1]
        have :
            sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2 * (x j) ^ 2) =
              sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2 * (x (1 : Fin 24)) ^ 2) := by
          simpa [hcoords] using! hinv
        simpa [b] using! this
    let s : Finset (Fin 24) := (Finset.univ.erase (0 : Fin 24))
    have hs_card : (s.card : ℝ) = (23 : ℝ) := by simp [s]
    have hs_sum :
        sphereAvg24
            (fun x : ℝ²⁴ => s.sum (fun j => (x (0 : Fin 24)) ^ 2 * (x j) ^ 2)) =
          (23 : ℝ) * b := by
      have hterm :
          ∀ j ∈ s, Integrable (fun x : S23 => (x.1 (0 : Fin 24) : ℝ) ^ 2 * (x.1 j) ^ 2)
            sphereMeasure24 := by
        exact fun j a => integrable_coord_pow_mul_coord_pow 0 j 2 2
      have hsum :=
        sphereAvg24_finset_sum (s := s)
          (f := fun j => fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2 * (x j) ^ 2) hterm
      have hconst :
          s.sum (fun j => sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2 * (x j) ^ 2)) =
            (23 : ℝ) * b := by
        -- rewrite each term using `hpair`
        have : ∀ j ∈ s, sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2 * (x j) ^ 2) = b := by
          intro j hj
          have : j ≠ (0 : Fin 24) := by simpa [s] using! (Finset.mem_erase.1 hj).1
          exact hpair j this
        -- all terms are `b`
        simp [Finset.sum_congr rfl (fun j hj => this j hj), hs_card]
      exact hsum.trans hconst
    -- Pointwise on the sphere: `x0^2 = x0^4 + ∑_{j≠0} x0^2 xj^2`.
    have hpoint : ∀ x : S23,
        ((x.1 (0 : Fin 24) : ℝ) ^ 2) =
          (x.1 (0 : Fin 24) : ℝ) ^ 4 +
            s.sum (fun j => (x.1 (0 : Fin 24) : ℝ) ^ 2 * (x.1 j) ^ 2) := by
      intro x
      have hx : ‖(x : ℝ²⁴)‖ = (1 : ℝ) := by
        exact mem_sphere_zero_iff_norm.mp x.2
      have hxsum : (∑ j : Fin 24, (x.1 j : ℝ) ^ 2) = (1 : ℝ) := by
        have : (∑ j : Fin 24, (x.1 j : ℝ) ^ 2) = ‖(x : ℝ²⁴)‖ ^ 2 := by
          simpa using! (sum_sq_eq_norm_sq (x := (x : ℝ²⁴)))
        simpa [this, hx, pow_two]
      -- Multiply the sum identity by `x0^2` and split off the `j=0` term.
      have hsum :
          (x.1 (0 : Fin 24) : ℝ) ^ 2 * (∑ j : Fin 24, (x.1 j : ℝ) ^ 2) =
            (∑ j : Fin 24, (x.1 (0 : Fin 24) : ℝ) ^ 2 * (x.1 j : ℝ) ^ 2) := by
        simp [Finset.mul_sum, mul_comm]
      have hsplit :
          (∑ j : Fin 24, (x.1 (0 : Fin 24) : ℝ) ^ 2 * (x.1 j : ℝ) ^ 2) =
            (x.1 (0 : Fin 24) : ℝ) ^ 4 +
              s.sum (fun j => (x.1 (0 : Fin 24) : ℝ) ^ 2 * (x.1 j : ℝ) ^ 2) := by
        -- `∑ = term(0) + ∑_{j≠0}`.
        let f : Fin 24 → ℝ :=
          fun j : Fin 24 => (x.1 (0 : Fin 24) : ℝ) ^ 2 * (x.1 j : ℝ) ^ 2
        have h :=
          (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 24))) (a := (0 : Fin 24))
            (f := f) (by simp))
        -- Rewrite `univ.sum` as `f 0 + (univ.erase 0).sum` and substitute `s = univ.erase 0`.
        have h' : (∑ j : Fin 24, f j) = f (0 : Fin 24) + s.sum f := by
          rfl
        have hf0 : f (0 : Fin 24) = (x.1 (0 : Fin 24) : ℝ) ^ 4 := by
          simp [f, pow_succ, mul_assoc, mul_comm]
        simpa [f, hf0] using! h'
      -- finish
      calc
        (x.1 (0 : Fin 24) : ℝ) ^ 2 =
            (x.1 (0 : Fin 24) : ℝ) ^ 2 * (∑ j : Fin 24, (x.1 j : ℝ) ^ 2) := by
              simp [hxsum]
        _ = (x.1 (0 : Fin 24) : ℝ) ^ 4 +
              s.sum (fun j => (x.1 (0 : Fin 24) : ℝ) ^ 2 * (x.1 j) ^ 2) := by
              simp [hsum, hsplit]
    have hI2 : Integrable (fun x : S23 => (x.1 (0 : Fin 24) : ℝ) ^ 2) sphereMeasure24 := by
      simpa [mul_one] using!
        integrable_coord_pow_mul_coord_pow (i := (0 : Fin 24)) (j := (0 : Fin 24)) (m := 2) (n := 0)
    have hI4 : Integrable (fun x : S23 => (x.1 (0 : Fin 24) : ℝ) ^ 4) sphereMeasure24 := by
      simpa [mul_one] using!
        integrable_coord_pow_mul_coord_pow (i := (0 : Fin 24)) (j := (0 : Fin 24)) (m := 4) (n := 0)
    have hIsum :
        Integrable
          (fun x : S23 => s.sum (fun j => (x.1 (0 : Fin 24) : ℝ) ^ 2 * (x.1 j) ^ 2))
          sphereMeasure24 := by
      refine (integrable_finset_sum (s := s)
        (f := fun j : Fin 24 => fun x : S23 => (x.1 (0 : Fin 24) : ℝ) ^ 2 * (x.1 j) ^ 2) ?_)
      intro j hj
      simpa using! integrable_coord_pow_mul_coord_pow (i := (0 : Fin 24)) (j := j) (m := 2) (n := 2)
    have havg :
        sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2) =
          sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4) +
            sphereAvg24 (fun x : ℝ²⁴ => s.sum (fun j => (x (0 : Fin 24)) ^ 2 * (x j) ^ 2)) := by
      have hcongr :=
        sphereAvg24_congr
          (f := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2)
          (g := fun x : ℝ²⁴ =>
            (x (0 : Fin 24)) ^ 4 + s.sum (fun j => (x (0 : Fin 24)) ^ 2 * (x j) ^ 2))
          (by intro x; simpa using! hpoint x)
      have hadd :=
        sphereAvg24_add
          (f := fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4)
          (g := fun x : ℝ²⁴ => s.sum (fun j => (x (0 : Fin 24)) ^ 2 * (x j) ^ 2))
          (hf := hI4) (hg := hIsum)
      simpa [hcongr] using! hcongr.trans hadd
    have h2 : sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 2) = (1 / 24 : ℝ) := by
      simpa using! (sphereAvg24_coord_sq (i := (0 : Fin 24)))
    have ha : sphereAvg24 (fun x : ℝ²⁴ => (x (0 : Fin 24)) ^ 4) = a := by simp [a]
    have : a + (23 : ℝ) * b = (1 / 24 : ℝ) := by
      -- rearrange `havg` using the computed pieces
      linarith [havg, h2, ha, hs_sum]
    exact this
  -- Solve the 2×2 system.
  have ha_val : a = (1 / 208 : ℝ) := by
    nlinarith [hab, hab2]
  simp [a, ha_val]

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14
