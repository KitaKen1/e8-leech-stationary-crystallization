import E8Leech.KronLeechH2Sign

/-!
# A quantitative form of the truncated Leech kernel inequality (6.4)(2)

The truncated numerator of `KronLeechH2Sign` is `H₂ = b² (b − a) S` with the split divided
difference `S = t̂ · ρ₁[a, b] + b · ρ₂[a, b]`, and
`21743271936 Λ π û t̂² Δ(it) 𝒩 · (𝒦̂(iu, it) − e^{2πt}(a₁ t + a₀)) = H₂`. If a cell passes the
vertex check with the margin `μ` (the margin of the pivot `a⁵` lowered by `μ`), then
`S > t̂ a⁵ μ` on the cell, hence

`b² t̂ a⁵ μ < 21743271936 Λ π û t̂² Δ(it) (𝒩/(b − a)) · (𝒦̂(iu, it) − e^{2πt}(a₁ t + a₀))`

(`LeechTruncMargin`). On a strip `u ∈ [3, 4]`, `t ≥ T` this gives the linear growth of the
truncated kernel (`LeechTruncLinear`).

* `combination_gt_vertex`: `t̂ f₁ + b f₂ > t̂ aⁱ⁺¹ μ` on a cell from two models, by the vertex
  check with a margin.
* `leechHatTrunc_margin_of_dd`, `leechHatTrunc_margin_of_cell`, `leechHatTrunc_margin_of_cover`:
  the quantitative form at a point, on a cell and on a cover.
-/

noncomputable section

namespace E8Leech.Kron

open E8Leech.Taylor
open scoped Real

/-! ## A split combination with the vertex check and a margin -/

/-- **`t̂ f₁ + b f₂ > t̂ aⁱ⁺¹ μ` on a cell, vertex check with a margin.** The statement of
`combination_pos_vertex` with the margin of the pivot `aⁱ⁺¹` lowered by `μ`. -/
theorem combination_gt_vertex {Bx : Bounds} {f₁ f₂ : NEnv → ℝ} {T₁ T₂ : MTM} {i : ℕ}
    (h₁ : T₁.Approx Bx (fun e => True ∧ e.a ≠ e.b) f₁)
    (h₂ : T₂.Approx Bx (fun e => True ∧ e.a ≠ e.b) f₂)
    (hd₁ : T₁.Divisible i 0) (hd₂ : T₂.Divisible i 0)
    (hPB : (T₁.quots i 0).PB.MultiAffine) (hPA : (T₁.quots i 0).PA.MultiAffine) {C : Cell}
    (hC : C.Valid) (hsub : C.hi.le Bx) {w μ : ℚ} (hw : WOK C w)
    (hOK : ∀ p q r : Bool,
      C.PosOK ((T₁.quots i 0).marginBv C p q r + w * min ((T₂.quots i 0).marginB C) 0)
        ((T₁.quots i 0).marginAv C p q r + (w * min ((T₂.quots i 0).marginA C) 0 - μ)) 0)
    {u t : ℝ} (ht : 0 < t) (hut : u ≠ t) (hmem : C.Mem (axisNEnv u t)) :
    (axisNEnv u t).t * ((axisNEnv u t).a ^ (i + 1) * μ) <
      (axisNEnv u t).t * f₁ (axisNEnv u t) + (axisNEnv u t).b * f₂ (axisNEnv u t) := by
  have hπ := Real.pi_pos
  have ha : 0 < (axisNEnv u t).a := Real.exp_pos _
  have hb : 0 < (axisNEnv u t).b := Real.exp_pos _
  have hY : 0 < (axisNEnv u t).t := by
    have h : (axisNEnv u t).t = 1 / (π * t) := rfl
    rw [h]
    positivity
  have hab : (axisNEnv u t).a ≠ (axisNEnv u t).b := by
    intro h
    have h' : Real.exp (-π * u) = Real.exp (-π * t) := h
    exact hut (mul_left_cancel₀ (neg_ne_zero.mpr hπ.ne') (Real.exp_injective h'))
  have l₁ := MTM.lower_of_divisible_eval h₁ hd₁ hC hsub hmem ⟨trivial, hab⟩ ha.le hb.le
  have l₂ := MTM.lower_of_divisible h₂ hd₂ hC hsub hmem ⟨trivial, hab⟩ ha.le hb.le
  have hwb : (axisNEnv u t).b ≤ (w : ℝ) * (axisNEnv u t).t := by
    have hmem' : C.Mem (recNEnv (1 / (π * u)) (1 / (π * t))) := by
      rw [← axisNEnv_eq_recNEnv]
      exact hmem
    have h := hw.le hC (y := 1 / (π * t)) (by positivity) hmem'
    have hb' : (axisNEnv u t).b = Real.exp (-(1 / (π * t))⁻¹) := by
      rw [axisNEnv_eq_recNEnv]
      rfl
    have ht' : (axisNEnv u t).t = 1 / (π * t) := rfl
    rw [hb', ht']
    exact h
  obtain ⟨W, hWdef, hW0, hWw⟩ : ∃ W : ℝ, W * (axisNEnv u t).t = (axisNEnv u t).b ∧ 0 ≤ W ∧
      W ≤ (w : ℝ) :=
    ⟨(axisNEnv u t).b / (axisNEnv u t).t, div_mul_cancel₀ _ hY.ne', div_nonneg hb.le hY.le,
      (div_le_iff₀ hY).mpr hwb⟩
  have hkey := Cell.pos_of_vertices hC hPB hPA hOK hmem ha hb
  push_cast at hkey
  have hB := mul_min_le (m := (((T₂.quots i 0).marginB C : ℚ) : ℝ)) hW0 hWw
  have hA := mul_min_le (m := (((T₂.quots i 0).marginA C : ℚ) : ℝ)) hW0 hWw
  have kB := mul_le_mul_of_nonneg_left hB hb.le
  have kA := mul_le_mul_of_nonneg_left hA ha.le
  have hc : 0 < (axisNEnv u t).a ^ i * (axisNEnv u t).b ^ 0 := by positivity
  have k2 := mul_le_mul_of_nonneg_left l₂ hW0
  have hpos : (axisNEnv u t).a ^ (i + 1) * μ <
      f₁ (axisNEnv u t) + W * f₂ (axisNEnv u t) := by
    have hin : (axisNEnv u t).a * (μ : ℝ) <
        (axisNEnv u t).b * (IPoly.eval (T₁.quots i 0).PB (axisNEnv u t) -
          (IPoly.evalUB C.hi (T₁.quots i 0).RB : ℝ)) +
        (axisNEnv u t).a * (IPoly.eval (T₁.quots i 0).PA (axisNEnv u t) -
          (IPoly.evalUB C.hi (T₁.quots i 0).RA : ℝ)) +
        W * ((axisNEnv u t).b * (((T₂.quots i 0).marginB C : ℚ) : ℝ) +
          (axisNEnv u t).a * (((T₂.quots i 0).marginA C : ℚ) : ℝ)) := by
      nlinarith [hkey, kB, kA]
    have hmul := mul_lt_mul_of_pos_left hin hc
    have hpow : (axisNEnv u t).a ^ (i + 1) * (μ : ℝ) =
        (axisNEnv u t).a ^ i * (axisNEnv u t).b ^ 0 * ((axisNEnv u t).a * μ) := by
      ring
    rw [hpow]
    generalize (axisNEnv u t).a ^ i * (axisNEnv u t).b ^ 0 = c at hmul l₁ k2
    nlinarith [hmul, l₁, k2]
  have hlin : (axisNEnv u t).t * f₁ (axisNEnv u t) + (axisNEnv u t).b * f₂ (axisNEnv u t) =
      (axisNEnv u t).t * (f₁ (axisNEnv u t) + W * f₂ (axisNEnv u t)) := by
    rw [← hWdef]
    ring
  rw [hlin]
  exact mul_lt_mul_of_pos_left hpos hY

/-! ## The quantitative form -/

/-- The real-number core: from `c Δ N (K − E) = b² δ S` and `S > s`. -/
theorem trunc_gt_of_split {c Δ N δ K E b S s : ℝ} (hδ : δ ≠ 0) (hb : 0 < b) (hS : s < S)
    (h : c * Δ * N * (K - E) = b ^ 2 * δ * S) : b ^ 2 * s < c * Δ * (N / δ) * (K - E) := by
  have e : c * Δ * (N / δ) * (K - E) = b ^ 2 * S := by
    field_simp
    linear_combination h
  rw [e]
  exact mul_lt_mul_of_pos_left hS (pow_pos hb 2)

/-- **The quantitative form of the truncated inequality at `(u, t)`** with the margin `μ`:
`b² t̂ a⁵ μ < 21743271936 Λ π û t̂² Δ(it) (𝒩/(b − a)) (𝒦̂(iu, it) − e^{2πt}(a₁ t + a₀))`. -/
def LeechTruncMargin (Λ : ℕ) (μ : ℚ) (u t : ℝ) : Prop :=
  Real.exp (-π * t) ^ 2 * (1 / (π * t) * (Real.exp (-π * u) ^ 5 * μ)) <
    21743271936 * Λ * π * (1 / (π * u)) * (1 / (π * t)) ^ 2 * axDelta (axV t) (axW t) *
      (axNu (axV u) (axW u) (axV t) (axW t) / (Real.exp (-π * t) - Real.exp (-π * u))) *
      ((ckmrvLeechHatKernel (imagPt u) (imagPt t)).re -
        Real.exp (2 * π * t) * ((leechAxisCusp (-1) u 0).re * t + (leechAxisCusp (-1) u 1).re))

section Lin

variable {Λ : ℕ} {prog : List IInstr} {k₁ k₀ : ℕ}

/-- **The quantitative form at a point** from a lower bound `s` of the split divided difference
`t̂ · ρ₁[a, b] + b · ρ₂[a, b]`. -/
theorem leechHatTrunc_margin_of_dd (h2 : 2 ∣ Λ)
    (hp₁ : (ISLP.runExpr prog []).getD k₁ (.cst 0) = leechH21E Λ)
    (hp₀ : (ISLP.runExpr prog []).getD k₀ (.cst 0) = leechH20E Λ) {u t : ℝ} (hu : 0 < u)
    (ht : 0 < t) (hut : u ≠ t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t))
    (hsmall : NomeSmallH (axisNEnv u t))
    (hc₁ : ∀ side : Bool, ∀ j, j < 2 →
      (ISLP.runR (hAtoms Λ) side (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
        ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₁ 1 + j) 0 = 0)
    (hc₀ : ∀ side : Bool, ∀ j, j < 3 →
      (ISLP.runR (hAtoms Λ) side (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
        ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + j) 0 = 0) {s : ℝ}
    (hDD : s < (axisNEnv u t).t *
        (((ISLP.runR (hAtoms Λ) false (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
            ((ISLP.tr3 (ISLP.zleafH Λ) prog).1.length + 1) 0 -
          (ISLP.runR (hAtoms Λ) true (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
            ((ISLP.tr3 (ISLP.zleafH Λ) prog).1.length + 1) 0) /
          ((axisNEnv u t).b - (axisNEnv u t).a)) +
      (axisNEnv u t).b *
        (((ISLP.runR (hAtoms Λ) false (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
            ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + 3) 0 -
          (ISLP.runR (hAtoms Λ) true (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
            ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + 3) 0) /
          ((axisNEnv u t).b - (axisNEnv u t).a))) :
    (axisNEnv u t).b ^ 2 * s <
      21743271936 * Λ * π * (1 / (π * u)) * (1 / (π * t)) ^ 2 * axDelta (axV t) (axW t) *
        (axNu (axV u) (axW u) (axV t) (axW t) / ((axisNEnv u t).b - (axisNEnv u t).a)) *
        ((ckmrvLeechHatKernel (imagPt u) (imagPt t)).re -
          Real.exp (2 * π * t) *
            ((leechAxisCusp (-1) u 0).re * t + (leechAxisCusp (-1) u 1).re)) := by
  have hπ := Real.pi_pos
  obtain ⟨⟨ha4, hb4, ha3s, ha4s, hb3s, hb4s⟩, haη, hbη⟩ := hsmall
  have ha : 0 < (axisNEnv u t).a := Real.exp_pos _
  have hb : 0 < (axisNEnv u t).b := Real.exp_pos _
  -- the two parts on the two sides
  have hB1 := h2_rho1 (prog := prog) h2 false (axisNEnv u t) hb.le hb4 hb3s hb4s hbη k₁ (hc₁ false)
  have hA1 := h2_rho1 (prog := prog) h2 true (axisNEnv u t) ha.le ha4 ha3s ha4s haη k₁ (hc₁ true)
  have hB0 := h2_rho2 (prog := prog) h2 false (axisNEnv u t) hb.le hb4 hb3s hb4s hbη k₁ k₀
    (hc₀ false)
  have hA0 := h2_rho2 (prog := prog) h2 true (axisNEnv u t) ha.le ha4 ha3s ha4s haη k₁ k₀
    (hc₀ true)
  rw [hp₁] at hB1 hA1
  rw [hp₀] at hB0 hA0
  have z1 : IExpr.evalA (hAtoms Λ) (leechH21E Λ) (axisNEnv u t) = 0 := by
    rw [hAtoms_eq]
    exact leechH21E_evalA Λ _ _
  have z0 : IExpr.evalA (hAtoms Λ) (leechH20E Λ) (axisNEnv u t) = 0 := by
    rw [hAtoms_eq]
    exact leechH20E_evalA Λ _ _
  have hA1' : (ISLP.runR (hAtoms Λ) true (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
      ((ISLP.tr3 (ISLP.zleafH Λ) prog).1.length + 1) 0 = 0 := by
    have h : IExpr.evalA (hAtoms Λ) (leechH21E Λ) (axisNEnv u t) = (axisNEnv u t).a ^ 2 *
        (ISLP.runR (hAtoms Λ) true (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
          ((ISLP.tr3 (ISLP.zleafH Λ) prog).1.length + 1) 0 := hA1
    rw [z1] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero 2 ha.ne')
  have hA0' : (ISLP.runR (hAtoms Λ) true (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
      ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + 3) 0 = 0 := by
    have h : IExpr.evalA (hAtoms Λ) (leechH20E Λ) (axisNEnv u t) = (axisNEnv u t).a ^ 3 *
        (ISLP.runR (hAtoms Λ) true (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
          ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + 3) 0 := hA0
    rw [z0] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero 3 ha.ne')
  rw [hA1', hA0', sub_zero, sub_zero] at hDD
  have hB1' : IExpr.evalB (hAtoms Λ) (leechH21E Λ) (axisNEnv u t) = (axisNEnv u t).b ^ 2 *
      (ISLP.runR (hAtoms Λ) false (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
        ((ISLP.tr3 (ISLP.zleafH Λ) prog).1.length + 1) 0 := hB1
  have hB0' : IExpr.evalB (hAtoms Λ) (leechH20E Λ) (axisNEnv u t) = (axisNEnv u t).b ^ 3 *
      (ISLP.runR (hAtoms Λ) false (axisNEnv u t) (ISLP.h2Prog Λ prog k₁) []).getD
        ((ISLP.tr3 (ISLP.zleafH Λ) prog).2.getD k₀ 1 + 3) 0 := hB0
  -- the numerator
  have hax := leechH2_eval_axis Λ (red3Atoms Λ ++ [lam2Eta Λ]) hu ht hJ
  rw [← hAtoms_eq, hB0', hB1'] at hax
  have hδ : (axisNEnv u t).b - (axisNEnv u t).a ≠ 0 := by
    intro h0
    have h' : Real.exp (-π * t) = Real.exp (-π * u) := sub_eq_zero.mp h0
    exact hut (mul_left_cancel₀ (neg_ne_zero.mpr hπ.ne') (Real.exp_injective h')).symm
  refine trunc_gt_of_split hδ hb hDD ?_
  rw [← hax]
  field_simp
  ring

/-- **The quantitative form on a cell.** A cell inside the bounds of the models that passes the
vertex check with the margin `μ` (pivots `a⁴b` and `a⁵`) consists of points where the quantitative
form holds. -/
theorem leechHatTrunc_margin_of_cell {Bx : Bounds} {T₁ T₂ : MTM} (h2 : 2 ∣ Λ)
    (hp₁ : (ISLP.runExpr prog []).getD k₁ (.cst 0) = leechH21E Λ)
    (hp₀ : (ISLP.runExpr prog []).getD k₀ (.cst 0) = leechH20E Λ)
    (hM : LeechH2Models Bx Λ prog k₁ k₀ T₁ T₂) (hd₁ : T₁.Divisible 4 0) (hd₂ : T₂.Divisible 4 0)
    (hPB : (T₁.quots 4 0).PB.MultiAffine) (hPA : (T₁.quots 4 0).PA.MultiAffine) {C : Cell}
    (hC : C.Valid) (hsub : C.hi.le Bx) {w μ : ℚ} (hw : WOK C w)
    (hOK : ∀ p q r : Bool,
      C.PosOK ((T₁.quots 4 0).marginBv C p q r + w * min ((T₂.quots 4 0).marginB C) 0)
        ((T₁.quots 4 0).marginAv C p q r + (w * min ((T₂.quots 4 0).marginA C) 0 - μ)) 0)
    {u t : ℝ} (hu : 0 < u) (ht : 0 < t) (hut : u ≠ t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t))
    (hmem : C.Mem (axisNEnv u t)) : LeechTruncMargin Λ μ u t := by
  have hBx : Bx.Mem (axisNEnv u t) := Bounds.mem_of_le hC.2 hsub hmem.2.2.2.2.2
  exact leechHatTrunc_margin_of_dd h2 hp₁ hp₀ hu ht hut hJ (hM.small _ hBx)
    (fun side j hj => hM.zero₁ side j hj _ hBx) (fun side j hj => hM.zero₀ side j hj _ hBx)
    (combination_gt_vertex hM.dd₁ hM.dd₀ hd₁ hd₂ hPB hPA hC hsub hw hOK ht hut hmem)

/-- The cell test of the truncated numerator with the vertex check and the margin `μ`. `w` bounds
`b / t̂` on the cell; the second auxiliary number of a leaf is not used. -/
def vertexMarginCellOK (Bx : Bounds) (Q₁ Q₂ : Quots) (μ : ℚ) (C : Cell) (w _ : ℚ) : Bool :=
  decide (C.hi.le Bx ∧ WOK C w ∧ ∀ p q r : Bool,
    C.PosOK (Q₁.marginBv C p q r + w * min (Q₂.marginB C) 0)
      (Q₁.marginAv C p q r + (w * min (Q₂.marginA C) 0 - μ)) 0)

/-- **The quantitative form on a cover**, in reciprocal coordinates, outside the corner. -/
theorem leechHatTrunc_margin_of_cover {Bx : Bounds} {T₁ T₂ : MTM} (h2 : 2 ∣ Λ)
    (hp₁ : (ISLP.runExpr prog []).getD k₁ (.cst 0) = leechH21E Λ)
    (hp₀ : (ISLP.runExpr prog []).getD k₀ (.cst 0) = leechH20E Λ)
    (hM : LeechH2Models Bx Λ prog k₁ k₀ T₁ T₂) (hd₁ : T₁.Divisible 4 0) (hd₂ : T₂.Divisible 4 0)
    {Q₁ Q₂ : Quots} (hQ₁ : T₁.quots 4 0 = Q₁) (hQ₂ : T₂.quots 4 0 = Q₂)
    (hPB : Q₁.PB.MultiAffine) (hPA : Q₁.PA.MultiAffine) {k n : ℕ} {c μ : ℚ} {cov : Cover}
    {r : Rect} (hcov : cov.check (cellOKb k n) (vertexMarginCellOK Bx Q₁ Q₂ μ) c r = true)
    {u t : ℝ} (hu : 0 < u) (ht : 0 < t) (hr : r.Mem (1 / (π * u)) (1 / (π * t))) (hut : u ≠ t)
    (hJ : kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t)) :
    ((c : ℝ) ≤ 1 / (π * u) ∧ (c : ℝ) ≤ 1 / (π * t)) ∨ LeechTruncMargin Λ μ u t := by
  subst hQ₁ hQ₂
  have hπ := Real.pi_pos
  have hx : 0 < 1 / (π * u) := by positivity
  have hy : 0 < 1 / (π * t) := by positivity
  have h := Cover.sound (env := recNEnv)
    (P := fun x y => ∀ u t : ℝ, 0 < u → 0 < t → x = 1 / (π * u) → y = 1 / (π * t) → u ≠ t →
      kleinModularJ (imagPt u) ≠ kleinModularJ (imagPt t) → LeechTruncMargin Λ μ u t)
    (cellOKb_spec k n)
    (fun C w _ hC hok x y _ _ hmem u t hu ht hxu hyt hut hJ => by
      simp only [vertexMarginCellOK, decide_eq_true_eq] at hok
      refine leechHatTrunc_margin_of_cell h2 hp₁ hp₀ hM hd₁ hd₂ hPB hPA hC hok.1 hok.2.1 hok.2.2
        hu ht hut hJ ?_
      rw [axisNEnv_eq_recNEnv, ← hxu, ← hyt]
      exact hmem)
    cov r hcov _ _ hx hy hr
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (h u t hu ht rfl rfl hut hJ)

end Lin

end E8Leech.Kron
