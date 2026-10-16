import E8Leech.EvenUnimodularTheta
import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# Counting lattice points in a ball through a sublattice with a short basis

Let `Λ ⊂ ℝᵈ` be a lattice containing the lattice `ℤb₁ + ⋯ + ℤb_d` of a basis `b`. A finite set of
points of `Λ` in a ball of radius `R` has at most `vol(B_{R+ρ}) / covol(Λ)` elements, where
`ρ = ∑ |bᵢ|` (`card_mul_covolume_le`). No basis of `Λ` enters: the points are counted coset by coset
of the sublattice, whose fundamental parallelepiped has diameter at most `ρ`, and the number of
cosets is the ratio of the covolumes. This replaces the Voronoi cell in Step 3 of the proof of
Theorem 1.5 of Böröczky–Radchenko–Ramos.

* `card_mul_volume_fundamentalDomain_le`: the count in one coset.
* `card_mul_covolume_le`: the count in `Λ`.
* `covolume_sq_eq_det_gram`: the covolume of the lattice of a basis and its Gram determinant.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric
open scoped ENNReal InnerProductSpace Pointwise

/-- Points of one coset of the lattice of a basis `b` in a ball: the translates of the fundamental
parallelepiped are disjoint and lie in a ball of radius `R + ∑ |bᵢ|`. -/
theorem card_mul_volume_fundamentalDomain_le {d : ℕ} (b : Module.Basis (Fin d) ℝ (Ambient d))
    (T : Finset (Ambient d))
    (hT : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ Submodule.span ℤ (Set.range b)) {c : Ambient d} {R : ℝ}
    (hball : ∀ t ∈ T, t ∈ closedBall c R) :
    (T.card : ℝ≥0∞) * volume (ZSpan.fundamentalDomain b) ≤
      volume (closedBall c (R + ∑ i, ‖b i‖)) := by
  classical
  have hdisj : (T : Set (Ambient d)).PairwiseDisjoint fun t => t +ᵥ ZSpan.fundamentalDomain b := by
    intro t ht t' ht' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro y ⟨f, hf, rfl⟩ ⟨f', hf', hy⟩
    apply hne
    have hvadd : t' + f' = t + f := hy
    obtain ⟨v, _, huniq⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b f
    have h0 : (0 : Submodule.span ℤ (Set.range b)) = v := huniq 0 (by
      show (0 : Ambient d) + f ∈ ZSpan.fundamentalDomain b
      rw [zero_add]
      exact hf)
    have h1 : (⟨t - t', hT t ht t' ht'⟩ : Submodule.span ℤ (Set.range b)) = v := huniq _ (by
      show t - t' + f ∈ ZSpan.fundamentalDomain b
      have e : t - t' + f = f' := by
        rw [sub_add_eq_add_sub, ← hvadd]
        abel
      rw [e]
      exact hf')
    have h2 : t - t' = 0 := congrArg Subtype.val (h1.trans h0.symm)
    exact sub_eq_zero.mp h2
  have hmeas : ∀ t ∈ T, MeasurableSet (t +ᵥ ZSpan.fundamentalDomain b) := fun t _ =>
    (ZSpan.fundamentalDomain_measurableSet b).const_vadd t
  have hsub : (⋃ t ∈ T, t +ᵥ ZSpan.fundamentalDomain b) ⊆ closedBall c (R + ∑ i, ‖b i‖) := by
    intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨t, ht, f, hf, rfl⟩ := hy
    have hfn : ‖f‖ ≤ ∑ i, ‖b i‖ := by
      have h := ZSpan.norm_fract_le (K := ℝ) b f
      rwa [ZSpan.fract_eq_self.mpr hf] at h
    have ht' := hball t ht
    rw [mem_closedBall, dist_eq_norm] at ht' ⊢
    have e : (fun x => t +ᵥ x) f - c = (t - c) + f := by
      show t + f - c = t - c + f
      abel
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add ht' hfn)
  calc (T.card : ℝ≥0∞) * volume (ZSpan.fundamentalDomain b)
      = ∑ t ∈ T, volume (t +ᵥ ZSpan.fundamentalDomain b) := by
        rw [Finset.sum_congr rfl fun t _ => measure_vadd volume t (ZSpan.fundamentalDomain b),
          Finset.sum_const, nsmul_eq_mul]
    _ = volume (⋃ t ∈ T, t +ᵥ ZSpan.fundamentalDomain b) :=
        (measure_biUnion_finset hdisj hmeas).symm
    _ ≤ volume (closedBall c (R + ∑ i, ‖b i‖)) := measure_mono hsub

/-- **Lattice points in a ball.** A lattice `Λ` containing the lattice of a basis `b` has at most
`vol(B_{R+ρ}) / covol(Λ)` points in a ball of radius `R`, `ρ = ∑ |bᵢ|`. -/
theorem card_mul_covolume_le {d : ℕ} (b : Module.Basis (Fin d) ℝ (Ambient d))
    (Λ : Submodule ℤ (Ambient d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hle : Submodule.span ℤ (Set.range b) ≤ Λ) (T : Finset (Ambient d))
    (hT : ∀ t ∈ T, t ∈ Λ) {c : Ambient d} {R : ℝ} (hball : ∀ t ∈ T, t ∈ closedBall c R) :
    (T.card : ℝ) * ZLattice.covolume Λ ≤ volume.real (closedBall c (R + ∑ i, ‖b i‖)) := by
  classical
  have hcov' : ZLattice.covolume (Submodule.span ℤ (Set.range b)) =
      volume.real (ZSpan.fundamentalDomain b) :=
    ZLattice.covolume_eq_measure_fundamentalDomain _ volume (ZSpan.isAddFundamentalDomain b volume)
  have hidx := ZLattice.covolume_div_covolume_eq_relIndex' (Submodule.span ℤ (Set.range b)) Λ hle
  have hposΛ := ZLattice.covolume_pos Λ volume
  have hpos' := ZLattice.covolume_pos (Submodule.span ℤ (Set.range b)) volume
  have hm0 : 0 < (Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex Λ.toAddSubgroup := by
    have h : (0 : ℝ) <
        ((Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) := by
      rw [← hidx]
      exact div_pos hpos' hposΛ
    exact_mod_cast h
  -- the cosets of the sublattice in `Λ`
  have hcardQ : Nat.card (Λ.toAddSubgroup ⧸
      (Submodule.span ℤ (Set.range b)).toAddSubgroup.addSubgroupOf Λ.toAddSubgroup) =
      (Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex Λ.toAddSubgroup := rfl
  have hfinQ : Finite (Λ.toAddSubgroup ⧸
      (Submodule.span ℤ (Set.range b)).toAddSubgroup.addSubgroupOf Λ.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero (by rw [hcardQ]; exact hm0.ne')
  have hfinT : Fintype (Λ.toAddSubgroup ⧸
      (Submodule.span ℤ (Set.range b)).toAddSubgroup.addSubgroupOf Λ.toAddSubgroup) :=
    Fintype.ofFinite _
  let φ : {t // t ∈ T} → Λ.toAddSubgroup ⧸
      (Submodule.span ℤ (Set.range b)).toAddSubgroup.addSubgroupOf Λ.toAddSubgroup :=
    fun t => QuotientAddGroup.mk ⟨t.1, hT t.1 t.2⟩
  have hfib : ∀ q ∈ T.attach.image φ,
      ((T.attach.filter fun x => φ x = q).card : ℝ) * volume.real (ZSpan.fundamentalDomain b) ≤
        volume.real (closedBall c (R + ∑ i, ‖b i‖)) := by
    intro q _
    have hcard : ((T.attach.filter fun x => φ x = q).image Subtype.val).card =
        (T.attach.filter fun x => φ x = q).card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    have hT' : ∀ t ∈ (T.attach.filter fun x => φ x = q).image Subtype.val,
        ∀ t' ∈ (T.attach.filter fun x => φ x = q).image Subtype.val,
        t - t' ∈ Submodule.span ℤ (Set.range b) := by
      intro t ht t' ht'
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp ht'
      have e : φ x' = φ x := (Finset.mem_filter.mp hx').2.trans (Finset.mem_filter.mp hx).2.symm
      have h1 := QuotientAddGroup.eq.mp e
      have h2 := AddSubgroup.mem_addSubgroupOf.mp h1
      have h3 : (x.1 : Ambient d) - x'.1 = -x'.1 + x.1 := sub_eq_neg_add _ _
      rw [h3]
      exact h2
    have hb' : ∀ t ∈ (T.attach.filter fun x => φ x = q).image Subtype.val,
        t ∈ closedBall c R := by
      intro t ht
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ht
      exact hball x.1 x.2
    have h1 := card_mul_volume_fundamentalDomain_le b _ hT' hb'
    have h2 := ENNReal.toReal_mono (measure_closedBall_lt_top (μ := volume)).ne h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, hcard] at h2
    exact h2
  have hV0 : 0 ≤ volume.real (closedBall c (R + ∑ i, ‖b i‖)) := measureReal_nonneg
  have hcount : (T.card : ℝ) * volume.real (ZSpan.fundamentalDomain b) ≤
      ((Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) *
        volume.real (closedBall c (R + ∑ i, ‖b i‖)) := by
    have e1 : T.card = ∑ q ∈ T.attach.image φ, (T.attach.filter fun x => φ x = q).card := by
      rw [← Finset.card_attach]
      exact Finset.card_eq_sum_card_image φ T.attach
    have e2 : ((T.attach.image φ).card : ℝ) ≤
        ((Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) := by
      have h := Finset.card_le_univ (T.attach.image φ)
      rw [← Nat.card_eq_fintype_card, hcardQ] at h
      exact_mod_cast h
    calc (T.card : ℝ) * volume.real (ZSpan.fundamentalDomain b)
        = ∑ q ∈ T.attach.image φ, ((T.attach.filter fun x => φ x = q).card : ℝ) *
            volume.real (ZSpan.fundamentalDomain b) := by
          rw [e1]
          push_cast
          rw [Finset.sum_mul]
      _ ≤ ∑ q ∈ T.attach.image φ, volume.real (closedBall c (R + ∑ i, ‖b i‖)) :=
          Finset.sum_le_sum hfib
      _ = ((T.attach.image φ).card : ℝ) * volume.real (closedBall c (R + ∑ i, ‖b i‖)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right e2 hV0
  -- `covol Λ' = relIndex · covol Λ`
  have hrel : ZLattice.covolume (Submodule.span ℤ (Set.range b)) =
      ((Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) *
        ZLattice.covolume Λ := by
    rw [← hidx]
    field_simp
  rw [← hcov', hrel] at hcount
  have hm' : (0 : ℝ) <
      ((Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) := by
    exact_mod_cast hm0
  have h3 : ((Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) *
      ((T.card : ℝ) * ZLattice.covolume Λ) ≤
      ((Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) *
        volume.real (closedBall c (R + ∑ i, ‖b i‖)) := by
    calc _ = (T.card : ℝ) * (((Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex
          Λ.toAddSubgroup : ℝ) * ZLattice.covolume Λ) := by ring
      _ ≤ _ := hcount
  exact le_of_mul_le_mul_left h3 hm'

/-- The squared covolume of the lattice of a basis is the determinant of its Gram matrix. -/
theorem covolume_sq_eq_det_gram {d : ℕ} (b : Module.Basis (Fin d) ℝ (Ambient d)) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) ^ 2 =
      (Matrix.of fun i j => ⟪b i, b j⟫_ℝ).det := by
  classical
  let b₀ : OrthonormalBasis (Fin d) ℝ (Ambient d) := EuclideanSpace.basisFun (Fin d) ℝ
  let bZ : Module.Basis (Fin d) ℤ (Submodule.span ℤ (Set.range b)) := b.restrictScalars ℤ
  have hbZ : ((↑) ∘ bZ : Fin d → Ambient d) = b := by
    funext i
    exact Module.Basis.restrictScalars_apply ℤ b i
  have hvol : (volume : Measure (Ambient d)).real (ZSpan.fundamentalDomain b₀.toBasis) = 1 := by
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped b₀.toBasis volume),
      measureReal_def, OrthonormalBasis.coe_toBasis, b₀.volume_parallelepiped]
    simp
  have hgram : (b₀.toBasis.toMatrix b).transpose * b₀.toBasis.toMatrix b =
      Matrix.of fun i j => ⟪b i, b j⟫_ℝ := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Module.Basis.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply, Matrix.of_apply]
    rw [← b₀.sum_inner_mul_inner (b j) (b k)]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm (b j) (b₀ i)]
  rw [ZLattice.covolume_eq_det_mul_measureReal _ volume bZ b₀.toBasis, hbZ, hvol, mul_one, sq_abs,
    Module.Basis.det_apply, ← hgram, Matrix.det_mul, Matrix.det_transpose, sq]

end E8Leech
