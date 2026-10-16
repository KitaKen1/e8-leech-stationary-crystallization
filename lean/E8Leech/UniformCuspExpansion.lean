import E8Leech.CKMRVKernelUniform
import E8Leech.CuspExpansion

/-!
# Cusp expansions uniform in a bounded parameter family

Second-order expansions with bounded coefficient functions on the product
filter `𝓟 K ×ˢ atImInfty`. The algebra retains a common remainder bound,
which cannot be inferred from the separate pointwise expansions.
-/

noncomputable section
namespace E8Leech
open Complex Filter Topology Set Asymptotics
open UpperHalfPlane hiding I
open scoped Real

structure HasUniformExp3 (K : Set ℍ) (f a b c : ℍ × ℍ → ℂ) : Prop where
  remainder : (fun p => f p - (a p + b p * cuspS p.2 + c p * cuspS p.2 ^ 2))
    =O[𝓟 K ×ˢ atImInfty] fun p => ‖cuspS p.2‖ ^ 3
  bound_a : a =O[𝓟 K ×ˢ atImInfty] fun _ => (1 : ℝ)
  bound_b : b =O[𝓟 K ×ˢ atImInfty] fun _ => (1 : ℝ)
  bound_c : c =O[𝓟 K ×ˢ atImInfty] fun _ => (1 : ℝ)

namespace HasUniformExp3
variable {K : Set ℍ} {f g a b c a' b' c' : ℍ × ℍ → ℂ}

theorem congr_fun (hf : HasUniformExp3 K f a b c) (h : ∀ p, f p = g p) :
    HasUniformExp3 K g a b c :=
  ⟨hf.remainder.congr_left (fun p => by rw [h]), hf.bound_a, hf.bound_b, hf.bound_c⟩

theorem congr_coeff (hf : HasUniformExp3 K f a b c)
    (ha : ∀ p, a p = a' p) (hb : ∀ p, b p = b' p) (hc : ∀ p, c p = c' p) :
    HasUniformExp3 K f a' b' c' := by
  have ha' : a = a' := funext ha
  have hb' : b = b' := funext hb
  have hc' : c = c' := funext hc
  rwa [← ha', ← hb', ← hc']

theorem of_snd {F : ℍ → ℂ} {A B C : ℂ} (h : HasExp3 F A B C) :
    HasUniformExp3 K (fun p => F p.2) (fun _ => A) (fun _ => B) (fun _ => C) :=
  ⟨h.comp_tendsto tendsto_snd, isBigO_const_one ℝ A _,
    isBigO_const_one ℝ B _, isBigO_const_one ℝ C _⟩

theorem of_fst {F : ℍ → ℂ}
    (h : (fun p : ℍ × ℍ => F p.1) =O[𝓟 K ×ˢ atImInfty] fun _ => (1 : ℝ)) :
    HasUniformExp3 K (fun p => F p.1) (fun p => F p.1) (fun _ => 0) (fun _ => 0) :=
  ⟨(isBigO_zero _ _).congr_left (fun p => by ring), h,
    isBigO_const_one ℝ 0 _, isBigO_const_one ℝ 0 _⟩

theorem of_fst_continuous {F : ℍ → ℂ} (hK : IsCompact K) (hF : Continuous F) :
    HasUniformExp3 K (fun p => F p.1) (fun p => F p.1) (fun _ => 0) (fun _ => 0) := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  exact of_fst (isBigO_fst_of_bound hM)

theorem const (A : ℂ) : HasUniformExp3 K (fun _ => A) (fun _ => A)
    (fun _ => 0) (fun _ => 0) := of_snd (HasExp3.const A)

theorem quad_bound (ha : a =O[𝓟 K ×ˢ atImInfty] fun _ => (1 : ℝ))
    (hb : b =O[𝓟 K ×ˢ atImInfty] fun _ => (1 : ℝ))
    (hc : c =O[𝓟 K ×ˢ atImInfty] fun _ => (1 : ℝ)) :
    (fun p => a p + b p * cuspS p.2 + c p * cuspS p.2 ^ 2)
      =O[𝓟 K ×ˢ atImInfty] fun _ => (1 : ℝ) := by
  have hs := isBigO_snd_of_isBigO ((HasExp3.cuspS').isBigO_one) K
  have hs2 := isBigO_snd_of_isBigO ((HasExp3.cuspS'.pow).isBigO_one) K
  exact (ha.add ((hb.mul hs).congr_right fun _ => one_mul _)).add
    ((hc.mul hs2).congr_right fun _ => one_mul _)

theorem isBigO_one (hf : HasUniformExp3 K f a b c) :
    f =O[𝓟 K ×ˢ atImInfty] fun _ => (1 : ℝ) :=
  ((hf.remainder.trans (isBigO_snd_of_isBigO' isBigO_cube_one K)).add
    (quad_bound hf.bound_a hf.bound_b hf.bound_c)).congr_left fun p => by ring

theorem add (hf : HasUniformExp3 K f a b c) (hg : HasUniformExp3 K g a' b' c') :
    HasUniformExp3 K (fun p => f p + g p) (fun p => a p + a' p)
      (fun p => b p + b' p) (fun p => c p + c' p) :=
  ⟨(hf.remainder.add hg.remainder).congr_left (fun p => by ring),
    hf.bound_a.add hg.bound_a, hf.bound_b.add hg.bound_b, hf.bound_c.add hg.bound_c⟩

theorem sub (hf : HasUniformExp3 K f a b c) (hg : HasUniformExp3 K g a' b' c') :
    HasUniformExp3 K (fun p => f p - g p) (fun p => a p - a' p)
      (fun p => b p - b' p) (fun p => c p - c' p) :=
  ⟨(hf.remainder.sub hg.remainder).congr_left (fun p => by ring),
    hf.bound_a.sub hg.bound_a, hf.bound_b.sub hg.bound_b, hf.bound_c.sub hg.bound_c⟩

theorem const_mul (k : ℂ) (hf : HasUniformExp3 K f a b c) :
    HasUniformExp3 K (fun p => k * f p) (fun p => k * a p)
      (fun p => k * b p) (fun p => k * c p) :=
  ⟨(hf.remainder.const_mul_left k).congr_left (fun p => by ring),
    hf.bound_a.const_mul_left k, hf.bound_b.const_mul_left k, hf.bound_c.const_mul_left k⟩

theorem mul (hf : HasUniformExp3 K f a b c) (hg : HasUniformExp3 K g a' b' c') :
    HasUniformExp3 K (fun p => f p * g p) (fun p => a p * a' p)
      (fun p => a p * b' p + b p * a' p)
      (fun p => a p * c' p + b p * b' p + c p * a' p) := by
  have h1 := (hf.remainder.mul hg.isBigO_one).congr_right fun p => mul_one _
  have h2 := ((quad_bound hf.bound_a hf.bound_b hf.bound_c).mul hg.remainder).congr_right
    fun p => one_mul _
  have hbc := (hf.bound_b.mul hg.bound_c).add (hf.bound_c.mul hg.bound_b)
  have hcc := hf.bound_c.mul hg.bound_c
  have h3 : (fun p : ℍ × ℍ => (b p * c' p + c p * b' p) * cuspS p.2 ^ 3 +
      c p * c' p * cuspS p.2 ^ 4) =O[𝓟 K ×ˢ atImInfty] fun p => ‖cuspS p.2‖ ^ 3 :=
    (((hbc.mul (isBigO_snd_of_isBigO (isBigO_cuspS_pow le_rfl) K)).congr_right
    fun p => by norm_num).add
    ((hcc.mul (isBigO_snd_of_isBigO (isBigO_cuspS_pow (by norm_num : 3 ≤ 4)) K)).congr_right
      fun p => by norm_num))
  refine ⟨((h1.add h2).add h3).congr_left (fun p => by ring), ?_, ?_, ?_⟩
  · simpa using hf.bound_a.mul hg.bound_a
  · simpa using (hf.bound_a.mul hg.bound_b).add (hf.bound_b.mul hg.bound_a)
  · simpa using ((hf.bound_a.mul hg.bound_c).add
      (hf.bound_b.mul hg.bound_b)).add (hf.bound_c.mul hg.bound_a)

theorem fst_mul {F : ℍ → ℂ} (hK : IsCompact K) (hF : Continuous F)
    (hf : HasUniformExp3 K f a b c) :
    HasUniformExp3 K (fun p => F p.1 * f p) (fun p => F p.1 * a p)
      (fun p => F p.1 * b p) (fun p => F p.1 * c p) :=
  ((of_fst_continuous hK hF).mul hf).congr_coeff
    (fun p => rfl) (fun p => by ring) (fun p => by ring)

theorem pow (hf : HasUniformExp3 K f a b c) :
    HasUniformExp3 K (fun p => f p ^ 2) (fun p => a p ^ 2)
      (fun p => 2 * a p * b p) (fun p => 2 * a p * c p + b p ^ 2) :=
  (hf.mul hf).congr_fun (fun p => by ring)
    |>.congr_coeff (fun p => by ring) (fun p => by ring) (fun p => by ring)

theorem tendsto_const {A : ℂ}
    (hf : HasUniformExp3 K f (fun _ => A) b c) :
    Tendsto f (𝓟 K ×ˢ atImInfty) (𝓝 A) := by
  have hs : Tendsto (fun p : ℍ × ℍ => ‖cuspS p.2‖) (𝓟 K ×ˢ atImInfty) (𝓝 0) :=
    tendsto_norm_cuspS.comp tendsto_snd
  have hs3 : Tendsto (fun p : ℍ × ℍ => ‖cuspS p.2‖ ^ 3) (𝓟 K ×ˢ atImInfty) (𝓝 0) :=
    by simpa only [zero_pow (by norm_num : 3 ≠ 0)] using hs.pow 3
  have hS : (fun p : ℍ × ℍ => cuspS p.2) =O[𝓟 K ×ˢ atImInfty]
      fun p => ‖cuspS p.2‖ := (isBigO_refl _ _).norm_right
  have hS2 : (fun p : ℍ × ℍ => cuspS p.2 ^ 2) =O[𝓟 K ×ˢ atImInfty]
      fun p => ‖cuspS p.2‖ ^ 2 := by
    exact ((isBigO_refl (fun p : ℍ × ℍ => cuspS p.2 ^ 2)
      (𝓟 K ×ˢ atImInfty)).norm_right).congr_right (fun p => norm_pow _ _)
  have hr := hf.remainder.trans_tendsto hs3
  have hb := ((hf.bound_b.mul hS).congr_right fun p => one_mul _).trans_tendsto hs
  have hc := ((hf.bound_c.mul hS2).congr_right fun p => one_mul _).trans_tendsto
    (by simpa only [zero_pow (by norm_num : 2 ≠ 0)] using hs.pow 2)
  have h := hr.add (((tendsto_const_nhds (x := A)).add hb).add hc)
  simpa only [zero_add, add_zero] using h.congr (fun p => by ring)

/-- Inversion with a nonzero constant leading coefficient. -/
theorem inv_const {A : ℂ} (hf : HasUniformExp3 K f (fun _ => A) b c) (hA : A ≠ 0) :
    HasUniformExp3 K (fun p => (f p)⁻¹) (fun _ => A⁻¹)
      (fun p => -b p / A ^ 2) (fun p => (b p ^ 2 - A * c p) / A ^ 3) := by
  let B : ℍ × ℍ → ℂ := fun p => -b p / A ^ 2
  let C : ℍ × ℍ → ℂ := fun p => (b p ^ 2 - A * c p) / A ^ 3
  let R : ℍ × ℍ → ℂ := fun p => A⁻¹ + B p * cuspS p.2 + C p * cuspS p.2 ^ 2
  have hB : B =O[𝓟 K ×ˢ atImInfty] fun _ => (1 : ℝ) := by
    exact (hf.bound_b.neg_left.const_mul_left ((A ^ 2)⁻¹)).congr_left
      (fun p => by dsimp only [B]; rw [div_eq_mul_inv]; ring)
  have hC : C =O[𝓟 K ×ˢ atImInfty] fun _ => (1 : ℝ) := by
    exact ((((hf.bound_b.mul hf.bound_b).congr_right (fun p => one_mul _)).sub
      (hf.bound_c.const_mul_left A)).const_mul_left ((A ^ 3)⁻¹)).congr_left
        (fun p => by dsimp only [C]; rw [div_eq_mul_inv]; ring)
  have hR : HasUniformExp3 K R (fun _ => A⁻¹) B C :=
    ⟨(isBigO_zero _ _).congr_left (fun p => by simp only [R]; ring),
      isBigO_const_one ℝ _ _, hB, hC⟩
  have hfR : HasUniformExp3 K (fun p => f p * R p) (fun _ => 1)
      (fun _ => 0) (fun _ => 0) := by
    refine (hf.mul hR).congr_coeff (fun p => ?_) (fun p => ?_) (fun p => ?_)
    · field_simp
    · dsimp [B]; field_simp; ring
    · dsimp [B, C]; field_simp; ring
  have hne := hf.tendsto_const.eventually_ne hA
  have hinv := (hf.tendsto_const.inv₀ hA).isBigO_one ℝ
  have h := ((hinv.mul hfR.remainder).congr_right fun p => one_mul _).neg_left
  refine ⟨h.congr' ?_ (Eventually.of_forall fun p => rfl), hR.bound_a, hB, hC⟩
  filter_upwards [hne] with p hp
  dsimp only [R, B, C]
  field_simp
  ring

end HasUniformExp3
end E8Leech
