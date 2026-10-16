-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.EqCase24Facts
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Package
public import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Counting fibers for BS81 Lemma 16

Fix an equality-case code `C ⊆ Ω₂₄` and a vector `v ∈ L := span_ℤ (2 • C)` with `‖v‖ ^ 2 = 2`.
Then for `u ∈ C`, the value `⟪u, v⟫` lies in `{0, ±1/2, ±1}`. We introduce the fibers and the
associated counts used in the BS81 counting argument.

## Main definitions
* `fiber`
* `alpha`, `beta`, `gamma`

## Main statements
* `sum_inner_sq_eq_beta_gamma`
* `sum_inner_pow_four_eq_beta_gamma`
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16

noncomputable section

open scoped RealInnerProductSpace BigOperators

open Finset

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- The fiber `{u ∈ C | ⟪u, v⟫ = t}` as a `Finset`. -/
@[expose] public def fiber (C : Finset ℝ²⁴) (v : ℝ²⁴) (t : ℝ) : Finset ℝ²⁴ :=
  C.filter (fun u => (⟪u, v⟫ : ℝ) = t)

/-- The count `α(v) := |{u ∈ C | ⟪u, v⟫ = 0}|`. -/
@[expose] public def alpha (C : Finset ℝ²⁴) (v : ℝ²⁴) : ℕ :=
  (fiber C v (0 : ℝ)).card

/-- The count `β(v) := |{u ∈ C | ⟪u, v⟫ = 1/2}|`. -/
@[expose] public def beta (C : Finset ℝ²⁴) (v : ℝ²⁴) : ℕ :=
  (fiber C v (1 / 2 : ℝ)).card

/-- The count `γ(v) := |{u ∈ C | ⟪u, v⟫ = 1}|`. -/
@[expose] public def gamma (C : Finset ℝ²⁴) (v : ℝ²⁴) : ℕ :=
  (fiber C v (1 : ℝ)).card

lemma fiber_mem_iff (C : Finset ℝ²⁴) (v : ℝ²⁴) (t : ℝ) (u : ℝ²⁴) :
    u ∈ fiber C v t ↔ u ∈ C ∧ (⟪u, v⟫ : ℝ) = t := by
  simp [fiber]

attribute [grind =] fiber_mem_iff

lemma fiber_disjoint_of_ne (C : Finset ℝ²⁴) (v : ℝ²⁴) {t s : ℝ} (hts : t ≠ s) :
    Disjoint (fiber C v t) (fiber C v s) := by
  refine Finset.disjoint_left.2 ?_
  intro u hut hus
  grind

theorem fiber_neg_eq_of_antipodal
    (C : Set ℝ²⁴) (hEq : Uniqueness.BS81.EqCase24 C)
    (v : ℝ²⁴) (t : ℝ) :
    (fiber hEq.code.finite.toFinset v (-t)).card = (fiber hEq.code.finite.toFinset v t).card := by
  let Cfin : Finset ℝ²⁴ := hEq.code.finite.toFinset
  have hcard : (fiber Cfin v (-t)).card = (fiber Cfin v t).card := by
    refine Finset.card_bij (s := fiber Cfin v (-t)) (t := fiber Cfin v t)
      (i := fun u _ => -u) (hi := ?_) (i_inj := ?_) (i_surj := ?_)
    · intro u hu
      have huCfin : u ∈ Cfin :=
        (fiber_mem_iff (C := Cfin) (v := v) (t := -t) (u := u)).1 hu |>.1
      have huC : u ∈ C := by simpa [Cfin] using! huCfin
      have hnegCfin : -u ∈ Cfin := by
        have : -u ∈ C := neg_mem_of_eqCase24 (C := C) hEq u huC
        simpa [Cfin] using! this
      have hinner : (⟪u, v⟫ : ℝ) = -t :=
        (fiber_mem_iff (C := Cfin) (v := v) (t := -t) (u := u)).1 hu |>.2
      exact (fiber_mem_iff (C := Cfin) (v := v) (t := t) (u := -u)).2
        ⟨hnegCfin, by simp [inner_neg_left, hinner]⟩
    · intro u₁ _ u₂ _ h
      exact neg_injective h
    · intro b hb
      refine ⟨-b, ?_, by simp⟩
      have hbCfin : b ∈ Cfin :=
        (fiber_mem_iff (C := Cfin) (v := v) (t := t) (u := b)).1 hb |>.1
      have hbC : b ∈ C := by simpa [Cfin] using! hbCfin
      have hnegCfin : -b ∈ Cfin := by
        have : -b ∈ C := neg_mem_of_eqCase24 (C := C) hEq b hbC
        simpa [Cfin] using! this
      have hinner : (⟪b, v⟫ : ℝ) = t :=
        (fiber_mem_iff (C := Cfin) (v := v) (t := t) (u := b)).1 hb |>.2
      exact (fiber_mem_iff (C := Cfin) (v := v) (t := -t) (u := -b)).2
        ⟨hnegCfin, by simp [inner_neg_left, hinner]⟩
  simpa [Cfin] using! hcard

private lemma sum_eq_sum_fibers_of_hvals (Cfin : Finset ℝ²⁴) (v : ℝ²⁴) {β : Type _}
    [AddCommMonoid β] (f : ℝ²⁴ → β)
    (hvals : ∀ u ∈ Cfin,
      (⟪u, v⟫ : ℝ) = 0 ∨ (⟪u, v⟫ : ℝ) = (1 / 2 : ℝ) ∨ (⟪u, v⟫ : ℝ) = (-1 / 2 : ℝ) ∨
        (⟪u, v⟫ : ℝ) = (1 : ℝ) ∨ (⟪u, v⟫ : ℝ) = (-1 : ℝ)) :
    Cfin.sum f =
      (fiber Cfin v (0 : ℝ)).sum f +
        (fiber Cfin v (1 / 2 : ℝ)).sum f +
          (fiber Cfin v (-(1 / 2 : ℝ))).sum f +
            (fiber Cfin v (1 : ℝ)).sum f + (fiber Cfin v (-1 : ℝ)).sum f := by
  let s0 : Finset ℝ²⁴ := fiber Cfin v (0 : ℝ)
  let sHp : Finset ℝ²⁴ := fiber Cfin v (1 / 2 : ℝ)
  let sHn : Finset ℝ²⁴ := fiber Cfin v (-(1 / 2 : ℝ))
  let s1p : Finset ℝ²⁴ := fiber Cfin v (1 : ℝ)
  let s1n : Finset ℝ²⁴ := fiber Cfin v (-1 : ℝ)
  let s01 : Finset ℝ²⁴ := s0 ∪ sHp
  let s012 : Finset ℝ²⁴ := s01 ∪ sHn
  let s0123 : Finset ℝ²⁴ := s012 ∪ s1p
  let U : Finset ℝ²⁴ := s0123 ∪ s1n
  have hcover : Cfin = U := by
    ext u
    constructor
    · intro huCfin
      rcases hvals u huCfin with h0 | hhp | hhn | h1 | h1n'
      · have : u ∈ s0 := by simp [s0, fiber, huCfin, h0]
        simp [U, s0123, s012, s01, this]
      · have : u ∈ sHp := by simp [sHp, fiber, huCfin, hhp]
        simp [U, s0123, s012, s01, this]
      · have hhn' : (⟪u, v⟫ : ℝ) = (-(1 / 2 : ℝ)) := by nlinarith [hhn]
        have : u ∈ sHn := by simp [sHn, fiber, huCfin, hhn']
        simp [U, s0123, s012, s01, this]
      · have : u ∈ s1p := by simp [s1p, fiber, huCfin, h1]
        simp [U, s0123, s012, s01, this]
      · have : u ∈ s1n := by simp [s1n, fiber, huCfin, h1n']
        simp [U, s0123, s012, s01, this]
    · intro huU
      have hu_cases : u ∈ s0 ∨ u ∈ sHp ∨ u ∈ sHn ∨ u ∈ s1p ∨ u ∈ s1n := by
        simpa [U, s0123, s012, s01] using! huU
      rcases hu_cases with hu0 | huHp | huHn | hu1p | hu1n
      · exact (fiber_mem_iff (C := Cfin) (v := v) (t := (0 : ℝ)) (u := u)).1
          (by simpa [s0] using! hu0) |>.1
      · exact (fiber_mem_iff (C := Cfin) (v := v) (t := (1 / 2 : ℝ)) (u := u)).1
          (by simpa [sHp] using! huHp) |>.1
      · exact (fiber_mem_iff (C := Cfin) (v := v) (t := (-(1 / 2 : ℝ))) (u := u)).1
          (by simpa [sHn] using! huHn) |>.1
      · exact (fiber_mem_iff (C := Cfin) (v := v) (t := (1 : ℝ)) (u := u)).1
          (by simpa [s1p] using! hu1p) |>.1
      · exact (fiber_mem_iff (C := Cfin) (v := v) (t := (-1 : ℝ)) (u := u)).1
          (by simpa [s1n] using! hu1n) |>.1
  have hdis0Hp : Disjoint s0 sHp :=
    fiber_disjoint_of_ne (C := Cfin) (v := v) (t := (0 : ℝ)) (s := (1 / 2 : ℝ)) (by norm_num)
  have hdis0Hn : Disjoint s0 sHn :=
    fiber_disjoint_of_ne (C := Cfin) (v := v) (t := (0 : ℝ)) (s := (-(1 / 2 : ℝ))) (by norm_num)
  have hdisHpHn : Disjoint sHp sHn :=
    fiber_disjoint_of_ne (C := Cfin) (v := v) (t := (1 / 2 : ℝ)) (s := (-(1 / 2 : ℝ)))
      (by norm_num)
  have hdis01Hn : Disjoint s01 sHn := (Finset.disjoint_union_left).2 ⟨hdis0Hn, hdisHpHn⟩
  have hdis0_1p : Disjoint s0 s1p :=
    fiber_disjoint_of_ne (C := Cfin) (v := v) (t := (0 : ℝ)) (s := (1 : ℝ)) (by norm_num)
  have hdisHp_1p : Disjoint sHp s1p :=
    fiber_disjoint_of_ne (C := Cfin) (v := v) (t := (1 / 2 : ℝ)) (s := (1 : ℝ)) (by norm_num)
  have hdisHn_1p : Disjoint sHn s1p :=
    fiber_disjoint_of_ne (C := Cfin) (v := v) (t := (-(1 / 2 : ℝ))) (s := (1 : ℝ)) (by norm_num)
  have hdis012_1p : Disjoint s012 s1p :=
    (Finset.disjoint_union_left).2
      ⟨(Finset.disjoint_union_left).2 ⟨hdis0_1p, hdisHp_1p⟩, hdisHn_1p⟩
  have hdis0_1n : Disjoint s0 s1n :=
    fiber_disjoint_of_ne (C := Cfin) (v := v) (t := (0 : ℝ)) (s := (-1 : ℝ)) (by norm_num)
  have hdisHp_1n : Disjoint sHp s1n :=
    fiber_disjoint_of_ne (C := Cfin) (v := v) (t := (1 / 2 : ℝ)) (s := (-1 : ℝ)) (by norm_num)
  have hdisHn_1n : Disjoint sHn s1n :=
    fiber_disjoint_of_ne (C := Cfin) (v := v) (t := (-(1 / 2 : ℝ))) (s := (-1 : ℝ)) (by norm_num)
  have hdis1p_1n : Disjoint s1p s1n :=
    fiber_disjoint_of_ne (C := Cfin) (v := v) (t := (1 : ℝ)) (s := (-1 : ℝ)) (by norm_num)
  have hdis0123_1n : Disjoint s0123 s1n :=
    (Finset.disjoint_union_left).2
      ⟨(Finset.disjoint_union_left).2
        ⟨(Finset.disjoint_union_left).2 ⟨hdis0_1n, hdisHp_1n⟩, hdisHn_1n⟩, hdis1p_1n⟩
  have hsum01 : s01.sum f = s0.sum f + sHp.sum f := by
    simpa [s01] using! (Finset.sum_union hdis0Hp)
  have hsum012 : s012.sum f = s01.sum f + sHn.sum f := by
    simpa [s012] using! (Finset.sum_union hdis01Hn)
  have hsum0123 : s0123.sum f = s012.sum f + s1p.sum f := by
    simpa [s0123] using! (Finset.sum_union hdis012_1p)
  have hsumU : U.sum f = s0123.sum f + s1n.sum f := by
    simpa [U] using! (Finset.sum_union hdis0123_1n)
  have hsumCfin :
      Cfin.sum f = s0.sum f + sHp.sum f + sHn.sum f + s1p.sum f + s1n.sum f := by
    simp_all
  simpa [s0, sHp, sHn, s1p, s1n] using! hsumCfin

private lemma sum_fiber_inner_pow_eq_card_mul (Cfin : Finset ℝ²⁴) (v : ℝ²⁴) (t : ℝ) (n : ℕ) :
    (fiber Cfin v t).sum (fun u => (⟪u, v⟫ : ℝ) ^ n) = ((fiber Cfin v t).card : ℝ) * (t ^ n) := by
  calc
    (fiber Cfin v t).sum (fun u => (⟪u, v⟫ : ℝ) ^ n) =
        (fiber Cfin v t).sum (fun _ : ℝ²⁴ => t ^ n) := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          have hinner : (⟪u, v⟫ : ℝ) = t :=
            (fiber_mem_iff (C := Cfin) (v := v) (t := t) (u := u)).1 hu |>.2
          simp [hinner]
    _ = ((fiber Cfin v t).card : ℝ) * (t ^ n) := by simp

theorem totalCount_eq_alpha_beta_gamma
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (v : ℝ²⁴)
    (hvals : ∀ u ∈ h.code.finite.toFinset,
      (⟪u, v⟫ : ℝ) = 0 ∨ (⟪u, v⟫ : ℝ) = (1 / 2 : ℝ) ∨ (⟪u, v⟫ : ℝ) = (-1 / 2 : ℝ) ∨
        (⟪u, v⟫ : ℝ) = (1 : ℝ) ∨ (⟪u, v⟫ : ℝ) = (-1 : ℝ)) :
   (h.code.finite.toFinset.card) =
      alpha h.code.finite.toFinset v + 2 * beta h.code.finite.toFinset v +
        2 * gamma h.code.finite.toFinset v := by
  let hEq : Uniqueness.BS81.EqCase24 C :=
    Uniqueness.BS81.Thm14.EqCase24Pkg.toEqCase24 (C := C) h
  let Cfin : Finset ℝ²⁴ := h.code.finite.toFinset
  let s0 : Finset ℝ²⁴ := fiber Cfin v (0 : ℝ)
  let sHp : Finset ℝ²⁴ := fiber Cfin v (1 / 2 : ℝ)
  let sHn : Finset ℝ²⁴ := fiber Cfin v (-(1 / 2 : ℝ))
  let s1p : Finset ℝ²⁴ := fiber Cfin v (1 : ℝ)
  let s1n : Finset ℝ²⁴ := fiber Cfin v (-1 : ℝ)
  have hcardU :
      Cfin.card = s0.card + sHp.card + sHn.card + s1p.card + s1n.card := by
    have hsum :
        Cfin.sum (fun _ : ℝ²⁴ => (1 : ℕ)) =
          s0.sum (fun _ : ℝ²⁴ => (1 : ℕ)) + sHp.sum (fun _ : ℝ²⁴ => (1 : ℕ)) +
            sHn.sum (fun _ : ℝ²⁴ => (1 : ℕ)) + s1p.sum (fun _ : ℝ²⁴ => (1 : ℕ)) +
              s1n.sum (fun _ : ℝ²⁴ => (1 : ℕ)) :=
      sum_eq_sum_fibers_of_hvals Cfin v (fun x => 1) hvals
    have hsum' := hsum
    rw [(Finset.card_eq_sum_ones (s := Cfin)).symm] at hsum'
    rw [(Finset.card_eq_sum_ones (s := s0)).symm] at hsum'
    rw [(Finset.card_eq_sum_ones (s := sHp)).symm] at hsum'
    rw [(Finset.card_eq_sum_ones (s := sHn)).symm] at hsum'
    rw [(Finset.card_eq_sum_ones (s := s1p)).symm] at hsum'
    rw [(Finset.card_eq_sum_ones (s := s1n)).symm] at hsum'
    exact hsum'
  have hcardHn : sHn.card = sHp.card := by
    simpa [Cfin, sHp, sHn] using!
      fiber_neg_eq_of_antipodal (C := C) (hEq := hEq) (v := v) (t := (1 / 2 : ℝ))
  have hcard1n : s1n.card = s1p.card := by
    simpa [Cfin, s1p, s1n] using!
      fiber_neg_eq_of_antipodal (C := C) (hEq := hEq) (v := v) (t := (1 : ℝ))
  -- Substitute the symmetry relations into `hcardU`.
  have : Cfin.card = s0.card + 2 * sHp.card + 2 * s1p.card := by
    grind only
  -- Convert to the named counts `alpha`, `beta`, `gamma`.
  simpa [Cfin, alpha, beta, gamma, s0, sHp, s1p] using! this

/-- Under the value restriction `⟪u,v⟫ ∈ {0, ±1/2, ±1}`, the sum of squares `∑ ⟪u,v⟫^2` is
expressed in terms of `beta` and `gamma`. -/
public theorem sum_inner_sq_eq_beta_gamma
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (v : ℝ²⁴)
    (hvals : ∀ u ∈ h.code.finite.toFinset,
      (⟪u, v⟫ : ℝ) = 0 ∨ (⟪u, v⟫ : ℝ) = (1 / 2 : ℝ) ∨ (⟪u, v⟫ : ℝ) = (-1 / 2 : ℝ) ∨
        (⟪u, v⟫ : ℝ) = (1 : ℝ) ∨ (⟪u, v⟫ : ℝ) = (-1 : ℝ)) :
    (h.code.finite.toFinset.sum fun u => (⟪u, v⟫ : ℝ) ^ 2) =
      (beta h.code.finite.toFinset v : ℝ) * (1 / 2 : ℝ) +
        (gamma h.code.finite.toFinset v : ℝ) * 2 := by
  let hEq : Uniqueness.BS81.EqCase24 C :=
    Uniqueness.BS81.Thm14.EqCase24Pkg.toEqCase24 (C := C) h
  let Cfin : Finset ℝ²⁴ := h.code.finite.toFinset
  let f : ℝ²⁴ → ℝ := fun u => (⟪u, v⟫ : ℝ) ^ 2
  let s0 : Finset ℝ²⁴ := fiber Cfin v (0 : ℝ)
  let sHp : Finset ℝ²⁴ := fiber Cfin v (1 / 2 : ℝ)
  let sHn : Finset ℝ²⁴ := fiber Cfin v (-(1 / 2 : ℝ))
  let s1p : Finset ℝ²⁴ := fiber Cfin v (1 : ℝ)
  let s1n : Finset ℝ²⁴ := fiber Cfin v (-1 : ℝ)
  have hsumU :
      Cfin.sum f = s0.sum f + sHp.sum f + sHn.sum f + s1p.sum f + s1n.sum f := by
    simpa [s0, sHp, sHn, s1p, s1n] using!
      sum_eq_sum_fibers_of_hvals (Cfin := Cfin) (v := v) (f := f) hvals
  have hsum0 : s0.sum f = 0 := by
    simpa [s0, f] using!
      sum_fiber_inner_pow_eq_card_mul (Cfin := Cfin) (v := v) (t := (0 : ℝ)) (n := 2)
  have hsumHp : sHp.sum f = (sHp.card : ℝ) * (4 : ℝ)⁻¹ := by
    simpa [sHp, f, show ((2 : ℝ) ^ 2) = 4 by norm_num] using!
      sum_fiber_inner_pow_eq_card_mul (Cfin := Cfin) (v := v) (t := (1 / 2 : ℝ)) (n := 2)
  have hsumHn : sHn.sum f = (sHn.card : ℝ) * (4 : ℝ)⁻¹ := by
    simpa [sHn, f, show ((2 : ℝ) ^ 2) = 4 by norm_num] using!
      sum_fiber_inner_pow_eq_card_mul (Cfin := Cfin) (v := v) (t := (-(1 / 2 : ℝ))) (n := 2)
  have hsum1p : s1p.sum f = (s1p.card : ℝ) := by
    simpa [s1p, f] using!
      sum_fiber_inner_pow_eq_card_mul (Cfin := Cfin) (v := v) (t := (1 : ℝ)) (n := 2)
  have hsum1n : s1n.sum f = (s1n.card : ℝ) := by
    simpa [s1n, f, show ((-1 : ℝ) ^ 2) = (1 : ℝ) by norm_num] using!
      sum_fiber_inner_pow_eq_card_mul (Cfin := Cfin) (v := v) (t := (-1 : ℝ)) (n := 2)
  have hcardHn : sHn.card = sHp.card := by
    simpa [Cfin, sHp, sHn] using!
      fiber_neg_eq_of_antipodal (C := C) (hEq := hEq) (v := v) (t := (1 / 2 : ℝ))
  have hcard1n : s1n.card = s1p.card := by
    simpa [Cfin, s1p, s1n] using!
      fiber_neg_eq_of_antipodal (C := C) (hEq := hEq) (v := v) (t := (1 : ℝ))
  -- Combine.
  have :
      Cfin.sum f = (sHp.card : ℝ) * (1 / 2 : ℝ) + (s1p.card : ℝ) * 2 := by
    -- Rewrite the sum using the fiber decomposition, then use antipodality on the negative fibers.
    grind only
  simpa [Cfin, f, beta, gamma, sHp, s1p] using! this

/-- Under the value restriction `⟪u,v⟫ ∈ {0, ±1/2, ±1}`, the sum of fourth powers `∑ ⟪u,v⟫^4` is
expressed in terms of `beta` and `gamma`. -/
public theorem sum_inner_pow_four_eq_beta_gamma
    (C : Set ℝ²⁴) (h : Uniqueness.BS81.Thm14.EqCase24Pkg C)
    (v : ℝ²⁴)
    (hvals : ∀ u ∈ h.code.finite.toFinset,
      (⟪u, v⟫ : ℝ) = 0 ∨ (⟪u, v⟫ : ℝ) = (1 / 2 : ℝ) ∨ (⟪u, v⟫ : ℝ) = (-1 / 2 : ℝ) ∨
        (⟪u, v⟫ : ℝ) = (1 : ℝ) ∨ (⟪u, v⟫ : ℝ) = (-1 : ℝ)) :
    (h.code.finite.toFinset.sum fun u => (⟪u, v⟫ : ℝ) ^ 4) =
      (beta h.code.finite.toFinset v : ℝ) * (1 / 8 : ℝ) +
        (gamma h.code.finite.toFinset v : ℝ) * 2 := by
  let hEq : Uniqueness.BS81.EqCase24 C :=
    Uniqueness.BS81.Thm14.EqCase24Pkg.toEqCase24 (C := C) h
  let Cfin : Finset ℝ²⁴ := h.code.finite.toFinset
  let f : ℝ²⁴ → ℝ := fun u => (⟪u, v⟫ : ℝ) ^ 4
  let s0 : Finset ℝ²⁴ := fiber Cfin v (0 : ℝ)
  let sHp : Finset ℝ²⁴ := fiber Cfin v (1 / 2 : ℝ)
  let sHn : Finset ℝ²⁴ := fiber Cfin v (-(1 / 2 : ℝ))
  let s1p : Finset ℝ²⁴ := fiber Cfin v (1 : ℝ)
  let s1n : Finset ℝ²⁴ := fiber Cfin v (-1 : ℝ)
  have hsumU :
      Cfin.sum f = s0.sum f + sHp.sum f + sHn.sum f + s1p.sum f + s1n.sum f := by
    simpa [s0, sHp, sHn, s1p, s1n] using!
      sum_eq_sum_fibers_of_hvals (Cfin := Cfin) (v := v) (f := f) hvals
  have hsum0 : s0.sum f = 0 := by
    simpa [s0, f] using!
      sum_fiber_inner_pow_eq_card_mul (Cfin := Cfin) (v := v) (t := (0 : ℝ)) (n := 4)
  have hsumHp : sHp.sum f = (sHp.card : ℝ) * (16 : ℝ)⁻¹ := by
    simpa [sHp, f, show ((2 : ℝ) ^ 4) = 16 by norm_num] using!
      sum_fiber_inner_pow_eq_card_mul (Cfin := Cfin) (v := v) (t := (1 / 2 : ℝ)) (n := 4)
  have hsumHn : sHn.sum f = (sHn.card : ℝ) * (16 : ℝ)⁻¹ := by
    simpa [sHn, f, show ((-(2 : ℝ)⁻¹) ^ 4) = (16 : ℝ)⁻¹ by norm_num] using!
      sum_fiber_inner_pow_eq_card_mul (Cfin := Cfin) (v := v) (t := (-(1 / 2 : ℝ))) (n := 4)
  have hsum1p : s1p.sum f = (s1p.card : ℝ) := by
    simpa [s1p, f] using!
      sum_fiber_inner_pow_eq_card_mul (Cfin := Cfin) (v := v) (t := (1 : ℝ)) (n := 4)
  have hsum1n : s1n.sum f = (s1n.card : ℝ) := by
    simpa [s1n, f, show ((-1 : ℝ) ^ 4) = (1 : ℝ) by norm_num] using!
      sum_fiber_inner_pow_eq_card_mul (Cfin := Cfin) (v := v) (t := (-1 : ℝ)) (n := 4)
  have hcardHn : sHn.card = sHp.card := by
    simpa [Cfin, sHp, sHn] using!
      fiber_neg_eq_of_antipodal (C := C) (hEq := hEq) (v := v) (t := (1 / 2 : ℝ))
  have hcard1n : s1n.card = s1p.card := by
    simpa [Cfin, s1p, s1n] using!
      fiber_neg_eq_of_antipodal (C := C) (hEq := hEq) (v := v) (t := (1 : ℝ))
  have :
      Cfin.sum f = (sHp.card : ℝ) * (1 / 8 : ℝ) + (s1p.card : ℝ) * 2 := by
    grind only
  simpa [Cfin, f, beta, gamma, sHp, s1p] using! this

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16
