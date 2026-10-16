-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Cardinality bounds for isotropic subgroups

Let `G` be a finite abelian group and `pair : G →+ G →+ AddCircle (1 : ℝ)` a bilinear pairing
which is nondegenerate in the left variable. If `H ≤ G` is isotropic for `pair`
(i.e. `pair a b = 0` for all `a, b ∈ H`), then `|H|^2 ≤ |G|`.

The proof is the standard character-theoretic argument: each `a ∈ H` defines a character
`b ↦ exp(2π i · pair a b)` that is trivial on `H`, hence factors through `G ⧸ H`. Injectivity of
`a ↦ χ_a` yields `|H| ≤ |G ⧸ H|`, and then `|G| = |H| · |G ⧸ H|`.

## Main statements
* `FinitePairing.card_isotropic_sq_le`
-/


namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

noncomputable section

local notation "𝕋" => AddCircle (1 : ℝ)

namespace FinitePairing

variable {G : Type*} [AddCommGroup G] [Fintype G]

namespace AddCharCircle

noncomputable instance instFintype [Finite G] : Fintype (AddChar G Circle) :=
  Fintype.ofEquiv (AddChar G ℂ) (AddChar.circleEquivComplex (α := G)).symm

@[simp]
lemma card_eq : Fintype.card (AddChar G Circle) = Fintype.card G := by
  -- reduce to the complex case, where `AddChar.card_eq` is already proved in mathlib
  simpa using!
    (Fintype.card_congr (AddChar.circleEquivComplex (α := G))).trans (AddChar.card_eq (α := G))

end AddCharCircle

-- We frequently use `Fintype.card` on subgroups and quotients of a finite group; provide
-- noncomputable `Fintype` instances without requiring decidable membership predicates.
instance instNormal (H : AddSubgroup G) : H.Normal := inferInstance

noncomputable instance instFiniteQuotient {G : Type*} [AddCommGroup G] [Finite G]
    (H : AddSubgroup G) :
    Finite (G ⧸ H) :=
  Finite.of_surjective (QuotientAddGroup.mk' H) (QuotientAddGroup.mk'_surjective H)

noncomputable instance instFintypeQuotient (H : AddSubgroup G) : Fintype (G ⧸ H) :=
  Fintype.ofFinite (G ⧸ H)

/-- A subgroup of a finite additive commutative group is finite. -/
public noncomputable instance instFiniteSubgroup {G : Type*} [AddCommGroup G] [Finite G]
    (H : AddSubgroup G) :
    Finite (↥H) :=
  Finite.of_injective (fun x : (↥H) => (x : G)) Subtype.val_injective

/-- A subgroup of a finite additive commutative group inherits a `Fintype` structure. -/
public noncomputable instance instFintypeSubgroup (H : AddSubgroup G) : Fintype (↥H) :=
  Fintype.ofFinite (↥H)

noncomputable instance instFintypeCharsTrivial (H : AddSubgroup G) :
    Fintype { χ : AddChar G Circle // ∀ h : H, χ h = 1 } :=
  Fintype.ofFinite _

lemma toCircle_injective : Function.Injective (AddCircle.toCircle : 𝕋 → Circle) :=
  AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero

lemma toCircle_eq_one_iff (x : 𝕋) : AddCircle.toCircle x = 1 ↔ x = 0 := by
  constructor
  · intro hx
    apply toCircle_injective
    simpa [AddCircle.toCircle_zero] using! hx
  · rintro rfl
    simp [AddCircle.toCircle_zero]

variable (pair : G →+ G →+ 𝕋)

omit [Fintype G] in
/-- The circle-valued additive character `b ↦ toCircle (pair a b)`. -/
noncomputable def circleChar (a : G) : AddChar G Circle :=
  AddCircle.toCircle_addChar.compAddMonoidHom (pair a)

omit [Fintype G] in
@[simp]
lemma circleChar_apply (a b : G) : circleChar pair a b = AddCircle.toCircle (pair a b) := rfl

omit [Fintype G] in
theorem circleChar_injective_of_nondegenerate_left
    (hnondeg : ∀ a : G, (∀ b : G, pair a b = 0) → a = 0) :
    Function.Injective (circleChar pair) := by
  intro a₁ a₂ ha
  have hpair : ∀ b : G, pair a₁ b = pair a₂ b := by
    intro b
    have :
        AddCircle.toCircle (pair a₁ b) = AddCircle.toCircle (pair a₂ b) := by
      simpa [circleChar_apply] using! congrArg (fun χ : AddChar G Circle => χ b) ha
    exact toCircle_injective this
  have hsub : ∀ b : G, pair (a₁ - a₂) b = 0 := by
    intro b
    have hmap :
        pair (a₁ - a₂) b = pair a₁ b - pair a₂ b :=
      congrArg (fun f : G →+ 𝕋 => f b) (pair.map_sub a₁ a₂)
    -- `pair a₁ b = pair a₂ b`
    simp [hpair b]
  have : a₁ - a₂ = 0 := hnondeg (a := a₁ - a₂) hsub
  exact sub_eq_zero.mp this

/-- Characters on `G ⧸ H` correspond to characters on `G` that are trivial on `H`. -/
noncomputable def charsOnQuotientEquiv (H : AddSubgroup G) :
    AddChar (G ⧸ H) Circle ≃ { χ : AddChar G Circle // ∀ h : H, χ h = 1 } := by
  let π : G →+ G ⧸ H := QuotientAddGroup.mk' H
  refine
    { toFun := fun ψ =>
        ⟨ψ.compAddMonoidHom π, by
          intro h
          have : π h.1 = 0 := by
            simp [π, QuotientAddGroup.eq_zero_iff, h.2]
          simp [AddChar.compAddMonoidHom_apply, this]⟩
      invFun := fun χ =>
        { toFun := fun q =>
            Quotient.liftOn q (fun g : G => (χ.1 g))
              (by
                intro a b hab
                have hab' : (-a + b) ∈ H := (QuotientAddGroup.leftRel_apply (s := H)).1 hab
                have htriv : χ.1 (-a + b) = 1 := by
                  simpa using! χ.2 ⟨-a + b, hab'⟩
                have hb : b = a + (-a + b) := by abel
                -- `χ b = χ (a + (-a + b)) = χ a * χ (-a + b) = χ a`
                have hba : χ.1 b = χ.1 a := by
                  -- rewrite `b` and use the character law
                  rw [hb]
                  calc
                    χ.1 (a + (-a + b)) = χ.1 a * χ.1 (-a + b) := by
                      simpa using! (χ.1.map_add_eq_mul a (-a + b))
                    _ = χ.1 a := by simp [htriv]
                exact hba.symm)
          map_zero_eq_one' := by
            -- rewrite `0` as `mk 0` and unfold the lift
            rw [← QuotientAddGroup.mk_zero (N := H)]
            change χ.1 0 = 1
            exact χ.1.map_zero_eq_one
          map_add_eq_mul' := by
            intro x y
            refine Quotient.inductionOn₂ x y ?_
            intro a b
            -- reduce to representatives using `QuotientAddGroup.mk_add`
            have hmk :
                ((a : G ⧸ H) + (b : G ⧸ H) : G ⧸ H) = ((a + b : G) : G ⧸ H) := by
              simp [QuotientAddGroup.mk_add]
            rw [hmk]
            change χ.1 (a + b) = χ.1 a * χ.1 b
            exact χ.1.map_add_eq_mul a b }
      left_inv := by
        intro ψ
        ext q
        refine Quotient.inductionOn q ?_
        intro g
        rfl
      right_inv := by
        tauto }

theorem card_chars_trivial_on (H : AddSubgroup G) :
    Fintype.card { χ : AddChar G Circle // ∀ h : H, χ h = 1 } = Fintype.card (G ⧸ H) := by
  -- Identify characters trivial on `H` with characters of `G ⧸ H`, then use `AddChar.card_eq`.
  simpa using!
    (Fintype.card_congr (charsOnQuotientEquiv (G := G) H).symm).trans
      (AddCharCircle.card_eq (G := G ⧸ H))

/-- If `pair` is left-nondegenerate and `H` is isotropic, then `|H|^2 ≤ |G|`. -/
public theorem card_isotropic_sq_le
    (hnondeg : ∀ a : G, (∀ b : G, pair a b = 0) → a = 0)
    (H : AddSubgroup G)
    (hIso : ∀ a ∈ H, ∀ b ∈ H, pair a b = 0) :
    (Fintype.card H) ^ 2 ≤ Fintype.card G := by
  -- Map `H` into the characters of `G` that are trivial on `H`.
  let f : H → { χ : AddChar G Circle // ∀ h : H, χ h = 1 } :=
    fun a =>
      ⟨circleChar pair a.1, by
        intro h
        have : pair a.1 h.1 = 0 := hIso a.1 a.2 h.1 h.2
        simp [circleChar_apply, this, AddCircle.toCircle_zero]⟩
  have hf : Function.Injective f := by
    intro a₁ a₂ ha
    apply Subtype.ext
    have hinj : Function.Injective (circleChar pair) :=
      circleChar_injective_of_nondegenerate_left (pair := pair) hnondeg
    exact hinj (congrArg Subtype.val ha)
  have hcard_le :
      Fintype.card H ≤ Fintype.card (G ⧸ H) := by
    calc
      Fintype.card H ≤ Fintype.card { χ : AddChar G Circle // ∀ h : H, χ h = 1 } :=
        Fintype.card_le_of_injective f hf
      _ = Fintype.card (G ⧸ H) := (card_chars_trivial_on (G := G) H)
  have hmul :
      Fintype.card H * Fintype.card (G ⧸ H) = Fintype.card G := by
    -- `Nat.card` version of Lagrange + `Nat.card_eq_fintype_card`
    simpa [AddSubgroup.index, Nat.card_eq_fintype_card] using! (H.card_mul_index : _)
  -- multiply the inequality `|H| ≤ |G ⧸ H|` by `|H|` and rewrite
  have hmul_le :
      Fintype.card H * Fintype.card H ≤ Fintype.card H * Fintype.card (G ⧸ H) :=
    Nat.mul_le_mul_left (Fintype.card H) hcard_le
  simpa [pow_two, Nat.mul_assoc, hmul] using! hmul_le

end FinitePairing

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
