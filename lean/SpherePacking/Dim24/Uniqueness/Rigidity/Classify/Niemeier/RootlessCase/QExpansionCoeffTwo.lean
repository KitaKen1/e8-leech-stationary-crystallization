-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.RootlessCase.ThetaEquality
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.EvenUnimodular.ThetaSeries
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Set.Card

/-!
# The `q^2` coefficient of the theta series

This file bridges the modular-forms `qExpansion` framework (used in `ThetaEquality.lean`) to the
combinatorial shell-counting coefficients `thetaCoeff` defined in
`EvenUnimodular.ThetaSeries`.

## Main statements
* `NiemeierRootless.qExpansion_coeff_two_thetaSeries_eq_thetaCoeff`
-/


namespace SpherePacking.Dim24.Uniqueness.RigidityClassify
noncomputable section

open scoped RealInnerProductSpace BigOperators CongruenceSubgroup
open Complex UpperHalfPlane
open TopologicalSpace
open ModularFormClass

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace NiemeierRootless

variable {L : Submodule ℤ ℝ²⁴} [DiscreteTopology L] [IsZLattice ℝ L]

private lemma thetaCoeff_eq_ncard_thetaShell (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L] (n : ℕ) :
    thetaCoeff L n = Set.ncard (thetaShell L n) := by
  -- `thetaCoeff` is defined as the card of `finite_thetaShell.toFinset`.
  simpa [thetaCoeff, Set.ncard_eq_toFinset_card] using!
    (Set.ncard_eq_toFinset_card (thetaShell L n) (finite_thetaShell (L := L) n)).symm

private lemma ncard_shellSubtype_eq_thetaShell (L : Submodule ℤ ℝ²⁴) [DiscreteTopology L] (n : ℕ) :
    Set.ncard {z : L | ‖(z : ℝ²⁴)‖ ^ 2 = (2 : ℝ) * n} = Set.ncard (thetaShell L n) := by
  let f : L ↪ ℝ²⁴ := ⟨fun z : L => (z : ℝ²⁴), Subtype.val_injective⟩
  have himg :
      (f '' {z : L | ‖(z : ℝ²⁴)‖ ^ 2 = (2 : ℝ) * n}) = thetaShell L n := by
    ext v
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, hz⟩
    · rintro ⟨hvL, hv⟩
      refine ⟨⟨v, hvL⟩, ?_, rfl⟩
      simpa using! hv
  -- `f` is injective, so `ncard` is preserved under `image`.
  have h :=
    (Set.ncard_image_of_injective (s := {z : L | ‖(z : ℝ²⁴)‖ ^ 2 = (2 : ℝ) * n}) f.injective)
  simpa [himg] using! h.symm

/-! ### Main lemma: coefficient `2` equals the `n = 2` shell count -/

/-- The `q^2` coefficient of `thetaSeriesUHP L` equals the shell count `thetaCoeff L 2`. -/
public lemma qExpansion_coeff_two_thetaSeries_eq_thetaCoeff
    (hEven : EvenNormSq L)
    (f : ModularForm (Γ(1)) (12 : ℤ)) (hf : ∀ z : ℍ, f z = thetaSeriesUHP L z) :
    (qExpansion (1 : ℝ) f).coeff 2 = (thetaCoeff L 2 : ℂ) := by
  have hcoeff :=
    ModularFormClass.qExpansion_coeff_eq_intervalIntegral (f := f) (h := (1 : ℝ)) zero_lt_one_real
      one_mem_strictPeriods_Gamma1 2 zero_lt_one_real
  -- Normalize the coefficient formula at `n = 2` and `h = 1`.
  simp only [ofReal_one, one_mul, one_div] at hcoeff
  have hτpos : ∀ u : ℝ, 0 < (u + (Complex.I : ℂ)).im := im_add_I_pos
  have hrewrite :
      (fun u : ℝ =>
          (Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I) ^ (2 : ℕ))⁻¹ *
            f ⟨(u : ℂ) + Complex.I, hτpos u⟩) =
        fun u : ℝ =>
          ∑' z : L,
            (Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I) ^ (2 : ℕ))⁻¹ *
              thetaTerm L ((u : ℂ) + Complex.I) z := by
    funext u
    simp only [hf, thetaSeriesUHP, thetaSeries]
    exact Eq.symm tsum_mul_left
  have hswap :
      (∫ u : ℝ in (0 : ℝ)..1,
          ∑' z : L,
            (Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I) ^ (2 : ℕ))⁻¹ *
              thetaTerm L ((u : ℂ) + Complex.I) z) =
        ∑' z : L,
          ∫ u : ℝ in (0 : ℝ)..1,
            (Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I) ^ (2 : ℕ))⁻¹ *
              thetaTerm L ((u : ℂ) + Complex.I) z := by
    simpa [qParamPowInvMulThetaTerm_apply] using!
      (intervalIntegral_tsum_intervalIntegral_qParamPowInvMulThetaTerm_eq (L := L) (n := 2))
  have hcoeff' :
      (qExpansion (1 : ℝ) f).coeff 2 =
        ∑' z : L,
          ∫ u : ℝ in (0 : ℝ)..1,
            (Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I) ^ (2 : ℕ))⁻¹ *
              thetaTerm L ((u : ℂ) + Complex.I) z := by
    simpa [hrewrite, hswap] using! hcoeff
  -- Term-by-term integral evaluation.
  let S : Set L := {z : L | ‖(z : ℝ²⁴)‖ ^ 2 = (2 : ℝ) * (2 : ℕ)}
  have hSfinite : S.Finite := by
    let f' : L ↪ ℝ²⁴ := ⟨fun z : L => (z : ℝ²⁴), Subtype.val_injective⟩
    have hpre : S = f' ⁻¹' thetaShell L 2 := by
      ext z
      constructor
      · intro hz; exact ⟨z.property, hz⟩
      · rintro ⟨-, hz⟩; simpa using! hz
    simpa [hpre] using! (Set.Finite.preimage_embedding (f := f') (finite_thetaShell (L := L) 2))
  have hterm : ∀ z : L,
      (∫ u : ℝ in (0 : ℝ)..1,
          (Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I) ^ (2 : ℕ))⁻¹ *
            thetaTerm L ((u : ℂ) + Complex.I) z) =
        (if z ∈ S then (1 : ℂ) else 0) := by
    intro z
    rcases hEven (z : ℝ²⁴) z.property with ⟨m, hm⟩
    let k : ℤ := (m : ℤ) - 2
    let A : ℂ := (k : ℂ) * ((2 * (Real.pi : ℝ)) * Complex.I)
    have hk_cast : (k : ℂ) = (m : ℂ) - 2 := by
      -- `k = m - 2` in `ℤ`.
      simp [k]
    have hrewrite_z :
        (fun u : ℝ =>
            (Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I) ^ (2 : ℕ))⁻¹ *
              thetaTerm L ((u : ℂ) + Complex.I) z) =
          fun u : ℝ => Complex.exp (A * ((u : ℂ) + Complex.I)) := by
      simpa [A, hk_cast, mul_assoc] using!
        (qParamPowInvMulThetaTerm_fun_eq_exp (L := L) (n := 2) (z := z) (m := m) hm)
    -- Now integrate.
    by_cases hzS : z ∈ S
    · have hk0 : k = 0 := by
        have hm2 : m = 2 := by
          have : ‖(z : ℝ²⁴)‖ ^ 2 = (2 : ℝ) * (2 : ℕ) := hzS
          have : (2 : ℝ) * (m : ℝ) = (2 : ℝ) * (2 : ℕ) := by simpa [hm] using! this
          have : (m : ℝ) = (2 : ℕ) := by nlinarith
          exact_mod_cast this
        simp [k, hm2]
      have hint0 :
          (∫ u : ℝ in (0 : ℝ)..1, Complex.exp (A * (u : ℂ))) = (1 : ℂ) := by
        simp [A, hk0]
      have :
          (∫ u : ℝ in (0 : ℝ)..1, Complex.exp (A * ((u : ℂ) + Complex.I))) = (1 : ℂ) := by
        rw [exp_mul_add_I_split (A := A)]
        simp [A, hk0]
      simpa [hrewrite_z, hzS] using! this
    · have hk : k ≠ 0 := by
        intro hk0
        have hm2Z : (m : ℤ) = 2 := by
          have : (m : ℤ) - 2 = 0 := by simpa [k] using! hk0
          linarith
        have hm2 : m = 2 := by exact_mod_cast hm2Z
        apply hzS
        simpa [S, hm2] using! hm
      have :
          (∫ u : ℝ in (0 : ℝ)..1, Complex.exp (A * ((u : ℂ) + Complex.I))) = 0 := by
        simpa [A, mul_assoc] using!
          (intervalIntegral_cexp_two_pi_mul_I_int_mul_add_I_eq_zero_of_ne_zero (k := k) hk)
      simpa [hrewrite_z, hzS] using! this
  have htsum :
      (∑' z : L, (if z ∈ S then (1 : ℂ) else 0)) = (thetaCoeff L 2 : ℂ) := by
    -- Reduce to a finite sum over `S`.
    have htsum' :
        (∑' z : L, (if z ∈ S then (1 : ℂ) else 0)) =
          Finset.sum hSfinite.toFinset (fun z => if z ∈ S then (1 : ℂ) else 0) := by
      -- `tsum_eq_sum` applies since the summand vanishes off the finite set `S`.
      refine
        tsum_eq_sum (L := SummationFilter.unconditional (↥L)) (s := hSfinite.toFinset)
          (f := fun z : L => if z ∈ S then (1 : ℂ) else 0) ?_
      intro z hz
      have hzS : z ∉ S := by
        intro hzS
        apply hz
        simpa [Set.Finite.mem_toFinset] using! hzS
      simp [hzS]
    have hsum_val :
        (Finset.sum hSfinite.toFinset (fun z => if z ∈ S then (1 : ℂ) else 0)) =
          (hSfinite.toFinset.card : ℂ) := by
      have hsum1 :
          (Finset.sum hSfinite.toFinset (fun z => if z ∈ S then (1 : ℂ) else 0)) =
            Finset.sum hSfinite.toFinset (fun _ : L => (1 : ℂ)) := by
        refine Finset.sum_congr rfl ?_
        intro z hz
        have : z ∈ S := by simpa [Set.Finite.mem_toFinset] using! hz
        simp [this]
      have hsumConst :
          Finset.sum hSfinite.toFinset (fun _ : L => (1 : ℂ)) = (hSfinite.toFinset.card : ℂ) := by
        simp
      exact hsum1.trans hsumConst
    have hcard :
        (hSfinite.toFinset.card : ℂ) = (thetaCoeff L 2 : ℂ) := by
      have hS_ncard : Set.ncard S = Set.ncard (thetaShell L 2) := by
        -- `S` is the subtype version of the shell.
        simpa [S] using! (ncard_shellSubtype_eq_thetaShell (L := L) 2)
      have htheta : thetaCoeff L 2 = Set.ncard (thetaShell L 2) :=
        thetaCoeff_eq_ncard_thetaShell (L := L) 2
      have hcard_nat : hSfinite.toFinset.card = thetaCoeff L 2 := by
        have : Set.ncard S = hSfinite.toFinset.card := by
          simpa [Set.ncard_eq_toFinset_card] using! (Set.ncard_eq_toFinset_card S hSfinite)
        -- combine
        have : hSfinite.toFinset.card = Set.ncard S := by simpa using! this.symm
        -- replace `Set.ncard S` by `thetaCoeff L 2`.
        have : hSfinite.toFinset.card = Set.ncard (thetaShell L 2) := by
          simpa [hS_ncard] using! this
        simpa [htheta] using! this
      exact_mod_cast hcard_nat
    calc
      (∑' z : L, if z ∈ S then (1 : ℂ) else 0)
          = Finset.sum hSfinite.toFinset (fun z => if z ∈ S then (1 : ℂ) else 0) := htsum'
      _ = (hSfinite.toFinset.card : ℂ) := hsum_val
      _ = (thetaCoeff L 2 : ℂ) := hcard
  -- Put everything together.
  calc
    (qExpansion (1 : ℝ) f).coeff 2
        = ∑' z : L,
            ∫ u : ℝ in (0 : ℝ)..1,
              (Function.Periodic.qParam (1 : ℝ) ((u : ℂ) + Complex.I) ^ (2 : ℕ))⁻¹ *
                thetaTerm L ((u : ℂ) + Complex.I) z := hcoeff'
    _ = ∑' z : L, (if z ∈ S then (1 : ℂ) else 0) := by
          exact tsum_congr hterm
    _ = (thetaCoeff L 2 : ℂ) := htsum

end NiemeierRootless

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
