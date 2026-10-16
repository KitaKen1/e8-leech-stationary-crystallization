-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.RootlessCase.MinShell
public import SpherePacking.Dim24.LeechLattice.Defs

/-!
# Leech lattice: generators in the minimal shell

We record that all generator rows except the first lie in the minimal shell.
The exceptional row has squared norm `8` in the current normalization.

## Main statements
* `leechGeneratorRows_mem_minShell_of_ne_zero`
* `spanZ_minShell_eq_leechLattice`
-/


namespace SpherePacking.Dim24.Uniqueness.RigidityClassify
noncomputable section

open scoped BigOperators RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace NiemeierRootless

private lemma norm_inv_sqrt8 : ‖((Real.sqrt 8)⁻¹ : ℝ)‖ = ((Real.sqrt 8)⁻¹ : ℝ) := by
  simp [Real.norm_eq_abs]

lemma leechGeneratorMatrixInt_row_sq_sum (i : Fin 24) :
    (∑ k : Fin 24, (leechGeneratorMatrixInt i k) ^ (2 : ℕ)) =
      (if i = 0 then (64 : ℤ) else (32 : ℤ)) := by
  fin_cases i <;> decide

lemma norm_sq_leechGeneratorRowsUnscaled (i : Fin 24) :
    ‖leechGeneratorRowsUnscaled i‖ ^ 2 = (if i = 0 then (64 : ℝ) else (32 : ℝ)) := by
  -- Expand the Euclidean norm to a sum of squares of coordinates.
  have h1 :
      ‖leechGeneratorRowsUnscaled i‖ ^ 2 =
        ∑ k : Fin 24, ((leechGeneratorRowsUnscaled i) k) ^ (2 : ℕ) := by
    -- `‖x‖^2 = ∑ ‖x k‖^2 = ∑ (x k)^2` for `ℝ`.
    simpa [pow_two, Real.norm_eq_abs, sq_abs] using!
      (EuclideanSpace.norm_sq_eq (leechGeneratorRowsUnscaled i))
  -- Rewrite coordinates and use the explicit integer computation.
  have h2 :
      (∑ k : Fin 24, ((leechGeneratorRowsUnscaled i) k) ^ (2 : ℕ)) =
        (∑ k : Fin 24, (leechGeneratorMatrixInt i k : ℝ) ^ (2 : ℕ)) := by
    simp [leechGeneratorRowsUnscaled]
  have h3 :
      (∑ k : Fin 24, (leechGeneratorMatrixInt i k : ℝ) ^ (2 : ℕ)) =
        ((∑ k : Fin 24, (leechGeneratorMatrixInt i k) ^ (2 : ℕ)) : ℝ) := by
    -- push the cast through the sum
    simp
  have h4 :
      ((∑ k : Fin 24, (leechGeneratorMatrixInt i k) ^ (2 : ℕ)) : ℝ) =
        (if i = 0 then (64 : ℝ) else (32 : ℝ)) := by
    simpa using! congrArg (fun z : ℤ => (z : ℝ)) (leechGeneratorMatrixInt_row_sq_sum i)
  -- assemble
  calc
    ‖leechGeneratorRowsUnscaled i‖ ^ 2
        = ∑ k : Fin 24, ((leechGeneratorRowsUnscaled i) k) ^ (2 : ℕ) := h1
    _ = ∑ k : Fin 24, (leechGeneratorMatrixInt i k : ℝ) ^ (2 : ℕ) := h2
    _ = ((∑ k : Fin 24, (leechGeneratorMatrixInt i k) ^ (2 : ℕ)) : ℝ) := h3
    _ = (if i = 0 then (64 : ℝ) else (32 : ℝ)) := h4

lemma norm_sq_leechGeneratorRows (i : Fin 24) :
    ‖leechGeneratorRows i‖ ^ 2 = (if i = 0 then (8 : ℝ) else (4 : ℝ)) := by
  have hun :
      ‖leechGeneratorRowsUnscaled i‖ ^ 2 = (if i = 0 then (64 : ℝ) else (32 : ℝ)) :=
    norm_sq_leechGeneratorRowsUnscaled i
  have hnorm_smul :
      ‖leechGeneratorRows i‖ ^ 2 =
        (((Real.sqrt 8)⁻¹ : ℝ) ^ (2 : ℕ)) * (‖leechGeneratorRowsUnscaled i‖ ^ 2) := by
    -- use `‖a • v‖ = ‖a‖ * ‖v‖` and `‖a‖ = |a| = a` since `a > 0`
    have habs : ‖((Real.sqrt 8)⁻¹ : ℝ)‖ = ((Real.sqrt 8)⁻¹ : ℝ) := norm_inv_sqrt8
    -- now expand
    simp [leechGeneratorRows, norm_smul, pow_two, mul_assoc, mul_left_comm, mul_comm, habs]
  -- evaluate in the two cases `i = 0` and `i ≠ 0`
  by_cases hi : i = 0
  · subst hi
    -- unscaled norm^2 is `64`, so scaled norm^2 is `64/8 = 8`
    have hun0 : ‖leechGeneratorRowsUnscaled (0 : Fin 24)‖ ^ 2 = (64 : ℝ) := by
      simpa using! hun
    have h0 : ‖leechGeneratorRows (0 : Fin 24)‖ ^ 2 = (8 : ℝ) := by
      calc
        ‖leechGeneratorRows (0 : Fin 24)‖ ^ 2
            =
          (((Real.sqrt 8)⁻¹ : ℝ) ^ (2 : ℕ)) * (‖leechGeneratorRowsUnscaled (0 : Fin 24)‖ ^ 2) :=
            hnorm_smul
        _ = (8 : ℝ)⁻¹ * (64 : ℝ) := by simp [hun0]
        _ = (8 : ℝ) := by norm_num
    simpa using! h0
  · have hun' : ‖leechGeneratorRowsUnscaled i‖ ^ 2 = (32 : ℝ) := by
        simpa [hi] using! hun
    have hne0 : ‖leechGeneratorRows i‖ ^ 2 = (4 : ℝ) := by
      calc
        ‖leechGeneratorRows i‖ ^ 2
            =
          (((Real.sqrt 8)⁻¹ : ℝ) ^ (2 : ℕ)) * (‖leechGeneratorRowsUnscaled i‖ ^ 2) :=
            hnorm_smul
        _ = (8 : ℝ)⁻¹ * (32 : ℝ) := by simp [hun']
        _ = (4 : ℝ) := by norm_num
    simpa [hi] using! hne0

private lemma leechGeneratorRows_mem_leechLattice (i : Fin 24) :
    leechGeneratorRows i ∈ (LeechLattice : Set ℝ²⁴) := by
  change leechGeneratorRows i ∈ Submodule.span ℤ (Set.range leechGeneratorRows)
  exact Submodule.subset_span ⟨i, rfl⟩

/-- Every generator row except the first lies in the minimal shell of the Leech lattice. -/
public lemma leechGeneratorRows_mem_minShell_of_ne_zero {i : Fin 24} (hi : i ≠ 0) :
    leechGeneratorRows i ∈ minShell LeechLattice := by
  refine ⟨?_, ?_⟩
  · exact leechGeneratorRows_mem_leechLattice i
  · -- and have squared norm `4 = 2*2`
    have h4 : ‖leechGeneratorRows i‖ ^ 2 = (4 : ℝ) := by
      simpa [hi] using! (norm_sq_leechGeneratorRows i)
    -- `thetaShell` expects `‖v‖^2 = 2 * 2`.
    simpa [minShell, thetaShell, h4] using! (by norm_num : (4 : ℝ) = (2 : ℝ) * (2 : ℕ))

lemma leechGeneratorMatrixInt_row0_sub_row1_sq_sum :
    (∑ k : Fin 24,
        (leechGeneratorMatrixInt (⟨0, by decide⟩ : Fin 24) k -
            leechGeneratorMatrixInt (⟨1, by decide⟩ : Fin 24) k) ^ (2 : ℕ)) = (32 : ℤ) := by
  decide

lemma norm_sq_leechGeneratorRowsUnscaled_sub_row0_row1 :
    ‖leechGeneratorRowsUnscaled (⟨0, by decide⟩ : Fin 24) -
        leechGeneratorRowsUnscaled (⟨1, by decide⟩ : Fin 24)‖ ^ 2 = (32 : ℝ) := by
  have h1 :
      ‖leechGeneratorRowsUnscaled (⟨0, by decide⟩ : Fin 24) -
            leechGeneratorRowsUnscaled (⟨1, by decide⟩ : Fin 24)‖ ^ 2 =
        ∑ k : Fin 24,
          ((leechGeneratorRowsUnscaled (⟨0, by decide⟩ : Fin 24) -
                leechGeneratorRowsUnscaled (⟨1, by decide⟩ : Fin 24)) k) ^ (2 : ℕ) := by
    simpa [pow_two, Real.norm_eq_abs, sq_abs] using!
      (EuclideanSpace.norm_sq_eq
        (leechGeneratorRowsUnscaled (⟨0, by decide⟩ : Fin 24) -
          leechGeneratorRowsUnscaled (⟨1, by decide⟩ : Fin 24)))
  have h2 :
      (∑ k : Fin 24,
          ((leechGeneratorRowsUnscaled (⟨0, by decide⟩ : Fin 24) -
                leechGeneratorRowsUnscaled (⟨1, by decide⟩ : Fin 24)) k) ^ (2 : ℕ)) =
        (∑ k : Fin 24,
            (leechGeneratorMatrixInt (⟨0, by decide⟩ : Fin 24) k -
                leechGeneratorMatrixInt (⟨1, by decide⟩ : Fin 24) k : ℝ) ^ (2 : ℕ)) := by
    simp [leechGeneratorRowsUnscaled, sub_eq_add_neg]
  have h3 :
      (∑ k : Fin 24,
          (leechGeneratorMatrixInt (⟨0, by decide⟩ : Fin 24) k -
                leechGeneratorMatrixInt (⟨1, by decide⟩ : Fin 24) k : ℝ) ^ (2 : ℕ)) =
        ((∑ k : Fin 24,
            (leechGeneratorMatrixInt (⟨0, by decide⟩ : Fin 24) k -
                leechGeneratorMatrixInt (⟨1, by decide⟩ : Fin 24) k) ^ (2 : ℕ)) : ℝ) := by
    simp
  have h4 :
      ((∑ k : Fin 24,
            (leechGeneratorMatrixInt (⟨0, by decide⟩ : Fin 24) k -
                leechGeneratorMatrixInt (⟨1, by decide⟩ : Fin 24) k) ^ (2 : ℕ)) : ℝ) =
        (32 : ℝ) := by
    simpa using! congrArg (fun z : ℤ => (z : ℝ)) leechGeneratorMatrixInt_row0_sub_row1_sq_sum
  calc
    ‖leechGeneratorRowsUnscaled (⟨0, by decide⟩ : Fin 24) -
          leechGeneratorRowsUnscaled (⟨1, by decide⟩ : Fin 24)‖ ^ 2
        =
      ∑ k : Fin 24,
        ((leechGeneratorRowsUnscaled (⟨0, by decide⟩ : Fin 24) -
              leechGeneratorRowsUnscaled (⟨1, by decide⟩ : Fin 24)) k) ^ (2 : ℕ) := h1
    _ =
      ∑ k : Fin 24,
        (leechGeneratorMatrixInt (⟨0, by decide⟩ : Fin 24) k -
              leechGeneratorMatrixInt (⟨1, by decide⟩ : Fin 24) k : ℝ) ^ (2 : ℕ) := h2
    _ =
      ((∑ k : Fin 24,
          (leechGeneratorMatrixInt (⟨0, by decide⟩ : Fin 24) k -
              leechGeneratorMatrixInt (⟨1, by decide⟩ : Fin 24) k) ^ (2 : ℕ)) : ℝ) := h3
    _ = (32 : ℝ) := h4

lemma norm_sq_leechGeneratorRows_sub_row0_row1 :
    ‖leechGeneratorRows (⟨0, by decide⟩ : Fin 24) -
        leechGeneratorRows (⟨1, by decide⟩ : Fin 24)‖ ^ 2 = (4 : ℝ) := by
  have habs : ‖((Real.sqrt 8)⁻¹ : ℝ)‖ = ((Real.sqrt 8)⁻¹ : ℝ) := norm_inv_sqrt8
  have hun :
      ‖leechGeneratorRowsUnscaled (⟨0, by decide⟩ : Fin 24) -
            leechGeneratorRowsUnscaled (⟨1, by decide⟩ : Fin 24)‖ ^ 2 = (32 : ℝ) :=
    norm_sq_leechGeneratorRowsUnscaled_sub_row0_row1
  have hdiff :
      leechGeneratorRows (⟨0, by decide⟩ : Fin 24) -
            leechGeneratorRows (⟨1, by decide⟩ : Fin 24) =
          ((Real.sqrt 8)⁻¹ : ℝ) •
            (leechGeneratorRowsUnscaled (⟨0, by decide⟩ : Fin 24) -
              leechGeneratorRowsUnscaled (⟨1, by decide⟩ : Fin 24)) := by
    simp [leechGeneratorRows, sub_eq_add_neg, smul_add, smul_neg]
  have hnorm :
      ‖leechGeneratorRows (⟨0, by decide⟩ : Fin 24) -
            leechGeneratorRows (⟨1, by decide⟩ : Fin 24)‖ ^ 2 =
        (‖((Real.sqrt 8)⁻¹ : ℝ)‖ ^ (2 : ℕ)) *
          ‖leechGeneratorRowsUnscaled (⟨0, by decide⟩ : Fin 24) -
              leechGeneratorRowsUnscaled (⟨1, by decide⟩ : Fin 24)‖ ^ 2 := by
    calc
      ‖leechGeneratorRows (⟨0, by decide⟩ : Fin 24) -
            leechGeneratorRows (⟨1, by decide⟩ : Fin 24)‖ ^ (2 : ℕ)
          =
        ‖((Real.sqrt 8)⁻¹ : ℝ) •
              (leechGeneratorRowsUnscaled (⟨0, by decide⟩ : Fin 24) -
                leechGeneratorRowsUnscaled (⟨1, by decide⟩ : Fin 24))‖ ^ (2 : ℕ) := by
          simpa using! congrArg (fun x : ℝ²⁴ => ‖x‖ ^ (2 : ℕ)) hdiff
      _ =
        (‖((Real.sqrt 8)⁻¹ : ℝ)‖ *
              ‖leechGeneratorRowsUnscaled (⟨0, by decide⟩ : Fin 24) -
                  leechGeneratorRowsUnscaled (⟨1, by decide⟩ : Fin 24)‖) ^ (2 : ℕ) := by
          simp [norm_smul]
      _ =
        (‖((Real.sqrt 8)⁻¹ : ℝ)‖ ^ (2 : ℕ)) *
          (‖leechGeneratorRowsUnscaled (⟨0, by decide⟩ : Fin 24) -
                leechGeneratorRowsUnscaled (⟨1, by decide⟩ : Fin 24)‖ ^ (2 : ℕ)) := by
          simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
  calc
    ‖leechGeneratorRows (⟨0, by decide⟩ : Fin 24) -
          leechGeneratorRows (⟨1, by decide⟩ : Fin 24)‖ ^ 2
        = (8 : ℝ)⁻¹ * (32 : ℝ) := by
            calc
              ‖leechGeneratorRows (⟨0, by decide⟩ : Fin 24) -
                    leechGeneratorRows (⟨1, by decide⟩ : Fin 24)‖ ^ 2
                  =
                (‖((Real.sqrt 8)⁻¹ : ℝ)‖ ^ (2 : ℕ)) *
                  ‖leechGeneratorRowsUnscaled (⟨0, by decide⟩ : Fin 24) -
                      leechGeneratorRowsUnscaled (⟨1, by decide⟩ : Fin 24)‖ ^ 2 := hnorm
              _ = (‖((Real.sqrt 8)⁻¹ : ℝ)‖ ^ (2 : ℕ)) * (32 : ℝ) := by rw [hun]
              _ = (((Real.sqrt 8)⁻¹ : ℝ) ^ (2 : ℕ)) * (32 : ℝ) := by simp [habs]
              _ = (8 : ℝ)⁻¹ * (32 : ℝ) := by simp
    _ = (4 : ℝ) := by norm_num

lemma leechGeneratorRows_sub_row0_row1_mem_minShell :
    leechGeneratorRows (⟨0, by decide⟩ : Fin 24) -
        leechGeneratorRows (⟨1, by decide⟩ : Fin 24) ∈ minShell LeechLattice := by
  refine ⟨?_, ?_⟩
  · exact sub_mem (leechGeneratorRows_mem_leechLattice _) (leechGeneratorRows_mem_leechLattice _)
  · have h4 :
        ‖leechGeneratorRows (⟨0, by decide⟩ : Fin 24) -
              leechGeneratorRows (⟨1, by decide⟩ : Fin 24)‖ ^ 2 = (4 : ℝ) :=
      norm_sq_leechGeneratorRows_sub_row0_row1
    -- `thetaShell` expects `‖v‖^2 = 2 * 2`
    calc
      ‖leechGeneratorRows (⟨0, by decide⟩ : Fin 24) -
            leechGeneratorRows (⟨1, by decide⟩ : Fin 24)‖ ^ 2
          = (4 : ℝ) := h4
      _ = (2 : ℝ) * (2 : ℕ) := by norm_num

/-- The minimal shell of the Leech lattice spans the lattice over `ℤ`. -/
public theorem spanZ_minShell_eq_leechLattice :
    Submodule.span ℤ (minShell LeechLattice : Set ℝ²⁴) = LeechLattice := by
  have h₁ : Submodule.span ℤ (minShell LeechLattice : Set ℝ²⁴) ≤ LeechLattice :=
    Submodule.span_le.2 (fun v hv => hv.1)
  have hrow0 :
      leechGeneratorRows (⟨0, by decide⟩ : Fin 24) ∈
        Submodule.span ℤ (minShell LeechLattice : Set ℝ²⁴) := by
    have hsubSpan :
        leechGeneratorRows (⟨0, by decide⟩ : Fin 24) -
            leechGeneratorRows (⟨1, by decide⟩ : Fin 24) ∈
          Submodule.span ℤ (minShell LeechLattice : Set ℝ²⁴) :=
      Submodule.subset_span leechGeneratorRows_sub_row0_row1_mem_minShell
    have hrow1Span :
        leechGeneratorRows (⟨1, by decide⟩ : Fin 24) ∈
          Submodule.span ℤ (minShell LeechLattice : Set ℝ²⁴) :=
      Submodule.subset_span
        (leechGeneratorRows_mem_minShell_of_ne_zero (i := (⟨1, by decide⟩ : Fin 24)) (by decide))
    exact
      (Submodule.sub_mem_iff_left (Submodule.span ℤ (minShell LeechLattice)) hrow1Span).mp
        hsubSpan
  have hrow_ne0 :
      ∀ i : Fin 24, i ≠ 0 →
        leechGeneratorRows i ∈ Submodule.span ℤ (minShell LeechLattice : Set ℝ²⁴) := by
    intro i hi
    exact Submodule.subset_span (leechGeneratorRows_mem_minShell_of_ne_zero (i := i) hi)
  have h₂ : LeechLattice ≤ Submodule.span ℤ (minShell LeechLattice : Set ℝ²⁴) := by
    intro v hv
    change v ∈ Submodule.span ℤ (Set.range leechGeneratorRows) at hv
    have hgen :
        Set.range leechGeneratorRows ⊆
          (Submodule.span ℤ (minShell LeechLattice : Set ℝ²⁴) : Set ℝ²⁴) := by
      rintro _ ⟨i, rfl⟩
      by_cases hi : i = 0
      · subst hi; simpa using! hrow0
      · exact hrow_ne0 i hi
    have hspan :
        Submodule.span ℤ (Set.range leechGeneratorRows) ≤
          Submodule.span ℤ (minShell LeechLattice : Set ℝ²⁴) :=
      Submodule.span_le.2 (fun x hx => hgen hx)
    exact hspan hv
  exact le_antisymm h₁ h₂

end NiemeierRootless

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
