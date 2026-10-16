-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.CodeBounds.Basic
import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayBounds
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.ScaledCoord


/-!
# Reduced witnesses for `codeFromLattice`

Given a nonzero word `c` in the extracted code `codeFromLattice`, a witness consists of a vector
`x ∈ latticeL C` and an even integer coordinate vector `z` such that
`c i = ((z i / 2 : ℤ) : ZMod 2)`.

This file proves a reduction step: after subtracting a suitable element of the embedded
`√2 D₂₄ ⊆ latticeL C`, we may assume every coordinate satisfies `z i ∈ {0, 2, -2}`.

## Main statement
* `CodeFromLattice.exists_reduced_witness`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21

noncomputable section

open scoped RealInnerProductSpace BigOperators

open Set

open Uniqueness.BS81.CodingTheory

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace CodeFromLattice

private lemma zmod2_intCast_eq_zero_of_even (a : ℤ) (hE : Even a) : (a : ZMod 2) = 0 :=
  ZMod.intCast_eq_zero_iff_even.mpr hE

private lemma zmod2_intCast_eq_one_of_not_even (a : ℤ) (hE : ¬Even a) : (a : ZMod 2) = 1 := by
  have ha_ne0 : (a : ZMod 2) ≠ 0 := by
    intro ha0
    have hdvd : (2 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd (a := a) (b := 2)).1 ha0
    rcases hdvd with ⟨k, hk⟩
    have : Even a := ⟨k, by simpa [two_mul] using! hk⟩
    exact hE this
  exact (GolayBounds.zmod2_eq_zero_or_eq_one a).resolve_left ha_ne0


/-- Reduction step: for a nonzero codeword `c` witnessed by even coordinates `z`,
adjust by a `√2 D₂₄` vector to obtain a witness with coordinates in `{0,±2}`. -/
public theorem exists_reduced_witness
    (C : Set ℝ²⁴)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24)
    {c : BinWord 24} (hc : c ∈ codeFromLattice (C := C) hDn) (hc0 : c ≠ 0) :
    ∃ x : ℝ²⁴,
      x ∈ (latticeL C : Set ℝ²⁴) ∧
        ∃ z : Fin 24 → ℤ,
          (∀ i : Fin 24, scaledCoord hDn.e i x = (z i : ℝ)) ∧
            (∀ i : Fin 24, z i = 0 ∨ z i = 2 ∨ z i = -2) ∧
              (∀ i : Fin 24, c i = ((z i / 2 : ℤ) : ZMod 2)) := by
  rcases hc with ⟨x0, hx0L, z0, hz0, hz0E, hc0z⟩
  -- Let `m = z0/2` and choose `s ∈ {0,±1}` so that `z' = 2s` has entries in `{0,±2}` and
  -- represents the same codeword.
  let m : Fin 24 → ℤ := fun i => z0 i / 2
  have hz0_eq_two_mul_m : ∀ i : Fin 24, z0 i = 2 * m i :=
    fun i => Eq.symm (Int.two_mul_ediv_two_of_even (hz0E i))
  have hc_m : ∀ i : Fin 24, c i = (m i : ZMod 2) := by
    intro i
    simpa [m] using! (hc0z i)
  rcases exists_idx_one_of_ne_zero (c := c) hc0 with ⟨i₁, hi₁⟩
  have hi₁_odd : ¬Even (m i₁) := by
    -- if `m i₁` were even then `(m i₁ : ZMod 2) = 0`, contradicting `c i₁ = 1`
    intro hE
    have : (m i₁ : ZMod 2) = 0 := zmod2_intCast_eq_zero_of_even (m i₁) hE
    have hc0' : c i₁ = 0 := by simpa [hc_m i₁] using! this
    simp [hi₁] at hc0'
  -- Default choice of `s`: `0` on even `m`, `1` on odd `m`.
  let s0 : Fin 24 → ℤ := fun i => if Even (m i) then 0 else 1
  have hs0_spec : ∀ i : Fin 24, s0 i = 0 ∨ s0 i = 1 := by
    intro i
    by_cases hE : Even (m i) <;> simp [s0, hE]
  -- The corresponding `a0 = (m - s0)/2`.
  let a0 : Fin 24 → ℤ := fun i => (m i - s0 i) / 2
  have ha0_integral : ∀ i : Fin 24, Even (m i - s0 i) := by
    intro i
    by_cases hE : Even (m i)
    · -- then `s0 i = 0`
      have hs0 : s0 i = 0 := by simp [s0, hE]
      simpa [hs0] using! hE
    · -- then `s0 i = 1` and `m i` is odd
      have hs0 : s0 i = 1 := by simp [s0, hE]
      have hOdd : Odd (m i) := (Int.odd_iff).2 ((Int.not_even_iff).1 hE)
      have hEven : Even (m i - 1) := hOdd.sub_odd odd_one
      simpa [hs0, sub_eq_add_neg] using! hEven
  -- Possibly flip `s0` at `i₁` to make `∑ a` even.
  let S : ℤ := ∑ i : Fin 24, a0 i
  by_cases hSEven : Even S
  · -- use `s0`
    let s : Fin 24 → ℤ := s0
    let a : Fin 24 → ℤ := a0
    have haSum : Even (∑ i : Fin 24, a i) := by simpa [S, a]
    have ha_def : ∀ i : Fin 24, m i - s i = 2 * a i :=
      fun i => Eq.symm (Int.two_mul_ediv_two_of_even (ha0_integral i))
    -- build the shift vector with scaled coordinates `4a`
    rcases exists_lattice_vector_scaledCoord_eq_four_mul (C := C) hDn a haSum with ⟨y, hyL, hyCoord⟩
    let x : ℝ²⁴ := x0 - y
    refine ⟨x, sub_mem hx0L hyL, ?_⟩
    let z : Fin 24 → ℤ := fun i => 2 * s i
    refine ⟨z, ?_, ?_, ?_⟩
    · intro i
      have hx0 : scaledCoord hDn.e i x0 = (z0 i : ℝ) := hz0 i
      have hy : scaledCoord hDn.e i y = ((4 * a i : ℤ) : ℝ) := hyCoord i
      -- use `ha_def i : m i - s i = 2 * a i` to identify the shifted coordinates
      have hm : m i = s i + 2 * a i :=
        Int.sub_eq_iff_eq_add'.mp (ha_def i)
      have hZ : (2 * m i - 4 * a i : ℤ) = 2 * s i := by
        calc
          (2 * m i - 4 * a i : ℤ) = 2 * (s i + 2 * a i) - 4 * a i := by simp [hm]
          _ = 2 * s i := by ring_nf
      have hR' : ((2 * m i - 4 * a i : ℤ) : ℝ) = (2 * s i : ℤ) := by exact_mod_cast hZ
      have hR : (2 : ℝ) * (m i : ℝ) - (4 : ℝ) * (a i : ℝ) = (2 : ℝ) * (s i : ℝ) := by
        simpa [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, sub_eq_add_neg, add_assoc, add_comm,
          add_left_comm, mul_assoc, mul_comm, mul_left_comm] using! hR'
      simpa [x, SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.scaledCoord_sub, hx0, hy, z,
        hz0_eq_two_mul_m i, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
        mul_left_comm] using! hR
    · intro i
      have hs : s i = 0 ∨ s i = 1 := by simpa [s] using! hs0_spec i
      rcases hs with hs | hs
      · left
        simp [z, hs]
      · right; left
        simp [z, hs]
    · intro i
      by_cases hE : Even (m i)
      · have hs : s i = 0 := by simp [s, s0, hE]
        have hm0 : (m i : ZMod 2) = 0 := zmod2_intCast_eq_zero_of_even (m i) hE
        have hc0 : c i = 0 := by simpa [hc_m i] using! hm0
        simp [hs, z, hc0]
      · have hs : s i = 1 := by simp [s, s0, hE]
        have hm1 : (m i : ZMod 2) = 1 := zmod2_intCast_eq_one_of_not_even (m i) hE
        have hc1 : c i = 1 := by simpa [hc_m i] using! hm1
        simp [hs, z, hc1]
  · -- flip at `i₁`
    let s : Fin 24 → ℤ := fun i => if i = i₁ then - (s0 i) else s0 i
    let a : Fin 24 → ℤ := fun i => (m i - s i) / 2
    have hs_i1 : s i₁ = - (s0 i₁) := by simp [s]
    have hs_i_ne : ∀ i : Fin 24, i ≠ i₁ → s i = s0 i := by
      intro i hi
      simp [s, hi]
    have hs0_i1 : s0 i₁ = 1 := by
      -- since `m i₁` is odd
      have : ¬Even (m i₁) := hi₁_odd
      simp [s0, this]
    have hs_i1_val : s i₁ = -1 := by simp [hs_i1, hs0_i1]
    have haSum : Even (∑ i : Fin 24, a i) := by
      -- For `i ≠ i₁`, `s i = s0 i`, hence `a i = a0 i`.
      have ha_eq : ∀ i : Fin 24, i ≠ i₁ → a i = a0 i := by
        intro i hi
        simp [a, a0, hs_i_ne i hi]
      have hsum_erase :
          (∑ i ∈ (Finset.univ.erase i₁), a i) = ∑ i ∈ (Finset.univ.erase i₁), a0 i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hi' : i ≠ i₁ := (Finset.mem_erase.1 hi).1
        simpa using! (ha_eq i hi')
      have hsum_a :
          (∑ i : Fin 24, a i) = (∑ i ∈ (Finset.univ.erase i₁), a i) + a i₁ := by
        exact
          (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 24))) (f := a)
                (a := i₁) (Finset.mem_univ i₁)).symm
      have hsum_a0 :
          (∑ i : Fin 24, a0 i) = (∑ i ∈ (Finset.univ.erase i₁), a0 i) + a0 i₁ := by
        exact
          (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 24))) (f := a0)
                (a := i₁) (Finset.mem_univ i₁)).symm
      have ha_i1 : a i₁ = a0 i₁ + 1 := by
        have hmOdd : Odd (m i₁) := (Int.odd_iff).2 ((Int.not_even_iff).1 hi₁_odd)
        rcases hmOdd with ⟨k, hk⟩
        have hm : m i₁ = 2 * k + 1 := by
          simpa [two_mul, add_assoc, add_left_comm, add_comm] using! hk
        have ha0i1 : a0 i₁ = k := by
          calc
            a0 i₁ = (m i₁ - s0 i₁) / 2 := by simp [a0]
            _ = (m i₁ - 1) / 2 := by simp [hs0_i1]
            _ = (2 * k + 1 - 1) / 2 := by simp [hm]
            _ = (2 * k) / 2 := by ring_nf
            _ = k := by
                  exact (Int.mul_ediv_cancel_left (a := (2 : ℤ)) k (two_ne_zero : (2 : ℤ) ≠ 0))
        have hai1 : a i₁ = k + 1 := by
          calc
            a i₁ = (m i₁ - s i₁) / 2 := by simp [a]
            _ = (m i₁ - (-1)) / 2 := by simp [hs_i1_val]
            _ = (m i₁ + 1) / 2 := by ring_nf
            _ = (2 * k + 1 + 1) / 2 := by simp [hm]
            _ = (2 * (k + 1)) / 2 := by ring_nf
            _ = k + 1 := by
                  exact
                    (Int.mul_ediv_cancel_left (a := (2 : ℤ)) (k + 1) (two_ne_zero : (2 : ℤ) ≠ 0))
        calc
          a i₁ = k + 1 := hai1
          _ = a0 i₁ + 1 := by simp [ha0i1]
      have hflip : (∑ i : Fin 24, a i) = S + 1 := by
        have hErase_a0 :
            (∑ i ∈ (Finset.univ.erase i₁), a0 i) = (∑ i : Fin 24, a0 i) - a0 i₁ := by
          -- rearrange `hsum_a0`
          nlinarith [hsum_a0]
        calc
          (∑ i : Fin 24, a i)
              = (∑ i ∈ (Finset.univ.erase i₁), a i) + a i₁ := hsum_a
          _ = (∑ i ∈ (Finset.univ.erase i₁), a0 i) + a i₁ := by simp [hsum_erase]
          _ = ((∑ i : Fin 24, a0 i) - a0 i₁) + a i₁ := by simp [hErase_a0]
          _ = (∑ i : Fin 24, a0 i) + (a i₁ - a0 i₁) := by ring
          _ = S + 1 := by simp [S, ha_i1]
      have hSodd : Odd S := (Int.odd_iff).2 ((Int.not_even_iff).1 hSEven)
      have hEven : Even (S + 1) := Odd.add_odd hSodd odd_one
      simpa [hflip] using! hEven
    -- build the shift vector with scaled coordinates `4a`
    rcases exists_lattice_vector_scaledCoord_eq_four_mul (C := C) hDn a haSum with ⟨y, hyL, hyCoord⟩
    let x : ℝ²⁴ := x0 - y
    refine ⟨x, sub_mem hx0L hyL, ?_⟩
    let z : Fin 24 → ℤ := fun i => 2 * s i
    refine ⟨z, ?_, ?_, ?_⟩
    · intro i
      have hx0 : scaledCoord hDn.e i x0 = (z0 i : ℝ) := hz0 i
      have hy : scaledCoord hDn.e i y = ((4 * a i : ℤ) : ℝ) := hyCoord i
      have haEven : Even (m i - s i) := by
        by_cases hi1 : i = i₁
        · subst i
          have hmOdd : Odd (m i₁) := (Int.odd_iff).2 ((Int.not_even_iff).1 hi₁_odd)
          have hEven : Even (m i₁ + 1) := Odd.add_odd hmOdd odd_one
          -- `m i₁ - s i₁ = m i₁ + 1` since `s i₁ = -1`.
          simpa [hs_i1_val, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using! hEven
        · -- for `i ≠ i₁`, `s i = s0 i`, hence the evenness is already proved.
          simpa [hs_i_ne i hi1] using! (ha0_integral i)
      have hdvd : (2 : ℤ) ∣ m i - s i := by
        exact Even.two_dvd haEven
      have h2a : 2 * a i = m i - s i := by
        exact Int.two_mul_ediv_two_of_even haEven
      have hZ : (2 * m i - 4 * a i : ℤ) = 2 * s i := by
        calc
          (2 * m i - 4 * a i : ℤ) = 2 * m i - 2 * (2 * a i) := by ring
          _ = 2 * m i - 2 * (m i - s i) := by simp [h2a]
          _ = 2 * s i := by ring
      have hR' : ((2 * m i - 4 * a i : ℤ) : ℝ) = (2 * s i : ℤ) := by
        exact_mod_cast hZ
      have hR : (2 : ℝ) * (m i : ℝ) - (4 : ℝ) * (a i : ℝ) = (2 : ℝ) * (s i : ℝ) := by
        simpa [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, sub_eq_add_neg, add_assoc, add_comm,
          add_left_comm, mul_assoc, mul_comm, mul_left_comm] using! hR'
      simpa [x, SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.scaledCoord_sub, hx0, hy, z,
        hz0_eq_two_mul_m i, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
        mul_left_comm] using! hR
    · intro i
      by_cases hi : i = i₁
      · subst hi
        right; right
        simp [z, hs_i1_val]
      · have hs : s i = 0 ∨ s i = 1 := by
          by_cases hE : Even (m i)
          · exact Or.inl (by simp [s, s0, hE, hi])
          · exact Or.inr (by simp [s, s0, hE, hi])
        rcases hs with hs | hs
        · left
          simp [z, hs]
        · right; left
          simp [z, hs]
    · intro i
      -- represent the same codeword (in `ZMod 2`, `-1 = 1`)
      by_cases hi : i = i₁
      · subst i
        have hz : z i₁ = -2 := by simp [z, hs_i1_val]
        have hc1 : c i₁ = 1 := hi₁
        simp [hz, hc1]
      · by_cases hE : Even (m i)
        · have hs : s i = 0 := by simp [s, s0, hE, hi]
          have hz : z i = 0 := by simp [z, hs]
          have hm0 : (m i : ZMod 2) = 0 := zmod2_intCast_eq_zero_of_even (m i) hE
          have hc0 : c i = 0 := by simpa [hc_m i] using! hm0
          simp [hz, hc0]
        · have hs : s i = 1 := by simp [s, s0, hE, hi]
          have hz : z i = 2 := by simp [z, hs]
          have hm1 : (m i : ZMod 2) = 1 := zmod2_intCast_eq_one_of_not_even (m i) hE
          have hc1 : c i = 1 := by simpa [hc_m i] using! hm1
          simp [hz, hc1]


end CodeFromLattice

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21
