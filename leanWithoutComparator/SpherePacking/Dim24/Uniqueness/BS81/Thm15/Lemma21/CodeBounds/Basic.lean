-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.CodeFromLattice
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Coordinates
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayBounds

/-!
# Code-from-lattice weight bound (BS81 Lemma 21)

This file proves the main input for BS81 Lemma 21: if `c ∈ codeFromLattice` is nonzero, then
`weight c ≥ 8`. The argument is explained in the note
`paper/Notes/CodingTheory/bs81_lemma21_golay_inputs.tex`.

The proof uses:
* Lemma 16: the lattice `latticeL` has minimum squared norm at least `4`;
* a coordinate reduction step: after adjusting by `√2 D₂₄ ⊆ latticeL`, scaled coordinates lie in
  `{0, ±2}`.
-/


namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21

noncomputable section

open scoped RealInnerProductSpace BigOperators

open Set

open Uniqueness.BS81.CodingTheory

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace CodeFromLattice

lemma sqrt8_mul_sqrt2 : (Real.sqrt 8 : ℝ) * Real.sqrt 2 = 4 := by
  calc
    (Real.sqrt 8 : ℝ) * Real.sqrt 2 = ((2 : ℝ) * Real.sqrt 2) * Real.sqrt 2 := by
      simp [_root_.SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.sqrt8_eq_two_mul_sqrt2]
    _ = (2 : ℝ) * ((Real.sqrt 2) * Real.sqrt 2) := by ring
    _ = (2 : ℝ) * (2 : ℝ) := by
      have h2 : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
      simp [Real.mul_self_sqrt h2]
    _ = 4 := by ring

def scaledCoordAddHom (e : Fin 24 → ℝ²⁴) (i : Fin 24) : ℝ²⁴ →+ ℝ where
  toFun x := scaledCoord e i x
  map_zero' := by simp [scaledCoord, coord]
  map_add' x y := by
    simp [scaledCoord, coord, inner_add_right, mul_add]

lemma scaledCoord_zsmul (e : Fin 24 → ℝ²⁴) (i : Fin 24) (n : ℤ) (x : ℝ²⁴) :
    scaledCoord e i (n • x) = (n : ℝ) * scaledCoord e i x := by
  have h' : scaledCoord e i (n • x) = n • scaledCoord e i x := by
    exact map_zsmul (scaledCoordAddHom e i) n x
  refine h'.trans ?_
  simp [zsmul_eq_mul]

lemma scaledCoord_sum (e : Fin 24 → ℝ²⁴) (i : Fin 24) {α : Type*}
    (s : Finset α) (f : α → ℝ²⁴) :
    scaledCoord e i (∑ a ∈ s, f a) = ∑ a ∈ s, scaledCoord e i (f a) := by
  -- rewrite the goal in terms of the additive hom, then use `map_sum`
  change (scaledCoordAddHom e i) (∑ a ∈ s, f a) = ∑ a ∈ s, (scaledCoordAddHom e i) (f a)
  exact map_sum (g := scaledCoordAddHom e i) (f := f) (s := s)

lemma scaledCoord_minVec_add
    (e : Fin 24 → ℝ²⁴) (he : Orthonormal ℝ e) (i j k : Fin 24) :
    scaledCoord e k (Real.sqrt 2 • (e i + e j)) =
      (if k = i then (4 : ℝ) else 0) + (if k = j then (4 : ℝ) else 0) := by
  have hite := (orthonormal_iff_ite).1 he
  have hs : (Real.sqrt 2 : ℝ) * Real.sqrt 8 = 4 := by
    simpa [mul_comm] using! (sqrt8_mul_sqrt2 : (Real.sqrt 8 : ℝ) * Real.sqrt 2 = 4)
  have hbase :
      scaledCoord e k (Real.sqrt 2 • (e i + e j)) =
        ((if k = i then (Real.sqrt 2 : ℝ) else 0) + (if k = j then (Real.sqrt 2 : ℝ) else 0)) *
          (Real.sqrt 8 : ℝ) := by
    -- unfold and reduce the inner products using orthonormality
    simp [scaledCoord, coord, real_inner_smul_right, inner_add_right, hite, add_mul, mul_comm]
  -- distribute the final multiplication by `√8` and use `√2*√8 = 4`
  rw [hbase]
  -- `simp` finishes after splitting the `if`s
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp [hki, hkj, add_mul, hs]

lemma scaledCoord_minVec_sub
    (e : Fin 24 → ℝ²⁴) (he : Orthonormal ℝ e) (i j k : Fin 24) :
    scaledCoord e k (Real.sqrt 2 • (e i - e j)) =
      (if k = i then (4 : ℝ) else 0) - (if k = j then (4 : ℝ) else 0) := by
  have hite := (orthonormal_iff_ite).1 he
  have hs : (Real.sqrt 2 : ℝ) * Real.sqrt 8 = 4 := by
    simpa [mul_comm] using! (sqrt8_mul_sqrt2 : (Real.sqrt 8 : ℝ) * Real.sqrt 2 = 4)
  have hbase :
      scaledCoord e k (Real.sqrt 2 • (e i - e j)) =
        ((if k = i then (Real.sqrt 2 : ℝ) else 0) - (if k = j then (Real.sqrt 2 : ℝ) else 0)) *
          (Real.sqrt 8 : ℝ) := by
    simp [scaledCoord, coord, real_inner_smul_right, inner_sub_right, hite, sub_mul, mul_comm]
  rw [hbase]
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp [hki, hkj, sub_mul, hs]

/-- For an integer vector `a` with even coordinate sum, we can realize the scaled coordinate vector
`4a` inside `latticeL` using the embedded `D₂₄`. -/
public theorem exists_lattice_vector_scaledCoord_eq_four_mul
    (C : Set ℝ²⁴) (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24)
    (a : Fin 24 → ℤ) (ha : Even (∑ i : Fin 24, a i)) :
    ∃ y : ℝ²⁴,
      y ∈ (latticeL C : Set ℝ²⁴) ∧
        ∀ k : Fin 24, scaledCoord hDn.e k y = ((4 * a k : ℤ) : ℝ) := by
  rcases ha with ⟨t, ht⟩
  -- generators inside `latticeL`
  have h01 : (0 : Fin 24) ≠ (1 : Fin 24) := by decide
  let vSum : ℝ²⁴ := Real.sqrt 2 • (hDn.e 0 + hDn.e 1)
  have hvSum : vSum ∈ (latticeL C : Set ℝ²⁴) := (hDn.minVec_mem 0 1 h01).1.1
  let vDiff : Fin 24 → ℝ²⁴ := fun i => Real.sqrt 2 • (hDn.e i - hDn.e 0)
  have hvDiff : ∀ i : Fin 24, i ≠ 0 → vDiff i ∈ (latticeL C : Set ℝ²⁴) := by
    intro i hi
    have hmem := (hDn.minVec_mem i 0 hi).2
    exact hmem.1
  -- coefficients for the spanning expression
  let b : Fin 24 → ℤ := fun i => if i = 1 then a 1 - t else a i
  let y : ℝ²⁴ :=
    t • vSum + ∑ i ∈ (Finset.univ.erase 0), (b i) • vDiff i
  refine ⟨y, ?_, ?_⟩
  · -- membership in the lattice
    have hsum :
        (∑ i ∈ (Finset.univ.erase 0), (b i) • vDiff i) ∈ (latticeL C : Set ℝ²⁴) := by
      refine (latticeL C).sum_mem ?_
      intro i hi
      have hi0 : i ≠ (0 : Fin 24) := (Finset.mem_erase.1 hi).1
      exact (latticeL C).smul_mem (b i) (hvDiff i hi0)
    exact (latticeL C).add_mem ((latticeL C).smul_mem t hvSum) hsum
  · -- scaled coordinates are `4a`
    intro k
    have he : Orthonormal ℝ hDn.e := hDn.ortho
    -- generator coordinates
    have hSumCoord :
        scaledCoord hDn.e k vSum =
          (if k = 0 then (4 : ℝ) else 0) + (if k = 1 then (4 : ℝ) else 0) := by
      simpa [vSum] using!
        scaledCoord_minVec_add (e := hDn.e) he (i := (0 : Fin 24)) (j := (1 : Fin 24)) (k := k)
    have hDiffCoord :
        ∀ i : Fin 24,
          scaledCoord hDn.e k (vDiff i) =
            (if k = i then (4 : ℝ) else 0) - (if k = 0 then (4 : ℝ) else 0) :=
      fun i => scaledCoord_minVec_sub hDn.e he i 0 k
    -- expand `scaledCoord` on `y` using additivity, `zsmul`, and `sum`
    have hy_expand :
        scaledCoord hDn.e k y =
          (t : ℝ) * scaledCoord hDn.e k vSum +
            ∑ i ∈ (Finset.univ.erase 0), (b i : ℝ) * scaledCoord hDn.e k (vDiff i) := by
      -- unfold `y` and push `scaledCoord` through `+`, `•`, and `∑` without rewriting the finset
      have hadd :
          scaledCoord hDn.e k y =
            scaledCoord hDn.e k (t • vSum) +
              scaledCoord hDn.e k (∑ i ∈ (Finset.univ.erase 0), (b i) • vDiff i) := by
        exact (scaledCoordAddHom hDn.e k).map_add (t • vSum)
            (∑ i ∈ (Finset.univ.erase 0), (b i) • vDiff i)
      have hsmul : scaledCoord hDn.e k (t • vSum) = (t : ℝ) * scaledCoord hDn.e k vSum := by
        simpa using! (scaledCoord_zsmul (e := hDn.e) (i := k) t vSum)
      have hsum :
          scaledCoord hDn.e k (∑ i ∈ (Finset.univ.erase 0), (b i) • vDiff i) =
            ∑ i ∈ (Finset.univ.erase 0), (b i : ℝ) * scaledCoord hDn.e k (vDiff i) := by
        -- first map through the sum, then through each `zsmul`
        calc
          scaledCoord hDn.e k (∑ i ∈ (Finset.univ.erase 0), (b i) • vDiff i) =
              ∑ i ∈ (Finset.univ.erase 0), scaledCoord hDn.e k ((b i) • vDiff i) :=
                scaledCoord_sum hDn.e k (Finset.univ.erase 0) fun a => b a • vDiff a
          _ = ∑ i ∈ (Finset.univ.erase 0), (b i : ℝ) * scaledCoord hDn.e k (vDiff i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [scaledCoord_zsmul]
      -- assemble
      calc
        scaledCoord hDn.e k y =
            scaledCoord hDn.e k (t • vSum) +
              scaledCoord hDn.e k (∑ i ∈ (Finset.univ.erase 0), (b i) • vDiff i) := hadd
        _ = (t : ℝ) * scaledCoord hDn.e k vSum +
              ∑ i ∈ (Finset.univ.erase 0), (b i : ℝ) * scaledCoord hDn.e k (vDiff i) := by
              rw [hsmul, hsum]
    -- now compute by cases on `k`
    by_cases hk0 : k = (0 : Fin 24)
    · subst hk0
      -- for `k=0`, each `vDiff i` contributes `-4`
      have hdiff0 :
          ∀ i : Fin 24, i ∈ (Finset.univ.erase 0) →
            scaledCoord hDn.e 0 (vDiff i) = (-4 : ℝ) := by
        intro i hi
        have hi0 : i ≠ (0 : Fin 24) := (Finset.mem_erase.1 hi).1
        have :
            scaledCoord hDn.e 0 (vDiff i) =
              (if (0 : Fin 24) = i then (4 : ℝ) else 0) -
                (if (0 : Fin 24) = 0 then (4 : ℝ) else 0) := by
          simpa using! (hDiffCoord i)
        -- simplify the `if`s
        have hi0' : (0 : Fin 24) ≠ i := by simpa [eq_comm] using! hi0
        simpa [hi0'] using! this
      -- rewrite the sum term
      have hsum_term :
          (∑ i ∈ (Finset.univ.erase 0), (b i : ℝ) * scaledCoord hDn.e 0 (vDiff i)) =
            (∑ i ∈ (Finset.univ.erase 0), (b i : ℝ) * (-4 : ℝ)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [hdiff0 i hi]
      -- simplify the `vSum` coordinate
      have hvSum0 : scaledCoord hDn.e 0 vSum = (4 : ℝ) := by simp [hSumCoord]
      -- evaluate and use `ht : ∑ a = 2*t` to identify the coefficient
      -- first compute `∑ b` over `erase 0`
      have hb_sum :
          (∑ i ∈ (Finset.univ.erase 0), b i) =
            (∑ i ∈ (Finset.univ.erase 0), a i) - t := by
        -- isolate the `i=1` term
        have h1mem : (1 : Fin 24) ∈ (Finset.univ.erase 0) := by simp
        have hb_split :
            (∑ i ∈ (Finset.univ.erase 0), b i) =
              (∑ i ∈ ((Finset.univ.erase 0).erase 1), b i) + b 1 :=
          Eq.symm (Finset.sum_erase_add (Finset.univ.erase 0) b h1mem)
        have ha_split :
            (∑ i ∈ (Finset.univ.erase 0), a i) =
              (∑ i ∈ ((Finset.univ.erase 0).erase 1), a i) + a 1 :=
          Eq.symm (Finset.sum_erase_add (Finset.univ.erase 0) a h1mem)
        have hEraseEq :
            (∑ i ∈ ((Finset.univ.erase 0).erase 1), b i) =
              ∑ i ∈ ((Finset.univ.erase 0).erase 1), a i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hi1 : i ≠ (1 : Fin 24) := (Finset.mem_erase.1 hi).1
          simp [b, hi1]
        -- combine
        calc
          (∑ i ∈ (Finset.univ.erase 0), b i)
              = (∑ i ∈ ((Finset.univ.erase 0).erase 1), b i) + b 1 := hb_split
          _ = (∑ i ∈ ((Finset.univ.erase 0).erase 1), a i) + (a 1 - t) := by
                simp [hEraseEq, b]
          _ = (∑ i ∈ (Finset.univ.erase 0), a i) - t := by
                -- rewrite using `ha_split`
                nlinarith [ha_split]
      have ha_total : (∑ i : Fin 24, a i) = 2 * t := by
        calc
          (∑ i : Fin 24, a i) = t + t := ht
          _ = 2 * t := by simp [two_mul]
      have ha_total' : (a 0) + (∑ i ∈ (Finset.univ.erase 0), a i) = 2 * t := by
        -- split off index `0`
        assumption
      -- finish the coordinate computation
      -- start from `hy_expand`
      calc
          scaledCoord hDn.e 0 y
            = (t : ℝ) * scaledCoord hDn.e 0 vSum +
                ∑ i ∈ (Finset.univ.erase 0), (b i : ℝ) * scaledCoord hDn.e 0 (vDiff i) := hy_expand
        _ = (t : ℝ) * (4 : ℝ) + ∑ i ∈ (Finset.univ.erase 0), (b i : ℝ) * (-4 : ℝ) := by
              simp [hvSum0, hsum_term]
        _ = ((4 * a 0 : ℤ) : ℝ) := by
              have hsum_b :
                  (∑ i ∈ (Finset.univ.erase 0), (b i : ℝ) * (-4 : ℝ)) =
                    (-4 : ℝ) * ∑ i ∈ (Finset.univ.erase 0), (b i : ℝ) := by
                -- factor the right multiplication, then commute
                calc
                  (∑ i ∈ (Finset.univ.erase 0), (b i : ℝ) * (-4 : ℝ)) =
                      (∑ i ∈ (Finset.univ.erase 0), (b i : ℝ)) * (-4 : ℝ) := by
                        simpa using!
                          (Finset.sum_mul (s := (Finset.univ.erase 0))
                              (f := fun i : Fin 24 => (b i : ℝ)) (a := (-4 : ℝ))).symm
                  _ = (-4 : ℝ) * ∑ i ∈ (Finset.univ.erase 0), (b i : ℝ) := by
                        simp [mul_comm]
              have hb_sum_cast :
                  (∑ i ∈ (Finset.univ.erase 0), (b i : ℝ)) =
                    (∑ i ∈ (Finset.univ.erase 0), (a i : ℝ)) - (t : ℝ) := by
                -- cast `hb_sum : ∑ b = ∑ a - t`
                have := congrArg (fun z : ℤ => (z : ℝ)) hb_sum
                simpa [Int.cast_sub, Int.cast_add, Int.cast_mul, Finset.sum_sub_distrib] using! this
              -- package the two relevant partial sums
              let SB : ℝ := ∑ i ∈ (Finset.univ.erase 0), (b i : ℝ)
              let SA : ℝ := ∑ i ∈ (Finset.univ.erase 0), (a i : ℝ)
              have hbSB : SB = SA - (t : ℝ) := by simpa [SB, SA] using! hb_sum_cast
              have ha_total_cast : (a 0 : ℝ) + SA = (2 : ℝ) * (t : ℝ) := by
                have := congrArg (fun z : ℤ => (z : ℝ)) ha_total'
                simpa [Int.cast_add, Int.cast_mul, SA] using! this
              have ha0_eq : (a 0 : ℝ) = (2 : ℝ) * (t : ℝ) - SA := by
                nlinarith [ha_total_cast]
              have hsum_b' :
                  (∑ i ∈ (Finset.univ.erase 0), (b i : ℝ) * (-4 : ℝ)) = (-4 : ℝ) * SB := by
                simpa [SB] using! hsum_b
              have :
                  (t : ℝ) * (4 : ℝ) + ∑ i ∈ (Finset.univ.erase 0), (b i : ℝ) * (-4 : ℝ) =
                    (4 : ℝ) * (a 0 : ℝ) := by
                calc
                  (t : ℝ) * (4 : ℝ) + ∑ i ∈ (Finset.univ.erase 0), (b i : ℝ) * (-4 : ℝ)
                      = (t : ℝ) * (4 : ℝ) + (-4 : ℝ) * SB := by
                          rw [hsum_b']
                  _ = (4 : ℝ) * ((2 : ℝ) * (t : ℝ) - SA) := by
                          -- rewrite `SB = SA - t` and normalize
                          simp [hbSB]
                          ring_nf
                  _ = (4 : ℝ) * (a 0 : ℝ) := by simp [ha0_eq]
              simpa [Int.cast_mul, mul_assoc, mul_left_comm, mul_comm] using! this
    · by_cases hk1 : k = (1 : Fin 24)
      · subst hk1
        -- only the `i=1` term contributes in the sum, and `b 1 = a 1 - t`
        have hkMem : (1 : Fin 24) ∈ (Finset.univ.erase 0) := by simp
        have hdiff1 :
            ∀ i : Fin 24, i ∈ (Finset.univ.erase 0) →
              scaledCoord hDn.e 1 (vDiff i) = (if i = 1 then (4 : ℝ) else 0) := by
          intro i hi
          have : scaledCoord hDn.e 1 (vDiff i) =
              (if (1 : Fin 24) = i then (4 : ℝ) else 0) -
                (if (1 : Fin 24) = 0 then (4 : ℝ) else 0) := by
            simpa using! (hDiffCoord i)
          simpa [eq_comm] using! this
        have hvSum1 : scaledCoord hDn.e 1 vSum = (4 : ℝ) := by simp [hSumCoord]
        -- evaluate the sum using `Finset.sum_eq_single`
        have hsum_single :
            (∑ i ∈ (Finset.univ.erase 0), (b i : ℝ) * scaledCoord hDn.e 1 (vDiff i)) =
              (b 1 : ℝ) * (4 : ℝ) := by
          refine (Finset.sum_eq_single (1 : Fin 24) ?_ ?_).trans ?_
          · intro i hi hiNe
            have : scaledCoord hDn.e 1 (vDiff i) = 0 := by
              have := hdiff1 i hi
              simpa [hiNe] using! this
            simp [this]
          · intro hnot
            exact False.elim (hnot hkMem)
          · simp [hdiff1 _ hkMem]
        calc
          scaledCoord hDn.e 1 y
              = (t : ℝ) * scaledCoord hDn.e 1 vSum +
                  ∑ i ∈ (Finset.univ.erase 0), (b i : ℝ) * scaledCoord hDn.e 1 (vDiff i) :=
                hy_expand
          _ = (t : ℝ) * (4 : ℝ) + (b 1 : ℝ) * (4 : ℝ) := by simp [hvSum1, hsum_single]
          _ = ((4 * a 1 : ℤ) : ℝ) := by
                simp [b]
                ring
      · -- k is neither 0 nor 1: only the `i=k` term contributes, and `b k = a k`
        have hkMem : k ∈ (Finset.univ.erase 0) := by simp [hk0]
        have hvSumk : scaledCoord hDn.e k vSum = (0 : ℝ) := by
          have : (if k = 0 then (4 : ℝ) else 0) = 0 := by simp [hk0]
          have : (if k = 1 then (4 : ℝ) else 0) = 0 := by simp [hk1]
          simpa [hSumCoord, this]
        have hdiffk :
            ∀ i : Fin 24, i ∈ (Finset.univ.erase 0) →
              scaledCoord hDn.e k (vDiff i) = (if i = k then (4 : ℝ) else 0) := by
          intro i hi
          have hk0' : (if k = 0 then (4 : ℝ) else 0) = 0 := by simp [hk0]
          have : scaledCoord hDn.e k (vDiff i) =
              (if k = i then (4 : ℝ) else 0) - (if k = 0 then (4 : ℝ) else 0) := by
            simpa using! (hDiffCoord i)
          -- rewrite `if k=i` as `if i=k` for later simp
          simpa [hk0', eq_comm] using! this
        have hsum_single :
            (∑ i ∈ (Finset.univ.erase 0), (b i : ℝ) * scaledCoord hDn.e k (vDiff i)) =
              (b k : ℝ) * (4 : ℝ) := by
          refine (Finset.sum_eq_single k ?_ ?_).trans ?_
          · intro i hi hik
            have : scaledCoord hDn.e k (vDiff i) = 0 := by
              have := hdiffk i hi
              simpa [hik] using! this
            simp [this]
          · intro hnot
            exact False.elim (hnot hkMem)
          · simp [hdiffk _ hkMem]
        calc
          scaledCoord hDn.e k y
              = (t : ℝ) * scaledCoord hDn.e k vSum +
                  ∑ i ∈ (Finset.univ.erase 0), (b i : ℝ) * scaledCoord hDn.e k (vDiff i) :=
                hy_expand
          _ = (t : ℝ) * (0 : ℝ) + (b k : ℝ) * (4 : ℝ) := by simp [hvSumk, hsum_single]
          _ = ((4 * a k : ℤ) : ℝ) := by
                have : b k = a k := by simp [b, hk1]
                simp [this]
                ring

/-- In an orthonormal basis, `‖x‖ ^ 2` is the average of the squared scaled coordinates. -/
public lemma norm_sq_eq_sum_scaledCoord_sq_div8
    (e : Fin 24 → ℝ²⁴) (he : Orthonormal ℝ e) (x : ℝ²⁴) :
    ‖x‖ ^ 2 = (1 / 8 : ℝ) * ∑ i : Fin 24, (scaledCoord e i x) ^ 2 := by
  have hs8 : (Real.sqrt 8 : ℝ) ^ 2 = (8 : ℝ) := by
    have hs : (0 : ℝ) ≤ (8 : ℝ) := by norm_num
    exact Real.sq_sqrt hs
  have hcoord :
      ∀ i : Fin 24, (coord e i x) ^ 2 = (1 / 8 : ℝ) * (scaledCoord e i x) ^ 2 := by
    intro i
    have hne : (8 : ℝ) ≠ 0 := by norm_num
    have hsc : (scaledCoord e i x) ^ 2 = (8 : ℝ) * (coord e i x) ^ 2 := by
      calc
        (scaledCoord e i x) ^ 2 = (Real.sqrt 8 : ℝ) ^ 2 * (coord e i x) ^ 2 := by
          simp [scaledCoord, mul_pow]
        _ = (8 : ℝ) * (coord e i x) ^ 2 := by simp [hs8]
    -- reduce to `a = (1/8) * (8*a)`
    rw [hsc]
    field_simp [hne]
  calc
    ‖x‖ ^ 2 = ∑ i : Fin 24, (coord e i x) ^ 2 := norm_sq_eq_sum_coord_sq (e := e) he x
    _ = ∑ i : Fin 24, (1 / 8 : ℝ) * (scaledCoord e i x) ^ 2 :=
          Fintype.sum_congr (fun a => coord e a x ^ 2)
              (fun a => 1 / 8 * scaledCoord e a x ^ 2) hcoord
    _ = (1 / 8 : ℝ) * ∑ i : Fin 24, (scaledCoord e i x) ^ 2 := by
          simp [Finset.mul_sum]

/-- A nonzero binary word has a coordinate equal to `1`. -/
public lemma exists_idx_one_of_ne_zero {c : BinWord 24} (hc : c ≠ 0) :
    ∃ i : Fin 24, c i = 1 := by
  by_contra h
  apply hc
  funext i
  have hi : c i = 0 ∨ c i = 1 := GolayBounds.zmod2_eq_zero_or_eq_one (c i)
  rcases hi with hi | hi
  · simp [hi]
  · exfalso
    exact h ⟨i, hi⟩

lemma cast_div2_zmod2_eq_one_of_eq_two_or_eq_neg_two (z : ℤ) :
    (z = 2 ∨ z = -2) → ((z / 2 : ℤ) : ZMod 2) = 1 := by
  intro hz
  rcases hz with rfl | rfl <;> simp

lemma cast_div2_zmod2_eq_zero_of_eq_zero (z : ℤ) :
    z = 0 → ((z / 2 : ℤ) : ZMod 2) = 0 := by
  intro hz
  subst hz
  simp


end CodeFromLattice

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21
