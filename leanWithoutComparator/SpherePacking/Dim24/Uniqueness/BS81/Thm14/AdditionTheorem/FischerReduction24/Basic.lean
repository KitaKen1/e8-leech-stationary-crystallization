-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.FischerDecompositionFixed
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.DoubleSumsToHarmonics24
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.MeanZeroHarmonics24.Basic
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.AvgLemmas24
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.EvalLemmas24
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.FischerReduction24.Deg1Harm
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.FischerReduction24.Deg0Const
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.FischerReduction24.MulR2Pointwise
import SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.FischerReduction24.MulR2SphereAvg

/-!
# Fischer decomposition reduction for the design bridge

Goal (used in `DesignEquivBridge24.lean`):

If `C ⊆ Ω₂₄` is a harmonic design up to degree `t`, then for every homogeneous polynomial `p` of
degree `k ≤ t`, the finite average of `p` over `C` equals the sphere average.

Blueprint:
* use Fischer decomposition on homogeneous pieces:
  `Pk (k+2) = Harm (k+2) ⊕ range (mulR2Pk k)`;
* on the unit sphere, `mulR2Pk` corresponds to multiplying by `r² = ‖x‖² = 1`, hence does not change
  the restriction;
* induct on `k` in steps of `2`, peeling off harmonic pieces whose averages are `0`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24

noncomputable section

open scoped BigOperators RealInnerProductSpace

open Uniqueness.BS81.LP

open Uniqueness.BS81.LP.Gegenbauer24.PSD

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
### Fischer decomposition on homogeneous pieces

We work in the homogeneous submodule `Fischer.Pk k`.
-/

theorem exists_add_harm_add_mulR2Pk (k : ℕ) (p : Fischer.Pk (k + 2)) :
    ∃ h : Harmonic.Harm (k + 2), ∃ q : Fischer.Pk k,
      (p : Fischer.Pk (k + 2)) = (h : Fischer.Pk (k + 2)) + (Fischer.mulR2Pk (k := k) q) := by
  -- This is a direct consequence of `isCompl_Harm_range_mulR2Pk`.
  have hCompl := Fischer.isCompl_Harm_range_mulR2Pk (k := k)
  -- Decompose `p` as `h + r²*q` using the `sup = ⊤` characterization.
  have hpSup :
      (p : Fischer.Pk (k + 2)) ∈
        (Harmonic.Harm (k + 2) ⊔ LinearMap.range (Fischer.mulR2Pk (k := k))) := by
    -- `sup = ⊤`, so this is automatic.
    simp [hCompl.sup_eq_top]
  rcases (Submodule.mem_sup).1 hpSup with ⟨h, hh, r, hr, hhr⟩
  rcases hr with ⟨q, rfl⟩
  refine ⟨⟨h, hh⟩, q, ?_⟩
  simpa using! hhr.symm

/-!
### Restriction of `r²`-multiplication to the unit sphere

On `Ω₂₄`, we have `r²(x) = ∑ xᵢ² = ‖x‖² = 1`, so evaluation of `mulR2Pk q` should coincide with
evaluation of `q`. We record this both pointwise and at the level of averages.
-/

namespace FischerReduction24Steps

/-- On the unit sphere, averaging `mulR2Pk q` agrees with averaging `q` (step `k → k+2`). -/
public theorem finsetAvg_eval_mulR2Pk_eq_finsetAvg_eval_step
    (k : ℕ) (C : Finset ℝ²⁴) (hC : ∀ u ∈ C, ‖u‖ = (1 : ℝ)) (q : Fischer.Pk k) :
    finsetAvg C (fun x : ℝ²⁴ => evalPk24 (k := k + 2) (y := x) (Fischer.mulR2Pk (k := k) q)) =
      finsetAvg C (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) q) := by
  -- Reduce to equality of the corresponding sums by pointwise evaluation on the unit sphere.
  unfold finsetAvg
  congr 1
  refine Finset.sum_congr rfl ?_
  exact fun x a => evalPk24_mulR2Pk_of_norm_eq_one_step k q x (hC x a)

end FischerReduction24Steps

/-!
### Harmonic pieces have the correct averages
-/

theorem finsetAvg_eval_harm_eq_zero_of_isHarmonicDesign24
    (t : ℕ) (C : Finset ℝ²⁴) (hH : IsHarmonicDesign24 t C)
    (k : ℕ) (hk1 : 1 ≤ k) (hkt : k ≤ t)
    (h : Harmonic.Harm k) :
    finsetAvg C (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) (h : Fischer.Pk k)) = 0 := by
  -- Unfold `finsetAvg` and use the definition of `IsHarmonicDesign24` (which is a sum condition).
  have hsum : C.sum (fun u => evalPk24 (k := k) (y := u) (h : Fischer.Pk k)) = 0 :=
    hH k hk1 hkt h
  -- Convert the sum condition into an average condition.
  unfold finsetAvg
  simp [hsum]

theorem sphereAvg24_eval_harm_eq_zero_of_degree_pos
    (k : ℕ) (hk : 1 ≤ k) (h : Harmonic.Harm k) :
    sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) (h : Fischer.Pk k)) = 0 :=
  Bridge24.sphereAvg24_harmonic_degree_pos_eq_zero (k := k) hk h

/-!
### Base cases

Degree `0` is constant; degree `1` is harmonic (Laplacian lowers degree by `2`).
-/

theorem mem_Harm_of_degree_one (p : Fischer.Pk 1) : p ∈ Harmonic.Harm 1 := by
  -- Degree `1` is harmonic since the Laplacian lowers degree by `2`.
  -- Concretely, all second partial derivatives of a homogeneous degree-`1` polynomial are `0`.
  simpa using! (FischerReduction24Steps.mem_Harm_of_degree_one_step (p := p))

theorem finsetAvg_eq_sphereAvg_of_degree_one
    (t : ℕ) (C : Finset ℝ²⁴) (hH : IsHarmonicDesign24 t C)
    (ht : 1 ≤ t) (p : Fischer.Pk 1) :
    finsetAvg C (fun x : ℝ²⁴ => evalPk24 (k := 1) (y := x) p) =
      sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := 1) (y := x) p) := by
  -- Both sides are `0`: finite average by `IsHarmonicDesign24`, sphere average by mean-zero.
  have hpH : p ∈ Harmonic.Harm 1 := mem_Harm_of_degree_one (p := p)
  let h : Harmonic.Harm 1 := ⟨p, hpH⟩
  have hfin : finsetAvg C (fun x : ℝ²⁴ => evalPk24 (k := 1) (y := x) (h : Fischer.Pk 1)) = 0 :=
    finsetAvg_eval_harm_eq_zero_of_isHarmonicDesign24 (t := t) (C := C) hH (k := 1) (by simp)
      (by simpa using! ht) h
  have hsph : sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := 1) (y := x) (h : Fischer.Pk 1)) = 0 :=
    sphereAvg24_eval_harm_eq_zero_of_degree_pos (k := 1) (by simp) h
  -- The coercions are definitional: `h.1 = p`.
  simpa [h] using! (hfin.trans hsph.symm)

/-!
### Main reduction lemma for homogeneous pieces `Pk k`
-/

/-- Main Fischer-induction lemma: harmonic moments give `finsetAvg = sphereAvg24` on `Pk k`. -/
public theorem finsetAvg_eq_sphereAvg_of_isHarmonicDesign24_Pk
    (t : ℕ) (C : Finset ℝ²⁴) (hC : ∀ u ∈ C, ‖u‖ = (1 : ℝ))
    (hH : IsHarmonicDesign24 t C) (hCne : C.Nonempty) :
    ∀ k : ℕ, k ≤ t → ∀ p : Fischer.Pk k,
      finsetAvg C (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) p) =
        sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) p) := by
  -- Two-step induction on `k` (step `k → k+2` via Fischer decomposition).
  intro k hk p
  induction k using Nat.twoStepInduction with
  | zero =>
      exact FischerReduction24Steps.finsetAvg_eq_sphereAvg_of_degree_zero_step C hCne p
  | one =>
      have ht : (1 : ℕ) ≤ t := by simpa using! hk
      simpa using! finsetAvg_eq_sphereAvg_of_degree_one (t := t) (C := C) hH ht (p := p)
  | more k ihk ihk1 =>
      have hk2 : k + 2 ≤ t := hk
      rcases exists_add_harm_add_mulR2Pk (k := k) (p := p) with ⟨h, q, hpq⟩
      have hkpos : 1 ≤ k + 2 := Nat.succ_le_succ (Nat.zero_le (k + 1))
      have hfin_h :
          finsetAvg C (fun x : ℝ²⁴ => evalPk24 (k := k + 2) (y := x) (h : Fischer.Pk _)) = 0 :=
        finsetAvg_eval_harm_eq_zero_of_isHarmonicDesign24 (t := t) (C := C) hH (k := k + 2) hkpos
          hk2 h
      have hsph_h :
          sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := k + 2) (y := x) (h : Fischer.Pk _)) = 0 :=
        sphereAvg24_eval_harm_eq_zero_of_degree_pos (k := k + 2) hkpos h
      have hk_le_t : k ≤ t := Nat.le_trans (Nat.le_add_right k 2) hk2
      have ihq :
          finsetAvg C (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) q) =
            sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) q) :=
        ihk (p := q) hk_le_t
      -- Split `p` using `hpq`, kill the harmonic part, and reduce `r²*q` to `q` on the unit sphere.
      have hfin_decomp :
          finsetAvg C (fun x : ℝ²⁴ => evalPk24 (k := k + 2) (y := x) p) =
            finsetAvg C (fun x : ℝ²⁴ => evalPk24 (k := k + 2) (y := x) (h : Fischer.Pk _)) +
              finsetAvg C (fun x : ℝ²⁴ =>
                evalPk24 (k := k + 2) (y := x) (Fischer.mulR2Pk (k := k) q)) := by
        -- rewrite `p` as `h + r²*q`, then use `finsetAvg_evalPk24_add`.
        simpa [hpq] using!
          (finsetAvg_evalPk24_add (k := k + 2) (C := C) (p := (h : Fischer.Pk _))
            (q := Fischer.mulR2Pk (k := k) q))
      have hsph_decomp :
          sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := k + 2) (y := x) p) =
            sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := k + 2) (y := x) (h : Fischer.Pk _)) +
              sphereAvg24 (fun x : ℝ²⁴ =>
                evalPk24 (k := k + 2) (y := x) (Fischer.mulR2Pk (k := k) q)) := by
        simpa [hpq] using!
          (sphereAvg24_evalPk24_add (k := k + 2) (p := (h : Fischer.Pk _))
            (q := Fischer.mulR2Pk (k := k) q))
      have hfin_reduce :
          finsetAvg C (fun x : ℝ²⁴ => evalPk24 (k := k + 2) (y := x) p) =
            finsetAvg C (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) q) := by
        -- harmonic part averages to `0`; `r²*q` average reduces to `q`.
        rw [hfin_decomp]
        simp [hfin_h,
          FischerReduction24Steps.finsetAvg_eval_mulR2Pk_eq_finsetAvg_eval_step
            (k := k) (C := C) hC q]
      have hsph_reduce :
          sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := k + 2) (y := x) p) =
            sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) q) := by
        -- same reduction on the sphere.
        rw [hsph_decomp]
        simp [hsph_h,
          FischerReduction24Steps.sphereAvg24_eval_mulR2Pk_eq_sphereAvg24_eval_step
            (k := k) (q := q)]
      -- Conclude by induction on `q`.
      calc
        finsetAvg C (fun x : ℝ²⁴ => evalPk24 (k := k + 2) (y := x) p)
            = finsetAvg C (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) q) := hfin_reduce
        _ = sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := k) (y := x) q) := ihq
        _ = sphereAvg24 (fun x : ℝ²⁴ => evalPk24 (k := k + 2) (y := x) p) := by
            simpa using! hsph_reduce.symm

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24
