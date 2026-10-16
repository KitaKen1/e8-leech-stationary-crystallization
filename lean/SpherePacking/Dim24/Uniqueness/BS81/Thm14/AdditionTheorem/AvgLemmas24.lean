-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.Defs
public import SpherePacking.Dim24.Uniqueness.BS81.Thm14.Design.SphereAvgMoments
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Averaging lemmas for `finsetAvg` and `sphereAvg24`

This file records small algebraic lemmas used in the BS81 design bridge, mostly rewriting between
averages and sums and distributing `finsetAvg` and `sphereAvg24` over addition and scalar
multiplication.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24

noncomputable section

open scoped BigOperators
open MeasureTheory

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- The average of the zero function is `0`. -/
public lemma finsetAvg_zero (C : Finset ℝ²⁴) :
    finsetAvg C (fun _ : ℝ²⁴ => (0 : ℝ)) = 0 := by
  simp [finsetAvg]

/-- `finsetAvg` distributes over addition. -/
public lemma finsetAvg_add (C : Finset ℝ²⁴) (f g : ℝ²⁴ → ℝ) :
    finsetAvg C (fun x => f x + g x) = finsetAvg C f + finsetAvg C g := by
  unfold finsetAvg
  simp [Finset.sum_add_distrib, mul_add]

/-- `finsetAvg` commutes with scalar multiplication. -/
public lemma finsetAvg_smul (C : Finset ℝ²⁴) (a : ℝ) (f : ℝ²⁴ → ℝ) :
    finsetAvg C (fun x => a * f x) = a * finsetAvg C f := by
  unfold finsetAvg
  have hsum : C.sum (fun x => a * f x) = a * C.sum f := by
    simpa using! (Finset.mul_sum a (f := fun x => f x) (s := C)).symm
  -- normalize both sides
  simp [hsum, mul_assoc, mul_comm]

open scoped Classical in
/-- `finsetAvg` commutes with finite sums. -/
public lemma finsetAvg_finset_sum {ι : Type*} (Cfin : Finset ℝ²⁴) (s : Finset ι)
    (f : ι → ℝ²⁴ → ℝ) :
    finsetAvg Cfin (fun x => s.sum (fun a => f a x)) = s.sum (fun a => finsetAvg Cfin (f a)) := by
  refine Finset.induction_on s ?_ ?_
  · simp [finsetAvg]
  · intro a s ha hs
    simp [Finset.sum_insert, ha, finsetAvg_add, hs]

open scoped Classical in
/-- `finsetAvg` commutes with double finite sums. -/
public lemma finsetAvg_finset_sum₂ {ι κ : Type*} (Cfin : Finset ℝ²⁴) (s : Finset ι) (t : Finset κ)
    (f : ι → κ → ℝ²⁴ → ℝ) :
    finsetAvg Cfin (fun x => s.sum (fun i => t.sum (fun j => f i j x))) =
      s.sum (fun i => t.sum (fun j => finsetAvg Cfin (f i j))) := by
  calc
    finsetAvg Cfin (fun x => s.sum (fun i => t.sum (fun j => f i j x))) =
        s.sum (fun i => finsetAvg Cfin (fun x => t.sum (fun j => f i j x))) :=
          finsetAvg_finset_sum Cfin s fun a x => ∑ j ∈ t, f a j x
    _ = s.sum (fun i => t.sum (fun j => finsetAvg Cfin (f i j))) := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          simpa using! (finsetAvg_finset_sum (Cfin := Cfin) (s := t) (f := fun j : κ => f i j))

/-- Rewrite a sum as `card * finsetAvg`. -/
public lemma sum_eq_card_mul_finsetAvg (C : Finset ℝ²⁴) (f : ℝ²⁴ → ℝ) :
    C.sum f = (C.card : ℝ) * finsetAvg C f := by
  by_cases h : (C.card : ℝ) = 0
  · have hcard : C.card = 0 := by exact_mod_cast h
    have hC : C = ∅ := Finset.card_eq_zero.mp hcard
    subst hC
    simp [finsetAvg]
  · -- multiply out the definition and use `mul_inv_cancel`.
    simp [finsetAvg, h]

/-- If `finsetAvg C f = 0`, then `C.sum f = 0`. -/
public lemma sum_eq_zero_of_finsetAvg_eq_zero (C : Finset ℝ²⁴) (f : ℝ²⁴ → ℝ)
    (havg : finsetAvg C f = 0) : C.sum f = 0 := by
  -- `C.sum f = card * avg`, so if `avg = 0` then the sum is `0`.
  simpa [havg] using! (sum_eq_card_mul_finsetAvg (C := C) (f := f))

/-!
`sphereAvg24` is defined via a normalized integral, so its linearity depends on integral linearity.
We keep the key manipulation lemmas as separate statements here.

These are all standard and provable; we keep them here to keep later bridge files small.
-/

/-- The sphere average of the zero function is `0`. -/
public lemma sphereAvg24_zero : sphereAvg24 (fun _ : ℝ²⁴ => (0 : ℝ)) = 0 := by
  simp [sphereAvg24]

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm14.AdditionTheorem.Bridge24
