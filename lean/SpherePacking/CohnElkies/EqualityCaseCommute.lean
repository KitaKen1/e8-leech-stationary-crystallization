-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
import SpherePacking.CohnElkies.LPBoundSwapSums
import SpherePacking.CohnElkies.LPBoundSummability
public import SpherePacking.CohnElkies.LPBoundCalcLemmas

/-!
# Cohn-Elkies equality case: a commutation identity

This file proves a Poisson summation / commutation identity for periodic packings, rewriting a real
triple sum over centers and lattice translates as a Fourier series on the dual lattice weighted by
`‖expSum‖^2`.

This is the key commutation step used to analyze the equality case of the Cohn-Elkies linear
programming bound.
-/
open scoped FourierTransform ENNReal SchwartzMap
open SpherePacking Metric BigOperators Pointwise Filter MeasureTheory Complex Real ZSpan Bornology
  Summable Module

namespace SpherePacking.CohnElkies

local notation "conj" => starRingEnd ℂ

variable {d : ℕ}
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)}
variable {P : PeriodicSpherePacking d}
variable {D : Set (EuclideanSpace ℝ (Fin d))}

/--
Rewrite the real triple sum appearing in the equality case as a dual-lattice sum weighted by
`‖expSum‖^2`.
-/
public lemma tripleSum_re_eq_one_div_covol_mul_tsum_fourier_re_mul_norm_expSum_sq
    (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), (↑((𝓕 f x).re) : ℂ) = (𝓕 f x))
    (hD_isBounded : Bornology.IsBounded D) (hd : 0 < d) :
    (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
        (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re)
      =
      (1 / ZLattice.covolume P.lattice volume) *
        ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
          ((𝓕 f) (m : EuclideanSpace ℝ (Fin d))).re * (norm (expSum P D m) ^ 2) := by
  -- Replace the real triple sum by the real part of the complex triple sum.
  have hRe :
      (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
          (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re)
        =
        (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
          f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re := by
    haveI : Finite (↑(P.centers ∩ D)) :=
      finite_centers_inter_of_isBounded P D hD_isBounded hd
    rw [re_tsum Summable.of_finite]
    refine tsum_congr ?_
    intro x
    rw [re_tsum Summable.of_finite]
    refine tsum_congr ?_
    intro y
    rw [re_tsum]
    -- Summability of the lattice translate follows from Schwartz decay.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using!
      (SpherePacking.CohnElkies.LPBoundSummability.summable_lattice_translate
        (Λ := P.lattice) (f := f)
        (a := ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)))))
  -- Follow the end of `LPBound.lean`'s `calc_steps_part1`.
  calc
    (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
        (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re)
        =
        (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
          f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
            (ℓ : EuclideanSpace ℝ (Fin d)))).re := hRe
    _ =
        (∑' x : ↑(P.centers ∩ D),
          ∑' y : ↑(P.centers ∩ D), (1 / ZLattice.covolume P.lattice volume) *
            ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, (𝓕 f m) *
              exp (2 * π * I *
                ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                  (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])).re := by
          congr! 5 with x y
          exact SchwartzMap.PoissonSummation_Lattices P.lattice f _
    _ =
        ((1 / ZLattice.covolume P.lattice volume) *
            ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
              (𝓕 f m).re *
                (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)),
                  exp (2 * π * I *
                    ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                      (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))).re := by
          exact calc_steps_swap_sums f hRealFourier P hD_isBounded hd
    _ =
        (1 / ZLattice.covolume P.lattice volume) *
          ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
            ((𝓕 f) (m : EuclideanSpace ℝ (Fin d))).re * (norm (expSum P D m) ^ 2) := by
          -- This is copied (nearly verbatim) from `LPBound.lean`, rewriting the `x,y` sum to
          -- `‖expSum‖^2` and turning the whole `tsum` into a real series.
          let A : SchwartzMap.dualLattice (d := d) P.lattice → ℂ := expSum P D
          -- Rewrite the `x,y` sum as `A m * conj (A m)`.
          have hxy :
              ∀ m : SchwartzMap.dualLattice (d := d) P.lattice,
                (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)),
                    exp (2 * π * I *
                      ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                        (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))
                  =
                  A m * conj (A m) := by
            intro m
            -- Factor the `x,y` sum.
            have :
                (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)),
                    exp (2 * π * I *
                      ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                        (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))
                  =
                  (∑' x : ↑(P.centers ∩ D),
                      exp (2 * π * I *
                        ⟪(x : EuclideanSpace ℝ (Fin d)),
                          (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) *
                    (∑' y : ↑(P.centers ∩ D),
                      exp (-(2 * π * I *
                        ⟪(y : EuclideanSpace ℝ (Fin d)),
                          (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))) := by
              -- This matches the rewrite used in `LPBound.lean`, but we do it pointwise under the
              -- `tsum` so rewriting works under binders.
              have hterm :
                  ∀ (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)),
                    exp (2 * π * I *
                        ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                          (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])
                      =
                      exp (2 * π * I *
                          ⟪(x : EuclideanSpace ℝ (Fin d)),
                            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) *
                        exp (2 * π * I *
                          ⟪-(y : EuclideanSpace ℝ (Fin d)),
                            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) := by
                intro x y
                simp only [sub_eq_neg_add, mul_comm]
                simp only [WithLp.ofLp_add]
                rw [RCLike.wInner_add_left]
                simp only [ofReal_add]
                rw [mul_add, Complex.exp_add, mul_comm]
                -- Goal is now definitional.
              have hrewrite :
                  (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)),
                      exp (2 * π * I *
                        ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                          (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))
                    =
                    ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)),
                      exp (2 * π * I *
                          ⟪(x : EuclideanSpace ℝ (Fin d)),
                            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) *
                        exp (2 * π * I *
                          ⟪-(y : EuclideanSpace ℝ (Fin d)),
                            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) := tsum_congr₂ hterm
              calc
                (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)),
                    exp (2 * π * I *
                      ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
                        (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))
                    =
                    ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)),
                      exp (2 * π * I *
                          ⟪(x : EuclideanSpace ℝ (Fin d)),
                            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) *
                        exp (2 * π * I *
                          ⟪-(y : EuclideanSpace ℝ (Fin d)),
                            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) := hrewrite
                _ =
                    (∑' x : ↑(P.centers ∩ D),
                        exp (2 * π * I *
                          ⟪(x : EuclideanSpace ℝ (Fin d)),
                            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) *
                      ∑' y : ↑(P.centers ∩ D),
                        exp (2 * π * I *
                          ⟪-(y : EuclideanSpace ℝ (Fin d)),
                            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) := by
                    simp_rw [mul_assoc, ← tsum_mul_right, ← tsum_mul_left]
                _ =
                    (∑' x : ↑(P.centers ∩ D),
                        exp (2 * π * I *
                          ⟪(x : EuclideanSpace ℝ (Fin d)),
                            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) *
                      ∑' y : ↑(P.centers ∩ D),
                        exp (-(2 * π * I *
                          ⟪(y : EuclideanSpace ℝ (Fin d)),
                            (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) := by
                    have hy :
                        (∑' y : ↑(P.centers ∩ D),
                            exp (2 * π * I *
                              ⟪-(y : EuclideanSpace ℝ (Fin d)),
                                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]))
                          =
                          ∑' y : ↑(P.centers ∩ D),
                            exp (-(2 * π * I *
                              ⟪(y : EuclideanSpace ℝ (Fin d)),
                                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) := by
                      refine tsum_congr ?_
                      intro y
                      simp [WithLp.ofLp_neg, RCLike.wInner_neg_left, ofReal_neg, mul_neg]
                    have :=
                      congrArg (fun t : ℂ =>
                        (∑' x : ↑(P.centers ∩ D),
                            exp (2 * π * I *
                              ⟪(x : EuclideanSpace ℝ (Fin d)),
                                (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) * t) hy
                    exact this
            -- Identify the second factor as a conjugate.
            have hconj :
                (∑' y : ↑(P.centers ∩ D),
                    exp (-(2 * π * I *
                      ⟪(y : EuclideanSpace ℝ (Fin d)),
                        (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])))
                  =
                  conj (∑' y : ↑(P.centers ∩ D),
                    exp (2 * π * I *
                      ⟪(y : EuclideanSpace ℝ (Fin d)),
                        (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])) := by
              simp_rw [conj_tsum]
              refine tsum_congr ?_
              intro y
              exact Complex.exp_neg_real_I_eq_conj (x := (y : EuclideanSpace ℝ (Fin d)))
                (m := (m : EuclideanSpace ℝ (Fin d)))
            simpa [A, expSum, hconj] using! this
          -- Reduce termwise to a real series using `mul_conj'`.
          let r : SchwartzMap.dualLattice (d := d) P.lattice → ℝ := fun m =>
            ((𝓕 f) (m : EuclideanSpace ℝ (Fin d))).re * (‖A m‖ ^ 2)
          have hterm :
              ∀ m : SchwartzMap.dualLattice (d := d) P.lattice,
                ((𝓕 f m).re : ℂ) * A m * conj (A m) = (r m : ℂ) := by
            intro m
            have hmul : A m * conj (A m) = (‖A m‖ ^ 2 : ℂ) := by
              simpa using! (Complex.mul_conj' (A m))
            simp [r, mul_assoc, hmul]
          have hsum :
              ((1 / ZLattice.covolume P.lattice volume) *
                    ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
                      ((𝓕 f m).re : ℂ) * A m * conj (A m)).re
                =
                (1 / ZLattice.covolume P.lattice volume) *
                  ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, r m := by
            -- Rewrite the inner series using `hterm`, then convert to an `ofReal` series.
            have hsum' :
                (∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
                    ((𝓕 f m).re : ℂ) * A m * conj (A m))
                  =
                  ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, (r m : ℂ) :=
              tsum_congr fun m => hterm m
            have hcongr :
                ((1 / ZLattice.covolume P.lattice volume : ℂ) *
                    ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
                      ((𝓕 f m).re : ℂ) * A m * conj (A m)).re
                  =
                  ((1 / ZLattice.covolume P.lattice volume : ℂ) *
                    ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, (r m : ℂ)).re := by
              -- Push equality through multiplication and `re`.
              have :=
                congrArg (fun t : ℂ =>
                  ((1 / ZLattice.covolume P.lattice volume : ℂ) * t).re) hsum'
              simpa [mul_assoc] using! this
            have hofReal :
                (∑' m : SchwartzMap.dualLattice (d := d) P.lattice, (r m : ℂ))
                  =
                  ((∑' m : SchwartzMap.dualLattice (d := d) P.lattice, r m : ℝ) : ℂ) := by
              exact Eq.symm (ofReal_tsum r)
            -- Finish by simplifying real parts of a product of `ofReal`'s.
            calc
              ((1 / ZLattice.covolume P.lattice volume) *
                    ∑' m : SchwartzMap.dualLattice (d := d) P.lattice,
                      ((𝓕 f m).re : ℂ) * A m * conj (A m)).re
                  =
                  ((1 / ZLattice.covolume P.lattice volume : ℂ) *
                    ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, (r m : ℂ)).re := by
                    simpa using! hcongr
              _ =
                  ((1 / ZLattice.covolume P.lattice volume : ℂ) *
                    ((∑' m : SchwartzMap.dualLattice (d := d) P.lattice, r m : ℝ) : ℂ)).re := by
                    simp [hofReal]
              _ =
                  (1 / ZLattice.covolume P.lattice volume) *
                    ∑' m : SchwartzMap.dualLattice (d := d) P.lattice, r m := by
                    simp
          -- Rewrite the `x,y` sum using `hxy`, then apply `hsum` and unfold `r`.
          simp_rw [hxy, ← mul_assoc]
          exact hsum
  rfl

end SpherePacking.CohnElkies
