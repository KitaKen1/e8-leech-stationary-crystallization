-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-13); see SpherePacking/PORTING.txt.
module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Adjoint
import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Harmonic

/-!
# Fischer adjointness for basic operators

This file proves the adjointness of multiplication by variables and partial derivatives on
homogeneous pieces, and packages the corresponding adjointness between the degree-`k+2`
Laplacian and multiplication by `r² = ∑ i, X i ^ 2` (implemented via degree-shifting maps).

## Main statements
* `inner_mulXPk_eq_inner_pderivPk`
-/
namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer
noncomputable section

open scoped BigOperators RealInnerProductSpace

open Finset Finsupp MvPolynomial

local notation "Pk" => Pk

open Harmonic

private def e (i : Var) : Var →₀ ℕ := Finsupp.single i 1

lemma mem_expFinset_add_e {k : ℕ} (i : Var) (d : Var →₀ ℕ) (hd : d ∈ expFinset k) :
    d + e i ∈ expFinset (k + 1) := by
  have hddeg : Finsupp.degree d = k := (mem_expFinset_iff k d).1 hd
  have hdeg :
      Finsupp.degree (d + e i) = Finsupp.degree d + Finsupp.degree (e i) :=
    Finsupp.degree.map_add d (e i)
  have : Finsupp.degree (d + e i) = k + 1 := by
    calc
      Finsupp.degree (d + e i) = Finsupp.degree d + Finsupp.degree (e i) := hdeg
      _ = k + 1 := by simp [hddeg, e, Finsupp.degree_single]
  exact (mem_expFinset_iff (k + 1) (d + e i)).2 this

lemma mem_support_add_e (i : Var) (d : Var →₀ ℕ) : i ∈ (d + e i).support := by
  simp [Finsupp.mem_support_iff, e, Finsupp.add_apply]

lemma add_tsub_e_cancel (i : Var) (d : Var →₀ ℕ) : (d + e i) - e i = d :=
  add_tsub_cancel_right d (e i)

lemma tsub_e_add_cancel {i : Var} {d : Var →₀ ℕ} (hi : i ∈ d.support) :
    (d - e i) + e i = d := by
  have hdi0 : d i ≠ 0 := by simpa [Finsupp.mem_support_iff] using! hi
  simpa [e] using! (Finsupp.sub_add_single_one_cancel (u := d) (i := i) hdi0)

lemma mem_expFinset_tsub_e {k : ℕ} {i : Var} (d : Var →₀ ℕ)
    (hd : d ∈ expFinset (k + 1)) (hi : i ∈ d.support) :
    d - e i ∈ expFinset k := by
  have hddeg : Finsupp.degree d = k + 1 := (mem_expFinset_iff (k + 1) d).1 hd
  -- Use `degree = ∑` and split into `i` and `erase i`.
  have hsumd : (∑ j : Var, d j) = k + 1 := by
    simpa [Finsupp.degree_eq_sum] using! hddeg
  have hdi0 : d i ≠ 0 := by simpa [Finsupp.mem_support_iff] using! hi
  have hle : 1 ≤ d i := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hdi0)
  let rest : ℕ := ((univ : Finset Var).erase i).sum fun j => d j
  have hsum_split : (∑ j : Var, d j) = d i + rest := by
    -- `∑ j, d j = d i + ∑ j ∈ erase i, d j`.
    have hi_univ : i ∈ (univ : Finset Var) := mem_univ i
    -- The `Fintype` sum is definitionaly a sum over `univ`.
    simpa [rest] using!
      (Finset.add_sum_erase (s := (univ : Finset Var)) (f := fun j => d j) (a := i) hi_univ).symm
  have hsum_rest : d i + rest = k + 1 := by
    simpa [hsum_split] using! hsumd
  have hsum_sub :
      (∑ j : Var, (d - e i) j) = k := by
    -- Off `i`, subtraction is zero; at `i`, it is `d i - 1`.
    have hi_univ : i ∈ (univ : Finset Var) := mem_univ i
    have h_on_i : (d - e i) i = d i - 1 := by
      simp [e]
    have h_off :
        ((univ : Finset Var).erase i).sum (fun j => (d - e i) j) = rest := by
      have :
          ((univ : Finset Var).erase i).sum (fun j => (d - e i) j) =
            ((univ : Finset Var).erase i).sum (fun j => d j) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        simp [e, hji]
      simpa [rest] using! this
    have hsplit_sub :
        (∑ j : Var, (d - e i) j) =
          (d - e i) i + ((univ : Finset Var).erase i).sum (fun j => (d - e i) j) :=
      Eq.symm (Finset.add_sum_erase univ (⇑(d - e i)) hi_univ)
    -- Convert `d i + rest = k+1` into `(d i - 1) + rest = k`.
    have : (d i - 1) + rest = k := by
      have hdi : (d i - 1) + 1 = d i := Nat.sub_add_cancel hle
      have hplus : ((d i - 1) + rest) + 1 = k + 1 := by
        calc
          ((d i - 1) + rest) + 1 = ((d i - 1) + 1) + rest := by
            ac_rfl
          _ = d i + rest := by simp [hdi]
          _ = k + 1 := hsum_rest
      exact Nat.add_right_cancel hplus
    -- Assemble.
    calc
      (∑ j : Var, (d - e i) j)
          = (d - e i) i + ((univ : Finset Var).erase i).sum (fun j => (d - e i) j) := hsplit_sub
      _ = (d i - 1) + rest := by
            -- Use the computed `i`-term and the erased-sum identity (avoid unfolding `tsub_apply`).
            rw [h_on_i, h_off]
      _ = k := by simpa using! this
  have : Finsupp.degree (d - e i) = k := by
    simpa [Finsupp.degree_eq_sum] using! hsum_sub
  exact (mem_expFinset_iff k (d - e i)).2 this

lemma multiFactorial_eq_prod_univ (d : Var →₀ ℕ) :
    multiFactorial d = (univ : Finset Var).prod (fun j => Nat.factorial (d j)) := by
  unfold multiFactorial
  have hs : d.support ⊆ (univ : Finset Var) := by
    intro j hj; simp
  -- Outside the support, `d j = 0` and `0! = 1`.
  simpa using! (Finset.prod_subset hs (by
    simp_all))

lemma multiFactorial_add_e (i : Var) (d : Var →₀ ℕ) :
    multiFactorial (d + e i) = (d i + 1) * multiFactorial d := by
  have hi : i ∈ (univ : Finset Var) := mem_univ i
  rw [multiFactorial_eq_prod_univ (d := d + e i), multiFactorial_eq_prod_univ (d := d)]
  rw [← Finset.mul_prod_erase (s := (univ : Finset Var))
    (f := fun j => Nat.factorial ((d + e i) j)) (a := i) hi]
  rw [← Finset.mul_prod_erase (s := (univ : Finset Var))
    (f := fun j => Nat.factorial (d j)) (a := i) hi]
  have herase :
      ((univ : Finset Var).erase i).prod (fun j => Nat.factorial ((d + e i) j)) =
        ((univ : Finset Var).erase i).prod (fun j => Nat.factorial (d j)) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [e, Finsupp.add_apply, hji]
  have hfacI : Nat.factorial ((d + e i) i) = (d i + 1) * Nat.factorial (d i) := by
    simp [e, Finsupp.add_apply, Nat.factorial_succ]
  rw [herase, hfacI]
  ac_rfl

/-- Adjointness: multiplication by `X i` is adjoint to `pderiv i` (between homogeneous pieces). -/
public lemma inner_mulXPk_eq_inner_pderivPk (k : ℕ) (i : Var) (p : Pk k) (q : Pk (k + 1)) :
    Fischer.inner (k + 1) (mulXPk (k := k) i p) q =
      Fischer.inner k p (pderivPk (k := k) i q) := by
  -- Rewrite the LHS sum by discarding the `d` with `i ∉ d.support` (the coefficient vanishes).
  have hL :
      (expFinset (k + 1)).sum (fun d =>
          ((multiFactorial d : ℕ) : ℝ) * coeff d (mulXPk (k := k) i p).1 * coeff d q.1) =
        ((expFinset (k + 1)).filter (fun d => i ∈ d.support)).sum (fun d =>
          ((multiFactorial d : ℕ) : ℝ) * coeff d (mulXPk (k := k) i p).1 * coeff d q.1) := by
    -- Use `sum_filter_add_sum_filter_not` and show the complement sum is `0`.
    have hzero :
        ((expFinset (k + 1)).filter (fun d => d i = 0)).sum (fun d =>
          ((multiFactorial d : ℕ) : ℝ) * coeff d (mulXPk (k := k) i p).1 * coeff d q.1) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro d hd
      have hdi0 : d i = 0 := (Finset.mem_filter.1 hd).2
      have hd' : i ∉ d.support := by
        exact Finsupp.notMem_support_iff.mpr hdi0
      have hcoeff : coeff d (mulXPk (k := k) i p).1 = 0 := by
        -- Unfold `mulXPk` just enough to see a coefficient of `X i * p`.
        -- `coeff_X_mul'` makes it `0` when `i ∉ support d`.
        simp [mulXPk, LinearMap.codRestrict, LinearMap.comp_apply, MvPolynomial.coeff_X_mul', hd']
      simp [hcoeff]
    -- Combine the filtered sums and cancel the zero complement.
    have hsplit :=
      (Finset.sum_filter_add_sum_filter_not (s := expFinset (k + 1))
        (p := fun d : Var →₀ ℕ => i ∈ d.support)
        (f := fun d =>
          ((multiFactorial d : ℕ) : ℝ) * coeff d (mulXPk (k := k) i p).1 * coeff d q.1)).symm
    -- `hsplit : sum = sum(filter) + sum(filter not)`.
    calc
      (expFinset (k + 1)).sum (fun d =>
            ((multiFactorial d : ℕ) : ℝ) * coeff d (mulXPk (k := k) i p).1 * coeff d q.1)
          =
          ((expFinset (k + 1)).filter (fun d => i ∈ d.support)).sum (fun d =>
              ((multiFactorial d : ℕ) : ℝ) * coeff d (mulXPk (k := k) i p).1 * coeff d q.1) +
            ((expFinset (k + 1)).filter (fun d => d i = 0)).sum (fun d =>
              ((multiFactorial d : ℕ) : ℝ) * coeff d (mulXPk (k := k) i p).1 * coeff d q.1) := by
            -- Rewrite the complement predicate `¬ i ∈ d.support` as `d i = 0`.
            -- (This is the only place we use that `Var` is finite.)
            -- `simp` is safe here: it only changes the filter predicate.
            simpa [Finsupp.mem_support_iff] using! hsplit
      _ = ((expFinset (k + 1)).filter (fun d => i ∈ d.support)).sum (fun d =>
              ((multiFactorial d : ℕ) : ℝ) * coeff d (mulXPk (k := k) i p).1 * coeff d q.1) := by
            simp [hzero]
  -- Reindex the filtered sum using `d ↦ d - e i` and `d ↦ d + e i`.
  let S : Finset (Var →₀ ℕ) := (expFinset (k + 1)).filter (fun d => i ∈ d.support)
  have hreindex :
      S.sum (fun d =>
          ((multiFactorial d : ℕ) : ℝ) * coeff d (mulXPk (k := k) i p).1 * coeff d q.1) =
        (expFinset k).sum (fun d =>
          ((multiFactorial (d + e i) : ℕ) : ℝ) *
            coeff (d + e i) (mulXPk (k := k) i p).1 * coeff (d + e i) q.1) := by
    -- Prove the reverse equality with `sum_bij`, then symmetrize.
    have h' :
        (expFinset k).sum (fun d =>
            ((multiFactorial (d + e i) : ℕ) : ℝ) *
              coeff (d + e i) (mulXPk (k := k) i p).1 * coeff (d + e i) q.1) =
          S.sum (fun d =>
            ((multiFactorial d : ℕ) : ℝ) * coeff d (mulXPk (k := k) i p).1 * coeff d q.1) := by
      refine Finset.sum_bij (s := expFinset k) (t := S)
        (i := fun d _hd => d + e i)
        (hi := fun d hd => by
          refine Finset.mem_filter.2 ?_
          constructor
          · exact mem_expFinset_add_e (k := k) i d hd
          · exact mem_support_add_e (i := i) (d := d))
        (i_inj := fun d₁ _ d₂ _ h => by
          -- Injectivity of `d ↦ d + e i`.
          have : d₁ + e i = d₂ + e i := h
          ext j
          have := congrArg (fun t : Var →₀ ℕ => t j) this
          simpa [Finsupp.add_apply] using! this)
        (i_surj := fun b hb => by
          -- Surjectivity onto `S` using `b - e i`.
          refine ⟨b - e i, ?_, ?_⟩
          · have hb_exp : b ∈ expFinset (k + 1) := (Finset.mem_filter.1 hb).1
            have hb_sup : i ∈ b.support := (Finset.mem_filter.1 hb).2
            exact mem_expFinset_tsub_e (k := k) b hb_exp hb_sup
          · have hb_sup : i ∈ b.support := (Finset.mem_filter.1 hb).2
            simpa using! (tsub_e_add_cancel (i := i) (d := b) hb_sup))
        (h := fun d hd => by rfl)
    exact h'.symm
  -- Helper unfoldings for the degree-shifting maps.
  have mulXPk_coe (d : Pk k) : (mulXPk (k := k) i d).1 = (X i : Poly) * d.1 := by
    rfl
  have pderivPk_coe (d : Pk (k + 1)) : (pderivPk (k := k) i d).1 = MvPolynomial.pderiv i d.1 := by
    rfl
  -- Replace the multiplication coefficient at `d + e i`.
  have hcoeffX (d : Var →₀ ℕ) :
      coeff (d + e i) (mulXPk (k := k) i p).1 = coeff d p.1 := by
    -- `coeff_X_mul` is the shift lemma for multiplication by `X i`.
    -- Rewrite `d + e i` as `e i + d` to match the lemma.
    simpa [mulXPk_coe (d := p), e, add_comm, add_left_comm, add_assoc] using!
      (MvPolynomial.coeff_X_mul (m := d) (s := i) (p := p.1))
  -- Replace the derivative coefficient.
  have hcoeffD (d : Var →₀ ℕ) :
      coeff d (pderivPk (k := k) i q).1 =
        ((d i + 1 : ℕ) : ℝ) * coeff (d + e i) q.1 := by
    simpa [pderivPk_coe (d := q), e] using! (coeff_pderiv (i := i) (p := q.1) (d := d))
  -- Now compute.
  unfold Fischer.inner
  -- Move to the reindexed form on the LHS.
  calc
    (expFinset (k + 1)).sum (fun d =>
          ((multiFactorial d : ℕ) : ℝ) * coeff d (mulXPk (k := k) i p).1 * coeff d q.1)
        = S.sum (fun d =>
            ((multiFactorial d : ℕ) : ℝ) * coeff d (mulXPk (k := k) i p).1 * coeff d q.1) := by
            simpa [S] using! hL
    _ = (expFinset k).sum (fun d =>
          ((multiFactorial (d + e i) : ℕ) : ℝ) *
            coeff (d + e i) (mulXPk (k := k) i p).1 * coeff (d + e i) q.1) := hreindex
    _ = (expFinset k).sum (fun d =>
          ((multiFactorial d : ℕ) : ℝ) * coeff d p.1 * coeff d (pderivPk (k := k) i q).1) := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          have hfac : multiFactorial (d + e i) = (d i + 1) * multiFactorial d :=
            multiFactorial_add_e (i := i) (d := d)
          simp [hfac, hcoeffX d, hcoeffD d, mul_assoc, mul_left_comm, mul_comm]

end

end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer
