import E8Leech.LatticeDistance
import Mathlib.Topology.Bases

/-!
# A countable family approximating every isometry on finite observations

Encode inverse isometries by their values on a dense sequence in the ambient space.
The induced topology is second countable, so it has a countable dense family.
Finite coordinate tests and the isometry triangle inequality extend approximation
from that sequence to arbitrary finite observations. No affine classification,
rotation matrices, fundamental region, or measurable selection of witnesses is used.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory TopologicalSpace
open scoped ENNReal Classical

theorem exists_countable_inverse_isometry_approximation {A : Type*} [MetricSpace A]
    [SecondCountableTopology A] [Nonempty A] :
    ∃ Φ : ℕ → A ≃ᵢ A, ∀ Ψ : A ≃ᵢ A, ∀ X : Set A, X.Finite →
      ∀ η : ℝ, 0 < η → ∃ n, ∀ x ∈ X, dist ((Φ n).symm x) (Ψ.symm x) < η := by
  let q : ℕ → A := denseSeq A
  let encode : (A ≃ᵢ A) → ℕ → A := fun Ψ k => Ψ.symm (q k)
  let : TopologicalSpace (A ≃ᵢ A) :=
    TopologicalSpace.induced encode inferInstance
  let : SecondCountableTopology (A ≃ᵢ A) :=
    secondCountableTopology_induced (A ≃ᵢ A) (ℕ → A) encode
  let : Nonempty (A ≃ᵢ A) := ⟨IsometryEquiv.refl A⟩
  let Φ : ℕ → A ≃ᵢ A := denseSeq (A ≃ᵢ A)
  have hencode : Continuous encode := continuous_induced_dom
  have hcoord (k : ℕ) : Continuous (fun Ψ : A ≃ᵢ A => Ψ.symm (q k)) := by
    simpa only [encode, Function.comp_def] using (continuous_apply k).comp hencode
  refine ⟨Φ, ?_⟩
  intro Ψ X hX η hη
  have hthird : 0 < η / 3 := by positivity
  choose k hk using fun x : A => (denseRange_denseSeq A).exists_dist_lt x hthird
  let U : Set (A ≃ᵢ A) := ⋂ x ∈ X,
    {Ψ' | dist (Ψ'.symm (q (k x))) (Ψ.symm (q (k x))) < η / 3}
  have hU : IsOpen U := hX.isOpen_biInter (fun x _ =>
    isOpen_lt ((hcoord (k x)).dist continuous_const) continuous_const)
  have hΨ : Ψ ∈ U := by
    simp only [U, mem_iInter, mem_ofPred_eq, dist_self]
    exact fun _ _ => hthird
  obtain ⟨n, hΨ'U⟩ :=
    (denseRange_denseSeq (A ≃ᵢ A)).exists_mem_open hU ⟨Ψ, hΨ⟩
  refine ⟨n, ?_⟩
  intro x hx
  have hmiddle : dist ((Φ n).symm (q (k x))) (Ψ.symm (q (k x))) < η / 3 :=
    mem_iInter.mp (mem_iInter.mp hΨ'U x) hx
  calc
    dist ((Φ n).symm x) (Ψ.symm x) ≤
        dist ((Φ n).symm x) ((Φ n).symm (q (k x))) +
          dist ((Φ n).symm (q (k x))) (Ψ.symm x) := dist_triangle _ _ _
    _ ≤ dist x (q (k x)) +
        (dist ((Φ n).symm (q (k x))) (Ψ.symm (q (k x))) +
          dist (Ψ.symm (q (k x))) (Ψ.symm x)) := by
      rw [(Φ n).symm.dist_eq]
      exact add_le_add le_rfl
        (dist_triangle ((Φ n).symm (q (k x))) (Ψ.symm (q (k x))) (Ψ.symm x))
    _ = dist x (q (k x)) +
        (dist ((Φ n).symm (q (k x))) (Ψ.symm (q (k x))) + dist x (q (k x))) := by
      rw [Ψ.symm.dist_eq, dist_comm (q (k x)) x]
    _ < η := by
      have hnear : dist x (q (k x)) < η / 3 := hk x
      linarith

theorem finiteLatticeMatch_of_inverse_approximation {A : Type*} [MetricSpace A]
    [ProperSpace A] {Λ X : Set A} (hΛ : IsClosed Λ) (hne : Λ.Nonempty)
    (hX : X.Finite) {Φ Ψ : A ≃ᵢ A} {error η : ℝ}
    (hnear : ∀ x ∈ X, dist (Φ.symm x) (Ψ.symm x) ≤ η)
    (hmatch : FiniteLatticeMatch Λ X Ψ error) :
    FiniteLatticeMatch Λ X Φ (error + η) := by
  apply (finiteLatticeMatch_iff_infDist hΛ hne hX Φ _).mpr
  have h := (finiteLatticeMatch_iff_infDist hΛ hne hX Ψ error).mp hmatch
  intro x hx
  exact Metric.infDist_le_infDist_add_dist.trans (add_le_add (h x hx) (hnear x hx))

/-- Every successful configuration lies in a Borel event with only a positive error margin. -/
theorem exists_measurable_localCrystal_envelope {d : ℕ} {Λ : Set (Ambient d)}
    (hΛ : IsClosed Λ) (hne : Λ.Nonempty) (R error loss η : ℝ) (hη : 0 < η) :
    ∃ G : Set (Configuration (Ambient d)), MeasurableSet G ∧
      {c | LocalCrystal Λ c R error loss} ⊆ G ∧
      G ⊆ {c | LocalCrystal Λ c R (error + η) loss} := by
  obtain ⟨Φ, hΦ⟩ := exists_countable_inverse_isometry_approximation (A := Ambient d)
  obtain ⟨G, hG, hmem, hsub⟩ :=
    measurable_countable_match_good_subevent hΛ hne Φ R (error + η) loss
  refine ⟨G, hG, ?_, hsub⟩
  rintro c ⟨⟨Ψ, hmatch⟩, hdensity⟩
  have hfinite := c.finite_on_compacts _ (isCompact_closedBall (0 : Ambient d) R)
  obtain ⟨n, hn⟩ := hΦ Ψ _ hfinite η hη
  apply (hmem c).mpr
  exact ⟨⟨n, finiteLatticeMatch_of_inverse_approximation hΛ hne hfinite
    (fun x hx => (hn x hx).le) hmatch⟩, hdensity⟩

theorem exists_measurable_localCrystal_envelope_double {d : ℕ} {Λ : Set (Ambient d)}
    (hΛ : IsClosed Λ) (hne : Λ.Nonempty) (R error loss : ℝ) (herror : 0 < error) :
    ∃ G : Set (Configuration (Ambient d)), MeasurableSet G ∧
      {c | LocalCrystal Λ c R error loss} ⊆ G ∧
      G ⊆ {c | LocalCrystal Λ c R (2 * error) loss} := by
  simpa only [two_mul] using
    exists_measurable_localCrystal_envelope hΛ hne R error loss error herror

/-- Pull the envelope back along any measurable configuration map, including random centres. -/
theorem exists_measurable_localCrystal_envelope_param {d : ℕ} {Λ : Set (Ambient d)}
    (hΛ : IsClosed Λ) (hne : Λ.Nonempty) {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → Configuration (Ambient d)) (hf : Measurable f)
    (R error loss η : ℝ) (hη : 0 < η) :
    ∃ G : Set Ω, MeasurableSet G ∧
      {ω | LocalCrystal Λ (f ω) R error loss} ⊆ G ∧
      G ⊆ {ω | LocalCrystal Λ (f ω) R (error + η) loss} := by
  obtain ⟨G, hG, hcontains, hsub⟩ :=
    exists_measurable_localCrystal_envelope hΛ hne R error loss η hη
  exact ⟨f ⁻¹' G, hG.preimage hf, fun _ h => hcontains h, fun _ h => hsub h⟩

/-- A bound on the exceptional set transfers to the Borel envelope.
The exceptional set itself need not be measurable: the measure upper bound is outer measure. -/
theorem exists_measurable_localCrystal_good_of_exception {d : ℕ}
    {Λ : Set (Ambient d)} (hΛ : IsClosed Λ) (hne : Λ.Nonempty)
    (μ : Measure (Configuration (Ambient d))) [IsProbabilityMeasure μ]
    (R error loss η : ℝ) (hη : 0 < η) (E : Set (Configuration (Ambient d)))
    (q : ℝ≥0∞) (hE : μ E ≤ q)
    (hgood : ∀ c, c ∉ E → LocalCrystal Λ c R error loss) :
    ∃ G : Set (Configuration (Ambient d)), MeasurableSet G ∧
      G ⊆ {c | LocalCrystal Λ c R (error + η) loss} ∧ 1 - q ≤ μ G := by
  obtain ⟨G, hG, hcontains, hsub⟩ :=
    exists_measurable_localCrystal_envelope hΛ hne R error loss η hη
  refine ⟨G, hG, hsub, ?_⟩
  have hcover : (univ : Set (Configuration (Ambient d))) ⊆ E ∪ G := by
    intro c _
    by_cases hc : c ∈ E
    · exact Or.inl hc
    · exact Or.inr (hcontains (hgood c hc))
  have hsum : 1 ≤ q + μ G := by
    calc
      1 = μ univ := (measure_univ : μ univ = 1).symm
      _ ≤ μ (E ∪ G) := measure_mono hcover
      _ ≤ μ E + μ G := measure_union_le E G
      _ ≤ q + μ G := add_le_add hE le_rfl
  exact tsub_le_iff_right.mpr (by simpa only [add_comm] using hsum)

theorem exists_measurable_localCrystal_good_of_exception_param {d : ℕ}
    {Λ : Set (Ambient d)} (hΛ : IsClosed Λ) (hne : Λ.Nonempty)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → Configuration (Ambient d)) (hf : Measurable f)
    (R error loss η : ℝ) (hη : 0 < η) (E : Set Ω) (q : ℝ≥0∞)
    (hE : μ E ≤ q) (hgood : ∀ ω, ω ∉ E → LocalCrystal Λ (f ω) R error loss) :
    ∃ G : Set Ω, MeasurableSet G ∧
      G ⊆ {ω | LocalCrystal Λ (f ω) R (error + η) loss} ∧ 1 - q ≤ μ G := by
  obtain ⟨G, hG, hcontains, hsub⟩ :=
    exists_measurable_localCrystal_envelope_param hΛ hne f hf R error loss η hη
  refine ⟨G, hG, hsub, ?_⟩
  have hcover : (univ : Set Ω) ⊆ E ∪ G := by
    intro ω _
    by_cases hω : ω ∈ E
    · exact Or.inl hω
    · exact Or.inr (hcontains (hgood ω hω))
  apply tsub_le_iff_right.mpr
  calc
    1 = μ univ := (measure_univ : μ univ = 1).symm
    _ ≤ μ (E ∪ G) := measure_mono hcover
    _ ≤ μ E + μ G := measure_union_le E G
    _ ≤ q + μ G := add_le_add hE le_rfl
    _ = μ G + q := add_comm _ _

end E8Leech
