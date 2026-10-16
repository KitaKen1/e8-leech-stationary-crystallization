import E8Leech.LatticeDistance
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Sequences

/-!
# A single containing lattice from vanishing finite-window errors

Recenter each approximate lattice at a lattice point near one fixed point
of the configuration. The translations then lie in a fixed compact ball.
The linear isometries lie in a compact operator ball. A subsequential limit
contains every configuration point; no measurable lattice selection is
asserted here.
-/

noncomputable section
namespace E8Leech
open Set Filter Topology
open scoped Classical

/-- Recentring an isometry at a lattice point preserves its affine action. -/
theorem isometry_recenter_apply {d : ℕ} (Φ : Ambient d ≃ᵢ Ambient d) (x z : Ambient d) :
    Φ.toRealLinearIsometryEquiv (x - z) + Φ z = Φ x := by
  rw [map_sub, IsometryEquiv.toRealLinearIsometryEquiv_apply,
    IsometryEquiv.toRealLinearIsometryEquiv_apply]
  abel

theorem exists_containing_isometry_of_bounded_affine_approximants {d : ℕ}
    {Λ X : Set (Ambient d)} (hclosed : IsClosed Λ) (hne : Λ.Nonempty)
    (Q : ℕ → Ambient d ≃ₗᵢ[ℝ] Ambient d) (b : ℕ → Ambient d) (a : Ambient d)
    (hb : ∀ n, b n ∈ Metric.closedBall a 1) (R ε : ℕ → ℝ)
    (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (hmatch : ∀ n, ∀ x ∈ X ∩ Metric.closedBall 0 (R n),
      ∃ z ∈ Λ, dist x (Q n z + b n) ≤ ε n) :
    ∃ Φ : Ambient d ≃ᵢ Ambient d, X ⊆ Φ '' Λ := by
  let p : ℕ → (Ambient d →L[ℝ] Ambient d) × Ambient d :=
    fun n => ((Q n).toContinuousLinearMap, b n)
  have hcompact := (isCompact_closedBall (0 : Ambient d →L[ℝ] Ambient d) 1).prod
    (isCompact_closedBall a 1)
  have hp : ∀ n, p n ∈ Metric.closedBall (0 : Ambient d →L[ℝ] Ambient d) 1 ×ˢ
      Metric.closedBall a 1 := by
    intro n
    refine ⟨?_, hb n⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖(Q n).toContinuousLinearMap‖ ≤ 1
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    simp
  obtain ⟨⟨L, v⟩, -, k, hk, hlim⟩ := hcompact.tendsto_subseq hp
  have hLnorm : ∀ x : Ambient d, ‖L x‖ = ‖x‖ := by
    intro x
    have hc : Continuous (fun p : (Ambient d →L[ℝ] Ambient d) × Ambient d => ‖p.1 x‖) :=
      (continuous_fst.clm_apply continuous_const).norm
    have ht := (hc.tendsto (L, v)).comp hlim
    change Tendsto (fun n => ‖Q (k n) x‖) atTop (𝓝 ‖L x‖) at ht
    simp only [LinearIsometryEquiv.norm_map] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  let l : Ambient d →ₗᵢ[ℝ] Ambient d := ⟨L.toLinearMap, hLnorm⟩
  have hsurj : Function.Surjective l :=
    LinearMap.surjective_of_injective (f := l.toLinearMap) l.injective
  let e : Ambient d ≃ₗᵢ[ℝ] Ambient d := LinearIsometryEquiv.ofSurjective l hsurj
  let Φ : Ambient d ≃ᵢ Ambient d := e.toIsometryEquiv.trans (IsometryEquiv.addRight v)
  refine ⟨Φ, fun x hx => ?_⟩
  let w := e.symm (x - v)
  have hxw : L w + v = x := by
    have h : e w = x - v := e.apply_symm_apply (x - v)
    change L w = x - v at h
    rw [h]
    abel
  have hc : Continuous (fun p : (Ambient d →L[ℝ] Ambient d) × Ambient d => p.1 w + p.2) :=
    (continuous_fst.clm_apply continuous_const).add continuous_snd
  have ht : Tendsto (fun n => Q (k n) w + b (k n)) atTop (𝓝 x) := by
    have ht₀ := (hc.tendsto (L, v)).comp hlim
    change Tendsto (fun n => Q (k n) w + b (k n)) atTop (𝓝 (L w + v)) at ht₀
    simpa only [hxw] using ht₀
  have herror : Tendsto (fun n => dist (Q (k n) w + b (k n)) x + ε (k n)) atTop (𝓝 0) := by
    simpa using (ht.dist (tendsto_const_nhds (x := x))).add (hε.comp hk.tendsto_atTop)
  have hdist : Metric.infDist w Λ ≤ 0 := by
    apply ge_of_tendsto herror
    filter_upwards [(hR.comp hk.tendsto_atTop).eventually (eventually_ge_atTop ‖x‖)] with n hn
    obtain ⟨z, hz, hd⟩ := hmatch (k n) x ⟨hx, by simpa [Metric.mem_closedBall, dist_zero_right] using hn⟩
    calc
      Metric.infDist w Λ ≤ dist w z := Metric.infDist_le_dist_of_mem hz
      _ = dist (Q (k n) w + b (k n)) (Q (k n) z + b (k n)) := by simp
      _ ≤ dist (Q (k n) w + b (k n)) x + ε (k n) :=
        (dist_triangle _ x _).trans (add_le_add le_rfl hd)
  have hw : w ∈ Λ := (hclosed.mem_iff_infDist_zero hne).mpr
    (le_antisymm hdist Metric.infDist_nonneg)
  refine ⟨w, hw, ?_⟩
  change e w + v = x
  change L w + v = x
  exact hxw

/-- Finite-window crystallization along diverging windows and vanishing errors gives one
containing affine lattice. The lattice witness need not be unique or measurably selected. -/
theorem exists_containing_isometry_of_localCrystal_sequence {d : ℕ}
    {Λ : Set (Ambient d)} (hclosed : IsClosed Λ) (hne : Λ.Nonempty)
    (hsub : ∀ x ∈ Λ, ∀ y ∈ Λ, x - y ∈ Λ)
    (c : Configuration (Ambient d)) (R ε loss : ℕ → ℝ)
    (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (hlocal : ∀ᶠ n in atTop, LocalCrystal Λ c (R n) (ε n) (loss n)) :
    ∃ Φ : Ambient d ≃ᵢ Ambient d, c.support ⊆ Φ '' Λ := by
  by_cases hc : c.support.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hc
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((hlocal.and (hR.eventually (eventually_ge_atTop ‖x₀‖))).and
        (hε.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))))
    have hdata : ∀ n : ℕ, ∃ Φ : Ambient d ≃ᵢ Ambient d, ∃ z ∈ Λ,
        dist x₀ (Φ z) ≤ ε (n + N) ∧
        ∀ x ∈ c.support ∩ Metric.closedBall 0 (R (n + N)),
          ∃ w ∈ Λ, dist x (Φ w) ≤ ε (n + N) := by
      intro n
      obtain ⟨⟨hl, hR₀⟩, _⟩ := hN (n + N) (by omega)
      obtain ⟨⟨Φ, Z, hZ, hf, _⟩, _⟩ := hl
      obtain ⟨z, hz, hd⟩ := hf x₀ ⟨hx₀, by simpa [Metric.mem_closedBall, dist_zero_right] using hR₀⟩
      refine ⟨Φ, z, hZ hz, hd, fun x hx => ?_⟩
      obtain ⟨w, hw, hdist⟩ := hf x hx
      exact ⟨w, hZ hw, hdist⟩
    choose Φ z hz hanchor hmatch using hdata
    let Q := fun n => (Φ n).toRealLinearIsometryEquiv
    let b := fun n => Φ n (z n)
    have hb : ∀ n, b n ∈ Metric.closedBall x₀ 1 := by
      intro n
      have he := (hN (n + N) (by omega)).2
      rw [Metric.mem_closedBall, dist_comm]
      exact (hanchor n).trans he
    apply exists_containing_isometry_of_bounded_affine_approximants hclosed hne Q b x₀ hb
      (fun n => R (n + N)) (fun n => ε (n + N))
      (hR.comp (tendsto_add_atTop_nat N)) (hε.comp (tendsto_add_atTop_nat N))
    intro n x hx
    obtain ⟨w, hw, hd⟩ := hmatch n x hx
    refine ⟨w - z n, hsub w hw (z n) (hz n), ?_⟩
    simpa only [Q, b, isometry_recenter_apply] using hd
  · exact ⟨IsometryEquiv.refl _, fun x hx => False.elim (hc ⟨x, hx⟩)⟩

end E8Leech
