import E8Leech.E8PeriodicStructure
import E8Leech.PeriodizationDensity

/-!
# The guarded periodization as a periodic sphere packing

The guarded periodization of a separated configuration (`guardedPeriodization`) is periodic under
the cube lattice `L ℤᵈ`. This file presents it as a `PeriodicSpherePacking` of the ported
Sphere-Packing-Lean development, with the period cell `[0,L)ᵈ` as fundamental domain, so that the
results on periodic packings apply to it:

* `mem_cubeLattice_iff`: the cube lattice consists of the period shifts.
* `guardedPacking`: the packing; its centres are the support of the periodization and its lattice
  is the cube lattice.
* `guardedPacking_density_ge`: a guard deficit below `η` gives density at least `1 - η`.
* `localCrystal_translate_of_window`: closeness of a window to an isometric copy of a set, and a
  count, give `LocalCrystal` for the translated configuration.
-/

noncomputable section

namespace E8Leech

open MeasureTheory Metric Set SpherePacking
open scoped ENNReal

theorem cubeBasis_repr_apply {d : ℕ} (L : ℝ) (hL : 0 < L) (x : Ambient d) (i : Fin d) :
    (cubeBasis (d := d) L hL).repr x i = L⁻¹ * x i := by
  simp [cubeBasis, Module.Basis.repr_isUnitSMul, Units.smul_def, Units.val_inv_eq_inv_val]

/-- The cube lattice consists of the period shifts. -/
theorem mem_cubeLattice_iff {d : ℕ} (L : ℝ) (hL : 0 < L) (x : Ambient d) :
    x ∈ cubeLattice (d := d) L hL ↔ ∃ m : Fin d → ℤ, x = periodShift L m := by
  rw [cubeLattice, Module.Basis.mem_span_iff_repr_mem]
  constructor
  · intro h
    choose m hm using h
    refine ⟨m, ?_⟩
    ext i
    have h1 := hm i
    rw [cubeBasis_repr_apply] at h1
    have h2 : (m i : ℝ) = L⁻¹ * x i := h1
    rw [periodShift_apply, h2]
    field_simp
  · rintro ⟨m, rfl⟩ i
    refine ⟨m i, ?_⟩
    rw [cubeBasis_repr_apply, periodShift_apply]
    show ((m i : ℤ) : ℝ) = L⁻¹ * (L * (m i : ℝ))
    field_simp

set_option backward.isDefEq.respectTransparency false in
/-- The guarded periodization as a periodic sphere packing with lattice `L ℤᵈ`. -/
def guardedPacking {d : ℕ} (c : Configuration (Ambient d)) (L r : ℝ) (hr : 0 < r)
    (hL : r < L) (hs : ∀ x ∈ c.support, ∀ y ∈ c.support, x ≠ y → r ≤ dist x y) :
    PeriodicSpherePacking d where
  centers := guardedPeriodizationSupport c L r
  separation := r
  separation_pos := hr
  centers_dist := fun x y hne =>
    guardedPeriodization_separated c L r (hr.trans hL).le hs x.1 x.2 y.1 y.2
      fun e => hne (Subtype.ext e)
  lattice := cubeLattice (d := d) L (hr.trans hL)
  lattice_action := by
    intro x y hx hy
    obtain ⟨m, rfl⟩ := (mem_cubeLattice_iff L (hr.trans hL) x).mp hx
    rw [← guardedPeriodizationSupport_periodic c L r m]
    exact ⟨y, hy, rfl⟩
  lattice_discrete := by
    dsimp [cubeLattice]
    infer_instance
  lattice_isZLattice := by
    dsimp [cubeLattice]
    infer_instance

theorem periodCell_eq_coordCube (d : ℕ) (L : ℝ) : periodCell d L = coordCube (d := d) L := rfl

/-- The period cell contains exactly one point of every orbit of the cube lattice. -/
theorem guardedPacking_unique_covers {d : ℕ} (c : Configuration (Ambient d)) (L r : ℝ)
    (hr : 0 < r) (hL : r < L)
    (hs : ∀ x ∈ c.support, ∀ y ∈ c.support, x ≠ y → r ≤ dist x y) :
    ∀ v, ∃! ℓ : (guardedPacking c L r hr hL hs).lattice, ℓ +ᵥ v ∈ periodCell d L :=
  PeriodicConstant.coordCube_unique_covers (d := d) L (hr.trans hL)

/-- The number of representatives in the period cell is the count in the guard box. -/
theorem guardedPacking_numReps {d : ℕ} (hd : 0 < d) (c : Configuration (Ambient d)) (L r : ℝ)
    (hr : 0 < r) (hL : r < L)
    (hs : ∀ x ∈ c.support, ∀ y ∈ c.support, x ≠ y → r ≤ dist x y) :
    (((guardedPacking c L r hr hL hs).numReps' hd (isBounded_periodCell d L) : ℕ) :
      ℝ≥0∞) = c.count (guardInnerBox d L r) := by
  rw [numReps'_eq_ncard, Configuration.count_eq_encard]
  have he : (guardedPacking c L r hr hL hs).centers ∩ periodCell d L =
      c.support ∩ guardInnerBox d L r := guardedPeriodizationSupport_inter_cell c L r hr hL
  have hfin : (c.support ∩ guardInnerBox d L r).Finite := by
    rw [← he]
    exact finite_centers_inter (guardedPacking c L r hr hL hs) hd
      (isBounded_periodCell d L)
  rw [he, ← hfin.cast_ncard_eq]
  rfl

/-- A guard deficit below `η` gives density at least `1 - η` for the periodized packing. -/
theorem guardedPacking_density_ge {d : ℕ} (hd : 0 < d) (c : Configuration (Ambient d))
    (L r : ℝ) (hr : 0 < r) (hL : r < L)
    (hs : ∀ x ∈ c.support, ∀ y ∈ c.support, x ≠ y → r ≤ dist x y) {η : ℝ}
    (hdef : 1 - guardDensity c L r < ENNReal.ofReal η) :
    1 - η ≤ ((guardedPacking c L r hr hL hs).numReps' hd
      (isBounded_periodCell d L) : ℝ) /
        ZLattice.covolume (guardedPacking c L r hr hL hs).lattice volume := by
  have hL0 : 0 < L := hr.trans hL
  have hcov : ZLattice.covolume (guardedPacking c L r hr hL hs).lattice volume = L ^ d :=
    covolume_cubeLattice L hL0
  have hLd : (0 : ℝ) < L ^ d := pow_pos hL0 d
  have hN := guardedPacking_numReps hd c L r hr hL hs
  rw [hcov]
  -- the guard density is the ratio
  have hgd : guardDensity c L r = ENNReal.ofReal
      (((guardedPacking c L r hr hL hs).numReps' hd (isBounded_periodCell d L) : ℝ) /
        L ^ d) := by
    rw [guardDensity, ← hN, ENNReal.ofReal_div_of_pos hLd, ENNReal.ofReal_pow hL0.le]
    simp
  rw [hgd] at hdef
  by_contra hcon
  have hlt : ((guardedPacking c L r hr hL hs).numReps' hd (isBounded_periodCell d L) : ℝ) /
      L ^ d < 1 - η := lt_of_not_ge hcon
  have hq0 : 0 ≤ ((guardedPacking c L r hr hL hs).numReps' hd (isBounded_periodCell d L) : ℝ) /
      L ^ d := by positivity
  have h1 : ENNReal.ofReal η ≤ 1 - ENNReal.ofReal
      (((guardedPacking c L r hr hL hs).numReps' hd (isBounded_periodCell d L) : ℝ) /
        L ^ d) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hq0]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  exact absurd hdef (not_lt.mpr h1)

/-- **From a window to `LocalCrystal`.** If the points of a configuration in `B(u,R)` are within
`error` of `p₀ + Φ₀(Λ)` for a linear isometry `Φ₀`, and the count in `B(u,R)` is at least
`(1 - loss)·vol(B_R)`, then the configuration translated by `-u` is a local crystal. -/
theorem localCrystal_translate_of_window {d : ℕ} {Λ : Set (Ambient d)}
    (cfg : Configuration (Ambient d)) (u : Ambient d) {R error loss : ℝ}
    (Φ₀ : Ambient d ≃ₗᵢ[ℝ] Ambient d) (p₀ : Ambient d)
    (hnear : ∀ x ∈ cfg.support ∩ closedBall u R, ∃ z ∈ Λ, ‖(x - p₀) - Φ₀ z‖ ≤ error)
    (hcount : ENNReal.ofReal (1 - loss) * volume (closedBall (0 : Ambient d) R) ≤
      cfg.count (closedBall u R)) :
    LocalCrystal Λ (translate (-u) cfg) R error loss := by
  classical
  have hfin : (cfg.support ∩ closedBall u R).Finite :=
    cfg.finite_on_compacts _ (isCompact_closedBall u R)
  choose! zf hzΛ hzdist using hnear
  have hsupp : ∀ x', x' ∈ (translate (-u) cfg).support ∩ closedBall 0 R ↔
      ∃ x ∈ cfg.support ∩ closedBall u R, x' = -u + x := by
    intro x'
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hball⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      rw [mem_closedBall, dist_eq_norm] at hball ⊢
      have e : (Homeomorph.addLeft (-u)) x - 0 = x - u := by
        show -u + x - 0 = x - u
        abel
      rwa [e] at hball
    · rintro ⟨x, ⟨hx, hball⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_eq_norm] at hball ⊢
      have e : -u + x - 0 = x - u := by abel
      rwa [e]
  have hdist : ∀ x z : Ambient d,
      dist (-u + x) ((Φ₀.toIsometryEquiv.trans (IsometryEquiv.addRight (p₀ - u))) z) =
        ‖(x - p₀) - Φ₀ z‖ := by
    intro x z
    rw [dist_eq_norm]
    have e : -u + x - (Φ₀.toIsometryEquiv.trans (IsometryEquiv.addRight (p₀ - u))) z =
        (x - p₀) - Φ₀ z := by
      show -u + x - (Φ₀ z + (p₀ - u)) = (x - p₀) - Φ₀ z
      abel
    rw [e]
  refine ⟨⟨Φ₀.toIsometryEquiv.trans (IsometryEquiv.addRight (p₀ - u)),
    hfin.toFinset.image zf, ?_, ?_, ?_⟩, ?_⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact hzΛ x (hfin.mem_toFinset.mp hx)
  · intro x' hx'
    obtain ⟨x, hx, rfl⟩ := (hsupp x').mp hx'
    refine ⟨zf x, Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hx), ?_⟩
    rw [hdist]
    exact hzdist x hx
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hx' := hfin.mem_toFinset.mp hx
    refine ⟨-u + x, (hsupp _).mpr ⟨x, hx', rfl⟩, ?_⟩
    rw [dist_comm, hdist]
    exact hzdist x hx'
  · rw [count_translate, translate_negative_closedBall_preimage]
    exact hcount

end E8Leech
