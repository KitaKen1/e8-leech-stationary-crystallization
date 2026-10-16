import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# From approximately even squared lengths to an integer Gram matrix

This is the polarization step used after BRR's magic-function estimate.
It applies in any real inner product space, keeps the three error budgets,
and proves that sufficiently accurate integer Gram entries are symmetric.
No basis perturbation or lattice classification is asserted here.
-/

namespace E8Leech

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

open scoped InnerProductSpace

theorem inner_approx_of_even_squared_lengths {x y : V} {a b c : ℤ}
    {εx εy εsub : ℝ}
    (hx : |‖x‖ ^ 2 - 2 * a| ≤ εx) (hy : |‖y‖ ^ 2 - 2 * b| ≤ εy)
    (hsub : |‖x - y‖ ^ 2 - 2 * c| ≤ εsub) :
    |⟪x, y⟫_ℝ - (a + b - c : ℤ)| ≤ (εx + εy + εsub) / 2 := by
  rcases abs_le.mp hx with ⟨hxlo, hxhi⟩
  rcases abs_le.mp hy with ⟨hylo, hyhi⟩
  rcases abs_le.mp hsub with ⟨hslo, hshi⟩
  rw [norm_sub_sq_real] at hslo hshi
  apply abs_le.mpr
  push_cast
  constructor <;> linarith

theorem exists_integer_inner_approx {x y : V} {ε : ℝ}
    (hx : ∃ a : ℤ, |‖x‖ ^ 2 - 2 * a| ≤ ε)
    (hy : ∃ b : ℤ, |‖y‖ ^ 2 - 2 * b| ≤ ε)
    (hsub : ∃ c : ℤ, |‖x - y‖ ^ 2 - 2 * c| ≤ ε) :
    ∃ k : ℤ, |⟪x, y⟫_ℝ - k| ≤ 3 / 2 * ε := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  obtain ⟨c, hc⟩ := hsub
  refine ⟨a + b - c, ?_⟩
  simpa only [show (ε + ε + ε) / 2 = 3 / 2 * ε by ring] using
    inner_approx_of_even_squared_lengths ha hb hc

/-- An integer within less than half a unit is unique. -/
theorem integer_approx_unique {x ε : ℝ} {a b : ℤ} (hε : ε < 1 / 2)
    (ha : |x - a| ≤ ε) (hb : |x - b| ≤ ε) : a = b := by
  rcases abs_le.mp ha with ⟨halo, hahi⟩
  rcases abs_le.mp hb with ⟨hblo, hbhi⟩
  have hlo : (-1 : ℝ) < (a - b : ℤ) := by push_cast; linarith
  have hhi : ((a - b : ℤ) : ℝ) < 1 := by push_cast; linarith
  have hlo' : (-1 : ℤ) < a - b := by exact_mod_cast hlo
  have hhi' : a - b < 1 := by exact_mod_cast hhi
  omega

/-- The rounded Gram matrix is symmetric; symmetry is not an extra hypothesis. -/
theorem integer_gram_symmetric {ι : Type*} {v : ι → V} {K : ι → ι → ℤ} {ε : ℝ}
    (hε : ε < 1 / 2) (hK : ∀ i j, |⟪v i, v j⟫_ℝ - K i j| ≤ ε) :
    ∀ i j, K i j = K j i := by
  intro i j
  apply integer_approx_unique hε (hK i j)
  simpa only [real_inner_comm] using hK j i

end E8Leech
