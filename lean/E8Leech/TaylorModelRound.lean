import E8Leech.TaylorModelOps
import Mathlib.Data.Rat.Floor

/-!
# Outward rounding of Taylor models to dyadic precision

Coefficient rounding errors are bounded on the actual box and added to the radius.
The radius is rounded upward. This is a sound approximation operation, not an equality
with the original model, and not a claim that any particular sign certificate succeeds.
-/

namespace E8Leech.Taylor

def dyadicFloor (p : ℕ) (q : ℚ) : ℚ := (⌊q * (2 : ℚ) ^ p⌋ : ℚ) / (2 : ℚ) ^ p

def dyadicCeil (p : ℕ) (q : ℚ) : ℚ := (⌈q * (2 : ℚ) ^ p⌉ : ℚ) / (2 : ℚ) ^ p

theorem dyadicFloor_le (p : ℕ) (q : ℚ) : dyadicFloor p q ≤ q := by
  unfold dyadicFloor
  rw [div_le_iff₀ (pow_pos (by norm_num : (0 : ℚ) < 2) p)]
  exact Int.floor_le _

theorem le_dyadicCeil (p : ℕ) (q : ℚ) : q ≤ dyadicCeil p q := by
  unfold dyadicCeil
  rw [le_div_iff₀ (pow_pos (by norm_num : (0 : ℚ) < 2) p)]
  exact Int.le_ceil _

theorem abs_sub_dyadicFloor_le (p : ℕ) (q : ℚ) :
    |q - dyadicFloor p q| ≤ 1 / (2 : ℚ) ^ p := by
  have hs : (0 : ℚ) < 2 ^ p := pow_pos (by norm_num) p
  rw [abs_of_nonneg (sub_nonneg.mpr (dyadicFloor_le p q))]
  apply (le_div_iff₀ hs).mpr
  have h := Int.lt_floor_add_one (q * (2 : ℚ) ^ p)
  dsimp [dyadicFloor]
  rw [sub_mul, div_mul_cancel₀ _ hs.ne']
  linarith

namespace Poly

def round (p : ℕ) (P : Poly) : Poly := P.map fun mc => (mc.1, dyadicFloor p mc.2)

/-- A coefficient-independent error budget, avoiding arithmetic with coefficient differences. -/
def roundSlack (B : Box) (p : ℕ) (P : Poly) : ℚ :=
  (P.map fun mc => Mono.bound B mc.1).sum / (2 : ℚ) ^ p

theorem abs_eval_sub_round_le {B : Box} (hB : B.Valid) {e : Env} (he : B.Mem e)
    (p : ℕ) (P : Poly) : |Poly.eval P e - (round p P).eval e| ≤ (roundSlack B p P : ℝ) := by
  induction P with
  | nil => simp [round, roundSlack]
  | cons mc P ih =>
    have hc : |(mc.2 : ℝ) - (dyadicFloor p mc.2 : ℝ)| ≤ (1 / (2 : ℚ) ^ p : ℚ) := by
      exact_mod_cast abs_sub_dyadicFloor_le p mc.2
    have hm := Mono.abs_eval_le hB he mc.1
    have hr : (0 : ℝ) ≤ (1 / (2 : ℚ) ^ p : ℚ) := by positivity
    have hslack : roundSlack B p (mc :: P) =
        Mono.bound B mc.1 / (2 : ℚ) ^ p + roundSlack B p P := by
      simp [roundSlack, add_div]
    rw [hslack, Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
    simp only [round, List.map_cons, eval_cons] at ih ⊢
    calc |(mc.2 : ℝ) * mc.1.eval e + Poly.eval P e -
          ((dyadicFloor p mc.2 : ℝ) * mc.1.eval e +
            Poly.eval (P.map fun (mc : Mono × ℚ) => (mc.1, dyadicFloor p mc.2)) e)|
        = |((mc.2 : ℝ) - (dyadicFloor p mc.2 : ℝ)) * mc.1.eval e +
            (Poly.eval P e - Poly.eval (P.map fun (mc : Mono × ℚ) => (mc.1, dyadicFloor p mc.2)) e)| := by
          congr 1
          ring
      _ ≤ |(mc.2 : ℝ) - (dyadicFloor p mc.2 : ℝ)| * |mc.1.eval e| +
          |Poly.eval P e - Poly.eval (P.map fun (mc : Mono × ℚ) => (mc.1, dyadicFloor p mc.2)) e| := by
          rw [← abs_mul]
          exact abs_add_le _ _
      _ ≤ ((1 / (2 : ℚ) ^ p : ℚ) : ℝ) * (Mono.bound B mc.1 : ℝ) +
          (roundSlack B p P : ℝ) :=
          add_le_add (mul_le_mul hc hm (abs_nonneg _) hr) ih
      _ = _ := by push_cast; ring

end Poly

namespace TM

def round (B : Box) (p : ℕ) (T : TM) : TM :=
  ⟨T.P.round p, dyadicCeil p (T.r + T.P.roundSlack B p)⟩

theorem approx_round {B : Box} (hB : B.Valid) (p : ℕ) {S : Env → Prop}
    {T : TM} {f : Env → ℝ} (h : T.Approx B S f) : (round B p T).Approx B S f := by
  intro e he hs
  have hq := Poly.abs_eval_sub_round_le hB he p T.P
  have hu : ((T.r + T.P.roundSlack B p : ℚ) : ℝ) ≤
      (dyadicCeil p (T.r + T.P.roundSlack B p) : ℝ) := by
    exact_mod_cast le_dyadicCeil p (T.r + T.P.roundSlack B p)
  change |f e - (T.P.round p).eval e| ≤ _
  calc |f e - (T.P.round p).eval e|
      = |(f e - T.P.eval e) + (T.P.eval e - (T.P.round p).eval e)| := by congr 1; ring
    _ ≤ |f e - T.P.eval e| + |T.P.eval e - (T.P.round p).eval e| := abs_add_le _ _
    _ ≤ (T.r : ℝ) + (T.P.roundSlack B p : ℝ) := add_le_add (h e he hs) hq
    _ ≤ _ := by simpa only [round, Rat.cast_add] using hu

end TM

namespace DD

def round (B : Box) (p : ℕ) (X : DD) : DD :=
  ⟨X.A.round B p, X.B.round B p, X.D.round B p⟩

theorem approx_round {B : Box} (hB : B.Valid) (p : ℕ) {S : Env → Prop}
    {X : DD} {fa fb : Env → ℝ} (h : X.Approx B S fa fb) :
    (round B p X).Approx B S fa fb :=
  ⟨TM.approx_round hB p h.1, TM.approx_round hB p h.2.1, TM.approx_round hB p h.2.2⟩

end DD

end E8Leech.Taylor
