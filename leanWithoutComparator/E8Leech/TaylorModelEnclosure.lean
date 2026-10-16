import E8Leech.TaylorModelOps

/-!
# Signed interval enclosures for Taylor models

The absolute bound used for error propagation loses all cancellation. For the final sign test,
`Poly.lower` and `Poly.upper` instead bound each signed monomial at the appropriate endpoint.
`TM.lower` and `TM.upper` include the remainder radius. Their inequalities are rational and
computable, while the soundness lemmas apply to the real function represented by the model.
-/

namespace E8Leech.Taylor

def zpowLo (lo hi : ℚ) (n : ℤ) : ℚ := if 0 ≤ n then lo ^ n.toNat else hi ^ n

theorem zpowLo_le_zpow {lo hi : ℚ} {x : ℝ} (hlo : 0 < lo) (hx1 : (lo : ℝ) ≤ x)
    (hx2 : x ≤ hi) (n : ℤ) : (zpowLo lo hi n : ℝ) ≤ x ^ n := by
  have hx : 0 < x := lt_of_lt_of_le (by exact_mod_cast hlo) hx1
  unfold zpowLo
  split_ifs with hn
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    simp only [zpow_natCast, Int.toNat_natCast]
    push_cast
    exact pow_le_pow_left₀ (by exact_mod_cast hlo.le) hx1 k
  · obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat (not_le.mp hn).le
    subst hk
    simp only [zpow_neg, zpow_natCast]
    push_cast
    exact inv_anti₀ (pow_pos hx k) (pow_le_pow_left₀ hx.le hx2 k)

def Mono.lower (B : Box) (m : Mono) : ℚ :=
  B.alo ^ m.ea * B.blo ^ m.eb * B.ulo ^ m.eu * zpowLo B.tlo B.thi m.et *
    zpowLo B.plo B.phi m.ep * B.llo ^ m.el

theorem Mono.lower_le_eval {B : Box} (hB : B.Valid) {e : Env} (he : B.Mem e) (m : Mono) :
    (m.lower B : ℝ) ≤ m.eval e := by
  obtain ⟨ha0, hb0, hu0, ht0, hp0, hl0⟩ := hB
  obtain ⟨ha1, ha2, hb1, hb2, hu1, hu2, ht1, ht2, hp1, hp2, hl1, hl2⟩ := he
  have ha : 0 ≤ e.a := le_trans (by exact_mod_cast ha0) ha1
  have hb : 0 ≤ e.b := le_trans (by exact_mod_cast hb0) hb1
  have hu : 0 < e.u := lt_of_lt_of_le (by exact_mod_cast hu0) hu1
  have ht : 0 < e.t := lt_of_lt_of_le (by exact_mod_cast ht0) ht1
  have hp : 0 < e.p := lt_of_lt_of_le (by exact_mod_cast hp0) hp1
  have hl : 0 < e.l := lt_of_lt_of_le (by exact_mod_cast hl0) hl1
  have htHi : 0 < (B.thi : ℝ) := lt_of_lt_of_le ht ht2
  have hpHi : 0 < (B.phi : ℝ) := lt_of_lt_of_le hp hp2
  have f1 := pow_le_pow_left₀ (by exact_mod_cast ha0 : (0 : ℝ) ≤ B.alo) ha1 m.ea
  have f2 := pow_le_pow_left₀ (by exact_mod_cast hb0 : (0 : ℝ) ≤ B.blo) hb1 m.eb
  have f3 := pow_le_pow_left₀ (by exact_mod_cast hu0.le : (0 : ℝ) ≤ B.ulo) hu1 m.eu
  have f4 := zpowLo_le_zpow ht0 ht1 ht2 m.et
  have f5 := zpowLo_le_zpow hp0 hp1 hp2 m.ep
  have f6 := pow_le_pow_left₀ (by exact_mod_cast hl0.le : (0 : ℝ) ≤ B.llo) hl1 m.el
  have htl : (0 : ℝ) ≤ zpowLo B.tlo B.thi m.et := by
    unfold zpowLo
    split_ifs <;> push_cast <;> positivity
  have hpl : (0 : ℝ) ≤ zpowLo B.plo B.phi m.ep := by
    unfold zpowLo
    split_ifs <;> push_cast <;> positivity
  unfold Mono.lower Mono.eval
  push_cast
  gcongr

def termLower (B : Box) (mc : Mono × ℚ) : ℚ :=
  if 0 ≤ mc.2 then mc.2 * mc.1.lower B else mc.2 * mc.1.bound B

def termUpper (B : Box) (mc : Mono × ℚ) : ℚ :=
  if 0 ≤ mc.2 then mc.2 * mc.1.bound B else mc.2 * mc.1.lower B

theorem termLower_le {B : Box} (hB : B.Valid) {e : Env} (he : B.Mem e) (mc : Mono × ℚ) :
    (termLower B mc : ℝ) ≤ (mc.2 : ℝ) * mc.1.eval e := by
  have hlo := Mono.lower_le_eval hB he mc.1
  have hhi := (le_abs_self (mc.1.eval e)).trans (Mono.abs_eval_le hB he mc.1)
  unfold termLower
  split_ifs with hc
  · push_cast
    exact mul_le_mul_of_nonneg_left hlo (by exact_mod_cast hc)
  · push_cast
    exact mul_le_mul_of_nonpos_left hhi (by exact_mod_cast (not_le.mp hc).le)

theorem term_le_upper {B : Box} (hB : B.Valid) {e : Env} (he : B.Mem e) (mc : Mono × ℚ) :
    (mc.2 : ℝ) * mc.1.eval e ≤ (termUpper B mc : ℝ) := by
  have hlo := Mono.lower_le_eval hB he mc.1
  have hhi := (le_abs_self (mc.1.eval e)).trans (Mono.abs_eval_le hB he mc.1)
  unfold termUpper
  split_ifs with hc
  · push_cast
    exact mul_le_mul_of_nonneg_left hhi (by exact_mod_cast hc)
  · push_cast
    exact mul_le_mul_of_nonpos_left hlo (by exact_mod_cast (not_le.mp hc).le)

def Poly.lower (B : Box) (P : Poly) : ℚ := (P.map (termLower B)).sum
def Poly.upper (B : Box) (P : Poly) : ℚ := (P.map (termUpper B)).sum

theorem Poly.lower_le_eval {B : Box} (hB : B.Valid) {e : Env} (he : B.Mem e) (P : Poly) :
    (P.lower B : ℝ) ≤ P.eval e := by
  induction P with
  | nil => simp [lower]
  | cons mc P ih =>
    simp only [lower, List.map_cons, List.sum_cons, Rat.cast_add, eval_cons] at ih ⊢
    exact add_le_add (termLower_le hB he mc) ih

theorem Poly.eval_le_upper {B : Box} (hB : B.Valid) {e : Env} (he : B.Mem e) (P : Poly) :
    P.eval e ≤ (P.upper B : ℝ) := by
  induction P with
  | nil => simp [upper]
  | cons mc P ih =>
    simp only [upper, List.map_cons, List.sum_cons, Rat.cast_add, eval_cons] at ih ⊢
    exact add_le_add (term_le_upper hB he mc) ih

namespace TM

def lower (B : Box) (T : TM) : ℚ := T.P.lower B - T.r
def upper (B : Box) (T : TM) : ℚ := T.P.upper B + T.r

theorem lower_le {B : Box} (hB : B.Valid) {S : Env → Prop} {T : TM} {f : Env → ℝ}
    (hT : T.Approx B S f) {e : Env} (he : B.Mem e) (hs : S e) : (T.lower B : ℝ) ≤ f e := by
  have h := (abs_le.mp (hT e he hs)).1
  have hp := Poly.lower_le_eval hB he T.P
  unfold lower
  push_cast
  linarith

theorem le_upper {B : Box} (hB : B.Valid) {S : Env → Prop} {T : TM} {f : Env → ℝ}
    (hT : T.Approx B S f) {e : Env} (he : B.Mem e) (hs : S e) : f e ≤ (T.upper B : ℝ) := by
  have h := (abs_le.mp (hT e he hs)).2
  have hp := Poly.eval_le_upper hB he T.P
  unfold upper
  push_cast
  linarith

theorem pos_of_lower_pos {B : Box} (hB : B.Valid) {S : Env → Prop} {T : TM} {f : Env → ℝ}
    (hT : T.Approx B S f) (hpos : 0 < T.lower B) {e : Env} (he : B.Mem e) (hs : S e) : 0 < f e :=
  lt_of_lt_of_le (by exact_mod_cast hpos) (lower_le hB hT he hs)

theorem neg_of_upper_neg {B : Box} (hB : B.Valid) {S : Env → Prop} {T : TM} {f : Env → ℝ}
    (hT : T.Approx B S f) (hneg : T.upper B < 0) {e : Env} (he : B.Mem e) (hs : S e) : f e < 0 :=
  lt_of_le_of_lt (le_upper hB hT he hs) (by exact_mod_cast hneg)

end TM

end E8Leech.Taylor
