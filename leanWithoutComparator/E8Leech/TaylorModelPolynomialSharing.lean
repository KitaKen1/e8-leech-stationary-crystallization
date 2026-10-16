import E8Leech.TaylorModelRound
import E8Leech.TaylorModelLogDD

/-! A future reuse interface: polynomial calculations can be shared across boxes
at fixed orders. Remainders, endpoint bounds and signs still require separate proofs.
This file does not certify another rectangle or claim a measured speedup. -/

namespace E8Leech.Taylor.TM

theorem add_same_polynomial {X X' Y Y' : TM} (hx : X.P = X'.P) (hy : Y.P = Y'.P) :
    (X.add Y).P = (X'.add Y').P := by simp only [add, hx, hy]

theorem scale_same_polynomial (c : ℚ) {X X' : TM} (hx : X.P = X'.P) :
    (X.scale c).P = (X'.scale c).P := by simp only [scale, hx]

theorem sub_same_polynomial {X X' Y Y' : TM} (hx : X.P = X'.P) (hy : Y.P = Y'.P) :
    (X.sub Y).P = (X'.sub Y').P :=
  add_same_polynomial hx (scale_same_polynomial (-1) hy)

theorem mul_same_polynomial (B B' : Box) (D : ℕ) {X X' Y Y' : TM}
    (hx : X.P = X'.P) (hy : Y.P = Y'.P) :
    (TM.mul B D X Y).P = (TM.mul B' D X' Y').P := by simp only [mul, hx, hy]

theorem round_same_polynomial (B B' : Box) (p : ℕ) {X X' : TM} (hx : X.P = X'.P) :
    (X.round B p).P = (X'.round B' p).P := by simp only [round, hx]

theorem horner_same_polynomial (B B' : Box) (D : ℕ) {X X' : TM} (hx : X.P = X'.P)
    (cs : List ℚ) : (horner B D X cs).P = (horner B' D X' cs).P := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    exact add_same_polynomial rfl (mul_same_polynomial B B' D hx ih)

theorem inv1p_same_polynomial (B B' : Box) (D K : ℕ) {X X' : TM} (hx : X.P = X'.P) :
    (inv1p B D K X).P = (inv1p B' D K X').P :=
  horner_same_polynomial B B' D hx _

theorem log1p_same_polynomial (B B' : Box) (D n : ℕ) {X X' : TM} (hx : X.P = X'.P) :
    (log1p B D n X).P = (log1p B' D n X').P :=
  horner_same_polynomial B B' D hx _

theorem logRatioTM_same_polynomial (B B' : Box) (D n : ℕ) {X X' : TM} (hx : X.P = X'.P) :
    (logRatioTM B D n X).P = (logRatioTM B' D n X').P :=
  horner_same_polynomial B B' D hx _

end E8Leech.Taylor.TM

