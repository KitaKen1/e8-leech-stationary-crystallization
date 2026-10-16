import E8Leech.CKMRVKernelSLP
import E8Leech.TaylorModelRound

/-! Round every shared-program instruction outward, preserving its real semantics. -/

namespace E8Leech.Taylor.SLP

def runDDRounded (B : Box) (Dg p : ℕ) (G : Fin 5 → DD) (L : Fin 3 → DD) :
    List Instr → List DD → List DD
  | [], regs => regs
  | ins :: rest, regs => runDDRounded B Dg p G L rest
      (regs ++ [DD.round B p (stepDD B Dg G L regs ins)])

theorem approx_runDDRounded {B : Box} (hB : B.Valid) (Dg p : ℕ) {S : Env → Prop} {G : Fin 5 → DD}
    {L : Fin 3 → DD}
    (hG : ∀ i, (G i).Approx B S (fun e => genFun i e.a) (fun e => genFun i e.b))
    (hL : ∀ j, (L j).Approx B S (fun e => logFun j e.a) (fun e => logFun j e.b)) :
    ∀ (prog : List Instr) (regs : List DD) (ra rb : Env → List ℝ),
      (∀ e, (ra e).length = regs.length ∧ (rb e).length = regs.length) →
      (∀ k, (regs.getD k dd0).Approx B S (fun e => (ra e).getD k 0) (fun e => (rb e).getD k 0)) →
      ∀ k, ((runDDRounded B Dg p G L prog regs).getD k dd0).Approx B S
        (fun e => (runR true e prog (ra e)).getD k 0) (fun e => (runR false e prog (rb e)).getD k 0)
  | [], regs, ra, rb, _, hk => hk
  | ins :: rest, regs, ra, rb, hlen, hk => by
    simp only [runDDRounded, runR]
    refine approx_runDDRounded hB Dg p hG hL rest _ (fun e => ra e ++ [stepR true e (ra e) ins])
      (fun e => rb e ++ [stepR false e (rb e) ins]) (fun e => ?_) (fun k => ?_)
    · simp [(hlen e).1, (hlen e).2]
    · have hstep := DD.approx_round hB p (approx_stepDD hB Dg hG hL hk ins)
      have hfun : ∀ (f : Env → List ℝ) (g : Env → ℝ), (∀ e, (f e).length = regs.length) →
          (fun e => (f e ++ [g e]).getD k 0) =
            fun e => if k < regs.length then (f e).getD k 0 else if k = regs.length then g e else 0 := by
        intro f g hf
        funext e
        rw [getD_append_single, hf e]
      rw [hfun _ _ fun e => (hlen e).1, hfun _ _ fun e => (hlen e).2, getD_append_single]
      split_ifs with h1 h2
      · exact hk k
      · exact hstep
      · exact approx_dd0

/-- Run a program from the empty register file. -/
theorem approx_runRounded {B : Box} (hB : B.Valid) (Dg p : ℕ) {S : Env → Prop} {G : Fin 5 → DD}
    {L : Fin 3 → DD}
    (hG : ∀ i, (G i).Approx B S (fun e => genFun i e.a) (fun e => genFun i e.b))
    (hL : ∀ j, (L j).Approx B S (fun e => logFun j e.a) (fun e => logFun j e.b))
    (prog : List Instr) (k : ℕ) :
    ((runDDRounded B Dg p G L prog []).getD k dd0).Approx B S
      (fun e => (runR true e prog []).getD k 0) (fun e => (runR false e prog []).getD k 0) :=
  approx_runDDRounded hB Dg p hG hL prog [] (fun _ => []) (fun _ => []) (fun _ => by simp)
    (fun k => by simpa using approx_dd0) k

theorem approx_checkedRounded {B : Box} (hB : B.Valid) (D p : ℕ) {S : Env → Prop}
    {G : Fin 5 → DD} {L : Fin 3 → DD}
    (hG : ∀ i, (G i).Approx B S (fun e => genFun i e.a) (fun e => genFun i e.b))
    (hL : ∀ j, (L j).Approx B S (fun e => logFun j e.a) (fun e => logFun j e.b))
    (prog : List Instr) (k : ℕ) (x : KExpr) (h : (runExpr prog []).getD k (.cst 0) = x) :
    ((runDDRounded B D p G L prog []).getD k dd0).Approx B S (KExpr.evalA x) (KExpr.evalB x) := by
  have ha : (fun e => (runR true e prog []).getD k 0) = KExpr.evalA x := by
    funext e
    rw [← eval_runExpr_getD, h]
    rfl
  have hb : (fun e => (runR false e prog []).getD k 0) = KExpr.evalB x := by
    funext e
    rw [← eval_runExpr_getD, h]
    rfl
  simpa only [ha, hb] using approx_runRounded hB D p hG hL prog k

end E8Leech.Taylor.SLP
