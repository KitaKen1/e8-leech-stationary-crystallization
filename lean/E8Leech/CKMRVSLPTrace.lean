import E8Leech.CKMRVSLPRound

/-!
# Checked register witnesses for rounded shared programs

Precomputed register values are untrusted. The checker validates each instruction
against the preceding register file, rejects forward references and requires exactly
one witness per instruction. Individual equality proofs can be shared between stages.
-/

namespace E8Leech.Taylor

deriving instance DecidableEq for TM
deriving instance DecidableEq for DD

namespace SLP

def checkScope (size : ℕ) : Instr → Bool
  | .add i j | .sub i j | .mul i j => decide (i < size ∧ j < size)
  | _ => true

def checkRoundedTrace (B : Box) (D p : ℕ) (G : Fin 5 → DD) (L : Fin 3 → DD) :
    List Instr → List DD → List DD → Bool
  | [], [], _ => true
  | ins :: prog, w :: ws, regs =>
      checkScope regs.length ins && decide (w = DD.round B p (stepDD B D G L regs ins)) &&
        checkRoundedTrace B D p G L prog ws (regs ++ [w])
  | _, _, _ => false

theorem checkRoundedTrace_cons {B : Box} {D p : ℕ} {G : Fin 5 → DD} {L : Fin 3 → DD}
    {ins : Instr} {prog : List Instr} {w : DD} {ws regs : List DD}
    (hs : checkScope regs.length ins = true)
    (hw : w = DD.round B p (stepDD B D G L regs ins))
    (ht : checkRoundedTrace B D p G L prog ws (regs ++ [w]) = true) :
    checkRoundedTrace B D p G L (ins :: prog) (w :: ws) regs = true := by
  simp only [checkRoundedTrace, hs, decide_eq_true hw, ht, Bool.and_self]

theorem checkRoundedTrace_length {B : Box} {D p : ℕ} {G : Fin 5 → DD} {L : Fin 3 → DD}
    {prog : List Instr} {ws regs : List DD}
    (h : checkRoundedTrace B D p G L prog ws regs = true) : ws.length = prog.length := by
  induction prog generalizing ws regs with
  | nil => cases ws <;> simp_all [checkRoundedTrace]
  | cons ins prog ih =>
    cases ws with
    | nil => simp [checkRoundedTrace] at h
    | cons w ws =>
      have ht := (Bool.and_eq_true_iff.mp h).2
      simpa using congrArg Nat.succ (ih ht)

theorem checkRoundedTrace_eq_run {B : Box} {D p : ℕ} {G : Fin 5 → DD} {L : Fin 3 → DD}
    {prog : List Instr} {ws regs : List DD}
    (h : checkRoundedTrace B D p G L prog ws regs = true) :
    regs ++ ws = runDDRounded B D p G L prog regs := by
  induction prog generalizing ws regs with
  | nil => cases ws <;> simp_all [checkRoundedTrace, runDDRounded]
  | cons ins prog ih =>
    cases ws with
    | nil => simp [checkRoundedTrace] at h
    | cons w ws =>
      obtain ⟨hh, ht⟩ := Bool.and_eq_true_iff.mp h
      have hw : w = DD.round B p (stepDD B D G L regs ins) :=
        of_decide_eq_true (Bool.and_eq_true_iff.mp hh).2
      have hr := ih ht
      simpa only [List.append_assoc, List.singleton_append, runDDRounded, hw] using hr

/-- Join checked stages without evaluating their register calculations again. -/
theorem checkRoundedTrace_append {B : Box} {D p : ℕ} {G : Fin 5 → DD} {L : Fin 3 → DD}
    {prog₁ prog₂ : List Instr} {ws₁ ws₂ regs : List DD}
    (h₁ : checkRoundedTrace B D p G L prog₁ ws₁ regs = true)
    (h₂ : checkRoundedTrace B D p G L prog₂ ws₂ (regs ++ ws₁) = true) :
    checkRoundedTrace B D p G L (prog₁ ++ prog₂) (ws₁ ++ ws₂) regs = true := by
  induction prog₁ generalizing ws₁ regs with
  | nil =>
    cases ws₁ with
    | nil => simpa only [List.nil_append, List.append_nil] using h₂
    | cons w ws => simp [checkRoundedTrace] at h₁
  | cons ins prog ih =>
    cases ws₁ with
    | nil => simp [checkRoundedTrace] at h₁
    | cons w ws =>
      obtain ⟨hh, ht⟩ := Bool.and_eq_true_iff.mp h₁
      have hw := (Bool.and_eq_true_iff.mp hh).2
      have hs := (Bool.and_eq_true_iff.mp hh).1
      apply checkRoundedTrace_cons hs (of_decide_eq_true hw)
      apply ih ht
      simpa only [List.append_assoc, List.singleton_append] using h₂

/-- Extend a previously checked prefix using just the new instruction's equality. -/
theorem checkRoundedTrace_snoc {B : Box} {D p : ℕ} {G : Fin 5 → DD} {L : Fin 3 → DD}
    {prog : List Instr} {ws regs : List DD} {ins : Instr} {w : DD}
    (ht : checkRoundedTrace B D p G L prog ws regs = true)
    (hs : checkScope (regs ++ ws).length ins = true)
    (hw : w = DD.round B p (stepDD B D G L (regs ++ ws) ins)) :
    checkRoundedTrace B D p G L (prog ++ [ins]) (ws ++ [w]) regs = true :=
  checkRoundedTrace_append ht (checkRoundedTrace_cons hs hw rfl)

theorem approx_checkedTrace {B : Box} (hB : B.Valid) (D p : ℕ) {S : Env → Prop}
    {G : Fin 5 → DD} {L : Fin 3 → DD}
    (hG : ∀ i, (G i).Approx B S (fun e => genFun i e.a) (fun e => genFun i e.b))
    (hL : ∀ j, (L j).Approx B S (fun e => logFun j e.a) (fun e => logFun j e.b))
    (prog : List Instr) (ws : List DD) (k : ℕ) (x : KExpr)
    (ht : checkRoundedTrace B D p G L prog ws [] = true)
    (hx : (runExpr prog []).getD k (.cst 0) = x) :
    (ws.getD k dd0).Approx B S (KExpr.evalA x) (KExpr.evalB x) := by
  have he : ws = runDDRounded B D p G L prog [] := by
    simpa only [List.nil_append] using checkRoundedTrace_eq_run ht
  rw [he]
  exact approx_checkedRounded hB D p hG hL prog k x hx

end SLP
end E8Leech.Taylor
