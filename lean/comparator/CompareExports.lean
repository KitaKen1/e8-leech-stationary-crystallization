import Comparator
import Export.Parse

/-! Development statement/definition and axiom comparison using upstream APIs.
This does not replace the complete upstream CLI or perform kernel replay.
-/

open Lean

def main (args : List String) : IO Unit := do
  let [configPath, challengePath, solutionPath] := args
    | throw <| IO.userError "usage: CompareExports config.json challenge.ndjson solution.ndjson"
  let config ← IO.ofExcept <| Json.parse (← IO.FS.readFile configPath)
  let targetStrings : Array String ← IO.ofExcept <| fromJson? (← IO.ofExcept <| config.getObjVal? "theorem_names")
  let axiomStrings : Array String ← IO.ofExcept <| fromJson? (← IO.ofExcept <| config.getObjVal? "permitted_axioms")
  let targets := targetStrings.map String.toName
  let axioms := axiomStrings.map String.toName
  let h₁ ← IO.FS.Handle.mk challengePath .read
  let h₂ ← IO.FS.Handle.mk solutionPath .read
  let challenge ← Export.parseStream (IO.FS.Stream.ofHandle h₁)
  let solution ← Export.parseStream (IO.FS.Stream.ofHandle h₂)
  let primitives : Array Name := #[``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow,
    ``Nat.gcd, ``Nat.div, ``Nat.mod, ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor,
    ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight, ``String.ofList, ``Char.ofNat,
    ``List, ``eagerReduce]
  IO.ofExcept <| Comparator.compareAt challenge solution (targets ++ axioms) #[] primitives
  IO.ofExcept <| Comparator.checkAxioms solution targets #[] axioms
  IO.println "LOCAL_STATEMENT_DEFINITION_AND_AXIOM_COMPARISON_PASS"
