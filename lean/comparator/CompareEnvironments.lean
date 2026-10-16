import Lean
import Comparator
open Lean

def exported (env : Environment) : Export.ExportedEnv := Id.run do
  let mut m := {}
  for (n,c) in env.constants.toList do
    m := m.insert n c
  return { constMap := m, constOrder := #[] }

unsafe def main (args : List String) : IO Unit := do
  let [configPath] := args | throw <| IO.userError "usage: compareEnvironments config.json"
  initSearchPath (← findSysroot)
  let config ← IO.ofExcept <| Json.parse (← IO.FS.readFile configPath)
  let targetStrings : Array String ← IO.ofExcept <| fromJson? (← IO.ofExcept <| config.getObjVal? "theorem_names")
  let axiomStrings : Array String ← IO.ofExcept <| fromJson? (← IO.ofExcept <| config.getObjVal? "permitted_axioms")
  let targets := targetStrings.map String.toName
  let axioms := axiomStrings.map String.toName
  IO.println "Importing independent reference"
  let a ← importModules #[{ module := `Challenge }] {} (loadExts := false)
  IO.println "Importing solution"
  let b ← importModules #[{ module := `FCSolution }] {} (loadExts := false)
  IO.println "Building constant maps"
  let ca := exported a
  let cb := exported b
  IO.println "Comparing targets and definitions"
  IO.ofExcept <| Comparator.compareAt ca cb (targets ++ axioms) #[] #[]
  IO.println "Checking all target proof dependencies for axioms"
  IO.ofExcept <| Comparator.checkAxioms cb targets #[] axioms
  IO.println "LOCAL_STATEMENT_DEFINITION_AND_AXIOM_COMPARISON_PASS"
