/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in Mathlib's LICENSE.
Adapted from the pinned Lean 4.33.1 LeanChecker.lean module-data loading routine.

Replay all selected project declarations together against external imports.
Load each module's exported/server/private parts as the bundled checker does.
External imports are finalized once; project constants are sent to the same
Lean kernel via Environment.replay. This is not an independent implementation.
-/
import Lean.CoreM
import Lean.Replay

open Lean

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  if args.isEmpty then throw <| IO.userError "No project modules supplied"
  let modules := args.map String.toName
  let selected : NameSet := modules.foldl (fun s n => s.insert n) {}
  let mut external : Array Import := #[]
  let mut constants : Std.HashMap Name ConstantInfo := {}
  for module in modules do
    let mFile ← findOLean module
    unless (← mFile.pathExists) do
      throw <| IO.userError s!"Missing object: {module}"
    let mut fnames := #[mFile]
    let sFile := OLeanLevel.server.adjustFileName mFile
    if (← sFile.pathExists) then
      fnames := fnames.push sFile
      let pFile := OLeanLevel.private.adjustFileName mFile
      if (← pFile.pathExists) then fnames := fnames.push pFile
    let parts ← readModuleDataParts fnames
    if h : parts.size = 0 then throw <| IO.userError "Empty module data" else
      let (mod, _) := parts[0]
      external := external ++ mod.imports.filter (fun i => !selected.contains i.module)
      for name in parts[parts.size - 1].1.constNames,
          ci in parts[parts.size - 1].1.constants do
        constants := constants.insert name ci
      IO.println s!"loaded {module}"
  IO.println s!"project declaration inventory: {constants.size}"
  let (_, state) ← importModulesCore external |>.run
  let env ← finalizeImport state external {} 0 false false (isModule := true)
  for (name, _) in constants.toList do
    if env.contains name then
      throw <| IO.userError s!"Project declaration already in imported environment: {name}"
  let checked ← env.replay constants
  checked.freeRegions
  for module in modules do IO.println s!"replaying {module}"
  IO.println "Aggregate project replay passed"
  return 0
