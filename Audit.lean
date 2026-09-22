import HoffmanChromatic
import Lean.Util.CollectAxioms

/-!
Discover every declaration by its source module, including private declarations
and definitions. This audit does not rely on a handwritten theorem list.
Compiler runtime staging code is counted separately and is required to be absent
from the transitive mathematical dependency closure.
-/
open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let mut names : Array Name := #[]
  let mut theoremCount := 0
  let mut definitions := 0
  let mut runtimeOnly := 0
  for moduleName in env.header.moduleNames do
    logInfo m!"IMPORTED_MODULE {moduleName}"
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[idx.toNat]!
      if moduleName == `HoffmanChromatic ||
          "HoffmanChromatic.".isPrefixOf moduleName.toString then
        if ci.isUnsafe then
          unless (name.toString.splitOn "._cstage").length > 1 ||
              ((name.toString.splitOn "._at.").length > 1 &&
               (name.toString.splitOn "._spec_").length > 1) do
            throwError "Unexpected unsafe declaration: {name}"
          runtimeOnly := runtimeOnly + 1
          logInfo m!"COMPILER_RUNTIME_ONLY {name}"
        else
          match ci with
          | .axiomInfo _ => throwError "Project-local axiom: {name}"
          | .thmInfo _ => theoremCount := theoremCount + 1
          | .defnInfo _ => definitions := definitions + 1
          | _ => pure ()
          names := names.push name
          logInfo m!"CHECKED_DECLARATION {moduleName} {name}"
  unless names.size > 0 do
    throwError "No project declarations discovered"
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  for dep in state.axioms do
    unless allowed.contains dep do
      throwError "Unexpected axiom in aggregate transitive dependencies: {dep}"
  for dep in state.visited.toList do
    if let some ci := env.checked.get.find? dep then
      if ci.isUnsafe then
        throwError "Unsafe declaration in mathematical dependency closure: {dep}"
  logInfo m!"PASS: dynamically checked {names.size} mathematical declarations; {theoremCount} theorems (including generated equations), {definitions} definitions. Only propext, Classical.choice and Quot.sound; no unsafe declaration or project-local axiom in the mathematical dependency closure. {runtimeOnly} compiler runtime staging declarations are outside this closure."
