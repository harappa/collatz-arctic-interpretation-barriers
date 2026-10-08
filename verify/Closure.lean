/-
Counts the modules `CollatzProof.Arctic.*` in the import closure and the constants declared in them, traverses every
constant reachable from these constants (including those of Mathlib and of the Lean core), and prints the axioms met
on the way. (Modules are counted from the import closure, so that a file with only `example`s, which declares no
constant, such as `Nat/NonVacuityW2a.lean`, is counted as well.)
The root module `CollatzProof.Arctic.Paper` imports every file of `CollatzProof/Arctic` (through `Paper5.lean` also
the files of `Nat/` and `DPFilter*.lean`), so the modules counted are all 285 files of the directory.
Run with `lake env lean verify/Closure.lean` after `lake build`.
Expected output: 285 modules, and the axioms `propext`, `Classical.choice` and `Quot.sound` only.
-/
import CollatzProof.Arctic.Paper
open Lean Elab Command

/-- All constants reachable from `todo` through the constants used in types and values. -/
def reachable (env : Environment) (todo : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := todo
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for m in ci.getUsedConstantsAsSet.toList do
        if !seen.contains m then stack := stack.push m
  return seen

run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut own : Array Name := #[]
  let mut modset : NameSet := {}
  for m in mods do
    if (`CollatzProof.Arctic).isPrefixOf m then
      modset := modset.insert m
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := mods[idx.toNat]!
      if (`CollatzProof.Arctic).isPrefixOf m then
        own := own.push n
  let reach := reachable env own
  let mut axs : Array Name := #[]
  for n in reach.toList do
    if let some (.axiomInfo _) := env.find? n then axs := axs.push n
  let sorted := axs.qsort (fun a b => a.toString < b.toString)
  logInfo m!"modules: {modset.size}, declared constants: {own.size}, reachable constants: {reach.size}, axioms: {sorted.toList}"
