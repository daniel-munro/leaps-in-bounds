/-
Check Lean certificates against their formal statements. Called by
scripts/certificates.py, from formal/, as

    lake env lean --run ../scripts/check_lean.lean <input.json>

The input is a JSON list of certificates, each with fields `id`,
`statementModule`, `statement` (the constant naming the bound, such as
`LeapsInBounds.Cage.LowerBound`), `args` (its natural number arguments),
`proofModule` and `theorem`. Prints a JSON object mapping the ID of each
certificate that fails to an error message.

The expected type is built directly as an expression, rather than parsed and
elaborated, so nothing in the submission (notation, macros, instances,
unification hints) can change what it means. The proof modules are loaded
without running any of their code: only their declarations are read, and the
type of each theorem is compared with the expected type by syntactic equality
or, failing that, by the kernel.

Every declaration in the proof modules is also replayed through the kernel on
top of the other imported modules, so a compiled proof module is trusted no
more than its source would be, even if it was tampered with.
-/
import Lean

open Lean

/-- Axioms a proof may depend on. Notably excludes `sorryAx` and
`Lean.ofReduceBool` (used by `native_decide`, which trusts the compiler). -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

structure Cert where
  id : String
  statementModule : Name
  statement : Name
  args : List Nat
  proofModule : Name
  thm : Name

def Cert.ofJson (j : Json) : Except String Cert := do
  let name (field : String) : Except String Name := return (← j.getObjValAs? String field).toName
  return {
    id := ← j.getObjValAs? String "id"
    statementModule := ← name "statementModule"
    statement := ← name "statement"
    args := ← j.getObjValAs? (List Nat) "args"
    proofModule := ← name "proofModule"
    thm := ← name "theorem"
  }

/-- Check one certificate, returning an error message if it fails. -/
def check (env : Environment) (c : Cert) : IO (Option String) := do
  -- The statement must be the trusted one, not a declaration of the same name
  -- elsewhere. (Importing two declarations with the same name fails.)
  unless (env.getModuleIdxFor? c.statement).isSome &&
      env.getModuleIdxFor? c.statement == env.getModuleIdx? c.statementModule do
    return s!"{c.statement} is not declared in {c.statementModule}"
  let some info := env.find? c.thm
    | return s!"Unknown theorem {c.thm}"
  unless env.getModuleIdxFor? c.thm == env.getModuleIdx? c.proofModule do
    return s!"{c.thm} is not declared in {c.proofModule}"
  let .thmInfo val := info
    | return s!"{c.thm} is not a theorem"
  unless val.levelParams.isEmpty do
    return s!"{c.thm} has universe parameters"
  let expected := mkAppN (mkConst c.statement) (c.args.map mkNatLit).toArray
  unless val.type == expected || Kernel.isDefEqGuarded env {} val.type expected do
    return s!"{c.thm} has type `{val.type}`, not `{expected}`"
  let axioms ← (collectAxioms c.thm : CoreM _).toIO' { fileName := "<check>", fileMap := default } { env }
  let disallowed := axioms.toList.filter (· ∉ allowedAxioms)
  unless disallowed.isEmpty do
    return s!"Proof uses disallowed axioms: {disallowed}"
  return none

/-- Modules whose compiled files come from the submission rather than from the
trusted build. -/
def isProofModule (module : Name) : Bool :=
  (`LeapsInBounds.Proofs).isPrefixOf module

/-- Send every declaration in the proof modules imported by `env` to the
kernel, on top of an environment that imports only the other modules. -/
def replayProofs (env : Environment) : IO Unit := do
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  for module in env.header.moduleNames, data in env.header.moduleData do
    if isProofModule module then
      for name in data.constNames, info in data.constants do
        newConstants := newConstants.insert name info
  let trusted := env.header.moduleNames.filter (!isProofModule ·)
  let base ← importModules (trusted.map ({ module := · })) {}
  discard <| base.toKernelEnv.replay newConstants

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw <| .userError "usage: check_lean.lean <input.json>"
  let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile path)
  let certs ← IO.ofExcept <| json.getArr? >>= (·.toList.mapM Cert.ofJson)
  initSearchPath (← findSysroot)
  let mut errors : List (String × Json) := []
  for proofModule in (certs.map (·.proofModule)).eraseDups do
    let group := certs.filter (·.proofModule == proofModule)
    let modules := (group.map (·.statementModule)).eraseDups ++ [proofModule]
    -- Fails if the proof module redeclares something in a statement module
    let env ← try
      importModules (modules.map ({ module := · })).toArray {}
    catch e =>
      for c in group do
        errors := (c.id, toJson s!"Could not import {modules}: {e}") :: errors
      continue
    try
      replayProofs env
    catch e =>
      for c in group do
        errors := (c.id, toJson s!"The kernel rejected a declaration in {proofModule}: {e}") :: errors
      continue
    for c in group do
      if let some err ← check env c then
        errors := (c.id, toJson err) :: errors
  IO.println (Json.mkObj errors.reverse).compress
  return 0
