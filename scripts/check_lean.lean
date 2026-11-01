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
  return none

/-- The constants that the declaration `c` refers to directly. -/
def directDeps (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some (.axiomInfo v) => v.type.getUsedConstants
  | some (.defnInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.thmInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
  | some (.ctorInfo v) => v.type.getUsedConstants
  | some (.recInfo v) => v.type.getUsedConstants
  | some (.inductInfo v) => v.type.getUsedConstants ++ v.ctors.toArray
  | some (.quotInfo _) | none => #[]

/-- The disallowed axioms that each of `thms` depends on, for those that
depend on any. Walks the declarations directly rather than using
`collectAxioms`, which reads axiom lists stored in compiled modules, and those
come from the submission. All the theorems share one walk, which records who
uses each constant, so the theorems that reach a disallowed axiom can be found
by walking back from it. -/
def disallowedAxioms (env : Environment) (thms : List Name) : NameMap (List Name) := Id.run do
  let mut seen : NameSet := thms.foldl (·.insert ·) {}
  let mut stack := thms
  let mut users : NameMap (Array Name) := {}
  let mut disallowed : List Name := []
  while true do
    let c :: rest := stack | break
    stack := rest
    if let some (.axiomInfo _) := env.find? c then
      unless c ∈ allowedAxioms do disallowed := c :: disallowed
    for d in directDeps env c do
      users := users.insert d ((users.getD d #[]).push c)
      unless seen.contains d do
        seen := seen.insert d
        stack := d :: stack
  let thmSet : NameSet := thms.foldl (·.insert ·) {}
  let mut result : NameMap (List Name) := {}
  for ax in disallowed do
    let mut reached : NameSet := NameSet.empty.insert ax
    let mut queue := [ax]
    while true do
      let c :: rest := queue | break
      queue := rest
      if thmSet.contains c then
        result := result.insert c (ax :: result.getD c [])
      for u in users.getD c #[] do
        unless reached.contains u do
          reached := reached.insert u
          queue := u :: queue
  return result

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

/-- Check certificates with their proof modules imported together. Returns the
errors for individual certificates, or a single error if the modules can't be
imported or the kernel rejects a declaration. -/
def checkGroup (group : List Cert) : IO (Except String (List (String × Json))) := do
  let proofModules := (group.map (·.proofModule)).eraseDups
  let modules := (group.map (·.statementModule)).eraseDups ++ proofModules
  -- Fails if a proof module redeclares something in a statement module or
  -- another proof module
  let env ← try
    importModules (modules.map ({ module := · })).toArray {}
  catch e =>
    return .error s!"Could not import {modules}: {e}"
  try
    replayProofs env
  catch e =>
    return .error s!"The kernel rejected a declaration in {proofModules}: {e}"
  let mut errors : List (String × Json) := []
  let mut passed : List Cert := []
  for c in group do
    match ← check env c with
    | some err => errors := (c.id, toJson err) :: errors
    | none => passed := c :: passed
  let disallowed := disallowedAxioms env (passed.map (·.thm))
  for c in passed do
    if let some axioms := disallowed.get? c.thm then
      errors := (c.id, toJson s!"Proof uses disallowed axioms: {axioms}") :: errors
  return .ok errors

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw <| .userError "usage: check_lean.lean <input.json>"
  let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile path)
  let certs ← IO.ofExcept <| json.getArr? >>= (·.toList.mapM Cert.ofJson)
  initSearchPath (← findSysroot)
  -- Importing every module once is fastest. If that fails, check one proof
  -- module at a time to find which one is to blame.
  let mut errors : List (String × Json) := []
  match ← checkGroup certs with
  | .ok errs => errors := errs
  | .error _ =>
    for proofModule in (certs.map (·.proofModule)).eraseDups do
      let group := certs.filter (·.proofModule == proofModule)
      match ← checkGroup group with
      | .ok errs => errors := errs ++ errors
      | .error e => errors := group.map (·.id, toJson e) ++ errors
  IO.println (Json.mkObj errors).compress
  return 0
