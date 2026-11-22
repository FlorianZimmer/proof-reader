import Lean
open Lean Elab Command

/-!
Diagnostic support, outside the authors' sources. `#dump_closure n` prints one
JSON line for `n` and for every constant in the `Breakdown` namespace that `n`
uses, transitively. Each line holds the full constant data a kernel comparison
can see: kind, universe names, type and value (binder names and metadata kept,
and separately erased), reducibility hints, safety, and the `all` list.
-/

namespace Audit2

partial def eraseNames : Expr → Expr
  | .lam _ t b bi => .lam .anonymous (eraseNames t) (eraseNames b) bi
  | .forallE _ t b bi => .forallE .anonymous (eraseNames t) (eraseNames b) bi
  | .letE _ t v b nd => .letE .anonymous (eraseNames t) (eraseNames v) (eraseNames b) nd
  | .app f x => .app (eraseNames f) (eraseNames x)
  | .mdata _ e => eraseNames e
  | .proj n i e => .proj n i (eraseNames e)
  | e => e

def hintsStr : ReducibilityHints → String
  | .opaque => "opaque"
  | .abbrev => "abbrev"
  | .regular h => s!"regular {h}"

def kindStr : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def extraJson : ConstantInfo → List (String × Json)
  | .defnInfo v => [("hints", toJson (hintsStr v.hints)), ("safety", toJson (reprStr v.safety)),
      ("all", toJson (v.all.map Name.toString))]
  | .thmInfo v => [("all", toJson (v.all.map Name.toString))]
  | .opaqueInfo v => [("isUnsafe", toJson v.isUnsafe), ("all", toJson (v.all.map Name.toString))]
  | .inductInfo v => [("ctors", toJson (v.ctors.map Name.toString)), ("numParams", toJson v.numParams),
      ("numIndices", toJson v.numIndices), ("isRec", toJson v.isRec), ("isUnsafe", toJson v.isUnsafe)]
  | _ => []

def recordJson (c : ConstantInfo) : Json :=
  Json.mkObj ([
    ("closure_name", toJson c.name.toString),
    ("kind", toJson (kindStr c)),
    ("levels", toJson (c.levelParams.map Name.toString)),
    ("type", toJson (reprStr c.type)),
    ("type_erased", toJson (reprStr (eraseNames c.type))),
    ("value", match c.value? with
      | some e => toJson (reprStr e) | none => Json.null),
    ("value_erased", match c.value? with
      | some e => toJson (reprStr (eraseNames e)) | none => Json.null)] ++ extraJson c)

partial def visit (env : Environment) (n : Name) (seen : NameSet) : NameSet × Array Name :=
  if seen.contains n then (seen, #[]) else
  let seen := seen.insert n
  match env.find? n with
  | none => (seen, #[n])
  | some c =>
    let deps := c.getUsedConstantsAsSet.toList.filter fun m => (`Breakdown).isPrefixOf m
    deps.foldl (fun (acc : NameSet × Array Name) m =>
      let r := visit env m acc.1
      (r.1, acc.2 ++ r.2)) (seen, #[n])

elab "#dump_closure " id:ident : command => do
  let env ← getEnv
  let (_, names) := visit env id.getId {}
  for n in names do
    match env.find? n with
    | some c => liftIO <| IO.println (recordJson c).compress
    | none => liftIO <| IO.println (Json.mkObj [("closure_name", toJson n.toString),
        ("kind", toJson "missing")]).compress

/-- Whether a constant is an auxiliary proof made by abstracting a nested proof
during elaboration (`foo._proof_3`). Its name depends on declaration order. -/
def isAuxProof (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "_proof_"
  | _ => false

/-- Replace every auxiliary proof constant by a name made from the hash of its
statement, so that two aux proofs of the same proposition compare equal. -/
def normalizeAux (env : Environment) (e : Expr) : Expr :=
  e.replace fun s => match s with
    | .const n us =>
      if isAuxProof n then
        match env.find? n with
        | some c => some (.const (Name.mkSimple s!"AUX_{hash (reprStr (eraseNames c.type))}") us)
        | none => none
      else none
    | _ => none

/-- Constants of the statement closure: theorems contribute their type only,
definitions their type and value; only `Breakdown` names are followed. -/
partial def visitStmt (env : Environment) (n : Name) (seen : NameSet) : NameSet × Array Name :=
  if seen.contains n then (seen, #[]) else
  let seen := seen.insert n
  match env.find? n with
  | none => (seen, #[n])
  | some c =>
    let used : Array Name := match c with
      | .thmInfo v => v.type.getUsedConstants
      | _ => c.getUsedConstantsAsSet.toList.toArray
    let deps := used.toList.filter fun m => (`Breakdown).isPrefixOf m && !isAuxProof m
    deps.foldl (fun (acc : NameSet × Array Name) m =>
      let r := visitStmt env m acc.1
      (r.1, acc.2 ++ r.2)) (seen, #[n])

/-- One line per constant of the statement closure of the given theorems: hashes
and lengths of the normalized type and value, and the reducibility hints. -/
elab "#dump_statement_hashes " ids:ident* : command => do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut names : Array Name := #[]
  for id in ids do
    let (s, out) := visitStmt env id.getId seen
    seen := s
    names := names ++ out
  for n in names do
    match env.find? n with
    | some c =>
      let ty := reprStr (eraseNames (normalizeAux env c.type))
      let val := match c with
        | .thmInfo _ => ""
        | _ => match c.value? with
          | some e => reprStr (eraseNames (normalizeAux env e))
          | none => ""
      let hints := match c with
        | .defnInfo v => hintsStr v.hints
        | _ => ""
      liftIO <| IO.println (Json.mkObj [("stmt_name", toJson n.toString),
        ("kind", toJson (kindStr c)), ("levels", toJson (c.levelParams.map Name.toString)),
        ("type_hash", toJson (toString (hash ty))), ("type_len", toJson ty.length),
        ("value_hash", toJson (toString (hash val))), ("value_len", toJson val.length),
        ("hints", toJson hints)]).compress
    | none => liftIO <| IO.println (Json.mkObj [("stmt_name", toJson n.toString),
        ("kind", toJson "missing")]).compress

end Audit2
