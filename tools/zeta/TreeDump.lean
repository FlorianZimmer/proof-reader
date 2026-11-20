/-
Proof-tree dump for kernel-checked numerical certificates (core Lean only; no Mathlib).

`dumpTree e` walks a proof term and records one node per lemma application:
the lemma, the statement it proves at that point (its type instantiated at the arguments),
and the children that are themselves proofs. Values passed to the lemma (reals, naturals,
expressions) are recorded in the statement, not as children. Three node kinds matter for
the zeta certificates:

* `lemma`: an ordinary theorem applied to arguments;
* `sealed`: a module auxiliary lemma (a checkpoint or a cached closed enclosure); its body
  is walked once and shared by every citation;
* `kernel`: `Eq.refl`/`rfl`-style leaves, where the kernel decides the statement by evaluation
  rather than by a lemma.

If the statement is `Real.IsNear x neg cn cd rn rd` (|x − ±cn/cd| ≤ rn/rd) the node also
carries the enclosure's centre and radius; `Complex.IsNear` carries both rectangles.

Output is JSON: `{root, nodes: [{id, head, kind, statement, subject?, re?, im?, children}]}`.
Shared subproofs appear once (keyed by the term), so the result is a DAG.
-/
import Lean
open Lean Meta

namespace TreeDump

structure Encl where
  neg : Bool
  cn : Nat
  cd : Nat
  rn : Nat
  rd : Nat
  deriving ToJson

structure Node where
  id : Nat
  head : String
  kind : String
  statement : String
  subject : Option String := none
  re : Option Encl := none
  im : Option Encl := none
  nargs : Nat := 0
  children : Array Nat := #[]
  /-- The binder name each child fills in `head` (the field or hypothesis it proves). -/
  labels : Array String := #[]
  /-- For `kernel` leaves: the head of the expression the kernel must evaluate (e.g. `Nat.ble`). -/
  reduces : Option String := none
  deriving ToJson

structure St where
  nodes : Array Node := #[]
  seen : Std.HashMap Expr Nat := {}

structure Cfg where
  maxNodes : Nat := 6000
  stmtChars : Nat := 400

abbrev M := ReaderT Cfg (StateRefT St MetaM)

def natOf? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | e => match e.nat? with
    | some n => some n
    | none => e.rawNatLit?

def boolOf? (e : Expr) : Option Bool :=
  if e.isConstOf ``Bool.true then some true
  else if e.isConstOf ``Bool.false then some false else none

def enclOf? (neg cn cd rn rd : Expr) : Option Encl := do
  return { neg := ← boolOf? neg, cn := ← natOf? cn, cd := ← natOf? cd,
           rn := ← natOf? rn, rd := ← natOf? rd }

def endsWith (n : Name) (s : String) : Bool := n.toString.endsWith s

/-- Auxiliary lemmas made by `mkAuxLemma` (checkpoints and cached closed enclosures). -/
def isAux (n : Name) : Bool :=
  (n.toString.splitOn "_auxLemma").length > 1 || n.isInternal

def kernelLeaf (n : Name) : Bool :=
  n == ``Eq.refl || n == ``rfl || n == ``HEq.refl || endsWith n "reflBoolTrue"
    || n == ``of_decide_eq_true

def pp (e : Expr) (k : Nat) : MetaM String := do
  let s ← try
      withOptions (fun o => o |>.setBool `pp.proofs false |>.setBool `pp.deepTerms false
          |>.set `pp.deepTerms.threshold (8 : Nat)) do
        return toString (← ppExpr e)
    catch _ => pure "(could not print)"
  let s := s.replace "\n" " "
  return if s.length > k then (s.take k).toString ++ " …" else s

/-- Instantiate `ty` at `args`, returning the conclusion and, for each argument, whether its
binder type is a proposition (so the argument is a proof to walk). -/
def splitArgs (ty : Expr) (args : Array Expr) : MetaM (Expr × Array (Bool × Name × Expr)) := do
  let mut t := ty
  let mut isPf : Array (Bool × Name × Expr) := #[]
  for a in args do
    let t' ← whnfR t
    match t' with
    | .forallE nm d b _ =>
      isPf := isPf.push ((← (try isProp d catch _ => pure false)), nm, d)
      t := b.instantiate1 a
    | _ => isPf := isPf.push (false, .anonymous, mkConst ``True)
  return (t, isPf)

/-- The left side of `lhs = rhs`, `lhs ≤ rhs`, … : what the kernel has to evaluate for a refl leaf. -/
def reducedHead (t : Expr) : Option String :=
  let a := t.getAppArgs
  let lhs := if t.isAppOf ``Eq && a.size == 3 then a[1]! else t
  lhs.getAppFn.constName?.map (·.toString)

partial def walk (e : Expr) (expected : Option Expr := none) : M Nat := do
  let e := e.consumeMData
  -- a refl leaf proves whatever its parent asks for, so it is keyed by that statement too
  let isKernelLeaf := match e.getAppFn with | .const c _ => kernelLeaf c | _ => false
  let key := match expected, isKernelLeaf with
    | some t, true => mkApp2 (mkConst `TreeDump.kernelKey) e t
    | _, _ => e
  if let some i := (← get).seen[key]? then return i
  let cfg ← read
  let id := (← get).nodes.size
  -- reserve the slot so cycles through sharing cannot recurse forever
  modify fun s => { s with seen := s.seen.insert key id,
                           nodes := s.nodes.push { id, head := "", kind := "pending", statement := "" } }
  let fn := e.getAppFn
  let args := e.getAppArgs
  let mut node : Node := { id, head := "", kind := "other", statement := "" }
  match fn with
  | .const c us =>
    let ci ← getConstInfo c
    let (concl, isPf) ← splitArgs (ci.instantiateTypeLevelParams us) args
    let concl ← instantiateMVars concl
    -- for a refl leaf, show what the parent needs proved (e.g. `Nat.ble a b = true`), not `true = true`
    let shown := if isKernelLeaf then (expected.getD concl) else concl
    node := { node with head := c.toString, nargs := args.size,
                        statement := ← pp shown cfg.stmtChars,
                        reduces := if isKernelLeaf then reducedHead shown else none,
                        kind := if kernelLeaf c then "kernel" else if isAux c then "sealed" else "lemma" }
    -- enclosure fields
    let cf := concl.getAppFn
    let ca := concl.getAppArgs
    if let .const h _ := cf then
      if endsWith h "Real.IsNear" && ca.size == 6 then
        node := { node with subject := some (← pp ca[0]! 200), re := enclOf? ca[1]! ca[2]! ca[3]! ca[4]! ca[5]! }
      else if endsWith h "Complex.IsNear" && ca.size == 11 then
        node := { node with subject := some (← pp ca[0]! 200),
                            re := enclOf? ca[1]! ca[2]! ca[3]! ca[4]! ca[5]!,
                            im := enclOf? ca[6]! ca[7]! ca[8]! ca[9]! ca[10]! }
    if (← get).nodes.size < cfg.maxNodes then
      let mut kids := #[]
      let mut labels := #[]
      if node.kind == "sealed" then
        if let some v := ci.value? (allowOpaque := true) then
          kids := kids.push (← walk v); labels := labels.push "body"
        else
          node := { node with kind := "sealed-body-unavailable" }
      else if node.kind == "lemma" then
        for a in args, (p, nm, d) in isPf do
          if p then kids := kids.push (← walk a (some (← instantiateMVars d))); labels := labels.push nm.toString
      node := { node with children := kids, labels }
    else
      node := { node with kind := node.kind ++ "-truncated" }
  | _ =>
    node := { node with head := s!"({fn.ctorName})", statement := ← pp (← inferType e) cfg.stmtChars }
  modify fun s => { s with nodes := s.nodes.set! id node }
  return id

def dumpTree (e : Expr) (cfg : Cfg := {}) : MetaM Json := do
  let (root, st) ← (walk e |>.run cfg).run {}
  let kinds := st.nodes.foldl (fun (m : Std.HashMap String Nat) n => m.insert n.kind (m.getD n.kind 0 + 1)) {}
  return Json.mkObj [("root", toJson root), ("node_count", toJson st.nodes.size),
    ("kinds", Json.mkObj (kinds.toList.map fun (k, v) => (k, toJson v))),
    ("nodes", toJson st.nodes)]

end TreeDump
