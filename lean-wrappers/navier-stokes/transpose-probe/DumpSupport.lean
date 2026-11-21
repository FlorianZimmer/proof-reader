import Lean
open Lean Elab Command

namespace Audit

partial def eraseBinderNames : Expr → Expr
  | .bvar i => .bvar i
  | .fvar i => .fvar i
  | .mvar i => .mvar i
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f x => .app (eraseBinderNames f) (eraseBinderNames x)
  | .lam _ t b bi => .lam .anonymous (eraseBinderNames t) (eraseBinderNames b) bi
  | .forallE _ t b bi => .forallE .anonymous (eraseBinderNames t) (eraseBinderNames b) bi
  | .letE _ t v b nd => .letE .anonymous (eraseBinderNames t) (eraseBinderNames v) (eraseBinderNames b) nd
  | .lit l => .lit l
  | .mdata _ e => eraseBinderNames e
  | .proj n i e => .proj n i (eraseBinderNames e)

def declarationJson (c : ConstantInfo) : Json :=
  Json.mkObj [
    ("name", toJson c.name.toString),
    ("levels", toJson (c.levelParams.map Name.toString)),
    ("type", toJson (reprStr (eraseBinderNames c.type))),
    ("value", match c.value? with | some e => toJson (reprStr (eraseBinderNames e)) | none => Json.null),
    ("constructors", match c with | .inductInfo v => toJson (v.ctors.map Name.toString) | _ => Json.null)]

elab "#dump_audit " file:str : command => do
  let names ← liftIO <| IO.FS.lines file.getString
  for s in names do
    let n := s.toName
    let c ← getConstInfo n
    liftIO <| IO.println (declarationJson c).compress
    if let .inductInfo v := c then
      for ctor in v.ctors do
        let cc ← getConstInfo ctor
        liftIO <| IO.println (declarationJson cc).compress

end Audit
