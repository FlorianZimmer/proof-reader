/-
Driver: assembled after the zeta imports and TreeDump (see .github/workflows/zeta-trees.yml),
run from the root of a built smmercuri/zeta checkout with `lake env lean`.

For the first rows of Euler–Maclaurin batch 1 and Riemann–Siegel batch 1 it

1. reads the compiled proof of each batch theorem (the bundle the kernel checked) and takes the
   certificate terms out of it in row order (`source = "compiled_batch"`);
2. if the compiled proof is not visible from this import, rebuilds the same rows with the
   authors' own builders (`buildBundle` / `buildBundleRS`) and says so (`source = "rebuilt"`);
3. writes one JSON per certificate to `$ZETA_TREES_OUT` (default `trees/`).

ZETA_TREES_ROWS (default 3) sets how many rows per method; ZETA_TREES_MAX (default 60000) caps
nodes per tree.
-/
open Lean Meta Elab Command TreeDump

/-- `…Certificate.mk` / `…Certificate₀.mk` applications in order of appearance, deduplicated. -/
partial def collectCerts (e : Expr) (n : Nat) : StateT (Array Expr) MetaM Unit := do
  if (← get).size ≥ n then return
  let e := e.consumeMData
  if let .const c _ := e.getAppFn then
    let s := c.toString
    if s.endsWith "Certificate.mk" || s.endsWith "Certificate₀.mk" then
      unless (← get).contains e do modify (·.push e)
      return
  match e with
  | .app f a => collectCerts f n; collectCerts a n
  | .letE _ _ v b _ => collectCerts v n; collectCerts b n
  | .lam _ _ b _ => collectCerts b n
  | .proj _ _ b => collectCerts b n
  | _ => pure ()

/-- `sfrac false m d` → `(m, d)`. -/
def sfracOf? (e : Expr) : Option (Nat × Nat) :=
  let a := e.consumeMData.getAppArgs
  if a.size == 3 then do return (← natOf? a[1]!, ← natOf? a[2]!) else none

def endpointsOf (cert : Expr) : Json :=
  let I := cert.getAppArgs[0]!.consumeMData
  let a := I.getAppArgs
  let ep (k : Nat) : Json := match a[k]? >>= sfracOf? with
    | some (m, d) => Json.mkObj [("num", toJson m), ("den", toJson d)]
    | none => Json.null
  Json.mkObj [("left", ep 0), ("right", ep 1), ("interval_head", toJson I.getAppFn.constName?.get!.toString),
    ("interval_nat_params", toJson ((a.extract 3 a.size).filterMap natOf?))]

def envNat (k : String) (d : Nat) : IO Nat := return ((← IO.getEnv k).bind String.toNat?).getD d

def compiledValue? (n : Name) : MetaM (Option Expr) := do
  let some ci := (← getEnv).find? n | return none
  return ci.value? (allowOpaque := true)

def dumpMethod (method : String) (batch : Name) (rebuild : Nat → MetaM Expr) : MetaM Unit := do
  let rows ← envNat "ZETA_TREES_ROWS" 3
  let maxNodes ← envNat "ZETA_TREES_MAX" 60000
  let out : System.FilePath := ((← IO.getEnv "ZETA_TREES_OUT").getD "trees")
  IO.FS.createDirAll out
  let (src, e) ← match ← compiledValue? batch with
    | some v => pure ("compiled_batch", v)
    | none => do
      IO.println s!"{method}: compiled proof of {batch} not visible from this import; rebuilding"
      pure ("rebuilt", ← rebuild rows)
  let ((), certs) ← (collectCerts e rows).run #[]
  IO.println s!"{method}: {certs.size} certificates from {src}"
  for cert in certs, i in [0:certs.size] do
    let t0 ← IO.monoMsNow
    let tree ← dumpTree cert { maxNodes }
    let ms := (← IO.monoMsNow) - t0
    let j := Json.mkObj [("method", toJson method), ("row", toJson (i + 1)), ("source", toJson src),
      ("batch_theorem", toJson batch.toString), ("certificate_ctor", toJson cert.getAppFn.constName?.get!.toString),
      ("endpoints", endpointsOf cert), ("walk_ms", toJson ms), ("tree", tree)]
    let f := out / s!"{method}_row{i + 1}.json"
    IO.FS.writeFile f j.compress
    IO.println s!"  wrote {f} ({(tree.getObjValD "node_count").compress} nodes, {ms} ms)"

run_meta do
  dumpMethod "euler_maclaurin" `Zeta.Certificates.EulerMaclaurin.Batch0001.batch fun n => do
    Zeta.Certificates.buildBundle (Zeta.Certificates.parseRows
      (← Zeta.Certificates.storeLines Zeta.Certificates.storeDir 0 n))
  dumpMethod "riemann_siegel" `Zeta.Certificates.RiemannSiegel.Batch0001.batch fun n => do
    let rows ← ofExcept <| Zeta.Certificates.parseRowsRS
      (← Zeta.Certificates.storeLines Zeta.Certificates.storeDirRS 0 n) 0
    Zeta.Certificates.buildBundleRS rows
