-- Local check of TreeDump on core-only proofs: `cat TreeDump.lean TestTreeDump.lean > /tmp/t.lean && lean /tmp/t.lean`
open Lean Meta Elab Command TreeDump
set_option Elab.async false

theorem toy (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := Nat.le_succ_of_le h
theorem toy2 : (2 : Nat) ≤ 5 + 1 := toy 2 5 (by decide)

run_meta do
  let ci ← getConstInfo ``toy2
  let j ← dumpTree (ci.value? (allowOpaque := true)).get!
  IO.println j.compress
