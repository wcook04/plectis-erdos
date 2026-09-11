/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Lean

/-!
# `hypOf%` — lift a hypothesis binder into a first-class `Prop`

Every recorded open antecedent of #249 / #257 is already a Lean `Prop`: it is the
type of a named hypothesis binder on a `conditional_implication` theorem. It is
just not *addressable* — you cannot name it, compare it, or state a theorem about
it, because it only exists in binder position.

`hypOf% thm hname` elaborates to exactly that binder's type, taken from the
kernel's own `ConstantInfo`. No pretty-printing, no re-parsing, no transcription:
the resulting `Prop` is definitionally the hypothesis, or the elaborator fails.

This is what turns a demand-side gap from prose in `frontier.json` into an object
the kernel can reason about.
-/

open Lean Elab Term Meta

/-- `hypOf% thm h` is the type of the binder named `h` in the type of `thm`.
Fails if there is no such binder, or if its type depends on earlier binders
(in which case it is not a standalone statement). -/
elab "hypOf% " d:ident h:ident : term => do
  let c ← realizeGlobalConstNoOverload d
  let ci ← getConstInfo c
  let target := h.getId
  forallTelescopeReducing ci.type fun args _ => do
    let mut found : Option Expr := none
    for a in args do
      let ld ← a.fvarId!.getDecl
      if ld.userName == target && found.isNone then
        found := some ld.type
    match found with
    | none => throwError "hypOf%: `{d}` has no binder named `{h}`"
    | some t =>
      if t.hasFVar then
        throwError "hypOf%: binder `{h}` of `{d}` is not closed (depends on earlier binders)"
      else
        return t
