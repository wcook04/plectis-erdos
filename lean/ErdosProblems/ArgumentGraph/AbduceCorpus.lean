-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Defs
import ErdosProblems.ArgumentGraph.Residualise
import ErdosProblems.ArgumentGraph.Abduce

/-!
# Abduction against the corpus

`abduceClause` eliminates the atoms that the given facts control. Here the facts come from the
corpus. Every comparison reading of a corpus theorem (its statement with leading binders
instantiated, a conjunct, or the unfolding of a corpus definition) is indexed under the corpus
constants it mentions, and so is every eventual comparison reading `∀ᶠ X in f, F X`. A
comparison `C` retrieves the readings that share its constants, instantiated by unifying their
subterms with the atoms of `C`, closed, with their hypotheses discharged by the hypotheses in
scope or by the closing battery. Several facts then combine linearly, which a supplier search
that unifies one theorem at a time with the whole of `C` does not see.

`abduceProp` applies this under `∀`, `→`, `∧`, `∃` and the filter quantifiers:

* a hypothesis met on the way down is a fact, together with the comparisons it gives through
  conjunctions, membership in `Ico`, `Icc`, `range` and `filter` and the unfolding of corpus
  finsets; a clause `s.Nonempty` is read as `0 < s.card`;
* a variable bound by `∀` inside the proposition may be eliminated like a hidden atom, and a
  binder that the restated body no longer mentions is dropped;
* under `∃ᶠ X` or `∀ᶠ X` an eventual fact is used at `X` and supplied along the filter.

It returns the restated proposition with a proof that it implies the original.
`restateAntecedents` restates every hypothesis of a theorem this way, drops those the facts
give outright, and returns the new statement with a proof built from the original theorem.
-/

set_option autoImplicit false

open Lean Meta Elab Term
open ErdosProblems.ArgumentGraph.Residualise

namespace ErdosProblems.ArgumentGraph.Abduce

/-- Readings of corpus theorems keyed by the corpus constants they mention: comparisons, and
eventual comparisons `∀ᶠ X in f, F X`. -/
structure Facts where
  pointwise : Std.HashMap Name (Array Ref) := {}
  eventual : Std.HashMap Name (Array Ref) := {}

def corpusConsts (unfoldOk : Name → Bool) (e : Expr) : Array Name :=
  e.getUsedConstants.filter unfoldOk

/-- Whether `stmt` is `∀ᶠ X in f, F X` with `F X` a comparison. -/
def eventualComparison? (stmt : Expr) : MetaM Bool := do
  let stmt ← instantiateMVars stmt
  unless stmt.isAppOfArity ``Filter.Eventually 3 do return false
  let p := stmt.getArg! 1
  let α := stmt.getArg! 0
  withLocalDeclD `X α fun x => do return (← comparison? (p.beta #[x])).isSome

/-- Add the comparison and eventual comparison readings of the theorem `n`. -/
def indexFacts (facts : Facts) (unfoldOk : Name → Bool) (n : Name) (depth : Nat) :
    MetaM (Facts × Nat) := do
  let some ci := (← getEnv).find? n | return (facts, 0)
  let found ← withNewMCtxDepth do
    let lvls ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
    let ty := ci.type.instantiateLevelParams ci.levelParams lvls
    let rs := (← Residualise.budgeted 2000 (readingPaths unfoldOk ty #[] depth)).getD #[]
    let mut out : Array (Bool × Array Name × Array Step) := #[]
    for (stmt, path) in rs do
      let stmt ← instantiateMVars stmt
      let ev ← eventualComparison? stmt
      if ev || (← comparison? stmt).isSome then
        let cs := corpusConsts unfoldOk stmt
        unless cs.isEmpty do out := out.push (ev, cs, path)
    return out
  let mut facts := facts
  for (ev, cs, path) in found do
    for c in cs do
      let ref : Ref := { name := n, path }
      if ev then
        let refs := (facts.eventual.getD c #[]).push ref
        facts := { facts with eventual := facts.eventual.insert c refs }
      else
        let refs := (facts.pointwise.getD c #[]).push ref
        facts := { facts with pointwise := facts.pointwise.insert c refs }
  return (facts, found.size)

/-- The facts of every theorem of the modules under `roots`. -/
def buildFactIndex (roots : Array Name) (unfoldOk : Name → Bool) (depth : Nat := 6) :
    MetaM (Facts × Nat) := do
  let env ← getEnv
  let mut facts : Facts := {}
  let mut total := 0
  for modName in env.header.moduleNames, data in env.header.moduleData do
    unless roots.any (·.isPrefixOf modName) do continue
    for n in data.constNames do
      if n.isInternal then continue
      let some (.thmInfo _) := env.find? n | continue
      let (f, k) ← indexFacts facts unfoldOk n depth
      facts := f
      total := total + k
  return (facts, total)

/-- The facts of the given theorems only (a supplier set). -/
def factsOf (names : Array Name) (unfoldOk : Name → Bool) (depth : Nat := 8) : MetaM Facts := do
  let mut facts : Facts := {}
  for n in names do
    facts := (← indexFacts facts unfoldOk n depth).1
  return facts

/-- Subterms of `e` whose head is a constant, up to `fuel` nodes. -/
def appSubterms : Nat → Expr → Array Expr → Array Expr
  | 0, _, acc => acc
  | fuel + 1, e, acc =>
    match e with
    | .app f a =>
      let acc := if e.getAppFn.isConst then acc.push e else acc
      appSubterms fuel a (appSubterms fuel f acc)
    | .mdata _ b => appSubterms fuel b acc
    | _ => acc

/-- Replay a reading with fresh metavariables for its binders (propositional and instance
binders are obligations): its proof, its statement and the obligations. -/
def replayPlain (proof stmt : Expr) (obls : Array Expr) :
    List Step → MetaM (Option (Expr × Expr × Array Expr))
  | [] => return some (proof, ← instantiateMVars stmt, obls)
  | s :: rest => do
    let stmt ← whnfR (← instantiateMVars stmt)
    match s with
    | .inst =>
        let .forallE _ d b bi := stmt | return none
        let isP ← isProp d
        let m ← mkFreshExprMVar d (if isP then .syntheticOpaque else .natural)
        let obls := if isP || bi.isInstImplicit then obls.push m else obls
        replayPlain (mkApp proof m) (b.instantiate1 m) obls rest
    | .left =>
        unless stmt.isAppOfArity ``And 2 do return none
        replayPlain (← mkAppM ``And.left #[proof]) stmt.appFn!.appArg! obls rest
    | .right =>
        unless stmt.isAppOfArity ``And 2 do return none
        replayPlain (← mkAppM ``And.right #[proof]) stmt.appArg! obls rest
    | .unfold =>
        let some u ← unfoldDefinition? stmt | return none
        replayPlain proof u obls rest
    | .evLeft | .evRight =>
        unless stmt.isAppOfArity ``Filter.Eventually 3 do return none
        let α := stmt.getArg! 0
        let pred := stmt.getArg! 1
        let proj := if s == .evLeft then ``And.left else ``And.right
        let some p ← withLocalDeclD `x α fun x => do
            let body ← whnfR (pred.beta #[x])
            unless body.isAppOfArity ``And 2 do return none
            let g ← withLocalDeclD `h body fun h => do mkLambdaFVars #[x, h] (← mkAppM proj #[h])
            return some (← mkAppM ``Filter.Eventually.mono #[proof, g])
          | return none
        replayPlain p (← inferType p) obls rest

/-- The atoms of the comparison `C`. -/
def atomsOf (C : Expr) : MetaM (Array Expr) := do
  let some (α, a, b, _) ← comparison? C | return #[]
  let (natSub, integral) ← carrierKind α
  Mathlib.Tactic.AtomM.run .reducible do
    discard <| linForm natSub integral 256 a
    discard <| linForm natSub integral 256 b
    return (← get).atoms

/-- The compound atoms of the comparisons in `e` that mention no bound variable. -/
def comparisonAtoms (e : Expr) : MetaM (Array Expr) := do
  let mut out : Array Expr := #[]
  for s in appSubterms 4000 e #[e] do
    if s.hasLooseBVars then continue
    if (← comparison? s).isSome then
      for a in ← atomsOf s do
        if a.getAppFn.isConst && !out.contains a then out := out.push a
  return out

/-- Discharge the obligations of a replayed reading: instances by synthesis, propositions by a
hypothesis in scope or by the battery. -/
def dischargeObligations (locals obls : Array Expr) : TermElabM Bool := do
  for o in obls do
    if ← o.mvarId!.isAssigned then continue
    let oT ← instantiateMVars (← inferType o)
    if oT.hasMVar then return false
    if (← isClass? oT).isSome then
      let some inst ← (try some <$> synthInstance oT catch _ => pure none) | return false
      o.mvarId!.assign inst
      continue
    let mut done := false
    for l in locals do
      if ← withReducible (isDefEq (← inferType l) oT) then
        o.mvarId!.assign l
        done := true
        break
    unless done do
      let some p ← battery oT | return false
      o.mvarId!.assign p
  return true

/-- Candidate readings for a statement with corpus constants `cs`, best overlap first. -/
def rankedRefs (idx : Std.HashMap Name (Array Ref)) (cs : Array Name) (exclude : Array Name)
    (maxK : Nat) : Array Ref := Id.run do
  let mut scored : Array (Ref × Nat) := #[]
  for c in cs do
    for r in idx.getD c #[] do
      if exclude.contains r.name then continue
      match scored.findIdx? (·.1 == r) with
      | some i => scored := scored.modify i fun (x, k) => (x, k + 1)
      | none => scored := scored.push (r, 1)
  return ((scored.qsort fun a b => a.2 > b.2).extract 0 maxK).map (·.1)

/-- Unify the metavariable-bearing subterms of `stmt` with the atoms, one by one. -/
def unifyWithAtoms (stmt : Expr) (atoms : Array Expr) : MetaM Unit := do
  for t in atoms do
    for u in appSubterms 4000 stmt #[] do
      if u.hasMVar && u.getAppFn.constName? == t.getAppFn.constName? then
        let s2 ← saveState
        unless ← isDefEq u t do s2.restore

/-- The local variables of non-propositional type, in declaration order. -/
def ctxDataVars : MetaM (Array Expr) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if ← isProp d.type then continue
    if (← whnfR d.type).isSort then continue
    out := out.push d.toExpr
  return out

/-- The closings of a replayed reading: its data metavariables assigned local variables of
their types (at most `cap` closings), its obligations discharged; each closing is `ts`
instantiated. -/
def closeByContext (ts obls vars locals : Array Expr) (cap : Nat := 4) :
    TermElabM (Array (Array Expr)) := do
  let mut ms : Array MVarId := #[]
  for t in ts do
    for m in ← getMVars (← instantiateMVars t) do
      unless ms.contains m do ms := ms.push m
  let rec go (ms : List MVarId) (fuel : Nat) : TermElabM (Array (Array Expr)) := do
    match fuel, ms with
    | 0, _ => return #[]
    | _, [] =>
      let s ← saveState
      let ok ← dischargeObligations locals obls
      let es ← ts.mapM instantiateMVars
      s.restore
      return if ok && !es.any (·.hasMVar) then #[es] else #[]
    | fuel + 1, m :: rest =>
      if ← m.isAssigned then return ← go rest fuel
      if (← m.getKind).isSyntheticOpaque then return ← go rest fuel
      let mT ← instantiateMVars (← m.getType)
      let mut out : Array (Array Expr) := #[]
      for v in vars do
        if out.size ≥ cap then break
        let s ← saveState
        if ← isDefEq (← inferType v) mT then
          m.assign v
          out := out ++ (← go rest fuel)
        s.restore
      return out.extract 0 cap
  go ms.toList (ms.size + 1)

/-- Facts for the comparison `C` from the readings `refs`: each instantiated by unifying its
subterms with the compound atoms of `C`, then closed by local variables, its hypotheses
discharged. -/
def retrieveFacts (refs : Array Ref) (locals : Array Expr) (C : Expr) :
    TermElabM (Array Expr) := do
  let some _ ← comparison? C | return #[]
  let atoms := (← atomsOf C).filter (·.getAppFn.isConst)
  let vars ← ctxDataVars
  let mut out : Array Expr := #[]
  for ref in refs do
    let s ← saveState
    let got? ← withHeartbeatBudget 4000 do
      let c0 ← mkConstWithFreshMVarLevels ref.name
      let some (proof, stmt, obls) ← replayPlain c0 (← inferType c0) #[] ref.path.toList
        | return #[]
      -- any carrier: a count over `ℕ` and a bound over `ℝ` meet after lifting
      let some _ ← comparison? stmt | return #[]
      unifyWithAtoms stmt atoms
      return (← closeByContext #[proof] obls vars locals).map (·[0]!)
    s.restore
    for p in got?.getD #[] do
      unless out.contains p do out := out.push p
  return out

/-- Eventual facts for the body `B` of a filter quantifier over `f` at the variable `X`, from
the readings `refs` of the form `∀ᶠ Y in f, F Y`: `F X` instantiated by unifying its subterms
with the comparison atoms of `B`, then closed by local variables. Returns each proof with its
statement at `X`. -/
def retrieveEventual (refs : Array Ref) (locals : Array Expr) (B X f : Expr) :
    TermElabM (Array (Expr × Expr)) := do
  let atoms ← comparisonAtoms B
  let vars ← ctxDataVars
  let mut out : Array (Expr × Expr) := #[]
  for ref in refs do
    let s ← saveState
    let got? ← withHeartbeatBudget 4000 do
      let c0 ← mkConstWithFreshMVarLevels ref.name
      let some (proof, stmt, obls) ← replayPlain c0 (← inferType c0) #[] ref.path.toList
        | return #[]
      unless stmt.isAppOfArity ``Filter.Eventually 3 do return #[]
      unless ← isDefEq (stmt.getArg! 2) f do return #[]
      let F := (stmt.getArg! 1).beta #[X]
      unifyWithAtoms F atoms
      return (← closeByContext #[proof, F] obls vars locals).map fun es => (es[0]!, es[1]!)
    s.restore
    for r in got?.getD #[] do
      unless out.any (·.2 == r.2) do out := out.push r
  return out

/-- Membership and nonemptiness read as comparisons: `x ∈ Ico a b`, `Icc`, `range`, `filter`
and corpus finsets (unfolded), and `s.Nonempty` as `0 < s.card`. Returns the normal form with a
proof that it equals `P`, or `none` when nothing applies. -/
def comparisonForm (unfoldOk : Name → Bool) (P : Expr) : MetaM (Option (Expr × Expr)) := do
  let mut thms : SimpTheorems := {}
  for n in [``Finset.mem_Ico, ``Finset.mem_Icc, ``Finset.mem_Ioc, ``Finset.mem_Ioo,
      ``Finset.mem_range, ``Finset.mem_filter] do
    thms ← thms.addConst n
  thms ← thms.addConst ``Finset.card_pos (inv := true)
  -- a corpus finset is unfolded only as the collection of a membership, never inside atoms
  if P.isAppOfArity ``Membership.mem 5 then
    if let .const c _ := (P.getArg! 3).getAppFn then
      if unfoldOk c then
        if let some (.defnInfo _) := (← getEnv).find? c then
          thms ← thms.addDeclToUnfold c
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let some (r, _) ← Residualise.budgeted 2000 (simp P ctx) | return none
  if r.expr == P then return none
  match r.proof? with
  | some p => return some (r.expr, p)
  | none => return some (r.expr, ← mkEqRefl P)

/-- The comparison facts a hypothesis gives, through conjunctions and `comparisonForm`. -/
def expandFact (unfoldOk : Name → Bool) : Nat → Expr → MetaM (Array Expr)
  | 0, _ => return #[]
  | fuel + 1, h => do
    let T ← instantiateMVars (← inferType h)
    if (← comparison? T).isSome then return #[h]
    if T.isAppOfArity ``And 2 then
      return (← expandFact unfoldOk fuel (← mkAppM ``And.left #[h])) ++
        (← expandFact unfoldOk fuel (← mkAppM ``And.right #[h]))
    match ← comparisonForm unfoldOk T with
    | some (T', eq) =>
      if T' == T then return #[] else expandFact unfoldOk fuel (← mkEqMP eq h)
    | none => return #[]

/-- The proof `fun h : A => h`. -/
def idProof (A : Expr) : MetaM Expr := withLocalDeclD `h A fun h => mkLambdaFVars #[h] h

/-- How `abduceProp` finds facts and witnesses. -/
structure Retrieval where
  unfoldOk : Name → Bool
  /-- corpus facts for a comparison, given the hypotheses in scope -/
  pointwise : Array Expr → Expr → TermElabM (Array Expr)
  /-- eventual facts for a filter body `B` at `X` over `f`, given the hypotheses in scope -/
  eventual : Array Expr → Expr → Expr → Expr → TermElabM (Array (Expr × Expr))
  /-- candidate witnesses of a type, given the filter variable in scope -/
  witnesses : Option (Expr × Expr) → Expr → TermElabM (Array Expr) := fun _ _ => pure #[]
  /-- witness evaluations left for the current statement, shared by nested existentials -/
  evals : Option (IO.Ref Nat) := none
  /-- witness evaluations allowed for one statement -/
  evalBudget : Nat := 32
  /-- print progress lines on standard error, flushed at once -/
  trace : Bool := false

/-- A progress line when tracing is on. -/
def Retrieval.say (R : Retrieval) (msg : String) : TermElabM Unit := do
  if R.trace then
    IO.eprintln msg
    (← IO.getStderr).flush

/-- Give the next statement its full allowance of witness evaluations. -/
def Retrieval.resetEvals (R : Retrieval) : TermElabM Unit := do
  if let some r := R.evals then r.set R.evalBudget

/-- A cofinal existential from a frequent universal: if for arbitrarily large `X` the statement
`Q A X` holds for every `A ≤ X`, then every `A` has some `X` with `Q A X`. -/
theorem forall_exists_of_frequently_forall_le {Q : ℕ → ℕ → Prop}
    (h : ∃ᶠ X in Filter.atTop, ∀ A, A ≤ X → Q A X) : ∀ A, ∃ X, Q A X := by
  intro A
  obtain ⟨X, hX, hQ⟩ := Filter.frequently_atTop.mp h A
  exact ⟨X, hQ A hX⟩

/-- Every closing of the metavariables of `t` by local variables of their types (at most
`cap` of them); `t` itself when it has none. -/
def fillByContext (t : Expr) (vars : Array Expr) (cap : Nat := 8) : MetaM (Array Expr) := do
  let t ← instantiateMVars t
  let ms := (← getMVars t).toList
  let rec go (ms : List MVarId) (fuel : Nat) : MetaM (Array Expr) := do
    match fuel, ms with
    | 0, _ => return #[]
    | _, [] =>
      let e ← instantiateMVars t
      return if e.hasMVar then #[] else #[e]
    | fuel + 1, m :: rest =>
      if ← m.isAssigned then return ← go rest fuel
      let mT ← instantiateMVars (← m.getType)
      let mut out : Array Expr := #[]
      for v in vars do
        if out.size ≥ cap then break
        let s ← saveState
        if ← isDefEq (← inferType v) mT then
          m.assign v
          out := out ++ (← go rest fuel)
        s.restore
      return out.extract 0 cap
  go ms (ms.length + 1)

/-- The number of clauses a proposition leaves: `True` none, a conjunction the sum, an
existential one more than its body (a witness left unchosen is itself a cost), anything else one
(through binders and the filter quantifiers). -/
def clauseScore : Nat → Expr → Nat
  | 0, _ => 1
  | fuel + 1, e =>
    if e.isConstOf ``True then 0
    else if e.isAppOfArity ``And 2 then clauseScore fuel e.appFn!.appArg! + clauseScore fuel e.appArg!
    else if e.isAppOfArity ``Exists 2 then
      match e.appArg! with
      | .lam _ _ b _ => 1 + clauseScore fuel b
      | _ => 2
    else if e.isAppOfArity ``Filter.Frequently 3 || e.isAppOfArity ``Filter.Eventually 3 then
      match e.getArg! 1 with
      | .lam _ _ b _ => clauseScore fuel b
      | _ => 1
    else match e with
      | .forallE _ _ b _ => clauseScore fuel b
      | _ => 1

/-- Candidate witnesses of type `α` from the readings of a fact index: subterms of that type
(an eventual reading read at the filter variable in scope), their metavariables closed by local
variables. Terms headed by a corpus constant come first. -/
def witnessCandidates (facts : Facts) (unfoldOk : Name → Bool) (fv : Option (Expr × Expr))
    (α : Expr) (maxK : Nat := 12) : TermElabM (Array Expr) := do
  let mut refs : Array Ref := #[]
  for (_, rs) in facts.eventual.toList ++ facts.pointwise.toList do
    for r in rs do
      unless refs.contains r do refs := refs.push r
  let vars ← ctxDataVars
  let mut out : Array (Expr × Nat) := #[]
  for ref in refs do
    let s ← saveState
    let found ← try
        let c0 ← mkConstWithFreshMVarLevels ref.name
        let some (_, stmt, _) ← replayPlain c0 (← inferType c0) #[] ref.path.toList
          | pure #[]
        let body ← match fv with
          | some (X, f) =>
            if stmt.isAppOfArity ``Filter.Eventually 3 then
              if ← isDefEq (stmt.getArg! 2) f then pure ((stmt.getArg! 1).beta #[X]) else pure stmt
            else pure stmt
          | none => pure stmt
        let mut acc : Array (Expr × Nat) := #[]
        for u in appSubterms 4000 body #[] do
          if u.hasLooseBVars then continue
          let some uT ← (try some <$> inferType u catch _ => pure none) | continue
          unless ← isDefEq uT α do continue
          let fills := (← getMVars (← instantiateMVars u)).size
          for e in ← fillByContext u vars do
            unless acc.any (·.1 == e) do acc := acc.push (e, fills)
        pure acc
      catch _ => pure #[]
    s.restore
    for (e, k) in found do
      unless out.any (·.1 == e) do out := out.push (e, k)
  let corpusHead (e : Expr) : Bool := match e.getAppFn with
    | .const c _ => unfoldOk c
    | _ => false
  -- corpus terms first, and among them those needing the fewest local substitutions; ties keep
  -- the order found, in which local variables are tried outermost first
  let key (p : Expr × Nat) : Nat := (if corpusHead p.1 then 0 else 1000) + p.2
  let mut indexed : Array (Expr × Nat × Nat) := #[]
  for i in [0:out.size] do
    indexed := indexed.push (out[i]!.1, key out[i]!, i)
  let ranked := indexed.qsort fun a b => a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)
  return (ranked.extract 0 maxK).map (·.1)

/-- `(↑e : ℝ)` for `e : ℕ`, with the cast pushed through sums, products by numerals and
numerals. -/
def castReal : Nat → Expr → MetaM Expr
  | 0, e => mkAppOptM ``Nat.cast #[Lean.mkConst ``Real, none, e]
  | fuel + 1, e => do
    let realT := Lean.mkConst ``Real
    if let some q ← numeral? 64 e then return ← numeralExpr realT q
    match e.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
        mkAppM ``HAdd.hAdd #[← castReal fuel a, ← castReal fuel b]
    | (``HMul.hMul, #[_, _, _, _, a, b]) =>
        if let some q ← numeral? 64 a then
          return ← mkAppM ``HMul.hMul #[← numeralExpr realT q, ← castReal fuel b]
        if let some q ← numeral? 64 b then
          return ← mkAppM ``HMul.hMul #[← castReal fuel a, ← numeralExpr realT q]
        mkAppOptM ``Nat.cast #[realT, none, e]
    | _ => mkAppOptM ``Nat.cast #[realT, none, e]

/-- An atom with a cast from `ℕ` removed, so that a count and its real cast compare equal. -/
def uncast (e : Expr) : Expr :=
  if e.isAppOfArity ``Nat.cast 3 then e.appArg! else e

/-- The facts relevant to the comparison `C`: those sharing an atom with it, most shared atoms
first, then those sharing an atom with one of these, at most `cap` in all. Elimination grows
doubly exponentially in the facts, and a hypothesis in scope that mentions none of the clause's
quantities cannot help eliminate them. -/
def relevantFacts (C : Expr) (facts : Array Expr) (cap : Nat := 16) : MetaM (Array Expr) := do
  if facts.size ≤ cap then return facts
  let goalAtoms := ((← try atomsOf C catch _ => pure #[])).map uncast
  if goalAtoms.isEmpty then return facts.extract 0 cap
  let mut scored : Array (Expr × Array Expr × Nat) := #[]
  for f in facts do
    let T ← instantiateMVars (← inferType f)
    let as := ((← try atomsOf T catch _ => pure #[])).map uncast
    if as.isEmpty then continue
    scored := scored.push (f, as, (as.filter goalAtoms.contains).size)
  let hop1 := (scored.filter (·.2.2 > 0)).qsort fun a b => a.2.2 > b.2.2
  let atoms1 := hop1.foldl (fun acc s => acc ++ s.2.1) goalAtoms
  let hop2 := scored.filter fun s => s.2.2 == 0 && s.2.1.any atoms1.contains
  return ((hop1 ++ hop2).map (·.1)).extract 0 cap

/-- The comparison over `ℝ` of a comparison over `ℕ`. -/
def realComparison? (P : Expr) : MetaM (Option Expr) := do
  let some (α, a, b, rel) ← comparison? P | return none
  unless (← carrierKind α).1 do return none
  let a' ← castReal 64 a
  let b' ← castReal 64 b
  match rel with
  | .le => return some (← mkAppM ``LE.le #[a', b'])
  | .lt => return some (← mkAppM ``LT.lt #[a', b'])
  | .eq => return some (← mkAppM ``Eq #[a', b'])

def isRealCarrier (P : Expr) : MetaM Bool := do
  let some (β, _, _, _) ← comparison? P | return false
  return (← whnfR β).isConstOf ``Real

/-- Abduce one comparison. When the facts mix counts over `ℕ` with bounds over `ℝ`, the
comparisons over `ℕ` (the clause and the facts) are lifted to `ℝ` first. The variables bound
inside the proposition are eliminated innermost first; then none are. A restatement counts
only when the facts give the clause or eliminate an atom. -/
def abduceLeaf (R : Retrieval) (locals bound : Array Expr) (C : Expr) :
    TermElabM (Option (Expr × Expr)) := do
  let raw ← relevantFacts C (locals ++ (← R.pointwise locals C))
  let mut facts := raw
  let mut goal := C
  let mut back : Option Expr := none
  let factTypes ← raw.mapM fun f => do instantiateMVars (← inferType f)
  if ← factTypes.anyM (fun t => isRealCarrier t) then
    if let some CR ← realComparison? C then
      if let some pb ← proveByTactic (← mkArrow CR C) "(intro h; exact_mod_cast h)" then
        goal := CR
        back := some pb
    -- over `ℝ` a count's fact is kept only in its lifted form
    let mut lifted : Array Expr := #[]
    let mut kept : Array Expr := #[]
    for i in [0:raw.size] do
      let mut done := false
      if let some TR ← realComparison? factTypes[i]! then
        if let some p ← proveByTactic (← mkArrow factTypes[i]! TR) "(intro h; exact_mod_cast h)" then
          lifted := lifted.push (mkApp p raw[i]!)
          done := true
      unless done do kept := kept.push raw[i]!
    facts := if back.isSome then kept ++ lifted else raw ++ lifted
  R.say s!"[leaf] {facts.size} facts, {bound.size} bound variables"
  -- elimination can grow doubly exponentially in the facts; each attempt has its own budget, and
  -- running out counts as finding nothing
  let attempt (extra : Array Expr) : TermElabM (Option (Expr × Expr)) := do
    let t0 ← IO.monoMsNow
    let r? := (← Residualise.budgetedTerm 20000 (abduceClause goal facts none extra)).join
    R.say s!"[leaf] elimination with {extra.size} extra hidden: {if r?.isSome then "done" else "none"} in {(← IO.monoMsNow) - t0} ms"
    let some r := r? | return none
    unless r.residual.isConstOf ``True || !r.hidden.isEmpty do return none
    if ← withReducible (isDefEq r.residual goal) then return none
    return some (r.residual, r.proof)
  let mut found : Option (Expr × Expr) := none
  for k in [1:bound.size + 1] do
    if found.isNone then
      found ← attempt (bound.extract (bound.size - k) bound.size)
  if found.isNone then found ← attempt #[]
  let some (C', pf) := found | return none
  match back with
  | none => return some (C', pf)
  | some pb =>
    let proof ← withLocalDeclD `h C' fun h => do mkLambdaFVars #[h] (mkApp pb (mkApp pf h))
    return some (C', proof)

/-- `C'` with a proof of `C' → C`: each comparison is abduced against the hypotheses in scope
and the facts `R` finds, under `∀`, `→`, `∧`, `∃` and the filter quantifiers. `none` when
nothing changes. `bound` lists the variables bound by `∀` inside the original proposition and
`fv` the filter variable in scope.

* A binder whose body becomes `True` goes with it. A data binder that the restated body no
  longer mentions is dropped, and so is `∀ x, hyp x → P'` with `P'` free of `x`. A hypothesis
  binder stays otherwise: dropping it would ask for more.
* `∀ A, ∃ X, Q A X` over `ℕ` may be read as `∃ᶠ X, ∀ A ≤ X, Q A X`, which puts the eventual
  facts at `X` in reach; the reading is kept only when it restates something.
* `∃ w, P w` tries the witnesses `R` proposes and keeps the one leaving the fewest clauses. -/
def abduceProp (R : Retrieval) : Nat → Array Expr → Array Expr → Option (Expr × Expr) → Expr →
    TermElabM (Option (Expr × Expr))
  | 0, _, _, _, _ => return none
  | fuel + 1, locals, bound, fv, C => do
    let C ← instantiateMVars C
    match C with
    | .forallE n d b bi =>
      -- the cofinal reading
      if (← whnfR d).isConstOf ``Nat && !(← isProp d) then
        let cof? ← withLocalDecl n bi d fun a => do
          let body ← whnfR (b.instantiate1 a)
          unless body.isAppOfArity ``Exists 2 do return none
          unless (← whnfR body.appFn!.appArg!).isConstOf ``Nat do return none
          let qfun ← mkLambdaFVars #[a] body.appArg!
          -- `Q A X := (fun A => fun X => …) A X`
          let Q ← withLocalDeclD `A (Lean.mkConst ``Nat) fun A => withLocalDeclD `X (Lean.mkConst ``Nat) fun X => do
            mkLambdaFVars #[A, X] ((qfun.beta #[A]).beta #[X])
          let freq ← withLocalDeclD `X (Lean.mkConst ``Nat) fun X => do
            let inner ← withLocalDeclD `A (Lean.mkConst ``Nat) fun A => do
              let le ← mkAppM ``LE.le #[A, X]
              mkForallFVars #[A] (← mkArrow le (Q.beta #[A, X]))
            mkAppM ``Filter.Frequently #[← mkLambdaFVars #[X] inner, ← mkAppOptM ``Filter.atTop
              #[Lean.mkConst ``Nat, none]]
          return some (Q, freq)
        if let some (Q, freq) := cof? then
          if let some (C', pf) ← abduceProp R fuel locals bound fv freq then
            -- `pf : C' → freq`, then the lemma gives `C`
            let proof ← withLocalDeclD `h C' fun h => do
              let lem ← mkAppOptM ``forall_exists_of_frequently_forall_le #[Q, mkApp pf h]
              mkLambdaFVars #[h] lem
            return some (C', proof)
      withLocalDecl n bi d fun x => do
        let isH ← isProp d
        let derived ← if isH then expandFact R.unfoldOk 16 x else pure #[]
        let locals := if isH then locals ++ derived ++ #[x] else locals
        let bound := if isH then bound else bound.push x
        let some (B', pf) ← abduceProp R fuel locals bound fv (b.instantiate1 x) | return none
        if B'.isConstOf ``True || (!isH && !B'.containsFVar x.fvarId!) then
          let proof ← withLocalDeclD `h B' fun h => do
            mkLambdaFVars #[h] (← mkLambdaFVars #[x] (mkApp pf h))
          return some (B', proof)
        if !isH then
          if let .forallE _ d' b' _ := B' then
            if (← isProp d') && !b'.hasLooseBVars && !b'.containsFVar x.fvarId! then
              let proof ← withLocalDeclD `h b' fun h => do
                let const ← withLocalDeclD `hx d' fun hx => mkLambdaFVars #[hx] h
                mkLambdaFVars #[h] (← mkLambdaFVars #[x] (mkApp pf const))
              return some (b', proof)
        let C' ← mkForallFVars #[x] B'
        let proof ← withLocalDeclD `h C' fun h => do
          mkLambdaFVars #[h] (← mkLambdaFVars #[x] (mkApp pf (mkApp h x)))
        return some (C', proof)
    | _ =>
      if C.isAppOfArity ``And 2 then
        let A := C.appFn!.appArg!
        let B := C.appArg!
        let ra ← abduceProp R fuel locals bound fv A
        let rb ← abduceProp R fuel locals bound fv B
        if ra.isNone && rb.isNone then return none
        let (A', pa) ← match ra with
          | some r => pure r
          | none => do pure (A, ← idProof A)
        let (B', pb) ← match rb with
          | some r => pure r
          | none => do pure (B, ← idProof B)
        let aTrue := A'.isConstOf ``True
        let bTrue := B'.isConstOf ``True
        let C' := if aTrue && bTrue then Lean.mkConst ``True
          else if aTrue then B' else if bTrue then A' else mkApp2 (Lean.mkConst ``And) A' B'
        let proof ← withLocalDeclD `h C' fun h => do
          let ha ← if aTrue then pure (Lean.mkConst ``True.intro)
            else if bTrue then pure h else mkAppM ``And.left #[h]
          let hb ← if bTrue then pure (Lean.mkConst ``True.intro)
            else if aTrue then pure h else mkAppM ``And.right #[h]
          mkLambdaFVars #[h] (← mkAppM ``And.intro #[mkApp pa ha, mkApp pb hb])
        return some (C', proof)
      if C.isAppOfArity ``Exists 2 then
        let α := C.appFn!.appArg!
        let P := C.appArg!
        -- proposed witnesses in rank order, keeping the one leaving the fewest clauses; the scan
        -- stops at a witness leaving none, at one leaving at most one once three have been
        -- tried, and when the evaluations allowed for the statement run out
        let mut best : Option (Expr × Expr × Nat) := none
        let mut tried := 0
        for t in ← R.witnesses fv α do
          if let some b := best then
            if b.2.2 == 0 || (b.2.2 ≤ 1 && tried ≥ 3) then break
          if let some r := R.evals then
            let left ← r.get
            if left == 0 then break
            r.set (left - 1)
          tried := tried + 1
          let tw ← IO.monoMsNow
          R.say s!"[witness] trying {← ppExpr t}"
          let s ← saveState
          let r? ← try abduceProp R fuel locals bound fv (P.beta #[t]) catch _ => pure none
          R.say s!"[witness] {if r?.isSome then "restated" else "nothing"} in {(← IO.monoMsNow) - tw} ms"
          match r? with
          | some (P', pf) =>
            let score := clauseScore 64 P'
            R.say s!"[witness] score {score}"
            if best.all (fun b => score < b.2.2) then
              let proof ← withLocalDeclD `h P' fun h => do
                mkLambdaFVars #[h] (← mkAppOptM ``Exists.intro #[α, P, t, mkApp pf h])
              best := some (← instantiateMVars P', ← instantiateMVars proof, score)
          | none => pure ()
          s.restore
        if let some (P', proof, _) := best then return some (P', proof)
        return ← withLocalDeclD `w α fun w => do
          let some (P', pf) ← abduceProp R fuel locals bound fv (P.beta #[w]) | return none
          let C' ← mkAppM ``Exists #[← mkLambdaFVars #[w] P']
          let impl ← mkLambdaFVars #[w] pf
          let proof ← withLocalDeclD `h C' fun h => do
            mkLambdaFVars #[h] (← mkAppM ``Exists.imp #[impl, h])
          return some (C', proof)
      if C.isAppOfArity ``Filter.Frequently 3 || C.isAppOfArity ``Filter.Eventually 3 then
        let α := C.getArg! 0
        let P := C.getArg! 1
        let f := C.getArg! 2
        let freq := C.isAppOfArity ``Filter.Frequently 3
        return ← withLocalDeclD `X α fun X => do
          let body := P.beta #[X]
          let evs ← R.eventual locals body X f
          let decls := (Array.range evs.size).map fun i => (Name.mkSimple s!"hev{i}", evs[i]!.2)
          withLocalDeclsDND decls fun hs => do
            let mut locals' := locals
            for h in hs do
              locals' := locals' ++ (← expandFact R.unfoldOk 16 h) ++ #[h]
            let some (P', pf) ← abduceProp R fuel locals' bound (some (X, f)) body | return none
            -- `pf : P' X → P X` may use the eventual facts `hs` at `X`
            let pred ← mkLambdaFVars #[X] P'
            let C' ← mkAppM (if freq then ``Filter.Frequently else ``Filter.Eventually) #[pred, f]
            if hs.isEmpty then
              let impl ← mkLambdaFVars #[X] pf
              let proof ← withLocalDeclD `h C' fun h => do
                mkLambdaFVars #[h] (← mkAppM (if freq then ``Filter.Frequently.mono
                  else ``Filter.Eventually.mono) #[h, impl])
              return some (C', proof)
            -- all eventual facts together, and the pointwise step from `P' X ∧ facts` to `P X`
            let mut eAll := evs.back!.1
            for i in (List.range (evs.size - 1)).reverse do
              eAll ← mkAppM ``Filter.Eventually.and #[evs[i]!.1, eAll]
            let lam ← mkLambdaFVars (#[X] ++ hs) pf
            let factsAt (Y : Expr) : Expr := Id.run do
              let mut acc := evs.back!.2.replaceFVar X Y
              for i in (List.range (evs.size - 1)).reverse do
                acc := mkApp2 (Lean.mkConst ``And) (evs[i]!.2.replaceFVar X Y) acc
              return acc
            let impl ← withLocalDeclD `Y α fun Y => do
              let pair := mkApp2 (Lean.mkConst ``And) (P'.replaceFVar X Y) (factsAt Y)
              withLocalDeclD `hp pair fun hp => do
                let hP' ← mkAppM ``And.left #[hp]
                let mut rest ← mkAppM ``And.right #[hp]
                let mut args : Array Expr := #[Y]
                for i in [0:evs.size] do
                  if i + 1 == evs.size then args := args.push rest
                  else
                    args := args.push (← mkAppM ``And.left #[rest])
                    rest ← mkAppM ``And.right #[rest]
                mkLambdaFVars #[Y, hp] (mkApp (mkAppN lam args).headBeta hP')
            let proof ← withLocalDeclD `h C' fun h => do
              let both ← mkAppM (if freq then ``Filter.Frequently.and_eventually
                else ``Filter.Eventually.and) #[h, eAll]
              mkLambdaFVars #[h] (← mkAppM (if freq then ``Filter.Frequently.mono
                else ``Filter.Eventually.mono) #[both, impl])
            return some (C', proof)
      if (← comparison? C).isSome then
        return ← abduceLeaf R locals bound C
      -- membership or nonemptiness read as comparisons
      match ← comparisonForm R.unfoldOk C with
      | some (C₁, eq) =>
        if C₁ == C || (← comparison? C₁).isNone && !C₁.isAppOfArity ``And 2 then return none
        let some (C', pf) ← abduceProp R fuel locals bound fv C₁ | return none
        let proof ← withLocalDeclD `h C' fun h => do
          mkLambdaFVars #[h] (← mkEqMPR eq (mkApp pf h))
        return some (C', proof)
      | none => return none

/-- The hypotheses of the theorem `thm` restated by `abduceProp`: a hypothesis the facts give is
dropped, another is replaced by its restatement. Returns the new statement, a proof of it from
`thm`, and the numbers of hypotheses dropped and restated; `none` when nothing changes.
Only hypotheses that no later binder and not the conclusion depend on are touched. -/
def restateAntecedents (R : Retrieval) (thm : Name) :
    TermElabM (Option (Expr × Expr × Nat × Nat)) := do
  let ci ← getConstInfo thm
  let lvls := ci.levelParams.map Level.param
  forallTelescopeReducing ci.type fun xs body => do
    let rec go (j : Nat) (newXs args : Array Expr) (dropped restated : Nat) (fuel : Nat) :
        TermElabM (Option (Expr × Expr × Nat × Nat)) := do
      match fuel with
      | 0 => return none
      | fuel + 1 =>
      if h : j < xs.size then
        let x := xs[j]
        let d := (← inferType x).replaceFVars (xs.extract 0 j) args
        let decl ← x.fvarId!.getDecl
        let dependsLater ← (xs.extract (j + 1) xs.size).anyM fun y => do
          return (← inferType y).containsFVar x.fvarId!
        let bodyDepends := body.containsFVar x.fvarId!
        if (← isProp d) && !dependsLater && !bodyDepends then
          let localFacts ← newXs.filterM fun y => do isProp (← inferType y)
          R.resetEvals
          match ← abduceProp R 64 localFacts #[] none d with
          | some (d', pf) =>
            if d'.isConstOf ``True then
              go (j + 1) newXs (args.push (mkApp pf (Lean.mkConst ``True.intro))) (dropped + 1)
                restated fuel
            else
              withLocalDecl decl.userName decl.binderInfo d' fun y =>
                go (j + 1) (newXs.push y) (args.push (mkApp pf y)) dropped (restated + 1) fuel
          | none =>
            withLocalDecl decl.userName decl.binderInfo d fun y =>
              go (j + 1) (newXs.push y) (args.push y) dropped restated fuel
        else
          withLocalDecl decl.userName decl.binderInfo d fun y =>
            go (j + 1) (newXs.push y) (args.push y) dropped restated fuel
      else
        if dropped + restated == 0 then return none
        let body' := body.replaceFVars xs args
        let value ← mkLambdaFVars newXs (mkAppN (Lean.mkConst thm lvls) args)
        let type ← mkForallFVars newXs body'
        return some (type, value, dropped, restated)
    go 0 #[] #[] 0 0 (xs.size + 1)

/-- Every reading of an index, once. -/
def allRefs (m : Std.HashMap Name (Array Ref)) : Array Ref := Id.run do
  let mut out : Array Ref := #[]
  for (_, rs) in m.toList do
    for r in rs do
      unless out.contains r do out := out.push r
  return out

/-- The retrieval over a fact index, excluding the theorems `exclude`: the readings sharing the
most corpus constants with the statement. Witnesses are not proposed: over the whole corpus
there are too many candidates. -/
def corpusRetrieval (facts : Facts) (unfoldOk : Name → Bool) (exclude : Array Name) :
    Retrieval where
  unfoldOk := unfoldOk
  pointwise := fun locals C =>
    retrieveFacts (rankedRefs facts.pointwise (corpusConsts unfoldOk C) exclude 16) locals C
  eventual := fun locals B X f =>
    retrieveEventual (rankedRefs facts.eventual (corpusConsts unfoldOk B) exclude 16) locals B X f

/-- The retrieval over every reading of a supplier set, with witnesses proposed from them. -/
def supplierRetrieval (suppliers : Array Name) (unfoldOk : Name → Bool) : MetaM Retrieval := do
  let facts ← factsOf suppliers unfoldOk
  let pw := allRefs facts.pointwise
  let ev := allRefs facts.eventual
  let evals ← IO.mkRef 32
  return {
    unfoldOk
    pointwise := fun locals C => retrieveFacts pw locals C
    eventual := fun locals B X f => retrieveEventual ev locals B X f
    witnesses := fun fv α => witnessCandidates facts unfoldOk fv α
    evals := some evals }

end ErdosProblems.ArgumentGraph.Abduce

/-! ## The command -/

namespace ErdosProblems.ArgumentGraph.Abduce

open Lean Meta Elab Command

/- Every atom below except `restate` is already a keyword of Lean. -/
syntax (name := restateCmd) "restate " ident " for " ident " using " ident+ : command

/-- `restate N for D using s₁ … sₙ` restates with the facts of the theorems `s₁ … sₙ`: for a
theorem `D`, each hypothesis the facts give is dropped and each other one is replaced by what it
still needs in the quantities no fact controls, and `N` is the restated theorem; for a
proposition `D` (a definition of type `Prop`), `N : D' → D` with `D'` the restatement. The kernel
checks `N`. The restatement is recomputed whenever the module is built. -/
@[command_elab restateCmd] def elabRestate : CommandElab := fun stx => do
  liftTermElabM do
    let name := (← getCurrNamespace) ++ stx[1].getId
    let target ← realizeGlobalConstNoOverloadWithInfo stx[3]
    let suppliers ← stx[5].getArgs.mapM fun s => realizeGlobalConstNoOverloadWithInfo s
    let unfoldOk := fun (n : Name) => [`ErdosProblems, `Erdos249257].any (·.isPrefixOf n)
    let R ← supplierRetrieval suppliers unfoldOk
    let ci ← getConstInfo target
    match ci with
    | .thmInfo _ =>
      let some (ty, val, dropped, restated) ← restateAntecedents R target
        | throwError "restate {target}: the facts of {suppliers.toList} change no hypothesis"
      addDecl (.thmDecl { name, levelParams := ci.levelParams, type := ty, value := val })
      logInfo m!"restate {target}: {dropped} hypothesis(es) dropped, {restated} restated:\n  {ty}"
    | .defnInfo d =>
      unless d.type.isProp do throwError "restate: {target} is not a proposition"
      R.resetEvals
      let some (C', pf) ← abduceProp R 64 #[] #[] none d.value
        | throwError "restate {target}: the facts of {suppliers.toList} change nothing"
      let ty ← mkArrow C' (Lean.mkConst target (d.levelParams.map Level.param))
      addDecl (.thmDecl { name, levelParams := d.levelParams, type := ty, value := pf })
      logInfo m!"restate {target}:\n  {C'}"
    | _ => throwError "restate: {target} is neither a theorem nor a proposition"

end ErdosProblems.ArgumentGraph.Abduce
