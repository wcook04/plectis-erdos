import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Erdos249257.FirstHarmonicGap

-- CANDIDATE GENERATED FROM THE ROUND-4 V4 SOURCE; LEAN COMPILATION NOT YET RUN.
-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0

/-!
# Residualisation

`residualise N for D using s₁ … sₙ` searches for a proof of the demand `D` from the readings of
the suppliers `s₁ … sₙ` and adds `N : ∀ residual clauses, D` once the kernel checks it; the
residual clauses are what the readings could not supply. A reading of a theorem is its statement with some leading binders instantiated, a
conjunct, the unfolding of a corpus definition, or a conjunct of an eventual conjunction.

* Witnesses and supplier parameters are metavariables of the root context applied to the local
  variables, so a supplier that fixes one (a depth function, an exponent) fixes it in every
  clause that shares it.
* A goal `∃ᶠ X in atTop, Q X` (or `∀ᶠ`) is split pointwise: every clause of `Q X` that a supplier
  gives for all large `X` is supplied along the filter; the others stay together as one
  residual `∃ᶠ X, …` (or `∀ᶠ X, …`).
* A clause for all large `X` may also come from an eventual reading by glue: the reading
  rewritten with equation lemmas, a conjunct of it, or its non-strict form, unified with the
  clause. No tactic ever sees a metavariable of the search.
* The cost of an alternative is the number of atomic clauses (counted through `∧`, `∃`, `∀`,
  corpus definitions and filter bodies) it leaves open, so leaving a goal whole costs as much
  as the goal and only supply lowers it.
-/

set_option autoImplicit false

open Lean Meta Elab Term

namespace ErdosProblems.ArgumentGraph.Residualise

/-! ## Cofinal quantifiers read as `Filter.Frequently` -/

theorem forall_exists₂_max_le_of_frequently {P : ℕ → ℕ → Prop}
    (h : ∃ᶠ X in Filter.atTop, ∃ L, P X L) :
    ∀ X₀ : ℕ, ∃ X L : ℕ, max X₀ 1 ≤ X ∧ P X L := by
  intro X₀
  obtain ⟨X, hX, L, hP⟩ := Filter.frequently_atTop.mp h (max X₀ 1)
  exact ⟨X, L, hX, hP⟩

theorem forall_exists_max_le_of_frequently {P : ℕ → Prop}
    (h : ∃ᶠ X in Filter.atTop, P X) : ∀ X₀ : ℕ, ∃ X : ℕ, max X₀ 1 ≤ X ∧ P X := by
  intro X₀
  obtain ⟨X, hX, hP⟩ := Filter.frequently_atTop.mp h (max X₀ 1)
  exact ⟨X, hX, hP⟩

theorem forall_exists_le_of_frequently {P : ℕ → Prop}
    (h : ∃ᶠ X in Filter.atTop, P X) : ∀ A : ℕ, ∃ X : ℕ, A ≤ X ∧ P X := by
  intro A
  obtain ⟨X, hX, hP⟩ := Filter.frequently_atTop.mp h A
  exact ⟨X, hX, hP⟩

/-- Rules the search applies like suppliers, read only at their whole conclusion. -/
def adapters : Array Name :=
  #[``forall_exists₂_max_le_of_frequently, ``forall_exists_max_le_of_frequently,
    ``forall_exists_le_of_frequently]

/-! ## Budgets and tactics -/

def budgeted {α : Type} (heartbeats : Nat) (x : MetaM α) : MetaM (Option α) := do
  withCurrHeartbeats <|
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := heartbeats * 1000 }) do
      tryCatchRuntimeEx (do return some (← x)) fun _ => return none

def budgetedTerm {α : Type} (heartbeats : Nat) (x : TermElabM α) : TermElabM (Option α) := do
  withCurrHeartbeats <|
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := heartbeats * 1000 }) do
      tryCatchRuntimeEx (do return some (← x)) fun _ => return none

/-- `isDefEq` within a budget, leaving no assignment behind when it fails. -/
def defEq (a b : Expr) : MetaM Bool := do
  let s ← saveState
  if (← budgeted 4000 (isDefEq a b)) == some true then return true
  s.restore
  return false

def closingTactics : List String :=
  ["norm_num", "positivity", "decide", "simp", "linarith", "omega"]

/-- A proof of `goalType` by the tactic `tac`, only for a goal with no metavariable (a tactic
may assign any metavariable it sees). Messages the tactic logs are dropped. -/
def runTac (goalType : Expr) (tac : String) : TermElabM (Option Expr) := do
  if goalType.hasMVar then return none
  let env ← getEnv
  let .ok stx := Parser.runParserCategory env `tactic tac | return none
  let msgs := (← getThe Core.State).messages
  let s ← Term.saveState
  let r ← budgetedTerm 4000 <| Term.withoutErrToSorry do
    let goal ← mkFreshExprMVar goalType .syntheticOpaque
    let remaining ← Tactic.run goal.mvarId! (Tactic.evalTactic stx)
    unless remaining.isEmpty do return none
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars goal
    if proof.hasSorry || proof.hasMVar then return none
    return some proof
  let out ← match r with
    | some (some p) => pure (some p)
    | _ => do s.restore; pure none
  modifyThe Core.State fun st => { st with messages := msgs }
  return out

def battery (goalType : Expr) : TermElabM (Option Expr) := do
  for tac in closingTactics do
    if let some p ← runTac goalType tac then return some p
  return none

/-- `proof : R` rewritten with the equation lemma `G` (right to left when `symm`), or `none`
when `G` does not occur or leaves side goals. -/
def rewriteWith (proof R : Expr) (G : Name) (symm : Bool) : MetaM (Option (Expr × Expr)) := do
  let s ← saveState
  try
    let heq ← mkConstWithFreshMVarLevels G
    let carrier ← mkFreshExprMVar R
    let r ← carrier.mvarId!.rewrite R heq symm
    unless r.mvarIds.isEmpty do
      s.restore
      return none
    return some (← mkEqMP r.eqProof proof, ← instantiateMVars r.eNew)
  catch _ =>
    s.restore
    return none

/-- What `proof : R` gives by glue: `R`, `R` rewritten by up to two equation lemmas of `glue`
in either direction, the conjuncts, and the non-strict form of a strict inequality. -/
def glueCandidates (glue : Array Name) (proof R : Expr) : MetaM (Array (Expr × Expr)) := do
  let mut stage : Array (Expr × Expr) := #[(proof, R)]
  for _ in [0:2] do
    let mut next := stage
    for (p, S) in stage do
      for g in glue do
        for symm in [false, true] do
          if let some c ← rewriteWith p S g symm then next := next.push c
    stage := next
  let mut out := #[]
  for (p, S) in stage do
    out := out.push (p, S)
    let S ← whnfR S
    if S.isAppOfArity ``And 2 then
      out := out.push (← mkAppM ``And.left #[p], S.appFn!.appArg!)
      out := out.push (← mkAppM ``And.right #[p], S.appArg!)
  let mut weak := #[]
  for (p, S) in out do
    if S.isAppOfArity ``LT.lt 4 then
      if let some q ← (try some <$> mkAppM ``le_of_lt #[p] catch _ => pure none) then
        weak := weak.push (q, ← inferType q)
  return out ++ weak

/-! ## Readings and the index -/

/-- One step of a reading: instantiate the first binder, take a conjunct, unfold a corpus
definition, or take a conjunct of an eventual conjunction. -/
inductive Step where
  | inst | left | right | unfold | evLeft | evRight
  deriving BEq, Inhabited, Repr

/-- A reading of a theorem, replayable in any context. -/
structure Ref where
  name : Name
  path : Array Step
  deriving BEq, Inhabited

/-- Statements of the readings of `stmt` with their paths (fresh metavariables for every
binder), for the index. -/
def readingPaths (unfoldOk : Name → Bool) (stmt : Expr) (path : Array Step) :
    Nat → MetaM (Array (Expr × Array Step))
  | 0 => do return #[(← instantiateMVars stmt, path)]
  | depth + 1 => do
    let stmt ← instantiateMVars stmt
    let mut out := #[(stmt, path)]
    let stmt ← whnfR stmt
    match stmt with
    | .forallE _ d b _ =>
        let m ← mkFreshExprMVar d
        return out ++ (← readingPaths unfoldOk (b.instantiate1 m) (path.push .inst) depth)
    | _ =>
      if stmt.isAppOfArity ``And 2 then
        out := out ++ (← readingPaths unfoldOk stmt.appFn!.appArg! (path.push .left) depth)
        out := out ++ (← readingPaths unfoldOk stmt.appArg! (path.push .right) depth)
        return out
      if stmt.isAppOfArity ``Filter.Eventually 3 then
        if let .lam n α body bi := stmt.getArg! 1 then
          if body.isAppOfArity ``And 2 then
            let f := stmt.getArg! 2
            for (b, step) in [(body.appFn!.appArg!, Step.evLeft), (body.appArg!, Step.evRight)] do
              let e ← mkAppM ``Filter.Eventually #[.lam n α b bi, f]
              out := out ++ (← readingPaths unfoldOk e (path.push step) depth)
        return out
      if let .const n _ := stmt.getAppFn then
        if unfoldOk n then
          if let some u ← unfoldDefinition? stmt then
            out := out ++ (← readingPaths unfoldOk u (path.push .unfold) depth)
      return out

/-- Add the readings of `n` (up to `depth` steps) to the index. -/
def indexTheorem (tree : DiscrTree Ref) (unfoldOk : Name → Bool) (n : Name) (depth : Nat) :
    MetaM (DiscrTree Ref × Nat) := do
  let some ci := (← getEnv).find? n | return (tree, 0)
  let paths ← withNewMCtxDepth do
    let lvls ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
    let ty := ci.type.instantiateLevelParams ci.levelParams lvls
    let rs := (← budgeted 2000 (readingPaths unfoldOk ty #[] depth)).getD #[]
    let mut out := #[]
    for (stmt, path) in rs do
      if let some keys ← budgeted 500 (DiscrTree.mkPath stmt) then
        out := out.push (keys, path)
    return out
  let mut tree := tree
  let mut added := 0
  for (keys, path) in paths do
    if keys.size ≤ 1 then continue
    if keys[0]! == .star then continue
    tree := tree.insertCore keys { name := n, path }
    added := added + 1
  return (tree, added)

/-- The index of the given theorems and of the adapters. -/
def indexOf (names : Array Name) (unfoldOk : Name → Bool) (depth : Nat := 10) :
    MetaM (DiscrTree Ref) := do
  let mut tree : DiscrTree Ref := {}
  for n in names do
    tree := (← indexTheorem tree unfoldOk n depth).1
  for n in adapters do
    tree := (← indexTheorem tree unfoldOk n 2).1
  return tree

/-- The index of every theorem of the modules under `roots`, and of the adapters. -/
def indexCorpus (roots : Array Name) (unfoldOk : Name → Bool) (depth : Nat := 8) :
    MetaM (DiscrTree Ref × Nat × Nat) := do
  let env ← getEnv
  let mut tree : DiscrTree Ref := {}
  let mut theorems := 0
  let mut entries := 0
  for modName in env.header.moduleNames, data in env.header.moduleData do
    unless roots.any (·.isPrefixOf modName) do continue
    for n in data.constNames do
      if n.isInternal then continue
      let some (.thmInfo _) := env.find? n | continue
      theorems := theorems + 1
      let (t, k) ← indexTheorem tree unfoldOk n depth
      tree := t
      entries := entries + k
  for n in adapters do
    tree := (← indexTheorem tree unfoldOk n 2).1
  return (tree, theorems, entries)

/-! ## Search state -/

structure Config where
  glue : Array Name
  unfoldPrefixes : Array Name
  rootLCtx : LocalContext
  rootInsts : LocalInstances
  index : DiscrTree Ref
  /-- theorems the search may not use (the held-out consumer, a withdrawn supplier) -/
  exclude : Array Name := #[]
  maxCandidates : Nat := 24
  /-- search calls allowed for one demand, counted across backtracking -/
  callBudget : Nat := 600
  budgetRef : IO.Ref Nat
  /-- facts from a supplier's existential under an ∃-transport (the conjuncts of its body),
  which may fix metavariables when they close a goal -/
  unifiable : Array Expr := #[]
  /-- inside an ∃-transport (no nested transport) -/
  inTransport : Bool := false
  /-- take a productive ∃-transport alternative whenever one succeeds (experiment switch) -/
  preferTransport : Bool := false
  /-- A bounded replay plan. Empty means the existing greedy choice at each node. -/
  choicePlan : Array Nat := #[]

/-- A clause of a filter body: a local metavariable standing for it, its clause count, and
its proof along the filter when some supplier gives it for all large `X`. -/
structure Leaf where
  mvar : Expr
  cost : Nat
  eventual : Option Expr
  deriving Inhabited

structure RState where
  /-- Selected-path decisions only: restored together with the metavariable state. -/
  choiceCursor : Nat := 0
  choiceWidths : Array Nat := #[]
  choiceTaken : Array Nat := #[]
  /-- root holes (residual clauses) with their clause counts -/
  holes : Array (Expr × Nat) := #[]
  leaves : Array Leaf := #[]
  /-- data metavariables whose type is not known to be inhabited: each is an obligation
  (an object to construct) until unification fixes it -/
  dataHoles : Array Expr := #[]
  /-- theorems whose readings the search applied -/
  used : Array Name := #[]
  /-- goals closed by a transported supplier fact -/
  factUses : Nat := 0

abbrev ResM := ReaderT Config (StateRefT RState TermElabM)

/-- The open clauses of the current state: its residual clauses, the kept clauses of the
filter body being decomposed, and the data obligations unification has not fixed. -/
def costNow : ResM Nat := do
  let s ← get
  let mut open_ := 0
  for d in s.dataHoles do
    if (← instantiateMVars d).hasMVar then open_ := open_ + 1
  return s.holes.foldl (fun a h => a + h.2) 0 +
    s.leaves.foldl (fun a l => a + (if l.eventual.isNone then l.cost else 0)) 0 + open_

/-- Whether `Nonempty t` synthesises. -/
def knownInhabited (t : Expr) : MetaM Bool := do
  try
    let u ← getLevel t
    return (← synthInstance? (mkApp (mkConst ``Nonempty [u]) t)).isSome
  catch _ => return false

inductive Mode where
  /-- an unsupplied clause becomes a residual clause -/
  | residual
  /-- every clause must be supplied, except a closed proposition (a named input) -/
  | eventual
  /-- inside a filter: an unsupplied clause becomes a clause of the filter's residual -/
  | pointwise (x filt : Expr)

structure Snapshot where
  term : Term.SavedState
  st : RState

def snapshot : ResM Snapshot := return { term := ← Term.saveState, st := ← get }

def Snapshot.restore (s : Snapshot) : ResM Unit := do
  s.term.restore
  set s.st

/-- A metavariable of the root context, applied to the local variables `ctx`. -/
def freshIn (ctx : Array Expr) (type : Expr) (kind : MetavarKind := .natural) : ResM Expr := do
  let cfg ← read
  let closed ← mkForallFVars ctx type
  let m ← withLCtx cfg.rootLCtx cfg.rootInsts <| mkFreshExprMVar closed kind
  return mkAppN m ctx

def conj : List Expr → Expr
  | [] => mkConst ``True
  | [a] => a
  | a :: rest => mkApp2 (mkConst ``And) a (conj rest)

/-- Assign the leaves, in order, the components of `h : conj leaves`. -/
def assignProjections (ls : List Leaf) (h : Expr) : MetaM Unit := do
  match ls with
  | [] => pure ()
  | [l] => l.mvar.mvarId!.assign h
  | l :: rest =>
      l.mvar.mvarId!.assign (← mkAppM ``And.left #[h])
      assignProjections rest (← mkAppM ``And.right #[h])

def isAtTop (f : Expr) : Bool := f.getAppFn.isConstOf ``Filter.atTop

def headsMatch (stmt T : Expr) : Bool :=
  match stmt, T with
  | .forallE .., .forallE .. => true
  | _, _ =>
    match stmt.getAppFn, T.getAppFn with
    | .const a _, .const b _ => a == b
    | _, _ => false

def unfoldable (T : Expr) : ResM Bool := do
  let .const n _ := T.getAppFn | return false
  unless (← read).unfoldPrefixes.any (·.isPrefixOf n) do return false
  match (← getEnv).find? n with
  | some (.defnInfo _) => return true
  | _ => return false

/-- Atomic clauses of `T`, counted through `∧`, `∃`, `∀`, corpus definitions and filter
bodies (the hypotheses of an implication are not clauses). -/
def clauseCountAux : Nat → Expr → ResM Nat
  | 0, _ => return 1
  | depth + 1, T => do
    let T ← whnfR (← instantiateMVars T)
    match T with
    | .forallE n d b bi => withLocalDecl n bi d fun x => clauseCountAux depth (b.instantiate1 x)
    | _ =>
      if T.isAppOfArity ``And 2 then
        return (← clauseCountAux depth T.appFn!.appArg!) + (← clauseCountAux depth T.appArg!)
      if T.isAppOfArity ``Exists 2 then
        return ← withLocalDeclD `w T.appFn!.appArg! fun w =>
          clauseCountAux depth (T.appArg!.beta #[w])
      if T.isAppOfArity ``Filter.Eventually 3 || T.isAppOfArity ``Filter.Frequently 3 then
        return ← withLocalDeclD `X (T.getArg! 0) fun x =>
          clauseCountAux depth ((T.getArg! 1).beta #[x])
      if ← unfoldable T then
        if let some u ← unfoldDefinition? T then return ← clauseCountAux depth u
      return 1

/-- Atomic clauses of `T`, counted to depth `depth`. -/
def clauseCount (T : Expr) (depth : Nat := 10) : ResM Nat := clauseCountAux depth T

def mkHole (ctx : Array Expr) (T : Expr) : ResM Expr := do
  let h ← freshIn ctx T .syntheticOpaque
  let c ← clauseCount T
  modify fun s => { s with holes := s.holes.push (h, c) }
  return h

/-- Replay a reading path of `proof : stmt` in context `ctx`: its proof, statement and
obligations (data binders become root metavariables, propositions obligations). -/
def replay (ctx : Array Expr) (proof stmt : Expr) (obls : Array Expr) :
    List Step → ResM (Option (Expr × Expr × Array Expr))
  | [] => return some (proof, ← instantiateMVars stmt, obls)
  | s :: rest => do
    let stmt ← whnfR (← instantiateMVars stmt)
    match s with
    | .inst =>
        let .forallE _ d b bi := stmt | return none
        if bi.isInstImplicit then
          let m ← mkFreshExprMVar d
          replay ctx (mkApp proof m) (b.instantiate1 m) (obls.push m) rest
        else if ← isProp d then
          let m ← mkFreshExprMVar d .syntheticOpaque
          replay ctx (mkApp proof m) (b.instantiate1 m) (obls.push m) rest
        else
          let m ← freshIn ctx d
          unless ← knownInhabited d do
            modify fun st => { st with dataHoles := st.dataHoles.push m }
          replay ctx (mkApp proof m) (b.instantiate1 m) obls rest
    | .left =>
        unless stmt.isAppOfArity ``And 2 do return none
        replay ctx (← mkAppM ``And.left #[proof]) stmt.appFn!.appArg! obls rest
    | .right =>
        unless stmt.isAppOfArity ``And 2 do return none
        replay ctx (← mkAppM ``And.right #[proof]) stmt.appArg! obls rest
    | .unfold =>
        let some u ← unfoldDefinition? stmt | return none
        replay ctx proof u obls rest
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
        replay ctx p (← inferType p) obls rest

/-- The conjuncts of `h : A₁ ∧ … ∧ Aₙ` as proofs, with `h` itself. -/
def conjunctFactsAux : Nat → Expr → Expr → MetaM (Array Expr)
  | 0, h, _ => return #[h]
  | depth + 1, h, T => do
    let T ← whnfR T
    if T.isAppOfArity ``And 2 then
      let l ← conjunctFactsAux depth (← mkAppM ``And.left #[h]) T.appFn!.appArg!
      let r ← conjunctFactsAux depth (← mkAppM ``And.right #[h]) T.appArg!
      return #[h] ++ l ++ r
    return #[h]

def conjunctFacts (h T : Expr) : MetaM (Array Expr) := conjunctFactsAux 32 h T

/-- Readings retrieved for `T`: at most `maxCandidates`, excluded theorems skipped. -/
def candidates (T : Expr) : ResM (Array Ref) := do
  let cfg ← read
  let refs ← cfg.index.getUnify T
  let mut out := #[]
  for r in refs do
    if out.size ≥ cfg.maxCandidates then break
    if cfg.exclude.contains r.name then continue
    unless out.contains r do out := out.push r
  return out

/-- An unsupplied clause with no recursion left: a residual clause, a named input, or a kept
clause of a filter body. -/
def leaveBase (ctx : Array Expr) (T : Expr) (mode : Mode) : ResM (Option (Expr × Nat)) := do
  match mode with
  | .residual => return some (← mkHole ctx T, 0)
  | .eventual =>
      if T.hasFVar || T.hasMVar then return none
      return some (← mkHole ctx T, 0)
  | .pointwise _ _ =>
      let leafM ← mkFreshExprMVar T .syntheticOpaque
      let c ← clauseCount T
      modify fun st => { st with leaves := st.leaves.push { mvar := leafM, cost := c, eventual := none } }
      return some (leafM, 0)

mutual

/-- A proof of `T` in context `ctx` and the number of clauses it leaves open. -/
def solve (k : Nat) (ctx : Array Expr) (T : Expr) (fuel : Nat) (mode : Mode) :
    ResM (Option (Expr × Nat)) := do
  match k with
  | 0 => leaveBase ctx T mode
  | k + 1 => do
    let cfg ← read
    let admitted ← cfg.budgetRef.modifyGet fun n =>
      if n < cfg.callBudget then (true, n + 1) else (false, n)
    unless admitted do return (← leaveBase ctx T mode)
    let T ← instantiateMVars T
    -- a transported supplier fact, which may fix witnesses (they carry the supplier's parameters)
    for f in cfg.unifiable do
      if ← defEq (← inferType f) T then
        modify fun st => { st with factUses := st.factUses + 1 }
        return some (f, 0)
    -- a hypothesis in context, without fixing any witness
    for x in ctx do
      let d ← inferType x
      if ← isProp d then
        if ← withNewMCtxDepth (defEq d T) then return some (x, 0)
    -- the battery, on a goal with no metavariable and no corpus constant
    if !T.hasMVar && !(T.getUsedConstants.any fun c => cfg.unfoldPrefixes.any (·.isPrefixOf c)) then
      if let some p ← battery T then return some (p, 0)
    if fuel == 0 then return (← leave k ctx T fuel mode)
    let slot := (← get).choiceCursor
    modify fun st => { st with choiceCursor := slot + 1,
      choiceWidths := st.choiceWidths.push 0, choiceTaken := st.choiceTaken.push 0 }
    let start ← snapshot
    let base ← costNow
    let mut alternatives : Array (Expr × Nat × Snapshot) := #[]
    -- a goal along `atTop`
    if (T.isAppOfArity ``Filter.Frequently 3 || T.isAppOfArity ``Filter.Eventually 3) &&
        isAtTop (T.getArg! 2) then
      if let .residual := mode then
        if let some p ← filterRule k ctx T fuel then
          let c := (← costNow) - base
          alternatives := alternatives.push (p, c, ← snapshot)
        start.restore
    -- readings retrieved from the index
    for ref in ← candidates T do
      start.restore
      let c0 ← mkConstWithFreshMVarLevels ref.name
      let some (proof, stmt, obls) ← replay ctx c0 (← inferType c0) #[] ref.path.toList | continue
      unless headsMatch stmt T do continue
      unless ← defEq stmt T do continue
      unless ← discharge k ctx obls fuel mode do continue
      modify fun st => { st with used := st.used.push ref.name }
      let p ← instantiateMVars proof
      let c := (← costNow) - base
      alternatives := alternatives.push (p, c, ← snapshot)
    -- ∃-transport: a reading `∃ x, Q x` for the goal `∃ x, P x` leaves `∀ x, Q x → P x`, with the
    -- conjuncts of `Q x` usable by unification; productive only when one of them closes a goal
    if T.isAppOfArity ``Exists 2 && !cfg.inTransport && fuel > 0 then
      let α := T.appFn!.appArg!
      let P := T.appArg!
      for ref in ← candidates T do
        start.restore
        let c0 ← mkConstWithFreshMVarLevels ref.name
        let some (proof, stmt, obls) ← replay ctx c0 (← inferType c0) #[] ref.path.toList | continue
        let stmt ← whnfR stmt
        unless stmt.isAppOfArity ``Exists 2 do continue
        unless ← defEq stmt.appFn!.appArg! α do continue
        let Q := stmt.appArg!
        let uses0 := (← get).factUses
        let body? ← withLocalDeclD `x α fun x => do
          let Qx ← whnfR (Q.beta #[x])
          withLocalDeclD `hq Qx fun hq => do
            let facts ← conjunctFacts hq Qx
            let r ← withReader (fun c => { c with unifiable := c.unifiable ++ facts, inTransport := true }) <|
              solve k ((ctx.push x).push hq) (P.beta #[x]) (fuel - 1) mode
            match r with
            | some (p, _) => return some (← mkLambdaFVars #[x, hq] (← instantiateMVars p))
            | none => return none
        let some body := body? | continue
        unless (← get).factUses > uses0 do continue
        unless ← discharge k ctx obls fuel mode do continue
        modify fun st => { st with used := st.used.push ref.name }
        let p ← mkAppM ``Exists.imp #[body, ← instantiateMVars proof]
        let c := (← costNow) - base
        alternatives := alternatives.push (p, c, ← snapshot)
    -- structure
    start.restore
    if let some p ← structural k ctx T fuel mode then
      let c := (← costNow) - base
      alternatives := alternatives.push (p, c, ← snapshot)
    -- leave it
    start.restore
    if let some (p, _) ← leave k ctx T fuel mode then
      let c := (← costNow) - base
      alternatives := alternatives.push (p, c, ← snapshot)
    if alternatives.isEmpty then
      start.restore
      return none
    let mut cheapest := 0
    for i in [1:alternatives.size] do
      if alternatives[i]!.2.1 < alternatives[cheapest]!.2.1 then cheapest := i
    let chosen := cfg.choicePlan[slot]?.getD cheapest
    if chosen ≥ alternatives.size then
      start.restore
      return none
    let (p, c, saved) := alternatives[chosen]!
    saved.restore
    modify fun st => { st with
      choiceWidths := st.choiceWidths.set! slot alternatives.size,
      choiceTaken := st.choiceTaken.set! slot chosen }
    return some (p, c)

/-- Prove a reading's obligations (instances by synthesis). -/
def discharge (k : Nat) (ctx : Array Expr) (obls : Array Expr) (fuel : Nat) (mode : Mode) :
    ResM Bool := do
  match k with
  | 0 => return false
  | k + 1 => do
    for o in obls do
      if ← o.mvarId!.isAssigned then continue
      let oT ← instantiateMVars (← inferType o)
      if (← isClass? oT).isSome then
        match ← (try (some <$> synthInstance oT) catch _ => pure none) with
        | some inst => o.mvarId!.assign inst
        | none => return false
      else
        match ← solve k ctx oT (fuel - 1) mode with
        | some (p, _) => o.mvarId!.assign p
        | none => return false
    return true

def structural (k : Nat) (ctx : Array Expr) (T : Expr) (fuel : Nat) (mode : Mode) :
    ResM (Option Expr) := do
  match k with
  | 0 => return none
  | k + 1 => do
    match T with
    | .forallE n d b bi =>
        match mode with
        | .pointwise .. => return none
        | _ =>
          withLocalDecl n bi d fun x => do
            match ← solve k (ctx.push x) (b.instantiate1 x) fuel mode with
            | some (p, _) => return some (← mkLambdaFVars #[x] p)
            | none => return none
    | _ =>
      if T.isAppOfArity ``And 2 then
        let A := T.appFn!.appArg!
        let B := T.appArg!
        -- the larger conjunct first, so that witnesses it fixes reach the side conditions
        let swapped := A.approxDepth < B.approxDepth
        let (first, second) := if swapped then (B, A) else (A, B)
        let some (p1, _) ← solve k ctx first fuel mode | return none
        let some (p2, _) ← solve k ctx (← instantiateMVars second) fuel mode | return none
        let (pa, pb) := if swapped then (p2, p1) else (p1, p2)
        return some (← mkAppM ``And.intro #[pa, pb])
      if T.isAppOfArity ``Exists 2 then
        let α := T.appFn!.appArg!
        let pred := T.appArg!
        let w ← freshIn ctx α
        unless ← knownInhabited α do
          modify fun st => { st with dataHoles := st.dataHoles.push w }
        let some (p, _) ← solve k ctx (pred.beta #[w]) fuel mode | return none
        return some (← mkAppOptM ``Exists.intro #[α, pred, w, p])
      if ← unfoldable T then
        if let some T' ← unfoldDefinition? T then
          return (← solve k ctx T' (fuel - 1) mode).map (·.1)
      return none

/-- An unsupplied clause: a residual clause, a named input, or a clause of a filter body
(supplied along the filter when some reading gives it for all large `X`). -/
def leave (k : Nat) (ctx : Array Expr) (T : Expr) (fuel : Nat) (mode : Mode) :
    ResM (Option (Expr × Nat)) := do
  match k with
  | 0 => leaveBase ctx T mode
  | k + 1 => do
    match mode with
    | .residual => return some (← mkHole ctx T, 0)
    | .eventual =>
        if T.hasFVar || T.hasMVar then return none
        return some (← mkHole ctx T, 0)
    | .pointwise x f =>
        let leafM ← mkFreshExprMVar T .syntheticOpaque
        let c ← clauseCount T
        if fuel > 0 then
          if let some e ← supplyEventually k ctx.pop x f T (fuel - 1) then
            modify fun st => { st with leaves := st.leaves.push { mvar := leafM, cost := c, eventual := some e } }
            return some (leafM, 0)
        modify fun st => { st with leaves := st.leaves.push { mvar := leafM, cost := c, eventual := none } }
        return some (leafM, 0)

/-- A proof of `∀ᶠ X in f, T X`: from a reading directly, or from an eventual reading
`∀ᶠ X, R X` whose glue candidates unify with `T X`. -/
def supplyEventually (k : Nat) (outer : Array Expr) (x f T : Expr) (fuel : Nat) :
    ResM (Option Expr) := do
  match k with
  | 0 => return none
  | k + 1 => do
    let s ← snapshot
    let E ← mkAppM ``Filter.Eventually #[← mkLambdaFVars #[x] T, f]
    if let some (e, _) ← solve k outer E fuel .eventual then return some e
    s.restore
    -- every eventual reading along `f`
    let α ← inferType x
    let pat ← mkAppM ``Filter.Eventually #[← mkFreshExprMVar (← mkArrow α (mkSort levelZero)), f]
    for ref in ← candidates pat do
      s.restore
      let c0 ← mkConstWithFreshMVarLevels ref.name
      let some (proof, stmt, obls) ← replay outer c0 (← inferType c0) #[] ref.path.toList | continue
      unless stmt.isAppOfArity ``Filter.Eventually 3 do continue
      let R := (stmt.getArg! 1).beta #[x]
      let glue := (← read).glue
      let found ← withLocalDeclD `hR R fun hR => do
        for (p, C) in ← glueCandidates glue hR R do
          if ← defEq C T then
            return some (← mkLambdaFVars #[x, hR] (← instantiateMVars p))
        return none
      let some g := found | continue
      unless ← discharge k outer obls fuel .eventual do continue
      modify fun st => { st with used := st.used.push ref.name }
      return some (← mkAppM ``Filter.Eventually.mono #[← instantiateMVars proof, g])
    s.restore
    return none

/-- `∃ᶠ X in atTop, Q X` or `∀ᶠ X in atTop, Q X`: decompose `Q X`, supply what some reading
gives for all large `X`, and keep the rest as one residual along the filter. -/
def filterRule (k : Nat) (ctx : Array Expr) (T : Expr) (fuel : Nat) : ResM (Option Expr) := do
  match k with
  | 0 => return none
  | k + 1 => do
    let freq := T.isAppOfArity ``Filter.Frequently 3
    let α := T.getArg! 0
    let pred := T.getArg! 1
    let f := T.getArg! 2
    withLocalDeclD `X α fun x => do
      let saved := (← get).leaves
      modify fun s => { s with leaves := #[] }
      let r ← solve k (ctx.push x) (pred.beta #[x]) (fuel - 1) (.pointwise x f)
      let leaves := (← get).leaves
      modify fun s => { s with leaves := saved }
      let some (q, _) := r | return none
      let kept := leaves.filter (·.eventual.isNone)
      let sup := leaves.filter (·.eventual.isSome)
      let keptT ← kept.mapM fun l => do instantiateMVars (← inferType l.mvar)
      let supT ← sup.mapM fun l => do instantiateMVars (← inferType l.mvar)
      let K := conj keptT.toList
      let S := conj supT.toList
      let mut eS ← mkAppM ``Filter.eventually_true #[f]
      if !sup.isEmpty then
        eS := sup.back!.eventual.getD eS
        for l in (sup.pop).reverse do
          eS ← mkAppM ``Filter.Eventually.and #[l.eventual.getD eS, eS]
      let glue ← withLocalDeclD `hKS (mkApp2 (mkConst ``And) K S) fun hKS => do
        assignProjections kept.toList (← mkAppM ``And.left #[hKS])
        assignProjections sup.toList (← mkAppM ``And.right #[hKS])
        mkLambdaFVars #[x, hKS] (← instantiateMVars q)
      let predK ← mkLambdaFVars #[x] K
      if freq then
        let comb ←
          if kept.isEmpty then
            mkAppM ``Filter.Eventually.frequently
              #[← mkAppM ``Filter.Eventually.and #[← mkAppM ``Filter.eventually_true #[f], eS]]
          else
            let hole ← mkHole ctx (← mkAppM ``Filter.Frequently #[predK, f])
            mkAppM ``Filter.Frequently.and_eventually #[hole, eS]
        return some (← mkAppM ``Filter.Frequently.mono #[comb, glue])
      else
        let hK ←
          if kept.isEmpty then mkAppM ``Filter.eventually_true #[f]
          else mkHole ctx (← mkAppM ``Filter.Eventually #[predK, f])
        return some (← mkAppM ``Filter.Eventually.mono #[← mkAppM ``Filter.Eventually.and #[hK, eS], glue])

end

/-- Residualise `demand` against `index`: the proof term with its holes, and the number of
search calls. -/
def searchResidual (demand : Expr) (index : DiscrTree Ref) (glue : Array Name) (fuel : Nat := 8)
    (exclude : Array Name := #[]) (callBudget : Nat := 600) (maxCandidates : Nat := 24)
    (preferTransport : Bool := false) :
    TermElabM (Option Expr × Nat × Array Name) := do
  let budgetRef ← IO.mkRef 0
  let cfg : Config := {
    glue, unfoldPrefixes := #[`ErdosProblems, `Erdos249257, `DemandLedger]
    rootLCtx := ← getLCtx, rootInsts := ← getLocalInstances
    index, exclude, callBudget, maxCandidates, budgetRef, preferTransport }
  let (r, st) ← ((solve 100000 #[] demand fuel .residual).run cfg).run {}
  let mut used : Array Name := #[]
  for n in st.used do
    unless used.contains n || adapters.contains n do used := used.push n
  return (r.map (·.1), ← budgetRef.get, used)

/-- One deterministic replay, sharing one budget across all explored alternatives.
The trace describes only the finally selected path; prefix mutations can enumerate other paths.
A missing proof is UNKNOWN, never a refutation. -/
def searchResidualReplay (demand : Expr) (index : DiscrTree Ref) (glue : Array Name)
    (choicePlan : Array Nat) (fuel : Nat := 8) (exclude : Array Name := #[])
    (callBudget : Nat := 600) (maxCandidates : Nat := 24) :
    TermElabM (Option Expr × Nat × Array Name × Array Nat × Array Nat) := do
  let budgetRef ← IO.mkRef 0
  let cfg : Config := {
    glue, unfoldPrefixes := #[`ErdosProblems, `Erdos249257, `DemandLedger]
    rootLCtx := ← getLCtx, rootInsts := ← getLocalInstances
    index, exclude, callBudget, maxCandidates, budgetRef, choicePlan }
  let (r, st) ← ((solve 100000 #[] demand fuel .residual).run cfg).run {}
  let mut used : Array Name := #[]
  for n in st.used do
    unless used.contains n || adapters.contains n do used := used.push n
  return (r.map (·.1), ← budgetRef.get, used, st.choiceTaken, st.choiceWidths)

/-- Close residual clauses that became closed propositions (a witness fixed later) by the
battery, abstract the rest, report them, and add `name : ∀ residual clauses, demand` after
the kernel checks it. Returns the number of propositional clauses and the suppliers used. -/
def certify (name : Name) (label : String) (proof : Expr) (used : Array Name) :
    TermElabM (Nat × Array Name) := do
  let proof ← instantiateMVars proof
  for m in (← getMVars proof) do
    unless ← m.isAssigned do
      let t ← instantiateMVars (← m.getType)
      if (← isProp t) && !t.hasMVar then
        if let some p ← runTac t "(intros; first | norm_num | positivity | decide | simp)" then
          m.assign p
  let proof ← instantiateMVars proof
  let res ← abstractMVars proof
  let value := res.expr
  let type ← instantiateMVars (← inferType value)
  -- only the abstracted holes: `type` continues into the demand's own binders
  let (props, objects) ← forallBoundedTelescope type (some res.numMVars) fun xs _ => do
    let mut n := 0
    let mut objs := 0
    for x in xs do
      let t ← inferType x
      if ← isProp t then
        n := n + 1
        logInfo m!"[{label}]  clause {← x.fvarId!.getUserName} : {t}"
      else if ← knownInhabited t then
        logInfo m!"[{label}]  witness {← x.fvarId!.getUserName} : {t}"
      else
        objs := objs + 1
        logInfo m!"[{label}]  object {← x.fvarId!.getUserName} : {t}"
    return (n, objs)
  addDecl (.thmDecl { name, levelParams := res.paramNames.toList, type, value })
  logInfo m!"[{label}] certificate {name}: {props} propositional clause(s), {objects} \
    object(s) to construct, {res.numMVars - props - objects} witness(es); readings applied from \
    {used.toList}"
  return (props + objects, used)

end ErdosProblems.ArgumentGraph.Residualise


/-! ## The command -/

namespace ErdosProblems.ArgumentGraph.Residualise

open Lean Meta Elab Command

/- Every atom below except `residualise` is already a keyword of Lean, so importing this module
reserves no new word (a reserved `glue` or `as` would break those names downstream). -/
syntax (name := residualiseCmd)
  "residualise " ident " for " ident " using " ident+ (" with " ident+)? : command

/-- `residualise N for D using s₁ … sₙ with g₁ … gₖ` searches for a proof of the proposition `D`
from the readings of `s₁ … sₙ`, gluing eventual readings with the equation lemmas `g₁ … gₖ`, and
adds `N : ∀ residual clauses, D` after the kernel checks it. The residual clauses are logged.
The certificate is regenerated whenever the module is built, so a change in the search that
changes its statement breaks every use of `N`. -/
@[command_elab residualiseCmd] def elabResidualise : CommandElab := fun stx => do
  liftTermElabM do
    let name := (← getCurrNamespace) ++ stx[1].getId
    let demandName ← realizeGlobalConstNoOverloadWithInfo stx[3]
    let suppliers ← stx[5].getArgs.mapM fun s => realizeGlobalConstNoOverloadWithInfo s
    let glue ← if stx[6].isNone then pure #[]
      else stx[6][1].getArgs.mapM fun s => realizeGlobalConstNoOverloadWithInfo s
    let unfoldOk := fun (n : Name) => [`ErdosProblems, `Erdos249257].any (·.isPrefixOf n)
    let index ← indexOf suppliers unfoldOk
    let (r, calls, used) ← searchResidual (mkConst demandName) index glue
    match r with
    | none => throwError "residualise {demandName}: no residualisation found ({calls} calls)"
    | some proof =>
        let (clauses, _) ← certify name s!"{demandName}" proof used
        addDocStringCore name <| s!"`{demandName}` from its residual clauses (the binders of this \
          theorem): found by `residualise` from the readings of {suppliers.toList} \
          ({clauses} clause(s) or object(s) left open, {calls} search calls) and checked by the \
          kernel."

end ErdosProblems.ArgumentGraph.Residualise

/-! ## Experiment: ∃-transport on the #249 certificate endpoint

The demand is `Irrational (∑' n, φ(n)/2^n)`. The suppliers are the certificate consumer
`irrational_totient_series_of_certificate_supply` and the subset barrier
`exists_certifiedKill_of_first_harmonic_gap_subset`. Arm A uses the default objective (fewest
clauses); arm B takes a productive ∃-transport whenever one exists, which should leave the
support-gap interface (some support in `[N₀, 2X)` whose average first cosine is at most `9/10`). -/

open ErdosProblems.ArgumentGraph.Residualise Erdos249257.TotientTailPeriodKiller in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ci ← Lean.getConstInfo ``irrational_totient_series_of_certificate_supply
  let .forallE _ _ goal _ := ci.type | Lean.logError "unexpected consumer type"
  let unfoldOk := fun (n : Lean.Name) => [`ErdosProblems, `Erdos249257].any (·.isPrefixOf n)
  let index ← indexOf #[``irrational_totient_series_of_certificate_supply,
    ``exists_certifiedKill_of_first_harmonic_gap_subset] unfoldOk
  for (label, prefer, name) in [("A default objective", false, `ErdosProblems.ArgumentGraph.Residualise.endpoint_default),
      ("B prefer transport", true, `ErdosProblems.ArgumentGraph.Residualise.endpoint_transport)] do
    let (r, calls, used) ← searchResidual goal index #[] (preferTransport := prefer)
    Lean.logInfo m!"[{label}] search calls: {calls}"
    match r with
    | some proof => discard <| certify name label proof used
    | none => Lean.logError m!"[{label}] no residualisation found"

#check @ErdosProblems.ArgumentGraph.Residualise.endpoint_transport
#print axioms ErdosProblems.ArgumentGraph.Residualise.endpoint_default
#print axioms ErdosProblems.ArgumentGraph.Residualise.endpoint_transport

/-! Arm C: the transport rule alone. The supply statement's binders `h`, `0 < h`, `N₀` are opened,
the inner goal `∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill h N L` is residualised with transport preferred,
and the result is closed over the binders and certified. -/

open ErdosProblems.ArgumentGraph.Residualise Erdos249257.TotientTailPeriodKiller in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ci ← Lean.getConstInfo ``irrational_totient_series_of_certificate_supply
  let .forallE _ supply _ _ := ci.type | Lean.logError "unexpected consumer type"
  let unfoldOk := fun (n : Lean.Name) => [`ErdosProblems, `Erdos249257].any (·.isPrefixOf n)
  let index ← indexOf #[``exists_certifiedKill_of_first_harmonic_gap_subset] unfoldOk
  let r ← Lean.Meta.forallTelescope supply fun xs body => do
    let (r, calls, used) ← searchResidual body index #[] (preferTransport := true)
    Lean.logInfo m!"[C transport on the supply goal] search calls: {calls}, used {used}"
    match r with
    | some p => return some (← Lean.Meta.mkLambdaFVars xs p, used)
    | none => return none
  match r with
  | some (proof, used) =>
      discard <| certify `ErdosProblems.ArgumentGraph.Residualise.supply_transport
        "C transport on the supply goal" proof used
  | none => Lean.logError "[C] no residualisation found"

#check @ErdosProblems.ArgumentGraph.Residualise.supply_transport
#print axioms ErdosProblems.ArgumentGraph.Residualise.supply_transport

-- CANDIDATE: requires the replay extension to Residualise.lean.
-- Not compiled in this response. No admitted proof holes are used.

open Lean Meta Elab Term
namespace ErdosProblems.ArgumentGraph.Residualise

/-- A closed joint residual and a proof of its implication to the fixed endpoint.
Data witnesses are existentially packed, NOT silently treated as discharged. -/
structure ClosedResidual where
  levelParams : List Name
  residual : Expr
  target : Expr
  proof : Expr
  used : Array Name
  unchanged : Bool

/-- Pack the first n arguments of a closed proof type as a dependent existential.
Even proof-dependent types are preserved; no flat string conjunction is used. -/
def packArguments : Nat → Expr → MetaM Expr
  | 0, _ => return mkConst ``True
  | n + 1, ty => do
    let ty ← whnfR ty
    let .forallE name dom body bi := ty
      | throwError "residual telescope shorter than its recorded argument count"
    withLocalDecl name bi dom fun x => do
      let rest ← packArguments n (body.instantiate1 x)
      mkAppM ``Exists #[← mkLambdaFVars #[x] rest]

/-- Consume the joint residual by dependent Exists elimination. -/
def applyPackedArguments : Nat → Expr → Expr → Expr → MetaM Expr
  | 0, _, f, _ => return f
  | n + 1, ty, f, h => do
    let ty ← whnfR ty
    let .forallE name dom body bi := ty
      | throwError "malformed residual telescope"
    let consume ← withLocalDecl name bi dom fun x => do
      let tail := body.instantiate1 x
      let R ← packArguments n tail
      withLocalDeclD `remaining R fun hr => do
        let result ← applyPackedArguments n tail (mkApp f x) hr
        mkLambdaFVars #[x, hr] result
    mkAppM ``Exists.elim #[h, consume]

/-- Freeze a proof with holes before restoring the replay state. -/
def closeResidual (target proof : Expr) (used : Array Name) : TermElabM ClosedResidual := do
  unless ← isProp target do throwError "endpoint must be a proposition"
  let proof ← instantiateMVars proof
  if proof.hasSorry then throwError "a residual proof contains sorry"
  let abs ← abstractMVars proof
  let value := abs.expr
  let ty ← instantiateMVars (← inferType value)
  if value.hasMVar || ty.hasMVar || value.hasFVar || ty.hasFVar then
    throwError "residual closure left a metavariable or local variable"
  let R ← packArguments abs.numMVars ty
  let rebuilt ← withLocalDeclD `residual R fun h => do
    let out ← applyPackedArguments abs.numMVars ty value h
    let outTy ← inferType out
    unless ← isDefEq outTy target do
      throwError "residual reconstructs a different endpoint"
    mkLambdaFVars #[h] out
  let unchanged ← if abs.numMVars == 1 then do
      let ty ← whnfR ty
      match ty with
      | .forallE _ dom _ _ => withoutModifyingState <| isDefEq dom target
      | _ => pure false
    else pure false
  return {levelParams := abs.paramNames.toList, residual := R, target,
          proof := rebuilt, used, unchanged}

structure FrontierBudget where
  maxReplays : Nat := 64
  callsPerReplay : Nat := 600
  totalCalls : Nat := 20000
  maxQueued : Nat := 4096
  maxSaved : Nat := 64
  fuel : Nat := 10
  maxCandidates : Nat := 32

/-- Replay is a bounded search tactic, not a completeness claim. Syntactically
unchanged endpoints are not promoted, but their alternative branches are explored.
Logical ranking happens AFTER closure, never by clause count inside certification. -/
def collectResidualFrontier (target : Expr) (index : DiscrTree Ref)
    (glue exclude : Array Name) (cfg : FrontierBudget := {}) :
    TermElabM (Array ClosedResidual × Nat × Nat) := do
  if target.hasMVar || target.hasFVar then
    throwError "close the endpoint telescope before collecting a frontier"
  let base ← Term.saveState
  let mut queue : Array (Array Nat) := #[#[]]
  let mut seen : Array (Array Nat) := #[]
  let mut saved : Array ClosedResidual := #[]
  let mut cursor := 0
  let mut calls := 0
  let mut replays := 0
  while cursor < queue.size && replays < cfg.maxReplays && calls < cfg.totalCalls do
    let plan := queue[cursor]!
    cursor := cursor + 1
    if seen.contains plan then continue
    seen := seen.push plan
    base.restore
    let budget := min cfg.callsPerReplay (cfg.totalCalls - calls)
    let (proof?, spent, used, taken, widths) ←
      searchResidualReplay target index glue plan cfg.fuel exclude budget cfg.maxCandidates
    calls := calls + spent
    replays := replays + 1
    -- Each prefix changes one decision; later decisions are recomputed, not copied
    -- from a different witness/metavariable context.
    for i in [:taken.size] do
      if i >= widths.size then break
      for j in [:widths[i]!] do
        if j == taken[i]! || queue.size >= cfg.maxQueued then continue
        let next := (taken.extract 0 i).push j
        unless seen.contains next || queue.contains next do queue := queue.push next
    if let some proof := proof? then
      let candidate? ← try
        pure (some (← closeResidual target proof used))
      catch _ => pure none
      let some c := candidate? | continue
      if c.unchanged then continue
      let mut duplicate := false
      for old in saved do
        -- Universe parameter alignment is required before comparing polymorphic
        -- candidates; retain unequal parameter lists rather than guessing.
        if old.levelParams == c.levelParams then
          if ← withoutModifyingState (isDefEq old.residual c.residual) then
            duplicate := true
      unless duplicate || saved.size >= cfg.maxSaved do saved := saved.push c
  base.restore
  return (saved, replays, calls)

/-- Kernel-check and admit a reconstruction. The existing axiom/dependency policy
must ALSO inspect the declaration before it becomes a corpus supplier. -/
def admitResidual (name : Name) (c : ClosedResidual) : TermElabM Unit := do
  if c.unchanged || c.proof.hasSorry || c.proof.hasMVar || c.proof.hasFVar then
    throwError "refused an unchanged or open candidate"
  let ty ← mkArrow c.residual c.target
  addDecl (.thmDecl {name, levelParams := c.levelParams, type := ty, value := c.proof})

/-- Search for an implication; failure remains unknown. A successful proof is
admitted by addDecl, not by an authored success flag. For polymorphic candidates,
this conservative implementation compares only identical parameter lists. -/
def checkResidualImplication (name : Name) (a b : ClosedResidual) :
    TermElabM Bool := do
  unless a.levelParams == b.levelParams do return false
  unless ← withoutModifyingState (isDefEq a.target b.target) do return false
  let ty ← mkArrow a.residual b.residual
  for tactic in ["intro h; exact h", "intro h; simpa using h", "aesop", "intro h; aesop"] do
    if let some p ← runTac ty tactic then
      if p.hasSorry || p.hasMVar || p.hasFVar then continue
      addDecl (.thmDecl {name, levelParams := a.levelParams, type := ty, value := p})
      return true
  return false

end ErdosProblems.ArgumentGraph.Residualise

-- CANDIDATE: not compiled here. Run after the replay and frontier modules compile.
-- These are closure tests, not claims of corpus discovery.

open Lean Meta Elab Term
open ErdosProblems.ArgumentGraph.Residualise

open Lean Elab Command in
run_cmd liftTermElabM do
  let target := mkConst ``False
  let hole ← mkFreshExprMVar target .syntheticOpaque
  let c ← closeResidual target hole #[]
  unless c.unchanged do throwError "an unchanged endpoint was not recognised"
  logInfo "identity residual recognised without admitting False"

open Lean Elab Command in
run_cmd liftTermElabM do
  let x ← mkFreshExprMVar (mkConst ``Empty) .syntheticOpaque
  let p ← mkAppM ``Nonempty.intro #[x]
  let target ← inferType p
  let c ← closeResidual target p #[]
  unless c.residual.isAppOfArity ``Exists 2 do
    throwError "the unconstructed data object was lost"
  admitResidual `Plectis.Round4Smoke.data_obligation_preserved c
  logInfo m!"retained data obligation: {c.residual}"

#print axioms Plectis.Round4Smoke.data_obligation_preserved
