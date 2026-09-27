import ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactorEstimate
import ErdosProblems.Erdos249.TypeBReturnV8.PeripheralFiniteBridge
import ErdosProblems
import Erdos249257
import ErdosProblems.DemandLedger.Basic
import ErdosProblems.ArgumentGraph.Derived.Erdos1041
import ErdosProblems.ArgumentGraph.Derived.Erdos1049
import ErdosProblems.ArgumentGraph.Derived.Erdos243
import ErdosProblems.ArgumentGraph.Derived.Erdos249
import ErdosProblems.ArgumentGraph.Derived.Erdos251
import ErdosProblems.ArgumentGraph.Derived.Erdos257
import ErdosProblems.ArgumentGraph.Derived.Erdos269
import ErdosProblems.ArgumentGraph.Derived.Erdos68
import ErdosProblems.ArgumentGraph.Results.Erdos1041
import ErdosProblems.ArgumentGraph.Results.Erdos243
import ErdosProblems.ArgumentGraph.Results.Erdos251
import ErdosProblems.EightPaperR21Audit
import ErdosProblems.EightPaperRecoveryAudit
import ErdosProblems.Erdos1041.PaperCorrespondenceAudit
import ErdosProblems.Erdos1041.PaperTrinomialCoverageAuditR20
import ErdosProblems.Erdos1049.PaperCorrespondenceAudit
import ErdosProblems.Erdos1049.PaperR20.RecoveredProofAudit
import ErdosProblems.Erdos243.PaperCompleteR20.CubicArithmeticAudit
import ErdosProblems.Erdos243.PaperCompleteR20.CubicRecoveryAudit
import ErdosProblems.Erdos243.PaperCorrespondenceAudit
import ErdosProblems.Erdos249.PaperCompleteR20.CyclotomicRecoveryAudit
import ErdosProblems.Erdos249.PaperCompleteR20.DenominatorRecoveryAudit
import ErdosProblems.Erdos249.PaperCompleteR20.FiniteCarryCorrespondence
import ErdosProblems.Erdos249.PaperCompleteR20.FiniteCertificateBatch
import ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodelEndpoint
import ErdosProblems.Erdos249.PaperCompleteR20.GridArcRealInterface
import ErdosProblems.Erdos249.PaperCompleteR20.LcmGridCorrespondence
import ErdosProblems.Erdos249.PaperCompleteR20.MobiusSquareReduction
import ErdosProblems.Erdos249.PaperCompleteR20.RadicalDecomposition
import ErdosProblems.Erdos249.PaperCompleteR20.RationalSpacingCorrespondence
import ErdosProblems.Erdos249.PaperCompleteR20.SignedDyadicClearing
import ErdosProblems.Erdos249.PaperCompleteR20.TailDepthCorrespondence
import ErdosProblems.Erdos249.PaperCorrespondenceAudit
import ErdosProblems.Erdos249.PaperCorrespondenceAuditAdditive
import ErdosProblems.Erdos249.PaperCorrespondenceAuditRecovery
import ErdosProblems.Erdos251.PaperCompleteR20.ExactDenominator
import ErdosProblems.Erdos251.PaperCompleteR20.FiniteSeparation
import ErdosProblems.Erdos251.PaperCompleteR20.LocalTargetInterval
import ErdosProblems.Erdos251.PaperCompleteR20.SparseConstructionAudit
import ErdosProblems.Erdos251.PaperCorrespondenceAudit
import ErdosProblems.Erdos257.PaperCompleteR20.AchievementGeometry
import ErdosProblems.Erdos257.PaperCompleteR20.CofinalCarryCollapse
import ErdosProblems.Erdos257.PaperCompleteR20.GeneralRepairCorrespondence
import ErdosProblems.Erdos257.PaperCompleteR20.MersenneConstantDecimal
import ErdosProblems.Erdos257.PaperCompleteR20.QuotientRowReal
import ErdosProblems.Erdos257.PaperCompleteR20.TerminalSetCorrespondence
import ErdosProblems.Erdos257.PaperCorrespondenceAudit
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditive
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditiveWave10
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditiveWave11
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditiveWave12
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditiveWave2
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditiveWave3
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditiveWave4
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditiveWave5
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditiveWave6
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditiveWave7
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditiveWave8
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditiveWave9
import ErdosProblems.Erdos269.PaperCompleteR20.UniformRankAudit
import ErdosProblems.Erdos269.PaperCorrespondenceAudit
import ErdosProblems.Erdos68.PaperCompleteFiniteSizeCertificate
import ErdosProblems.Erdos68.PaperCorrespondenceAudit
import ErdosProblems.Erdos68.PaperCorrespondenceAuditAdditive

/-!
# Residualisation

`residualise D` searches for a proof of the demand `D` from an index of supplier readings and
returns what it could not supply, with a proof of `∀ residual clauses, D` that the kernel
checks. A reading of a theorem is its statement with some leading binders instantiated, a
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
partial def readingPaths (unfoldOk : Name → Bool) (stmt : Expr) (path : Array Step) (depth : Nat) :
    MetaM (Array (Expr × Array Step)) := do
  let stmt ← instantiateMVars stmt
  let mut out := #[(stmt, path)]
  if depth == 0 then return out
  let stmt ← whnfR stmt
  match stmt with
  | .forallE _ d b _ =>
      let m ← mkFreshExprMVar d
      return out ++ (← readingPaths unfoldOk (b.instantiate1 m) (path.push .inst) (depth - 1))
  | _ =>
    if stmt.isAppOfArity ``And 2 then
      out := out ++ (← readingPaths unfoldOk stmt.appFn!.appArg! (path.push .left) (depth - 1))
      out := out ++ (← readingPaths unfoldOk stmt.appArg! (path.push .right) (depth - 1))
      return out
    if stmt.isAppOfArity ``Filter.Eventually 3 then
      if let .lam n α body bi := stmt.getArg! 1 then
        if body.isAppOfArity ``And 2 then
          let f := stmt.getArg! 2
          for (b, step) in [(body.appFn!.appArg!, Step.evLeft), (body.appArg!, Step.evRight)] do
            let e ← mkAppM ``Filter.Eventually #[.lam n α b bi, f]
            out := out ++ (← readingPaths unfoldOk e (path.push step) (depth - 1))
      return out
    if let .const n _ := stmt.getAppFn then
      if unfoldOk n then
        if let some u ← unfoldDefinition? stmt then
          out := out ++ (← readingPaths unfoldOk u (path.push .unfold) (depth - 1))
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

/-- A clause of a filter body: a local metavariable standing for it, its clause count, and
its proof along the filter when some supplier gives it for all large `X`. -/
structure Leaf where
  mvar : Expr
  cost : Nat
  eventual : Option Expr
  deriving Inhabited

structure RState where
  /-- root holes (residual clauses) with their clause counts -/
  holes : Array (Expr × Nat) := #[]
  leaves : Array Leaf := #[]

abbrev ResM := ReaderT Config (StateRefT RState TermElabM)

/-- The open clauses of a state: its residual clauses, and the kept clauses of the filter
body being decomposed. -/
def RState.cost (s : RState) : Nat :=
  s.holes.foldl (fun a h => a + h.2) 0 +
    s.leaves.foldl (fun a l => a + (if l.eventual.isNone then l.cost else 0)) 0

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
partial def assignProjections (ls : List Leaf) (h : Expr) : MetaM Unit := do
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
partial def clauseCount (T : Expr) (depth : Nat := 10) : ResM Nat := do
  if depth == 0 then return 1
  let T ← whnfR (← instantiateMVars T)
  match T with
  | .forallE n d b bi => withLocalDecl n bi d fun x => clauseCount (b.instantiate1 x) (depth - 1)
  | _ =>
    if T.isAppOfArity ``And 2 then
      return (← clauseCount T.appFn!.appArg! (depth - 1)) + (← clauseCount T.appArg! (depth - 1))
    if T.isAppOfArity ``Exists 2 then
      return ← withLocalDeclD `w T.appFn!.appArg! fun w =>
        clauseCount (T.appArg!.beta #[w]) (depth - 1)
    if T.isAppOfArity ``Filter.Eventually 3 || T.isAppOfArity ``Filter.Frequently 3 then
      return ← withLocalDeclD `X (T.getArg! 0) fun x =>
        clauseCount ((T.getArg! 1).beta #[x]) (depth - 1)
    if ← unfoldable T then
      if let some u ← unfoldDefinition? T then return ← clauseCount u (depth - 1)
    return 1

def mkHole (ctx : Array Expr) (T : Expr) : ResM Expr := do
  let h ← freshIn ctx T .syntheticOpaque
  let c ← clauseCount T
  modify fun s => { s with holes := s.holes.push (h, c) }
  return h

/-- Replay a reading path of `proof : stmt` in context `ctx`: its proof, statement and
obligations (data binders become root metavariables, propositions obligations). -/
partial def replay (ctx : Array Expr) (proof stmt : Expr) (obls : Array Expr) :
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

mutual

/-- A proof of `T` in context `ctx` and the number of clauses it leaves open. -/
partial def solve (ctx : Array Expr) (T : Expr) (fuel : Nat) (mode : Mode) :
    ResM (Option (Expr × Nat)) := do
  let cfg ← read
  let spent ← cfg.budgetRef.modifyGet fun n => (n + 1, n + 1)
  let fuel := if spent > cfg.callBudget then 0 else fuel
  let T ← instantiateMVars T
  -- a hypothesis in context, without fixing any witness
  for x in ctx do
    let d ← inferType x
    if ← isProp d then
      if ← withNewMCtxDepth (defEq d T) then return some (x, 0)
  -- the battery, on a goal with no metavariable and no corpus constant
  if !T.hasMVar && !(T.getUsedConstants.any fun c => cfg.unfoldPrefixes.any (·.isPrefixOf c)) then
    if let some p ← battery T then return some (p, 0)
  if fuel == 0 then return (← leave ctx T fuel mode)
  let start ← snapshot
  let base := start.st.cost
  let mut best : Option (Expr × Nat × Snapshot) := none
  -- a goal along `atTop`
  if (T.isAppOfArity ``Filter.Frequently 3 || T.isAppOfArity ``Filter.Eventually 3) &&
      isAtTop (T.getArg! 2) then
    if let .residual := mode then
      if let some p ← filterRule ctx T fuel then
        let c := (← get).cost - base
        if c == 0 then return some (p, 0)
        best := some (p, c, ← snapshot)
      start.restore
  -- readings retrieved from the index
  for ref in ← candidates T do
    start.restore
    let c0 ← mkConstWithFreshMVarLevels ref.name
    let some (proof, stmt, obls) ← replay ctx c0 (← inferType c0) #[] ref.path.toList | continue
    unless headsMatch stmt T do continue
    unless ← defEq stmt T do continue
    unless ← discharge ctx obls fuel mode do continue
    let p ← instantiateMVars proof
    let c := (← get).cost - base
    if c == 0 then return some (p, 0)
    if best.all (fun b => c < b.2.1) then best := some (p, c, ← snapshot)
  -- structure
  start.restore
  if let some p ← structural ctx T fuel mode then
    let c := (← get).cost - base
    if best.all (fun b => c < b.2.1) then best := some (p, c, ← snapshot)
  -- leave it
  start.restore
  if let some (p, _) ← leave ctx T fuel mode then
    let c := (← get).cost - base
    if best.all (fun b => c < b.2.1) then best := some (p, c, ← snapshot)
  match best with
  | some (p, c, s) =>
      s.restore
      return some (p, c)
  | none =>
      start.restore
      return none

/-- Prove a reading's obligations (instances by synthesis). -/
partial def discharge (ctx : Array Expr) (obls : Array Expr) (fuel : Nat) (mode : Mode) :
    ResM Bool := do
  for o in obls do
    if ← o.mvarId!.isAssigned then continue
    let oT ← instantiateMVars (← inferType o)
    if (← isClass? oT).isSome then
      match ← (try (some <$> synthInstance oT) catch _ => pure none) with
      | some inst => o.mvarId!.assign inst
      | none => return false
    else
      match ← solve ctx oT (fuel - 1) mode with
      | some (p, _) => o.mvarId!.assign p
      | none => return false
  return true

partial def structural (ctx : Array Expr) (T : Expr) (fuel : Nat) (mode : Mode) :
    ResM (Option Expr) := do
  match T with
  | .forallE n d b bi =>
      match mode with
      | .pointwise .. => return none
      | _ =>
        withLocalDecl n bi d fun x => do
          match ← solve (ctx.push x) (b.instantiate1 x) fuel mode with
          | some (p, _) => return some (← mkLambdaFVars #[x] p)
          | none => return none
  | _ =>
    if T.isAppOfArity ``And 2 then
      let A := T.appFn!.appArg!
      let B := T.appArg!
      -- the larger conjunct first, so that witnesses it fixes reach the side conditions
      let swapped := A.approxDepth < B.approxDepth
      let (first, second) := if swapped then (B, A) else (A, B)
      let some (p1, _) ← solve ctx first fuel mode | return none
      let some (p2, _) ← solve ctx (← instantiateMVars second) fuel mode | return none
      let (pa, pb) := if swapped then (p2, p1) else (p1, p2)
      return some (← mkAppM ``And.intro #[pa, pb])
    if T.isAppOfArity ``Exists 2 then
      let α := T.appFn!.appArg!
      let pred := T.appArg!
      let w ← freshIn ctx α
      let some (p, _) ← solve ctx (pred.beta #[w]) fuel mode | return none
      return some (← mkAppOptM ``Exists.intro #[α, pred, w, p])
    if ← unfoldable T then
      if let some T' ← unfoldDefinition? T then
        return (← solve ctx T' (fuel - 1) mode).map (·.1)
    return none

/-- An unsupplied clause: a residual clause, a named input, or a clause of a filter body
(supplied along the filter when some reading gives it for all large `X`). -/
partial def leave (ctx : Array Expr) (T : Expr) (fuel : Nat) (mode : Mode) :
    ResM (Option (Expr × Nat)) := do
  match mode with
  | .residual => return some (← mkHole ctx T, 0)
  | .eventual =>
      if T.hasFVar || T.hasMVar then return none
      return some (← mkHole ctx T, 0)
  | .pointwise x f =>
      let leafM ← mkFreshExprMVar T .syntheticOpaque
      let c ← clauseCount T
      if fuel > 0 then
        if let some e ← supplyEventually ctx.pop x f T (fuel - 1) then
          modify fun st => { st with leaves := st.leaves.push { mvar := leafM, cost := c, eventual := some e } }
          return some (leafM, 0)
      modify fun st => { st with leaves := st.leaves.push { mvar := leafM, cost := c, eventual := none } }
      return some (leafM, 0)

/-- A proof of `∀ᶠ X in f, T X`: from a reading directly, or from an eventual reading
`∀ᶠ X, R X` whose glue candidates unify with `T X`. -/
partial def supplyEventually (outer : Array Expr) (x f T : Expr) (fuel : Nat) :
    ResM (Option Expr) := do
  let s ← snapshot
  let E ← mkAppM ``Filter.Eventually #[← mkLambdaFVars #[x] T, f]
  if let some (e, _) ← solve outer E fuel .eventual then return some e
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
    unless ← discharge outer obls fuel .eventual do continue
    return some (← mkAppM ``Filter.Eventually.mono #[← instantiateMVars proof, g])
  s.restore
  return none

/-- `∃ᶠ X in atTop, Q X` or `∀ᶠ X in atTop, Q X`: decompose `Q X`, supply what some reading
gives for all large `X`, and keep the rest as one residual along the filter. -/
partial def filterRule (ctx : Array Expr) (T : Expr) (fuel : Nat) : ResM (Option Expr) := do
  let freq := T.isAppOfArity ``Filter.Frequently 3
  let α := T.getArg! 0
  let pred := T.getArg! 1
  let f := T.getArg! 2
  withLocalDeclD `X α fun x => do
    let saved := (← get).leaves
    modify fun s => { s with leaves := #[] }
    let r ← solve (ctx.push x) (pred.beta #[x]) (fuel - 1) (.pointwise x f)
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
def residualise (demand : Expr) (index : DiscrTree Ref) (glue : Array Name) (fuel : Nat := 8)
    (exclude : Array Name := #[]) (callBudget : Nat := 600) (maxCandidates : Nat := 24) :
    TermElabM (Option Expr × Nat) := do
  let budgetRef ← IO.mkRef 0
  let cfg : Config := {
    glue, unfoldPrefixes := #[`ErdosProblems, `Erdos249257, `DemandLedger]
    rootLCtx := ← getLCtx, rootInsts := ← getLocalInstances
    index, exclude, callBudget, maxCandidates, budgetRef }
  let (r, _) ← ((solve #[] demand fuel .residual).run cfg).run {}
  return (r.map (·.1), ← budgetRef.get)

/-- Close residual clauses that became closed propositions (a witness fixed later) by the
battery, abstract the rest, report them, and add `name : ∀ residual clauses, demand` after
the kernel checks it. Returns the number of propositional clauses and the suppliers used. -/
def certify (name : Name) (label : String) (proof : Expr) (isSupplier : Name → Bool) :
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
  let used := value.getUsedConstants.filter isSupplier
  let props ← forallTelescope type fun xs _ => do
    let mut n := 0
    for x in xs do
      let t ← inferType x
      if ← isProp t then n := n + 1
      logInfo m!"[{label}]  {← x.fvarId!.getUserName} : {t}"
    return n
  addDecl (.thmDecl { name, levelParams := res.paramNames.toList, type, value })
  logInfo m!"[{label}] certificate {name}: {props} propositional residual clause(s), \
    {res.numMVars - props} witness(es); suppliers used {used.toList}"
  return (props, used)

end ErdosProblems.ArgumentGraph.Residualise

/-! ## Demand-ledger sweep

The index holds the readings of every corpus theorem. For each ledger demand the consumer it
was extracted from is withheld, the search retrieves suppliers from the index, and the
certificate `∀ residual clauses, demand` is added after the kernel checks it. A supplier is
cross-consumer when the consumer's proof never mentions it. -/

open ErdosProblems.ArgumentGraph.Residualise

/-- The consumer a ledger demand was extracted from, read off its docstring
("antecedent `h` of `Thm`"). -/
def consumerOf (g : Lean.Name) : Lean.MetaM (Option Lean.Name) := do
  let some doc ← Lean.findDocString? (← Lean.getEnv) g | return none
  let parts := doc.splitOn "`"
  if parts.length ≥ 4 then return some parts[3]!.toName else return none

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← Lean.getEnv
  let corpus : Array Lean.Name := #[`ErdosProblems, `Erdos249257]
  let unfoldOk := fun (n : Lean.Name) => (corpus.push `DemandLedger).any (·.isPrefixOf n)
  let isSupplier := fun (n : Lean.Name) =>
    corpus.any (·.isPrefixOf n) && !(`ErdosProblems.ArgumentGraph.Residualise).isPrefixOf n &&
      match env.find? n with
      | some (.thmInfo _) => true
      | _ => false
  let t0 ← IO.monoMsNow
  let (index, nThm, nEntries) ← indexCorpus corpus unfoldOk
  Lean.logInfo m!"index: {nThm} theorems, {nEntries} readings, {(← IO.monoMsNow) - t0} ms"
  let glue : Array Lean.Name := #[
    `ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactor.filter_excluded_eq_pivotBadBases,
    `ErdosProblems.Erdos249.PaperCompleteR21.filter_not_mem_pivotSupplierBases]
  let mut demands : Array Lean.Name := #[]
  for modName in env.header.moduleNames, data in env.header.moduleData do
    unless (`ErdosProblems.DemandLedger).isPrefixOf modName do continue
    for n in data.constNames do
      unless (`DemandLedger).isPrefixOf n do continue
      if let some (.defnInfo d) := env.find? n then
        if d.type.isProp then demands := demands.push n
  Lean.logInfo m!"ledger demands: {demands.size}"
  let sweepStart ← IO.monoMsNow
  let mut visited := 0
  let mut progressed := 0
  let mut cross := 0
  let mut closed := 0
  for g in demands do
    if (← IO.monoMsNow) - sweepStart > 1300000 then break
    visited := visited + 1
    let consumer ← consumerOf g
    let consumerConsts : Array Lean.Name :=
      match consumer.bind env.find? with
      | some ci => (ci.value?.map (·.getUsedConstants)).getD #[]
      | none => #[]
    let t1 ← IO.monoMsNow
    let (r, calls) ← residualise (Lean.mkConst g) index glue
      (exclude := consumer.toArray) (callBudget := 250) (maxCandidates := 16)
    match r with
    | none => Lean.logInfo m!"[{g}] no residualisation ({calls} calls)"
    | some p =>
      let (props, used) ← certify (`ErdosProblems.ArgumentGraph.Residualise.cert ++ g) g.toString
        p isSupplier
      let crossUsed := used.filter fun s => !consumerConsts.contains s && some s != consumer
      Lean.logInfo m!"[{g}] consumer {consumer}; {props} clause(s); used {used.toList}; \
        cross-consumer {crossUsed.toList}; {calls} calls, {(← IO.monoMsNow) - t1} ms"
      if !used.isEmpty then progressed := progressed + 1
      if !crossUsed.isEmpty then cross := cross + 1
      if props == 0 then closed := closed + 1
  Lean.logInfo m!"sweep: {visited} of {demands.size} demands; {progressed} with a supplier used, \
    {cross} with a cross-consumer supplier, {closed} with no residual clause"
