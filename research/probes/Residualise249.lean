import ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactorEstimate
import ErdosProblems.Erdos249.TypeBReturnV8.PeripheralFiniteBridge

/-!
# Residualisation probe

`residualise D suppliers` searches for a proof of the demand `D` from the given supplier
theorems and returns the clauses it could not supply, together with a proof of
`∀ residual clauses, D` that the kernel checks. Witnesses are metavariables of the root
context applied to the local variables, so a supplier that fixes one (a depth function,
an exponent) fixes it in every clause that shares it. A goal `∃ᶠ X in atTop, Q X` or
`∀ᶠ X in atTop, Q X` is split pointwise: each clause of `Q X` that some supplier gives for
all large `X` is supplied along the filter, and the others stay together as one residual
`∃ᶠ X, …` (or `∀ᶠ X, …`).

The control below is the oracle-premise arm for Erdős #249: the suppliers are the three
theorems the hand-written composition `dtw_of_fiberMean_and_centered` used, plus the two
bridge lemmas and two equation lemmas; that composition itself is withheld.
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

/-- Rules the search applies like suppliers. -/
def adapters : Array Name :=
  #[``forall_exists₂_max_le_of_frequently, ``forall_exists_max_le_of_frequently,
    ``forall_exists_le_of_frequently]

/-! ## Budgets -/

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

/-! ## Tactics for closed goals and for glue -/

def closingTactics : List String :=
  ["norm_num", "positivity", "decide", "simp", "linarith", "omega"]

/-- A proof of `goalType` in the current context by the tactic `tac`, or `none` (and no
change of state). -/
def runTac (goalType : Expr) (tac : String) : TermElabM (Option Expr) := do
  let env ← getEnv
  let .ok stx := Parser.runParserCategory env `tactic tac | return none
  let s ← Term.saveState
  let r ← budgetedTerm 4000 do
    let goal ← mkFreshExprMVar goalType .syntheticOpaque
    let remaining ← Tactic.run goal.mvarId! (Tactic.evalTactic stx)
    unless remaining.isEmpty do return none
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars goal
    if proof.hasSorry then return none
    return some proof
  match r with
  | some (some p) => return some p
  | _ => s.restore; return none

def battery (goalType : Expr) : TermElabM (Option Expr) := do
  for tac in closingTactics do
    if let some p ← runTac goalType tac then return some p
  return none

/-- Closing tactics for a clause `T X` from an eventual reading `hR : R X`: `R X` itself or
its non-strict form, possibly after rewriting with an equation lemma of `glue`. -/
def glueTactics (glue : Array Name) : List String :=
  ["exact hR", "exact hR.le", "linarith [hR]"] ++
  glue.toList.flatMap fun g =>
    [s!"(rw [← {g}]; exact hR.le)", s!"(rw [← {g}]; exact hR)",
     s!"(rw [{g}] at hR; exact hR.le)", s!"(rw [{g}] at hR; exact hR)"]

/-! ## Search state -/

structure Config where
  suppliers : Array Name
  glue : Array Name
  unfoldPrefixes : Array Name
  rootLCtx : LocalContext
  rootInsts : LocalInstances

/-- A clause of a filter body: a local metavariable standing for it, and its proof along
the filter when some supplier gives it for all large `X`. -/
structure Leaf where
  mvar : Expr
  eventual : Option Expr
  deriving Inhabited

structure RState where
  holes : Array Expr := #[]
  leaves : Array Leaf := #[]
  calls : Nat := 0

abbrev ResM := ReaderT Config (StateRefT RState TermElabM)

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

def mkHole (ctx : Array Expr) (T : Expr) : ResM Expr := do
  let h ← freshIn ctx T .syntheticOpaque
  modify fun s => { s with holes := s.holes.push h }
  return h

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

/-- The ways to read a supplier's proof `proof : stmt`: the statement itself, its binders
instantiated (data by root metavariables, propositions by obligations), its conjuncts,
the unfolding of a corpus definition, and the conjuncts of an eventual conjunction. -/
partial def readings (ctx : Array Expr) (proof stmt : Expr) (obls : Array Expr) (depth : Nat) :
    ResM (Array (Expr × Expr × Array Expr)) := do
  let stmt ← instantiateMVars stmt
  let mut out := #[(proof, stmt, obls)]
  if depth == 0 then return out
  let stmt ← whnfR stmt
  match stmt with
  | .forallE _ d b bi =>
      if bi.isInstImplicit then
        let m ← mkFreshExprMVar d
        out := out ++ (← readings ctx (mkApp proof m) (b.instantiate1 m) (obls.push m) (depth - 1))
      else if ← isProp d then
        let m ← mkFreshExprMVar d .syntheticOpaque
        out := out ++ (← readings ctx (mkApp proof m) (b.instantiate1 m) (obls.push m) (depth - 1))
      else
        let m ← freshIn ctx d
        out := out ++ (← readings ctx (mkApp proof m) (b.instantiate1 m) obls (depth - 1))
      return out
  | _ =>
    if stmt.isAppOfArity ``And 2 then
      let l ← mkAppM ``And.left #[proof]
      let r ← mkAppM ``And.right #[proof]
      out := out ++ (← readings ctx l stmt.appFn!.appArg! obls (depth - 1))
      out := out ++ (← readings ctx r stmt.appArg! obls (depth - 1))
      return out
    if stmt.isAppOfArity ``Filter.Eventually 3 then
      let α := stmt.getArg! 0
      let pred := stmt.getArg! 1
      let parts ← withLocalDeclD `x α fun x => do
        let body ← whnfR (pred.beta #[x])
        unless body.isAppOfArity ``And 2 do return #[]
        let mut res := #[]
        for proj in [``And.left, ``And.right] do
          let g ← withLocalDeclD `h body fun h => do mkLambdaFVars #[x, h] (← mkAppM proj #[h])
          res := res.push (← mkAppM ``Filter.Eventually.mono #[proof, g])
        return res
      for p in parts do
        out := out ++ (← readings ctx p (← inferType p) obls (depth - 1))
      return out
    if ← unfoldable stmt then
      if let some u ← unfoldDefinition? stmt then
        out := out ++ (← readings ctx proof u obls (depth - 1))
    return out

mutual

/-- A proof of `T` in context `ctx` and the number of residual clauses it leaves. -/
partial def solve (ctx : Array Expr) (T : Expr) (fuel : Nat) (mode : Mode) :
    ResM (Option (Expr × Nat)) := do
  modify fun s => { s with calls := s.calls + 1 }
  let T ← instantiateMVars T
  for x in ctx do
    let d ← inferType x
    if ← isProp d then
      if ← defEq d T then return some (x, 0)
  -- the battery, on a goal with no metavariable and no corpus constant (arithmetic side
  -- conditions such as `0 < 1 / 1000`)
  let corpus := (← read).unfoldPrefixes
  if !T.hasMVar && !(T.getUsedConstants.any fun c => corpus.any (·.isPrefixOf c)) then
    if let some p ← battery T then return some (p, 0)
  if fuel == 0 then return (← leave ctx T fuel mode)
  let start ← snapshot
  let mut best : Option (Expr × Nat × Snapshot) := none
  -- a goal along `atTop`
  if (T.isAppOfArity ``Filter.Frequently 3 || T.isAppOfArity ``Filter.Eventually 3) &&
      isAtTop (T.getArg! 2) then
    match mode with
    | .residual =>
        if let some (p, c) ← filterRule ctx T fuel then
          if c == 0 then return some (p, 0)
          best := some (p, c, ← snapshot)
        start.restore
    | _ => pure ()
  -- suppliers and adapters
  for s in (← read).suppliers ++ adapters do
    start.restore
    let c0 ← mkConstWithFreshMVarLevels s
    let cands ← readings ctx c0 (← inferType c0) #[] 14
    let enumState ← snapshot
    for (proof, stmt, obls) in cands do
      enumState.restore
      unless headsMatch stmt T do continue
      unless ← defEq stmt T do continue
      let before := (← get).holes.size
      match ← discharge ctx obls fuel mode with
      | some c =>
          let p ← instantiateMVars proof
          let cost := c + ((← get).holes.size - before)
          if cost == 0 && c == 0 then return some (p, 0)
          if best.all (fun b => cost < b.2.1) then best := some (p, cost, ← snapshot)
      | none => pure ()
  -- structure
  start.restore
  if let some (p, c) ← structural ctx T fuel mode then
    if best.all (fun b => c < b.2.1) then best := some (p, c, ← snapshot)
  -- leave it
  start.restore
  if let some (p, c) ← leave ctx T fuel mode then
    if best.all (fun b => c < b.2.1) then best := some (p, c, ← snapshot)
  match best with
  | some (p, c, s) =>
      s.restore
      return some (p, c)
  | none =>
      start.restore
      return none

/-- Prove a supplier's obligations; the total residual cost, or `none`. -/
partial def discharge (ctx : Array Expr) (obls : Array Expr) (fuel : Nat) (mode : Mode) :
    ResM (Option Nat) := do
  let mut cost := 0
  for o in obls do
    if ← o.mvarId!.isAssigned then continue
    let oT ← instantiateMVars (← inferType o)
    if (← isClass? oT).isSome then
      match ← (try (some <$> synthInstance oT) catch _ => pure none) with
      | some inst => o.mvarId!.assign inst
      | none => return none
    else
      match ← solve ctx oT (fuel - 1) mode with
      | some (p, c) =>
          o.mvarId!.assign p
          cost := cost + c
      | none => return none
  return some cost

partial def structural (ctx : Array Expr) (T : Expr) (fuel : Nat) (mode : Mode) :
    ResM (Option (Expr × Nat)) := do
  match T with
  | .forallE n d b bi =>
      match mode with
      | .pointwise .. => return none
      | _ =>
        withLocalDecl n bi d fun x => do
          match ← solve (ctx.push x) (b.instantiate1 x) fuel mode with
          | some (p, c) => return some (← mkLambdaFVars #[x] p, c)
          | none => return none
  | _ =>
    if T.isAppOfArity ``And 2 then
      let A := T.appFn!.appArg!
      let B := T.appArg!
      let swapped := A.approxDepth < B.approxDepth
      let (first, second) := if swapped then (B, A) else (A, B)
      let some (p1, c1) ← solve ctx first fuel mode | return none
      let some (p2, c2) ← solve ctx (← instantiateMVars second) fuel mode | return none
      let (pa, pb) := if swapped then (p2, p1) else (p1, p2)
      return some (← mkAppM ``And.intro #[pa, pb], c1 + c2)
    if T.isAppOfArity ``Exists 2 then
      let α := T.appFn!.appArg!
      let pred := T.appArg!
      let w ← freshIn ctx α
      let some (p, c) ← solve ctx (pred.beta #[w]) fuel mode | return none
      return some (← mkAppOptM ``Exists.intro #[α, pred, w, p], c)
    if ← unfoldable T then
      if let some T' ← unfoldDefinition? T then
        return (← solve ctx T' (fuel - 1) mode)
    return none

/-- An unsupplied clause: a residual clause, a named input, or a clause of a filter body
(supplied along the filter when some supplier gives it for all large `X`). -/
partial def leave (ctx : Array Expr) (T : Expr) (fuel : Nat) (mode : Mode) :
    ResM (Option (Expr × Nat)) := do
  match mode with
  | .residual => return some (← mkHole ctx T, 1)
  | .eventual =>
      if T.hasFVar || T.hasMVar then return none
      return some (← mkHole ctx T, 1)
  | .pointwise x f =>
      let before := (← get).holes.size
      let leafM ← mkFreshExprMVar T .syntheticOpaque
      if fuel > 0 then
        if let some e ← supplyEventually ctx.pop x f T (fuel - 1) then
          modify fun st => { st with leaves := st.leaves.push { mvar := leafM, eventual := some e } }
          return some (leafM, (← get).holes.size - before)
      modify fun st => { st with leaves := st.leaves.push { mvar := leafM, eventual := none } }
      return some (leafM, 1)

/-- A proof of `∀ᶠ X in f, T X`: from a supplier directly, or from an eventual reading
`∀ᶠ X, R X` and a closing tactic from `R X` to `T X`. -/
partial def supplyEventually (outer : Array Expr) (x f T : Expr) (fuel : Nat) :
    ResM (Option Expr) := do
  let s ← snapshot
  let E ← mkAppM ``Filter.Eventually #[← mkLambdaFVars #[x] T, f]
  if let some (e, _) ← solve outer E fuel .eventual then return some e
  s.restore
  for sName in (← read).suppliers do
    s.restore
    let c0 ← mkConstWithFreshMVarLevels sName
    let cands ← readings outer c0 (← inferType c0) #[] 14
    let enumState ← snapshot
    for (proof, stmt, obls) in cands do
      enumState.restore
      unless stmt.isAppOfArity ``Filter.Eventually 3 do continue
      let R := (stmt.getArg! 1).beta #[x]
      let found ← withLocalDeclD `hR R fun hR => do
        for tac in glueTactics (← read).glue do
          if let some g ← runTac T tac then
            return some (← mkLambdaFVars #[x, hR] g)
        return none
      let some g := found | continue
      let some _ ← discharge outer obls fuel .eventual | continue
      return some (← mkAppM ``Filter.Eventually.mono #[← instantiateMVars proof, g])
  s.restore
  return none

/-- `∃ᶠ X in atTop, Q X` or `∀ᶠ X in atTop, Q X`: decompose `Q X`; supply what some supplier
gives for all large `X`; keep the rest as one residual along the filter. -/
partial def filterRule (ctx : Array Expr) (T : Expr) (fuel : Nat) :
    ResM (Option (Expr × Nat)) := do
  let freq := T.isAppOfArity ``Filter.Frequently 3
  let α := T.getArg! 0
  let pred := T.getArg! 1
  let f := T.getArg! 2
  let before := (← get).holes.size
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
    -- `∀ᶠ X, S X`
    let mut eS ← mkAppM ``Filter.eventually_true #[f]
    if !sup.isEmpty then
      eS := (sup.back!.eventual.getD eS)
      for l in (sup.pop).reverse do
        eS ← mkAppM ``Filter.Eventually.and #[l.eventual.getD eS, eS]
    -- `∀ X, K X ∧ S X → Q X`
    let glue ← withLocalDeclD `hKS (mkApp2 (mkConst ``And) K S) fun hKS => do
      assignProjections kept.toList (← mkAppM ``And.left #[hKS])
      assignProjections sup.toList (← mkAppM ``And.right #[hKS])
      mkLambdaFVars #[x, hKS] (← instantiateMVars q)
    let predK ← mkLambdaFVars #[x] K
    let proof ←
      if freq then
        let comb ←
          if kept.isEmpty then
            mkAppM ``Filter.Eventually.frequently
              #[← mkAppM ``Filter.Eventually.and #[← mkAppM ``Filter.eventually_true #[f], eS]]
          else
            let hole ← mkHole ctx (← mkAppM ``Filter.Frequently #[predK, f])
            mkAppM ``Filter.Frequently.and_eventually #[hole, eS]
        mkAppM ``Filter.Frequently.mono #[comb, glue]
      else
        let hK ←
          if kept.isEmpty then mkAppM ``Filter.eventually_true #[f]
          else mkHole ctx (← mkAppM ``Filter.Eventually #[predK, f])
        mkAppM ``Filter.Eventually.mono #[← mkAppM ``Filter.Eventually.and #[hK, eS], glue]
    return some (proof, (← get).holes.size - before)

end

/-- Residualise `demand` against `suppliers`: the proof term with its holes, and the number
of search calls. -/
def residualise (demand : Expr) (suppliers glue : Array Name) (fuel : Nat := 8) :
    TermElabM (Option Expr × Nat) := do
  let cfg : Config := {
    suppliers, glue, unfoldPrefixes := #[`ErdosProblems, `Erdos249257]
    rootLCtx := ← getLCtx, rootInsts := ← getLocalInstances }
  let (r, st) ← ((solve #[] demand fuel .residual).run cfg).run {}
  return (r.map (·.1), st.calls)

/-- Close the residual clauses that became closed propositions (a witness fixed later) by
the battery, abstract the rest, report them, and add `name : ∀ residual clauses, demand`
after the kernel checks it. -/
def certify (name : Name) (demand proof : Expr) : TermElabM Unit := do
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
  logInfo m!"residual of {demand}: {res.numMVars} clause(s)"
  forallTelescope type fun xs _ => do
    for x in xs do
      logInfo m!"  {← x.fvarId!.getUserName} : {← inferType x}"
  addDecl (.thmDecl { name, levelParams := res.paramNames.toList, type, value })
  logInfo m!"certificate {name} added"

end ErdosProblems.ArgumentGraph.Residualise

/-! ## Oracle-premise control: Erdős #249, first-harmonic route -/

open ErdosProblems.ArgumentGraph.Residualise
open Erdos249257.TotientTailPeriodKiller ErdosProblems.Erdos249.PaperCompleteR21
  ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactor in
run_cmd Lean.Elab.Command.liftTermElabM do
  let demand := Lean.mkConst ``DTWPivotResidualDecorrelation
  let suppliers := #[``prop_dickman, ``excluded_budget_one_thousandth_of_chebyshev,
    ``pivotBudgetAt_of_peripheral_estimates]
  let glue := #[``filter_excluded_eq_pivotBadBases, ``filter_not_mem_pivotSupplierBases]
  let (r, calls) ← residualise demand suppliers glue
  Lean.logInfo m!"search calls: {calls}"
  match r with
  | some proof => certify `ErdosProblems.ArgumentGraph.Residualise.dtw_residual_cert demand proof
  | none => Lean.logError "no residualisation found"

#print axioms ErdosProblems.ArgumentGraph.Residualise.dtw_residual_cert
