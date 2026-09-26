import Erdos249257
import ErdosProblems
import Lean

/-!
# Argument-continuation export

A conditional theorem `T : ∀ ρ, H₁ → ⋯ → Hₖ → G` is an unfinished argument:
it establishes `G` once its hypotheses are supplied. This script reads every
theorem of the corpus libraries out of the elaborated environment and emits:

* `theorem` rows: the hypothesis telescope of each theorem, with each binder
  classified as data, instance or proposition, and each proposition marked
  closed (it mentions no earlier binder, so it is a standalone statement) or
  schematic;
* `match` rows: for every closed hypothesis `P`, each corpus theorem `T'`
  whose conclusion unifies with `P` after `P`'s own binders are introduced,
  together with the hypotheses `T'` leaves behind. `T'` may also supply `P`
  through one side of an `↔` or one component of an `∧`. The residual
  hypotheses are closed again over `P`'s binders and fed back into the same
  search, so chains of reductions are followed.

Unification is the kernel's own `isDefEq` with a heartbeat budget per
attempt. An exhausted budget is written as a `match` row with status
`budget_exhausted`; it is never folded into "no producer". A producer whose
conclusion mentions a constant absent from `P` is not tried, so a match that
needs delta-unfolding of such a constant can be missed: the stream is a
lower bound on the producer relation, and `summary` says so.

`scripts/build_argument_continuations.py` owns the JSON normalisation, the
source-coordinate join and the argument graph. Environment variables:

* `PLECTIS_CONTINUATION_EXPORT_FILE`: output path (JSON Lines; stdout if unset);
* `PLECTIS_CONTINUATION_ROOTS`: comma-separated module roots
  (default `Erdos249257,ErdosProblems`);
* `PLECTIS_CONTINUATION_NAME_PREFIXES`: if set, select declarations by name
  prefix instead of by module (used by the toy-corpus test);
* `PLECTIS_CONTINUATION_MATCH_HEARTBEATS`: per-attempt budget, in thousands
  (default 20000);
* `PLECTIS_CONTINUATION_MAX_CANDIDATES`: candidate producers tried per
  statement (default 96);
* `PLECTIS_CONTINUATION_MAX_STATEMENTS`: closed statements searched in total
  (default 60000);
* `PLECTIS_CONTINUATION_TIME_BUDGET_SECONDS`: wall-clock budget for the
  producer search (default 5400).
-/

open Lean Meta Elab Command

namespace ArgumentContinuationExport

structure Config where
  roots : Array Name
  namePrefixes : Array Name
  matchHeartbeats : Nat
  maxCandidates : Nat
  maxStatements : Nat
  timeBudgetMs : Nat

private def squeeze (s : String) : String :=
  String.ofList (s.toList.filter fun c => !c.isWhitespace)

private def envNat (key : String) (default : Nat) : IO Nat := do
  match ← IO.getEnv key with
  | some raw => return (squeeze raw).toNat?.getD default
  | none => return default

private def envNames (key : String) (default : Array Name) : IO (Array Name) := do
  match ← IO.getEnv key with
  | some raw =>
      let parts := (raw.splitOn ",").map squeeze |>.filter (· ≠ "")
      return parts.toArray.map String.toName
  | none => return default

def readConfig : IO Config := do
  return {
    roots := ← envNames "PLECTIS_CONTINUATION_ROOTS" #[`Erdos249257, `ErdosProblems]
    namePrefixes := ← envNames "PLECTIS_CONTINUATION_NAME_PREFIXES" #[]
    matchHeartbeats := ← envNat "PLECTIS_CONTINUATION_MATCH_HEARTBEATS" 20000
    maxCandidates := ← envNat "PLECTIS_CONTINUATION_MAX_CANDIDATES" 96
    maxStatements := ← envNat "PLECTIS_CONTINUATION_MAX_STATEMENTS" 60000
    timeBudgetMs := (← envNat "PLECTIS_CONTINUATION_TIME_BUDGET_SECONDS" 5400) * 1000
  }

def exportStream : IO IO.FS.Stream := do
  match ← IO.getEnv "PLECTIS_CONTINUATION_EXPORT_FILE" with
  | some path =>
      if path.isEmpty then
        throw <| IO.userError "PLECTIS_CONTINUATION_EXPORT_FILE must name a nonempty path"
      let handle ← IO.FS.Handle.mk path IO.FS.Mode.write
      return IO.FS.Stream.ofHandle handle
  | none => IO.getStdout

def moduleOf (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some index => env.header.moduleNames[index.toNat]?.getD .anonymous
  | none => env.mainModule

def selected (cfg : Config) (env : Environment) (name : Name) : Bool :=
  if name.isInternal then false
  else if cfg.namePrefixes.isEmpty then
    let owner := moduleOf env name
    cfg.roots.any fun root => root.isPrefixOf owner
  else
    cfg.namePrefixes.any fun p => p.isPrefixOf name

private def hex16 (n : Nat) : String :=
  let digits := Nat.toDigits 16 n
  String.ofList (List.replicate (16 - digits.length) '0' ++ digits)

/-- The identity of a closed statement. `Expr.hash` alone carries 32 bits,
so tens of thousands of statements would collide; the key pairs it with a
64-bit hash of the full term rendering (constants fully qualified, universe
levels included). -/
def keyOf (e : Expr) : String :=
  hex16 e.hash.toNat ++ hex16 (hash (toString e)).toNat

def clip (s : String) (limit : Nat := 700) : String :=
  let flat := (s.replace "\n" " ").replace "\t" " "
  if flat.length ≤ limit then flat else String.ofList (flat.toList.take limit) ++ " …"

def render (e : Expr) : MetaM String := do
  let fmt ← withOptions (fun o =>
      (o.setBool `pp.proofs false).setBool `pp.deepTerms false) <| ppExpr e
  return clip (toString fmt)

def binderInfoLabel : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strict_implicit"
  | .instImplicit => "instance_implicit"

/-- Strip leading `∀`/`let` binders syntactically; the result has loose
bound variables where the stripped binders were. -/
partial def strippedConclusion : Expr → Expr
  | .forallE _ _ body _ => strippedConclusion body
  | .letE _ _ _ body _ => strippedConclusion body
  | .mdata _ body => strippedConclusion body
  | conclusion => conclusion

def headName? (e : Expr) : Option Name :=
  match e.consumeMData.getAppFn with
  | .const name _ => some name
  | _ => none

/-- A producer: a corpus theorem, one way of reading its conclusion (the
conclusion itself, one side of an `↔`, or one conjunct), the head constant of
that reading, and the constants it mentions (the prefilter). -/
structure Producer where
  name : Name
  reading : String
  head : Name
  constants : NameSet

/-- The readings of a stripped conclusion under which it can supply a
statement. `lhs`/`rhs` of an `↔` supply their own side and leave the other
side as a residual; each conjunct of an `∧` is supplied outright. -/
def readings (conclusion : Expr) : Array (String × Expr) := Id.run do
  let c := conclusion.consumeMData
  let mut out := #[("conclusion", c)]
  if c.isAppOfArity ``Iff 2 then
    out := out.push ("iff_mpr_supplies_lhs", c.appFn!.appArg!)
    out := out.push ("iff_mp_supplies_rhs", c.appArg!)
  if c.isAppOfArity ``And 2 then
    out := out.push ("and_left", c.appFn!.appArg!)
    out := out.push ("and_right", c.appArg!)
  return out

def producerIndex (cfg : Config) (env : Environment) :
    Std.HashMap Name (Array Producer) := Id.run do
  let mut index : Std.HashMap Name (Array Producer) := {}
  for (name, info) in env.constants.toList do
    unless selected cfg env name do continue
    let .thmInfo _ := info | continue
    let conclusion := strippedConclusion info.type
    for (reading, body) in readings conclusion do
      match headName? body with
      | some head =>
          let producer : Producer :=
            { name, reading, head, constants := body.getUsedConstantsAsSet }
          index := index.insert head ((index.getD head #[]).push producer)
      | none => pure ()
  return index

/-- Corpus constants a statement mentions: the object index key. -/
def corpusConstants (cfg : Config) (env : Environment) (e : Expr) : Array String :=
  let names := e.getUsedConstants.filter (selected cfg env)
  ((names.map Name.toString).qsort (· < ·)).extract 0 48

/-- One delta step on a corpus-named proposition: `c a₁ … aₙ`, with `c` a
corpus definition, becomes its body applied to the arguments. The two terms
are definitionally equal but structurally different, so without this step a
named antecedent (for example one lifted by `hypOf%`) and the binder type it
names would be two unrelated statements. -/
def unfoldNamedProp? (cfg : Config) (env : Environment) (e : Expr) : Option Expr := do
  let e := e.consumeMData
  -- Only named propositions without arguments: the shape of a lifted
  -- antecedent or a registered target. Unfolding every predicate
  -- application would double the statements searched for little gain.
  let .const c us := e | none
  unless selected cfg env c do none
  let .defnInfo d ← env.find? c | none
  let unfolded := d.value.instantiateLevelParams d.levelParams us
  if unfolded.hasLooseBVars || unfolded == e then none else some unfolded

def emit (stream : IO.FS.Stream) (j : Json) : IO Unit :=
  stream.putStr (j.compress ++ "\n")

/-- Run `x` with its own heartbeat budget, turning an exhausted budget or any
other exception into `none` plus a reason, so one hard unification cannot
stop the export. -/
def budgeted (heartbeats : Nat) (x : MetaM α) : MetaM (Except String α) := do
  withCurrHeartbeats <|
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := heartbeats * 1000 }) do
      tryCatchRuntimeEx (do return .ok (← x)) fun ex =>
        if ex.isMaxHeartbeat then return .error "budget_exhausted"
        else if ex.isMaxRecDepth then return .error "runtime_limit"
        else return .error "elaboration_error"

structure MatchOutcome where
  status : String
  residuals : Array Expr
  openData : Bool

/-- Try to supply `matrix` (the body of a closed statement under its own
binders `xs`) from producer `p`. On success the producer's remaining
propositional hypotheses are first discharged against the local hypotheses
among `xs`, and the rest are closed over the binders they use. -/
def tryProducer (cfg : Config) (xs : Array Expr) (localHyps : Array Expr)
    (matrix : Expr) (p : Producer) : MetaM (Option MatchOutcome) := do
  let attempt : MetaM (Option MatchOutcome) := withNewMCtxDepth do
    let constant ← mkConstWithFreshMVarLevels p.name
    let (mvars, _, body) ← forallMetaTelescopeReducing (← inferType constant)
    let mut extra : Array Expr := #[]
    let target? : Option Expr :=
      match p.reading with
      | "conclusion" => some body
      | "iff_mpr_supplies_lhs" =>
          if body.isAppOfArity ``Iff 2 then some body.appFn!.appArg! else none
      | "iff_mp_supplies_rhs" =>
          if body.isAppOfArity ``Iff 2 then some body.appArg! else none
      | "and_left" =>
          if body.isAppOfArity ``And 2 then some body.appFn!.appArg! else none
      | "and_right" =>
          if body.isAppOfArity ``And 2 then some body.appArg! else none
      | _ => none
    let some target := target? | return none
    if p.reading == "iff_mpr_supplies_lhs" then extra := extra.push body.appArg!
    if p.reading == "iff_mp_supplies_rhs" then extra := extra.push body.appFn!.appArg!
    unless ← isDefEq target matrix do return none
    let mut residuals : Array Expr := #[]
    let mut openData := false
    for m in mvars do
      let id := m.mvarId!
      if ← id.isAssigned then continue
      let type ← instantiateMVars (← inferType m)
      if ← isProp type then
        -- An instance-implicit proposition (a `Fact`, `NeZero`, ...) may be
        -- synthesisable outright.
        if let some inst ← (try synthInstance? type catch _ => pure none) then
          id.assign inst
          continue
        let mut discharged := false
        for h in localHyps do
          if ← isDefEq type (← inferType h) then
            id.assign h
            discharged := true
            break
        unless discharged do residuals := residuals.push type
      else
        if let some inst ← (try synthInstance? type catch _ => pure none) then
          id.assign inst
    for e in extra do
      residuals := residuals.push (← instantiateMVars e)
    let mut closed : Array Expr := #[]
    for r in residuals do
      let r ← instantiateMVars r
      if r.hasMVar then openData := true
      let abstracted ← mkForallFVars (usedOnly := true) xs r
      closed := closed.push (← instantiateMVars abstracted)
    return some { status := "matched", residuals := closed, openData }
  match ← budgeted cfg.matchHeartbeats attempt with
  | .ok outcome => return outcome
  | .error reason =>
      if reason == "budget_exhausted" || reason == "runtime_limit" then
        return some { status := reason, residuals := #[], openData := false }
      else
        return none

structure State where
  seen : Std.HashSet String := {}
  queue : Array (Expr × String) := #[]
  processed : Nat := 0
  matchCount : Nat := 0
  exhausted : Nat := 0
  truncated : Bool := false

def enqueue (s : State) (e : Expr) (origin : String) : State :=
  let k := keyOf e
  if s.seen.contains k then s
  else { s with seen := s.seen.insert k, queue := s.queue.push (e, origin) }

def binderRows (cfg : Config) (env : Environment) (type : Expr) :
    MetaM (Array Json × Array Expr × Json × Option Expr) := do
  forallTelescope type fun xs body => do
    let mut rows : Array Json := #[]
    let mut closedHyps : Array Expr := #[]
    for x in xs, i in [0:xs.size] do
      let decl ← x.fvarId!.getDecl
      let t ← instantiateMVars decl.type
      let isPropBinder ← isProp t
      let closed := !t.hasFVar
      let kind :=
        if decl.binderInfo == .instImplicit then "instance"
        else if isPropBinder then "hypothesis" else "data"
      let mut row : List (String × Json) := [
        ("i", toJson i), ("name", toJson decl.userName.toString),
        ("info", toJson (binderInfoLabel decl.binderInfo)),
        ("kind", toJson kind), ("closed", toJson closed)]
      if isPropBinder then
        row := row ++ [("type", toJson (← render t))]
        if closed then row := row ++ [("key", toJson (keyOf t))]
      else
        row := row ++ [("type", toJson (← render t))]
      rows := rows.push (Json.mkObj row)
      if isPropBinder && closed && decl.binderInfo != .instImplicit then
        closedHyps := closedHyps.push t
    let body ← instantiateMVars body
    let bodyClosed := !body.hasFVar
    let mut conclusion : List (String × Json) := [
      ("closed", toJson bodyClosed), ("type", toJson (← render body)),
      ("head", toJson ((headName? body).map Name.toString |>.getD "")),
      ("constants", toJson (corpusConstants cfg env body))]
    if bodyClosed then conclusion := conclusion ++ [("key", toJson (keyOf body))]
    return (rows, closedHyps, Json.mkObj conclusion, if bodyClosed then some body else none)

def exportAll : MetaM Unit := do
  let cfg ← readConfig
  let env ← getEnv
  let stream ← exportStream
  let startMs ← IO.monoMsNow
  emit stream <| Json.mkObj [
    ("record", "meta"), ("schema", "plectis-argument-continuation-export/1"),
    ("lean_version", toJson Lean.versionString),
    ("roots", toJson (cfg.roots.map Name.toString)),
    ("name_prefixes", toJson (cfg.namePrefixes.map Name.toString)),
    ("match_heartbeats_thousands", toJson cfg.matchHeartbeats),
    ("max_candidates", toJson cfg.maxCandidates),
    ("max_statements", toJson cfg.maxStatements),
    ("time_budget_ms", toJson cfg.timeBudgetMs)]
  let producers := producerIndex cfg env
  -- Pass 1: telescopes.
  let mut state : State := {}
  let mut theoremCount := 0
  let mut names : Array Name := #[]
  for (name, info) in env.constants.toList do
    if selected cfg env name then
      if let .thmInfo _ := info then names := names.push name
  names := names.qsort (fun a b => a.toString < b.toString)
  for name in names do
    let some info := env.find? name | continue
    let result ← budgeted 400000 (binderRows cfg env info.type)
    match result with
    | .ok (rows, closedHyps, conclusion, closedBody) =>
        emit stream <| Json.mkObj [
          ("record", "theorem"), ("name", toJson name.toString),
          ("module", toJson (moduleOf env name).toString),
          ("binders", Json.arr rows), ("conclusion", conclusion)]
        for h in closedHyps do state := enqueue state h "hypothesis"
        -- The conclusion of a conditional argument is itself a statement the
        -- graph must be able to reach and unfold.
        if let some body := closedBody then
          if !closedHyps.isEmpty then state := enqueue state body "conclusion"
        theoremCount := theoremCount + 1
    | .error reason =>
        emit stream <| Json.mkObj [
          ("record", "theorem_error"), ("name", toJson name.toString),
          ("reason", toJson reason)]
  -- Pass 2: producer search over the closed statements, following residuals.
  let mut cursor := 0
  while cursor < state.queue.size do
    if state.processed ≥ cfg.maxStatements then
      state := { state with truncated := true }
      break
    if (← IO.monoMsNow) - startMs > cfg.timeBudgetMs then
      state := { state with truncated := true }
      break
    let (statement, origin) := state.queue[cursor]!
    cursor := cursor + 1
    state := { state with processed := state.processed + 1 }
    let key := keyOf statement
    let searched ← budgeted 2000000 <| forallTelescope statement fun xs matrix => do
      let mut localHyps : Array Expr := #[]
      for x in xs do
        if ← isProp (← inferType x) then localHyps := localHyps.push x
      let mut rows : Array (Json × Array Expr) := #[]
      let some head := headName? matrix | return rows
      let used := matrix.getUsedConstantsAsSet
      let candidates := (producers.getD head #[]).filter fun p =>
        p.constants.toList.all fun c => used.contains c
      let mut tried := 0
      for p in candidates do
        if tried ≥ cfg.maxCandidates then
          rows := rows.push (Json.mkObj [
            ("record", "candidate_cap"), ("statement", toJson key),
            ("candidates", toJson candidates.size),
            ("tried", toJson tried)], #[])
          break
        tried := tried + 1
        match ← tryProducer cfg xs localHyps matrix p with
        | none => pure ()
        | some outcome =>
            let mut residualRows : Array Json := #[]
            for r in outcome.residuals do
              residualRows := residualRows.push <| Json.mkObj [
                ("key", toJson (keyOf r)), ("type", toJson (← render r)),
                ("has_open_data", toJson r.hasMVar)]
            rows := rows.push (Json.mkObj [
              ("record", "match"), ("statement", toJson key),
              ("producer", toJson p.name.toString), ("reading", toJson p.reading),
              ("status", toJson outcome.status),
              ("open_data", toJson outcome.openData),
              ("residuals", Json.arr residualRows)],
              outcome.residuals.filter (fun r => !r.hasMVar))
      return rows
    emit stream <| Json.mkObj [
      ("record", "statement"), ("key", toJson key), ("origin", toJson origin),
      ("type", toJson (← render statement)),
      ("constants", toJson (corpusConstants cfg env statement))]
    if let some unfolded := unfoldNamedProp? cfg env statement then
      emit stream <| Json.mkObj [
        ("record", "unfold"), ("statement", toJson key),
        ("unfolded", toJson (keyOf unfolded)), ("type", toJson (← render unfolded)),
        ("constants", toJson (corpusConstants cfg env unfolded))]
      state := enqueue state unfolded "unfolding"
    match searched with
    | .ok rows =>
        for (row, residuals) in rows do
          emit stream row
          if (row.getObjValAs? String "status").toOption == some "matched" then
            state := { state with matchCount := state.matchCount + 1 }
          else if (row.getObjValAs? String "record").toOption == some "match" then
            state := { state with exhausted := state.exhausted + 1 }
          for r in residuals do state := enqueue state r "residual"
    | .error reason =>
        emit stream <| Json.mkObj [
          ("record", "statement_error"), ("statement", toJson key),
          ("reason", toJson reason)]
  emit stream <| Json.mkObj [
    ("record", "summary"), ("theorems", toJson theoremCount),
    ("statements_discovered", toJson state.queue.size),
    ("statements_searched", toJson state.processed),
    ("matches", toJson state.matchCount),
    ("budget_exhausted_attempts", toJson state.exhausted),
    ("truncated", toJson state.truncated),
    ("elapsed_ms", toJson ((← IO.monoMsNow) - startMs)),
    ("producer_relation", "lower_bound_prefiltered_by_conclusion_constants")]
  stream.flush

end ArgumentContinuationExport

-- @@TEST_DECLARATIONS@@

set_option maxHeartbeats 0 in
run_cmd liftTermElabM ArgumentContinuationExport.exportAll
