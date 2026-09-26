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
  producer search (default 5400);
* `PLECTIS_CONTINUATION_BATTERY_HEARTBEATS` and
  `PLECTIS_CONTINUATION_BATTERY_SECONDS`: per-tactic budget (thousands) and
  wall-clock budget for the tactic battery on open leaves (defaults 40000 and
  1200);
* `PLECTIS_CONTINUATION_IDLE_SECONDS`: wall-clock budget for the idle-hypothesis
  pass (default 600);
* `PLECTIS_CONTINUATION_WORKERS`: statements searched in parallel (default 4);
* `PLECTIS_CONTINUATION_DEEP_LEAVES` and `PLECTIS_CONTINUATION_DEEP_SECONDS`:
  library search (`exact?`) on that many of the most-consumed leaves the
  battery left open, within that wall-clock budget (defaults 0, off, and 600).

After the producer search, three more passes run. Pass 3 composes each
conditional theorem whose closed hypotheses all have a residual-free producer
and has the kernel check the composed term. The idle pass finds the
proposition binders a theorem's proof never uses; dropping them leaves a
stronger statement with the same proof, and the kernel checks it (`idle`
rows). Pass 4 tries a fixed battery of
standard closing tactics (after introducing binders and unfolding the corpus
definitions the statement mentions) on every closed statement for which the
search found no producer at all, most-consumed first, and then on its
negation, and has the kernel check every proof it finds. A leaf the battery
neither closes nor refutes is reported as open, never as false.

Pass 2 also searches, for every antecedent (a hypothesis or a residual),
corpus theorems proving its negation (`refutation` rows): a refuted antecedent
makes every conditional argument that needs it vacuous.
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
  batteryHeartbeats : Nat
  batteryBudgetMs : Nat
  idleBudgetMs : Nat
  workers : Nat
  deepLeaves : Nat
  deepBudgetMs : Nat

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
    batteryHeartbeats := ← envNat "PLECTIS_CONTINUATION_BATTERY_HEARTBEATS" 40000
    batteryBudgetMs := (← envNat "PLECTIS_CONTINUATION_BATTERY_SECONDS" 1200) * 1000
    idleBudgetMs := (← envNat "PLECTIS_CONTINUATION_IDLE_SECONDS" 600) * 1000
    workers := max 1 (← envNat "PLECTIS_CONTINUATION_WORKERS" 4)
    deepLeaves := ← envNat "PLECTIS_CONTINUATION_DEEP_LEAVES" 0
    deepBudgetMs := (← envNat "PLECTIS_CONTINUATION_DEEP_SECONDS" 600) * 1000
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

/-- Theorems the elaborator generates (injectivity, `sizeOf` specifications,
equation lemmas, internal details); they are not arguments of the corpus. -/
def generatedTheorem (name : Name) : Bool :=
  name.isInternalDetail ||
    match name with
    | .str _ s => s == "inj" || s == "injEq" || s == "sizeOf_spec" || Meta.isEqnReservedNameSuffix s
    | _ => false

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

/-- A statement with its binder names, binder annotations and metadata
erased (bound variables are named by depth): two statements that differ only
in how their bound variables are named or marked implicit are one
proposition. -/
partial def normaliseBinders (e : Expr) (depth : Nat := 0) : Expr :=
  let name := Name.mkSimple s!"x{depth}"
  match e with
  | .forallE _ t b _ => .forallE name (normaliseBinders t depth) (normaliseBinders b (depth + 1)) .default
  | .lam _ t b _ => .lam name (normaliseBinders t depth) (normaliseBinders b (depth + 1)) .default
  | .letE _ t v b nondep =>
      .letE name (normaliseBinders t depth) (normaliseBinders v depth) (normaliseBinders b (depth + 1)) nondep
  | .app f a => .app (normaliseBinders f depth) (normaliseBinders a depth)
  | .mdata _ b => normaliseBinders b depth
  | .proj s i b => .proj s i (normaliseBinders b depth)
  | e => e

/-- The identity of a closed statement: a 64-bit hash of the normalised
term's full rendering (constants fully qualified, universe levels included)
followed by the 32-bit structural `Expr.hash`, so any prefix of the key is
informative. -/
def keyOf (e : Expr) : String :=
  let n := normaliseBinders e
  hex16 (hash (toString n)).toNat ++ hex16 n.hash.toNat

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

/-- `@Ne α a b` as `¬ @Eq α a b`, definitionally equal by one delta step. -/
def neAsNot (c : Expr) : Expr :=
  mkNot (mkApp3 (mkConst ``Eq c.getAppFn.constLevels!) (c.getArg! 0) (c.getArg! 1) (c.getArg! 2))

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
  -- `a ≠ b` is `¬ a = b` by one delta step; reading it so lets a proved
  -- disequation refute the equation.
  if c.isAppOfArity ``Ne 3 then
    out := out.push ("ne_as_not", neAsNot c)
  return out

def producerIndex (cfg : Config) (env : Environment) :
    Std.HashMap Name (Array Producer) := Id.run do
  let mut index : Std.HashMap Name (Array Producer) := {}
  for (name, info) in env.constants.toList do
    unless selected cfg env name && !generatedTheorem name do continue
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

/-- Whether a binder type is known to be inhabited: an instance binder's
instance synthesises, or `Nonempty T` does for a data binder. `false` means
unknown, never empty. -/
def knownInhabited (t : Expr) (isInstance : Bool) : MetaM Bool := do
  try
    if isInstance then return (← synthInstance? t).isSome
    let u ← getLevel t
    return (← synthInstance? (mkApp (mkConst ``Nonempty [u]) t)).isSome
  catch _ => return false

/-- `Nonempty T` for a closed data type `T`. -/
def mkNonempty (t : Expr) : MetaM Expr := do
  let u ← instantiateLevelMVars (← getLevel t)
  return mkApp (mkConst ``Nonempty [u]) t

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
    -- Not reducing: the index is keyed on the syntactic conclusion, and a
    -- reducing telescope would open `¬ P`, `a ≠ b` or a named ∀-proposition
    -- past the head the statement side sees.
    let (mvars, _, body) ← forallMetaTelescope (← inferType constant)
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
      | "ne_as_not" => if body.isAppOfArity ``Ne 3 then some (neAsNot body) else none
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
    -- A data argument unification left open is a witness the producer needs:
    -- the match is usable only if its type is known to be inhabited.
    for m in mvars do
      unless ← m.mvarId!.isAssigned do
        let type ← instantiateMVars (← inferType m)
        unless ← isProp type do
          unless ← knownInhabited type false do openData := true
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
  direct : Std.HashMap String (Name × String) := {}
  seen : Std.HashSet String := {}
  queue : Array (Expr × String) := #[]
  processed : Nat := 0
  matchCount : Nat := 0
  exhausted : Nat := 0
  truncated : Bool := false
  /-- Statements that are ever an antecedent (a closed hypothesis or a
  residual), whatever origin first enqueued them: each gets a refutation
  search. -/
  antecedents : Std.HashSet String := {}
  refutationSearched : Std.HashSet String := {}

def enqueue (s : State) (e : Expr) (origin : String) : State :=
  let k := keyOf e
  if s.seen.contains k then s
  else { s with seen := s.seen.insert k, queue := s.queue.push (e, origin) }

def binderRows (cfg : Config) (env : Environment) (type : Expr) :
    MetaM (Array Json × Array Expr × Json × Option Expr) := do
  forallTelescope type fun xs body => do
    let mut rows : Array Json := #[]
    -- Closed antecedents: closed proposition binders (instance binders
    -- included) and `Nonempty T` for each closed data binder whose type is
    -- not known to be inhabited.
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
      row := row ++ [("prop", toJson isPropBinder), ("type", toJson (← render t))]
      if isPropBinder then
        if closed then
          row := row ++ [("key", toJson (keyOf t))]
          closedHyps := closedHyps.push t
      else
        let inhabited ← knownInhabited t (decl.binderInfo == .instImplicit)
        row := row ++ [("inhabited", toJson inhabited)]
        if !inhabited && closed then
          let nonempty ← mkNonempty t
          row := row ++ [("nonempty_key", toJson (keyOf nonempty)),
                         ("nonempty_type", toJson (← render nonempty))]
          closedHyps := closedHyps.push nonempty
      rows := rows.push (Json.mkObj row)
    let body ← instantiateMVars body
    let bodyClosed := !body.hasFVar
    let mut conclusion : List (String × Json) := [
      ("closed", toJson bodyClosed), ("type", toJson (← render body)),
      ("head", toJson ((headName? body).map Name.toString |>.getD "")),
      ("constants", toJson (corpusConstants cfg env body))]
    if bodyClosed then conclusion := conclusion ++ [("key", toJson (keyOf body))]
    return (rows, closedHyps, Json.mkObj conclusion, if bodyClosed then some body else none)


/-- A proof of the closed statement `statement` from a residual-free
producer, rebuilt the way the search found it: introduce the statement's
binders, apply the producer with metavariables, unify, discharge its
remaining propositions from the introduced hypotheses or by instance
synthesis, and close over the binders. -/
def proveDirect (statement : Expr) (producer : Name) (reading : String) : MetaM (Option Expr) :=
  forallTelescope statement fun xs matrix => do
    let mut localHyps : Array Expr := #[]
    for x in xs do
      if ← isProp (← inferType x) then localHyps := localHyps.push x
    let constant ← mkConstWithFreshMVarLevels producer
    let (mvars, _, body) ← forallMetaTelescope (← inferType constant)
    let target? : Option Expr :=
      match reading with
      | "conclusion" => some body
      | "and_left" => if body.isAppOfArity ``And 2 then some body.appFn!.appArg! else none
      | "and_right" => if body.isAppOfArity ``And 2 then some body.appArg! else none
      | "ne_as_not" => if body.isAppOfArity ``Ne 3 then some (neAsNot body) else none
      | _ => none
    let some target := target? | return none
    unless ← isDefEq target matrix do return none
    for m in mvars do
      let id := m.mvarId!
      if ← id.isAssigned then continue
      let type ← instantiateMVars (← inferType m)
      if let some inst ← (try synthInstance? type catch _ => pure none) then
        id.assign inst
        continue
      if ← isProp type then
        let mut done := false
        for h in localHyps do
          if ← isDefEq type (← inferType h) then
            id.assign h
            done := true
            break
        unless done do return none
    let applied ← instantiateMVars (mkAppN constant mvars)
    let proof ←
      match reading with
      | "and_left" => mkAppM ``And.left #[applied]
      | "and_right" => mkAppM ``And.right #[applied]
      | _ => pure applied
    let closed ← instantiateMVars (← mkLambdaFVars xs proof)
    if closed.hasMVar then return none
    return some closed

/-- Kernel verdict on `value : type`, checked synchronously against the
current environment (so auxiliary lemmas a tactic just created are visible).
`none` means accepted. -/
def kernelVerdict (type value : Expr) (levelParams : List Name := []) : MetaM (Option String) := do
  let decl := Declaration.thmDecl
    { name := `_argument_continuation_check, levelParams, type, value }
  match Kernel.Environment.addDecl (← getEnv).toKernelEnv (← getOptions) decl with
  | .ok _ => return none
  | .error ex => return some (clip (← (ex.toMessageData (← getOptions)).toString) 400)

/-- Compose a conditional theorem with residual-free producers of each of
its closed hypotheses and ask the kernel to check the result as a new
theorem declaration (in a scratch environment). -/
def composeAndCheck (info : ConstantInfo) (direct : Std.HashMap String (Name × String)) :
    MetaM (Option Json) := do
  unless info.levelParams.isEmpty do return none
  let (mvars, _, body) ← forallMetaTelescope info.type
  let mut used : Array Json := #[]
  let mut anyHypothesis := false
  for m in mvars do
    let id := m.mvarId!
    let type ← instantiateMVars (← inferType m)
    if (← id.isAssigned) then continue
    if let some inst ← (try synthInstance? type catch _ => pure none) then
      id.assign inst
      continue
    unless ← isProp type do return none      -- a free data binder: nothing to compose
    if type.hasMVar then return none         -- a hypothesis about a data binder
    let key := keyOf type
    let some (producer, reading) := direct.get? key | return none
    let some proof ← proveDirect type producer reading | return none
    unless ← isDefEq (← inferType proof) type do return none
    id.assign proof
    anyHypothesis := true
    used := used.push (Json.mkObj [("key", toJson key), ("producer", toJson producer.toString),
                                    ("reading", toJson reading)])
  unless anyHypothesis do return none
  let value ← instantiateMVars (mkAppN (mkConst info.name) mvars)
  let type ← instantiateMVars body
  if value.hasMVar || type.hasMVar || type.hasFVar then return none
  let checked ← kernelVerdict type value
  return some <| Json.mkObj [
    ("record", "composition"), ("theorem", toJson info.name.toString),
    ("conclusion", toJson (keyOf type)), ("type", toJson (← render type)),
    ("hypotheses", Json.arr used),
    ("kernel_checked", toJson checked.isNone),
    ("kernel_error", toJson (checked.map (clip · 400) |>.getD ""))]

/-- The proposition binders of a theorem that its proof never uses. Sound in
the direction it answers: the binder's free variable occurs neither in the
proof (beta-reduced against the statement's binders), nor in a later binder
type, nor in the conclusion, so the statement without the binder has the same
proof. A proof that is not a lambda over the binders, such as a bare
constant, counts every binder as used. -/
def idleHypotheses (info : ConstantInfo) : MetaM (Array Nat) := do
  let some value := info.value? | return #[]
  forallTelescope info.type fun xs body => do
    let used := (collectFVars {} (value.beta xs)).fvarSet
    let mut idle : Array Nat := #[]
    for x in xs, i in [0:xs.size] do
      let decl ← x.fvarId!.getDecl
      if decl.binderInfo == .instImplicit then continue
      unless ← isProp decl.type do continue
      let id := x.fvarId!
      if used.contains id || body.containsFVar id then continue
      let mut later := false
      for j in [i+1:xs.size] do
        if (← xs[j]!.fvarId!.getDecl).type.containsFVar id then
          later := true
          break
      unless later do idle := idle.push i
    return idle

/-- Drop a theorem's idle binders and ask the kernel to check the stronger
statement with the same proof. -/
def strengthenAndCheck (info : ConstantInfo) (idle : Array Nat) : MetaM (Option Json) := do
  let some value := info.value? | return none
  forallTelescope info.type fun xs body => do
    let proof := value.beta xs
    let mut keep : Array Expr := #[]
    let mut dropped : Array Json := #[]
    for x in xs, i in [0:xs.size] do
      if idle.contains i then
        let t ← instantiateMVars (← x.fvarId!.getDecl).type
        let mut row : List (String × Json) := [("i", toJson i), ("type", toJson (← render t))]
        unless t.hasFVar do row := row ++ [("key", toJson (keyOf t))]
        dropped := dropped.push (Json.mkObj row)
      else
        keep := keep.push x
    let strongerType ← mkForallFVars keep body
    let strongerValue ← mkLambdaFVars keep proof
    let checked ← kernelVerdict strongerType strongerValue info.levelParams
    return some <| Json.mkObj [
      ("record", "idle"), ("theorem", toJson info.name.toString),
      ("dropped", Json.arr dropped), ("type", toJson (← render strongerType)),
      ("kernel_checked", toJson checked.isNone),
      ("kernel_error", toJson (checked.getD ""))]


/-- Corpus theorems whose conclusion unifies with `target` (after `target`'s
own binders are introduced), as `match`-shaped rows labelled `recordName` and
keyed by the subject statement `key`, each with its closed residuals. -/
def searchProducers (cfg : Config) (producers : Std.HashMap Name (Array Producer))
    (key : String) (recordName : String) (target : Expr) :
    MetaM (Array (Json × Array Expr)) :=
  forallTelescope target fun xs matrix => do
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
          ("record", "candidate_cap"), ("statement", toJson key), ("search", toJson recordName),
          ("candidates", toJson candidates.size), ("tried", toJson tried)], #[])
        break
      tried := tried + 1
      match ← tryProducer cfg xs localHyps matrix p with
      | none => pure ()
      | some outcome =>
          let mut residualRows : Array Json := #[]
          for r in outcome.residuals do
            -- A residual with a metavariable is not a statement: its
            -- rendering names an arbitrary metavariable, so it gets no key.
            residualRows := residualRows.push <| Json.mkObj <|
              (if r.hasMVar then [] else [("key", toJson (keyOf r))]) ++
              [("type", toJson (← render r)), ("has_open_data", toJson r.hasMVar)]
          rows := rows.push (Json.mkObj [
            ("record", toJson recordName), ("statement", toJson key),
            ("producer", toJson p.name.toString), ("reading", toJson p.reading),
            ("status", toJson outcome.status),
            ("open_data", toJson outcome.openData),
            ("residuals", Json.arr residualRows)],
            if outcome.openData then #[] else outcome.residuals.filter (fun r => !r.hasMVar))
    return rows

/-- `budgeted` for elaboration-level work (tactics). -/
def budgetedTerm (heartbeats : Nat) (x : Elab.TermElabM α) : Elab.TermElabM (Except String α) := do
  withCurrHeartbeats <|
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := heartbeats * 1000 }) do
      tryCatchRuntimeEx (do return .ok (← x)) fun ex =>
        if ex.isMaxHeartbeat then return .error "budget_exhausted"
        else if ex.isMaxRecDepth then return .error "runtime_limit"
        else return .error "tactic_failed"

/-- The closing tactics tried on an open leaf, each after `intros` and after
unfolding the corpus definitions the statement mentions. Scripts are parsed
against the current environment, so a tactic the environment lacks (for
example a Mathlib tactic in a core-only test) is skipped, not an error. -/
def batteryScripts (defs : Array Name)
    (tactics : List String := ["decide", "omega", "norm_num", "simp_all", "positivity", "linarith"]) :
    Elab.TermElabM (Array (String × Syntax)) := do
  let env ← getEnv
  let pre :=
    if defs.isEmpty then "intros"
    else "(intros; try unfold " ++ String.intercalate " " (defs.toList.map toString) ++ " at *)"
  let mut out := #[]
  for tac in tactics do
    match Parser.runParserCategory env `tactic s!"({pre}; {tac})" with
    | .ok stx => out := out.push (tac, stx)
    | .error _ => pure ()
  return out

/-- Try the battery on a closed statement; return the tactic that closed it
if the kernel accepts the resulting proof. -/
def tryBattery (cfg : Config) (env : Environment) (statement : Expr)
    (tactics : List String := ["decide", "omega", "norm_num", "simp_all", "positivity", "linarith"]) :
    Elab.TermElabM (Option String) := do
  let defs := (statement.getUsedConstants.filter fun c =>
      selected cfg env c && (match env.find? c with | some (.defnInfo _) => true | _ => false))
  for (label, script) in ← batteryScripts defs tactics do
    -- The kernel check runs inside the reverted block: a tactic's auxiliary
    -- lemmas exist only there.
    let attempt : Elab.TermElabM Bool := withoutModifyingState do
      let goal ← mkFreshExprMVar statement
      let remaining ← Elab.Tactic.run goal.mvarId! (Elab.Tactic.evalTactic script)
      unless remaining.isEmpty do return false
      Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let proof ← instantiateMVars goal
      if proof.hasMVar || proof.hasSyntheticSorry then return false
      return (← kernelVerdict statement proof).isNone
    let accepted := match ← budgetedTerm cfg.batteryHeartbeats attempt with
      | .ok true => true
      | _ => false
    modifyThe Core.State fun st => { st with messages := {} }
    if accepted then return some label
  return none

/-- The producer and refutation searches of one wave of statements, run in
parallel tasks. Each task gets its own copy of the elaboration state over the
shared (immutable) environment and returns closed terms only, so the results
are merged by the caller in wave order. -/
def searchWave (cfg : Config) (producers : Std.HashMap Name (Array Producer)) (budget : Nat)
    (wave : Array (Expr × Bool)) :
    MetaM (Array (Except String (Array (Json × Array Expr)) × Except String (Array (Json × Array Expr)))) := do
  let coreContext ← readThe Core.Context
  let coreState ← getThe Core.State
  let one (statement : Expr) (refute : Bool) :
      MetaM (Except String (Array (Json × Array Expr)) × Except String (Array (Json × Array Expr))) := do
    let key := keyOf statement
    let searched ← budgeted budget <| searchProducers cfg producers key "match" statement
    let refutations ← if refute then
        budgeted budget <| searchProducers cfg producers key "refutation" (mkNot statement)
      else pure (.ok #[])
    return (searched, refutations)
  let tasks ← wave.mapM fun (statement, refute) =>
    IO.asTask do
      let (result, _, _) ← (one statement refute).toIO coreContext coreState
      return result
  tasks.mapM fun task => do
    match ← IO.wait task with
    | .ok result => return result
    | .error error => return (.error s!"task_error: {error}", .ok #[])

def exportAll : Elab.TermElabM Unit := do
  let cfg ← readConfig
  let env ← getEnv
  let stream ← exportStream
  let startMs ← IO.monoMsNow
  emit stream <| Json.mkObj [
    ("record", "meta"), ("schema", "plectis-argument-continuation-export/1"),
    ("lean_version", toJson Lean.versionString),
    ("roots", toJson (cfg.roots.map Name.toString)),
    ("imports", toJson (env.imports.map (·.module.toString))),
    ("name_prefixes", toJson (cfg.namePrefixes.map Name.toString)),
    ("match_heartbeats_thousands", toJson cfg.matchHeartbeats),
    ("max_candidates", toJson cfg.maxCandidates),
    ("max_statements", toJson cfg.maxStatements),
    ("time_budget_ms", toJson cfg.timeBudgetMs)]
  let producers := producerIndex cfg env
  -- Pass 1: telescopes.
  let mut state : State := {}
  let mut theoremCount := 0
  let mut consumerCount : Std.HashMap String Nat := {}
  let mut hasProducer : Std.HashSet String := {}
  let mut names : Array Name := #[]
  for (name, info) in env.constants.toList do
    if selected cfg env name && !generatedTheorem name then
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
        for h in closedHyps do
          state := enqueue state h "hypothesis"
          state := { state with antecedents := state.antecedents.insert (keyOf h) }
          consumerCount := consumerCount.insert (keyOf h) (consumerCount.getD (keyOf h) 0 + 1)
        -- The conclusion of a conditional argument is itself a statement the
        -- graph must be able to reach and unfold.
        if let some body := closedBody then
          if !closedHyps.isEmpty then state := enqueue state body "conclusion"
          -- Both sides of a proved equivalence are statements, so every
          -- recorded equivalence reaches the disguise-class computation.
          let c := body.consumeMData
          if c.isAppOfArity ``Iff 2 then
            state := enqueue state c.appFn!.appArg! "iff_side"
            state := enqueue state c.appArg! "iff_side"
        theoremCount := theoremCount + 1
    | .error reason =>
        emit stream <| Json.mkObj [
          ("record", "theorem_error"), ("name", toJson name.toString),
          ("reason", toJson reason)]
  -- Pass 2: producer search over the closed statements, following residuals.
  -- The per-statement budget covers every candidate's own budget, so it trips
  -- only on work outside the attempts.
  let searchBudget := cfg.matchHeartbeats * (cfg.maxCandidates + 4) * 2
  let mut cursor := 0
  let mut outcomes : Array (Except String (Array (Json × Array Expr)) ×
      Except String (Array (Json × Array Expr))) := #[]
  let mut outcomeBase := 0
  while cursor < state.queue.size do
    if state.processed ≥ cfg.maxStatements then
      state := { state with truncated := true }
      break
    if (← IO.monoMsNow) - startMs > cfg.timeBudgetMs then
      state := { state with truncated := true }
      break
    -- A wave: the next statements of the queue, searched in parallel. The
    -- refutation search covers antecedents (where a refutation turns a
    -- conditional argument vacuous) known when the wave starts; the late
    -- pass below covers the rest.
    if cursor ≥ outcomeBase + outcomes.size then
      let stop := min state.queue.size (min (cursor + 2 * cfg.workers) (cursor + (cfg.maxStatements - state.processed)))
      let mut wave : Array (Expr × Bool) := #[]
      for (statement, _) in state.queue.extract cursor stop do
        let key := keyOf statement
        let refute := state.antecedents.contains key
        if refute then
          state := { state with refutationSearched := state.refutationSearched.insert key }
        wave := wave.push (statement, refute)
      outcomes ← searchWave cfg producers searchBudget wave
      outcomeBase := cursor
    let (statement, origin) := state.queue[cursor]!
    let (searched, refutations) := outcomes[cursor - outcomeBase]!
    cursor := cursor + 1
    state := { state with processed := state.processed + 1 }
    let key := keyOf statement
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
            -- Only a usable match (no undetermined data, and not the
            -- statement reducing to itself) keeps the leaf from the battery.
            if (row.getObjValAs? Bool "open_data").toOption != some true &&
                !(residuals.any fun r => keyOf r == key) then
              hasProducer := hasProducer.insert key
            let residualCount := match row.getObjVal? "residuals" with
              | .ok (.arr xs) => xs.size
              | _ => 1
            let reading := (row.getObjValAs? String "reading").toOption.getD ""
            let producer := (row.getObjValAs? String "producer").toOption.getD ""
            if residualCount == 0 && !state.direct.contains key &&
                (row.getObjValAs? Bool "open_data").toOption != some true &&
                (reading == "conclusion" || reading == "and_left" || reading == "and_right" ||
                  reading == "ne_as_not") then
              state := { state with direct := state.direct.insert key (producer.toName, reading) }
          else if (row.getObjValAs? String "record").toOption == some "match" then
            state := { state with exhausted := state.exhausted + 1 }
          for r in residuals do
            state := enqueue state r "residual"
            state := { state with antecedents := state.antecedents.insert (keyOf r) }
    | .error reason =>
        emit stream <| Json.mkObj [
          ("record", "statement_error"), ("statement", toJson key),
          ("reason", toJson reason)]
    if let .ok rows := refutations then
      for (row, residuals) in rows do
        emit stream row
        for r in residuals do
          state := enqueue state r "residual"
          state := { state with antecedents := state.antecedents.insert (keyOf r) }
  -- A statement searched before it was seen as an antecedent (for example a
  -- conclusion that is later a residual) gets its refutation search now.
  for (statement, _) in state.queue.extract 0 cursor do
    if (← IO.monoMsNow) - startMs > cfg.timeBudgetMs then
      state := { state with truncated := true }
      break
    let key := keyOf statement
    unless state.antecedents.contains key && !state.refutationSearched.contains key do continue
    state := { state with refutationSearched := state.refutationSearched.insert key }
    match ← budgeted searchBudget <| searchProducers cfg producers key "refutation" (mkNot statement) with
    | .ok rows => for (row, _) in rows do emit stream row
    | .error _ => pure ()
  let searchEnd ← IO.monoMsNow
  -- Pass 3: compose conditional theorems whose closed hypotheses all have a
  -- residual-free producer, and have the kernel check each composition.
  let mut compositions := 0
  let mut checkedCompositions := 0
  for name in names do
    if (← IO.monoMsNow) - startMs > cfg.timeBudgetMs + 1200000 then
      state := { state with truncated := true }
      break
    let some info := env.find? name | continue
    match ← budgeted 400000 (composeAndCheck info state.direct) with
    | .ok (some row) =>
        emit stream row
        compositions := compositions + 1
        if (row.getObjValAs? Bool "kernel_checked").toOption == some true then
          checkedCompositions := checkedCompositions + 1
    | _ => pure ()
  -- Idle pass: hypotheses a proof never uses. Dropping them leaves a stronger
  -- statement with the same proof, which the kernel checks.
  let idleStart ← IO.monoMsNow
  let mut idleTheorems := 0
  let mut idleChecked := 0
  let mut idleTruncated := false
  for name in names do
    if (← IO.monoMsNow) - idleStart > cfg.idleBudgetMs then
      idleTruncated := true
      break
    let some info := env.find? name | continue
    let idle := match ← budgeted 400000 (idleHypotheses info) with
      | .ok idle => idle
      | .error _ => #[]
    if idle.isEmpty then continue
    match ← budgeted 2000000 (strengthenAndCheck info idle) with
    | .ok (some row) =>
        emit stream row
        idleTheorems := idleTheorems + 1
        if (row.getObjValAs? Bool "kernel_checked").toOption == some true then
          idleChecked := idleChecked + 1
    | _ => pure ()
  -- Pass 4: the tactic battery on open leaves, most-consumed first.
  let batteryStart ← IO.monoMsNow
  let mut leaves : Array (Nat × Expr) := #[]
  for (statement, _) in state.queue.extract 0 cursor do
    let key := keyOf statement
    unless hasProducer.contains key do
      leaves := leaves.push (consumerCount.getD key 0, statement)
  leaves := leaves.qsort (fun a b => a.1 > b.1)
  let mut batteryTried := 0
  let mut batteryClosed := 0
  let mut batteryRefuted := 0
  let mut batteryDone : Std.HashSet String := {}
  for (_, statement) in leaves do
    if (← IO.monoMsNow) - batteryStart > cfg.batteryBudgetMs then break
    batteryTried := batteryTried + 1
    if let some label ← tryBattery cfg env statement then
      batteryClosed := batteryClosed + 1
      batteryDone := batteryDone.insert (keyOf statement)
      emit stream <| Json.mkObj [
        ("record", "battery"), ("statement", toJson (keyOf statement)),
        ("tactic", toJson label), ("kernel_checked", toJson true)]
    else if let some label ← tryBattery cfg env (mkNot statement) then
      batteryRefuted := batteryRefuted + 1
      batteryDone := batteryDone.insert (keyOf statement)
      emit stream <| Json.mkObj [
        ("record", "battery_refutation"), ("statement", toJson (keyOf statement)),
        ("tactic", toJson label), ("kernel_checked", toJson true)]
  -- Library search on the most-consumed leaves the battery left open: a leaf
  -- that is a single library lemma is not an open question.
  let deepStart ← IO.monoMsNow
  let mut deepTried := 0
  let mut deepClosed := 0
  for (_, statement) in (leaves.extract 0 (min leaves.size (batteryTried))) do
    if deepTried ≥ cfg.deepLeaves then break
    if (← IO.monoMsNow) - deepStart > cfg.deepBudgetMs then break
    if batteryDone.contains (keyOf statement) then continue
    deepTried := deepTried + 1
    if let some label ← tryBattery cfg env statement ["exact?"] then
      deepClosed := deepClosed + 1
      emit stream <| Json.mkObj [
        ("record", "battery"), ("statement", toJson (keyOf statement)),
        ("tactic", toJson label), ("kernel_checked", toJson true)]
  emit stream <| Json.mkObj [
    ("record", "summary"), ("theorems", toJson theoremCount),
    ("battery_leaves", toJson leaves.size),
    ("battery_tried", toJson batteryTried),
    ("battery_closed", toJson batteryClosed),
    ("battery_refuted", toJson batteryRefuted),
    ("library_search_tried", toJson deepTried),
    ("library_search_closed", toJson deepClosed),
    ("compositions", toJson compositions),
    ("kernel_checked_compositions", toJson checkedCompositions),
    ("idle_theorems", toJson idleTheorems),
    ("idle_kernel_checked", toJson idleChecked),
    ("idle_truncated", toJson idleTruncated),
    ("statements_discovered", toJson state.queue.size),
    ("statements_searched", toJson state.processed),
    ("matches", toJson state.matchCount),
    ("budget_exhausted_attempts", toJson state.exhausted),
    ("truncated", toJson state.truncated),
    ("elapsed_ms", toJson ((← IO.monoMsNow) - startMs)),
    ("search_ms", toJson (searchEnd - startMs)),
    ("composition_ms", toJson (idleStart - searchEnd)),
    ("idle_ms", toJson (batteryStart - idleStart)),
    ("battery_ms", toJson (deepStart - batteryStart)),
    ("library_search_ms", toJson ((← IO.monoMsNow) - deepStart)),
    ("producer_relation", "lower_bound_prefiltered_by_conclusion_constants")]
  stream.flush

end ArgumentContinuationExport

-- @@TEST_DECLARATIONS@@

set_option maxHeartbeats 0 in
run_cmd liftTermElabM ArgumentContinuationExport.exportAll
