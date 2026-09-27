import ErdosProblems.Erdos251.PaperCompleteR21.JointPrimeGapCountermodel
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
* `PLECTIS_CONTINUATION_WEAKEN_SECONDS`: wall-clock budget for the
  used-consequence pass (default 600);
* `PLECTIS_CONTINUATION_WORKERS`: statements searched in parallel (default 4);
* `PLECTIS_CONTINUATION_DEEP_LEAVES` and `PLECTIS_CONTINUATION_DEEP_SECONDS`:
  library search (`exact?`) on that many of the most-consumed leaves the
  battery left open, within that wall-clock budget (defaults 0, off, and 600);
* `PLECTIS_CONTINUATION_GROUND_SECONDS`, `..._GROUND_HEARTBEATS` and
  `..._GROUND_MAX_SIZE`: wall-clock budget, per-tactic budget (thousands) and
  largest statement (tree nodes) of the ground tier (defaults 240, 2000, 400;
  0 seconds turns it off);
* `PLECTIS_CONTINUATION_KERNEL_HEARTBEATS`: bound (thousands) on each kernel
  check made by the ground tier, the scope-aware used consequences, the
  literal generalisation and the counterexample search (default 200000);
* optional passes, all off by default: `PLECTIS_CONTINUATION_USED_V2=1`
  (scope-aware used consequences), `PLECTIS_CONTINUATION_GENERALISE_SECONDS`
  (literal generalisation; `..._GENERALISE_HEARTBEATS`, default 200000, per
  literal), `PLECTIS_CONTINUATION_NAT_REFUTE_SECONDS` (bounded counterexamples
  for leading-ℕ universals), `PLECTIS_CONTINUATION_LIBRARY_PRODUCERS=1`
  (every theorem of the environment is a producer),
  `PLECTIS_CONTINUATION_RELAXED_PREFILTER=1` (no conclusion-constant
  prefilter; producers sharing the most constants go first over the cap),
  `PLECTIS_CONTINUATION_UNFOLD_PREDICATES=1` (one delta step on applied corpus
  predicates too), `PLECTIS_CONTINUATION_FOCUS_DECLARATIONS` (telescopes of
  these declarations only; producers unchanged) and
  `PLECTIS_CONTINUATION_EXTRA_TACTICS` (extra battery tactics separated by
  `;;`, or `,`; `native_decide`, `sorry` and `admit` are dropped).

After the producer search, four more passes run. Pass 3 composes each
conditional theorem whose closed hypotheses all have a residual-free producer
and has the kernel check the composed term. The idle pass finds the
proposition binders a theorem's proof never uses; dropping them leaves a
stronger statement with the same proof, and the kernel checks it (`idle`
rows). The ground tier (below, before the battery) settles small ground
statements and exhibits inhabitants of `Nonempty T`. Pass 4 tries a fixed
battery of standard closing tactics (after introducing binders and unfolding
the corpus definitions the statement mentions) on every searched statement
without a residual-free producer, most-consumed first, and then on its
negation, and has the kernel check every proof it finds. A leaf the battery
neither closes nor refutes is reported as open, never as false.

Pass 2 also searches, for every antecedent (a hypothesis or a residual),
corpus theorems proving its negation (`refutation` rows): a refuted antecedent
makes every conditional argument that needs it vacuous.

Between the telescopes and the search, the used-consequence pass asks, for
each closed hypothesis of each theorem (most-consumed first), what the proof
derives from it. When the proof uses `h : H` only through use sites such as
`L h`, `h.1` or `h 3`, the theorem with `h` replaced by the propositions those
sites prove is added to the environment (the kernel checks it on the way in)
and becomes a producer like any other theorem; each consequence `C` is a new
statement, searched, refuted and tried by the battery like the rest, and the
kernel checks `H → C` for each (`weakening` rows).
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
  weakenBudgetMs : Nat
  workers : Nat
  deepLeaves : Nat
  deepBudgetMs : Nat
  usedConsequencesV2 : Bool
  libraryProducers : Bool
  relaxedProducerFilter : Bool
  unfoldPredicates : Bool
  focusDeclarations : Array Name
  extraTactics : List String
  natRefuteBudgetMs : Nat
  groundBudgetMs : Nat
  groundHeartbeats : Nat
  groundMaxSize : Nat
  generaliseBudgetMs : Nat
  generaliseHeartbeats : Nat
  kernelHeartbeats : Nat

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

/-- Extra battery tactics, separated by `;;` (or by `,` when no `;;` is
present). A tactic that could hand the kernel an unchecked certificate
(`native_decide`, `+native`, `sorry`, `admit`) is dropped: the battery's
verdicts are kernel checks, and those tactics would make them trust the
compiler or nothing. -/
def extraTacticList (raw : String) : List String :=
  let parts := if (raw.splitOn ";;").length > 1 then raw.splitOn ";;" else raw.splitOn ","
  let banned := ["native", "sorry", "admit", "ofReduceBool", "trustCompiler"]
  parts.filterMap fun part =>
    let t := String.ofList (part.toList.dropWhile Char.isWhitespace |>.reverse.dropWhile Char.isWhitespace |>.reverse)
    if t.isEmpty || banned.any (fun b => (t.splitOn b).length > 1) then none else some t

def readConfig : IO Config := do
  return {
    roots := ← envNames "PLECTIS_CONTINUATION_ROOTS" #[`Erdos249257, `ErdosProblems]
    namePrefixes := ← envNames "PLECTIS_CONTINUATION_NAME_PREFIXES" #[`ErdosProblems.Erdos251.PaperCompleteR21.long_joint_prime_gap_countermodel, `ErdosProblems.Erdos251.PaperCompleteR21.short_joint_prime_gap_countermodel, `ErdosProblems.Erdos251.PaperCompleteR21.cut_prefix_bound, `ErdosProblems.Erdos251.prime_polylogarithmic_interval]
    matchHeartbeats := ← envNat "PLECTIS_CONTINUATION_MATCH_HEARTBEATS" 20000
    maxCandidates := ← envNat "PLECTIS_CONTINUATION_MAX_CANDIDATES" 96
    maxStatements := ← envNat "PLECTIS_CONTINUATION_MAX_STATEMENTS" 60000
    timeBudgetMs := (← envNat "PLECTIS_CONTINUATION_TIME_BUDGET_SECONDS" 300) * 1000
    batteryHeartbeats := ← envNat "PLECTIS_CONTINUATION_BATTERY_HEARTBEATS" 40000
    batteryBudgetMs := (← envNat "PLECTIS_CONTINUATION_BATTERY_SECONDS" 60) * 1000
    idleBudgetMs := (← envNat "PLECTIS_CONTINUATION_IDLE_SECONDS" 30) * 1000
    weakenBudgetMs := (← envNat "PLECTIS_CONTINUATION_WEAKEN_SECONDS" 240) * 1000
    workers := max 1 (← envNat "PLECTIS_CONTINUATION_WORKERS" 2)
    deepLeaves := ← envNat "PLECTIS_CONTINUATION_DEEP_LEAVES" 0
    deepBudgetMs := (← envNat "PLECTIS_CONTINUATION_DEEP_SECONDS" 600) * 1000
    usedConsequencesV2 := (← envNat "PLECTIS_CONTINUATION_USED_V2" 1) != 0
    libraryProducers := (← envNat "PLECTIS_CONTINUATION_LIBRARY_PRODUCERS" 0) != 0
    relaxedProducerFilter := (← envNat "PLECTIS_CONTINUATION_RELAXED_PREFILTER" 0) != 0
    unfoldPredicates := (← envNat "PLECTIS_CONTINUATION_UNFOLD_PREDICATES" 0) != 0
    focusDeclarations := ← envNames "PLECTIS_CONTINUATION_FOCUS_DECLARATIONS" #[]
    natRefuteBudgetMs := (← envNat "PLECTIS_CONTINUATION_NAT_REFUTE_SECONDS" 30) * 1000
    extraTactics := extraTacticList ((← IO.getEnv "PLECTIS_CONTINUATION_EXTRA_TACTICS").getD "")
    groundBudgetMs := (← envNat "PLECTIS_CONTINUATION_GROUND_SECONDS" 120) * 1000
    groundHeartbeats := ← envNat "PLECTIS_CONTINUATION_GROUND_HEARTBEATS" 2000
    groundMaxSize := ← envNat "PLECTIS_CONTINUATION_GROUND_MAX_SIZE" 400
    generaliseBudgetMs := (← envNat "PLECTIS_CONTINUATION_GENERALISE_SECONDS" 300) * 1000
    generaliseHeartbeats := ← envNat "PLECTIS_CONTINUATION_GENERALISE_HEARTBEATS" 200000
    kernelHeartbeats := ← envNat "PLECTIS_CONTINUATION_KERNEL_HEARTBEATS" 200000
  }

def exportStream : IO IO.FS.Stream := do
  match ← IO.getEnv "PLECTIS_CONTINUATION_EXPORT_FILE" with
  | some path =>
      if path.isEmpty then
        throw <| IO.userError "PLECTIS_CONTINUATION_EXPORT_FILE must name a nonempty path"
      let handle ← IO.FS.Handle.mk path IO.FS.Mode.write
      return IO.FS.Stream.ofHandle handle
  | none =>
      -- Probe copy: the full export beside the verdicts the workflow uploads.
      match ← IO.getEnv "RUNNER_TEMP" with
      | some dir =>
          let handle ← IO.FS.Handle.mk (dir ++ "/kernel-probe/InterfacesJointPrimeGap.export.jsonl") IO.FS.Mode.write
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

/-- A proof term as a reader would want to see a use site: `L h`, `h.2`. -/
def renderProof (e : Expr) : MetaM String := do
  let fmt ← withOptions (fun o =>
      (o.setBool `pp.proofs true).setBool `pp.deepTerms false) <| ppExpr e
  return clip (toString fmt) 300

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

def producerIndex (cfg : Config) (env : Environment) (extra : Array Name := #[]) :
    Std.HashMap Name (Array Producer) := Id.run do
  let mut index : Std.HashMap Name (Array Producer) := {}
  let mut theorems : Array (Name × ConstantInfo) := #[]
  for (name, info) in env.constants.toList do
    if (selected cfg env name || cfg.libraryProducers) && !name.isInternal && !generatedTheorem name then
      theorems := theorems.push (name, info)
  -- Theorems this export derived (weakened hypotheses) are producers too.
  for name in extra do
    if let some info := env.find? name then theorems := theorems.push (name, info)
  theorems := theorems.qsort (fun a b => a.1.toString < b.1.toString)
  for (name, info) in theorems do
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
  unless cfg.unfoldPredicates || e.isConst do none
  let .const c us := e.getAppFn | none
  unless selected cfg env c do none
  let .defnInfo d ← env.find? c | none
  let unfolded := (d.value.instantiateLevelParams d.levelParams us).beta e.getAppArgs
  if unfolded.hasLooseBVars || unfolded == e then none else some unfolded

def emit (stream : IO.FS.Stream) (j : Json) : IO Unit := do
  stream.putStr (j.compress ++ "\n")
  -- Probe copy: compact lines for the verdict tail.
  let field (k : String) : String := (j.getObjValAs? String k).toOption.getD ""
  let flag (k : String) : String := toString ((j.getObjValAs? Bool k).toOption.getD false)
  let short (s : String) (n : Nat) : String := String.ofList (s.toList.take n)
  let last (s : String) : String := (s.splitOn ".").getLast!
  let types (k : String) (n : Nat) : List String := match j.getObjVal? k with
    | .ok (.arr xs) => xs.toList.map fun (x : Json) => short ((x.getObjValAs? String "type").toOption.getD "") n
    | _ => []
  let record := field "record"
  if record == "weakening" then
    (← IO.getStderr).putStrLn s!"W {last (field "theorem")}#{(j.getObjValAs? Nat "i").toOption.getD 0} ok={flag "kernel_checked"} :: {types "consequences" 90}"
  else if record == "weakening_attempt" then
    (← IO.getStderr).putStrLn s!"WA {last (field "theorem")} {field "status"}"
  else if record == "generalisation" then
    if field "status" == "generalised" then
      (← IO.getStdout).putStrLn s!"G {last (field "theorem")} {field "literal"}:{field "literal_type"} ok={flag "kernel_checked"} uniform={flag "uniform"} ob={types "obligations" 60} dis={types "discharged" 40}"
  else if record == "summary" then
    let keys := ["theorems", "weakening_tried", "weakened_theorems", "weakening_rejected",
      "weakening_consequences", "generalisation_literals", "generalised", "generalised_uniform",
      "generalisation_obligations", "generalisation_discharged", "generalisation_refused",
      "generalisation_rejected", "generalisation_truncated", "ground_candidates", "ground_tried",
      "ground_closed", "ground_nonempty_closed", "ground_refuted", "ground_truncated",
      "battery_leaves", "battery_conditional_leaves", "battery_tried", "battery_closed",
      "battery_refuted", "nat_refute_tried", "nat_refuted", "statements_discovered",
      "statements_searched", "truncated", "elapsed_ms", "weakening_ms", "generalise_ms", "ground_ms"]
    let picked := keys.filterMap fun k => (j.getObjVal? k).toOption.map fun v => (k, v)
    (← IO.getStderr).putStrLn (Json.mkObj picked).compress
  else if record == "theorem_error" || record == "statement_error" then
    (← IO.getStderr).putStrLn s!"E {record} {field "name"}{field "statement"} {field "reason"}"

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
`none` means accepted. The kernel is called directly, so no option (such as
`debug.skipKernelTC`) can turn the check off; `heartbeats` (thousands, 0 for
unbounded) bounds the kernel's own work. -/
def kernelVerdict (type value : Expr) (levelParams : List Name := []) (heartbeats : Nat := 0) :
    MetaM (Option String) := do
  let decl := Declaration.thmDecl
    { name := `_argument_continuation_check, levelParams, type, value }
  match Kernel.Environment.addDeclCore (← getEnv).toKernelEnv (heartbeats * 1000).toUSize decl none with
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

/-! ## Used consequences

A proof may use a hypothesis `h : H` only through what it derives from it:
`L h` for a lemma `L`, a component `h.1`, an instance `h 3`. Replacing `h` by
those consequences gives a theorem with weaker hypotheses and the same
argument. A *use site* is an occurrence of `h` inside the largest application
around it that mentions no bound variable of the proof and no other binder of
the statement, whose type is a proposition that neither mentions `H` nor is
`H` up to unfolding nor is the theorem's own conclusion. The weakening exists
when every occurrence of `h` lies in a use site. -/

/-- Whether `e` is the hypothesis `h` itself, possibly transported by a cast,
`Eq.mp`, `Eq.mpr` or `id` whose other arguments do not use `h`. -/
partial def isHypRef (h : FVarId) (e : Expr) : Bool :=
  match e.consumeMData with
  | .fvar id => id == h
  | e =>
      match e.getAppFn with
      | .const n _ =>
          let args := e.getAppArgs
          if (n == ``Eq.mpr || n == ``Eq.mp || n == ``cast) && args.size == 4 then
            !args[2]!.containsFVar h && isHypRef h args[3]!
          else if n == ``id && args.size == 2 then isHypRef h args[1]!
          else false
      | _ => false

structure UseScan where
  /-- Per subterm: whether it mentions `h`, and whether it mentions another
  free variable. Memoised, so shared subterms are visited once. -/
  facts : Std.HashMap Expr (Bool × Bool) := {}
  verdicts : Std.HashMap Expr Bool := {}
  sites : Array Expr := #[]
  visited : Nat := 0

abbrev UseM := StateT UseScan MetaM

partial def useFacts (h : FVarId) (e : Expr) : UseM (Bool × Bool) := do
  if !e.hasFVar then return (false, false)
  if let some f := (← get).facts.get? e then return f
  let f ← match e with
    | .fvar id => pure (id == h, id != h)
    | .app f a => do
        let x ← useFacts h f
        let y ← useFacts h a
        pure (x.1 || y.1, x.2 || y.2)
    | .lam _ t b _ | .forallE _ t b _ => do
        let x ← useFacts h t
        let y ← useFacts h b
        pure (x.1 || y.1, x.2 || y.2)
    | .letE _ t v b _ => do
        let x ← useFacts h t
        let y ← useFacts h v
        let z ← useFacts h b
        pure (x.1 || y.1 || z.1, x.2 || y.2 || z.2)
    | .mdata _ b | .proj _ _ b => useFacts h b
    | _ => pure (false, false)
  modify fun s => { s with facts := s.facts.insert e f }
  return f

/-- No bound variable of the proof, no metavariable, no free variable but `h`. -/
def closedFor (h : FVarId) (e : Expr) : UseM Bool := do
  if e.hasLooseBVars || e.hasMVar then return false
  return !(← useFacts h e).2

/-- The proposition a use site proves, if the site qualifies. -/
def siteType? (hType : Expr) (conclusionKey : Option String) (site : Expr) : MetaM (Option Expr) := do
  try
    let t ← instantiateMVars (← inferType site)
    unless ← isProp t do return none
    if t.hasFVar || t.hasMVar || t.hasLooseBVars then return none
    if (t.find? (· == hType)).isSome then return none
    if conclusionKey == some (keyOf t) then return none
    if let .ok true ← budgeted 5000 (withNewMCtxDepth (isDefEq t hType)) then return none
    return some t
  catch _ => return none

mutual
/-- Whether every occurrence of `h` in `e` lies inside a use site; the sites
are collected in the state. `false`: some occurrence uses `h` as it stands. -/
partial def collectUses (h : FVarId) (hType : Expr) (conclusionKey : Option String) (e : Expr) :
    UseM Bool := do
  if !(← useFacts h e).1 then return true
  if let some v := (← get).verdicts.get? e then return v
  let s ← get
  if s.visited ≥ 200000 then return false
  set { s with visited := s.visited + 1 }
  let v ← visitUses h hType conclusionKey e
  modify fun s => { s with verdicts := s.verdicts.insert e v }
  return v

partial def visitUses (h : FVarId) (hType : Expr) (conclusionKey : Option String) (e : Expr) :
    UseM Bool := do
  match e with
  | .fvar _ => return false
  | .mdata _ b => collectUses h hType conclusionKey b
  | .proj _ _ b =>
      if isHypRef h b && (← closedFor h e) then
        unless (← siteType? hType conclusionKey e).isSome do return false
        modify fun s => { s with sites := s.sites.push e }
        return true
      collectUses h hType conclusionKey b
  | .lam _ t b _ | .forallE _ t b _ =>
      let x ← collectUses h hType conclusionKey t
      let y ← collectUses h hType conclusionKey b
      return x && y
  | .letE _ t v b _ =>
      let x ← collectUses h hType conclusionKey t
      let y ← collectUses h hType conclusionKey v
      let z ← collectUses h hType conclusionKey b
      return x && y && z
  | .app .. =>
      -- `h` transported by a cast is `h`; the application around it decides.
      if isHypRef h e then return false
      let fn := e.getAppFn
      let args := e.getAppArgs
      let mut k := 0
      if ← closedFor h fn then
        while k < args.size do
          if ← closedFor h args[k]! then k := k + 1 else break
      if k > 0 && (isHypRef h fn || (args.extract 0 k).any (isHypRef h)) then
        let site := mkAppN fn (args.extract 0 k)
        unless (← siteType? hType conclusionKey site).isSome do return false
        modify fun s => { s with sites := s.sites.push site }
        let mut ok := true
        for a in args.extract k args.size do
          unless ← collectUses h hType conclusionKey a do ok := false
        return ok
      let mut ok ← collectUses h hType conclusionKey fn
      for a in args do
        unless ← collectUses h hType conclusionKey a do ok := false
      return ok
  | _ => return true
end

structure Weakening where
  type : Expr
  value : Expr
  hypothesis : Expr
  consequences : Array Expr
  /-- Per consequence: the constants its use sites apply `h` to, and the
  sites as rendered. -/
  via : Array (Array String)
  sites : Array (Array String)
  /-- Per consequence: whether the kernel accepts `H → C` as the use site. -/
  implied : Array Bool

/-- Binder `i` of a theorem replaced by what the proof uses of it: one
hypothesis per distinct use-site proposition, placed where the binder was,
with each use site in the proof replaced by the new hypothesis. -/
def weakenAt (info : ConstantInfo) (i : Nat) : MetaM (Option Weakening) := do
  let some value := info.value? | return none
  forallTelescope info.type fun xs body => do
    unless i < xs.size do return none
    let x := xs[i]!
    let h := x.fvarId!
    let hType ← instantiateMVars (← h.getDecl).type
    if body.containsFVar h then return none
    for j in [i+1:xs.size] do
      if (← xs[j]!.fvarId!.getDecl).type.containsFVar h then return none
    let proof := value.beta xs
    let conclusionKey := if body.hasFVar then none else some (keyOf body)
    let (ok, scan) ← (collectUses h hType conclusionKey proof).run {}
    unless ok && !scan.sites.isEmpty do return none
    let mut consequences : Array Expr := #[]
    let mut slot : Array Nat := #[]
    let mut via : Array (Array String) := #[]
    let mut rendered : Array (Array String) := #[]
    for site in scan.sites do
      let t ← instantiateMVars (← inferType site)
      let head := (headName? site).map Name.toString |>.getD (if isHypRef h site.getAppFn then "hypothesis" else "")
      let text ← renderProof site
      match consequences.findIdx? (· == t) with
      | some j =>
          slot := slot.push j
          unless via[j]!.contains head do via := via.modify j (·.push head)
          unless rendered[j]!.contains text do rendered := rendered.modify j (·.push text)
      | none =>
          slot := slot.push consequences.size
          consequences := consequences.push t
          via := via.push #[head]
          rendered := rendered.push #[text]
    let mut implied : Array Bool := #[]
    for j in [0:consequences.size] do
      let some k := slot.findIdx? (· == j) | implied := implied.push false; continue
      let checked ← kernelVerdict (← mkForallFVars #[x] consequences[j]!)
        (← mkLambdaFVars #[x] scan.sites[k]!) info.levelParams
      implied := implied.push checked.isNone
    let decls := consequences.mapIdx fun j t =>
      (Name.mkSimple s!"used{j}", fun (_ : Array Expr) => (pure t : MetaM Expr))
    withLocalDeclsD decls fun cs => do
      let sites := scan.sites
      let replaced := proof.replace fun e =>
        if !e.hasFVar then none
        else match sites.findIdx? (· == e) with
          | some j => some cs[slot[j]!]!
          | none => none
      if replaced.containsFVar h then return none
      let keep := xs.extract 0 i ++ cs ++ xs.extract (i + 1) xs.size
      let type ← instantiateMVars (← mkForallFVars keep body)
      let value ← instantiateMVars (← mkLambdaFVars keep replaced)
      if type.hasMVar || value.hasMVar then return none
      return some { type, value, hypothesis := hType, consequences, via, sites := rendered, implied }

/-! ## Scope-aware used consequences (`PLECTIS_CONTINUATION_USED_V2`)

The pass above admits a use site only when it mentions no variable other than
`h`, so `L n h` under a binder `n`, a use inside a lambda, or one that needs a
dependent datum `x : Fin (n + 1)` leaves the hypothesis as it stands. This
version opens every binder of the proof (and zeta-reduces `let`s), so a use
site may mention local variables. Its consequence is the site's proposition
closed over the variables the site needs, in context order, together with the
variables their types need (`∀ n (x : Fin (n + 1)), P n x`), and the site
becomes that new hypothesis applied to them.

A site is rejected when one of those variables has a type that mentions `h`,
when its proposition mentions `h` or `H`, is `H` up to unfolding, or is the
theorem's own statement; the whole weakening is rejected when the proof itself
becomes a new hypothesis applied to arguments (the consequence proves the goal
outright, so the weakening says nothing). The kernel checks `H → C` for each
consequence before admitting it, and the whole weakened theorem when it is
added. New hypotheses are placeholder constants until the final term is built;
no term containing one reaches the kernel or the environment.
-/

structure LiftUseState where
  consequences : Array Expr := #[]
  holes : Array Name := #[]
  via : Array (Array String) := #[]
  sites : Array (Array String) := #[]
  visited : Nat := 0
  exceeded : Bool := false
  /-- Rewrites of shared subterms, so a proof DAG is walked once per node. -/
  memo : Std.HashMap Expr (Option Expr) := {}

abbrev LiftUseM := StateT LiftUseState MetaM

/-- The local variables a use site needs as parameters: those it mentions
other than `h`, and transitively those their types mention, in context order.
`none` when one of them has a type that mentions `h` (the site cannot be
stated without `h`) or is not in scope. -/
def boundaryParameters (h : FVarId) (context : Array Expr) (site : Expr) :
    MetaM (Option (Array Expr)) := do
  let mut needed : Std.HashSet FVarId := {}
  for id in (collectFVars {} site).fvarSet.toList do
    if id != h then needed := needed.insert id
  let mut changed := true
  while changed do
    changed := false
    for x in context do
      let id := x.fvarId!
      if needed.contains id then
        let ty ← instantiateMVars (← id.getDecl).type
        if ty.containsFVar h then return none
        for y in context do
          let yid := y.fvarId!
          if yid != h && !needed.contains yid && ty.containsFVar yid then
            needed := needed.insert yid
            changed := true
  let params := context.filter fun x => needed.contains x.fvarId!
  if params.size != needed.size then return none
  return some params

/-- `G` when `t` is `¬¬G`, `¬G → False` or `(G → False) → False`. -/
def doubleNegated? (t : Expr) : Option Expr :=
  let negated? (d : Expr) : Option Expr :=
    if d.isAppOfArity ``Not 1 then some d.appArg!
    else match d with
      | .forallE _ g b _ => if b.isConstOf ``False && !b.hasLooseBVars then some g else none
      | _ => none
  let t := t.consumeMData
  if t.isAppOfArity ``Not 1 then negated? t.appArg!.consumeMData
  else match t with
    | .forallE _ d b _ => if b.isConstOf ``False then negated? d.consumeMData else none
    | _ => none

/-- Admit the use site `site`: its proposition closed over its parameters is a
consequence of `H` (the kernel checks `H → C` the first time `C` is seen), and
the site becomes that consequence's placeholder applied to the parameters. -/
def liftBoundary (h : FVarId) (hType : Expr) (levelParams : List Name) (goalKeys : Array String)
    (kernelHeartbeats : Nat) (context : Array Expr) (site : Expr) : LiftUseM (Option Expr) := do
  try
    let t ← instantiateMVars (← inferType site)
    unless ← isProp t do return none
    if t.containsFVar h || t.hasMVar || t.hasLooseBVars then return none
    if (t.find? (· == hType)).isSome then return none
    let some params ← boundaryParameters h context site | return none
    let c ← instantiateMVars (← mkForallFVars params t)
    if c.hasFVar || c.hasMVar || c.hasLooseBVars then return none
    if goalKeys.contains (keyOf c) then return none
    -- A `by_contra` use (`¬G → False`, `¬¬G`) restates the goal classically.
    if let some g := doubleNegated? t then
      if goalKeys.contains (keyOf g) || goalKeys.contains (keyOf (← mkForallFVars params g)) then
        return none
    if let .ok true ← budgeted 5000 (withNewMCtxDepth (isDefEq c hType)) then return none
    let head := (headName? site).map Name.toString |>.getD "hypothesis"
    let rendered ← renderProof site
    let current ← get
    if let some index := current.consequences.findIdx? (· == c) then
      set { current with
        via := current.via.modify index fun v => if v.contains head then v else v.push head
        sites := current.sites.modify index fun v => if v.contains rendered then v else v.push rendered }
      return some (mkAppN (mkConst current.holes[index]!) params)
    if current.consequences.size ≥ 128 then
      set { current with exceeded := true }
      return none
    let recover ← instantiateMVars (← mkLambdaFVars #[mkFVar h] (← mkLambdaFVars params site))
    if recover.hasFVar || recover.hasMVar then return none
    let recoverType ← mkForallFVars #[mkFVar h] c
    unless (← kernelVerdict recoverType recover levelParams kernelHeartbeats).isNone do return none
    let hole ← mkFreshUserName `_plectis_boundary_hole
    modify fun s => { s with
      consequences := s.consequences.push c, holes := s.holes.push hole
      via := s.via.push #[head], sites := s.sites.push #[rendered] }
    return some (mkAppN (mkConst hole) params)
  catch _ => return none

/-- Shrink an application prefix `f a₁ … aₖ` containing `h` by dropping
trailing arguments that are local variables mentioned nowhere else in it (nor
in the types of the variables it mentions): the closed consequence is the same
statement up to those binders, and the shorter site keeps a named proposition
(`weak_of_strong h : Weak`) rather than its unfolding at a bound variable. -/
def trimTrailing (h : FVarId) (fn : Expr) (args : Array Expr) (k : Nat) (use : Expr → Bool) :
    MetaM Nat := do
  let mut k := k
  while k > 0 do
    let a := args[k - 1]!
    unless a.isFVar && a.fvarId! != h do break
    let id := a.fvarId!
    let rest := args.extract 0 (k - 1)
    unless isHypRef h fn || use fn || rest.any use do break
    if fn.containsFVar id || rest.any (·.containsFVar id) then break
    let mut dependent := false
    for y in (collectFVars {} (mkAppN fn rest)).fvarSet.toList do
      if (← y.getDecl).type.containsFVar id then
        dependent := true
        break
    if dependent then break
    k := k - 1
  return k

mutual
/-- The proof with every use of `h` replaced by a placeholder application, or
`none` when some occurrence of `h` is not inside an admissible use site. -/
partial def rewriteUsesV2 (h : FVarId) (hType : Expr) (levelParams : List Name)
    (goalKeys : Array String) (kernelHeartbeats : Nat) (context : Array Expr) (e : Expr) :
    LiftUseM (Option Expr) := do
  unless e.containsFVar h do return some e
  if let some r := (← get).memo.get? e then return r
  let state ← get
  if state.visited ≥ 200000 then
    set { state with exceeded := true }
    return none
  set { state with visited := state.visited + 1 }
  let r ← rewriteNodeV2 h hType levelParams goalKeys kernelHeartbeats context e
  modify fun s => { s with memo := s.memo.insert e r }
  return r

/-- One node of `rewriteUsesV2` (a separate function, so that its `return`s
come back to the memoising wrapper). -/
partial def rewriteNodeV2 (h : FVarId) (hType : Expr) (levelParams : List Name)
    (goalKeys : Array String) (kernelHeartbeats : Nat) (context : Array Expr) (e : Expr) :
    LiftUseM (Option Expr) := do
  let recur := rewriteUsesV2 h hType levelParams goalKeys kernelHeartbeats
  match e with
    | .mdata md b => return (← recur context b).map (Expr.mdata md)
    | .lam n t b bi =>
        if t.containsFVar h then return none
        withLocalDecl n bi t fun x => do
          let some body ← recur (context.push x) (b.instantiate1 x) | return none
          return some (← mkLambdaFVars #[x] body)
    | .forallE n t b bi =>
        if t.containsFVar h then return none
        withLocalDecl n bi t fun x => do
          let some body ← recur (context.push x) (b.instantiate1 x) | return none
          return some (← mkForallFVars #[x] body)
    | .letE _ _ value body _ => recur context (body.instantiate1 value)
    | .proj n i b =>
        let saved ← get
        if isHypRef h b then
          if let some out ← liftBoundary h hType levelParams goalKeys kernelHeartbeats context e then
            return some out
        if let some b' ← recur context b then return some (Expr.proj n i b')
        -- `(h n).i` under a binder: `h n` alone closes back to `H`, so the
        -- projection is the use site.
        if b.containsFVar h then
          set saved
          if let some out ← liftBoundary h hType levelParams goalKeys kernelHeartbeats context e then
            return some out
        return none
    | .app .. =>
        let beta := e.headBeta
        if beta != e then return ← recur context beta
        if isHypRef h e then return none
        let fn := e.getAppFn
        let args := e.getAppArgs
        let saved ← get
        -- 1. `h` itself is the function or an argument: the application is the
        -- use site (the V1 site, now allowed to mention local variables).
        if isHypRef h fn || args.any (isHypRef h) then
          if let some r ← liftPrefixes h hType levelParams goalKeys kernelHeartbeats context fn args
              (isHypRef h) then
            return some r
          set saved
        -- 2. Otherwise rewrite the function and the arguments.
        let generic ← (do
          let some f ← recur context fn | return none
          let mut newArgs : Array Expr := #[]
          for a in args do
            let some a' ← recur context a | return none
            newArgs := newArgs.push a'
          return some (mkAppN f newArgs) : LiftUseM (Option Expr))
        if generic.isSome then return generic
        -- 3. An argument using `h` admits no site of its own (`h n` or
        -- `L n h` under a binder `n` closes back to `H`): the enclosing
        -- application is the use site (`And.left (h n)`, `le_of_lt (L n h)`).
        let uses : Expr → Bool := fun a => a.containsFVar h
        if uses fn || args.any uses then
          set saved
          if let some r ← liftPrefixes h hType levelParams goalKeys kernelHeartbeats context fn args uses then
            return some r
        return none
    | _ => return none

/-- The prefixes of `fn args` containing an argument that satisfies `use` (all
of them when `fn` is `h`) as use sites: the trimmed full application first,
then every other prefix from the largest, so a bad large boundary does not
hide a smaller one. The first admissible site is replaced and the remaining
arguments are rewritten. -/
partial def liftPrefixes (h : FVarId) (hType : Expr) (levelParams : List Name)
    (goalKeys : Array String) (kernelHeartbeats : Nat) (context : Array Expr) (fn : Expr)
    (args : Array Expr) (use : Expr → Bool) : LiftUseM (Option Expr) := do
  let trimmed ← trimTrailing h fn args args.size use
  let mut order : Array Nat := #[trimmed]
  for k in (List.range args.size).reverse do
    if k + 1 != trimmed then order := order.push (k + 1)
  for count in order do
    let pre := args.extract 0 count
    unless isHypRef h fn || use fn || pre.any use do continue
    if let some replaced ← liftBoundary h hType levelParams goalKeys kernelHeartbeats context
        (mkAppN fn pre) then
      let mut rest : Array Expr := #[]
      for a in args.extract count args.size do
        let some a' ← rewriteUsesV2 h hType levelParams goalKeys kernelHeartbeats context a | return none
        rest := rest.push a'
      return some (mkAppN replaced rest)
  return none
end

/-- Strip leading lambdas (the result may have loose bound variables). -/
partial def stripLambdas : Expr → Expr
  | .lam _ _ b _ => stripLambdas b
  | .mdata _ b => stripLambdas b
  | e => e

/-- Binder `i` of a theorem replaced by what the proof uses of it, scope-aware.
`.error reason` when there is no admissible weakening. The weakened theorem is
kernel-checked when `addWeakened` installs it. -/
def weakenAtV2 (info : ConstantInfo) (i : Nat) (kernelHeartbeats : Nat) :
    MetaM (Except String Weakening) := do
  let some value := info.value? | return .error "no_value"
  forallTelescope info.type fun xs body => do
    unless i < xs.size do return .error "no_binder"
    let h := xs[i]!.fvarId!
    let hType ← instantiateMVars (← h.getDecl).type
    unless ← isProp hType do return .error "not_a_proposition"
    if hType.hasFVar || hType.hasMVar || body.containsFVar h then return .error "dependent"
    for j in [i+1:xs.size] do
      if (← xs[j]!.fvarId!.getDecl).type.containsFVar h then return .error "dependent"
    let others := xs.extract 0 i ++ xs.extract (i + 1) xs.size
    let wholeType ← instantiateMVars (← mkForallFVars others body)
    let goalKeys := if body.hasFVar then #[keyOf wholeType] else #[keyOf wholeType, keyOf body]
    let (result, scan) ← (rewriteUsesV2 h hType info.levelParams goalKeys kernelHeartbeats xs
      (value.beta xs)).run {}
    if scan.exceeded then return .error "exceeded"
    let some template := result | return .error "bare_use"
    if scan.consequences.isEmpty then return .error "no_use_site"
    if template.containsFVar h then return .error "bare_use"
    let isHole : Expr → Bool := fun e => match e.getAppFn with
      | .const n _ => scan.holes.contains n
      | _ => false
    if isHole (stripLambdas template) then return .error "vacuous"
    let decls := scan.consequences.mapIdx fun j t =>
      (Name.mkSimple s!"used{j}", fun (_ : Array Expr) => (pure t : MetaM Expr))
    withLocalDeclsD decls fun cs => do
      let replaced := template.replace fun sub =>
        match sub with
        | .const name _ => (scan.holes.findIdx? (· == name)).map (fun j => cs[j]!)
        | _ => none
      if (replaced.find? fun sub => match sub with
          | .const n _ => scan.holes.contains n
          | _ => false).isSome then return .error "placeholder_left"
      let keep := xs.extract 0 i ++ cs ++ xs.extract (i + 1) xs.size
      let type ← instantiateMVars (← mkForallFVars keep body)
      let proof ← instantiateMVars (← mkLambdaFVars keep replaced)
      if type.hasMVar || type.hasFVar || proof.hasMVar || proof.hasFVar then return .error "open_term"
      let w : Weakening := {
        type := type, value := proof, hypothesis := hType,
        consequences := scan.consequences, via := scan.via, sites := scan.sites,
        implied := scan.consequences.map fun _ => true }
      return .ok w

/-- The used-consequence pass the configuration selects. -/
def weakenEither (cfg : Config) (info : ConstantInfo) (i : Nat) : MetaM (Except String Weakening) := do
  if cfg.usedConsequencesV2 then weakenAtV2 info i cfg.kernelHeartbeats
  else return match ← weakenAt info i with
    | some w => .ok w
    | none => .error "no_weakening"

/-- Add the weakened theorem to the environment under a derived name; the
kernel checks it on the way in, and the passes after this one can use it. -/
def addWeakened (info : ConstantInfo) (i : Nat) (type value : Expr) : MetaM (Except String Name) := do
  let name := info.name ++ Name.mkSimple s!"_argument_weakening_{i}"
  let decl := Declaration.thmDecl { name, levelParams := info.levelParams, type, value }
  match (← getEnv).addDeclCore 0 decl none with
  | .ok env =>
      setEnv env
      return .ok name
  | .error ex => return .error (clip (← (ex.toMessageData (← getOptions)).toString) 400)

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
      -- The stronger statement is closed (every binder is abstracted), so it
      -- is a statement of the graph that the kernel just proved.
      ("key", toJson (keyOf strongerType)),
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
    let mut scored : Array (Nat × String × Producer) := #[]
    for p in producers.getD head #[] do
      let cs := p.constants.toList
      let shared := (cs.filter fun c => used.contains c).length
      if cfg.relaxedProducerFilter || shared == cs.length then
        scored := scored.push (shared, p.name.toString, p)
    -- Over the cap, the producers sharing the most constants with the
    -- statement are tried first (then by name, so the choice is
    -- reproducible). This only orders attempts: every candidate still goes
    -- through the unifier, inhabitation and residual checks, and the relation
    -- stays a lower bound.
    if scored.size > cfg.maxCandidates then
      scored := scored.qsort fun a b => a.1 > b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
    let candidates := scored.map (·.2.2)
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

/-- Tactic scripts for a battery: each `(label, tactic)` runs after `intros`
and after unfolding the corpus definitions the statement mentions. Scripts are
parsed against the current environment, so a tactic the environment lacks (for
example a Mathlib tactic in a core-only test) is skipped, not an error. -/
def batteryScripts (defs : Array Name) (tactics : List (String × String)) :
    Elab.TermElabM (Array (String × Syntax)) := do
  let env ← getEnv
  let pre :=
    if defs.isEmpty then "intros"
    else "(intros; try unfold " ++ String.intercalate " " (defs.toList.map toString) ++ " at *)"
  let mut out := #[]
  for (label, tac) in tactics do
    match Parser.runParserCategory env `tactic s!"({pre}; {tac})" with
    | .ok stx => out := out.push (label, stx)
    | .error _ => pure ()
  return out

/-- The standard closing tactics of the battery. -/
def standardTactics : List String := ["decide", "omega", "norm_num", "simp_all", "positivity", "linarith"]

/-- Whether a proof leans on a certificate the kernel does not check: an axiom
that trusts the compiler, or `sorry`, in the proof or in an auxiliary
declaration the tactic created (`env₀` is the environment before it ran). -/
partial def untrustedCertificate (env₀ : Environment) (proof : Expr) (fuel : Nat := 32) :
    MetaM Bool := do
  let banned : List Name := [`Lean.ofReduceBool, `Lean.ofReduceNat, `Lean.trustCompiler, ``sorryAx]
  for c in proof.getUsedConstants do
    if banned.contains c then return true
    if fuel > 0 && !env₀.contains c then
      if let some info := (← getEnv).find? c then
        if let some value := info.value? then
          if ← untrustedCertificate env₀ value (fuel - 1) then return true
  return false

/-- `proof` with every auxiliary declaration the tactic created (absent from
`env₀`) replaced by its value, so that the term outlives the reverted state. -/
partial def inlineAuxiliary (env₀ : Environment) (proof : Expr) (fuel : Nat := 32) :
    MetaM (Option Expr) := do
  if (proof.getUsedConstants.filter fun c => !env₀.contains c).isEmpty then return some proof
  if fuel == 0 then return none
  let env ← getEnv
  let replaced := proof.replace fun e => match e with
    | .const c us =>
        if env₀.contains c then none
        else (env.find? c).bind fun info => info.value?.map (·.instantiateLevelParams info.levelParams us)
    | _ => none
  inlineAuxiliary env₀ replaced (fuel - 1)

/-- Run `tactics` on the closed `statement` in order, each within `heartbeats`
thousand heartbeats, and return the label of the first whose proof the kernel
accepts (bounded by `kernelHeartbeats` thousand, 0 for unbounded), with the
proof when `wantProof` (auxiliary declarations inlined, so it can be reused
after the attempt's state is reverted). -/
def runTactics (cfg : Config) (env : Environment) (statement : Expr) (tactics : List (String × String))
    (heartbeats : Nat) (kernelHeartbeats : Nat := 0) (wantProof : Bool := false) :
    Elab.TermElabM (Option (String × Expr)) := do
  let defs := (statement.getUsedConstants.filter fun c =>
      selected cfg env c && (match env.find? c with | some (.defnInfo _) => true | _ => false))
  let env₀ ← getEnv
  for (label, script) in ← batteryScripts defs tactics do
    -- The kernel check runs inside the reverted block: a tactic's auxiliary
    -- lemmas exist only there. The goal starts in an empty local context: a
    -- caller's locals (the generalised `v` and its obligations) must not be
    -- hypotheses the tactic can use, or the proof would mention them.
    let attempt : Elab.TermElabM (Option Expr) := withoutModifyingState <| withLCtx {} {} do
      let goal ← mkFreshExprMVar statement
      let remaining ← Elab.Tactic.run goal.mvarId! (Elab.Tactic.evalTactic script)
      unless remaining.isEmpty do return none
      Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let proof ← instantiateMVars goal
      if proof.hasMVar || proof.hasSorry then return none
      if ← untrustedCertificate env₀ proof then return none
      unless (← kernelVerdict statement proof [] kernelHeartbeats).isNone do return none
      if wantProof then inlineAuxiliary env₀ proof else return some proof
    let result ← budgetedTerm heartbeats attempt
    modifyThe Core.State fun st => { st with messages := {} }
    if let .ok (some proof) := result then return some (label, proof)
  return none

/-- The label of the first tactic whose proof of `statement` the kernel accepts. -/
def tryTactics (cfg : Config) (env : Environment) (statement : Expr) (tactics : List (String × String))
    (heartbeats : Nat) (kernelHeartbeats : Nat := 0) : Elab.TermElabM (Option String) := do
  return (← runTactics cfg env statement tactics heartbeats kernelHeartbeats).map (·.1)

/-- Try the battery on a closed statement (the standard tactics and the
configured extra ones, unless `tactics` names others); return the tactic that
closed it if the kernel accepts the resulting proof. -/
def tryBattery (cfg : Config) (env : Environment) (statement : Expr) (tactics : List String := []) :
    Elab.TermElabM (Option String) := do
  let list := if tactics.isEmpty then standardTactics ++ cfg.extraTactics else tactics
  tryTactics cfg env statement (list.map fun t => (t, t)) cfg.batteryHeartbeats

/-! ## Ground tier

The consumer-ordered battery reaches a few thousand leaves in its budget, and
a statement that has any conditional producer was never one of its leaves,
so trivially decidable residuals (`2 ≤ 13`, `0 < 1 / 2`) stayed open and
filled open counts, disguise classes and bundles. The ground tier runs first,
on every discovered statement (searched or not, whatever its producers) that
is small and ground: no λ, no `let`, and every `∀` a non-dependent implication
between propositions, so it is a fact about constants. It tries `decide`,
`norm_num` and `simp` on the statement and on its negation with a small
heartbeat budget each, most-consumed statements first and then the smallest.
`Nonempty T` statements are tried with an instance, `default` and a bounded
constructor search; a failure leaves them open and never refutes them. Every
success is a kernel-checked `battery` or `battery_refutation` row marked
`"tier": "ground"`.
-/

/-- Tree size of `e` (shared subterms counted each time), stopping once past `cap`. -/
partial def sizeUpTo (cap : Nat) (e : Expr) (acc : Nat := 0) : Nat :=
  if acc > cap then acc else
  match e with
  | .app f a => sizeUpTo cap a (sizeUpTo cap f (acc + 1))
  | .lam _ t b _ => sizeUpTo cap b (sizeUpTo cap t (acc + 1))
  | .forallE _ t b _ => sizeUpTo cap b (sizeUpTo cap t (acc + 1))
  | .letE _ t v b _ => sizeUpTo cap b (sizeUpTo cap v (sizeUpTo cap t (acc + 1)))
  | .mdata _ b => sizeUpTo cap b acc
  | .proj _ _ b => sizeUpTo cap b (acc + 1)
  | _ => acc + 1

/-- A ground proposition: built from constants and literals by application and
non-dependent implication between propositions only. -/
partial def isGround (e : Expr) : MetaM Bool := do
  match e with
  | .app f a => return (← isGround f) && (← isGround a)
  | .forallE _ d b _ =>
      if b.hasLooseBVars then return false
      unless ← isProp d do return false
      return (← isGround d) && (← isGround b)
  | .mdata _ b => isGround b
  | .proj _ _ b => isGround b
  | .const .. | .lit _ | .sort _ => return true
  | _ => return false

/-- `nonempty` for a closed `Nonempty T`, `ground` for a small ground statement
other than a bare named proposition (a named input is the ordinary battery's). -/
def groundKind (cfg : Config) (statement : Expr) : MetaM (Option String) := do
  let e := statement.consumeMData
  if e.hasFVar || e.hasMVar || e.hasLevelParam || e.hasLooseBVars then return none
  if sizeUpTo cfg.groundMaxSize e > cfg.groundMaxSize then return none
  if e.isAppOfArity ``Nonempty 1 then return some "nonempty"
  if e.isConst then return none
  if ← isGround e then return some "ground" else return none

def groundTactics : List String := ["decide", "norm_num", "simp"]

/-- Ways to exhibit an inhabitant: an instance, `default`, and a bounded
constructor search. `constructor` lists proof fields before the data fields
they depend on, so the data goals are filled with `default` first and the
proof goals are then closed by a closing tactic. A field that is `False`
leaves a goal nothing closes, so the search fails and the statement stays open. -/
def nonemptyTactics : List (String × String) :=
  let leaves := "(try any_goals exact default); all_goals first | trivial | rfl | decide | " ++
    "(intros; rfl) | (intros; trivial) | (intros; simp) | exact default"
  [("infer_instance", "infer_instance"),
   ("default", "exact ⟨default⟩"),
   ("constructor", s!"exact ⟨by constructor; {leaves}⟩"),
   ("constructor_search", s!"exact ⟨by (repeat' constructor); {leaves}⟩")]

/-- Bounded witness search for a leading Nat universal: for `n < limit`, try to
prove the negation of the instance at `n`; a proof becomes a proof of the
negation of the ORIGINAL statement, which the kernel checks. Finding none is
unknown, never a verdict. -/
def tryNatCounterexample (cfg : Config) (statement : Expr) (deadlineMs : Nat) (limit : Nat := 16) :
    Elab.TermElabM (Option (Nat × String)) := do
  let .forallE _ domain body _ := statement.consumeMData | return none
  unless domain.isConstOf ``Nat do return none
  let env₀ ← getEnv
  let scripts ← batteryScripts #[]
    [("omega", "omega"), ("norm_num", "norm_num at *"), ("simp_all", "simp_all"), ("decide", "decide")]
  for n in [:limit] do
    if (← IO.monoMsNow) ≥ deadlineMs then return none
    let inst := body.instantiate1 (mkNatLit n)
    if inst.hasFVar || inst.hasMVar || inst.hasLooseBVars then continue
    for (label, script) in scripts do
      if (← IO.monoMsNow) ≥ deadlineMs then return none
      let attempt : Elab.TermElabM Bool := withoutModifyingState do
        let goal ← mkFreshExprMVar (mkNot inst)
        let remaining ← Elab.Tactic.run goal.mvarId! (Elab.Tactic.evalTactic script)
        unless remaining.isEmpty do return false
        Elab.Term.synthesizeSyntheticMVarsNoPostponing
        let negative ← instantiateMVars goal
        if negative.hasMVar || negative.hasSorry then return false
        if ← untrustedCertificate env₀ negative then return false
        withLocalDeclD `_universal statement fun universal => do
          let proof ← mkLambdaFVars #[universal] (mkApp negative (mkApp universal (mkNatLit n)))
          return (← kernelVerdict (mkNot statement) proof [] cfg.kernelHeartbeats).isNone
      let result ← budgetedTerm cfg.batteryHeartbeats attempt
      modifyThe Core.State fun st => { st with messages := {} }
      if let .ok true := result then return some (n, label)
  return none

/-! ## Literal generalisation (`PLECTIS_CONTINUATION_GENERALISE_SECONDS`)

For a theorem `T : S` and a numeral `L` of `S` (an `OfNat.ofNat` literal of ℕ,
ℤ, ℚ or ℝ, other than 0 and 1), abstract `L` to a variable `v` in the
statement and in the proof. A proof step that holds only at `L` (a `decide`,
a `norm_num` computation) no longer checks once `L` is abstracted. Each such
step is replaced by a new hypothesis stating what it proved, with `L`
abstracted: a closed proof subterm whose proposition mentions `L` is kept
abstracted when the kernel accepts it so, rebuilt from its repaired parts when
that is accepted, and cut into an obligation otherwise, so the cuts are as
small as the kernel allows and the obligations as weak. A closed proof of a
proposition that does not mention `L` is kept as it is. The result
`∀ v, Φ₁ v → ⋯ → Φₘ v → S[v]` is kernel-checked; the battery then tries each
`∀ v, Φⱼ v`, a proved obligation is discharged, and the final statement is
checked again.

Refused (a `generalisation` row with status `refused` and a reason): a
statement that is ill-typed once `L` is abstracted (the literal fixes a
dependent type), a proof that becomes a single obligation (the generalisation
would restate the theorem), obligations that pin `v` to `L` (the battery
proves `Φ₁ v → ⋯ → v = L`), and anything past the per-literal check or
heartbeat budget. An accepted generalisation is added to the environment
(checked by the kernel on the way in) and is a producer like a weakened
theorem.
-/

/-- A numeral `@OfNat.ofNat τ n _` of ℕ, ℤ, ℚ or ℝ with `n ≥ 2`, and one
occurrence of it as a term. -/
structure Literal where
  type : Expr
  value : Nat
  term : Expr

def literalTypeNames : List Name := [``Nat, ``Int, `Rat, `Real]

def literalOf? (e : Expr) : Option Literal :=
  if e.isAppOfArity ``OfNat.ofNat 3 then
    match e.appFn!.appFn!.appArg!, e.appFn!.appArg! with
    | .const c [], .lit (.natVal n) =>
        if literalTypeNames.contains c && n ≥ 2 then some ⟨.const c [], n, e⟩ else none
    | _, _ => none
  else none

def isLiteralOf (l : Literal) (e : Expr) : Bool :=
  match literalOf? e with
  | some m => m.value == l.value && m.type == l.type
  | none => false

def literalTypeName (l : Literal) : String :=
  match l.type with
  | .const c _ => c.toString
  | _ => "?"

partial def collectLiterals (e : Expr) : StateM (Array Literal × Std.HashSet Expr) Unit := do
  if (← get).2.contains e then return
  modify fun (found, seen) => (found, seen.insert e)
  if let some l := literalOf? e then
    modify fun (found, seen) =>
      (if found.any (fun m => m.value == l.value && m.type == l.type) then found else found.push l, seen)
    return
  match e with
  | .app f a => do collectLiterals f; collectLiterals a
  | .lam _ t b _ => do collectLiterals t; collectLiterals b
  | .forallE _ t b _ => do collectLiterals t; collectLiterals b
  | .letE _ t v b _ => do collectLiterals t; collectLiterals v; collectLiterals b
  | .mdata _ b => collectLiterals b
  | .proj _ _ b => collectLiterals b
  | _ => pure ()

/-- The distinct numerals of `e`, in order of first occurrence. -/
def literalsOf (e : Expr) : Array Literal :=
  (Id.run ((collectLiterals e).run (#[], {}))).2.1

def containsLiteral (l : Literal) (e : Expr) : Bool :=
  (e.find? (isLiteralOf l)).isSome

def abstractLiteral (l : Literal) (v : Expr) (e : Expr) : Expr :=
  e.replace fun sub => if isLiteralOf l sub then some v else none

structure GenState where
  /-- Obligation placeholders and their propositions (which mention `v`). -/
  holes : Array (Name × Expr) := #[]
  checks : Nat := 0
  exceeded : Bool := false
  /-- Wall-clock deadline (ms) for this literal's checks: kernel time is not
  counted by the heartbeat budget. -/
  deadline : Nat := 0

abbrev GenM := StateT GenState MetaM

/-- Kernel check of `term : type`, both closed apart from `v` and obligation
placeholders, as `λ v h₁ … hₖ, term : ∀ v h₁ … hₖ, type`. At most 96 checks
per literal. -/
def genCheck (v : Expr) (levelParams : List Name) (kernelHeartbeats : Nat) (term type : Expr) :
    GenM Bool := do
  let s ← get
  if s.checks ≥ 96 || (s.deadline > 0 && (← IO.monoMsNow) > s.deadline) then
    set { s with exceeded := true }
    return false
  set { s with checks := s.checks + 1 }
  let used := term.getUsedConstants
  let holes := s.holes.filter fun (n, _) => used.contains n
  let decls := holes.map fun (n, t) => (n, fun (_ : Array Expr) => (pure t : GenM Expr))
  withLocalDeclsD decls fun hs => do
    let term' := term.replace fun sub => match sub with
      | .const n _ => (holes.findIdx? (·.1 == n)).map fun j => hs[j]!
      | _ => none
    let value ← instantiateMVars (← mkLambdaFVars (#[v] ++ hs) term')
    let ty ← instantiateMVars (← mkForallFVars (#[v] ++ hs) type)
    if value.hasFVar || value.hasMVar || ty.hasFVar || ty.hasMVar then return false
    return (← kernelVerdict ty value levelParams kernelHeartbeats).isNone

/-- The placeholder of the obligation `type` (one per distinct proposition). -/
def newObligation (type : Expr) : GenM Expr := do
  let s ← get
  if let some (n, _) := s.holes.find? (·.2 == type) then return mkConst n
  let n ← mkFreshUserName `_plectis_literal_obligation
  modify fun s => { s with holes := s.holes.push (n, type) }
  return mkConst n

/-- The term standing for a cut subterm of proposition `type`. A certificate
proposition (`decide p = true`, which `decide` wraps in `id`; `p = True` or
`p = False` from `simp`) becomes an obligation stating `p` (or `¬p`), turned
back into the certificate by `decide_eq_true`, `eq_true` or `eq_false`: the
obligation says what the proof step established, and a certificate of the
statement itself is then recognised as vacuous. -/
def obligationTerm (type : Expr) : GenM Expr := do
  let t := type.consumeMData
  if t.isAppOfArity ``Eq 3 then
    let lhs := t.appFn!.appArg!
    let rhs := t.appArg!
    if rhs.isConstOf ``Bool.true && lhs.isAppOfArity ``Decidable.decide 2 then
      let p := lhs.appFn!.appArg!
      return mkApp3 (mkConst ``decide_eq_true) p lhs.appArg! (← newObligation p)
    if rhs.isConstOf ``True then
      return mkApp2 (mkConst ``eq_true) lhs (← newObligation lhs)
    if rhs.isConstOf ``False then
      return mkApp2 (mkConst ``eq_false) lhs (← newObligation (mkNot lhs))
  newObligation type

/-- What the repair of one literal needs. -/
structure GenCtx where
  lit : Literal
  v : Expr
  levelParams : List Name
  kernelHeartbeats : Nat
  /-- Key of the statement with the literal abstracted: a subterm proving it
  is repaired in place, never cut (the cut would restate the theorem). -/
  statementKey : String

mutual
/-- The closed proof `s` of `type'` (the literal abstracted in both): `s`
abstracted when the kernel accepts that, else `s` rebuilt from its repaired
maximal closed proof subterms when that is accepted; `none` otherwise. -/
partial def repairAt (ctx : GenCtx) (s type' : Expr) : GenM (Option Expr) := do
  let uniform := abstractLiteral ctx.lit ctx.v s
  if ← genCheck ctx.v ctx.levelParams ctx.kernelHeartbeats uniform type' then return some uniform
  if (← get).exceeded then return none
  let rebuilt ← rebuildTerm ctx s true
  if rebuilt != uniform then
    if ← genCheck ctx.v ctx.levelParams ctx.kernelHeartbeats rebuilt type' then return some rebuilt
  return none

/-- A maximal closed proof subterm `c` of the proof: kept as it is when its
proposition does not mention the literal, abstracted when the kernel accepts
that, repaired in place when it proves the whole statement, and otherwise cut
whole into an obligation stating its proposition. Cutting the largest failing
subterm gives the weakest obligation, and the proposition an author wrote
(`5 < v` for a `decide` or `norm_num` step) rather than a certificate inside
it (`decide (5 < v) = true`). -/
partial def repairChild (ctx : GenCtx) (c : Expr) : GenM Expr := do
  let type ← instantiateMVars (← inferType c)
  unless containsLiteral ctx.lit type do return c
  let type' := abstractLiteral ctx.lit ctx.v type
  if keyOf type' == ctx.statementKey then
    if let some r ← repairAt ctx c type' then return r
    return ← obligationTerm type'
  let uniform := abstractLiteral ctx.lit ctx.v c
  if ← genCheck ctx.v ctx.levelParams ctx.kernelHeartbeats uniform type' then return uniform
  obligationTerm type'

/-- `e` with the literal abstracted and every maximal closed proof subterm
(other than `e` itself when `top`) replaced by `repairChild`. An application
is taken apart into its head and its arguments, never into partial
applications: a closed prefix `@Eq.rec _ 93 motive h₀` has a lemma-shaped type
(`∀ {a}, 93 = a → P a`), and cutting it would restate the theorem. -/
partial def rebuildTerm (ctx : GenCtx) (e : Expr) (top : Bool) : GenM Expr := do
  if isLiteralOf ctx.lit e then return ctx.v
  if !top && !e.hasLooseBVars then
    let proof ← try isProp (← inferType e) catch _ => pure false
    if proof then return ← repairChild ctx e
    unless containsLiteral ctx.lit e do return e
  let r := rebuildTerm ctx
  match e with
  | .app .. => return mkAppN (← r e.getAppFn false) (← e.getAppArgs.mapM (r · false))
  | .lam n t b bi => return .lam n (← r t false) (← r b false) bi
  | .forallE n t b bi => return .forallE n (← r t false) (← r b false) bi
  | .letE n t x b nd => return .letE n (← r t false) (← r x false) (← r b false) nd
  | .mdata m b => return .mdata m (← r b top)
  | .proj sn i b => return .proj sn i (← r b false)
  | e => return e
end

structure Generalisation where
  status : String := "refused"
  reason : String := ""
  uniform : Bool := false
  type : Expr := mkConst ``True
  value : Expr := mkConst ``True.intro
  obligations : Array Json := #[]
  discharged : Array Json := #[]
  /-- A value other than the literal at which every remaining obligation was
  proved (empty when none remained). -/
  witness : String := ""

/-- Values tried as witnesses of generality for the literal `n`. -/
def witnessCandidates (n : Nat) : List Nat :=
  let raw := [n + 1, n + 2, 2 * n, n + 7] ++ (if n ≥ 3 then [n - 1] else [])
  raw.foldl (fun acc w => if acc.contains w || w == n then acc else acc ++ [w]) []

/-- The numeral `w` of type `type` (ℕ, ℤ, ℚ or ℝ). -/
def numeralOf (type : Expr) (w : Nat) : MetaM Expr :=
  if type.isConstOf ``Nat then pure (mkNatLit w) else mkNumeral type w

/-- Generalise the literal `l` of theorem `info`, as described above. -/
def generaliseLiteral (cfg : Config) (env : Environment) (info : ConstantInfo) (l : Literal) :
    Elab.TermElabM Generalisation := do
  let some value := info.value? | return { reason := "no_value" }
  let lp := info.levelParams
  let khb := cfg.kernelHeartbeats
  withLocalDeclD `v l.type fun v => do
    let statement := abstractLiteral l v info.type
    unless containsLiteral l info.type do return { reason := "literal_not_in_statement" }
    unless ← isTypeCorrect (← mkForallFVars #[v] statement) do
      return { reason := "statement_ill_typed" }
    let ctx : GenCtx := { lit := l, v, levelParams := lp, kernelHeartbeats := khb,
                          statementKey := keyOf statement }
    let (root?, st) ← (repairAt ctx value statement).run { deadline := (← IO.monoMsNow) + 30000 }
    if st.exceeded then return { reason := "check_cap" }
    let some root := root? | return { reason := "not_generalisable" }
    let usedNames := root.getUsedConstants
    let mut holes := st.holes.filter fun (n, _) => usedNames.contains n
    -- Vacuous: the proof is an obligation applied to arguments, or an
    -- obligation states the whole statement.
    if let .const n _ := (stripLambdas root).getAppFn then
      if holes.any (·.1 == n) then return { reason := "vacuous" }
    if holes.any (fun (_, t) => keyOf t == ctx.statementKey) then return { reason := "vacuous" }
    let uniform := holes.isEmpty
    -- Discharge the obligations the battery proves for every v.
    let mut term := root
    let mut discharged : Array Json := #[]
    let mut kept : Array (Name × Expr) := #[]
    for (n, phi) in holes do
      let closed ← mkForallFVars #[v] phi
      let tactics := (standardTactics ++ cfg.extraTactics).map fun t => (t, t)
      match ← runTactics cfg env closed tactics (cfg.groundHeartbeats * 4) khb (wantProof := true) with
      | some (label, pf) =>
          term := term.replace fun sub => match sub with
            | .const m _ => if m == n then some (mkApp pf v) else none
            | _ => none
          discharged := discharged.push <| Json.mkObj [
            ("type", toJson (← render phi)), ("closed_key", toJson (keyOf closed)),
            ("tactic", toJson label)]
      | none => kept := kept.push (n, phi)
    holes := kept
    -- The final statement, checked by the kernel.
    let decls := holes.map fun (n, t) => (n, fun (_ : Array Expr) => (pure t : Elab.TermElabM Expr))
    let result ← withLocalDeclsD decls fun hs => do
      let term' := term.replace fun sub => match sub with
        | .const n _ => (holes.findIdx? (·.1 == n)).map fun j => hs[j]!
        | _ => none
      let finalValue ← instantiateMVars (← mkLambdaFVars (#[v] ++ hs) term')
      let finalType ← instantiateMVars (← mkForallFVars (#[v] ++ hs) statement)
      if finalValue.hasFVar || finalValue.hasMVar || finalType.hasFVar || finalType.hasMVar then
        return none
      if let some _ ← kernelVerdict finalType finalValue lp khb then return none
      -- Obligations that pin v to the literal make the generalisation a restatement.
      if !hs.isEmpty then
        let pinned ← mkForallFVars (#[v] ++ hs) (← mkEq v l.term)
        let pinTactics := ["omega", "decide", "norm_num", "simp_all", "linarith"].map fun t => (t, t)
        if (← tryTactics cfg env pinned pinTactics (cfg.groundHeartbeats * 4) khb).isSome then
          return some (finalType, finalValue, true)
      return some (finalType, finalValue, false)
    let some (finalType, finalValue, pinned) := result | return { reason := "kernel_rejected" }
    if pinned then return { reason := "pinned" }
    let mut obligations : Array Json := #[]
    for (_, phi) in holes do
      let closed ← mkForallFVars #[v] phi
      obligations := obligations.push <| Json.mkObj [
        ("type", toJson (← render phi)), ("closed_key", toJson (keyOf closed))]
    -- An obligation that is the statement up to unfolding is a restatement.
    for (_, phi) in holes do
      if let .ok true ← budgeted 2000 (withNewMCtxDepth (isDefEq phi statement)) then
        return { reason := "vacuous", obligations }
    -- Witnessed generality: with obligations left, some value other than the
    -- literal must satisfy all of them (each instance a kernel-checked proof),
    -- or they may pin v to the literal in substance ((1 / v).den = 21) and the
    -- generalisation is refused.
    let mut witness : Option Nat := none
    if !holes.isEmpty then
      let tactics := ["decide", "norm_num", "simp", "omega"].map fun t => (t, t)
      for w in witnessCandidates l.value do
        let some wTerm ← (try some <$> numeralOf l.type w catch _ => pure none) | continue
        let mut all := true
        for (_, phi) in holes do
          if (← runTactics cfg env (phi.replaceFVar v wTerm) tactics (cfg.groundHeartbeats * 2) khb).isNone then
            all := false
            break
        if all then
          witness := some w
          break
      if witness.isNone then return { reason := "unwitnessed", obligations }
    return { status := "generalised", uniform, type := finalType, value := finalValue,
             obligations, discharged, witness := (witness.map toString).getD "" }

/-- Add a generalised theorem under a derived name; the kernel checks it on
the way in. -/
def addGeneralised (info : ConstantInfo) (k : Nat) (type value : Expr) : MetaM (Except String Name) := do
  let name := info.name ++ Name.mkSimple s!"_argument_generalisation_{k}"
  let decl := Declaration.thmDecl { name, levelParams := info.levelParams, type, value }
  match (← getEnv).addDeclCore 0 decl none with
  | .ok env =>
      setEnv env
      return .ok name
  | .error ex => return .error (clip (← (ex.toMessageData (← getOptions)).toString) 400)

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
    ("focus_declarations", toJson (cfg.focusDeclarations.map Name.toString)),
    ("coverage_scope", toJson (if cfg.focusDeclarations.isEmpty then "selected_corpus" else "focused_declarations")),
    ("used_consequences_v2", toJson cfg.usedConsequencesV2),
    ("library_producers", toJson cfg.libraryProducers),
    ("relaxed_producer_filter", toJson cfg.relaxedProducerFilter),
    ("unfold_predicates", toJson cfg.unfoldPredicates),
    ("extra_tactics", toJson cfg.extraTactics),
    ("nat_refute_budget_ms", toJson cfg.natRefuteBudgetMs),
    ("ground_budget_ms", toJson cfg.groundBudgetMs),
    ("ground_heartbeats_thousands", toJson cfg.groundHeartbeats),
    ("ground_max_size", toJson cfg.groundMaxSize),
    ("generalise_budget_ms", toJson cfg.generaliseBudgetMs),
    ("kernel_heartbeats_thousands", toJson cfg.kernelHeartbeats),
    ("match_heartbeats_thousands", toJson cfg.matchHeartbeats),
    ("max_candidates", toJson cfg.maxCandidates),
    ("max_statements", toJson cfg.maxStatements),
    ("time_budget_ms", toJson cfg.timeBudgetMs)]
  -- Pass 1: telescopes.
  let mut state : State := {}
  let mut weakenCandidates : Array (Name × Nat × String) := #[]
  let mut theoremCount := 0
  let mut consumerCount : Std.HashMap String Nat := {}
  let mut hasProducer : Std.HashSet String := {}
  let mut names : Array Name := #[]
  for (name, info) in env.constants.toList do
    if selected cfg env name && !generatedTheorem name &&
        (cfg.focusDeclarations.isEmpty || cfg.focusDeclarations.contains name) then
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
        for row in rows do
          if (row.getObjValAs? String "kind").toOption == some "hypothesis" then
            if let .ok key := row.getObjValAs? String "key" then
              if let .ok i := row.getObjValAs? Nat "i" then
                weakenCandidates := weakenCandidates.push (name, i, key)
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
  -- Pass 1b: what each proof uses of each closed hypothesis, the hypotheses
  -- most consumed across the corpus (named inputs) first.
  let weakenStart ← IO.monoMsNow
  let ordered := weakenCandidates.qsort fun a b =>
    consumerCount.getD a.2.2 0 > consumerCount.getD b.2.2 0 ||
      (consumerCount.getD a.2.2 0 == consumerCount.getD b.2.2 0 && a.1.toString < b.1.toString)
  let mut weakened : Array Name := #[]
  let mut weakenTried := 0
  let mut weakenRejected := 0
  let mut weakenTruncated := false
  let mut consequenceKeys : Std.HashSet String := {}
  for (name, i, hKey) in ordered do
    if (← IO.monoMsNow) - weakenStart > cfg.weakenBudgetMs then
      weakenTruncated := true
      break
    let some info := (← getEnv).find? name | continue
    weakenTried := weakenTried + 1
    -- A budget or runtime failure, and a V2 rejection other than "no
    -- admissible use site", is recorded as an attempt: failure, timeout and
    -- absence are different observations.
    let result ← budgeted 400000 (weakenEither cfg info i)
    let mut found : Option Weakening := none
    match result with
    | .ok (.ok w) => found := some w
    | .ok (.error reason) =>
        if ["vacuous", "exceeded", "open_term", "placeholder_left"].contains reason then
          emit stream <| Json.mkObj [("record", "weakening_attempt"), ("theorem", toJson name.toString),
            ("i", toJson i), ("status", toJson reason)]
    | .error reason =>
        emit stream <| Json.mkObj [("record", "weakening_attempt"), ("theorem", toJson name.toString),
          ("i", toJson i), ("status", toJson reason)]
    let some w := found | continue
    let mut consequenceRows : Array Json := #[]
    for c in w.consequences, via in w.via, sites in w.sites, implied in w.implied do
      consequenceRows := consequenceRows.push <| Json.mkObj [
        ("key", toJson (keyOf c)), ("type", toJson (← render c)),
        ("via", toJson via), ("sites", toJson sites),
        ("implication_kernel_checked", toJson implied)]
    let verdict ← addWeakened info i w.type w.value
    emit stream <| Json.mkObj [
      ("record", "weakening"), ("theorem", toJson name.toString), ("i", toJson i),
      ("hypothesis", toJson hKey), ("hypothesis_type", toJson (← render w.hypothesis)),
      ("consequences", Json.arr consequenceRows),
      ("weakened", toJson (match verdict with | .ok n => n.toString | .error _ => "")),
      ("type", toJson (← render w.type)),
      ("kernel_checked", toJson verdict.isOk),
      ("kernel_error", toJson (match verdict with | .ok _ => "" | .error e => e))]
    match verdict with
    | .error _ => weakenRejected := weakenRejected + 1
    | .ok synthetic =>
        weakened := weakened.push synthetic
        for c in w.consequences do
          state := enqueue state c "consequence"
          state := { state with antecedents := state.antecedents.insert (keyOf c) }
          consumerCount := consumerCount.insert (keyOf c) (consumerCount.getD (keyOf c) 0 + 1)
          consequenceKeys := consequenceKeys.insert (keyOf c)
  let weakenEnd ← IO.monoMsNow
  -- Pass 1c (opt-in): literal generalisation, smallest statements first. An
  -- accepted generalisation is a producer like a weakened theorem.
  let generaliseStart ← IO.monoMsNow
  let mut generalised : Array Name := #[]
  let mut genTheorems := 0
  let mut genLiterals := 0
  let mut genUniform := 0
  let mut genObligations := 0
  let mut genDischarged := 0
  let mut genRefused := 0
  let mut genRejected := 0
  let mut genTruncated := false
  if cfg.generaliseBudgetMs > 0 then
    let mut work : Array (Nat × String × Name) := #[]
    for name in names do
      let some info := env.find? name | continue
      if (literalsOf info.type).isEmpty then continue
      work := work.push (sizeUpTo 100000 info.type, name.toString, name)
    work := work.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
    for (_, _, name) in work do
      if (← IO.monoMsNow) - generaliseStart > cfg.generaliseBudgetMs then
        genTruncated := true
        break
      let some info := (← getEnv).find? name | continue
      let some value := info.value? | continue
      genTheorems := genTheorems + 1
      let lits := (literalsOf info.type).extract 0 3
      let tooLarge := sizeUpTo 20000 value > 20000
      for l in lits, k in [0:lits.size] do
        if (← IO.monoMsNow) - generaliseStart > cfg.generaliseBudgetMs then
          genTruncated := true
          break
        genLiterals := genLiterals + 1
        let head : List (String × Json) := [
          ("record", "generalisation"), ("theorem", toJson name.toString),
          ("literal", toJson (toString l.value)), ("literal_type", toJson (literalTypeName l))]
        let g : Generalisation ←
          if tooLarge then pure { reason := "proof_too_large" }
          else match ← budgetedTerm cfg.generaliseHeartbeats (generaliseLiteral cfg env info l) with
            | .ok g => pure g
            | .error reason => pure { reason := reason }
        modifyThe Core.State fun st => { st with messages := {} }
        if g.status != "generalised" then
          genRefused := genRefused + 1
          emit stream <| Json.mkObj (head ++ [("status", toJson "refused"), ("reason", toJson g.reason)] ++
            (if g.obligations.isEmpty then [] else [("obligations", Json.arr g.obligations)]) ++
            [("kernel_checked", toJson false)])
          continue
        let verdict ← addGeneralised info k g.type g.value
        emit stream <| Json.mkObj (head ++ [
          ("status", toJson "generalised"), ("uniform", toJson g.uniform), ("witness", toJson g.witness),
          ("generalised", toJson (match verdict with | .ok n => n.toString | .error _ => "")),
          ("type", toJson (← render g.type)), ("key", toJson (keyOf g.type)),
          ("obligations", Json.arr g.obligations), ("discharged", Json.arr g.discharged),
          ("kernel_checked", toJson verdict.isOk),
          ("kernel_error", toJson (match verdict with | .ok _ => "" | .error e => e))])
        match verdict with
        | .error _ => genRejected := genRejected + 1
        | .ok synthetic =>
            generalised := generalised.push synthetic
            if g.uniform then genUniform := genUniform + 1
            genObligations := genObligations + g.obligations.size
            genDischarged := genDischarged + g.discharged.size
  let generaliseEnd ← IO.monoMsNow
  -- The search budget runs from the start, less the used-consequence and
  -- generalisation passes, which have their own.
  let searchBase := startMs + (weakenEnd - weakenStart) + (generaliseEnd - generaliseStart)
  let env ← getEnv
  let producers := producerIndex cfg env (weakened ++ generalised)
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
    if (← IO.monoMsNow) - searchBase > cfg.timeBudgetMs then
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
    -- `is_false` is written only on the statement `False` itself, read off
    -- the term rather than its rendering.
    let falseMark : List (String × Json) :=
      if statement.consumeMData.isConstOf ``False then [("is_false", toJson true)] else []
    emit stream <| Json.mkObj <|
      [("record", toJson "statement"), ("key", toJson key), ("origin", toJson origin)] ++ falseMark ++
      [("type", toJson (← render statement)), ("constants", toJson (corpusConstants cfg env statement))]
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
    if (← IO.monoMsNow) - searchBase > cfg.timeBudgetMs then
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
  for name in names ++ weakened do
    if (← IO.monoMsNow) - searchBase > cfg.timeBudgetMs + 1200000 then
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
  -- Ground tier: small ground statements and `Nonempty T` statements, every
  -- discovered one whatever its producers, most-consumed first and then the
  -- smallest, before the consumer-ordered battery.
  let groundStart ← IO.monoMsNow
  let mut batteryDone : Std.HashSet String := {}
  let mut groundCandidates : Array (Nat × Nat × Nat × Expr × String) := #[]
  let mut queueIndex := 0
  for (statement, _) in state.queue do
    queueIndex := queueIndex + 1
    if cfg.groundBudgetMs == 0 then break
    let key := keyOf statement
    if state.direct.contains key then continue
    let kind := match ← budgeted 2000 (groundKind cfg statement) with
      | .ok (some kind) => kind
      | _ => ""
    if kind.isEmpty then continue
    groundCandidates := groundCandidates.push
      (consumerCount.getD key 0, sizeUpTo cfg.groundMaxSize statement, queueIndex, statement, kind)
  groundCandidates := groundCandidates.qsort fun a b =>
    a.1 > b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2.1 < b.2.2.1)))
  let mut groundTried := 0
  let mut groundClosed := 0
  let mut groundRefuted := 0
  let mut groundNonempty := 0
  let mut groundTruncated := false
  for (_, _, _, statement, kind) in groundCandidates do
    if (← IO.monoMsNow) - groundStart > cfg.groundBudgetMs then
      groundTruncated := true
      break
    let key := keyOf statement
    if batteryDone.contains key then continue
    groundTried := groundTried + 1
    if kind == "nonempty" then
      -- An inhabitant or nothing: a failed search is never a refutation.
      if let some label ← tryTactics cfg env statement nonemptyTactics cfg.groundHeartbeats
          cfg.kernelHeartbeats then
        groundClosed := groundClosed + 1
        groundNonempty := groundNonempty + 1
        batteryDone := batteryDone.insert key
        emit stream <| Json.mkObj [
          ("record", "battery"), ("statement", toJson key), ("tactic", toJson label),
          ("kernel_checked", toJson true), ("tier", toJson "ground")]
      continue
    for tactic in groundTactics do
      if let some label ← tryTactics cfg env statement [(tactic, tactic)] cfg.groundHeartbeats
          cfg.kernelHeartbeats then
        groundClosed := groundClosed + 1
        batteryDone := batteryDone.insert key
        emit stream <| Json.mkObj [
          ("record", "battery"), ("statement", toJson key), ("tactic", toJson label),
          ("kernel_checked", toJson true), ("tier", toJson "ground")]
        break
      if let some label ← tryTactics cfg env (mkNot statement) [(tactic, tactic)] cfg.groundHeartbeats
          cfg.kernelHeartbeats then
        groundRefuted := groundRefuted + 1
        batteryDone := batteryDone.insert key
        emit stream <| Json.mkObj [
          ("record", "battery_refutation"), ("statement", toJson key), ("tactic", toJson label),
          ("kernel_checked", toJson true), ("tier", toJson "ground")]
        break
  -- Pass 4: the tactic battery on open leaves, most-consumed first.
  let batteryStart ← IO.monoMsNow
  -- A leaf is a searched statement with no residual-free producer: a
  -- conditional producer supplies nothing until its residuals are supplied,
  -- and in a cycle (the two sides of a proved equivalence, say) every member
  -- has one, so skipping such statements left whole cycles untried. Among
  -- statements with as many consumers, those with no usable producer at all
  -- still go first, then the order of discovery.
  -- A used consequence always has a producer (the lemma at its use site
  -- proves it from the hypothesis), so it is a leaf whatever the search found,
  -- and it goes first: a consequence the battery proves makes a conditional
  -- theorem unconditional. Consequences get their own time (half the
  -- used-consequence budget), and the ordinary leaves keep the whole battery
  -- budget, counted from the first ordinary leaf.
  let mut ranked : Array (Nat × Nat × Nat × Expr) := #[]
  let mut conditionalLeaves := 0
  queueIndex := 0
  for (statement, _) in state.queue.extract 0 cursor do
    queueIndex := queueIndex + 1
    let key := keyOf statement
    if batteryDone.contains key then continue
    if consequenceKeys.contains key then
      ranked := ranked.push (consumerCount.getD key 0 + 1000000000, 0, queueIndex, statement)
    else unless state.direct.contains key do
      let conditional := hasProducer.contains key
      if conditional then conditionalLeaves := conditionalLeaves + 1
      ranked := ranked.push (consumerCount.getD key 0, if conditional then 1 else 0, queueIndex, statement)
  ranked := ranked.qsort fun a b =>
    a.1 > b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2.1 < b.2.2.1)))
  let leaves : Array (Nat × Expr) := ranked.map fun (priority, _, _, statement) => (priority, statement)
  let consequenceBudgetMs := cfg.weakenBudgetMs / 2
  let mut batteryTried := 0
  let mut batteryConsequences := 0
  let mut batteryClosed := 0
  let mut batteryRefuted := 0
  let mut triedKeys : Std.HashSet String := {}
  let mut ordinaryStart? : Option Nat := none
  for (_, statement) in leaves do
    let key := keyOf statement
    let now ← IO.monoMsNow
    if consequenceKeys.contains key then
      if now - batteryStart > consequenceBudgetMs then continue
      batteryConsequences := batteryConsequences + 1
    else
      if ordinaryStart?.isNone then ordinaryStart? := some now
      if now - ordinaryStart?.getD now > cfg.batteryBudgetMs then break
    batteryTried := batteryTried + 1
    triedKeys := triedKeys.insert key
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
  -- Optional bounded counterexample search on leading-ℕ leaves the battery
  -- left open, with its own wall-clock budget.
  let natRefuteStart ← IO.monoMsNow
  let mut natRefuteTried := 0
  let mut natRefuted := 0
  if cfg.natRefuteBudgetMs > 0 then
    for (_, statement) in leaves do
      if (← IO.monoMsNow) - natRefuteStart > cfg.natRefuteBudgetMs then break
      let key := keyOf statement
      if batteryDone.contains key then continue
      let leadingNat := match statement.consumeMData with
        | .forallE _ d _ _ => d.isConstOf ``Nat
        | _ => false
      unless leadingNat do continue
      natRefuteTried := natRefuteTried + 1
      match ← tryNatCounterexample cfg statement (natRefuteStart + cfg.natRefuteBudgetMs) with
      | some (n, label) =>
          natRefuted := natRefuted + 1
          batteryDone := batteryDone.insert key
          emit stream <| Json.mkObj [("record", "battery_refutation"), ("statement", toJson key),
            ("tactic", toJson s!"{label} at {n}"), ("kernel_checked", toJson true),
            ("counterexample_nat", toJson n)]
      | none =>
          emit stream <| Json.mkObj [("record", "counterexample_attempt"), ("statement", toJson key),
            ("status", "unknown_no_checked_witness"), ("tested_prefix_bound", toJson (16 : Nat))]
  -- Library search on the most-consumed leaves the battery left open: a leaf
  -- that is a single library lemma is not an open question.
  -- Used consequences first again, with half the leaves and half the time of
  -- their own; the ordinary leaves keep the whole allowance.
  let deepStart ← IO.monoMsNow
  let mut deepTried := 0
  let mut deepConsequences := 0
  let mut deepOrdinary := 0
  let mut deepClosed := 0
  let mut ordinaryDeepStart? : Option Nat := none
  for (_, statement) in leaves do
    let key := keyOf statement
    unless triedKeys.contains key do continue
    if batteryDone.contains key then continue
    let now ← IO.monoMsNow
    if consequenceKeys.contains key then
      if deepConsequences ≥ cfg.deepLeaves / 2 || now - deepStart > cfg.deepBudgetMs / 2 then continue
      deepConsequences := deepConsequences + 1
    else
      if ordinaryDeepStart?.isNone then ordinaryDeepStart? := some now
      if deepOrdinary ≥ cfg.deepLeaves || now - ordinaryDeepStart?.getD now > cfg.deepBudgetMs then break
      deepOrdinary := deepOrdinary + 1
    deepTried := deepTried + 1
    if let some label ← tryBattery cfg env statement ["exact?"] then
      deepClosed := deepClosed + 1
      emit stream <| Json.mkObj [
        ("record", "battery"), ("statement", toJson (keyOf statement)),
        ("tactic", toJson label), ("kernel_checked", toJson true)]
  emit stream <| Json.mkObj [
    ("record", "summary"), ("theorems", toJson theoremCount),
    ("ground_candidates", toJson groundCandidates.size),
    ("ground_tried", toJson groundTried),
    ("ground_closed", toJson groundClosed),
    ("ground_nonempty_closed", toJson groundNonempty),
    ("ground_refuted", toJson groundRefuted),
    ("ground_truncated", toJson groundTruncated),
    ("battery_leaves", toJson leaves.size),
    ("battery_conditional_leaves", toJson conditionalLeaves),
    ("battery_tried", toJson batteryTried),
    ("battery_consequences_tried", toJson batteryConsequences),
    ("battery_closed", toJson batteryClosed),
    ("battery_refuted", toJson batteryRefuted),
    ("nat_refute_tried", toJson natRefuteTried),
    ("nat_refuted", toJson natRefuted),
    ("library_search_tried", toJson deepTried),
    ("library_search_consequences_tried", toJson deepConsequences),
    ("library_search_closed", toJson deepClosed),
    ("compositions", toJson compositions),
    ("kernel_checked_compositions", toJson checkedCompositions),
    ("idle_theorems", toJson idleTheorems),
    ("idle_kernel_checked", toJson idleChecked),
    ("idle_truncated", toJson idleTruncated),
    ("weakening_tried", toJson weakenTried),
    ("weakened_theorems", toJson weakened.size),
    ("weakening_rejected", toJson weakenRejected),
    ("weakening_consequences", toJson consequenceKeys.size),
    ("weakening_truncated", toJson weakenTruncated),
    ("weakening_ms", toJson (weakenEnd - weakenStart)),
    ("generalisation_theorems", toJson genTheorems),
    ("generalisation_literals", toJson genLiterals),
    ("generalised", toJson generalised.size),
    ("generalised_uniform", toJson genUniform),
    ("generalisation_obligations", toJson genObligations),
    ("generalisation_discharged", toJson genDischarged),
    ("generalisation_refused", toJson genRefused),
    ("generalisation_rejected", toJson genRejected),
    ("generalisation_truncated", toJson genTruncated),
    ("generalise_ms", toJson (generaliseEnd - generaliseStart)),
    ("statements_discovered", toJson state.queue.size),
    ("statements_searched", toJson state.processed),
    ("matches", toJson state.matchCount),
    ("budget_exhausted_attempts", toJson state.exhausted),
    ("truncated", toJson state.truncated),
    ("elapsed_ms", toJson ((← IO.monoMsNow) - startMs)),
    ("search_ms", toJson (searchEnd - generaliseEnd)),
    ("telescope_ms", toJson (weakenStart - startMs)),
    ("composition_ms", toJson (idleStart - searchEnd)),
    ("idle_ms", toJson (groundStart - idleStart)),
    ("ground_ms", toJson (batteryStart - groundStart)),
    ("battery_ms", toJson (deepStart - batteryStart)),
    ("library_search_ms", toJson ((← IO.monoMsNow) - deepStart)),
    ("producer_relation", "lower_bound_prefiltered_by_conclusion_constants")]
  stream.flush

end ArgumentContinuationExport

-- @@TEST_DECLARATIONS@@

set_option maxHeartbeats 0 in
run_cmd liftTermElabM ArgumentContinuationExport.exportAll
