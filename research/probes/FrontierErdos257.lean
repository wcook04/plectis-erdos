import Lean
import Erdos249257.AdelicHeightObstruction
import Erdos249257.BooleanMobiusCriticalCapacityCofinal
import Erdos249257.BooleanMobiusExactRowCrossing
import Erdos249257.BooleanMobiusExactRowDoubling
import Erdos249257.BooleanMobiusGreedyReduction
import Erdos249257.BooleanMobiusLocalRepair
import Erdos249257.BooleanMobiusSkipRow
import Erdos249257.BooleanMobiusSkipRowCofinal
import Erdos249257.CertificateKernel
import Erdos249257.CofinalStripReturn
import Erdos249257.DyadicPrefixCompression
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCarryReachability
import Erdos249257.HalfCutLocator
import Erdos249257.HalfCylinderFullShellSeamBridge
import Erdos249257.HalfCylinderLargestSkipInduction
import Erdos249257.HalfCylinderMiddleCarryLowerBound
import Erdos249257.HalfCylinderSkippedEndpointClassifier
import Erdos249257.HalfTrappingReturnCarry
import Erdos249257.HalfUpperResetCriticalBand
import Erdos249257.RationalSupportCarrySkeleton
import Erdos249257.SuffixCylinderTerminalOnlyBridge
import Erdos249257.TwentyOneQuotientGreedy
import ErdosProblems.Erdos257.PaperCompleteR20.CarryCollapseCorrespondence
import ErdosProblems.Erdos257.PaperCompleteR20.GeneralRepairCorrespondence
import ErdosProblems.Erdos257.PaperCompleteR20.QuotientRowReal
import ErdosProblems.Erdos257.PaperCompleteR21.ArithmeticCounterexampleAssembly
import ErdosProblems.Erdos257.PaperCompleteR21.BalancedPulseFanOutCount
import ErdosProblems.Erdos257.PaperCompleteR21.BranchCellHorizonExclusions
import ErdosProblems.Erdos257.PaperCompleteR21.CentredCompletionAndDecisionBoundary
import ErdosProblems.Erdos257.PaperCompleteR21.CompatibleFiniteRowFamily
import ErdosProblems.Erdos257.PaperCompleteR21.DenominatorBudget
import ErdosProblems.Erdos257.PaperCompleteR21.DyadicBandAndTwoSidedBounds
import ErdosProblems.Erdos257.PaperCompleteR21.EventualNonnegativeMargin
import ErdosProblems.Erdos257.PaperCompleteR21.ExactRowDichotomyCountermodels
import ErdosProblems.Erdos257.PaperCompleteR21.FeedbackRowStripWitnessAllDepths
import ErdosProblems.Erdos257.PaperCompleteR21.GreedyGapCriteria
import ErdosProblems.Erdos257.PaperCompleteR21.GreedyOrbitNoTies
import ErdosProblems.Erdos257.PaperCompleteR21.LinearChannelAndMiddleCellExclusion
import ErdosProblems.Erdos257.PaperCompleteR21.LogarithmicInitialInterval
import ErdosProblems.Erdos257.PaperCompleteR21.MersenneChannelSurvivalAllHeights
import ErdosProblems.Erdos257.PaperCompleteR21.MersenneQuotientRowRecurrences
import ErdosProblems.Erdos257.PaperCompleteR21.OneSidedCertificateHierarchy
import ErdosProblems.Erdos257.PaperCompleteR21.ResetSqrtEscapeHalfMembership
import ErdosProblems.Erdos257.PaperCompleteR21.ResidueClassSupport
import ErdosProblems.Erdos257.PaperCompleteR21.ScalarLocalisationHeightObstruction
import ErdosProblems.Erdos257.PaperCompleteR21.SeamEscapeAndTerminalStrip
import ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase
import ErdosProblems.Erdos257.PaperCompleteR21.SkipSafetyAndDivisorZeroRuns
import ErdosProblems.Erdos257.PaperCompleteR21.SquareDepthAndHalfMembershipEquivalences
import ErdosProblems.Erdos257.PaperCompleteR21.TerminalStripExactRowGap
import ErdosProblems.Erdos257.PaperCompleteR21.ThreeBranchRowDynamics
import ErdosProblems.Erdos257.PaperCompleteR21.TruncatedRungGreedyDecision
import ErdosProblems.Erdos257.PaperCompleteR21.TruncatedRungWitnessHorizon
import ErdosProblems.Erdos257.PaperCompleteR21.UpperResetBandCertificate
import ErdosProblems.Erdos257.PaperCompleteR8.WeightedReturn
import ErdosProblems.Erdos257.WitnessLogicIrrational
-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0

/-!
# Theorems derived from what proofs use

The argument-graph exporter (`scripts/export_argument_continuations.lean`) reads
every theorem of this library and records, among other things, the hypotheses a
proof never uses and the hypotheses a proof uses only through a consequence. This
module turns those observations into ordinary theorems of the library, so a
paper, the paper-to-Lean ledger or another proof can cite them. Every theorem it
adds is checked by the kernel before it is added.

* `derive_idle T` adds `T.idle`: the statement of `T` without the proposition
  hypotheses its proof never uses, with the same proof.
* `derive_weakening T` adds, for each proposition hypothesis `h : H` of `T` that
  the proof uses only inside use sites, `T.weakened_i`: `T` with `H` replaced by
  the propositions `C₁ … Cₖ` those sites prove, and `T.use_i_j : H → Cⱼ`. A use
  site is the largest application around `h` (such as `L h`, `h.2` or `h 3`) that
  mentions no bound variable of the proof and no other hypothesis; its
  proposition must not mention `H`, be `H` up to unfolding, or be the conclusion.
  When some occurrence of `h` lies in no such site, a use site may mention local
  variables (`L n h` under a binder `n`): its consequence is its proposition
  closed over the variables it needs, `Cⱼ = ∀ n, P n`, and the site becomes the
  new hypothesis applied to them.
* `derive_conjuncts T` adds, for each claim of `T`'s conclusion (a conjunct, or
  a direction of an equivalence) whose own proof leaves some hypotheses unused,
  `T.part_k`: that claim assuming only what its proof needs. A claim's proof is
  the projection of `T`'s proof onto it, reduced; it is the claim's own proof
  when the proof builds the claims separately.
* `derive_frontier T` follows those weakenings through the library. When a use
  site is `L a₁ … h … aₘ` for a theorem `L` whose proof uses that hypothesis only
  through consequences of its own, the site is replaced by `L.weakened_p` applied
  to proofs of those consequences, recursively; when the arguments mention the
  site's variables, the step is closed over them. `T.frontier_i` states `T` with
  `H` replaced by the consequences where the recursion stops, each assumed once
  however many branches need it. `derive_frontier T at L₁ L₂` keeps the use
  sites of `L₁` and `L₂` as they are, and names the result `T.frontier_i_L₁`.

Each command adds nothing, and logs why, when a proof lacks the shape it needs.
The weakenings a frontier passes through are added once each, as
`L.weakened_p`, so the frontier's proof is a readable chain of library
theorems.
-/

set_option autoImplicit false

open Lean Meta Elab Command


namespace ErdosProblems.ArgumentGraph

/-- Report a derivation that added nothing: an error under `argumentGraph.strict`,
a warning otherwise. The option is read by name, so a file that inlines this
module (a kernel probe) can use the commands without evaluating the option's
initialiser in the module that declares it. -/
def reportFailure (msg : MessageData) : MetaM Unit := do
  if (← getOptions).getBool `argumentGraph.strict false then logError msg else logWarning msg

/-- Run `x` with its own heartbeat budget (in thousands); `none` when the budget
runs out or `x` throws. -/
def budgeted {α : Type} (heartbeats : Nat) (x : MetaM α) : MetaM (Option α) := do
  withCurrHeartbeats <|
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := heartbeats * 1000 }) do
      tryCatchRuntimeEx (do return some (← x)) fun _ => return none

/-- The recursion bound of every traversal in this module: the depth of term it
follows (every definition here is total). When a bound is reached the traversal
gives its conservative answer (no use site, no weakening, no split), and anything
built from a partial result still has to pass the kernel. -/
def traversalFuel : Nat := 100000

/-- `normaliseBinders`, following at most `fuel` levels of the term. -/
def normaliseBindersAux : Nat → Expr → Nat → Expr
  | 0, e, _ => e
  | fuel + 1, e, depth =>
    let name := Name.mkSimple s!"x{depth}"
    match e with
    | .forallE _ t b _ =>
        .forallE name (normaliseBindersAux fuel t depth) (normaliseBindersAux fuel b (depth + 1)) .default
    | .lam _ t b _ =>
        .lam name (normaliseBindersAux fuel t depth) (normaliseBindersAux fuel b (depth + 1)) .default
    | .letE _ t v b nondep =>
        .letE name (normaliseBindersAux fuel t depth) (normaliseBindersAux fuel v depth)
          (normaliseBindersAux fuel b (depth + 1)) nondep
    | .app f a => .app (normaliseBindersAux fuel f depth) (normaliseBindersAux fuel a depth)
    | .mdata _ b => normaliseBindersAux fuel b depth
    | .proj s i b => .proj s i (normaliseBindersAux fuel b depth)
    | e => e

/-- A statement with binder names, binder annotations and metadata erased, so two
statements that differ only in naming compare equal. -/
def normaliseBinders (e : Expr) : Expr := normaliseBindersAux traversalFuel e 0

/-- Whether the declaration `name` exists with universe parameters `levels` and a
statement definitionally equal to `wanted`. A derived name is a contract on its
statement: a command that finds the name taken by a different statement reports
it, rather than taking the old theorem for the one it was asked for. The check
assigns nothing. -/
def existingTypeMatches (name : Name) (levels : List Name) (wanted : Expr) : MetaM Bool := do
  let some info := (← getEnv).find? name | return false
  unless info.levelParams.length == levels.length do return false
  let actual := info.type.instantiateLevelParams info.levelParams (levels.map mkLevelParam)
  return (← budgeted 5000 (withoutModifyingState (withNewMCtxDepth (isDefEq actual wanted)))) == some true

/-- Add a theorem after a synchronous kernel check; the error text when the
kernel rejects it. When `name` already exists with the same statement (the command
ran before in this environment) nothing is added; when it exists with another
statement, that is an error. -/
def addChecked (name : Name) (levelParams : List Name) (type value : Expr) (doc : String) :
    MetaM (Except String Unit) := do
  if (← getEnv).contains name then
    if ← existingTypeMatches name levelParams type then return .ok ()
    return .error s!"{name} already exists with a different statement"
  let decl := Declaration.thmDecl { name, levelParams, type, value }
  match Kernel.Environment.addDecl (← getEnv).toKernelEnv (← getOptions) decl with
  | .error ex => return .error (← (ex.toMessageData (← getOptions)).toString)
  | .ok _ =>
      addDecl decl
      addDocStringCore name doc
      return .ok ()

/-! ## Idle hypotheses -/

/-- The proposition binders of a theorem that its proof never uses: the binder's
free variable occurs neither in the proof (beta-reduced against the statement's
binders), nor in a later binder type, nor in the conclusion. Instance binders
are kept. -/
def idleBinders (info : ConstantInfo) : MetaM (Array Nat) := do
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

/-- `T.idle`, when `T` has idle proposition hypotheses. -/
def deriveIdle (name : Name) : MetaM (Except String Name) := do
  let info ← getConstInfo name
  let some value := info.value? | return .error "not a theorem with a proof term"
  let idle ← idleBinders info
  if idle.isEmpty then return .error "its proof uses every proposition hypothesis"
  let (type, value, dropped) ← forallTelescope info.type fun xs body => do
    let proof := value.beta xs
    let mut keep : Array Expr := #[]
    let mut dropped : Array String := #[]
    for x in xs, i in [0:xs.size] do
      if idle.contains i then
        dropped := dropped.push (toString (← ppExpr (← inferType x)))
      else
        keep := keep.push x
    return (← mkForallFVars keep body, ← mkLambdaFVars keep proof, dropped)
  let newName := name ++ `idle
  let doc := s!"`{name}` without the hypotheses its proof never uses: \
    {", ".intercalate dropped.toList}. Derived by `derive_idle` from the same proof."
  match ← addChecked newName info.levelParams type value doc with
  | .ok () => return .ok newName
  | .error e => return .error s!"kernel rejected {newName}: {e}"

/-! ## Conjuncts

A paper result often states several claims as one conjunction, or an equivalence,
and assumes a named input that only some of the claims need. Projecting the proof
onto one claim and reducing the projection (beta, `let`, a projection of a
constructor, definitions such as `id`; never a theorem) gives that claim's own
proof when the proof builds the claims separately, directly or under `have`,
`show` or `let`; its free variables are the hypotheses the claim uses. -/

/-- The conjuncts of `A₁ ∧ (A₂ ∧ (… ∧ Aₙ))`, splitting at most `fuel` times. -/
def andSpineAux : Nat → Expr → Array Expr
  | 0, t => #[t]
  | fuel + 1, t =>
    match t.consumeMData.and? with
    | some (a, b) => #[a] ++ andSpineAux fuel b
    | none => #[t]

/-- The claims of a conclusion, each with the projection of a proof of the
conclusion onto it: `A₁ ∧ (A₂ ∧ (… ∧ Aₙ))` gives the `Aᵢ`, and `A ↔ B` gives
`A → B` and `B → A`. A conclusion of any other shape is one claim. -/
def conclusionClaims (type : Expr) : Array (Expr × (Expr → Expr)) := Id.run do
  if let some (a, b) := type.consumeMData.app2? ``Iff then
    return #[(mkForall `h .default a b, fun p => mkProj ``Iff 0 p),
             (mkForall `h .default b a, fun p => mkProj ``Iff 1 p)]
  let parts := andSpineAux 256 type
  let mut out : Array (Expr × (Expr → Expr)) := #[]
  for a in parts, k in [0:parts.size] do
    out := out.push (a, fun p =>
      let rest := (List.range k).foldl (fun e _ => mkProj ``And 1 e) p
      if k + 1 < parts.size then mkProj ``And 0 rest else rest)
  return out

/-- For each claim of `T`'s conclusion (a conjunct, or a direction of an
equivalence) whose proof leaves some proposition hypotheses unused, `T.part_k`
(counting from 1): the claim alone, assuming only the binders its proof and
statement need. -/
def deriveConjuncts (name : Name) : MetaM (Except String (Array Name)) := do
  let info ← getConstInfo name
  let some value := info.value? | return .error "not a theorem with a proof term"
  let parts ← forallTelescope info.type fun xs body => do
    let claims := conclusionClaims body
    if claims.size < 2 then
      return Except.error "its conclusion is neither a conjunction nor an equivalence"
    let mut hasPropHypothesis := false
    for x in xs do
      let decl ← x.fvarId!.getDecl
      if decl.binderInfo != .instImplicit && (← isProp decl.type) then
        hasPropHypothesis := true
    unless hasPropHypothesis do
      return Except.error "it has no proposition hypothesis to leave out"
    let proof ← instantiateMVars (value.beta xs)
    let mut out : Array (Nat × Expr × Expr × Array String) := #[]
    let mut uses : Array String := #[]
    for (a, project) in claims, k in [1:claims.size + 1] do
      let p := (← budgeted 2000 (whnf (project proof))).getD (project proof)
      -- the binders the part needs: those its proof or statement mention, closed
      -- under the binder types that mention them
      let mut needed : Std.HashSet FVarId := {}
      for x in xs do
        if p.containsFVar x.fvarId! || a.containsFVar x.fvarId! then
          needed := needed.insert x.fvarId!
      let mut changed := true
      while changed do
        changed := false
        for x in xs do
          if needed.contains x.fvarId! then
            for y in xs do
              if !needed.contains y.fvarId! && (← x.fvarId!.getDecl).type.containsFVar y.fvarId! then
                needed := needed.insert y.fvarId!
                changed := true
      let keep := xs.filter fun x => needed.contains x.fvarId!
      let mut dropped : Array String := #[]
      let mut used : Array String := #[]
      for x in xs do
        let decl ← x.fvarId!.getDecl
        if decl.binderInfo == .instImplicit then continue
        unless ← isProp decl.type do continue
        if needed.contains x.fvarId! then
          used := used.push (toString decl.userName)
        else
          dropped := dropped.push (toString (← ppExpr decl.type))
      if dropped.isEmpty then
        uses := uses.push s!"claim {k} uses {", ".intercalate used.toList}"
        continue
      out := out.push (k, ← mkForallFVars keep a, ← mkLambdaFVars keep p, dropped)
    if out.isEmpty then
      return Except.error s!"every claim of its conclusion uses every proposition hypothesis \
        ({"; ".intercalate uses.toList})"
    return Except.ok out
  let parts ← match parts with
    | .ok parts => pure parts
    | .error e => return .error e
  let mut added : Array Name := #[]
  for (k, type, value, dropped) in parts do
    let newName := name ++ Name.mkSimple s!"part_{k}"
    if (← getEnv).contains newName then
      unless ← existingTypeMatches newName info.levelParams type do
        return .error s!"{newName} already exists with a different statement"
      added := added.push newName
      continue
    let doc := s!"Conjunct {k} of `{name}`, which its proof establishes without \
      {", ".intercalate dropped.toList}. Derived by `derive_conjuncts` from the same proof."
    match ← addChecked newName info.levelParams type value doc with
    | .ok () => added := added.push newName
    | .error e => return .error s!"kernel rejected {newName}: {e}"
  return .ok added

/-! ## Used consequences -/

/-- `isHypRef`, looking through at most `fuel` casts. -/
def isHypRefAux : Nat → FVarId → Expr → Bool
  | 0, _, _ => false
  | fuel + 1, h, e =>
    match e.consumeMData with
    | .fvar id => id == h
    | e =>
        match e.getAppFn with
        | .const n _ =>
            let args := e.getAppArgs
            if (n == ``Eq.mpr || n == ``Eq.mp || n == ``cast) && args.size == 4 then
              !args[2]!.containsFVar h && isHypRefAux fuel h args[3]!
            else if n == ``id && args.size == 2 then isHypRefAux fuel h args[1]!
            else false
        | _ => false

/-- Whether `e` is the hypothesis `h`, possibly transported by `Eq.mpr`, `Eq.mp`,
`cast` or `id` whose other arguments do not use `h`. -/
def isHypRef (h : FVarId) (e : Expr) : Bool := isHypRefAux 64 h e

structure UseScan where
  /-- Per subterm: whether it mentions `h`, and whether it mentions another free
  variable. Memoised, so shared subterms are visited once. -/
  facts : Std.HashMap Expr (Bool × Bool) := {}
  verdicts : Std.HashMap Expr Bool := {}
  sites : Array Expr := #[]
  visited : Nat := 0

abbrev UseM := StateT UseScan MetaM

/-- `useFacts`, following at most `fuel` levels. Past the bound a subterm counts
as mentioning `h` and another variable, the answer that admits no use site. -/
def useFactsAux : Nat → FVarId → Expr → UseM (Bool × Bool)
  | 0, _, _ => return (true, true)
  | fuel + 1, h, e => do
    if !e.hasFVar then return (false, false)
    if let some f := (← get).facts.get? e then return f
    let f ← match e with
      | .fvar id => pure (id == h, id != h)
      | .app f a => do
          let x ← useFactsAux fuel h f
          let y ← useFactsAux fuel h a
          pure (x.1 || y.1, x.2 || y.2)
      | .lam _ t b _ | .forallE _ t b _ => do
          let x ← useFactsAux fuel h t
          let y ← useFactsAux fuel h b
          pure (x.1 || y.1, x.2 || y.2)
      | .letE _ t v b _ => do
          let x ← useFactsAux fuel h t
          let y ← useFactsAux fuel h v
          let z ← useFactsAux fuel h b
          pure (x.1 || y.1 || z.1, x.2 || y.2 || z.2)
      | .mdata _ b | .proj _ _ b => useFactsAux fuel h b
      | _ => pure (false, false)
    modify fun s => { s with facts := s.facts.insert e f }
    return f

/-- Whether `e` mentions `h`, and whether it mentions another free variable. -/
def useFacts (h : FVarId) (e : Expr) : UseM (Bool × Bool) := useFactsAux traversalFuel h e

/-- No bound variable of the proof, no metavariable, no free variable but `h`. -/
def closedFor (h : FVarId) (e : Expr) : UseM Bool := do
  if e.hasLooseBVars || e.hasMVar then return false
  return !(← useFacts h e).2

/-- The proposition a use site proves, if the site qualifies. -/
def siteType? (hType : Expr) (conclusion : Option Expr) (site : Expr) : MetaM (Option Expr) := do
  try
    let t ← instantiateMVars (← inferType site)
    unless ← isProp t do return none
    if t.hasFVar || t.hasMVar || t.hasLooseBVars then return none
    if (t.find? (· == hType)).isSome then return none
    if conclusion == some (normaliseBinders t) then return none
    if (← budgeted 5000 (withNewMCtxDepth (isDefEq t hType))) == some true then return none
    return some t
  catch _ => return none

mutual
/-- `collectUses` with a recursion bound; past it the answer is `false` (no
weakening). -/
def collectUsesAux : Nat → FVarId → Expr → Option Expr → Expr → UseM Bool
  | 0, _, _, _, _ => return false
  | fuel + 1, h, hType, conclusion, e => do
    if !(← useFacts h e).1 then return true
    if let some v := (← get).verdicts.get? e then return v
    let s ← get
    if s.visited ≥ 200000 then return false
    set { s with visited := s.visited + 1 }
    let v ← visitUsesAux fuel h hType conclusion e
    modify fun s => { s with verdicts := s.verdicts.insert e v }
    return v

/-- One step of `collectUses`: the cases by the shape of `e`. -/
def visitUsesAux : Nat → FVarId → Expr → Option Expr → Expr → UseM Bool
  | 0, _, _, _, _ => return false
  | fuel + 1, h, hType, conclusion, e => do
    match e with
    | .fvar _ => return false
    | .mdata _ b => collectUsesAux fuel h hType conclusion b
    | .proj _ _ b =>
        if isHypRef h b && (← closedFor h e) then
          unless (← siteType? hType conclusion e).isSome do return false
          modify fun s => { s with sites := s.sites.push e }
          return true
        collectUsesAux fuel h hType conclusion b
    | .lam _ t b _ | .forallE _ t b _ =>
        let x ← collectUsesAux fuel h hType conclusion t
        let y ← collectUsesAux fuel h hType conclusion b
        return x && y
    | .letE _ t v b _ =>
        let x ← collectUsesAux fuel h hType conclusion t
        let y ← collectUsesAux fuel h hType conclusion v
        let z ← collectUsesAux fuel h hType conclusion b
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
          unless (← siteType? hType conclusion site).isSome do return false
          modify fun s => { s with sites := s.sites.push site }
          let mut ok := true
          for a in args.extract k args.size do
            unless ← collectUsesAux fuel h hType conclusion a do ok := false
          return ok
        let mut ok ← collectUsesAux fuel h hType conclusion fn
        for a in args do
          unless ← collectUsesAux fuel h hType conclusion a do ok := false
        return ok
    | _ => return true
end

/-- Whether every occurrence of `h` in `e` lies inside a use site; the sites are
collected in the state. `false`: some occurrence uses `h` as it stands. -/
def collectUses (h : FVarId) (hType : Expr) (conclusion : Option Expr) (e : Expr) : UseM Bool :=
  collectUsesAux traversalFuel h hType conclusion e

/-- Binder `i` of a theorem replaced by what the proof uses of it. -/
structure Weakening where
  type : Expr
  value : Expr
  hypothesis : Expr
  /-- The distinct propositions the use sites prove, in order of first use. -/
  consequences : Array Expr
  /-- Per consequence, one of its use sites as a closed function of the hypothesis
  and of the site's parameters. -/
  sites : Array Expr
  /-- Per consequence, how many parameters its site has (none for a site that
  mentions no variable but the hypothesis). -/
  arity : Array Nat

/-- The weakening of binder `i` by use sites that mention no variable but the
hypothesis: one hypothesis per distinct use-site proposition, placed where the
binder was, each use site in the proof replaced by the new hypothesis. -/
def weakenClosed (info : ConstantInfo) (i : Nat) : MetaM (Option Weakening) := do
  let some value := info.value? | return none
  forallTelescope info.type fun xs body => do
    unless i < xs.size do return none
    let x := xs[i]!
    let h := x.fvarId!
    let decl ← h.getDecl
    if decl.binderInfo == .instImplicit then return none
    let hType ← instantiateMVars decl.type
    unless ← isProp hType do return none
    if body.containsFVar h then return none
    for j in [i+1:xs.size] do
      if (← xs[j]!.fvarId!.getDecl).type.containsFVar h then return none
    let proof := value.beta xs
    let conclusion := if body.hasFVar then none else some (normaliseBinders body)
    let (ok, scan) ← (collectUses h hType conclusion proof).run {}
    unless ok && !scan.sites.isEmpty do return none
    let mut consequences : Array Expr := #[]
    let mut slot : Array Nat := #[]
    let mut sites : Array Expr := #[]
    for site in scan.sites do
      let t ← instantiateMVars (← inferType site)
      match consequences.findIdx? (· == t) with
      | some j => slot := slot.push j
      | none =>
          slot := slot.push consequences.size
          consequences := consequences.push t
          sites := sites.push (← mkLambdaFVars #[x] site)
    let decls := consequences.mapIdx fun j t =>
      (Name.mkSimple s!"used{j}", fun (_ : Array Expr) => (pure t : MetaM Expr))
    withLocalDeclsD decls fun cs => do
      let replaced := proof.replace fun e =>
        if !e.hasFVar then none
        else match scan.sites.findIdx? (· == e) with
          | some j => some cs[slot[j]!]!
          | none => none
      if replaced.containsFVar h then return none
      let keep := xs.extract 0 i ++ cs ++ xs.extract (i + 1) xs.size
      let type ← instantiateMVars (← mkForallFVars keep body)
      let value ← instantiateMVars (← mkLambdaFVars keep replaced)
      if type.hasMVar || value.hasMVar then return none
      return some { type, value, hypothesis := hType, consequences, sites,
                    arity := consequences.map fun _ => 0 }

/-! ## Used consequences with parameters

When some occurrence of `h` lies in no use site of the rule above (`L n h` under a
binder `n`, a use inside a lambda, one that needs a dependent datum
`x : Fin (n + 1)`), the proof is read again with every binder opened and every
`let` replaced by its value, so a use site may mention local variables. Its
consequence is the site's proposition closed over the variables the site needs, in
context order, together with the variables their types need
(`∀ n (x : Fin (n + 1)), P n x`), and the site becomes that new hypothesis applied
to them. When `h` itself admits no site there (`h n` closes back to `H`), the
enclosing application or projection is the site.

A site is rejected when one of its variables has a type that mentions `h`, or when
its proposition mentions `h` or `H`, is `H` up to unfolding, or is the theorem's
statement or conclusion (also as the double negation a `by_contra` leaves); the
kernel checks `H → C` before a consequence is admitted. The whole weakening is
rejected when the proof itself becomes a new hypothesis applied to arguments. New
hypotheses are placeholder constants until the final term is built; no term that
contains one reaches the kernel. -/

/-- What a search for use sites with parameters knows about `h : hType`. -/
structure SiteContext where
  h : FVarId
  hType : Expr
  levelParams : List Name
  /-- The statements a consequence must not be, binder names erased: the theorem's
  statement without `h`, and its conclusion when that is closed. -/
  goals : Array Expr

structure SiteScan where
  consequences : Array Expr := #[]
  /-- Per consequence, the placeholder constant that stands for it in the proof. -/
  holes : Array Name := #[]
  sites : Array Expr := #[]
  arity : Array Nat := #[]
  /-- Rewrites of shared subterms, so a proof DAG is walked once per node. -/
  memo : Std.HashMap Expr (Option Expr) := {}
  visited : Nat := 0
  exceeded : Bool := false

abbrev SiteM := StateT SiteScan MetaM

/-- Undo the rewrites and admissions made since `saved`; the work counters stay. -/
def restoreScan (saved : SiteScan) : SiteM Unit :=
  modify fun s => { saved with visited := s.visited, exceeded := s.exceeded }

/-- Whether the kernel accepts `value : type` as a theorem; nothing is added. -/
def kernelAccepts (levelParams : List Name) (type value : Expr) : MetaM Bool := do
  let decl := Declaration.thmDecl { name := `_argumentGraph_check, levelParams, type, value }
  match Kernel.Environment.addDecl (← getEnv).toKernelEnv (← getOptions) decl with
  | .ok _ => return true
  | .error _ => return false

/-- The local variables a use site needs as parameters: those it mentions other
than `h`, and those their types mention, in context order. `none` when one of them
has a type that mentions `h`, or is not in `context`. -/
def siteParameters (h : FVarId) (context : Array Expr) (site : Expr) :
    MetaM (Option (Array Expr)) := do
  let mut needed : Std.HashSet FVarId := {}
  for id in (collectFVars {} site).fvarSet.toList do
    if id != h then needed := needed.insert id
  for _ in [0:context.size + 1] do
    let mut changed := false
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
    unless changed do break
  let params := context.filter fun x => needed.contains x.fvarId!
  if params.size != needed.size then return none
  return some params

/-- `G` when `t` is `¬¬G`, `¬G → False` or `(G → False) → False`. -/
def doubleNegated? (t : Expr) : Option Expr :=
  let negated? (d : Expr) : Option Expr :=
    if d.isAppOfArity ``Not 1 then some d.appArg!
    else match d with
      | .forallE _ g b _ => if b.isConstOf ``False then some g else none
      | _ => none
  let t := t.consumeMData
  if t.isAppOfArity ``Not 1 then negated? t.appArg!.consumeMData
  else match t with
    | .forallE _ d b _ => if b.isConstOf ``False then negated? d.consumeMData else none
    | _ => none

/-- The statement a closed consequence `c` restates classically: `∀ xs, X` when
`c` is `∀ xs, ¬¬X` (in a form `doubleNegated?` reads), or `∀ xs (_ : ¬X), False`,
the shape of a `by_contra` site closed over the negated goal it assumes. -/
def classicalRestatement? (c : Expr) : MetaM (Option Expr) :=
  forallTelescope c fun xs body => do
    if let some x := doubleNegated? body then
      return some (← mkForallFVars xs x)
    unless body.consumeMData.isConstOf ``False && !xs.isEmpty do return none
    let last := (← inferType xs.back!).consumeMData
    let negated? : Option Expr :=
      if last.isAppOfArity ``Not 1 then some last.appArg!
      else match last with
        | .forallE _ x b _ => if b.consumeMData.isConstOf ``False && !b.hasLooseBVars then some x else none
        | _ => none
    match negated? with
    | some x => return some (← mkForallFVars xs.pop x)
    | none => return none

/-- Admit `site` as a use site with parameters: its proposition closed over its
parameters is a consequence of `H` (the kernel checks `H → C` the first time `C`
is seen), and the site becomes that consequence's placeholder applied to the
parameters. -/
def liftSite (ctx : SiteContext) (context : Array Expr) (site : Expr) : SiteM (Option Expr) := do
  try
    let t ← instantiateMVars (← inferType site)
    unless ← isProp t do return none
    if t.containsFVar ctx.h || t.hasMVar || t.hasLooseBVars then return none
    if (t.find? (· == ctx.hType)).isSome then return none
    let some params ← siteParameters ctx.h context site | return none
    let c ← instantiateMVars (← mkForallFVars params t)
    if c.hasFVar || c.hasMVar || c.hasLooseBVars then return none
    if ctx.goals.contains (normaliseBinders c) then return none
    if let some g := doubleNegated? t then
      if ctx.goals.contains (normaliseBinders g) then return none
      if ctx.goals.contains (normaliseBinders (← instantiateMVars (← mkForallFVars params g))) then
        return none
    -- A `by_contra` site proves `False` under the negated goal, so only its closed
    -- form `¬G → False` shows that it restates the goal.
    if let some g ← classicalRestatement? c then
      if ctx.goals.contains (normaliseBinders (← instantiateMVars g)) then return none
    if (← budgeted 5000 (withNewMCtxDepth (isDefEq c ctx.hType))) == some true then return none
    let current ← get
    if let some j := current.consequences.findIdx? (· == c) then
      return some (mkAppN (mkConst current.holes[j]!) params)
    if current.consequences.size ≥ 128 then
      set { current with exceeded := true }
      return none
    let recover ← instantiateMVars (← mkLambdaFVars (#[mkFVar ctx.h] ++ params) site)
    if recover.hasFVar || recover.hasMVar then return none
    unless ← kernelAccepts ctx.levelParams (Expr.forallE `h ctx.hType c .default) recover do
      return none
    let hole := Name.mkNum `_argumentGraph_hole current.consequences.size
    set { current with
      consequences := current.consequences.push c, holes := current.holes.push hole,
      sites := current.sites.push recover, arity := current.arity.push params.size }
    return some (mkAppN (mkConst hole) params)
  catch _ => return none

/-- The length of the application prefix `f a₁ … aₖ` of `f a₁ … aₙ` after dropping
trailing arguments that are local variables mentioned nowhere else in it (nor in the
types of the variables it mentions): the closed consequence is the same statement
up to those binders, and the shorter site keeps a named proposition (`L h : Weak`)
rather than its unfolding at a bound variable. -/
def trimTrailing (h : FVarId) (fn : Expr) (args : Array Expr) (use : Expr → Bool) :
    MetaM Nat := do
  let mut k := args.size
  for _ in [0:args.size] do
    if k == 0 then break
    let a := args[k - 1]!
    unless a.isFVar && a.fvarId! != h do break
    let id := a.fvarId!
    let rest := args.extract 0 (k - 1)
    unless use fn || rest.any use do break
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
/-- The proof with every use of `h` replaced by a placeholder application, or `none`
when some occurrence of `h` lies in no admissible use site; following at most
`fuel` levels, past which the answer is `none`. -/
def rewriteUsesAux : Nat → SiteContext → Array Expr → Expr → SiteM (Option Expr)
  | 0, _, _, _ => return none
  | fuel + 1, ctx, context, e => do
    unless e.containsFVar ctx.h do return some e
    if let some r := (← get).memo.get? e then return r
    let s ← get
    if s.exceeded || s.visited ≥ 200000 then
      set { s with exceeded := true }
      return none
    set { s with visited := s.visited + 1 }
    let r ← rewriteNodeAux fuel ctx context e
    modify fun s => { s with memo := s.memo.insert e r }
    return r

/-- One node of `rewriteUsesAux` (a separate function, so that its `return`s come
back to the memoising wrapper). -/
def rewriteNodeAux : Nat → SiteContext → Array Expr → Expr → SiteM (Option Expr)
  | 0, _, _, _ => return none
  | fuel + 1, ctx, context, e => do
    match e with
    | .mdata md b => return (← rewriteUsesAux fuel ctx context b).map (Expr.mdata md)
    | .lam n t b bi =>
        if t.containsFVar ctx.h then return none
        withLocalDecl n bi t fun x => do
          let some body ← rewriteUsesAux fuel ctx (context.push x) (b.instantiate1 x) | return none
          return some (← mkLambdaFVars #[x] body)
    | .forallE n t b bi =>
        if t.containsFVar ctx.h then return none
        withLocalDecl n bi t fun x => do
          let some body ← rewriteUsesAux fuel ctx (context.push x) (b.instantiate1 x) | return none
          return some (← mkForallFVars #[x] body)
    | .letE _ _ value body _ => rewriteUsesAux fuel ctx context (body.instantiate1 value)
    | .proj n i b =>
        let saved ← get
        if isHypRef ctx.h b then
          if let some out ← liftSite ctx context e then return some out
        if let some b' ← rewriteUsesAux fuel ctx context b then return some (Expr.proj n i b')
        -- `(h n).i` under a binder: `h n` closes back to `H`, so the projection is
        -- the use site.
        if b.containsFVar ctx.h then
          restoreScan saved
          if let some out ← liftSite ctx context e then return some out
        return none
    | .app .. =>
        let beta := e.headBeta
        if beta != e then return ← rewriteUsesAux fuel ctx context beta
        if isHypRef ctx.h e then return none
        let fn := e.getAppFn
        let args := e.getAppArgs
        let saved ← get
        -- `h` itself is the function or an argument: the application is the use site.
        if isHypRef ctx.h fn || args.any (isHypRef ctx.h) then
          if let some r ← liftPrefixesAux fuel ctx context fn args (isHypRef ctx.h) then
            return some r
          restoreScan saved
        -- Otherwise rewrite the function and the arguments.
        let generic ← (do
          let some f ← rewriteUsesAux fuel ctx context fn | return none
          let mut newArgs : Array Expr := #[]
          for a in args do
            let some a' ← rewriteUsesAux fuel ctx context a | return none
            newArgs := newArgs.push a'
          return some (mkAppN f newArgs) : SiteM (Option Expr))
        if generic.isSome then return generic
        -- An argument using `h` admits no site of its own (`h n` or `L n h` under a
        -- binder `n` closes back to `H`): the enclosing application is the use
        -- site (`And.left (h n)`, `le_of_lt (L n h)`).
        let uses : Expr → Bool := fun a => a.containsFVar ctx.h
        if uses fn || args.any uses then
          restoreScan saved
          if let some r ← liftPrefixesAux fuel ctx context fn args uses then
            return some r
        return none
    | _ => return none

/-- The prefixes of `fn args` containing an argument that satisfies `use` (all of
them when `fn` does) as use sites: the trimmed full application first, then every
other prefix from the largest, so a bad large site does not hide a smaller one. The
first admissible site is replaced and the remaining arguments are rewritten. -/
def liftPrefixesAux : Nat → SiteContext → Array Expr → Expr → Array Expr → (Expr → Bool) →
    SiteM (Option Expr)
  | 0, _, _, _, _, _ => return none
  | fuel + 1, ctx, context, fn, args, use => do
    let trimmed ← trimTrailing ctx.h fn args use
    let mut order : Array Nat := #[trimmed]
    for k in (List.range args.size).reverse do
      if k + 1 != trimmed then order := order.push (k + 1)
    for count in order do
      let pre := args.extract 0 count
      unless use fn || pre.any use do continue
      if let some site ← liftSite ctx context (mkAppN fn pre) then
        let mut rest : Array Expr := #[]
        for a in args.extract count args.size do
          let some a' ← rewriteUsesAux fuel ctx context a | return none
          rest := rest.push a'
        return some (mkAppN site rest)
    return none
end

/-- `e` without its leading lambdas, following at most `fuel` of them (the result
may have loose bound variables). -/
def stripLambdasAux : Nat → Expr → Expr
  | 0, e => e
  | fuel + 1, .lam _ _ b _ => stripLambdasAux fuel b
  | fuel + 1, .mdata _ b => stripLambdasAux fuel b
  | _, e => e

/-- Binder `i` of a theorem replaced by what the proof uses of it, by use sites with
parameters. `.error reason` when there is none: `bare_use` (some occurrence of the
hypothesis lies in no admissible site), `vacuous` (the proof is a new hypothesis
applied to arguments), `dependent` (the hypothesis is not closed, or the statement
depends on it), `no_use_site`, `exceeded`, `open_term`, `placeholder_left`, or why
the binder is not a candidate. -/
def weakenWithParameters (info : ConstantInfo) (i : Nat) : MetaM (Except String Weakening) := do
  let some value := info.value? | return .error "no_value"
  forallTelescope info.type fun xs body => do
    unless i < xs.size do return .error "no_binder"
    let h := xs[i]!.fvarId!
    let decl ← h.getDecl
    if decl.binderInfo == .instImplicit then return .error "instance"
    let hType ← instantiateMVars decl.type
    unless ← isProp hType do return .error "not_a_proposition"
    if hType.hasFVar || hType.hasMVar || body.containsFVar h then return .error "dependent"
    for j in [i+1:xs.size] do
      if (← xs[j]!.fvarId!.getDecl).type.containsFVar h then return .error "dependent"
    let others := xs.extract 0 i ++ xs.extract (i + 1) xs.size
    let whole ← instantiateMVars (← mkForallFVars others body)
    let goals := if body.hasFVar then #[normaliseBinders whole]
      else #[normaliseBinders whole, normaliseBinders body]
    let ctx : SiteContext := { h, hType, levelParams := info.levelParams, goals }
    let (result, scan) ← (rewriteUsesAux traversalFuel ctx xs (value.beta xs)).run {}
    if scan.exceeded then return .error "exceeded"
    let some template := result | return .error "bare_use"
    if scan.consequences.isEmpty then return .error "no_use_site"
    if template.containsFVar h then return .error "bare_use"
    let isHole : Expr → Bool := fun e => match e.getAppFn with
      | .const n _ => scan.holes.contains n
      | _ => false
    if isHole (stripLambdasAux traversalFuel template) then return .error "vacuous"
    let decls := scan.consequences.mapIdx fun j t =>
      (Name.mkSimple s!"used{j}", fun (_ : Array Expr) => (pure t : MetaM Expr))
    withLocalDeclsD decls fun cs => do
      let replaced := template.replace fun e => match e with
        | .const n _ => (scan.holes.findIdx? (· == n)).map (fun j => cs[j]!)
        | _ => none
      if (replaced.find? fun e => match e with
          | .const n _ => scan.holes.contains n
          | _ => false).isSome then return .error "placeholder_left"
      let keep := xs.extract 0 i ++ cs ++ xs.extract (i + 1) xs.size
      let type ← instantiateMVars (← mkForallFVars keep body)
      let proof ← instantiateMVars (← mkLambdaFVars keep replaced)
      if type.hasMVar || type.hasFVar || proof.hasMVar || proof.hasFVar then
        return .error "open_term"
      return .ok { type, value := proof, hypothesis := hType, consequences := scan.consequences,
                   sites := scan.sites, arity := scan.arity }

/-- The heartbeat budget, in thousands, of one search for use sites with parameters. -/
def parameterBudget : Nat := 200000

/-- Binder `i` of a theorem replaced by what the proof uses of it: by use sites that
mention no variable but the hypothesis when every occurrence of it lies in one, and
otherwise by use sites with parameters (within `parameterBudget`; `budget` when it
runs out). -/
def weakenAt (info : ConstantInfo) (i : Nat) : MetaM (Except String Weakening) := do
  if let some w ← weakenClosed info i then return .ok w
  return (← budgeted parameterBudget (weakenWithParameters info i)).getD (.error "budget")

/-- The number of binders of a theorem's statement, without unfolding. -/
def binderCount (info : ConstantInfo) : MetaM Nat :=
  forallTelescope info.type fun xs _ => return xs.size

/-- Weakenings added so far in this command, by theorem and binder, or why there is
none. -/
abbrev DeriveM := StateRefT (Std.HashMap (Name × Nat) (Except String (Name × Weakening))) MetaM

/-- The weakening of `name` at binder `i`, added to the environment as
`name.weakened_i` the first time it is needed, or why there is none. -/
def weakeningResult (name : Name) (i : Nat) : DeriveM (Except String (Name × Weakening)) := do
  if let some r := (← get).get? (name, i) then return r
  let info ← getConstInfo name
  let r : Except String (Name × Weakening) ← do
    match ← weakenAt info i with
    | .error e => pure (.error e)
    | .ok w =>
      let wName := name ++ Name.mkSimple s!"weakened_{i}"
      if (← getEnv).contains wName then
        if ← existingTypeMatches wName info.levelParams w.type then pure (.ok (wName, w))
        else pure (.error s!"{wName} already exists with a different statement")
      else
        let doc := s!"`{name}` with its hypothesis number {i} replaced by what its proof \
          uses of it. Derived by `derive_weakening` from the same proof."
        match ← addChecked wName info.levelParams w.type w.value doc with
        | .ok () => pure (.ok (wName, w))
        | .error e => pure (.error s!"kernel rejected {wName}: {e}")
  modify (·.insert (name, i) r)
  return r

/-- The weakening of `name` at binder `i` (see `weakeningResult`). -/
def weakeningOf (name : Name) (i : Nat) : DeriveM (Option (Name × Weakening)) := do
  return (← weakeningResult name i).toOption

/-! ## Frontiers -/

/-- How a frontier proves one consequence: assumed as it stands (`arity` is the
number of parameters of the use site that proves it), or obtained as
`fun ps => fn before … after` with each child consequence supplied recursively,
where `binders` are the site's parameters `ps` and `before`, `after` may mention
them. -/
inductive Plan where
  | leaf (type : Expr) (arity : Nat)
  | step (fn : Expr) (binders : Array (Name × Expr × BinderInfo)) (before after : Array Expr)
      (children : Array Plan)
  deriving Inhabited

/-- The first `n` lambda binders of `e` and the body under them. -/
def peelLambdas : Nat → Expr → Option (Array (Name × Expr × BinderInfo) × Expr)
  | 0, e => some (#[], e)
  | n + 1, .lam name t b bi => (peelLambdas n b).map fun r => (#[(name, t, bi)] ++ r.1, r.2)
  | _ + 1, _ => none

/-- The plan for a consequence `c` proved at `site`, a closed function of the
hypothesis and of the site's `arity` parameters. A site `L a₁ … h … aₘ` whose
other arguments mention only the parameters is followed into `L`'s weakening at
`h`'s position, whose consequences are proved recursively. `stops` lists theorems
whose use sites stay as they are. -/
def plan (stops : Array Name) : Nat → Expr → Expr → Nat → DeriveM Plan
  | 0, c, _, arity => return .leaf c arity
  | fuel + 1, c, site, arity => do
    let .lam _ _ inner _ := site | return .leaf c arity
    -- The hypothesis becomes a marker constant, so the parameters' binders and the
    -- other arguments can be kept as they are.
    let marker := mkConst `_argumentGraph_hypothesis
    let mentions (e : Expr) : Bool := (e.find? (· == marker)).isSome
    let some (binders, body) := peelLambdas arity (inner.instantiate1 marker)
      | return .leaf c arity
    if binders.any (fun b => mentions b.2.1) then return .leaf c arity
    let .const n us := body.getAppFn | return .leaf c arity
    if stops.contains n then return .leaf c arity
    let args := body.getAppArgs
    let some p := args.findIdx? (fun a => a.consumeMData == marker) | return .leaf c arity
    for a in args, k in [0:args.size] do
      if k != p && mentions a then return .leaf c arity
    let some (wName, w) ← weakeningOf n p | return .leaf c arity
    let info ← getConstInfo n
    let inst (e : Expr) : Expr := e.instantiateLevelParams info.levelParams us
    let mut children : Array Plan := #[]
    for d in w.consequences, s in w.sites, a in w.arity do
      children := children.push (← plan stops fuel (inst d) (inst s) a)
    return .step (mkConst wName us) binders (args.extract 0 p) (args.extract (p + 1) args.size)
      children

/-- The bound for walking a plan; `plan` builds plans at most `planFuel` deep. -/
def planFuel : Nat := 64

def Plan.leavesAux : Nat → Plan → Array (Expr × Nat) → Array (Expr × Nat)
  | _, .leaf t a, acc =>
      match acc.findIdx? (·.1 == t) with
      | some j => acc.modify j fun l => (l.1, max l.2 a)
      | none => acc.push (t, a)
  | 0, .step .., acc => acc
  | fuel + 1, .step _ _ _ _ cs, acc => cs.foldl (fun a c => Plan.leavesAux fuel c a) acc

/-- The distinct statements where a plan stops, each with the most parameters of a
site that proves it, added to `acc`. -/
def Plan.leaves (p : Plan) (acc : Array (Expr × Nat)) : Array (Expr × Nat) :=
  Plan.leavesAux planFuel p acc

/-- `fun ps => body` for the binders `ps`. -/
def closeOver (binders : Array (Name × Expr × BinderInfo)) (body : Expr) : Expr :=
  binders.foldr (fun b e => Expr.lam b.1 b.2.1 e b.2.2) body

def Plan.buildAux : Nat → Array Expr → Array Expr → Plan → Expr
  | _, types, vars, .leaf t _ => vars[(types.findIdx? (· == t)).getD 0]!
  | 0, _, _, .step fn binders before after _ => closeOver binders (mkAppN fn (before ++ after))
  | fuel + 1, types, vars, .step fn binders before after cs =>
      closeOver binders (mkAppN fn (before ++ cs.map (Plan.buildAux fuel types vars ·) ++ after))

/-- The proof term a plan describes, with `vars[j]` for the leaf `types[j]`. A term
built past the bound is ill-typed, so the kernel rejects it. -/
def Plan.build (types vars : Array Expr) (p : Plan) : Expr := Plan.buildAux planFuel types vars p

def Plan.depthAux : Nat → Plan → Nat
  | _, .leaf .. => 0
  | 0, .step .. => 1
  | fuel + 1, .step _ _ _ _ cs => 1 + cs.foldl (fun m c => max m (Plan.depthAux fuel c)) 0

/-- How many weakenings deep the plan goes. -/
def Plan.depth (p : Plan) : Nat := Plan.depthAux planFuel p

/-- A proof of the closed proposition `t` by one of `suppliers`: the supplier
itself when its statement is `t`, or the supplier applied to arguments found by
unification when a prefix of its binders instantiates to `t` (instance
arguments synthesised). `none` when no supplier fits without leftover
metavariables. -/
def supplyDirect (t : Expr) (suppliers : Array Name) : MetaM (Option Expr) := do
  for s in suppliers do
    let info ← getConstInfo s
    let n ← forallTelescope info.type fun xs _ => return xs.size
    for k in [0:n+1] do
      let found ← withNewMCtxDepth do
        let us ← mkFreshLevelMVarsFor info
        let (mvars, _, rest) ← forallMetaBoundedTelescope
          (info.type.instantiateLevelParams info.levelParams us) k
        unless mvars.size == k do return none
        unless (← budgeted 20000 (isDefEq rest t)) == some true do return none
        for m in mvars do
          unless ← m.mvarId!.isAssigned do
            if let some inst ← (try synthInstance? (← inferType m) catch _ => pure none) then
              m.mvarId!.assign inst
        let proof ← instantiateMVars (mkAppN (mkConst s us) mvars)
        if proof.hasMVar || proof.hasLevelMVar then return none
        return some proof
      if found.isSome then return found
  return none

/-- A proof of the closed proposition `t`, the consequence of a use site with
`arity` parameters, by one of `suppliers`: `supplyDirect t`, or else
`fun x₁ … xₖ => p` for the first `k ≤ arity` binders of `t` and a supplier's proof
`p` of what they bind, fewest first. A supplier of the site's own proposition so
discharges its closure over the parameters, whichever of them it needs. -/
def supplyLeaf (t : Expr) (arity : Nat) (suppliers : Array Name) : MetaM (Option Expr) := do
  if let some p ← supplyDirect t suppliers then return some p
  for k in [1:arity + 1] do
    let found ← forallBoundedTelescope t (some k) fun xs body => do
      unless xs.size == k do return none
      let some p ← supplyDirect body suppliers | return none
      let proof ← instantiateMVars (← mkLambdaFVars xs p)
      if proof.hasMVar || proof.hasFVar then return none
      return some proof
    if found.isSome then return found
  return none

/-- The statement and proof of a frontier: `info`'s statement with binder `i`
replaced by one hypothesis per leaf type that no supplier proves, proved by
`wName` (the weakening at `i`) applied to the plans' proofs of its consequences. -/
def frontierDecl (info : ConstantInfo) (i : Nat) (wName : Name) (plans : Array Plan)
    (leafTypes : Array Expr) (supplied : Array (Option Expr)) : MetaM (Expr × Expr) := do
  let lvls := info.levelParams.map mkLevelParam
  let openLeaves := (Array.range leafTypes.size).filter fun j => (supplied[j]!).isNone
  forallTelescope info.type fun xs body => do
    let decls := openLeaves.map fun j =>
      (Name.mkSimple s!"interface{j}", fun (_ : Array Expr) => (pure leafTypes[j]! : MetaM Expr))
    withLocalDeclsD decls fun ls => do
      let vars := (Array.range leafTypes.size).map fun j =>
        match supplied[j]! with
        | some proof => proof
        | none => ls[(openLeaves.findIdx? (· == j)).getD 0]!
      let proofs := plans.map (·.build leafTypes vars)
      let keep := xs.extract 0 i ++ ls ++ xs.extract (i + 1) xs.size
      let applied := mkAppN (mkConst wName lvls) (xs.extract 0 i ++ proofs ++ xs.extract (i + 1) xs.size)
      return (← mkForallFVars keep body, ← mkLambdaFVars keep applied)

/-- `name.frontier_i` (or `name.frontier_i_<L>` when stopping at the use sites of
`L`): `name` with hypothesis `i` replaced by the consequences where the chain of
weakenings stops. With `suppliers`, each such consequence a supplier proves is
discharged, and the theorem is named `…_supplied`; when every consequence is
discharged, hypothesis `i` is gone. An error when the chain adds nothing. -/
def frontierAt (name : Name) (i : Nat) (stops : Array Name) (suppliers : Array Name := #[]) :
    DeriveM (Except String Name) := do
  let some (wName, w) ← weakeningOf name i | return .error s!"hypothesis {i} has no weakening"
  let info ← getConstInfo name
  let mut plans : Array Plan := #[]
  for c in w.consequences, s in w.sites, a in w.arity do
    plans := plans.push (← plan stops 24 c s a)
  let leaves := plans.foldl (fun acc p => p.leaves acc) #[]
  let leafTypes := leaves.map (·.1)
  let mut supplied : Array (Option Expr) := #[]
  for (t, a) in leaves do
    supplied := supplied.push (← if suppliers.isEmpty then pure none else supplyLeaf t a suppliers)
  let discharged := (supplied.filter (·.isSome)).size
  if plans.all (·.depth == 0) && discharged == 0 then
    return .error s!"hypothesis {i}: the chain stops at the first weakening ({wName})"
  if !suppliers.isEmpty && discharged == 0 then
    return .error s!"hypothesis {i}: no supplier proves a consequence where the chain stops"
  let (type, value) ← frontierDecl info i wName plans leafTypes supplied
  let suffix := (match stops[0]? with
    | some n => "_" ++ n.getString!
    | none => "") ++ (if discharged > 0 then "_supplied" else "")
  let newName := name ++ Name.mkSimple s!"frontier_{i}{suffix}"
  if (← getEnv).contains newName then
    if ← existingTypeMatches newName info.levelParams type then return .ok newName
    return .error s!"{newName} already exists with a different statement"
  let stopText := if stops.isEmpty then "as far as the chain goes"
    else s!"keeping the use sites of {stops.toList}"
  let supplyText := if discharged == 0 then ""
    else s!" {discharged} of the {leafTypes.size} consequence(s) are discharged by {suppliers.toList}\
      {if discharged == leafTypes.size then ", so the hypothesis is gone" else ""}."
  let doc := s!"`{name}` with its hypothesis number {i} replaced by the {leafTypes.size} \
    consequence(s) reached by following the weakenings of the theorems its proof applies \
    that hypothesis to, {stopText}.{supplyText} Derived by `derive_frontier`."
  match ← addChecked newName info.levelParams type value doc with
  | .ok () => return .ok newName
  | .error e => return .error s!"kernel rejected {newName}: {e}"

/-! ## Commands -/

syntax (name := deriveIdleCmd) "derive_idle " ident : command
syntax (name := deriveWeakeningCmd) "derive_weakening " ident : command
syntax (name := deriveConjunctsCmd) "derive_conjuncts " ident : command
-- `at` and `using` are already Lean keywords, so the frontier command adds no new
-- token that would shadow an identifier in a module importing this one.
syntax (name := deriveFrontierCmd)
  "derive_frontier " ident (" at " ident+)? (" using " ident+)? : command

/-- The statement of an added theorem, on one line and at most `limit` characters,
so a build log stays readable. -/
def statementLine (n : Name) (limit : Nat := 600) : MetaM String := do
  let fmt ← withOptions (fun o => o.setBool `pp.proofs false)
    (ppExpr (← getConstInfo n).type)
  let flat := (toString fmt).replace "\n" " "
  let flat := " ".intercalate (flat.splitOn " " |>.filter (· ≠ ""))
  return if flat.length ≤ limit then flat else String.ofList (flat.toList.take limit) ++ " …"

def reportAdded (n : Name) : MetaM Unit := do
  logInfo m!"added {n} : {← statementLine n}"

@[command_elab deriveIdleCmd] def elabDeriveIdle : CommandElab := fun stx => do
  liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo stx[1]
    match ← deriveIdle name with
    | .ok n => reportAdded n
    | .error e => reportFailure m!"derive_idle {name}: {e}"

@[command_elab deriveConjunctsCmd] def elabDeriveConjuncts : CommandElab := fun stx => do
  liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo stx[1]
    match ← deriveConjuncts name with
    | .ok names => for n in names do reportAdded n
    | .error e => reportFailure m!"derive_conjuncts {name}: {e}"

@[command_elab deriveWeakeningCmd] def elabDeriveWeakening : CommandElab := fun stx => do
  liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo stx[1]
    let info ← getConstInfo name
    let n ← binderCount info
    let ((added, reasons), _) ← (do
      let mut added : Array Name := #[]
      let mut reasons : Array String := #[]
      for i in [0:n] do
        match ← weakeningResult name i with
        | .error e =>
          unless ["no_value", "no_binder", "not_a_proposition", "instance"].contains e do
            reasons := reasons.push s!"hypothesis {i}: {e}"
        | .ok (wName, w) =>
          added := added.push wName
          -- `H → Cⱼ`, when `H` is closed; `Cⱼ` is `∀ ps, Pⱼ ps` for a site with
          -- parameters `ps`.
          unless w.hypothesis.hasFVar do
            for s in w.sites, j in [0:w.sites.size] do
              let uName := name ++ Name.mkSimple s!"use_{i}_{j}"
              unless (← getEnv).contains uName do
                let type ← withLocalDeclD `h w.hypothesis fun h => do
                  mkForallFVars #[h] (← inferType (s.beta #[h]))
                let doc := s!"What `{name}` derives from its hypothesis number {i}: \
                  its use site number {j}."
                if (← addChecked uName info.levelParams type s doc) matches .ok () then
                  added := added.push uName
      return (added, reasons) : DeriveM (Array Name × Array String)).run {}
    if added.isEmpty then
      let why := if reasons.isEmpty then "" else s!" ({"; ".intercalate reasons.toList})"
      reportFailure m!"derive_weakening {name}: no hypothesis is used only through consequences{why}"
    for a in added do reportAdded a

@[command_elab deriveFrontierCmd] def elabDeriveFrontier : CommandElab := fun stx => do
  liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo stx[1]
    let stops ← if stx[2].isNone then pure #[]
      else stx[2][1].getArgs.mapM (fun s => realizeGlobalConstNoOverloadWithInfo s)
    let suppliers ← if stx[3].isNone then pure #[]
      else stx[3][1].getArgs.mapM (fun s => realizeGlobalConstNoOverloadWithInfo s)
    let info ← getConstInfo name
    let n ← binderCount info
    let (results, _) ← (do
      let mut results : Array (Except String Name) := #[]
      for i in [0:n] do
        if (← weakeningOf name i).isSome then
          results := results.push (← frontierAt name i stops suppliers)
      return results : DeriveM (Array (Except String Name))).run {}
    if results.isEmpty then
      reportFailure m!"derive_frontier {name}: no hypothesis is used only through consequences"
    for r in results do
      match r with
      | .ok a => reportAdded a
      | .error e => reportFailure m!"derive_frontier {name}: {e}"

end ErdosProblems.ArgumentGraph

-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0

/-!
# Factoring: each hypothesis at the claims whose proofs use it

A paper result often proves several claims about one construction and assumes a
named input that only some of the claims need. `derive_factor T` reads the proof
of `T` and adds `T.factored`: the statement of `T` with each proposition
hypothesis moved to the claims of the conclusion whose proofs use it. From a proof
of `H₁ → H₂ → ∃ w, A w ∧ B w ∧ C w` whose witness and whose proof of `A w` use
neither hypothesis, whose proof of `B w` uses only `H₁` and whose proof of `C w`
uses only `H₂`, it adds

  `T.factored : ∃ w, A w ∧ (H₁ → B w) ∧ (H₂ → C w)`,

with the proof's own witness. The two statements differ: the factored one says the
construction exists unconditionally and that each input is needed only for the
property it proves. A hypothesis that a witness needs stays above that `∃`; one
no claim needs is left out. The conclusion is read through `∃`, `∧` and `∀`
(implications included); anything else is one claim.

The proof is read after its spine is normalised: a `have` whose value uses a
hypothesis being moved is inlined; an elimination of a constructor is reduced
(`obtain ⟨a, b⟩ := ⟨x, y⟩` is `x, y`); an elimination whose major premise is
itself an elimination moves inside it; a compiled `match` is unfolded to its
eliminations. An application `L a₁ … aₘ` of a library theorem that passes it a
hypothesis being moved, and proves a structured claim, is replaced by
`L.factored` (derived first, recursively), rebuilt into `L`'s conclusion: this is
how the command follows a construction through the lemmas it is built from, so
that an input a lemma needs for one property does not stay attached to the
lemma's witness.

The reading only proposes where each hypothesis goes; every theorem the command
adds, including the library factorings it derives on the way, is checked by the
kernel before it is added.
-/

set_option autoImplicit false

open Lean Meta Elab Command

namespace ErdosProblems.ArgumentGraph

/-! ## Claims -/

/-- How factoring reads a claim: a conjunction, an existential `Exists.{u} α p`, a
`∀` or implication (binder name, domain, body with a loose bound variable, binder
info), or an atom. -/
inductive ClaimShape where
  | conj (left right : Expr)
  | ex (u : Level) (domain predicate : Expr)
  | pi (name : Name) (domain body : Expr) (bi : BinderInfo)
  | atom

def claimShape (g : Expr) : ClaimShape :=
  let g := g.consumeMData
  match g.and? with
  | some (a, b) => .conj a b
  | none =>
    if g.isAppOfArity ``Exists 2 then
      match g.getAppFn with
      | .const _ [u] => .ex u g.appFn!.appArg! g.appArg!
      | _ => .atom
    else
      match g with
      | .forallE n d b bi => .pi n d b bi
      | _ => .atom

/-- The claim `p w` of an existential with predicate `p`. -/
def predicateAt (p w : Expr) : Expr := (mkApp p w).headBeta

/-- The bound name of an existential's predicate, for readable statements. -/
def predicateBinder (p : Expr) : Name :=
  match p.consumeMData with
  | .lam n .. => n
  | _ => `w

/-! ## Placements and usage -/

/-- Where a factored statement assumes the hypotheses it moves: one node per claim
the conclusion is read into, each with the hypotheses assumed at that node (local
hypotheses while a proof is read, binder indices once a factoring is stored). -/
inductive Placement (α : Type) where
  | leaf (guards : Array α)
  | conj (guards : Array α) (left right : Placement α)
  | ex (guards : Array α) (body : Placement α)
  | pi (guards : Array α) (body : Placement α)

instance {α : Type} : Inhabited (Placement α) := ⟨.leaf #[]⟩

namespace Placement
variable {α β : Type}

def guards : Placement α → Array α
  | .leaf g | .conj g .. | .ex g .. | .pi g .. => g

def withGuards (g : Array α) : Placement α → Placement α
  | .leaf _ => .leaf g
  | .conj _ l r => .conj g l r
  | .ex _ b => .ex g b
  | .pi _ b => .pi g b

def map (f : α → β) : Placement α → Placement β
  | .leaf g => .leaf (g.map f)
  | .conj g l r => .conj (g.map f) (l.map f) (r.map f)
  | .ex g b => .ex (g.map f) (b.map f)
  | .pi g b => .pi (g.map f) (b.map f)

/-- Every guard of the tree, root first. -/
def allGuards : Placement α → Array α
  | .leaf g => g
  | .conj g l r => g ++ l.allGuards ++ r.allGuards
  | .ex g b => g ++ b.allGuards
  | .pi g b => g ++ b.allGuards

end Placement

/-- What the claims of a proof use: per atom, the hypotheses being moved that its
proof mentions, directly or through an elimination it sits under; per existential,
those its witness depends on. -/
inductive Usage where
  | leaf (uses : Array FVarId)
  | conj (left right : Usage)
  | ex (witness : Array FVarId) (body : Usage)
  | pi (body : Usage)

instance : Inhabited Usage := ⟨.leaf #[]⟩

def unionIds (a b : Array FVarId) : Array FVarId :=
  b.foldl (fun acc x => if acc.contains x then acc else acc.push x) a

namespace Usage

def addAll (d : Array FVarId) : Usage → Usage
  | .leaf u => .leaf (unionIds u d)
  | .conj l r => .conj (l.addAll d) (r.addAll d)
  | .ex w b => .ex (unionIds w d) (b.addAll d)
  | .pi b => .pi (b.addAll d)

def all : Usage → Array FVarId
  | .leaf u => u
  | .conj l r => unionIds l.all r.all
  | .ex w b => unionIds w b.all
  | .pi b => b.all

/-- The usage of a proof by cases: node by node, the union of the alternatives'. -/
def merge : Usage → Usage → Usage
  | .leaf d, u => u.addAll d
  | .conj l r, .conj l' r' => .conj (l.merge l') (r.merge r')
  | .ex w b, .ex w' b' => .ex (unionIds w w') (b.merge b')
  | .pi b, .pi b' => .pi (b.merge b')
  | u, .leaf d => u.addAll d
  | u, u' => .leaf (unionIds u.all u'.all)

/-- Each hypothesis at the lowest node that covers its uses and is not below a
witness that depends on it; `scope` are the hypotheses assumed above. -/
def place (scope : Array FVarId) : Usage → Placement FVarId
  | .leaf u => .leaf (u.filter (!scope.contains ·))
  | .conj l r => .conj #[] (l.place scope) (r.place scope)
  | .pi b => .pi #[] (b.place scope)
  | .ex w b =>
      let g := w.filter (!scope.contains ·)
      .ex g (b.place (scope ++ g))

end Usage

/-- Every guard in the order of `order` (the theorem's binders), so the moved
hypotheses keep their relative order. -/
def Placement.sortBy (order : Array FVarId) : Placement FVarId → Placement FVarId
  | .leaf g => .leaf (order.filter g.contains)
  | .conj g l r => .conj (order.filter g.contains) (l.sortBy order) (r.sortBy order)
  | .ex g b => .ex (order.filter g.contains) (b.sortBy order)
  | .pi g b => .pi (order.filter g.contains) (b.sortBy order)

/-! ## The factoring state -/

/-- A factoring of a library theorem: the factored theorem, the binders of the
source it keeps (by index, in order), the placement of the others over the source's
conclusion (guards by binder index), and whether some hypothesis moved below the
conclusion's first claim (otherwise the factoring only leaves out unused
hypotheses). -/
structure LibFactor where
  name : Name
  keep : Array Nat
  place : Placement Nat
  deep : Bool

structure FactorState where
  /-- Factorings of library theorems by name; `none` when there is none. -/
  library : Std.HashMap Name (Option LibFactor) := {}
  /-- Theorems whose factoring is under way: a cycle and depth guard. -/
  active : Array Name := #[]
  /-- Spine nodes visited by the whole command. -/
  work : Nat := 0
  /-- Theorems added, in order. -/
  added : Array Name := #[]
  /-- Per theorem added: each moved hypothesis and the claims that assume it. -/
  placements : Array (Name × String × String) := #[]

abbrev FactorM := StateRefT FactorState MetaM

/-- The number of spine nodes one command may visit. -/
def factorWork : Nat := 2000000

/-- The depth of the traversals of a proof's spine. -/
def spineFuel : Nat := 10000

/-- How deep factoring follows a construction into the lemmas it is built from. -/
def libraryDepth : Nat := 6

/-- The heartbeat budget (in thousands) of one command, and of each library factoring. -/
def factorBudget : Nat := 400000
def libraryBudget : Nat := 150000

def tick : FactorM Unit := do
  let s ← get
  if s.work ≥ factorWork then throwError "the spine has more than {factorWork} nodes"
  set { s with work := s.work + 1 }

/-- Run `x` with its own heartbeat budget (in thousands); `none` when the budget runs
out or `x` throws. -/
def factorBudgeted {α : Type} (heartbeats : Nat) (x : FactorM α) : FactorM (Option α) := do
  withCurrHeartbeats <|
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := heartbeats * 1000 }) do
      tryCatchRuntimeEx (do return some (← x)) fun _ => return none

/-- Whether a constant is a theorem. -/
def isTheoremInfo : ConstantInfo → Bool
  | .thmInfo _ => true
  | _ => false

/-- The name of the factoring of `name`: `name.factored` for a theorem of this library
(or of the file being checked), and `ErdosProblems.ArgumentGraph.Factored.<name>` for
one imported from another library, so that nothing is added in another library's
namespace. -/
def factoredName (name : Name) : MetaM Name := do
  let env ← getEnv
  match env.getModuleIdxFor? name with
  | none => return name ++ `factored
  | some idx =>
    let module := env.header.moduleNames[idx.toNat]!
    if (`ErdosProblems).isPrefixOf module || (`Erdos249257).isPrefixOf module then
      return name ++ `factored
    return `ErdosProblems.ArgumentGraph.Factored ++ name

/-- The hypotheses of `mv` that `e` mentions. -/
def movedIn (mv : Array FVarId) (e : Expr) : Array FVarId :=
  if e.hasFVar then mv.filter (e.containsFVar ·) else #[]

/-! ## Eliminations -/

/-- The body of a motive `fun xs => b` with `n` binders when `b` mentions none of them. -/
def constMotiveBody? (motive : Expr) (n : Nat) : MetaM (Option Expr) :=
  lambdaBoundedTelescope motive n fun xs body => do
    unless xs.size == n do return none
    -- an unfolded `match` leaves its motive applied to the discriminants
    let body := body.headBeta
    if xs.any (fun x => body.containsFVar x.fvarId!) then return none
    return some body

/-- `e` as a `casesOn` application. -/
def casesApp? (e : Expr) : MetaM (Option MatcherApp) := do
  let some app ← matchMatcherApp? e (alsoCasesOn := true) | return none
  unless isCasesOnRecursor (← getEnv) app.matcherName do return none
  return some app

/-- `app` with its major premise replaced. -/
def withMajor (app : MatcherApp) (major : Expr) : MatcherApp :=
  { app with discrs := app.discrs.pop.push major }

/-- Open an alternative's `n` fields, eta-expanding when it is not a function of all
of them syntactically. -/
def altTelescope {α : Type} (alt : Expr) (n : Nat) (k : Array Expr → Expr → FactorM α) :
    FactorM α :=
  lambdaBoundedTelescope alt n fun xs body => do
    if xs.size == n then k xs body
    else
      let ty ← inferType body
      forallBoundedTelescope ty (some (n - xs.size)) fun ys _ => do
        unless xs.size + ys.size == n do
          throwError "an alternative is not a function of its fields"
        k (xs ++ ys) (mkAppN body ys).headBeta

/-- `app` eliminating into `ty` (which ignores the discriminants) with the
alternatives `alts`. -/
def rebuildCases (app : MatcherApp) (ty : Expr) (alts : Array Expr) : MetaM Expr := do
  let motive ← lambdaBoundedTelescope app.motive app.discrs.size fun xs _ => mkLambdaFVars xs ty
  let levels ← match app.uElimPos? with
    | some p => do
        let l ← getLevel ty
        pure (app.matcherLevels.modify p fun _ => l)
    | none => pure app.matcherLevels
  return { app with motive, matcherLevels := levels, alts, remaining := #[] }.toExpr

/-- The `i`-th component of a proof of a conjunction. -/
def projAnd (i : Nat) (e : Expr) : Expr :=
  if e.isAppOfArity ``And.intro 4 then e.getAppArgs[2 + i]! else .proj ``And i e

/-- The `i`-th component of an elimination proving a conjunction, as an elimination
proving that component. -/
def projectAlts? (app : MatcherApp) (i : Nat) : FactorM (Option Expr) := do
  unless app.remaining.isEmpty do return none
  let some body ← constMotiveBody? app.motive app.discrs.size | return none
  let some (a, b) := body.consumeMData.and? | return none
  let mut alts : Array Expr := #[]
  for alt in app.alts, k in [0:app.alts.size] do
    alts := alts.push (← altTelescope alt (app.altNumParams[k]!) fun xs e =>
      mkLambdaFVars xs (projAnd i e))
  return some (← rebuildCases app (if i == 0 then a else b) alts)

/-- An elimination proving a `∀`, applied to `x`, as an elimination proving `ty`. -/
def applyAlts? (app : MatcherApp) (x ty : Expr) : FactorM (Option Expr) := do
  unless app.remaining.isEmpty do return none
  unless (← constMotiveBody? app.motive app.discrs.size).isSome do return none
  let mut alts : Array Expr := #[]
  for alt in app.alts, k in [0:app.alts.size] do
    alts := alts.push (← altTelescope alt (app.altNumParams[k]!) fun xs e =>
      mkLambdaFVars xs (mkApp e x).headBeta)
  return some (← rebuildCases app ty alts)

/-- An elimination applied to arguments past its alternatives, with the arguments
moved into the alternatives. -/
def pushRemaining? (app : MatcherApp) : FactorM (Option Expr) := do
  let some body ← constMotiveBody? app.motive app.discrs.size | return none
  let some ty ← (try some <$> instantiateForall body app.remaining catch _ => pure none) | return none
  let mut alts : Array Expr := #[]
  for alt in app.alts, k in [0:app.alts.size] do
    alts := alts.push (← altTelescope alt (app.altNumParams[k]!) fun xs e =>
      mkLambdaFVars xs (mkAppN e app.remaining).headBeta)
  return some (← rebuildCases { app with remaining := #[] } ty alts)

/-- The elimination of a constructor, reduced. -/
def iota? (app : MatcherApp) (major : Expr) : MetaM (Option Expr) := do
  unless app.remaining.isEmpty do return none
  let .const c _ := major.getAppFn | return none
  let some (.ctorInfo ci) := (← getEnv).find? c | return none
  unless ci.induct == app.matcherName.getPrefix do return none
  let args := major.getAppArgs
  unless args.size == ci.numParams + ci.numFields do return none
  let some alt := app.alts[ci.cidx]? | return none
  return some (mkAppN alt (args.extract ci.numParams args.size)).headBeta

/-- An elimination whose major premise is an elimination, with the outer one moved
inside the inner one's alternatives. Both motives must ignore their arguments. -/
def commute? (outer : MatcherApp) (major : Expr) : FactorM (Option Expr) := do
  unless outer.remaining.isEmpty do return none
  let some inner ← casesApp? major | return none
  unless inner.remaining.isEmpty do return none
  let some resultType ← constMotiveBody? outer.motive outer.discrs.size | return none
  unless (← constMotiveBody? inner.motive inner.discrs.size).isSome do return none
  let mut alts : Array Expr := #[]
  for alt in inner.alts, k in [0:inner.alts.size] do
    alts := alts.push (← altTelescope alt (inner.altNumParams[k]!) fun xs e =>
      mkLambdaFVars xs (withMajor outer e).toExpr)
  return some (← rebuildCases inner resultType alts)

/-- Whether a claim, under its leading `∀`s, is a conjunction or an existential. -/
def structuredClaim (ty : Expr) : Bool :=
  let body := ty.getForallBody.consumeMData
  body.isAppOfArity ``And 2 || body.isAppOfArity ``Exists 2

/-! ## Rebuilding a claim from its factored form -/

/-- A proof of `g` from a proof `y` of its factoring by `p`, whose guards are the
arguments each node is given. -/
def unfactorAux : Nat → Expr → Placement Expr → Expr → MetaM Expr
  | 0, _, _, _ => throwError "the claim is nested too deeply"
  | fuel + 1, y, p, g => do
    let y := mkAppN y p.guards
    match p, claimShape g with
    | .leaf _, _ => return y
    | .conj _ l r, .conj a b =>
        return mkApp4 (mkConst ``And.intro) a b (← unfactorAux fuel (.proj ``And 0 y) l a)
          (← unfactorAux fuel (.proj ``And 1 y) r b)
    | .pi _ b, .pi n d body bi =>
        withLocalDecl n bi d fun x => do
          mkLambdaFVars #[x] (← unfactorAux fuel (mkApp y x) b (body.instantiate1 x))
    | .ex _ b, .ex u α pred => do
        let yType := (← whnfR (← inferType y)).consumeMData
        unless yType.isAppOfArity ``Exists 2 do throwError "a factored claim is not an existential"
        let factoredPred := yType.appArg!
        let motive := Expr.lam `h yType g .default
        let alt ← withLocalDecl (predicateBinder pred) .default α fun w => do
          withLocalDecl `h .default (predicateAt factoredPred w) fun q => do
            let inner ← unfactorAux fuel q b (predicateAt pred w)
            mkLambdaFVars #[w, q] (mkApp4 (mkConst ``Exists.intro [u]) α pred w inner)
        return mkAppN (mkConst ``Exists.casesOn [u]) #[α, factoredPred, motive, y, alt]
    | _, _ => throwError "the claim does not have the shape of its factoring"

/-! ## Building the factored claim -/

mutual
/-- The factored claim: `g` with the guards of `p` assumed at each node. -/
def buildClaimAux : Nat → Placement FVarId → Expr → MetaM Expr
  | 0, _, g => return g
  | fuel + 1, p, g => do mkForallFVars (p.guards.map mkFVar) (← buildInnerAux fuel p g)

/-- The factored claim without the guards of its root. -/
def buildInnerAux : Nat → Placement FVarId → Expr → MetaM Expr
  | 0, _, g => return g
  | fuel + 1, p, g => do
    match p, claimShape g with
    | .conj _ l r, .conj a b => return mkAnd (← buildClaimAux fuel l a) (← buildClaimAux fuel r b)
    | .pi _ b, .pi n d gb bi =>
        withLocalDecl n bi d fun x => do mkForallFVars #[x] (← buildClaimAux fuel b (gb.instantiate1 x))
    | .ex _ b, .ex u α pred =>
        let factoredPred ← withLocalDecl (predicateBinder pred) .default α fun x => do
          mkLambdaFVars #[x] (← buildClaimAux fuel b (predicateAt pred x))
        return mkApp2 (mkConst ``Exists [u]) α factoredPred
    | _, _ => return g
end

/-- Whether some node below the root assumes something. -/
def Placement.hasInnerGuards {α : Type} (p : Placement α) : Bool :=
  !(p.withGuards #[]).allGuards.isEmpty

mutual
/-- A proof of the factored claim from a proof `e` of `g` that needs no hypothesis
out of scope: every guard is assumed and ignored. -/
def liftAux : Nat → Placement FVarId → Expr → Expr → MetaM Expr
  | 0, _, _, e => return e
  | fuel + 1, p, g, e => do mkLambdaFVars (p.guards.map mkFVar) (← liftInnerAux fuel p g e)

def liftInnerAux : Nat → Placement FVarId → Expr → Expr → MetaM Expr
  | 0, _, _, e => return e
  | fuel + 1, p, g, e => do
    unless p.hasInnerGuards do return e
    match p, claimShape g with
    | .conj _ l r, .conj a b =>
        return mkApp4 (mkConst ``And.intro) (← buildClaimAux fuel l a) (← buildClaimAux fuel r b)
          (← liftAux fuel l a (projAnd 0 e)) (← liftAux fuel r b (projAnd 1 e))
    | .pi _ b, .pi n d gb bi =>
        withLocalDecl n bi d fun x => do
          mkLambdaFVars #[x] (← liftAux fuel b (gb.instantiate1 x) (mkApp e x).headBeta)
    | .ex _ b, .ex u α pred =>
        let ty ← buildInnerAux fuel p g
        let factoredPred ← withLocalDecl (predicateBinder pred) .default α fun x => do
          mkLambdaFVars #[x] (← buildClaimAux fuel b (predicateAt pred x))
        let motive := Expr.lam `h g ty .default
        let alt ← withLocalDecl (predicateBinder pred) .default α fun w => do
          withLocalDecl `h .default (predicateAt pred w) fun q => do
            let inner ← liftAux fuel b (predicateAt pred w) q
            mkLambdaFVars #[w, q] (mkApp4 (mkConst ``Exists.intro [u]) α factoredPred w inner)
        return mkAppN (mkConst ``Exists.casesOn [u]) #[α, pred, motive, e, alt]
    | _, _ => return e
end

/-- Per guard of a placement, the first and last claim number below its node (claims
numbered from `k` in the order the conclusion states them); and the next number. -/
def Placement.claimSpans : Placement FVarId → Nat → Array (FVarId × Nat × Nat) × Nat
  | .leaf g, k => (g.map fun h => (h, k, k), k + 1)
  | .conj g l r, k =>
      let (sl, k₁) := l.claimSpans k
      let (sr, k₂) := r.claimSpans k₁
      (g.map (fun h => (h, k, k₂ - 1)) ++ sl ++ sr, k₂)
  | .ex g b, k =>
      let (sb, k₁) := b.claimSpans k
      (g.map (fun h => (h, k, k₁ - 1)) ++ sb, k₁)
  | .pi g b, k =>
      let (sb, k₁) := b.claimSpans k
      (g.map (fun h => (h, k, k₁ - 1)) ++ sb, k₁)

/-- Whether the factoring says more than the theorem without its unused hypotheses:
some hypothesis it keeps is assumed by some claims and not by others. When every
hypothesis a proof uses is still assumed by every claim, the factored statement is
the original one with its premises moved inward, which says nothing new. -/
def Placement.separates (p : Placement FVarId) (moved : Array FVarId) : Bool :=
  let (spans, next) := p.claimSpans 1
  moved.any fun h =>
    let here := spans.filter (·.1 == h)
    !here.isEmpty && here.foldl (fun n (_, a, b) => n + (b + 1 - a)) 0 < next - 1

/-- The claims of a conclusion read along a placement, pretty-printed on one line
(binders opened under their own names), in the order the conclusion states them. -/
def leafClaimTexts : Nat → Placement FVarId → Expr → MetaM (Array String)
  | 0, _, g => return #[flat (toString (← ppExpr g))]
  | fuel + 1, p, g => do
    match p, claimShape g with
    | .conj _ l r, .conj a b => return (← leafClaimTexts fuel l a) ++ (← leafClaimTexts fuel r b)
    | .pi _ b, .pi n d gb bi =>
        withLocalDecl n bi d fun x => leafClaimTexts fuel b (gb.instantiate1 x)
    | .ex _ b, .ex _ α pred =>
        withLocalDecl (predicateBinder pred) .default α fun x => leafClaimTexts fuel b (predicateAt pred x)
    | _, _ => return #[flat (toString (← ppExpr g))]
where
  flat (s : String) : String := " ".intercalate ((s.replace "\n" " ").splitOn " " |>.filter (· ≠ ""))

/-- The docstring of a factored theorem, and per moved hypothesis where it went:
claims are numbered from 1 in the order the conclusion states them. -/
def factorDoc (name : Name) (xs : Array Expr) (moved : Array FVarId)
    (inner : Placement FVarId) (body : Expr) : MetaM (String × Array (String × String)) := do
  let (spans, total) := inner.claimSpans 1
  let texts ← leafClaimTexts spineFuel inner body
  let mut parts : Array String := #[]
  let mut placed : Array (String × String) := #[]
  for h in moved do
    let some x := xs.find? (·.fvarId! == h) | continue
    let ty := toString (← ppExpr (← inferType x))
    let at_ := spans.filter (·.1 == h)
    if at_.isEmpty then
      parts := parts.push s!"`{ty}` is not used"
      placed := placed.push (ty, "unused")
    else
      let where_ := at_.map fun (_, a, b) => if a == b then s!"claim {a}" else s!"claims {a}-{b}"
      parts := parts.push s!"`{ty}` is assumed by {", ".intercalate where_.toList}"
      let shown := at_.map fun (_, a, b) =>
        if a == b then s!"claim {a}: {(texts[a - 1]?).getD ""}" else s!"claims {a}-{b}"
      placed := placed.push (ty, "; ".intercalate shown.toList)
  let doc := s!"`{name}` with each hypothesis assumed only by the claims whose proofs use it \
    (claims numbered 1 to {total - 1} as the conclusion states them): \
    {"; ".intercalate parts.toList}. The witnesses are those of the same proof. \
    Derived by `derive_factor`."
  return (doc, placed)

/-! ## Normalising the spine, and following a construction into the library -/

mutual
/-- `e` with its spine normalised (see the module docstring); `mv` are the
hypotheses being moved. -/
def normAux : Nat → Array FVarId → Expr → FactorM Expr
  | 0, _, e => return e
  | fuel + 1, mv, e => do
    tick
    match e with
    | .mdata _ b => normAux fuel mv b
    | .letE n t v b _ =>
        if !(movedIn mv v).isEmpty then normAux fuel mv (b.instantiate1 v)
        else withLetDecl n t v fun x => do
          mkLetFVars #[x] (← normAux fuel mv (b.instantiate1 x)) (generalizeNondepLet := false)
    | .lam n t b bi =>
        withLocalDecl n bi t fun x => do mkLambdaFVars #[x] (← normAux fuel mv (b.instantiate1 x))
    | .proj s i b =>
        let b' ← normAux fuel mv b
        if s == ``And then
          if b'.isAppOfArity ``And.intro 4 then return ← normAux fuel mv b'.getAppArgs[2 + i]!
          if let some app ← casesApp? b' then
            if let some r ← projectAlts? app i then return ← normAux fuel mv r
        return .proj s i b'
    | .app .. => normAppAux fuel mv e
    | _ => return e

def normAppAux : Nat → Array FVarId → Expr → FactorM Expr
  | 0, _, e => return e
  | fuel + 1, mv, e => do
    let e' := e.headBeta
    if e' != e then return ← normAux fuel mv e'
    if e.isAppOfArity ``id 2 then return ← normAux fuel mv e.appArg!
    if e.isAppOfArity `letFun 4 then
      let args := e.getAppArgs
      match args[3]! with
      | .lam n t b _ => return ← normAux fuel mv (.letE n t args[2]! b false)
      | f => return ← normAux fuel mv (mkApp f args[2]!)
    if e.isAppOfArity ``Exists.elim 5 then
      if let .const _ us := e.getAppFn then
        let args := e.getAppArgs
        let motive := Expr.lam `h (mkApp2 (mkConst ``Exists us) args[0]! args[1]!) args[2]! .default
        return ← normAux fuel mv
          (mkAppN (mkConst ``Exists.casesOn us) #[args[0]!, args[1]!, motive, args[3]!, args[4]!])
    if e.isAppOfArity ``Exists.intro 4 then
      let args := e.getAppArgs
      return mkAppN e.getAppFn #[args[0]!, args[1]!, args[2]!, ← normAux fuel mv args[3]!]
    if e.isAppOfArity ``And.intro 4 then
      let args := e.getAppArgs
      return mkAppN e.getAppFn #[args[0]!, args[1]!, ← normAux fuel mv args[2]!,
        ← normAux fuel mv args[3]!]
    if let some app ← matchMatcherApp? e (alsoCasesOn := true) then
      if isCasesOnRecursor (← getEnv) app.matcherName then return ← normCasesAux fuel mv app
      -- a compiled `match` is an elimination by its definition (`unfoldDefinition?`
      -- declines matchers, so the definition is instantiated here)
      if let some (.defnInfo d) := (← getEnv).find? app.matcherName then
        if d.levelParams.length == app.matcherLevels.size then
          let value := d.value.instantiateLevelParams d.levelParams app.matcherLevels.toList
          return ← normAux fuel mv (mkAppN value e.getAppArgs).headBeta
      return e
    -- a library theorem given a hypothesis being moved, proving a structured claim
    if !(movedIn mv e).isEmpty then
      if structuredClaim (← instantiateMVars (← inferType e)) then
        if let some r ← substLibraryAux fuel mv e then return ← normAux fuel mv r
    return e

def normCasesAux : Nat → Array FVarId → MatcherApp → FactorM Expr
  | 0, _, app => return app.toExpr
  | fuel + 1, mv, app => do
    if !app.remaining.isEmpty then
      if let some r ← pushRemaining? app then return ← normAux fuel mv r
      return app.toExpr
    let mut major ← normAux fuel mv app.discrs.back!
    -- a `let` variable stands for its value
    if let .fvar id := major then
      if let some v := (← id.getDecl).value? then
        if (← iota? app v).isSome || (← casesApp? v).isSome then major := v
    let app := withMajor app major
    if let some r ← iota? app major then return ← normAux fuel mv r
    if let some r ← commute? app major then return ← normAux fuel mv r
    let mut alts : Array Expr := #[]
    for alt in app.alts, k in [0:app.alts.size] do
      alts := alts.push (← altTelescope alt (app.altNumParams[k]!) fun xs body => do
        mkLambdaFVars xs (← normAux fuel mv body))
    return { app with alts }.toExpr

/-- `L a₁ … aₘ` rebuilt from `L.factored` when some `aⱼ` mentions a hypothesis being
moved and `L`'s factoring takes the `j`-th hypothesis away from `L`'s top level. -/
def substLibraryAux : Nat → Array FVarId → Expr → FactorM (Option Expr)
  | 0, _, _ => return none
  | fuel + 1, mv, e => do
    let .const L us := e.getAppFn | return none
    let some info := (← getEnv).find? L | return none
    unless isTheoremInfo info do return none
    let args := e.getAppArgs
    let n ← forallTelescope info.type fun xs _ => return xs.size
    unless args.size == n do return none
    let some lf ← factorLibraryAux fuel L | return none
    let hot := (Array.range n).filter fun j => !(movedIn mv args[j]!).isEmpty
    unless hot.any (fun j => !lf.keep.contains j) do return none
    let conclusion ← instantiateForall (info.type.instantiateLevelParams info.levelParams us) args
    let y := mkAppN (mkConst lf.name us) (lf.keep.map (args[·]!))
    return some (← unfactorAux spineFuel y (lf.place.map (args[·]!)) conclusion)

/-- The factoring of a library theorem, derived (and added) the first time it is
needed. -/
def factorLibraryAux : Nat → Name → FactorM (Option LibFactor)
  | 0, _ => return none
  | fuel + 1, L => do
    if let some r := (← get).library.get? L then return r
    let s ← get
    if s.active.contains L || s.active.size ≥ libraryDepth then return none
    set { s with active := s.active.push L }
    let r ← factorBudgeted libraryBudget (factorTheoremAux fuel L false)
    let r := match r with
      | some (.ok lf) => some lf
      | _ => none
    modify fun s => { s with active := s.active.pop, library := s.library.insert L r }
    return r

/-- Factor theorem `name`: add `name.factored` and return where it put each moved
hypothesis. With `requireDeep`, an error when no hypothesis moves below the
conclusion's first claim (leaving out unused hypotheses is `derive_idle`). -/
def factorTheoremAux : Nat → Name → Bool → FactorM (Except String LibFactor)
  | 0, _, _ => return .error "the library is nested too deeply"
  | fuel + 1, name, requireDeep => do
    let info ← getConstInfo name
    let some value := info.value? | return .error "not a theorem with a proof term"
    unless isTheoremInfo info do return .error "not a theorem"
    forallTelescope info.type fun xs body => do
      let mut mv : Array FVarId := #[]
      for x in xs, i in [0:xs.size] do
        let decl ← x.fvarId!.getDecl
        if decl.binderInfo == .instImplicit then continue
        unless ← isProp decl.type do continue
        if body.containsFVar x.fvarId! then continue
        let mut later := false
        for j in [i+1:xs.size] do
          if (← xs[j]!.fvarId!.getDecl).type.containsFVar x.fvarId! then
            later := true
            break
        unless later do mv := mv.push x.fvarId!
      if mv.isEmpty then return .error "it has no proposition hypothesis that could move"
      let proof ← normAux fuel mv (← instantiateMVars (value.beta xs))
      let usage ← analyzeAux fuel mv proof body #[]
      let order := xs.map (·.fvarId!)
      let place := (usage.place #[]).sortBy order
      let top := place.guards
      let moved := mv.filter (!top.contains ·)
      if moved.isEmpty then
        return .error "every hypothesis its proof uses is needed before the conclusion's first claim"
      let inner := place.withGuards #[]
      let deep := inner.separates moved
      if requireDeep && !deep then
        return .error (if inner.hasInnerGuards
          then "every hypothesis it moves is still assumed by every claim, which says nothing new"
          else "it only leaves out hypotheses the proof never uses, which derive_idle adds")
      let keep := xs.filter fun x => !moved.contains x.fvarId!
      let type ← instantiateMVars (← mkForallFVars keep (← buildInnerAux spineFuel inner body))
      let proofBody ← factorInnerAux fuel mv inner body proof top
      let value ← instantiateMVars (← mkLambdaFVars keep proofBody)
      if type.hasFVar || type.hasMVar || value.hasFVar || value.hasMVar then
        return .error "the factored proof uses a hypothesis outside the claims that assume it"
      let newName ← factoredName name
      let (doc, placed) ← factorDoc name xs moved inner body
      match ← addChecked newName info.levelParams type value doc with
      | .error e => return .error s!"kernel rejected {newName}: {e}"
      | .ok () =>
        let rows : Array (Name × String × String) := placed.map fun (h, w) => (newName, h, w)
        modify fun s => { s with added := s.added.push newName, placements := s.placements ++ rows }
        let index : FVarId → Nat := fun h => (order.findIdx? (· == h)).getD 0
        let keepIdx := (Array.range xs.size).filter fun j => !moved.contains order[j]!
        return .ok { name := newName, keep := keepIdx, place := inner.map index, deep }

/-- What the claims of `e`, a proof of `g`, use of the hypotheses `mv`; `ctrl` are
those the eliminations above `e` depend on. -/
def analyzeAux : Nat → Array FVarId → Expr → Expr → Array FVarId → FactorM Usage
  | 0, mv, e, _, ctrl => return .leaf (unionIds ctrl (movedIn mv e))
  | fuel + 1, mv, e, g, ctrl => do
    tick
    let d := movedIn mv e
    if d.isEmpty then return .leaf ctrl
    match e with
    | .mdata _ b => analyzeAux fuel mv b g ctrl
    | .letE n t v b _ =>
        let ctrl := unionIds ctrl (movedIn mv v)
        withLetDecl n t v fun x => analyzeAux fuel mv (b.instantiate1 x) g ctrl
    | .lam n t b bi =>
        match claimShape g with
        | .pi _ _ gb _ =>
            withLocalDecl n bi t fun x => do
              return .pi (← analyzeAux fuel mv (b.instantiate1 x) (gb.instantiate1 x) ctrl)
        | _ => return .leaf (unionIds ctrl d)
    | _ =>
      if let some app ← casesApp? e then
        if app.remaining.isEmpty && (← constMotiveBody? app.motive app.discrs.size).isSome then
          let heads := app.params ++ app.discrs
          let ctrl' := heads.foldl (fun acc h => unionIds acc (movedIn mv h)) ctrl
          let mut acc : Option Usage := none
          for alt in app.alts, k in [0:app.alts.size] do
            let u ← altTelescope alt (app.altNumParams[k]!) fun _ body =>
              analyzeAux fuel mv body g ctrl'
            acc := some (match acc with
              | none => u
              | some a => a.merge u)
          return acc.getD (.leaf ctrl')
      match claimShape g with
      | .ex _ _ pred =>
          if e.isAppOfArity ``Exists.intro 4 then
            let args := e.getAppArgs
            return .ex (unionIds ctrl (movedIn mv args[2]!))
              (← analyzeAux fuel mv args[3]! (predicateAt pred args[2]!) ctrl)
          return .leaf (unionIds ctrl d)
      | .conj a b =>
          if e.isAppOfArity ``And.intro 4 then
            let args := e.getAppArgs
            return .conj (← analyzeAux fuel mv args[2]! a ctrl) (← analyzeAux fuel mv args[3]! b ctrl)
          return .leaf (unionIds ctrl d)
      | _ => return .leaf (unionIds ctrl d)

/-- A proof of the factored claim (guards of `p` included) from a normalised proof `e`
of `g`; `scope` are the moved hypotheses assumed above. -/
def factorProofAux : Nat → Array FVarId → Placement FVarId → Expr → Expr → Array FVarId →
    FactorM Expr
  | 0, _, _, _, _, _ => throwError "the proof is nested too deeply"
  | fuel + 1, mv, p, g, e, scope => do
    let gs := p.guards
    mkLambdaFVars (gs.map mkFVar) (← factorInnerAux fuel mv p g e (scope ++ gs))

/-- A proof of the factored claim without the guards of its root. -/
def factorInnerAux : Nat → Array FVarId → Placement FVarId → Expr → Expr → Array FVarId →
    FactorM Expr
  | 0, _, _, _, _, _ => throwError "the proof is nested too deeply"
  | fuel + 1, mv, p, g, e, scope => do
    tick
    if (movedIn mv e).all scope.contains then return ← liftInnerAux spineFuel p g e
    match e with
    | .mdata _ b => factorInnerAux fuel mv p g b scope
    | .letE n t v b _ =>
        withLetDecl n t v fun x => do
          mkLetFVars #[x] (← factorInnerAux fuel mv p g (b.instantiate1 x) scope)
            (generalizeNondepLet := false)
    | .lam n t b bi =>
        match p, claimShape g with
        | .pi _ pb, .pi _ _ gb _ =>
            withLocalDecl n bi t fun x => do
              mkLambdaFVars #[x] (← factorProofAux fuel mv pb (gb.instantiate1 x) (b.instantiate1 x) scope)
        | _, _ => throwError "a function proves a claim that is not a ∀"
    | _ =>
      if let some app ← casesApp? e then
        if app.remaining.isEmpty && (← constMotiveBody? app.motive app.discrs.size).isSome then
          let heads := app.params ++ app.discrs
          if heads.all (fun h => (movedIn mv h).all scope.contains) then
            let ty ← buildInnerAux spineFuel p g
            let mut alts : Array Expr := #[]
            for alt in app.alts, k in [0:app.alts.size] do
              alts := alts.push (← altTelescope alt (app.altNumParams[k]!) fun xs body => do
                mkLambdaFVars xs (← factorInnerAux fuel mv p g body scope))
            return ← rebuildCases app ty alts
          -- the elimination needs a hypothesis not yet assumed: split it over the claims
          match p, claimShape g with
          | .conj _ pl pr, .conj a b =>
              let some ea ← projectAlts? app 0 | throwError "cannot split an elimination over a conjunction"
              let some eb ← projectAlts? app 1 | throwError "cannot split an elimination over a conjunction"
              let ea ← normAux fuel mv ea
              let eb ← normAux fuel mv eb
              return mkApp4 (mkConst ``And.intro) (← buildClaimAux spineFuel pl a)
                (← buildClaimAux spineFuel pr b) (← factorProofAux fuel mv pl a ea scope)
                (← factorProofAux fuel mv pr b eb scope)
          | .pi _ pb, .pi n d gb bi =>
              return ← withLocalDecl n bi d fun x => do
                let some ex ← applyAlts? app x (gb.instantiate1 x) | throwError "cannot apply an elimination"
                let ex ← normAux fuel mv ex
                mkLambdaFVars #[x] (← factorProofAux fuel mv pb (gb.instantiate1 x) ex scope)
          | _, _ => throwError "an elimination on a hypothesis that is not assumed decides a witness"
      match p, claimShape g with
      | .ex _ pb, .ex u α pred =>
          unless e.isAppOfArity ``Exists.intro 4 do throwError "no witness is exposed"
          let args := e.getAppArgs
          let w := args[2]!
          unless (movedIn mv w).all scope.contains do
            throwError "a witness uses a hypothesis that is not assumed"
          let factoredPred ← withLocalDecl (predicateBinder pred) .default α fun x => do
            mkLambdaFVars #[x] (← buildClaimAux spineFuel pb (predicateAt pred x))
          let q ← factorProofAux fuel mv pb (predicateAt pred w) args[3]! scope
          return mkApp4 (mkConst ``Exists.intro [u]) α factoredPred w q
      | .conj _ pl pr, .conj a b =>
          let ea := if e.isAppOfArity ``And.intro 4 then e.getAppArgs[2]! else .proj ``And 0 e
          let eb := if e.isAppOfArity ``And.intro 4 then e.getAppArgs[3]! else .proj ``And 1 e
          return mkApp4 (mkConst ``And.intro) (← buildClaimAux spineFuel pl a)
            (← buildClaimAux spineFuel pr b) (← factorProofAux fuel mv pl a ea scope)
            (← factorProofAux fuel mv pr b eb scope)
      | .pi _ pb, .pi n d gb bi =>
          withLocalDecl n bi d fun x => do
            mkLambdaFVars #[x] (← factorProofAux fuel mv pb (gb.instantiate1 x) (mkApp e x).headBeta scope)
      | _, _ => throwError "a claim uses a hypothesis that is not assumed"

end

/-- `derive_factor`'s entry: factor `name`, requiring some hypothesis to move below
the conclusion's first claim. -/
def factorTheorem (name : Name) : FactorM (Except String LibFactor) :=
  factorTheoremAux spineFuel name true

/-! ## The command -/

syntax (name := deriveFactorCmd) "derive_factor " ident : command

@[command_elab deriveFactorCmd] def elabDeriveFactor : CommandElab := fun stx => do
  liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo stx[1]
    let (r, s) ← (factorBudgeted factorBudget (factorTheorem name)).run {}
    -- library factorings derived on the way are theorems in their own right
    let own ← factoredName name
    for n in s.added do
      unless n == own do reportAdded n
    match r with
    | some (.ok lf) => reportAdded lf.name
    | some (.error e) => reportFailure m!"derive_factor {name}: {e}"
    | none => reportFailure m!"derive_factor {name}: the budget ran out (unknown)"
    -- one line per moved hypothesis, for the frontier's input map
    for (n, h, w) in s.placements do
      logInfo m!"placed {n} :: {h} :: {w}"

end ErdosProblems.ArgumentGraph

/-! Frontier probe for Erdos257. -/

set_option maxHeartbeats 4000000

run_cmd Lean.logInfo "@@COMMAND 2054"
derive_idle ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_divisorResidueSum
run_cmd Lean.logInfo "@@COMMAND 2056"
derive_idle ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_geometricForm
run_cmd Lean.logInfo "@@COMMAND 2058"
derive_idle ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_tsum_divisorResidue
run_cmd Lean.logInfo "@@COMMAND 2060"
derive_idle ErdosProblems.Erdos257.PaperCompleteR21.arithmetic_logarithmic_counterexample
run_cmd Lean.logInfo "@@COMMAND 2062"
derive_idle ErdosProblems.Erdos257.PaperCompleteR21.logarithmic_initial_interval
run_cmd Lean.logInfo "@@COMMAND 2064"
derive_idle ErdosProblems.Erdos257.PaperCompleteR21.paper_effective_horizon_test
run_cmd Lean.logInfo "@@COMMAND 2066"
derive_idle ErdosProblems.Erdos257.PaperCompleteR21.paper_mersenne_channel_survival
run_cmd Lean.logInfo "@@COMMAND 2068"
derive_idle ErdosProblems.Erdos257.PaperCompleteR21.paper_one_orbit_stability
run_cmd Lean.logInfo "@@COMMAND 2070"
derive_idle ErdosProblems.Erdos257.PaperCompleteR21.paper_shared_prefix_family_strip_witness_after_feedback_of_all_depths
run_cmd Lean.logInfo "@@COMMAND 2072"
derive_idle ErdosProblems.Erdos257.PaperCompleteR21.paper_zero_run_le_eps_logb
run_cmd Lean.logInfo "@@COMMAND 2074"
derive_weakening Erdos249257.HalfCarryReachability.greedy_half_infinite_of_cofinalStripReturn
run_cmd Lean.logInfo "@@COMMAND 2076"
derive_frontier Erdos249257.HalfCarryReachability.greedy_half_infinite_of_cofinalStripReturn
run_cmd Lean.logInfo "@@COMMAND 2078"
derive_weakening Erdos249257.SeamTwoSidedDyadicCellEscape.twoSided
run_cmd Lean.logInfo "@@COMMAND 2080"
derive_frontier Erdos249257.SeamTwoSidedDyadicCellEscape.twoSided
run_cmd Lean.logInfo "@@COMMAND 2082"
derive_weakening Erdos249257.SuffixCylinderTerminalOnlyBridge.exists_infinite_positive_support_half_of_cofinalCylinderStages
run_cmd Lean.logInfo "@@COMMAND 2084"
derive_weakening Erdos249257.exists_laterProtectedExactLocalMersenneRow
run_cmd Lean.logInfo "@@COMMAND 2086"
derive_weakening Erdos249257.halfGreedySkippedCriticalQuotientSupply_of_precriticalSuffix
run_cmd Lean.logInfo "@@COMMAND 2088"
derive_weakening Erdos249257.half_mem_mersenneAchievementSet_of_criticalQuotientSupply
run_cmd Lean.logInfo "@@COMMAND 2090"
derive_weakening Erdos249257.half_mem_mersenneAchievementSet_of_largestSkipLateStepSocket
run_cmd Lean.logInfo "@@COMMAND 2092"
derive_weakening Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerCardEscape
run_cmd Lean.logInfo "@@COMMAND 2094"
derive_frontier Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerCardEscape
run_cmd Lean.logInfo "@@COMMAND 2096"
derive_weakening Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerRowEscape
run_cmd Lean.logInfo "@@COMMAND 2098"
derive_frontier Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerRowEscape
run_cmd Lean.logInfo "@@COMMAND 2100"
derive_weakening Erdos249257.half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips
run_cmd Lean.logInfo "@@COMMAND 2102"
derive_weakening Erdos249257.half_mem_mersenneAchievementSet_of_secondChannelSeparation
run_cmd Lean.logInfo "@@COMMAND 2104"
derive_weakening Erdos249257.half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven
run_cmd Lean.logInfo "@@COMMAND 2106"
derive_weakening Erdos249257.half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative
run_cmd Lean.logInfo "@@COMMAND 2108"
derive_frontier Erdos249257.half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative
run_cmd Lean.logInfo "@@COMMAND 2110"
derive_weakening Erdos249257.half_mem_mersenneAchievementSet_of_skippedSeamEscape
run_cmd Lean.logInfo "@@COMMAND 2112"
derive_frontier Erdos249257.half_mem_mersenneAchievementSet_of_skippedSeamEscape
run_cmd Lean.logInfo "@@COMMAND 2114"
derive_weakening Erdos249257.half_mem_mersenneAchievementSet_of_skipped_dyadicCap
run_cmd Lean.logInfo "@@COMMAND 2116"
derive_weakening Erdos249257.half_mem_mersenneAchievementSet_of_skipped_twoChannelCap
run_cmd Lean.logInfo "@@COMMAND 2118"
derive_weakening Erdos249257.half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape
run_cmd Lean.logInfo "@@COMMAND 2120"
derive_frontier Erdos249257.half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape
run_cmd Lean.logInfo "@@COMMAND 2122"
derive_frontier Erdos249257.half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape at Erdos249257.SeamUpperResetDyadicBandEscape.remainder_ge_row
run_cmd Lean.logInfo "@@COMMAND 2124"
derive_frontier Erdos249257.half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape at Erdos249257.SeamUpperResetDyadicBandEscape.not_rowSmall_after_upperRightRun
run_cmd Lean.logInfo "@@COMMAND 2126"
derive_weakening Erdos249257.twentyOneFatalAlignedBranch_eventually_affine_supercapacity
run_cmd Lean.logInfo "@@COMMAND 2128"
derive_frontier Erdos249257.twentyOneFatalAlignedBranch_eventually_affine_supercapacity
run_cmd Lean.logInfo "@@COMMAND 2130"
derive_weakening Erdos249257.twentyOneFatalAlignedBranch_eventually_strict_supercapacity
run_cmd Lean.logInfo "@@COMMAND 2132"
derive_weakening ErdosProblems.Erdos257.PaperCompleteR21.half_mem_mersenneAchievementSet_of_resetSqrtEscape
run_cmd Lean.logInfo "@@COMMAND 2134"
derive_frontier ErdosProblems.Erdos257.PaperCompleteR21.half_mem_mersenneAchievementSet_of_resetSqrtEscape
run_cmd Lean.logInfo "@@COMMAND 2136"
derive_frontier ErdosProblems.Erdos257.PaperCompleteR21.half_mem_mersenneAchievementSet_of_resetSqrtEscape at ErdosProblems.Erdos257.PaperCompleteR21.SeamResetSqrtEscape.crossingBoundEscape
run_cmd Lean.logInfo "@@COMMAND 2138"
derive_weakening ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_escape_implies_full_shell_nonnegative
run_cmd Lean.logInfo "@@COMMAND 2140"
derive_weakening ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_escape_implies_half_membership
run_cmd Lean.logInfo "@@COMMAND 2142"
derive_frontier ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_escape_implies_half_membership
run_cmd Lean.logInfo "@@COMMAND 2144"
derive_weakening ErdosProblems.Erdos257.PaperCompleteR21.paper_terminal_strip_forces_half_membership
run_cmd Lean.logInfo "@@COMMAND 2146"
derive_weakening ErdosProblems.Erdos257.PaperCompleteR21.paper_theoremA_half_membership
run_cmd Lean.logInfo "@@COMMAND 2148"
derive_weakening ErdosProblems.Erdos257.PaperCompleteR21.paper_two_sided_dyadic_bound
run_cmd Lean.logInfo "@@COMMAND 2150"
derive_frontier ErdosProblems.Erdos257.PaperCompleteR21.paper_two_sided_dyadic_bound
run_cmd Lean.logInfo "@@COMMAND 2152"
derive_frontier ErdosProblems.Erdos257.PaperCompleteR21.paper_two_sided_dyadic_bound at Erdos249257.SeamTwoSidedDyadicCellEscape.step
run_cmd Lean.logInfo "@@COMMAND 2154"
derive_weakening Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound
run_cmd Lean.logInfo "@@COMMAND 2156"
derive_frontier Erdos249257.half_mem_mersenneAchievementSet_of_largestSkipLateStepSocket
run_cmd Lean.logInfo "@@COMMAND 2158"
derive_frontier Erdos249257.half_mem_mersenneAchievementSet_of_largestSkipLateStepSocket at Erdos249257.largestSkipLateAt_of_stepSocket
run_cmd Lean.logInfo "@@COMMAND 2160"
derive_frontier Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound using Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound
run_cmd Lean.logInfo "@@COMMAND 2162"
derive_conjuncts Erdos249257.HalfCarryReachability.greedy_half_infinite_of_cofinalStripReturn
run_cmd Lean.logInfo "@@COMMAND 2164"
derive_conjuncts Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound
run_cmd Lean.logInfo "@@COMMAND 2166"
derive_conjuncts Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound
run_cmd Lean.logInfo "@@COMMAND 2168"
derive_conjuncts Erdos249257.SuffixCylinderTerminalOnlyBridge.exists_infinite_positive_support_half_of_cofinalCylinderStages
run_cmd Lean.logInfo "@@COMMAND 2170"
derive_conjuncts Erdos249257.twentyOneFatalAlignedBranch_eventually_affine_supercapacity
run_cmd Lean.logInfo "@@COMMAND 2172"
derive_conjuncts ErdosProblems.Erdos257.PaperCompleteR21.paper_terminal_strip_forces_half_membership
run_cmd Lean.logInfo "@@COMMAND 2174"
derive_factor Erdos249257.AdelicHeightObstruction.linearDescender_eq_smul_eval
run_cmd Lean.logInfo "@@COMMAND 2176"
derive_factor Erdos249257.BooleanMobiusGreedyReduction.localMersenneHalfTarget_lower_word_eq_greedy_and_remainder_eq
run_cmd Lean.logInfo "@@COMMAND 2178"
derive_factor Erdos249257.BooleanMobiusGreedyReduction.remainder_lt_gap_iff_eq_integerGreedyBits
run_cmd Lean.logInfo "@@COMMAND 2180"
derive_factor Erdos249257.HalfCarryReachability.greedy_half_infinite_of_cofinalStripReturn
run_cmd Lean.logInfo "@@COMMAND 2182"
derive_factor Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound
run_cmd Lean.logInfo "@@COMMAND 2184"
derive_factor Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound
run_cmd Lean.logInfo "@@COMMAND 2186"
derive_factor Erdos249257.HalfCarryReachability.infinite_support_half_of_mobiusCenteredHalfCarry_sqrtBound
run_cmd Lean.logInfo "@@COMMAND 2188"
derive_factor Erdos249257.HalfTrappingReturnCarry.overlappingReverseCarryWords_carryDifference_eq_twoPow_mul_odd
run_cmd Lean.logInfo "@@COMMAND 2190"
derive_factor Erdos249257.HalfUpperResetCriticalBand.dyadicBandEscape_iff_exists_critical
run_cmd Lean.logInfo "@@COMMAND 2192"
derive_factor Erdos249257.HalfUpperResetCriticalBand.exists_criticalDyadicBandIndex
run_cmd Lean.logInfo "@@COMMAND 2194"
derive_factor Erdos249257.IsStraddlePrefix.half_step_forced
run_cmd Lean.logInfo "@@COMMAND 2196"
derive_factor Erdos249257.IsStraddlePrefix.half_strict
run_cmd Lean.logInfo "@@COMMAND 2198"
derive_factor Erdos249257.SuffixCylinderTerminalOnlyBridge.exists_infinite_positive_support_half_of_cofinalCylinderStages
run_cmd Lean.logInfo "@@COMMAND 2200"
derive_factor Erdos249257.balancedPulse_no_autonomous_decoder
run_cmd Lean.logInfo "@@COMMAND 2202"
derive_factor Erdos249257.divInt_mem_nextMersenneDyadicSliver_iff_excess
run_cmd Lean.logInfo "@@COMMAND 2204"
derive_factor Erdos249257.dyadicResidualInt_denominator_sandwich
run_cmd Lean.logInfo "@@COMMAND 2206"
derive_factor Erdos249257.dyadicResidual_denominator_sandwich
run_cmd Lean.logInfo "@@COMMAND 2208"
derive_factor Erdos249257.exists_boolean_word_of_lt_two_pow
run_cmd Lean.logInfo "@@COMMAND 2210"
derive_factor Erdos249257.exists_exactRowStrictUpperExtension_two_mul_sub_one_of_exact_below
run_cmd Lean.logInfo "@@COMMAND 2212"
derive_factor Erdos249257.exists_exactRowStrictUpperFill_of_skippedCoreSharpCapacity
run_cmd Lean.logInfo "@@COMMAND 2214"
derive_factor Erdos249257.exists_first_localMersenne_crossing
run_cmd Lean.logInfo "@@COMMAND 2216"
derive_factor Erdos249257.exists_laterProtectedExactLocalMersenneRow
run_cmd Lean.logInfo "@@COMMAND 2218"
derive_factor Erdos249257.exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction
run_cmd Lean.logInfo "@@COMMAND 2220"
derive_factor Erdos249257.greedy_survives_of_mem_mersenneAchievementSet
run_cmd Lean.logInfo "@@COMMAND 2222"
derive_factor Erdos249257.halfGreedy_skipped_endpoint_trichotomy
run_cmd Lean.logInfo "@@COMMAND 2224"
derive_factor Erdos249257.irrational_erdosSupportSeries_tail_of_irrational
run_cmd Lean.logInfo "@@COMMAND 2226"
derive_factor Erdos249257.irrational_or_bpow_mul_eq_intCast_intWeightedErdosSeries_periodic
run_cmd Lean.logInfo "@@COMMAND 2228"
derive_factor Erdos249257.isStraddlePrefix_step_trichotomy
run_cmd Lean.logInfo "@@COMMAND 2230"
derive_factor Erdos249257.not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit
run_cmd Lean.logInfo "@@COMMAND 2232"
derive_factor Erdos249257.shifted_state_unbounded_of_infinite_support
run_cmd Lean.logInfo "@@COMMAND 2234"
derive_factor Erdos249257.skipped_fullShell_neg_iff_alignment_and_seamRemainder_pos
run_cmd Lean.logInfo "@@COMMAND 2236"
derive_factor Erdos249257.twentyOneFatalAlignedBranch_eventually_affine_supercapacity
run_cmd Lean.logInfo "@@COMMAND 2238"
derive_factor Erdos249257.twentyOneFatalAlignedBranch_eventually_strict_supercapacity
run_cmd Lean.logInfo "@@COMMAND 2240"
derive_factor ErdosProblems.Erdos257.PaperCompleteR20.paper_general_repair_criteria
run_cmd Lean.logInfo "@@COMMAND 2242"
derive_factor ErdosProblems.Erdos257.PaperCompleteR20.paper_real_quotient_core
run_cmd Lean.logInfo "@@COMMAND 2244"
derive_factor ErdosProblems.Erdos257.PaperCompleteR20.paper_real_quotient_margins
run_cmd Lean.logInfo "@@COMMAND 2246"
derive_factor ErdosProblems.Erdos257.PaperCompleteR20.square_depth_witness
run_cmd Lean.logInfo "@@COMMAND 2248"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.iLeast_mem_Icc
run_cmd Lean.logInfo "@@COMMAND 2250"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.approx_orbit_induction
run_cmd Lean.logInfo "@@COMMAND 2252"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.arithmetic_logarithmic_counterexample
run_cmd Lean.logInfo "@@COMMAND 2254"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.certificate_of_existsFatalHalfGap
run_cmd Lean.logInfo "@@COMMAND 2256"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.exists_support_paperCoverCost_ge
run_cmd Lean.logInfo "@@COMMAND 2258"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.fatal_absorbing
run_cmd Lean.logInfo "@@COMMAND 2260"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.fatal_gap_endpoint_bounds
run_cmd Lean.logInfo "@@COMMAND 2262"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.fatal_gap_within_prefix_interval
run_cmd Lean.logInfo "@@COMMAND 2264"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.irrational_residueClass_positive_support
run_cmd Lean.logInfo "@@COMMAND 2266"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_capacity_band_exclusion
run_cmd Lean.logInfo "@@COMMAND 2268"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_centred_completion_of_fixed_precision
run_cmd Lean.logInfo "@@COMMAND 2270"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_channel_factor_gcd_eq_one
run_cmd Lean.logInfo "@@COMMAND 2272"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_compatible_finite_row_conditions
run_cmd Lean.logInfo "@@COMMAND 2274"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_consecutive_not_both_divisible
run_cmd Lean.logInfo "@@COMMAND 2276"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_crossing_support_is_greedy_prefix
run_cmd Lean.logInfo "@@COMMAND 2278"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_dyadic_band_index_unique
run_cmd Lean.logInfo "@@COMMAND 2280"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_dyadic_boundary_is_smallest
run_cmd Lean.logInfo "@@COMMAND 2282"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_dynamics
run_cmd Lean.logInfo "@@COMMAND 2284"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_endpoint_term_counts_divisors
run_cmd Lean.logInfo "@@COMMAND 2286"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_eventual_nonnegative_margin_equivalence
run_cmd Lean.logInfo "@@COMMAND 2288"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_mass_threshold
run_cmd Lean.logInfo "@@COMMAND 2290"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_double_or_recycle
run_cmd Lean.logInfo "@@COMMAND 2292"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_from_skipped_prefix
run_cmd Lean.logInfo "@@COMMAND 2294"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_final_middle_cell_at_least_neg_two
run_cmd Lean.logInfo "@@COMMAND 2296"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_forced_greedy_low_ranks
run_cmd Lean.logInfo "@@COMMAND 2298"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_forced_greedy_unique_support_and_criterion
run_cmd Lean.logInfo "@@COMMAND 2300"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_half_lcm_horizon
run_cmd Lean.logInfo "@@COMMAND 2302"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_mersenne_height
run_cmd Lean.logInfo "@@COMMAND 2304"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_next_floor_quotient_no_fixed_point
run_cmd Lean.logInfo "@@COMMAND 2306"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_no_ties
run_cmd Lean.logInfo "@@COMMAND 2308"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_one_orbit_stability
run_cmd Lean.logInfo "@@COMMAND 2310"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_perturbed_prefixChoice_maximal
run_cmd Lean.logInfo "@@COMMAND 2312"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_perturbed_two_stage_is_global_maximum
run_cmd Lean.logInfo "@@COMMAND 2314"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_pulse_family_finite_state_card
run_cmd Lean.logInfo "@@COMMAND 2316"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_pulse_family_no_autonomous_decoder
run_cmd Lean.logInfo "@@COMMAND 2318"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_relationInvariant_channels_rank_le_one
run_cmd Lean.logInfo "@@COMMAND 2320"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_rowLower_existsUnique
run_cmd Lean.logInfo "@@COMMAND 2322"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_rowUpper_existsUnique
run_cmd Lean.logInfo "@@COMMAND 2324"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_scalar_localization
run_cmd Lean.logInfo "@@COMMAND 2326"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_escape_forces_remainder_band
run_cmd Lean.logInfo "@@COMMAND 2328"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_shared_prefix_family_strip_witness_after_feedback_all_depths
run_cmd Lean.logInfo "@@COMMAND 2330"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_shared_prefix_family_strip_witness_after_feedback_of_all_depths
run_cmd Lean.logInfo "@@COMMAND 2332"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_skipped_core_recycling_witness_bounded
run_cmd Lean.logInfo "@@COMMAND 2334"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_square_depth_terminal_bound
run_cmd Lean.logInfo "@@COMMAND 2336"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_terminal_strip_forces_half_membership
run_cmd Lean.logInfo "@@COMMAND 2338"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_three_channel_margin_identity
run_cmd Lean.logInfo "@@COMMAND 2340"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_unconditional_bound_one_extra_bit
run_cmd Lean.logInfo "@@COMMAND 2342"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_upper_branch_needs_no_exceptional_cell
run_cmd Lean.logInfo "@@COMMAND 2344"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_witness_exclusion
run_cmd Lean.logInfo "@@COMMAND 2346"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.paper_zero_run_le_eps_logb
run_cmd Lean.logInfo "@@COMMAND 2348"
derive_factor ErdosProblems.Erdos257.PaperCompleteR21.weighted_denominator_budget
run_cmd Lean.logInfo "@@COMMAND 2350"
derive_factor ErdosProblems.Erdos257.PaperCompleteR8.weighted_displacement_cofinal_close_return
run_cmd Lean.logInfo "@@COMMAND 2352"
derive_factor ErdosProblems.Erdos257.finite_monotone_witness_rule_realised

-- The statement hash of every theorem this file added, so the frontier can check
-- that a published name still states what it stated.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, ci) in env.constants.map₂.toList do
    if let .thmInfo _ := ci then
      if let .str _ last := n then
        if last == "idle" || last == "factored" || last.startsWith "weakened_" || last.startsWith "frontier_"
            || last.startsWith "part_" || last.startsWith "use_" then
          let h := hash (toString (ErdosProblems.ArgumentGraph.normaliseBinders ci.type))
          out := out.push s!"DERIVED	{n}	{String.ofList (Nat.toDigits 16 h.toNat)}"
  IO.println ("
".intercalate (out.qsort (· < ·)).toList)

