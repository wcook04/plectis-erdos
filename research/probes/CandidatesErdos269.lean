import Lean
import ErdosProblems.Erdos269.PaperCompleteR21.TwoPrimeSums
import ErdosProblems.Erdos269.PaperR7BasicAssembly
import ErdosProblems.Erdos269.PaperR7WindowResults
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
* `derive_conjuncts T` adds, for each claim of `T`'s conclusion (a conjunct, or
  a direction of an equivalence) whose own proof leaves some hypotheses unused,
  `T.part_k`: that claim assuming only what its proof needs. A claim's proof is
  the projection of `T`'s proof onto it, reduced; it is the claim's own proof
  when the proof builds the claims separately.
* `derive_frontier T` follows those weakenings through the library. When a use
  site is `L a₁ … h … aₘ` for a theorem `L` whose proof uses that hypothesis only
  through consequences of its own, the site is replaced by `L.weakened_p` applied
  to proofs of those consequences, recursively. `T.frontier_i` states `T` with
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

register_option argumentGraph.strict : Bool := {
  defValue := false
  descr := "make a derive_* command that cannot add what it was asked for fail with an \
    error; by default it logs a warning"
}

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

/-- Add a theorem after a synchronous kernel check; the error text when the
kernel rejects it. -/
def addChecked (name : Name) (levelParams : List Name) (type value : Expr) (doc : String) :
    MetaM (Except String Unit) := do
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
  /-- Per consequence, one of its use sites as a closed function of the hypothesis. -/
  sites : Array Expr

/-- The weakening of binder `i`: one hypothesis per distinct use-site
proposition, placed where the binder was, each use site in the proof replaced by
the new hypothesis. -/
def weakenAt (info : ConstantInfo) (i : Nat) : MetaM (Option Weakening) := do
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
      return some { type, value, hypothesis := hType, consequences, sites }

/-- The number of binders of a theorem's statement, without unfolding. -/
def binderCount (info : ConstantInfo) : MetaM Nat :=
  forallTelescope info.type fun xs _ => return xs.size

/-- Weakenings added so far in this command, by theorem and binder. -/
abbrev DeriveM := StateRefT (Std.HashMap (Name × Nat) (Option (Name × Weakening))) MetaM

/-- The weakening of `name` at binder `i`, added to the environment as
`name.weakened_i` the first time it is needed. -/
def weakeningOf (name : Name) (i : Nat) : DeriveM (Option (Name × Weakening)) := do
  if let some r := (← get).get? (name, i) then return r
  let info ← getConstInfo name
  let mut r : Option (Name × Weakening) := none
  match ← weakenAt info i with
  | none => pure ()
  | some w =>
      let wName := name ++ Name.mkSimple s!"weakened_{i}"
      if (← getEnv).contains wName then
        r := some (wName, w)
      else
        let doc := s!"`{name}` with its hypothesis number {i} replaced by what its proof \
          uses of it. Derived by `derive_weakening` from the same proof."
        if (← addChecked wName info.levelParams w.type w.value doc) matches .ok () then
          r := some (wName, w)
  modify (·.insert (name, i) r)
  return r

/-! ## Frontiers -/

/-- How a frontier proves one consequence: assumed as it stands, or obtained from
`fn before … after` with each child consequence supplied recursively. -/
inductive Plan where
  | leaf (type : Expr)
  | step (fn : Expr) (before after : Array Expr) (children : Array Plan)
  deriving Inhabited

/-- The plan for a consequence `c` proved at `site` (a closed function of the
hypothesis). `stops` lists theorems whose use sites stay as they are. -/
def plan (stops : Array Name) : Nat → Expr → Expr → DeriveM Plan
  | 0, c, _ => return .leaf c
  | fuel + 1, c, site => do
    let .lam _ _ body _ := site | return .leaf c
    let .const n us := body.getAppFn | return .leaf c
    if stops.contains n then return .leaf c
    let args := body.getAppArgs
    let some p := args.findIdx? (fun a => a.consumeMData == .bvar 0) | return .leaf c
    for a in args, k in [0:args.size] do
      if k != p && a.hasLooseBVars then return .leaf c
    let some (wName, w) ← weakeningOf n p | return .leaf c
    let info ← getConstInfo n
    let inst (e : Expr) : Expr := e.instantiateLevelParams info.levelParams us
    let mut children : Array Plan := #[]
    for d in w.consequences, s in w.sites do
      children := children.push (← plan stops fuel (inst d) (inst s))
    return .step (mkConst wName us) (args.extract 0 p) (args.extract (p + 1) args.size) children

/-- The bound for walking a plan; `plan` builds plans at most `planFuel` deep. -/
def planFuel : Nat := 64

def Plan.leavesAux : Nat → Plan → Array Expr → Array Expr
  | _, .leaf t, acc => if acc.contains t then acc else acc.push t
  | 0, .step .., acc => acc
  | fuel + 1, .step _ _ _ cs, acc => cs.foldl (fun a c => Plan.leavesAux fuel c a) acc

/-- The distinct statements where a plan stops, added to `acc`. -/
def Plan.leaves (p : Plan) (acc : Array Expr) : Array Expr := Plan.leavesAux planFuel p acc

def Plan.buildAux : Nat → Array Expr → Array Expr → Plan → Expr
  | _, types, vars, .leaf t => vars[(types.findIdx? (· == t)).getD 0]!
  | 0, _, _, .step fn before after _ => mkAppN fn (before ++ after)
  | fuel + 1, types, vars, .step fn before after cs =>
      mkAppN fn (before ++ cs.map (Plan.buildAux fuel types vars ·) ++ after)

/-- The proof term a plan describes, with `vars[j]` for the leaf `types[j]`. A term
built past the bound is ill-typed, so the kernel rejects it. -/
def Plan.build (types vars : Array Expr) (p : Plan) : Expr := Plan.buildAux planFuel types vars p

def Plan.depthAux : Nat → Plan → Nat
  | _, .leaf _ => 0
  | 0, .step .. => 1
  | fuel + 1, .step _ _ _ cs => 1 + cs.foldl (fun m c => max m (Plan.depthAux fuel c)) 0

/-- How many weakenings deep the plan goes. -/
def Plan.depth (p : Plan) : Nat := Plan.depthAux planFuel p

/-- A proof of the closed proposition `t` by one of `suppliers`: the supplier
itself when its statement is `t`, or the supplier applied to arguments found by
unification when a prefix of its binders instantiates to `t` (instance
arguments synthesised). `none` when no supplier fits without leftover
metavariables. -/
def supplyLeaf (t : Expr) (suppliers : Array Name) : MetaM (Option Expr) := do
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
  for c in w.consequences, s in w.sites do
    plans := plans.push (← plan stops 24 c s)
  let leafTypes := plans.foldl (fun acc p => p.leaves acc) #[]
  let mut supplied : Array (Option Expr) := #[]
  for t in leafTypes do
    supplied := supplied.push (← if suppliers.isEmpty then pure none else supplyLeaf t suppliers)
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
  if (← getEnv).contains newName then return .ok newName
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

private def reportAdded (n : Name) : MetaM Unit := do
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
    let (added, _) ← (do
      let mut added : Array Name := #[]
      for i in [0:n] do
        match ← weakeningOf name i with
        | none => pure ()
        | some (wName, w) =>
          added := added.push wName
          -- `H → Cⱼ`, when `H` is closed.
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
      return added : DeriveM (Array Name)).run {}
    if added.isEmpty then
      reportFailure m!"derive_weakening {name}: no hypothesis is used only through consequences"
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

open ErdosProblems.ArgumentGraph
set_option maxHeartbeats 4000000
derive_conjuncts ErdosProblems.Erdos269.PaperCompleteR21.two_prime_sums_transcendental
derive_conjuncts ErdosProblems.Erdos269.PaperCompleteR21.two_prime_transcendence
