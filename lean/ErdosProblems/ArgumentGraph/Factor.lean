-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import ErdosProblems.ArgumentGraph.Derive

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

/-- The docstring of a factored theorem: where each moved hypothesis went, claims
numbered from 1 in the order the conclusion states them. -/
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
      -- a compiled `match` is an elimination by its definition
      if let some u ← unfoldDefinition? e (ignoreTransparency := true) then
        return ← normAux fuel mv u.headBeta
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
        modify fun s => { s with added := s.added.push newName,
                              placements := s.placements ++ placed.map fun (h, w) => (newName, h, w) }
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
