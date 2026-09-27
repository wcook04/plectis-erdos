import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Util.AtomM
import Erdos249257.FirstHarmonicPivot

-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0

/-!
# Abduction in an observable language

A residual clause `C` that a search could not supply is often a linear comparison between
quantities, some of which the corpus already controls: a lower bound on a cardinality, a
partition identity, a budget. Keeping `C` as the residual asks for more than the corpus needs;
leaving the demand itself is the degenerate answer. This module computes what `C` still needs
once the controlled quantities are eliminated.

Fix the facts `Γ` (linear comparisons in context), and split the atoms into *hidden* ones
(those some fact mentions, other than the parameters in scope) and *observable* ones (the
parameters, and the quantities no fact mentions). The weakest condition on the observables
that gives `C` under `Γ` is

  `R*(x) = ¬ ∃ y, Γ(x, y) ∧ ¬ C(x, y)`,

since any sufficient condition excludes every counterexample. Over an ordered field the
counterexample region is a polyhedron and Fourier–Motzkin elimination of the hidden atoms
computes its projection exactly; `R*` is the negation of that projection, a disjunction of
linear comparisons in the observables. The kernel then checks `Γ → R* → C` by `linarith`, so
sufficiency is proved; weakestness holds relative to the linear facts used and is computed,
not proved. Over `ℕ` and `ℤ` the rational projection still gives a sufficient condition.

The tactic `abduce` replaces a comparison goal by `R*` (closing it when `R*` is `True`) and
logs `R*`; `abduce [o₁, …]` fixes the observable atoms; `abduce using f₁, …` restricts the
facts to the given terms. `abduceClause` is the same operation for a search.
-/

set_option autoImplicit false

open Lean Meta Elab Term Mathlib.Tactic

namespace ErdosProblems.ArgumentGraph.Abduce

/-! ## Linear rows over ℚ -/

inductive Rel where
  | eq | le | lt
  deriving BEq, Inhabited, Repr

def Rel.join : Rel → Rel → Rel
  | .lt, _ => .lt
  | _, .lt => .lt
  | .le, _ => .le
  | _, .le => .le
  | .eq, .eq => .eq

/-- `∑ i, c[i] * x i + k  rel  0`, with `c` dense over the atoms. -/
structure Row where
  c : Array ℚ
  k : ℚ
  rel : Rel
  deriving BEq, Inhabited, Repr

def Row.coeff (r : Row) (i : Nat) : ℚ := r.c.getD i 0

def Row.scale (q : ℚ) (r : Row) : Row := { r with c := r.c.map (q * ·), k := q * r.k }

def Row.add (r s : Row) : Row :=
  let n := max r.c.size s.c.size
  { c := (Array.range n).map fun i => r.coeff i + s.coeff i, k := r.k + s.k,
    rel := r.rel.join s.rel }

def Row.isConstant (r : Row) : Bool := r.c.all (· == 0)

/-- For a row with no atom: `some true` when it holds, `some false` when it fails. -/
def Row.constantTruth (r : Row) : Option Bool :=
  if !r.isConstant then none
  else match r.rel with
    | .eq => some (r.k == 0)
    | .le => some (r.k ≤ 0)
    | .lt => some (r.k < 0)

/-- Scale a row so that its first nonzero coefficient has absolute value one. -/
def Row.normalize (r : Row) : Row :=
  match r.c.find? (· != 0) with
  | some a => r.scale (1 / |a|)
  | none => r

/-- Drop rows that hold identically and duplicates; `none` when some row fails identically. -/
def tidy (rows : Array Row) : Option (Array Row) := Id.run do
  let mut out : Array Row := #[]
  for r in rows do
    match r.constantTruth with
    | some true => continue
    | some false => return none
    | none =>
      let r := r.normalize
      unless out.contains r do out := out.push r
  return some out

/-- One Fourier–Motzkin step: eliminate atom `v` (by an equality when one has it). -/
def eliminate (v : Nat) (rows : Array Row) : Array Row := Id.run do
  let pivot? := rows.findIdx? fun r => r.rel == .eq && r.coeff v != 0
  match pivot? with
  | some p =>
    let e := rows[p]!
    let c := e.coeff v
    let mut out := #[]
    for i in [0:rows.size] do
      if i == p then continue
      let r := rows[i]!
      let d := r.coeff v
      out := out.push (if d == 0 then r else r.add (e.scale (-d / c)))
    return out
  | none =>
    let pos := rows.filter (·.coeff v > 0)
    let neg := rows.filter (·.coeff v < 0)
    let mut out := rows.filter (·.coeff v == 0)
    for p in pos do
      for n in neg do
        out := out.push ((p.scale (-(n.coeff v))).add (n.scale (p.coeff v)))
    return out

/-- Eliminate the atoms `hidden`, cheapest first. `some (some rows)` is the projection,
`some none` means the rows are inconsistent, and `none` means the elimination passed `maxRows`
rows and gave up. -/
def project (hidden : Array Nat) (rows : Array Row) (maxRows : Nat := 4000) :
    Option (Option (Array Row)) := Id.run do
  let some rows0 := tidy rows | return some none
  let mut rows := rows0
  let mut todo := hidden
  for _ in [0:hidden.size] do
    if todo.isEmpty then break
    -- the atom whose elimination creates the fewest rows
    let mut best := todo[0]!
    let mut bestCost := rows.size * rows.size + 1
    for v in todo do
      let hasEq := rows.any fun r => r.rel == .eq && r.coeff v != 0
      let cost := if hasEq then 0 else
        (rows.filter (·.coeff v > 0)).size * (rows.filter (·.coeff v < 0)).size
      if cost < bestCost then
        best := v
        bestCost := cost
    todo := todo.filter (· != best)
    let next := eliminate best rows
    if next.size > maxRows then return none
    let some t := tidy next | return some none
    rows := t
  return some (some rows)

/-- Rows implied by the others are dropped (checked by eliminating every atom). -/
def pruneRedundant (rows : Array Row) : Array Row := Id.run do
  let mut keep := rows
  let mut i := 0
  for _ in [0:rows.size] do
    if i ≥ keep.size then break
    let r := keep[i]!
    let others := (keep.toList.eraseIdx i).toArray
    -- `r` is redundant when `others ∧ ¬r` is inconsistent
    let negR : Array Row := match r.rel with
      | .le => #[{ r.scale (-1) with rel := .lt }]
      | .lt => #[{ r.scale (-1) with rel := .le }]
      | .eq => #[]
    if negR.isEmpty then
      i := i + 1
      continue
    let n := (others.foldl (fun m s => max m s.c.size) r.c.size)
    match project ((Array.range n)) (others ++ negR) with
    | some none => keep := others
    | _ => i := i + 1
  return keep

/-- Whether the rows `fs` imply the row `r` (checked by eliminating every atom). -/
def impliedBy (fs : Array Row) (r : Row) : Bool :=
  let negR : Array Row := match r.rel with
    | .le => #[{ r.scale (-1) with rel := .lt }]
    | .lt => #[{ r.scale (-1) with rel := .le }]
    | .eq => #[]
  if negR.isEmpty then false
  else
    let n := fs.foldl (fun m s => max m s.c.size) r.c.size
    match project (Array.range n) (fs ++ negR) with
    | some none => true
    | _ => false

/-! ## Reading linear forms off expressions -/

/-- A rational numeral: literals, casts of literals, and `+ - * /` of numerals. -/
def numeral? : Nat → Expr → MetaM (Option ℚ)
  | 0, _ => return none
  | fuel + 1, e => do
    let e ← instantiateMVars e
    if let .lit (.natVal v) := e then return some v
    match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_, n, _]) =>
        match n with
        | .lit (.natVal v) => return some v
        | _ => return none
    | (``Nat.cast, #[_, _, a]) => numeral? fuel a
    | (``NatCast.natCast, #[_, _, a]) => numeral? fuel a
    | (``Int.cast, #[_, _, a]) => numeral? fuel a
    | (``IntCast.intCast, #[_, _, a]) => numeral? fuel a
    | (``OfScientific.ofScientific, #[_, _, m, b, x]) =>
        match m, b, x with
        | .lit (.natVal m), .const ``Bool.true _, .lit (.natVal x) => return some ((m : ℚ) / 10 ^ x)
        | .lit (.natVal m), .const ``Bool.false _, .lit (.natVal x) => return some ((m : ℚ) * 10 ^ x)
        | _, _, _ => return none
    | (``Neg.neg, #[_, _, a]) => return (← numeral? fuel a).map (- ·)
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) => do
        let some x ← numeral? fuel a | return none
        let some y ← numeral? fuel b | return none
        return some (x + y)
    | (``HSub.hSub, #[_, _, _, _, a, b]) => do
        let some x ← numeral? fuel a | return none
        let some y ← numeral? fuel b | return none
        return some (x - y)
    | (``HMul.hMul, #[_, _, _, _, a, b]) => do
        let some x ← numeral? fuel a | return none
        let some y ← numeral? fuel b | return none
        return some (x * y)
    | (``HDiv.hDiv, #[_, _, _, _, a, b]) => do
        let some x ← numeral? fuel a | return none
        let some y ← numeral? fuel b | return none
        if y == 0 then return none
        return some (x / y)
    | _ => return none

/-- A sparse linear form: coefficients by atom index, and a constant. -/
structure Lin where
  terms : List (Nat × ℚ) := []
  k : ℚ := 0
  deriving Inhabited

def Lin.scale (q : ℚ) (l : Lin) : Lin := { terms := l.terms.map fun (i, a) => (i, q * a), k := q * l.k }

def Lin.add (l m : Lin) : Lin := Id.run do
  let mut t := l.terms
  for (i, a) in m.terms do
    if t.any (·.1 == i) then t := t.map fun (j, b) => if j == i then (j, b + a) else (j, b)
    else t := t ++ [(i, a)]
  return { terms := t, k := l.k + m.k }

/-- The linear form of `e`; subterms that are not sums, differences, negations, or products and
quotients by numerals are atoms. Truncated subtraction (`natSub`, over `ℕ`) and integer
division (`integral`, over `ℕ` and `ℤ`) are atoms. -/
def linForm (natSub integral : Bool) : Nat → Expr → AtomM Lin
  | 0, e => do return { terms := [((← AtomM.addAtom e).1, 1)] }
  | fuel + 1, e => do
    let e ← instantiateMVars e
    if let some q ← numeral? 64 e then return { k := q }
    let atom : AtomM Lin := do return { terms := [((← AtomM.addAtom e).1, 1)] }
    match e.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
        return (← linForm natSub integral fuel a).add (← linForm natSub integral fuel b)
    | (``HSub.hSub, #[_, _, _, _, a, b]) =>
        if natSub then atom
        else return (← linForm natSub integral fuel a).add
          ((← linForm natSub integral fuel b).scale (-1))
    | (``Neg.neg, #[_, _, a]) => return (← linForm natSub integral fuel a).scale (-1)
    | (``HMul.hMul, #[_, _, _, _, a, b]) =>
        if let some q ← numeral? 64 a then return (← linForm natSub integral fuel b).scale q
        if let some q ← numeral? 64 b then return (← linForm natSub integral fuel a).scale q
        atom
    | (``HDiv.hDiv, #[_, _, _, _, a, b]) =>
        if integral then atom
        else if let some q ← numeral? 64 b then
          if q == 0 then atom else return (← linForm natSub integral fuel a).scale (1 / q)
        else atom
    | _ => atom

/-- `lhs rel rhs` read off a comparison proposition (through `≥`, `>` and `¬`), with its
carrier type. -/
def comparison? (P : Expr) : MetaM (Option (Expr × Expr × Expr × Rel)) := do
  let P ← instantiateMVars P
  match P.getAppFnArgs with
  | (``LE.le, #[α, _, a, b]) => return some (α, a, b, .le)
  | (``LT.lt, #[α, _, a, b]) => return some (α, a, b, .lt)
  | (``GE.ge, #[α, _, a, b]) => return some (α, b, a, .le)
  | (``GT.gt, #[α, _, a, b]) => return some (α, b, a, .lt)
  | (``Eq, #[α, a, b]) =>
      if (← isProp α) || α.isSort then return none else return some (α, a, b, .eq)
  | (``Not, #[Q]) =>
      match Q.getAppFnArgs with
      | (``LE.le, #[α, _, a, b]) => return some (α, b, a, .lt)
      | (``LT.lt, #[α, _, a, b]) => return some (α, b, a, .le)
      | (``GE.ge, #[α, _, a, b]) => return some (α, a, b, .lt)
      | (``GT.gt, #[α, _, a, b]) => return some (α, a, b, .le)
      | _ => return none
  | _ => return none

/-- `(is ℕ, is ℕ or ℤ)`. -/
def carrierKind (α : Expr) : MetaM (Bool × Bool) := do
  let α ← whnfR α
  return (α.isConstOf ``Nat, α.isConstOf ``Nat || α.isConstOf ``Int)

/-- A parameter: a local variable, or a cast of one. -/
def isParameter (e : Expr) : Bool :=
  e.isFVar ||
    match e.getAppFnArgs with
    | (``Nat.cast, #[_, _, a]) => a.isFVar
    | (``NatCast.natCast, #[_, _, a]) => a.isFVar
    | (``Int.cast, #[_, _, a]) => a.isFVar
    | (``IntCast.intCast, #[_, _, a]) => a.isFVar
    | _ => false

def isNatCast (e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``Nat.cast, #[_, _, a]) => some a
  | (``NatCast.natCast, #[_, _, a]) => some a
  | _ => none

/-! ## Building the residual -/

def numeralExpr (α : Expr) (q : ℚ) : MetaM Expr := do
  let natE (n : Nat) : MetaM Expr := mkNumeral α n
  let absq := |q|
  let body ←
    if absq.den == 1 then natE absq.num.natAbs
    else mkAppM ``HDiv.hDiv #[← natE absq.num.natAbs, ← natE absq.den]
  if q < 0 then mkAppM ``Neg.neg #[body] else return body

/-- `∑ q_i * x_i + k` over `α` with positive terms added and negative ones subtracted;
`none` for the empty sum with zero constant. -/
def sumExpr (α : Expr) (atoms : Array Expr) (coeffs : List (Nat × ℚ)) (k : ℚ) :
    MetaM Expr := do
  let term (i : Nat) (q : ℚ) : MetaM Expr := do
    let x := atoms[i]!
    if q == 1 then return x else mkAppM ``HMul.hMul #[← numeralExpr α q, x]
  let mut acc : Option Expr := none
  for (i, q) in coeffs do
    if q == 0 then continue
    match acc with
    | none => acc := some (← term i q)
    | some s =>
      if q > 0 then acc := some (← mkAppM ``HAdd.hAdd #[s, ← term i q])
      else acc := some (← mkAppM ``HSub.hSub #[s, ← term i (-q)])
  match acc with
  | none => numeralExpr α k
  | some s =>
    if k == 0 then return s
    else if k > 0 then mkAppM ``HAdd.hAdd #[s, ← numeralExpr α k]
    else mkAppM ``HSub.hSub #[s, ← numeralExpr α (-k)]

/-- The negation of the projected row `r` (`∑ c x + k rel 0`), solved for a pivot atom when
the carrier is a field: `x_e ≤ …`, `… < x_e` and so on. Over `ℕ`-like carriers the
coefficients are cleared of denominators and each side keeps nonnegative coefficients. -/
def negatedRow (α : Expr) (integral : Bool) (atoms : Array Expr) (pivotOk : Expr → Bool)
    (r : Row) : MetaM Expr := do
  -- ¬(s ≤ 0) is 0 < s; ¬(s < 0) is 0 ≤ s; ¬(s = 0) is s ≠ 0
  let nonzero := (List.range r.c.size).filterMap fun i =>
    let q := r.coeff i
    if q == 0 then none else some (i, q)
  if integral || r.rel == .eq then
    let den := nonzero.foldl (fun d (_, q) => Nat.lcm d q.den) r.k.den
    let s := r.scale den
    let pos := nonzero.filterMap fun (i, _) => if s.coeff i > 0 then some (i, s.coeff i) else none
    let neg := nonzero.filterMap fun (i, _) => if s.coeff i < 0 then some (i, -(s.coeff i)) else none
    -- `∑ pos + k (rel') ∑ neg` with the constant on the side where it is nonnegative
    let (kl, kr) := if s.k ≥ 0 then (s.k, (0 : ℚ)) else ((0 : ℚ), -s.k)
    let lhs ← sumExpr α atoms pos kl
    let rhs ← sumExpr α atoms neg kr
    match r.rel with
    | .le => mkAppM ``LT.lt #[rhs, lhs]
    | .lt => mkAppM ``LE.le #[rhs, lhs]
    | .eq => mkAppM ``Ne #[lhs, rhs]
  else
    let pivot := (nonzero.find? fun (i, _) => pivotOk atoms[i]!).orElse fun _ => nonzero.head?
    match pivot with
    | none =>
      -- a constant row cannot reach here after `tidy`
      mkAppM ``LE.le #[← numeralExpr α 0, ← numeralExpr α r.k]
    | some (e, ce) =>
      let rest := nonzero.filter (·.1 != e)
      -- ce * x_e + rest + k, divided by |ce|
      let other := rest.map fun (i, q) => (i, -q / ce)
      let otherK := -r.k / ce
      let xe := atoms[e]!
      let bound ← sumExpr α atoms other otherK
      -- 0 < s  (rel le)  or  0 ≤ s  (rel lt):  with ce > 0 this is  bound < x_e  /  bound ≤ x_e
      match r.rel, decide (ce > 0) with
      | .le, true => mkAppM ``LT.lt #[bound, xe]
      | .le, false => mkAppM ``LT.lt #[xe, bound]
      | _, true => mkAppM ``LE.le #[bound, xe]
      | _, false => mkAppM ``LE.le #[xe, bound]

def disj : List Expr → Expr
  | [] => mkConst ``False
  | [a] => a
  | a :: rest => mkApp2 (mkConst ``Or) a (disj rest)

/-! ## Tactics under a budget -/

def budgetedTerm {α : Type} (heartbeats : Nat) (x : TermElabM α) : TermElabM (Option α) := do
  withCurrHeartbeats <|
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := heartbeats * 1000 }) do
      tryCatchRuntimeEx (do return some (← x)) fun _ => return none

/-- A proof of `goalType` by the tactic `tac` (no metavariables allowed in the goal). -/
def runTac (goalType : Expr) (tac : String) (heartbeats : Nat := 20000) : TermElabM (Option Expr) := do
  if goalType.hasMVar then return none
  let env ← getEnv
  let .ok stx := Parser.runParserCategory env `tactic tac | return none
  let msgs := (← getThe Core.State).messages
  let s ← Term.saveState
  let r ← budgetedTerm heartbeats <| Term.withoutErrToSorry do
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

/-! ## The operation -/

structure Abduced where
  /-- the condition left (`True` when the facts give the clause) -/
  residual : Expr
  /-- a proof of `residual → clause` -/
  proof : Expr
  hidden : Array Expr
  observed : Array Expr
  /-- the facts that entered the elimination (their types) -/
  facts : Array Expr

/-- The weakest condition on the observable atoms that gives `goal` under the linear facts
among `facts` (proofs), with a kernel-checked proof. `observable` fixes the observable atoms;
by default they are the parameters and the atoms no fact mentions. `none` when `goal` is not a
linear comparison, when every observable condition fails (the facts leave nothing sufficient
in this language), or when the check fails. -/
def abduceClause (goal : Expr) (facts : Array Expr) (observable : Option (Array Expr) := none) :
    TermElabM (Option Abduced) := do
  let some (α, gl, gr, grel) ← comparison? goal | return none
  let (natSub, integral) ← carrierKind α
  -- facts over the same carrier
  let mut used : Array (Expr × Expr × Expr × Rel) := #[]
  for f in facts do
    let fT ← instantiateMVars (← inferType f)
    let some (β, a, b, rel) ← comparison? fT | continue
    unless ← isDefEq α β do continue
    used := used.push (f, a, b, rel)
  let parsed ← AtomM.run .reducible do
    let g := (← linForm natSub integral 256 gl).add ((← linForm natSub integral 256 gr).scale (-1))
    let mut rows : Array Lin := #[]
    for (_, a, b, _) in used do
      rows := rows.push ((← linForm natSub integral 256 a).add
        ((← linForm natSub integral 256 b).scale (-1)))
    return (g, rows, (← get).atoms)
  let (g, factLins, atoms0) := parsed
  -- nonnegativity of cast atoms (and of every atom over `ℕ`), proved by `positivity`
  let atoms := atoms0
  let mut extra : Array (Expr × Lin) := #[]
  for i in [0:atoms.size] do
    if natSub || (isNatCast atoms[i]!).isSome then
      let t ← mkAppM ``LE.le #[← numeralExpr α 0, atoms[i]!]
      if let some p ← runTac t "positivity" then
        extra := extra.push (p, { terms := [(i, -1)] })
  let dense (l : Lin) (rel : Rel) : Row :=
    { c := (Array.range atoms.size).map fun i =>
        (l.terms.filter (·.1 == i)).foldl (fun s (_, q) => s + q) 0,
      k := l.k, rel }
  -- the counterexample: the facts and the negated clause
  let negGoal : Array Row := match grel with
    | .le => #[dense (g.scale (-1)) .lt]
    | .lt => #[dense (g.scale (-1)) .le]
    | .eq => #[]
  if negGoal.isEmpty then return none
  let mut rows := negGoal
  for i in [0:used.size] do
    rows := rows.push (dense factLins[i]! used[i]!.2.2.2)
  for (_, l) in extra do
    rows := rows.push (dense l .le)
  -- hidden atoms
  let mentioned : Array Nat := Id.run do
    let mut m := #[]
    for l in factLins do
      for (i, q) in l.terms do
        if q != 0 && !m.contains i then m := m.push i
    return m
  let mut hidden : Array Nat := #[]
  match observable with
  | some obs =>
    for i in [0:atoms.size] do
      let mut isObs := false
      for o in obs do
        if ← withReducible (isDefEq o atoms[i]!) then isObs := true
      unless isObs do hidden := hidden.push i
  | none =>
    for i in mentioned do
      unless isParameter atoms[i]! do hidden := hidden.push i
  let obsAtoms := (Array.range atoms.size).filter (!hidden.contains ·) |>.map (atoms[·]!)
  let hiddenAtoms := hidden.map (atoms[·]!)
  let some projected := project hidden rows | return none
  -- the facts alone, projected: a counterexample row they imply adds an always-false disjunct
  let factProj := project hidden (rows.extract negGoal.size rows.size)
  let kept : Option (Array Row) := projected.map fun ps =>
    (pruneRedundant ps).filter fun r =>
      match factProj with
      | some (some fs) => !impliedBy fs r
      | some none => false
      | none => true
  let residual ← match kept with
    | none => pure (mkConst ``True)
    | some ps =>
      if ps.isEmpty then return none
      let pivotOk (e : Expr) : Bool := !isParameter e
      let negs ← ps.toList.mapM (negatedRow α integral atoms pivotOk)
      pure (disj negs)
  -- the kernel check: facts → residual → goal
  let factProofs := used.map (·.1) ++ extra.map (·.1)
  let factTypes ← factProofs.mapM fun p => do instantiateMVars (← inferType p)
  let decls := (Array.range factTypes.size).map fun i => (Name.mkSimple s!"hf{i}", factTypes[i]!)
  let stmt ← withLocalDeclsDND decls fun hs => do
    mkForallFVars hs (← mkArrow residual goal)
  let nDisj := match kept with
    | none => 1
    | some ps => ps.size
  let rcasesPat := String.intercalate " | " (List.replicate nDisj "hR")
  let tacs :=
    if nDisj ≤ 1 then ["intros; linarith", "intros; omega"]
    else [s!"intros; rename_i hR; rcases hR with {rcasesPat} <;> linarith",
          s!"intros; rename_i hR; rcases hR with {rcasesPat} <;> omega"]
  let mut pf? : Option Expr := none
  for t in tacs do
    if pf?.isNone then
      pf? ← runTac stmt t
  let some pf := pf? | return none
  return some { residual, proof := mkAppN pf factProofs, hidden := hiddenAtoms,
                observed := obsAtoms, facts := factTypes }

end ErdosProblems.ArgumentGraph.Abduce

/-! ## The tactic -/

namespace ErdosProblems.ArgumentGraph.Abduce

open Lean Meta Elab Tactic

/- `abduce` is the only new word; `[`, `]`, `,` and `using` are already tokens. -/
syntax (name := abduceTac) "abduce" ("[" term,* "]")? (" using " term,+)? : tactic

/-- `abduce` replaces a linear comparison goal by the weakest condition on the observable
atoms that gives it under the linear hypotheses in context, and logs that condition; it closes
the goal when the hypotheses already give it. `abduce [o₁, …]` fixes the observable atoms;
`abduce using f₁, …` uses only the given facts. -/
@[tactic abduceTac] def evalAbduce : Tactic := fun stx => withMainContext do
  let goal ← getMainGoal
  let C ← instantiateMVars (← goal.getType)
  let obs? ← if stx[1].isNone then pure none
    else some <$> (stx[1][1].getSepArgs.mapM fun t => elabTerm t none)
  let facts ← if stx[2].isNone then do
      let mut fs : Array Expr := #[]
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        if ← isProp d.type then fs := fs.push d.toExpr
      pure fs
    else stx[2][1].getSepArgs.mapM fun t => elabTerm t none
  let some r ← abduceClause C facts obs?
    | throwError "abduce: no condition on the observable atoms gives the goal under these facts"
  if r.residual.isConstOf ``True then
    logInfo m!"abduce: the facts give the goal"
    goal.assign (mkApp r.proof (mkConst ``True.intro))
    replaceMainGoal []
  else
    logInfo m!"abduce: {r.residual}\n  eliminated {r.hidden.toList}\n  kept {r.observed.toList}"
    let newGoal ← mkFreshExprSyntheticOpaqueMVar r.residual
    goal.assign (mkApp r.proof newGoal)
    replaceMainGoal [newGoal.mvarId!]

end ErdosProblems.ArgumentGraph.Abduce

/-! ## Calibration and corpus checks for `abduce` -/

section AbduceTests

open ErdosProblems.ArgumentGraph.Abduce

/-- The subset calibration with the scale normalised to one: shares `m`, `b`, `u` of good,
bad and non-supplier bases, `g` the good-base cosine sum, `γ` its bound. Only `γ` is
observable; the search is given no threshold. -/
theorem abduce_subset_calibration (m b u g γ : ℝ) (hp : m + b + u = 1) (hb0 : 0 ≤ b)
    (hb : b < 1 / 100) (hu0 : 0 ≤ u) (hu : u < 8 / 25) (hg1 : -m ≤ g) (hg2 : g ≤ m)
    (hγ : g ≤ γ) (hgap : γ ≤ 603 / 1000) : g ≤ 9 / 10 * m := by
  abduce [γ] using hp, hb0, hb, hu0, hu, hg1, hg2, hγ
  guard_target = γ ≤ 603 / 1000
  exact hgap

/-- The whole-block alternative pays for the complement. -/
theorem abduce_whole_block_calibration (t g b u γ : ℝ) (ht : t ≤ g + b + u) (hb0 : 0 ≤ b)
    (hb : b < 1 / 100) (hu0 : 0 ≤ u) (hu : u < 8 / 25) (hγ : g ≤ γ) (hgap : γ ≤ 57 / 100) :
    t ≤ 9 / 10 := by
  abduce [γ] using ht, hb0, hb, hu0, hu, hγ
  guard_target = γ ≤ 57 / 100
  exact hgap

open Erdos249257.TotientTailPeriodKiller in
/-- The #249 subset-barrier clause on the pivot-good bases, with the corpus's count as the only
fact: the cardinality is eliminated and the bound on the cosine sum in terms of `X` is left.
No observable is named; the default language keeps the parameters and the unconstrained sum. -/
theorem abduce_goodBase_clause (h X L : ℕ)
    (hcard : (67 / 100 : ℝ) * X < ((pivotGoodBases X L 26 (1 / 1000 : ℝ)).card : ℝ))
    (hgap : ∑ N ∈ pivotGoodBases X L 26 (1 / 1000 : ℝ), windowFirstCos h N L ≤
      603 / 1000 * (X : ℝ)) :
    ∑ N ∈ pivotGoodBases X L 26 (1 / 1000 : ℝ), windowFirstCos h N L ≤
      9 / 10 * ((pivotGoodBases X L 26 (1 / 1000 : ℝ)).card : ℝ) := by
  abduce using hcard
  guard_target = ∑ N ∈ pivotGoodBases X L 26 (1 / 1000 : ℝ), windowFirstCos h N L ≤
      603 / 1000 * (X : ℝ)
  exact hgap

/-- Over `ℕ` the rational projection still gives a sufficient condition. -/
theorem abduce_nat_example (n q : ℕ) (hq : 2 * n ≤ q) (hn : 2 ≤ n) : n + 1 < q := by
  abduce [n] using hq
  guard_target = 1 < n
  omega

/-- An equality eliminates an atom; here the facts give the goal outright. -/
theorem abduce_closes (a b c : ℝ) (h1 : a = b + c) (h2 : b ≤ 5) : a ≤ c + 7 := by
  abduce [c]

end AbduceTests

#print axioms abduce_subset_calibration
#print axioms abduce_goodBase_clause
#print axioms abduce_nat_example
#print axioms abduce_closes
