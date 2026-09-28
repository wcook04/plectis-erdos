import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Util.AtomM
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.Interval.Finset.Defs
import ErdosProblems.ArgumentGraph.Residualise
import Erdos249257
import ErdosProblems

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
        else do
          let la ← linForm natSub integral fuel a
          let lb ← linForm natSub integral fuel b
          return la.add (lb.scale (-1))
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
  | [] => Lean.mkConst ``False
  | [a] => a
  | a :: rest => mkApp2 (Lean.mkConst ``Or) a (disj rest)

/-! ## Tactics under a budget -/

def withHeartbeatBudget {α : Type} (heartbeats : Nat) (x : TermElabM α) : TermElabM (Option α) := do
  withCurrHeartbeats <|
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := heartbeats * 1000 }) do
      tryCatchRuntimeEx (do return some (← x)) fun _ => return none

/-- A proof of `goalType` by the tactic `tac` (no metavariables allowed in the goal). -/
def proveByTactic (goalType : Expr) (tac : String) (heartbeats : Nat := 20000) : TermElabM (Option Expr) := do
  if goalType.hasMVar then return none
  let env ← getEnv
  let .ok stx := Parser.runParserCategory env `tactic tac | return none
  let msgs := (← getThe Core.State).messages
  let s ← Term.saveState
  let r ← withHeartbeatBudget heartbeats <| Term.withoutErrToSorry do
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
by default they are the parameters and the atoms no fact mentions, together with the atoms of
`forcedObservable`, which stay observable even when a fact mentions them. `none` when `goal` is
not a linear comparison, when every observable condition fails (the facts leave nothing
sufficient in this language), or when the check fails. -/
def abduceClause (goal : Expr) (facts : Array Expr) (observable : Option (Array Expr) := none)
    (extraHidden : Array Expr := #[]) (forcedObservable : Array Expr := #[]) :
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
      if let some p ← proveByTactic t "positivity" then
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
      if isParameter atoms[i]! then continue
      let mut forced := false
      for o in forcedObservable do
        if ← withReducible (isDefEq o atoms[i]!) then forced := true
      unless forced do hidden := hidden.push i
    -- variables bound inside the clause being restated are eliminated as well
    for i in [0:atoms.size] do
      if hidden.contains i then continue
      let a := atoms[i]!
      let base := match isNatCast a with | some x => x | none => a
      if extraHidden.any (· == base) then hidden := hidden.push i
  let obsAtoms := (Array.range atoms.size).filter (!hidden.contains ·) |>.map (atoms[·]!)
  let hiddenAtoms := hidden.map (atoms[·]!)
  -- an empty counterexample region shows only once every atom is eliminated
  let emptyRegion := match project (Array.range atoms.size) rows with
    | some none => true
    | _ => false
  let some projected := (if emptyRegion then some none else project hidden rows) | return none
  -- the facts alone, projected: a counterexample row they imply adds an always-false disjunct
  let factProj := project hidden (rows.extract negGoal.size rows.size)
  let kept : Option (Array Row) := projected.map fun ps =>
    (pruneRedundant ps).filter fun r =>
      match factProj with
      | some (some fs) => !impliedBy fs r
      | some none => false
      | none => true
  let residual ← match kept with
    | none => pure (Lean.mkConst ``True)
    | some ps =>
      if ps.isEmpty then return none
      let pivotOk (e : Expr) : Bool := !isParameter e
      let negs ← ps.toList.mapM fun r => negatedRow α integral atoms pivotOk r
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
  -- one tactic each (a bare `a; b` does not parse in the tactic category)
  let tacs :=
    if nDisj ≤ 1 then ["(intros; linarith)", "(intros; omega)"]
    else [s!"(intros; rename_i hR; rcases hR with {rcasesPat} <;> linarith)",
          s!"(intros; rename_i hR; rcases hR with {rcasesPat} <;> omega)"]
  let mut pf? : Option Expr := none
  for t in tacs do
    if pf?.isNone then
      pf? ← proveByTactic stmt t
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
    else some <$> (stx[1][1].getSepArgs.mapM fun t => Tactic.elabTerm t none)
  let facts ← if stx[2].isNone then do
      let mut fs : Array Expr := #[]
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        if ← isProp d.type then fs := fs.push d.toExpr
      pure fs
    else stx[2][1].getSepArgs.mapM fun t => Tactic.elabTerm t none
  let some r ← abduceClause C facts obs?
    | throwError "abduce: no condition on the observable atoms gives the goal under these facts"
  if r.residual.isConstOf ``True then
    logInfo m!"abduce: the facts give the goal"
    goal.assign (mkApp r.proof (Lean.mkConst ``True.intro))
    replaceMainGoal []
  else
    logInfo m!"abduce: {r.residual}\n  eliminated {r.hidden.toList}\n  kept {r.observed.toList}"
    let newGoal ← mkFreshExprSyntheticOpaqueMVar r.residual
    goal.assign (mkApp r.proof newGoal)
    replaceMainGoal [newGoal.mvarId!]

end ErdosProblems.ArgumentGraph.Abduce

/-!
# Abduction against the corpus

`abduceClause` eliminates the atoms that the given facts control. Here the facts come from the
corpus. Every comparison reading of a corpus theorem (its statement with leading binders
instantiated, a conjunct, or the unfolding of a corpus definition) is indexed under the corpus
constants it mentions, and so is every eventual comparison reading `∀ᶠ X in f, F X`. A
comparison `C` retrieves the readings that share its constants, instantiated by unifying their
subterms with the atoms of `C`, closed, with their hypotheses discharged by the hypotheses in
scope or by the closing battery. Several facts then combine linearly, which a supplier search
that unifies one theorem at a time with the whole of `C` does not see.

`abduceProp` applies this under `∀`, `→`, `∧`, `∃` and the filter quantifiers:

* a hypothesis met on the way down is a fact, together with the comparisons it gives through
  conjunctions, membership in `Ico`, `Icc`, `range` and `filter` and the unfolding of corpus
  finsets; a clause `s.Nonempty` is read as `0 < s.card`;
* a variable bound by `∀` inside the proposition may be eliminated like a hidden atom, and a
  binder that the restated body no longer mentions is dropped;
* under `∃ᶠ X` or `∀ᶠ X` an eventual fact is used at `X` and supplied along the filter; over
  `atTop` every clause `t < X` or `t ≤ X` with `t` free of `X` is such a fact, since it holds for
  all large `X`;
* `∀ A, ∃ X, Q A X` over `ℕ` is asked as `∀ A, ∃ᶠ X, Q A X`, which suffices, puts the eventual
  facts at `X` in reach, and never ties `A` to `X`;
* a statement that becomes `∃ᶠ X, True`, `∀ᶠ X, True` or `∃ w, True` is given, not restated.

A restatement that the hypotheses in scope refute (by `omega` or `linarith`) asks for the
impossible: it implies anything, so it is refused, at the node where it arises. The result is
the restated proposition with a proof that it implies the original.

`restateScoped` restates every hypothesis of a theorem this way, drops those the facts give
outright, and returns the new statement with a proof built from the original theorem. It walks
the telescope one binder at a time: when a hypothesis is restated, the only variables in scope
are the binders before it, in their restated form, so a restatement never mentions a later
binder or the original version of an earlier one. Each change is also returned as a closed
contract `∀ (binders it needs), R → H` with its proof.
-/

set_option autoImplicit false

open Lean Meta Elab Term
open ErdosProblems.ArgumentGraph.Residualise

namespace ErdosProblems.ArgumentGraph.Abduce

/-- Readings of corpus theorems keyed by the corpus constants they mention: comparisons, and
eventual comparisons `∀ᶠ X in f, F X`. -/
structure Facts where
  pointwise : Std.HashMap Name (Array Ref) := {}
  eventual : Std.HashMap Name (Array Ref) := {}

def corpusConsts (unfoldOk : Name → Bool) (e : Expr) : Array Name :=
  e.getUsedConstants.filter unfoldOk

/-- Whether `stmt` is `∀ᶠ X in f, F X` with `F X` a comparison. -/
def eventualComparison? (stmt : Expr) : MetaM Bool := do
  let stmt ← instantiateMVars stmt
  unless stmt.isAppOfArity ``Filter.Eventually 3 do return false
  let p := stmt.getArg! 1
  let α := stmt.getArg! 0
  withLocalDeclD `X α fun x => do return (← comparison? (p.beta #[x])).isSome

/-- Add the comparison and eventual comparison readings of the theorem `n`. -/
def indexFacts (facts : Facts) (unfoldOk : Name → Bool) (n : Name) (depth : Nat) :
    MetaM (Facts × Nat) := do
  let some ci := (← getEnv).find? n | return (facts, 0)
  let found ← withNewMCtxDepth do
    let lvls ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
    let ty := ci.type.instantiateLevelParams ci.levelParams lvls
    let rs := (← Residualise.budgeted 2000 (readingPaths unfoldOk ty #[] depth)).getD #[]
    let mut out : Array (Bool × Array Name × Array Step) := #[]
    for (stmt, path) in rs do
      let stmt ← instantiateMVars stmt
      let ev ← eventualComparison? stmt
      if ev || (← comparison? stmt).isSome then
        let cs := corpusConsts unfoldOk stmt
        unless cs.isEmpty do out := out.push (ev, cs, path)
    return out
  let mut facts := facts
  for (ev, cs, path) in found do
    for c in cs do
      let ref : Ref := { name := n, path }
      if ev then
        let refs := (facts.eventual.getD c #[]).push ref
        facts := { facts with eventual := facts.eventual.insert c refs }
      else
        let refs := (facts.pointwise.getD c #[]).push ref
        facts := { facts with pointwise := facts.pointwise.insert c refs }
  return (facts, found.size)

/-- The facts of every theorem of the modules under `roots`. -/
def buildFactIndex (roots : Array Name) (unfoldOk : Name → Bool) (depth : Nat := 6) :
    MetaM (Facts × Nat) := do
  let env ← getEnv
  let mut facts : Facts := {}
  let mut total := 0
  for modName in env.header.moduleNames, data in env.header.moduleData do
    unless roots.any (·.isPrefixOf modName) do continue
    for n in data.constNames do
      if n.isInternal then continue
      let some (.thmInfo _) := env.find? n | continue
      let (f, k) ← indexFacts facts unfoldOk n depth
      facts := f
      total := total + k
  return (facts, total)

/-- The facts of the given theorems only (a supplier set). -/
def factsOf (names : Array Name) (unfoldOk : Name → Bool) (depth : Nat := 8) : MetaM Facts := do
  let mut facts : Facts := {}
  for n in names do
    facts := (← indexFacts facts unfoldOk n depth).1
  return facts

/-- Subterms of `e` whose head is a constant, up to `fuel` nodes. -/
def appSubterms : Nat → Expr → Array Expr → Array Expr
  | 0, _, acc => acc
  | fuel + 1, e, acc =>
    match e with
    | .app f a =>
      let acc := if e.getAppFn.isConst then acc.push e else acc
      appSubterms fuel a (appSubterms fuel f acc)
    | .mdata _ b => appSubterms fuel b acc
    | _ => acc

/-- Replay a reading with fresh metavariables for its binders (propositional and instance
binders are obligations): its proof, its statement and the obligations. -/
def replayPlain (proof stmt : Expr) (obls : Array Expr) :
    List Step → MetaM (Option (Expr × Expr × Array Expr))
  | [] => return some (proof, ← instantiateMVars stmt, obls)
  | s :: rest => do
    let stmt ← whnfR (← instantiateMVars stmt)
    match s with
    | .inst =>
        let .forallE _ d b bi := stmt | return none
        let isP ← isProp d
        let m ← mkFreshExprMVar d (if isP then .syntheticOpaque else .natural)
        let obls := if isP || bi.isInstImplicit then obls.push m else obls
        replayPlain (mkApp proof m) (b.instantiate1 m) obls rest
    | .left =>
        unless stmt.isAppOfArity ``And 2 do return none
        replayPlain (← mkAppM ``And.left #[proof]) stmt.appFn!.appArg! obls rest
    | .right =>
        unless stmt.isAppOfArity ``And 2 do return none
        replayPlain (← mkAppM ``And.right #[proof]) stmt.appArg! obls rest
    | .unfold =>
        let some u ← unfoldDefinition? stmt | return none
        replayPlain proof u obls rest
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
        replayPlain p (← inferType p) obls rest

/-- The atoms of the comparison `C`. -/
def atomsOf (C : Expr) : MetaM (Array Expr) := do
  let some (α, a, b, _) ← comparison? C | return #[]
  let (natSub, integral) ← carrierKind α
  Mathlib.Tactic.AtomM.run .reducible do
    discard <| linForm natSub integral 256 a
    discard <| linForm natSub integral 256 b
    return (← get).atoms

/-- The compound atoms of the comparisons in `e` that mention no bound variable. -/
def comparisonAtoms (e : Expr) : MetaM (Array Expr) := do
  let mut out : Array Expr := #[]
  for s in appSubterms 4000 e #[e] do
    if s.hasLooseBVars then continue
    if (← comparison? s).isSome then
      for a in ← atomsOf s do
        if a.getAppFn.isConst && !out.contains a then out := out.push a
  return out

/-- Discharge the obligations of a replayed reading: instances by synthesis, propositions by a
hypothesis in scope or by the battery. -/
def dischargeObligations (locals obls : Array Expr) : TermElabM Bool := do
  for o in obls do
    if ← o.mvarId!.isAssigned then continue
    let oT ← instantiateMVars (← inferType o)
    if oT.hasMVar then return false
    if (← isClass? oT).isSome then
      let some inst ← (try some <$> synthInstance oT catch _ => pure none) | return false
      o.mvarId!.assign inst
      continue
    let mut done := false
    for l in locals do
      if ← withReducible (isDefEq (← inferType l) oT) then
        o.mvarId!.assign l
        done := true
        break
    unless done do
      let some p ← battery oT | return false
      o.mvarId!.assign p
  return true

/-- Candidate readings for a statement with corpus constants `cs`, best overlap first. -/
def rankedRefs (idx : Std.HashMap Name (Array Ref)) (cs : Array Name) (exclude : Array Name)
    (maxK : Nat) : Array Ref := Id.run do
  let mut scored : Array (Ref × Nat) := #[]
  for c in cs do
    for r in idx.getD c #[] do
      if exclude.contains r.name then continue
      match scored.findIdx? (·.1 == r) with
      | some i => scored := scored.modify i fun (x, k) => (x, k + 1)
      | none => scored := scored.push (r, 1)
  return ((scored.qsort fun a b => a.2 > b.2).extract 0 maxK).map (·.1)

/-- Unify the metavariable-bearing subterms of `stmt` with the atoms, one by one. -/
def unifyWithAtoms (stmt : Expr) (atoms : Array Expr) : MetaM Unit := do
  for t in atoms do
    for u in appSubterms 4000 stmt #[] do
      if u.hasMVar && u.getAppFn.constName? == t.getAppFn.constName? then
        let s2 ← saveState
        unless ← isDefEq u t do s2.restore

/-- The local variables of non-propositional type, in declaration order. -/
def ctxDataVars : MetaM (Array Expr) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if ← isProp d.type then continue
    if (← whnfR d.type).isSort then continue
    out := out.push d.toExpr
  return out

/-- The closings of a replayed reading: its data metavariables assigned local variables of
their types (at most `cap` closings), its obligations discharged; each closing is `ts`
instantiated. -/
def closeByContext (ts obls vars locals : Array Expr) (cap : Nat := 4) :
    TermElabM (Array (Array Expr)) := do
  let mut ms : Array MVarId := #[]
  for t in ts do
    for m in ← getMVars (← instantiateMVars t) do
      unless ms.contains m do ms := ms.push m
  let rec go (ms : List MVarId) (fuel : Nat) : TermElabM (Array (Array Expr)) := do
    match fuel, ms with
    | 0, _ => return #[]
    | _, [] =>
      let s ← saveState
      let ok ← dischargeObligations locals obls
      let es ← ts.mapM instantiateMVars
      s.restore
      return if ok && !es.any (·.hasMVar) then #[es] else #[]
    | fuel + 1, m :: rest =>
      if ← m.isAssigned then return ← go rest fuel
      if (← m.getKind).isSyntheticOpaque then return ← go rest fuel
      let mT ← instantiateMVars (← m.getType)
      let mut out : Array (Array Expr) := #[]
      for v in vars do
        if out.size ≥ cap then break
        let s ← saveState
        if ← isDefEq (← inferType v) mT then
          m.assign v
          out := out ++ (← go rest fuel)
        s.restore
      return out.extract 0 cap
  go ms.toList (ms.size + 1)

/-- Facts for the comparison `C` from the readings `refs`: each instantiated by unifying its
subterms with the compound atoms of `C`, then closed by local variables, its hypotheses
discharged. -/
def retrieveFacts (refs : Array Ref) (locals : Array Expr) (C : Expr) :
    TermElabM (Array Expr) := do
  let some _ ← comparison? C | return #[]
  let atoms := (← atomsOf C).filter (·.getAppFn.isConst)
  let vars ← ctxDataVars
  let mut out : Array Expr := #[]
  for ref in refs do
    let s ← saveState
    let got? ← withHeartbeatBudget 4000 do
      let c0 ← mkConstWithFreshMVarLevels ref.name
      let some (proof, stmt, obls) ← replayPlain c0 (← inferType c0) #[] ref.path.toList
        | return #[]
      -- any carrier: a count over `ℕ` and a bound over `ℝ` meet after lifting
      let some _ ← comparison? stmt | return #[]
      unifyWithAtoms stmt atoms
      return (← closeByContext #[proof] obls vars locals).map (·[0]!)
    s.restore
    for p in got?.getD #[] do
      unless out.contains p do out := out.push p
  return out

/-- Eventual facts for the body `B` of a filter quantifier over `f` at the variable `X`, from
the readings `refs` of the form `∀ᶠ Y in f, F Y`: `F X` instantiated by unifying its subterms
with the comparison atoms of `B`, then closed by local variables. Returns each proof with its
statement at `X`. -/
def retrieveEventual (refs : Array Ref) (locals : Array Expr) (B X f : Expr) :
    TermElabM (Array (Expr × Expr)) := do
  let atoms ← comparisonAtoms B
  let vars ← ctxDataVars
  let mut out : Array (Expr × Expr) := #[]
  for ref in refs do
    let s ← saveState
    let got? ← withHeartbeatBudget 4000 do
      let c0 ← mkConstWithFreshMVarLevels ref.name
      let some (proof, stmt, obls) ← replayPlain c0 (← inferType c0) #[] ref.path.toList
        | return #[]
      unless stmt.isAppOfArity ``Filter.Eventually 3 do return #[]
      unless ← isDefEq (stmt.getArg! 2) f do return #[]
      let F := (stmt.getArg! 1).beta #[X]
      unifyWithAtoms F atoms
      return (← closeByContext #[proof, F] obls vars locals).map fun es => (es[0]!, es[1]!)
    s.restore
    for r in got?.getD #[] do
      unless out.any (·.2 == r.2) do out := out.push r
  return out

/-- Membership and nonemptiness read as comparisons: `x ∈ Ico a b`, `Icc`, `range`, `filter`
and corpus finsets (unfolded), and `s.Nonempty` as `0 < s.card`. Returns the normal form with a
proof that it equals `P`, or `none` when nothing applies. -/
def comparisonForm (unfoldOk : Name → Bool) (P : Expr) : MetaM (Option (Expr × Expr)) := do
  let mut thms : SimpTheorems := {}
  for n in [``Finset.mem_Ico, ``Finset.mem_Icc, ``Finset.mem_Ioc, ``Finset.mem_Ioo,
      ``Finset.mem_range, ``Finset.mem_filter] do
    thms ← thms.addConst n
  thms ← thms.addConst ``Finset.card_pos (inv := true)
  -- a corpus finset is unfolded only as the collection of a membership, never inside atoms
  if P.isAppOfArity ``Membership.mem 5 then
    if let .const c _ := (P.getArg! 3).getAppFn then
      if unfoldOk c then
        if let some (.defnInfo _) := (← getEnv).find? c then
          thms ← thms.addDeclToUnfold c
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let some (r, _) ← Residualise.budgeted 2000 (simp P ctx) | return none
  if r.expr == P then return none
  match r.proof? with
  | some p => return some (r.expr, p)
  | none => return some (r.expr, ← mkEqRefl P)

/-- The comparison facts a hypothesis gives, through conjunctions and `comparisonForm`. -/
def expandFact (unfoldOk : Name → Bool) : Nat → Expr → MetaM (Array Expr)
  | 0, _ => return #[]
  | fuel + 1, h => do
    let T ← instantiateMVars (← inferType h)
    if (← comparison? T).isSome then return #[h]
    if T.isAppOfArity ``And 2 then
      return (← expandFact unfoldOk fuel (← mkAppM ``And.left #[h])) ++
        (← expandFact unfoldOk fuel (← mkAppM ``And.right #[h]))
    match ← comparisonForm unfoldOk T with
    | some (T', eq) =>
      if T' == T then return #[] else expandFact unfoldOk fuel (← mkEqMP eq h)
    | none => return #[]

/-- The proof `fun h : A => h`. -/
def idProof (A : Expr) : MetaM Expr := withLocalDeclD `h A fun h => mkLambdaFVars #[h] h

/-- How `abduceProp` finds facts and witnesses, and which readings it may use. -/
structure Retrieval where
  unfoldOk : Name → Bool
  /-- corpus facts for a comparison, given the hypotheses in scope -/
  pointwise : Array Expr → Expr → TermElabM (Array Expr)
  /-- eventual facts for a filter body `B` at `X` over `f`, given the hypotheses in scope -/
  eventual : Array Expr → Expr → Expr → Expr → TermElabM (Array (Expr × Expr))
  /-- candidate witnesses of a type, given the filter variable in scope -/
  witnesses : Option (Expr × Expr) → Expr → TermElabM (Array Expr) := fun _ _ => pure #[]
  /-- witness evaluations left for the current statement, shared by nested existentials -/
  evals : Option (IO.Ref Nat) := none
  /-- witness evaluations allowed for one statement -/
  evalBudget : Nat := 32
  /-- print progress lines on standard error, flushed at once -/
  trace : Bool := false
  /-- refuse a restatement that the hypotheses in scope refute -/
  vacuityGuard : Bool := true
  /-- over `atTop`, read every clause `t < X` or `t ≤ X` with `t` free of `X` as eventual -/
  eventualBounds : Bool := true
  /-- read a named corpus predicate through its definition when nothing else applies -/
  unfoldHeads : Bool := true
  /-- round a count's strict lower bound up to the next integer before eliminating the count -/
  integerRounding : Bool := false
  /-- for each hypothesis changed, also ask whether standard automation proves it in scope -/
  baseline : Bool := false
  /-- what the search did for the current statement: `cofinal`, `witness`, `integer`,
  `eventual_bound`, `given_through_filter`, `vacuity_refused` -/
  notes : Option (IO.Ref (Array String)) := none
  /-- the corpus theorems whose readings entered an elimination that gave a restatement -/
  used : Option (IO.Ref (Array Name)) := none

/-- A progress line when tracing is on. -/
def Retrieval.say (R : Retrieval) (msg : String) : TermElabM Unit := do
  if R.trace then
    IO.eprintln msg
    (← IO.getStderr).flush

/-- Give the next statement its full allowance of witness evaluations. -/
def Retrieval.resetEvals (R : Retrieval) : TermElabM Unit := do
  if let some r := R.evals then r.set R.evalBudget

/-- Record what the search did. -/
def Retrieval.note (R : Retrieval) (tag : String) : TermElabM Unit := do
  if let some r := R.notes then
    let acc ← r.get
    unless acc.contains tag do r.set (acc.push tag)

/-- Record the corpus theorems named by the facts that entered an elimination. The engine's own
lemmas are not facts. -/
def Retrieval.noteUsed (R : Retrieval) (facts : Array Expr) : TermElabM Unit := do
  let some r := R.used | return
  let env ← getEnv
  let mut acc ← r.get
  for f in facts do
    for c in (← instantiateMVars f).getUsedConstants do
      if acc.contains c || !R.unfoldOk c || (`ErdosProblems.ArgumentGraph.Abduce).isPrefixOf c then
        continue
      if let some (.thmInfo _) := env.find? c then acc := acc.push c
  r.set acc

/-- Start the record of the next statement. -/
def Retrieval.resetNotes (R : Retrieval) : TermElabM Unit := do
  if let some r := R.notes then r.set #[]
  if let some r := R.used then r.set #[]

/-- The record of the current statement. -/
def Retrieval.readNotes (R : Retrieval) : TermElabM (Array String × Array Name) := do
  let ns ← match R.notes with
    | some r => r.get
    | none => pure #[]
  let us ← match R.used with
    | some r => r.get
    | none => pure #[]
  return (ns, us)

/-- A cofinal existential from a frequent universal: if for arbitrarily large `X` the statement
`Q A X` holds for every `A ≤ X`, then every `A` has some `X` with `Q A X`. Kept for replay of
earlier restatements; `abduceProp` now asks for the weaker `∀ A, ∃ᶠ X, Q A X`. -/
theorem forall_exists_of_frequently_forall_le {Q : ℕ → ℕ → Prop}
    (h : ∃ᶠ X in Filter.atTop, ∀ A, A ≤ X → Q A X) : ∀ A, ∃ X, Q A X := by
  intro A
  obtain ⟨X, hX, hQ⟩ := Filter.frequently_atTop.mp h A
  exact ⟨X, hQ A hX⟩

/-- A cofinal existential from frequent statements: if for every `A` the statement `Q A X`
holds for arbitrarily large `X`, then every `A` has some `X` with `Q A X`. -/
theorem forall_exists_of_forall_frequently {Q : ℕ → ℕ → Prop}
    (h : ∀ A, ∃ᶠ X in Filter.atTop, Q A X) : ∀ A, ∃ X, Q A X :=
  fun A => (h A).exists

/-- The old cofinal reading asks for more than the new one: `∃ᶠ X, ∀ A ≤ X, Q A X` gives
`∀ A, ∃ᶠ X, Q A X`, while `Q A X := A < X / 2 + 1` satisfies the second and not the first. -/
theorem forall_frequently_of_frequently_forall_le {Q : ℕ → ℕ → Prop}
    (h : ∃ᶠ X in Filter.atTop, ∀ A, A ≤ X → Q A X) : ∀ A, ∃ᶠ X in Filter.atTop, Q A X := by
  intro A
  refine (h.and_eventually (Filter.eventually_ge_atTop A)).mono ?_
  intro X hX
  exact hX.1 A hX.2

theorem not_frequently_forall_le_half :
    ¬ ∃ᶠ X in Filter.atTop, ∀ A : ℕ, A ≤ X → A < X / 2 + 1 := by
  intro h
  obtain ⟨X, hX, hX2⟩ := (h.and_eventually (Filter.eventually_ge_atTop 2)).exists
  have := hX X le_rfl
  omega

theorem forall_frequently_half : ∀ A : ℕ, ∃ᶠ X in Filter.atTop, A < X / 2 + 1 := by
  intro A
  refine (Filter.eventually_ge_atTop (2 * A)).frequently.mono ?_
  intro X hX
  omega

/-- A count above a nonnegative real bound is at least the next integer. -/
theorem floor_add_one_le_of_lt {a : ℝ} {m : ℕ} (ha : 0 ≤ a) (h : a < (m : ℝ)) :
    ((⌊a⌋₊ : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by
  have h1 : ⌊a⌋₊ < m := (Nat.floor_lt ha).mpr h
  have h2 : ⌊a⌋₊ + 1 ≤ m := by omega
  exact_mod_cast h2

/-- The key of a statement, as the argument-continuation export computes it: binder names and
binder kinds normalised, then two hashes of the result. -/
partial def keyNormalise (e : Expr) (depth : Nat := 0) : Expr :=
  let name := Name.mkSimple s!"x{depth}"
  match e with
  | .forallE _ t b _ => .forallE name (keyNormalise t depth) (keyNormalise b (depth + 1)) .default
  | .lam _ t b _ => .lam name (keyNormalise t depth) (keyNormalise b (depth + 1)) .default
  | .letE _ t v b nondep =>
      .letE name (keyNormalise t depth) (keyNormalise v depth) (keyNormalise b (depth + 1)) nondep
  | .app f a => .app (keyNormalise f depth) (keyNormalise a depth)
  | .mdata _ b => keyNormalise b depth
  | .proj s i b => .proj s i (keyNormalise b depth)
  | e => e

private def hex16 (n : Nat) : String :=
  let digits := Nat.toDigits 16 n
  String.ofList (List.replicate (16 - digits.length) '0' ++ digits)

def statementKey (e : Expr) : String :=
  let n := keyNormalise e
  hex16 (hash (toString n)).toNat ++ hex16 n.hash.toNat

/-- The conjuncts of `P`. -/
partial def conjunctsOf (P : Expr) : Array Expr :=
  if P.isAppOfArity ``And 2 then conjunctsOf P.appFn!.appArg! ++ conjunctsOf P.appArg! else #[P]

/-- Whether `P` contradicts the comparisons in scope: `omega` or `linarith` derives `False` from
them and the conjuncts of `P`, under a small budget. A restatement asking for such a `P` asks
for the impossible. Failing to refute proves nothing. -/
def refutedInScope (locals : Array Expr) (P : Expr) : TermElabM Bool := do
  let P ← instantiateMVars P
  if P.hasMVar || P.isConstOf ``True then return false
  let mut hyps : Array Expr := #[]
  for f in locals do
    let T ← instantiateMVars (← inferType f)
    if T.hasMVar || hyps.contains T then continue
    if (← comparison? T).isSome then hyps := hyps.push T
  hyps := hyps.extract 0 24 ++ conjunctsOf P
  let decls := (Array.range hyps.size).map fun i => (Name.mkSimple s!"hv{i}", hyps[i]!)
  let stmt ← withLocalDeclsDND decls fun hs => mkForallFVars hs (Lean.mkConst ``False)
  for tac in ["(intros; omega)", "(intros; linarith)"] do
    if (← proveByTactic stmt tac 3000).isSome then return true
  return false

/-- For a filter body `B` at `X` over `atTop`: the eventual facts `t < X` (proofs of
`∀ᶠ Y in atTop, t < Y`, with their statements at `X`) for every term `t` free of `X` that `B`
compares with `X` from below (`t ≤ X`, `t < X`, `X ≥ t`, `X > t`), and for every variable in
scope of the type of `X` that `B` mentions: a quantity fixed while `X` grows is eventually below
it (the threshold `A` of `∀ A, ∃ᶠ X, …`, say). -/
def atTopBounds (B X f : Expr) : TermElabM (Array (Expr × Expr)) := do
  let α ← inferType X
  let some top ← (try some <$> mkAppOptM ``Filter.atTop #[α, none] catch _ => pure none)
    | return #[]
  unless ← isDefEq f top do return #[]
  let mut candidates : Array Expr := #[]
  for s in appSubterms 4000 B #[B] do
    if s.hasLooseBVars then continue
    let some (β, t, u, rel) ← comparison? s | continue
    if rel == .eq || u != X || candidates.contains t then continue
    if t.containsFVar X.fvarId! || t.hasLooseBVars || t.hasMVar then continue
    unless ← isDefEq β α do continue
    candidates := candidates.push t
  for v in ← ctxDataVars do
    if v == X || candidates.contains v || !B.containsFVar v.fvarId! then continue
    if ← isDefEq (← inferType v) α then candidates := candidates.push v
  let mut out : Array (Expr × Expr) := #[]
  for t in candidates do
    let some pf ← (try some <$> mkAppM ``Filter.eventually_gt_atTop #[t] catch _ => pure none)
      | continue
    out := out.push (pf, ← mkAppM ``LT.lt #[t, X])
  return out

/-- The binders of `pre` that the expressions `es` mention, together with those the types of
these mention, in the order of `pre`. -/
def neededBinders (pre : Array Expr) (es : Array Expr) : MetaM (Array Expr) := do
  let mut need : Std.HashSet FVarId := {}
  for e in es do
    for x in pre do
      if e.containsFVar x.fvarId! then need := need.insert x.fvarId!
  for x in pre.reverse do
    if need.contains x.fvarId! then
      let T ← inferType x
      for y in pre do
        if T.containsFVar y.fvarId! then need := need.insert y.fvarId!
  return pre.filter fun x => need.contains x.fvarId!

/-- Every closing of the metavariables of `t` by local variables of their types (at most
`cap` of them); `t` itself when it has none. -/
def fillByContext (t : Expr) (vars : Array Expr) (cap : Nat := 8) : MetaM (Array Expr) := do
  let t ← instantiateMVars t
  let ms := (← getMVars t).toList
  let rec go (ms : List MVarId) (fuel : Nat) : MetaM (Array Expr) := do
    match fuel, ms with
    | 0, _ => return #[]
    | _, [] =>
      let e ← instantiateMVars t
      return if e.hasMVar then #[] else #[e]
    | fuel + 1, m :: rest =>
      if ← m.isAssigned then return ← go rest fuel
      let mT ← instantiateMVars (← m.getType)
      let mut out : Array Expr := #[]
      for v in vars do
        if out.size ≥ cap then break
        let s ← saveState
        if ← isDefEq (← inferType v) mT then
          m.assign v
          out := out ++ (← go rest fuel)
        s.restore
      return out.extract 0 cap
  go ms (ms.length + 1)

/-- The number of clauses a proposition leaves: `True` none, a conjunction the sum, an
existential one more than its body (a witness left unchosen is itself a cost), anything else one
(through binders and the filter quantifiers). -/
def clauseScore : Nat → Expr → Nat
  | 0, _ => 1
  | fuel + 1, e =>
    if e.isConstOf ``True then 0
    else if e.isAppOfArity ``And 2 then clauseScore fuel e.appFn!.appArg! + clauseScore fuel e.appArg!
    else if e.isAppOfArity ``Exists 2 then
      match e.appArg! with
      | .lam _ _ b _ => 1 + clauseScore fuel b
      | _ => 2
    else if e.isAppOfArity ``Filter.Frequently 3 || e.isAppOfArity ``Filter.Eventually 3 then
      match e.getArg! 1 with
      | .lam _ _ b _ => clauseScore fuel b
      | _ => 1
    else match e with
      | .forallE _ _ b _ => clauseScore fuel b
      | _ => 1

/-- Candidate witnesses of type `α` from the readings of a fact index: subterms of that type
(an eventual reading read at the filter variable in scope), their metavariables closed by local
variables. Terms headed by a corpus constant come first. -/
def witnessCandidates (facts : Facts) (unfoldOk : Name → Bool) (fv : Option (Expr × Expr))
    (α : Expr) (maxK : Nat := 12) : TermElabM (Array Expr) := do
  let mut refs : Array Ref := #[]
  for (_, rs) in facts.eventual.toList ++ facts.pointwise.toList do
    for r in rs do
      unless refs.contains r do refs := refs.push r
  let vars ← ctxDataVars
  let mut out : Array (Expr × Nat) := #[]
  for ref in refs do
    let s ← saveState
    let found ← try
        let c0 ← mkConstWithFreshMVarLevels ref.name
        let some (_, stmt, _) ← replayPlain c0 (← inferType c0) #[] ref.path.toList
          | pure #[]
        let body ← match fv with
          | some (X, f) =>
            if stmt.isAppOfArity ``Filter.Eventually 3 then
              if ← isDefEq (stmt.getArg! 2) f then pure ((stmt.getArg! 1).beta #[X]) else pure stmt
            else pure stmt
          | none => pure stmt
        let mut acc : Array (Expr × Nat) := #[]
        for u in appSubterms 4000 body #[] do
          if u.hasLooseBVars then continue
          let some uT ← (try some <$> inferType u catch _ => pure none) | continue
          unless ← isDefEq uT α do continue
          let fills := (← getMVars (← instantiateMVars u)).size
          for e in ← fillByContext u vars do
            unless acc.any (·.1 == e) do acc := acc.push (e, fills)
        pure acc
      catch _ => pure #[]
    s.restore
    for (e, k) in found do
      unless out.any (·.1 == e) do out := out.push (e, k)
  let corpusHead (e : Expr) : Bool := match e.getAppFn with
    | .const c _ => unfoldOk c
    | _ => false
  -- corpus terms first, and among them those needing the fewest local substitutions; ties keep
  -- the order found, in which local variables are tried outermost first
  let key (p : Expr × Nat) : Nat := (if corpusHead p.1 then 0 else 1000) + p.2
  let mut indexed : Array (Expr × Nat × Nat) := #[]
  for i in [0:out.size] do
    indexed := indexed.push (out[i]!.1, key out[i]!, i)
  let ranked := indexed.qsort fun a b => a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)
  return (ranked.extract 0 maxK).map (·.1)

/-- `(↑e : ℝ)` for `e : ℕ`, with the cast pushed through sums, products by numerals and
numerals. -/
def castReal : Nat → Expr → MetaM Expr
  | 0, e => mkAppOptM ``Nat.cast #[Lean.mkConst ``Real, none, e]
  | fuel + 1, e => do
    let realT := Lean.mkConst ``Real
    if let some q ← numeral? 64 e then return ← numeralExpr realT q
    match e.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
        mkAppM ``HAdd.hAdd #[← castReal fuel a, ← castReal fuel b]
    | (``HMul.hMul, #[_, _, _, _, a, b]) =>
        if let some q ← numeral? 64 a then
          return ← mkAppM ``HMul.hMul #[← numeralExpr realT q, ← castReal fuel b]
        if let some q ← numeral? 64 b then
          return ← mkAppM ``HMul.hMul #[← castReal fuel a, ← numeralExpr realT q]
        mkAppOptM ``Nat.cast #[realT, none, e]
    | _ => mkAppOptM ``Nat.cast #[realT, none, e]

/-- An atom with a cast from `ℕ` removed, so that a count and its real cast compare equal. -/
def uncast (e : Expr) : Expr :=
  if e.isAppOfArity ``Nat.cast 3 then e.appArg! else e

/-- The facts relevant to the comparison `C`: those sharing an atom with it, most shared atoms
first, then those sharing an atom with one of these, at most `cap` in all. Elimination grows
doubly exponentially in the facts, and a hypothesis in scope that mentions none of the clause's
quantities cannot help eliminate them. -/
def relevantFacts (C : Expr) (facts : Array Expr) (cap : Nat := 16) : MetaM (Array Expr) := do
  if facts.size ≤ cap then return facts
  let goalAtoms := ((← try atomsOf C catch _ => pure #[])).map uncast
  if goalAtoms.isEmpty then return facts.extract 0 cap
  let mut scored : Array (Expr × Array Expr × Nat) := #[]
  for f in facts do
    let T ← instantiateMVars (← inferType f)
    let as := ((← try atomsOf T catch _ => pure #[])).map uncast
    if as.isEmpty then continue
    scored := scored.push (f, as, (as.filter goalAtoms.contains).size)
  let hop1 := (scored.filter (·.2.2 > 0)).qsort fun a b => a.2.2 > b.2.2
  let atoms1 := hop1.foldl (fun acc s => acc ++ s.2.1) goalAtoms
  let hop2 := scored.filter fun s => s.2.2 == 0 && s.2.1.any atoms1.contains
  return ((hop1 ++ hop2).map (·.1)).extract 0 cap

/-- The comparison over `ℝ` of a comparison over `ℕ`. -/
def realComparison? (P : Expr) : MetaM (Option Expr) := do
  let some (α, a, b, rel) ← comparison? P | return none
  unless (← carrierKind α).1 do return none
  let a' ← castReal 64 a
  let b' ← castReal 64 b
  match rel with
  | .le => return some (← mkAppM ``LE.le #[a', b'])
  | .lt => return some (← mkAppM ``LT.lt #[a', b'])
  | .eq => return some (← mkAppM ``Eq #[a', b'])

def isRealCarrier (P : Expr) : MetaM Bool := do
  let some (β, _, _, _) ← comparison? P | return false
  return (← whnfR β).isConstOf ``Real


/-- The rounded lower bounds of the counts among `facts`: for a fact `a < ↑m` over `ℝ`, with `m`
a natural number and `a` a nonnegative combination of parameters, the facts `↑⌊a⌋₊ + 1 ≤ ↑m`
and `a < ↑⌊a⌋₊ + 1`, and the floor `↑⌊a⌋₊`, which is to stay observable. Over the reals the
count only exceeds `a`; as an integer it is at least `⌊a⌋₊ + 1`, and a condition on the other
quantities that uses this is weaker than the one the reals give. -/
def integerRoundings (facts : Array Expr) : TermElabM (Array Expr × Array Expr) := do
  let realT := Lean.mkConst ``Real
  let mut out : Array Expr := #[]
  let mut floors : Array Expr := #[]
  for f in facts do
    let T ← instantiateMVars (← inferType f)
    let some (α, a, b, rel) ← comparison? T | continue
    unless rel == .lt && (← whnfR α).isConstOf ``Real do continue
    unless (isNatCast b).isSome do continue
    let aAtoms ← Mathlib.Tactic.AtomM.run .reducible do
      discard <| linForm false false 256 a
      return (← get).atoms
    if aAtoms.isEmpty || !aAtoms.all isParameter then continue
    let some F ← (try some <$> (do
        mkAppOptM ``Nat.cast #[realT, none, ← mkAppM ``Nat.floor #[a]]) catch _ => pure none)
      | continue
    if floors.contains F then continue
    let one ← numeralExpr realT 1
    let F1 ← mkAppM ``HAdd.hAdd #[F, one]
    let some p1 ← proveByTactic (← mkArrow T (← mkAppM ``LE.le #[F1, b]))
        "(intro h; exact ErdosProblems.ArgumentGraph.Abduce.floor_add_one_le_of_lt (by positivity) h)"
      | continue
    let some p2 ← proveByTactic (← mkAppM ``LT.lt #[a, F1]) "(exact Nat.lt_floor_add_one _)"
      | continue
    out := out ++ #[mkApp p1 f, p2]
    floors := floors.push F
  return (out, floors)

/-- Abduce one comparison. When the facts mix counts over `ℕ` with bounds over `ℝ`, the
comparisons over `ℕ` (the clause and the facts) are lifted to `ℝ` first. The variables bound
inside the proposition are eliminated innermost first; then none are. With `integerRounding`,
the elimination is first tried with the counts' lower bounds rounded to integers. A
restatement counts only when the facts give the clause or eliminate an atom. -/
def abduceLeaf (R : Retrieval) (locals bound : Array Expr) (C : Expr) :
    TermElabM (Option (Expr × Expr)) := do
  let raw ← relevantFacts C (locals ++ (← R.pointwise locals C))
  let mut facts := raw
  let mut goal := C
  let mut back : Option Expr := none
  let factTypes ← raw.mapM fun f => do instantiateMVars (← inferType f)
  if ← factTypes.anyM (fun t => isRealCarrier t) then
    if let some CR ← realComparison? C then
      if let some pb ← proveByTactic (← mkArrow CR C) "(intro h; exact_mod_cast h)" then
        goal := CR
        back := some pb
    -- over `ℝ` a count's fact is kept only in its lifted form
    let mut lifted : Array Expr := #[]
    let mut kept : Array Expr := #[]
    for i in [0:raw.size] do
      let mut done := false
      if let some TR ← realComparison? factTypes[i]! then
        if let some p ← proveByTactic (← mkArrow factTypes[i]! TR) "(intro h; exact_mod_cast h)" then
          lifted := lifted.push (mkApp p raw[i]!)
          done := true
      unless done do kept := kept.push raw[i]!
    facts := if back.isSome then kept ++ lifted else raw ++ lifted
  let (rounding, floors) ←
    if R.integerRounding && (← isRealCarrier goal) then integerRoundings facts
    else pure (#[], #[])
  R.say s!"[leaf] {facts.size} facts, {rounding.size} rounded, {bound.size} bound variables"
  -- elimination can grow doubly exponentially in the facts; each attempt has its own budget, and
  -- running out counts as finding nothing
  let attempt (extra : Array Expr) (rounded : Bool) :
      TermElabM (Option (Expr × Expr × Array Expr)) := do
    let fs := if rounded then facts ++ rounding else facts
    let t0 ← IO.monoMsNow
    let r? := (← Residualise.budgetedTerm 20000
      (abduceClause goal fs none extra (if rounded then floors else #[]))).join
    R.say s!"[leaf] elimination with {extra.size} extra hidden{if rounded then ", rounded" else ""}: {if r?.isSome then "done" else "none"} in {(← IO.monoMsNow) - t0} ms"
    let some r := r? | return none
    unless r.residual.isConstOf ``True || !r.hidden.isEmpty do return none
    -- a variable the statement binds is eliminated only through a fact that mentions it: with its
    -- sign alone, `A ≤ N` over all `N ≥ 0` would become `A ≤ 0`, true of no positive `A`
    for x in extra do
      unless ← fs.anyM (fun f => do return (← instantiateMVars (← inferType f)).containsFVar x.fvarId!) do
        return none
    if ← withReducible (isDefEq r.residual goal) then return none
    return some (r.residual, r.proof, fs)
  let mut found : Option (Expr × Expr × Array Expr) := none
  for rounded in (if floors.isEmpty then [false] else [true, false]) do
    if found.isNone then
      for k in [1:bound.size + 1] do
        if found.isNone then
          found ← attempt (bound.extract (bound.size - k) bound.size) rounded
      if found.isNone then found ← attempt #[] rounded
      if found.isSome && rounded then R.note "integer"
  let some (C', pf, used) := found | return none
  R.noteUsed used
  match back with
  | none => return some (C', pf)
  | some pb =>
    let proof ← withLocalDeclD `h C' fun h => do mkLambdaFVars #[h] (mkApp pb (mkApp pf h))
    return some (C', proof)

/-- `C'` with a proof of `C' → C`: each comparison is abduced against the hypotheses in scope
and the facts `R` finds, under `∀`, `→`, `∧`, `∃` and the filter quantifiers. `none` when
nothing changes. `bound` lists the variables bound by `∀` inside the original proposition and
`fv` the filter variable in scope.

* A binder whose body becomes `True` goes with it. A data binder that the restated body no
  longer mentions is dropped, and so is `∀ x, hyp x → P'` with `P'` free of `x`. A hypothesis
  binder stays otherwise: dropping it would ask for more.
* `∀ A, ∃ X, Q A X` over `ℕ` may be read as `∀ A, ∃ᶠ X, Q A X`, which puts the eventual facts at
  `X` in reach; the reading is kept only when it restates something.
* `∃ w, P w` tries the witnesses `R` proposes and keeps the one leaving the fewest clauses.
* A restatement the hypotheses in scope refute is refused where it arises (`vacuityGuard`). -/
def abduceProp (R : Retrieval) : Nat → Array Expr → Array Expr → Option (Expr × Expr) → Expr →
    TermElabM (Option (Expr × Expr))
  | 0, _, _, _, _ => return none
  | fuel + 1, locals, bound, fv, C => do
    let C ← instantiateMVars C
    match C with
    | .forallE n d b bi =>
      -- the cofinal reading, `∀ A, ∃ᶠ X, Q A X`
      if (← whnfR d).isConstOf ``Nat && !(← isProp d) then
        let natT := Lean.mkConst ``Nat
        let cof? ← withLocalDecl n bi d fun a => do
          let body ← whnfR (b.instantiate1 a)
          unless body.isAppOfArity ``Exists 2 do return none
          unless (← whnfR body.appFn!.appArg!).isConstOf ``Nat do return none
          let qfun ← mkLambdaFVars #[a] body.appArg!
          -- `Q A X := (fun A => fun X => …) A X`
          let Q ← withLocalDeclD `A natT fun A => withLocalDeclD `X natT fun X => do
            mkLambdaFVars #[A, X] ((qfun.beta #[A]).beta #[X])
          let atTop ← mkAppOptM ``Filter.atTop #[natT, none]
          let freq ← withLocalDeclD `A natT fun A => do
            let pred ← withLocalDeclD `X natT fun X => do mkLambdaFVars #[X] (Q.beta #[A, X])
            mkForallFVars #[A] (← mkAppM ``Filter.Frequently #[pred, atTop])
          return some (Q, freq)
        if let some (Q, freq) := cof? then
          if let some (C', pf) ← abduceProp R fuel locals bound fv freq then
            R.note "cofinal"
            -- `pf : C' → freq`, then the lemma gives `C`
            let proof ← withLocalDeclD `h C' fun h => do
              let lem ← mkAppOptM ``forall_exists_of_forall_frequently #[Q, mkApp pf h]
              mkLambdaFVars #[h] lem
            return some (C', proof)
      withLocalDecl n bi d fun x => do
        let isH ← isProp d
        let derived ← if isH then expandFact R.unfoldOk 16 x else pure #[]
        let locals := if isH then locals ++ derived ++ #[x] else locals
        let bound := if isH then bound else bound.push x
        let some (B', pf) ← abduceProp R fuel locals bound fv (b.instantiate1 x) | return none
        if B'.isConstOf ``True || (!isH && !B'.containsFVar x.fvarId!) then
          let proof ← withLocalDeclD `h B' fun h => do
            mkLambdaFVars #[h] (← mkLambdaFVars #[x] (mkApp pf h))
          return some (B', proof)
        if !isH then
          if let .forallE _ d' b' _ := B' then
            if (← isProp d') && !b'.hasLooseBVars && !b'.containsFVar x.fvarId! then
              let proof ← withLocalDeclD `h b' fun h => do
                let const ← withLocalDeclD `hx d' fun hx => mkLambdaFVars #[hx] h
                mkLambdaFVars #[h] (← mkLambdaFVars #[x] (mkApp pf const))
              return some (b', proof)
        let C' ← mkForallFVars #[x] B'
        let proof ← withLocalDeclD `h C' fun h => do
          mkLambdaFVars #[h] (← mkLambdaFVars #[x] (mkApp pf (mkApp h x)))
        return some (C', proof)
    | _ =>
      if C.isAppOfArity ``And 2 then
        let A := C.appFn!.appArg!
        let B := C.appArg!
        let ra ← abduceProp R fuel locals bound fv A
        let rb ← abduceProp R fuel locals bound fv B
        if ra.isNone && rb.isNone then return none
        let (A', pa) ← match ra with
          | some r => pure r
          | none => do pure (A, ← idProof A)
        let (B', pb) ← match rb with
          | some r => pure r
          | none => do pure (B, ← idProof B)
        let aTrue := A'.isConstOf ``True
        let bTrue := B'.isConstOf ``True
        let C' := if aTrue && bTrue then Lean.mkConst ``True
          else if aTrue then B' else if bTrue then A' else mkApp2 (Lean.mkConst ``And) A' B'
        let proof ← withLocalDeclD `h C' fun h => do
          let ha ← if aTrue then pure (Lean.mkConst ``True.intro)
            else if bTrue then pure h else mkAppM ``And.left #[h]
          let hb ← if bTrue then pure (Lean.mkConst ``True.intro)
            else if aTrue then pure h else mkAppM ``And.right #[h]
          mkLambdaFVars #[h] (← mkAppM ``And.intro #[mkApp pa ha, mkApp pb hb])
        return some (C', proof)
      if C.isAppOfArity ``Exists 2 then
        let α := C.appFn!.appArg!
        let P := C.appArg!
        -- proposed witnesses in rank order, keeping the one leaving the fewest clauses; the scan
        -- stops at a witness leaving none, at one leaving at most one once three have been
        -- tried, and when the evaluations allowed for the statement run out
        let mut best : Option (Expr × Expr × Nat) := none
        let mut tried := 0
        for t in ← R.witnesses fv α do
          if let some b := best then
            if b.2.2 == 0 || (b.2.2 ≤ 1 && tried ≥ 3) then break
          if let some r := R.evals then
            let left ← r.get
            if left == 0 then break
            r.set (left - 1)
          tried := tried + 1
          let tw ← IO.monoMsNow
          R.say s!"[witness] trying {← ppExpr t}"
          let s ← saveState
          let r? ← try abduceProp R fuel locals bound fv (P.beta #[t]) catch _ => pure none
          R.say s!"[witness] {if r?.isSome then "restated" else "nothing"} in {(← IO.monoMsNow) - tw} ms"
          match r? with
          | some (P', pf) =>
            if R.vacuityGuard && (← refutedInScope locals P') then
              -- this witness asks for the impossible
              R.note "vacuity_refused"
            else
              let score := clauseScore 64 P'
              R.say s!"[witness] score {score}"
              if best.all (fun b => score < b.2.2) then
                let proof ← withLocalDeclD `h P' fun h => do
                  mkLambdaFVars #[h] (← mkAppOptM ``Exists.intro #[α, P, t, mkApp pf h])
                best := some (← instantiateMVars P', ← instantiateMVars proof, score)
          | none => pure ()
          s.restore
        if let some (P', proof, _) := best then
          R.note "witness"
          return some (P', proof)
        return ← withLocalDeclD `w α fun w => do
          let some (P', pf) ← abduceProp R fuel locals bound fv (P.beta #[w]) | return none
          if R.vacuityGuard && (← refutedInScope locals P') then
            R.note "vacuity_refused"
            return none
          let impl ← mkLambdaFVars #[w] pf
          let C' ← mkAppM ``Exists #[← mkLambdaFVars #[w] P']
          if P'.isConstOf ``True then
            -- `∃ w, True` holds when the type is inhabited: the statement is given
            if let some ex ← proveByTactic C' "exact ⟨Classical.ofNonempty, trivial⟩" then
              let proof ← withLocalDeclD `h (Lean.mkConst ``True) fun h => do
                mkLambdaFVars #[h] (← mkAppM ``Exists.imp #[impl, ex])
              return some (Lean.mkConst ``True, proof)
          let proof ← withLocalDeclD `h C' fun h => do
            mkLambdaFVars #[h] (← mkAppM ``Exists.imp #[impl, h])
          return some (C', proof)
      if C.isAppOfArity ``Filter.Frequently 3 || C.isAppOfArity ``Filter.Eventually 3 then
        let α := C.getArg! 0
        let P := C.getArg! 1
        let f := C.getArg! 2
        let freq := C.isAppOfArity ``Filter.Frequently 3
        return ← withLocalDeclD `X α fun X => do
          let body := P.beta #[X]
          let evs0 ← R.eventual locals body X f
          -- over `atTop`, a clause `t < X` or `t ≤ X` holds for all large `X`
          let bounds ← if R.eventualBounds then atTopBounds body X f else pure #[]
          let evs := evs0 ++ bounds.filter fun p => !evs0.any (·.2 == p.2)
          let decls := (Array.range evs.size).map fun i => (Name.mkSimple s!"hev{i}", evs[i]!.2)
          withLocalDeclsDND decls fun hs => do
            let mut locals' := locals
            for h in hs do
              locals' := locals' ++ (← expandFact R.unfoldOk 16 h) ++ #[h]
            let some (P', pf) ← abduceProp R fuel locals' bound (some (X, f)) body | return none
            if (hs.extract evs0.size hs.size).any (fun h => pf.containsFVar h.fvarId!) then
              R.note "eventual_bound"
            -- a body the facts at `X` refute holds at no large `X`
            if R.vacuityGuard && (← refutedInScope locals' P') then
              R.note "vacuity_refused"
              return none
            -- `pf : P' X → P X` may use the eventual facts `hs` at `X`
            let pred ← mkLambdaFVars #[X] P'
            let C' ← mkAppM (if freq then ``Filter.Frequently else ``Filter.Eventually) #[pred, f]
            let proof ← if hs.isEmpty then do
                let impl ← mkLambdaFVars #[X] pf
                withLocalDeclD `h C' fun h => do
                  mkLambdaFVars #[h] (← mkAppM (if freq then ``Filter.Frequently.mono
                    else ``Filter.Eventually.mono) #[h, impl])
              else do
                -- all eventual facts together, and the pointwise step from `P' X ∧ facts` to `P X`
                let mut eAll := evs.back!.1
                for i in (List.range (evs.size - 1)).reverse do
                  eAll ← mkAppM ``Filter.Eventually.and #[evs[i]!.1, eAll]
                let lam ← mkLambdaFVars (#[X] ++ hs) pf
                let factsAt (Y : Expr) : Expr := Id.run do
                  let mut acc := evs.back!.2.replaceFVar X Y
                  for i in (List.range (evs.size - 1)).reverse do
                    acc := mkApp2 (Lean.mkConst ``And) (evs[i]!.2.replaceFVar X Y) acc
                  return acc
                let impl ← withLocalDeclD `Y α fun Y => do
                  let pair := mkApp2 (Lean.mkConst ``And) (P'.replaceFVar X Y) (factsAt Y)
                  withLocalDeclD `hp pair fun hp => do
                    let hP' ← mkAppM ``And.left #[hp]
                    let mut rest ← mkAppM ``And.right #[hp]
                    let mut args : Array Expr := #[Y]
                    for i in [0:evs.size] do
                      if i + 1 == evs.size then args := args.push rest
                      else
                        args := args.push (← mkAppM ``And.left #[rest])
                        rest ← mkAppM ``And.right #[rest]
                    mkLambdaFVars #[Y, hp] (mkApp (mkAppN lam args).headBeta hP')
                withLocalDeclD `h C' fun h => do
                  let both ← mkAppM (if freq then ``Filter.Frequently.and_eventually
                    else ``Filter.Eventually.and) #[h, eAll]
                  mkLambdaFVars #[h] (← mkAppM (if freq then ``Filter.Frequently.mono
                    else ``Filter.Eventually.mono) #[both, impl])
            if P'.isConstOf ``True then
              -- `∃ᶠ X, True` (over a proper filter) and `∀ᶠ X, True` hold: the statement is given
              let tac := if freq then "exact Filter.Frequently.of_forall (fun _ => trivial)"
                else "exact Filter.Eventually.of_forall (fun _ => trivial)"
              if let some pC' ← proveByTactic C' tac then
                R.note "given_through_filter"
                let given ← withLocalDeclD `h (Lean.mkConst ``True) fun h => do
                  mkLambdaFVars #[h] (mkApp proof pC')
                return some (Lean.mkConst ``True, given)
            return some (C', proof)
      if (← comparison? C).isSome then
        return ← abduceLeaf R locals bound C
      -- membership or nonemptiness read as comparisons
      match ← comparisonForm R.unfoldOk C with
      | some (C₁, eq) =>
        if C₁ == C || (← comparison? C₁).isNone && !C₁.isAppOfArity ``And 2 then return none
        let some (C', pf) ← abduceProp R fuel locals bound fv C₁ | return none
        let proof ← withLocalDeclD `h C' fun h => do
          mkLambdaFVars #[h] (← mkEqMPR eq (mkApp pf h))
        return some (C', proof)
      | none =>
        -- a named predicate of the corpus is read through its definition, one step at a time;
        -- `C'` implies the unfolded body, which is `C` up to definitional unfolding
        unless R.unfoldHeads do return none
        let .const c _ := C.getAppFn | return none
        unless R.unfoldOk c do return none
        let some C₁ ← (try unfoldDefinition? C catch _ => pure none) | return none
        let C₁ ← instantiateMVars C₁.headBeta
        if C₁ == C then return none
        let some (C', pf) ← abduceProp R fuel locals bound fv C₁ | return none
        R.note "unfolded"
        let proof ← withLocalDeclD `h C' fun h => do
          mkLambdaFVars #[h] (← mkExpectedTypeHint (mkApp pf h) C)
        return some (C', proof)

/-- One hypothesis of a theorem changed by `restateScoped`: its position in the original
telescope and its binder name; the hypothesis `H` and what replaces it `R` (`True` when the facts
give it), each closed over the binders before it that it mentions; the contract
`∀ (binders), R → H` with its proof; whether all three are closed as they stand (no earlier
binder mentioned, no hypothesis in scope used); whether `H → R` was also proved in scope (the
restatement asks no more than the hypothesis; otherwise it is only sufficient); with `baseline`,
whether standard automation proves `H` itself in scope; what the search did, and the corpus
theorems whose readings entered an elimination. -/
structure SlotChange where
  index : Nat
  binder : Name
  hyp : Expr
  residual : Expr
  contract : Expr
  proof : Expr
  given : Bool
  closed : Bool
  weaker : Bool
  baseline : Bool := false
  notes : Array String
  facts : Array Name

/-- A theorem with its hypotheses restated: the new statement and its proof from the original,
the numbers of hypotheses dropped and restated, each change, and the restatements refused
(because the hypotheses before them refute them, or because they mention a variable out of
scope). -/
structure Restated where
  type : Expr := Lean.mkConst ``True
  value : Expr := Lean.mkConst ``True.intro
  dropped : Nat := 0
  restated : Nat := 0
  changes : Array SlotChange := #[]
  vacuous : Nat := 0
  leaked : Nat := 0

/-- The hypotheses of the theorem `thm` restated by `abduceProp`, one binder at a time: a
hypothesis the facts give is dropped, another is replaced by its restatement. Only hypotheses
that no later binder and not the conclusion depend on are touched. When a hypothesis is
restated, the variables in scope are exactly the binders before it (restated ones in their new
form): the original telescope is never opened, so no restatement can mention a later binder or
an earlier one's original version. `none` when nothing changes. -/
def restateScoped (R : Retrieval) (thm : Name) (depth : Nat := 64) :
    TermElabM (Option Restated) := do
  let ci ← getConstInfo thm
  let lvls := ci.levelParams.map Level.param
  let rec go (ty : Expr) (pre args : Array Expr) (acc : Restated) (j fuel : Nat) :
      TermElabM (Option Restated) := do
    match fuel with
    | 0 => return none
    | fuel + 1 =>
    let ty ← instantiateMVars ty
    -- as `forallTelescopeReducing`: unfold to expose a binder, else keep the statement as it is
    -- a negation (`Irrational x`, say) exposes `P → False`: that is the conclusion, not a hypothesis
    let ty ← if ty.isForall then pure ty else do
      let ty' ← whnf ty
      if !ty'.isForall then pure ty
      else if ← forallTelescopeReducing ty' fun _ e => return e.isConstOf ``False then pure ty
      else pure ty'
    match ty with
    | .forallE n d b bi =>
      let keep (acc : Restated) : TermElabM (Option Restated) :=
        withLocalDecl n bi d fun y =>
          go (b.instantiate1 y) (pre.push y) (args.push y) acc (j + 1) fuel
      unless (← isProp d) && !b.hasLooseBVars do return ← keep acc
      let localFacts ← pre.filterM fun y => do isProp (← inferType y)
      R.resetEvals
      R.resetNotes
      let some (d', pf) ← abduceProp R depth localFacts #[] none d | return ← keep acc
      let d' ← instantiateMVars d'
      let pf ← instantiateMVars pf
      let (notes, used) ← R.readNotes
      let ids := pre.map (·.fvarId!)
      let outOfScope (e : Expr) : Bool := e.hasAnyFVar fun v => !ids.contains v
      if d'.hasMVar || pf.hasMVar || outOfScope d' || outOfScope pf then
        return ← keep { acc with leaked := acc.leaked + 1 }
      let given := d'.isConstOf ``True
      if !given && R.vacuityGuard && (← refutedInScope localFacts d') then
        return ← keep { acc with vacuous := acc.vacuous + 1 }
      -- does the hypothesis itself give the restatement, with the binders before it?
      let weaker ← if given then pure true else do
        let t ← mkArrow d d'
        pure ((← proveByTactic t "(intro h; first | assumption | omega | linarith)" 3000).isSome ||
          (← proveByTactic t "(intro h; simp_all)" 3000).isSome)
      -- the comparison: does standard automation prove the hypothesis itself in scope?
      let baseline ← if R.baseline then
          pure (← proveByTactic d
            "(first | assumption | omega | linarith | positivity | simp_all | aesop)" 3000).isSome
        else pure false
      let needH ← neededBinders pre #[d]
      let needR ← neededBinders pre #[d']
      let needC ← neededBinders pre #[d, d', pf]
      let change : SlotChange := {
        index := j, binder := n, hyp := ← mkForallFVars needH d,
        residual := ← mkForallFVars needR d',
        contract := ← mkForallFVars needC (← mkArrow d' d),
        proof := ← mkLambdaFVars needC pf,
        given, closed := needC.isEmpty, weaker, baseline, notes, facts := used }
      if given then
        let arg := mkApp pf (Lean.mkConst ``True.intro)
        go (b.instantiate1 arg) pre (args.push arg)
          { acc with dropped := acc.dropped + 1, changes := acc.changes.push change } (j + 1) fuel
      else
        withLocalDecl n bi d' fun y => do
          let arg := mkApp pf y
          go (b.instantiate1 arg) (pre.push y) (args.push arg)
            { acc with restated := acc.restated + 1, changes := acc.changes.push change }
            (j + 1) fuel
    | body =>
      if acc.dropped + acc.restated == 0 then return none
      let type ← mkForallFVars pre body
      let value ← mkLambdaFVars pre (mkAppN (Lean.mkConst thm lvls) args)
      return some { acc with type, value }
  go ci.type #[] #[] {} 0 4096

/-- `restateScoped`, as the statement, its proof and the numbers dropped and restated. -/
def restateAntecedents (R : Retrieval) (thm : Name) :
    TermElabM (Option (Expr × Expr × Nat × Nat)) := do
  let some r ← restateScoped R thm | return none
  return some (r.type, r.value, r.dropped, r.restated)

/-- Every reading of an index, once. -/
def allRefs (m : Std.HashMap Name (Array Ref)) : Array Ref := Id.run do
  let mut out : Array Ref := #[]
  for (_, rs) in m.toList do
    for r in rs do
      unless out.contains r do out := out.push r
  return out

/-- The retrieval over a fact index, excluding the theorems `exclude`: the readings sharing the
most corpus constants with the statement. Witnesses are not proposed: over the whole corpus
there are too many candidates. -/
def corpusRetrieval (facts : Facts) (unfoldOk : Name → Bool) (exclude : Array Name) :
    Retrieval where
  unfoldOk := unfoldOk
  pointwise := fun locals C =>
    retrieveFacts (rankedRefs facts.pointwise (corpusConsts unfoldOk C) exclude 16) locals C
  eventual := fun locals B X f =>
    retrieveEventual (rankedRefs facts.eventual (corpusConsts unfoldOk B) exclude 16) locals B X f


/-- The retrieval over every reading of a supplier set; witnesses are proposed from them unless
`proposeWitnesses` is off (the export's corpus retrieval proposes none, so its restatements
replay with it off). -/
def supplierRetrieval (suppliers : Array Name) (unfoldOk : Name → Bool)
    (proposeWitnesses : Bool := true) : MetaM Retrieval := do
  let facts ← factsOf suppliers unfoldOk
  let pw := allRefs facts.pointwise
  let ev := allRefs facts.eventual
  let evals ← IO.mkRef 32
  return {
    unfoldOk
    pointwise := fun locals C => retrieveFacts pw locals C
    eventual := fun locals B X f => retrieveEventual ev locals B X f
    witnesses := if proposeWitnesses then fun fv α => witnessCandidates facts unfoldOk fv α
      else fun _ _ => pure #[]
    evals := some evals }

end ErdosProblems.ArgumentGraph.Abduce

/-! ## The commands -/

namespace ErdosProblems.ArgumentGraph.Abduce

open Lean Meta Elab Command

/- Every atom below except `restate`, `restate_integral` and `expecting` is already a keyword of
Lean. -/
syntax (name := restateCmd)
  "restate " ident " for " ident " using " ident+ (" expecting " str)? : command
syntax (name := restateFromCmd)
  "restate " ident " for " ident " from " ident* (" expecting " str)? : command
syntax (name := restateIntegralCmd)
  "restate_integral " ident " for " ident " using " ident+ : command

/-- A restatement that could not be added: an error under `argumentGraph.strict` (the option
of the generated argument-frontier modules, read by name), a warning otherwise, as for the
`derive_*` commands; a kernel probe runs every command and reads what each added. -/
def reportRestateFailure (msg : MessageData) : TermElabM Unit := do
  if (← getOptions).getBool `argumentGraph.strict false then logError msg else logWarning msg

/-- Add `name : type` after a kernel check, and log `added name : statement` on one line (the
line the argument frontier's verdicts read). A theorem already named `name` with the same
statement (the command ran before in this environment) is kept; one with another statement is
a failure. -/
def addRestated (name : Name) (levelParams : List Name) (type value : Expr) : TermElabM Bool := do
  if let some ci := (← getEnv).find? name then
    if statementKey ci.type == statementKey type then return true
    reportRestateFailure m!"restate: {name} already exists with a different statement"
    return false
  try
    addDecl (.thmDecl { name, levelParams, type, value })
  catch e =>
    reportRestateFailure m!"restate: the kernel rejected {name}: {e.toMessageData}"
    return false
  let line := (toString (← withOptions (fun o => o.setBool `pp.proofs false) (ppExpr type))).replace "\n" " "
  logInfo m!"added {name} : {line}"
  return true

/-- Restate `target` with the facts of `suppliers` and add the result as `name`: for a theorem,
each hypothesis the facts give is dropped and each other one is replaced by what it still needs
in the quantities no fact controls; for a proposition (a definition of type `Prop`),
`name : D' → D`. With `expecting k`, the restatement must have the key `k` (the export's key),
so a replay that finds another restatement adds nothing. The kernel checks the declaration. -/
def elabRestateWith (nameStx targetStx : Syntax) (supplierStx : Array Syntax)
    (proposeWitnesses integral : Bool) (expectedKey : Option String) : CommandElabM Unit :=
  liftTermElabM do
    let name := (← getCurrNamespace) ++ nameStx.getId
    let target ← realizeGlobalConstNoOverloadWithInfo targetStx
    let suppliers ← supplierStx.mapM fun s => realizeGlobalConstNoOverloadWithInfo s
    if suppliers.contains target then
      reportRestateFailure m!"restate: {target} cannot supply itself"
      return
    let unfoldOk := fun (n : Name) => [`ErdosProblems, `Erdos249257].any (·.isPrefixOf n)
    let R ← supplierRetrieval suppliers unfoldOk proposeWitnesses
    let R := { R with integerRounding := integral }
    let keyOk (ty : Expr) : TermElabM Bool := do
      let some k := expectedKey | return true
      let k' := statementKey ty
      if k' == k then return true
      reportRestateFailure m!"restate {target}: the restatement has key {k'}, expected {k}:\n  {ty}"
      return false
    let ci ← getConstInfo target
    match ci with
    | .thmInfo _ =>
      let some r ← restateScoped R target
        | reportRestateFailure m!"restate {target}: the facts of {suppliers.toList} change no hypothesis"
      unless ← keyOk r.type do return
      discard <| addRestated name ci.levelParams r.type r.value
    | .defnInfo d =>
      unless d.type.isProp do
        reportRestateFailure m!"restate: {target} is not a proposition"
        return
      R.resetEvals
      let some (C', pf) ← abduceProp R 64 #[] #[] none d.value
        | reportRestateFailure m!"restate {target}: the facts of {suppliers.toList} change nothing"
      let ty ← mkArrow C' (Lean.mkConst target (d.levelParams.map Level.param))
      unless ← keyOk ty do return
      discard <| addRestated name d.levelParams ty pf
    | _ => reportRestateFailure m!"restate: {target} is neither a theorem nor a proposition"

/-- The key named by an optional ` expecting "k"`. -/
def expectingKey (stx : Syntax) : Option String :=
  if stx.getNumArgs == 0 then none else stx[1].isStrLit?

/-- `restate N for D using s₁ … sₙ` restates `D` with the facts of the theorems `s₁ … sₙ`, with
witnesses proposed from them. The restatement is recomputed whenever the module is built. -/
@[command_elab restateCmd] def elabRestate : CommandElab := fun stx =>
  elabRestateWith stx[1] stx[3] stx[5].getArgs true false (expectingKey stx[6])

/-- `restate N for D from s₁ … sₙ` restates `D` with the facts of `s₁ … sₙ` only, proposing no
witnesses: the replay of a restatement the export found. -/
@[command_elab restateFromCmd] def elabRestateFrom : CommandElab := fun stx =>
  elabRestateWith stx[1] stx[3] stx[5].getArgs false false (expectingKey stx[6])

/-- `restate_integral N for D using s₁ … sₙ` is `restate` with the counts' lower bounds rounded
to integers before a count is eliminated. -/
@[command_elab restateIntegralCmd] def elabRestateIntegral : CommandElab := fun stx =>
  elabRestateWith stx[1] stx[3] stx[5].getArgs true true none

end ErdosProblems.ArgumentGraph.Abduce

/-!
# Abduction export

Two passes over the corpus libraries, both with the comparison readings of every corpus theorem
as facts (`AbduceCorpus`), writing JSON Lines rows next to the argument-continuation export and
keyed exactly as that export keys statements (`keyOf` below is a copy of it).

**Closed hypotheses.** For every hypothesis that mentions no earlier binder, what it still needs
once the corpus's facts are used (`abduceProp`). A statement is tried once however many theorems
assume it.

* `abduction` with `given: true`: a combination of corpus facts gives the hypothesis; the kernel
  has checked a proof of it;
* `abduction` with a `residual`: the restatement in the quantities no fact controls, with the
  kernel-checked proof that it implies the hypothesis, and a `statement` row for the residual so
  the graph can search it.

**Whole theorems.** Every theorem restated hypothesis by hypothesis in its own scope
(`restateScoped`), parameterised hypotheses included; the theorems the papers cite first
(`PLECTIS_ABDUCTION_PRIORITY`), then the rest while the budget lasts. A `restatement` row gives
the restated theorem (kernel-checked), and for each hypothesis changed its closed contract
`∀ (binders it needs), R → H`, whether the facts give it, whether `H → R` also holds in scope,
what the search did (`notes`) and the corpus theorems whose readings entered an elimination
(`facts`), which is what `restate … from …` replays. A restatement that the hypotheses before it
refute, or that mentions a variable out of scope, is refused and counted.

A `meta` record comes first and a `summary` record last (fields prefixed `abduction_`), so the
stream combines with the main export. The facts named in a closed row are the corpus theorems in
the proof. `scripts/build_argument_continuations.py` reads the rows with the main export
(`--export <abductions> --export <main>`, the main export last): a given statement is supplied
by an `abduction` reduction with no residual, a restated one reduces to its residual, and the
`restatement` rows are counted and kept. Environment variables:

* `PLECTIS_ABDUCTION_EXPORT_FILE`: output path (stdout if unset);
* `PLECTIS_ABDUCTION_SECONDS`: wall-clock budget of both passes (default 1800);
* `PLECTIS_ABDUCTION_CLOSED_SECONDS`: the part of it the closed pass may use (default 600);
* `PLECTIS_ABDUCTION_ROOTS`: module roots (default `Erdos249257,ErdosProblems`);
* `PLECTIS_ABDUCTION_PRIORITY`: a file of theorem names, one per line, restated first;
* `PLECTIS_ABDUCTION_THEOREMS`: `priority` to restate only those (default `all`).
-/

open Lean Meta Elab Term
open ErdosProblems.ArgumentGraph.Residualise ErdosProblems.ArgumentGraph.Abduce

namespace AbductionExport

/-! ## Keys, as in `export_argument_continuations.lean` -/

private def hex16 (n : Nat) : String :=
  let digits := Nat.toDigits 16 n
  String.ofList (List.replicate (16 - digits.length) '0' ++ digits)

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

def emit (stream : IO.FS.Stream) (j : Json) : IO Unit := do
  stream.putStrLn j.compress
  stream.flush

/-- Whether the kernel accepts `value : type` as a theorem (in a scratch environment). -/
def kernelAccepts (type value : Expr) (levelParams : List Name) : MetaM Bool := do
  if type.hasFVar || type.hasMVar || value.hasFVar || value.hasMVar then return false
  let decl := Declaration.thmDecl { name := `_abduction_check, levelParams, type, value }
  match Kernel.Environment.addDeclCore (← getEnv).toKernelEnv 0 decl none with
  | .ok _ => return true
  | .error _ => return false

/-- The corpus theorems a proof term names, other than `exclude` and the engine's own lemmas. -/
def factsNamed (unfoldOk : Name → Bool) (exclude : Name) (proof : Expr) : MetaM (Array String) := do
  let env ← getEnv
  return (proof.getUsedConstants.filter fun c =>
      c != exclude && unfoldOk c && !(`ErdosProblems.ArgumentGraph.Abduce).isPrefixOf c &&
        (match env.find? c with | some (.thmInfo _) => true | _ => false))
    |>.map toString

/-- A fresh record of what the search did. -/
def instrumented (R : Retrieval) : IO Retrieval := do
  return { R with notes := some (← IO.mkRef #[]), used := some (← IO.mkRef #[]), baseline := true }

structure Counts where
  tried : Nat := 0
  given : Nat := 0
  restated : Nat := 0
  rejected : Nat := 0
  exhausted : Nat := 0
  vacuous : Nat := 0
  errors : Nat := 0

/-- The theorems to restate as a whole: the priority names that exist first, then (unless only the
priority names are asked for) every other theorem of the roots. -/
def theoremOrder (roots : Array Name) (priority : Array Name) (onlyPriority : Bool) :
    MetaM (Array Name × Nat) := do
  let env ← getEnv
  let mut out : Array Name := #[]
  let mut inPriority := 0
  for n in priority do
    if let some (.thmInfo _) := env.find? n then
      unless out.contains n do
        out := out.push n
        inPriority := inPriority + 1
  if onlyPriority then return (out, inPriority)
  let seen : Std.HashSet Name := out.foldl (·.insert ·) {}
  for modName in env.header.moduleNames, data in env.header.moduleData do
    unless roots.any (·.isPrefixOf modName) do continue
    for thm in data.constNames do
      if thm.isInternal || seen.contains thm then continue
      let some (.thmInfo _) := env.find? thm | continue
      out := out.push thm
  return (out, inPriority)

/-- What one export does. -/
structure Config where
  path : Option String := none
  seconds : Nat := 1800
  closedSeconds : Nat := 600
  roots : Array Name := #[`Erdos249257, `ErdosProblems]
  priority : Array Name := #[]
  onlyPriority : Bool := false

/-- The configuration the environment variables give. -/
def configFromEnv : IO Config := do
  let roots : Array Name := match ← IO.getEnv "PLECTIS_ABDUCTION_ROOTS" with
    | some raw => ((raw.splitOn ",").filter (· ≠ "")).toArray.map String.toName
    | none => #[`Erdos249257, `ErdosProblems]
  let priority : Array Name ← match ← IO.getEnv "PLECTIS_ABDUCTION_PRIORITY" with
    | some p => do
        let text ← IO.FS.readFile p
        let names := ((text.splitOn "\n").map String.trim).filter (· ≠ "")
        pure (names.toArray.map String.toName)
    | none => pure #[]
  return {
    path := ← IO.getEnv "PLECTIS_ABDUCTION_EXPORT_FILE"
    seconds := ((← IO.getEnv "PLECTIS_ABDUCTION_SECONDS").bind String.toNat?).getD 1800
    closedSeconds := ((← IO.getEnv "PLECTIS_ABDUCTION_CLOSED_SECONDS").bind String.toNat?).getD 600
    roots, priority
    onlyPriority := (← IO.getEnv "PLECTIS_ABDUCTION_THEOREMS") == some "priority" }

def exportWith (cfg : Config) : TermElabM Unit := do
  let path? := cfg.path
  let seconds := cfg.seconds
  let closedSeconds := cfg.closedSeconds
  let roots := cfg.roots
  let priority := cfg.priority
  let onlyPriority := cfg.onlyPriority
  let stream ← match path? with
    | some p => IO.FS.Stream.ofHandle <$> IO.FS.Handle.mk p .write
    | none => IO.getStdout
  let unfoldOk := fun (n : Name) => roots.any (·.isPrefixOf n)
  -- the builder reads a stream that opens with this meta record and has a summary record;
  -- give it before the main export (`--export abductions --export main`) so that the main
  -- export's meta and summary are the ones kept
  emit stream <| Json.mkObj [
    ("record", "meta"), ("schema", "plectis-argument-continuation-export/1"),
    ("stream", "abductions"), ("abduction_engine", "scoped/2"),
    ("lean_version", toJson Lean.versionString),
    ("imports", toJson ((← getEnv).header.moduleNames.map toString))]
  let t0 ← IO.monoMsNow
  let (facts, nFacts) ← buildFactIndex roots unfoldOk
  let indexMs := (← IO.monoMsNow) - t0
  let env ← getEnv
  let mut seen : Std.HashSet String := {}
  let mut c : Counts := {}
  let mut truncated := false
  /- Pass 1: closed hypotheses. -/
  for modName in env.header.moduleNames, data in env.header.moduleData do
    unless roots.any (·.isPrefixOf modName) do continue
    for thm in data.constNames do
      if thm.isInternal then continue
      let some (.thmInfo info) := env.find? thm | continue
      if (← IO.monoMsNow) - t0 > closedSeconds * 1000 then
        truncated := true
        break
      let hyps ← forallTelescopeReducing info.type fun xs _ => do
        let mut out : Array Expr := #[]
        for x in xs do
          let d ← inferType x
          if (← isProp d) && !d.hasFVar && !d.hasMVar then out := out.push d
        return out
      for H in hyps do
        let key := keyOf H
        if seen.contains key then continue
        seen := seen.insert key
        c := { c with tried := c.tried + 1 }
        let R ← instrumented (corpusRetrieval facts unfoldOk #[thm])
        -- each statement gets the default declaration budget; running out is counted apart
        -- from finding nothing, and is never read as the absence of a restatement
        let res ← ErdosProblems.ArgumentGraph.Residualise.budgetedTerm 200000
          (try abduceProp R 64 #[] #[] none H catch _ => pure none)
        let (notes, _) ← R.readNotes
        if notes.contains "vacuity_refused" then c := { c with vacuous := c.vacuous + 1 }
        if res.isNone then c := { c with exhausted := c.exhausted + 1 }
        let some (H', pf) := res.join | continue
        let lps := info.levelParams
        if H'.isConstOf ``True then
          let value := mkApp pf (mkConst ``True.intro)
          if ← kernelAccepts H value lps then
            c := { c with given := c.given + 1 }
            emit stream <| Json.mkObj [
              ("record", "abduction"), ("statement", toJson key), ("given", toJson true),
              ("theorem", toJson thm.toString), ("type", toJson (← render H)),
              ("facts", toJson (← factsNamed unfoldOk thm value)), ("notes", toJson notes),
              ("kernel_checked", toJson true)]
          else c := { c with rejected := c.rejected + 1 }
        else
          let ty ← mkArrow H' H
          if ← kernelAccepts ty pf lps then
            c := { c with restated := c.restated + 1 }
            let rkey := keyOf H'
            emit stream <| Json.mkObj [
              ("record", "statement"), ("key", toJson rkey), ("origin", "abduction"),
              ("type", toJson (← render H'))]
            emit stream <| Json.mkObj [
              ("record", "abduction"), ("statement", toJson key), ("given", toJson false),
              ("residual", toJson rkey), ("theorem", toJson thm.toString),
              ("type", toJson (← render H)), ("residual_type", toJson (← render H')),
              ("facts", toJson (← factsNamed unfoldOk thm pf)), ("notes", toJson notes),
              ("kernel_checked", toJson true)]
          else c := { c with rejected := c.rejected + 1 }
    if truncated then break
  let closedMs := (← IO.monoMsNow) - t0
  /- Pass 2: whole theorems, restated in scope. -/
  let (order, nPriority) ← theoremOrder roots priority onlyPriority
  let prioritySet : Std.HashSet Name := priority.foldl (·.insert ·) {}
  let mut w : Counts := {}
  let mut wTheorems := 0
  let mut wUnchanged := 0
  let mut wLeaked := 0
  let mut wSlotsGiven := 0
  let mut wSlotsRestated := 0
  let mut wSlotsWeaker := 0
  let mut wSlotsBaseline := 0
  let mut wTruncated := false
  let mut wDone := 0
  for thm in order do
    if (← IO.monoMsNow) - t0 > seconds * 1000 then
      wTruncated := true
      break
    let some (.thmInfo info) := env.find? thm | continue
    wTheorems := wTheorems + 1
    let R ← instrumented (corpusRetrieval facts unfoldOk #[thm])
    let s ← IO.monoMsNow
    -- running out of budget (`none`), an error, no change and a restatement are four outcomes
    let res ← ErdosProblems.ArgumentGraph.Residualise.budgetedTerm 400000 (do
      try return Except.ok (← restateScoped R thm) catch _ => return Except.error ())
    let ms := (← IO.monoMsNow) - s
    wDone := wDone + 1
    -- one attempt row per visited theorem, so every outcome is attributable to a theorem and the
    -- outcomes of a set of theorems add up to the theorems visited
    let attempt := fun (outcome : String) => Json.mkObj [
      ("record", "restatement_attempt"), ("theorem", toJson thm.toString),
      ("priority", toJson (prioritySet.contains thm)), ("outcome", toJson outcome),
      ("elapsed_ms", toJson ms)]
    match res with
    | none =>
      w := { w with exhausted := w.exhausted + 1 }
      emit stream (attempt "budget")
    | some (.error _) =>
      w := { w with errors := w.errors + 1 }
      emit stream (attempt "error")
    | some (.ok none) =>
      wUnchanged := wUnchanged + 1
      emit stream (attempt "unchanged")
    | some (.ok (some r)) =>
      w := { w with vacuous := w.vacuous + r.vacuous }
      wLeaked := wLeaked + r.leaked
      unless ← kernelAccepts r.type r.value info.levelParams do
        w := { w with rejected := w.rejected + 1 }
        emit stream (attempt "rejected")
        continue
      emit stream (attempt "restated")
      w := { w with restated := w.restated + 1 }
      let mut slots : Array Json := #[]
      let mut replay : Array Name := #[]
      for ch in r.changes do
        if ch.given then wSlotsGiven := wSlotsGiven + 1 else wSlotsRestated := wSlotsRestated + 1
        if ch.weaker && !ch.given then wSlotsWeaker := wSlotsWeaker + 1
        if ch.baseline then wSlotsBaseline := wSlotsBaseline + 1
        for f in ch.facts do
          unless replay.contains f do replay := replay.push f
        let contractOk ← kernelAccepts ch.contract ch.proof info.levelParams
        slots := slots.push <| Json.mkObj [
          ("index", toJson ch.index), ("binder", toJson ch.binder.toString),
          ("hypothesis", toJson (← render ch.hyp)), ("hypothesis_key", toJson (keyOf ch.hyp)),
          ("residual", toJson (← render ch.residual)), ("residual_key", toJson (keyOf ch.residual)),
          ("contract_key", toJson (keyOf ch.contract)), ("contract_kernel_checked", toJson contractOk),
          ("given", toJson ch.given), ("weaker", toJson ch.weaker), ("closed", toJson ch.closed),
          ("baseline_closes", toJson ch.baseline),
          ("notes", toJson ch.notes), ("facts", toJson (ch.facts.map toString))]
        -- a closed contract is also a reduction between closed statements, as in pass 1
        if ch.closed && contractOk && !seen.contains (keyOf ch.hyp) then
          seen := seen.insert (keyOf ch.hyp)
          if ch.given then
            emit stream <| Json.mkObj [
              ("record", "abduction"), ("statement", toJson (keyOf ch.hyp)), ("given", toJson true),
              ("theorem", toJson thm.toString), ("type", toJson (← render ch.hyp)),
              ("facts", toJson (← factsNamed unfoldOk thm ch.proof)), ("notes", toJson ch.notes),
              ("kernel_checked", toJson true)]
          else
            emit stream <| Json.mkObj [
              ("record", "statement"), ("key", toJson (keyOf ch.residual)), ("origin", "abduction"),
              ("type", toJson (← render ch.residual))]
            emit stream <| Json.mkObj [
              ("record", "abduction"), ("statement", toJson (keyOf ch.hyp)), ("given", toJson false),
              ("residual", toJson (keyOf ch.residual)), ("theorem", toJson thm.toString),
              ("type", toJson (← render ch.hyp)), ("residual_type", toJson (← render ch.residual)),
              ("facts", toJson (← factsNamed unfoldOk thm ch.proof)), ("notes", toJson ch.notes),
              ("kernel_checked", toJson true)]
      emit stream <| Json.mkObj [
        ("record", "restatement"), ("theorem", toJson thm.toString),
        ("priority", toJson (prioritySet.contains thm)),
        ("theorem_key", toJson (keyOf info.type)), ("restated_key", toJson (keyOf r.type)),
        ("type", toJson (← render r.type)), ("dropped", toJson r.dropped),
        ("restated", toJson r.restated), ("vacuous", toJson r.vacuous), ("leaked", toJson r.leaked),
        ("replay_facts", toJson (replay.map toString)), ("elapsed_ms", toJson ms),
        ("slots", Json.arr slots), ("kernel_checked", toJson true)]
  emit stream <| Json.mkObj [
    ("record", "summary"), ("abduction_statements_tried", toJson c.tried),
    ("abduction_given", toJson c.given), ("abduction_restated", toJson c.restated),
    ("abduction_kernel_rejected", toJson c.rejected), ("abduction_budget_exhausted", toJson c.exhausted),
    ("abduction_vacuity_refused", toJson c.vacuous),
    ("abduction_fact_readings", toJson nFacts),
    ("abduction_index_ms", toJson indexMs),
    ("abduction_closed_elapsed_ms", toJson closedMs),
    ("abduction_truncated", toJson truncated),
    ("abduction_theorems_in_order", toJson order.size),
    ("abduction_priority_theorems", toJson nPriority),
    ("abduction_theorems_visited", toJson wDone),
    ("abduction_theorems_restated", toJson w.restated),
    ("abduction_theorems_unchanged", toJson wUnchanged),
    ("abduction_theorems_budget_exhausted", toJson w.exhausted),
    ("abduction_theorems_errors", toJson w.errors),
    ("abduction_theorems_kernel_rejected", toJson w.rejected),
    ("abduction_slots_given", toJson wSlotsGiven),
    ("abduction_slots_restated", toJson wSlotsRestated),
    ("abduction_slots_weaker", toJson wSlotsWeaker),
    ("abduction_slots_baseline_closes", toJson wSlotsBaseline),
    ("abduction_slots_vacuity_refused", toJson w.vacuous),
    ("abduction_slots_out_of_scope", toJson wLeaked),
    ("abduction_theorems_truncated", toJson wTruncated),
    ("abduction_elapsed_ms", toJson ((← IO.monoMsNow) - t0)),
    ("abduction_budget_seconds", toJson seconds)]
  stream.flush

def exportAll : TermElabM Unit := do
  exportWith (← configFromEnv)

end AbductionExport

/-! ## Probe R5B: the export over the roots, the paper-cited theorems first -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM (AbductionExport.exportWith
  { seconds := 1380, closedSeconds := 420, priority := (#["ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.le_of_lam_le", "ErdosProblems.Erdos1041.PaperCompleteR21.SeparationParent.separation_parent", "ErdosProblems.Erdos1041.PaperCompleteR21.cfaArity_length_le", "ErdosProblems.Erdos1041.PaperCompleteR21.discSep_cubic_six_fifths", "ErdosProblems.Erdos1041.PaperCompleteR21.discSep_uniform_radius", "ErdosProblems.Erdos1041.PaperCompleteR21.subcritical_perimeter_path_paper", "ErdosProblems.Erdos1041.PaperCompleteR21.Arity.arity_not_capacity", "ErdosProblems.Erdos1041.PaperCompleteR21.cfa_constant_factor_path", "ErdosProblems.Erdos1041.PaperCompleteR21.discSep_separation_short", "ErdosProblems.Erdos1041.PaperCompleteR21.scaledLowCriticalFiveHalves_of_lowCritical", "ErdosProblems.Erdos1041.PaperCompleteR21.scaledLowCritical_of_lowCritical", "ErdosProblems.Erdos1041.PaperCompleteR20.exists_two_nearest_roots_of_polynomial_critical", "ErdosProblems.Erdos1041.PaperCompleteR20.newton_real_value_whole", "ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chords_path", "ErdosProblems.Erdos1041.PaperCompleteR21.binomial_inner_chord_maximal", "ErdosProblems.Erdos1041.PaperCompleteR21.chebyshev_configuration_attains", "ErdosProblems.Erdos1041.PaperCompleteR21.collinear_erdos_1041", "ErdosProblems.Erdos1041.PaperCompleteR21.collinear_erdos_1041_monic", "ErdosProblems.Erdos1041.PaperCompleteR21.discSep_transport", "ErdosProblems.Erdos1041.PaperCompleteR21.primitive_quintic_two_tail_of_polynomial", "ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_equality_attained", "ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_root_diameter_monic", "ErdosProblems.Erdos1041.PaperCubicCompletion.cubic_paper_complete", "ErdosProblems.Erdos1041.PaperPrimitiveCompletionR10.complete_primitive_quintic", "ErdosProblems.Erdos1041.PaperTrinomial.complete_trinomial", "ErdosProblems.Erdos1041.PaperTrinomialWholeR21.all_degree_monic_trinomials_whole", "ErdosProblems.Erdos1041.exists_two_roots_dist_sum_le_two_mul_geomMean", "ErdosProblems.Erdos1041.translated_samePositiveRay_parameterization", "ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_measure_uniform", "ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_threshold", "ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_threshold_log", "ErdosProblems.Erdos1049.PaperCompleteR21.GeometricUniversality.geometric_universality", "ErdosProblems.Erdos1049.PaperCompleteR21.TailLattice.tail_prefix_lattice", "ErdosProblems.Erdos1049.PaperR7.endpoint_scalar_content_exclusion", "ErdosProblems.Erdos1049.PaperR7.height_and_hankel_deficits", "ErdosProblems.Erdos1049.PaperR7.rank_fortyone", "ErdosProblems.Erdos1049.PaperR7.scalar_margin", "ErdosProblems.Erdos1049.commonMultiplier_not_two_not_three_of_endpoint_units", "ErdosProblems.Erdos1049.exists_small_real_escape_of_conditional_multiplicity", "ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.oddPrimePower_supply", "ErdosProblems.Erdos243.PaperCompleteR21.exists_avoiding_in_window", "ErdosProblems.Erdos243.PaperCompleteR21.exists_multiplier_ge_four", "ErdosProblems.Erdos243.PaperCompleteR21.exists_slow_rise_avoiding_sequence", "ErdosProblems.Erdos243.PaperCompleteR21.maximal_gap_limsup_eq_inv_sigma", "ErdosProblems.Erdos243.PaperCompleteR21.unit_word_saturates_old_modulus", "ErdosProblems.Erdos243.PaperCompleteR11.primitive_zero_density_paper_multiplier_lemma", "ErdosProblems.Erdos243.PaperCompleteR21.cubic_profile_gcd_stabilisation_and_primitive_shape", "ErdosProblems.Erdos243.PaperCompleteR21.epoch_energy_named_crossing_set", "ErdosProblems.Erdos243.PaperCompleteR21.overlapDebt_dvd_gcd", "ErdosProblems.Erdos243.PaperCompleteR21.squareSpecialisation_holds", "ErdosProblems.Erdos243.PaperCompleteR21.sylvesterTail_shiftedCorrection", "ErdosProblems.Erdos243.PaperCompleteR21.transport_square_unconditional", "ErdosProblems.Erdos243.PaperCompleteR7.gcd_stabilises_and_reduces", "ErdosProblems.Erdos243.PaperCompleteR7.persistent_coprimality", "ErdosProblems.Erdos249.PaperCompleteR20.short_lcm_window_nondivisor", "ErdosProblems.Erdos249.PaperCompleteR21.complementDenominator_dvd_scalar", "ErdosProblems.Erdos249.PaperCompleteR21.complementSummand_low_double_echo", "ErdosProblems.Erdos249.PaperCompleteR21.divisorChannels_sum_eq", "ErdosProblems.Erdos249.PaperCompleteR21.dvd_pow_sub_one_iff_orderOf_dvd", "ErdosProblems.Erdos249.PaperCompleteR21.extremal_order_curvature_neg", "ErdosProblems.Erdos249.PaperCompleteR21.extremal_order_curvature_pos", "ErdosProblems.Erdos249.PaperCompleteR21.inversePhaseGauge_locks_row_and_preserves_minor", "ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_near_integer_base_powers", "ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_eval_two", "ErdosProblems.Erdos249.PaperCompleteR21.real_part_bound_of_norm_bound", "ErdosProblems.Erdos249.PaperCompleteR21.residueOffset_of_dvd", "ErdosProblems.Erdos249.PaperCompleteR21.twoAtom_strict_logConcave", "ErdosProblems.Erdos249.PaperCompleteR21.lambert_id_rung_transcendental", "ErdosProblems.Erdos249.PaperCompleteR21.prop_badcof", "Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_cone_nonintegrality_supply", "Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_diagonal_nonintegrality_supply", "Erdos249257.not_irrational_totientSeries_implies_mod_period_and_unbounded_rank", "ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_supply_irrational", "ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_flatness", "ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_fractional_parts", "ErdosProblems.Erdos249.PaperCompleteR21.exists_simultaneous_depth_of_irrational", "ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_accumulated_halfModulus_supply", "ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_diagonal_orbit_separation_supply", "ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_four_tail_supply", "ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_lower_escape_supply", "ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_modFour_pulse_supply", "ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_paperAdjacentSuffixMidbandSupply", "ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_short_window_diagonal_supply", "ErdosProblems.Erdos249.PaperCompleteR21.irrational_qZeta_half_difference_of_linearIndependent", "ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_block_cosine_gap", "ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_digitChange_count", "ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_fareyGapExclusionUnbounded", "ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_quarterFarPhase_count", "ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_quarterFarPhase_proportion", "ErdosProblems.Erdos249.PaperCompleteR21.paperAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude", "ErdosProblems.Erdos249.PaperCompleteR21.paperAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand", "ErdosProblems.Erdos249.PaperCompleteR21.rational_forces_four_tail_diagonals_integral", "ErdosProblems.Erdos249.PaperCompleteR21.rational_forces_period_multiple_integrality", "ErdosProblems.Erdos249.PaperCompleteR21.rational_forces_pulse_class_integrality", "ErdosProblems.Erdos249.PaperCompleteR21.tail_diff_notMem_int_of_irrational", "ErdosProblems.Erdos249.PaperCompleteR21.transcendental_sigma_series", "Erdos249257.TotientTailPeriodKiller.eq_prime_pow_of_not_dvd_periodLcm", "ErdosProblems.Erdos249.PaperCompleteR20.clean_lcm_ray_factorisation", "ErdosProblems.Erdos249.PaperCompleteR20.radical_decomposition", "ErdosProblems.Erdos249.PaperCompleteR20.specified_euler_tail_period", "ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.upper_bound_needed_for_every_q", "ErdosProblems.Erdos249.PaperCompleteR21.b6_adjugate_tail_cost_floor", "ErdosProblems.Erdos249.PaperCompleteR21.b6_mobiusMersenne_rung_estimates", "ErdosProblems.Erdos249.PaperCompleteR21.b6_synthetic_sequence_prescribed_differences", "ErdosProblems.Erdos249.PaperCompleteR21.bracket_of_two_sided_separation", "ErdosProblems.Erdos249.PaperCompleteR21.canonicalTotientKernelFamily_independent_card_and_span", "ErdosProblems.Erdos249.PaperCompleteR21.canonical_family_basis_through_level", "ErdosProblems.Erdos249.PaperCompleteR21.divisorIndex_endpoint_behaviour", "ErdosProblems.Erdos249.PaperCompleteR21.eventual_integral_tailDiff_twoAdic_half_pulse", "ErdosProblems.Erdos249.PaperCompleteR21.exists_clean_cyclotomic_anchor_paper", "ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_integral_tailDiff_half_pulse", "ErdosProblems.Erdos249.PaperCompleteR21.fixedRank_cleanWindow_structure", "ErdosProblems.Erdos249.PaperCompleteR21.forwardMultiple_spec", "ErdosProblems.Erdos249.PaperCompleteR21.integral_carry_strictly_between", "ErdosProblems.Erdos249.PaperCompleteR21.joint35_truncation_error", "ErdosProblems.Erdos249.PaperCompleteR21.lacCoef_bounds", "ErdosProblems.Erdos249.PaperCompleteR21.lcmRay_divisor_clean_formula", "ErdosProblems.Erdos249.PaperCompleteR21.lcmRay_nondivisor_literal", "ErdosProblems.Erdos249.PaperCompleteR21.oddHalfCenteredLift_spec", "ErdosProblems.Erdos249.PaperCompleteR21.penultimate_shortWindow_difference_eq_half", "ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_strict_jump_at_prime_pred", "ErdosProblems.Erdos249.PaperCompleteR21.pulse_delta_of_divisor_data", "ErdosProblems.Erdos249.PaperCompleteR21.rationalValue_integral_carry_and_rank_floor", "ErdosProblems.Erdos249.PaperCompleteR21.rational_tail_period_explicit_witnesses", "ErdosProblems.Erdos249.PaperCompleteR21.shortWindowSupply_single_witness_six_ninetyThree", "ErdosProblems.Erdos249.PaperCompleteR21.shortWindowSupply_through_six_paper", "ErdosProblems.Erdos249.PaperCompleteR21.short_window_diagonal_through_six", "ErdosProblems.Erdos249.PaperCompleteR21.totientTail_enclosure", "ErdosProblems.Erdos249.PaperCompleteR21.twoAdic_pulse_error_bound", "ErdosProblems.Erdos249.PaperCompleteR21.two_mul_totient_dvd_totient_second_difference", "ErdosProblems.Erdos249.PaperCompleteR8.displayed_all_base_kernel", "ErdosProblems.Erdos249.PaperCompleteR21.exists_simultaneous_depth_succ_of_irrational", "ErdosProblems.Erdos251.PaperCompleteR20.finite_separation_complete", "ErdosProblems.Erdos251.PaperCompleteR20.one_tail_signed_certificate", "ErdosProblems.Erdos251.PaperCompleteR21.long_joint_prime_gap_countermodel", "ErdosProblems.Erdos251.PaperCompleteR21.nonconcentration_does_not_force_irrationality", "ErdosProblems.Erdos251.PaperCompleteR21.prime_gap_equal_shift_zeroDensity", "ErdosProblems.Erdos251.PaperCompleteR21.short_joint_prime_gap_countermodel", "ErdosProblems.Erdos251.irrational_tsum_primeDyadicTerm_iff_primeGap", "ErdosProblems.Erdos251.PaperCompleteR20.local_target_interval", "ErdosProblems.Erdos251.PaperCompleteR20.real_orbit_exact_den_and_shift", "ErdosProblems.Erdos251.PaperCompleteR21.cut_prefix_bound", "ErdosProblems.Erdos251.PaperR11.SparsePaper.polylogarithmic_word_interval_uniform", "ErdosProblems.Erdos251.PaperR7.rational_bounded_perturbation", "ErdosProblems.Erdos251.PaperR7.real_small_pair_prime_endpoint", "ErdosProblems.Erdos251.PaperR9.SparseAmbient.arbitrary_word_sparse_rationalisation_uniform", "ErdosProblems.Erdos251.PaperCompleteR21.prime_gap_two_window_sparse", "ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_divisorResidueSum", "ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_geometricForm", "ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_tsum_divisorResidue", "ErdosProblems.Erdos257.PaperCompleteR21.arithmetic_logarithmic_counterexample", "ErdosProblems.Erdos257.PaperCompleteR21.logarithmic_initial_interval", "ErdosProblems.Erdos257.PaperCompleteR21.paper_effective_horizon_test", "ErdosProblems.Erdos257.PaperCompleteR21.paper_mersenne_channel_survival", "ErdosProblems.Erdos257.PaperCompleteR21.paper_one_orbit_stability", "ErdosProblems.Erdos257.PaperCompleteR21.paper_shared_prefix_family_strip_witness_after_feedback_of_all_depths", "ErdosProblems.Erdos257.PaperCompleteR21.paper_zero_run_le_eps_logb", "Erdos249257.HalfCarryReachability.greedy_half_infinite_of_cofinalStripReturn", "Erdos249257.SeamTwoSidedDyadicCellEscape.twoSided", "Erdos249257.SuffixCylinderTerminalOnlyBridge.exists_infinite_positive_support_half_of_cofinalCylinderStages", "Erdos249257.exists_laterProtectedExactLocalMersenneRow", "Erdos249257.halfGreedySkippedCriticalQuotientSupply_of_precriticalSuffix", "Erdos249257.half_mem_mersenneAchievementSet_of_criticalQuotientSupply", "Erdos249257.half_mem_mersenneAchievementSet_of_largestSkipLateStepSocket", "Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerCardEscape", "Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerRowEscape", "Erdos249257.half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips", "Erdos249257.half_mem_mersenneAchievementSet_of_secondChannelSeparation", "Erdos249257.half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven", "Erdos249257.half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative", "Erdos249257.half_mem_mersenneAchievementSet_of_skippedSeamEscape", "Erdos249257.half_mem_mersenneAchievementSet_of_skipped_dyadicCap", "Erdos249257.half_mem_mersenneAchievementSet_of_skipped_twoChannelCap", "Erdos249257.half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape", "Erdos249257.twentyOneFatalAlignedBranch_eventually_affine_supercapacity", "Erdos249257.twentyOneFatalAlignedBranch_eventually_strict_supercapacity", "ErdosProblems.Erdos257.PaperCompleteR21.half_mem_mersenneAchievementSet_of_resetSqrtEscape", "ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_escape_implies_full_shell_nonnegative", "ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_escape_implies_half_membership", "ErdosProblems.Erdos257.PaperCompleteR21.paper_terminal_strip_forces_half_membership", "ErdosProblems.Erdos257.PaperCompleteR21.paper_theoremA_half_membership", "ErdosProblems.Erdos257.PaperCompleteR21.paper_two_sided_dyadic_bound", "Erdos249257.HalfCarryReachability.infinite_support_half_of_mobiusCenteredHalfCarry_sqrtBound", "Erdos249257.HalfTrappingReturnCarry.overlappingReverseCarryWords_carryDifference_eq_twoPow_mul_odd", "Erdos249257.exists_boolean_word_of_lt_two_pow", "Erdos249257.exists_exactRowStrictUpperExtension_two_mul_sub_one_of_exact_below", "Erdos249257.exists_exactRowStrictUpperFill_of_skippedCoreSharpCapacity", "Erdos249257.exists_first_localMersenne_crossing", "ErdosProblems.Erdos257.PaperCompleteR20.square_depth_witness", "ErdosProblems.Erdos257.PaperCompleteR21.fatal_absorbing", "ErdosProblems.Erdos257.PaperCompleteR21.fatal_gap_within_prefix_interval", "ErdosProblems.Erdos257.PaperCompleteR21.paper_capacity_band_exclusion", "ErdosProblems.Erdos257.PaperCompleteR21.paper_channel_factor_gcd_eq_one", "ErdosProblems.Erdos257.PaperCompleteR21.paper_dynamics", "ErdosProblems.Erdos257.PaperCompleteR21.paper_endpoint_term_counts_divisors", "ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_mass_threshold", "ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_from_skipped_prefix", "ErdosProblems.Erdos257.PaperCompleteR21.paper_half_lcm_horizon", "ErdosProblems.Erdos257.PaperCompleteR21.paper_mersenne_height", "ErdosProblems.Erdos257.PaperCompleteR21.paper_perturbed_prefixChoice_maximal", "ErdosProblems.Erdos257.PaperCompleteR21.paper_perturbed_two_stage_is_global_maximum", "ErdosProblems.Erdos257.PaperCompleteR21.paper_pulse_family_finite_state_card", "ErdosProblems.Erdos257.PaperCompleteR21.paper_scalar_localization", "ErdosProblems.Erdos257.PaperCompleteR21.paper_square_depth_terminal_bound", "ErdosProblems.Erdos257.PaperCompleteR21.paper_unconditional_bound_one_extra_bit", "ErdosProblems.Erdos257.PaperCompleteR21.paper_upper_branch_needs_no_exceptional_cell", "ErdosProblems.Erdos257.PaperCompleteR21.weighted_denominator_budget", "ErdosProblems.Erdos257.PaperCompleteR8.weighted_displacement_cofinal_close_return", "ErdosProblems.Erdos257.finite_monotone_witness_rule_realised", "Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound", "ErdosProblems.Erdos269.PaperR7.long_no_bounded_length", "ErdosProblems.Erdos269.PaperR7.long_window_growth", "ErdosProblems.Erdos269.PaperR7.paper_uniform_rank_and_nonseparation", "ErdosProblems.Erdos269.PaperCompleteR21.transcendental_heckeValue", "ErdosProblems.Erdos269.PaperCompleteR21.two_prime_sums_transcendental", "ErdosProblems.Erdos269.PaperCompleteR21.two_prime_transcendence", "ErdosProblems.Erdos269.PaperCompleteR20.conditional_denominator_reduction_real_bound", "ErdosProblems.Erdos269.PaperCompleteR20.realSmoothExponentShell_bounds", "ErdosProblems.Erdos269.PaperR13.exact_denominators_and_minimal_clearing", "ErdosProblems.Erdos269.PaperR8.uniform_rank_complete", "ErdosProblems.Erdos68.PaperComplete.maximal_prime_power_survival", "ErdosProblems.Erdos68.PaperComplete.global_complementary_criterion_nat"] : Array String).map String.toName })
