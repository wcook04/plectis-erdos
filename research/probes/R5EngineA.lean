import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Util.AtomM
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.Interval.Finset.Defs
import ErdosProblems.ArgumentGraph.Residualise
import ErdosProblems.ArgumentGraph.Results.Erdos249Endpoint
import ErdosProblems.Erdos68.PaperCompleteSupplementary
import ErdosProblems.Erdos251.PaperCompleteR21.JointPrimeGapCountermodel
import ErdosProblems.Erdos251.RealPrimeGapTail
import Erdos249257.HalfCarryReachability

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
  /-- round a count's strict lower bound up to the next integer before eliminating the count -/
  integerRounding : Bool := false
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
compares with `X` from below (`t ≤ X`, `t < X`, `X ≥ t`, `X > t`). -/
def atTopBounds (B X f : Expr) : TermElabM (Array (Expr × Expr)) := do
  let α ← inferType X
  let some top ← (try some <$> mkAppOptM ``Filter.atTop #[α, none] catch _ => pure none)
    | return #[]
  unless ← isDefEq f top do return #[]
  let mut seen : Array Expr := #[]
  let mut out : Array (Expr × Expr) := #[]
  for s in appSubterms 4000 B #[B] do
    if s.hasLooseBVars then continue
    let some (β, t, u, rel) ← comparison? s | continue
    if rel == .eq || u != X || seen.contains t then continue
    if t.containsFVar X.fvarId! || t.hasLooseBVars || t.hasMVar then continue
    unless ← isDefEq β α do continue
    let some pf ← (try some <$> mkAppM ``Filter.eventually_gt_atTop #[t] catch _ => pure none)
      | continue
    seen := seen.push t
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
      | none => return none

/-- One hypothesis of a theorem changed by `restateScoped`: its position in the original
telescope and its binder name; the hypothesis `H` and what replaces it `R` (`True` when the facts
give it), each closed over the binders before it that it mentions; the contract
`∀ (binders), R → H` with its proof; whether all three are closed as they stand (no earlier
binder mentioned, no hypothesis in scope used); whether `H → R` was also proved in scope (the
restatement asks no more than the hypothesis; otherwise it is only sufficient); what the search
did, and the corpus theorems whose readings entered an elimination. -/
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
    let ty ← if ty.isForall then pure ty else do
      let ty' ← whnf ty
      pure (if ty'.isForall then ty' else ty)
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
      let needH ← neededBinders pre #[d]
      let needR ← neededBinders pre #[d']
      let needC ← neededBinders pre #[d, d', pf]
      let change : SlotChange := {
        index := j, binder := n, hyp := ← mkForallFVars needH d,
        residual := ← mkForallFVars needR d',
        contract := ← mkForallFVars needC (← mkArrow d' d),
        proof := ← mkLambdaFVars needC pf,
        given, closed := needC.isEmpty, weaker, notes, facts := used }
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

/-- Restate `target` with the facts of `suppliers` and add the result as `name`: for a theorem,
each hypothesis the facts give is dropped and each other one is replaced by what it still needs
in the quantities no fact controls; for a proposition (a definition of type `Prop`),
`name : D' → D`. With `expecting k`, the command fails unless the computed statement has the
key `k` (the export's key). The kernel checks the declaration. -/
def elabRestateWith (nameStx targetStx : Syntax) (supplierStx : Array Syntax)
    (proposeWitnesses integral : Bool) (expecting : Option String) : CommandElabM Unit :=
  liftTermElabM do
    let name := (← getCurrNamespace) ++ nameStx.getId
    let target ← realizeGlobalConstNoOverloadWithInfo targetStx
    let suppliers ← supplierStx.mapM fun s => realizeGlobalConstNoOverloadWithInfo s
    if suppliers.contains target then throwError "restate: {target} cannot supply itself"
    let unfoldOk := fun (n : Name) => [`ErdosProblems, `Erdos249257].any (·.isPrefixOf n)
    let R ← supplierRetrieval suppliers unfoldOk proposeWitnesses
    let R := { R with integerRounding := integral }
    let check (ty : Expr) : TermElabM Unit := do
      if let some k := expecting then
        let k' := statementKey ty
        unless k' == k do
          throwError "restate {target}: the restatement has key {k'}, expected {k}:\n  {ty}"
    let ci ← getConstInfo target
    match ci with
    | .thmInfo _ =>
      let some r ← restateScoped R target
        | throwError "restate {target}: the facts of {suppliers.toList} change no hypothesis"
      check r.type
      addDecl (.thmDecl { name, levelParams := ci.levelParams, type := r.type, value := r.value })
      logInfo m!"restate {target}: {r.dropped} hypothesis(es) dropped, {r.restated} restated:\n  {r.type}"
    | .defnInfo d =>
      unless d.type.isProp do throwError "restate: {target} is not a proposition"
      R.resetEvals
      let some (C', pf) ← abduceProp R 64 #[] #[] none d.value
        | throwError "restate {target}: the facts of {suppliers.toList} change nothing"
      let ty ← mkArrow C' (Lean.mkConst target (d.levelParams.map Level.param))
      check ty
      addDecl (.thmDecl { name, levelParams := d.levelParams, type := ty, value := pf })
      logInfo m!"restate {target}:\n  {C'}"
    | _ => throwError "restate: {target} is neither a theorem nor a proposition"

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


/-! # Probe R5A: the scoped engine on the corpus

1. The calibrations of `abduce` are unchanged.
2. The #249 clause for arbitrarily large scales restates to the good-base gap as before; with
   integer rounding it restates to a weaker condition that the gap implies.
3. The cofinal reading `∀ A, ∃ᶠ X, …` with the eventual bounds gives a cofinal statement outright.
4. The vacuity test refutes the #68 shapes the old reading produced, and not a satisfiable one.
5. Real theorems restated in scope: each restatement closed and accepted by the kernel.
-/

namespace ProbeR5A

open Filter Finset
open ErdosProblems.ArgumentGraph.Abduce Erdos249257.TotientTailPeriodKiller
open ErdosProblems.Erdos249.PaperCompleteR21

/-! ## 1. Calibrations -/

theorem subset_threshold (m b u g γ : ℝ) (hp : m + b + u = 1) (hb0 : 0 ≤ b)
    (hb : b < 1 / 100) (hu0 : 0 ≤ u) (hu : u < 8 / 25) (hg1 : -m ≤ g) (hg2 : g ≤ m)
    (hγ : g ≤ γ) (hgap : γ ≤ 603 / 1000) : g ≤ 9 / 10 * m := by
  abduce [γ] using hp, hb0, hb, hu0, hu, hg1, hg2, hγ
  guard_target = γ ≤ 603 / 1000
  exact hgap

theorem whole_block_threshold (t g b u γ : ℝ) (ht : t ≤ g + b + u) (hb0 : 0 ≤ b)
    (hb : b < 1 / 100) (hu0 : 0 ≤ u) (hu : u < 8 / 25) (hγ : g ≤ γ) (hgap : γ ≤ 57 / 100) :
    t ≤ 9 / 10 := by
  abduce [γ] using ht, hb0, hb, hu0, hu, hγ
  guard_target = γ ≤ 57 / 100
  exact hgap

theorem goodBase_clause (h X L : ℕ)
    (hcard : (67 / 100 : ℝ) * X < ((pivotGoodBases X L 26 (1 / 1000 : ℝ)).card : ℝ))
    (hgap : ∑ N ∈ pivotGoodBases X L 26 (1 / 1000 : ℝ), windowFirstCos h N L ≤
      603 / 1000 * (X : ℝ)) :
    ∑ N ∈ pivotGoodBases X L 26 (1 / 1000 : ℝ), windowFirstCos h N L ≤
      9 / 10 * ((pivotGoodBases X L 26 (1 / 1000 : ℝ)).card : ℝ) := by
  abduce using hcard
  guard_target = ∑ N ∈ pivotGoodBases X L 26 (1 / 1000 : ℝ), windowFirstCos h N L ≤
      603 / 1000 * (X : ℝ)
  exact hgap

/-! ## 2. The #249 clause for arbitrarily large scales -/

def GoodBaseClause : Prop :=
  ∀ h : ℕ, ∃ᶠ X in atTop,
    (∑ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
      windowFirstCos h N (minimalDepth h 26 X)) ≤
      9 / 10 * ((pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).card : ℝ)

def GoodBaseGap : Prop :=
  ∀ h : ℕ, ∃ᶠ X in atTop,
    (∑ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
      windowFirstCos h N (minimalDepth h 26 X)) ≤ 603 / 1000 * (X : ℝ)

set_option maxHeartbeats 4000000 in
restate goodBaseClause_of_restated for GoodBaseClause using eventually_card_pivotGoodBases_gt

/-- As before: the computed restatement is the good-base gap. -/
theorem goodBaseClause_of_goodBaseGap (h : GoodBaseGap) : GoodBaseClause :=
  goodBaseClause_of_restated h

set_option maxHeartbeats 4000000 in
restate_integral goodBaseClause_of_integral for GoodBaseClause using eventually_card_pivotGoodBases_gt

#check @goodBaseClause_of_integral

/-- The gap gives the integer restatement: `603X/1000 = (9/10)(67X/100) < (9/10)(⌊67X/100⌋₊ + 1)`. -/
theorem goodBaseClause_of_goodBaseGap' (h : GoodBaseGap) : GoodBaseClause :=
  goodBaseClause_of_integral (fun k => (h k).mono fun X hX => by
    have := Nat.lt_floor_add_one ((67 / 100 : ℝ) * (X : ℝ))
    linarith)

/-! ## 3. A cofinal statement given outright -/

def FreqDemo : Prop := ∀ A : ℕ, ∃ X : ℕ, A ≤ X ∧ 3 ≤ X

restate freqDemo_given for FreqDemo from

example : FreqDemo := freqDemo_given trivial

/-- The old cofinal reading asks for the impossible where the new one does not. -/
example : ¬ ∃ᶠ X in atTop, ∀ A : ℕ, A ≤ X → A < X / 2 + 1 := not_frequently_forall_le_half
example : ∀ A : ℕ, ∃ᶠ X in atTop, A < X / 2 + 1 := forall_frequently_half

/-! ## 4. The vacuity test -/

set_option hygiene false in
open Lean Meta Elab Term in
#eval show TermElabM Unit from do
  withLocalDeclD `X (Lean.mkConst ``Nat) fun _ => withLocalDeclD `w (Lean.mkConst ``Nat) fun _ => do
    let check (stx : TSyntax `term) (expect : Bool) : TermElabM Unit := do
      let P ← elabTerm stx (some (Lean.mkSort .zero))
      Term.synthesizeSyntheticMVarsNoPostponing
      let P ← instantiateMVars P
      let got ← refutedInScope #[] P
      IO.println s!"[r5a] refuted {← ppExpr P}: {got}"
      unless got == expect do throwError "vacuity test: {P} refuted = {got}, expected {expect}"
    check (← `(4 ≤ X ∧ X < X / 2 + 1)) true
    check (← `(X < w ∧ w + 1 < X)) true
    check (← `(4 ≤ X ∧ 1 < X / 2 + 1)) false

/-! ## 5. Restated in scope -/

open Lean Meta Elab Term in
def kernelOk (type value : Expr) (lps : List Name) : MetaM Bool := do
  if type.hasFVar || type.hasMVar || value.hasFVar || value.hasMVar then return false
  let decl := Declaration.thmDecl { name := `_r5a_check, levelParams := lps, type, value }
  match Kernel.Environment.addDeclCore (← getEnv).toKernelEnv 0 decl none with
  | .ok _ => return true
  | .error _ => return false

open Lean Meta Elab Term in
def probeCorpus (thms : Array Name) : TermElabM Unit := do
  let unfoldOk := fun (n : Name) => [`ErdosProblems, `Erdos249257].any (·.isPrefixOf n)
  let t0 ← IO.monoMsNow
  let (facts, k) ← buildFactIndex #[`ErdosProblems, `Erdos249257] unfoldOk
  IO.println s!"[r5a] fact readings {k} in {(← IO.monoMsNow) - t0} ms"
  let mut bad := 0
  for thm in thms do
    let some (.thmInfo info) := (← getEnv).find? thm
      | IO.println s!"[r5a] {thm}: absent"
    let R : Retrieval := { corpusRetrieval facts unfoldOk #[thm] with
      notes := some (← IO.mkRef #[]), used := some (← IO.mkRef #[]) }
    let s ← IO.monoMsNow
    let res ← ErdosProblems.ArgumentGraph.Residualise.budgetedTerm 400000 (do
      try return Except.ok (← restateScoped R thm)
      catch e => return Except.error (← e.toMessageData.toString))
    let ms := (← IO.monoMsNow) - s
    match res with
    | none => IO.println s!"[r5a] {thm}: budget ({ms} ms)"
    | some (.error e) => IO.println s!"[r5a] {thm}: error {e}"
    | some (.ok none) => IO.println s!"[r5a] {thm}: unchanged ({ms} ms)"
    | some (.ok (some r)) =>
      let ok ← kernelOk r.type r.value info.levelParams
      unless ok do bad := bad + 1
      IO.println s!"[r5a] {thm}: dropped {r.dropped} restated {r.restated} vacuous {r.vacuous} out-of-scope {r.leaked} kernel {ok} ({ms} ms)"
      IO.println s!"   restated: {← ppExpr r.type}"
      for ch in r.changes do
        let cok ← kernelOk ch.contract ch.proof info.levelParams
        unless cok do bad := bad + 1
        IO.println s!"   slot {ch.index} {ch.binder}: given {ch.given} weaker {ch.weaker} closed {ch.closed} contract {cok} notes {ch.notes} facts {ch.facts}"
        IO.println s!"     H: {← ppExpr ch.hyp}"
        IO.println s!"     R: {← ppExpr ch.residual}"
  if bad > 0 then throwError "[r5a] {bad} restatement(s) or contract(s) not accepted by the kernel"

open Lean Meta Elab Term in
set_option maxHeartbeats 0 in
#eval show TermElabM Unit from probeCorpus #[
  `ErdosProblems.Erdos68.PaperComplete.moving_factor_pair_criterion,
  `ErdosProblems.Erdos251.PaperCompleteR21.short_joint_prime_gap_countermodel,
  `ErdosProblems.Erdos251.PaperCompleteR21.long_joint_prime_gap_countermodel,
  `ErdosProblems.Erdos251.irrational_primeSeries_of_realPrimeGapTail_small_mismatch,
  `Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound,
  `ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_goodBase_gap,
  `ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_support_gap]

end ProbeR5A
