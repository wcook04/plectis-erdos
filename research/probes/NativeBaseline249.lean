import ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactorEstimate
import ErdosProblems.Erdos249.TypeBReturnV8.PeripheralFiniteBridge

/-!
# Native baseline for the #249 generation-1 residualisation

The residualiser, given `DTWPivotResidualDecorrelation` (demand `G064`) and the suppliers
`prop_dickman`, `excluded_budget_one_thousandth_of_chebyshev` and
`pivotBudgetAt_of_peripheral_estimates`, with the hand-written composition absent from the
environment, leaves one witness and two clauses (runs 36347571483, 36349878790). Each arm below
gives the same demand to Lean's own search in the same environment, on a fresh goal within a
heartbeat budget, and prints the goals it leaves with their atomic clause counts (counted as the
residualiser counts them). An arm that closes the goal prints a proof; one that fails prints why.
-/

open Lean Meta Elab Term

namespace NativeBaseline

partial def clauseCount (T : Expr) (depth : Nat := 10) : MetaM Nat := do
  if depth == 0 then return 1
  let T ← whnfR (← instantiateMVars T)
  match T with
  | .forallE n d b bi => withLocalDecl n bi d fun x => clauseCount (b.instantiate1 x) (depth - 1)
  | _ =>
    if T.isAppOfArity ``And 2 then
      return (← clauseCount T.appFn!.appArg! (depth - 1)) + (← clauseCount T.appArg! (depth - 1))
    if T.isAppOfArity ``Exists 2 then
      return ← withLocalDeclD `w T.appFn!.appArg! fun w =>
        clauseCount (T.appArg!.beta #[w]) (depth - 1)
    if T.isAppOfArity ``Filter.Eventually 3 || T.isAppOfArity ``Filter.Frequently 3 then
      return ← withLocalDeclD `X (T.getArg! 0) fun x =>
        clauseCount ((T.getArg! 1).beta #[x]) (depth - 1)
    if let some c := T.getAppFn.constName? then
      if [`ErdosProblems, `Erdos249257].any (·.isPrefixOf c) then
        if let some u ← unfoldDefinition? T then return ← clauseCount u (depth - 1)
    return 1

/-- Run `tac` on a fresh goal `T` within `hb` thousand heartbeats and report the goals it leaves
(or why it stopped); the elaboration state is restored afterwards. -/
def arm (label : String) (T : Expr) (tac : String) (hb : Nat := 400000) : TermElabM Unit := do
  let env ← getEnv
  match Parser.runParserCategory env `tactic tac with
  | .error e => logInfo m!"[{label}] parse error: {e}"
  | .ok stx =>
    let s ← Term.saveState
    let g ← mkFreshExprMVar T .syntheticOpaque
    let t0 ← IO.monoMsNow
    let r ← withCurrHeartbeats <|
      withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := hb * 1000 }) do
        tryCatchRuntimeEx
          (do
            let gs ← Term.withoutErrToSorry <| Tactic.run g.mvarId! (Tactic.evalTactic stx)
            return Except.ok gs)
          (fun e => do return Except.error (← e.toMessageData.toString))
    let ms := (← IO.monoMsNow) - t0
    let report ← match r with
      | .error e => pure s!"[{label}] stopped after {ms} ms: {e.take 400}"
      | .ok gs => do
        let mut total := 0
        let mut body := ""
        for g' in gs do
          let ty ← instantiateMVars (← g'.getType)
          let c ← clauseCount ty
          total := total + c
          body := body ++ s!"\n  goal ({c} clause(s)): {(← ppExpr ty).pretty 100 |>.take 600}"
        let closed := if gs.isEmpty then
            s!"; proof uses sorry: {(← instantiateMVars g).hasSorry}" else ""
        pure s!"[{label}] {gs.length} goal(s) left, {total} clause(s), {ms} ms{closed}{body}"
    s.restore
    logInfo report

end NativeBaseline

open Erdos249257.TotientTailPeriodKiller ErdosProblems.Erdos249.PaperCompleteR21
  ErdosProblems.Erdos249.PaperCompleteR21.ExcludedCofactor in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let T := Lean.mkConst ``DTWPivotResidualDecorrelation
  let rules := "(add unsafe 50% apply prop_dickman) " ++
    "(add unsafe 50% apply excluded_budget_one_thousandth_of_chebyshev) " ++
    "(add unsafe 50% apply pivotBudgetAt_of_peripheral_estimates)"
  let cfg := "(config := { terminal := false, warnOnNonterminal := false, maxRuleApplications := 4000 })"
  let arms : List (String × String) := [
    ("exact?", "exact?"),
    ("apply?", "apply?"),
    ("aesop + suppliers", s!"aesop {rules} {cfg}"),
    ("unfold; aesop + suppliers",
      s!"(unfold DTWPivotResidualDecorrelation PivotBudgetAt; aesop {rules} {cfg})"),
    ("unfold; intro; exact?", "(unfold DTWPivotResidualDecorrelation; intro h hh; exact?)"),
    ("unfold; intro; apply?", "(unfold DTWPivotResidualDecorrelation; intro h hh; apply?)")]
  for (label, tac) in arms do
    NativeBaseline.arm label T tac
