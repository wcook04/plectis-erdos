import Erdos249257
import ErdosProblems
import ErdosProblems.ArgumentGraph.AbduceCorpus

/-!
# Abduction export

For every closed hypothesis of every theorem of the corpus libraries, this script asks what the
hypothesis still needs once the corpus's facts are used (`abduceProp` of
`ErdosProblems.ArgumentGraph.AbduceCorpus`, with the comparison readings of every corpus theorem
as facts). It writes JSON Lines rows next to the argument-continuation export, keyed exactly as
that export keys statements (`keyOf` below is a copy of it):

* `abduction` with `given: true`: a combination of corpus facts gives the hypothesis; the kernel
  has checked a proof of it;
* `abduction` with a `residual`: the restatement in the quantities no fact controls, with the
  kernel-checked proof that it implies the hypothesis, and a `statement` row for the residual so
  the graph can search it;
* a `meta` record first and a `summary` record last (fields prefixed `abduction_`), so the
  stream combines with the main export.

A statement is tried once however many theorems assume it. The facts used are the corpus
theorems named in the proof. `scripts/build_argument_continuations.py` reads these rows with the
main export (`--export <abductions> --export <main>`, the main export last): a given statement is
supplied by an `abduction` reduction with no residual, and a restated one reduces to its
residual. Environment variables:

* `PLECTIS_ABDUCTION_EXPORT_FILE`: output path (stdout if unset);
* `PLECTIS_ABDUCTION_SECONDS`: wall-clock budget (default 1800);
* `PLECTIS_ABDUCTION_ROOTS`: module roots (default `Erdos249257,ErdosProblems`).
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

def emit (stream : IO.FS.Stream) (j : Json) : IO Unit :=
  stream.putStrLn j.compress

/-- Whether the kernel accepts `value : type` as a theorem (in a scratch environment). -/
def kernelAccepts (type value : Expr) (levelParams : List Name) : MetaM Bool := do
  let decl := Declaration.thmDecl { name := `_abduction_check, levelParams, type, value }
  match Kernel.Environment.addDeclCore (← getEnv).toKernelEnv 0 decl none with
  | .ok _ => return true
  | .error _ => return false

/-- The corpus theorems a proof term names, other than `exclude`. -/
def factsNamed (unfoldOk : Name → Bool) (exclude : Name) (proof : Expr) : MetaM (Array String) := do
  let env ← getEnv
  return (proof.getUsedConstants.filter fun c =>
      c != exclude && unfoldOk c && (match env.find? c with | some (.thmInfo _) => true | _ => false))
    |>.map toString

def exportAll : TermElabM Unit := do
  let path? ← IO.getEnv "PLECTIS_ABDUCTION_EXPORT_FILE"
  let seconds := ((← IO.getEnv "PLECTIS_ABDUCTION_SECONDS").bind String.toNat?).getD 1800
  let roots : Array Name := match ← IO.getEnv "PLECTIS_ABDUCTION_ROOTS" with
    | some raw => ((raw.splitOn ",").filter (· ≠ "")).toArray.map String.toName
    | none => #[`Erdos249257, `ErdosProblems]
  let stream ← match path? with
    | some p => IO.FS.Stream.ofHandle <$> IO.FS.Handle.mk p .write
    | none => IO.getStdout
  let unfoldOk := fun (n : Name) => roots.any (·.isPrefixOf n)
  -- the builder reads a stream that opens with this meta record and has a summary record;
  -- give it before the main export (`--export abductions --export main`) so that the main
  -- export's meta and summary are the ones kept
  emit stream <| Json.mkObj [
    ("record", "meta"), ("schema", "plectis-argument-continuation-export/1"),
    ("stream", "abductions"), ("lean_version", toJson Lean.versionString),
    ("imports", toJson ((← getEnv).header.moduleNames.map toString))]
  let t0 ← IO.monoMsNow
  let (facts, nFacts) ← buildFactIndex roots unfoldOk
  let indexMs := (← IO.monoMsNow) - t0
  let env ← getEnv
  let mut seen : Std.HashSet String := {}
  let mut tried := 0
  let mut given := 0
  let mut restated := 0
  let mut rejected := 0
  let mut exhausted := 0
  let mut truncated := false
  for modName in env.header.moduleNames, data in env.header.moduleData do
    unless roots.any (·.isPrefixOf modName) do continue
    for thm in data.constNames do
      if thm.isInternal then continue
      let some (.thmInfo info) := env.find? thm | continue
      if (← IO.monoMsNow) - t0 > seconds * 1000 then
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
        tried := tried + 1
        let R := corpusRetrieval facts unfoldOk #[thm]
        -- each statement gets the default declaration budget; running out is counted apart
        -- from finding nothing, and is never read as the absence of a restatement
        let res ← ErdosProblems.ArgumentGraph.Residualise.budgetedTerm 200000
          (try abduceProp R 64 #[] #[] none H catch _ => pure none)
        if res.isNone then exhausted := exhausted + 1
        let some (H', pf) := res.join | continue
        let lps := info.levelParams
        if H'.isConstOf ``True then
          let value := mkApp pf (mkConst ``True.intro)
          if ← kernelAccepts H value lps then
            given := given + 1
            emit stream <| Json.mkObj [
              ("record", "abduction"), ("statement", toJson key), ("given", toJson true),
              ("theorem", toJson thm.toString), ("type", toJson (← render H)),
              ("facts", toJson (← factsNamed unfoldOk thm value)), ("kernel_checked", toJson true)]
          else rejected := rejected + 1
        else
          let ty ← mkArrow H' H
          if ← kernelAccepts ty pf lps then
            restated := restated + 1
            let rkey := keyOf H'
            emit stream <| Json.mkObj [
              ("record", "statement"), ("key", toJson rkey), ("origin", "abduction"),
              ("type", toJson (← render H'))]
            emit stream <| Json.mkObj [
              ("record", "abduction"), ("statement", toJson key), ("given", toJson false),
              ("residual", toJson rkey), ("theorem", toJson thm.toString),
              ("type", toJson (← render H)), ("residual_type", toJson (← render H')),
              ("facts", toJson (← factsNamed unfoldOk thm pf)), ("kernel_checked", toJson true)]
          else rejected := rejected + 1
    if truncated then break
  emit stream <| Json.mkObj [
    ("record", "summary"), ("abduction_statements_tried", toJson tried),
    ("abduction_given", toJson given), ("abduction_restated", toJson restated),
    ("abduction_kernel_rejected", toJson rejected), ("abduction_budget_exhausted", toJson exhausted),
    ("abduction_fact_readings", toJson nFacts),
    ("abduction_index_ms", toJson indexMs),
    ("abduction_elapsed_ms", toJson ((← IO.monoMsNow) - t0)),
    ("abduction_truncated", toJson truncated), ("abduction_budget_seconds", toJson seconds)]
  stream.flush

end AbductionExport

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM AbductionExport.exportAll
