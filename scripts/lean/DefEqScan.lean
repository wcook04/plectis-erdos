import ErdosProblems.DemandLedger.Basic

open Lean Elab Command Meta

set_option maxHeartbeats 2000000 in
run_cmd liftTermElabM do
  let env ← getEnv
  let mut gaps : Array (Name × Expr) := #[]
  for (nm, ci) in env.constants.toList do
    if nm.getPrefix == `DemandLedger then
      match ci with
      | .defnInfo d => gaps := gaps.push (nm, d.value)
      | _ => pure ()
  let sorted := gaps.qsort (fun a b => a.1.toString < b.1.toString)
  IO.println s!"### gaps {sorted.size}"
  -- exact structural duplicates
  let mut seen : Array (Expr × Array Name) := #[]
  for (n, v) in sorted do
    match seen.findIdx? (fun p => p.1 == v) with
    | some i => seen := seen.set! i (seen[i]!.1, seen[i]!.2.push n)
    | none => seen := seen.push (v, #[n])
  for (_, ns) in seen do
    if ns.size > 1 then IO.println s!"STRUCT-EQ {String.intercalate " " (ns.toList.map toString)}"
  IO.println s!"### distinct-up-to-structural {seen.size}"
  -- defeq beyond structural
  let reps := seen.map (fun p => (p.2[0]!, p.1))
  let mut hits := 0
  for i in [0:reps.size] do
    for j in [i+1:reps.size] do
      let ok ← withoutModifyingState <|
        (try withReducible (isDefEq reps[i]!.2 reps[j]!.2) catch _ => pure false)
      if ok then
        hits := hits + 1
        IO.println s!"DEFEQ {reps[i]!.1} {reps[j]!.1}"
  IO.println s!"### defeq-pairs-beyond-structural {hits}"
