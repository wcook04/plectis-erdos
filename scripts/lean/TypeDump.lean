import Erdos249257
import ErdosProblems

open Lean Elab Command Meta

/-- Is this constant declared in one of the two project libraries? -/
def isOurs (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i =>
    match env.header.moduleNames[i.toNat]? with
    | some m => let r := m.getRoot; r == `Erdos249257 || r == `ErdosProblems
    | none => false
  | none => false

def flat (s : String) : String :=
  (s.replace "\n" " ").replace "\t" " " |>.replace "|||" "/PIPE/"

run_cmd liftTermElabM do
  let env ← getEnv
  let mut n := 0
  for (nm, ci) in env.constants.toList do
    unless isOurs env nm do continue
    if nm.isInternal then continue
    unless (match ci with | .thmInfo _ => true | _ => false) do continue
    let line ← withOptions (fun o =>
        (o.setBool `pp.fullNames true).setBool `pp.deepTerms true) do
      forallTelescopeReducing ci.type fun args body => do
        let mut hyps : Array String := #[]
        let mut binders : Array String := #[]
        for a in args do
          let t ← inferType a
          let s ← inferType t
          let d ← a.fvarId!.getDecl
          if s.isProp then
            hyps := hyps.push (toString d.userName ++ " :: " ++ flat (toString (← ppExpr t)))
          else
            binders := binders.push (toString d.userName ++ " : " ++ flat (toString (← ppExpr t)))
        let concl := flat (toString (← ppExpr body))
        return toString nm ++ "|||" ++ String.intercalate "@@" binders.toList ++ "|||"
          ++ String.intercalate "@@" hyps.toList ++ "|||" ++ concl
    IO.println line
    n := n + 1
  IO.println s!"###TOTAL {n}"
