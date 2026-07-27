import Erdos249257
import Lean

open Lean

private def moduleString (env : Environment) (name : Name) : String :=
  (env.getModuleFor? name).map (·.toString) |>.getD ""

private def isCorpusConstant (env : Environment) (name : Name) : Bool :=
  match env.getModuleFor? name with
  | some ownerModule => (`Erdos249257).isPrefixOf ownerModule
  | none => false

private def emitLine (stdout : IO.FS.Stream) (line : String) :
    Lean.Elab.Command.CommandElabM Unit :=
  liftM <| stdout.putStr (line ++ "\n")

private partial def conclusionShape (type : Expr) (binderCount : Nat := 0) :
    Nat × Expr :=
  match type with
  | .forallE _ _ body _ => conclusionShape body (binderCount + 1)
  | .letE _ _ _ body _ => conclusionShape body binderCount
  | conclusion => (binderCount, conclusion)

private def conclusionHeadLabel (conclusion : Expr) : String :=
  match conclusion.getAppFn with
  | .const name _ => name.toString
  | _ => "expr.nonconstant_head"

private structure BinderShape where
  userName : Name
  binderInfo : BinderInfo
  isProp : Bool
  head : String
  symbols : NameSet

private def binderInfoLabel : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strict_implicit"
  | .instImplicit => "instance_implicit"

private def binderShapes (type : Expr) :
    Lean.Elab.Term.TermElabM (Array BinderShape) :=
  Lean.Meta.forallTelescope type fun xs _ => do
    let mut rows := #[]
    for x in xs do
      let declaration ← x.fvarId!.getDecl
      rows := rows.push {
        userName := declaration.userName
        binderInfo := declaration.binderInfo
        isProp := ← Lean.Meta.isProp declaration.type
        head := conclusionHeadLabel declaration.type
        symbols := declaration.type.getUsedConstantsAsSet
      }
    return rows

private def emitDependencies (stdout : IO.FS.Stream) (env : Environment)
    (source : Name) (relation : String) (dependencies : NameSet) :
    Lean.Elab.Command.CommandElabM Nat := do
  let mut omittedInternal : Nat := 0
  for dependency in dependencies do
    if isCorpusConstant env dependency && dependency != source then
      if dependency.isInternal then
        omittedInternal := omittedInternal + 1
      else
        emitLine stdout <|
          "AIW_EDGE\t" ++ source.toString ++ "\t" ++
          moduleString env source ++ "\t" ++ dependency.toString ++ "\t" ++
          moduleString env dependency ++ "\t" ++ relation
  return omittedInternal

/-!
Emit a tab-separated projection of direct constant references from the
elaborated environment. `build_lean_dependency_index.py` owns the JSON
normalisation and source-coordinate join.
-/
run_cmd do
  let env ← getEnv
  let stdout ← liftM IO.getStdout
  for info in env.constants.map₁.values do
    let source := info.name
    if isCorpusConstant env source && !source.isInternal then
      emitLine stdout <|
        "AIW_NODE\t" ++ source.toString ++ "\t" ++ moduleString env source
      match info with
      | .thmInfo _ =>
        let (_, conclusion) := conclusionShape info.type
        let binders ← Lean.Elab.Command.liftTermElabM <| binderShapes info.type
        emitLine stdout <|
          "AIW_TYPE_SHAPE\t" ++ source.toString ++ "\t" ++
          toString binders.size ++ "\t" ++ conclusionHeadLabel conclusion
        for binder in binders, index in [0:binders.size] do
          emitLine stdout <|
            "AIW_BINDER_SHAPE\t" ++ source.toString ++ "\t" ++
            toString index ++ "\t" ++ binder.userName.toString ++ "\t" ++
            binderInfoLabel binder.binderInfo ++ "\t" ++
            toString binder.isProp ++ "\t" ++ binder.head
          for reference in binder.symbols do
            if !reference.isInternal then
              emitLine stdout <|
                "AIW_BINDER_REF\t" ++ source.toString ++ "\t" ++
                toString index ++ "\t" ++ reference.toString
        for reference in conclusion.getUsedConstantsAsSet do
          if !reference.isInternal then
            emitLine stdout <|
              "AIW_CONCLUSION_REF\t" ++ source.toString ++ "\t" ++
              reference.toString
      | _ => pure ()
      let typeOmissions ← emitDependencies stdout env source
        "type_reference" info.type.getUsedConstantsAsSet
      let valueOmissions ←
        match info.value? with
        | some value =>
            emitDependencies stdout env source "value_reference"
              value.getUsedConstantsAsSet
        | none => pure 0
      emitLine stdout <|
        "AIW_INTERNAL_OMISSION\t" ++ source.toString ++ "\t" ++
        toString (typeOmissions + valueOmissions)
  liftM stdout.flush
