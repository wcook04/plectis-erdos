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
