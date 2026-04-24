/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Coffee.DDMTransform.Translate
public import Strata.Languages.Core.Verifier
public import Strata.Languages.Core.Options
public import Strata.DDM.Integration.Lean
public import Strata.DDM.Elab
public import Strata.DDM.BuiltinDialects

public section

namespace Strata.Coffee

private def parseCore (src : String) (displayName : String)
    : IO (Except String (Strata.Program × Lean.Parser.InputContext)) := do
  let ictx    := Lean.Parser.mkInputContext src displayName
  let dctx    := Elab.LoadedDialects.builtin
  let dctx    := dctx.addDialect! Core
  let leanEnv ← Lean.mkEmptyEnvironment 0
  match Strata.Elab.elabProgram dctx leanEnv ictx with
  | .ok pgm => pure (.ok (pgm, ictx))
  | .error msgs =>
    let strs ← msgs.toList.mapM (·.toString)
    pure (.error (String.intercalate "\n" strs))

/-- Translate a Coffee program to Strata Core, dump the generated source for
    inspection, then invoke the Core verifier on the result. -/
def verify (p : Strata.Program) (options : Core.VerifyOptions := Core.VerifyOptions.default)
    : IO Core.VCResults := do
  let (src, names) ← IO.ofExcept (translateToCoreSource p.commands)
  let dir := options.vcDirectory.map toString |>.getD "."
  let path := s!"{dir}/coffee-generated.core.st"
  IO.FS.writeFile path src
  IO.println s!"(wrote generated Core to {path})"
  match ← parseCore src path with
  | .error msg => throw (IO.userError s!"Coffee: generated Core failed to parse:\n{msg}")
  | .ok (pgm, ictx) => Strata.verify pgm ictx (some names) options

end Strata.Coffee
