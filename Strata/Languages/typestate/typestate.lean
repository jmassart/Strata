/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.typestate.TranslateExpr
public import Strata.Languages.Core.Verifier
public import Strata.Languages.Core.Options

public section

namespace Strata.typestate

def verify (p : Strata.Program) (options : Core.VerifyOptions := Core.VerifyOptions.default)
    : IO Core.VCResults := do
  let (corePgm, names) ← IO.ofExcept (translateToProgram p.commands)
  let dir := options.vcDirectory.map toString |>.getD "."
  match ← (Core.verify corePgm ⟨dir⟩ (some names) options).toIO' with
  | .ok r => pure r
  | .error e => throw (IO.userError (toString (Std.format e)))

/-- Spec-only invariant checker: ignores user commands; verifies that
    init establishes every invariant and every API preserves them. -/
def verifyInvariants (p : Strata.Program) (options : Core.VerifyOptions := Core.VerifyOptions.default)
    : IO Core.VCResults := do
  let corePgm ← IO.ofExcept (translateToInvariantChecker p.commands)
  let dir := options.vcDirectory.map toString |>.getD "."
  match ← (Core.verify corePgm ⟨dir⟩ none options).toIO' with
  | .ok r => pure r
  | .error e => throw (IO.userError (toString (Std.format e)))

end Strata.typestate

end
