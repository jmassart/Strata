/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.typestate.typestate
import Strata.DDM.BuiltinDialects
import Strata.DDM.Elab
import Strata.Languages.Core.Options

/-! Battery runner for the typestate Handles spec.
    `lake env lean --run StrataTest/Languages/typestate/RunHandlesBattery.lean` -/

open Strata Strata.Elab

def specsPath : String := "Examples/handle-domains/handles.typestate.st"
def batteryDir : System.FilePath := "Examples/handle-domains"

inductive Expectation where | pass | fail | unknown
deriving DecidableEq, Repr

private def padRight (s : String) (w : Nat) : String :=
  if s.length >= w then s else s ++ "".pushn ' ' (w - s.length)

def Expectation.toStr : Expectation → String
  | .pass    => "pass"
  | .fail    => "fail"
  | .unknown => "unknown"

private def parseExpectation (src : String) : Expectation :=
  let firstLines := src.splitOn "\n" |>.take 5
  let has (tag : String) := firstLines.any (fun l => (l.splitOn tag).length > 1)
  if has "EXPECT: unknown" then .unknown
  else if has "EXPECT: pass" then .pass
  else if has "EXPECT: fail" then .fail
  else .unknown

private def buildCombinedSource (userPath : System.FilePath) : IO String := do
  let specSrc ← IO.FS.readFile specsPath
  let userSrc ← IO.FS.readFile userPath
  let stripped :=
    let lines := userSrc.splitOn "\n"
    let dropped := lines.filter
      (fun l => !(l.trimAscii.toString == "program typestate;"))
    String.intercalate "\n" dropped
  pure (specSrc ++ "\n\n// ---- user: " ++ userPath.toString ++ " ----\n\n" ++ stripped)

def runProgram (programPath : System.FilePath)
    : IO (Option Bool × List String) := do
  let src ← buildCombinedSource programPath
  let ictx := Lean.Parser.mkInputContext src s!"<spec>+{programPath}"
  let dctx := LoadedDialects.builtin
  let dctx := dctx.addDialect! Core
  let dctx := dctx.addDialect! Strata.typestate
  let leanEnv ← Lean.mkEmptyEnvironment 0
  match Strata.Elab.elabProgram dctx leanEnv ictx with
  | .error _ => return (none, ["parse-error"])
  | .ok pgm =>
    try
      let opts : Core.VerifyOptions :=
        { Core.VerifyOptions.default with
            verbose := .quiet
            solverTimeout := 30
            useArrayTheory := true }
      let results ← Strata.typestate.verify pgm opts
      let fails := results.toList.filter (fun r => !r.isSuccess)
      let labels := fails.map (fun r => r.obligation.label)
      let allOk := fails.isEmpty
      return (some allOk, labels)
    catch e =>
      return (none, [s!"infra-error: {e}"])

structure Outcome where
  name      : String
  expected  : Expectation
  verdict   : Option Bool
  failLabels: List String

def Outcome.matches (o : Outcome) : Bool :=
  match o.expected, o.verdict with
  | .pass, some true  => true
  | .fail, some false => true
  | .unknown, _       => true
  | _, _              => false

def main (_args : List String) : IO Unit := do
  let dir ← batteryDir.readDir
  let files := dir.toList
                 |>.filter (fun e => e.fileName.endsWith ".typestate.st"
                                     && e.fileName != "handles.typestate.st")
                 |>.map (·.path)
                 |>.mergeSort (fun a b => a.toString < b.toString)
  IO.println s!"Running handle-domains battery — {files.length} programs.\n"
  let mut outcomes : Array Outcome := #[]
  for path in files do
    let src ← IO.FS.readFile path
    let exp := parseExpectation src
    let (verdict, labels) ← runProgram path
    let name := path.fileName.getD path.toString
    let o : Outcome := { name, expected := exp, verdict, failLabels := labels }
    outcomes := outcomes.push o
    let mark := if o.matches then "OK" else "FAIL"
    let verdictStr := match verdict with
      | some true  => "pass"
      | some false => "fail"
      | none       => "infra"
    IO.println s!"{padRight mark 4} {padRight name 46} exp={padRight exp.toStr 7}  got={verdictStr}"
  IO.println ""
  let matched := outcomes.toList.filter Outcome.matches |>.length
  IO.println s!"Result: {matched}/{outcomes.size} programs verified matching expectations."
  let mismatches := outcomes.toList.filter (fun o => !o.matches)
  unless mismatches.isEmpty do
    IO.println "\nMismatches:"
    for o in mismatches do
      let verdictStr := match o.verdict with
        | some true  => "pass"
        | some false => "fail"
        | none       => "infra"
      IO.println s!"  {o.name}: expected {o.expected.toStr}, got {verdictStr}"
      unless o.failLabels.isEmpty do
        IO.println s!"    failing labels: {o.failLabels}"
