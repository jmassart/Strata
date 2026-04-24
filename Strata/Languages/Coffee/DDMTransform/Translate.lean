module

public import Strata.Languages.Coffee.DDMTransform.Parse
public import Strata.DDM.AST

public section

namespace Strata.Coffee

-- Core prelude prepended to every generated file: Moore-machine definition.
def prelude : String :=
  include_str "machine_moore.core.st"

-- Translate one Coffee op to one line of Core.
private def renderOp : CoffeeOp α → String
  | .op_espresso   _        => "  call selectDrink(Espresso());"
  | .op_latte      _        => "  call selectDrink(Latte());"
  | .op_cappuccino _        => "  call selectDrink(Cappuccino());"
  | .op_pay      _ ⟨_, n⟩   => s!"  call insertCoin({n});"
  | .op_dispense _          => "  call dispense();"
  | .op_take_cup _          => "  call takeCup();"
  | .op_cancel   _          => "  call cancel();"

private def renderOps (ops : Array (CoffeeOp α)) : String :=
  ops.toList.map renderOp |> String.intercalate "\n"

private def procedureTemplate (name body : String) : String :=
  s!"procedure {name}() returns ()
spec \{
  modifies state, drink, credit, change, refund;
  requires [machine_wellFormed]: machineInvariant(state, drink, credit, change, refund);
  requires [start_from_idle]:    State..isIDLE(state);
}
\{
{body}
};
"

private def renderProgram : Command α → String × String
  | .program_cmd _ ⟨_, name⟩ ⟨_, body⟩ =>
    (name, procedureTemplate name (renderOps body))

-- Translate Coffee programs to Core source.
def translateToCoreSource (ops : Array Strata.Operation)
    : Except String (String × List String) := do
  let cmds ← ops.toList.mapM Command.ofAst
  let pieces := cmds.map renderProgram
  let names  := pieces.map (·.1)
  let source := prelude ++ String.intercalate "\n" (pieces.map (·.2))
  .ok (source, names)

end Strata.Coffee
