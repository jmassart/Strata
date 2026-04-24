module

public import Strata.DDM.Integration.Lean

public section

#dialect
dialect Coffee;

category CoffeeOp;

// One operator per drink keyword — no numeric encoding on the surface.
op op_espresso   () : CoffeeOp => "select espresso;";
op op_latte      () : CoffeeOp => "select latte;";
op op_cappuccino () : CoffeeOp => "select cappuccino;";

op op_pay      (n : Num) : CoffeeOp => "pay " n ";";
op op_dispense ()        : CoffeeOp => "dispense;";
op op_take_cup ()        : CoffeeOp => "take_cup;";
op op_cancel   ()        : CoffeeOp => "cancel;";

op program_cmd (lbl : Ident, body : Seq CoffeeOp) : Command =>
  "program " lbl " {\n" body "};";

#end

namespace Strata.Coffee
#strata_gen Coffee
end Strata.Coffee
