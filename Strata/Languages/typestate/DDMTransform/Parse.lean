/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Integration.Lean
public import Strata.DDM.Util.Format

public section

namespace Strata

/-!
## `typestate` — typestate-flavored API contract dialect

Two surfaces, one dialect:

  * Spec side — `service`, `resource`, `states { ... }`, `field`,
                `initial`, `api` with `before`/`after`/`transitions`,
                and `invariants`/`always`.
  * User side — straight-line API call sequences.

The expression category is `AExpr` (not `Expr`) to avoid colliding
with the built-in `Init` dialect.
-/

#dialect
dialect typestate;

category AExpr;

op ae_num   (n : Num)    : AExpr => @[prec(100)] n;
op ae_str   (s : Str)    : AExpr => @[prec(100)] s;
op ae_true  ()           : AExpr => @[prec(100)] "true";
op ae_false ()           : AExpr => @[prec(100)] "false";
op ae_var   (x : Ident)  : AExpr => @[prec(100)] x;
op ae_paren (a : AExpr)  : AExpr => @[prec(100)] "(" a ")";

// `old(...)` accepts only an identifier; for indexing write `old(m)[k]`.
op ae_old       (x : Ident) : AExpr =>
  @[prec(100)] "old" "(" x ")";
op ae_old_idx1  (x : Ident, k : Ident) : AExpr =>
  @[prec(100)] "old" "(" x ")" "[" k "]";
op ae_old_idx1_str (x : Ident, k : Str) : AExpr =>
  @[prec(100)] "old" "(" x ")" "[" k "]";
op ae_old_idx2  (x : Ident, b : Ident, k : Ident) : AExpr =>
  @[prec(100)] "old" "(" x ")" "[" b "]" "[" k "]";

op ae_index1 (m : Ident, k : Ident) : AExpr =>
  @[prec(100)] m "[" k "]";
op ae_index1_str (m : Ident, k : Str) : AExpr =>
  @[prec(100)] m "[" k "]";
op ae_index2 (m : Ident, b : Ident, k : Ident) : AExpr =>
  @[prec(100)] m "[" b "]" "[" k "]";
op ae_index2_ss (m : Ident, b : Str, k : Str) : AExpr =>
  @[prec(100)] m "[" b "]" "[" k "]";

op ae_not (a : AExpr)             : AExpr => @[prec(80)] "not" a;
op ae_add (a : AExpr, b : AExpr)  : AExpr => @[prec(50)] a " + " b;
op ae_sub (a : AExpr, b : AExpr)  : AExpr => @[prec(50)] a " - " b;

op ae_eq (a : AExpr, b : AExpr) : AExpr => @[prec(40)] a " == " b;
op ae_ne (a : AExpr, b : AExpr) : AExpr => @[prec(40)] a " != " b;
op ae_lt (a : AExpr, b : AExpr) : AExpr => @[prec(40)] a " < "  b;
op ae_le (a : AExpr, b : AExpr) : AExpr => @[prec(40)] a " <= " b;
op ae_gt (a : AExpr, b : AExpr) : AExpr => @[prec(40)] a " > "  b;
op ae_ge (a : AExpr, b : AExpr) : AExpr => @[prec(40)] a " >= " b;

op ae_in_id      (x : Ident, s : Ident) : AExpr =>
  @[prec(40)] x " in " s;
op ae_in_str     (x : Str,   s : Ident) : AExpr =>
  @[prec(40)] x " in " s;
op ae_in_id_old  (x : Ident, s : Ident) : AExpr =>
  @[prec(40)] x " in " "old" "(" s ")";
op ae_notin_id   (x : Ident, s : Ident) : AExpr =>
  @[prec(40)] x " not in " s;
op ae_notin_str  (x : Str,   s : Ident) : AExpr =>
  @[prec(40)] x " not in " s;

op ae_and     (a : AExpr, b : AExpr) : AExpr => @[prec(30)] a " and "     b;
op ae_or      (a : AExpr, b : AExpr) : AExpr => @[prec(25)] a " or "      b;
op ae_implies (a : AExpr, b : AExpr) : AExpr => @[prec(10)] a " implies " b;

op ae_forall1 (x : Ident,            body : AExpr) : AExpr =>
  @[prec(5)] "forall" x ":" "str" "::" body;
op ae_forall2 (x : Ident, y : Ident, body : AExpr) : AExpr =>
  @[prec(5)] "forall" x ":" "str" "," y ":" "str" "::" body;
op ae_exists1 (x : Ident,            body : AExpr) : AExpr =>
  @[prec(5)] "exists" x ":" "str" "::" body;

category StateList;
op states_decl (names : CommaSepBy Ident) : StateList =>
  "states" "{" names "}" ";";

category FieldType;
op ft_int  () : FieldType => "int";
op ft_bool () : FieldType => "bool";
op ft_str  () : FieldType => "str";
// `state` resolves to the enclosing resource's StateEnum.
op ft_state () : FieldType => "state";
op ft_set  (t : FieldType)          : FieldType => "set"  "[" t "]";
op ft_dict (k : FieldType, v : FieldType) : FieldType => "dict" "[" k "," v "]";

category FieldDecl;
op field_decl (name : Ident, ty : FieldType) : FieldDecl =>
  "field" name ":" ty ";";

category InitAssign;
op init_assign         (x : Ident, e : AExpr) : InitAssign => x ":=" e ";";
op init_empty_set      (x : Ident)            : InitAssign =>
  x ":=" "{" "}" ";";
op init_dict_const_int (x : Ident, n : Num)   : InitAssign =>
  x ":=" "dict_const" "(" n ")" ";";
op init_dict_const_str (x : Ident, s : Str)   : InitAssign =>
  x ":=" "dict_const" "(" s ")" ";";
op init_state_default  (x : Ident, n : Ident) : InitAssign =>
  x ":=" "dict_const" "(" n ")" ";";

category InitBlock;
op initial_block (assigns : Seq InitAssign) : InitBlock =>
  "initial" "{" assigns "}" ";";

category TypedParam;
op tp_int  (name : Ident) : TypedParam => name ":" "int";
op tp_bool (name : Ident) : TypedParam => name ":" "bool";
op tp_str  (name : Ident) : TypedParam => name ":" "str";

category ApiClause;
op clause_requires (e : AExpr) : ApiClause => "precondition" e ";";
op clause_ensures  (e : AExpr) : ApiClause => "postcondition"  e ";";
op clause_before   (e : AExpr) : ApiClause => "before" e ";";
op clause_after    (e : AExpr) : ApiClause => "after"  e ";";
// `transitions m[k] : Pre -> Post;` desugars (in `expandClause`) to
// a pre, a post, and a frame on every other key.
op clause_transitions
    (m : Ident, k : Ident, pre : Ident, post : Ident) : ApiClause =>
  "transitions" m "[" k "]" ":" pre " -> " post ";";

category ApiDecl;
op api_decl
    (name : Ident,
     params : CommaSepBy TypedParam,
     clauses : Seq ApiClause)
  : ApiDecl =>
    "api" name "(" params ")" clauses;

category InvariantDecl;
op invariant_decl (name : Ident, body : AExpr) : InvariantDecl =>
  "invariant" name ":" body ";";
op always_decl (name : Ident, body : AExpr) : InvariantDecl =>
  "always" name ":" body ";";

category InvariantsBlock;
op invariants_block (invs : Seq InvariantDecl) : InvariantsBlock =>
  "invariants" "{" invs "}" ";";

category ResourceDecl;
op resource_decl
    (name : Ident,
     states : StateList,
     fields : Seq FieldDecl,
     init : InitBlock)
  : ResourceDecl =>
    "resource" name "{" states fields init "}" ";";

// Stateless resource: an implicit `Active` state is added at lowering.
op resource_decl_nostates
    (name : Ident,
     fields : Seq FieldDecl,
     init : InitBlock)
  : ResourceDecl =>
    "resource" name "{" fields init "}" ";";

op service_cmd
    (name : Ident,
     resource : ResourceDecl,
     apis : Seq ApiDecl)
  : Command =>
    "service" name "{" resource apis "}" ";";

op service_cmd_inv
    (name : Ident,
     resource : ResourceDecl,
     apis : Seq ApiDecl,
     invariants : InvariantsBlock)
  : Command =>
    "service" name "{" resource apis invariants "}" ";";

category CallArgument;
op ca_num   (n : Num)   : CallArgument => @[prec(100)] n;
op ca_ident (x : Ident) : CallArgument => @[prec(100)] x;
op ca_true  ()          : CallArgument => @[prec(100)] "true";
op ca_false ()          : CallArgument => @[prec(100)] "false";
op ca_str   (s : Str)   : CallArgument => @[prec(100)] s;

op api_call (name : Ident, args : CommaSepBy CallArgument) : Command =>
  name "(" args ")" ";";

#end

namespace typestate
#strata_gen typestate
end typestate

end Strata
