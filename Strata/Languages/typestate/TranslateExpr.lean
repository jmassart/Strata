/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.typestate.DDMTransform.Parse
public import Strata.Languages.Core.Factory
public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.Statement

/-! # typestate → Core AST-level expression translator. -/

public section

namespace Strata.typestate

open Strata.typestate
open Core (Expression CoreIdent Decl Statement Procedure)
open Imperative (MetaData ExprOrNondet)
open Lambda (LExpr LTy LMonoTy)

def stateNames {α : Type} : StateList α → List String
  | .states_decl _ ⟨_, names⟩ => names.toList.map (fun ⟨_, n⟩ => n)

@[expose] def mkVar (x : String) : Expression.Expr :=
  .fvar () ⟨x, ()⟩ none

@[expose] def mkOldVar (x : String) : Expression.Expr :=
  .fvar () (CoreIdent.mkOld x) none

@[expose] def mkStateCtorExpr (tag : String) : Expression.Expr :=
  .op () ⟨tag, ()⟩ none

@[expose] def mkTesterExpr (tag : String) (e : Expression.Expr) : Expression.Expr :=
  .app () (.op () ⟨"is" ++ tag, ()⟩ none) e

@[expose] def mkBinApp (op : Expression.Expr) (a b : Expression.Expr) : Expression.Expr :=
  .app () (.app () op a) b

@[expose] def mkSelect (m k : Expression.Expr) : Expression.Expr :=
  mkBinApp Core.mapSelectOp m k

@[expose] def resolveVar (bound : List String) (x : String) : Expression.Expr :=
  match bound.findIdx? (· == x) with
  | some idx => .bvar () idx
  | none     => mkVar x

@[simp] theorem resolveVar_nil (x : String) : resolveVar [] x = mkVar x := rfl

@[expose] def stateLitName {α : Type} (states : List String) : AExpr α → Option String
  | .ae_var _ ⟨_, x⟩ => if states.contains x then some x else none
  | _               => none

@[expose] def translateExpr {α : Type} (states : List String) (e : AExpr α) (bound : List String := []) : Expression.Expr :=
  match e with
  | .ae_num _ ⟨_, n⟩ => .intConst () n
  | .ae_str _ ⟨_, s⟩ => .strConst () s
  | .ae_true  _      => .boolConst () true
  | .ae_false _      => .boolConst () false
  | .ae_var _ ⟨_, x⟩ =>
    if states.contains x then mkStateCtorExpr x
    else resolveVar bound x
  | .ae_paren _ a => translateExpr states a (bound := bound)
  | .ae_old _ ⟨_, x⟩ =>
    if states.contains x then mkStateCtorExpr x
    else mkOldVar x
  | .ae_old_idx1 _ ⟨_, m⟩ ⟨_, k⟩ =>
    mkSelect (mkOldVar m) (resolveVar bound k)
  | .ae_old_idx1_str _ ⟨_, m⟩ ⟨_, k⟩ =>
    mkSelect (mkOldVar m) (.strConst () k)
  | .ae_old_idx2 _ ⟨_, m⟩ ⟨_, b⟩ ⟨_, k⟩ =>
    mkSelect (mkSelect (mkOldVar m) (resolveVar bound b)) (resolveVar bound k)
  | .ae_index1 _ ⟨_, m⟩ ⟨_, k⟩ =>
    mkSelect (mkVar m) (resolveVar bound k)
  | .ae_index1_str _ ⟨_, m⟩ ⟨_, k⟩ =>
    mkSelect (mkVar m) (.strConst () k)
  | .ae_index2 _ ⟨_, m⟩ ⟨_, b⟩ ⟨_, k⟩ =>
    mkSelect (mkSelect (mkVar m) (resolveVar bound b)) (resolveVar bound k)
  | .ae_index2_ss _ ⟨_, m⟩ ⟨_, b⟩ ⟨_, k⟩ =>
    mkSelect (mkSelect (mkVar m) (.strConst () b)) (.strConst () k)
  | .ae_not _ a => .app () Core.boolNotOp (translateExpr states a (bound := bound))
  | .ae_add _ a b => mkBinApp Core.intAddOp (translateExpr states a (bound := bound)) (translateExpr states b (bound := bound))
  | .ae_sub _ a b => mkBinApp Core.intSubOp (translateExpr states a (bound := bound)) (translateExpr states b (bound := bound))
  -- State literal on either side → StateEnum tester; else Core equality.
  | .ae_eq _ a b =>
    match stateLitName states a, stateLitName states b with
    | _, some tag => mkTesterExpr tag (translateExpr states a (bound := bound))
    | some tag, _ => mkTesterExpr tag (translateExpr states b (bound := bound))
    | _, _        => .eq () (translateExpr states a (bound := bound)) (translateExpr states b (bound := bound))
  | .ae_ne _ a b =>
    .app () Core.boolNotOp <|
      match stateLitName states a, stateLitName states b with
      | _, some tag => mkTesterExpr tag (translateExpr states a (bound := bound))
      | some tag, _ => mkTesterExpr tag (translateExpr states b (bound := bound))
      | _, _        => .eq () (translateExpr states a (bound := bound)) (translateExpr states b (bound := bound))
  | .ae_lt _ a b => mkBinApp Core.intLtOp (translateExpr states a (bound := bound)) (translateExpr states b (bound := bound))
  | .ae_le _ a b => mkBinApp Core.intLeOp (translateExpr states a (bound := bound)) (translateExpr states b (bound := bound))
  | .ae_gt _ a b => mkBinApp Core.intGtOp (translateExpr states a (bound := bound)) (translateExpr states b (bound := bound))
  | .ae_ge _ a b => mkBinApp Core.intGeOp (translateExpr states a (bound := bound)) (translateExpr states b (bound := bound))
  | .ae_in_id _ ⟨_, x⟩ ⟨_, s⟩ => mkSelect (mkVar s) (resolveVar bound x)
  | .ae_in_str _ ⟨_, x⟩ ⟨_, s⟩ => mkSelect (mkVar s) (.strConst () x)
  | .ae_in_id_old _ ⟨_, x⟩ ⟨_, s⟩ => mkSelect (mkOldVar s) (resolveVar bound x)
  | .ae_notin_id _ ⟨_, x⟩ ⟨_, s⟩ =>
    .app () Core.boolNotOp (mkSelect (mkVar s) (resolveVar bound x))
  | .ae_notin_str _ ⟨_, x⟩ ⟨_, s⟩ =>
    .app () Core.boolNotOp (mkSelect (mkVar s) (.strConst () x))
  | .ae_and _ a b => mkBinApp Core.boolAndOp (translateExpr states a (bound := bound)) (translateExpr states b (bound := bound))
  | .ae_or _ a b => mkBinApp Core.boolOrOp (translateExpr states a (bound := bound)) (translateExpr states b (bound := bound))
  | .ae_implies _ a b => mkBinApp Core.boolImpliesOp (translateExpr states a (bound := bound)) (translateExpr states b (bound := bound))
  | .ae_forall1 _ ⟨_, x⟩ body =>
    .quant () .all x (some (LMonoTy.tcons "string" []))
      (.bvar () 0) (translateExpr states body (bound := x :: bound))
  | .ae_forall2 _ ⟨_, x⟩ ⟨_, y⟩ body =>
    .quant () .all x (some (LMonoTy.tcons "string" []))
      (.bvar () 0)
      (.quant () .all y (some (LMonoTy.tcons "string" []))
        (.bvar () 0) (translateExpr states body (bound := y :: x :: bound)))
  | .ae_exists1 _ ⟨_, x⟩ body =>
    .quant () .exist x (some (LMonoTy.tcons "string" []))
      (.bvar () 0) (translateExpr states body (bound := x :: bound))

def translateFieldType {α : Type} : FieldType α → Lambda.LMonoTy
  | .ft_int  _    => .tcons "int"    []
  | .ft_bool _    => .tcons "bool"   []
  | .ft_str  _    => .tcons "string" []
  | .ft_state _   => .tcons "StateEnum" []
  | .ft_set  _ _  => .tcons "Map" [.tcons "string" [], .tcons "bool" []]
  | .ft_dict _ k v =>
    .tcons "Map" [translateFieldType k, translateFieldType v]

def fieldType {α : Type} : FieldDecl α → Lambda.LMonoTy
  | .field_decl _ _ ty => translateFieldType ty

def fieldName {α : Type} : FieldDecl α → String
  | .field_decl _ ⟨_, n⟩ _ => n

def paramIdent {α : Type} : TypedParam α → CoreIdent × Lambda.LMonoTy
  | .tp_int  _ ⟨_, n⟩ => (⟨n, ()⟩, .tcons "int" [])
  | .tp_bool _ ⟨_, n⟩ => (⟨n, ()⟩, .tcons "bool" [])
  | .tp_str  _ ⟨_, n⟩ => (⟨n, ()⟩, .tcons "string" [])

private def noMeta : MetaData Expression := default
private def mkId (s : String) : CoreIdent := ⟨s, ()⟩

def translateStateEnum {α : Type} (sl : StateList α) : Lambda.LDatatype Unit :=
  let names := stateNames sl
  { name := "StateEnum"
    typeArgs := []
    constrs := names.map fun n => { name := mkId n, args := [] }
    constrs_ne := sorry }

def translateGlobals {α : Type} (fields : Array (FieldDecl α)) : List Core.Decl :=
  let stateVar := Decl.var (mkId "state")
    (LTy.forAll [] (.tcons "StateEnum" []))
    .nondet noMeta
  let fieldVars := fields.toList.map fun fd =>
    Decl.var (mkId (fieldName fd)) (LTy.forAll [] (fieldType fd)) .nondet noMeta
  stateVar :: fieldVars

def modifiesIdents {α : Type} (fields : Array (FieldDecl α)) : List CoreIdent :=
  mkId "state" :: fields.toList.map (fun fd => mkId (fieldName fd))

private def stringTy : Lambda.LMonoTy := .tcons "string" []

private def forallKey (body : Expression.Expr) : Expression.Expr :=
  .quant () .all "k" (some stringTy) (.bvar () 0) body

def fieldTypeOf {α : Type} (fields : Array (FieldDecl α)) (name : String) : Option (FieldType α) :=
  (fields.toList.filterMap fun
    | .field_decl _ ⟨_, n⟩ ty => if n == name then some ty else none).head?

def translateInitEnsures {α : Type} (states : List String)
    (fields : Array (FieldDecl α)) :
    InitAssign α → Expression.Expr
  | .init_assign _ ⟨_, x⟩ e =>
    .eq () (mkVar x) (translateExpr states e)
  | .init_empty_set _ ⟨_, x⟩ =>
    forallKey (.app () Core.boolNotOp (mkSelect (mkVar x) (.bvar () 0)))
  | .init_dict_const_int _ ⟨_, x⟩ ⟨_, n⟩ =>
    forallKey (.eq () (mkSelect (mkVar x) (.bvar () 0)) (.intConst () n))
  | .init_dict_const_str _ ⟨_, x⟩ ⟨_, s⟩ =>
    -- 2-level dict needs `forall b k :: x[b][k] == s`; 1-level uses one binder.
    match fieldTypeOf fields x with
    | some (.ft_dict _ _ (.ft_dict ..)) =>
      .quant () .all "b" (some stringTy) (.bvar () 0) <|
        forallKey
          (.eq () (mkSelect (mkSelect (mkVar x) (.bvar () 1)) (.bvar () 0)) (.strConst () s))
    | _ =>
      forallKey (.eq () (mkSelect (mkVar x) (.bvar () 0)) (.strConst () s))
  | .init_state_default _ ⟨_, x⟩ ⟨_, n⟩ =>
    forallKey (mkTesterExpr n (mkSelect (mkVar x) (.bvar () 0)))

def translateInitProcedure {α : Type} (svcName : String) (states : List String)
    (init : InitBlock α) (fields : Array (FieldDecl α)) : Procedure :=
  let initEnsures := match init with
    | .initial_block _ ⟨_, assigns⟩ =>
      assigns.toList.map fun a =>
        ("", ({ expr := translateInitEnsures states fields a } : Procedure.Check))
  { header := { name := mkId s!"init_{svcName}", typeArgs := [], inputs := [], outputs := [] }
    spec := { modifies := modifiesIdents fields, preconditions := [],
              postconditions := initEnsures }
    body := [] }

def translateInitProcedureWithInvariants {α : Type} (svcName : String) (states : List String)
    (init : InitBlock α) (fields : Array (FieldDecl α))
    (invs : List (String × AExpr α)) : Procedure :=
  let initAssumes : List Core.Statement := match init with
    | .initial_block _ ⟨_, assigns⟩ =>
      assigns.toList.mapIdx fun i a =>
        Statement.assume s!"init_{i}" (translateInitEnsures states fields a) noMeta
  let invEnsures : ListMap Core.CoreLabel Procedure.Check :=
    invs.map fun (nm, body) =>
      (s!"invariant_{nm}_init", ({ expr := translateExpr states body } : Procedure.Check))
  { header := { name := mkId s!"init_{svcName}", typeArgs := [], inputs := [], outputs := [] }
    spec := { modifies := modifiesIdents fields, preconditions := [],
              postconditions := invEnsures }
    body := initAssumes }

abbrev IsPre := Bool

/-- Flatten an `ApiClause` into one or more `(IsPre, Expr)` checks.
    The `transitions m[k] : Pre -> Post;` sugar expands
    into a precondition `m[k] == Pre`, a postcondition `m[k] == Post`,
    and a frame asserting every other key of `m` is unchanged. -/
def expandClause {α : Type} (states : List String) :
    ApiClause α → List (IsPre × Expression.Expr)
  | .clause_requires _ e => [(true,  translateExpr states e)]
  | .clause_before   _ e => [(true,  translateExpr states e)]
  | .clause_ensures  _ e => [(false, translateExpr states e)]
  | .clause_after    _ e => [(false, translateExpr states e)]
  | .clause_transitions _ ⟨_, m⟩ ⟨_, k⟩ ⟨_, pre⟩ ⟨_, post⟩ =>
    let sel := mkSelect (mkVar m) (mkVar k)
    let frame :=
      forallKey <|
        mkBinApp Core.boolOrOp
          (.eq () (.bvar () 0) (mkVar k))
          (.eq () (mkSelect (mkVar m) (.bvar () 0))
                  (mkSelect (mkOldVar m) (.bvar () 0)))
    [(true, mkTesterExpr pre sel), (false, mkTesterExpr post sel), (false, frame)]

def translateApiProcedure {α : Type} (svcName : String) (states : List String)
    (fields : Array (FieldDecl α)) : ApiDecl α → Procedure
  | .api_decl _ ⟨_, name⟩ ⟨_, params⟩ ⟨_, clauses⟩ =>
    let inputs := params.toList.map paramIdent
    let expanded := clauses.toList.flatMap (expandClause states)
    let pres := (expanded.filter (·.fst)).map fun (_, e) =>
      ("", ({ expr := e } : Procedure.Check))
    let posts := (expanded.filter (!·.fst)).map fun (_, e) =>
      ("", ({ expr := e } : Procedure.Check))
    { header := { name := mkId s!"{svcName}_{name}", typeArgs := [], inputs := inputs, outputs := [] }
      spec := { modifies := modifiesIdents fields, preconditions := pres, postconditions := posts }
      body := [] }

/-- One preservation check per (API, invariant): assume the invariant
    on entry, havoc modifies, assume postconditions, recheck on exit. -/
def translateInvariantPreservationProc {α : Type}
    (svcName : String) (states : List String)
    (fields : Array (FieldDecl α))
    (invName : String) (invBody : AExpr α)
    (api : ApiDecl α) : Procedure :=
  match api with
  | .api_decl _ ⟨_, apiName⟩ ⟨_, params⟩ ⟨_, clauses⟩ =>
    let inputs := params.toList.map paramIdent
    let expanded := clauses.toList.flatMap (expandClause states)
    let apiPres : ListMap Core.CoreLabel Procedure.Check :=
      (expanded.filter (·.fst)).mapIdx fun i (_, e) =>
        (s!"api_req_{i}", ({ expr := e } : Procedure.Check))
    let apiPostAssumes : List Core.Statement :=
      (expanded.filter (!·.fst)).mapIdx fun i (_, e) =>
        Statement.assume s!"api_ens_{i}" e noMeta
    let havocs : List Core.Statement :=
      (modifiesIdents fields).map fun x => Statement.havoc x noMeta
    let invCheck : Procedure.Check := { expr := translateExpr states invBody }
    let pres : ListMap Core.CoreLabel Procedure.Check :=
      (s!"invariant_{invName}_holds_on_entry_{apiName}", invCheck) :: apiPres
    { header := { name := mkId s!"check_{svcName}_{apiName}_preserves_{invName}",
                  typeArgs := [], inputs := inputs, outputs := [] }
      spec := { modifies := modifiesIdents fields,
                preconditions := pres,
                postconditions := [(s!"{apiName}_preserves_{invName}", invCheck)] }
      body := havocs ++ apiPostAssumes }

def translateCallArg {α : Type} : CallArgument α → Expression.Expr
  | .ca_num   _ ⟨_, n⟩ => .intConst () n
  | .ca_ident _ ⟨_, x⟩ => mkVar x
  | .ca_true  _        => .boolConst () true
  | .ca_false _        => .boolConst () false
  | .ca_str   _ ⟨_, s⟩ => .strConst () s

def extractInvariants {α : Type} : InvariantsBlock α → List (String × AExpr α)
  | .invariants_block _ ⟨_, invs⟩ =>
    invs.toList.map fun
      | .invariant_decl _ ⟨_, nm⟩ body => (nm, body)
      | .always_decl    _ ⟨_, nm⟩ body => (nm, body)

/-- Stateless resources synthesize a single implicit `Active` state. -/
def extractResource {α : Type} (rd : ResourceDecl α) :
    List String × Array (FieldDecl α) × InitBlock α :=
  match rd with
  | .resource_decl _ _ stList ⟨_, fields⟩ init =>
    (stateNames stList, fields, init)
  | .resource_decl_nostates _ _ ⟨_, fields⟩ init =>
    (["Active"], fields, init)

def mkStateEnum (names : List String) : Lambda.LDatatype Unit :=
  { name := "StateEnum"
    typeArgs := []
    constrs := names.map fun n => { name := mkId n, args := [] }
    constrs_ne := sorry }

def translateService {α : Type} : Command α → Option (String × List String × List Core.Decl)
  | .service_cmd _ ⟨_, name⟩ resource ⟨_, apis⟩ =>
    translateServiceCore name (extractResource resource) apis
  | .service_cmd_inv _ ⟨_, name⟩ resource ⟨_, apis⟩ _invariants =>
    -- Invariants are checked by `translateToInvariantChecker`, not here.
    translateServiceCore name (extractResource resource) apis
  | _ => none
where
  translateServiceCore {α : Type} (name : String)
      (resourceParts : List String × Array (FieldDecl α) × InitBlock α)
      (apis : Array (ApiDecl α)) :
      Option (String × List String × List Core.Decl) :=
    let (states, fields, init) := resourceParts
    let enumDecl := Core.Decl.type (Core.TypeDecl.data [mkStateEnum states]) noMeta
    let globals := translateGlobals fields
    let initProc := Decl.proc (translateInitProcedure name states init fields) noMeta
    let apiProcs := apis.toList.map fun api =>
      Decl.proc (translateApiProcedure name states fields api) noMeta
    some (name, states, [enumDecl] ++ globals ++ [initProc] ++ apiProcs)

def translateApiCall {α : Type} (svcName : String) : Command α → Option Core.Statement
  | .api_call _ ⟨_, name⟩ ⟨_, args⟩ =>
    let a := args.toList.map translateCallArg
    some (Statement.call [] s!"{svcName}_{name}" a noMeta)
  | _ => none

def translateToProgram (ops : Array Operation)
    : Except String (Core.Program × List String) := do
  let cmds ← ops.toList.mapM Command.ofAst
  let mut decls : List Core.Decl := []
  let mut svcName : Option String := none
  for c in cmds do
    match translateService c with
    | some (n, _, ds) =>
      decls := decls ++ ds
      if svcName.isNone then svcName := some n
    | none => pure ()
  let svc ← match svcName with
    | some n => .ok n
    | none   => .error "typestate: no `service` declaration found"
  let callStmts := cmds.filterMap (translateApiCall svc)
  let initCall := Statement.call [] s!"init_{svc}" [] noMeta
  let verifyProc := Decl.proc
    { header := { name := mkId "verify_main", typeArgs := [], inputs := [], outputs := [] }
      spec := { modifies := [], preconditions := [], postconditions := [] }
      body := initCall :: callStmts }
    noMeta
  .ok ({ decls := decls ++ [verifyProc] }, ["verify_main"])

/-! Invariant-checker pipeline: verifies service-level invariants
    against the spec alone (no user program), one obligation per
    (init, invariant) and (api, invariant) pair. -/

def translateServiceToInvariantChecker {α : Type} :
    Command α → Option (String × List String × List Core.Decl)
  | .service_cmd_inv _ ⟨_, name⟩ resource ⟨_, apis⟩ invariants =>
    let (states, fields, init) := extractResource resource
    let invs := extractInvariants invariants
    let enumDecl := Core.Decl.type (Core.TypeDecl.data [mkStateEnum states]) noMeta
    let globals := translateGlobals fields
    let initProc := Decl.proc
      (translateInitProcedureWithInvariants name states init fields invs) noMeta
    let preservationProcs : List Core.Decl :=
      apis.toList.flatMap fun api =>
        invs.map fun (invName, invBody) =>
          Decl.proc
            (translateInvariantPreservationProc name states fields invName invBody api)
            noMeta
    some (name, states, [enumDecl] ++ globals ++ [initProc] ++ preservationProcs)
  | _ => none

def translateToInvariantChecker (ops : Array Operation)
    : Except String Core.Program := do
  let cmds ← ops.toList.mapM Command.ofAst
  match cmds.findSome? translateServiceToInvariantChecker with
  | some (_, _, decls) => .ok { decls := decls }
  | none => .error "typestate: no `service` with `invariants { ... }` block found"

end Strata.typestate

end
