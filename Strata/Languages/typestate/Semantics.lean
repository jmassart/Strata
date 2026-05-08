/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.typestate.DDMTransform.Parse

/-!
# Big-step reference semantics for typestate.
Independent of the Core translation; consumed by correctness proofs.
-/

public section

namespace Strata.typestate.Semantics

open Strata.typestate

inductive Value where
  | int   : Int → Value
  | bool  : Bool → Value
  | str   : String → Value
  | enum  : String → Value
  | set   : List String → Value
  | map1  : List (String × Value) → Value → Value
  | map2  : List (String × List (String × Value)) → Value → Value
  deriving Repr, Inhabited

namespace Value

partial def eq : Value → Value → Bool
  | .int a,    .int b    => a == b
  | .bool a,   .bool b   => a == b
  | .str a,    .str b    => a == b
  | .enum a,   .enum b   => a == b
  | .set a,    .set b    =>
    a.all (b.contains ·) && b.all (a.contains ·)
  | .map1 kvs1 d1, .map1 kvs2 d2 =>
    Value.eq d1 d2 &&
      (kvs1 ++ kvs2).all (fun ⟨k, _⟩ =>
        Value.eq
          ((kvs1.find? (·.fst == k)).map (·.snd) |>.getD d1)
          ((kvs2.find? (·.fst == k)).map (·.snd) |>.getD d2))
  | .map2 kvs1 d1, .map2 kvs2 d2 =>
    Value.eq d1 d2 &&
      (kvs1 ++ kvs2).all (fun ⟨k, _⟩ =>
        let inner1 : Value :=
          match kvs1.find? (·.fst == k) with
          | some ⟨_, v⟩ => .map1 v d1
          | none        => .map1 [] d1
        let inner2 : Value :=
          match kvs2.find? (·.fst == k) with
          | some ⟨_, v⟩ => .map1 v d2
          | none        => .map1 [] d2
        Value.eq inner1 inner2)
  | _, _ => false

instance : BEq Value := ⟨Value.eq⟩

@[simp] axiom Value.eq_int  (a b : Int)    : Value.eq (.int a) (.int b) = (a == b)
@[simp] axiom Value.eq_bool (a b : Bool)   : Value.eq (.bool a) (.bool b) = (a == b)
@[simp] axiom Value.eq_str  (a b : String) : Value.eq (.str a) (.str b) = (a == b)
@[simp] axiom Value.eq_enum (a b : String) : Value.eq (.enum a) (.enum b) = (a == b)
@[simp] axiom Value.eq_int_bool  (a : Int) (b : Bool)   : Value.eq (.int a) (.bool b) = false
@[simp] axiom Value.eq_int_str   (a : Int) (b : String) : Value.eq (.int a) (.str b) = false
@[simp] axiom Value.eq_int_enum  (a : Int) (b : String) : Value.eq (.int a) (.enum b) = false
@[simp] axiom Value.eq_bool_int  (a : Bool) (b : Int)   : Value.eq (.bool a) (.int b) = false
@[simp] axiom Value.eq_bool_str  (a : Bool) (b : String) : Value.eq (.bool a) (.str b) = false
@[simp] axiom Value.eq_bool_enum (a : Bool) (b : String) : Value.eq (.bool a) (.enum b) = false
@[simp] axiom Value.eq_str_int   (a : String) (b : Int)   : Value.eq (.str a) (.int b) = false
@[simp] axiom Value.eq_str_bool  (a : String) (b : Bool)  : Value.eq (.str a) (.bool b) = false
@[simp] axiom Value.eq_str_enum  (a b : String) : Value.eq (.str a) (.enum b) = false
@[simp] axiom Value.eq_enum_int  (a : String) (b : Int)   : Value.eq (.enum a) (.int b) = false
@[simp] axiom Value.eq_enum_bool (a : String) (b : Bool)  : Value.eq (.enum a) (.bool b) = false
@[simp] axiom Value.eq_enum_str  (a b : String) : Value.eq (.enum a) (.str b) = false

@[expose] def asInt  : Value → Option Int    | .int n => some n  | _ => none
@[expose] def asBool : Value → Option Bool   | .bool b => some b | _ => none
@[expose] def asStr  : Value → Option String | .str s => some s  | _ => none

@[expose] def index (container : Value) (key : String) : Option Value :=
  match container with
  | .set keys =>
    some (.bool (keys.contains key))
  | .map1 kvs d =>
    some ((kvs.find? (·.fst == key)).map (·.snd) |>.getD d)
  | .map2 kvs d =>
    match kvs.find? (·.fst == key) with
    | some ⟨_, row⟩ => some (.map1 row d)
    | none          => some (.map1 [] d)
  | _ => none

end Value

structure TypestateState where
  stateTags : List String
  vars      : List (String × Value)
  deriving Repr, Inhabited

namespace TypestateState

@[expose] def lookup (s : TypestateState) (name : String) : Option Value :=
  (s.vars.find? (·.fst == name)).map (·.snd)

def update (s : TypestateState) (name : String) (v : Value) : TypestateState :=
  let filtered := s.vars.filter (·.fst != name)
  { s with vars := (name, v) :: filtered }

@[expose] def isStateTag (s : TypestateState) (name : String) : Bool :=
  s.stateTags.contains name

end TypestateState

@[expose] def indexByIdent (s : TypestateState) (container : Value) (keyName : String) : Option Value := do
  let keyVal ← s.lookup keyName >>= Value.asStr
  Value.index container keyVal

@[expose] def evalAExpr {α : Type} (pre cur : TypestateState) : AExpr α → Option Value
  | .ae_num _ ⟨_, n⟩ => some (.int n)
  | .ae_str _ ⟨_, s⟩ => some (.str s)
  | .ae_true  _      => some (.bool true)
  | .ae_false _      => some (.bool false)
  | .ae_var _ ⟨_, x⟩ =>
    if cur.isStateTag x then some (.enum x)
    else cur.lookup x
  | .ae_paren _ a    => evalAExpr pre cur a
  | .ae_old _ ⟨_, x⟩ =>
    if pre.isStateTag x then some (.enum x) else pre.lookup x
  | .ae_old_idx1 _ ⟨_, x⟩ ⟨_, k⟩ => do
    let c ← pre.lookup x
    indexByIdent cur c k
  | .ae_old_idx1_str _ ⟨_, x⟩ ⟨_, k⟩ => do
    let c ← pre.lookup x
    Value.index c k
  | .ae_old_idx2 _ ⟨_, x⟩ ⟨_, b⟩ ⟨_, k⟩ => do
    let c     ← pre.lookup x
    let bVal  ← cur.lookup b >>= Value.asStr
    let kVal  ← cur.lookup k >>= Value.asStr
    let inner ← Value.index c bVal
    Value.index inner kVal
  | .ae_index1 _ ⟨_, m⟩ ⟨_, k⟩ => do
    let c ← cur.lookup m
    indexByIdent cur c k
  | .ae_index1_str _ ⟨_, m⟩ ⟨_, k⟩ => do
    let c ← cur.lookup m
    Value.index c k
  | .ae_index2 _ ⟨_, m⟩ ⟨_, b⟩ ⟨_, k⟩ => do
    let c     ← cur.lookup m
    let bVal  ← cur.lookup b >>= Value.asStr
    let kVal  ← cur.lookup k >>= Value.asStr
    let inner ← Value.index c bVal
    Value.index inner kVal
  | .ae_index2_ss _ ⟨_, m⟩ ⟨_, b⟩ ⟨_, k⟩ => do
    let c     ← cur.lookup m
    let inner ← Value.index c b
    Value.index inner k
  | .ae_not _ a => do
    let v ← evalAExpr pre cur a >>= Value.asBool
    return .bool !v
  | .ae_add _ a b => do
    let va ← evalAExpr pre cur a >>= Value.asInt
    let vb ← evalAExpr pre cur b >>= Value.asInt
    return .int (va + vb)
  | .ae_sub _ a b => do
    let va ← evalAExpr pre cur a >>= Value.asInt
    let vb ← evalAExpr pre cur b >>= Value.asInt
    return .int (va - vb)
  | .ae_eq _ a b => do
    let va ← evalAExpr pre cur a
    let vb ← evalAExpr pre cur b
    return .bool (va == vb)
  | .ae_ne _ a b => do
    let va ← evalAExpr pre cur a
    let vb ← evalAExpr pre cur b
    return .bool !(va == vb)
  | .ae_lt _ a b => do
    let va ← evalAExpr pre cur a >>= Value.asInt
    let vb ← evalAExpr pre cur b >>= Value.asInt
    return .bool (va < vb)
  | .ae_le _ a b => do
    let va ← evalAExpr pre cur a >>= Value.asInt
    let vb ← evalAExpr pre cur b >>= Value.asInt
    return .bool (va <= vb)
  | .ae_gt _ a b => do
    let va ← evalAExpr pre cur a >>= Value.asInt
    let vb ← evalAExpr pre cur b >>= Value.asInt
    return .bool (va > vb)
  | .ae_ge _ a b => do
    let va ← evalAExpr pre cur a >>= Value.asInt
    let vb ← evalAExpr pre cur b >>= Value.asInt
    return .bool (va >= vb)
  | .ae_in_id _ ⟨_, x⟩ ⟨_, s⟩ => do
    let xs ← cur.lookup x >>= Value.asStr
    let vs ← cur.lookup s
    match vs with
    | .set keys   => return .bool (keys.contains xs)
    | .map1 kvs _ => return .bool (kvs.any (·.fst == xs))
    | _ => none
  | .ae_in_str _ ⟨_, x⟩ ⟨_, s⟩ => do
    let vs ← cur.lookup s
    match vs with
    | .set keys   => return .bool (keys.contains x)
    | .map1 kvs _ => return .bool (kvs.any (·.fst == x))
    | _ => none
  | .ae_in_id_old _ ⟨_, x⟩ ⟨_, s⟩ => do
    let xs ← cur.lookup x >>= Value.asStr
    let vs ← pre.lookup s
    match vs with
    | .set keys   => return .bool (keys.contains xs)
    | .map1 kvs _ => return .bool (kvs.any (·.fst == xs))
    | _ => none
  | .ae_notin_id _ ⟨_, x⟩ ⟨_, s⟩ => do
    let xs ← cur.lookup x >>= Value.asStr
    let vs ← cur.lookup s
    match vs with
    | .set keys   => return .bool !(keys.contains xs)
    | .map1 kvs _ => return .bool !(kvs.any (·.fst == xs))
    | _ => none
  | .ae_notin_str _ ⟨_, x⟩ ⟨_, s⟩ => do
    let vs ← cur.lookup s
    match vs with
    | .set keys   => return .bool !(keys.contains x)
    | .map1 kvs _ => return .bool !(kvs.any (·.fst == x))
    | _ => none
  | .ae_and _ a b => do
    let va ← evalAExpr pre cur a >>= Value.asBool
    let vb ← evalAExpr pre cur b >>= Value.asBool
    return .bool (va && vb)
  | .ae_or _ a b => do
    let va ← evalAExpr pre cur a >>= Value.asBool
    let vb ← evalAExpr pre cur b >>= Value.asBool
    return .bool (va || vb)
  | .ae_implies _ a b => do
    let va ← evalAExpr pre cur a >>= Value.asBool
    let vb ← evalAExpr pre cur b >>= Value.asBool
    return .bool (!va || vb)
  | .ae_forall1 _ _ _   => none
  | .ae_forall2 _ _ _ _ => none
  | .ae_exists1 _ _ _   => none

@[simp]
theorem evalAExpr_forall1 {α : Type} (pre cur : TypestateState)
    (ann : α) (x : Ann String α) (body : AExpr α) :
    evalAExpr pre cur (.ae_forall1 ann x body) = none := rfl

@[simp]
theorem evalAExpr_forall2 {α : Type} (pre cur : TypestateState)
    (ann : α) (x y : Ann String α) (body : AExpr α) :
    evalAExpr pre cur (.ae_forall2 ann x y body) = none := rfl

@[simp]
theorem evalAExpr_exists1 {α : Type} (pre cur : TypestateState)
    (ann : α) (x : Ann String α) (body : AExpr α) :
    evalAExpr pre cur (.ae_exists1 ann x body) = none := rfl

inductive ClauseKind where | pre | post
  deriving Repr, DecidableEq

def clauseKind {α : Type} : ApiClause α → ClauseKind
  | .clause_requires .. | .clause_before .. => .pre
  | .clause_ensures  .. | .clause_after  .. => .post
  -- The transitions sugar is checked via Core lowering only.
  | .clause_transitions .. => .post

def clauseBody {α : Type} : ApiClause α → AExpr α
  | .clause_requires _ e | .clause_before _ e
  | .clause_ensures  _ e | .clause_after  _ e => e
  | .clause_transitions ann _ _ _ _ => .ae_true ann

def evalClause {α : Type} (pre post : TypestateState) (c : ApiClause α) : Option Bool := do
  let v ← (match clauseKind c with
    | .pre  => evalAExpr pre pre  (clauseBody c)
    | .post => evalAExpr pre post (clauseBody c))
  Value.asBool v

def preconditionsHold {α : Type} (pre : TypestateState) (clauses : Array (ApiClause α)) : Prop :=
  ∀ c ∈ clauses.toList,
    clauseKind c == .pre → evalClause pre pre c = some true

def postconditionsHold {α : Type} (pre post : TypestateState) (clauses : Array (ApiClause α)) : Prop :=
  ∀ c ∈ clauses.toList,
    clauseKind c == .post → evalClause pre post c = some true

def findApi {α : Type} (apis : Array (ApiDecl α)) (name : String) : Option (ApiDecl α) :=
  apis.find? (fun
    | .api_decl _ ⟨_, n⟩ _ _ => n == name)

def apiClauses {α : Type} : ApiDecl α → Array (ApiClause α)
  | .api_decl _ _ _ ⟨_, cs⟩ => cs

inductive StepApi {α : Type} (apis : Array (ApiDecl α)) (pre : TypestateState) :
    String → TypestateState → Prop where
  | step
      (name : String) (post : TypestateState) (decl : ApiDecl α)
      (hFind : findApi apis name = some decl)
      (hPre  : preconditionsHold  pre      (apiClauses decl))
      (hPost : postconditionsHold pre post (apiClauses decl)) :
      StepApi apis pre name post

inductive StepStar {α : Type} (apis : Array (ApiDecl α)) :
    TypestateState → List String → TypestateState → Prop where
  | nil  (s : TypestateState) : StepStar apis s [] s
  | cons (s s' sF : TypestateState) (nm : String) (rest : List String)
         (h1 : StepApi apis s nm s')
         (h2 : StepStar apis s' rest sF) :
      StepStar apis s (nm :: rest) sF

def RespectsContracts {α : Type}
    (apis : Array (ApiDecl α)) (init : TypestateState) (calls : List String) : Prop :=
  ∃ final : TypestateState, StepStar apis init calls final

def invariantBody {α : Type} : InvariantDecl α → AExpr α
  | .invariant_decl _ _ e => e
  | .always_decl    _ _ e => e

def invariantName {α : Type} : InvariantDecl α → String
  | .invariant_decl _ ⟨_, n⟩ _ => n
  | .always_decl    _ ⟨_, n⟩ _ => n

def InvariantHolds {α : Type} [Inhabited α] (s : TypestateState) (inv : InvariantDecl α) : Prop :=
  evalClause s s (.clause_ensures default (invariantBody inv)) = some true

def AllInvariants {α : Type} [Inhabited α] (invs : Array (InvariantDecl α)) (s : TypestateState) : Prop :=
  ∀ inv ∈ invs.toList, InvariantHolds s inv

def InvariantsPreservedOnce {α : Type} [Inhabited α]
    (apis : Array (ApiDecl α)) (invs : Array (InvariantDecl α)) : Prop :=
  ∀ s s' name,
    AllInvariants invs s →
    StepApi apis s name s' →
    AllInvariants invs s'

theorem invariants_by_induction {α : Type} [Inhabited α]
    (apis : Array (ApiDecl α)) (init : TypestateState) (invs : Array (InvariantDecl α))
    (hInit : AllInvariants invs init)
    (hPres : InvariantsPreservedOnce apis invs) :
    ∀ s calls, StepStar apis init calls s → AllInvariants invs s := by
  sorry

def InvariantsSound {α : Type} [Inhabited α]
    (apis : Array (ApiDecl α)) (init : TypestateState)
    (invs : Array (InvariantDecl α)) : Prop :=
  ∀ s calls, StepStar apis init calls s → AllInvariants invs s

def preconditionsHoldDec {α : Type} (pre : TypestateState) (clauses : Array (ApiClause α)) : Bool :=
  clauses.all (fun c =>
    match clauseKind c with
    | .pre  => evalClause pre pre c == some true
    | .post => true)

def postconditionsHoldDec {α : Type} (pre post : TypestateState) (clauses : Array (ApiClause α)) : Bool :=
  clauses.all (fun c =>
    match clauseKind c with
    | .post => evalClause pre post c == some true
    | .pre  => true)

end Strata.typestate.Semantics

end
