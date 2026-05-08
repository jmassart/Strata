/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.typestate.TranslateExpr

/-! Axiomatic interface to Core's evaluator. -/

public section

namespace Strata.typestate.CoreEvalProps

open Core (Expression CoreIdent)

abbrev CoreStore := Expression.Ident → Option Expression.Expr
abbrev CoreEval := CoreStore → Expression.Expr → Option Expression.Expr


axiom eval_intConst (δ : CoreEval) (σ : CoreStore) (n : Int) :
    δ σ (.intConst () n) = some (.intConst () n)

axiom eval_strConst (δ : CoreEval) (σ : CoreStore) (s : String) :
    δ σ (.strConst () s) = some (.strConst () s)

axiom eval_boolConst (δ : CoreEval) (σ : CoreStore) (b : Bool) :
    δ σ (.boolConst () b) = some (.boolConst () b)


axiom eval_fvar (δ : CoreEval) (σ : CoreStore) (x : CoreIdent) :
    δ σ (.fvar () x none) = σ x


axiom eval_stateCtor (δ : CoreEval) (σ : CoreStore) (tag : String) :
    δ σ (mkStateCtorExpr tag) = some (mkStateCtorExpr tag)

axiom eval_stateTester (δ : CoreEval) (σ : CoreStore) (tag : String) (e v : Expression.Expr) :
    δ σ e = some v →
    δ σ (mkTesterExpr tag e) = some (.boolConst () (v == mkStateCtorExpr tag))


axiom eval_intAdd (δ : CoreEval) (σ : CoreStore) (a b : Expression.Expr) (na nb : Int) :
    δ σ a = some (.intConst () na) → δ σ b = some (.intConst () nb) →
    δ σ (mkBinApp Core.intAddOp a b) = some (.intConst () (na + nb))

axiom eval_intSub (δ : CoreEval) (σ : CoreStore) (a b : Expression.Expr) (na nb : Int) :
    δ σ a = some (.intConst () na) → δ σ b = some (.intConst () nb) →
    δ σ (mkBinApp Core.intSubOp a b) = some (.intConst () (na - nb))


axiom eval_intLt (δ : CoreEval) (σ : CoreStore) (a b : Expression.Expr) (na nb : Int) :
    δ σ a = some (.intConst () na) → δ σ b = some (.intConst () nb) →
    δ σ (mkBinApp Core.intLtOp a b) = some (.boolConst () (na < nb))

axiom eval_intLe (δ : CoreEval) (σ : CoreStore) (a b : Expression.Expr) (na nb : Int) :
    δ σ a = some (.intConst () na) → δ σ b = some (.intConst () nb) →
    δ σ (mkBinApp Core.intLeOp a b) = some (.boolConst () (na <= nb))

axiom eval_intGt (δ : CoreEval) (σ : CoreStore) (a b : Expression.Expr) (na nb : Int) :
    δ σ a = some (.intConst () na) → δ σ b = some (.intConst () nb) →
    δ σ (mkBinApp Core.intGtOp a b) = some (.boolConst () (na > nb))

axiom eval_intGe (δ : CoreEval) (σ : CoreStore) (a b : Expression.Expr) (na nb : Int) :
    δ σ a = some (.intConst () na) → δ σ b = some (.intConst () nb) →
    δ σ (mkBinApp Core.intGeOp a b) = some (.boolConst () (na >= nb))

axiom eval_eq (δ : CoreEval) (σ : CoreStore) (a b va vb : Expression.Expr) :
    δ σ a = some va → δ σ b = some vb →
    δ σ (.eq () a b) = some (.boolConst () (va == vb))


axiom eval_boolNot (δ : CoreEval) (σ : CoreStore) (a : Expression.Expr) (ba : Bool) :
    δ σ a = some (.boolConst () ba) →
    δ σ (.app () Core.boolNotOp a) = some (.boolConst () !ba)

axiom eval_boolAnd (δ : CoreEval) (σ : CoreStore) (a b : Expression.Expr) (ba bb : Bool) :
    δ σ a = some (.boolConst () ba) → δ σ b = some (.boolConst () bb) →
    δ σ (mkBinApp Core.boolAndOp a b) = some (.boolConst () (ba && bb))

axiom eval_boolOr (δ : CoreEval) (σ : CoreStore) (a b : Expression.Expr) (ba bb : Bool) :
    δ σ a = some (.boolConst () ba) → δ σ b = some (.boolConst () bb) →
    δ σ (mkBinApp Core.boolOrOp a b) = some (.boolConst () (ba || bb))

axiom eval_boolImplies (δ : CoreEval) (σ : CoreStore) (a b : Expression.Expr) (ba bb : Bool) :
    δ σ a = some (.boolConst () ba) → δ σ b = some (.boolConst () bb) →
    δ σ (mkBinApp Core.boolImpliesOp a b) = some (.boolConst () (!ba || bb))


axiom eval_mapSelect (δ : CoreEval) (σ : CoreStore) (m k vm vk : Expression.Expr) :
    δ σ m = some vm → δ σ k = some vk →
    δ σ (mkSelect m k) = δ σ (mkSelect vm vk)

end Strata.typestate.CoreEvalProps

end
