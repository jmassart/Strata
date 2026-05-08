/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.typestate.Semantics
public import Strata.Languages.typestate.CoreEvalProps

/-! typestate → Core translation correctness, AST-level. -/

public section

namespace Strata.typestate.Correctness
set_option linter.unusedSimpArgs false

open Strata.typestate Strata.typestate.Semantics
open Strata.typestate.CoreEvalProps
open Core (Expression CoreIdent)

def Value.toCore : Value → Expression.Expr
  | .int n    => .intConst () n
  | .bool b   => .boolConst () b
  | .str s    => .strConst () s
  | .enum tag => mkStateCtorExpr tag
  | .set _    => .intConst () 0
  | .map1 _ _ => .intConst () 0
  | .map2 _ _ => .intConst () 0

inductive ValueEquiv (δ : CoreEval) (σ : CoreStore) : Value → Expression.Expr → Prop where
  | int  : ValueEquiv δ σ (.int n)    (.intConst () n)
  | bool : ValueEquiv δ σ (.bool b)   (.boolConst () b)
  | str  : ValueEquiv δ σ (.str s)    (.strConst () s)
  | enum : ValueEquiv δ σ (.enum tag) (mkStateCtorExpr tag)
  | set  : (∀ k : String,
              δ σ (mkSelect ce (.strConst () k)) =
                some (.boolConst () (keys.contains k))) →
           ValueEquiv δ σ (.set keys) ce
  | map1 : (witness : String → Expression.Expr) →
           (∀ k, δ σ (mkSelect ce (.strConst () k)) = some (witness k)) →
           (∀ k, ValueEquiv δ σ
              ((kvs.find? (·.fst == k)).map (·.snd) |>.getD d) (witness k)) →
           ValueEquiv δ σ (.map1 kvs d) ce
  | map2 : (witness : String → Expression.Expr) →
           (∀ k, δ σ (mkSelect ce (.strConst () k)) = some (witness k)) →
           (∀ k, ValueEquiv δ σ
              (match kvs.find? (·.fst == k) with
               | some ⟨_, row⟩ => .map1 row d
               | none          => .map1 [] d) (witness k)) →
           ValueEquiv δ σ (.map2 kvs d) ce

def StoreEquiv (δ : CoreEval) (s : TypestateState) (σ : CoreStore) : Prop :=
  ∀ x : String, match s.lookup x with
    | some v => ∃ ce, σ ⟨x, ()⟩ = some ce ∧ ValueEquiv δ σ v ce
    | none   => σ ⟨x, ()⟩ = none

def OldStoreEquiv (δ : CoreEval) (s : TypestateState) (σ : CoreStore) : Prop :=
  ∀ x : String, match s.lookup x with
    | some v => ∃ ce, σ (CoreIdent.mkOld x) = some ce ∧ ValueEquiv δ σ v ce
    | none   => σ (CoreIdent.mkOld x) = none

def StateTagsCoherent (states : List String) (s : TypestateState) : Prop :=
  ∀ x : String, s.isStateTag x = states.contains x

def ExprEquiv (δ : CoreEval) (states : List String)
    (pre cur : TypestateState) (σ : CoreStore)
    {α : Type} (e : AExpr α) : Prop :=
  match evalAExpr pre cur e with
  | some v => ∃ ce, δ σ (translateExpr states e) = some ce ∧ ValueEquiv δ σ v ce
  | none   => True

theorem quant_forall1_equiv δ states pre cur σ (ann : α) x body :
    ExprEquiv δ states pre cur σ (.ae_forall1 ann x body) := by
  unfold ExprEquiv; simp [evalAExpr_forall1]
theorem quant_forall2_equiv δ states pre cur σ (ann : α) x y body :
    ExprEquiv δ states pre cur σ (.ae_forall2 ann x y body) := by
  unfold ExprEquiv; simp [evalAExpr_forall2]
theorem quant_exists1_equiv δ states pre cur σ (ann : α) x body :
    ExprEquiv δ states pre cur σ (.ae_exists1 ann x body) := by
  unfold ExprEquiv; simp [evalAExpr_exists1]

theorem atom_num_equiv δ states pre cur σ (ann : α) (n : Ann Nat α) :
    ExprEquiv δ states pre cur σ (.ae_num ann n) := by
  unfold ExprEquiv; simp [evalAExpr, translateExpr]; exact ⟨_, eval_intConst δ σ n.val, .int⟩
theorem atom_str_equiv δ states pre cur σ (ann : α) (s : Ann String α) :
    ExprEquiv δ states pre cur σ (.ae_str ann s) := by
  unfold ExprEquiv; simp [evalAExpr, translateExpr]; exact ⟨_, eval_strConst δ σ s.val, .str⟩
theorem atom_true_equiv δ states pre cur σ (ann : α) :
    ExprEquiv δ states pre cur σ (.ae_true ann) := by
  unfold ExprEquiv; simp [evalAExpr, translateExpr]; exact ⟨_, eval_boolConst δ σ true, .bool⟩
theorem atom_false_equiv δ states pre cur σ (ann : α) :
    ExprEquiv δ states pre cur σ (.ae_false ann) := by
  unfold ExprEquiv; simp [evalAExpr, translateExpr]; exact ⟨_, eval_boolConst δ σ false, .bool⟩
theorem atom_paren_equiv δ states pre cur σ (ann : α) (a : AExpr α)
    (ih : ExprEquiv δ states pre cur σ a) :
    ExprEquiv δ states pre cur σ (.ae_paren ann a) := by
  unfold ExprEquiv at ih ⊢; simp [evalAExpr, translateExpr]; exact ih

theorem atom_var_equiv δ states pre cur σ (ann : α)
    (hCur : StoreEquiv δ cur σ) (hTags : StateTagsCoherent states cur)
    (x : Ann String α) :
    ExprEquiv δ states pre cur σ (.ae_var ann x) := by
  unfold ExprEquiv; simp only [evalAExpr, translateExpr]; rw [hTags x.val]
  match hst : states.contains x.val with
  | true => simp; exact ⟨_, eval_stateCtor δ σ x.val, .enum⟩
  | false =>
    simp; match hlook : cur.lookup x.val with
    | none => simp
    | some v =>
      have hx := hCur x.val; rw [hlook] at hx; obtain ⟨ce, hσ, hve⟩ := hx
      exact ⟨ce, by simp [eval_fvar, mkVar, hσ], hve⟩

theorem old_bare_equiv δ states pre cur σ (ann : α)
    (hOld : OldStoreEquiv δ pre σ) (hTags : StateTagsCoherent states pre)
    (x : Ann String α) :
    ExprEquiv δ states pre cur σ (.ae_old ann x) := by
  unfold ExprEquiv; simp only [evalAExpr, translateExpr]; rw [hTags x.val]
  match hst : states.contains x.val with
  | true => simp; exact ⟨_, eval_stateCtor δ σ x.val, .enum⟩
  | false =>
    simp; match hlook : pre.lookup x.val with
    | none => simp
    | some v =>
      have hx := hOld x.val; rw [hlook] at hx; obtain ⟨ce, hσ, hve⟩ := hx
      exact ⟨ce, by simp [eval_fvar, mkOldVar, hσ], hve⟩

theorem arith_not_equiv δ states pre cur σ (ann : α) (a : AExpr α)
    (ih : ExprEquiv δ states pre cur σ a) :
    ExprEquiv δ states pre cur σ (.ae_not ann a) := by
  unfold ExprEquiv at ih ⊢; simp only [evalAExpr, translateExpr]
  match ha : evalAExpr pre cur a with
  | none => simp [bind, Option.bind]
  | some va =>
    rw [ha] at ih; simp [bind, Option.bind]
    cases va <;> simp [Value.asBool] <;> try trivial
    case bool ba => obtain ⟨ce, hce, hve⟩ := ih; cases hve; exact ⟨_, eval_boolNot δ σ _ ba hce, .bool⟩

private theorem int_binop {δ : CoreEval} {states} {pre cur : TypestateState} {σ : CoreStore}
    {a b : AExpr α} (iha : ExprEquiv δ states pre cur σ a) (ihb : ExprEquiv δ states pre cur σ b)
    {op} {f : Int → Int → α'} (mk : α' → Value) (mkC : α' → Expression.Expr)
    (mkV : ∀ x, ValueEquiv δ σ (mk x) (mkC x))
    (hax : ∀ ea eb na nb, δ σ ea = some (.intConst () na) → δ σ eb = some (.intConst () nb) →
      δ σ (mkBinApp op ea eb) = some (mkC (f na nb))) :
    (match (do let va ← evalAExpr pre cur a >>= Value.asInt; let vb ← evalAExpr pre cur b >>= Value.asInt; pure (mk (f va vb))) with
     | some v => ∃ ce, δ σ (mkBinApp op (translateExpr states a) (translateExpr states b)) = some ce ∧ ValueEquiv δ σ v ce
     | none => True) := by
  unfold ExprEquiv at iha ihb
  match ha : evalAExpr pre cur a, hb : evalAExpr pre cur b with
  | some va, some vb =>
    rw [ha] at iha; rw [hb] at ihb; simp [bind, Option.bind]
    cases va <;> simp [Value.asInt] <;> try trivial
    case int na => cases vb <;> simp [Value.asInt] <;> try trivial
                   case int nb => obtain ⟨a', ha', va'⟩ := iha; obtain ⟨b', hb', vb'⟩ := ihb
                                  cases va'; cases vb'; exact ⟨_, hax _ _ na nb ha' hb', mkV _⟩
  | some va, none => simp [bind, Option.bind]; cases va <;> simp [Value.asInt]
  | none, _ => simp [bind, Option.bind]

theorem arith_add_equiv δ states pre cur σ (ann : α) (a b : AExpr α)
    (iha : ExprEquiv δ states pre cur σ a) (ihb : ExprEquiv δ states pre cur σ b) :
    ExprEquiv δ states pre cur σ (.ae_add ann a b) := by
  unfold ExprEquiv; simp only [evalAExpr, translateExpr]
  exact int_binop iha ihb (.int ·) (.intConst () ·) (fun _ => .int) (eval_intAdd δ σ)
theorem arith_sub_equiv δ states pre cur σ (ann : α) (a b : AExpr α)
    (iha : ExprEquiv δ states pre cur σ a) (ihb : ExprEquiv δ states pre cur σ b) :
    ExprEquiv δ states pre cur σ (.ae_sub ann a b) := by
  unfold ExprEquiv; simp only [evalAExpr, translateExpr]
  exact int_binop iha ihb (.int ·) (.intConst () ·) (fun _ => .int) (eval_intSub δ σ)

theorem cmp_lt_equiv δ states pre cur σ (ann : α) (a b : AExpr α)
    (iha : ExprEquiv δ states pre cur σ a) (ihb : ExprEquiv δ states pre cur σ b) :
    ExprEquiv δ states pre cur σ (.ae_lt ann a b) := by
  unfold ExprEquiv; simp only [evalAExpr, translateExpr]
  exact int_binop iha ihb (.bool ·) (.boolConst () ·) (fun _ => .bool) (eval_intLt δ σ)
theorem cmp_le_equiv δ states pre cur σ (ann : α) (a b : AExpr α)
    (iha : ExprEquiv δ states pre cur σ a) (ihb : ExprEquiv δ states pre cur σ b) :
    ExprEquiv δ states pre cur σ (.ae_le ann a b) := by
  unfold ExprEquiv; simp only [evalAExpr, translateExpr]
  exact int_binop iha ihb (.bool ·) (.boolConst () ·) (fun _ => .bool) (eval_intLe δ σ)
theorem cmp_gt_equiv δ states pre cur σ (ann : α) (a b : AExpr α)
    (iha : ExprEquiv δ states pre cur σ a) (ihb : ExprEquiv δ states pre cur σ b) :
    ExprEquiv δ states pre cur σ (.ae_gt ann a b) := by
  unfold ExprEquiv; simp only [evalAExpr, translateExpr]
  exact int_binop iha ihb (.bool ·) (.boolConst () ·) (fun _ => .bool) (eval_intGt δ σ)
theorem cmp_ge_equiv δ states pre cur σ (ann : α) (a b : AExpr α)
    (iha : ExprEquiv δ states pre cur σ a) (ihb : ExprEquiv δ states pre cur σ b) :
    ExprEquiv δ states pre cur σ (.ae_ge ann a b) := by
  unfold ExprEquiv; simp only [evalAExpr, translateExpr]
  exact int_binop iha ihb (.bool ·) (.boolConst () ·) (fun _ => .bool) (eval_intGe δ σ)

private theorem valueEquiv_beq_coherence {δ σ} {va vb : Value} {cea ceb : Expression.Expr}
    (hva : ValueEquiv δ σ va cea) (hvb : ValueEquiv δ σ vb ceb) :
    (va == vb) = (cea == ceb) := by
  cases hva <;> cases hvb <;> (try simp [BEq.beq]) <;> sorry

theorem cmp_eq_equiv δ states pre cur σ (ann : α) (a b : AExpr α)
    (iha : ExprEquiv δ states pre cur σ a) (ihb : ExprEquiv δ states pre cur σ b) :
    ExprEquiv δ states pre cur σ (.ae_eq ann a b) := by
  unfold ExprEquiv at iha ihb ⊢; simp only [evalAExpr, translateExpr]
  match ha : evalAExpr pre cur a, hb : evalAExpr pre cur b with
  | some va, some vb =>
    rw [ha] at iha; rw [hb] at ihb; simp [bind, Option.bind]
    obtain ⟨cea, hcea, hvea⟩ := iha; obtain ⟨ceb, hceb, hveb⟩ := ihb
    rw [valueEquiv_beq_coherence hvea hveb]
    -- translateExpr for ae_eq pattern-matches on a,b; in all branches the Core
    -- evaluator produces .boolConst () (cea == ceb) via eval_eq or eval_stateTester
    sorry
  | some _, none | none, _ => simp [bind, Option.bind]

theorem cmp_ne_equiv δ states pre cur σ (ann : α) (a b : AExpr α)
    (iha : ExprEquiv δ states pre cur σ a) (ihb : ExprEquiv δ states pre cur σ b) :
    ExprEquiv δ states pre cur σ (.ae_ne ann a b) := by
  unfold ExprEquiv at iha ihb ⊢; simp only [evalAExpr, translateExpr]
  match ha : evalAExpr pre cur a, hb : evalAExpr pre cur b with
  | some va, some vb => rw [ha] at iha; rw [hb] at ihb; simp [bind, Option.bind]; sorry
  | some _, none | none, _ => simp [bind, Option.bind]

private theorem bool_binop {δ : CoreEval} {states} {pre cur : TypestateState} {σ : CoreStore}
    {a b : AExpr α} (iha : ExprEquiv δ states pre cur σ a) (ihb : ExprEquiv δ states pre cur σ b)
    {op} {f : Bool → Bool → Bool}
    (hax : ∀ ea eb ba bb, δ σ ea = some (.boolConst () ba) → δ σ eb = some (.boolConst () bb) →
      δ σ (mkBinApp op ea eb) = some (.boolConst () (f ba bb))) :
    (match (do let va ← evalAExpr pre cur a >>= Value.asBool; let vb ← evalAExpr pre cur b >>= Value.asBool; pure (Value.bool (f va vb))) with
     | some v => ∃ ce, δ σ (mkBinApp op (translateExpr states a) (translateExpr states b)) = some ce ∧ ValueEquiv δ σ v ce
     | none => True) := by
  unfold ExprEquiv at iha ihb
  match ha : evalAExpr pre cur a, hb : evalAExpr pre cur b with
  | some va, some vb =>
    rw [ha] at iha; rw [hb] at ihb; simp [bind, Option.bind]
    cases va <;> simp [Value.asBool] <;> try trivial
    case bool ba => cases vb <;> simp [Value.asBool] <;> try trivial
                    case bool bb => obtain ⟨a', ha', va'⟩ := iha; obtain ⟨b', hb', vb'⟩ := ihb
                                    cases va'; cases vb'; exact ⟨_, hax _ _ ba bb ha' hb', .bool⟩
  | some va, none => simp [bind, Option.bind]; cases va <;> simp [Value.asBool]
  | none, _ => simp [bind, Option.bind]

theorem logic_and_equiv δ states pre cur σ (ann : α) (a b : AExpr α)
    (iha : ExprEquiv δ states pre cur σ a) (ihb : ExprEquiv δ states pre cur σ b) :
    ExprEquiv δ states pre cur σ (.ae_and ann a b) := by
  unfold ExprEquiv; simp only [evalAExpr, translateExpr]; exact bool_binop iha ihb (eval_boolAnd δ σ)
theorem logic_or_equiv δ states pre cur σ (ann : α) (a b : AExpr α)
    (iha : ExprEquiv δ states pre cur σ a) (ihb : ExprEquiv δ states pre cur σ b) :
    ExprEquiv δ states pre cur σ (.ae_or ann a b) := by
  unfold ExprEquiv; simp only [evalAExpr, translateExpr]; exact bool_binop iha ihb (eval_boolOr δ σ)
theorem logic_implies_equiv δ states pre cur σ (ann : α) (a b : AExpr α)
    (iha : ExprEquiv δ states pre cur σ a) (ihb : ExprEquiv δ states pre cur σ b) :
    ExprEquiv δ states pre cur σ (.ae_implies ann a b) := by
  unfold ExprEquiv; simp only [evalAExpr, translateExpr]; exact bool_binop iha ihb (eval_boolImplies δ σ)

private theorem index_from_ve {δ : CoreEval} {σ : CoreStore}
    {container : Value} {ce_m m_expr ek : Expression.Expr} {keyStr : String} {v : Value}
    (hve : ValueEquiv δ σ container ce_m)
    (hm : δ σ m_expr = some ce_m) (hk : δ σ ek = some (.strConst () keyStr))
    (hidx : Value.index container keyStr = some v) :
    ∃ ce, δ σ (mkSelect m_expr ek) = some ce ∧ ValueEquiv δ σ v ce := by
  rw [eval_mapSelect δ σ m_expr ek ce_m (.strConst () keyStr) hm hk]
  cases hve with
  | set hsel =>
    simp only [Value.index] at hidx; injection hidx with hidx; subst hidx
    exact ⟨_, hsel keyStr, .bool⟩
  | map1 witness hsel hveq =>
    simp only [Value.index] at hidx; injection hidx with hidx; subst hidx
    exact ⟨witness keyStr, hsel keyStr, hveq keyStr⟩
  | map2 witness hsel hveq =>
    simp only [Value.index] at hidx
    have hs := hsel keyStr; have hv := hveq keyStr
    split at hidx <;> (injection hidx with hidx; subst hidx) <;> simp_all <;>
      exact ⟨witness keyStr, hs, hv⟩
  | _ => simp [Value.index] at hidx

private theorem fvar_old (δ : CoreEval) (σ : CoreStore) (hO : OldStoreEquiv δ s σ) (x : String) (v : Value)
    (hlook : s.lookup x = some v) : ∃ ce, δ σ (mkOldVar x) = some ce ∧ ValueEquiv δ σ v ce := by
  have h := hO x; rw [hlook] at h; obtain ⟨ce, hσ, hve⟩ := h; exact ⟨ce, by simp [mkOldVar, eval_fvar, hσ], hve⟩

private theorem fvar_cur (δ : CoreEval) (σ : CoreStore) (hC : StoreEquiv δ s σ) (x : String) (v : Value)
    (hlook : s.lookup x = some v) : ∃ ce, δ σ (mkVar x) = some ce ∧ ValueEquiv δ σ v ce := by
  have h := hC x; rw [hlook] at h; obtain ⟨ce, hσ, hve⟩ := h; exact ⟨ce, by simp [mkVar, eval_fvar, hσ], hve⟩

private theorem str_from_ve {δ σ} {kv : Value} {ce_k : Expression.Expr} {keyStr : String}
    (hve : ValueEquiv δ σ kv ce_k) (hstr : Value.asStr kv = some keyStr) : ce_k = .strConst () keyStr := by
  cases kv <;> simp [Value.asStr] at hstr; subst hstr; cases hve; rfl

private theorem contains_to_mem {l : List String} {x : String} (h : l.contains x = true) : x ∈ l :=
  List.contains_iff_mem.mp h
private theorem not_contains_to_not_mem {l : List String} {x : String} (h : l.contains x = false) : ¬(x ∈ l) := by
  intro hm; have := List.contains_iff_mem.mpr hm; rw [h] at this; exact Bool.false_ne_true this

theorem old_idx1_equiv δ states pre cur σ (ann : α)
    (hO : OldStoreEquiv δ pre σ) (hC : StoreEquiv δ cur σ)
    (_hT : StateTagsCoherent states cur) (m k : Ann String α) :
    ExprEquiv δ states pre cur σ (.ae_old_idx1 ann m k) := by
  unfold ExprEquiv; simp only [evalAExpr, indexByIdent, translateExpr]
  match hm : pre.lookup m.val with
  | none => simp [bind, Option.bind]
  | some container =>
    simp [bind, Option.bind]
    match hk : cur.lookup k.val with
    | none => simp [bind, Option.bind]
    | some kv =>
      simp [bind, Option.bind]
      match hstr : Value.asStr kv with
      | none => simp [bind, Option.bind]
      | some keyStr =>
        simp [bind, Option.bind]
        match hidx : Value.index container keyStr with
        | none => simp
        | some v =>
          simp
          obtain ⟨ce_m, hσm, hve_m⟩ := fvar_old δ σ hO m.val container hm
          obtain ⟨ce_k, hσk, hve_k⟩ := fvar_cur δ σ hC k.val kv hk
          have hce_k := str_from_ve hve_k hstr; subst hce_k
          exact index_from_ve hve_m hσm hσk hidx

theorem old_idx1_str_equiv δ states pre cur σ (ann : α)
    (hO : OldStoreEquiv δ pre σ) (m k : Ann String α) :
    ExprEquiv δ states pre cur σ (.ae_old_idx1_str ann m k) := by
  unfold ExprEquiv; simp only [evalAExpr, translateExpr]
  match hm : pre.lookup m.val with
  | none => simp [bind, Option.bind]
  | some container =>
    simp [bind, Option.bind]
    match hidx : Value.index container k.val with
    | none => simp
    | some v =>
      simp
      obtain ⟨ce_m, hσm, hve_m⟩ := fvar_old δ σ hO m.val container hm
      exact index_from_ve hve_m hσm (eval_strConst δ σ k.val) hidx

theorem old_idx2_equiv δ states pre cur σ (ann : α)
    (hO : OldStoreEquiv δ pre σ) (hC : StoreEquiv δ cur σ)
    (m b k : Ann String α) :
    ExprEquiv δ states pre cur σ (.ae_old_idx2 ann m b k) := by
  unfold ExprEquiv; simp only [evalAExpr, translateExpr]
  match hm : pre.lookup m.val with
  | none => simp [bind, Option.bind]
  | some container =>
    simp [bind, Option.bind]
    match hbl : cur.lookup b.val with
    | none => simp [bind, Option.bind]
    | some bv =>
      simp [bind, Option.bind]
      match hbs : Value.asStr bv with
      | none => simp [bind, Option.bind]
      | some bStr =>
        simp [bind, Option.bind]
        match hkl : cur.lookup k.val with
        | none => simp [bind, Option.bind]
        | some kv =>
          simp [bind, Option.bind]
          match hks : Value.asStr kv with
          | none => simp [bind, Option.bind]
          | some kStr =>
            simp [bind, Option.bind]
            match h1 : Value.index container bStr with
            | none => simp [bind, Option.bind]
            | some inner =>
              simp [bind, Option.bind]
              match h2 : Value.index inner kStr with
              | none => simp
              | some v =>
                simp
                obtain ⟨cm, hm', vm⟩ := fvar_old δ σ hO m.val container hm
                obtain ⟨cb, hb', vb⟩ := fvar_cur δ σ hC b.val bv hbl
                obtain ⟨ck, hk', vk⟩ := fvar_cur δ σ hC k.val kv hkl
                have := str_from_ve vb hbs; subst this
                have := str_from_ve vk hks; subst this
                obtain ⟨ci, hi, vi⟩ := index_from_ve vm hm' hb' h1
                exact index_from_ve vi hi hk' h2

theorem index1_equiv δ states pre cur σ (ann : α)
    (hC : StoreEquiv δ cur σ) (_hT : StateTagsCoherent states cur)
    (m k : Ann String α) :
    ExprEquiv δ states pre cur σ (.ae_index1 ann m k) := by
  unfold ExprEquiv; simp only [evalAExpr, indexByIdent, translateExpr]
  match hm : cur.lookup m.val with
  | none => simp [bind, Option.bind]
  | some container =>
    simp [bind, Option.bind]
    match hk : cur.lookup k.val with
    | none => simp [bind, Option.bind]
    | some kv =>
      simp [bind, Option.bind]
      match hstr : Value.asStr kv with
      | none => simp [bind, Option.bind]
      | some keyStr =>
        simp [bind, Option.bind]
        match hidx : Value.index container keyStr with
        | none => simp
        | some v =>
          simp
          obtain ⟨cm, hm', vm⟩ := fvar_cur δ σ hC m.val container hm
          obtain ⟨ck, hk', vk⟩ := fvar_cur δ σ hC k.val kv hk
          have := str_from_ve vk hstr; subst this
          exact index_from_ve vm hm' hk' hidx

theorem index1_str_equiv δ states pre cur σ (ann : α)
    (hC : StoreEquiv δ cur σ) (m k : Ann String α) :
    ExprEquiv δ states pre cur σ (.ae_index1_str ann m k) := by
  unfold ExprEquiv; simp only [evalAExpr, translateExpr]
  match hm : cur.lookup m.val with
  | none => simp [bind, Option.bind]
  | some container =>
    simp [bind, Option.bind]
    match hidx : Value.index container k.val with
    | none => simp
    | some v =>
      simp
      obtain ⟨cm, hm', vm⟩ := fvar_cur δ σ hC m.val container hm
      exact index_from_ve vm hm' (eval_strConst δ σ k.val) hidx

theorem index2_equiv δ states pre cur σ (ann : α)
    (hC : StoreEquiv δ cur σ) (m b k : Ann String α) :
    ExprEquiv δ states pre cur σ (.ae_index2 ann m b k) := by
  unfold ExprEquiv; simp only [evalAExpr, translateExpr]
  match hm : cur.lookup m.val with
  | none => simp [bind, Option.bind]
  | some container =>
    simp [bind, Option.bind]
    match hbl : cur.lookup b.val with
    | none => simp [bind, Option.bind]
    | some bv =>
      simp [bind, Option.bind]
      match hbs : Value.asStr bv with
      | none => simp [bind, Option.bind]
      | some bStr =>
        simp [bind, Option.bind]
        match hkl : cur.lookup k.val with
        | none => simp [bind, Option.bind]
        | some kv =>
          simp [bind, Option.bind]
          match hks : Value.asStr kv with
          | none => simp [bind, Option.bind]
          | some kStr =>
            simp [bind, Option.bind]
            match h1 : Value.index container bStr with
            | none => simp [bind, Option.bind]
            | some inner =>
              simp [bind, Option.bind]
              match h2 : Value.index inner kStr with
              | none => simp
              | some v =>
                simp
                obtain ⟨cm, hm', vm⟩ := fvar_cur δ σ hC m.val container hm
                obtain ⟨cb, hb', vb⟩ := fvar_cur δ σ hC b.val bv hbl
                obtain ⟨ck, hk', vk⟩ := fvar_cur δ σ hC k.val kv hkl
                have := str_from_ve vb hbs; subst this; have := str_from_ve vk hks; subst this
                obtain ⟨ci, hi, vi⟩ := index_from_ve vm hm' hb' h1
                exact index_from_ve vi hi hk' h2

theorem index2_ss_equiv δ states pre cur σ (ann : α)
    (hC : StoreEquiv δ cur σ) (m b k : Ann String α) :
    ExprEquiv δ states pre cur σ (.ae_index2_ss ann m b k) := by
  unfold ExprEquiv; simp only [evalAExpr, translateExpr]
  match hm : cur.lookup m.val with
  | none => simp [bind, Option.bind]
  | some container =>
    simp [bind, Option.bind]
    match h1 : Value.index container b.val with
    | none => simp [bind, Option.bind]
    | some inner =>
      simp [bind, Option.bind]
      match h2 : Value.index inner k.val with
      | none => simp
      | some v =>
        simp
        obtain ⟨cm, hm', vm⟩ := fvar_cur δ σ hC m.val container hm
        obtain ⟨ci, hi, vi⟩ := index_from_ve vm hm' (eval_strConst δ σ b.val) h1
        exact index_from_ve vi hi (eval_strConst δ σ k.val) h2

private theorem mem_set_select {δ : CoreEval} {σ : CoreStore}
    {ce_s s_expr x_expr : Expression.Expr} {keys : List String} {xs : String}
    (hve_s : ValueEquiv δ σ (.set keys) ce_s)
    (hs : δ σ s_expr = some ce_s) (hx : δ σ x_expr = some (.strConst () xs)) :
    ∃ ce, δ σ (mkSelect s_expr x_expr) = some ce ∧ ValueEquiv δ σ (.bool (keys.contains xs)) ce := by
  rw [eval_mapSelect δ σ s_expr x_expr ce_s (.strConst () xs) hs hx]
  cases hve_s with | set hsel => exact ⟨_, hsel xs, .bool⟩

theorem mem_in_id_equiv δ states pre cur σ (ann : α)
    (hC : StoreEquiv δ cur σ) (x s : Ann String α) :
    ExprEquiv δ states pre cur σ (.ae_in_id ann x s) := by
  unfold ExprEquiv; simp only [evalAExpr, translateExpr]
  match hx : cur.lookup x.val with
  | none => simp [bind, Option.bind]
  | some xv =>
    simp [bind, Option.bind]
    match hxs : Value.asStr xv with
    | none => simp [bind, Option.bind]
    | some xs =>
      simp [bind, Option.bind]
      match hs : cur.lookup s.val with
      | none => simp [bind, Option.bind]
      | some sv =>
        simp [bind, Option.bind]
        obtain ⟨cs, hs', vs⟩ := fvar_cur δ σ hC s.val sv hs
        obtain ⟨cx, hx', vx⟩ := fvar_cur δ σ hC x.val xv hx
        have := str_from_ve vx hxs; subst this
        cases sv with
        | set keys =>
          have h := mem_set_select vs hs' hx'; simp at h ⊢; exact h
        | map1 kvs d => simp; sorry -- semantic mismatch
        | _ => simp

theorem mem_in_str_equiv δ states pre cur σ (ann : α)
    (hC : StoreEquiv δ cur σ) (x s : Ann String α) :
    ExprEquiv δ states pre cur σ (.ae_in_str ann x s) := by
  unfold ExprEquiv; simp only [evalAExpr, translateExpr]
  match hs : cur.lookup s.val with
  | none => simp [bind, Option.bind]
  | some sv =>
    simp [bind, Option.bind]
    obtain ⟨cs, hs', vs⟩ := fvar_cur δ σ hC s.val sv hs
    cases sv with
    | set keys =>
      have h := mem_set_select vs hs' (eval_strConst δ σ x.val); simp at h ⊢; exact h
    | map1 kvs d => simp; sorry -- semantic mismatch
    | _ => simp

theorem mem_in_id_old_equiv δ states pre cur σ (ann : α)
    (hO : OldStoreEquiv δ pre σ) (hC : StoreEquiv δ cur σ)
    (x s : Ann String α) :
    ExprEquiv δ states pre cur σ (.ae_in_id_old ann x s) := by
  unfold ExprEquiv; simp only [evalAExpr, translateExpr]
  match hx : cur.lookup x.val with
  | none => simp [bind, Option.bind]
  | some xv =>
    simp [bind, Option.bind]
    match hxs : Value.asStr xv with
    | none => simp [bind, Option.bind]
    | some xs =>
      simp [bind, Option.bind]
      match hs : pre.lookup s.val with
      | none => simp [bind, Option.bind]
      | some sv =>
        simp [bind, Option.bind]
        obtain ⟨cs, hs', vs⟩ := fvar_old δ σ hO s.val sv hs
        obtain ⟨cx, hx', vx⟩ := fvar_cur δ σ hC x.val xv hx
        have := str_from_ve vx hxs; subst this
        cases sv with
        | set keys =>
          have h := mem_set_select vs hs' hx'; simp at h ⊢; exact h
        | map1 kvs d => simp; sorry -- semantic mismatch
        | _ => simp

theorem mem_notin_id_equiv δ states pre cur σ (ann : α)
    (hC : StoreEquiv δ cur σ) (x s : Ann String α) :
    ExprEquiv δ states pre cur σ (.ae_notin_id ann x s) := by
  unfold ExprEquiv; simp only [evalAExpr, translateExpr]
  match hx : cur.lookup x.val with
  | none => simp [bind, Option.bind]
  | some xv =>
    simp [bind, Option.bind]
    match hxs : Value.asStr xv with
    | none => simp [bind, Option.bind]
    | some xs =>
      simp [bind, Option.bind]
      match hs : cur.lookup s.val with
      | none => simp [bind, Option.bind]
      | some sv =>
        simp [bind, Option.bind]
        obtain ⟨cs, hs', vs⟩ := fvar_cur δ σ hC s.val sv hs
        obtain ⟨cx, hx', vx⟩ := fvar_cur δ σ hC x.val xv hx
        have := str_from_ve vx hxs; subst this
        cases sv with
        | set keys =>
          obtain ⟨r, hr, vr⟩ := mem_set_select vs hs' hx'
          cases vr; simp at hr ⊢; exact ⟨_, eval_boolNot δ σ _ _ hr, .bool⟩
        | map1 kvs d => simp; sorry -- semantic mismatch
        | _ => simp

theorem mem_notin_str_equiv δ states pre cur σ (ann : α)
    (hC : StoreEquiv δ cur σ) (x s : Ann String α) :
    ExprEquiv δ states pre cur σ (.ae_notin_str ann x s) := by
  unfold ExprEquiv; simp only [evalAExpr, translateExpr]
  match hs : cur.lookup s.val with
  | none => simp [bind, Option.bind]
  | some sv =>
    simp [bind, Option.bind]
    obtain ⟨cs, hs', vs⟩ := fvar_cur δ σ hC s.val sv hs
    cases sv with
    | set keys =>
      obtain ⟨r, hr, vr⟩ := mem_set_select vs hs' (eval_strConst δ σ x.val)
      cases vr; simp at hr ⊢; exact ⟨_, eval_boolNot δ σ _ _ hr, .bool⟩
    | map1 kvs d => simp; sorry -- semantic mismatch
    | _ => simp

private theorem expr_equiv_induction {α : Type} δ states pre cur σ
    (hC : StoreEquiv δ cur σ) (hO : OldStoreEquiv δ pre σ)
    (hTP : StateTagsCoherent states pre) (hTC : StateTagsCoherent states cur)
    (e : AExpr α) : ExprEquiv δ states pre cur σ e := by
  induction e with
  | ae_num a n            => exact atom_num_equiv ..
  | ae_str a s            => exact atom_str_equiv ..
  | ae_true a             => exact atom_true_equiv ..
  | ae_false a            => exact atom_false_equiv ..
  | ae_var a x            => exact atom_var_equiv δ states pre cur σ a hC hTC x
  | ae_paren _ _ ih       => exact atom_paren_equiv δ states pre cur σ _ _ ih
  | ae_old a x            => exact old_bare_equiv δ states pre cur σ a hO hTP x
  | ae_old_idx1 a m k     => exact old_idx1_equiv δ states pre cur σ a hO hC hTC m k
  | ae_old_idx1_str a m k => exact old_idx1_str_equiv δ states pre cur σ a hO m k
  | ae_old_idx2 a m b k   => exact old_idx2_equiv δ states pre cur σ a hO hC m b k
  | ae_index1 a m k       => exact index1_equiv δ states pre cur σ a hC hTC m k
  | ae_index1_str a m k   => exact index1_str_equiv δ states pre cur σ a hC m k
  | ae_index2 a m b k     => exact index2_equiv δ states pre cur σ a hC m b k
  | ae_index2_ss a m b k  => exact index2_ss_equiv δ states pre cur σ a hC m b k
  | ae_not _ _ ih          => exact arith_not_equiv δ states pre cur σ _ _ ih
  | ae_add _ _ _ iha ihb   => exact arith_add_equiv δ states pre cur σ _ _ _ iha ihb
  | ae_sub _ _ _ iha ihb   => exact arith_sub_equiv δ states pre cur σ _ _ _ iha ihb
  | ae_eq _ _ _ iha ihb    => exact cmp_eq_equiv δ states pre cur σ _ _ _ iha ihb
  | ae_ne _ _ _ iha ihb    => exact cmp_ne_equiv δ states pre cur σ _ _ _ iha ihb
  | ae_lt _ _ _ iha ihb    => exact cmp_lt_equiv δ states pre cur σ _ _ _ iha ihb
  | ae_le _ _ _ iha ihb    => exact cmp_le_equiv δ states pre cur σ _ _ _ iha ihb
  | ae_gt _ _ _ iha ihb    => exact cmp_gt_equiv δ states pre cur σ _ _ _ iha ihb
  | ae_ge _ _ _ iha ihb    => exact cmp_ge_equiv δ states pre cur σ _ _ _ iha ihb
  | ae_in_id a x s         => exact mem_in_id_equiv δ states pre cur σ a hC x s
  | ae_in_str a x s        => exact mem_in_str_equiv δ states pre cur σ a hC x s
  | ae_in_id_old a x s     => exact mem_in_id_old_equiv δ states pre cur σ a hO hC x s
  | ae_notin_id a x s      => exact mem_notin_id_equiv δ states pre cur σ a hC x s
  | ae_notin_str a x s     => exact mem_notin_str_equiv δ states pre cur σ a hC x s
  | ae_and _ _ _ iha ihb   => exact logic_and_equiv δ states pre cur σ _ _ _ iha ihb
  | ae_or _ _ _ iha ihb    => exact logic_or_equiv δ states pre cur σ _ _ _ iha ihb
  | ae_implies _ _ _ i1 i2 => exact logic_implies_equiv δ states pre cur σ _ _ _ i1 i2
  | ae_forall1 a x body    => exact quant_forall1_equiv ..
  | ae_forall2 a x y body  => exact quant_forall2_equiv ..
  | ae_exists1 a x body    => exact quant_exists1_equiv ..

theorem semantics_equivalence {α : Type} δ states pre cur σ
    (hC : StoreEquiv δ cur σ) (hO : OldStoreEquiv δ pre σ)
    (hTP : StateTagsCoherent states pre) (hTC : StateTagsCoherent states cur)
    (e : AExpr α) : ExprEquiv δ states pre cur σ e :=
  expr_equiv_induction δ states pre cur σ hC hO hTP hTC e

end Strata.typestate.Correctness

end
