From Coq Require Import Wellfounded.

From stdpp Require Import strings binders gmap gmultiset.

Inductive loc := to_loc : Z -> loc.

Definition of_loc : loc -> Z := fun '(to_loc x) => x.

#[export] Instance loc_eq_dec : EqDecision loc := ltac:(solve_decision).
#[export] Instance loc_countable : Countable loc :=
  ltac:(apply inj_countable' with of_loc to_loc; now intros []).
#[export] Instance loc_infinite : Infinite loc :=
  ltac:(apply inj_infinite with to_loc (fun x => Some (of_loc x)); easy).
#[export] Instance loc_inhabited : Inhabited loc := populate (to_loc inhabitant).

Inductive int_op := IntAdd | IntMul | IntSub | IntDiv | IntMod | IntMin | IntMax.

Inductive int_cmp := IntLt | IntLe | IntGt | IntGe.

Inductive bool_op := BoolAnd | BoolOr.

Inductive prim :=
| PrimEq : prim
| PrimBoolOp : bool_op -> prim
| PrimIntOp : int_op -> prim
| PrimIntCmp : int_cmp -> prim.

Inductive timestamp := to_timestamp : nat -> timestamp.

Definition of_timestamp : timestamp -> nat := fun '(to_timestamp x) => x.

#[export] Instance eqdec_timestamp : EqDecision timestamp := ltac:(solve_decision).
#[export] Instance countable_timestamp : Countable timestamp :=
  ltac:(apply inj_countable' with of_timestamp to_timestamp; now intros []).
#[export] Instance infinite_timestamp : Infinite timestamp :=
  ltac:(apply inj_infinite with to_timestamp (fun x => Some (of_timestamp x)); easy).
#[export] Instance inhabited_timestamp : Inhabited timestamp := populate (to_timestamp inhabitant).

Inductive expr : Set :=

| Val : val -> expr

| Clo : function -> expr
| Var : string -> expr
| Call : expr -> list expr -> expr
| CallPrim : prim -> expr -> expr -> expr
| If : expr -> expr -> expr -> expr
| Let : binder -> expr -> expr -> expr

| Prod : expr -> expr -> expr
| Fst : expr -> expr
| Snd : expr -> expr

| InL : expr -> expr
| InR : expr -> expr
| Case :
  expr ->
  binder -> expr ->
  binder -> expr ->
  expr

| Alloc : expr -> expr -> expr
| Load : expr -> expr -> expr
| Store : expr -> expr -> expr -> expr
| Length : expr -> expr

| Par : expr -> expr -> expr
| RunPar : expr -> expr -> expr
| CAS : expr -> expr -> expr -> expr -> expr

| Fold : expr -> expr
| Unfold : expr -> expr
with function : Set :=
  Lam :
    binder ->
    list binder ->
    expr ->
    function
with val : Set :=
| VUnit : val
| VBool : bool -> val
| VInt  : Z -> val
| VLoc : loc -> val
| VFold : val -> val
| VCode : function -> val.

Coercion VBool : bool >-> val.

Coercion VLoc : loc >-> val.

Coercion VInt : Z >-> val.

Coercion Val : val >-> expr.

Coercion Var : string >-> expr.

Definition to_val e :=
  match e with
  | Val v => Some v
  | _ => None end.

Definition is_val e :=
  match e with
  | Val v => true
  | _ => false end.

Fixpoint is_loc v :=
  match v with
  | VLoc _ => true
  | VFold v => is_loc v
  | _ => false end.

Fixpoint expr_size (e : expr):= 1 +
  match e with
  | Var _ => 0
  | Val v =>
      match v with
      | VCode c => clo_size c
      | _ => 0 end
  | Clo c => clo_size c
  | Length e | Fst e | Snd e | InL e | InR e | Fold e | Unfold e => expr_size e
  | Call e1 xs => expr_size e1 + list_sum (expr_size <$> xs)
  | Prod e1 e2 | CallPrim _ e1 e2 | Let _ e1 e2 | Alloc e1 e2 | Load e1 e2 | Par e1 e2 | RunPar e1 e2 => expr_size e1 + expr_size e2
  | Case e1 _ e2 _ e3 | Store e1 e2 e3 | If e1 e2 e3 => expr_size e1 + expr_size e2 + expr_size e3
  | CAS e1 e2 e3 e4 => expr_size e1 + expr_size e2 + expr_size e3 + expr_size e4
  end
with clo_size c := match c with Lam _ _ e => expr_size e end.

Inductive ctx : Set :=
| CtxCall1 : val -> list val -> list expr -> ctx
| CtxCall2 : list expr -> ctx
| CtxCallPrim1 : prim -> expr -> ctx
| CtxCallPrim2 : prim -> val -> ctx
| CtxIf : expr -> expr -> ctx
| CtxLet : binder -> expr -> ctx
| CtxAlloc1 : expr -> ctx
| CtxAlloc2 : val -> ctx
| CtxLoad1 : expr -> ctx
| CtxLoad2 : val -> ctx
| CtxStore1 : expr -> expr -> ctx
| CtxStore2 : val -> expr -> ctx
| CtxStore3 : val -> val -> ctx
| CtxLength : ctx
| CtxPair1 : expr -> ctx
| CtxPair2 : val -> ctx
| CtxFst : ctx
| CtxSnd : ctx
| CtxInL : ctx
| CtxInR : ctx
| CtxCase : binder -> expr -> binder -> expr -> ctx
| CtxCas1 : expr -> expr -> expr -> ctx
| CtxCas2 : val -> expr -> expr -> ctx
| CtxCas3 : val -> val -> expr -> ctx
| CtxCas4 : val -> val -> val -> ctx
| CtxPar1 : expr -> ctx
| CtxPar2 : val -> ctx
| CtxFold : ctx
| CtxUnfold : ctx
.

Definition fill_item (k:ctx) (e:expr) : expr :=
  match k with
  | CtxCall1 e' vs ts => Call e' ((Val <$> vs)++e::ts)
  | CtxCall2 ts => Call e ts
  | CtxCallPrim1 p e2 => CallPrim p e e2
  | CtxCallPrim2 p v => CallPrim p v e
  | CtxIf e2 e3 => If e e2 e3
  | CtxLet x e2 => Let x e e2
  | CtxAlloc1 e' => Alloc e e'
  | CtxAlloc2 v => Alloc (Val v) e
  | CtxLoad1 e2 => Load e e2
  | CtxLoad2 v => Load (Val v) e
  | CtxStore1 e1 e2 => Store e e1 e2
  | CtxStore2 v e2 => Store (Val v) e e2
  | CtxStore3 v1 v2 => Store (Val v1) (Val v2) e
  | CtxLength => Length e
  | CtxPair1 e2 => Prod e e2
  | CtxPair2 v1 => Prod v1 e
  | CtxFst => Fst e
  | CtxSnd => Snd e
  | CtxInL => InL e
  | CtxInR => InR e
  | CtxCase xl el xr er => Case e xl el xr er
  | CtxCas1 e1 e2 e3 => CAS e e1 e2 e3
  | CtxCas2 v e2 e3 => CAS (Val v) e e2 e3
  | CtxCas3 v1 v2 e3 => CAS (Val v1) (Val v2) e e3
  | CtxCas4 v1 v2 v3 => CAS (Val v1) (Val v2) (Val v3) e
  | CtxPar1 e1 => Par e e1
  | CtxPar2 v1 => Par v1 e
  | CtxFold => Fold e
  | CtxUnfold => Unfold e
  end.

Inductive storable :=
| SBlock : list val -> storable
| SProd : val -> val -> storable
| SInL : val -> storable
| SInR : val -> storable
| SClo : binder -> list binder -> expr -> storable.

Class Location A := locs : A -> gset loc.

Global Instance location_list `{Location A} : Location (list A) :=
  fun xs => ⋃ (locs <$> xs).
Global Instance location_loc : Location loc := gset_singleton.

Fixpoint locs_val (v:val) : gset loc :=
  match v with
  | VLoc l => {[l]}
  | VFold v => locs_val v
  | _ => ∅ end.

Global Instance location_val : Location val := locs_val.

Fixpoint locs_expr (e:expr) : gset loc :=
  match e with
  | Val v => locs_val v
  | Var _ => ∅
  | Clo c => locs_func c
  | Length e1 | Fst e1 | Snd e1 | InL e1 | InR e1 | Fold e1 | Unfold e1 => locs_expr e1
  | Call e1 e2 => locs_expr e1 ∪ ⋃ (locs_expr <$> e2)
  | Case e1 _ e2 _ e3 | If e1 e2 e3 | Store e1 e2 e3 => locs_expr e1 ∪ locs_expr e2 ∪ locs_expr e3
  | CAS e1 e2 e3 e4 => locs_expr e1 ∪ locs_expr e2 ∪ locs_expr e3 ∪ locs_expr e4
  | Prod e1 e2 | CallPrim _ e1 e2 | Let _ e1 e2 | Alloc e1 e2
  | Load e1 e2 | Par e1 e2 | RunPar e1 e2 => locs_expr e1 ∪ locs_expr e2 end
with locs_func (c:function) :=
  match c with
  | Lam _ _ e => locs_expr e end.

Global Instance location_expr : Location expr := locs_expr.
Global Instance location_clo : Location function := locs_func.

Definition locs_ctx (k:ctx) : gset loc :=
  match k with
  | CtxCall1 e vs ts => locs e ∪ locs vs ∪ locs ts
  | CtxCall2 vs => locs vs
  | CtxCallPrim1 p e => locs e
  | CtxCallPrim2 p v => locs v
  | CtxIf e2 e3 => locs e2 ∪ locs e3
  | CtxLet _ e2 => locs e2
  | CtxAlloc1 e => locs e
  | CtxAlloc2 v => locs v
  | CtxLoad1 e2 => locs e2
  | CtxLoad2 v => locs v
  | CtxStore1 e1 e2 => locs e1 ∪ locs e2
  | CtxStore2 v e2 => locs v ∪ locs e2
  | CtxStore3 v1 v2 => locs v1 ∪ locs v2
  | CtxLength | CtxFst | CtxSnd | CtxInL | CtxInR | CtxFold | CtxUnfold => ∅
  | CtxPair1 e1 => locs e1
  | CtxPair2 v1 => locs v1
  | CtxCase _ e1 _ e2 => locs e1 ∪ locs e2
  | CtxCas1 e1 e2 e3 => locs e1 ∪ locs e2 ∪ locs e3
  | CtxCas2 v e2 e3 => locs v ∪ locs e2 ∪ locs e3
  | CtxCas3 v1 v2 e3 => locs v1 ∪ locs v2 ∪ locs e3
  | CtxCas4 v1 v2 v3 => locs v1 ∪ locs v2 ∪ locs v3
  | CtxPar1 e1 => locs e1
  | CtxPar2 v1 => locs v1
  end.

Global Instance location_ctx : Location ctx := locs_ctx.
