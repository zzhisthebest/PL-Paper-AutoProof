From Coq.ssr Require Import ssreflect.

From stdpp Require Import strings binders gmap gmultiset.

From dislog.utils Require Export graph.

From dislog.lang Require Export syntax syntax_instances substitution.

Notation store := (gmap loc storable).

Implicit Type σ : store.

Section gen.

Context `{Countable A}.

Notation amap  := (gmap loc A).

Notation graph := (graph A).

Implicit Type t : A.

Implicit Type α : amap.

Implicit Type G : graph.

Definition exec_int_op op :=
  match op with
  | IntAdd => Z.add
  | IntMul => Z.mul
  | IntSub => Z.sub
  | IntDiv => Z.div
  | IntMod => Z.modulo
  | IntMin => Z.min
  | IntMax => Z.max end.

Definition exec_int_cmp op :=
  match op with
  | IntLt => Z.ltb
  | IntLe => Z.leb
  | IntGt => Z.gtb
  | IntGe => Z.geb end.

Definition exec_bool_bin_op op :=
  match op with
  | BoolAnd => andb
  | BoolOr => orb end.

Definition eval_call_prim p v1 v2 :=
  match p,v1,v2 with
  | PrimBoolOp op, VBool b1, VBool b2 => Some (VBool (exec_bool_bin_op op b1 b2))
  | PrimIntOp op, VInt m, VInt n => Some (VInt (exec_int_op op m n))
  | PrimIntCmp op, VInt m, VInt n => Some (VBool (exec_int_cmp op m n))
  | PrimEq, v1, v2 => Some (VBool (bool_decide (v1=v2)))
  | _,_,_ => None end.

Inductive head_step : graph -> A -> store -> amap -> expr -> store -> amap -> expr -> Prop :=
| HeadIf : forall G t σ α (b:bool) e1 e2,
    head_step G t
      σ α (If b e1 e2)
      σ α (if b then e1 else e2)
| HeadLet : forall G t σ α (v:val) x e,
    head_step G t
      σ α (Let x v e)
      σ α (subst' x v e)
| HeadCall : forall G t σ α ts vs self args code,
  ts = Val <$> vs ->
  length args = length ts ->
  locs code = ∅ ->
    head_step G t
      σ α (Call (VCode (Lam self args code)) ts)
      σ α (substs' (zip (self::args) (VCode (Lam self args code)::vs)) code)
| HeadCallClo : forall G t σ α ts vs self args body l,
    σ !! l = Some (SClo self args body) ->
    ts = Val <$> vs ->
    length args = length ts ->
    head_step G t
      σ α (Call (VLoc l) ts)
      σ α (substs' (zip (self::args) (VLoc l::vs)) body)
| HeadCallPrim : forall G t σ α v1 v2 v p,
    eval_call_prim p v1 v2 = Some v ->
    head_step G t
      σ α (CallPrim p v1 v2)
      σ α v
| HeadFunc : forall G t σ σ' α α' (l:loc) self args code,
    l ∉ dom σ ->
    l ∉ dom α ->
    σ' = <[l:=SClo self args code]> σ ->
    α' = <[l:=t]> α ->
    head_step G t
      σ  α  (Clo (Lam self args code))
      σ' α' (VLoc l)
| HeadAlloc : forall G t σ σ' α α' (n:Z) (v:val) (l:loc),
    (0 < n)%Z ->
    l ∉ dom σ ->
    l ∉ dom α ->
    σ' = <[l:=SBlock (replicate (Z.to_nat n) v)]> σ ->
    α' = <[l:=t]> α ->
    head_step G t
      σ  α  (Alloc n v)
      σ' α' (Val l)
| HeadLoad : forall G t σ α (l:loc) (bs:list val) (i:Z) (v:val),
    σ !! l = Some (SBlock bs) ->
    (0 <= i < Z.of_nat (length bs))%Z ->
    bs !! (Z.to_nat i) = Some v ->
    head_step G t
      σ α (Load l i)
      σ α v
| HeadStore : forall G t σ σ' α (l:loc) bs i (v:val),
    σ !! l = Some (SBlock bs) ->
    (0 <= i < Z.of_nat (length bs))%Z ->
    σ' = <[l := SBlock (<[Z.to_nat i := v]> bs)]> σ ->
    head_step G t
      σ  α (Store l i v)
      σ' α VUnit
| HeadProd : forall G t σ α (v1 v2:val) (l:loc),
    l ∉ dom σ ->
    l ∉ dom α ->
    head_step G t σ α (Prod v1 v2) (<[l:=SProd v1 v2]> σ) (<[l:=t]> α) l
| HeadProj : forall b G t σ α (v1 v2:val) (l:loc),
  σ !! l = Some (SProd v1 v2) ->
  head_step G t σ α (if b then Fst l else Snd l) σ α (if b then v1 else v2)
| HeadLength : forall G t σ α (l:loc) bs,
    σ !! l = Some (SBlock bs) ->
    head_step G t
      σ α (Length l)
      σ α (VInt (Z.of_nat (length bs)))
| HeadCAS : forall G t σ σ' α (l:loc) (i:Z) (v v0 v':val) bs,
    (0 <= i < Z.of_nat (length bs))%Z ->
    σ !! l = Some (SBlock bs) ->
    bs !! (Z.to_nat i) = Some v0 ->
    σ' = (if bool_decide (v=v0)
          then (insert l (SBlock (<[Z.to_nat i := v']> bs)) σ) else σ) ->
    head_step G t
      σ  α (CAS l i v v')
      σ' α (Val (bool_decide (v=v0)))
| HeadFold : forall G t σ α (v:val),
    head_step G t σ α (Fold v) σ α (VFold v)
| HeadUnfoldFold : forall G t σ α (v:val),
  head_step G t σ α (Unfold (VFold v)) σ α v
| HeadIn : forall b G t σ α (v:val) (l:loc),
  l ∉ dom σ ->
  l ∉ dom α ->
  head_step G t σ α (if b then InL v else InR v) (<[l:=if b then SInL v else SInR v]> σ) (<[l:=t]> α) l
| HeadCase : forall b G t σ α vl vr (l:loc) xl el xr er,
  σ !! l = Some (if b then SInL vl else SInR vr) ->
  head_step G t σ α (Case l xl el xr er) σ α (if b then subst' xl vl el else subst' xr vr er)
.

End gen.
