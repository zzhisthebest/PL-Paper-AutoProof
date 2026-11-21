Require Import Relations Decidable.

Require Import Lists.

Require Import Forall2.

Require Import ZArith.

Require Import Coq.Program.Equality.

Require Import RFJ.Utils.

Require Export Definitions.Syntax.

Require Export Definitions.Names.

Require Import Definitions.Semantics.

Require Import Definitions.SubDenotation.

Definition tybc (b:bool) : type :=
TRefn TBool (PCons (ExpBinOp (Eq) (Bc b) (BV 0))  PEmpty).

Definition tyic (n:Z) : type :=
TRefn TInt  (PCons (ExpBinOp (Eq) (Ic n) (BV 0))  PEmpty).

Definition refn_pred (c:UnOp) : expr :=
match c with
| Not      => (ExpBinOp (Eq) (ExpUnOp (Not) (BV 1)) (BV 0))
end.

Definition intype (c:UnOp) : type :=
match c with
| Not     => TRefn TBool   PEmpty
end.

Definition ty' (c:UnOp) : type :=
match c with
| Not      =>  TRefn TBool (PCons (refn_pred Not) PEmpty)
end.

Definition refn_pred2 (c:BinOp) : expr :=
match c with
| And      => (ExpBinOp (Eq) (ExpBinOp (And) (BV 2) (BV 1)) (BV 0))
| Or       => (ExpBinOp (Eq) (ExpBinOp (Or) (BV 2) (BV 1)) (BV 0))
| Eq       => (ExpBinOp (Eq) (ExpBinOp (Eq) (BV 2) (BV 1)) (BV 0))
end.

Definition intype2 (c:BinOp) : (type*type) :=
match c with
| And     => (TRefn TBool PEmpty, TRefn TBool PEmpty)
| Or      => (TRefn TBool PEmpty, TRefn TBool PEmpty)
| Eq      => (TRefn TAny PEmpty, TRefn TAny PEmpty)
end.

Definition ty'2 (c:BinOp) : type :=
match c with
| And      => (TRefn TBool (PCons (refn_pred2 And) PEmpty))
| Or       => (TRefn TBool (PCons (refn_pred2 Or)  PEmpty))
| Eq       => (TRefn TBool (PCons (refn_pred2 Eq)  PEmpty))
end.

Inductive HasFJtype : fjenv -> expr -> fjtype -> Prop :=
    | FTBC   : forall (g:fjenv) (b:bool),  HasFJtype g (Bc b) (TBool)
    | FTIC   : forall (g:fjenv) (n:Z),   HasFJtype g (Ic n) (TInt)
    | FTVar  : forall (g:fjenv) (x:vname) (b:fjtype),
        bound_inF x b g -> HasFJtype g (FV x) b
    | FTUnOP : forall (g:fjenv) (e:expr) (op: UnOp),
        HasFJtype g e (erase (intype op)) ->
        HasFJtype g (ExpUnOp op e) (erase (ty' op))
    | FTBinOP : forall (g:fjenv) (e1 e2:expr) (op: BinOp),
        HasFJtype g e1 (erase (fst (intype2 op))) -> HasFJtype g e2 (erase (snd (intype2 op))) ->
        HasFJtype g (ExpBinOp op e1 e2) (erase (ty'2 op))
    | FTInvok: forall (g:fjenv) (e1 :expr) (e2: expr) (m: MethodName) t rt C ps,
        HasFJtype g e1  (TNom (TClass C)) ->
        mtype(m, C) = ps ~> t ~> rt ->
        HasFJtype (g) e2 (erase t) ->
        HasFJtype g (ExpMethodInvoc e1 m e2) (erase rt)
    | FTInvokI: forall (g:fjenv) (e1 :expr) (e2: expr) (m: MethodName) t rt C ps,
        HasFJtype g e1 ((TNom (TInterface C))) ->
        mtypei(m, C) = ps ~> t ~> rt ->
        HasFJtype (g) e2 (erase t) ->
        HasFJtype g (ExpMethodInvoc e1 m e2) (erase rt)
    | FTField: forall g e f T C F i ff,
        HasFJtype g e ( (TNom (TClass C))) ->
        Reffields C F ->
        nth_error F i = Some ff ->
        ref ff = f ->
        ReffieldType ff = T ->
        HasFJtype g (ExpFieldAccess e f) (erase T)
    | FTNew:    forall g es C Fs Us fs,
        Us = map erase (map ReffieldType Fs) ->
        fs = map ReffieldName Fs ->
        Reffields C Fs ->
        Forall2 (HasFJtype g) es Us ->
        HasFJtype g (ExpNew C es) ((TNom (TClass C)))
    | FTLet  : forall (g:fjenv) (e_x:expr) (b:fjtype) (e:expr) (b':fjtype) (nms:names),
        HasFJtype g e_x b
            -> (forall (y:vname), ~ Elem y nms -> HasFJtype (FCons y b g) (unbind y e) b' )
            -> HasFJtype g (ExpLet e_x e) b'
    | FTSub  : forall (g:fjenv) (e:expr) (s:fjtype) (t:fjtype),
        HasFJtype g e s -> FJSubtype s t -> HasFJtype g e t
.

Inductive PIsBool : fjenv -> preds -> Prop :=
    | PFTEmp  : forall (g:fjenv), PIsBool g PEmpty
    | PFTCons : forall (g:fjenv) (p:expr) (ps:preds),
        HasFJtype g p (TBool) -> PIsBool g ps -> PIsBool g (PCons p ps).
