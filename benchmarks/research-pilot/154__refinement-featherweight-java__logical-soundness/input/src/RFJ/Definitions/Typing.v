Require Import Relations Decidable.

Require Import RFJ.Utils.

Require Export Definitions.Syntax.

Require Import Forall2.

Require Import Lists.

Require Import RFJ.Utils.Referable.

Require Export Definitions.Names.

Require Import ZArith.

Require Import Definitions.FJTyping.

Require Import Definitions.Semantics.

Require Import Definitions.SubDenotation.

Inductive WFtype : env -> type -> Prop :=
    | WFBase : forall (g : env) (b : fjtype),
           WFtype g (TRefn b PEmpty)
    | WFRefn : forall (g : env) (b : fjtype) (ps : preds) (nms : names),
          WFtype g (TRefn b PEmpty) -> ps <> PEmpty
              -> (forall (y:vname), ~ Elem y nms
                      -> PIsBool (FCons y (b) (erase_env g)) (unbindP y ps) )
              -> WFtype g (TRefn b ps).

Inductive WFEnv : env -> Prop :=
    | WFEEmpty : WFEnv Empty
    | WFEBind  : forall (g : env) (x : vname) (t : type),
          WFEnv g -> ~ (in_env x g) -> WFtype g t -> WFEnv (Cons x t g).

Reserved Notation "Gamma '|---' x ':' C" (at level 60, x at next level).

Inductive Hastype: env -> expr -> type -> Prop :=

  | TBC   : forall (g:env) (b:bool), Hastype g (Bc b) (tybc b)
  | TIC   : forall (g:env) (m:Z),  Hastype g (Ic m) (tyic m)
  | TUnOP  : forall (g:env) (e:expr) (op: UnOp) t,
        Hastype g e t -> Subtype g t (intype op) -> isLC e -> Hastype g (ExpUnOp op e) (tsubBV e (ty' op))
  | TBinOP : forall (g:env) (e1 e2:expr) (op: BinOp) t t',
        Hastype g e1 t ->
        (Subtype g t (fst (intype2 op))) ->
        Hastype g e2 t'->
        (Subtype g t' (tsubBV e1 (snd (intype2 op)))) ->
        isLC e1 -> isLC e2 ->
        Hastype g (ExpBinOp op e1 e2) (tsubBV_at 1 e1 (tsubBV e2 (ty'2 op)))
  | TVar  : forall (g:env) (x:vname) (t:type),
    bound_in x t g -> WFtype g t -> Hastype g (FV x) (self t (FV x))
  | TInvok: forall (g:env) (e1:expr) (e2: expr) (m: MethodName) t t' rt C ps ps',
        Hastype g e1 (TRefn (TNom (TClass C)) ps') ->
        mtype(m, C) = ps ~> t ~> rt ->
        (Subtype g (TRefn (TNom (TClass C)) ps') (TRefn (TNom (TClass C)) ps)) ->
        (Hastype g e2 t') -> (Subtype g t' (tsubBV e1 t)) -> isLC e2 -> isLC e1 ->
        Hastype g (ExpMethodInvoc e1 m e2) (self (tsubBV_at 1 e1 (tsubBV e2 rt)) (ExpMethodInvoc e1 m e2))
  | TInvokI: forall (g:env) (e1:expr) (e2: expr) (m: MethodName) t t' rt I ps ps',
        Hastype g e1 (TRefn (TNom (TInterface I)) ps') ->
        mtypei(m, I) = ps ~> t ~> rt ->
        (Subtype g (TRefn (TNom (TInterface I)) ps') (TRefn (TNom (TInterface I)) ps)) ->
        (Hastype g e2 t') -> (Subtype g t' (tsubBV e1 t)) -> isLC e2 -> isLC e1 ->
        Hastype g (ExpMethodInvoc e1 m e2) (self (tsubBV_at 1 e1 (tsubBV e2 rt)) (ExpMethodInvoc e1 m e2))
  | TField: forall g e f C Fs i fi ps,
                     isLC e ->
                    Hastype g e (TRefn (TNom (TClass C)) ps) ->
                    Reffields C Fs ->
                    nth_error Fs i = Some fi ->
                    ref fi = f ->
                    Hastype g (ExpFieldAccess e f) (self (tsubBV e (ReffieldType fi)) (ExpFieldAccess e f))
  | TNew:    forall g es Ts C Fs Us fs,
                Us = map ReffieldType Fs ->
                fs = map ref Fs ->
                (Forall isLC es) ->
                Reffields C Fs ->
                Forall2 (Hastype g) es Ts ->
                Forall2 (Subtype g) Ts (map (tsubBV (ExpNew C es)) Us) ->
                Hastype g (ExpNew C es) (self (TRefn (TNom (TClass C)) PEmpty) (ExpNew C es))
  | TLet  : forall (g:env) (e_x:expr) (b:type) (e:expr) (b':type) (nms:names),
    WFtype g b' -> Hastype g e_x b -> (forall (y:vname), ~ Elem y nms -> Hastype (Cons y b g) (unbind y e) (unbindT y b') )
    -> Hastype g (ExpLet e_x e) (self b' (ExpLet e_x e))

  | TSub  : forall (g:env) (e:expr) (s:type) (t:type),
                Hastype g e s -> WFtype g t -> Subtype g s t -> Hastype g e t

where " g '|---' e ':' C " := (Hastype g e C).

Definition Terminating g e:= forall th, DenotesEnv g th -> exists e', EvalsTo (csubst th e) e' /\ isValue e'.

Definition wf_under C Ds := (forall y,  WFtype (Cons y C Empty) (openT_at 0 y Ds)).

Definition wf_under2 C Cs Ds := (forall y y', y <> y' -> WFtype (Cons y' (openT_at 0 y Cs) (Cons y C Empty)) (openT_at 1 y (openT_at 0 y' Ds))).

Definition subtype_under C Ds Cs:= (forall y, Subtype (Cons y C Empty) (openT_at 0 y Ds) (openT_at 0 y Cs)).

Definition subtype_under2 C Cs C0 D0:= (forall y y', y<>y' -> Subtype (Cons y' (openT_at 0 y Cs) (Cons y C Empty)) (openT_at 1 y (openT_at 0 y' C0)) (openT_at 1 y (openT_at 0 y' D0))) .
