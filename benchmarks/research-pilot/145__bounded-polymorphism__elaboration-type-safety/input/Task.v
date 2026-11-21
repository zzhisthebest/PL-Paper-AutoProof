Require Export Metalib.Metatheory.

Require Import FSub_Definitions.

Require Import Syntax_ott.

Require Import Fii_inf.

Require Import Infrastructure.

Inductive fsub_trans_typ : env -> typ -> sty -> Prop :=
| fsub_trans_typ_top : forall FF,
    fsub_trans_typ FF typ_top sty_top
| fsub_trans_typ_nat : forall FF,
    fsub_trans_typ FF typ_nat sty_nat
| fsub_trans_typ_fvar_bind_sub_eq : forall FF a A B,
    binds a (bind_sub A) FF ->
    fsub_trans_typ FF A B ->
    fsub_trans_typ FF (typ_fvar a) (sty_and (sty_var_f a) B)
| fsub_trans_typ_arrow : forall FF A A' B B',
    fsub_trans_typ FF A A' ->
    fsub_trans_typ FF B B' ->
    fsub_trans_typ FF (typ_arrow A B) (sty_arrow A' B')
| fsub_trans_typ_all : forall L FF A B C,
    wf_typ FF A ->
    (forall X , X `notin` L ->
           fsub_trans_typ (X ~ bind_sub A ++ FF)
                          (open_tt B X)
                          (open_sty_wrt_sty C (sty_var_f X))) ->
    fsub_trans_typ FF (typ_all A B) (sty_all sty_top C)
| fsub_trans_typ_rcd_nil : forall FF,
    fsub_trans_typ FF (typ_rcd_nil) (sty_top)
| fsub_trans_typ_rcd_cons : forall FF i A' B' A B,
    fsub_trans_typ FF A A' ->
    fsub_trans_typ FF B B' ->
    rt_type B ->
    fsub_trans_typ FF (typ_rcd_cons i A B) (sty_and (sty_rcd i A') B')
.

Inductive fsub_trans_D : env -> stctx -> Prop :=
| fsub_trans_D_empty :
    fsub_trans_D nil nil
| fsub_trans_D_bind_sub : forall a FF Ttx A,
    fsub_trans_D FF Ttx ->
    a \notin dom FF \u dom Ttx ->
    fsub_trans_D (a ~ bind_sub A ++ FF) (a ~ sty_top ++ Ttx)
| fsub_trans_D_bind_typ : forall x FF Ttx A,
    fsub_trans_D FF Ttx ->
    fsub_trans_D (x ~ bind_typ A ++ FF) Ttx
.

Inductive fsub_trans_G : env -> sctx -> Prop :=
| fsub_trans_G_empty :
    fsub_trans_G nil nil
| fsub_trans_G_bind_sub : forall a FF Ttx A,
    fsub_trans_G FF Ttx ->
    a `notin` dom Ttx ->
    fsub_trans_G (a ~ bind_sub A ++ FF) Ttx
| fsub_trans_G_bind_typ : forall x FF Ttx A B,
    fsub_trans_G FF Ttx ->
    fsub_trans_typ FF A B ->
    x `notin` dom FF \u dom Ttx ->
    fsub_trans_G (x ~ bind_typ A ++ FF) (x ~ B ++ Ttx)
.

Inductive label_notin : i -> typ -> Prop :=
| label_notin_nil : forall i,
    label_notin i (typ_rcd_nil)
| label_notin_cons : forall i j A B,
    i <> j ->
    label_notin i B ->
    label_notin i (typ_rcd_cons j A B)
.

Inductive typing : env -> exp -> typ -> sexp -> Prop :=
  | typing_top : forall E,
      wf_env E ->
      typing E exp_top typ_top sexp_top
  | typing_lit : forall i E,
      wf_env E ->
      typing E (exp_lit i) typ_nat (sexp_lit i)
  | typing_var : forall E x T,
      wf_env E ->
      binds x (bind_typ T) E ->
      typing E (exp_fvar x) T (sexp_var_f x)
  | typing_abs : forall L E V e1 T1 EE A,
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ V ++ E) (open_ee e1 x) T1 (open_sexp_wrt_sexp EE (sexp_var_f x))) ->
      fsub_trans_typ E (typ_arrow V T1) A ->
      typing E (exp_abs V e1) (typ_arrow V T1) (sexp_anno (sexp_abs EE) A)
  | typing_app : forall T1 E e1 e2 T2 EE1 EE2,
      typing E e1 (typ_arrow T1 T2) EE1 ->
      typing E e2 T1 EE2 ->
      typing E (exp_app e1 e2) T2 (sexp_app EE1 EE2)
  | typing_tabs : forall L E V e1 T1 EE A,
      fsub_trans_typ E V A ->
      (forall X : atom, X `notin` L ->
                   typing (X ~ bind_sub V ++ E) (open_te e1 X)
                          (open_tt T1 X)
                          (open_sexp_wrt_sty EE (sty_var_f X))) ->
      typing E (exp_tabs V e1) (typ_all V T1) (sexp_tabs sty_top EE)
  | typing_tapp : forall T1 E e1 T T2 EE A1 A2,
      typing E e1 (typ_all T1 T2) EE ->
      fsub E T T1 ->
      fsub_trans_typ E T A1 ->
      fsub_trans_typ E (open_tt T2 T) A2 ->
      typing E (exp_tapp e1 T) (open_tt T2 T) (sexp_anno (sexp_tapp EE A1) A2)
  | typing_sub : forall S E e T EE A,
      typing E e S EE ->
      fsub E S T ->
      fsub_trans_typ E T A ->
      typing E e T (sexp_anno EE A)
  | typing_rcd_nil : forall E,
      wf_env E ->
      typing E (exp_rcd_nil) typ_rcd_nil (sexp_top)
  | typing_rcd_cons : forall E i e1 e2 T1 T2 EE1 EE2,
      typing E e1 T1 EE1 ->
      typing E e2 T2 EE2 ->
      rt_expr e2 ->
      rt_type T2 ->
      label_notin i T2 ->
      typing E (exp_rcd_cons i e1 e2) (typ_rcd_cons i T1 T2)
               (sexp_merge (sexp_rcd i EE1) EE2)
  | typing_rcd_proj : forall E i e1 T1 T2 EE1 A,
      typing E e1 (typ_rcd_cons i T1 T2) EE1 ->
      fsub_trans_typ E T1 A ->
      typing E (exp_rcd_proj e1 i) T1
               (sexp_proj (sexp_anno EE1 (sty_rcd i A)) i)
.

Theorem trans_typing : forall FF e T EE A D G,
    typing FF e T EE ->
    fsub_trans_D FF D ->
    fsub_trans_G FF G ->
    fsub_trans_typ FF T A ->
    has_type D G EE Inf A.
