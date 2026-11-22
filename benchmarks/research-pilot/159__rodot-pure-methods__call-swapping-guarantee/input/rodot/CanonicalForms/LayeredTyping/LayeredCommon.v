Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode Equivalence GeneralTyping.

Require Import PreciseTyping RecordTypes InertContext TightTyping Subenvironments Narrowing InertTightSubtyping EnvCorrespondence Indep Weakening Orctx Logctx.

Section WithTypingMode.

Context {typing_mode: Mode}.

Inductive logctx_tyq: renv -> logctx -> logctx -> Prop :=
| logctx_tyq_nil e:
    logctx_tyq e logctx_nil logctx_nil
| logctx_tyq_orl e oc1 oc2 T1 T2:
    typing_equiv e T1 T2 ->
    logctx_tyq e oc1 oc2 ->
    logctx_tyq e (logctx_orl oc1 T1) (logctx_orl oc2 T2)
| logctx_tyq_orr e oc1 oc2 T1 T2:
    typing_equiv e T1 T2 ->
    logctx_tyq e oc1 oc2 ->
    logctx_tyq e (logctx_orr T1 oc1) (logctx_orr T2 oc2)
| logctx_tyq_andl e oc1 oc2 T1 T2:
    typing_equiv e T1 T2 ->
    logctx_tyq e oc1 oc2 ->
    logctx_tyq e (logctx_andl oc1 T1) (logctx_andl oc2 T2)
| logctx_tyq_andr e oc1 oc2 T1 T2:
    typing_equiv e T1 T2 ->
    logctx_tyq e oc1 oc2 ->
    logctx_tyq e (logctx_andr T1 oc1) (logctx_andr T2 oc2)
.

Inductive orctx_tyq: renv -> orctx -> orctx -> Prop :=
| orctx_tyq_nil e:
    orctx_tyq e orctx_nil orctx_nil
| orctx_tyq_orl e oc1 oc2 T1 T2:
    typing_equiv e T1 T2 ->
    orctx_tyq e oc1 oc2 ->
    orctx_tyq e (orctx_l oc1 T1) (orctx_l oc2 T2)
| orctx_tyq_orr e oc1 oc2 T1 T2:
    typing_equiv e T1 T2 ->
    orctx_tyq e oc1 oc2 ->
    orctx_tyq e (orctx_r T1 oc1) (orctx_r T2 oc2)
.

Inductive ty_or_closure (P: typ -> Prop): typ -> Prop :=
| ty_or_closure_atomic (T: typ):
    P T ->
    ty_or_closure P T
| ty_or_closure_l T U:
    ty_or_closure P T ->
    ty_or_closure P (typ_or T U)
| ty_or_closure_r T U:
    ty_or_closure P T ->
    ty_or_closure P (typ_or U T)
| ty_or_closure_top:
    ty_or_closure P typ_top
.

Inductive typ_atomic: typ -> Prop :=
| typ_atomic_rcd D:
    typ_atomic (typ_rcd D)
| typ_atomic_fun S T:
    typ_atomic (typ_fun S T)
.

Inductive ty_and_closure (P: typ -> Prop): typ -> Prop :=
| ty_and_closure_atomic (T: typ):
    P T ->
    ty_and_closure P T
| ty_and_closure_and T U:
    ty_and_closure P T ->
    ty_and_closure P U ->
    ty_and_closure P (typ_and T U)
.

End WithTypingMode.

Notation ty_pf_not_typ G x A := (forall U TL TU, G ⊢! x ∶ U ⪼ typ_rcd (dec_typ A TL TU) -> False) (only parsing).

Definition ty_pf_or_none G x A TL TU := ((exists U, G ⊢! x ∶ U ⪼ typ_rcd (dec_typ A TL TU)) \/ ty_pf_not_typ G x A).

Notation typ_NM T1 T2 := (typ_or typ_nocap (typ_rcd (dec_typ (typ_label_refcap typ_refcap_mutability) T1 T2))) (only parsing).

Notation typ_NM_canon := (typ_NM typ_top typ_bot) (only parsing).

Section WithTypingMode.

Context {typing_mode: Mode}.

Inductive typ_logic_toplike (G: ctx) (e: renv): typ -> Prop :=
| typ_logic_toplike_top:
    typ_logic_toplike G e typ_top
| typ_logic_toplike_NM T1 T2:
    mode_has_top_nm_subtype typing_mode ->
    (mode_has_top_nm_complement typing_mode -> forall x0 : var, G ⁏ e ⊢# T1 /[-> x0] <: typ_bot) ->
    typ_logic_toplike G e (typ_NM T1 T2)
| typ_logic_toplike_has_top TL1 TU1:
  inert G ->
  renv_corr G e ->
  mode_has_mut_top typing_mode ->
  (forall x : var, G⁏e ⊢# TL1/[-> x] <: typ_bot) ->
  (forall x : var, G⁏e ⊢# typ_top <: TU1/[-> x]) ->
  typ_logic_toplike G e (typ_rcd (dec_typ (typ_label_refcap typ_refcap_mutability) TL1 TU1))
.

Inductive ty_inv_logic_liftable (G: ctx) (e: renv): forall (V S: typ), Prop :=
| ty_inv_logic_liftable_not_and V S:
  (forall oc T U, V <> orctx_typ oc (typ_and T U)) ->
  ty_inv_logic_liftable G e V S
| ty_inv_logic_liftable_toplike V S:
  typ_logic_toplike G e S ->
  ty_inv_logic_liftable G e V S
.

Inductive ty_inv_main_liftable: forall (T S: typ), Prop :=
| ty_inv_main_liftable_not_bndsel T S:
  (forall oc x A y, T <> logctx_typ oc (typ_sel x A y)) ->
  (forall oc U, T <> logctx_typ oc (typ_bnd U)) ->
  ty_inv_main_liftable T S
.

End WithTypingMode.

Section WithTypingMode.

Context {typing_mode: Mode}.

End WithTypingMode.
