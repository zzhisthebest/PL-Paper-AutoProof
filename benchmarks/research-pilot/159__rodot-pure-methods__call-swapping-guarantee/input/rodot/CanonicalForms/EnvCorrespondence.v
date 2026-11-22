Set Implicit Arguments.

Require Import LibExtra SyntaxClasses Program.Equality.

Require Import AbstractSyntax Equivalence RecordTypes TypingMode InertContext Indep GeneralTyping.

Section WithTypingMode.

Context (typing_mode: Mode).

Notation typ_refcap_corr Tw Ty := (
  match (mode_refcap_corr' typing_mode) with
  | mode_refcap_corr_same =>

    Ty = Tw
  | mode_refcap_corr_ref_mutability =>

    exists Tbnd, (Tw = (typ_mut_marker Tbnd) /\ Ty = (typ_mut_marker typ_bot))
  end) (only parsing).

Inductive typ_corr: typ -> typ -> Prop :=
| typ_corr_obj(T S U: typ):
  typ_refcap_corr S U ->
  typ_corr (typ_objref T S) (typ_objref T U)
| typ_corr_fun(t1 t2: typ):
  mode_has_fun typing_mode ->
  typ_corr (typ_fun t1 t2) (typ_fun t1 t2)
.

Inductive renv_corr: ctx -> renv -> Prop :=

| renv_corr_empty(G: ctx):
    renv_corr G renv_empty

| renv_corr_ref(G1 G2 G3: ctx)(e: renv)(w y: var)(Tw Ty: typ):
    ctx_binds_k_after w v_ref Tw G1 G2 ->
    ctx_binds_k_after y v_loc Ty G2 G3 ->
    typ_corr Tw Ty ->
    renv_corr G1 e ->
    renv_corr G1 (renv_bind e w y)
.

End WithTypingMode.

Arguments renv_corr {typing_mode}.

Arguments typ_corr {typing_mode}.

Section WithTypingMode.

Context (typing_mode: Mode).

End WithTypingMode.

Notation env_binds_more e e' :=
  (forall y w, binds w y e -> binds w y e') (only parsing).

Section WithTypingMode.

Context (typing_mode: Mode).

End WithTypingMode.
