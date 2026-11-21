Require Import TLC.LibLN.

Require Import Program.Equality.

Require Import Coq.Lists.ListSet.

Require Import Lists.List.

Require Import equivalence.

Inductive Ord : typ -> Prop :=
| o_int   : Ord t_int
| o_arrow : forall t1 t2, Ord (t_arrow t1 t2)
| o_unit  : Ord t_unit
| o_prim  : forall i, Ord (t_prim i).

Definition DisjSpec PG A B := forall C, Ord C -> not (declarative_subtyping PG C (t_and A B)).

Notation "PG ||- A *s B" := (DisjSpec PG A B) (at level 80).

Module Typing_part.

Export Notations.

Inductive exp : Set :=
 | e_var_b  : nat -> exp
 | e_var_f  : var -> exp
 | e_lit    : nat -> exp
 | e_abs    : exp -> exp
 | e_app    : exp -> exp -> exp
 | e_typeof : exp -> typ -> exp -> typ -> exp -> exp
 | e_null   : exp
 | e_new    : MetatheoryAtom.Atom.atom -> exp.

Inductive bind : Set :=
 | bind_typ : typ -> bind.

Notation "x ~: T" := (x ~ T)
 (at level 23, left associativity) : env_scope.

Definition env := LibEnv.env typ.

Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (e_var_b nat) => If (k = nat) then e_5 else (e_var_b nat)
  | (e_var_f x) => e_var_f x
  | (e_lit i5) => e_lit i5
  | (e_abs e) => e_abs (open_exp_wrt_exp_rec (S k) e_5 e)
  | (e_app e1 e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_typeof e A e1 B e2) => e_typeof (open_exp_wrt_exp_rec k e_5 e) A (open_exp_wrt_exp_rec (S k) e_5 e1) B (open_exp_wrt_exp_rec (S k) e_5 e2)
  | (e_null) => e_null
  | e_new A  => e_new A
end.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

Notation "t 'open_ee_var' x" := (open_exp_wrt_exp t (e_var_f x)) (at level 67).

Inductive lc_exp : exp -> Prop :=
 | lc_e_var_f : forall (x:var),
     (lc_exp (e_var_f x))
 | lc_e_lit : forall i5,
     (lc_exp (e_lit i5))
 | lc_e_abs : forall (L:vars) (e:exp),
      ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_abs e))
 | lc_e_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_app e1 e2))
 | lc_e_typeof : forall (L:vars) (e:exp) (A:typ) (e1:exp) (B:typ) (e2:exp),
     (lc_exp e) ->
     ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e1 (e_var_f x) )  ) ->
     ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e2 (e_var_f x) )  ) ->
     (lc_exp (e_typeof e A e1 B e2))
 | lec_e_null :
     lc_exp e_null
 | lc_e_new : forall A,
     lc_exp (e_new A).

Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => \{}
  | (e_var_f x) => \{x}
  | (e_lit i5) => \{}
  | (e_abs e) => (fv_exp e)
  | (e_app e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_typeof e A e1 B e2) => (fv_exp e) \u (fv_exp e1) \u (fv_exp e2)
  | (e_null) => \{}
  | e_new A  => \{}
end.

Fixpoint subst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (If x = x5 then e_5 else (e_var_f x))
  | (e_lit i5) => e_lit i5
  | (e_abs e) => e_abs (subst_exp e_5 x5 e)
  | (e_app e1 e2) => e_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_typeof e A e1 B e2) => e_typeof (subst_exp e_5 x5 e) A (subst_exp e_5 x5 e1) B (subst_exp e_5 x5 e2)
  | (e_null) => e_null
  | (e_new A) => e_new A
  end.

Inductive value : exp -> Prop :=
 | val_int : forall i5,
     value (e_lit i5)
 | val_abs : forall e,
     lc_exp (e_abs e) ->
     value (e_abs e)
 | val_null :
     value e_null
 | val_new  : forall P,
     value  (e_new P).

Inductive findtype : exp -> typ -> Prop :=
 | findtype_int : forall i5,
     findtype (e_lit i5) t_int
 | findtype_arrow : forall (e:exp),
     lc_exp (e_abs e) ->
     findtype  (e_abs e) (t_arrow t_top t_bot)
 | findtype_null :
     findtype e_null t_unit
 | find_type_new : forall P,
     findtype (e_new P) (t_prim P).

Inductive typing (PG:envp) : env -> exp -> typ -> Prop :=
 | typ_lit : forall (G:env) i5,
      ok  G  ->
      okenvp PG ->
     typing PG G (e_lit i5) t_int
 | typ_null : forall G,
      ok G ->
      okenvp PG ->
      typing PG G e_null t_unit
 | typ_var : forall (G:env) (x:var) (A:typ),
      ok  G  ->
      okenvp PG ->
      wft PG A ->
      binds  x A G  ->
     typing PG G (e_var_f x) A
 | typ_app : forall (G:env) (e1 e2:exp) (B A:typ),
     okenvp PG -> wft PG A -> wft PG B ->
     typing PG G e1 (t_arrow A B) ->
     typing PG G e2 A ->
     typing PG G (e_app e1 e2) B
 | typ_sub : forall (G:env) (e:exp) (A B:typ),
     typing PG G e B ->
     declarative_subtyping PG B A ->
     typing PG G e A
 | typ_abs : forall (L:vars) (G:env) (e:exp) (A B:typ),
      okenvp PG -> wft PG A -> wft PG B ->
      ( forall x , x \notin  L  -> typing PG (G & x ~: A )   ( open_exp_wrt_exp e (e_var_f x) ) B )  ->
     typing PG G (e_abs e) (t_arrow A B)
 | typ_typeof : forall (L:vars) (G:env) (e:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
     typing PG G e (t_union A B) ->
     ( forall x , x \notin  L  -> typing PG  (G & x ~: A )   ( open_exp_wrt_exp e1 (e_var_f x) ) C ) ->
     ( forall x , x \notin  L  -> typing PG  (G & x ~: B )   ( open_exp_wrt_exp e2 (e_var_f x) ) C ) ->
     PG ||- A *s B ->
     typing PG G (e_typeof e A e1 B e2) C
 | typ_prim : forall i G,
    ok G ->
    okenvp PG -> wft PG (t_prim i) ->
     typing PG G (e_new i) (t_prim i).

Reserved Notation "PG ||- e --> e'" (at level 80).

Inductive step (PG:envp) : exp -> exp -> Prop :=
 | step_appl : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     PG ||- e1 --> e1' ->
     PG ||- (e_app e1 e2) --> (e_app e1' e2)
 | step_appr : forall (v e e':exp),
     value v ->
     PG ||- e --> e' ->
     PG ||- (e_app v e) --> (e_app v e')
 | step_beta : forall (e:exp) (v:exp),
     lc_exp (e_abs e) ->
     value v ->
     PG ||- e_app  (e_abs e) v --> (open_exp_wrt_exp e v)
 | step_typeof : forall (e:exp) (A:typ) (e1:exp) (B:typ) (e2 e':exp),
     lc_exp (e_typeof e A e1 B e2) ->
     PG ||- e --> e' ->
     PG ||- (e_typeof e A e1 B e2) --> (e_typeof e' A e1 B e2)
 | step_typeofl : forall (v:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
     lc_exp (e_typeof v A e1 B e2) ->
     value v ->
     findtype v C ->
     declarative_subtyping PG C A ->
     PG ||- (e_typeof v A e1 B e2) -->  (open_exp_wrt_exp e1 v)
 | step_typeofr : forall (v:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
    lc_exp (e_typeof v A e1 B e2) ->
     value v ->
     findtype v C ->
     declarative_subtyping PG C B ->
     PG ||- (e_typeof v A e1 B e2) -->  (open_exp_wrt_exp  e2 v )
where "PG ||- e --> e'" := (step PG e e') : env_scope.

Require Import Program.Equality.

Theorem preservation : forall PG E e e' T,
  typing PG E e T ->
  PG ||- e --> e' ->
  typing PG E e' T.

Theorem progress : forall PG e T,
    typing PG empty e T -> (value e) \/ (exists e', PG ||- e --> e').

End Typing_part.
