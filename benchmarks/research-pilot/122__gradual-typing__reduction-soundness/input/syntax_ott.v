Require Import Bool.

Require Import Metalib.Metatheory.

Require Import List.

Require Import syntaxb_ott.

Inductive exp : Set :=
 | e_var_b (_:nat)
 | e_var_f (x:var)
 | e_lit (i5:i)
 | e_abs (A:typ) (e:exp) (B:typ)
 | e_app (e1:exp) (e2:exp)
 | e_anno (e:exp) (A:typ)
 | e_add : exp
 | e_addl (i5:i)  .

Inductive dirflag : Set :=
 | Inf : dirflag
 | Chk : dirflag.

Definition ctx : Set := list ( atom * typ ).

Definition ls : Set := list st.

Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (e_var_b nat) =>
      match lt_eq_lt_dec nat k with
        | inleft (left _) => e_var_b nat
        | inleft (right _) => e_5
        | inright _ => e_var_b (nat - 1)
      end
  | (e_var_f x) => e_var_f x
  | (e_lit i5) => e_lit i5
  | (e_abs A e B) => e_abs A (open_exp_wrt_exp_rec (S k) e_5 e) B
  | (e_app e1 e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_anno e A) => e_anno (open_exp_wrt_exp_rec k e_5 e) A
  | e_add => e_add
  | (e_addl i5) => e_addl i5
end.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

Inductive lc_exp : exp -> Prop :=
 | lc_e_var_f : forall (x:var),
     (lc_exp (e_var_f x))
 | lc_e_lit : forall (i5:i),
     (lc_exp (e_lit i5))
 | lc_e_abs : forall (A:typ) (e:exp) (B:typ),
      ( forall x , lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_abs A e B))
 | lc_e_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_app e1 e2))
 | lc_e_anno : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_exp (e_anno e A))
 | lc_e_add :
     (lc_exp e_add)
 | lc_e_addl : forall (i5:i),
     (lc_exp (e_addl i5)).

Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {{x}}
  | (e_lit i5) => {}
  | (e_abs A e B) => (fv_exp e)
  | (e_app e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_anno e A) => (fv_exp e)
  | e_add => {}
  | (e_addl i5) => {}
end.

Fixpoint subst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (if eq_var x x5 then e_5 else (e_var_f x))
  | (e_lit i5) => e_lit i5
  | (e_abs A e B) => e_abs A (subst_exp e_5 x5 e) B
  | (e_app e1 e2) => e_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_anno e A) => e_anno (subst_exp e_5 x5 e) A
  | e_add => e_add
  | (e_addl i5) => e_addl i5
end.

Fixpoint principal_type (v:exp) : typ :=
  match v with
  | (e_lit i5) => t_int
  | (e_abs A e B) => (t_arrow A B)
  | (e_anno e A) => A
  | (e_add) => (t_arrow t_int (t_arrow t_int t_int))
  | (e_addl i5) => (t_arrow t_int t_int)
  | _ => t_dyn
  end.

Inductive value : exp -> Prop :=
 | value_lit : forall (i5:i),
     value (e_lit i5)
 | value_add :
     value e_add
 | value_addl : forall (i5:i),
     value  ( (e_addl i5) )
 | value_anno : forall (A:typ) (e:exp) (B:typ),
     lc_exp (e_abs A e B) ->
     value (e_abs A e B)
 | value_fanno : forall (v:exp) (A B C D:typ),
     value v ->
      (t_arrow C D)  =   (principal_type   ( v )  )   ->
     value (e_anno v (t_arrow A B))
 | value_dyn : forall (v:exp),
     Ground   (principal_type  v )   ->
     value v ->
     value  ( (e_anno v t_dyn) ) .

Definition FLike A := not (A = t_dyn) /\ not (A = (t_arrow t_dyn t_dyn)) /\ (sim A (t_arrow t_dyn t_dyn)).

Inductive Typing : ctx -> exp -> dirflag -> typ -> Prop :=
 | Typ_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     Typing G (e_lit i5) Inf t_int
 | Typ_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
     Typing G (e_var_f x) Inf A
 | Typ_abs : forall (L:vars) (G:ctx) (A:typ) (e:exp) (B:typ),
      ( forall x , x \notin  L  -> Typing  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk B )  ->
     Typing G (e_abs A e B) Inf (t_arrow A B)
 | Typ_app : forall (G:ctx) (e1 e2:exp) (B A:typ),
     Typing G e1 Inf (t_arrow A B) ->
     Typing G e2 Chk A ->
     Typing G (e_app e1 e2) Inf B
 | Typ_add : forall (G:ctx),
     uniq  G  ->
     Typing G e_add Inf (t_arrow t_int  (t_arrow t_int t_int) )
 | Typ_addl : forall (G:ctx) (i1:i),
     uniq  G  ->
     Typing G (e_addl i1) Inf (t_arrow t_int t_int)
 | Typ_anno : forall (G:ctx) (e:exp) (A:typ),
     Typing G e Chk A ->
     Typing G  ( (e_anno e A) )  Inf A
 | Typ_sim : forall (G:ctx) (e:exp) (B A:typ),
     Typing G e Inf A ->
     sim A B ->
     Typing G e Chk B.

Inductive ttyping : ctx -> exp -> dirflag -> typ -> term -> Prop :=
 | ttyp_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     ttyping G (e_lit i5) Inf t_int (trm_lit i5)
 | ttyp_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
     ttyping G (e_var_f x) Inf A (trm_var_f x)
 | ttyp_abs : forall (L:vars) (G:ctx) (A:typ) (e:exp) (B:typ) (t:term),
      ( forall x , x \notin  L  -> ttyping  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk B ( open_term_wrt_term t (trm_var_f x) ))  ->
     ttyping G (e_abs A e B) Inf (t_arrow A B) (trm_abs A t)
 | ttyp_app : forall (G:ctx) (e1 e2:exp) (B A:typ) (t1 t2:term),
     ttyping G e1 Inf (t_arrow A B) t1 ->
     ttyping G e2 Chk A t2 ->
     ttyping G (e_app e1 e2) Inf B (trm_app t1 t2)
 | ttyp_add : forall (G:ctx),
      uniq  G  ->
     ttyping G e_add Inf (t_arrow t_int  (t_arrow t_int t_int) ) trm_add
 | ttyp_addl : forall (G:ctx) (i1:i),
      uniq  G  ->
     ttyping G (e_addl i1) Inf (t_arrow t_int t_int) (trm_addl i1)
 | ttyp_anno : forall (G:ctx) (e:exp) (A:typ) (t:term),
     ttyping G e Chk A t ->
     ttyping G  ( (e_anno e A) )  Inf A t
 | ttyp_sim : forall (G:ctx) (e:exp) (B A:typ) (t:term),
     ttyping G e Inf A t ->
     sim A B ->
     ttyping G e Chk B (trm_cast t A B).

Inductive ctx_item : Type :=
     | appCtxL : exp -> ctx_item
     | appCtxR : exp -> ctx_item
     | annoCtx : typ -> ctx_item.

Inductive wellformed : ctx_item -> Prop :=
     | wf_appCtxL : forall (e : exp),
                   lc_exp e ->
                    wellformed (appCtxL e)
     | wf_appCtxR : forall (v : exp),
                    value v ->
                    wellformed (appCtxR v)
     | wf_annoCtx : forall (A : typ),
                    wellformed (annoCtx A).

Definition fill (E : ctx_item) (e : exp) : exp :=
     match E with
     | appCtxL e2 => e_app e e2
     | appCtxR v1 => e_app v1 e
     | annoCtx A => e_anno e A
     end.

Inductive res : Type :=
     | e_exp  : exp -> res
     | e_blame : res.

Inductive TypedReduce : exp -> typ -> res -> Prop :=
 | TReduce_abs: forall v A B C D,
   sim (t_arrow C D) (t_arrow A B) ->
   principal_type v = (t_arrow C D) ->
   TypedReduce v (t_arrow A B) (e_exp (e_anno v (t_arrow A B)))
  | TReduce_v : forall (v:exp),
   Ground(principal_type v) ->
   TypedReduce v t_dyn (e_exp (e_anno v t_dyn))
 | TReduce_lit : forall (i5:i),
     TypedReduce (e_lit i5) t_int (e_exp (e_lit i5))
 | TReduce_dd : forall (v:exp),
     lc_exp v ->
     TypedReduce  ( (e_anno v t_dyn) )  t_dyn  (e_exp  (e_anno v t_dyn) )
 | TReduce_anyd : forall (v:exp),
      FLike (principal_type  v )  ->
     TypedReduce v t_dyn  (e_exp (e_anno  ( (e_anno v (t_arrow t_dyn t_dyn)) )  t_dyn) )
 | TReduce_dyna : forall (v:exp) (A:typ),
      FLike A ->
     sim (principal_type v) A ->
    TypedReduce  ( (e_anno v t_dyn) )  A  (e_exp (e_anno v A) )
 | TReduce_vany : forall (v:exp),
   TypedReduce (e_anno v t_dyn) (principal_type  v) (e_exp v)
 | TReduce_blame : forall (v:exp) (A:typ),
      not (sim A (principal_type  v ))  ->
     TypedReduce (e_anno v t_dyn) A e_blame.

Inductive step : exp -> res -> Prop :=
  | do_step E e1 e2 :
       wellformed E ->
       step e1 (e_exp e2 ) ->
      step (fill E e1) (e_exp (fill E e2))
  | blame_step E e1:
      wellformed E ->
      step e1 e_blame ->
      step (fill E e1) e_blame
 | Step_beta : forall (A:typ) (e:exp) (B:typ) (v v' : exp),
    lc_exp (e_abs A e B) ->
    value v ->
    TypedReduce v A (e_exp v') ->
    step (e_app  ( (e_abs A e B) )  v)  (e_exp (e_anno  (  (open_exp_wrt_exp  e v' )  )  B) )
 | Step_betap : forall (A:typ) (e:exp) (B:typ) (v v':exp),
    lc_exp (e_abs A e B) ->
    value v ->
    TypedReduce v A e_blame ->
    step (e_app  ( (e_abs A e B) )  v)  e_blame
 | Step_annov : forall (v:exp) (A:typ) (v':res),
     value v ->
     TypedReduce v A v' ->
     not (value (e_anno v A)) ->
     step (e_anno v A) v'
 | Step_add : forall (v1:exp) (i1:i),
     value v1 ->
     TypedReduce v1 t_int (e_exp (e_lit i1)) ->
     step (e_app e_add v1) (e_exp (e_addl i1))
 | Step_addp : forall (v1:exp),
     value v1 ->
     TypedReduce v1 t_int e_blame ->
     step (e_app e_add v1) e_blame
 | Step_addl : forall (i1:i) (v2:exp) (i2:i),
     value v2 ->
     TypedReduce v2 t_int (e_exp (e_lit i2)) ->
     step (e_app  ( (e_addl i1) )  v2)  (e_exp (e_lit ( i1  +  i2 )))
 | Step_addlp : forall (i1:i) (v2:exp),
     value v2 ->
     TypedReduce v2 t_int e_blame ->
     step (e_app  ( (e_addl i1) )  v2)  e_blame
 | Step_abeta : forall (v1:exp) (A B:typ) (v2 v2':exp),
     value  ( (e_anno v1 (t_arrow A B)) )  ->
     TypedReduce v2 A (e_exp v2') ->
     value v2 ->
     step (e_app  ( (e_anno v1 (t_arrow A B)) )  v2) (e_exp (e_anno  ( (e_app v1 v2') )  B))
 | Step_abetap : forall (v1:exp) (A B:typ) (v2 v2':exp),
     value  ( (e_anno v1 (t_arrow A B)) )  ->
     TypedReduce v2 A e_blame ->
     value v2 ->
     step (e_app  ( (e_anno v1 (t_arrow A B)) )  v2) e_blame.

Inductive steps : exp -> res -> Prop :=
  | step_refl e:
    steps e (e_exp e)

  | step_n e t' e':
    step e (e_exp e') ->
    steps e' (e_exp t') ->
    steps e  (e_exp t')

  | step_nb e e':
    step e (e_exp e') ->
    steps e' e_blame ->
    steps e  e_blame

  | step_b e:
    step e (e_blame) ->
    steps e (e_blame).
