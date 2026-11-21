Require Import Bool.

Require Import Metalib.Metatheory.

Require Import List.

Definition i : Set := nat.

Definition b : Set := bool.

Inductive typ : Set :=
 | t_int : typ
 | t_arrow (A:typ) (B:typ)
 | t_dyn : typ  .

Inductive st : Set :=
 | st_ty (A:typ).

Inductive term : Set :=
 | trm_var_b (_:nat)
 | trm_var_f (x:var)
 | trm_lit (i5:i)
 | trm_abs (A:typ) (t:term)
 | trm_app (t1:term) (t2:term)
 | trm_cast (t:term) (A:typ) (B:typ)
 | trm_add : term
 | trm_addl (i5:i)  .

Definition ctx : Set := list ( atom * typ ).

Definition ls : Set := list st.

Fixpoint open_term_wrt_term_rec (k:nat) (t_5:term) (t__6:term) {struct t__6}: term :=
   match t__6 with
   | (trm_var_b nat) =>
       match lt_eq_lt_dec nat k with
         | inleft (left _) => trm_var_b nat
         | inleft (right _) => t_5
         | inright _ => trm_var_b (nat - 1)
       end
   | (trm_var_f x) => trm_var_f x
   | (trm_lit i5) => trm_lit i5
   | (trm_abs A t) => trm_abs A (open_term_wrt_term_rec (S k) t_5 t)
   | (trm_app t1 t2) => trm_app (open_term_wrt_term_rec k t_5 t1) (open_term_wrt_term_rec k t_5 t2)
   | (trm_cast t A B) => trm_cast (open_term_wrt_term_rec k t_5 t) A B
   | trm_add => trm_add
   | (trm_addl i5) => trm_addl i5
 end.

Definition open_term_wrt_term t_5 t__6 := open_term_wrt_term_rec 0 t__6 t_5.

Inductive lc_term : term -> Prop :=
  | lc_trm_var_f : forall (x:var),
      (lc_term (trm_var_f x))
  | lc_trm_lit : forall (i5:i),
      (lc_term (trm_lit i5))
  | lc_trm_abs : forall (A:typ) (t:term),
       ( forall x , lc_term  ( open_term_wrt_term t (trm_var_f x) )  )  ->
      (lc_term (trm_abs A t))
  | lc_trm_app : forall (t1 t2:term),
      (lc_term t1) ->
      (lc_term t2) ->
      (lc_term (trm_app t1 t2))
  | lc_trm_cast : forall (t:term) (A B:typ),
      (lc_term t) ->
      (lc_term (trm_cast t A B))
  | lc_trm_add :
      (lc_term trm_add)
  | lc_trm_addl : forall (i5:i),
      (lc_term (trm_addl i5)).

Fixpoint fv_term (t_5:term) : vars :=
   match t_5 with
   | (trm_var_b nat) => {}
   | (trm_var_f x) => {{x}}
   | (trm_lit i5) => {}
   | (trm_abs A t) => (fv_term t)
   | (trm_app t1 t2) => (fv_term t1) \u (fv_term t2)
   | (trm_cast t A B) => (fv_term t)
   | trm_add => {}
   | (trm_addl i5) => {}
 end.

Fixpoint subst_term (t_5:term) (x5:var) (t__6:term) {struct t__6} : term :=
   match t__6 with
   | (trm_var_b nat) => trm_var_b nat
   | (trm_var_f x) => (if eq_var x x5 then t_5 else (trm_var_f x))
   | (trm_lit i5) => trm_lit i5
   | (trm_abs A t) => trm_abs A (subst_term t_5 x5 t)
   | (trm_app t1 t2) => trm_app (subst_term t_5 x5 t1) (subst_term t_5 x5 t2)
   | (trm_cast t A B) => trm_cast (subst_term t_5 x5 t) A B
   | trm_add => trm_add
   | (trm_addl i5) => trm_addl i5
 end.

Inductive Ground : typ -> Prop :=
  | Ground_lit :
      Ground t_int
  | Ground_dyn :
      Ground  (t_arrow t_dyn t_dyn) .

Inductive valueb : term -> Prop :=
  | valueb_lit : forall (i5:i),
      valueb (trm_lit i5)
  | valueb_add :
      valueb trm_add
  | valueb_addl : forall (i5:i),
      valueb  ( (trm_addl i5) )
  | valueb_anno : forall (A:typ) (t:term),
      lc_term (trm_abs A t) ->
      valueb (trm_abs A t)
  | valueb_fanno : forall (v:term) (A B C D:typ),
      valueb v ->
      valueb  ( (trm_cast v  (t_arrow A B)   (t_arrow C D) ) )
  | valueb_dyn : forall (v:term) (B:typ),
      valueb v ->
      Ground B ->
      valueb  ( (trm_cast v B t_dyn) ) .

Inductive sim : typ -> typ -> Prop :=
  | S_i :
      sim t_int t_int
  | S_arr : forall (A B C D:typ),
      sim A C ->
      sim B D ->
      sim (t_arrow A B) (t_arrow C D)
  | S_dynl : forall (A:typ),
      sim t_dyn A
  | S_dynr : forall (A:typ),
      sim A t_dyn.

Inductive Btyping : ctx -> term -> typ -> Prop :=
 | Btyp_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     Btyping G (trm_lit i5) t_int
 | Btyp_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
     Btyping G (trm_var_f x) A
 | Btyp_abs : forall (L:vars) (G:ctx) (A:typ) (t:term) (B:typ),
      ( forall x , x \notin  L  -> Btyping  (cons ( x , A )  G )   ( open_term_wrt_term t (trm_var_f x) )  B )  ->
     Btyping G (trm_abs A t) (t_arrow A B)
 | Btyp_app : forall (G:ctx) (t1 t2:term) (B A:typ),
     Btyping G t1 (t_arrow A B) ->
     Btyping G t2 A ->
     Btyping G (trm_app t1 t2) B
 | Btyp_add : forall (G:ctx),
     uniq  G  ->
     Btyping G trm_add (t_arrow t_int  (t_arrow t_int t_int) )
 | Btyp_addl : forall (G:ctx) (i1:i),
    uniq  G  ->
     Btyping G (trm_addl i1) (t_arrow t_int t_int)
 | Btyp_cast : forall (G:ctx) (t:term) (A B:typ),
     Btyping G t A ->
     sim A B ->
     Btyping G  ( (trm_cast t A B) )  B.

Inductive ctx_itemb : Type :=
  | appCtxLb : term -> ctx_itemb
  | appCtxRb : term -> ctx_itemb
  | castCtxb : typ -> typ -> ctx_itemb.

Inductive wellformedb : ctx_itemb -> Prop :=
  | wf_appCtxLb : forall (e : term),
                 lc_term e ->
                 wellformedb (appCtxLb e)
  | wf_appCtxRb : forall (v : term),
                 valueb v ->
                 wellformedb (appCtxRb v)
  | wf_castCtxb : forall (A B: typ),
                 wellformedb (castCtxb A B).

Definition fillb (E : ctx_itemb) (e : term) : term :=
  match E with
  | appCtxLb e2 => trm_app e e2
  | appCtxRb v1 => trm_app v1 e
  | castCtxb A B => trm_cast e A B
  end.

Inductive resb : Type :=
  | t_term  : term -> resb
  | t_blame :  resb.

Inductive bstep : term -> resb -> Prop :=
  | do_stepb E e1 e2 :
     wellformedb E ->
     bstep e1 ( t_term e2 ) ->
     bstep (fillb E e1) (t_term (fillb E e2))
  | blame_stepb E e1 :
     wellformedb E ->
     bstep e1 (t_blame) ->
     bstep (fillb E e1) (t_blame)
 | bStep_beta : forall (A:typ) (t v:term),
     lc_term (trm_abs A t) ->
     valueb v ->
     bstep (trm_app  ( (trm_abs A t) )  v)  (t_term  (open_term_wrt_term  t v )  )
 | bStep_lit : forall (i5:i),
     bstep (trm_cast (trm_lit i5) t_int t_int) (t_term (trm_lit i5))
 | bStep_abeta : forall (v1:term) (A B C D:typ) (v2:term),
     valueb  ( (trm_cast v1 (t_arrow A B) (t_arrow C D)) )  ->
     valueb v2 ->
     bstep (trm_app  ( (trm_cast v1 (t_arrow A B) (t_arrow C D)) )  v2) (t_term (trm_cast  ( (trm_app v1  ( (trm_cast v2 C A) ) ) )  B D))
 | bStep_dd : forall (v:term),
     valueb v ->
     bstep  ( (trm_cast v t_dyn t_dyn) )  (t_term v)
 | bStep_anyd : forall (v:term) (A:typ),
     valueb v ->
      not (   A  =  t_dyn   )  ->
      not (   A  =  (t_arrow t_dyn t_dyn)   )  ->
     sim A (t_arrow t_dyn t_dyn) ->
     bstep  ( (trm_cast v A t_dyn) )   (t_term (trm_cast  ( (trm_cast v A (t_arrow t_dyn t_dyn)) )  (t_arrow t_dyn t_dyn) t_dyn) )
 | bStep_dyna : forall (v:term) (A:typ),
     valueb v ->
      not (   A  =  t_dyn   )  ->
      not (   A  =  (t_arrow t_dyn t_dyn)   )  ->
     sim A (t_arrow t_dyn t_dyn) ->
     bstep  ( (trm_cast v t_dyn A) )   (t_term (trm_cast  ( (trm_cast v t_dyn (t_arrow t_dyn t_dyn)) )  (t_arrow t_dyn t_dyn) A) )
 | bStep_vany : forall (v:term) (A:typ),
     Ground A ->
     valueb v ->
     bstep  ( (trm_cast  ( (trm_cast v A t_dyn) )  t_dyn A) )  (t_term v)
 | bStep_vanyp : forall (v:term) (A B:typ),
     Ground A ->
     Ground B ->
     not (A = B) ->
     valueb v ->
     bstep  ( (trm_cast  ( (trm_cast v A t_dyn) )  t_dyn B) )  t_blame
 | bStep_add : forall (i1:i),
     bstep (trm_app trm_add (trm_lit i1)) (t_term (trm_addl i1))
 | bStep_addl : forall (i1 i2:i),
     bstep (trm_app  ( (trm_addl i1) )  (trm_lit i2))  (t_term (trm_lit ( i1  +  i2 ))).

Inductive bsteps : term -> resb -> Prop :=
  | bstep_refl e:
    bsteps e (t_term e)

  | bstep_n e t' e':
    bstep e (t_term e') ->
    bsteps e' (t_term t') ->
    bsteps e  (t_term t')

  | bstep_nb e e':
    bstep e (t_term e') ->
    bsteps e' t_blame ->
    bsteps e  t_blame

  | bstep_b e:
    bstep e (t_blame) ->
    bsteps e (t_blame).
