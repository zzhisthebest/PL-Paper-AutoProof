Require Import Bool.

From TLC Require Import LibLN.
Require Import PTS_Spec.

Require Import List.

Definition x : Set := var.

Definition nat : Set := nat.

Definition sort : Set := sort.

Inductive trm : Set :=
 | trm_var_b (_:nat)
 | trm_var_f (x5:var)
 | trm_sort (s:sort)
 | trm_app (e1:trm) (e2:trm)
 | trm_abs (A:trm) (e:trm)
 | trm_prod (A:trm) (B:trm)
 | trm_mu (A:trm) (e:trm)  .

Definition env := LibEnv.env trm.

Fixpoint open_trm_wrt_trm_rec (k:nat) (e_5:trm) (e__6:trm) {struct e__6}: trm :=
  match e__6 with
  | (trm_var_b nat) => If (k = nat) then e_5 else (trm_var_b nat)
  | (trm_var_f x5) => trm_var_f x5
  | (trm_sort s) => trm_sort s
  | (trm_app e1 e2) => trm_app (open_trm_wrt_trm_rec k e_5 e1) (open_trm_wrt_trm_rec k e_5 e2)
  | (trm_abs A e) => trm_abs (open_trm_wrt_trm_rec k e_5 A) (open_trm_wrt_trm_rec (S k) e_5 e)
  | (trm_prod A B) => trm_prod (open_trm_wrt_trm_rec k e_5 A) (open_trm_wrt_trm_rec (S k) e_5 B)
  | (trm_mu A e) => trm_mu (open_trm_wrt_trm_rec k e_5 A) (open_trm_wrt_trm_rec (S k) e_5 e)
end.

Definition open_trm_wrt_trm e_5 e__6 := open_trm_wrt_trm_rec 0 e__6 e_5.

Inductive lc_trm : trm -> Prop :=
 | lc_trm_var_f : forall (x5:var),
     (lc_trm (trm_var_f x5))
 | lc_trm_sort : forall (s:sort),
     (lc_trm (trm_sort s))
 | lc_trm_app : forall (e1 e2:trm),
     (lc_trm e1) ->
     (lc_trm e2) ->
     (lc_trm (trm_app e1 e2))
 | lc_trm_abs : forall (L:vars) (A e:trm),
     (lc_trm A) ->
      ( forall x5 , x5 \notin  L  -> lc_trm  ( open_trm_wrt_trm e (trm_var_f x5) )  )  ->
     (lc_trm (trm_abs A e))
 | lc_trm_prod : forall (L:vars) (A B:trm),
     (lc_trm A) ->
      ( forall x5 , x5 \notin  L  -> lc_trm  ( open_trm_wrt_trm B (trm_var_f x5) )  )  ->
     (lc_trm (trm_prod A B))
 | lc_trm_mu : forall (L:vars) (A e:trm),
     (lc_trm A) ->
      ( forall x5 , x5 \notin  L  -> lc_trm  ( open_trm_wrt_trm e (trm_var_f x5) )  )  ->
     (lc_trm (trm_mu A e)).

Fixpoint fv_trm (e_5:trm) : vars :=
  match e_5 with
  | (trm_var_b nat) => \{}
  | (trm_var_f x5) => \{x5}
  | (trm_sort s) => \{}
  | (trm_app e1 e2) => (fv_trm e1) \u (fv_trm e2)
  | (trm_abs A e) => (fv_trm A) \u (fv_trm e)
  | (trm_prod A B) => (fv_trm A) \u (fv_trm B)
  | (trm_mu A e) => (fv_trm A) \u (fv_trm e)
end.

Fixpoint subst_trm (e_5:trm) (y5:var) (e__6:trm) {struct e__6} : trm :=
  match e__6 with
  | (trm_var_b nat) => trm_var_b nat
  | (trm_var_f x5) => (If x5 = y5 then e_5 else (trm_var_f x5))
  | (trm_sort s) => trm_sort s
  | (trm_app e1 e2) => trm_app (subst_trm e_5 y5 e1) (subst_trm e_5 y5 e2)
  | (trm_abs A e) => trm_abs (subst_trm e_5 y5 A) (subst_trm e_5 y5 e)
  | (trm_prod A B) => trm_prod (subst_trm e_5 y5 A) (subst_trm e_5 y5 B)
  | (trm_mu A e) => trm_mu (subst_trm e_5 y5 A) (subst_trm e_5 y5 e)
end.

Definition Ax := pts_axiom PTS_Spec.PTS.

Definition Rel := pts_rules PTS_Spec.PTS.

Definition AxUniq := pts_axuniq PTS_Spec.PTS.

Definition RelUniq := pts_reluniq PTS_Spec.PTS.

Definition AxDec := pts_axdec PTS_Spec.PTS.

Definition RelDec := pts_reldec PTS_Spec.PTS.

Definition relation := trm -> trm -> Prop.

Inductive star_ (R : relation) : relation :=
  | star_refl : forall t,
      lc_trm t ->
      star_ R t t
  | star_trans : forall t2 t1 t3,
      star_ R t1 t2 -> star_ R t2 t3 -> star_ R t1 t3
  | star_step : forall t t',
      R t t' -> star_ R t t'.

Notation "R 'star'" := (star_ R) (at level 69).

Inductive equiv_ (R : relation) : relation :=
  | equiv_refl : forall t,
      lc_trm t ->
      equiv_ R t t
  | equiv_sym: forall t t',
      equiv_ R t t' ->
      equiv_ R t' t
  | equiv_trans : forall t2 t1 t3,
      equiv_ R t1 t2 -> equiv_ R t2 t3 -> equiv_ R t1 t3
  | equiv_step : forall t t',
      R t t' -> equiv_ R t t'.

Notation "R 'equiv'" := (equiv_ R) (at level 69).

Inductive iter_ (R : relation) : relation :=
  | iter_trans : forall t2 t1 t3,
      iter_ R t1 t2 -> iter_ R t2 t3 -> iter_ R t1 t3
  | iter_step : forall t t',
      R t t' -> iter_ R t t'.

Notation "R 'iter'" := (iter_ R) (at level 69).

Inductive value : trm -> Prop :=
 | value_sort : forall (s:sort),
     value (trm_sort s)
 | value_abs : forall (A e:trm),
     lc_trm A ->
     lc_trm (trm_abs A e) ->
     value (trm_abs A e)
 | value_prod : forall (A B:trm),
     lc_trm A ->
     lc_trm (trm_prod A B) ->
     value (trm_prod A B).

Inductive reduct : trm -> trm -> Prop :=
 | r_beta : forall (A e1 e2:trm),
     lc_trm A ->
     lc_trm (trm_abs A e1) ->
     lc_trm e2 ->
     reduct (trm_app  ( (trm_abs A e1) )  e2)  (open_trm_wrt_trm  e1   e2 )
 | r_app : forall (e1 e2 e1':trm),
     lc_trm e2 ->
     reduct e1 e1' ->
     reduct (trm_app e1 e2) (trm_app e1' e2)
 | r_mu : forall (A e:trm),
     lc_trm A ->
     lc_trm (trm_mu A e) ->
     reduct (trm_mu A e)  (open_trm_wrt_trm  e   (trm_mu A e) ) .

Inductive beta : trm -> trm -> Prop :=
 | beta_red : forall (A e1 e2:trm),
     lc_trm A ->
     lc_trm (trm_abs A e1) ->
     lc_trm e2 ->
     beta (trm_app  ( (trm_abs A e1) )  e2)  (open_trm_wrt_trm  e1   e2 )
 | beta_app1 : forall (e1 e2 e1':trm),
     lc_trm e2 ->
     beta e1 e1' ->
     beta (trm_app e1 e2) (trm_app e1' e2)
 | beta_app2 : forall (e1 e2 e2':trm),
     lc_trm e1 ->
     beta e2 e2' ->
     beta (trm_app e1 e2) (trm_app e1 e2')
 | beta_abs1 : forall (A e A':trm),
     lc_trm (trm_abs A e) ->
     beta A A' ->
     beta (trm_abs A e) (trm_abs A' e)
 | beta_abs2 : forall (L:vars) (A e e':trm),
     lc_trm A ->
      ( forall x5 , x5 \notin  L  -> beta  ( open_trm_wrt_trm e (trm_var_f x5) )   ( open_trm_wrt_trm e' (trm_var_f x5) )  )  ->
     beta (trm_abs A e) (trm_abs A e')
 | beta_prod1 : forall (A B A':trm),
     lc_trm (trm_prod A B) ->
     beta A A' ->
     beta (trm_prod A B) (trm_prod A' B)
 | beta_prod2 : forall (L:vars) (A B B':trm),
     lc_trm A ->
      ( forall x5 , x5 \notin  L  -> beta  ( open_trm_wrt_trm B (trm_var_f x5) )   ( open_trm_wrt_trm B' (trm_var_f x5) )  )  ->
     beta (trm_prod A B) (trm_prod A B')
 | beta_mured : forall (A e:trm),
     lc_trm A ->
     lc_trm (trm_mu A e) ->
     beta (trm_mu A e)  (open_trm_wrt_trm  e   (trm_mu A e) )
 | beta_mu1 : forall (A e A':trm),
     lc_trm (trm_mu A e) ->
     beta A A' ->
     beta (trm_mu A e) (trm_mu A' e)
 | beta_mu2 : forall (L:vars) (A e e':trm),
     lc_trm A ->
      ( forall x5 , x5 \notin  L  -> beta  ( open_trm_wrt_trm e (trm_var_f x5) )   ( open_trm_wrt_trm e' (trm_var_f x5) )  )  ->
     beta (trm_mu A e) (trm_mu A e').

Inductive para : trm -> trm -> Prop :=
 | para_red : forall (L:vars) (A e1 e2 e1' e2':trm),
      (lc_trm ( (trm_abs A e1') ))  ->
      ( forall x5 , x5 \notin  L  -> para  ( open_trm_wrt_trm e1 (trm_var_f x5) )   ( open_trm_wrt_trm e1' (trm_var_f x5) )  )  ->
     para e2 e2' ->
     para (trm_app  ( (trm_abs A e1) )  e2)  (open_trm_wrt_trm  e1'   e2' )
 | para_var : forall (x5:var),
     para (trm_var_f x5) (trm_var_f x5)
 | para_sort : forall (s:sort),
     para (trm_sort s) (trm_sort s)
 | para_app : forall (e1 e2 e1' e2':trm),
     para e1 e1' ->
     para e2 e2' ->
     para (trm_app e1 e2) (trm_app e1' e2')
 | para_abs : forall (L:vars) (A e A' e':trm),
     para A A' ->
      ( forall x5 , x5 \notin  L  -> para  ( open_trm_wrt_trm e (trm_var_f x5) )   ( open_trm_wrt_trm e' (trm_var_f x5) )  )  ->
     para (trm_abs A e) (trm_abs A' e')
 | para_prod : forall (L:vars) (A B A' B':trm),
     para A A' ->
      ( forall x5 , x5 \notin  L  -> para  ( open_trm_wrt_trm B (trm_var_f x5) )   ( open_trm_wrt_trm B' (trm_var_f x5) )  )  ->
     para (trm_prod A B) (trm_prod A' B')
 | para_mured : forall (L:vars) (A e e' A':trm),
     para A A' ->
      ( forall x5 , x5 \notin  L  -> para  ( open_trm_wrt_trm e (trm_var_f x5) )   ( open_trm_wrt_trm e' (trm_var_f x5) )  )  ->
     para (trm_mu A e)  (open_trm_wrt_trm  e'   (trm_mu A' e') )
 | para_mu : forall (L:vars) (A e A' e':trm),
     para A A' ->
      ( forall x5 , x5 \notin  L  -> para  ( open_trm_wrt_trm e (trm_var_f x5) )   ( open_trm_wrt_trm e' (trm_var_f x5) )  )  ->
     para (trm_mu A e) (trm_mu A' e').

Inductive dpara : trm -> trm -> Prop :=
 | dpara_red : forall (A e1 e2:trm),
     lc_trm A ->
     lc_trm (trm_abs A e1) ->
     lc_trm e2 ->
     dpara (trm_app  ( (trm_abs A e1) )  e2)  (open_trm_wrt_trm  e1   e2 )
 | dpara_var : forall (x5:var),
     dpara (trm_var_f x5) (trm_var_f x5)
 | dpara_sort : forall (s:sort),
     dpara (trm_sort s) (trm_sort s)
 | dpara_app : forall (e1 e2 e1' e2':trm),
     dpara e1 e1' ->
     dpara e2 e2' ->
     dpara (trm_app e1 e2) (trm_app e1' e2')
 | dpara_abs : forall (L:vars) (A e A' e':trm),
     dpara A A' ->
      ( forall x5 , x5 \notin  L  -> dpara  ( open_trm_wrt_trm e (trm_var_f x5) )   ( open_trm_wrt_trm e' (trm_var_f x5) )  )  ->
     dpara (trm_abs A e) (trm_abs A' e')
 | dpara_prod : forall (L:vars) (A B A' B':trm),
     dpara A A' ->
      ( forall x5 , x5 \notin  L  -> dpara  ( open_trm_wrt_trm B (trm_var_f x5) )   ( open_trm_wrt_trm B' (trm_var_f x5) )  )  ->
     dpara (trm_prod A B) (trm_prod A' B')
 | dpara_mured : forall (A e:trm),
     lc_trm A ->
     lc_trm (trm_mu A e) ->
     dpara (trm_mu A e)  (open_trm_wrt_trm  e   (trm_mu A e) )
 | dpara_mu : forall (L:vars) (A e A' e':trm),
     dpara A A' ->
      ( forall x5 , x5 \notin  L  -> dpara  ( open_trm_wrt_trm e (trm_var_f x5) )   ( open_trm_wrt_trm e' (trm_var_f x5) )  )  ->
     dpara (trm_mu A e) (trm_mu A' e').

Inductive typing : env -> trm -> trm -> Prop :=
 | t_ax : forall (G:env) (s1 s2:sort),
     wf G ->
      (Ax ( s1 ) ( s2 ) )  ->
     typing G (trm_sort s1) (trm_sort s2)
 | t_var : forall (G:env) (x5:var) (A:trm),
     wf G ->
      binds ( x5 ) ( A ) ( G )  ->
     typing G (trm_var_f x5) A
 | t_abs : forall (L:vars) (G:env) (A e B:trm) (s1 s2 s3:sort),
     typing G A (trm_sort s1) ->
      ( forall x5 , x5 \notin  L  -> typing  ( G  &  x5 ~ A )   ( open_trm_wrt_trm e (trm_var_f x5) )   ( open_trm_wrt_trm B (trm_var_f x5) )  )  ->
      ( forall x5 , x5 \notin  L  -> typing  ( G  &  x5 ~ A )   ( open_trm_wrt_trm B (trm_var_f x5) )  (trm_sort s2) )  ->
      (Rel ( s1 ) ( s2 ) ( s3 ) )  ->
     typing G (trm_abs A e) (trm_prod A B)
 | t_app : forall (G:env) (e1 e2 B A:trm),
     typing G e1 (trm_prod A B) ->
     typing G e2 A ->
     typing G (trm_app e1 e2)  (open_trm_wrt_trm  B   e2 )
 | t_prod : forall (L:vars) (G:env) (A B:trm) (s3 s1 s2:sort),
     typing G A (trm_sort s1) ->
      ( forall x5 , x5 \notin  L  -> typing  ( G  &  x5 ~ A )   ( open_trm_wrt_trm B (trm_var_f x5) )  (trm_sort s2) )  ->
      (Rel ( s1 ) ( s2 ) ( s3 ) )  ->
     typing G (trm_prod A B) (trm_sort s3)
 | t_mu : forall (L:vars) (G:env) (A e:trm) (s:sort),
     typing G A (trm_sort s) ->
      ( forall x5 , x5 \notin  L  -> typing  ( G  &  x5 ~ A )   ( open_trm_wrt_trm e (trm_var_f x5) )  A )  ->
     typing G (trm_mu A e) A
 | t_conv : forall (G:env) (e B A:trm) (s:sort),
     typing G e A ->
     typing G B (trm_sort s) ->
      ((beta equiv) ( A ) ( B ))  ->
     typing G e B
with wf : env -> Prop :=
 | wf_nil :
     wf  empty
 | wf_cons : forall (G:env) (x5:var) (A:trm) (s:sort),
     typing G A (trm_sort s) ->
      ( x5  # ( G ))  ->
     wf  ( G  &  x5 ~ A ) .

Inductive styping : env -> trm -> trm -> Prop :=
 | ts_ax : forall (G:env) (s1 s2:sort),
     swf G ->
      (Ax ( s1 ) ( s2 ) )  ->
     styping G (trm_sort s1) (trm_sort s2)
 | ts_var : forall (G:env) (x5:var) (A:trm),
     swf G ->
      binds ( x5 ) ( A ) ( G )  ->
     styping G (trm_var_f x5) A
 | ts_abs : forall (L:vars) (G:env) (A e B:trm) (s1 s2 s3:sort),
     styping G A (trm_sort s1) ->
      ( forall x5 , x5 \notin  L  -> styping  ( G  &  x5 ~ A )   ( open_trm_wrt_trm e (trm_var_f x5) )   ( open_trm_wrt_trm B (trm_var_f x5) )  )  ->
      ( forall x5 , x5 \notin  L  -> styping  ( G  &  x5 ~ A )   ( open_trm_wrt_trm B (trm_var_f x5) )  (trm_sort s2) )  ->
      (Rel ( s1 ) ( s2 ) ( s3 ) )  ->
     styping G (trm_abs A e) (trm_prod A B)
 | ts_app : forall (G:env) (e1 e2 B A:trm),
     styping G e1 (trm_prod A B) ->
     styping G e2 A ->
     styping G (trm_app e1 e2)  (open_trm_wrt_trm  B   e2 )
 | ts_prod : forall (L:vars) (G:env) (A B:trm) (s3 s1 s2:sort),
     styping G A (trm_sort s1) ->
      ( forall x5 , x5 \notin  L  -> styping  ( G  &  x5 ~ A )   ( open_trm_wrt_trm B (trm_var_f x5) )  (trm_sort s2) )  ->
      (Rel ( s1 ) ( s2 ) ( s3 ) )  ->
     styping G (trm_prod A B) (trm_sort s3)
 | ts_mu : forall (L:vars) (G:env) (A e:trm) (s:sort),
     styping G A (trm_sort s) ->
      ( forall x5 , x5 \notin  L  -> styping  ( G  &  x5 ~ A )   ( open_trm_wrt_trm e (trm_var_f x5) )  A )  ->
     styping G (trm_mu A e) A
 | ts_castup : forall (G:env) (e B A:trm) (s:sort),
     styping G e A ->
     styping G B (trm_sort s) ->
     beta B A ->
     styping G e B
 | ts_castdn : forall (G:env) (e B A:trm) (s:sort),
     styping G e A ->
     styping G B (trm_sort s) ->
     beta A B ->
     styping G e B
with swf : env -> Prop :=
 | swf_nil :
     swf  empty
 | swf_cons : forall (G:env) (x5:var) (A:trm) (s:sort),
     styping G A (trm_sort s) ->
      ( x5  # ( G ))  ->
     swf  ( G  &  x5 ~ A ) .
