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
 | trm_mu (A:trm) (e:trm)
 | trm_castup (A:trm) (e:trm)
 | trm_castdn (A:trm) (e:trm)  .

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
  | (trm_castup A e) => trm_castup (open_trm_wrt_trm_rec k e_5 A) (open_trm_wrt_trm_rec k e_5 e)
  | (trm_castdn A e) => trm_castdn (open_trm_wrt_trm_rec k e_5 A) (open_trm_wrt_trm_rec k e_5 e)
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
     (lc_trm (trm_mu A e))
 | lc_trm_castup : forall (A e:trm),
     (lc_trm A) ->
     (lc_trm e) ->
     (lc_trm (trm_castup A e))
 | lc_trm_castdn : forall (A e:trm),
     (lc_trm A) ->
     (lc_trm e) ->
     (lc_trm (trm_castdn A e)).

Fixpoint fv_trm (e_5:trm) : vars :=
  match e_5 with
  | (trm_var_b nat) => \{}
  | (trm_var_f x5) => \{x5}
  | (trm_sort s) => \{}
  | (trm_app e1 e2) => (fv_trm e1) \u (fv_trm e2)
  | (trm_abs A e) => (fv_trm A) \u (fv_trm e)
  | (trm_prod A B) => (fv_trm A) \u (fv_trm B)
  | (trm_mu A e) => (fv_trm A) \u (fv_trm e)
  | (trm_castup A e) => (fv_trm A) \u (fv_trm e)
  | (trm_castdn A e) => (fv_trm A) \u (fv_trm e)
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
  | (trm_castup A e) => trm_castup (subst_trm e_5 y5 A) (subst_trm e_5 y5 e)
  | (trm_castdn A e) => trm_castdn (subst_trm e_5 y5 A) (subst_trm e_5 y5 e)
end.

Definition Ax := pts_axiom PTS_Spec.PTS.

Definition Rel := pts_rules PTS_Spec.PTS.

Definition AxUniq := pts_axuniq PTS_Spec.PTS.

Definition RelUniq := pts_reluniq PTS_Spec.PTS.

Definition AxDec := pts_axdec PTS_Spec.PTS.

Definition RelDec := pts_reldec PTS_Spec.PTS.

Require PTSMu_ott.

Module C := PTSMu_ott.

Fixpoint erasure (s : trm) {struct s} : C.trm :=
  match s with
  | trm_var_b i      => C.trm_var_b i
  | trm_var_f x      => C.trm_var_f x
  | trm_sort s       => C.trm_sort s
  | trm_app t1 t2    => C.trm_app (erasure t1) (erasure t2)
  | trm_abs t1 t2    => C.trm_abs (erasure t1) (erasure t2)
  | trm_prod t1 t2   => C.trm_prod (erasure t1) (erasure t2)
  | trm_mu t1 t2     => C.trm_mu (erasure t1) (erasure t2)
  | trm_castup t1 t2 => erasure t2
  | trm_castdn t1 t2 => erasure t2
  end.

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
 | t_castup : forall (G:env) (B e:trm) (s:sort) (A:trm),
     typing G B (trm_sort s) ->
     typing G e A ->
      (C.dpara (erasure ( B )) (erasure ( A )))  ->
     typing G (trm_castup B e) B
 | t_castdn : forall (G:env) (B e:trm) (s:sort) (A:trm),
     typing G B (trm_sort s) ->
     typing G e A ->
      (C.dpara (erasure ( A )) (erasure ( B )))  ->
     typing G (trm_castdn B e) B
with wf : env -> Prop :=
 | wf_nil :
     wf  empty
 | wf_cons : forall (G:env) (x5:var) (A:trm) (s:sort),
     typing G A (trm_sort s) ->
      ( x5  # ( G ))  ->
     wf  ( G  &  x5 ~ A ) .
