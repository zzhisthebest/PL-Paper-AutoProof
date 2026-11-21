From TLC Require Import LibLN.

Inductive trm : Set :=
 | trm_var_b (_:nat)
 | trm_var_f (x5:var)
 | trm_star : trm
 | trm_top : trm
 | trm_app (e1:trm) (e2:trm)
 | trm_abs (e1:trm) (A:trm) (e2:trm)
 | trm_prod (e:trm) (A:trm) (B:trm)
 | trm_castup (A:trm) (e:trm)
 | trm_castdn (e:trm)
 | trm_anno (e:trm) (A:trm)  .

Inductive binding : Set :=
 | bind_sub (e:trm) (A:trm)  .

Definition env := LibEnv.env binding.

Fixpoint open_trm_wrt_trm_rec (k:nat) (e_5:trm) (e__6:trm) {struct e__6}: trm :=
  match e__6 with
  | (trm_var_b nat) => If (k = nat) then e_5 else (trm_var_b nat)
  | (trm_var_f x5) => trm_var_f x5
  | trm_star => trm_star
  | trm_top => trm_top
  | (trm_app e1 e2) => trm_app (open_trm_wrt_trm_rec k e_5 e1) (open_trm_wrt_trm_rec k e_5 e2)
  | (trm_abs e1 A e2) => trm_abs (open_trm_wrt_trm_rec k e_5 e1) (open_trm_wrt_trm_rec k e_5 A) (open_trm_wrt_trm_rec (S k) e_5 e2)
  | (trm_prod e A B) => trm_prod (open_trm_wrt_trm_rec k e_5 e) (open_trm_wrt_trm_rec k e_5 A) (open_trm_wrt_trm_rec (S k) e_5 B)
  | (trm_castup A e) => trm_castup (open_trm_wrt_trm_rec k e_5 A) (open_trm_wrt_trm_rec k e_5 e)
  | (trm_castdn e) => trm_castdn (open_trm_wrt_trm_rec k e_5 e)
  | (trm_anno e A) => trm_anno (open_trm_wrt_trm_rec k e_5 e) (open_trm_wrt_trm_rec k e_5 A)
end.

Definition open_binding_wrt_trm_rec (k:nat) (e5:trm) (b5:binding) : binding :=
  match b5 with
  | (bind_sub e A) => bind_sub (open_trm_wrt_trm_rec k e5 e) (open_trm_wrt_trm_rec k e5 A)
end.

Definition open_binding_wrt_trm e5 b5 := open_binding_wrt_trm_rec 0 b5 e5.

Definition open_trm_wrt_trm e_5 e__6 := open_trm_wrt_trm_rec 0 e__6 e_5.

Inductive lc_trm : trm -> Prop :=
 | lc_trm_var_f : forall (x5:var),
     (lc_trm (trm_var_f x5))
 | lc_trm_star :
     (lc_trm trm_star)
 | lc_trm_top :
     (lc_trm trm_top)
 | lc_trm_app : forall (e1 e2:trm),
     (lc_trm e1) ->
     (lc_trm e2) ->
     (lc_trm (trm_app e1 e2))
 | lc_trm_abs : forall (L:vars) (e1 A e2:trm),
     (lc_trm e1) ->
     (lc_trm A) ->
      ( forall x5 , x5 \notin  L  -> lc_trm  ( open_trm_wrt_trm e2 (trm_var_f x5) )  )  ->
     (lc_trm (trm_abs e1 A e2))
 | lc_trm_prod : forall (L:vars) (e A B:trm),
     (lc_trm e) ->
     (lc_trm A) ->
      ( forall x5 , x5 \notin  L  -> lc_trm  ( open_trm_wrt_trm B (trm_var_f x5) )  )  ->
     (lc_trm (trm_prod e A B))
 | lc_trm_castup : forall (A e:trm),
     (lc_trm A) ->
     (lc_trm e) ->
     (lc_trm (trm_castup A e))
 | lc_trm_castdn : forall (e:trm),
     (lc_trm e) ->
     (lc_trm (trm_castdn e))
 | lc_trm_anno : forall (e A:trm),
     (lc_trm e) ->
     (lc_trm A) ->
     (lc_trm (trm_anno e A)).

Inductive lc_binding : binding -> Prop :=
 | lc_bind_sub : forall (e A:trm),
     (lc_trm e) ->
     (lc_trm A) ->
     (lc_binding (bind_sub e A)).

Fixpoint fv_trm (e_5:trm) : vars :=
  match e_5 with
  | (trm_var_b nat) => \{}
  | (trm_var_f x5) => \{x5}
  | trm_star => \{}
  | trm_top => \{}
  | (trm_app e1 e2) => (fv_trm e1) \u (fv_trm e2)
  | (trm_abs e1 A e2) => (fv_trm e1) \u (fv_trm A) \u (fv_trm e2)
  | (trm_prod e A B) => (fv_trm e) \u (fv_trm A) \u (fv_trm B)
  | (trm_castup A e) => (fv_trm A) \u (fv_trm e)
  | (trm_castdn e) => (fv_trm e)
  | (trm_anno e A) => (fv_trm e) \u (fv_trm A)
end.

Definition fv_binding (b5:binding) : vars :=
  match b5 with
  | (bind_sub e A) => (fv_trm e) \u (fv_trm A)
end.

Fixpoint subst_trm (e_5:trm) (y5:var) (e__6:trm) {struct e__6} : trm :=
  match e__6 with
  | (trm_var_b nat) => trm_var_b nat
  | (trm_var_f x5) => (If x5 = y5 then e_5 else (trm_var_f x5))
  | trm_star => trm_star
  | trm_top => trm_top
  | (trm_app e1 e2) => trm_app (subst_trm e_5 y5 e1) (subst_trm e_5 y5 e2)
  | (trm_abs e1 A e2) => trm_abs (subst_trm e_5 y5 e1) (subst_trm e_5 y5 A) (subst_trm e_5 y5 e2)
  | (trm_prod e A B) => trm_prod (subst_trm e_5 y5 e) (subst_trm e_5 y5 A) (subst_trm e_5 y5 B)
  | (trm_castup A e) => trm_castup (subst_trm e_5 y5 A) (subst_trm e_5 y5 e)
  | (trm_castdn e) => trm_castdn (subst_trm e_5 y5 e)
  | (trm_anno e A) => trm_anno (subst_trm e_5 y5 e) (subst_trm e_5 y5 A)
end.

Definition subst_binding (e5:trm) (y5:var) (b5:binding) : binding :=
  match b5 with
  | (bind_sub e A) => bind_sub (subst_trm e5 y5 e) (subst_trm e5 y5 A)
end.

Inductive reduct : trm -> trm -> Prop :=
 | reduct_beta : forall (e3 A e1 e2:trm),
     lc_trm e3 ->
     lc_trm A ->
     lc_trm (trm_abs e3 A e1) ->
     lc_trm e2 ->
     reduct (trm_app  ( (trm_abs e3 A e1) )  e2)  (open_trm_wrt_trm  e1   e2 )
 | reduct_app : forall (e1 e2 e1':trm),
     lc_trm e2 ->
     reduct e1 e1' ->
     reduct (trm_app e1 e2) (trm_app e1' e2)
 | reduct_castdn : forall (e1 e1':trm),
     reduct e1 e1' ->
     reduct (trm_castdn e1) (trm_castdn e1')
 | reduct_castelim : forall (A e:trm),
     lc_trm A ->
     lc_trm e ->
     reduct (trm_castdn  ( (trm_castup A e) ) ) e.

Inductive sub : env -> trm -> trm -> trm -> Prop :=
 | sub_ax : forall (G:env),
     wf G ->
     sub G trm_star trm_star trm_star
 | sub_var_refl : forall (G:env) (x5:var) (A e:trm),
     wf G ->
      binds ( x5 ) ( (bind_sub e A) ) ( G )  ->
     sub G (trm_var_f x5) (trm_var_f x5) A
 | sub_var_trans : forall (G:env) (x5:var) (e2 A e1:trm),
      binds ( x5 ) ( (bind_sub e1 A) ) ( G )  ->
     sub G e1 e2 A ->
     sub G (trm_var_f x5) e2 A
 | sub_top : forall (G:env) (e A:trm),
      sub ( G ) ( e ) ( e ) ( A )  ->
     sub G e trm_top A
 | sub_top_refl : forall (G:env) (A:trm),
      sub ( G ) ( A ) ( A ) ( trm_star )  ->
     sub G trm_top trm_top A
 | sub_abs : forall (L:vars) (G:env) (e1 A e2 e2' B:trm),
      sub ( G ) ( e1 ) ( e1 ) ( A )  ->
      sub ( G ) ( A ) ( A ) ( trm_star )  ->
      ( forall x5 , x5 \notin  L  ->  sub  ( G  &  x5 ~ (bind_sub e1 A) )   ( open_trm_wrt_trm e2 (trm_var_f x5) )   ( open_trm_wrt_trm e2' (trm_var_f x5) )   ( open_trm_wrt_trm B (trm_var_f x5) )   )  ->
      ( forall x5 , x5 \notin  L  ->  sub (  ( G  &  x5 ~ (bind_sub e1 A) )  ) (  ( open_trm_wrt_trm B (trm_var_f x5) )  ) (  ( open_trm_wrt_trm B (trm_var_f x5) )  ) ( trm_star )  )  ->
     sub G  ( (trm_abs e1 A e2) )   ( (trm_abs e1 A e2') )  (trm_prod e1 A B)
 | sub_app : forall (G:env) (e1 A e2 C e3 B:trm),
     sub G e1 e2 (trm_prod e3 B C) ->
     sub G A e3 B ->
     sub G (trm_app e1 A) (trm_app e2 A)  (open_trm_wrt_trm  C   A )
 | sub_prod : forall (L:vars) (G:env) (e A B e' A' B':trm),
     sub G A' A trm_star ->
     sub G e' e A ->
      sub ( G ) ( A ) ( A ) ( trm_star )  ->
      ( forall x5 , x5 \notin  L  ->   sub (  ( G  &  x5 ~ (bind_sub e A) )  ) (  ( open_trm_wrt_trm B (trm_var_f x5) )  ) (  ( open_trm_wrt_trm B (trm_var_f x5) )  ) ( trm_star )   )  ->
      ( forall x5 , x5 \notin  L  -> sub  ( G  &  x5 ~ (bind_sub e' A') )   ( open_trm_wrt_trm B (trm_var_f x5) )   ( open_trm_wrt_trm B' (trm_var_f x5) )  trm_star )  ->
       sub ( G ) ( e ) ( e ) ( A )   ->
      sub ( G ) ( e' ) ( e' ) ( A' )  ->
     sub G  ( (trm_prod e A B) )   ( (trm_prod e' A' B') )  trm_star
 | sub_castup : forall (G:env) (B e1 e2 A:trm),
      sub ( G ) ( B ) ( B ) ( trm_star )  ->
     sub G e1 e2 A ->
     reduct B A ->
     sub G (trm_castup B e1) (trm_castup B e2) B
 | sub_castdn : forall (G:env) (e1 e2 B A:trm),
      sub ( G ) ( B ) ( B ) ( trm_star )  ->
     sub G e1 e2 A ->
     reduct A B ->
     sub G (trm_castdn e1) (trm_castdn e2) B
 | sub_sub : forall (G:env) (e1 e2 B A:trm),
     sub G e1 e2 A ->
     sub G A B trm_star ->
     sub G e1 e2 B
with wf : env -> Prop :=
 | wf_nil :
     wf  empty
 | wf_cons : forall (G:env) (x5:var) (e A:trm),
      sub ( G ) ( e ) ( e ) ( A )  ->
      sub ( G ) ( A ) ( A ) ( trm_star )  ->
      ( x5  # ( G ))  ->
     wf  ( G  &  x5 ~ (bind_sub e A) ) .

Inductive ivalue : trm -> Prop :=
 | ivalue_top :
     ivalue trm_top
 | ivalue_var : forall (x5:var),
     ivalue (trm_var_f x5)
 | ivalue_app : forall (e1 e2:trm),
     lc_trm e2 ->
     ivalue e1 ->
     ivalue (trm_app e1 e2)
 | ivalue_castdn : forall (e:trm),
     ivalue e ->
     ivalue (trm_castdn e).

Inductive value : trm -> Prop :=
 | value_star :
     value trm_star
 | value_ivalue : forall (e:trm),
     ivalue e ->
     value e
 | value_abs : forall (e1 A e2:trm),
     lc_trm e1 ->
     lc_trm A ->
     lc_trm (trm_abs e1 A e2) ->
     value (trm_abs e1 A e2)
 | value_prod : forall (e A B:trm),
     lc_trm e ->
     lc_trm A ->
     lc_trm (trm_prod e A B) ->
     value (trm_prod e A B)
 | value_castup : forall (A e:trm),
     lc_trm A ->
     lc_trm e ->
     value (trm_castup A e).
