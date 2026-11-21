From Stdlib Require Import Bool.

Require Import Metalib.Metatheory.

From Stdlib Require Import List.

Definition blame_label : Set := var.

Inductive modality : Set :=
 | mod_unsafe : modality
 | mod_safe : modality
 | mod_non_nullable : modality  .

Inductive label : Set :=
 | label_name (l:blame_label)
 | label_not_label (l:blame_label)  .

Inductive typ : Set :=
 | typ_null : typ
 | typ_mod_arrow (M:modality) (T:typ) (U:typ)  .

Inductive trm : Set :=
 | t_var_b (_:nat)
 | t_var_f (x:var)
 | t_null : trm
 | t_abs (T:typ) (t:trm)
 | t_app (s:trm) (t:trm)
 | t_app_safe (f:trm) (s:trm) (t:trm)
 | t_cast (s:trm) (V:typ) (p:label) (T:typ)  .

Inductive res : Set :=
 | r_term (t:trm)
 | r_blame (p:label).

Definition ctx : Set := list ( atom * typ ).

Fixpoint is_val_of_trm (t_5:trm) : bool :=
  match t_5 with
  | (t_var_b nat) => false
  | (t_var_f x) => false
  | t_null => (true)
  | (t_abs T t) => (true)
  | (t_app s t) => false
  | (t_app_safe f s t) => false
  | (t_cast s V p T) => ((is_val_of_trm s))
end.

Fixpoint open_trm_wrt_trm_rec (k:nat) (t_5:trm) (t__6:trm) {struct t__6}: trm :=
  match t__6 with
  | (t_var_b nat) =>
      match lt_eq_lt_dec nat k with
        | inleft (left _) => t_var_b nat
        | inleft (right _) => t_5
        | inright _ => t_var_b (nat - 1)
      end
  | (t_var_f x) => t_var_f x
  | t_null => t_null
  | (t_abs T t) => t_abs T (open_trm_wrt_trm_rec (S k) t_5 t)
  | (t_app s t) => t_app (open_trm_wrt_trm_rec k t_5 s) (open_trm_wrt_trm_rec k t_5 t)
  | (t_app_safe f s t) => t_app_safe (open_trm_wrt_trm_rec k t_5 f) (open_trm_wrt_trm_rec k t_5 s) (open_trm_wrt_trm_rec k t_5 t)
  | (t_cast s V p T) => t_cast (open_trm_wrt_trm_rec k t_5 s) V p T
end.

Definition open_trm_wrt_trm t_5 t__6 := open_trm_wrt_trm_rec 0 t__6 t_5.

Inductive lc_trm : trm -> Prop :=
 | lc_t_var_f : forall (x:var),
     (lc_trm (t_var_f x))
 | lc_t_null :
     (lc_trm t_null)
 | lc_t_abs : forall (T:typ) (t:trm),
      ( forall x , lc_trm  ( open_trm_wrt_trm t (t_var_f x) )  )  ->
     (lc_trm (t_abs T t))
 | lc_t_app : forall (s t:trm),
     (lc_trm s) ->
     (lc_trm t) ->
     (lc_trm (t_app s t))
 | lc_t_app_safe : forall (f s t:trm),
     (lc_trm f) ->
     (lc_trm s) ->
     (lc_trm t) ->
     (lc_trm (t_app_safe f s t))
 | lc_t_cast : forall (s:trm) (V:typ) (p:label) (T:typ),
     (lc_trm s) ->
     (lc_trm (t_cast s V p T)).

Inductive compat : typ -> typ -> Prop :=
 | compat_null_refl :
     compat typ_null typ_null
 | compat_null : forall (M:modality) (T1 T2:typ),
      M  <>  mod_non_nullable  ->
     compat typ_null (typ_mod_arrow M T1 T2)
 | compat_arrow : forall (M1:modality) (V T:typ) (M2:modality) (V' T':typ),
     compat V' V ->
     compat T T' ->
     compat (typ_mod_arrow M1 V T) (typ_mod_arrow M2 V' T').

Inductive typing : ctx -> trm -> typ -> Prop :=
 | typing_var : forall (G:ctx) (x:var) (T:typ),
      uniq  G  ->
      binds  x T G  ->
     typing G (t_var_f x) T
 | typing_null : forall (G:ctx),
      uniq  G  ->
     typing G t_null typ_null
 | typing_abs : forall (L:vars) (G:ctx) (V:typ) (s:trm) (T:typ),
      ( forall x , x \notin  L  -> typing  (( x ~ V )++ G )   ( open_trm_wrt_trm s (t_var_f x) )  T )  ->
     typing G (t_abs V s) (typ_mod_arrow mod_non_nullable V T)
 | typing_app : forall (G:ctx) (s t:trm) (T:typ) (M:modality) (V:typ),
     typing G s (typ_mod_arrow M V T) ->
      M  <>  mod_safe  ->
     typing G t V ->
     typing G (t_app s t) T
 | typing_safe_app : forall (G:ctx) (f s t:trm) (T:typ) (M:modality) (V:typ),
     typing G f (typ_mod_arrow M V T) ->
      M  <>  mod_non_nullable  ->
     typing G s V ->
     typing G t T ->
     typing G (t_app_safe f s t) T
 | typing_cast : forall (G:ctx) (s:trm) (V:typ) (p:label) (T:typ),
     typing G s V ->
     compat V T ->
     typing G  ( (t_cast s V p T) )  T.

Inductive isnull : trm -> Prop :=
 | isnull_null :
     isnull t_null
 | isnull_cast : forall (v:trm) (V:typ) (p:label) (T:typ),
     isnull v ->
     isnull  ( (t_cast v V p T) ) .

Inductive isabs : trm -> Prop :=
 | isabs_abs : forall (T:typ) (t:trm),
     lc_trm (t_abs T t) ->
     isabs (t_abs T t)
 | isabs_cast : forall (v:trm) (V:typ) (p:label) (T:typ),
     isabs v ->
     isabs  ( (t_cast v V p T) ) .

Inductive neglabel : label -> label -> Prop :=
 | nl_l : forall (l:blame_label),
     neglabel (label_name l) (label_not_label l)
 | nl_nl : forall (l:blame_label),
     neglabel (label_not_label l) (label_name l).

Inductive norm : trm -> trm -> Prop :=
 | norm_abs : forall (T:typ) (s:trm),
     lc_trm (t_abs T s) ->
     norm (t_abs T s) (t_abs T s)
 | norm_cast : forall (v:trm) (M1:modality) (V1 V2:typ) (p:label) (M2:modality) (T1 T2:typ) (v':trm),
     norm v v' ->
     norm (t_cast v  ( (typ_mod_arrow M1 V1 V2) )  p  ( (typ_mod_arrow M2 T1 T2) ) ) (t_cast v' (typ_mod_arrow mod_non_nullable V1 V2) p (typ_mod_arrow mod_non_nullable T1 T2)).

Inductive unwrap : trm -> label -> Prop :=
 | unwrap_null_bang : forall (v:trm) (p:label) (T1 T2:typ) (p':label),
     lc_trm v ->
     neglabel p p' ->
     unwrap  ( (t_cast v typ_null p  ( (typ_mod_arrow mod_unsafe T1 T2) ) ) )  p'
 | unwrap_hash : forall (v:trm) (T1 T2:typ) (p:label) (T3:typ) (p':label),
     unwrap v p' ->
     unwrap  ( (t_cast v  ( (typ_mod_arrow mod_non_nullable T1 T2) )  p T3) )  p'
 | unwrap_bang_hash : forall (v:trm) (T1 T2:typ) (p:label) (T3 T4:typ),
     lc_trm v ->
     unwrap  ( (t_cast v  ( (typ_mod_arrow mod_unsafe T1 T2) )  p  ( (typ_mod_arrow mod_non_nullable T3 T4) ) ) )  p
 | unwrap_bang_bang : forall (v:trm) (T1 T2:typ) (p:label) (T3 T4:typ) (p':label),
     unwrap v p' ->
     unwrap  ( (t_cast v  ( (typ_mod_arrow mod_unsafe T1 T2) )  p  ( (typ_mod_arrow mod_unsafe T3 T4) ) ) )  p'
 | unwrap_question_hash : forall (v:trm) (T1 T2:typ) (p:label) (T3 T4:typ),
     lc_trm v ->
     unwrap  ( (t_cast v  ( (typ_mod_arrow mod_safe T1 T2) )  p  ( (typ_mod_arrow mod_non_nullable T3 T4) ) ) )  p
 | unwrap_question_bang : forall (v:trm) (T1 T2:typ) (p:label) (T3 T4:typ) (p':label),
     lc_trm v ->
     neglabel p p' ->
     unwrap  ( (t_cast v  ( (typ_mod_arrow mod_safe T1 T2) )  p  ( (typ_mod_arrow mod_unsafe T3 T4) ) ) )  p'.

Inductive step : trm -> res -> Prop :=
 | step_cast_ctx : forall (t:trm) (V:typ) (p:label) (V':typ) (t':trm),
     step t (r_term t') ->
     step (t_cast t V p V') (r_term (t_cast t' V p V'))
 | step_cast_err : forall (t:trm) (V:typ) (p:label) (V':typ) (q:label),
     step t (r_blame q) ->
     step (t_cast t V p V') (r_blame q)
 | step_app : forall (T:typ) (t v:trm),
     Is_true (is_val_of_trm v) ->
     lc_trm (t_abs T t) ->
     lc_trm v ->
     step (t_app  ( (t_abs T t) )  v) (r_term  (  (open_trm_wrt_trm  t v )  ) )
 | step_app_ctxL : forall (s t s':trm),
     lc_trm t ->
     step s (r_term s') ->
     step (t_app s t) (r_term (t_app s' t))
 | step_app_ctxR : forall (t t' v:trm),
     Is_true (is_val_of_trm v) ->
     lc_trm v ->
     step t (r_term t') ->
     step (t_app v t) (r_term (t_app v t'))
 | step_app_errL : forall (s t:trm) (p:label),
     lc_trm t ->
     step s (r_blame p) ->
     step (t_app s t) (r_blame p)
 | step_app_errR : forall (t:trm) (p:label) (v:trm),
     Is_true (is_val_of_trm v) ->
     lc_trm v ->
     step t (r_blame p) ->
     step (t_app v t) (r_blame p)
 | step_app_fail : forall (p:label) (u v:trm),
     Is_true (is_val_of_trm v) ->
     Is_true (is_val_of_trm u) ->
     lc_trm u ->
     isnull v ->
     unwrap v p ->
     step (t_app v u) (r_blame p)
 | step_app_norm : forall (u v v':trm),
     Is_true (is_val_of_trm v) ->
     Is_true (is_val_of_trm u) ->
     Is_true (is_val_of_trm v') ->
     lc_trm u ->
     isabs v ->
     norm v v' ->
     step (t_app v u) (r_term (t_app v' u))
 | step_app_cast : forall (V1 V2:typ) (p:label) (T1 T2:typ) (p':label) (v' v:trm),
     Is_true (is_val_of_trm v) ->
     Is_true (is_val_of_trm v') ->
     lc_trm v' ->
     isabs v ->
     neglabel p p' ->
     step (t_app  ( (t_cast v  ( (typ_mod_arrow mod_non_nullable V1 V2) )  p  ( (typ_mod_arrow mod_non_nullable T1 T2) ) ) )  v') (r_term (t_cast  ( (t_app v  ( (t_cast v' T1 p' V1) ) ) )  V2 p T2))
 | step_safe_app_null : forall (t1 t2 v:trm),
     Is_true (is_val_of_trm v) ->
     lc_trm t1 ->
     lc_trm t2 ->
     isnull v ->
     step (t_app_safe v t1 t2) (r_term t2)
 | step_safe_app_norm : forall (t1 t2 v v':trm),
     Is_true (is_val_of_trm v) ->
     Is_true (is_val_of_trm v') ->
     lc_trm t2 ->
     lc_trm t1 ->
     isabs v ->
     norm v v' ->
     step (t_app_safe v t1 t2) (r_term (t_app v' t1))
 | step_safe_app_ctxL : forall (t t1 t2 t':trm),
     lc_trm t1 ->
     lc_trm t2 ->
     step t (r_term t') ->
     step (t_app_safe t t1 t2) (r_term (t_app_safe t' t1 t2))
 | step_safe_app_errL : forall (t t1 t2:trm) (p:label),
     lc_trm t1 ->
     lc_trm t2 ->
     step t (r_blame p) ->
     step (t_app_safe t t1 t2) (r_blame p).
