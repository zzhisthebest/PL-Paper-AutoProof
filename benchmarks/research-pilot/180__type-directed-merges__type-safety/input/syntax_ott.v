Require Import Metalib.Metatheory.

Definition i : Set := nat.

Inductive typ : Set :=
 | t_int : typ
 | t_top : typ
 | t_arrow (A:typ) (B:typ)
 | t_and (A:typ) (B:typ)  .

Definition ctx : Set := list ( atom * typ ).

Inductive exp : Set :=
 | e_var_b (_:nat)
 | e_var_f (x:var)
 | e_top : exp
 | e_lit (i5:i)
 | e_abs (A:typ) (e:exp) (B:typ)
 | e_fixpoint (e:exp) (A:typ)
 | e_app (e1:exp) (e2:exp)
 | e_merge (e1:exp) (e2:exp)
 | e_anno (e:exp) (A:typ)  .

Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (e_var_b nat) =>
      match lt_eq_lt_dec nat k with
        | inleft (left _) => e_var_b nat
        | inleft (right _) => e_5
        | inright _ => e_var_b (nat - 1)
      end
  | (e_var_f x) => e_var_f x
  | e_top => e_top
  | (e_lit i5) => e_lit i5
  | (e_abs A e B) => e_abs A (open_exp_wrt_exp_rec (S k) e_5 e) B
  | (e_fixpoint e A) => e_fixpoint (open_exp_wrt_exp_rec (S k) e_5 e) A
  | (e_app e1 e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_merge e1 e2) => e_merge (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_anno e A) => e_anno (open_exp_wrt_exp_rec k e_5 e) A
end.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

Inductive lc_exp : exp -> Prop :=
 | lc_e_var_f : forall (x:var),
     (lc_exp (e_var_f x))
 | lc_e_top :
     (lc_exp e_top)
 | lc_e_lit : forall (i5:i),
     (lc_exp (e_lit i5))
 | lc_e_abs : forall (A:typ) (e:exp) (B:typ),
      ( forall x , lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_abs A e B))
 | lc_e_fixpoint : forall (e:exp) (A:typ),
      ( forall x , lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_fixpoint e A))
 | lc_e_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_app e1 e2))
 | lc_e_merge : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_merge e1 e2))
 | lc_e_anno : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_exp (e_anno e A)).

Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {{x}}
  | e_top => {}
  | (e_lit i5) => {}
  | (e_abs A e B) => (fv_exp e)
  | (e_fixpoint e A) => (fv_exp e)
  | (e_app e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_merge e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_anno e A) => (fv_exp e)
end.

Fixpoint subst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (if eq_var x x5 then e_5 else (e_var_f x))
  | e_top => e_top
  | (e_lit i5) => e_lit i5
  | (e_abs A e B) => e_abs A (subst_exp e_5 x5 e) B
  | (e_fixpoint e A) => e_fixpoint (subst_exp e_5 x5 e) A
  | (e_app e1 e2) => e_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_merge e1 e2) => e_merge (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_anno e A) => e_anno (subst_exp e_5 x5 e) A
end.

Inductive value : exp -> Prop :=
 | value_unit :
     value e_top
 | value_lit : forall (i5:i),
     value (e_lit i5)
 | value_anno : forall (A:typ) (e:exp) (B:typ),
     lc_exp (e_abs A e B) ->
     value (e_abs A e B)
 | value_merge : forall (v1 v2:exp),
     value v1 ->
     value v2 ->
     value (e_merge v1 v2).

Inductive topLike : typ -> Prop :=
 | TL_top :
     topLike t_top
 | TL_and : forall (A B:typ),
     topLike A ->
     topLike B ->
     topLike (t_and A B)
 | TL_arr : forall (A B:typ),
     topLike B ->
     topLike (t_arrow A B).

Inductive ord : typ -> Prop :=
 | O_top :
     ord t_top
 | O_int :
     ord t_int
 | O_arrow : forall (A B:typ),
     ord (t_arrow A B).

Inductive disjoint : typ -> typ -> Prop :=
 | D_topL : forall (A:typ),
     disjoint t_top A
 | D_topR : forall (A:typ),
     disjoint A t_top
 | D_andL : forall (A1 A2 B:typ),
     disjoint A1 B ->
     disjoint A2 B ->
     disjoint (t_and A1 A2) B
 | D_andR : forall (A B1 B2:typ),
     disjoint A B1 ->
     disjoint A B2 ->
     disjoint A (t_and B1 B2)
 | D_IntArr : forall (A1 A2:typ),
     disjoint t_int (t_arrow A1 A2)
 | D_ArrInt : forall (A1 A2:typ),
     disjoint (t_arrow A1 A2) t_int
 | D_ArrArr : forall (A1 A2 B1 B2:typ),
     disjoint A2 B2 ->
     disjoint (t_arrow A1 A2) (t_arrow B1 B2).

Inductive sub : typ -> typ -> Prop :=
 | S_z :
     sub t_int t_int
 | S_top : forall (A:typ),
     sub A t_top
 | S_toparr : forall (A B1 B2:typ),
     sub t_top B2 ->
     sub A (t_arrow B1 B2)
 | S_arr : forall (A1 A2 B1 B2:typ),
     sub B1 A1 ->
     sub A2 B2 ->
     sub (t_arrow A1 A2) (t_arrow B1 B2)
 | S_andl1 : forall (A1 A2 A3:typ),
     sub A1 A3 ->
     sub (t_and A1 A2) A3
 | S_andl2 : forall (A1 A2 A3:typ),
     sub A2 A3 ->
     sub (t_and A1 A2) A3
 | S_andr : forall (A1 A2 A3:typ),
     sub A1 A2 ->
     sub A1 A3 ->
     sub A1 (t_and A2 A3).

Inductive TypedReduce : exp -> typ -> exp -> Prop :=
 | TReduce_lit : forall (i5:i),
     TypedReduce (e_lit i5) t_int (e_lit i5)
 | TReduce_top : forall (v:exp),
     lc_exp v ->
     TypedReduce v t_top e_top
 | TReduce_toparr : forall (v:exp) (A B:typ),
     lc_exp v ->
     topLike B ->
     TypedReduce v (t_arrow A B) (e_abs t_top e_top B)
 | TReduce_arrow : forall (A:typ) (e:exp) (B C D:typ),
     lc_exp (e_abs A e B) ->
      not ( topLike D )  ->
     sub C A ->
     sub B D ->
     TypedReduce (e_abs A e B)  (t_arrow C D)  (e_abs A e D)
 | TReduce_mergevl : forall (v1 v2:exp) (A:typ) (v1':exp),
     lc_exp v2 ->
     TypedReduce v1 A v1' ->
     ord A ->
     TypedReduce (e_merge v1 v2) A v1'
 | TReduce_mergevr : forall (v1 v2:exp) (A:typ) (v2':exp),
     lc_exp v1 ->
     TypedReduce v2 A v2' ->
     ord A ->
     TypedReduce (e_merge v1 v2) A v2'
 | TReduce_and : forall (v:exp) (A B:typ) (v1 v2:exp),
     TypedReduce v A v1 ->
     TypedReduce v B v2 ->
     TypedReduce v (t_and A B) (e_merge v1 v2)
with step : exp -> exp -> Prop :=
 | Step_beta : forall (A:typ) (e:exp) (D:typ) (v v':exp),
     lc_exp (e_abs A e D) ->
     value v ->
     TypedReduce v A v' ->
     step (e_app  ( (e_abs A e D) )  v) (e_anno  (  (open_exp_wrt_exp  e v' )  )  D)
 | Step_annov : forall (v:exp) (A:typ) (v':exp),
     value v ->
     TypedReduce v A v' ->
     step (e_anno v A) v'
 | Step_appl : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     step e1 e1' ->
     step (e_app e1 e2) (e_app e1' e2)
 | Step_appr : forall (v1 e2 e2':exp),
     value v1 ->
     step e2 e2' ->
     step (e_app v1 e2) (e_app v1 e2')
 | Step_mergel : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     step e1 e1' ->
     step (e_merge e1 e2) (e_merge e1' e2)
 | Step_merger : forall (v1 e2 e2':exp),
     value v1 ->
     step e2 e2' ->
     step (e_merge v1 e2) (e_merge v1 e2')
 | Step_anno : forall (e:exp) (A:typ) (e':exp),
     step e e' ->
     step (e_anno e A) (e_anno e' A)
 | Step_fix : forall (e:exp) (A:typ),
     lc_exp (e_fixpoint e A) ->
     step (e_fixpoint e A)  (open_exp_wrt_exp  e (e_fixpoint e A) ) .

Definition disjointSpec A B :=
  forall C, sub A C -> sub B C -> topLike C.

Definition consistencySpec v1 v2 :=
  forall A v1' v2', TypedReduce v1 A v1' -> TypedReduce v2 A v2' -> v1' = v2'.

Inductive Etyping : ctx -> exp -> typ -> Prop :=
 | Etyp_top : forall (G:ctx),
      uniq  G  ->
     Etyping G e_top t_top
 | Etyp_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     Etyping G (e_lit i5) t_int
 | Etyp_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
     Etyping G (e_var_f x) A
 | Etyp_abs : forall (L:vars) (G:ctx) (A:typ) (e:exp) (D C B:typ),
      ( forall x , x \notin  L  -> Etyping  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  B )  ->
     sub C A ->
     sub B D ->
     Etyping G  ( (e_abs A e D) )  (t_arrow C D)
 | Etyp_app : forall (G:ctx) (e1 e2:exp) (B A:typ),
     Etyping G e2 A ->
     Etyping G e1 (t_arrow A B) ->
     Etyping G (e_app e1 e2) B
 | Etyp_merge : forall (G:ctx) (e1 e2:exp) (A B:typ),
     Etyping G e1 A ->
     Etyping G e2 B ->
      disjointSpec A B  ->
     Etyping G (e_merge e1 e2) (t_and A B)
 | Etyp_anno : forall (G:ctx) (e:exp) (A B:typ),
     Etyping G e B ->
     sub B A ->
     Etyping G  ( (e_anno e A) )  A
 | Etyp_fix : forall (L:vars) (G:ctx) (e:exp) (A:typ),
      ( forall x , x \notin  L  -> Etyping  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  A )  ->
     Etyping G  ( (e_fixpoint e A) )  A
 | Etyp_mergev : forall (G:ctx) (v1 v2:exp) (A B:typ),
      uniq  G  ->
     value (e_merge v1 v2) ->
     Etyping  nil  v1 A ->
     Etyping  nil  v2 B ->
      consistencySpec v1 v2  ->
     Etyping G (e_merge v1 v2) (t_and A B).
