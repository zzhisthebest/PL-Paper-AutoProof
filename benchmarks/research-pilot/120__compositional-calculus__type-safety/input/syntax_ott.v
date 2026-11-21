Require Import Metalib.Metatheory.

Definition typevar : Set := var.

Definition termvar : Set := var.

Definition label : Set := nat.

Definition int : Set := nat.

Inductive typ : Set :=
 | t_tvar_b (_:nat)
 | t_tvar_f (X:typevar)
 | t_int : typ
 | t_top : typ
 | t_bot : typ
 | t_forall (A:typ) (B:typ)
 | t_arrow (A:typ) (B:typ)
 | t_and (A:typ) (B:typ)
 | t_rcd (l:label) (A:typ)  .

Inductive exp : Set :=
 | e_var_b (_:nat)
 | e_var_f (x:termvar)
 | e_top : exp
 | e_lit (i:int)
 | e_abs (A:typ) (e:exp)
 | e_fixpoint (A:typ) (e:exp)
 | e_app (e1:exp) (e2:exp)
 | e_merge (e1:exp) (e2:exp)
 | e_anno (e:exp) (A:typ)
 | e_rcd (l:label) (e:exp)
 | e_proj (e:exp) (l:label)
 | e_tabs (e:exp)
 | e_tapp (e:exp) (A:typ)  .

Definition tctx : Set := list ( atom * typ ).

Inductive dirflag : Set :=
 | Inf : dirflag
 | Chk : dirflag.

Inductive arg : Set :=
 | arg_exp (v:exp)
 | arg_la (l:label)
 | arg_typ (A:typ).

Definition ctx : Set := list ( atom * typ ).

Inductive inla : Set :=
 | inla_arrow : inla
 | inla_forall : inla
 | inla_label (l:label).

Fixpoint open_typ_wrt_typ_rec (k:nat) (A5:typ) (A_6:typ) {struct A_6}: typ :=
  match A_6 with
  | (t_tvar_b nat) =>
      match lt_eq_lt_dec nat k with
        | inleft (left _) => t_tvar_b nat
        | inleft (right _) => A5
        | inright _ => t_tvar_b (nat - 1)
      end
  | (t_tvar_f X) => t_tvar_f X
  | t_int => t_int
  | t_top => t_top
  | t_bot => t_bot
  | (t_forall A B) => t_forall (open_typ_wrt_typ_rec k A5 A) (open_typ_wrt_typ_rec (S k) A5 B)
  | (t_arrow A B) => t_arrow (open_typ_wrt_typ_rec k A5 A) (open_typ_wrt_typ_rec k A5 B)
  | (t_and A B) => t_and (open_typ_wrt_typ_rec k A5 A) (open_typ_wrt_typ_rec k A5 B)
  | (t_rcd l A) => t_rcd l (open_typ_wrt_typ_rec k A5 A)
end.

Fixpoint open_exp_wrt_typ_rec (k:nat) (A5:typ) (e_5:exp) {struct e_5}: exp :=
  match e_5 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => e_var_f x
  | e_top => e_top
  | (e_lit i) => e_lit i
  | (e_abs A e) => e_abs (open_typ_wrt_typ_rec k A5 A) (open_exp_wrt_typ_rec k A5 e)
  | (e_fixpoint A e) => e_fixpoint (open_typ_wrt_typ_rec k A5 A) (open_exp_wrt_typ_rec k A5 e)
  | (e_app e1 e2) => e_app (open_exp_wrt_typ_rec k A5 e1) (open_exp_wrt_typ_rec k A5 e2)
  | (e_merge e1 e2) => e_merge (open_exp_wrt_typ_rec k A5 e1) (open_exp_wrt_typ_rec k A5 e2)
  | (e_anno e A) => e_anno (open_exp_wrt_typ_rec k A5 e) (open_typ_wrt_typ_rec k A5 A)
  | (e_rcd l e) => e_rcd l (open_exp_wrt_typ_rec k A5 e)
  | (e_proj e l) => e_proj (open_exp_wrt_typ_rec k A5 e) l
  | (e_tabs e) => e_tabs (open_exp_wrt_typ_rec (S k) A5 e)
  | (e_tapp e A) => e_tapp (open_exp_wrt_typ_rec k A5 e) (open_typ_wrt_typ_rec k A5 A)
end.

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
  | (e_lit i) => e_lit i
  | (e_abs A e) => e_abs A (open_exp_wrt_exp_rec (S k) e_5 e)
  | (e_fixpoint A e) => e_fixpoint A (open_exp_wrt_exp_rec (S k) e_5 e)
  | (e_app e1 e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_merge e1 e2) => e_merge (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_anno e A) => e_anno (open_exp_wrt_exp_rec k e_5 e) A
  | (e_rcd l e) => e_rcd l (open_exp_wrt_exp_rec k e_5 e)
  | (e_proj e l) => e_proj (open_exp_wrt_exp_rec k e_5 e) l
  | (e_tabs e) => e_tabs (open_exp_wrt_exp_rec k e_5 e)
  | (e_tapp e A) => e_tapp (open_exp_wrt_exp_rec k e_5 e) A
end.

Definition open_arg_wrt_typ_rec (k:nat) (A5:typ) (arg5:arg) : arg :=
  match arg5 with
  | (arg_exp v) => arg_exp (open_exp_wrt_typ_rec k A5 v)
  | (arg_la l) => arg_la l
  | (arg_typ A) => arg_typ (open_typ_wrt_typ_rec k A5 A)
end.

Definition open_arg_wrt_exp_rec (k:nat) (e5:exp) (arg5:arg) : arg :=
  match arg5 with
  | (arg_exp v) => arg_exp (open_exp_wrt_exp_rec k e5 v)
  | (arg_la l) => arg_la l
  | (arg_typ A) => arg_typ A
end.

Definition open_arg_wrt_typ A5 arg5 := open_arg_wrt_typ_rec 0 arg5 A5.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

Definition open_arg_wrt_exp e5 arg5 := open_arg_wrt_exp_rec 0 arg5 e5.

Definition open_exp_wrt_typ A5 e_5 := open_exp_wrt_typ_rec 0 e_5 A5.

Definition open_typ_wrt_typ A5 A_6 := open_typ_wrt_typ_rec 0 A_6 A5.

Inductive lc_typ : typ -> Prop :=
 | lc_t_tvar_f : forall (X:typevar),
     (lc_typ (t_tvar_f X))
 | lc_t_int :
     (lc_typ t_int)
 | lc_t_top :
     (lc_typ t_top)
 | lc_t_bot :
     (lc_typ t_bot)
 | lc_t_forall : forall (A B:typ),
     (lc_typ A) ->
      ( forall X , lc_typ  ( open_typ_wrt_typ B (t_tvar_f X) )  )  ->
     (lc_typ (t_forall A B))
 | lc_t_arrow : forall (A B:typ),
     (lc_typ A) ->
     (lc_typ B) ->
     (lc_typ (t_arrow A B))
 | lc_t_and : forall (A B:typ),
     (lc_typ A) ->
     (lc_typ B) ->
     (lc_typ (t_and A B))
 | lc_t_rcd : forall (l:label) (A:typ),
     (lc_typ A) ->
     (lc_typ (t_rcd l A)).

Inductive lc_exp : exp -> Prop :=
 | lc_e_var_f : forall (x:termvar),
     (lc_exp (e_var_f x))
 | lc_e_top :
     (lc_exp e_top)
 | lc_e_lit : forall (i:int),
     (lc_exp (e_lit i))
 | lc_e_abs : forall (A:typ) (e:exp),
     (lc_typ A) ->
      ( forall x , lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_abs A e))
 | lc_e_fixpoint : forall (A:typ) (e:exp),
     (lc_typ A) ->
      ( forall x , lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_fixpoint A e))
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
     (lc_typ A) ->
     (lc_exp (e_anno e A))
 | lc_e_rcd : forall (l:label) (e:exp),
     (lc_exp e) ->
     (lc_exp (e_rcd l e))
 | lc_e_proj : forall (e:exp) (l:label),
     (lc_exp e) ->
     (lc_exp (e_proj e l))
 | lc_e_tabs : forall (e:exp),
      ( forall X , lc_exp  ( open_exp_wrt_typ e (t_tvar_f X) )  )  ->
     (lc_exp (e_tabs e))
 | lc_e_tapp : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_typ A) ->
     (lc_exp (e_tapp e A)).

Inductive lc_arg : arg -> Prop :=
 | lc_arg_exp : forall (v:exp),
     (lc_exp v) ->
     (lc_arg (arg_exp v))
 | lc_arg_la : forall (l:label),
     (lc_arg (arg_la l))
 | lc_arg_typ : forall (A:typ),
     (lc_typ A) ->
     (lc_arg (arg_typ A)).

Fixpoint typefv_typ (A5:typ) : vars :=
  match A5 with
  | (t_tvar_b nat) => {}
  | (t_tvar_f X) => {{X}}
  | t_int => {}
  | t_top => {}
  | t_bot => {}
  | (t_forall A B) => (typefv_typ A) \u (typefv_typ B)
  | (t_arrow A B) => (typefv_typ A) \u (typefv_typ B)
  | (t_and A B) => (typefv_typ A) \u (typefv_typ B)
  | (t_rcd l A) => (typefv_typ A)
end.

Fixpoint termfv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {{x}}
  | e_top => {}
  | (e_lit i) => {}
  | (e_abs A e) => (termfv_exp e)
  | (e_fixpoint A e) => (termfv_exp e)
  | (e_app e1 e2) => (termfv_exp e1) \u (termfv_exp e2)
  | (e_merge e1 e2) => (termfv_exp e1) \u (termfv_exp e2)
  | (e_anno e A) => (termfv_exp e)
  | (e_rcd l e) => (termfv_exp e)
  | (e_proj e l) => (termfv_exp e)
  | (e_tabs e) => (termfv_exp e)
  | (e_tapp e A) => (termfv_exp e)
end.

Fixpoint typefv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {}
  | e_top => {}
  | (e_lit i) => {}
  | (e_abs A e) => (typefv_typ A) \u (typefv_exp e)
  | (e_fixpoint A e) => (typefv_typ A) \u (typefv_exp e)
  | (e_app e1 e2) => (typefv_exp e1) \u (typefv_exp e2)
  | (e_merge e1 e2) => (typefv_exp e1) \u (typefv_exp e2)
  | (e_anno e A) => (typefv_exp e) \u (typefv_typ A)
  | (e_rcd l e) => (typefv_exp e)
  | (e_proj e l) => (typefv_exp e)
  | (e_tabs e) => (typefv_exp e)
  | (e_tapp e A) => (typefv_exp e) \u (typefv_typ A)
end.

Definition termfv_arg (arg5:arg) : vars :=
  match arg5 with
  | (arg_exp v) => (termfv_exp v)
  | (arg_la l) => {}
  | (arg_typ A) => {}
end.

Definition typefv_arg (arg5:arg) : vars :=
  match arg5 with
  | (arg_exp v) => (typefv_exp v)
  | (arg_la l) => {}
  | (arg_typ A) => (typefv_typ A)
end.

Fixpoint typsubst_typ (A5:typ) (X5:typevar) (A_6:typ) {struct A_6} : typ :=
  match A_6 with
  | (t_tvar_b nat) => t_tvar_b nat
  | (t_tvar_f X) => (if eq_var X X5 then A5 else (t_tvar_f X))
  | t_int => t_int
  | t_top => t_top
  | t_bot => t_bot
  | (t_forall A B) => t_forall (typsubst_typ A5 X5 A) (typsubst_typ A5 X5 B)
  | (t_arrow A B) => t_arrow (typsubst_typ A5 X5 A) (typsubst_typ A5 X5 B)
  | (t_and A B) => t_and (typsubst_typ A5 X5 A) (typsubst_typ A5 X5 B)
  | (t_rcd l A) => t_rcd l (typsubst_typ A5 X5 A)
end.

Fixpoint typsubst_exp (A5:typ) (X5:typevar) (e_5:exp) {struct e_5} : exp :=
  match e_5 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => e_var_f x
  | e_top => e_top
  | (e_lit i) => e_lit i
  | (e_abs A e) => e_abs (typsubst_typ A5 X5 A) (typsubst_exp A5 X5 e)
  | (e_fixpoint A e) => e_fixpoint (typsubst_typ A5 X5 A) (typsubst_exp A5 X5 e)
  | (e_app e1 e2) => e_app (typsubst_exp A5 X5 e1) (typsubst_exp A5 X5 e2)
  | (e_merge e1 e2) => e_merge (typsubst_exp A5 X5 e1) (typsubst_exp A5 X5 e2)
  | (e_anno e A) => e_anno (typsubst_exp A5 X5 e) (typsubst_typ A5 X5 A)
  | (e_rcd l e) => e_rcd l (typsubst_exp A5 X5 e)
  | (e_proj e l) => e_proj (typsubst_exp A5 X5 e) l
  | (e_tabs e) => e_tabs (typsubst_exp A5 X5 e)
  | (e_tapp e A) => e_tapp (typsubst_exp A5 X5 e) (typsubst_typ A5 X5 A)
end.

Fixpoint subst_exp (e_5:exp) (x5:termvar) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (if eq_var x x5 then e_5 else (e_var_f x))
  | e_top => e_top
  | (e_lit i) => e_lit i
  | (e_abs A e) => e_abs A (subst_exp e_5 x5 e)
  | (e_fixpoint A e) => e_fixpoint A (subst_exp e_5 x5 e)
  | (e_app e1 e2) => e_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_merge e1 e2) => e_merge (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_anno e A) => e_anno (subst_exp e_5 x5 e) A
  | (e_rcd l e) => e_rcd l (subst_exp e_5 x5 e)
  | (e_proj e l) => e_proj (subst_exp e_5 x5 e) l
  | (e_tabs e) => e_tabs (subst_exp e_5 x5 e)
  | (e_tapp e A) => e_tapp (subst_exp e_5 x5 e) A
end.

Definition typsubst_arg (A5:typ) (X5:typevar) (arg5:arg) : arg :=
  match arg5 with
  | (arg_exp v) => arg_exp (typsubst_exp A5 X5 v)
  | (arg_la l) => arg_la l
  | (arg_typ A) => arg_typ (typsubst_typ A5 X5 A)
end.

Definition subst_arg (e5:exp) (x5:termvar) (arg5:arg) : arg :=
  match arg5 with
  | (arg_exp v) => arg_exp (subst_exp e5 x5 v)
  | (arg_la l) => arg_la l
  | (arg_typ A) => arg_typ A
end.

Inductive TWell : tctx -> typ -> Prop :=
 | TW_top : forall (D:tctx),
     TWell D t_top
 | TW_bot : forall (D:tctx),
     TWell D t_bot
 | TW_int : forall (D:tctx),
     TWell D t_int
 | TW_var : forall (D:tctx) (X:typevar) (A:typ),
      binds  X A D  ->
     TWell D (t_tvar_f X)
 | TW_rcd : forall (D:tctx) (l:label) (A:typ),
     TWell D A ->
     TWell D (t_rcd l A)
 | TW_arrow : forall (D:tctx) (A B:typ),
     TWell D A ->
     TWell D B ->
     TWell D (t_arrow A B)
 | TW_and : forall (D:tctx) (A B:typ),
     TWell D A ->
     TWell D B ->
     TWell D (t_and A B)
 | TW_all : forall (L:vars) (D:tctx) (A B:typ),
     TWell D A ->
      ( forall X , X \notin  L  -> TWell  (cons ( X , A )  D )   ( open_typ_wrt_typ B (t_tvar_f X) )  )  ->
     TWell D (t_forall A B).

Inductive CWell : tctx -> ctx -> Prop :=
 | CW_empty : forall (D:tctx),
     CWell D  nil
 | CW_cons : forall (D:tctx) (G:ctx) (x:termvar) (A:typ),
     CWell D G ->
     TWell D A ->
     CWell D  (cons ( x , A )  G ) .

Inductive TCWell : tctx -> Prop :=
 | TCW_empty :
     TCWell  nil
 | TCW_cons : forall (D:tctx) (X:typevar) (A:typ),
     TCWell D ->
     TWell D A ->
      uniq   (cons ( X , A )  D )   ->
     TCWell  (cons ( X , A )  D ) .

Inductive botLike : typ -> Prop :=
 | BL_bot :
     botLike t_bot
 | BL_andl : forall (A B:typ),
     lc_typ B ->
     botLike A ->
     botLike (t_and A B)
 | BL_andr : forall (A B:typ),
     lc_typ A ->
     botLike B ->
     botLike (t_and A B).

Inductive topLike : tctx -> typ -> Prop :=
 | TL_top : forall (D:tctx),
     TCWell D ->
     topLike D t_top
 | TL_and : forall (D:tctx) (A B:typ),
     topLike D A ->
     topLike D B ->
     topLike D (t_and A B)
 | TL_arrow : forall (D:tctx) (A B:typ),
     TWell D A ->
     topLike D B ->
     topLike D (t_arrow A B)
 | TL_rcd : forall (D:tctx) (l:label) (B:typ),
     topLike D B ->
     topLike D (t_rcd l B)
 | TL_all : forall (L:vars) (D:tctx) (A B:typ),
      ( forall X , X \notin  L  -> topLike  (cons ( X , A )  D )   ( open_typ_wrt_typ B (t_tvar_f X) )  )  ->
     topLike D (t_forall A B)
 | TL_var : forall (D:tctx) (X:typevar) (A:typ),
     TCWell D ->
      binds  X A D  ->
     botLike A ->
     topLike D (t_tvar_f X).

Inductive notTopLike : tctx -> typ -> Prop :=
 | NTL : forall (D:tctx) (A:typ),
     TCWell D ->
     TWell D A ->
      not ( topLike D A )  ->
     notTopLike D A.

Inductive ord : typ -> Prop :=
 | O_var : forall (X:typevar),
     ord (t_tvar_f X)
 | O_top :
     ord t_top
 | O_bot :
     ord t_bot
 | O_int :
     ord t_int
 | O_arrow : forall (A B:typ),
     lc_typ A ->
     ord B ->
     ord (t_arrow A B)
 | O_all : forall (L:vars) (A B:typ),
     lc_typ A ->
      ( forall X , X \notin  L  -> ord  ( open_typ_wrt_typ B (t_tvar_f X) )  )  ->
     ord (t_forall A B)
 | O_rcd : forall (l:label) (B:typ),
     ord B ->
     ord (t_rcd l B).

Inductive spl : typ -> typ -> typ -> Prop :=
 | Sp_arrow : forall (A B C1 C2:typ),
     lc_typ A ->
     spl B C1 C2 ->
     spl (t_arrow A B) (t_arrow A C1) (t_arrow A C2)
 | Sp_all : forall (L:vars) (A B C1 C2:typ),
     lc_typ A ->
      ( forall X , X \notin  L  -> spl  ( open_typ_wrt_typ B (t_tvar_f X) )   ( open_typ_wrt_typ C1 (t_tvar_f X) )   ( open_typ_wrt_typ C2 (t_tvar_f X) )  )  ->
     spl (t_forall A B) (t_forall A C1) (t_forall A C2)
 | Sp_rcd : forall (l:label) (B C1 C2:typ),
     spl B C1 C2 ->
     spl (t_rcd l B) (t_rcd l C1) (t_rcd l C2)
 | Sp_and : forall (A B:typ),
     lc_typ A ->
     lc_typ B ->
     spl (t_and A B) A B.

Inductive sub : tctx -> typ -> typ -> Prop :=
 | DS_refl : forall (D:tctx) (A:typ),
     TCWell D ->
     TWell D A ->
     sub D A A
 | DS_trans : forall (D:tctx) (A C B:typ),
     sub D A B ->
     sub D B C ->
     sub D A C
 | DS_top : forall (D:tctx) (A:typ),
     TCWell D ->
     TWell D A ->
     sub D A t_top
 | DS_bot : forall (D:tctx) (A:typ),
     TCWell D ->
     TWell D A ->
     sub D t_bot A
 | DS_and : forall (D:tctx) (A B C:typ),
     sub D A B ->
     sub D A C ->
     sub D A (t_and B C)
 | DS_andl : forall (D:tctx) (A B:typ),
     TCWell D ->
     TWell D (t_and A B) ->
     sub D (t_and A B) A
 | DS_andr : forall (D:tctx) (A B:typ),
     TCWell D ->
     TWell D (t_and A B) ->
     sub D (t_and A B) B
 | DS_arr : forall (D:tctx) (A1 B1 A2 B2:typ),
     sub D A2 A1 ->
     sub D B1 B2 ->
     sub D (t_arrow A1 B1) (t_arrow A2 B2)
 | DS_distArrow : forall (D:tctx) (A B C:typ),
     TCWell D ->
     TWell D (t_arrow A (t_and B C)) ->
     sub D (t_and  (t_arrow A B)   (t_arrow A C) ) (t_arrow A (t_and B C))
 | DS_topArrow : forall (D:tctx),
     TCWell D ->
     sub D t_top (t_arrow t_top t_top)
 | DS_rcd : forall (D:tctx) (l:label) (A B:typ),
     sub D A B ->
     sub D (t_rcd l A) (t_rcd l B)
 | DS_distRcd : forall (D:tctx) (l:label) (A B:typ),
     TCWell D ->
     TWell D (t_rcd l (t_and A B)) ->
     sub D (t_and (t_rcd l A) (t_rcd l B)) (t_rcd l (t_and A B))
 | DS_topRcd : forall (D:tctx) (l:label),
     TCWell D ->
     sub D t_top (t_rcd l t_top)
 | DS_all : forall (L:vars) (D:tctx) (A1 B1 A2 B2:typ),
     sub D A2 A1 ->
      ( forall X , X \notin  L  -> sub  (cons ( X , A2 )  D )   ( open_typ_wrt_typ B1 (t_tvar_f X) )   ( open_typ_wrt_typ B2 (t_tvar_f X) )  )  ->
     sub D (t_forall A1 B1) (t_forall A2 B2)
 | DS_distAll : forall (D:tctx) (A B1 B2:typ),
     TCWell D ->
     TWell D (t_forall A  (t_and B1 B2) ) ->
     sub D (t_and  (t_forall A B1)   (t_forall A B2) ) (t_forall A  (t_and B1 B2) )
 | DS_topAll : forall (D:tctx),
     TCWell D ->
     sub D t_top (t_forall t_top t_top)
 | DS_topVar : forall (D:tctx) (X:typevar) (A:typ),
      binds  X A D  ->
     sub D A t_bot ->
     sub D t_top (t_tvar_f X).

Inductive algo_sub : tctx -> typ -> typ -> Prop :=
 | S_var : forall (D:tctx) (X:typevar),
     TCWell D ->
     TWell D (t_tvar_f X) ->
     algo_sub D (t_tvar_f X) (t_tvar_f X)
 | S_int : forall (D:tctx),
     TCWell D ->
     algo_sub D t_int t_int
 | S_top : forall (D:tctx) (A B:typ),
     TWell D A ->
     ord B ->
     topLike D B ->
     algo_sub D A B
 | S_bot : forall (D:tctx) (A:typ),
     TCWell D ->
     TWell D A ->
     ord A ->
     algo_sub D t_bot A
 | S_andl : forall (D:tctx) (A B C:typ),
     TWell D B ->
     ord C ->
     algo_sub D A C ->
     algo_sub D (t_and A B) C
 | S_andr : forall (D:tctx) (A B C:typ),
     TWell D A ->
     ord C ->
     algo_sub D B C ->
     algo_sub D (t_and A B) C
 | S_arrow : forall (D:tctx) (A1 B1 A2 B2:typ),
     ord B2 ->
     algo_sub D A2 A1 ->
     algo_sub D B1 B2 ->
     algo_sub D (t_arrow A1 B1) (t_arrow A2 B2)
 | S_all : forall (L:vars) (D:tctx) (A1 A2 B1 B2:typ),
      ( forall X , X \notin  L  -> ord  ( open_typ_wrt_typ B2 (t_tvar_f X) )  )  ->
     algo_sub D B1 A1 ->
      ( forall X , X \notin  L  -> algo_sub  (cons ( X , B1 )  D )   ( open_typ_wrt_typ A2 (t_tvar_f X) )   ( open_typ_wrt_typ B2 (t_tvar_f X) )  )  ->
     algo_sub D (t_forall A1 A2) (t_forall B1 B2)
 | S_rcd : forall (D:tctx) (l:label) (A B:typ),
     ord B ->
     algo_sub D A B ->
     algo_sub D (t_rcd l A) (t_rcd l B)
 | S_and : forall (D:tctx) (A B B1 B2:typ),
     spl B B1 B2 ->
     algo_sub D A B1 ->
     algo_sub D A B2 ->
     algo_sub D A B.

Inductive msub : tctx -> typ -> typ -> Prop :=
 | MS_refl : forall (D:tctx) (A:typ),
     TCWell D ->
     TWell D A ->
     msub D A A
 | MS_top : forall (D:tctx) (A B:typ),
     TWell D A ->
     topLike D B ->
     msub D A B
 | MS_bot : forall (D:tctx) (A:typ),
     TCWell D ->
     TWell D A ->
     msub D t_bot A
 | MS_andl : forall (D:tctx) (A B C:typ),
     TWell D B ->
     msub D A C ->
     msub D (t_and A B) C
 | MS_andr : forall (D:tctx) (A B C:typ),
     TWell D A ->
     msub D B C ->
     msub D (t_and A B) C
 | MS_arrow : forall (D:tctx) (A1 B1 A2 B2:typ),
     msub D A2 A1 ->
     msub D B1 B2 ->
     msub D (t_arrow A1 B1) (t_arrow A2 B2)
 | MS_rcd : forall (D:tctx) (l:label) (A B:typ),
     msub D A B ->
     msub D (t_rcd l A) (t_rcd l B)
 | MS_and : forall (D:tctx) (A B B1 B2:typ),
     spl B B1 B2 ->
     msub D A B1 ->
     msub D A B2 ->
     msub D A B
 | MS_all : forall (L:vars) (D:tctx) (A1 A2 B1 B2:typ),
     msub D B1 A1 ->
      ( forall X , X \notin  L  -> msub  (cons ( X , B1 )  D )   ( open_typ_wrt_typ A2 (t_tvar_f X) )   ( open_typ_wrt_typ B2 (t_tvar_f X) )  )  ->
     msub D (t_forall A1 A2) (t_forall B1 B2).

Inductive disjoint_axiom : typ -> typ -> Prop :=
 | Dax_intArrow : forall (A1 A2:typ),
     lc_typ A1 ->
     lc_typ A2 ->
     disjoint_axiom t_int (t_arrow A1 A2)
 | Dax_intRcd : forall (l:label) (A:typ),
     lc_typ A ->
     disjoint_axiom t_int (t_rcd l A)
 | Dax_intAll : forall (A B:typ),
     lc_typ A ->
     lc_typ (t_forall A B) ->
     disjoint_axiom t_int (t_forall A B)
 | Dax_arrowRcd : forall (A1 A2:typ) (l:label) (A:typ),
     lc_typ A1 ->
     lc_typ A2 ->
     lc_typ A ->
     disjoint_axiom (t_arrow A1 A2) (t_rcd l A)
 | Dax_arrowAll : forall (A1 A2 A B:typ),
     lc_typ A1 ->
     lc_typ A2 ->
     lc_typ A ->
     lc_typ (t_forall A B) ->
     disjoint_axiom (t_arrow A1 A2) (t_forall A B)
 | Dax_rcdAll : forall (l:label) (C A B:typ),
     lc_typ C ->
     lc_typ A ->
     lc_typ (t_forall A B) ->
     disjoint_axiom (t_rcd l C) (t_forall A B)
 | Dax_arrowInt : forall (A1 A2:typ),
     lc_typ A1 ->
     lc_typ A2 ->
     disjoint_axiom (t_arrow A1 A2) t_int
 | Dax_rcdInt : forall (l:label) (A:typ),
     lc_typ A ->
     disjoint_axiom (t_rcd l A) t_int
 | Dax_allInt : forall (A B:typ),
     lc_typ A ->
     lc_typ (t_forall A B) ->
     disjoint_axiom (t_forall A B) t_int
 | Dax_rcdArrow : forall (l:label) (A A1 A2:typ),
     lc_typ A ->
     lc_typ A1 ->
     lc_typ A2 ->
     disjoint_axiom (t_rcd l A) (t_arrow A1 A2)
 | Dax_allArrow : forall (A B A1 A2:typ),
     lc_typ A ->
     lc_typ (t_forall A B) ->
     lc_typ A1 ->
     lc_typ A2 ->
     disjoint_axiom (t_forall A B) (t_arrow A1 A2)
 | Dax_allRcd : forall (A B:typ) (l:label) (C:typ),
     lc_typ A ->
     lc_typ (t_forall A B) ->
     lc_typ C ->
     disjoint_axiom (t_forall A B) (t_rcd l C)
 | Dax_rcdNeq : forall (l1:label) (A:typ) (l2:label) (B:typ),
     lc_typ A ->
     lc_typ B ->
      l1  <>  l2  ->
     disjoint_axiom (t_rcd l1 A) (t_rcd l2 B).

Inductive disjoint : tctx -> typ -> typ -> Prop :=
 | D_ax : forall (D:tctx) (A B:typ),
     TCWell D ->
     TWell D A ->
     TWell D B ->
     disjoint_axiom A B ->
     disjoint D A B
 | D_topl : forall (D:tctx) (A B:typ),
     TWell D B ->
     topLike D A ->
     disjoint D A B
 | D_topr : forall (D:tctx) (A B:typ),
     TWell D A ->
     topLike D B ->
     disjoint D A B
 | D_arrow : forall (D:tctx) (A1 A2 B1 B2:typ),
     TWell D (t_arrow A1 A2) ->
     TWell D (t_arrow B1 B2) ->
     disjoint D A2 B2 ->
     disjoint D (t_arrow A1 A2) (t_arrow B1 B2)
 | D_rcdEq : forall (D:tctx) (l:label) (A B:typ),
     disjoint D A B ->
     disjoint D (t_rcd l A) (t_rcd l B)
 | D_all : forall (L:vars) (D:tctx) (A1 B1 A2 B2:typ),
     TWell D A1 ->
     TWell D A2 ->
      ( forall X , X \notin  L  -> disjoint  (cons ( X , (t_and A1 A2) )  D )   ( open_typ_wrt_typ B1 (t_tvar_f X) )   ( open_typ_wrt_typ B2 (t_tvar_f X) )  )  ->
     disjoint D (t_forall A1 B1) (t_forall A2 B2)
 | D_varl : forall (D:tctx) (X:typevar) (B A:typ),
      binds  X A D  ->
     algo_sub D A B ->
     disjoint D (t_tvar_f X) B
 | D_varr : forall (D:tctx) (B:typ) (X:typevar) (A:typ),
      binds  X A D  ->
     algo_sub D A B ->
     disjoint D B (t_tvar_f X)
 | D_andl : forall (D:tctx) (A B A1 A2:typ),
     spl A A1 A2 ->
     disjoint D A1 B ->
     disjoint D A2 B ->
     disjoint D A B
 | D_andr : forall (D:tctx) (A B B1 B2:typ),
     spl B B1 B2 ->
     disjoint D A B1 ->
     disjoint D A B2 ->
     disjoint D A B.

Inductive subsub : typ -> typ -> Prop :=
 | IS_refl : forall (A:typ),
     lc_typ A ->
     subsub A A
 | IS_and : forall (A1 A2 B B1 B2:typ),
     spl B B1 B2 ->
     subsub A1 B1 ->
     subsub A2 B2 ->
     subsub (t_and A1 A2) B.

Inductive DuplicatedType : typ -> typ -> Prop :=
 | DT_refl : forall (A:typ),
     lc_typ A ->
     DuplicatedType A A
 | DT_copy : forall (A B C:typ),
     DuplicatedType A C ->
     DuplicatedType B C ->
     DuplicatedType (t_and A B) C
 | DT_and : forall (A' B' A B:typ),
     DuplicatedType A' A ->
     DuplicatedType B' B ->
     DuplicatedType (t_and A' B') (t_and A B).

Inductive appDist : typ -> typ -> Prop :=
 | AD_andArrow : forall (A1 A2 B1 B2 C1 C2:typ),
     appDist A1 (t_arrow B1 C1) ->
     appDist A2 (t_arrow B2 C2) ->
     appDist (t_and A1 A2) (t_arrow (t_and B1 B2) (t_and C1 C2))
 | AD_andRcd : forall (A1 A2:typ) (l:label) (B1 B2:typ),
     appDist A1 (t_rcd l B1) ->
     appDist A2 (t_rcd l B2) ->
     appDist (t_and A1 A2) (t_rcd l (t_and B1 B2))
 | AD_andAll : forall (A1 A2 B1 B2 C1 C2:typ),
     appDist A1 (t_forall B1 C1) ->
     appDist A2 (t_forall B2 C2) ->
     appDist (t_and A1 A2) (t_forall (t_and B1 B2)  (t_and C1 C2) )
 | AD_refl : forall (A:typ),
     lc_typ A ->
     appDist A A.

Inductive value : exp -> Prop :=
 | V_unit :
     value e_top
 | V_lit : forall (i:int),
     value (e_lit i)
 | V_abs : forall (A:typ) (e:exp) (B:typ),
     lc_typ A ->
     lc_exp (e_abs A e) ->
     lc_typ B ->
     value (e_anno  ( (e_abs A e) )  B)
 | V_bareAbs : forall (A:typ) (e:exp),
     lc_typ A ->
     lc_exp (e_abs A e) ->
     value  ( (e_abs A e) )
 | V_tabs : forall (e:exp) (B:typ),
     lc_exp (e_tabs e) ->
     lc_typ B ->
     value (e_anno  ( (e_tabs e) )  B)
 | V_bareTabs : forall (e:exp),
     lc_exp (e_tabs e) ->
     value  ( (e_tabs e) )
 | V_rcd : forall (l:label) (e:exp) (B:typ),
     lc_exp e ->
     lc_typ B ->
     value (e_anno (e_rcd l e) B)
 | V_bareRcd : forall (l:label) (e:exp),
     lc_exp e ->
     value (e_rcd l e)
 | V_merge : forall (v1 v2:exp),
     value v1 ->
     value v2 ->
     value (e_merge v1 v2).

Inductive casting : exp -> typ -> exp -> Prop :=
 | Cast_int : forall (i:int),
     casting (e_lit i) t_int (e_lit i)
 | Cast_top : forall (v:exp),
      lc_exp  v  ->
     casting v t_top e_top
 | Cast_topArrow : forall (v:exp) (A1 A2:typ),
      lc_exp  v  ->
     ord (t_arrow A1 A2) ->
     topLike  nil  (t_arrow A1 A2) ->
     casting v (t_arrow A1 A2) (e_anno  ( (e_abs t_top e_top) )  (t_arrow A1 A2))
 | Cast_topAll : forall (v:exp) (A1 A2:typ),
      lc_exp  v  ->
     ord (t_forall A1 A2) ->
     topLike  nil  (t_forall A1 A2) ->
     casting v (t_forall A1 A2) (e_anno  ( (e_tabs e_top) )  (t_forall A1 A2))
 | Cast_topRcd : forall (v:exp) (l:label) (A:typ),
      lc_exp  v  ->
     ord (t_rcd l A) ->
     topLike  nil  (t_rcd l A) ->
     casting v (t_rcd l A) (e_anno (e_rcd l e_top) (t_rcd l A))
 | Cast_anno : forall (e:exp) (A B:typ),
     lc_exp e ->
     ord B ->
     notTopLike  nil  B ->
     algo_sub  nil  A B ->
     casting (e_anno e A) B (e_anno e B)
 | Cast_mergel : forall (v1 v2:exp) (A:typ) (v1':exp),
     lc_exp v2 ->
     ord A ->
     casting v1 A v1' ->
     casting (e_merge v1 v2) A v1'
 | Cast_merger : forall (v1 v2:exp) (A:typ) (v2':exp),
     lc_exp v1 ->
     ord A ->
     casting v2 A v2' ->
     casting (e_merge v1 v2) A v2'
 | Cast_and : forall (v:exp) (A:typ) (v1 v2:exp) (B C:typ),
     spl A B C ->
     casting v B v1 ->
     casting v C v2 ->
     casting v A (e_merge v1 v2).

Inductive wrapping : exp -> typ -> exp -> Prop :=
 | EW_top : forall (e:exp),
     lc_exp e ->
     wrapping e t_top e_top
 | EW_topArrow : forall (e:exp) (A1 A2:typ),
     lc_exp e ->
     ord (t_arrow A1 A2) ->
     topLike  nil  (t_arrow A1 A2) ->
     wrapping e (t_arrow A1 A2) (e_anno  ( (e_abs t_top e_top) )  (t_arrow A1 A2))
 | EW_topAll : forall (e:exp) (A1 A2:typ),
     lc_exp e ->
     ord (t_forall A1 A2) ->
     topLike  nil  (t_forall A1 A2) ->
     wrapping e (t_forall A1 A2) (e_anno  ( (e_tabs e_top) )  (t_forall A1 A2))
 | EW_topRcd : forall (e:exp) (l:label) (A:typ),
     lc_exp e ->
     ord (t_rcd l A) ->
     topLike  nil  (t_rcd l A) ->
     wrapping e (t_rcd l A) (e_anno (e_rcd l e_top) (t_rcd l A))
 | EW_anno : forall (e:exp) (A:typ),
     lc_exp e ->
     ord A ->
     notTopLike  nil  A ->
     wrapping e A (e_anno e A)
 | EW_and : forall (e:exp) (A:typ) (e1 e2:exp) (B C:typ),
     spl A B C ->
     wrapping e B e1 ->
     wrapping e C e2 ->
     wrapping e A (e_merge e1 e2).

Inductive papp : exp -> arg -> exp -> Prop :=
 | PApp_abs : forall (A:typ) (e1:exp) (B:typ) (e2 e2':exp) (C2 C1:typ),
     lc_exp (e_abs A e1) ->
     appDist B (t_arrow C1 C2) ->
     wrapping e2 A e2' ->
     papp (e_anno  ( (e_abs A e1) )  B) (arg_exp e2) (e_anno  (  (open_exp_wrt_exp  e1 e2' )  )  C2)
 | PApp_tabs : forall (e:exp) (A C B2 B1:typ),
     lc_exp (e_tabs e) ->
     lc_typ C ->
     appDist A (t_forall B1 B2) ->
     papp (e_anno  ( (e_tabs e) )  A) (arg_typ C) (e_anno  (  (open_exp_wrt_typ  e C )  )    (open_typ_wrt_typ  B2 C )  )
 | PApp_proj : forall (l:label) (e:exp) (A B:typ),
     lc_exp e ->
     appDist A (t_rcd l B) ->
     papp (e_anno (e_rcd l e) A) (arg_la l) (e_anno e B)
 | PApp_merge : forall (v1 v2:exp) (arg5:arg) (e1 e2:exp),
     papp v1 arg5 e1 ->
     papp v2 arg5 e2 ->
     papp (e_merge v1 v2) arg5 (e_merge e1 e2).

Inductive prevalue : exp -> Prop :=
 | PV_int : forall (i:int),
     prevalue (e_lit i)
 | PV_top :
     prevalue e_top
 | PV_anno : forall (e:exp) (A:typ),
     lc_exp e ->
     lc_typ A ->
     prevalue (e_anno e A)
 | PV_merge : forall (u1 u2:exp),
     prevalue u1 ->
     prevalue u2 ->
     prevalue (e_merge u1 u2).

Inductive pType : exp -> typ -> Prop :=
 | PT_top :
     pType e_top t_top
 | PT_int : forall (i:int),
     pType (e_lit i) t_int
 | PT_anno : forall (e:exp) (A:typ),
     lc_exp e ->
     lc_typ A ->
     pType  ( (e_anno e A) )  A
 | PT_merge : forall (u1 u2:exp) (A B:typ),
     pType u1 A ->
     pType u2 B ->
     pType  ( (e_merge u1 u2) )   (t_and A B) .

Inductive consistent : exp -> exp -> Prop :=
 | C_lit : forall (i:int),
     consistent (e_lit i) (e_lit i)
 | C_anno : forall (e:exp) (A B:typ),
     lc_typ A ->
     lc_exp e ->
     lc_typ B ->
     consistent (e_anno e A) (e_anno e B)
 | C_disjoint : forall (u1 u2:exp) (A B:typ),
     pType u1 A ->
     pType u2 B ->
     disjoint  nil  A B ->
     prevalue u1 ->
     prevalue u2 ->
     consistent u1 u2
 | C_mergel : forall (u1 u2 u:exp),
     consistent u1 u ->
     consistent u2 u ->
     consistent (e_merge u1 u2) u
 | C_merger : forall (u u1 u2:exp),
     consistent u u1 ->
     consistent u u2 ->
     consistent u (e_merge u1 u2).

Inductive Typing : tctx -> ctx -> exp -> dirflag -> typ -> Prop :=
 | Typ_top : forall (D:tctx) (G:ctx),
     TCWell D ->
     CWell D G ->
      uniq  G  ->
     Typing D G e_top Inf t_top
 | Typ_lit : forall (D:tctx) (G:ctx) (i:int),
     TCWell D ->
     CWell D G ->
      uniq  G  ->
     Typing D G (e_lit i) Inf t_int
 | Typ_var : forall (D:tctx) (G:ctx) (x:termvar) (A:typ),
     TCWell D ->
     CWell D G ->
      binds  x A G  ->
      uniq  G  ->
     Typing D G (e_var_f x) Inf A
 | Typ_abs : forall (L:vars) (D:tctx) (G:ctx) (A:typ) (e:exp) (B1 B2:typ),
      algo_sub D B1 A  ->
      ( forall x , x \notin  L  -> Typing D  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk B2 )  ->
     Typing D G (e_abs A e) Chk (t_arrow B1 B2)
 | Typ_app : forall (D:tctx) (G:ctx) (e1 e2:exp) (C A B:typ),
     Typing D G e1 Inf A ->
      appDist A (t_arrow B C)  ->
     Typing D G e2 Chk B ->
     Typing D G (e_app e1 e2) Inf C
 | Typ_tabs : forall (L:vars) (D:tctx) (G:ctx) (e:exp) (A B:typ),
     CWell D G ->
      ( forall X , X \notin  L  -> Typing  (cons ( X , A )  D )  G  ( open_exp_wrt_typ e (t_tvar_f X) )  Chk  ( open_typ_wrt_typ B (t_tvar_f X) )  )  ->
     Typing D G (e_tabs e) Chk (t_forall A B)
 | Typ_tapp : forall (D:tctx) (G:ctx) (e:exp) (A C2 B C1:typ),
     Typing D G e Inf B ->
      appDist B (t_forall C1 C2)  ->
      disjoint D A C1  ->
     Typing D G (e_tapp e A) Inf  (open_typ_wrt_typ  C2 A )
 | Typ_proj : forall (D:tctx) (G:ctx) (e:exp) (l:label) (C A:typ),
     Typing D G e Inf A ->
      appDist A (t_rcd l C)  ->
     Typing D G (e_proj e l) Inf C
 | Typ_rcd : forall (D:tctx) (G:ctx) (l:label) (e:exp) (A:typ),
     Typing D G e Chk A ->
     Typing D G (e_rcd l e) Chk (t_rcd l A)
 | Typ_merge : forall (D:tctx) (G:ctx) (e1 e2:exp) (A B:typ),
     Typing D G e1 Inf A ->
     Typing D G e2 Inf B ->
      disjoint D A B  ->
     Typing D G (e_merge e1 e2) Inf (t_and A B)
 | Typ_inter : forall (D:tctx) (G:ctx) (e:exp) (A B:typ),
     Typing D G e Chk A ->
     Typing D G e Chk B ->
     Typing D G e Chk (t_and A B)
 | Typ_anno : forall (D:tctx) (G:ctx) (e:exp) (A:typ),
     Typing D G e Chk A ->
     Typing D G  ( (e_anno e A) )  Inf A
 | Typ_fix : forall (L:vars) (D:tctx) (G:ctx) (A:typ) (e:exp),
      ( forall x , x \notin  L  -> Typing D  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk A )  ->
     Typing D G (e_fixpoint A e) Inf A
 | Typ_mergev : forall (D:tctx) (G:ctx) (u1 u2:exp) (A B:typ),
     TCWell D ->
     CWell D G ->
      uniq  G  ->
     Typing  nil   nil  u1 Inf A ->
     Typing  nil   nil  u2 Inf B ->
      consistent u1 u2  ->
     Typing D G (e_merge u1 u2) Inf (t_and A B)
 | Typ_sub : forall (D:tctx) (G:ctx) (e:exp) (B A:typ),
     Typing D G e Inf A ->
      algo_sub D A B  ->
     Typing D G e Chk B.

Inductive step : exp -> exp -> Prop :=
 | Step_papp : forall (v e e':exp),
     value v ->
     papp v (arg_exp e) e' ->
     step (e_app v e) e'
 | Step_pproj : forall (v:exp) (l:label) (e:exp),
     value v ->
     papp v (arg_la l) e ->
     step (e_proj v l) e
 | Step_ptapp : forall (v:exp) (A:typ) (e:exp),
     value v ->
     papp v (arg_typ A) e ->
     step (e_tapp v A) e
 | Step_annov : forall (v:exp) (A:typ) (v':exp),
     value v ->
     prevalue v ->
     casting v A v' ->
     step (e_anno v A) v'
 | Step_appl : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     step e1 e1' ->
     step (e_app e1 e2) (e_app e1' e2)
 | Step_merge : forall (e1 e2 e1' e2':exp),
     step e1 e1' ->
     step e2 e2' ->
     step (e_merge e1 e2) (e_merge e1' e2')
 | Step_mergel : forall (e1 v2 e1':exp),
     value v2 ->
     step e1 e1' ->
     step (e_merge e1 v2) (e_merge e1' v2)
 | Step_merger : forall (v1 e2 e2':exp),
     value v1 ->
     step e2 e2' ->
     step (e_merge v1 e2) (e_merge v1 e2')
 | Step_anno : forall (e:exp) (A:typ) (e':exp),
     lc_typ A ->
     step e e' ->
     step (e_anno e A) (e_anno e' A)
 | Step_fix : forall (A:typ) (e:exp),
     lc_exp (e_fixpoint A e) ->
     lc_typ A ->
     step (e_fixpoint A e) (e_anno  (open_exp_wrt_exp  e (e_fixpoint A e) )  A)
 | Step_proj : forall (e:exp) (l:label) (e':exp),
     step e e' ->
     step (e_proj e l) (e_proj e' l)
 | Step_tapp : forall (e:exp) (A:typ) (e':exp),
     lc_typ A ->
     step e e' ->
     step (e_tapp e A) (e_tapp e' A).
