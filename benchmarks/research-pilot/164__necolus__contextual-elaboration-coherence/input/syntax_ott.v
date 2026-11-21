Require Import Metalib.Metatheory.

Definition i := nat.

Inductive co : Set :=
 | co_id : co
 | co_trans (c1:co) (c2:co)
 | co_top : co
 | co_arr (c1:co) (c2:co)
 | co_pair (c1:co) (c2:co)
 | co_proj1 : co
 | co_proj2 : co
 | co_distArr : co
 | co_distRcd (l:i)
 | co_rcd (l:i) (c:co)
 | co_topArr : co
 | co_topRcd (l:i).

Inductive styp : Set :=
 | styp_top : styp
 | styp_nat : styp
 | styp_and (A:styp) (B:styp)
 | styp_arrow (A:styp) (B:styp)
 | styp_rcd (l:i) (A:styp)  .

Inductive exp : Set :=
 | trm_var_b (_:nat)
 | trm_var_f (x:var)
 | trm_unit : exp
 | trm_lit (i5:i)
 | trm_abs (e:exp)
 | trm_app (e1:exp) (e2:exp)
 | trm_pair (e1:exp) (e2:exp)
 | trm_rcd (l:i) (e:exp)
 | trm_proj (e:exp) (l:i)
 | trm_capp (c:co) (e:exp)  .

Inductive sexp : Set :=
 | e_var_b (_:nat)
 | e_var_f (x:var)
 | e_top : sexp
 | e_lit (i5:i)
 | e_abs (ee:sexp)
 | e_app (ee1:sexp) (ee2:sexp)
 | e_merge (ee1:sexp) (ee2:sexp)
 | e_anno (ee:sexp) (A:styp)
 | e_rcd (l:i) (ee:sexp)
 | e_proj (ee:sexp) (l:i)  .

Inductive st : Set :=
 | st_ty (A:styp)
 | st_la (l:i).

Inductive typ : Set :=
 | a_nat : typ
 | a_unit : typ
 | a_arrow (T1:typ) (T2:typ)
 | a_prod (T1:typ) (T2:typ)
 | a_rcd (l:i) (T:typ)  .

Inductive cc : Set :=
 | cc_Empty : cc
 | cc_Lam (x:var) (cc5:cc)
 | cc_AppL (cc5:cc) (e:exp)
 | cc_AppR (e:exp) (cc5:cc)
 | cc_PairL (cc5:cc) (e:exp)
 | cc_PairR (e:exp) (cc5:cc)
 | cc_Co (c:co) (cc5:cc)
 | cc_Rcd (l:i) (cc5:cc)
 | cc_Proj (cc5:cc) (l:i).

Definition sctx : Set := list ( atom * styp ).

Inductive dirflag : Set :=
 | Inf : dirflag
 | Chk : dirflag.

Inductive C : Set :=
 | C_Empty : C
 | C_Lam (x:var) (C5:C)
 | C_AppL (C5:C) (ee:sexp)
 | C_AppRd (ee:sexp) (C5:C)
 | C_MergeL (C5:C) (ee:sexp)
 | C_MergeR (ee:sexp) (C5:C)
 | C_Anno (C5:C) (A:styp)
 | C_Rcd (l:i) (C5:C)
 | C_Proj (C5:C) (l:i).

Definition ls : Set := list st.

Definition ctx : Set := list ( atom * typ ).

Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (trm_var_b nat) =>
      match lt_eq_lt_dec nat k with
        | inleft (left _) => trm_var_b nat
        | inleft (right _) => e_5
        | inright _ => trm_var_b (nat - 1)
      end
  | (trm_var_f x) => trm_var_f x
  | trm_unit => trm_unit
  | (trm_lit i5) => trm_lit i5
  | (trm_abs e) => trm_abs (open_exp_wrt_exp_rec (S k) e_5 e)
  | (trm_app e1 e2) => trm_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (trm_pair e1 e2) => trm_pair (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (trm_rcd l e) => trm_rcd l (open_exp_wrt_exp_rec k e_5 e)
  | (trm_proj e l) => trm_proj (open_exp_wrt_exp_rec k e_5 e) l
  | (trm_capp c e) => trm_capp c (open_exp_wrt_exp_rec k e_5 e)
end.

Fixpoint open_sexp_wrt_sexp_rec (k:nat) (ee_5:sexp) (ee__6:sexp) {struct ee__6}: sexp :=
  match ee__6 with
  | (e_var_b nat) =>
      match lt_eq_lt_dec nat k with
        | inleft (left _) => e_var_b nat
        | inleft (right _) => ee_5
        | inright _ => e_var_b (nat - 1)
      end
  | (e_var_f x) => e_var_f x
  | e_top => e_top
  | (e_lit i5) => e_lit i5
  | (e_abs ee) => e_abs (open_sexp_wrt_sexp_rec (S k) ee_5 ee)
  | (e_app ee1 ee2) => e_app (open_sexp_wrt_sexp_rec k ee_5 ee1) (open_sexp_wrt_sexp_rec k ee_5 ee2)
  | (e_merge ee1 ee2) => e_merge (open_sexp_wrt_sexp_rec k ee_5 ee1) (open_sexp_wrt_sexp_rec k ee_5 ee2)
  | (e_anno ee A) => e_anno (open_sexp_wrt_sexp_rec k ee_5 ee) A
  | (e_rcd l ee) => e_rcd l (open_sexp_wrt_sexp_rec k ee_5 ee)
  | (e_proj ee l) => e_proj (open_sexp_wrt_sexp_rec k ee_5 ee) l
end.

Fixpoint open_cc_wrt_exp_rec (k:nat) (e5:exp) (cc_6:cc) {struct cc_6}: cc :=
  match cc_6 with
  | cc_Empty => cc_Empty
  | (cc_Lam x cc5) => cc_Lam x (open_cc_wrt_exp_rec k e5 cc5)
  | (cc_AppL cc5 e) => cc_AppL (open_cc_wrt_exp_rec k e5 cc5) (open_exp_wrt_exp_rec k e5 e)
  | (cc_AppR e cc5) => cc_AppR (open_exp_wrt_exp_rec k e5 e) (open_cc_wrt_exp_rec k e5 cc5)
  | (cc_PairL cc5 e) => cc_PairL (open_cc_wrt_exp_rec k e5 cc5) (open_exp_wrt_exp_rec k e5 e)
  | (cc_PairR e cc5) => cc_PairR (open_exp_wrt_exp_rec k e5 e) (open_cc_wrt_exp_rec k e5 cc5)
  | (cc_Co c cc5) => cc_Co c (open_cc_wrt_exp_rec k e5 cc5)
  | (cc_Rcd l cc5) => cc_Rcd l (open_cc_wrt_exp_rec k e5 cc5)
  | (cc_Proj cc5 l) => cc_Proj (open_cc_wrt_exp_rec k e5 cc5) l
end.

Fixpoint open_C_wrt_sexp_rec (k:nat) (ee5:sexp) (C_6:C) {struct C_6}: C :=
  match C_6 with
  | C_Empty => C_Empty
  | (C_Lam x C5) => C_Lam x (open_C_wrt_sexp_rec k ee5 C5)
  | (C_AppL C5 ee) => C_AppL (open_C_wrt_sexp_rec k ee5 C5) (open_sexp_wrt_sexp_rec k ee5 ee)
  | (C_AppRd ee C5) => C_AppRd (open_sexp_wrt_sexp_rec k ee5 ee) (open_C_wrt_sexp_rec k ee5 C5)
  | (C_MergeL C5 ee) => C_MergeL (open_C_wrt_sexp_rec k ee5 C5) (open_sexp_wrt_sexp_rec k ee5 ee)
  | (C_MergeR ee C5) => C_MergeR (open_sexp_wrt_sexp_rec k ee5 ee) (open_C_wrt_sexp_rec k ee5 C5)
  | (C_Anno C5 A) => C_Anno (open_C_wrt_sexp_rec k ee5 C5) A
  | (C_Rcd l C5) => C_Rcd l (open_C_wrt_sexp_rec k ee5 C5)
  | (C_Proj C5 l) => C_Proj (open_C_wrt_sexp_rec k ee5 C5) l
end.

Definition open_cc_wrt_exp e5 cc_6 := open_cc_wrt_exp_rec 0 cc_6 e5.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

Definition open_C_wrt_sexp ee5 C_6 := open_C_wrt_sexp_rec 0 C_6 ee5.

Definition open_sexp_wrt_sexp ee_5 ee__6 := open_sexp_wrt_sexp_rec 0 ee__6 ee_5.

Inductive lc_exp : exp -> Prop :=
 | lc_trm_var_f : forall (x:var),
     (lc_exp (trm_var_f x))
 | lc_trm_unit :
     (lc_exp trm_unit)
 | lc_trm_lit : forall (i5:i),
     (lc_exp (trm_lit i5))
 | lc_trm_abs : forall (e:exp),
      ( forall x , lc_exp  ( open_exp_wrt_exp e (trm_var_f x) )  )  ->
     (lc_exp (trm_abs e))
 | lc_trm_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (trm_app e1 e2))
 | lc_trm_pair : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (trm_pair e1 e2))
 | lc_trm_rcd : forall (l:i) (e:exp),
     (lc_exp e) ->
     (lc_exp (trm_rcd l e))
 | lc_trm_proj : forall (e:exp) (l:i),
     (lc_exp e) ->
     (lc_exp (trm_proj e l))
 | lc_trm_capp : forall (c:co) (e:exp),
     (lc_exp e) ->
     (lc_exp (trm_capp c e)).

Inductive lc_sexp : sexp -> Prop :=
 | lc_e_var_f : forall (x:var),
     (lc_sexp (e_var_f x))
 | lc_e_top :
     (lc_sexp e_top)
 | lc_e_lit : forall (i5:i),
     (lc_sexp (e_lit i5))
 | lc_e_abs : forall (ee:sexp),
      ( forall x , lc_sexp  ( open_sexp_wrt_sexp ee (e_var_f x) )  )  ->
     (lc_sexp (e_abs ee))
 | lc_e_app : forall (ee1 ee2:sexp),
     (lc_sexp ee1) ->
     (lc_sexp ee2) ->
     (lc_sexp (e_app ee1 ee2))
 | lc_e_merge : forall (ee1 ee2:sexp),
     (lc_sexp ee1) ->
     (lc_sexp ee2) ->
     (lc_sexp (e_merge ee1 ee2))
 | lc_e_anno : forall (ee:sexp) (A:styp),
     (lc_sexp ee) ->
     (lc_sexp (e_anno ee A))
 | lc_e_rcd : forall (l:i) (ee:sexp),
     (lc_sexp ee) ->
     (lc_sexp (e_rcd l ee))
 | lc_e_proj : forall (ee:sexp) (l:i),
     (lc_sexp ee) ->
     (lc_sexp (e_proj ee l)).

Inductive lc_cc : cc -> Prop :=
 | lc_cc_Empty :
     (lc_cc cc_Empty)
 | lc_cc_Lam : forall (x:var) (cc5:cc),
     (lc_cc cc5) ->
     (lc_cc (cc_Lam x cc5))
 | lc_cc_AppL : forall (cc5:cc) (e:exp),
     (lc_cc cc5) ->
     (lc_exp e) ->
     (lc_cc (cc_AppL cc5 e))
 | lc_cc_AppR : forall (e:exp) (cc5:cc),
     (lc_exp e) ->
     (lc_cc cc5) ->
     (lc_cc (cc_AppR e cc5))
 | lc_cc_PairL : forall (cc5:cc) (e:exp),
     (lc_cc cc5) ->
     (lc_exp e) ->
     (lc_cc (cc_PairL cc5 e))
 | lc_cc_PairR : forall (e:exp) (cc5:cc),
     (lc_exp e) ->
     (lc_cc cc5) ->
     (lc_cc (cc_PairR e cc5))
 | lc_cc_Co : forall (c:co) (cc5:cc),
     (lc_cc cc5) ->
     (lc_cc (cc_Co c cc5))
 | lc_cc_Rcd : forall (l:i) (cc5:cc),
     (lc_cc cc5) ->
     (lc_cc (cc_Rcd l cc5))
 | lc_cc_Proj : forall (cc5:cc) (l:i),
     (lc_cc cc5) ->
     (lc_cc (cc_Proj cc5 l)).

Inductive lc_C : C -> Prop :=
 | lc_C_Empty :
     (lc_C C_Empty)
 | lc_C_Lam : forall (x:var) (C5:C),
     (lc_C C5) ->
     (lc_C (C_Lam x C5))
 | lc_C_AppL : forall (C5:C) (ee:sexp),
     (lc_C C5) ->
     (lc_sexp ee) ->
     (lc_C (C_AppL C5 ee))
 | lc_C_AppRd : forall (ee:sexp) (C5:C),
     (lc_sexp ee) ->
     (lc_C C5) ->
     (lc_C (C_AppRd ee C5))
 | lc_C_MergeL : forall (C5:C) (ee:sexp),
     (lc_C C5) ->
     (lc_sexp ee) ->
     (lc_C (C_MergeL C5 ee))
 | lc_C_MergeR : forall (ee:sexp) (C5:C),
     (lc_sexp ee) ->
     (lc_C C5) ->
     (lc_C (C_MergeR ee C5))
 | lc_C_Anno : forall (C5:C) (A:styp),
     (lc_C C5) ->
     (lc_C (C_Anno C5 A))
 | lc_C_Rcd : forall (l:i) (C5:C),
     (lc_C C5) ->
     (lc_C (C_Rcd l C5))
 | lc_C_Proj : forall (C5:C) (l:i),
     (lc_C C5) ->
     (lc_C (C_Proj C5 l)).

Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (trm_var_b nat) => {}
  | (trm_var_f x) => {{x}}
  | trm_unit => {}
  | (trm_lit i5) => {}
  | (trm_abs e) => (fv_exp e)
  | (trm_app e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (trm_pair e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (trm_rcd l e) => (fv_exp e)
  | (trm_proj e l) => (fv_exp e)
  | (trm_capp c e) => (fv_exp e)
end.

Fixpoint fv_cc (cc_6:cc) : vars :=
  match cc_6 with
  | cc_Empty => {}
  | (cc_Lam x cc5) => (fv_cc cc5)
  | (cc_AppL cc5 e) => (fv_cc cc5) \u (fv_exp e)
  | (cc_AppR e cc5) => (fv_exp e) \u (fv_cc cc5)
  | (cc_PairL cc5 e) => (fv_cc cc5) \u (fv_exp e)
  | (cc_PairR e cc5) => (fv_exp e) \u (fv_cc cc5)
  | (cc_Co c cc5) => (fv_cc cc5)
  | (cc_Rcd l cc5) => (fv_cc cc5)
  | (cc_Proj cc5 l) => (fv_cc cc5)
end.

Fixpoint subst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (trm_var_b nat) => trm_var_b nat
  | (trm_var_f x) => (if eq_var x x5 then e_5 else (trm_var_f x))
  | trm_unit => trm_unit
  | (trm_lit i5) => trm_lit i5
  | (trm_abs e) => trm_abs (subst_exp e_5 x5 e)
  | (trm_app e1 e2) => trm_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (trm_pair e1 e2) => trm_pair (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (trm_rcd l e) => trm_rcd l (subst_exp e_5 x5 e)
  | (trm_proj e l) => trm_proj (subst_exp e_5 x5 e) l
  | (trm_capp c e) => trm_capp c (subst_exp e_5 x5 e)
end.

Fixpoint subst_cc (e5:exp) (x5:var) (cc_6:cc) {struct cc_6} : cc :=
  match cc_6 with
  | cc_Empty => cc_Empty
  | (cc_Lam x cc5) => cc_Lam x (subst_cc e5 x5 cc5)
  | (cc_AppL cc5 e) => cc_AppL (subst_cc e5 x5 cc5) (subst_exp e5 x5 e)
  | (cc_AppR e cc5) => cc_AppR (subst_exp e5 x5 e) (subst_cc e5 x5 cc5)
  | (cc_PairL cc5 e) => cc_PairL (subst_cc e5 x5 cc5) (subst_exp e5 x5 e)
  | (cc_PairR e cc5) => cc_PairR (subst_exp e5 x5 e) (subst_cc e5 x5 cc5)
  | (cc_Co c cc5) => cc_Co c (subst_cc e5 x5 cc5)
  | (cc_Rcd l cc5) => cc_Rcd l (subst_cc e5 x5 cc5)
  | (cc_Proj cc5 l) => cc_Proj (subst_cc e5 x5 cc5) l
end.

Fixpoint calAnd (fs : ls) : co :=
  match fs with
  | nil => co_id
  | cons l fs' =>
    match l with
    | st_ty _ => (co_trans (co_arr co_id (calAnd fs')) co_distArr)
    | st_la l => (co_trans (co_rcd l (calAnd fs')) (co_distRcd l))
    end
  end.

Fixpoint calTop (fs : ls) : co :=
  match fs with
  | nil => co_top
  | cons l fs' =>
    match l with
    | st_ty _ =>  (co_trans (co_arr co_id (calTop fs')) (co_trans (co_arr co_top co_top) (co_trans co_topArr co_top)))
    | st_la l => (co_trans (co_rcd l (calTop fs')) (co_topRcd l))
    end
  end.

Fixpoint ptyp2styp (A : styp) : typ :=
  match A with
    | styp_nat => a_nat
    | styp_arrow A1 A2  => a_arrow (ptyp2styp A1) (ptyp2styp A2)
    | styp_and A1 A2 => a_prod (ptyp2styp A1) (ptyp2styp A2)
    | styp_top => a_unit
    | styp_rcd l A => a_rcd l (ptyp2styp A)
  end.

Inductive sub : styp -> styp -> co -> Prop :=
 | S_refl : forall (A:styp),
     sub A A co_id
 | S_trans : forall (A1 A3:styp) (c1 c2:co) (A2:styp),
     sub A2 A3 c1 ->
     sub A1 A2 c2 ->
     sub A1 A3 (co_trans c1 c2)
 | S_top : forall (A:styp),
     sub A styp_top co_top
 | S_topArr :
     sub styp_top (styp_arrow styp_top styp_top) co_topArr
 | S_topRcd : forall (l:i),
     sub styp_top (styp_rcd l styp_top) (co_topRcd l)
 | S_arr : forall (A1 A2 B1 B2:styp) (c1 c2:co),
     sub B1 A1 c1 ->
     sub A2 B2 c2 ->
     sub (styp_arrow A1 A2) (styp_arrow B1 B2) (co_arr c1 c2)
 | S_and : forall (A1 A2 A3:styp) (c1 c2:co),
     sub A1 A2 c1 ->
     sub A1 A3 c2 ->
     sub A1 (styp_and A2 A3) (co_pair c1 c2)
 | S_andl : forall (A1 A2:styp),
     sub (styp_and A1 A2) A1 co_proj1
 | S_andr : forall (A1 A2:styp),
     sub (styp_and A1 A2) A2 co_proj2
 | S_distArr : forall (A1 A2 A3:styp),
     sub (styp_and  (styp_arrow A1 A2)   (styp_arrow A1 A3) ) (styp_arrow A1 (styp_and A2 A3)) co_distArr
 | S_rcd : forall (l:i) (A B:styp) (c:co),
     sub A B c ->
     sub (styp_rcd l A) (styp_rcd l B) (co_rcd l c)
 | S_distRcd : forall (l:i) (A B:styp),
     sub (styp_and (styp_rcd l A) (styp_rcd l B)) (styp_rcd l (styp_and A B)) (co_distRcd l).

Inductive ASub : ls -> styp -> styp -> co -> Prop :=
 | A_nat :
     ASub  nil  styp_nat styp_nat co_id
 | A_rcdNat : forall (l:i) (fs:ls) (A:styp) (c:co),
     ASub fs A styp_nat c ->
     ASub  (cons (st_la  l )  fs )  (styp_rcd l A) styp_nat (co_rcd l c)
 | A_rcd : forall (fs:ls) (A:styp) (l:i) (B:styp) (c:co),
     ASub  ( fs  ++ (cons (st_la  l ) nil))  A B c ->
     ASub fs A (styp_rcd l B) c
 | A_top : forall (fs:ls) (A:styp),
     ASub fs A styp_top (co_trans  (calTop  fs )  co_top)
 | A_and : forall (fs:ls) (A B1 B2:styp) (c1 c2:co),
     ASub fs A B1 c1 ->
     ASub fs A B2 c2 ->
     ASub fs A (styp_and B1 B2) (co_trans  (calAnd  fs )  (co_pair c1 c2))
 | A_arr : forall (fs:ls) (A B1 B2:styp) (c:co),
     ASub  ( fs  ++ (cons (st_ty  B1 ) nil))  A B2 c ->
     ASub fs A (styp_arrow B1 B2) c
 | A_andN1 : forall (fs:ls) (A1 A2:styp) (c:co),
     ASub fs A1 styp_nat c ->
     ASub fs (styp_and A1 A2) styp_nat (co_trans c co_proj1)
 | A_andN2 : forall (fs:ls) (A1 A2:styp) (c:co),
     ASub fs A2 styp_nat c ->
     ASub fs (styp_and A1 A2) styp_nat (co_trans c co_proj2)
 | A_arrNat : forall (A:styp) (fs:ls) (A1 A2:styp) (c1 c2:co),
     ASub  nil  A A1 c1 ->
     ASub fs A2 styp_nat c2 ->
     ASub  (cons (st_ty  A )  fs )  (styp_arrow A1 A2) styp_nat (co_arr c1 c2).

Inductive disjoint : styp -> styp -> Prop :=
 | D_topL : forall (A:styp),
     disjoint styp_top A
 | D_topR : forall (A:styp),
     disjoint A styp_top
 | D_arr : forall (A1 A2 B1 B2:styp),
     disjoint A2 B2 ->
     disjoint (styp_arrow A1 A2) (styp_arrow B1 B2)
 | D_andL : forall (A1 A2 B:styp),
     disjoint A1 B ->
     disjoint A2 B ->
     disjoint (styp_and A1 A2) B
 | D_andR : forall (A B1 B2:styp),
     disjoint A B1 ->
     disjoint A B2 ->
     disjoint A (styp_and B1 B2)
 | D_rcdEq : forall (l:i) (A B:styp),
     disjoint A B ->
     disjoint (styp_rcd l A) (styp_rcd l B)
 | D_rcdNeq : forall (l1:i) (A:styp) (l2:i) (B:styp),
      l1  <>  l2  ->
     disjoint (styp_rcd l1 A) (styp_rcd l2 B)
 | D_axNatArr : forall (A1 A2:styp),
     disjoint styp_nat (styp_arrow A1 A2)
 | D_axArrNat : forall (A1 A2:styp),
     disjoint (styp_arrow A1 A2) styp_nat
 | D_axNatRcd : forall (l:i) (A:styp),
     disjoint styp_nat (styp_rcd l A)
 | D_axRcdNat : forall (l:i) (A:styp),
     disjoint (styp_rcd l A) styp_nat
 | D_axArrRcd : forall (A1 A2:styp) (l:i) (A:styp),
     disjoint (styp_arrow A1 A2) (styp_rcd l A)
 | D_axRcdArr : forall (l:i) (A A1 A2:styp),
     disjoint (styp_rcd l A) (styp_arrow A1 A2).

Inductive has_type : sctx -> sexp -> dirflag -> styp -> exp -> Prop :=
 | T_top : forall (GG:sctx),
      uniq  GG  ->
     has_type GG e_top Inf styp_top trm_unit
 | T_lit : forall (GG:sctx) (i5:i),
      uniq  GG  ->
     has_type GG (e_lit i5) Inf styp_nat (trm_lit i5)
 | T_var : forall (GG:sctx) (x:var) (A:styp),
      uniq  GG  ->
      binds  x A GG  ->
     has_type GG (e_var_f x) Inf A (trm_var_f x)
 | T_app : forall (GG:sctx) (ee1 ee2:sexp) (A2:styp) (e1 e2:exp) (A1:styp),
     has_type GG ee1 Inf (styp_arrow A1 A2) e1 ->
     has_type GG ee2 Chk A1 e2 ->
     has_type GG (e_app ee1 ee2) Inf A2 (trm_app e1 e2)
 | T_merge : forall (GG:sctx) (ee1 ee2:sexp) (A1 A2:styp) (e1 e2:exp),
     has_type GG ee1 Inf A1 e1 ->
     has_type GG ee2 Inf A2 e2 ->
     disjoint A1 A2 ->
     has_type GG (e_merge ee1 ee2) Inf (styp_and A1 A2) (trm_pair e1 e2)
 | T_rcd : forall (GG:sctx) (l:i) (ee:sexp) (A:styp) (e:exp),
     has_type GG ee Inf A e ->
     has_type GG (e_rcd l ee) Inf (styp_rcd l A) (trm_rcd l e)
 | T_proj : forall (GG:sctx) (ee:sexp) (l:i) (A:styp) (e:exp),
     has_type GG ee Inf (styp_rcd l A) e ->
     has_type GG (e_proj ee l) Inf A (trm_proj e l)
 | T_anno : forall (GG:sctx) (ee:sexp) (A:styp) (e:exp),
     has_type GG ee Chk A e ->
     has_type GG (e_anno ee A) Inf A e
 | T_abs : forall (L:vars) (GG:sctx) (ee:sexp) (A B:styp) (e:exp),
      ( forall x , x \notin  L  -> has_type  (( x ~ A )++ GG )   ( open_sexp_wrt_sexp ee (e_var_f x) )  Chk B  ( open_exp_wrt_exp e (trm_var_f x) )  )  ->
     has_type GG (e_abs ee) Chk (styp_arrow A B) (trm_abs e)
 | T_sub : forall (GG:sctx) (ee:sexp) (A:styp) (c:co) (e:exp) (B:styp),
     has_type GG ee Inf B e ->
     sub B A c ->
     has_type GG ee Chk A (trm_capp c e).

Inductive CTyp : C -> sctx -> dirflag -> styp -> sctx -> dirflag -> styp -> cc -> Prop :=
 | CTyp_empty1 : forall (GG:sctx) (A:styp),
     CTyp C_Empty GG Inf A GG Inf A cc_Empty
 | CTyp_empty2 : forall (GG:sctx) (A:styp),
     CTyp C_Empty GG Chk A GG Chk A cc_Empty
 | CTyp_appL1 : forall (C5:C) (ee2:sexp) (GG:sctx) (A:styp) (GG':sctx) (A2:styp) (cc5:cc) (e:exp) (A1:styp),
     CTyp C5 GG Inf A GG' Inf (styp_arrow A1 A2) cc5 ->
     has_type GG' ee2 Chk A1 e ->
     CTyp (C_AppL C5 ee2) GG Inf A GG' Inf A2 (cc_AppL cc5 e)
 | CTyp_appL2 : forall (C5:C) (ee2:sexp) (GG:sctx) (A:styp) (GG':sctx) (A2:styp) (cc5:cc) (e:exp) (A1:styp),
     CTyp C5 GG Chk A GG' Inf (styp_arrow A1 A2) cc5 ->
     has_type GG' ee2 Chk A1 e ->
     CTyp (C_AppL C5 ee2) GG Chk A GG' Inf A2 (cc_AppL cc5 e)
 | CTyp_appR1 : forall (ee1:sexp) (C5:C) (GG:sctx) (A:styp) (GG':sctx) (A2:styp) (e:exp) (cc5:cc) (A1:styp),
     has_type GG' ee1 Inf (styp_arrow A1 A2) e ->
     CTyp C5 GG Inf A GG' Chk A1 cc5 ->
     CTyp (C_AppRd ee1 C5) GG Inf A GG' Inf A2 (cc_AppR e cc5)
 | CTyp_appR2 : forall (ee1:sexp) (C5:C) (GG:sctx) (A:styp) (GG':sctx) (A2:styp) (e:exp) (cc5:cc) (A1:styp),
     has_type GG' ee1 Inf (styp_arrow A1 A2) e ->
     CTyp C5 GG Chk A GG' Chk A1 cc5 ->
     CTyp (C_AppRd ee1 C5) GG Chk A GG' Inf A2 (cc_AppR e cc5)
 | CTyp_mergeL1 : forall (C5:C) (ee2:sexp) (GG:sctx) (A:styp) (GG':sctx) (A1 A2:styp) (cc5:cc) (e:exp),
     CTyp C5 GG Inf A GG' Inf A1 cc5 ->
     has_type GG' ee2 Inf A2 e ->
     disjoint A1 A2 ->
     CTyp (C_MergeL C5 ee2) GG Inf A GG' Inf (styp_and A1 A2) (cc_PairL cc5 e)
 | CTyp_mergeL2 : forall (C5:C) (ee2:sexp) (GG:sctx) (A:styp) (GG':sctx) (A1 A2:styp) (cc5:cc) (e:exp),
     CTyp C5 GG Chk A GG' Inf A1 cc5 ->
     has_type GG' ee2 Inf A2 e ->
     disjoint A1 A2 ->
     CTyp (C_MergeL C5 ee2) GG Chk A GG' Inf (styp_and A1 A2) (cc_PairL cc5 e)
 | CTyp_mergeR1 : forall (ee1:sexp) (C5:C) (GG:sctx) (A:styp) (GG':sctx) (A1 A2:styp) (e:exp) (cc5:cc),
     has_type GG' ee1 Inf A1 e ->
     CTyp C5 GG Inf A GG' Inf A2 cc5 ->
     disjoint A1 A2 ->
     CTyp (C_MergeR ee1 C5) GG Inf A GG' Inf (styp_and A1 A2) (cc_PairR e cc5)
 | CTyp_mergeR2 : forall (ee1:sexp) (C5:C) (GG:sctx) (A:styp) (GG':sctx) (A1 A2:styp) (e:exp) (cc5:cc),
     has_type GG' ee1 Inf A1 e ->
     CTyp C5 GG Chk A GG' Inf A2 cc5 ->
     disjoint A1 A2 ->
     CTyp (C_MergeR ee1 C5) GG Chk A GG' Inf (styp_and A1 A2) (cc_PairR e cc5)
 | CTyp_rcd1 : forall (l:i) (C5:C) (GG:sctx) (A:styp) (GG':sctx) (B:styp) (cc5:cc),
     CTyp C5 GG Inf A GG' Inf B cc5 ->
     CTyp (C_Rcd l C5) GG Inf A GG' Inf (styp_rcd l B) (cc_Rcd l cc5)
 | CTyp_rcd2 : forall (l:i) (C5:C) (GG:sctx) (A:styp) (GG':sctx) (B:styp) (cc5:cc),
     CTyp C5 GG Chk A GG' Inf B cc5 ->
     CTyp (C_Rcd l C5) GG Chk A GG' Inf (styp_rcd l B) (cc_Rcd l cc5)
 | CTyp_proj1 : forall (C5:C) (l:i) (GG:sctx) (A:styp) (GG':sctx) (B:styp) (cc5:cc),
     CTyp C5 GG Inf A GG' Inf (styp_rcd l B) cc5 ->
     CTyp (C_Proj C5 l) GG Inf A GG' Inf B (cc_Proj cc5 l)
 | CTyp_proj2 : forall (C5:C) (l:i) (GG:sctx) (A:styp) (GG':sctx) (B:styp) (cc5:cc),
     CTyp C5 GG Chk A GG' Inf (styp_rcd l B) cc5 ->
     CTyp (C_Proj C5 l) GG Chk A GG' Inf B (cc_Proj cc5 l)
 | CTyp_anno1 : forall (C5:C) (A:styp) (GG:sctx) (B:styp) (GG':sctx) (cc5:cc),
     CTyp C5 GG Inf B GG' Chk A cc5 ->
     CTyp (C_Anno C5 A) GG Inf B GG' Inf A cc5
 | CTyp_anno2 : forall (C5:C) (A:styp) (GG:sctx) (B:styp) (GG':sctx) (cc5:cc),
     CTyp C5 GG Chk B GG' Chk A cc5 ->
     CTyp (C_Anno C5 A) GG Chk B GG' Inf A cc5
 | CTyp_abs1 : forall (x:var) (C5:C) (GG:sctx) (A:styp) (GG':sctx) (A1 A2:styp) (cc5:cc),
     CTyp C5 GG Inf A  (( x ~ A1 )++ GG' )  Chk A2 cc5 ->
      ~ AtomSetImpl.In  x  (dom  GG' )  ->
     CTyp (C_Lam x C5) GG Inf A GG' Chk (styp_arrow A1 A2) (cc_Lam x cc5)
 | CTyp_abs2 : forall (x:var) (C5:C) (GG:sctx) (A:styp) (GG':sctx) (A1 A2:styp) (cc5:cc),
     CTyp C5 GG Chk A  (( x ~ A1 )++ GG' )  Chk A2 cc5 ->
      ~ AtomSetImpl.In  x  (dom  GG' )  ->
     CTyp (C_Lam x C5) GG Chk A GG' Chk (styp_arrow A1 A2) (cc_Lam x cc5).

Inductive cotyp : co -> typ -> typ -> Prop :=
 | cotyp_refl : forall (T:typ),
     cotyp co_id T T
 | cotyp_trans : forall (c1 c2:co) (T1 T3 T2:typ),
     cotyp c1 T2 T3 ->
     cotyp c2 T1 T2 ->
     cotyp (co_trans c1 c2) T1 T3
 | cotyp_top : forall (T:typ),
     cotyp co_top T a_unit
 | cotyp_topArr :
     cotyp co_topArr a_unit (a_arrow a_unit a_unit)
 | cotyp_arr : forall (c1 c2:co) (T1 T2 T1' T2':typ),
     cotyp c1 T1' T1 ->
     cotyp c2 T2 T2' ->
     cotyp (co_arr c1 c2) (a_arrow T1 T2) (a_arrow T1' T2')
 | cotyp_pair : forall (c1 c2:co) (T1 T2 T3:typ),
     cotyp c1 T1 T2 ->
     cotyp c2 T1 T3 ->
     cotyp (co_pair c1 c2) T1 (a_prod T2 T3)
 | cotyp_distArr : forall (T1 T2 T3:typ),
     cotyp co_distArr (a_prod  (a_arrow T1 T2)   (a_arrow T1 T3) ) (a_arrow T1 (a_prod T2 T3))
 | cotyp_projl : forall (T1 T2:typ),
     cotyp co_proj1 (a_prod T1 T2) T1
 | cotyp_projr : forall (T1 T2:typ),
     cotyp co_proj2 (a_prod T1 T2) T2
 | cotyp_rcd : forall (l:i) (c:co) (T1 T2:typ),
     cotyp c T1 T2 ->
     cotyp (co_rcd l c) (a_rcd l T1) (a_rcd l T2)
 | cotyp_topRcd : forall (l:i),
     cotyp (co_topRcd l) a_unit (a_rcd l a_unit)
 | cotyp_distRcd : forall (l:i) (T1 T2:typ),
     cotyp (co_distRcd l) (a_prod (a_rcd l T1) (a_rcd l T2)) (a_rcd l (a_prod T1 T2)).

Inductive typing : ctx -> exp -> typ -> Prop :=
 | typ_unit : forall (G:ctx),
      uniq  G  ->
     typing G trm_unit a_unit
 | typ_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     typing G (trm_lit i5) a_nat
 | typ_var : forall (G:ctx) (x:var) (T:typ),
      uniq  G  ->
      binds  x T G  ->
     typing G (trm_var_f x) T
 | typ_abs : forall (L:vars) (G:ctx) (e:exp) (T1 T2:typ),
      ( forall x , x \notin  L  -> typing  (( x ~ T1 )++ G )   ( open_exp_wrt_exp e (trm_var_f x) )  T2 )  ->
     typing G (trm_abs e) (a_arrow T1 T2)
 | typ_app : forall (G:ctx) (e1 e2:exp) (T2 T1:typ),
     typing G e1 (a_arrow T1 T2) ->
     typing G e2 T1 ->
     typing G (trm_app e1 e2) T2
 | typ_pair : forall (G:ctx) (e1 e2:exp) (T1 T2:typ),
     typing G e1 T1 ->
     typing G e2 T2 ->
     typing G (trm_pair e1 e2) (a_prod T1 T2)
 | typ_capp : forall (G:ctx) (c:co) (e:exp) (T' T:typ),
     typing G e T ->
     cotyp c T T' ->
     typing G (trm_capp c e) T'
 | typ_rcd : forall (G:ctx) (l:i) (e:exp) (T:typ),
     typing G e T ->
     typing G (trm_rcd l e) (a_rcd l T)
 | typ_proj : forall (G:ctx) (e:exp) (l:i) (T:typ),
     typing G e (a_rcd l T) ->
     typing G (trm_proj e l) T.

Inductive value : exp -> Prop :=
 | value_unit :
     value trm_unit
 | value_lit : forall (i5:i),
     value (trm_lit i5)
 | value_abs : forall (e:exp),
     lc_exp (trm_abs e) ->
     value (trm_abs e)
 | value_pair : forall (v1 v2:exp),
     value v1 ->
     value v2 ->
     value (trm_pair v1 v2)
 | value_rcd : forall (l:i) (v:exp),
     value v ->
     value (trm_rcd l v)
 | value_cabs : forall (c1 c2:co) (v:exp),
     value v ->
     value (trm_capp  ( (co_arr c1 c2) )  v)
 | value_cpair : forall (v:exp),
     value v ->
     value (trm_capp co_distArr v)
 | value_topArr : forall (v:exp),
     value v ->
     value (trm_capp co_topArr v).

Inductive step : exp -> exp -> Prop :=
 | step_id : forall (v:exp),
     value v ->
     step (trm_capp co_id v) v
 | step_trans : forall (c1 c2:co) (v:exp),
     value v ->
     step (trm_capp  ( (co_trans c1 c2) )  v) (trm_capp c1  ( (trm_capp c2 v) ) )
 | step_top : forall (v:exp),
     value v ->
     step (trm_capp co_top v) trm_unit
 | step_topArr :
     step (trm_app  ( (trm_capp co_topArr trm_unit) )  trm_unit) trm_unit
 | step_arr : forall (c1 c2:co) (v1 v2:exp),
     value v1 ->
     value v2 ->
     step (trm_app  ( (trm_capp  ( (co_arr c1 c2) )  v1) )  v2) (trm_capp c2  ( (trm_app v1  ( (trm_capp c1 v2) ) ) ) )
 | step_pair : forall (c1 c2:co) (v:exp),
     value v ->
     step (trm_capp (co_pair c1 c2) v) (trm_pair (trm_capp c1 v) (trm_capp c2 v))
 | step_distArr : forall (v1 v2 v3:exp),
     value v1 ->
     value v2 ->
     value v3 ->
     step (trm_app  ( (trm_capp co_distArr (trm_pair v1 v2)) )  v3) (trm_pair (trm_app v1 v3) (trm_app v2 v3))
 | step_projl : forall (v1 v2:exp),
     value v1 ->
     value v2 ->
     step (trm_capp co_proj1 (trm_pair v1 v2)) v1
 | step_projr : forall (v1 v2:exp),
     value v1 ->
     value v2 ->
     step (trm_capp co_proj2 (trm_pair v1 v2)) v2
 | step_crcd : forall (l:i) (c:co) (v:exp),
     value v ->
     step (trm_capp (co_rcd l c) (trm_rcd l v)) (trm_rcd l (trm_capp c v))
 | step_topRcd : forall (l:i),
     step (trm_capp (co_topRcd l) trm_unit) (trm_rcd l trm_unit)
 | step_distRcd : forall (l:i) (v1 v2:exp),
     value v1 ->
     value v2 ->
     step (trm_capp (co_distRcd l) (trm_pair (trm_rcd l v1) (trm_rcd l v2))) (trm_rcd l (trm_pair v1 v2))
 | step_projRcd : forall (l:i) (v:exp),
     value v ->
     step (trm_proj (trm_rcd l v) l) v
 | step_beta : forall (e v:exp),
     lc_exp (trm_abs e) ->
     value v ->
     step (trm_app  ( (trm_abs e) )  v)  (open_exp_wrt_exp  e v )
 | step_app1 : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     step e1 e1' ->
     step (trm_app e1 e2) (trm_app e1' e2)
 | step_app2 : forall (v1 e2 e2':exp),
     value v1 ->
     step e2 e2' ->
     step (trm_app v1 e2) (trm_app v1 e2')
 | step_pair1 : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     step e1 e1' ->
     step (trm_pair e1 e2) (trm_pair e1' e2)
 | step_pair2 : forall (v1 e2 e2':exp),
     value v1 ->
     step e2 e2' ->
     step (trm_pair v1 e2) (trm_pair v1 e2')
 | step_capp : forall (c:co) (e e':exp),
     step e e' ->
     step (trm_capp c e) (trm_capp c e')
 | step_rcd1 : forall (l:i) (e e':exp),
     step e e' ->
     step (trm_rcd l e) (trm_rcd l e')
 | step_rcd2 : forall (e:exp) (l:i) (e':exp),
     step e e' ->
     step (trm_proj e l) (trm_proj e' l).
