Require Import Coq.Logic.FunctionalExtensionality.

Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.

Require Export Metalib.LibLNgen.

Require Export Syntax_ott.

Scheme rlist_ind' := Induction for rlist Sort Prop
  with rt_ind' := Induction for rt Sort Prop
  with rtyp_ind' := Induction for rtyp Sort Prop.

Definition rlist_rt_rtyp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  (conj (rlist_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)
  ((conj (rt_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)
  (rtyp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)))).

Scheme rlist_rec' := Induction for rlist Sort Set
  with rt_rec' := Induction for rt Sort Set
  with rtyp_rec' := Induction for rtyp Sort Set.

Definition rlist_rt_rtyp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  (pair ((pair (rlist_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)
  (rt_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)))
  (rtyp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)).

Scheme rexp_ind' := Induction for rexp Sort Prop.

Definition rexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  rexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.

Scheme rexp_rec' := Induction for rexp Sort Set.

Definition rexp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  rexp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.

Fixpoint close_rlist_wrt_rtyp_rec (n1 : nat) (a1 : typvar) (R1 : rlist) {struct R1} : rlist :=
  match R1 with
    | R_Empty => R_Empty
    | R_Cons r1 R2 => R_Cons (close_rtyp_wrt_rtyp_rec n1 a1 r1) (close_rlist_wrt_rtyp_rec n1 a1 R2)
  end

with close_rt_wrt_rtyp_rec (n1 : nat) (a1 : typvar) (u1 : rt) {struct u1} : rt :=
  match u1 with
    | rt_Base => rt_Base
    | rt_Fun rt1 rt2 => rt_Fun (close_rt_wrt_rtyp_rec n1 a1 rt1) (close_rt_wrt_rtyp_rec n1 a1 rt2)
    | rt_ConQuan R1 rt1 => rt_ConQuan (close_rlist_wrt_rtyp_rec n1 a1 R1) (close_rt_wrt_rtyp_rec (S n1) a1 rt1)
    | rt_Record r1 => rt_Record (close_rtyp_wrt_rtyp_rec n1 a1 r1)
  end

with close_rtyp_wrt_rtyp_rec (n1 : nat) (a1 : typvar) (r1 : rtyp) {struct r1} : rtyp :=
  match r1 with
    | r_TyVar_f a2 => if (a1 == a2) then (r_TyVar_b n1) else (r_TyVar_f a2)
    | r_TyVar_b n2 => if (lt_ge_dec n2 n1) then (r_TyVar_b n2) else (r_TyVar_b (S n2))
    | r_Empty => r_Empty
    | r_SingleField l1 rt1 => r_SingleField l1 (close_rt_wrt_rtyp_rec n1 a1 rt1)
    | r_Merge r2 r3 => r_Merge (close_rtyp_wrt_rtyp_rec n1 a1 r2) (close_rtyp_wrt_rtyp_rec n1 a1 r3)
  end.

Definition close_rlist_wrt_rtyp a1 R1 := close_rlist_wrt_rtyp_rec 0 a1 R1.

Definition close_rt_wrt_rtyp a1 u1 := close_rt_wrt_rtyp_rec 0 a1 u1.

Definition close_rtyp_wrt_rtyp a1 r1 := close_rtyp_wrt_rtyp_rec 0 a1 r1.

Fixpoint close_rexp_wrt_rtyp_rec (n1 : nat) (a1 : typvar) (re1 : rexp) {struct re1} : rexp :=
  match re1 with
    | re_Var_f x1 => re_Var_f x1
    | re_Var_b n2 => re_Var_b n2
    | re_Lit x1 => re_Lit x1
    | re_Abs rt1 re2 => re_Abs (close_rt_wrt_rtyp_rec n1 a1 rt1) (close_rexp_wrt_rtyp_rec n1 a1 re2)
    | re_App re2 re3 => re_App (close_rexp_wrt_rtyp_rec n1 a1 re2) (close_rexp_wrt_rtyp_rec n1 a1 re3)
    | re_Empty => re_Empty
    | re_SingleField l1 re2 => re_SingleField l1 (close_rexp_wrt_rtyp_rec n1 a1 re2)
    | re_Res re2 l1 => re_Res (close_rexp_wrt_rtyp_rec n1 a1 re2) l1
    | re_Merge re2 re3 => re_Merge (close_rexp_wrt_rtyp_rec n1 a1 re2) (close_rexp_wrt_rtyp_rec n1 a1 re3)
    | re_Selection re2 l1 => re_Selection (close_rexp_wrt_rtyp_rec n1 a1 re2) l1
    | re_ConTyAbs R1 re2 => re_ConTyAbs (close_rlist_wrt_rtyp_rec n1 a1 R1) (close_rexp_wrt_rtyp_rec (S n1) a1 re2)
    | re_ConTyApp re2 r1 => re_ConTyApp (close_rexp_wrt_rtyp_rec n1 a1 re2) (close_rtyp_wrt_rtyp_rec n1 a1 r1)
  end.

Fixpoint close_rexp_wrt_rexp_rec (n1 : nat) (x1 : expvar) (re1 : rexp) {struct re1} : rexp :=
  match re1 with
    | re_Var_f x2 => if (x1 == x2) then (re_Var_b n1) else (re_Var_f x2)
    | re_Var_b n2 => if (lt_ge_dec n2 n1) then (re_Var_b n2) else (re_Var_b (S n2))
    | re_Lit n2 => re_Lit n2
    | re_Abs rt1 re2 => re_Abs rt1 (close_rexp_wrt_rexp_rec (S n1) x1 re2)
    | re_App re2 re3 => re_App (close_rexp_wrt_rexp_rec n1 x1 re2) (close_rexp_wrt_rexp_rec n1 x1 re3)
    | re_Empty => re_Empty
    | re_SingleField l1 re2 => re_SingleField l1 (close_rexp_wrt_rexp_rec n1 x1 re2)
    | re_Res re2 l1 => re_Res (close_rexp_wrt_rexp_rec n1 x1 re2) l1
    | re_Merge re2 re3 => re_Merge (close_rexp_wrt_rexp_rec n1 x1 re2) (close_rexp_wrt_rexp_rec n1 x1 re3)
    | re_Selection re2 l1 => re_Selection (close_rexp_wrt_rexp_rec n1 x1 re2) l1
    | re_ConTyAbs R1 re2 => re_ConTyAbs R1 (close_rexp_wrt_rexp_rec n1 x1 re2)
    | re_ConTyApp re2 r1 => re_ConTyApp (close_rexp_wrt_rexp_rec n1 x1 re2) r1
  end.

Definition close_rexp_wrt_rtyp a1 re1 := close_rexp_wrt_rtyp_rec 0 a1 re1.

Definition close_rexp_wrt_rexp x1 re1 := close_rexp_wrt_rexp_rec 0 x1 re1.

Fixpoint size_rlist (R1 : rlist) {struct R1} : nat :=
  match R1 with
    | R_Empty => 1
    | R_Cons r1 R2 => 1 + (size_rtyp r1) + (size_rlist R2)
  end

with size_rt (u1 : rt) {struct u1} : nat :=
  match u1 with
    | rt_Base => 1
    | rt_Fun rt1 rt2 => 1 + (size_rt rt1) + (size_rt rt2)
    | rt_ConQuan R1 rt1 => 1 + (size_rlist R1) + (size_rt rt1)
    | rt_Record r1 => 1 + (size_rtyp r1)
  end

with size_rtyp (r1 : rtyp) {struct r1} : nat :=
  match r1 with
    | r_TyVar_f a1 => 1
    | r_TyVar_b n1 => 1
    | r_Empty => 1
    | r_SingleField l1 rt1 => 1 + (size_rt rt1)
    | r_Merge r2 r3 => 1 + (size_rtyp r2) + (size_rtyp r3)
  end.

Fixpoint size_rexp (re1 : rexp) {struct re1} : nat :=
  match re1 with
    | re_Var_f x1 => 1
    | re_Var_b n1 => 1
    | re_Lit n1 => 1
    | re_Abs rt1 re2 => 1 + (size_rt rt1) + (size_rexp re2)
    | re_App re2 re3 => 1 + (size_rexp re2) + (size_rexp re3)
    | re_Empty => 1
    | re_SingleField l1 re2 => 1 + (size_rexp re2)
    | re_Res re2 l1 => 1 + (size_rexp re2)
    | re_Merge re2 re3 => 1 + (size_rexp re2) + (size_rexp re3)
    | re_Selection re2 l1 => 1 + (size_rexp re2)
    | re_ConTyAbs R1 re2 => 1 + (size_rlist R1) + (size_rexp re2)
    | re_ConTyApp re2 r1 => 1 + (size_rexp re2) + (size_rtyp r1)
  end.

Inductive degree_rlist_wrt_rtyp : nat -> rlist -> Prop :=
  | degree_wrt_rtyp_R_Empty : forall n1,
    degree_rlist_wrt_rtyp n1 (R_Empty)
  | degree_wrt_rtyp_R_Cons : forall n1 r1 R1,
    degree_rtyp_wrt_rtyp n1 r1 ->
    degree_rlist_wrt_rtyp n1 R1 ->
    degree_rlist_wrt_rtyp n1 (R_Cons r1 R1)

with degree_rt_wrt_rtyp : nat -> rt -> Prop :=
  | degree_wrt_rtyp_rt_Base : forall n1,
    degree_rt_wrt_rtyp n1 (rt_Base)
  | degree_wrt_rtyp_rt_Fun : forall n1 rt1 rt2,
    degree_rt_wrt_rtyp n1 rt1 ->
    degree_rt_wrt_rtyp n1 rt2 ->
    degree_rt_wrt_rtyp n1 (rt_Fun rt1 rt2)
  | degree_wrt_rtyp_rt_ConQuan : forall n1 R1 rt1,
    degree_rlist_wrt_rtyp n1 R1 ->
    degree_rt_wrt_rtyp (S n1) rt1 ->
    degree_rt_wrt_rtyp n1 (rt_ConQuan R1 rt1)
  | degree_wrt_rtyp_rt_Record : forall n1 r1,
    degree_rtyp_wrt_rtyp n1 r1 ->
    degree_rt_wrt_rtyp n1 (rt_Record r1)

with degree_rtyp_wrt_rtyp : nat -> rtyp -> Prop :=
  | degree_wrt_rtyp_r_TyVar_f : forall n1 a1,
    degree_rtyp_wrt_rtyp n1 (r_TyVar_f a1)
  | degree_wrt_rtyp_r_TyVar_b : forall n1 n2,
    lt n2 n1 ->
    degree_rtyp_wrt_rtyp n1 (r_TyVar_b n2)
  | degree_wrt_rtyp_r_Empty : forall n1,
    degree_rtyp_wrt_rtyp n1 (r_Empty)
  | degree_wrt_rtyp_r_SingleField : forall n1 l1 rt1,
    degree_rt_wrt_rtyp n1 rt1 ->
    degree_rtyp_wrt_rtyp n1 (r_SingleField l1 rt1)
  | degree_wrt_rtyp_r_Merge : forall n1 r1 r2,
    degree_rtyp_wrt_rtyp n1 r1 ->
    degree_rtyp_wrt_rtyp n1 r2 ->
    degree_rtyp_wrt_rtyp n1 (r_Merge r1 r2).

Scheme degree_rlist_wrt_rtyp_ind' := Induction for degree_rlist_wrt_rtyp Sort Prop
  with degree_rt_wrt_rtyp_ind' := Induction for degree_rt_wrt_rtyp Sort Prop
  with degree_rtyp_wrt_rtyp_ind' := Induction for degree_rtyp_wrt_rtyp Sort Prop.

Definition degree_rlist_wrt_rtyp_degree_rt_wrt_rtyp_degree_rtyp_wrt_rtyp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  (conj (degree_rlist_wrt_rtyp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)
  ((conj (degree_rt_wrt_rtyp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)
  (degree_rtyp_wrt_rtyp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)))).

Inductive degree_rexp_wrt_rtyp : nat -> rexp -> Prop :=
  | degree_wrt_rtyp_re_Var_f : forall n1 x1,
    degree_rexp_wrt_rtyp n1 (re_Var_f x1)
  | degree_wrt_rtyp_re_Var_b : forall n1 n2,
    degree_rexp_wrt_rtyp n1 (re_Var_b n2)
  | degree_wrt_rtyp_re_Lit_f : forall n1 x1,
    degree_rexp_wrt_rtyp n1 (re_Lit x1)
  | degree_wrt_rtyp_re_Abs : forall n1 rt1 re1,
    degree_rt_wrt_rtyp n1 rt1 ->
    degree_rexp_wrt_rtyp n1 re1 ->
    degree_rexp_wrt_rtyp n1 (re_Abs rt1 re1)
  | degree_wrt_rtyp_re_App : forall n1 re1 re2,
    degree_rexp_wrt_rtyp n1 re1 ->
    degree_rexp_wrt_rtyp n1 re2 ->
    degree_rexp_wrt_rtyp n1 (re_App re1 re2)
  | degree_wrt_rtyp_re_Empty : forall n1,
    degree_rexp_wrt_rtyp n1 (re_Empty)
  | degree_wrt_rtyp_re_SingleField : forall n1 l1 re1,
    degree_rexp_wrt_rtyp n1 re1 ->
    degree_rexp_wrt_rtyp n1 (re_SingleField l1 re1)
  | degree_wrt_rtyp_re_Res : forall n1 re1 l1,
    degree_rexp_wrt_rtyp n1 re1 ->
    degree_rexp_wrt_rtyp n1 (re_Res re1 l1)
  | degree_wrt_rtyp_re_Merge : forall n1 re1 re2,
    degree_rexp_wrt_rtyp n1 re1 ->
    degree_rexp_wrt_rtyp n1 re2 ->
    degree_rexp_wrt_rtyp n1 (re_Merge re1 re2)
  | degree_wrt_rtyp_re_Selection : forall n1 re1 l1,
    degree_rexp_wrt_rtyp n1 re1 ->
    degree_rexp_wrt_rtyp n1 (re_Selection re1 l1)
  | degree_wrt_rtyp_re_ConTyAbs : forall n1 R1 re1,
    degree_rlist_wrt_rtyp n1 R1 ->
    degree_rexp_wrt_rtyp (S n1) re1 ->
    degree_rexp_wrt_rtyp n1 (re_ConTyAbs R1 re1)
  | degree_wrt_rtyp_re_ConTyApp : forall n1 re1 r1,
    degree_rexp_wrt_rtyp n1 re1 ->
    degree_rtyp_wrt_rtyp n1 r1 ->
    degree_rexp_wrt_rtyp n1 (re_ConTyApp re1 r1).

Inductive degree_rexp_wrt_rexp : nat -> rexp -> Prop :=
  | degree_wrt_rexp_re_Var_f : forall n1 x1,
    degree_rexp_wrt_rexp n1 (re_Var_f x1)
  | degree_wrt_rexp_re_Var_b : forall n1 n2,
    lt n2 n1 ->
    degree_rexp_wrt_rexp n1 (re_Var_b n2)
  | degree_wrt_rexp_re_Lit : forall n1 x1,
    degree_rexp_wrt_rexp n1 (re_Lit x1)
  | degree_wrt_rexp_re_Abs : forall n1 rt1 re1,
    degree_rexp_wrt_rexp (S n1) re1 ->
    degree_rexp_wrt_rexp n1 (re_Abs rt1 re1)
  | degree_wrt_rexp_re_App : forall n1 re1 re2,
    degree_rexp_wrt_rexp n1 re1 ->
    degree_rexp_wrt_rexp n1 re2 ->
    degree_rexp_wrt_rexp n1 (re_App re1 re2)
  | degree_wrt_rexp_re_Empty : forall n1,
    degree_rexp_wrt_rexp n1 (re_Empty)
  | degree_wrt_rexp_re_SingleField : forall n1 l1 re1,
    degree_rexp_wrt_rexp n1 re1 ->
    degree_rexp_wrt_rexp n1 (re_SingleField l1 re1)
  | degree_wrt_rexp_re_Res : forall n1 re1 l1,
    degree_rexp_wrt_rexp n1 re1 ->
    degree_rexp_wrt_rexp n1 (re_Res re1 l1)
  | degree_wrt_rexp_re_Merge : forall n1 re1 re2,
    degree_rexp_wrt_rexp n1 re1 ->
    degree_rexp_wrt_rexp n1 re2 ->
    degree_rexp_wrt_rexp n1 (re_Merge re1 re2)
  | degree_wrt_rexp_re_Selection : forall n1 re1 l1,
    degree_rexp_wrt_rexp n1 re1 ->
    degree_rexp_wrt_rexp n1 (re_Selection re1 l1)
  | degree_wrt_rexp_re_ConTyAbs : forall n1 R1 re1,
    degree_rexp_wrt_rexp n1 re1 ->
    degree_rexp_wrt_rexp n1 (re_ConTyAbs R1 re1)
  | degree_wrt_rexp_re_ConTyApp : forall n1 re1 r1,
    degree_rexp_wrt_rexp n1 re1 ->
    degree_rexp_wrt_rexp n1 (re_ConTyApp re1 r1).

Scheme degree_rexp_wrt_rtyp_ind' := Induction for degree_rexp_wrt_rtyp Sort Prop.

Definition degree_rexp_wrt_rtyp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  degree_rexp_wrt_rtyp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.

Scheme degree_rexp_wrt_rexp_ind' := Induction for degree_rexp_wrt_rexp Sort Prop.

Definition degree_rexp_wrt_rexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  degree_rexp_wrt_rexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.

Inductive lc_set_rlist : rlist -> Set :=
  | lc_set_R_Empty :
    lc_set_rlist (R_Empty)
  | lc_set_R_Cons : forall r1 R1,
    lc_set_rtyp r1 ->
    lc_set_rlist R1 ->
    lc_set_rlist (R_Cons r1 R1)

with lc_set_rt : rt -> Set :=
  | lc_set_rt_Base :
    lc_set_rt (rt_Base)
  | lc_set_rt_Fun : forall rt1 rt2,
    lc_set_rt rt1 ->
    lc_set_rt rt2 ->
    lc_set_rt (rt_Fun rt1 rt2)
  | lc_set_rt_ConQuan : forall R1 rt1,
    lc_set_rlist R1 ->
    (forall a1 : typvar, lc_set_rt (open_rt_wrt_rtyp rt1 (r_TyVar_f a1))) ->
    lc_set_rt (rt_ConQuan R1 rt1)
  | lc_set_rt_Record : forall r1,
    lc_set_rtyp r1 ->
    lc_set_rt (rt_Record r1)

with lc_set_rtyp : rtyp -> Set :=
  | lc_set_r_TyVar_f : forall a1,
    lc_set_rtyp (r_TyVar_f a1)
  | lc_set_r_Empty :
    lc_set_rtyp (r_Empty)
  | lc_set_r_SingleField : forall l1 rt1,
    lc_set_rt rt1 ->
    lc_set_rtyp (r_SingleField l1 rt1)
  | lc_set_r_Merge : forall r1 r2,
    lc_set_rtyp r1 ->
    lc_set_rtyp r2 ->
    lc_set_rtyp (r_Merge r1 r2).

Scheme lc_rlist_ind' := Induction for lc_rlist Sort Prop
  with lc_rt_ind' := Induction for lc_rt Sort Prop
  with lc_rtyp_ind' := Induction for lc_rtyp Sort Prop.

Definition lc_rlist_lc_rt_lc_rtyp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  (conj (lc_rlist_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)
  ((conj (lc_rt_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)
  (lc_rtyp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)))).

Scheme lc_set_rlist_ind' := Induction for lc_set_rlist Sort Prop
  with lc_set_rt_ind' := Induction for lc_set_rt Sort Prop
  with lc_set_rtyp_ind' := Induction for lc_set_rtyp Sort Prop.

Definition lc_set_rlist_lc_set_rt_lc_set_rtyp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  (conj (lc_set_rlist_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)
  ((conj (lc_set_rt_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)
  (lc_set_rtyp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)))).

Scheme lc_set_rlist_rec' := Induction for lc_set_rlist Sort Set
  with lc_set_rt_rec' := Induction for lc_set_rt Sort Set
  with lc_set_rtyp_rec' := Induction for lc_set_rtyp Sort Set.

Definition lc_set_rlist_lc_set_rt_lc_set_rtyp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  (pair ((pair (lc_set_rlist_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)
  (lc_set_rt_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)))
  (lc_set_rtyp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)).

Inductive lc_set_rexp : rexp -> Set :=
  | lc_set_re_Var_f : forall x1,
    lc_set_rexp (re_Var_f x1)
  | lc_set_re_Abs : forall rt1 re1,
    lc_set_rt rt1 ->
    (forall x1 : expvar, lc_set_rexp (open_rexp_wrt_rexp re1 (re_Var_f x1))) ->
    lc_set_rexp (re_Abs rt1 re1)
  | lc_set_re_Lit : forall x1,
    lc_set_rexp (re_Lit x1)
  | lc_set_re_App : forall re1 re2,
    lc_set_rexp re1 ->
    lc_set_rexp re2 ->
    lc_set_rexp (re_App re1 re2)
  | lc_set_re_Empty :
    lc_set_rexp (re_Empty)
  | lc_set_re_SingleField : forall l1 re1,
    lc_set_rexp re1 ->
    lc_set_rexp (re_SingleField l1 re1)
  | lc_set_re_Res : forall re1 l1,
    lc_set_rexp re1 ->
    lc_set_rexp (re_Res re1 l1)
  | lc_set_re_Merge : forall re1 re2,
    lc_set_rexp re1 ->
    lc_set_rexp re2 ->
    lc_set_rexp (re_Merge re1 re2)
  | lc_set_re_Selection : forall re1 l1,
    lc_set_rexp re1 ->
    lc_set_rexp (re_Selection re1 l1)
  | lc_set_re_ConTyAbs : forall R1 re1,
    lc_set_rlist R1 ->
    (forall a1 : typvar, lc_set_rexp (open_rexp_wrt_rtyp re1 (r_TyVar_f a1))) ->
    lc_set_rexp (re_ConTyAbs R1 re1)
  | lc_set_re_ConTyApp : forall re1 r1,
    lc_set_rexp re1 ->
    lc_set_rtyp r1 ->
    lc_set_rexp (re_ConTyApp re1 r1).

Scheme lc_rexp_ind' := Induction for lc_rexp Sort Prop.

Definition lc_rexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  lc_rexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Scheme lc_set_rexp_ind' := Induction for lc_set_rexp Sort Prop.

Definition lc_set_rexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  lc_set_rexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Scheme lc_set_rexp_rec' := Induction for lc_set_rexp Sort Set.

Definition lc_set_rexp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  lc_set_rexp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Definition body_rlist_wrt_rtyp R1 := forall a1, lc_rlist (open_rlist_wrt_rtyp R1 (r_TyVar_f a1)).

Definition body_rt_wrt_rtyp u1 := forall a1, lc_rt (open_rt_wrt_rtyp u1 (r_TyVar_f a1)).

Definition body_rtyp_wrt_rtyp r1 := forall a1, lc_rtyp (open_rtyp_wrt_rtyp r1 (r_TyVar_f a1)).

Definition body_rexp_wrt_rtyp re1 := forall a1, lc_rexp (open_rexp_wrt_rtyp re1 (r_TyVar_f a1)).

Definition body_rexp_wrt_rexp re1 := forall x1, lc_rexp (open_rexp_wrt_rexp re1 (re_Var_f x1)).
