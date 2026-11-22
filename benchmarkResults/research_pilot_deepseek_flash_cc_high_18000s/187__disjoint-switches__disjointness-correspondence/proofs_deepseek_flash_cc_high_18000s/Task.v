Require Import TLC.LibLN.

Require Import Program.Equality.

Require Import Coq.Lists.ListSet.

From Coq Require Export Lists.List.

Export ListNotations.

Require Import Coq.Strings.String.

Inductive typ : Set :=
 | t_top : typ
 | t_int : typ
 | t_bot : typ
 | t_arrow : typ -> typ -> typ
 | t_union : typ -> typ -> typ
 | t_unit : typ.

Inductive exp : Set :=
 | e_var_b  : nat -> exp
 | e_var_f  : var -> exp
 | e_lit    : nat -> exp
 | e_abs    : exp -> exp
 | e_app    : exp -> exp -> exp
 | e_typeof : exp -> typ -> exp -> typ -> exp -> exp
 | e_null   : exp.

Inductive bind : Set :=
 | bind_typ : typ -> bind.

Notation "x ~: T" := (x ~ T)
 (at level 23, left associativity) : env_scope.

Definition env := LibEnv.env typ.

Inductive okt : env -> Prop :=
| okt_empty :
     okt empty
| okt_typ : forall E x T,
     okt E-> x # E -> okt (E & x ~: T).

Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (e_var_b nat) => If (k = nat) then e_5 else (e_var_b nat)
  | (e_var_f x) => e_var_f x
  | (e_lit i5) => e_lit i5
  | (e_abs e) => e_abs (open_exp_wrt_exp_rec (S k) e_5 e)
  | (e_app e1 e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_typeof e A e1 B e2) => e_typeof (open_exp_wrt_exp_rec k e_5 e) A (open_exp_wrt_exp_rec (S k) e_5 e1) B (open_exp_wrt_exp_rec (S k) e_5 e2)
  | (e_null) => e_null
end.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

Notation "t 'open_ee_var' x" := (open_exp_wrt_exp t (e_var_f x)) (at level 67).

Inductive lc_exp : exp -> Prop :=
 | lc_e_var_f : forall (x:var),
     (lc_exp (e_var_f x))
 | lc_e_lit : forall i5,
     (lc_exp (e_lit i5))
 | lc_e_abs : forall (L:vars) (e:exp),
      ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_abs e))
 | lc_e_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_app e1 e2))
 | lc_e_typeof : forall (L:vars) (e:exp) (A:typ) (e1:exp) (B:typ) (e2:exp),
     (lc_exp e) ->
     ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e1 (e_var_f x) )  ) ->
     ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e2 (e_var_f x) )  ) ->
     (lc_exp (e_typeof e A e1 B e2))
 | lec_e_null :
     lc_exp e_null.

Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => \{}
  | (e_var_f x) => \{x}
  | (e_lit i5) => \{}
  | (e_abs e) => (fv_exp e)
  | (e_app e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_typeof e A e1 B e2) => (fv_exp e) \u (fv_exp e1) \u (fv_exp e2)
  | (e_null) => \{}
end.

Fixpoint subst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (If x = x5 then e_5 else (e_var_f x))
  | (e_lit i5) => e_lit i5
  | (e_abs e) => e_abs (subst_exp e_5 x5 e)
  | (e_app e1 e2) => e_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_typeof e A e1 B e2) => e_typeof (subst_exp e_5 x5 e) A (subst_exp e_5 x5 e1) B (subst_exp e_5 x5 e2)
  | (e_null) => e_null
end.

Reserved Notation "A <: B" (at level 80).

Inductive subtyping : typ -> typ -> Prop :=
 | s_top : forall A,
   A <: t_top
 | s_int :
     t_int <: t_int
 | s_unit :
    t_unit <: t_unit
 | s_arrow : forall (A1 A2 B1 B2:typ),
     B1 <: A1 ->
     A2 <: B2 ->
     (t_arrow A1 A2) <: (t_arrow B1 B2)
 | s_ora : forall (A1 A2 A:typ),
     A1 <: A ->
     A2 <: A ->
     (t_union A1 A2) <: A
 | s_orb : forall (A A1 A2:typ),
     A <: A1 ->
     A <: (t_union A1 A2)
 | s_orc : forall (A A1 A2:typ),
     A <: A2 ->
     A <: (t_union A1 A2)
 | s_bot : forall A,
     t_bot <: A
where "A <: B" := (subtyping A B) : env_scope.

Inductive bottomlike : typ -> Prop :=
 | bl_bot :
     bottomlike t_bot
 | bl_or : forall (A B:typ),
     bottomlike A ->
     bottomlike B ->
     bottomlike (t_union A B).

Definition DisjSpec A B := forall C, C <: A /\ C <: B -> bottomlike C.

Notation "A *s B" := (DisjSpec A B) (at level 80).

Reserved Notation "A *a B" (at level 80).

Inductive disjointness : typ -> typ -> Prop :=
 | ad_btmr : forall (A:typ),
      A *a t_bot
 | ad_btml : forall (A:typ),
     t_bot *a A
 | ad_intl : forall (A B:typ),
     t_int *a (t_arrow A B)
 | ad_intr : forall (A B:typ),
     (t_arrow A B) *a t_int
 | ad_unit_intl :
      t_unit *a t_int
 | ad_unit_intr :
      t_int *a t_unit
 | ad_unit_arrowl: forall A B,
      t_unit *a (t_arrow A B)
 | ad_unit_arrowr: forall A B,
      (t_arrow A B) *a t_unit
 | ad_orl : forall (A B C:typ),
     A *a C ->
     B *a C ->
     (t_union A B) *a C
 | ad_orr : forall (C A B:typ),
     A *a C ->
     B *a C ->
     C *a (t_union A B)
where "A *a B" := (disjointness A B).

Require Import Program.Equality.

Require Import Lia.

Lemma sub_refl : forall A, A <: A.
Proof.
  induction A; simpl.
  - apply s_top.
  - apply s_int.
  - apply s_bot.
  - apply s_arrow; assumption.
  - apply s_ora.
    + apply s_orb. assumption.
    + apply s_orc. assumption.
  - apply s_unit.
Qed.

Lemma sub_incl_l : forall A1 A2 D, D <: A1 -> D <: t_union A1 A2.
Proof. intros; apply s_orb; assumption. Qed.
Lemma sub_incl_r : forall A1 A2 D, D <: A2 -> D <: t_union A1 A2.
Proof. intros; apply s_orc; assumption. Qed.

Lemma sub_union_l : forall A1 A2 X, t_union A1 A2 <: X -> A1 <: X /\ A2 <: X.
Proof.
  intros A1 A2 X H.
  remember (t_union A1 A2) as U eqn:EU in H.
  revert A1 A2 EU.
  induction H; intros a1 a2 EU.
  - split; apply s_top.
  - discriminate EU.
  - discriminate EU.
  - discriminate EU.
  - inversion EU; subst; auto.
  - destruct (IHsubtyping a1 a2 EU) as [L R]. split; apply sub_incl_l; assumption.
  - destruct (IHsubtyping a1 a2 EU) as [L R]. split; apply sub_incl_r; assumption.
  - discriminate EU.
Qed.

Lemma sub_bot_inv : forall A, A <: t_bot -> bottomlike A.
Proof.
  intros A H. remember t_bot as R eqn:ER in H. revert ER.
  induction H; intros ER.
  - discriminate ER.
  - discriminate ER.
  - discriminate ER.
  - discriminate ER.
  - apply bl_or; [apply IHsubtyping1 | apply IHsubtyping2]; exact ER.
  - discriminate ER.
  - discriminate ER.
  - apply bl_bot.
Qed.

Lemma bl_not_top : bottomlike t_top -> False.
Proof. intros H; inversion H. Qed.
Lemma bl_not_int : bottomlike t_int -> False.
Proof. intros H; inversion H. Qed.
Lemma bl_not_unit : bottomlike t_unit -> False.
Proof. intros H; inversion H. Qed.
Lemma bl_not_arrow : forall A B, bottomlike (t_arrow A B) -> False.
Proof. intros A B H; inversion H. Qed.

Lemma sub_int_arrow : forall D A B, D <: t_int -> D <: t_arrow A B -> bottomlike D.
Proof.
  intros D A B H1 H2. remember t_int as R eqn:ER in H1. revert ER.
  induction H1; intros ER; try discriminate ER.
  - inversion H2.
  - apply sub_union_l in H2. destruct H2 as [H2a H2b].
    apply bl_or; [apply IHsubtyping1 | apply IHsubtyping2]; assumption.
  - apply bl_bot.
Qed.

Lemma sub_int_unit : forall D, D <: t_int -> D <: t_unit -> bottomlike D.
Proof.
  intros D H1 H2. remember t_int as R eqn:ER in H1. revert ER.
  induction H1; intros ER; try discriminate ER.
  - inversion H2.
  - apply sub_union_l in H2. destruct H2 as [H2a H2b].
    apply bl_or; [apply IHsubtyping1 | apply IHsubtyping2]; assumption.
  - apply bl_bot.
Qed.

Lemma sub_unit_int : forall D, D <: t_unit -> D <: t_int -> bottomlike D.
Proof.
  intros D H1 H2. remember t_unit as R eqn:ER in H1. revert ER.
  induction H1; intros ER; try discriminate ER.
  - inversion H2.
  - apply sub_union_l in H2. destruct H2 as [H2a H2b].
    apply bl_or; [apply IHsubtyping1 | apply IHsubtyping2]; assumption.
  - apply bl_bot.
Qed.

Lemma sub_unit_arrow : forall D A B, D <: t_unit -> D <: t_arrow A B -> bottomlike D.
Proof.
  intros D A B H1 H2. remember t_unit as R eqn:ER in H1. revert ER.
  induction H1; intros ER; try discriminate ER.
  - inversion H2.
  - apply sub_union_l in H2. destruct H2 as [H2a H2b].
    apply bl_or; [apply IHsubtyping1 | apply IHsubtyping2]; assumption.
  - apply bl_bot.
Qed.

Lemma sub_arrow_int : forall D A B, D <: t_arrow A B -> D <: t_int -> bottomlike D.
Proof.
  intros D A B H1 H2. remember (t_arrow A B) as R eqn:ER in H1. revert ER.
  induction H1; intros ER; try discriminate ER.
  - inversion H2.
  - apply sub_union_l in H2. destruct H2 as [H2a H2b].
    apply bl_or; [apply IHsubtyping1 | apply IHsubtyping2]; assumption.
  - apply bl_bot.
Qed.

Lemma sub_arrow_unit : forall D A B, D <: t_arrow A B -> D <: t_unit -> bottomlike D.
Proof.
  intros D A B H1 H2. remember (t_arrow A B) as R eqn:ER in H1. revert ER.
  induction H1; intros ER; try discriminate ER.
  - inversion H2.
  - apply sub_union_l in H2. destruct H2 as [H2a H2b].
    apply bl_or; [apply IHsubtyping1 | apply IHsubtyping2]; assumption.
  - apply bl_bot.
Qed.

Lemma bl_disj_l : forall A, bottomlike A -> forall B, A *a B.
Proof.
  intros A H. induction H; intros Z.
  - apply ad_btml.
  - apply ad_orl; eauto.
Qed.

Lemma bl_top_right : forall Z, bottomlike Z -> t_top *a Z.
Proof.
  intros Z H. induction H.
  - apply ad_btmr.
  - apply ad_orr; apply bl_disj_l; assumption.
Qed.

Lemma DisjSpec_l : forall A1 A2 B, (t_union A1 A2) *s B -> A1 *s B.
Proof.
  intros A1 A2 B H D [H1 H2]. apply H. split; [apply sub_incl_l |]; assumption.
Qed.
Lemma DisjSpec_r : forall A1 A2 B, (t_union A1 A2) *s B -> A2 *s B.
Proof.
  intros A1 A2 B H D [H1 H2]. apply H. split; [apply sub_incl_r |]; assumption.
Qed.
Lemma DisjSpec_rr : forall A B1 B2, A *s (t_union B1 B2) -> A *s B1.
Proof.
  intros A B1 B2 H D [H1 H2]. apply H. split; [assumption | apply sub_incl_l]; assumption.
Qed.
Lemma DisjSpec_rrr : forall A B1 B2, A *s (t_union B1 B2) -> A *s B2.
Proof.
  intros A B1 B2 H D [H1 H2]. apply H. split; [assumption | apply sub_incl_r]; assumption.
Qed.

Lemma DisjSpec_swap : forall A B, A *s B -> B *s A.
Proof. intros A B H D [H1 H2]. apply H. split; assumption. Qed.

Lemma disj_union_split_sem : forall A B X, A *s X -> B *s X ->
  forall D, D <: t_union A B -> D <: X -> bottomlike D.
Proof.
  intros A B X HS1 HS2 D HD HDC.
  remember (t_union A B) as U eqn:EU in HD.
  revert HS1 HS2 HDC. revert EU.
  induction HD; intros EU HS1 HS2 HDC; try discriminate EU.
  - apply sub_union_l in HDC. destruct HDC as [HDX1 HDX2].
    apply bl_or; [apply IHHD1 | apply IHHD2]; assumption.
  - injection EU as E1 E2. subst. apply HS1. split; assumption.
  - injection EU as E1 E2. subst. apply HS2. split; assumption.
  - apply bl_bot.
Qed.

Theorem Disj_soundness : forall A B, A *a B -> A *s B.
Proof.
  intros A B H. induction H.
  - intros D [HD1 HD2]. apply sub_bot_inv in HD2. exact HD2.
  - intros D [HD1 HD2]. apply sub_bot_inv in HD1. exact HD1.
  - intros D [HD1 HD2]. eapply sub_int_arrow; eauto.
  - intros D [HD1 HD2]. eapply sub_arrow_int; eauto.
  - intros D [HD1 HD2]. eapply sub_unit_int; eauto.
  - intros D [HD1 HD2]. eapply sub_int_unit; eauto.
  - intros D [HD1 HD2]. eapply sub_unit_arrow; eauto.
  - intros D [HD1 HD2]. eapply sub_arrow_unit; eauto.
  - intros D [HD1 HD2].
    apply (disj_union_split_sem A B C IHdisjointness1 IHdisjointness2 D HD1 HD2).
  - intros D [HD1 HD2].
    apply (disj_union_split_sem A B C IHdisjointness1 IHdisjointness2 D HD2 HD1).
Qed.

Fixpoint typ_size (A:typ) : nat :=
  match A with
  | t_top => 1
  | t_int => 1
  | t_bot => 1
  | t_arrow A1 A2 => S (typ_size A1 + typ_size A2)
  | t_union A1 A2 => S (typ_size A1 + typ_size A2)
  | t_unit => 1
  end.

Lemma typ_size_pos : forall A, 1 <= typ_size A.
Proof. intros A; destruct A; simpl; lia. Qed.

Lemma comp_aux : forall n A B, typ_size A + typ_size B <= n -> A *s B -> A *a B.
Proof.
  induction n as [| n IH]; intros A B Hn HS.
  - pose proof (typ_size_pos A). pose proof (typ_size_pos B). lia.
  - destruct A as [| | | A1 A2 | A1 A2 |].
    + (* top *) destruct B as [| | | B1 B2 | B1 B2 |].
      * exfalso. apply bl_not_top. apply HS. split; apply sub_refl.
      * exfalso. apply bl_not_int. apply HS. split; [apply s_top | apply sub_refl].
      * apply ad_btmr.
      * exfalso. apply (bl_not_arrow B1 B2). apply HS. split; [apply s_top | apply sub_refl].
      * apply bl_top_right. apply HS. split; [apply s_top | apply sub_refl].
      * exfalso. apply bl_not_unit. apply HS. split; [apply s_top | apply sub_refl].
    + (* int *) destruct B as [| | | B1 B2 | B1 B2 |].
      * exfalso. apply bl_not_int. apply HS. split; [apply sub_refl | apply s_top].
      * exfalso. apply bl_not_int. apply HS. split; apply sub_refl.
      * apply ad_btmr.
      * apply ad_intl.
      * apply ad_orr with (C := t_int) (A := B1) (B := B2).
        -- apply (IH B1 t_int); [simpl in *; lia | apply (DisjSpec_swap _ _ (DisjSpec_rr t_int B1 B2 HS))].
        -- apply (IH B2 t_int); [simpl in *; lia | apply (DisjSpec_swap _ _ (DisjSpec_rrr t_int B1 B2 HS))].
      * apply ad_unit_intr.
    + (* bot *) apply ad_btml.
    + (* arrow *) destruct B as [| | | B1 B2 | B1 B2 |].
      * exfalso. apply (bl_not_arrow A1 A2). apply HS. split; [apply sub_refl | apply s_top].
      * apply ad_intr.
      * apply ad_btmr.
      * exfalso. apply (bl_not_arrow t_top t_bot). apply HS.
        split.
        -- apply s_arrow; [apply s_top | apply s_bot].
        -- apply s_arrow; [apply s_top | apply s_bot].
      * apply ad_orr with (C := t_arrow A1 A2) (A := B1) (B := B2).
        -- apply (IH B1 (t_arrow A1 A2)); [simpl in *; lia | apply (DisjSpec_swap _ _ (DisjSpec_rr (t_arrow A1 A2) B1 B2 HS))].
        -- apply (IH B2 (t_arrow A1 A2)); [simpl in *; lia | apply (DisjSpec_swap _ _ (DisjSpec_rrr (t_arrow A1 A2) B1 B2 HS))].
      * apply ad_unit_arrowr.
    + (* union *) apply ad_orl.
      * apply (IH A1 B); [simpl in *; lia | apply (DisjSpec_l A1 A2 B HS)].
      * apply (IH A2 B); [simpl in *; lia | apply (DisjSpec_r A1 A2 B HS)].
    + (* unit *) destruct B as [| | | B1 B2 | B1 B2 |].
      * exfalso. apply bl_not_unit. apply HS. split; [apply sub_refl | apply s_top].
      * apply ad_unit_intl.
      * apply ad_btmr.
      * apply ad_unit_arrowl.
      * apply ad_orr with (C := t_unit) (A := B1) (B := B2).
        -- apply (IH B1 t_unit); [simpl in *; lia | apply (DisjSpec_swap _ _ (DisjSpec_rr t_unit B1 B2 HS))].
        -- apply (IH B2 t_unit); [simpl in *; lia | apply (DisjSpec_swap _ _ (DisjSpec_rrr t_unit B1 B2 HS))].
      * exfalso. apply bl_not_unit. apply HS. split; apply sub_refl.
Qed.

Theorem Disj_completeness : forall A B, A *s B -> A *a B.
Proof.
  intros A B HS. apply (comp_aux (typ_size A + typ_size B) A B); [lia | exact HS].
Qed.
