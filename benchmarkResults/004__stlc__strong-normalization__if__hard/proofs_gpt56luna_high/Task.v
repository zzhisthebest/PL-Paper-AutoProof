(** STLC call-by-value strong-normalization benchmark task. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Classical.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.

Module STLCCBVNormalizationTask.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
      R x y ->
      multi R y z ->
      multi R x z.

(** Language syntax, using locally nameless binders. *)

Definition atom := nat.

Inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tm_bvar : nat -> tm
  | tm_fvar : atom -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.

Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.

Notation "<{{ x }}>" := x (x custom stlc_ty).
Notation "x" := x
  (in custom stlc_ty at level 0, x constr at level 0) : stlc_scope.
Notation "'Bool'" := Ty_Bool
  (in custom stlc_ty at level 0) : stlc_scope.
Notation "S -> T" := (Ty_Arrow S T)
  (in custom stlc_ty at level 99, right associativity) : stlc_scope.
Notation "$( t )" := t
  (in custom stlc_ty at level 0, t constr) : stlc_scope.
Notation "( T )" := T
  (in custom stlc_ty at level 0, T custom stlc_ty) : stlc_scope.

Notation "<{ e }>" := e
  (e custom stlc_tm at level 200) : stlc_scope.
Notation "$( x )" := x
  (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
Notation "x" := x
  (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "'bvar' n" := (tm_bvar n)
  (in custom stlc_tm at level 0, n constr at level 0) : stlc_scope.
Notation "'fvar' x" := (tm_fvar x)
  (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "'true'" := tm_true
  (in custom stlc_tm at level 0) : stlc_scope.
Notation "'false'" := tm_false
  (in custom stlc_tm at level 0) : stlc_scope.
Notation "( x )" := x
  (in custom stlc_tm at level 0, x custom stlc_tm) : stlc_scope.
Notation "x y" := (tm_app x y)
  (in custom stlc_tm at level 10, left associativity) : stlc_scope.
Notation "'lambda' ':' T ',' t" := (tm_abs T t)
  (in custom stlc_tm at level 200,
   T custom stlc_ty,
   t custom stlc_tm at level 200,
   left associativity) : stlc_scope.
Notation "'if' t1 'then' t2 'else' t3" :=
  (tm_if t1 t2 t3)
  (in custom stlc_tm at level 200,
   t1 custom stlc_tm,
   t2 custom stlc_tm,
   t3 custom stlc_tm at level 200,
   left associativity) : stlc_scope.

(** Opening and local closure. *)

Fixpoint open_rec (k : nat) (u : tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => if Nat.eqb k i then u else tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_app t1 t2 => tm_app (open_rec k u t1) (open_rec k u t2)
  | tm_abs T t1 => tm_abs T (open_rec (S k) u t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 =>
      tm_if (open_rec k u t1) (open_rec k u t2) (open_rec k u t3)
  end.

Definition open (t u : tm) : tm := open_rec 0 u t.

Inductive lc_at : nat -> tm -> Prop :=
  | lc_bvar : forall k i,
      i < k ->
      lc_at k (tm_bvar i)
  | lc_fvar : forall k x,
      lc_at k (tm_fvar x)
  | lc_app : forall k t1 t2,
      lc_at k t1 ->
      lc_at k t2 ->
      lc_at k (tm_app t1 t2)
  | lc_abs : forall k T t1,
      lc_at (S k) t1 ->
      lc_at k (tm_abs T t1)
  | lc_true : forall k,
      lc_at k tm_true
  | lc_false : forall k,
      lc_at k tm_false
  | lc_if : forall k t1 t2 t3,
      lc_at k t1 ->
      lc_at k t2 ->
      lc_at k t3 ->
      lc_at k (tm_if t1 t2 t3).

Definition locally_closed (t : tm) : Prop := lc_at 0 t.

(** Call-by-value operational semantics. *)

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed (tm_abs T t) ->
      value (tm_abs T t)
  | v_true :
      value tm_true
  | v_false :
      value tm_false.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall T t v,
      locally_closed (tm_abs T t) ->
      value v ->
      tm_app (tm_abs T t) v --> open t v
  | ST_App1 : forall t1 t1' t2,
      t1 --> t1' ->
      locally_closed t2 ->
      tm_app t1 t2 --> tm_app t1' t2
  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      tm_app v1 t2 --> tm_app v1 t2'
  | ST_IfTrue : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_if tm_true t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_if tm_false t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      locally_closed t2 ->
      locally_closed t3 ->
      tm_if t1 t2 t3 --> tm_if t1' t2 t3
where "t '-->' t'" := (step t t').

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

(** Typing rules. *)

Definition context := atom -> option ty.

Definition empty : context := fun _ => None.

Definition update (Gamma : context) (x : atom) (T : ty) : context :=
  fun y => if Nat.eqb x y then Some T else Gamma y.

Notation "x '|->' v ';' m" := (update m x v)
  (in custom stlc_tm at level 0,
   x constr at level 0,
   v custom stlc_ty,
   right associativity) : stlc_scope.
Notation "x '|->' v" := (update empty x v)
  (in custom stlc_tm at level 0,
   x constr at level 0,
   v custom stlc_ty) : stlc_scope.
Notation "'empty'" := empty
  (in custom stlc_tm) : stlc_scope.

Reserved Notation "<{ Gamma '|--' t '\in' T }>"
  (at level 0,
   Gamma custom stlc_tm at level 200,
   t custom stlc_tm,
   T custom stlc_ty).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      <{ Gamma |-- fvar x \in T }>
  | T_Abs : forall (L : list atom) Gamma T1 T2 t1,
      (forall x, ~ In x L ->
        <{ x |-> T1 ; Gamma |-- $(open t1 (tm_fvar x)) \in T2 }>) ->
      <{ Gamma |-- lambda : T1, $(t1) \in T1 -> T2 }>
  | T_App : forall Gamma t1 t2 T1 T2,
      <{ Gamma |-- $(t1) \in T1 -> T2 }> ->
      <{ Gamma |-- $(t2) \in T1 }> ->
      <{ Gamma |-- $(tm_app t1 t2) \in T2 }>
  | T_True : forall Gamma,
      <{ Gamma |-- true \in Bool }>
  | T_False : forall Gamma,
      <{ Gamma |-- false \in Bool }>
  | T_If : forall Gamma t1 t2 t3 T,
      <{ Gamma |-- $(t1) \in Bool }> ->
      <{ Gamma |-- $(t2) \in T }> ->
      <{ Gamma |-- $(t3) \in T }> ->
      <{ Gamma |-- $(tm_if t1 t2 t3) \in T }>
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

(** Target theorem: strong normalization for the supplied CBV relation. *)

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

(* The relation below is the usual (unary) reducibility relation.  The
   local-closure component is useful here because the operational rules
   deliberately require it on evaluation arguments. *)

  Fixpoint fv (t : tm) : list atom :=
    match t with
    | tm_bvar _ => nil
    | tm_fvar x => x :: nil
    | tm_app t1 t2 => fv t1 ++ fv t2
    | tm_abs _ t1 => fv t1
    | tm_true => nil
    | tm_false => nil
    | tm_if t1 t2 t3 => fv t1 ++ fv t2 ++ fv t3
    end.

  Fixpoint subst (rho : atom -> tm) (t : tm) : tm :=
    match t with
    | tm_bvar i => tm_bvar i
    | tm_fvar x => rho x
    | tm_app t1 t2 => tm_app (subst rho t1) (subst rho t2)
    | tm_abs T t1 => tm_abs T (subst rho t1)
    | tm_true => tm_true
    | tm_false => tm_false
    | tm_if t1 t2 t3 =>
        tm_if (subst rho t1) (subst rho t2) (subst rho t3)
    end.

  Lemma lc_weaken : forall k t, lc_at k t -> forall j, k <= j -> lc_at j t.
  Proof.
    intros k t H; induction H; intros j Hj.
    - apply lc_bvar; lia.
    - apply lc_fvar.
    - apply lc_app; [apply IHlc_at1; assumption | apply IHlc_at2; assumption].
    - apply lc_abs. apply IHlc_at; lia.
    - apply lc_true.
    - apply lc_false.
    - apply lc_if; [apply IHlc_at1; assumption | apply IHlc_at2; assumption |
                    apply IHlc_at3; assumption].
  Qed.

  Lemma lc_open_rec : forall k t u,
      lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
  Proof.
    intros k t u; revert k u;
    induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| | |t1 IH1 t2 IH2 t3 IH3];
      intros k u Ht Hu; simpl.
    - inversion Ht; subst. destruct (Nat.eqb k i) eqn:E.
      + apply Nat.eqb_eq in E; subst; assumption.
      + apply Nat.eqb_neq in E; constructor; lia.
    - apply lc_fvar.
    - inversion Ht; subst. apply lc_app; [apply IH1 with (u := u); assumption | apply IH2 with (u := u); assumption].
    - inversion Ht; subst. apply lc_abs.
      apply IH with (k := S k) (u := u); [assumption | eapply lc_weaken; [exact Hu | lia]].
    - apply lc_true.
    - apply lc_false.
    - inversion Ht; subst. apply lc_if; [apply IH1 with (u := u); assumption |
                    apply IH2 with (u := u); assumption |
                    apply IH3 with (u := u); assumption].
  Qed.

  Lemma lc_open_rec_inv : forall k t u,
      lc_at k (open_rec k u t) -> lc_at (S k) t.
  Proof.
    intros k t u; revert k u;
    induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| | |t1 IH1 t2 IH2 t3 IH3];
      intros k u H; simpl.
    - destruct (Nat.eqb k i) eqn:E.
      + apply Nat.eqb_eq in E; subst; constructor; lia.
      + change (lc_at k (if Nat.eqb k i then u else tm_bvar i)) in H.
        rewrite E in H; inversion H; subst; constructor; lia.
    - apply lc_fvar.
    - inversion H; subst. apply lc_app; [apply IH1 with (u := u); assumption | apply IH2 with (u := u); assumption].
    - inversion H; subst. apply lc_abs. apply IH with (k := S k) (u := u); assumption.
    - apply lc_true.
    - apply lc_false.
    - inversion H; subst. apply lc_if; [apply IH1 with (u := u); assumption |
                    apply IH2 with (u := u); assumption |
                    apply IH3 with (u := u); assumption].
  Qed.

  Fixpoint max_list (l : list nat) : nat :=
    match l with
    | nil => 0
    | x :: l' => Nat.max x (max_list l')
    end.

  Lemma in_max_list : forall x l, In x l -> x <= max_list l.
  Proof.
    induction l as [|a l IH].
    - simpl; intros H; contradiction.
    - simpl; intros H; destruct H as [->|H].
      + apply Nat.le_max_l.
      + eapply Nat.le_trans; [apply IH; eassumption | apply Nat.le_max_r].
  Qed.

  Definition fresh (l : list atom) := S (max_list l).

  Lemma fresh_not_in : forall x l, x = fresh l -> ~ In x l.
  Proof.
    intros x l -> H; pose proof (in_max_list _ _ H); unfold fresh in *; lia.
  Qed.

  Lemma typing_lc : forall Gamma t T, <{ Gamma |-- t \in T }> -> locally_closed t.
  Proof.
    intros Gamma t T H; induction H as
      [ Gamma x T Hx
      | L Gamma T1 T2 t1 Hbody IH
      | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
      | Gamma
      | Gamma
      | Gamma t1 t2 t3 T H1 IH1 H2 IH2 H3 IH3 ].
    - constructor.
    - unfold locally_closed.
      assert (Hex : exists x, ~ In x (L ++ fv t1)).
      { exists (fresh (L ++ fv t1)). apply fresh_not_in. reflexivity. }
      destruct Hex as [x Hx].
      assert (HxL : ~ In x L) by (intro Hin; apply Hx; apply in_or_app; left; assumption).
      pose proof (Hbody x HxL) as Hb.
      pose proof (IH x HxL) as Hblc.
      unfold locally_closed in Hblc.
      apply lc_abs. eapply lc_open_rec_inv; eassumption.
    - unfold locally_closed in *; constructor; assumption.
    - constructor.
    - constructor.
    - unfold locally_closed in *; constructor; assumption.
  Qed.

  Lemma lc_subst : forall k rho t,
      lc_at k t -> (forall x, locally_closed (rho x)) -> lc_at k (subst rho t).
  Proof.
    intros k rho t; revert k rho;
    induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| | |t1 IH1 t2 IH2 t3 IH3];
      intros k rho Ht Hr; simpl.
    - inversion Ht; subst. apply lc_bvar; assumption.
    - apply lc_weaken with (k := 0); [apply Hr | lia].
    - inversion Ht; subst. apply lc_app; [apply IH1 with (rho := rho); assumption | apply IH2 with (rho := rho); assumption].
    - inversion Ht; subst. apply lc_abs.
      apply IH with (k := S k) (rho := rho).
      + assumption.
      + intro x; apply lc_weaken with (k := 0); [apply Hr | lia].
    - apply lc_true.
    - apply lc_false.
    - inversion Ht; subst. apply lc_if; [apply IH1 with (rho := rho); assumption |
                    apply IH2 with (rho := rho); assumption |
                    apply IH3 with (rho := rho); assumption].
  Qed.

  Lemma subst_id : forall t, subst (fun x => tm_fvar x) t = t.
  Proof.
    induction t; simpl; try rewrite IHt; try rewrite IHt1; try rewrite IHt2;
      try rewrite IHt3; reflexivity.
  Qed.

  Lemma open_rec_lc_identity : forall k t u,
      lc_at k t -> open_rec k u t = t.
  Proof.
    intros k t u; revert k u;
    induction t as [i|x|t1 IH1 t2 IH2|T t1 IH| | |t1 IH1 t2 IH2 t3 IH3];
      intros k u H; simpl.
    - inversion H; subst. destruct (Nat.eqb k i) eqn:E.
      + apply Nat.eqb_eq in E; lia.
      + reflexivity.
    - reflexivity.
    - inversion H; subst. f_equal; [apply IH1; assumption | apply IH2; assumption].
    - inversion H; subst. f_equal. apply IH; assumption.
    - reflexivity.
    - reflexivity.
    - inversion H; subst. f_equal; [apply IH1; assumption | apply IH2; assumption | apply IH3; assumption].
  Qed.

  Lemma subst_open_rec_fresh : forall rho x u t k,
      (forall y, locally_closed (rho y)) ->
      locally_closed u ->
      ~ In x (fv t) ->
      subst (fun y => if Nat.eqb x y then u else rho y)
        (open_rec k (tm_fvar x) t) = open_rec k u (subst rho t).
  Proof.
    intros rho x u t; induction t as [i|y|t1 IH1 t2 IH2|T t1 IH| | |t1 IH1 t2 IH2 t3 IH3];
      intros k Hlc Hu_lc Hfresh; simpl; try reflexivity.
    - destruct (Nat.eqb k i) eqn:E.
      + apply Nat.eqb_eq in E; subst; simpl; rewrite Nat.eqb_refl; reflexivity.
      + apply Nat.eqb_neq in E; simpl; reflexivity.
    - destruct (Nat.eqb x y) eqn:E.
      + apply Nat.eqb_eq in E; subst; exfalso; apply Hfresh; simpl; auto.
      + apply Nat.eqb_neq in E; simpl; symmetry;
        eapply open_rec_lc_identity; apply lc_weaken with (k := 0); [apply Hlc | lia].
    - f_equal.
      + apply IH1; [exact Hlc | exact Hu_lc | intro H; apply Hfresh; simpl; apply in_or_app; left; assumption].
      + apply IH2; [exact Hlc | exact Hu_lc | intro H; apply Hfresh; simpl; apply in_or_app; right; assumption].
    - f_equal. apply IH with (k := S k); [exact Hlc | exact Hu_lc | exact Hfresh].
    - f_equal.
      + apply IH1; [exact Hlc | exact Hu_lc | intro H; apply Hfresh; simpl; apply in_or_app; left; assumption].
      + apply IH2; [exact Hlc | exact Hu_lc | intro H; apply Hfresh; simpl; apply in_or_app; right; apply in_or_app; left; assumption].
      + apply IH3; [exact Hlc | exact Hu_lc | intro H; apply Hfresh; simpl; apply in_or_app; right; apply in_or_app; right; assumption].
  Qed.

  Lemma value_no_step : forall v v', value v -> ~ step v v'.
  Proof.
    intros v v' Hv Hs; destruct Hv; inversion Hs.
  Qed.

  Lemma step_not_value : forall t t', step t t' -> ~ value t.
  Proof.
    intros t t' Hs Hv; destruct Hv; inversion Hs.
  Qed.

  Lemma sn_step : forall t t', strongly_normalizing t -> step t t' -> strongly_normalizing t'.
  Proof.
    intros t t' H Hstep; inversion H; subst; eapply H0; exact Hstep.
  Qed.

  Lemma lc_step : forall t t', locally_closed t -> step t t' -> locally_closed t'.
  Proof.
    intros t t' Hlc Hstep; induction Hstep as
      [ A b v Habs Hv
      | b b' a Hb IH Ha
      | v a a' Hv Ha IH
      | a b H1 H2
      | a b H1 H2
      | a a' b c Ha IH Hb Hc ].
    - apply lc_open_rec.
      + inversion Habs; assumption.
      + destruct Hv as [X Y Hvlc | |].
        * inversion Hvlc; apply lc_abs; assumption.
        * apply lc_true.
        * apply lc_false.
    - unfold locally_closed in Hlc; inversion Hlc; apply lc_app.
      + apply IH; assumption.
      + assumption.
    - unfold locally_closed in Hlc; inversion Hlc; apply lc_app.
      + assumption.
      + apply IH; assumption.
    - apply H1.
    - apply H2.
    - unfold locally_closed in Hlc; inversion Hlc; apply lc_if.
      + apply IH; assumption.
      + assumption.
      + assumption.
  Qed.

  Lemma sn_beta_expand : forall A t v,
      locally_closed (tm_abs A t) -> value v ->
      strongly_normalizing (open t v) ->
      strongly_normalizing (tm_app (tm_abs A t) v).
  Proof.
    intros A t v Hlc Hv Hsn; constructor; intros q Hq; inversion Hq; subst.
    - assumption.
    - exfalso; apply (value_no_step (tm_abs A t) t1' (v_abs A t Hlc)); exact H1.
    - exfalso; apply (value_no_step v t2' Hv); exact H3.
  Qed.

  Fixpoint reducible (T : ty) (t : tm) : Prop :=
    locally_closed t /\ strongly_normalizing t /\
    match T with
    | Ty_Bool => True
    | Ty_Arrow A B => forall u, reducible A u -> reducible B (tm_app t u)
    end.

  Lemma reducible_lc : forall T t, reducible T t -> locally_closed t.
  Proof. intros T t H; destruct T; simpl in H; destruct H as [H _]; exact H. Qed.

  Lemma reducible_sn : forall T t, reducible T t -> strongly_normalizing t.
  Proof. intros T t H; destruct T; simpl in H; destruct H as [_ [H _]]; exact H. Qed.

  Lemma reducible_reduct : forall T t t', reducible T t -> step t t' -> reducible T t'.
  Proof.
    intros T; destruct T as [| A B].
    - intros t t' H R.
      change (locally_closed t /\ strongly_normalizing t /\ True) in H.
      destruct H as [Hlc [Hsn _]].
      apply conj.
      + apply lc_step with (t := t) (t' := t'); [exact Hlc | exact R].
      + apply conj.
        * apply sn_step with (t := t) (t' := t'); [exact Hsn | exact R].
        * exact I.
    - revert A; induction B as [|C IHC D IHD]; intros A t t' H R.
      + change (locally_closed t /\ strongly_normalizing t /\
                  (forall u, reducible A u -> reducible Ty_Bool (tm_app t u))) in H.
        destruct H as [Hlc [Hsn Hfun]]. apply conj.
        * apply lc_step with (t := t) (t' := t'); [exact Hlc | exact R].
        * apply conj.
          -- apply sn_step with (t := t) (t' := t'); [exact Hsn | exact R].
          -- intros u Hu.
            pose proof (Hfun u Hu) as Hbu.
            change (locally_closed (tm_app t u) /\ strongly_normalizing (tm_app t u) /\ True) in Hbu.
            destruct Hbu as [Hulc [Husn _]].
            apply conj.
            ++ apply lc_step with (t := tm_app t u) (t' := tm_app t' u); [exact Hulc |].
               apply ST_App1; [exact R | apply reducible_lc in Hu; exact Hu].
            ++ apply conj.
               ** apply sn_step with (t := tm_app t u) (t' := tm_app t' u); [exact Husn |].
                  apply ST_App1; [exact R | apply reducible_lc in Hu; exact Hu].
               ** exact I.
      + change (locally_closed t /\ strongly_normalizing t /\
                  (forall u, reducible A u -> reducible (Ty_Arrow C D) (tm_app t u))) in H.
        destruct H as [Hlc [Hsn Hfun]]. apply conj.
        * apply lc_step with (t := t) (t' := t'); [exact Hlc | exact R].
        * apply conj.
          -- apply sn_step with (t := t) (t' := t'); [exact Hsn | exact R].
          -- intros u Hu.
            apply IHD with (t := tm_app t u) (t' := tm_app t' u).
            (* The function component is inherited from the old application. *)
            apply Hfun; exact Hu.
            apply ST_App1; [exact R | apply reducible_lc in Hu; exact Hu].
  Qed.

  (* The following two lemmas are the neutral-term part of the relation.
     The induction on the result type accounts for stuck applications at
     every function arity; the inner induction handles a reducing argument. *)
  Lemma neutral_apply : forall T A h,
      ~ value h -> locally_closed h ->
      (forall h', step h h' -> reducible (Ty_Arrow A T) h') ->
      forall u, reducible A u -> reducible T (tm_app h u).
  Proof.
    induction T as [|C IHC D IHD]; intros A h Hnv Hhlc Hhall u Hu.
    - pose proof (reducible_lc A u Hu) as Hulc.
      pose proof (reducible_sn A u Hu) as Husn.
      induction Husn as [u Hred IHsn].
      apply conj.
      + constructor; assumption.
      + apply conj.
        * constructor; intros q Hq; inversion Hq; subst.
          ** exfalso; apply Hnv; apply v_abs; exact H1.
          ** apply reducible_sn with (T := Ty_Bool).
             pose proof (Hhall _ H1) as Hf.
             change (locally_closed t1' /\ strongly_normalizing t1' /\
                       (forall z, reducible A z -> reducible Ty_Bool (tm_app t1' z))) in Hf.
             destruct Hf as [_ [_ Hfun]]. apply Hfun; exact Hu.
          ** apply reducible_sn with (T := Ty_Bool).
             apply IHsn.
             *** exact H3.
             *** apply reducible_reduct with (T := A) (t := u) (t' := t2').
                 exact Hu. exact H3.
             *** apply lc_step with (t := u) (t' := t2'); [exact Hulc | exact H3].
        * trivial.
    - pose proof (reducible_lc A u Hu) as Hulc.
      pose proof (reducible_sn A u Hu) as Husn.
      induction Husn as [u Hred IHsn].
      apply conj.
      + constructor; assumption.
      + apply conj.
        * constructor; intros q Hq; inversion Hq; subst.
        ** exfalso; apply Hnv; apply v_abs; exact H1.
        ** apply reducible_sn with (T := Ty_Arrow C D).
          pose proof (Hhall _ H1) as Hf.
          change (locally_closed t1' /\ strongly_normalizing t1' /\
                    (forall z, reducible A z -> reducible (Ty_Arrow C D) (tm_app t1' z))) in Hf.
          destruct Hf as [_ [_ Hfun]]. apply Hfun; exact Hu.
        ** apply IHsn.
          *** exact H3.
          *** apply reducible_reduct with (T := A) (t := u) (t' := t2').
             exact Hu. exact H3.
          *** apply lc_step with (t := u) (t' := t2'); [exact Hulc | exact H3].
        * intros v Hv.
          apply IHD with (A := C) (h := tm_app h u).
        ** inversion 1.
        ** constructor; assumption.
        ** intros q Hq; inversion Hq; subst.
          *** exfalso; apply Hnv; apply v_abs; exact H1.
          *** pose proof (Hhall _ H1) as Hf.
              change (locally_closed t1' /\ strongly_normalizing t1' /\
                        (forall z, reducible A z -> reducible (Ty_Arrow C D) (tm_app t1' z))) in Hf.
              destruct Hf as [_ [_ Hfun]]. apply Hfun; exact Hu.
          *** apply IHsn.
              **** exact H3.
              **** apply reducible_reduct with (T := A) (t := u) (t' := t2').
                exact Hu. exact H3.
              **** apply lc_step with (t := u) (t' := t2'); [exact Hulc | exact H3].
        ** exact Hv.
  Qed.

  Lemma neutral_term : forall T t,
      ~ value t -> locally_closed t ->
      (forall t', step t t' -> reducible T t') -> reducible T t.
  Proof.
    induction T as [|A IHA B IHB]; intros t Hnv Hlc Hall.
    - change (locally_closed t /\ strongly_normalizing t /\ True).
      apply conj; [exact Hlc | apply conj].
      + constructor; intros t' Hstep; apply reducible_sn with (T := Ty_Bool); apply Hall; exact Hstep.
      + exact I.
    - change (locally_closed t /\ strongly_normalizing t /\
                (forall u, reducible A u -> reducible B (tm_app t u))).
      apply conj; [exact Hlc | apply conj].
      + constructor; intros t' Hstep; apply reducible_sn with (T := Ty_Arrow A B); apply Hall; exact Hstep.
      + intros u Hu; apply neutral_apply with (A := A) (h := t); assumption.
  Qed.

  Lemma reducible_abs_app : forall A B T t,
      locally_closed (tm_abs A t) ->
      (forall u, reducible T u -> reducible B (open t u)) ->
      forall u, reducible T u -> reducible B (tm_app (tm_abs A t) u).
  Proof.
    intros A B T t Hlc Hbody u Hu.
    pose proof (reducible_lc T u Hu) as Hulc.
    pose proof (reducible_sn T u Hu) as Husn.
    induction Husn as [u Hred IH].
    destruct (classic (value u)) as [Hv|Hnv].
    - apply neutral_term.
      + inversion 1.
      + constructor; assumption.
      + intros q Hq; inversion Hq; subst.
        * apply Hbody; exact Hu.
        * exfalso; apply (value_no_step (tm_abs A t) t1' (v_abs A t Hlc)); exact H1.
        * exfalso; apply (value_no_step u t2' Hv); exact H3.
    - apply neutral_term.
      + inversion 1.
      + constructor; assumption.
      + intros q Hq; inversion Hq; subst.
        * exfalso; apply Hnv; exact H4.
        * exfalso; apply (value_no_step (tm_abs A t) t1' (v_abs A t Hlc)); exact H1.
        * apply IH.
          exact H3.
          apply reducible_reduct with (T := T) (t := u) (t' := t2').
          exact Hu. exact H3.
          apply lc_step with (t := u) (t' := t2'); [exact Hulc | exact H3].
  Qed.

  Lemma reducible_if : forall T c t1 t2,
      reducible Ty_Bool c -> reducible T t1 -> reducible T t2 ->
      reducible T (tm_if c t1 t2).
  Proof.
    intros T c t1 t2 Hc H1 H2.
    destruct Hc as [Hclc [Hcsn HcR]].
    induction Hcsn as [c Hred IH].
    destruct (classic (value c)) as [Hv|Hnv].
    - destruct Hv as [| |].
      + apply neutral_term.
        * inversion 1.
        * constructor; assumption.
        * intros q Hq; inversion Hq; subst.
          ** exact H1.
          ** exfalso; eapply value_no_step; [apply v_true | exact H].
      + apply neutral_term.
        * inversion 1.
        * constructor; assumption.
        * intros q Hq; inversion Hq; subst.
          ** exact H2.
          ** exfalso; eapply value_no_step; [apply v_false | exact H].
    - apply neutral_term.
      + inversion 1.
      + apply lc_if; assumption.
      + intros q Hq; inversion Hq; subst.
        * exfalso; apply Hnv; exact H1.
        * exfalso; apply Hnv; exact H1.
        * apply IH; [apply reducible_reduct with (T := Ty_Bool) (t := c) (t' := t1'); exact Hc; exact H | exact H1 | exact H2].
  Qed.

  Definition rho_ext (rho : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
    fun y => if Nat.eqb x y then u else rho y.

  Lemma fundamental : forall Gamma t T, <{ Gamma |-- t \in T }> ->
      forall rho, (forall x U, Gamma x = Some U -> reducible U (rho x)) ->
      reducible T (subst rho t).
  Proof.
    intros Gamma t T H; induction H as
      [ Gamma x T Hx
      | L Gamma T1 T2 t1 Hbody IH
      | Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
      | Gamma
      | Gamma
      | Gamma t1 t2 t3 T H1 IH1 H2 IH2 H3 IH3 ].
    - intros rho Henv. simpl. apply Henv; exact Hx.
    - intros rho Henv. simpl.
      assert (Habs : locally_closed (tm_abs T1 (subst rho t1))).
      { apply lc_subst with (k := 0) (t := tm_abs T1 t1).
        - apply typing_lc with (Gamma := Gamma) (t := tm_abs T1 t1) (T := Ty_Arrow T1 T2).
          apply T_Abs; exact Hbody.
        - intro x; apply reducible_lc with (T := match Gamma x with Some U => U | None => Ty_Bool end).
          destruct (Gamma x); simpl; try constructor.
          apply Henv; reflexivity. }
      repeat split.
      + exact Habs.
      + constructor; intros q Hq; inversion Hq.
      + intros u Hu.
        apply reducible_abs_app with (A := T1) (T := T1) (t := subst rho t1); [exact Habs |].
        intros v Hv.
        assert (Hfresh : exists x, ~ In x (L ++ fv t1)).
        { exists (fresh (L ++ fv t1)). apply fresh_not_in. reflexivity. }
        destruct Hfresh as [x Hx].
        assert (HxL : ~ In x L) by (intro Hin; apply Hx; apply in_or_app; left; exact Hin).
        pose proof (IH x HxL (rho_ext rho x v)) as Hb.
        apply Hb.
        intros y U Hy.
        unfold rho_ext, update in *.
        destruct (Nat.eqb x y) eqn:E.
        * apply Nat.eqb_eq in E; subst; inversion Hy; exact Hv.
        * apply Henv; exact Hy.
        * unfold open in *.
          eapply subst_open_rec_fresh; [intro z; apply reducible_lc with (T := match Gamma z with Some W => W | None => Ty_Bool end); destruct (Gamma z); simpl; try constructor; apply Henv; reflexivity | exact (reducible_lc _ _ Hu) | exact Hx].
    - intros rho Henv. simpl in *.
      apply IH1 in Henv.
      apply IH2 in Henv.
      apply Henv0.
    - intros rho Henv. simpl. repeat split; try constructor.
      + constructor; intros q Hq; inversion Hq.
    - intros rho Henv. simpl. repeat split; try constructor.
      + constructor; intros q Hq; inversion Hq.
    - intros rho Henv. simpl in *.
      apply reducible_if with (c := subst rho t1) (t1 := subst rho t2) (t2 := subst rho t3).
      + apply IH1; exact Henv.
      + apply IH2; exact Henv.
      + apply IH3; exact Henv.
  Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T H.
  pose proof (fundamental empty t T H (fun x => tm_fvar x)) as HR.
  - unfold empty in *; discriminate.
  - exact (reducible_sn _ _ HR).
Qed.

End STLCCBVNormalizationTask.
