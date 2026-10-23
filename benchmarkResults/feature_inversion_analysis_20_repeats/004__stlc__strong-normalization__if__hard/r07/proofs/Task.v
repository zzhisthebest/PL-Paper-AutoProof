(** STLC call-by-value strong-normalization benchmark task. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.

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

(* ================================================================= *)
(* Added development: auxiliary definitions and lemmas.               *)
(* ================================================================= *)

(** ** Fresh atoms *)

Definition max_atom_list (L : list atom) : atom := fold_right max 0 L.

Lemma max_atom_list_ge : forall L x, In x L -> x <= max_atom_list L.
Proof.
  induction L as [| a L IH]; intros x Hin; simpl in *.
  - destruct Hin.
  - destruct Hin as [-> | Hin].
    + lia.
    + apply IH in Hin. lia.
Qed.

Lemma exists_fresh : forall L : list atom, exists x, ~ In x L.
Proof.
  intros L. exists (S (max_atom_list L)). intros Hin.
  apply max_atom_list_ge in Hin. lia.
Qed.

(** ** Local closure lemmas *)

(** ** Inversion lemmas for local closure *)

Lemma lc_at_bvar_inv : forall k i, lc_at k (tm_bvar i) -> i < k.
Proof. intros k i H. inversion H. assumption. Qed.

Lemma lc_at_app_inv : forall k t1 t2,
  lc_at k (tm_app t1 t2) -> lc_at k t1 /\ lc_at k t2.
Proof. intros k t1 t2 H. inversion H. split; assumption. Qed.

Lemma lc_at_abs_inv : forall k T t1, lc_at k (tm_abs T t1) -> lc_at (S k) t1.
Proof. intros k T t1 H. inversion H. assumption. Qed.

Lemma lc_at_if_inv : forall k t1 t2 t3,
  lc_at k (tm_if t1 t2 t3) -> lc_at k t1 /\ lc_at k t2 /\ lc_at k t3.
Proof. intros k t1 t2 t3 H. inversion H. auto. Qed.

Lemma lc_at_weaken : forall k (t : tm), lc_at k t -> forall j, k <= j -> lc_at j t.
Proof.
  intros k t H.
  induction H as [k' i Hlt | k' x | k' t1 t2 H1 IH1 H2 IH2
                 | k' T0 t1 H1 IH1 | k' | k' | k' t1 t2 t3 H1 IH1 H2 IH2 H3 IH3];
    intros j Hle.
  - apply lc_bvar; lia.
  - apply lc_fvar.
  - apply lc_app; [apply IH1 | apply IH2]; lia.
  - apply lc_abs; apply IH1; lia.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; [apply IH1 | apply IH2 | apply IH3]; lia.
Qed.

Lemma open_rec_lc_at : forall k (t : tm), lc_at k t ->
  forall j u, k <= j -> open_rec j u t = t.
Proof.
  intros k t H.
  induction H as [k' i Hlt | k' x | k' t1 t2 H1 IH1 H2 IH2
                 | k' T0 t1 H1 IH1 | k' | k' | k' t1 t2 t3 H1 IH1 H2 IH2 H3 IH3];
    intros j u Hle; simpl.
  - destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - rewrite IH1, IH2; auto.
  - rewrite IH1; [reflexivity | lia].
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2, IH3; auto.
Qed.

Lemma open_rec_closed : forall t, locally_closed t -> forall j u, open_rec j u t = t.
Proof.
  intros t H j u. apply open_rec_lc_at with (k := 0); [assumption | lia].
Qed.

Lemma open_rec_lc : forall t k u,
  lc_at (S k) t -> lc_at k u -> lc_at k (open_rec k u t).
Proof.
  intros t. induction t as [i | x | t1 IH1 t2 IH2 | T0 t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k u Ht Hu; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst. assumption.
    + apply Nat.eqb_neq in E. apply lc_bvar. apply lc_at_bvar_inv in Ht. lia.
  - apply lc_fvar.
  - apply lc_at_app_inv in Ht. destruct Ht as [H1 H2]. apply lc_app.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - apply lc_abs. apply IH1.
    + apply lc_at_abs_inv in Ht. assumption.
    + apply lc_at_weaken with (k := k); [assumption | lia].
  - apply lc_true.
  - apply lc_false.
  - apply lc_at_if_inv in Ht. destruct Ht as [H1 [H2 H3]]. apply lc_if.
    + apply IH1; assumption.
    + apply IH2; assumption.
    + apply IH3; assumption.
Qed.

(** Closing: if opening with a fresh free variable yields a locally closed
    term, then the original was locally closed one binder deeper. *)

Lemma lc_open_close : forall t k x,
  lc_at k (open_rec k (tm_fvar x) t) -> lc_at (S k) t.
Proof.
  intros t. induction t as [i | y | t1 IH1 t2 IH2 | T0 t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k x H; simpl in *.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_bvar. lia.
    + apply Nat.eqb_neq in E. apply lc_bvar. apply lc_at_bvar_inv in H. lia.
  - apply lc_fvar.
  - apply lc_at_app_inv in H. destruct H as [H1 H2]. apply lc_app.
    + apply IH1 with (x := x); assumption.
    + apply IH2 with (x := x); assumption.
  - apply lc_abs. apply IH1 with (x := x). apply lc_at_abs_inv in H. assumption.
  - apply lc_true.
  - apply lc_false.
  - apply lc_at_if_inv in H. destruct H as [H1 [H2 H3]]. apply lc_if.
    + apply IH1 with (x := x); assumption.
    + apply IH2 with (x := x); assumption.
    + apply IH3 with (x := x); assumption.
Qed.

(** ** Values and steps *)

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H. induction H as [T t Hlc | | ].
  - assumption.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma value_no_step : forall v t', value v -> ~ (v --> t').
Proof.
  intros v t' H. induction H as [T t Hlc | | ]; intro Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep.
Qed.

Lemma value_SN : forall v, value v -> strongly_normalizing v.
Proof.
  intros v H. apply SN_intro. intros t' Hstep.
  exfalso. eapply value_no_step; eassumption.
Qed.

Lemma step_preserves_lc : forall t t', t --> t' ->
  locally_closed t /\ locally_closed t'.
Proof.
  intros t t' H.
  induction H as [T t v Hlc Hval
                 | t1 t1' t2 Hstep IH Hlc2
                 | v1 t2 t2' Hval Hstep IH
                 | t1 t2 Hlc1 Hlc2
                 | t1 t2 Hlc1 Hlc2
                 | t1 t1' t2 t3 Hstep IH Hlc2 Hlc3].
  - (* ST_AppAbs *)
    simpl. split.
    + apply lc_app; [assumption | apply value_lc; assumption].
    + apply open_rec_lc.
      * apply lc_at_abs_inv in Hlc. exact Hlc.
      * apply value_lc; assumption.
  - (* ST_App1 *)
    destruct IH as [IH1 IH2]. simpl. split; apply lc_app; assumption.
  - (* ST_App2 *)
    destruct IH as [IH1 IH2]. simpl. split.
    + apply lc_app; [apply value_lc; assumption | assumption].
    + apply lc_app; [apply value_lc; assumption | assumption].
  - (* ST_IfTrue *)
    simpl. split.
    + apply lc_if; [apply lc_true | assumption | assumption].
    + assumption.
  - (* ST_IfFalse *)
    simpl. split.
    + apply lc_if; [apply lc_false | assumption | assumption].
    + assumption.
  - (* ST_If *)
    destruct IH as [IH1 IH2]. simpl. split; apply lc_if; assumption.
Qed.

(** Inversion principles for steps of applications and conditionals. *)

Lemma step_app_inv : forall t u t',
  tm_app t u --> t' ->
  (exists T0 body, t = tm_abs T0 body /\ locally_closed (tm_abs T0 body) /\
                   value u /\ t' = open body u)
  \/ (exists t1', t --> t1' /\ t' = tm_app t1' u)
  \/ (exists u', value t /\ u --> u' /\ t' = tm_app t u').
Proof.
  intros t u t' H. inversion H; subst.
  - left. repeat eexists. repeat split.
    all: try assumption.
  - right. left. eexists. split.
    + eassumption.
    + reflexivity.
  - right. right. repeat eexists. repeat split.
    all: try eassumption.
    all: try reflexivity.
Qed.

Lemma step_if_inv : forall t1 t2 t3 t',
  tm_if t1 t2 t3 --> t' ->
  (t1 = tm_true /\ t' = t2) \/ (t1 = tm_false /\ t' = t3) \/
  (exists t1', t1 --> t1' /\ t' = tm_if t1' t2 t3).
Proof.
  intros t1 t2 t3 t' H. inversion H; subst.
  - left. auto.
  - right. left. auto.
  - right. right. repeat eexists. repeat split.
    all: try eassumption.
    all: try reflexivity.
Qed.

(** ** Typing implies local closure *)

Lemma has_type_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T H.
  induction H as [Gamma x T Heq
                 | L Gamma T1 T2 t1 Hbody IHHbody
                 | Gamma t1 t2 T1 T2 Hty1 IH1 Hty2 IH2
                 | Gamma
                 | Gamma
                 | Gamma t1 t2 t3 T Hty1 IH1 Hty2 IH2 Hty3 IH3].
  - apply lc_fvar.
  - destruct (exists_fresh L) as [x Hx].
    apply lc_abs.
    specialize (IHHbody x Hx).
    unfold locally_closed, open in IHHbody.
    apply lc_open_close in IHHbody. assumption.
  - apply lc_app; assumption.
  - apply lc_true.
  - apply lc_false.
  - apply lc_if; assumption.
Qed.

(** ** Term substitution and free variables *)

Fixpoint subst (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst sigma t1) (subst sigma t2)
  | tm_abs T t1 => tm_abs T (subst sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (subst sigma t1) (subst sigma t2) (subst sigma t3)
  end.

Fixpoint fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => (x :: nil)%list
  | tm_app t1 t2 => (fvars t1 ++ fvars t2)%list
  | tm_abs _ t1 => fvars t1
  | tm_true => nil
  | tm_false => nil
  | tm_if t1 t2 t3 => (fvars t1 ++ fvars t2 ++ fvars t3)%list
  end.

Lemma subst_lc : forall t k sigma,
  lc_at k t -> (forall x, locally_closed (sigma x)) -> lc_at k (subst sigma t).
Proof.
  intros t. induction t as [i | x | t1 IH1 t2 IH2 | T0 t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k sigma Ht Hsig; simpl in *.
  - assumption.
  - apply lc_at_weaken with (k := 0); [apply Hsig | lia].
  - apply lc_at_app_inv in Ht. destruct Ht as [H1 H2]. apply lc_app.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - apply lc_abs. apply IH1.
    + apply lc_at_abs_inv in Ht. assumption.
    + assumption.
  - apply lc_true.
  - apply lc_false.
  - apply lc_at_if_inv in Ht. destruct Ht as [H1 [H2 H3]]. apply lc_if.
    + apply IH1; assumption.
    + apply IH2; assumption.
    + apply IH3; assumption.
Qed.

Lemma subst_open_rec : forall t k v sigma,
  (forall x, locally_closed (sigma x)) ->
  subst sigma (open_rec k v t) = open_rec k (subst sigma v) (subst sigma t).
Proof.
  intros t. induction t as [i | x | t1 IH1 t2 IH2 | T0 t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros k v sigma Hsig; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - symmetry. apply open_rec_closed. apply Hsig.
  - rewrite (IH1 k v sigma Hsig). rewrite (IH2 k v sigma Hsig). reflexivity.
  - rewrite (IH1 (S k) v sigma Hsig). reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite (IH1 k v sigma Hsig). rewrite (IH2 k v sigma Hsig).
    rewrite (IH3 k v sigma Hsig). reflexivity.
Qed.

Lemma subst_fresh : forall t sigma x u,
  ~ In x (fvars t) ->
  subst (fun y => if Nat.eqb x y then u else sigma y) t = subst sigma t.
Proof.
  intros t. induction t as [i | y | t1 IH1 t2 IH2 | T0 t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros sigma x u Hfresh; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. auto.
    + reflexivity.
  - assert (Hf1 : ~ In x (fvars t1)).
    { intro Hc. apply Hfresh. apply in_or_app. left. assumption. }
    assert (Hf2 : ~ In x (fvars t2)).
    { intro Hc. apply Hfresh. apply in_or_app. right. assumption. }
    rewrite (IH1 sigma x u Hf1). rewrite (IH2 sigma x u Hf2). reflexivity.
  - rewrite (IH1 sigma x u Hfresh). reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (Hf1 : ~ In x (fvars t1)).
    { intro Hc. apply Hfresh. apply in_or_app. left. assumption. }
    assert (Hf2 : ~ In x (fvars t2)).
    { intro Hc. apply Hfresh. apply in_or_app. right. apply in_or_app. left. assumption. }
    assert (Hf3 : ~ In x (fvars t3)).
    { intro Hc. apply Hfresh. apply in_or_app. right. apply in_or_app. right. assumption. }
    rewrite (IH1 sigma x u Hf1). rewrite (IH2 sigma x u Hf2).
    rewrite (IH3 sigma x u Hf3). reflexivity.
Qed.

Lemma subst_fvar_id : forall t, subst (fun x => tm_fvar x) t = t.
Proof.
  intros t. induction t as [i | x | t1 IH1 t2 IH2 | T0 t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2, IH3. reflexivity.
Qed.

(** ** The logical relation *)

Fixpoint LR (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => locally_closed t /\ strongly_normalizing t
  | Ty_Arrow T1 T2 =>
      locally_closed t /\ strongly_normalizing t /\
      (forall u, LR T1 u -> LR T2 (tm_app t u))
  end.

Lemma LR_lc : forall T t, LR T t -> locally_closed t.
Proof.
  intros T. induction T as [| A IHA B IHB]; intros t H; simpl in H.
  - destruct H as [H1 H2]. assumption.
  - destruct H as [H1 H2]. assumption.
Qed.

Lemma LR_sn : forall T t, LR T t -> strongly_normalizing t.
Proof.
  intros T. induction T as [| A IHA B IHB]; intros t H; simpl in H.
  - destruct H as [H1 H2]. assumption.
  - destruct H as [H1 [H2 H3]]. assumption.
Qed.

Lemma LR_app : forall A B t u,
  LR (Ty_Arrow A B) t -> LR A u -> LR B (tm_app t u).
Proof.
  intros A B t u HLR HLRu. simpl in HLR.
  destruct HLR as [Hlc [Hsn Hclause]]. apply Hclause; assumption.
Qed.

Lemma SN_step : forall t t',
  strongly_normalizing t -> t --> t' -> strongly_normalizing t'.
Proof.
  intros t t' Hsn Hstep. destruct Hsn as [t0 Hred]. apply (Hred t' Hstep).
Qed.

Lemma LR_step : forall T t t', LR T t -> t --> t' -> LR T t'.
Proof.
  intros T. induction T as [| A IHA B IHB]; intros t t' HLR Hstep.
  - simpl in HLR. simpl. destruct HLR as [Hlc Hsn]. split.
    + apply (proj2 (step_preserves_lc t t' Hstep)).
    + apply SN_step with (t := t); assumption.
  - simpl in HLR. simpl. destruct HLR as [Hlc [Hsn Hclause]]. split; [| split].
    + apply (proj2 (step_preserves_lc t t' Hstep)).
    + apply SN_step with (t := t); assumption.
    + intros u HLRu. apply IHB with (t := tm_app t u).
      * apply Hclause; assumption.
      * apply ST_App1; [assumption | exact (LR_lc A u HLRu)].
Qed.

(** Neutral closure: a non-value term is in the logical relation as soon as
    all of its one-step reducts are. *)

Lemma LR_neutral : forall T t,
  locally_closed t -> ~ value t ->
  (forall t', t --> t' -> LR T t') -> LR T t.
Proof.
  intros T. induction T as [| A IHA B IHB]; intros t Hlc Hnv Hred.
  - simpl. split; [assumption |].
    apply SN_intro. intros t' Hstep.
    exact (LR_sn Ty_Bool t' (Hred t' Hstep)).
  - simpl. split; [assumption | split].
    + apply SN_intro. intros t' Hstep.
      exact (LR_sn (Ty_Arrow A B) t' (Hred t' Hstep)).
    + intros u HLRu. apply IHB with (t := tm_app t u).
      * apply lc_app; [assumption | exact (LR_lc A u HLRu)].
      * intro Hv. inversion Hv.
      * intros s Hstep. apply step_app_inv in Hstep.
        destruct Hstep as [Hex | [Hex | Hex]].
        -- destruct Hex as [T0 [body [Heq [Hlc0 [Hval Hs]]]]]. subst.
           exfalso. apply Hnv. apply v_abs. assumption.
        -- destruct Hex as [t1' [Hst Hs]]. subst.
           apply LR_app with (A := A) (u := u). apply Hred; assumption. assumption.
        -- destruct Hex as [u' [Hval [Hst Hs]]]. subst.
           exfalso. apply Hnv. assumption.
Qed.

Lemma SN_if : forall t1 t2 t3,
  strongly_normalizing t1 -> strongly_normalizing t2 -> strongly_normalizing t3 ->
  strongly_normalizing (tm_if t1 t2 t3).
Proof.
  intros t1 t2 t3 H1.
  induction H1 as [t1 Hred IH].
  intros H2 H3.
  apply SN_intro. intros t' Hstep.
  apply step_if_inv in Hstep.
  destruct Hstep as [[Heq Ht] | [[Heq Ht] | [t1' [Hst Heq]]]]; subst.
  - assumption.
  - assumption.
  - apply (IH t1' Hst H2 H3).
Qed.

Lemma LR_if : forall T t1 t2 t3,
  LR Ty_Bool t1 -> LR T t2 -> LR T t3 -> LR T (tm_if t1 t2 t3).
Proof.
  assert (Hmain : forall t1, strongly_normalizing t1 ->
    forall T t2 t3, LR Ty_Bool t1 -> LR T t2 -> LR T t3 ->
      LR T (tm_if t1 t2 t3)).
  { intros t1 Hsn. induction Hsn as [t1 Hred IH].
    intros T t2 t3 H1 H2 H3.
    destruct T as [| A B].
    - (* Bool *) simpl. split.
      + apply lc_if.
        * exact (LR_lc _ _ H1).
        * exact (LR_lc _ _ H2).
        * exact (LR_lc _ _ H3).
      + apply SN_if.
        * exact (LR_sn _ _ H1).
        * exact (LR_sn _ _ H2).
        * exact (LR_sn _ _ H3).
    - (* Arrow *) simpl. split; [| split].
      + apply lc_if.
        * exact (LR_lc _ _ H1).
        * exact (LR_lc _ _ H2).
        * exact (LR_lc _ _ H3).
      + apply SN_if.
        * exact (LR_sn _ _ H1).
        * exact (LR_sn _ _ H2).
        * exact (LR_sn _ _ H3).
      + intros u HLRu. apply LR_neutral.
        * apply lc_app.
          -- apply lc_if.
             ++ exact (LR_lc _ _ H1).
             ++ exact (LR_lc _ _ H2).
             ++ exact (LR_lc _ _ H3).
          -- exact (LR_lc _ _ HLRu).
        * intro Hv. inversion Hv.
        * intros s Hstep. apply step_app_inv in Hstep.
          destruct Hstep as [[T0 [body [Heq [Hlc0 [Hvalu Hs]]]]] |
                            [[s1' [Hstep1 Hs]] | [u' [Hvalu [Hstep2 Hs]]]]].
          -- subst. exfalso. inversion Heq.
          -- subst. apply step_if_inv in Hstep1.
             destruct Hstep1 as [[Heq Ht] | [[Heq Ht] | [t1' [Hst Heq]]]]; subst.
             ++ apply LR_app with (A := A) (u := u); assumption.
             ++ apply LR_app with (A := A) (u := u); assumption.
             ++ apply LR_app with (A := A) (u := u).
                ** apply (IH t1' Hst (Ty_Arrow A B) t2 t3).
                   { apply LR_step with (t := t1); assumption. }
                   { assumption. }
                   { assumption. }
                ** assumption.
          -- subst. exfalso. inversion Hvalu.
  }
  intros T t1 t2 t3 H1 H2 H3.
  apply Hmain; [exact (LR_sn _ _ H1) | assumption | assumption | assumption].
Qed.

Lemma LR_abs_intro : forall T1 T2 body,
  locally_closed (tm_abs T1 body) ->
  (forall u, value u -> LR T1 u -> LR T2 (open body u)) ->
  LR (Ty_Arrow T1 T2) (tm_abs T1 body).
Proof.
  intros T1 T2 body Hlc Hsem.
  assert (Haux : forall u, strongly_normalizing u -> LR T1 u ->
    LR T2 (tm_app (tm_abs T1 body) u)).
  { intros u Hsn. induction Hsn as [u Hred IH]. intros HLRu.
    apply LR_neutral.
    - apply lc_app; [assumption | exact (LR_lc T1 u HLRu)].
    - intro Hv. inversion Hv.
    - intros s Hstep. apply step_app_inv in Hstep.
      destruct Hstep as [[T0 [body0 [Heq [Hlc0 [Hvalu Hs]]]]] |
                        [[s1' [Hstep1 Hs]] | [u' [Hvalu [Hstep2 Hs]]]]].
      + subst. inversion Heq; subst. apply Hsem; assumption.
      + subst. exfalso. inversion Hstep1.
      + subst. apply (IH u' Hstep2). apply LR_step with (t := u); assumption.
  }
  simpl. split; [assumption | split].
  - apply SN_intro. intros t' Hstep. inversion Hstep.
  - intros u HLRu. apply Haux; [exact (LR_sn _ _ HLRu) | assumption].
Qed.

(** ** Environments *)

Definition env_sat (Gamma : context) (sigma : atom -> tm) : Prop :=
  (forall x, locally_closed (sigma x)) /\
  (forall x T, Gamma x = Some T -> LR T (sigma x)).

Lemma update_eq : forall Gamma x T, update Gamma x T x = Some T.
Proof.
  intros. unfold update. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma update_neq : forall Gamma x y T, x <> y -> update Gamma x T y = Gamma y.
Proof.
  intros Gamma x y T Hneq. unfold update.
  apply Nat.eqb_neq in Hneq. rewrite Hneq. reflexivity.
Qed.

Lemma subst_ext : forall t phi sigma,
  (forall y, In y (fvars t) -> phi y = sigma y) ->
  subst phi t = subst sigma t.
Proof.
  intros t. induction t as [i | x | t1 IH1 t2 IH2 | T0 t1 IH1 | | | t1 IH1 t2 IH2 t3 IH3];
    intros phi sigma Hagree; simpl in *.
  - reflexivity.
  - apply Hagree. simpl. auto.
  - assert (H1 : subst phi t1 = subst sigma t1).
    { apply IH1. intros y Hy. apply Hagree. apply in_or_app. left. assumption. }
    assert (H2 : subst phi t2 = subst sigma t2).
    { apply IH2. intros y Hy. apply Hagree. apply in_or_app. right. assumption. }
    rewrite H1, H2. reflexivity.
  - assert (H1 : subst phi t1 = subst sigma t1).
    { apply IH1. intros y Hy. apply Hagree. assumption. }
    rewrite H1. reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (H1 : subst phi t1 = subst sigma t1).
    { apply IH1. intros y Hy. apply Hagree. apply in_or_app. left. assumption. }
    assert (H2 : subst phi t2 = subst sigma t2).
    { apply IH2. intros y Hy. apply Hagree.
      apply in_or_app. right. apply in_or_app. left. assumption. }
    assert (H3 : subst phi t3 = subst sigma t3).
    { apply IH3. intros y Hy. apply Hagree.
      apply in_or_app. right. apply in_or_app. right. assumption. }
    rewrite H1, H2, H3. reflexivity.
Qed.

Lemma subst_open_single : forall t sigma phi x u,
  (forall y, locally_closed (phi y)) ->
  phi x = u ->
  (forall y, In y (fvars t) -> phi y = sigma y) ->
  subst phi (open t (tm_fvar x)) = open (subst sigma t) u.
Proof.
  intros t sigma phi x u Hlc Hx Hagree.
  unfold open.
  rewrite (subst_open_rec t 0 (tm_fvar x) phi Hlc).
  assert (Hsub : subst phi (tm_fvar x) = u).
  { simpl. exact Hx. }
  rewrite Hsub.
  rewrite (subst_ext t phi sigma Hagree).
  reflexivity.
Qed.

(** ** Fundamental theorem *)

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall sigma, env_sat Gamma sigma -> LR T (subst sigma t).
Proof.
  intros Gamma t T H.
  induction H as [Gamma x T Heq
                 | L Gamma T1 T2 t1 Hbody IHHbody
                 | Gamma t1 t2 T1 T2 Hty1 IH1 Hty2 IH2
                 | Gamma
                 | Gamma
                 | Gamma t1 t2 t3 T Hty1 IH1 Hty2 IH2 Hty3 IH3];
    intros sigma Hsat.
  - (* T_Var *)
    simpl. apply (proj2 Hsat). assumption.
  - (* T_Abs *)
    simpl. apply LR_abs_intro.
    + (* local closure *)
      apply lc_abs. apply subst_lc.
      * assert (Hlcabs : locally_closed (tm_abs T1 t1)).
        { exact (has_type_lc Gamma (tm_abs T1 t1) (Ty_Arrow T1 T2)
                   (T_Abs L Gamma T1 T2 t1 Hbody)). }
        unfold locally_closed in Hlcabs.
        apply lc_at_abs_inv in Hlcabs. exact Hlcabs.
      * exact (proj1 Hsat).
    + (* semantic body *)
      intros u Hval HLRu.
      destruct (exists_fresh (L ++ fvars t1)) as [x Hx].
      assert (HxL : ~ In x L).
      { intro Hc. apply Hx. apply in_or_app. left. assumption. }
      assert (Hxt : ~ In x (fvars t1)).
      { intro Hc. apply Hx. apply in_or_app. right. assumption. }
      pose (sigma' := fun y => if Nat.eqb x y then u else sigma y).
      assert (Hsat' : env_sat (update Gamma x T1) sigma').
      { split.
        - intros y. unfold sigma'. destruct (Nat.eqb x y) eqn:E.
          + apply LR_lc in HLRu. assumption.
          + exact (proj1 Hsat y).
        - intros y A Hup. unfold sigma'. destruct (Nat.eqb x y) eqn:E.
          + apply Nat.eqb_eq in E. subst y.
            rewrite update_eq in Hup. injection Hup as <-. assumption.
          + apply Nat.eqb_neq in E.
            rewrite update_neq in Hup; [exact (proj2 Hsat y A Hup) | assumption].
      }
      assert (Hsigma'_x : sigma' x = u).
      { unfold sigma'. rewrite Nat.eqb_refl. reflexivity. }
      assert (Hsigma'_agree : forall y, In y (fvars t1) -> sigma' y = sigma y).
      { intros y Hy. unfold sigma'. destruct (Nat.eqb x y) eqn:E.
        - apply Nat.eqb_eq in E. subst y. exfalso. apply Hxt. assumption.
        - reflexivity. }
      pose proof (IHHbody x HxL sigma' Hsat') as HbodyLR.
      rewrite (subst_open_single t1 sigma sigma' x u (proj1 Hsat')
                 Hsigma'_x Hsigma'_agree) in HbodyLR.
      exact HbodyLR.
  - (* T_App *)
    simpl. apply LR_app with (A := T1) (B := T2).
    + apply IH1. assumption.
    + apply IH2. assumption.
  - (* T_True *)
    simpl. split.
    + apply lc_true.
    + apply SN_intro. intros t' Hstep. inversion Hstep.
  - (* T_False *)
    simpl. split.
    + apply lc_false.
    + apply SN_intro. intros t' Hstep. inversion Hstep.
  - (* T_If *)
    simpl. apply LR_if.
    + apply IH1. assumption.
    + apply IH2. assumption.
    + apply IH3. assumption.
Qed.

(** Target theorem: strong normalization for the supplied CBV relation. *)

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (Hsat : env_sat empty (fun x => tm_fvar x)).
  { split.
    - intros x. apply lc_fvar.
    - intros x T0 Heq. unfold empty in Heq. discriminate.
  }
  pose proof (fundamental empty t T Hty (fun x => tm_fvar x) Hsat) as HLR.
  rewrite subst_fvar_id in HLR.
  apply LR_sn in HLR. assumption.
Qed.

End STLCCBVNormalizationTask.
