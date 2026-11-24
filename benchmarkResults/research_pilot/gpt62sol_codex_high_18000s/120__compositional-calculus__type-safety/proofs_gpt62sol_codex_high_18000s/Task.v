Require Import Infrastructure.

Require Import Coq.Program.Equality.

Require Import List.

Import ListNotations.

Require Import Arith Lia.

Local Set Implicit Arguments.

(* The ordinary components of a type follow its covariant spine. *)
Fixpoint components (A : typ) : list typ :=
  match A with
  | t_and B C => components B ++ components C
  | t_arrow B C => map (t_arrow B) (components C)
  | t_forall B C => map (t_forall B) (components C)
  | t_rcd l B => map (t_rcd l) (components B)
  | _ => [A]
  end.

Local Ltac component_in :=
  repeat match goal with
  | H : In _ (_ ++ _) |- _ => apply in_app_or in H; destruct H
  | H : In _ (map _ _) |- _ => apply in_map_iff in H;
      let a := fresh "part" in let Heq := fresh "Heq" in let Hin := fresh "Hin" in
      destruct H as [a [Heq Hin] ]; subst
  | H : _ :: _ = [] |- _ => discriminate H
  end.

Lemma components_nonempty : forall A, exists a, In a (components A).
Proof.
  induction A; simpl; try (eexists; left; reflexivity).
  all: destruct IHA || destruct IHA2 || destruct IHA1.
  all: try solve [eexists; apply in_map; eassumption].
  eexists; apply in_or_app; eauto.
Qed.

Lemma component_size : forall A a, In a (components A) -> size_typ a <= size_typ A.
Proof.
  induction A; simpl; intros a H; try (destruct H as [<-|[] ]; simpl; lia).
  - apply in_map_iff in H. destruct H as [c [<- H] ]; simpl. specialize (IHA2 _ H); lia.
  - apply in_map_iff in H. destruct H as [c [<- H] ]; simpl. specialize (IHA2 _ H); lia.
  - apply in_app_or in H; destruct H; [specialize (IHA1 _ H) | specialize (IHA2 _ H)]; lia.
  - apply in_map_iff in H. destruct H as [c [<- H] ]; simpl. specialize (IHA _ H); lia.
Qed.

Definition push (P : nat -> Prop) (p : Prop) (n : nat) : Prop :=
  match n with 0 => p | S k => P k end.

Fixpoint bottom_shape (A : typ) : Prop :=
  match A with
  | t_bot => True
  | t_and B C => bottom_shape B \/ bottom_shape C
  | _ => False
  end.

Fixpoint top_shape (F : atom -> Prop) (P : nat -> Prop) (A : typ) : Prop :=
  match A with
  | t_tvar_b k => P k
  | t_tvar_f x => F x
  | t_top => True
  | t_and B C => top_shape F P B /\ top_shape F P C
  | t_arrow _ C => top_shape F P C
  | t_rcd _ C => top_shape F P C
  | t_forall B C => top_shape F (push P (bottom_shape B)) C
  | _ => False
  end.

Lemma bottom_components : forall A,
    bottom_shape A <-> In t_bot (components A).
Proof.
  induction A; simpl; try tauto.
  all: try (rewrite in_map_iff; split; [tauto | intros [a [H _] ]; discriminate H]).
  all: try (rewrite in_app_iff, <- IHA1, <- IHA2; tauto).
  all: intuition discriminate.
Qed.

Lemma top_components : forall A F P,
    top_shape F P A <-> (forall a, In a (components A) -> top_shape F P a).
Proof.
  induction A; simpl; intros F P.
  all: try solve [
    match goal with
    | |- _ <-> (forall a, ?c = a \/ False -> _) =>
        split; [intros H a [<-|[] ]; exact H | intros H; exact (H c (or_introl eq_refl))]
    end].
  all: try solve [
    split; intros H;
    [ intros a Ha; apply in_map_iff in Ha; destruct Ha as [a' [<- Ha] ];
      apply (proj1 (IHA2 _ _) H _ Ha)
    | apply (proj2 (IHA2 _ _)); intros a Ha;
      first [exact (H _ (in_map (t_forall A1) _ _ Ha)) |
             exact (H _ (in_map (t_arrow A1) _ _ Ha))] ] ].
  - split.
    + intros [H1 H2] a Ha. apply in_app_or in Ha. destruct Ha as [Ha|Ha].
      * exact (proj1 (IHA1 F P) H1 a Ha).
      * exact (proj1 (IHA2 F P) H2 a Ha).
    + intros H; split; [apply (proj2 (IHA1 F P)) | apply (proj2 (IHA2 F P))];
      intros; apply H; apply in_or_app; auto.
  - split; intros H.
    + intros a Ha. apply in_map_iff in Ha. destruct Ha as [a' [<- Ha] ]. exact (proj1 (IHA _ _) H _ Ha).
    + apply (proj2 (IHA _ _)); intros a Ha. exact (H _ (in_map (t_rcd l) _ _ Ha)).
Qed.

Lemma top_shape_mono : forall A F P F' P',
    (forall x, F x -> F' x) -> (forall k, P k -> P' k) ->
    top_shape F P A -> top_shape F' P' A.
Proof.
  induction A; simpl; intros; eauto.
  all: intuition eauto.
  eapply IHA2; [exact H | | exact H1]. intros [|n]; simpl; auto.
Qed.

(* Compare each target component with a source component, with separate
   rules for top-like targets and bottom-like sources. For a universal
   type, its bound controls when the bound variable is top-like. *)
Inductive normal_sub (F : atom -> Prop) : (nat -> Prop) -> typ -> typ -> Prop :=
| NS_parts : forall P A B,
    (forall b, In b (components B) -> component_sub F P A b) ->
    normal_sub F P A B
with component_sub (F : atom -> Prop) : (nat -> Prop) -> typ -> typ -> Prop :=
| NS_top : forall P A b, top_shape F P b -> component_sub F P A b
| NS_bottom : forall P A b, bottom_shape A -> component_sub F P A b
| NS_same : forall P A b, In b (components A) -> component_sub F P A b
| NS_arrow : forall P A U V B C,
    In (t_arrow U V) (components A) ->
    normal_sub F P B U -> normal_sub F P V C ->
    component_sub F P A (t_arrow B C)
| NS_all : forall P A U V B C,
    In (t_forall U V) (components A) ->
    normal_sub F P B U -> normal_sub F (push P (bottom_shape B)) V C ->
    component_sub F P A (t_forall B C)
| NS_rcd : forall P A l V C,
    In (t_rcd l V) (components A) -> normal_sub F P V C ->
    component_sub F P A (t_rcd l C).

Scheme normal_sub_ind' := Induction for normal_sub Sort Prop
with component_sub_ind' := Induction for component_sub Sort Prop.
Combined Scheme normal_sub_mutind from normal_sub_ind', component_sub_ind'.

Local Hint Constructors normal_sub component_sub : task.

Lemma normal_sub_mono : forall F,
  (forall P A B, normal_sub F P A B -> forall F' P',
    (forall x, F x -> F' x) -> (forall n, P n -> P' n) -> normal_sub F' P' A B) /\
  (forall P A B, component_sub F P A B -> forall F' P',
    (forall x, F x -> F' x) -> (forall n, P n -> P' n) -> component_sub F' P' A B).
Proof.
  intro F; apply normal_sub_mutind; eauto 8 using top_shape_mono with task.
  intros; eapply NS_all; eauto. eapply H0; eauto. intros []; simpl; auto.
Qed.

Lemma normal_sub_bottom : forall F P A B,
    normal_sub F P A B -> bottom_shape B -> bottom_shape A.
Proof.
  intros F P A B H; destruct H as [P A B H]; intro HB.
  apply bottom_components in HB. specialize (H _ HB). inversion H; subst; simpl in *;
    try contradiction; auto; apply bottom_components; assumption.
Qed.

Lemma normal_sub_top : forall F,
  (forall P A B, normal_sub F P A B -> top_shape F P A -> top_shape F P B) /\
  (forall P A B, component_sub F P A B -> top_shape F P A -> top_shape F P B).
Proof.
  intro F; apply normal_sub_mutind; intros.
  - apply top_components; auto.
  - assumption.
  - apply bottom_components in b0.
    pose proof (proj1 (top_components _ _ _) H _ b0) as Hbot. contradiction.
  - exact (proj1 (top_components _ _ _) H _ i).
  - apply H0. exact (proj1 (top_components _ _ _) H1 _ i).
  - apply H0. eapply top_shape_mono; [eauto | | exact (proj1 (top_components _ _ _) H1 _ i)].
    intros []; simpl; auto. eauto using normal_sub_bottom.
  - apply H. exact (proj1 (top_components _ _ _) H0 _ i).
Qed.

Lemma component_sub_source : forall F P A B b,
    (bottom_shape A -> bottom_shape B) ->
    (forall a, In a (components A) -> In a (components B)) ->
    component_sub F P A b -> component_sub F P B b.
Proof. intros; inversion H1; subst; eauto with task. Qed.

Lemma normal_sub_source : forall F P A B C,
    (forall a, In a (components A) -> In a (components B)) ->
    normal_sub F P A C -> normal_sub F P B C.
Proof.
  intros F P A B C Hin H; inversion H; subst; constructor; intros.
  eapply component_sub_source with (A := A); eauto. rewrite !bottom_components; eauto.
Qed.

Lemma normal_sub_refl : forall F P A, normal_sub F P A A.
Proof. eauto with task. Qed.

Lemma normal_sub_component : forall F P A B b,
    normal_sub F P A B -> In b (components B) -> component_sub F P A b.
Proof. intros F P A B b H; inversion H; subst; auto. Qed.

Lemma components_stable : forall A a b,
    In a (components A) -> In b (components a) -> b = a.
Proof.
  induction A; simpl; intros a b Ha Hb;
    try solve [destruct Ha as [<-|[] ]; simpl in Hb; intuition].
  all: component_in; simpl in *; component_in; f_equal; eauto.
Qed.

Lemma normal_sub_select : forall F P A a,
    In a (components A) -> normal_sub F P A a.
Proof.
  intros; constructor; intros b Hb.
  assert (b = a) by (eapply components_stable; eauto).
  subst; auto with task.
Qed.

Lemma component_sub_trans : forall n F P A B C,
    size_typ A + size_typ B + size_typ C <= n ->
    normal_sub F P A B -> component_sub F P B C -> component_sub F P A C.
Proof.
  induction n as [n IH] using lt_wf_ind.
  assert (compose : forall F P A B C,
      size_typ A + size_typ B + size_typ C < n ->
      normal_sub F P A B -> normal_sub F P B C -> normal_sub F P A C).
  { intros F P A B C Hsize HAB HBC; constructor; intros c Hc.
    eapply (IH (size_typ A + size_typ B + size_typ C)); eauto using normal_sub_component.
    pose proof (component_size _ _ Hc); lia. }
  intros F P A B C Hsize HAB HBC.
  inversion HBC; subst; try solve [eauto using normal_sub_bottom, normal_sub_component with task].
  all: pose proof (component_size _ _ H) as Hpart;
    pose proof (normal_sub_component _ HAB H) as Hmid;
    inversion Hmid; subst; try solve [eauto with task].
  - apply NS_top; simpl in *. eapply (proj1 (normal_sub_top F)); eauto.
  - match goal with Hc : In (t_arrow _ _) (components A) |- _ =>
      pose proof (component_size _ _ Hc); eapply NS_arrow; [exact Hc | | ] end.
    all: eapply compose; [ | eassumption | eassumption]; simpl in *; lia.
  - apply NS_top; simpl in *. eapply (proj1 (normal_sub_top F)); [eassumption |].
    eapply top_shape_mono; [eauto | | eassumption].
    intros [|k]; simpl; eauto using normal_sub_bottom.
  - match goal with Hc : In (t_forall _ _) (components A) |- _ =>
      pose proof (component_size _ _ Hc); eapply NS_all; [exact Hc | | ] end.
    + eapply compose; [ | eassumption | eassumption]; simpl in *; lia.
    + eapply compose; [ | | eassumption].
      2: { eapply (proj1 (normal_sub_mono F)); [eassumption | eauto | ].
           intros [|k]; simpl; eauto using normal_sub_bottom. }
      simpl in *; lia.
  - apply NS_top; simpl in *. eapply (proj1 (normal_sub_top F)); eauto.
  - match goal with Hc : In (t_rcd _ _) (components A) |- _ =>
      pose proof (component_size _ _ Hc); eapply NS_rcd; [exact Hc | ] end.
    eapply compose; [ | eassumption | eassumption]; simpl in *; lia.
Qed.

Lemma normal_sub_trans : forall F P A B C,
    normal_sub F P A B -> normal_sub F P B C -> normal_sub F P A C.
Proof.
  intros F P A B C HAB HBC; constructor; intros b Hb.
  eapply (component_sub_trans (n := size_typ A + size_typ B + size_typ C)); eauto using normal_sub_component.
  pose proof (component_size _ _ Hb); lia.
Qed.

Lemma normal_sub_top_rule : forall F P A B,
    top_shape F P B -> normal_sub F P A B.
Proof. intros; constructor; intros; apply NS_top; eapply (proj1 (top_components _ _ _) H); eauto. Qed.

Lemma normal_sub_bot_rule : forall F P A B,
    bottom_shape A -> normal_sub F P A B.
Proof. eauto with task. Qed.

Lemma normal_sub_left : forall F P A B, normal_sub F P (t_and A B) A.
Proof.
  intros; apply normal_sub_source with (A := A); [simpl; auto using in_or_app | apply normal_sub_refl].
Qed.

Lemma normal_sub_right : forall F P A B, normal_sub F P (t_and A B) B.
Proof.
  intros; apply normal_sub_source with (A := B); [simpl; auto using in_or_app | apply normal_sub_refl].
Qed.

Lemma component_self : forall A a, In a (components A) -> In a (components a).
Proof.
  intros A a H; destruct (components_nonempty a) as [b Hb].
  pose proof (components_stable A a b H Hb); congruence.
Qed.

Lemma component_sub_pick : forall F P A b,
    (forall c, In c (components b) -> c = b) ->
    component_sub F P A b ->
    top_shape F P b \/ exists a, In a (components A) /\ normal_sub F P a b.
Proof.
  intros F P A b Hb H; inversion H; subst.
  all: try solve [left; assumption].
  all: try solve [right; exists t_bot; split; [apply bottom_components | apply normal_sub_bot_rule]; auto; exact I].
  all: try solve [right; eauto using normal_sub_refl].
  all: right; eexists; split; [eassumption | ];
    constructor; intros c Hc; specialize (Hb _ Hc); subst;
    eauto 6 using component_self with task.
Qed.

Lemma normal_sub_arrow : forall F P A B C D,
    normal_sub F P C A -> normal_sub F P B D ->
    normal_sub F P (t_arrow A B) (t_arrow C D).
Proof.
  intros F P A B C D Hdom Hcod; constructor; intros b Hb; simpl in Hb; component_in.
  destruct (component_sub_pick (fun c Hc => components_stable D part c Hin Hc)
    (normal_sub_component _ Hcod Hin)) as [Htop|[a [Ha Hsub] ] ].
  - apply NS_top; exact Htop.
  - eapply NS_arrow; [apply in_map; exact Ha | exact Hdom | exact Hsub].
Qed.

Lemma normal_sub_all : forall F P A B C D,
    normal_sub F P C A -> normal_sub F (push P (bottom_shape C)) B D ->
    normal_sub F P (t_forall A B) (t_forall C D).
Proof.
  intros F P A B C D Hdom Hcod; constructor; intros b Hb; simpl in Hb; component_in.
  destruct (component_sub_pick (fun c Hc => components_stable D part c Hin Hc)
    (normal_sub_component _ Hcod Hin)) as [Htop|[a [Ha Hsub] ] ].
  - apply NS_top; exact Htop.
  - eapply NS_all; [apply in_map; exact Ha | exact Hdom | exact Hsub].
Qed.

Lemma normal_sub_rcd : forall F P l B D,
    normal_sub F P B D -> normal_sub F P (t_rcd l B) (t_rcd l D).
Proof.
  intros F P l B D Hcod; constructor; intros b Hb; simpl in Hb; component_in.
  destruct (component_sub_pick (fun c Hc => components_stable D part c Hin Hc)
    (normal_sub_component _ Hcod Hin)) as [Htop|[a [Ha Hsub] ] ].
  - apply NS_top; exact Htop.
  - eapply NS_rcd; [apply in_map; exact Ha | exact Hsub].
Qed.

Fixpoint transform_type (f : nat -> atom -> typ) (g : nat -> nat -> typ) (k : nat) (A : typ) : typ :=
  match A with
  | t_tvar_f x => f k x
  | t_tvar_b n => g k n
  | t_and B C => t_and (transform_type f g k B) (transform_type f g k C)
  | t_arrow B C => t_arrow (transform_type f g k B) (transform_type f g k C)
  | t_forall B C => t_forall (transform_type f g k B) (transform_type f g (S k) C)
  | t_rcd l B => t_rcd l (transform_type f g k B)
  | _ => A
  end.

Lemma transform_bottom : forall A f g k, bottom_shape A -> bottom_shape (transform_type f g k A).
Proof. induction A; simpl; intuition eauto. Qed.

Lemma transform_components : forall A f g k b,
    In b (components (transform_type f g k A)) <->
    exists a, In a (components A) /\ In b (components (transform_type f g k a)).
Proof.
  induction A; intros f g k b; simpl;
    try solve [split; [eauto|intros [a [ [<-|[] ] H] ]; exact H] ].
  all: try solve [
    split;
    [ intros H; apply in_map_iff in H; destruct H as [c [<- H] ];
      first [apply IHA2 in H | apply IHA in H]; destruct H as [a [Ha Hc] ];
      eexists; split; [apply in_map; exact Ha | simpl; apply in_map; exact Hc]
    | intros [a [Ha Hb] ]; apply in_map_iff in Ha; destruct Ha as [c [<- Hc] ];
      simpl in Hb; apply in_map_iff in Hb; destruct Hb as [b' [<- Hb'] ];
      apply in_map; first [apply IHA2 | apply IHA]; eauto ] ].
  rewrite in_app_iff, IHA1, IHA2.
  split; intros H.
  - destruct H as [ [a [H1 H2] ] | [a [H1 H2] ] ]; exists a; split; auto using in_or_app.
  - destruct H as [a [Ha Hb] ]; apply in_app_or in Ha; firstorder.
Qed.

Definition transform_top_ok f g (k : nat) (F : atom -> Prop) (P : nat -> Prop)
    (F' : atom -> Prop) (P' : nat -> Prop) :=
  (forall x, F x -> top_shape F' P' (f k x)) /\
  (forall n, P n -> top_shape F' P' (g k n)).

Definition transform_lifts f g :=
  forall k F P F' P' (q r : Prop),
  transform_top_ok f g k F P F' P' -> (q -> r) ->
  transform_top_ok f g (S k) F (push P q) F' (push P' r).

Lemma transform_top : forall A f g k F P F' P',
    transform_lifts f g -> transform_top_ok f g k F P F' P' ->
    top_shape F P A -> top_shape F' P' (transform_type f g k A).
Proof.
  induction A; simpl; intros f g k F P F' P' Hl Hok H; try tauto; eauto.
  - exact (proj2 Hok _ H).
  - exact (proj1 Hok _ H).
  - eapply IHA2; [exact Hl | | exact H]. eapply Hl; eauto using transform_bottom.
  - destruct H; split; eauto.
Qed.

Lemma transform_sub : forall F,
  (forall P A B, normal_sub F P A B -> forall f g k F' P',
    transform_lifts f g -> transform_top_ok f g k F P F' P' ->
    normal_sub F' P' (transform_type f g k A) (transform_type f g k B)) /\
  (forall P A B, component_sub F P A B -> forall f g k F' P',
    transform_lifts f g -> transform_top_ok f g k F P F' P' ->
    normal_sub F' P' (transform_type f g k A) (transform_type f g k B)).
Proof.
  intro F; apply normal_sub_mutind; intros.
  - constructor; intros b Hb; apply transform_components in Hb.
    destruct Hb as [a [Ha Hb] ]. eapply normal_sub_component; [eauto | exact Hb].
  - apply normal_sub_top_rule; eauto using transform_top.
  - apply normal_sub_bot_rule; eauto using transform_bottom.
  - constructor; intros c Hc; apply NS_same, transform_components; eauto.
  - eapply normal_sub_trans;
      [ constructor; intros b Hb; apply NS_same, transform_components; eauto | simpl ].
    apply normal_sub_arrow; eauto.
  - eapply normal_sub_trans;
      [ constructor; intros b Hb; apply NS_same, transform_components; eauto | simpl ].
    apply normal_sub_all; [eauto |].
    eapply H0; eauto. eapply H1; eauto using transform_bottom.
  - eapply normal_sub_trans;
      [ constructor; intros b Hb; apply NS_same, transform_components; eauto | simpl ].
    apply normal_sub_rcd; eauto.
Qed.

Definition no_indices (_ : nat) := False.
Definition marks (D : tctx) (x : atom) :=
  exists A, binds x A D /\ bottom_shape A.
Definition ctx_sub D := normal_sub (marks D) no_indices.
Definition ctx_top D := top_shape (marks D) no_indices.

Definition opened_index (U : typ) (k n : nat) :=
  match lt_eq_lt_dec n k with
  | inleft (left _) => t_tvar_b n
  | inleft (right _) => U
  | inright _ => t_tvar_b (n - 1)
  end.

Definition closed_index (k n : nat) :=
  if lt_ge_dec n k then t_tvar_b n else t_tvar_b (S n).
Definition closed_atom (x : atom) (k : nat) (y : atom) :=
  if x == y then t_tvar_b k else t_tvar_f y.

Lemma open_transform : forall A k U,
    open_typ_wrt_typ_rec k U A =
    transform_type (fun _ => t_tvar_f) (opened_index U) k A.
Proof. induction A; simpl; intros; f_equal; auto. Qed.

Lemma close_transform : forall A k x,
    close_typ_wrt_typ_rec k x A = transform_type (closed_atom x) closed_index k A.
Proof. induction A; simpl; intros; f_equal; auto. Qed.

Lemma subst_transform : forall A k x U,
    typsubst_typ U x A =
    transform_type (fun _ y => if y == x then U else t_tvar_f y)
      (fun _ => t_tvar_b) k A.
Proof. induction A; simpl; intros; f_equal; auto. Qed.

Lemma close_open_type : forall A x k,
    x \notin (typefv_typ A) ->
    close_typ_wrt_typ_rec k x (open_typ_wrt_typ_rec k (t_tvar_f x) A) = A.
Proof.
  induction A; simpl; intros x k H; try solve [f_equal; auto; apply notin_union in H; tauto].
  - destruct (lt_eq_lt_dec n k) as [ [LT|EQ] |GT]; simpl.
    + destruct (lt_ge_dec n k); [reflexivity | lia].
    + subst n; match goal with |- context[if ?d then _ else _] => destruct d as [Heq|Hneq] end; [reflexivity | exfalso; apply Hneq; reflexivity].
    + destruct (lt_ge_dec (n - 1) k); [lia | f_equal; lia].
  - match goal with |- context[if ?d then _ else _] => destruct d end; subst; [exfalso; fsetdec|reflexivity].
Qed.

Lemma close_lifts : forall x, transform_lifts (closed_atom x) closed_index.
Proof.
  intros x k F P F' P' q r [HF HP] Hqr; split.
  - intro y; specialize (HF y); unfold closed_atom in *; destruct (x == y); simpl; auto.
  - intros [|n] H; unfold closed_index; destruct (lt_ge_dec _ _) as [Hlt|Hge]; simpl in *; auto; try lia.
    all: specialize (HP n H); unfold closed_index in HP;
      destruct (lt_ge_dec n k); simpl in *; auto; lia.
Qed.

Lemma open_name_lifts : forall x, transform_lifts (fun _ => t_tvar_f) (opened_index (t_tvar_f x)).
Proof.
  intros x k F P F' P' q r [HF HP] Hqr; split; [exact HF|].
  intros [|n] H; unfold opened_index; destruct (lt_eq_lt_dec _ _) as [ [Hlt|Heq] |Hgt]; simpl in *;
    try lia; auto.
  all: specialize (HP n H); unfold opened_index in HP;
    destruct (lt_eq_lt_dec n k) as [ [Hlt'|Heq'] |Hgt']; simpl in *; try lia; auto.
  replace (n - 0) with (S (n-1)) by lia. exact HP.
Qed.

Lemma marks_cons : forall D x A y,
    marks ((x,A)::D) y <-> (x = y /\ bottom_shape A) \/ marks D y.
Proof.
  unfold marks; intros; split.
  - intros [B [Hb HB] ]; apply binds_cons_1 in Hb; destruct Hb as [ [<- <-] | Hb]; eauto.
  - intros [ [<- H] | [B [Hb HB] ] ]; eauto using binds_cons_2, binds_cons_3.
Qed.

Lemma marks_fresh : forall D x, x \notin dom D -> ~ marks D x.
Proof. unfold marks; intros D x H [A [Hbind _] ]; apply H; eauto using binds_In. Qed.

Lemma close_top_ok : forall D x A,
    x \notin dom D ->
    transform_top_ok (closed_atom x) closed_index 0
      (marks ((x,A)::D)) no_indices (marks D) (push no_indices (bottom_shape A)).
Proof.
  intros D x A Hx; split; [|intros n H; contradiction].
  intros y Hy; apply marks_cons in Hy; unfold closed_atom; destruct (x == y); simpl in *.
  - subst. destruct Hy as [ [_ Hb] | Hm]; auto. exact (False_rect _ (@marks_fresh D y Hx Hm)).
  - intuition congruence.
Qed.

Lemma open_name_top_ok : forall D x A,
    transform_top_ok (fun _ => t_tvar_f) (opened_index (t_tvar_f x)) 0
      (marks D) (push no_indices (bottom_shape A)) (marks ((x,A)::D)) no_indices.
Proof.
  intros; split.
  - intros y Hy; simpl; apply marks_cons; auto.
  - intros [|n] H; simpl in *; [|contradiction]. apply marks_cons; auto.
Qed.

Lemma subtype_close : forall D x U A B,
    x \notin dom D -> x \notin (typefv_typ A) -> x \notin (typefv_typ B) ->
    ctx_sub ((x,U)::D) (A -^ x) (B -^ x) ->
    normal_sub (marks D) (push no_indices (bottom_shape U)) A B.
Proof.
  unfold ctx_sub, open_typ_wrt_typ; intros.
  pose proof (proj1 (transform_sub _) _ _ _ H2 _ _ 0 _ _
    (@close_lifts x) (@close_top_ok D x U H)) as Hs.
  repeat rewrite <- close_transform in Hs.
  rewrite !close_open_type in Hs; auto.
Qed.

Lemma subtype_open_name : forall D x U A B,
    normal_sub (marks D) (push no_indices (bottom_shape U)) A B ->
    ctx_sub ((x,U)::D) (A -^ x) (B -^ x).
Proof.
  unfold ctx_sub, open_typ_wrt_typ; intros; rewrite !open_transform.
  eapply (proj1 (transform_sub _)); [eassumption | apply open_name_lifts | apply open_name_top_ok].
Qed.

Lemma top_close : forall D x U A,
    x \notin dom D -> x \notin (typefv_typ A) ->
    ctx_top ((x,U)::D) (A -^ x) ->
    top_shape (marks D) (push no_indices (bottom_shape U)) A.
Proof.
  unfold ctx_top, open_typ_wrt_typ; intros.
  pose proof (transform_top _ (@close_lifts x) (@close_top_ok D x U H) H1) as Hs.
  rewrite <- close_transform, close_open_type in Hs; auto.
Qed.

Lemma top_open_name : forall D x U A,
    top_shape (marks D) (push no_indices (bottom_shape U)) A ->
    ctx_top ((x,U)::D) (A -^ x).
Proof.
  unfold ctx_top, open_typ_wrt_typ; intros; rewrite open_transform.
  eapply transform_top; [apply open_name_lifts | apply open_name_top_ok | exact H].
Qed.

Lemma top_shape_dec : forall A F P,
    (forall x, {F x}+{~F x}) -> (forall n, {P n}+{~P n}) ->
    {top_shape F P A}+{~top_shape F P A}.
Proof.
  assert (HB : forall A, {bottom_shape A}+{~bottom_shape A}).
  { induction A; simpl; try tauto. all: (left; tauto) || (right; tauto) ||
    (destruct IHA1, IHA2; tauto). }
  induction A; simpl; intros F P HF HP; try (left; tauto); try (right; tauto); auto.
  - apply IHA2; auto. intros [|n]; simpl; auto.
  - destruct (IHA1 F P HF HP), (IHA2 F P HF HP); tauto.
Qed.

Fixpoint type_scope (k : nat) (F : atom -> Prop) (A : typ) : Prop :=
  match A with
  | t_tvar_b n => n < k
  | t_tvar_f x => F x
  | t_forall B C => type_scope k F B /\ type_scope (S k) F C
  | t_arrow B C | t_and B C => type_scope k F B /\ type_scope k F C
  | t_rcd _ B => type_scope k F B
  | _ => True
  end.

Lemma type_scope_mono : forall A k F k' F',
    k <= k' -> (forall x, F x -> F' x) ->
    type_scope k F A -> type_scope k' F' A.
Proof.
  induction A; simpl; intros; try lia; intuition eauto using le_n_S.
Qed.

Lemma type_scope_open : forall A k F F' U,
    (forall x, F x -> F' x) -> type_scope 0 F' U ->
    type_scope (S k) F A -> type_scope k F' (open_typ_wrt_typ_rec k U A).
Proof.
  induction A; simpl; intros; intuition eauto.
  destruct (lt_eq_lt_dec n k) as [ [Hlt|Heq] |Hgt]; simpl; try lia.
  eapply type_scope_mono; [| | eassumption]; eauto with arith.
Qed.

Lemma type_scope_open_inv : forall A k F F' U,
    (forall x, x \in (typefv_typ A) -> F' x -> F x) ->
    type_scope k F' (open_typ_wrt_typ_rec k U A) -> type_scope (S k) F A.
Proof.
  induction A; simpl; intros k F F' U HF H; try tauto.
  all: try solve [eapply IHA; [|exact H]; eauto].
  all: try (destruct H as [H1 H2]; split;
    [eapply (IHA1 k F F' U); [|exact H1] | eapply (IHA2 _ F F' U); [|exact H2] ]).
  all: try solve [intros x Hx HFx; apply HF; [fsetdec | exact HFx] ].
  - destruct (lt_eq_lt_dec n k) as [ [Hlt|Heq] |Hgt]; simpl in H; lia.
  - eapply HF; eauto; fsetdec.
Qed.

Definition in_ctx (D : tctx) (x : atom) := x \in dom D.
Definition wf_type D := type_scope 0 (in_ctx D).

Lemma in_ctx_cons : forall D x A y,
    in_ctx ((x,A)::D) y <-> y = x \/ in_ctx D y.
Proof. unfold in_ctx; simpl; intros; fsetdec. Qed.

Lemma wf_type_expand : forall D D' A,
    (forall x, in_ctx D x -> in_ctx D' x) -> wf_type D A -> wf_type D' A.
Proof. unfold wf_type; eauto using type_scope_mono. Qed.

Lemma twell_scope : forall D A, TWell D A -> wf_type D A.
Proof.
  intros D A H; induction H; try (unfold wf_type in *; simpl; tauto).
  - exact (@binds_In _ _ _ _ H).
  - unfold wf_type in *; simpl; split; auto.
    pick fresh x for (L \u dom D \u (typefv_typ B)).
    specialize (H1 x ltac:(fsetdec)).
    unfold open_typ_wrt_typ in H1.
    eapply type_scope_open_inv; [|exact H1].
    intros y Hy; rewrite in_ctx_cons; intros [->|Hin]; auto; fsetdec.
Qed.

Lemma size_open_type_name : forall A k x,
    size_typ (open_typ_wrt_typ_rec k (t_tvar_f x) A) = size_typ A.
Proof.
  induction A; simpl; intros; try (rewrite ?IHA, ?IHA1, ?IHA2; reflexivity).
  destruct (lt_eq_lt_dec n k) as [ [Hlt|Heq] |Hgt]; reflexivity.
Qed.

Lemma scope_twell : forall A D, wf_type D A -> TWell D A.
Proof.
  assert (Hw : forall n A D, size_typ A <= n -> wf_type D A -> TWell D A).
  { induction n as [n IH] using lt_wf_ind; intros A D Hn Hw.
    unfold wf_type in Hw; destruct A; simpl in *; try lia; try solve [constructor].
    - destruct (@binds_In_inv _ _ _ Hw) as [B HB]; eauto using TW_var.
    - destruct Hw as [H1 H2]. eapply TW_all with (L := empty).
      + eapply (IH (size_typ A1)); eauto; lia.
      + intros x _. unfold open_typ_wrt_typ.
        eapply (IH (size_typ A2)); [lia | rewrite size_open_type_name; lia | ].
        unfold wf_type. eapply type_scope_open; [| | exact H2].
        * intros y Hy; apply in_ctx_cons; auto.
        * simpl; apply in_ctx_cons; auto.
    - destruct Hw; constructor; [eapply (IH (size_typ A1)) | eapply (IH (size_typ A2))]; eauto; lia.
    - destruct Hw; constructor; [eapply (IH (size_typ A1)) | eapply (IH (size_typ A2))]; eauto; lia.
    - constructor; eapply (IH (size_typ A)); eauto; lia. }
  eauto.
Qed.

Definition index_scope := type_scope 0 (fun _ => True).

Lemma scope_lc_typ : forall A, index_scope A -> lc_typ A.
Proof.
  assert (Hw : forall n A, size_typ A <= n -> index_scope A -> lc_typ A).
  { induction n as [n IH] using lt_wf_ind; intros A Hn Hw.
    unfold index_scope in *; destruct A; simpl in *; try lia; try solve [constructor].
    - destruct Hw as [H1 H2]; constructor.
      + eapply (IH (size_typ A1)); eauto; lia.
      + intro x; unfold open_typ_wrt_typ.
        eapply (IH (size_typ A2)); [lia | rewrite size_open_type_name; lia | ].
        eapply type_scope_open; [intros; exact I | exact I | exact H2].
    - destruct Hw; constructor; [eapply (IH (size_typ A1)) | eapply (IH (size_typ A2))]; eauto; lia.
    - destruct Hw; constructor; [eapply (IH (size_typ A1)) | eapply (IH (size_typ A2))]; eauto; lia.
    - constructor; eapply (IH (size_typ A)); eauto; lia. }
  eauto.
Qed.

Lemma wf_type_lc : forall D A, wf_type D A -> lc_typ A.
Proof. intros; apply scope_lc_typ; eapply type_scope_mono; [apply le_n | intros; exact I | eassumption]. Qed.

Lemma lc_typ_scope : forall A, lc_typ A -> index_scope A.
Proof.
  intros A H; induction H; unfold index_scope in *; simpl; try tauto.
  split; auto.
  pick fresh x for ((typefv_typ B)).
  unfold open_typ_wrt_typ in H1.
  eapply type_scope_open_inv; [|exact (H1 x)]; auto.
Qed.

(* Splitting implements the same decomposition one binary step at a time. *)
Fixpoint split_type (A : typ) : option (typ * typ) :=
  match A with
  | t_and B C => Some (B,C)
  | t_arrow B C =>
      option_map (fun '(X,Y) => (t_arrow B X,t_arrow B Y)) (split_type C)
  | t_forall B C =>
      option_map (fun '(X,Y) => (t_forall B X,t_forall B Y)) (split_type C)
  | t_rcd l B =>
      option_map (fun '(X,Y) => (t_rcd l X,t_rcd l Y)) (split_type B)
  | _ => None
  end.

Lemma split_open_name : forall A k x,
    split_type (open_typ_wrt_typ_rec k (t_tvar_f x) A) =
    option_map (fun '(B,C) => (open_typ_wrt_typ_rec k (t_tvar_f x) B,
                              open_typ_wrt_typ_rec k (t_tvar_f x) C)) (split_type A).
Proof.
  induction A; simpl; intros; rewrite ?IHA, ?IHA1, ?IHA2; auto.
  - destruct (lt_eq_lt_dec n k) as [ [Hlt|Heq] |Hgt]; reflexivity.
  - destruct (split_type A2) as [ [B C]|]; reflexivity.
  - destruct (split_type A2) as [ [B C]|]; reflexivity.
  - destruct (split_type A) as [ [B C]|]; reflexivity.
Qed.

Lemma split_scope : forall A B C k F,
    split_type A = Some (B,C) ->
    (type_scope k F A <-> type_scope k F B /\ type_scope k F C).
Proof.
  induction A; simpl; intros B C k F H; try discriminate.
  all: try (destruct (split_type A2) as [ [U V]|] eqn:E;
    inversion H; subst; simpl; rewrite IHA2 with (B := U) (C := V) by reflexivity; tauto).
  all: try (destruct (split_type A) as [ [U V]|] eqn:E;
    inversion H; subst; simpl; apply IHA with (B := U) (C := V); reflexivity).
  inversion H; subst; tauto.
Qed.

Lemma split_size : forall A B C, split_type A = Some (B,C) ->
    size_typ B < size_typ A /\ size_typ C < size_typ A.
Proof.
  induction A; simpl; intros U V H; try discriminate.
  all: try (destruct (split_type A2) as [ [B C]|]; inversion H; subst;
    specialize (IHA2 _ _ eq_refl); simpl; lia).
  all: try (destruct (split_type A) as [ [B C]|]; inversion H; subst;
    specialize (IHA _ _ eq_refl); simpl; lia).
  inversion H; subst; simpl; lia.
Qed.

Lemma split_components : forall A B C, split_type A = Some (B,C) ->
    components A = components B ++ components C.
Proof.
  induction A; simpl; intros U V H; try discriminate.
  all: try solve [destruct (split_type A2) as [ [B C]|]; inversion H; subst;
    simpl; rewrite (IHA2 _ _ eq_refl), map_app; reflexivity].
  all: try solve [destruct (split_type A) as [ [B C]|]; inversion H; subst;
    simpl; rewrite (IHA _ _ eq_refl), map_app; reflexivity].
  inversion H; reflexivity.
Qed.

Lemma spl_compute : forall A B C, spl A B C -> split_type A = Some (B,C).
Proof.
  intros A B C H; induction H; simpl; rewrite ?IHspl; auto.
  destruct (split_type B) as [ [U V]|] eqn:E.
  - pick fresh x for (L \u typefv_typ U \u typefv_typ V \u typefv_typ C1 \u typefv_typ C2).
    specialize (H1 x ltac:(fsetdec)).
    unfold open_typ_wrt_typ in H1. rewrite split_open_name, E in H1.
    injection H1 as H1 H2.
    apply (f_equal (close_typ_wrt_typ_rec 0 x)) in H1, H2.
    repeat rewrite close_open_type in H1, H2 by fsetdec.
    subst; reflexivity.
  - pick fresh x for L. specialize (H1 x ltac:(fsetdec)).
    unfold open_typ_wrt_typ in H1. rewrite split_open_name, E in H1. discriminate.
Qed.

Lemma compute_spl : forall n A B C, size_typ A <= n ->
    index_scope A -> split_type A = Some (B,C) -> spl A B C.
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros A B C Hn HA H; unfold index_scope in HA; destruct A; simpl in *; try discriminate.
  - destruct (split_type A2) as [ [U V]|] eqn:E; inversion H; subst.
    destruct HA as [H1 H2]. apply Sp_all with (L := empty); [auto using scope_lc_typ |].
    intros x _. unfold open_typ_wrt_typ.
    eapply (IH (size_typ A2)); [lia | rewrite size_open_type_name; lia | | rewrite split_open_name, E; reflexivity].
    apply type_scope_open with (F := fun _ => True); auto; exact I.
  - destruct (split_type A2) as [ [U V]|] eqn:E; inversion H; subst.
    destruct HA; apply Sp_arrow; [auto using scope_lc_typ | eapply (IH (size_typ A2)); eauto; lia].
  - inversion H; subst; destruct HA; constructor; auto using scope_lc_typ.
  - destruct (split_type A) as [ [U V]|] eqn:E; inversion H; subst.
    apply Sp_rcd; eapply (IH (size_typ A)); eauto; lia.
Qed.

Lemma ord_compute : forall A, ord A -> split_type A = None.
Proof.
  intros A H; induction H; simpl; rewrite ?IHord; auto.
  pick fresh x for L. specialize (H1 x ltac:(fsetdec)).
  unfold open_typ_wrt_typ in H1. rewrite split_open_name in H1.
  destruct (split_type B) as [ [U V]|]; auto; discriminate.
Qed.

Lemma compute_ord : forall n A, size_typ A <= n ->
    index_scope A -> split_type A = None -> ord A.
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros A Hn HA H; unfold index_scope in HA; destruct A; simpl in *;
    try discriminate; try lia; try solve [constructor].
  - destruct (split_type A2) as [ [U V]|] eqn:E; try discriminate.
    destruct HA as [H1 H2]. apply O_all with (L := empty); [auto using scope_lc_typ |].
    intros x _. unfold open_typ_wrt_typ.
    eapply (IH (size_typ A2)); [lia | rewrite size_open_type_name; lia | | rewrite split_open_name, E; reflexivity].
    apply type_scope_open with (F := fun _ => True); auto; exact I.
  - destruct (split_type A2) as [ [U V]|] eqn:E; try discriminate.
    destruct HA; apply O_arrow; [auto using scope_lc_typ | eapply (IH (size_typ A2)); eauto; lia].
  - destruct (split_type A) as [ [U V]|] eqn:E; try discriminate.
    apply O_rcd; eapply (IH (size_typ A)); eauto; lia.
Qed.

Lemma ord_or_split : forall A, lc_typ A -> ord A \/ exists B C, spl A B C.
Proof.
  intros A HA; pose proof (lc_typ_scope HA).
  destruct (split_type A) as [ [B C]|] eqn:E.
  - right; exists B,C; eapply (compute_spl (n := size_typ A)); eauto.
  - left; eapply (compute_ord (n := size_typ A)); eauto.
Qed.

Lemma components_single : forall A, split_type A = None -> components A = [A].
Proof.
  induction A; simpl; intros H; auto; try discriminate.
  all: try solve [destruct (split_type A2) as [ [U V]|]; try discriminate; rewrite IHA2; auto].
  destruct (split_type A) as [ [U V]|]; try discriminate; rewrite IHA; auto.
Qed.

Lemma bottom_flag : forall A, botLike A -> bottom_shape A.
Proof. intros A H; induction H; simpl; auto. Qed.

Lemma flag_bottom : forall A, lc_typ A -> bottom_shape A -> botLike A.
Proof.
  induction A; simpl; intros H Hb; try contradiction; auto using BL_bot.
  inversion H; subst; destruct Hb; eauto using BL_andl, BL_andr.
Qed.

Lemma topLike_regular : forall D A, topLike D A -> TCWell D /\ wf_type D A.
Proof.
  intros D A H; induction H; try solve [unfold wf_type in *; simpl; intuition eauto using twell_scope].
  - destruct IHtopLike as [HT HW]; split; auto.
    split; auto. exact (twell_scope H).
  - pick fresh x for (L \u dom D \u typefv_typ B).
    destruct (H0 x ltac:(fsetdec)) as [HT HW].
    inversion HT; subst; split; auto.
    unfold wf_type in *; simpl; split; [apply twell_scope; assumption |].
    eapply type_scope_open_inv; [|exact HW].
    intros y Hy; rewrite in_ctx_cons; intros [->|Hin]; auto; fsetdec.
  - split; auto. exact (@binds_In _ _ _ _ H0).
Qed.

Lemma topLike_flag : forall D A, topLike D A -> ctx_top D A.
Proof.
  intros D A H; induction H; unfold ctx_top in *; simpl; intuition eauto.
  - pick fresh x for (L \u dom D \u typefv_typ B).
    eapply (@top_close D x A B); [fsetdec | fsetdec | exact (H0 x ltac:(fsetdec))].
  - unfold marks; eauto using bottom_flag.
Qed.

Lemma tcwell_uniq : forall D, TCWell D -> uniq D.
Proof. intros D H; destruct H; auto using uniq. Qed.

Lemma tcwell_binds : forall D x A, TCWell D -> binds x A D -> wf_type D A.
Proof.
  intros D x A HD; induction HD; intros Hb; [inversion Hb|].
  apply binds_cons_1 in Hb. destruct Hb as [ [<- <-] | Hb].
  all: eapply wf_type_expand with (D := D); [intros; apply in_ctx_cons; auto | eauto using twell_scope].
Qed.

Lemma flag_topLike : forall n D A, size_typ A <= n ->
    TCWell D -> wf_type D A -> ctx_top D A -> topLike D A.
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros D A Hn HD HW HT; unfold wf_type, ctx_top in *;
    destruct A; simpl in *; try contradiction.
  - destruct HT as [B [HB Hbot] ]; eapply TL_var; eauto.
    apply flag_bottom; auto. eapply wf_type_lc, tcwell_binds; eassumption.
  - apply TL_top; auto.
  - destruct HW as [H1 H2]. eapply TL_all with (L := dom D).
    intros x Hx. eapply (IH (size_typ A2)); [lia | unfold open_typ_wrt_typ; rewrite size_open_type_name; lia | | |].
    + apply TCW_cons; auto using scope_twell, uniq_cons_3, tcwell_uniq.
    + unfold wf_type, open_typ_wrt_typ. eapply type_scope_open; [| | exact H2].
      * intros y Hy; apply in_ctx_cons; auto.
      * simpl; apply in_ctx_cons; auto.
    + apply top_open_name; auto.
  - destruct HW; constructor; auto using scope_twell. eapply (IH (size_typ A2)); eauto; lia.
  - destruct HW, HT; constructor; [eapply (IH (size_typ A1)) | eapply (IH (size_typ A2))]; eauto; lia.
  - constructor; eapply (IH (size_typ A)); eauto; lia.
Qed.

Lemma ctx_sub_refl : forall D A, ctx_sub D A A.
Proof. exact (fun D => normal_sub_refl (marks D) no_indices). Qed.

Lemma ctx_sub_trans : forall D A B C, ctx_sub D A B -> ctx_sub D B C -> ctx_sub D A C.
Proof. unfold ctx_sub; eauto using normal_sub_trans. Qed.

Lemma ctx_sub_l : forall D A B, ctx_sub D (t_and A B) A.
Proof. intros; apply normal_sub_left. Qed.

Lemma ctx_sub_r : forall D A B, ctx_sub D (t_and A B) B.
Proof. intros; apply normal_sub_right. Qed.

Lemma wf_all_open : forall D X U A,
    wf_type D (t_forall U A) -> wf_type ((X,U)::D) (A -^ X).
Proof.
  unfold wf_type, open_typ_wrt_typ; simpl; intros D X U A [Hu HA].
  eapply type_scope_open; [| |exact HA].
  - intros; apply in_ctx_cons; auto.
  - simpl; apply in_ctx_cons; auto.
Qed.

Lemma wf_all_close : forall D X U A,
    X \notin typefv_typ A -> wf_type D U ->
    wf_type ((X,U)::D) (A -^ X) -> wf_type D (t_forall U A).
Proof.
  unfold wf_type, open_typ_wrt_typ; simpl; intros; split; auto.
  eapply type_scope_open_inv; [|eassumption].
  intros y Hy; rewrite in_ctx_cons; intros [->|Hin]; auto; fsetdec.
Qed.

Lemma ctx_sub_spl : forall D A B C, spl A B C ->
    ctx_sub D A B /\ ctx_sub D A C.
Proof.
  unfold ctx_sub; intros D A B C H; apply spl_compute, split_components in H; split.
  - eapply normal_sub_source with (A := B); [intros; rewrite H; apply in_or_app; eauto | apply normal_sub_refl].
  - eapply normal_sub_source with (A := C); [intros; rewrite H; apply in_or_app; eauto | apply normal_sub_refl].
Qed.

Lemma ctx_sub_spl_join : forall D A B C E, spl A B C ->
    ctx_sub D E B -> ctx_sub D E C -> ctx_sub D E A.
Proof.
  unfold ctx_sub; intros D A B C E HS HB HC.
  apply spl_compute, split_components in HS; constructor; rewrite HS; intros; component_in;
    eauto using normal_sub_component.
Qed.

Lemma algo_sub_sound : forall D A B, algo_sub D A B -> ctx_sub D A B.
Proof.
  intros D A B H; induction H.
  - apply ctx_sub_refl.
  - apply ctx_sub_refl.
  - apply normal_sub_top_rule; apply topLike_flag; assumption.
  - apply normal_sub_bot_rule; exact I.
  - eapply ctx_sub_trans; eauto using ctx_sub_l.
  - eapply ctx_sub_trans; eauto using ctx_sub_r.
  - apply normal_sub_arrow; auto.
  - apply normal_sub_all; [assumption|].
    pick fresh x for (L \u dom D \u typefv_typ A2 \u typefv_typ B2).
    eapply (@subtype_close D x B1 A2 B2); [fsetdec | fsetdec | fsetdec | exact (H2 x ltac:(fsetdec))].
  - apply normal_sub_rcd; auto.
  - eapply ctx_sub_spl_join; eauto.
Qed.

Lemma algo_sub_scope : forall D A B, algo_sub D A B -> TCWell D /\ wf_type D A /\ wf_type D B.
Proof.
  intros D A B H; induction H.
  all: try solve [intuition eauto using twell_scope, topLike_regular; try exact I].
  all: try solve [destruct IHalgo_sub as [HT [HA HB] ]; repeat split; auto; apply twell_scope; assumption].
  all: try solve [destruct IHalgo_sub1 as [HT [HA HB] ]; destruct IHalgo_sub2 as [_ [HC HD] ];
    repeat split; auto].
  - destruct (topLike_regular H1); intuition eauto using twell_scope.
  - destruct IHalgo_sub as [HT [HA HB] ].
    pick fresh x for (L \u typefv_typ A2 \u typefv_typ B2).
    destruct (H2 x ltac:(fsetdec)) as [_ [HC HD] ].
    split; [assumption|split].
    + eapply wf_all_close with (X := x); [fsetdec | exact HB |].
      eapply wf_type_expand; [|exact HC].
      intros y; rewrite !in_ctx_cons; tauto.
    + eapply wf_all_close with (X := x); [fsetdec | exact HA | exact HD].
  - destruct IHalgo_sub1 as [HT [HA HB] ]; destruct IHalgo_sub2 as [_ [_ HC] ].
    split; auto; split; auto. eapply split_scope; [eapply spl_compute; eassumption | auto].
Qed.

Lemma marks_nil : forall x, ~ marks nil x.
Proof. intros x [A [H _] ]; inversion H. Qed.

Lemma ctx_top_dec_nil : forall A, {ctx_top nil A}+{~ctx_top nil A}.
Proof.
  intro A; apply top_shape_dec; [right; apply marks_nil|right; exact (fun f => f)].
Qed.

Lemma ctx_flag_topLike : forall D A, TCWell D -> wf_type D A -> ctx_top D A -> topLike D A.
Proof. intros; eapply (flag_topLike (n := size_typ A)); eauto. Qed.

Lemma component_sub_and_source : forall F P A B b, component_sub F P (t_and A B) b ->
    component_sub F P A b \/ component_sub F P B b.
Proof. intros; inversion H; subst; simpl in *; component_in; intuition eauto with task. Qed.

Lemma sub_component_ord : forall F P A B,
    ord B -> (normal_sub F P A B <-> component_sub F P A B).
Proof.
  intros F P A B H; pose proof (components_single B (ord_compute H)) as E.
  split; intros HH.
  - eapply normal_sub_component; [exact HH|rewrite E; simpl; auto].
  - constructor; rewrite E; intros b [<-|[] ]; auto.
Qed.

Definition head_sub F P (A B : typ) : Prop :=
  match A, B with
  | t_arrow A1 A2, t_arrow B1 B2 =>
      normal_sub F P B1 A1 /\ normal_sub F P A2 B2
  | t_forall A1 A2, t_forall B1 B2 =>
      normal_sub F P B1 A1 /\ normal_sub F (push P (bottom_shape B1)) A2 B2
  | t_rcd l A2, t_rcd m B2 => l = m /\ normal_sub F P A2 B2
  | _, _ => A = B
  end.

Lemma head_sub_refl : forall F P A, head_sub F P A A.
Proof. destruct A; simpl; intuition auto using normal_sub_refl. Qed.

Lemma component_sub_inversion : forall F P A B, component_sub F P A B ->
    top_shape F P B \/ bottom_shape A \/
    exists a, In a (components A) /\ head_sub F P a B.
Proof.
  intros F P A B H; destruct H; auto.
  all: try solve [right; right; eexists; split; [eassumption | apply head_sub_refl] ].
  all: right; right; eexists; split; [eassumption | simpl; auto].
Qed.

Lemma algo_bottom : forall D A B, TCWell D -> wf_type D A -> wf_type D B ->
    ord B -> bottom_shape A -> algo_sub D A B.
Proof.
  intros D A; induction A; simpl; intros B HD HA HB HO H; try contradiction.
  - apply S_bot; auto using scope_twell.
  - destruct HA, H; eauto using S_andl, S_andr, scope_twell.
Qed.

Lemma algo_head : forall n D A B a,
    (forall m, m < n -> forall D A B, size_typ A + size_typ B <= m ->
       TCWell D -> wf_type D A -> wf_type D B -> ctx_sub D A B -> algo_sub D A B) ->
    size_typ A + size_typ B <= n ->
    TCWell D -> wf_type D A -> wf_type D B -> ord B ->
    In a (components A) -> head_sub (marks D) no_indices a B -> algo_sub D A B.
Proof.
  intros n D A; induction A; simpl;
    intros B a IH Hn HD HA HB HO Hin HH.
  all: try solve [
    destruct Hin as [<-|[] ]; destruct B; simpl in HH; try discriminate;
    inversion HH; subst;
    first [solve [apply S_var; auto using scope_twell] |
           solve [apply S_int; auto] |
           solve [apply S_top; auto using scope_twell, TL_top] |
           solve [apply S_bot; auto using scope_twell] |
           unfold wf_type in HA; simpl in HA; lia] ].
  - apply in_map_iff in Hin; destruct Hin as [b [<- Hin] ].
    destruct B; simpl in HH; try discriminate.
    destruct HA as [HA1 HA2], HB as [HB1 HB2], HH as [Hdom Hcod].
    inversion HO; subst; apply S_all with (L := L \u dom D).
    + intros; apply H2; fsetdec.
    + eapply (IH (size_typ B1 + size_typ A1)); eauto; simpl in *; lia.
    + intros x Hx.
      eapply (IH (size_typ A2 + size_typ B2));
        [simpl in Hn; lia | unfold open_typ_wrt_typ; rewrite !size_open_type_name; lia | | | |].
      * apply TCW_cons; auto using scope_twell.
        apply uniq_cons_3; auto using tcwell_uniq; fsetdec.
      * eapply wf_all_open with (U := B1); split; auto.
      * eapply wf_all_open with (U := B1); split; auto.
      * apply subtype_open_name. eapply normal_sub_trans; eauto using normal_sub_select.
  - apply in_map_iff in Hin; destruct Hin as [b [<- Hin] ].
    destruct B; simpl in HH; try discriminate.
    destruct HA, HB, HH. apply S_arrow; [inversion HO; assumption | |].
    + eapply (IH (size_typ B1 + size_typ A1)); eauto; simpl in *; lia.
    + eapply (IH (size_typ A2 + size_typ B2)); [simpl in Hn; lia | lia | exact HD | assumption | assumption |].
      eapply normal_sub_trans; [apply normal_sub_select; exact Hin | assumption].
  - apply in_app_or in Hin; destruct HA, Hin.
    + apply S_andl; auto using scope_twell. eapply IHA1; eauto; lia.
    + apply S_andr; auto using scope_twell. eapply IHA2; eauto; lia.
  - apply in_map_iff in Hin; destruct Hin as [b [<- Hin] ].
    destruct B; simpl in HH; try discriminate. destruct HH as [<- Hs].
    apply S_rcd; [inversion HO; assumption |].
    eapply (IH (size_typ A + size_typ B)); [simpl in Hn; lia | lia | exact HD | assumption | assumption |].
      eapply normal_sub_trans; [apply normal_sub_select; exact Hin | assumption].
Qed.

Lemma algo_sub_complete : forall n D A B, size_typ A + size_typ B <= n ->
    TCWell D -> wf_type D A -> wf_type D B -> ctx_sub D A B -> algo_sub D A B.
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros D A B Hn HD HA HB HS.
  destruct (ord_or_split (@wf_type_lc D B HB)) as [Hord|[L [R Hspl] ] ].
  - apply (@sub_component_ord (marks D) no_indices A B Hord) in HS.
    destruct (component_sub_inversion HS) as [Htop|[Hbot|[a [Hin HH] ] ] ].
    + apply S_top; eauto using scope_twell, ctx_flag_topLike.
    + eauto using algo_bottom.
    + eapply algo_head; eauto.
  - pose proof (spl_compute Hspl) as E.
    pose proof (@split_size B L R E) as [HL HR].
    destruct (proj1 (@split_scope B L R 0 (in_ctx D) E) HB) as [HWL HWR].
    destruct (@ctx_sub_spl D B L R Hspl) as [HSL HSR].
    eapply S_and; [eassumption | eapply (IH (size_typ A + size_typ L)) |
        eapply (IH (size_typ A + size_typ R))]; eauto using ctx_sub_trans; lia.
Qed.

Lemma ctx_sub_algo : forall D A B,
    TCWell D -> wf_type D A -> wf_type D B -> ctx_sub D A B -> algo_sub D A B.
Proof. intros; eapply (algo_sub_complete (n := size_typ A + size_typ B)); eauto. Qed.

(* Syntactic substitution and the two binder indices. *)
Lemma type_open_above : forall A k j F U,
    type_scope k F A -> k <= j -> open_typ_wrt_typ_rec j U A = A.
Proof.
  induction A; simpl; intros k j F U H Hj;
    try solve [f_equal; intuition eauto using le_n_S].
  destruct (lt_eq_lt_dec n j) as [ [Hlt|Heq] |Hgt]; auto; lia.
Qed.

Lemma type_subst_scope : forall A k F F' X U,
    (forall Y, F Y -> type_scope 0 F' (typsubst_typ U X (t_tvar_f Y))) ->
    type_scope k F A -> type_scope k F' (typsubst_typ U X A).
Proof.
  induction A; simpl; intros; intuition eauto.
  eapply type_scope_mono; [apply Nat.le_0_l | | apply H; eassumption]; auto.
Qed.

Lemma type_subst_fresh : forall A X U, X \notin typefv_typ A -> typsubst_typ U X A = A.
Proof.
  induction A; simpl; intros; try solve [f_equal; eauto; apply notin_union in H; tauto].
  match goal with |- context[if ?d then _ else _] => destruct d end; auto; subst; fsetdec.
Qed.

Lemma type_subst_open : forall A k X U V,
    index_scope U ->
    typsubst_typ U X (open_typ_wrt_typ_rec k V A) =
    open_typ_wrt_typ_rec k (typsubst_typ U X V) (typsubst_typ U X A).
Proof.
  induction A; simpl; intros; try solve [f_equal; eauto].
  - destruct (lt_eq_lt_dec n k) as [ [Hlt|Heq] |Hgt]; reflexivity.
  - match goal with |- context[if ?d then _ else _] => destruct d end; auto.
    symmetry; eapply type_open_above; [exact H|lia].
Qed.

Lemma type_subst_intro : forall A X U,
    index_scope U -> X \notin typefv_typ A ->
    typsubst_typ U X (A -^ X) = A ^-^ U.
Proof.
  unfold open_typ_wrt_typ; intros; rewrite type_subst_open by assumption.
  rewrite (@type_subst_fresh A X U H0); simpl.
  match goal with |- context[if ?d then _ else _] => destruct d end; congruence.
Qed.

Lemma top_index_mono : forall A k F P P',
    type_scope k (fun _ => True) A ->
    (forall n, n < k -> P n -> P' n) ->
    top_shape F P A -> top_shape F P' A.
Proof.
  induction A; simpl; intros; intuition eauto.
  eapply IHA2; [eassumption | | eassumption].
  intros [|n]; simpl; auto with arith.
Qed.

Lemma type_subst_lifts : forall X U,
    index_scope U ->
    transform_lifts (fun _ Y => if Y == X then U else t_tvar_f Y) (fun _ => t_tvar_b).
Proof.
  intros X U HU k F P F' P' q r [HF HP] Hqr; split.
  - intros Y H; specialize (HF Y H); destruct (Y == X); simpl in *; auto.
    eapply top_index_mono; [exact HU | intros; lia | exact HF].
  - intros [|n] H; [exact (Hqr H) | exact (HP n H)].
Qed.

Lemma ctx_sub_subst : forall D D' X U A B,
    index_scope U -> ctx_sub D A B ->
    (forall Y, marks D Y -> ctx_top D' (typsubst_typ U X (t_tvar_f Y))) ->
    ctx_sub D' (typsubst_typ U X A) (typsubst_typ U X B).
Proof.
  unfold ctx_sub, ctx_top; intros D D' X U A B HU HS HT.
  rewrite (subst_transform A 0 X U), (subst_transform B 0 X U).
  eapply (proj1 (transform_sub _)); [exact HS | apply type_subst_lifts; auto |].
  split; auto.
Qed.

Lemma ctx_top_subst : forall D D' X U A,
    index_scope U -> ctx_top D A ->
    (forall Y, marks D Y -> ctx_top D' (typsubst_typ U X (t_tvar_f Y))) ->
    ctx_top D' (typsubst_typ U X A).
Proof.
  unfold ctx_top; intros D D' X U A HU HS HT.
  rewrite (subst_transform A 0 X U).
  eapply transform_top; [apply type_subst_lifts; auto | | exact HS]. split; auto.
Qed.

Lemma bottom_subst : forall X U A, bottom_shape A -> bottom_shape (typsubst_typ U X A).
Proof. intros; rewrite (subst_transform A 0 X U); auto using transform_bottom. Qed.

Lemma spl_subst : forall X U A B C,
    index_scope U -> index_scope A -> spl A B C -> spl (typsubst_typ U X A) (typsubst_typ U X B) (typsubst_typ U X C).
Proof.
  intros X U A B C HU HA HS; apply spl_compute in HS.
  assert (HS' : forall A B C, split_type A = Some (B,C) ->
      split_type (typsubst_typ U X A) = Some (typsubst_typ U X B,typsubst_typ U X C)).
  { clear A B C HS HA; induction A; simpl; intros B C H; try discriminate.
    all: try solve [destruct (split_type A2) as [ [B' C']|] eqn:E;
      inversion H; subst; rewrite (IHA2 _ _ eq_refl); reflexivity].
    all: try solve [destruct (split_type A) as [ [B' C']|] eqn:E;
      inversion H; subst; rewrite (IHA _ _ eq_refl); reflexivity].
    inversion H; reflexivity. }
  eapply (compute_spl (n := size_typ (typsubst_typ U X A))); [lia | | auto].
  eapply type_subst_scope; [| exact HA].
  intros Y _. simpl. match goal with |- context[if ?d then _ else _] => destruct d end; auto. exact I.
Qed.

Lemma index_scope_subst : forall A X U,
    index_scope A -> index_scope U -> index_scope (typsubst_typ U X A).
Proof.
  intros; apply type_subst_scope with (F := fun _ => True); auto.
  intros y _; simpl; match goal with |- context[if ?d then _ else _] => destruct d end; auto; exact I.
Qed.

Lemma spl_lc : forall A B C, spl A B C -> index_scope A.
Proof.
  intros A B C H; induction H.
  - split; [apply lc_typ_scope; assumption | assumption].
  - split; [apply lc_typ_scope; assumption |].
    pick fresh x for L. unfold open_typ_wrt_typ in H1.
    eapply type_scope_open_inv; [|exact (H1 x ltac:(fsetdec))]; auto.
  - assumption.
  - split; apply lc_typ_scope; assumption.
Qed.

Lemma disjoint_scope : forall D A B, disjoint D A B -> wf_type D A /\ wf_type D B.
Proof.
  intros D A B H; induction H.
  all: try solve [intuition auto using twell_scope].
  all: try solve [match goal with Ht : topLike _ _ |- _ => destruct (topLike_regular Ht) end;
    intuition auto using twell_scope].
  all: try solve [destruct IHdisjoint; split; assumption].
  all: try solve [match goal with Hs : algo_sub _ _ _ |- _ => destruct (algo_sub_scope Hs) as [_ [_ ?] ] end;
    split; auto; eapply binds_In; eassumption].
  - pick fresh x for (L \u typefv_typ B1 \u typefv_typ B2).
    destruct (H2 x ltac:(fsetdec)) as [HA HB]; split.
    + eapply wf_all_close with (X := x); [fsetdec | apply twell_scope; eassumption |].
      eapply wf_type_expand; [|exact HA]. intros y; rewrite !in_ctx_cons; tauto.
    + eapply wf_all_close with (X := x); [fsetdec | apply twell_scope; eassumption |].
      eapply wf_type_expand; [|exact HB]. intros y; rewrite !in_ctx_cons; tauto.
  - destruct IHdisjoint1, IHdisjoint2; split; auto.
    eapply split_scope; eauto using spl_compute.
  - destruct IHdisjoint1, IHdisjoint2; split; auto.
    eapply split_scope; eauto using spl_compute.
Qed.

Definition rigid_head A : Prop :=
  match A with
  | t_int | t_arrow _ _ | t_forall _ _ | t_rcd _ _ => True
  | _ => False
  end.

(* A type argument satisfying an exclusion can instantiate a bottom-bound
   variable only at a top-like type. Keep this part of disjointness through
   substitution. Runtime merges do not require disjointness. *)
Inductive compatible (D : tctx) : typ -> typ -> Prop :=
| K_rigid : forall A B, rigid_head A -> rigid_head B -> compatible D A B
| K_top_l : forall A B, ctx_top D A -> compatible D A B
| K_top_r : forall A B, ctx_top D B -> compatible D A B
| K_bind : forall X A, binds X A D -> compatible D (t_tvar_f X) A
| K_sym : forall A B, compatible D A B -> compatible D B A
| K_widen : forall A B C, compatible D A B -> ctx_sub D B C -> compatible D A C
| K_split : forall A B C E, spl A B C -> compatible D B E -> compatible D C E -> compatible D A E.

Local Hint Constructors compatible : task.

Lemma disjoint_compatible : forall D A B, disjoint D A B -> compatible D A B.
Proof.
  intros D A B H; induction H.
  - inversion H2; subst; apply K_rigid; exact I.
  - apply K_top_l; apply topLike_flag; assumption.
  - apply K_top_r; apply topLike_flag; assumption.
  - apply K_rigid; exact I.
  - apply K_rigid; exact I.
  - apply K_rigid; exact I.
  - eapply K_widen; [apply K_bind; eassumption | apply algo_sub_sound; assumption].
  - apply K_sym. eapply K_widen; [apply K_bind; eassumption | apply algo_sub_sound; assumption].
  - eauto with task.
  - apply K_sym. eapply K_split; eauto with task.
Qed.

Lemma ctx_top_mono : forall D D' A,
    (forall x, marks D x -> marks D' x) -> ctx_top D A -> ctx_top D' A.
Proof. unfold ctx_top; eauto using top_shape_mono. Qed.

Lemma ctx_sub_mono : forall D D' A B,
    (forall x, marks D x -> marks D' x) -> ctx_sub D A B -> ctx_sub D' A B.
Proof. unfold ctx_sub; intros; eapply (proj1 (normal_sub_mono _)); eauto. Qed.

Lemma compat_bottom : forall D A B, compatible D A B ->
    (bottom_shape A -> ctx_top D B) /\ (bottom_shape B -> ctx_top D A).
Proof.
  intros D A B H; induction H.
  - destruct A,B; simpl in *; tauto.
  - split; [|auto]. intro Hb. exfalso. apply bottom_components in Hb.
    exact (proj1 (top_components _ _ _) H _ Hb).
  - split; [auto|]. intro Hb. exfalso. apply bottom_components in Hb.
    exact (proj1 (top_components _ _ _) H _ Hb).
  - simpl; split; [tauto|]. intro Hb; exists A; auto.
  - tauto.
  - destruct IHcompatible as [H1 H2]; split; intros.
    + eapply (proj1 (normal_sub_top _)); [exact H0 | apply H1; assumption].
    + apply H2. eapply normal_sub_bottom; eauto.
  - apply spl_compute, split_components in H.
    destruct IHcompatible1 as [HB HB'], IHcompatible2 as [HC HC'].
    split.
    + rewrite !bottom_components in *. rewrite H, in_app_iff. tauto.
    + unfold ctx_top in *. rewrite !top_components in *.
      intros HT a Ha; rewrite H in Ha; apply in_app_or in Ha; destruct Ha; auto.
Qed.

Lemma compatible_mono : forall D A B, compatible D A B -> forall D',
    (forall x, marks D x -> marks D' x) ->
    (forall x A, binds x A D -> compatible D' (t_tvar_f x) A) ->
    compatible D' A B.
Proof. intros D A B H; induction H; eauto 7 using ctx_sub_mono, ctx_top_mono with task. Qed.

Lemma compatible_subst : forall D A B, compatible D A B -> forall D' X U,
    index_scope U ->
    (forall Y, marks D Y -> ctx_top D' (typsubst_typ U X (t_tvar_f Y))) ->
    (forall Y A, binds Y A D -> compatible D' (typsubst_typ U X (t_tvar_f Y)) (typsubst_typ U X A)) ->
    compatible D' (typsubst_typ U X A) (typsubst_typ U X B).
Proof.
  intros D A B H; induction H; intros D' X' U HU HT HK;
    try solve [eauto 6 using ctx_top_subst, ctx_sub_subst, spl_subst, spl_lc with task].
  destruct A,B; simpl in *; try contradiction; apply K_rigid; exact I.
Qed.

Lemma wf_type_index : forall D A, wf_type D A -> index_scope A.
Proof. intros; eapply type_scope_mono; [apply le_n|intros; exact I|eassumption]. Qed.

Lemma appDist_scope : forall D A B, appDist A B -> wf_type D A -> wf_type D B.
Proof.
  intros D A B H; induction H; auto; intros [H1 H2];
    specialize (IHappDist1 H1); specialize (IHappDist2 H2); simpl in *;
    unfold wf_type in *; simpl in *; tauto.
Qed.

Lemma appDist_subst : forall A B, appDist A B -> forall X U, index_scope U ->
    appDist (typsubst_typ U X A) (typsubst_typ U X B).
Proof.
  intros A B H; induction H; simpl; intros; eauto using appDist.
  apply AD_refl, scope_lc_typ; auto using index_scope_subst, lc_typ_scope.
Qed.

Fixpoint exp_scope (i j : nat) (e : exp) : Prop :=
  match e with
  | e_var_b n => n < i
  | e_abs A b | e_fixpoint A b => type_scope j (fun _ => True) A /\ exp_scope (S i) j b
  | e_app a b | e_merge a b => exp_scope i j a /\ exp_scope i j b
  | e_anno a A | e_tapp a A => exp_scope i j a /\ type_scope j (fun _ => True) A
  | e_rcd _ a | e_proj a _ => exp_scope i j a
  | e_tabs b => exp_scope i (S j) b
  | _ => True
  end.

Lemma name_open_exp_size : forall e k x,
    size_exp (open_exp_wrt_exp_rec k (e_var_f x) e) = size_exp e.
Proof.
  induction e; simpl; intros; rewrite ?IHe, ?IHe1, ?IHe2; auto.
  destruct (lt_eq_lt_dec n k) as [ [Hlt|Heq] |Hgt]; reflexivity.
Qed.

Lemma name_open_texp_size : forall e k x,
    size_exp (open_exp_wrt_typ_rec k (t_tvar_f x) e) = size_exp e.
Proof. induction e; simpl; intros; rewrite ?size_open_type_name, ?IHe, ?IHe1, ?IHe2; auto. Qed.

Lemma name_open_exp_scope : forall e i j x,
    exp_scope i j (open_exp_wrt_exp_rec i (e_var_f x) e) <-> exp_scope (S i) j e.
Proof.
  induction e; simpl; intros; rewrite ?IHe, ?IHe1, ?IHe2; try tauto.
  destruct (lt_eq_lt_dec n i) as [ [Hlt|Heq] |Hgt]; simpl; try tauto; lia.
Qed.

Lemma name_open_texp_scope : forall e i j x,
    exp_scope i j (open_exp_wrt_typ_rec j (t_tvar_f x) e) <-> exp_scope i (S j) e.
Proof.
  assert (HT : forall A k x, type_scope k (fun _ => True) (open_typ_wrt_typ_rec k (t_tvar_f x) A) <->
      type_scope (S k) (fun _ => True) A).
  { split; intros; [eapply type_scope_open_inv | eapply type_scope_open]; eauto; intros; exact I. }
  induction e; simpl; intros; rewrite ?IHe, ?IHe1, ?IHe2, ?HT; tauto.
Qed.

Lemma lc_exp_indices : forall e, lc_exp e -> exp_scope 0 0 e.
Proof.
  intros e H; induction H; simpl; intuition auto using lc_typ_scope.
  all: try solve [apply lc_typ_scope; assumption].
  all: unfold open_exp_wrt_exp, open_exp_wrt_typ in *.
  all: first [
     apply (proj1 (name_open_exp_scope e 0 0 (Atom.fresh nil))); auto
   | apply (proj1 (name_open_texp_scope e 0 0 (Atom.fresh nil))); auto ].
Qed.

Lemma indices_lc_exp : forall n e, size_exp e <= n -> exp_scope 0 0 e -> lc_exp e.
Proof.
  induction n as [n IH] using lt_wf_ind.
  destruct e; simpl; intros Hn HS; try lia; try solve [constructor].
  all: try solve [
    destruct HS as [H1 H2]; constructor;
    first [apply scope_lc_typ; assumption | eapply (IH (size_exp e1)); eauto; lia |
           eapply (IH (size_exp e2)); eauto; lia | eapply (IH (size_exp e)); eauto; lia] ].
  all: try solve [constructor; eapply (IH (size_exp e)); eauto; lia].
  all: try solve [
    destruct HS as [H1 H2]; constructor; [apply scope_lc_typ; exact H1|]; intro x;
    unfold open_exp_wrt_exp; eapply (IH (size_exp e));
      [lia | rewrite name_open_exp_size; lia | apply name_open_exp_scope; exact H2] ].
  constructor; intro x; unfold open_exp_wrt_typ; eapply (IH (size_exp e));
    [lia | rewrite name_open_texp_size; lia | apply name_open_texp_scope; exact HS].
Qed.

Lemma exp_open_above : forall e i j k u,
    exp_scope i j e -> i <= k -> open_exp_wrt_exp_rec k u e = e.
Proof.
  induction e; simpl; intros; try solve [f_equal; intuition eauto using le_n_S].
  destruct (lt_eq_lt_dec n k) as [ [Hlt|Heq] |Hgt]; auto; lia.
Qed.

Lemma texp_open_above : forall e i j k U,
    exp_scope i j e -> j <= k -> open_exp_wrt_typ_rec k U e = e.
Proof. induction e; simpl; intros; f_equal; intuition eauto using le_n_S, type_open_above. Qed.

Lemma exp_subst_open : forall e k x u v,
    lc_exp u ->
    subst_exp u x (open_exp_wrt_exp_rec k v e) =
    open_exp_wrt_exp_rec k (subst_exp u x v) (subst_exp u x e).
Proof.
  induction e; simpl; intros; try solve [f_equal; eauto].
  - destruct (lt_eq_lt_dec n k) as [ [Hlt|Heq] |Hgt]; reflexivity.
  - match goal with |- context[if ?d then _ else _] => destruct d end; auto.
    symmetry; eapply exp_open_above; [apply lc_exp_indices; exact H|lia].
Qed.

Lemma exp_subst_topen : forall e k x u U,
    lc_exp u ->
    subst_exp u x (open_exp_wrt_typ_rec k U e) =
    open_exp_wrt_typ_rec k U (subst_exp u x e).
Proof.
  induction e; simpl; intros; try solve [f_equal; eauto].
  match goal with |- context[if ?d then _ else _] => destruct d end; auto.
  symmetry; eapply texp_open_above; [apply lc_exp_indices; exact H|lia].
Qed.

Lemma texp_subst_open : forall e k X U u,
    typsubst_exp U X (open_exp_wrt_exp_rec k u e) =
    open_exp_wrt_exp_rec k (typsubst_exp U X u) (typsubst_exp U X e).
Proof.
  induction e; simpl; intros; try solve [f_equal; eauto].
  destruct (lt_eq_lt_dec n k) as [ [Hlt|Heq] |Hgt]; reflexivity.
Qed.

Lemma texp_subst_topen : forall e k X U V,
    index_scope U ->
    typsubst_exp U X (open_exp_wrt_typ_rec k V e) =
    open_exp_wrt_typ_rec k (typsubst_typ U X V) (typsubst_exp U X e).
Proof. induction e; simpl; intros; f_equal; eauto using type_subst_open. Qed.

Lemma exp_subst_fresh : forall e x u, x \notin termfv_exp e -> subst_exp u x e = e.
Proof.
  induction e; simpl; intros; try solve [f_equal; eauto; apply notin_union in H; tauto].
  match goal with |- context[if ?d then _ else _] => destruct d end; auto; subst; fsetdec.
Qed.

Lemma texp_subst_fresh : forall e X U, X \notin typefv_exp e -> typsubst_exp U X e = e.
Proof.
  induction e; simpl; intros; f_equal; eauto using type_subst_fresh;
    apply notin_union in H; destruct H; eauto using type_subst_fresh.
Qed.

Lemma exp_subst_intro : forall e x u,
    lc_exp u -> x \notin termfv_exp e ->
    subst_exp u x (e ^ x) = e ^^ u.
Proof.
  unfold open_exp_wrt_exp; intros; rewrite exp_subst_open by assumption.
  rewrite (@exp_subst_fresh e x u H0); simpl.
  match goal with |- context[if ?d then _ else _] => destruct d end; congruence.
Qed.

Lemma texp_subst_intro : forall e X U,
    index_scope U -> X \notin typefv_exp e ->
    typsubst_exp U X (open_exp_wrt_typ e (t_tvar_f X)) = open_exp_wrt_typ e U.
Proof.
  unfold open_exp_wrt_typ; intros; rewrite texp_subst_topen by assumption.
  rewrite (@texp_subst_fresh e X U H0); simpl.
  match goal with |- context[if ?d then _ else _] => destruct d end; congruence.
Qed.

Lemma wf_open_with : forall D B C U,
    wf_type D (t_forall B C) -> wf_type D U -> wf_type D (C ^-^ U).
Proof.
  intros D B C U [_ HC] HU; unfold wf_type, open_typ_wrt_typ.
  eapply type_scope_open; [ | exact HU | exact HC]; auto.
Qed.

(* Typing with unrestricted runtime merges and the exclusion property needed
   to substitute a type argument. *)
Inductive runtime_typing : tctx -> ctx -> exp -> dirflag -> typ -> Prop :=
| RT_top : forall D G, runtime_typing D G e_top Inf t_top
| RT_lit : forall D G i, runtime_typing D G (e_lit i) Inf t_int
| RT_var : forall D G x A,
    binds x A G -> wf_type D A -> runtime_typing D G (e_var_f x) Inf A
| RT_abs : forall L D G A e B C,
    wf_type D A -> wf_type D (t_arrow B C) -> ctx_sub D B A ->
    (forall x, x \notin L -> runtime_typing D ((x,A)::G) (e ^ x) Chk C) ->
    runtime_typing D G (e_abs A e) Chk (t_arrow B C)
| RT_app : forall D G e u A B C,
    runtime_typing D G e Inf A -> appDist A (t_arrow B C) ->
    runtime_typing D G u Chk B -> runtime_typing D G (e_app e u) Inf C
| RT_tabs : forall L D G e A B,
    wf_type D (t_forall A B) ->
    (forall X, X \notin L -> runtime_typing ((X,A)::D) G (open_exp_wrt_typ e (t_tvar_f X)) Chk (B -^ X)) ->
    runtime_typing D G (e_tabs e) Chk (t_forall A B)
| RT_tapp : forall D G e A B C1 C2,
    runtime_typing D G e Inf B -> appDist B (t_forall C1 C2) ->
    wf_type D A -> compatible D A C1 ->
    runtime_typing D G (e_tapp e A) Inf (C2 ^-^ A)
| RT_proj : forall D G e l A C,
    runtime_typing D G e Inf A -> appDist A (t_rcd l C) ->
    runtime_typing D G (e_proj e l) Inf C
| RT_rcd : forall D G l e A,
    runtime_typing D G e Chk A -> runtime_typing D G (e_rcd l e) Chk (t_rcd l A)
| RT_merge : forall D G e u A B,
    runtime_typing D G e Inf A -> runtime_typing D G u Inf B ->
    runtime_typing D G (e_merge e u) Inf (t_and A B)
| RT_merge_parts : forall D G e u A B C,
    runtime_typing D G e Inf B -> runtime_typing D G u Inf C -> spl A B C ->
    runtime_typing D G (e_merge e u) Inf A
| RT_inter : forall D G e A B,
    runtime_typing D G e Chk A -> runtime_typing D G e Chk B ->
    runtime_typing D G e Chk (t_and A B)
| RT_anno : forall D G e A,
    runtime_typing D G e Chk A -> runtime_typing D G (e_anno e A) Inf A
| RT_fix : forall L D G A e,
    wf_type D A ->
    (forall x, x \notin L -> runtime_typing D ((x,A)::G) (e ^ x) Chk A) ->
    runtime_typing D G (e_fixpoint A e) Inf A
| RT_sub : forall D G e A B,
    runtime_typing D G e Inf A -> wf_type D B -> ctx_sub D A B ->
    runtime_typing D G e Chk B.

Local Hint Constructors runtime_typing : task.

Lemma rt_type_scope : forall D G e d A,
    runtime_typing D G e d A -> wf_type D A.
Proof.
  intros D G e d A H; induction H; simpl; try solve [assumption | exact I | split; auto].
  all: try solve [eapply wf_open_with; eauto using appDist_scope].
  - exact (proj2 (@appDist_scope D A (t_arrow B C) H0 IHruntime_typing1)).
  - exact (@appDist_scope D A (t_rcd l C) H0 IHruntime_typing).
  - eapply split_scope; [apply spl_compute; eassumption | split; assumption].
Qed.

Lemma rt_exp_scope : forall D G e d A,
    runtime_typing D G e d A -> exp_scope 0 0 e.
Proof.
  intros D G e d A H; induction H; simpl; try tauto.
  all: try solve [split; auto; eapply wf_type_index; eauto using rt_type_scope].
  all: try solve [
    split; [eapply wf_type_index; eassumption |];
    pick fresh x for L; apply (proj1 (name_open_exp_scope e 0 0 x)); eauto].
  pick fresh x for L; apply (proj1 (name_open_texp_scope e 0 0 x)); eauto.
Qed.

Lemma rt_lc : forall D G e d A,
    runtime_typing D G e d A -> lc_exp e.
Proof. intros; eapply (indices_lc_exp (n := size_exp e)); eauto using rt_exp_scope. Qed.

Definition ctx_embedding D D' :=
  (forall X, in_ctx D X -> in_ctx D' X) /\
  (forall X, marks D X -> marks D' X) /\
  (forall X A, binds X A D -> compatible D' (t_tvar_f X) A).

Lemma ctx_embedding_binds : forall D D',
    (forall x A, binds x A D -> binds x A D') -> ctx_embedding D D'.
Proof.
  unfold ctx_embedding, marks, in_ctx; intros D D' H; repeat split.
  - intros X HX; destruct (@binds_In_inv _ _ _ HX); eauto using binds_In.
  - intros X [A [HA HB] ]; eauto.
  - eauto using K_bind.
Qed.

Lemma ctx_embedding_push : forall D D' X A, ctx_embedding D D' ->
    ctx_embedding ((X,A)::D) ((X,A)::D').
Proof.
  intros D D' X A [HW [HM HK] ]; repeat split.
  - intros y; rewrite !in_ctx_cons; intuition auto.
  - intros y; rewrite !marks_cons; intuition auto.
  - intros y B Hy; apply binds_cons_1 in Hy. destruct Hy as [ [<- <-] |Hy].
    + apply K_bind; auto using binds_cons_2.
    + eapply compatible_mono; [apply HK; exact Hy | |].
      * intros; apply marks_cons; auto.
      * eauto using K_bind, binds_cons_3.
Qed.

Lemma rt_weaken : forall D G e d A,
    runtime_typing D G e d A -> forall D' G',
    ctx_embedding D D' ->
    (forall x B, binds x B G -> binds x B G') ->
    runtime_typing D' G' e d A.
Proof.
  intros D G e d A H; induction H; intros D' G' HD HG;
    pose proof HD as [HW [HM HK] ];
    try solve [eauto 6 using wf_type_expand, ctx_sub_mono, compatible_mono with task].
  - apply RT_abs with (L := L); eauto using wf_type_expand, ctx_sub_mono.
    intros x Hx; eapply H3; eauto.
    intros y P Hy; apply binds_cons_1 in Hy; destruct Hy as [ [<- <-] |Hy];
      eauto using binds_cons_2, binds_cons_3.
  - apply RT_tabs with (L := L); eauto using wf_type_expand, ctx_embedding_push.
  - apply RT_fix with (L := L); eauto using wf_type_expand.
    intros x Hx; eapply H1; eauto.
    intros y P Hy; apply binds_cons_1 in Hy; destruct Hy as [ [<- <-] |Hy];
      eauto using binds_cons_2, binds_cons_3.
Qed.

Lemma ctx_narrow : forall D X U V,
    ctx_sub D V U -> ctx_embedding ((X,U)::D) ((X,V)::D).
Proof.
  intros; repeat split.
  - intros y; rewrite !in_ctx_cons; auto.
  - intros y; rewrite !marks_cons; intros [ [<- Hb] |Hm]; auto.
    left; split; auto. eapply normal_sub_bottom; eauto.
  - intros y B Hb; apply binds_cons_1 in Hb; destruct Hb as [ [<- <-] |Hb].
    + eapply K_widen; [apply K_bind; apply binds_cons_2; reflexivity |].
      eapply ctx_sub_mono; [|eassumption]; intros; apply marks_cons; auto.
    + apply K_bind; eauto using binds_cons_3.
Qed.

Lemma cwell_binds : forall D G x A, CWell D G -> binds x A G -> wf_type D A.
Proof.
  intros D G x A H; induction H; intros Hb; [inversion Hb|].
  apply binds_cons_1 in Hb; destruct Hb as [ [<- <-] |Hb]; eauto using twell_scope.
Qed.

Lemma typing_tcwell : forall D G e d A, Typing D G e d A -> TCWell D.
Proof.
  intros D G e d A H; induction H; auto.
  - exact (proj1 (algo_sub_scope H)).
  - pick fresh x for L. specialize (H1 x ltac:(fsetdec)); inversion H1; assumption.
  - pick fresh x for L. exact (H0 x ltac:(fsetdec)).
Qed.

Lemma typing_runtime : forall D G e d A, Typing D G e d A -> runtime_typing D G e d A.
Proof.
  intros D G e d A H; induction H;
    try solve [eauto 5 using cwell_binds, algo_sub_sound with task].
  - destruct (algo_sub_scope H) as [_ [HB HA] ].
    apply RT_abs with (L := L); auto using algo_sub_sound.
    split; auto. pick fresh x for L. eapply rt_type_scope; eauto.
  - apply RT_tabs with (L := L); auto.
    pick fresh x for (L \u typefv_typ B).
    pose proof (typing_tcwell (H0 x ltac:(fsetdec))) as HT.
    eapply wf_all_close with (X := x); [fsetdec | | eapply rt_type_scope; eauto].
    inversion HT; subst; eauto using twell_scope.
  - destruct (disjoint_scope H1); eauto using disjoint_compatible with task.
  - apply RT_fix with (L := L); auto.
    pick fresh x for L. eapply rt_type_scope; eauto.
  - apply RT_merge.
    + eapply rt_weaken; [eassumption | apply ctx_embedding_binds |]; intros ? ? Hb; inversion Hb.
    + eapply rt_weaken; [eassumption | apply ctx_embedding_binds |]; intros ? ? Hb; inversion Hb.
  - destruct (algo_sub_scope H0) as [_ [_ HB] ]; eauto using algo_sub_sound with task.
Qed.

Lemma rt_subst_term : forall D G e d A,
    runtime_typing D G e d A -> forall G' x u,
    lc_exp u ->
    (forall y B, binds y B G -> runtime_typing D G' (subst_exp u x (e_var_f y)) Inf B) ->
    runtime_typing D G' (subst_exp u x e) d A.
Proof.
  intros D G e d A H; induction H; simpl; intros G' z u' Hu HG;
    try solve [eauto 6 with task].
  - apply RT_abs with (L := L \u singleton z); auto.
    intros x Hx; unfold open_exp_wrt_exp.
    assert (Hneq : x <> z) by fsetdec.
    assert (Hvar : subst_exp u' z (e_var_f x) = e_var_f x).
    { simpl; match goal with |- context[if ?d then _ else _] => destruct d end; congruence. }
    rewrite <- Hvar, <- exp_subst_open by exact Hu.
    apply H3; [fsetdec|exact Hu|].
    intros y T Hy; apply binds_cons_1 in Hy; destruct Hy as [ [<- <-] |Hy].
    + simpl; match goal with |- context[if ?d then _ else _] => destruct d end; try contradiction.
      apply RT_var; auto using binds_cons_2.
    + eapply rt_weaken; [apply HG; exact Hy | apply ctx_embedding_binds; auto |].
      auto using binds_cons_3.
  - apply RT_tabs with (L := L); auto. intros X HX.
    unfold open_exp_wrt_typ; rewrite <- exp_subst_topen by exact Hu.
    apply H1; auto.
    intros y T Hy; eapply rt_weaken; [apply HG; exact Hy | apply ctx_embedding_binds |];
      auto using binds_cons_3.
  - apply RT_fix with (L := L \u singleton z); auto.
    intros x Hx; unfold open_exp_wrt_exp.
    assert (Hneq : x <> z) by fsetdec.
    assert (Hvar : subst_exp u' z (e_var_f x) = e_var_f x).
    { simpl; match goal with |- context[if ?d then _ else _] => destruct d end; congruence. }
    rewrite <- Hvar, <- exp_subst_open by exact Hu.
    apply H1; [fsetdec|exact Hu|].
    intros y T Hy; apply binds_cons_1 in Hy; destruct Hy as [ [<- <-] |Hy].
    + simpl; match goal with |- context[if ?d then _ else _] => destruct d end; try contradiction.
      apply RT_var; auto using binds_cons_2.
    + eapply rt_weaken; [apply HG; exact Hy | apply ctx_embedding_binds; auto |].
      auto using binds_cons_3.
Qed.

Lemma rt_open_term : forall L e u A B,
    (forall x, x \notin L -> runtime_typing nil [(x,A)] (e ^ x) Chk B) ->
    runtime_typing nil nil u Inf A -> runtime_typing nil nil (e ^^ u) Chk B.
Proof.
  intros L e u A B H Hu.
  pick fresh x for (L \u termfv_exp e).
  pose proof (rt_lc Hu) as Hlc.
  rewrite <- (@exp_subst_intro e x u Hlc ltac:(fsetdec)).
  eapply rt_subst_term; [apply H; fsetdec |exact Hlc|].
  intros y T Hy; apply binds_cons_1 in Hy; destruct Hy as [ [<- <-] |Hy]; [|inversion Hy].
  simpl. match goal with |- context[if ?d then _ else _] => destruct d end; [exact Hu | contradiction].
Qed.

Definition map_types (X : typevar) (U : typ) (G : ctx) : ctx :=
  map (fun '(x,A) => (x, typsubst_typ U X A)) G.

Lemma binds_map_types : forall X U G x A, binds x A G ->
    binds x (typsubst_typ U X A) (map_types X U G).
Proof.
  intros X U G; induction G as [|[y B] G IH]; intros x A H; [inversion H|].
  apply binds_cons_1 in H. destruct H as [ [<- <-] |H]; simpl; eauto using binds_cons_2, binds_cons_3.
Qed.

Definition type_instantiation D D' X U :=
  wf_type D' U /\
  (forall Y, in_ctx D Y -> wf_type D' (typsubst_typ U X (t_tvar_f Y))) /\
  (forall Y, marks D Y -> ctx_top D' (typsubst_typ U X (t_tvar_f Y))) /\
  (forall Y A, binds Y A D ->
        compatible D' (typsubst_typ U X (t_tvar_f Y)) (typsubst_typ U X A)).

Lemma wf_type_inst : forall D D' X U A, type_instantiation D D' X U ->
    wf_type D A -> wf_type D' (typsubst_typ U X A).
Proof.
  intros D D' X U A [_ [HF _] ] HA.
  eapply type_subst_scope; [exact HF | exact HA].
Qed.

Lemma ctx_sub_inst : forall D D' X U A B, type_instantiation D D' X U ->
    ctx_sub D A B -> ctx_sub D' (typsubst_typ U X A) (typsubst_typ U X B).
Proof.
  intros D D' X U A B [HU [_ [HT _] ] ] HS.
  eapply ctx_sub_subst; [eapply wf_type_index; exact HU|exact HS|exact HT].
Qed.

Lemma ctx_compat_inst : forall D D' X U A B, type_instantiation D D' X U ->
    compatible D A B -> compatible D' (typsubst_typ U X A) (typsubst_typ U X B).
Proof.
  intros D D' X U A B [HU [_ [HT HK] ] ] HS.
  eapply compatible_subst; [exact HS|eapply wf_type_index; exact HU|exact HT|exact HK].
Qed.

Lemma type_inst_push : forall D D' X U Y A,
    Y <> X -> type_instantiation D D' X U ->
    type_instantiation ((Y,A)::D) ((Y,typsubst_typ U X A)::D') X U.
Proof.
  intros D D' X U Y A Hneq [HU [HF [HT HK] ] ].
  assert (Hscope : forall T, wf_type D' T -> wf_type ((Y,typsubst_typ U X A)::D') T).
  { intros; eapply wf_type_expand; [|eassumption]. intros; apply in_ctx_cons; auto. }
  assert (Hmark : forall Z, marks D' Z -> marks ((Y,typsubst_typ U X A)::D') Z).
  { intros; apply marks_cons; auto. }
  assert (Hvar : typsubst_typ U X (t_tvar_f Y) = t_tvar_f Y).
  { simpl; match goal with |- context[if ?d then _ else _] => destruct d end; congruence. }
  repeat split; auto.
  - intros z Hz; apply in_ctx_cons in Hz; destruct Hz as [->|Hz].
    + rewrite Hvar; simpl; apply in_ctx_cons; auto.
    + auto.
  - intros z Hz; apply marks_cons in Hz; destruct Hz as [ [<- Hb] |Hz].
    + rewrite Hvar. change (marks ((Y,typsubst_typ U X A)::D') Y).
      apply marks_cons; auto using bottom_subst.
    + eapply ctx_top_mono; [exact Hmark|auto].
  - intros z T Hz; apply binds_cons_1 in Hz; destruct Hz as [ [<- <-] |Hz].
    + rewrite Hvar. apply K_bind; auto using binds_cons_2.
    + eapply compatible_mono; [eauto |exact Hmark|].
      eauto using K_bind, binds_cons_3.
Qed.

Lemma rt_subst_type : forall D G e d A, runtime_typing D G e d A -> forall D' X U,
    type_instantiation D D' X U ->
    runtime_typing D' (map_types X U G) (typsubst_exp U X e) d (typsubst_typ U X A).
Proof.
  intros D G e d A H; induction H; simpl; intros D' Z U HI;
    assert (HU : index_scope U) by (eapply wf_type_index; exact (proj1 HI));
    try solve [eauto 6 using wf_type_inst, ctx_sub_inst, ctx_compat_inst, appDist_subst, binds_map_types with task].
  - apply RT_abs with (L := L).
    1: exact (@wf_type_inst D D' Z U A HI H).
    1: exact (@wf_type_inst D D' Z U (t_arrow B C) HI H0).
    1: exact (@ctx_sub_inst D D' Z U B A HI H1).
    intros x Hx. pose proof (H3 x Hx D' Z U HI) as HH.
    unfold open_exp_wrt_exp in HH. rewrite texp_subst_open in HH. exact HH.
  - eapply RT_app; [apply IHruntime_typing1; exact HI | |apply IHruntime_typing2; exact HI].
    exact (@appDist_subst A (t_arrow B C) H0 Z U HU).
  - apply RT_tabs with (L := L \u singleton Z).
    1: exact (@wf_type_inst D D' Z U (t_forall A B) HI H).
    intros X HX; unfold open_exp_wrt_typ, open_typ_wrt_typ.
    assert (Hvar : typsubst_typ U Z (t_tvar_f X) = t_tvar_f X).
    { simpl; match goal with |- context[if ?d then _ else _] => destruct d end; auto; subst; fsetdec. }
    pose proof (H1 X ltac:(fsetdec) _ Z U
      (@type_inst_push D D' Z U X A ltac:(fsetdec) HI)) as HH.
    unfold open_exp_wrt_typ, open_typ_wrt_typ in HH.
    rewrite texp_subst_topen, type_subst_open, Hvar in HH by assumption.
    exact HH.
  - unfold open_typ_wrt_typ; rewrite type_subst_open by assumption.
    eapply RT_tapp; [apply IHruntime_typing; exact HI | | |].
    + exact (@appDist_subst B (t_forall C1 C2) H0 Z U HU).
    + eapply wf_type_inst; eassumption.
    + eapply ctx_compat_inst; eassumption.
  - eapply RT_proj; [apply IHruntime_typing; exact HI |].
    exact (@appDist_subst A (t_rcd l C) H0 Z U HU).
  - eapply RT_merge_parts; [apply IHruntime_typing1; exact HI | apply IHruntime_typing2; exact HI |].
    eapply spl_subst; eauto using spl_lc.
  - apply RT_fix with (L := L).
    1: exact (@wf_type_inst D D' Z U A HI H).
    intros x Hx. pose proof (H1 x Hx D' Z U HI) as HH.
    unfold open_exp_wrt_exp in HH. rewrite texp_subst_open in HH. exact HH.
Qed.

Lemma scope_free : forall A k F X,
    type_scope k F A -> X \in typefv_typ A -> F X.
Proof.
  induction A; simpl; intros; try solve [exfalso; fsetdec].
  all: try solve [assert (X = X0) by fsetdec; subst; assumption].
  all: try solve [eapply IHA; eassumption].
  all: destruct H; apply F.union_iff in H0; destruct H0; first [solve [eapply IHA1; eassumption] | solve [eapply IHA2; eassumption] ].
Qed.

Lemma nil_scope_fresh : forall A X, wf_type nil A -> X \notin typefv_typ A.
Proof.
  unfold in_ctx, wf_type; intros A X HA HX.
  pose proof (@scope_free A 0 (fun x => x \in dom (@nil (atom*typ))) X HA HX).
  simpl in H; fsetdec.
Qed.

Lemma instantiate_nil : forall X A U, wf_type nil A -> wf_type nil U ->
    compatible nil U A -> type_instantiation [(X,A)] nil X U.
Proof.
  intros X A U HA HU HK.
  assert (Hvar : typsubst_typ U X (t_tvar_f X) = U).
  { simpl; match goal with |- context[if ?d then _ else _] => destruct d end; congruence. }
  repeat split; auto.
  - intros y Hy. apply in_ctx_cons in Hy. destruct Hy as [->|Hy].
    + rewrite Hvar; exact HU.
    + unfold in_ctx in Hy; simpl in Hy; exfalso; fsetdec.
  - intros y Hy. apply marks_cons in Hy. destruct Hy as [ [<- Hb] |Hy].
    + rewrite Hvar; exact (proj2 (compat_bottom HK) Hb).
    + exfalso; exact (marks_nil Hy).
  - intros y B Hy; apply binds_cons_1 in Hy; destruct Hy as [ [<- <-] |Hy]; [|inversion Hy].
    rewrite Hvar, type_subst_fresh; [exact HK | apply nil_scope_fresh; exact HA].
Qed.

Lemma rt_open_type : forall L e U A B,
    (forall X, X \notin L -> runtime_typing [(X,A)] nil (open_exp_wrt_typ e (t_tvar_f X)) Chk (B -^ X)) ->
    wf_type nil A -> wf_type nil U -> compatible nil U A ->
    runtime_typing nil nil (open_exp_wrt_typ e U) Chk (B ^-^ U).
Proof.
  intros L e U A B H HA HU HK.
  pick fresh X for (L \u typefv_exp e \u typefv_typ B).
  pose proof (@wf_type_index nil U HU) as HI.
  rewrite <- (@texp_subst_intro e X U HI ltac:(fsetdec)).
  rewrite <- (@type_subst_intro B X U HI ltac:(fsetdec)).
  exact (@rt_subst_type _ nil _ _ _ (H X ltac:(fsetdec)) nil X U (@instantiate_nil X A U HA HU HK)).
Qed.

Lemma ordinary_ctx_sub : forall D A B, ord B -> ctx_sub D A B ->
    component_sub (marks D) no_indices A B.
Proof. intros; apply sub_component_ord; assumption. Qed.

Lemma selected_head : forall D A B, ord B -> ~ ctx_top D B ->
    ~ bottom_shape A -> ctx_sub D A B ->
    exists a, In a (components A) /\ head_sub (marks D) no_indices a B.
Proof.
  intros; apply ordinary_ctx_sub in H2; auto.
  destruct (component_sub_inversion H2) as [HT|[HB|HH] ]; tauto.
Qed.

Lemma ord_all_open : forall D A B X,
    ord (t_forall A B) -> wf_type D (t_forall A B) -> ord (B -^ X).
Proof.
  intros D A B X HO HW. pose proof (ord_compute HO) as HS; simpl in HS.
  destruct (split_type B) as [ [U V]|] eqn:E; try discriminate.
  eapply (compute_ord (n := size_typ (B -^ X))); [lia | |].
  - eapply wf_type_index, wf_all_open; exact HW.
  - unfold open_typ_wrt_typ; rewrite split_open_name, E; reflexivity.
Qed.

(* An ordinary, non-top-like cast keeps the term inside the annotation.
   Its new type must therefore still check the same introduction form. *)
Lemma check_widen_aux : forall n D G e A B, size_exp e + size_typ A <= n ->
    runtime_typing D G e Chk A -> wf_type D B -> ord B ->
    ~ ctx_top D B -> ctx_sub D A B -> runtime_typing D G e Chk B.
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros D G e A T Hn HT HW HO Hnt HS.
  remember Chk as d eqn:Hd in HT.
  destruct HT; try discriminate Hd.
  - destruct (@selected_head D (t_arrow B C) T HO Hnt (fun x => x) HS) as [a [Hin Hhead] ].
    simpl in Hin; apply in_map_iff in Hin; destruct Hin as [c [<- Hin] ].
    destruct T; simpl in Hhead; try discriminate.
    destruct HW as [HWB HWC], Hhead as [Hdom Hcod].
    apply RT_abs with (L := L); auto.
    + split; assumption.
    + eapply ctx_sub_trans; eassumption.
    + intros x Hx. eapply (IH (size_exp e + size_typ C)) with (A := C).
      * simpl in Hn; lia.
      * unfold open_exp_wrt_exp; rewrite name_open_exp_size; lia.
      * apply H2; auto.
      * exact HWC.
      * inversion HO; auto.
      * exact Hnt.
      * eapply normal_sub_trans; [apply normal_sub_select; exact Hin | exact Hcod].
  - destruct (@selected_head D (t_forall A B) T HO Hnt (fun x => x) HS) as [a [Hin Hhead] ].
    simpl in Hin; apply in_map_iff in Hin; destruct Hin as [b [<- Hin] ].
    destruct T; simpl in Hhead; try discriminate.
    destruct Hhead as [Hdom Hcod].
    apply RT_tabs with (L := L \u dom D \u typefv_typ T2); auto.
    intros x Hx.
    assert (Hbody : runtime_typing ((x,T1)::D) G (open_exp_wrt_typ e (t_tvar_f x)) Chk (B -^ x)).
    { eapply rt_weaken; [apply H0; fsetdec | apply ctx_narrow; exact Hdom | auto]. }
    eapply (IH (size_exp e + size_typ B)) with (A := B -^ x).
    + simpl in Hn; lia.
    + unfold open_exp_wrt_typ, open_typ_wrt_typ; rewrite name_open_texp_size, size_open_type_name; lia.
    + exact Hbody.
    + eapply wf_all_open; exact HW.
    + eapply ord_all_open; eassumption.
    + intro Htop; apply Hnt. eapply (@top_close D x T1 T2); [fsetdec|fsetdec|exact Htop].
    + apply subtype_open_name. eapply normal_sub_trans; [apply normal_sub_select; exact Hin | exact Hcod].
  - destruct (@selected_head D (t_rcd l A) T HO Hnt (fun x => x) HS) as [a [Hin Hhead] ].
    simpl in Hin; apply in_map_iff in Hin; destruct Hin as [p [<- Hin] ].
    destruct T; simpl in Hhead; try discriminate.
    destruct Hhead as [<- Hcod]. apply RT_rcd.
    eapply (IH (size_exp e + size_typ A)) with (A := A).
    + simpl in Hn; lia.
    + lia.
    + exact HT.
    + exact HW.
    + inversion HO; auto.
    + exact Hnt.
    + eapply normal_sub_trans; [apply normal_sub_select; exact Hin | exact Hcod].
  - pose proof (@ordinary_ctx_sub D (t_and A B) T HO HS) as HC.
    apply component_sub_and_source in HC; destruct HC as [HC|HC].
    + eapply (IH (size_exp e + size_typ A)) with (A := A); eauto; try (simpl in Hn; lia).
      apply sub_component_ord; assumption.
    + eapply (IH (size_exp e + size_typ B)) with (A := B); eauto; try (simpl in Hn; lia).
      apply sub_component_ord; assumption.
  - eapply RT_sub; eauto using ctx_sub_trans.
Qed.

Lemma check_widen : forall D G e A B,
    runtime_typing D G e Chk A -> wf_type D B -> ord B ->
    ~ ctx_top D B -> ctx_sub D A B -> runtime_typing D G e Chk B.
Proof. intros; eapply (check_widen_aux (n := size_exp e + size_typ A)); eauto. Qed.

Lemma check_top : forall D G A,
    wf_type D A -> ctx_top D A -> runtime_typing D G e_top Chk A.
Proof.
  intros; eapply RT_sub; eauto with task. apply normal_sub_top_rule; exact H0.
Qed.

Lemma rt_top_arrow : forall A B, wf_type nil (t_arrow A B) ->
    ctx_top nil (t_arrow A B) ->
    runtime_typing nil nil (e_anno (e_abs t_top e_top) (t_arrow A B)) Inf (t_arrow A B).
Proof.
  intros A B HW HT; apply RT_anno, RT_abs with (L := empty); auto.
  - exact I.
  - apply normal_sub_top_rule; exact I.
  - intros; apply check_top; [exact (proj2 HW)|exact HT].
Qed.

Lemma rt_top_record : forall l A, wf_type nil (t_rcd l A) ->
    ctx_top nil (t_rcd l A) ->
    runtime_typing nil nil (e_anno (e_rcd l e_top) (t_rcd l A)) Inf (t_rcd l A).
Proof. intros; apply RT_anno, RT_rcd, check_top; assumption. Qed.

Lemma rt_top_all : forall A B, wf_type nil (t_forall A B) ->
    ctx_top nil (t_forall A B) ->
    runtime_typing nil nil (e_anno (e_tabs e_top) (t_forall A B)) Inf (t_forall A B).
Proof.
  intros A B HW HT; apply RT_anno, RT_tabs with (L := empty); auto.
  intros X _; simpl; apply check_top.
  - apply wf_all_open; exact HW.
  - apply top_open_name; exact HT.
Qed.

Lemma wf_split : forall D A B C, wf_type D A -> spl A B C -> wf_type D B /\ wf_type D C.
Proof. unfold wf_type; intros; eapply split_scope; eauto using spl_compute. Qed.

Arguments wf_split {D A B C} _ _.
Lemma rt_wrap_preservation : forall e A u, wrapping e A u ->
    forall B, runtime_typing nil nil e Chk B -> wf_type nil A -> ctx_sub nil B A ->
    runtime_typing nil nil u Inf A.
Proof.
  intros e A u H; induction H; intros T HT HW HS.
  - apply RT_top.
  - apply rt_top_arrow; auto. apply topLike_flag; assumption.
  - apply rt_top_all; auto. apply topLike_flag; assumption.
  - apply rt_top_record; auto. apply topLike_flag; assumption.
  - apply RT_anno. eapply check_widen; eauto.
    intro HH; inversion H1; subst; eauto using ctx_flag_topLike.
  - destruct (@wf_split nil A B C HW H) as [HB HC].
    destruct (@ctx_sub_spl nil A B C H) as [HAB HAC].
    eapply RT_merge_parts; eauto using ctx_sub_trans.
Qed.

Lemma ctx_not_topLike : forall A, wf_type nil A -> ~ ctx_top nil A -> notTopLike nil A.
Proof.
  intros A HW H; apply NTL; auto using TCW_empty, scope_twell.
  intro HT; apply H, topLike_flag; exact HT.
Qed.

Lemma wrapping_exists : forall n e A, size_typ A <= n ->
    lc_exp e -> wf_type nil A -> exists u, wrapping e A u.
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros e A Hn He HA.
  destruct (ord_or_split (@wf_type_lc nil A HA)) as [HO|[B [C HS] ] ].
  - destruct (ctx_top_dec_nil A) as [HT|HT].
    + pose proof (@ctx_flag_topLike nil A TCW_empty HA HT) as Htop.
      inversion Htop; subst; eauto using wrapping.
      * inversion HO.
      * match goal with H : binds _ _ nil |- _ => inversion H end.
    + eauto using EW_anno, ctx_not_topLike.
  - destruct (wf_split HA HS) as [HB HC].
    destruct (@split_size A B C (spl_compute HS)) as [HL HR].
    destruct (IH (size_typ B) ltac:(lia) e B ltac:(lia) He HB) as [u Hu].
    destruct (IH (size_typ C) ltac:(lia) e C ltac:(lia) He HC) as [v Hv].
    eauto using EW_and.
Qed.

Lemma rt_merge_inv : forall D G e u A, runtime_typing D G (e_merge e u) Inf A ->
    exists B C, runtime_typing D G e Inf B /\ runtime_typing D G u Inf C /\ spl A B C.
Proof.
  intros D G e u A H; inversion H; subst; clear H; eauto 8.
  eexists; eexists; repeat split; try eassumption.
  apply Sp_and; eapply wf_type_lc, rt_type_scope; eassumption.
Qed.

Lemma rt_anno_inv : forall D G e A B, runtime_typing D G (e_anno e A) Inf B ->
    A = B /\ runtime_typing D G e Chk A.
Proof. intros; inversion H; subst; auto. Qed.

Lemma rt_cast_preservation : forall v B u, casting v B u ->
    forall A, runtime_typing nil nil v Inf A -> wf_type nil B ->
    runtime_typing nil nil u Inf B.
Proof.
  intros v B u H; induction H; intros T HT HW.
  - apply RT_lit.
  - apply RT_top.
  - apply rt_top_arrow; auto. apply topLike_flag; assumption.
  - apply rt_top_all; auto. apply topLike_flag; assumption.
  - apply rt_top_record; auto. apply topLike_flag; assumption.
  - destruct (rt_anno_inv HT) as [_ HE].
    apply RT_anno. eapply check_widen; eauto using algo_sub_sound.
    intro HB; inversion H1; subst; eauto using ctx_flag_topLike.
  - destruct (rt_merge_inv HT) as [B [C [HB [HC HS] ] ] ]; eauto.
  - destruct (rt_merge_inv HT) as [B [C [HB [HC HS] ] ] ]; eauto.
  - destruct (wf_split HW H) as [HB HC].
    eapply RT_merge_parts; eauto.
Qed.

Lemma subtype_split_choice : forall D A B C T,
    spl A B C -> ord T -> ctx_sub D A T -> ctx_sub D B T \/ ctx_sub D C T.
Proof.
  intros D A B C T HS HO H.
  assert (H' : ctx_sub D (t_and B C) T).
  { apply normal_sub_source with (A := A); auto.
    simpl; rewrite (@split_components A B C (spl_compute HS)); auto. }
  apply ordinary_ctx_sub in H'; auto.
  apply component_sub_and_source in H'; destruct H'; [left|right];
    apply sub_component_ord; assumption.
Qed.

Lemma casting_exists : forall n v A B, size_exp v + size_typ B <= n ->
    value v -> runtime_typing nil nil v Inf A -> wf_type nil B ->
    ctx_sub nil A B -> exists u, casting v B u.
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros v A B Hn HV HR HW HS.
  destruct (ord_or_split (@wf_type_lc nil B HW)) as [HO|[L [R Hspl] ] ].
  2: {
    destruct (wf_split HW Hspl) as [HL HR'].
    destruct (@split_size B L R (spl_compute Hspl)) as [HS1 HS2].
    destruct (@ctx_sub_spl nil B L R Hspl) as [HB1 HB2].
    destruct (IH (size_exp v + size_typ L) ltac:(lia) v A L ltac:(lia) HV HR HL
      (@ctx_sub_trans nil A B L HS HB1)) as [u Hu].
    destruct (IH (size_exp v + size_typ R) ltac:(lia) v A R ltac:(lia) HV HR HR'
      (@ctx_sub_trans nil A B R HS HB2)) as [w Hw].
    eauto using Cast_and. }
  destruct (ctx_top_dec_nil B) as [Htop|Hnt].
  - pose proof (@ctx_flag_topLike nil B TCW_empty HW Htop) as HT.
    pose proof (rt_lc HR) as He.
    inversion HT; subst; eauto using casting.
    + inversion HO.
    + match goal with H : binds _ _ nil |- _ => inversion H end.
  - destruct HV; try solve [inversion HR].
    all: try solve [
      match type of HR with runtime_typing _ _ (e_anno ?e ?T) _ _ =>
      destruct (rt_anno_inv HR) as [<- HE];
      eexists; apply Cast_anno; [eapply rt_lc; exact HE|exact HO|
        apply ctx_not_topLike; assumption|apply ctx_sub_algo; auto using TCW_empty;
        exact (rt_type_scope HR)]
      end].
    + inversion HR; subst.
      destruct (@selected_head nil t_top B HO Hnt (fun p => p) HS) as [b [Hb Hhead] ].
      destruct Hb as [<-|[] ]; destruct B; simpl in Hhead; try discriminate.
      exfalso; apply Hnt; exact I.
    + inversion HR; subst.
      destruct (@selected_head nil t_int B HO Hnt (fun p => p) HS) as [b [Hb Hhead] ].
      destruct Hb as [<-|[] ]; destruct B; simpl in Hhead; try discriminate.
      eauto using Cast_int.
    + destruct (rt_merge_inv HR) as [B1 [B2 [H1 [H2 Hspl] ] ] ].
      destruct (@subtype_split_choice nil A B1 B2 B Hspl HO HS) as [HS1|HS2].
      * destruct (IH (size_exp v1 + size_typ B) ltac:(simpl in Hn; lia) v1 B1 B ltac:(lia)
          HV1 H1 HW HS1) as [u Hu].
        eexists; apply Cast_mergel; eauto using rt_lc.
      * destruct (IH (size_exp v2 + size_typ B) ltac:(simpl in Hn; lia) v2 B2 B ltac:(lia)
          HV2 H2 HW HS2) as [u Hu].
        eexists; apply Cast_merger; eauto using rt_lc.
Qed.

Lemma rt_value_prevalue : forall v, value v -> forall A, runtime_typing nil nil v Inf A -> prevalue v.
Proof.
  intros v H; induction H; intros T HT; try solve [inversion HT].
  all: try solve [constructor; eauto using lc_e_rcd].
  destruct (rt_merge_inv HT) as [B [C [HB [HC _] ] ] ]; eauto using PV_merge.
Qed.

Lemma wrapping_unique : forall e A u, wrapping e A u -> forall v, wrapping e A v -> u = v.
Proof.
  intros e A u H; induction H; intros v Hv; inversion Hv; subst; try reflexivity.
  all: try solve [match goal with
    H1 : ord ?A, H2 : spl ?A _ _ |- _ =>
    pose proof (ord_compute H1); pose proof (spl_compute H2); congruence end].
  all: try solve [match goal with
    H1 : notTopLike _ _ |- _ => inversion H1; subst; exfalso; eauto using TL_top, TCW_empty
    end].
  all: try solve [match goal with Hs : spl t_top _ _ |- _ => inversion Hs end].
  f_equal.
  all: match goal with
       H1 : spl ?A ?B ?C, H2 : spl ?A ?B' ?C' |- _ =>
       pose proof (spl_compute H1); pose proof (spl_compute H2);
       assert (B = B') by congruence; assert (C = C') by congruence; subst; eauto
       end.
Qed.

Definition elimination_head (A : typ) : option inla :=
  match A with
  | t_arrow _ _ => Some inla_arrow
  | t_forall _ _ => Some inla_forall
  | t_rcd l _ => Some (inla_label l)
  | _ => None
  end.

Lemma appDist_unique : forall A B, appDist A B -> forall C, appDist A C ->
    elimination_head B = elimination_head C -> B = C.
Proof.
  intros A B H; induction H; intros T HT HE;
    inversion HT; subst; simpl in HE; try discriminate; try reflexivity.
  all: match goal with
    | IH1 : forall T, appDist ?L T -> _ -> _,
      IH2 : forall T, appDist ?R T -> _ -> _,
      H1 : appDist ?L ?X, H2 : appDist ?R ?Y |- _ =>
      let Q1 := fresh "Q1" in let Q2 := fresh "Q2" in
      pose proof (IH1 X H1 ltac:(simpl; congruence)) as Q1;
      pose proof (IH2 Y H2 ltac:(simpl; congruence)) as Q2;
      inversion Q1; inversion Q2; subst; solve [reflexivity]
    end.
Qed.

Lemma papp_unique : forall v a r, papp v a r -> forall s, papp v a s -> r = s.
Proof.
  intros v a r H; induction H; intros s Hs; inversion Hs; subst.
  all: try solve [
    match goal with Hd1 : appDist ?A ?B, Hd2 : appDist ?A ?C |- _ =>
      let HE := fresh "HE" in
      assert (HE : B = C) by (eapply appDist_unique; [exact Hd1 | exact Hd2 | reflexivity]);
      inversion HE; subst; clear HE;
      try match goal with H1 : wrapping ?e ?A ?u, H2 : wrapping ?e ?A ?v |- _ =>
        let E := fresh "E" in assert (E : u = v) by (eapply wrapping_unique; eassumption);
        first [subst u | subst v | rewrite E]
      end; reflexivity
    end].
  f_equal; eauto.
Qed.

Definition intro_ready D G e T : Prop :=
  match e, T with
  | e_abs A b, t_arrow U V =>
      ctx_sub D U A /\ exists L, forall x, x \notin L ->
        runtime_typing D ((x,A)::G) (b ^ x) Chk V
  | e_tabs b, t_forall U V =>
      exists L, forall X, X \notin L ->
        runtime_typing ((X,U)::D) G (open_exp_wrt_typ b (t_tvar_f X)) Chk (V -^ X)
  | e_rcd l b, t_rcd m V => l = m /\ runtime_typing D G b Chk V
  | _, t_and _ _ => True
  | e_abs _ _, _ | e_tabs _, _ | e_rcd _ _, _ => False
  | _, _ => True
  end.

Lemma ready_refl_inf : forall D G e A T,
    runtime_typing D G e Inf A -> intro_ready D G e T.
Proof. intros; inversion H; subst; destruct T; exact I. Qed.

Lemma ready_inter : forall D G e A B T,
    (forall U, appDist A U -> intro_ready D G e U) ->
    (forall U, appDist B U -> intro_ready D G e U) ->
    appDist (t_and A B) T -> intro_ready D G e T.
Proof.
  intros D G e A B T H1 H2 HD; inversion HD; subst;
    try (destruct e; simpl; exact I).
  all: match type of H1 with forall U, appDist ?A U -> _ =>
    match type of H2 with forall U, appDist ?B U -> _ =>
      match goal with HL : appDist A ?X, HR : appDist B ?Y |- _ =>
        specialize (H1 X HL); specialize (H2 Y HR)
      end
    end
  end.
  all: destruct e; simpl in *; try tauto.
  - destruct H1 as [HL [L HB] ], H2 as [HR [R HB'] ]; split.
    + eapply ctx_sub_trans; [apply ctx_sub_l | exact HL].
    + exists (L \u R); intros; apply RT_inter; [apply HB|apply HB']; fsetdec.
  - destruct H1, H2; split; auto using RT_inter.
  - destruct H1 as [L HL], H2 as [R HR].
    exists (L \u R); intros X HX; apply RT_inter.
    + eapply rt_weaken; [apply HL; fsetdec | apply ctx_narrow, ctx_sub_l | auto].
    + eapply rt_weaken; [apply HR; fsetdec | apply ctx_narrow, ctx_sub_r | auto].
Qed.

Lemma rt_intro_ready : forall D G e A, runtime_typing D G e Chk A ->
    forall T, appDist A T -> intro_ready D G e T.
Proof.
  intros D G e A HT. remember Chk as d eqn:Hd in HT.
  induction HT; try discriminate Hd; intros T HD.
  - inversion HD; subst; simpl; eauto.
  - inversion HD; subst; simpl; eauto.
  - inversion HD; subst; simpl; auto.
  - eapply ready_inter; [ | | exact HD]; intros; eauto.
  - eapply ready_refl_inf; eassumption.
Qed.

Lemma poly_split_open : forall B C L R T,
    spl (t_forall B C) (t_forall B L) (t_forall B R) ->
    index_scope T -> spl (C ^-^ T) (L ^-^ T) (R ^-^ T).
Proof.
  intros B C L R T H HT; inversion H; subst.
  pick fresh X for (L0 \u typefv_typ C \u typefv_typ L \u typefv_typ R).
  match goal with Hs : forall X, X \notin L0 -> _ |- _ =>
    pose proof (Hs X ltac:(fsetdec)) as HH
  end.
  pose proof (@spl_subst X T _ _ _ HT (spl_lc HH) HH) as HH'.
  rewrite !type_subst_intro in HH' by (assumption || fsetdec).
  exact HH'.
Qed.

(* A typed elimination of a split value gives one request per component.
   The component result types split the original result type. *)
Inductive request : typ -> arg -> typ -> Prop :=
| Req_term : forall A B C e,
    appDist A (t_arrow B C) -> runtime_typing nil nil e Chk B ->
    request A (arg_exp e) C
| Req_proj : forall A l C,
    appDist A (t_rcd l C) -> request A (arg_la l) C
| Req_type : forall A B C T,
    appDist A (t_forall B C) -> wf_type nil T -> compatible nil T B ->
    request A (arg_typ T) (C ^-^ T).

Local Hint Constructors request : task.

Lemma rt_check_inter : forall D G e A B, runtime_typing D G e Chk (t_and A B) ->
    runtime_typing D G e Chk A /\ runtime_typing D G e Chk B.
Proof.
  intros D G e A B H; inversion H; subst; auto.
  match goal with Hw : wf_type D (t_and A B) |- _ => destruct Hw as [HA HB] end.
  split; eauto using RT_sub, ctx_sub_trans, ctx_sub_l, ctx_sub_r.
Qed.

Lemma request_split : forall A B C a T,
    spl A B C -> wf_type nil A -> request A a T ->
    exists T1 T2, request B a T1 /\ request C a T2 /\ spl T T1 T2.
Proof.
  intros A B C a T HS HW Hr; destruct Hr;
    match goal with H : appDist _ _ |- _ => inversion H; subst end;
    inversion HS; subst.
  - destruct (rt_check_inter H0) as [HL HR].
    exists C1,C2; repeat split; eauto with task.
    apply Sp_and; apply wf_type_lc with (D := nil);
      match goal with
      | H : appDist ?S (t_arrow ?B ?C) |- wf_type nil ?C =>
        apply (proj2 (@appDist_scope nil S (t_arrow B C) H ltac:(destruct HW; assumption)))
      end.
  - destruct (wf_split HW HS) as [HL HR].
    eexists; eexists; repeat split; eauto using AD_refl, wf_type_lc with task.
  - eexists; eexists; repeat split; eauto with task.
    apply Sp_and; apply wf_type_lc with (D := nil);
      match goal with
      | H : appDist ?S (t_rcd ?l ?C) |- wf_type nil ?C =>
        exact (@appDist_scope nil S (t_rcd l C) H ltac:(destruct HW; assumption))
      end.
  - destruct (wf_split HW HS) as [HL HR].
    eexists; eexists; repeat split; eauto using AD_refl, wf_type_lc with task.
  - eexists; eexists; repeat split.
    + eapply Req_type; [eassumption | assumption | eapply K_widen; [eassumption|apply ctx_sub_l] ].
    + eapply Req_type; [eassumption | assumption | eapply K_widen; [eassumption|apply ctx_sub_r] ].
    + apply Sp_and; apply wf_type_lc with (D := nil);
      match goal with
      | H : appDist ?S (t_forall ?B ?C) |- wf_type nil (?C ^-^ _) =>
        eapply wf_open_with; [exact (@appDist_scope nil S (t_forall B C) H
          ltac:(destruct HW; assumption))|assumption]
      end.
  - destruct (wf_split HW HS) as [HL HR].
    eexists; eexists; repeat split.
    + eapply Req_type; [apply AD_refl; eapply wf_type_lc; exact HL | assumption | assumption].
    + eapply Req_type; [apply AD_refl; eapply wf_type_lc; exact HR | assumption | assumption].
    + eapply poly_split_open; [exact HS | eapply wf_type_index; eassumption].
Qed.

Lemma rt_abs_parameter : forall D G e A B,
    runtime_typing D G (e_abs A e) Chk B -> wf_type D A.
Proof.
  intros D G e A B H.
  remember (e_abs A e) as u eqn:Hu in H; remember Chk as d eqn:Hd in H.
  induction H; try discriminate Hu; try discriminate Hd; inversion Hu; subst; eauto.
  inversion H.
Qed.

Lemma papp_exists_typed : forall v, value v -> forall A a T,
    runtime_typing nil nil v Inf A -> request A a T ->
    exists r, papp v a r /\ runtime_typing nil nil r Inf T.
Proof.
  intros v HV; induction HV; intros T a R HT Hr;
    try solve [inversion HT; subst; inversion Hr; subst;
      match goal with H : appDist _ _ |- _ => inversion H end].
  - destruct (rt_anno_inv HT) as [<- HE].
    inversion Hr; subst;
      match goal with Hd : appDist B ?T |- _ =>
        pose proof (rt_intro_ready HE Hd) as HH; simpl in HH
      end; try contradiction.
    destruct HH as [Hsub [L Hbody] ].
    pose proof (rt_abs_parameter HE) as HW.
    destruct (@wrapping_exists (size_typ A) e0 A (le_n _) (rt_lc H3) HW) as [w Hw].
    eexists; split.
    + eapply PApp_abs; eassumption.
    + apply RT_anno. eapply rt_open_term; [exact Hbody |].
      eapply rt_wrap_preservation; eassumption.
  - destruct (rt_anno_inv HT) as [<- HE].
    inversion Hr; subst;
      match goal with Hd : appDist B ?T |- _ =>
        pose proof (rt_intro_ready HE Hd) as HH; simpl in HH
      end; try contradiction.
    destruct HH as [L Hbody].
    eexists; split.
    + eapply PApp_tabs; eauto using wf_type_lc.
    + apply RT_anno. eapply rt_open_type; [exact Hbody | | eassumption | eassumption].
      match goal with Hd : appDist B (t_forall ?U ?V) |- _ =>
        exact (proj1 (@appDist_scope nil B (t_forall U V) Hd (rt_type_scope HT)))
      end.
  - destruct (rt_anno_inv HT) as [<- HE].
    inversion Hr; subst;
      match goal with Hd : appDist B ?T |- _ =>
        pose proof (rt_intro_ready HE Hd) as HH; simpl in HH
      end; try contradiction.
    destruct HH as [<- HH].
    eexists; split.
    + eapply PApp_proj; eassumption.
    + apply RT_anno; exact HH.
  - destruct (rt_merge_inv HT) as [B [C [HB [HC HS] ] ] ].
    destruct (@request_split T B C a R HS (rt_type_scope HT) Hr) as [R1 [R2 [HL [HR HS'] ] ] ].
    destruct (IHHV1 B a R1 HB HL) as [u [Hu Htu] ].
    destruct (IHHV2 C a R2 HC HR) as [w [Hw Htw] ].
    exists (e_merge u w); split; eauto using PApp_merge, RT_merge_parts.
Qed.

Lemma papp_preserves : forall v a r A T,
    value v -> papp v a r -> runtime_typing nil nil v Inf A -> request A a T ->
    runtime_typing nil nil r Inf T.
Proof.
  intros v a r A T Hv Hp Ht Hr.
  destruct (papp_exists_typed Hv Ht Hr) as [r' [Hp' Ht'] ].
  pose proof (papp_unique Hp Hp'); congruence.
Qed.

Inductive bare_intro : exp -> Prop :=
| BI_abs : forall A e, bare_intro (e_abs A e)
| BI_tabs : forall e, bare_intro (e_tabs e)
| BI_rcd : forall l e, bare_intro (e_rcd l e).

Lemma bare_intro_dec : forall e, {bare_intro e}+{~bare_intro e}.
Proof. destruct e; try solve [right; inversion 1]; left; constructor. Qed.

Lemma rt_check_infers : forall D G e A, runtime_typing D G e Chk A ->
    ~ bare_intro e -> exists B, runtime_typing D G e Inf B.
Proof.
  intros D G e A H; remember Chk as d eqn:Hd in H.
  induction H; try discriminate Hd; intro Hnb;
    first [solve [exfalso; apply Hnb; constructor] | eauto].
Qed.

Lemma prevalue_not_bare : forall e, prevalue e -> ~ bare_intro e.
Proof. intros e H Hb; destruct Hb; inversion H. Qed.

Lemma rt_check_cast : forall e A, runtime_typing nil nil e Chk A ->
    value e -> prevalue e -> exists u, casting e A u.
Proof.
  intros e A H.
  remember (@nil (atom * typ)) as D eqn:HD in H at 1; remember (@nil (atom * typ)) as G eqn:HG in H;
    remember Chk as d eqn:Hd in H.
  induction H; try discriminate Hd; intros HV HP; subst.
  all: try solve [inversion HP].
  - destruct (IHruntime_typing1 eq_refl eq_refl eq_refl HV HP) as [u Hu].
    destruct (IHruntime_typing2 eq_refl eq_refl eq_refl HV HP) as [v Hv].
    eapply ex_intro. eapply Cast_and; [apply Sp_and | exact Hu | exact Hv];
      eapply wf_type_lc, rt_type_scope; eassumption.
  - eapply (casting_exists (n := size_exp e + size_typ B)); eauto.
Qed.

Lemma annotation_progress : forall e A, runtime_typing nil nil e Chk A ->
    value e -> value (e_anno e A) \/ exists u, step (e_anno e A) u.
Proof.
  intros e A HT HV.
  destruct (bare_intro_dec e) as [Hb|Hb].
  - left; pose proof (rt_lc HT) as HE.
    pose proof (@wf_type_lc nil A (rt_type_scope HT)) as HA.
    destruct Hb; inversion HE; subst; eauto using V_abs, V_tabs, V_rcd.
  - destruct (rt_check_infers HT Hb) as [B HB].
    pose proof (rt_value_prevalue HV HB) as HP.
    destruct (rt_check_cast HT HV HP) as [u Hu].
    right; eauto using Step_annov.
Qed.

Lemma rt_preservation : forall e d A, runtime_typing nil nil e d A ->
    forall e', step e e' -> runtime_typing nil nil e' d A.
Proof.
  intros e d A H.
  remember (@nil (atom * typ)) as D eqn:HD in H at 1; remember (@nil (atom * typ)) as G eqn:HG in H.
  induction H; intros e' HS; subst; try solve [inversion HS].
  all: inversion HS; subst; try solve [eauto 7 with task].
  - eapply papp_preserves; eauto with task.
  - eapply papp_preserves; eauto with task.
  - eapply papp_preserves; eauto with task.
  - match goal with Hp : prevalue _ |- _ =>
      destruct (rt_check_infers H (prevalue_not_bare Hp)) as [T HT]
    end.
    eapply rt_cast_preservation; eauto using rt_type_scope.
  - apply RT_anno. eapply rt_open_term; [eassumption|].
    eapply RT_fix; eassumption.
Qed.

Lemma merge_progress : forall e u,
    (value e \/ exists e', step e e') ->
    (value u \/ exists u', step u u') ->
    value (e_merge e u) \/ exists r, step (e_merge e u) r.
Proof.
  intros e u [HV|[e' HS] ] [HV'|[u' HS'] ];
    eauto using V_merge, Step_merge, Step_mergel, Step_merger.
Qed.

Lemma rt_progress : forall e d A, runtime_typing nil nil e d A ->
    value e \/ exists e', step e e'.
Proof.
  intros e d A H.
  remember (@nil (atom * typ)) as D eqn:HD in H at 1; remember (@nil (atom * typ)) as G eqn:HG in H.
  induction H; subst; try solve [eauto using V_unit, V_lit, merge_progress].
  - inversion H.
  - left; apply V_bareAbs.
    + eapply wf_type_lc; eassumption.
    + eapply rt_lc; eauto using RT_abs.
  - destruct (IHruntime_typing1 eq_refl eq_refl) as [HV|[r HS] ].
    + assert (Hr : request A (arg_exp u) C) by (eapply Req_term; eassumption).
      destruct (papp_exists_typed HV H Hr) as [r [Hp _] ]; right; eauto using Step_papp.
    + right; eauto using Step_appl, rt_lc.
  - left; apply V_bareTabs. eapply rt_lc; eauto using RT_tabs.
  - destruct (IHruntime_typing eq_refl eq_refl) as [HV|[r HS] ].
    + assert (Hr : request B (arg_typ A) (C2 ^-^ A)) by (eapply Req_type; eassumption).
      destruct (papp_exists_typed HV H Hr) as [r [Hp _] ]; right; eauto using Step_ptapp.
    + right; eauto using Step_tapp, wf_type_lc.
  - destruct (IHruntime_typing eq_refl eq_refl) as [HV|[r HS] ].
    + assert (Hr : request A (arg_la l) C) by (eapply Req_proj; eassumption).
      destruct (papp_exists_typed HV H Hr) as [r [Hp _] ]; right; eauto using Step_pproj.
    + right; eauto using Step_proj.
  - left; eauto using V_bareRcd, rt_lc.
  - destruct (IHruntime_typing eq_refl eq_refl) as [HV|[r HS] ].
    + apply annotation_progress; assumption.
    + right; eauto using Step_anno, wf_type_lc, rt_type_scope.
  - right; eexists; apply Step_fix; eauto using rt_lc, RT_fix, wf_type_lc.
Qed.

Local Unset Implicit Arguments.

Theorem type_safety : forall e e' A,
    Typing nil nil e Inf A ->
    e ->* e' ->
    value e' \/ exists e'', step e' e''.
Proof.
  intros e e' A HT HS.
  apply typing_runtime in HT.
  induction HS; eauto using rt_progress, rt_preservation.
Qed.
