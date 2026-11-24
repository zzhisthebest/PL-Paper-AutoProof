Set Implicit Arguments.

From TLC Require Import LibLN.

Require Import Main_ott Main_Infra.

Implicit Types x : var.

Implicit Types G : env.

Fixpoint remove_anno (e : trm) {struct e} : trm :=
  match e with
  | trm_var_b i        => trm_var_b i
  | trm_var_f x        => trm_var_f x
  | trm_star          => trm_star
  | trm_top           => trm_top
  | trm_app t1 t2     => trm_app (remove_anno t1) (remove_anno t2)
  | trm_abs t0 t1 t2  => trm_abs (remove_anno t0) (remove_anno t1) (remove_anno t2)
  | trm_prod t0 t1 t2 => trm_prod (remove_anno t0) (remove_anno t1) (remove_anno t2)
  | trm_castup t1 t2  => trm_castup (remove_anno t1) (remove_anno t2)
  | trm_castdn t1     => trm_castdn (remove_anno t1)
  | trm_anno t1 t2    => remove_anno t1
  end.

Notation "[# e #]" := (remove_anno e) (at level 2).

Definition rem_anno_env (p:binding) :=
  match p with
  | bind_sub e A => bind_sub (remove_anno e) (remove_anno A)
  end.

Notation "{# E #}" := (map rem_anno_env E) (at level 2).

Inductive dsub : env -> trm -> trm -> Prop :=
  | dsub_star : forall G, ok G -> dsub G trm_star trm_star
  | dsub_var_refl : forall G x e A,
      ok G -> binds x (bind_sub e A) G -> dsub G (trm_var_f x) (trm_var_f x)
  | dsub_var_trans : forall e1 A G x e2,
      binds x (bind_sub e1 A) G -> dsub G e1 e2 ->
      dsub G (trm_var_f x) e2
  | dsub_top : forall G e,
      ok G -> lc_trm e -> dsub G e trm_top
  | dsub_lam : forall L G e1 e2 e3 A,
      ok G ->
      (forall x, x \notin L -> dsub (G & x ~ bind_sub [#e3#] [#A#]) (e1 ^ x) (e2 ^ x)) ->
      dsub G (trm_abs e3 A e1) (trm_abs e3 A e2)
  | dsub_app : forall G e1 e2 A,
      lc_trm A ->
      dsub G e1 e2 -> dsub G (trm_app e1 A) (trm_app e2 A)
  | dsub_pi : forall L G e A B C D,
      dsub G C A ->
      (forall x, x \notin L -> dsub (G & x ~ bind_sub [#e#] [#C#]) (B ^ x) (D ^ x)) ->
      dsub G (trm_prod e A B) (trm_prod e C D)
  | dsub_castup : forall G A e1 e2,
      lc_trm A -> dsub G e1 e2 -> dsub G (trm_castup A e1) (trm_castup A e2)
  | dsub_castdn : forall G e1 e2,
      dsub G e1 e2 -> dsub G (trm_castdn e1) (trm_castdn e2).

Inductive dir := inf | chk.

Inductive dtyping : dir -> env -> trm -> trm -> Prop :=
  | dtyping_star : forall G,
      dwf G -> dtyping inf G trm_star trm_star
  | dtyping_var : forall e G x A,
      dwf G -> binds x (bind_sub e A) G -> dtyping inf G (trm_var_f x) A
  | dtyping_top : forall G A,
      dtyping chk G A trm_star -> dtyping chk G trm_top A
  | dtyping_lam : forall L G e1 e2 A B,
      dtyping chk G e1 [#A#] ->
      dtyping chk G A trm_star ->
      (forall x, x \notin L ->
                 dtyping inf (G & x ~ bind_sub [#e1#] [#A#]) (e2 ^ x) (B ^ x)) ->
      dtyping inf G (trm_abs e1 A e2) (trm_prod [#e1#] [#A#] B)
  | dtyping_app : forall e3 G e A B C,
      dtyping chk G A B ->
      dsub G [#A#] e3 ->
      dtyping inf G e (trm_prod e3 B C) ->
      dtyping inf G (trm_app e A) (C ^^ [#A#])
  | dtyping_pi : forall L G e A B,
      dtyping chk G e [#A#] ->
      dtyping chk G A trm_star ->
      (forall x, x \notin L ->
        dtyping chk (G & x ~ bind_sub [#e#] [#A#]) (B ^ x) trm_star) ->
      dtyping inf G (trm_prod e A B) trm_star
  | dtyping_castup : forall G e A B,
      dtyping chk G B trm_star ->
      dtyping inf G e A ->
      reduct [#B#] [#A#] ->
      dtyping inf G (trm_castup B e) [#B#]
  | dtyping_castdn : forall G e A B,
      dtyping chk G B trm_star ->
      dtyping inf G e A ->
      reduct [#A#] [#B#] ->
      dtyping chk G (trm_castdn e) B
  | dtyping_anno : forall G e A,
      dtyping chk G e A ->
      dtyping chk G A trm_star ->
      dtyping inf G (trm_anno e A) [#A#]
  | dtyping_sub : forall A G e B,
      dtyping inf G e A ->
      dsub G A [#B#] ->
      dtyping chk G B trm_star ->
      dtyping chk G e B
  | dtyping_chk : forall G e A,
      dtyping inf G e A ->
      dtyping chk G e A

with dwf : env -> Prop :=
  | dwf_nil : dwf empty
  | dwf_cons : forall G x e A,
      x # G ->
      dtyping chk G e [#A#] ->
      dtyping chk G A trm_star ->
      dwf (G & x ~ bind_sub [#e#] [#A#]).

#[local] Hint Constructors lc_trm sub wf : core.
#[local] Hint Resolve ok_empty ok_push binds_push_eq binds_push_neq : core.

Lemma erase_open_rec : forall t k u,
  [#open_trm_wrt_trm_rec k u t#] =
  open_trm_wrt_trm_rec k [#u#] [#t#].
Proof.
  induction t; intros; simpl; try case_if; try reflexivity; congruence.
Qed.

Lemma erase_open : forall t u, [#t ^^ u#] = [#t#] ^^ [#u#].
Proof. exact (fun t u => erase_open_rec t 0 u). Qed.

Lemma erase_idem : forall t, [#[#t#]#] = [#t#].
Proof. induction t; simpl; congruence. Qed.

Fixpoint closed_at (k : nat) (t : trm) : Prop :=
  match t with
  | trm_var_b n => n < k
  | trm_var_f _ | trm_star | trm_top => True
  | trm_app s t | trm_castup s t | trm_anno s t =>
      closed_at k s /\ closed_at k t
  | trm_abs e A b | trm_prod e A b =>
      closed_at k e /\ closed_at k A /\ closed_at (S k) b
  | trm_castdn s => closed_at k s
  end.

From Stdlib Require Import Lia.

Lemma closed_open_var : forall t k x,
  closed_at k (open_trm_wrt_trm_rec k (trm_var_f x) t) <->
  closed_at (S k) t.
Proof.
  induction t; intros; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3;
    try tauto.
  case_if; simpl; lia.
Qed.

Lemma lc_closed : forall t, lc_trm t -> closed_at 0 t.
Proof.
  induction 1; simpl; try tauto;
    match goal with
    | IH : forall x, x \notin ?L -> closed_at 0 (?b ^ x) |- _ =>
        destruct (var_fresh L) as [x Hx];
        specialize (IH x Hx); apply closed_open_var in IH; tauto
    end.
Qed.

Ltac split_hyps := repeat match goal with H : _ /\ _ |- _ => destruct H end.
Lemma closed_open_same : forall t n k u,
  closed_at n t -> n <= k -> open_trm_wrt_trm_rec k u t = t.
Proof.
  induction t; simpl; intros; try solve [split_hyps; f_equal; eauto with arith].
  case_if; subst; lia || reflexivity.
Qed.

Lemma subst_open_rec : forall t k u x v,
  lc_trm u ->
  subst_trm u x (open_trm_wrt_trm_rec k v t) =
  open_trm_wrt_trm_rec k (subst_trm u x v) (subst_trm u x t).
Proof.
  induction t; intros; simpl; try case_if; try reflexivity; try congruence.
  symmetry; eapply closed_open_same; [eapply lc_closed; eassumption | lia].
  all: f_equal; auto.
Qed.

Lemma subst_open : forall t u x v,
  lc_trm u -> subst_trm u x (t ^^ v) =
  subst_trm u x t ^^ subst_trm u x v.
Proof. exact (fun t u x v => @subst_open_rec t 0 u x v). Qed.

Lemma subst_open_var : forall t u x y,
  lc_trm u -> y <> x -> subst_trm u x (t ^ y) = subst_trm u x t ^ y.
Proof.
  intros; rewrite subst_open by assumption; simpl; case_if; congruence.
Qed.

Lemma subst_lc : forall t u x,
  lc_trm t -> lc_trm u -> lc_trm (subst_trm u x t).
Proof.
  intros t u x H; induction H; intro Hu; simpl; try case_if; eauto;
    [eapply lc_trm_abs with (L := L \u \{x}) |
     eapply lc_trm_prod with (L := L \u \{x})]; eauto;
    intros y Hy; rewrite <- subst_open_var by (assumption || notin_solve);
    eauto.
Qed.

Lemma subst_fresh : forall t u x,
  x \notin fv_trm t -> subst_trm u x t = t.
Proof.
  induction t; simpl; intros; try case_if; subst; try notin_false;
    f_equal; eauto.
Qed.

Lemma fv_open_incl : forall t k u, fv_trm t \c fv_trm (open_trm_wrt_trm_rec k u t).
Proof.
  induction t; intros; simpl; try case_if;
    auto using subset_empty_l, subset_refl, subset_union_2.
Qed.

Lemma fv_open_body : forall L (D : vars) t,
  (forall x, x \notin L -> fv_trm (t ^ x) \c (\{x} \u D)) ->
  fv_trm t \c D.
Proof.
  intros L G t H z Hz.
  destruct (var_fresh (L \u \{z})) as [x Hx].
  specialize (H x ltac:(notin_solve)).
  assert (Hz' : z \in fv_trm (t ^ x)) by
    (eapply fv_open_incl; exact Hz).
  specialize (H z Hz'); rewrite in_union, in_singleton in H.
  destruct H as [-> | H]; [notin_false | exact H].
Qed.

Lemma reduct_subst : forall t s u x,
  reduct t s -> lc_trm u ->
  reduct (subst_trm u x t) (subst_trm u x s).
Proof.
  induction 1; intros; simpl; eauto using reduct_app, reduct_castdn, reduct_castelim, subst_lc.
  rewrite subst_open by assumption.
  apply reduct_beta; eauto using subst_lc.
  exact (@subst_lc (trm_abs e3 A e1) u x H1 H3).
Qed.

Lemma subst_intro : forall t u x,
  lc_trm u -> x \notin fv_trm t -> subst_trm u x (t ^ x) = t ^^ u.
Proof.
  intros; rewrite subst_open, subst_fresh by assumption.
  simpl; case_if; congruence.
Qed.

Scheme sub_ind_mut := Induction for sub Sort Prop
with wf_ind_mut := Induction for wf Sort Prop.
Combined Scheme sub_wf_ind from sub_ind_mut, wf_ind_mut.

Lemma sub_wf : forall G s t A, sub G s t A -> wf G.
Proof. induction 1; eauto. Qed.

Lemma wf_ok : forall G, wf G -> ok G.
Proof.
  assert (H : (forall G s t A, sub G s t A -> ok G) /\
              (forall G, wf G -> ok G)) by (apply sub_wf_ind; eauto).
  exact (proj2 H).
Qed.

Lemma sub_left_refl : forall G s t A, sub G s t A -> sub G s s A.
Proof.
  induction 1; eauto 6 using sub_wf.
Qed.

Lemma fv_open_upper : forall t k u z,
  z \in fv_trm (open_trm_wrt_trm_rec k u t) ->
  z \in fv_trm t \/ z \in fv_trm u.
Proof.
  induction t; intros k u z H; simpl in *; try case_if; try tauto.
  all: repeat rewrite in_union in *;
    repeat match goal with H : _ \/ _ |- _ => destruct H end;
    repeat match goal with
    | IH : forall k u z, _ -> _, H : _ \in fv_trm (open_trm_wrt_trm_rec _ _ _) |- _ =>
        first [apply IH in H | fail 1]
    end; tauto.
Qed.

Lemma binds_dom : forall G x (b : binding), binds x b G -> x \in dom G.
Proof. eauto using get_some_inv, binds_get. Qed.

Lemma subset_union_same : forall (P Q R : vars), P \c R -> Q \c R -> (P \u Q) \c R.
Proof. intros P Q R HP HQ x H; rewrite in_union in H; destruct H; auto. Qed.

Definition scoped_env G :=
  forall x e A, binds x (bind_sub e A) G ->
    fv_trm e \c dom G /\ fv_trm A \c dom G.

Lemma scope_binds : forall G, wf G -> scoped_env G.
Proof.
  assert (H : (forall G s t A, sub G s t A -> scoped_env G /\
                     fv_trm s \c dom G /\ fv_trm t \c dom G /\ fv_trm A \c dom G) /\
              (forall G, wf G -> scoped_env G)).
  { apply sub_wf_ind; intros; split_hyps;
      try (split; [assumption|]);
      try solve [simpl; auto using subset_empty_l].
    - match goal with H : scoped_env ?G, Hb : binds ?x (bind_sub ?e ?A) ?G |- _ =>
        destruct (H _ _ _ Hb) as [? ?]
      end.
      simpl; repeat split; auto; intros z Hz; rewrite in_singleton in Hz;
        subst; eauto using binds_dom.
    - simpl; repeat split; auto; intros z Hz; rewrite in_singleton in Hz;
        subst; eauto using binds_dom.
    - simpl; repeat split; repeat apply subset_union_same; auto.
      all: eapply fv_open_body with (L := L); intros;
        rewrite <- dom_push with (v := bind_sub e1 A);
        match goal with
        | IH : forall y, y \notin ?L0 -> scoped_env _ /\ _ |- _ =>
          let HS := fresh in pose proof (IH _ ltac:(eassumption)) as HS;
          split_hyps; assumption
        end.
    - simpl; repeat split; try (apply subset_union_same; assumption).
      intros z Hz; apply fv_open_upper in Hz; simpl in *.
      destruct Hz as [Hz | Hz]; [|eauto].
      match goal with H : fv_trm e3 \u fv_trm B \u fv_trm C \c dom G |- _ =>
        apply H; repeat rewrite in_union; tauto
      end.
    - simpl; repeat split; repeat apply subset_union_same; auto using subset_empty_l.
      all: eapply fv_open_body with (L := L); intros;
        rewrite <- dom_push with (v := bind_sub e A');
        match goal with
        | IH : forall y, y \notin ?L0 -> scoped_env (?G0 & y ~ bind_sub ?e0 ?A0) /\ _ |- _ =>
          let HS := fresh in pose proof (IH _ ltac:(eassumption)) as HS;
          split_hyps; assumption
        end.
    - simpl; repeat split; repeat apply subset_union_same; auto.
    - unfold scoped_env; intros; exfalso; eapply binds_empty_inv; eassumption.
    - unfold scoped_env; intros y f B Hb.
      apply binds_push_inv in Hb; destruct Hb as [[-> Heq] | [Hneq Hb]].
      + inversion Heq; subst.
        rewrite dom_push; split; intros z Hz; rewrite in_union; eauto.
      + match goal with H : scoped_env G |- _ => destruct (H _ _ _ Hb) as [? ?] end.
        rewrite dom_push; split; intros z Hz; rewrite in_union; eauto.
  }
  exact (proj2 H).
Qed.

Lemma sub_lc : forall G s t A, sub G s t A -> lc_trm s /\ lc_trm t.
Proof.
  induction 1; split_hyps; eauto.
  - split; eapply lc_trm_abs with (L := L); eauto.
    all: intros x Hx; destruct (H2 x Hx); assumption.
  - split; eapply lc_trm_prod with (L := L); eauto.
    all: intros x Hx; destruct (H3 x Hx); destruct (H5 x Hx); assumption.
Qed.

Definition preserves_bindings (G D : env) :=
  forall x b, binds x b G -> binds x b D.

Lemma preserves_push : forall G D x b,
  preserves_bindings G D -> preserves_bindings (G & x ~ b) (D & x ~ b).
Proof.
  unfold preserves_bindings; intros G D x b H y a Hy.
  apply binds_push_inv in Hy; destruct Hy as [[-> ->] | [? ?]]; eauto.
Qed.

Lemma sub_weaken : forall G s t A, sub G s t A ->
  forall D, wf D -> preserves_bindings G D -> sub D s t A.
Proof.
  induction 1; intros D0 HD HP; eauto 6;
    try solve [eapply sub_var_refl; eauto | eapply sub_var_trans; eauto].
  - eapply sub_abs with (L := L \u dom D0); eauto.
    all: intros x Hx; eauto 7 using preserves_push.
  - assert (Hdom : sub D0 A' A trm_star) by eauto.
    assert (He : sub D0 e e A') by eauto.
    assert (HA : sub D0 A A trm_star) by eauto.
    eapply sub_prod with (L := L \u dom D0); eauto.
    + intros x Hx; eapply H3; eauto 7 using preserves_push.
    + intros x Hx; eapply H5; eauto 7 using preserves_push, sub_left_refl.
Qed.

Lemma sub_weaken_push : forall G s t A x b,
  sub G s t A -> wf (G & x ~ b) -> sub (G & x ~ b) s t A.
Proof.
  intros; eapply sub_weaken; eauto.
  unfold preserves_bindings; intros; eapply binds_concat_left_ok; eauto using wf_ok.
Qed.

Lemma wf_binds_typing : forall G, wf G -> forall x e A,
  binds x (bind_sub e A) G -> sub G e e A /\ sub G A A trm_star.
Proof.
  set (P := fun G : env => forall x e A, binds x (bind_sub e A) G ->
                 sub G e e A /\ sub G A A trm_star).
  assert (H : (forall G s t A, sub G s t A -> P G) /\ (forall G, wf G -> P G)).
  { apply sub_wf_ind; intros; try assumption.
    - unfold P; intros; exfalso; eapply binds_empty_inv; eassumption.
    - unfold P in *; intros y f B Hb.
      apply binds_push_inv in Hb; destruct Hb as [[-> Heq] | [Hneq Hb]].
      + inversion Heq; subst; split; eauto using sub_weaken_push.
      + match goal with IH : forall x e A, binds x (bind_sub e A) G -> _ |- _ =>
          destruct (IH _ _ _ Hb)
        end.
        split; eauto using sub_weaken_push. }
  exact (proj2 H).
Qed.

Definition type_lift G A B :=
  forall s t, sub G s t A -> sub G s t B.

Definition left_parts G s T :=
  match s with
  | trm_var_f x => exists e A, binds x (bind_sub e A) G /\ type_lift G A T
  | trm_abs e A b => exists L B,
      sub G e e A /\ sub G A A trm_star /\
      (forall x, x \notin L -> sub (G & x ~ bind_sub e A) (b ^ x) (b ^ x) (B ^ x)) /\
      (forall x, x \notin L -> sub (G & x ~ bind_sub e A) (B ^ x) (B ^ x) trm_star) /\
      type_lift G (trm_prod e A B) T
  | trm_app f a => exists e B C,
      sub G f f (trm_prod e B C) /\ sub G a e B /\ type_lift G (C ^^ a) T
  | trm_prod e A B => exists L,
      sub G e e A /\ sub G A A trm_star /\
      (forall x, x \notin L -> sub (G & x ~ bind_sub e A) (B ^ x) (B ^ x) trm_star) /\
      type_lift G trm_star T
  | trm_castup B e => exists A,
      sub G B B trm_star /\ sub G e e A /\ reduct B A /\ type_lift G B T
  | trm_castdn e => exists A B,
      sub G B B trm_star /\ sub G e e A /\ reduct A B /\ type_lift G B T
  | _ => True
  end.

Lemma sub_left_parts : forall G s t T, sub G s t T -> left_parts G s T.
Proof.
  induction 1; simpl in *; try exact I.
  all: try solve [unfold type_lift; eauto 9 using sub_left_refl].
  - destruct e1; simpl in *; try exact I; split_hyps;
      repeat match goal with H : exists _, _ |- _ => destruct H; split_hyps end;
      unfold type_lift in *; eauto 10.
Qed.

Definition right_parts G t :=
  match t with
  | trm_abs e A b => exists L, forall x, x \notin L ->
      exists s T, sub (G & x ~ bind_sub e A) s (b ^ x) T
  | trm_app f _ | trm_castup _ f | trm_castdn f =>
      exists s T, sub G s f T
  | trm_prod e A B => sub G e e A /\ sub G A A trm_star /\
      (exists L, forall x, x \notin L ->
          exists s, sub (G & x ~ bind_sub e A) s (B ^ x) trm_star)
  | _ => True
  end.

Lemma sub_right_parts : forall G s t T, sub G s t T -> right_parts G t.
Proof.
  induction 1; simpl; eauto using sub_left_refl.
  - repeat split; eauto using sub_left_refl.
Qed.

Definition refines G D :=
  forall x e A, binds x (bind_sub e A) G ->
    exists C, binds x (bind_sub e C) D /\ type_lift D C A /\
              (C = A \/ sub D C A trm_star).

Lemma refines_push : forall G D x e A,
  refines G D -> wf (D & x ~ bind_sub e A) ->
  refines (G & x ~ bind_sub e A) (D & x ~ bind_sub e A).
Proof.
  unfold refines; intros G D x e A HR HW y f B Hb.
  apply binds_push_inv in Hb; destruct Hb as [[-> Heq] | [Hneq Hb]].
  - inversion Heq; subst. exists A; unfold type_lift; eauto.
  - destruct (HR _ _ _ Hb) as (C & HC & _ & [-> | HCA]).
    + exists B; unfold type_lift; eauto.
    + pose proof (sub_weaken_push HCA HW) as H.
      exists C; unfold type_lift; repeat split; eauto.
Qed.

(* A narrower variable binding changes the type at which its bound is
   compared. The second conclusion transports a comparison at any type
   already established for its left term in the new context. *)
Lemma sub_refine_retype : forall G s t T, sub G s t T ->
  forall D, wf D -> refines G D ->
    sub D s t T /\ (forall U, sub D s s U -> sub D s t U).
Proof.
  induction 1; intros D0 HW HR.
  - split; eauto.
  - destruct (HR _ _ _ H0) as (C & HC & Hlift & _).
    split; eauto.
  - destruct (HR _ _ _ H) as (C & HC & Hlift & _).
    destruct (wf_binds_typing HW HC) as [He HCtype].
    destruct (IHsub D0 HW HR) as [_ Hretype].
    assert (Hvar : sub D0 (trm_var_f x5) e2 C) by eauto.
    split; [apply Hlift; exact Hvar |].
    intros U Hself. apply sub_left_parts in Hself.
    simpl in Hself. destruct Hself as (f & B & Hb & Hup).
    pose proof (binds_functional HC Hb) as Heq.
    inversion Heq; subst; eauto.
  - destruct (IHsub D0 HW HR); split; intros; eauto.
  - destruct (IHsub D0 HW HR); split; intros; eauto.
  - assert (He : sub D0 e1 e1 A) by (edestruct IHsub1; eauto).
    assert (HA : sub D0 A A trm_star) by (edestruct IHsub2; eauto).
    assert (Hb : forall x, x \notin L \u dom D0 ->
        wf (D0 & x ~ bind_sub e1 A) /\ refines (G & x ~ bind_sub e1 A) (D0 & x ~ bind_sub e1 A)).
    { intros; split; eauto using refines_push. }
    split.
    + eapply sub_abs with (L := L \u dom D0); eauto.
      all: intros x Hx; destruct (Hb x Hx) as [Hw Hr].
      * exact (proj1 (H2 x ltac:(notin_solve) _ Hw Hr)).
      * exact (proj1 (H4 x ltac:(notin_solve) _ Hw Hr)).
    + intros U Hself. apply sub_left_parts in Hself; simpl in Hself.
      destruct Hself as (K & C & _ & _ & Hbody & Htype & Hlift).
      apply Hlift; eapply sub_abs with (L := L \u K \u dom D0); eauto.
      intros x Hx; destruct (Hb x ltac:(notin_solve)) as [Hw Hr].
      apply (proj2 (H2 x ltac:(notin_solve) _ Hw Hr)); eauto.
  - destruct (IHsub1 D0 HW HR) as [Hf Hretype].
    destruct (IHsub2 D0 HW HR) as [Ha _].
    split; eauto.
    intros U Hself. apply sub_left_parts in Hself; simpl in Hself.
    destruct Hself as (e & B0 & C0 & Hfun & Harg & Hlift).
    apply Hlift; eauto.
  - destruct (IHsub1 D0 HW HR) as [Hdom _].
    destruct (IHsub2 D0 HW HR) as [He _].
    destruct (IHsub3 D0 HW HR) as [HA _].
    assert (Hp : sub D0 (trm_prod e A B) (trm_prod e A' B') trm_star).
    { eapply sub_prod with (L := L \u dom D0); eauto.
      - intros x Hx. assert (HWx : wf (D0 & x ~ bind_sub e A)) by eauto 7.
        exact (proj1 (H3 x ltac:(notin_solve) _ HWx (refines_push HR HWx))).
      - intros x Hx. assert (HWx : wf (D0 & x ~ bind_sub e A')) by eauto using sub_left_refl.
        exact (proj1 (H5 x ltac:(notin_solve) _ HWx (refines_push HR HWx))). }
    split; [exact Hp|].
    intros U Hself. apply sub_left_parts in Hself; simpl in Hself.
    destruct Hself as (K & _ & _ & _ & Hlift); eauto.
  - destruct (IHsub1 D0 HW HR) as [HB _].
    destruct (IHsub2 D0 HW HR) as [He Hretype].
    split; eauto.
    intros U Hself. apply sub_left_parts in Hself; simpl in Hself.
    destruct Hself as (C & HC & Hbody & Hred & Hlift).
    apply Hlift; eauto.
  - destruct (IHsub1 D0 HW HR) as [HB _].
    destruct (IHsub2 D0 HW HR) as [He Hretype].
    split; eauto.
    intros U Hself. apply sub_left_parts in Hself; simpl in Hself.
    destruct Hself as (C & E & HE & Hbody & Hred & Hlift).
    apply Hlift; eauto.
  - destruct (IHsub1 D0 HW HR); destruct (IHsub2 D0 HW HR); eauto.
Qed.

Lemma sub_narrow_push : forall G x e A C s t T,
  sub (G & x ~ bind_sub e A) s t T ->
  sub G e e C -> sub G C A trm_star ->
  sub (G & x ~ bind_sub e C) s t T.
Proof.
  intros G x e A C s t T H He HCA.
  pose proof (proj2 (ok_push_inv (wf_ok (sub_wf H)))) as Hx.
  assert (HW : wf (G & x ~ bind_sub e C)) by eauto using sub_left_refl.
  cut (refines (G & x ~ bind_sub e A) (G & x ~ bind_sub e C)).
  { intro HR; exact (proj1 (sub_refine_retype H HW HR)). }
  unfold refines; intros y f B Hb.
  apply binds_push_inv in Hb; destruct Hb as [[-> Heq] | [Hneq Hb]].
  - inversion Heq; subst. pose proof (sub_weaken_push HCA HW).
    exists C; unfold type_lift; repeat split; eauto.
  - exists B; unfold type_lift; eauto.
Qed.

(* The structural comparison on erased terms. Context lookups use only bounds. *)
Inductive shape_sub : env -> trm -> trm -> Prop :=
  | shape_refl : forall G t, shape_sub G t t
  | shape_top : forall G t, shape_sub G t trm_top
  | shape_var : forall G x e A t,
      binds x (bind_sub e A) G -> shape_sub G e t ->
      shape_sub G (trm_var_f x) t
  | shape_abs : forall L G e A b c,
      (forall x, x \notin L -> shape_sub (G & x ~ bind_sub e A) (b ^ x) (c ^ x)) ->
      shape_sub G (trm_abs e A b) (trm_abs e A c)
  | shape_app : forall G f g a,
      shape_sub G f g -> shape_sub G (trm_app f a) (trm_app g a)
  | shape_prod : forall L G e A B C D,
      shape_sub G C A ->
      (forall x, x \notin L -> shape_sub (G & x ~ bind_sub e C) (B ^ x) (D ^ x)) ->
      shape_sub G (trm_prod e A B) (trm_prod e C D)
  | shape_up : forall G A e f,
      shape_sub G e f -> shape_sub G (trm_castup A e) (trm_castup A f)
  | shape_down : forall G e f,
      shape_sub G e f -> shape_sub G (trm_castdn e) (trm_castdn f).

#[local] Hint Constructors shape_sub : core.

Lemma sub_shape : forall G s t A, sub G s t A -> shape_sub G s t.
Proof.
  induction 1; eauto.
Qed.

Lemma shape_move : forall G s t, shape_sub G s t -> forall D,
  (forall x e A, binds x (bind_sub e A) G -> exists B, binds x (bind_sub e B) D) ->
  shape_sub D s t.
Proof.
  induction 1; intros D0 Hmove; eauto.
  - destruct (Hmove _ _ _ H) as [B HB]; eauto.
  - eapply shape_abs with (L := L).
    intros x Hx; eapply H0; eauto.
    intros y f C Hb; apply binds_push_inv in Hb;
      destruct Hb as [[-> Heq] | [Hneq Hb]].
    + inversion Heq; subst; eauto.
    + destruct (Hmove _ _ _ Hb); eauto.
  - eapply shape_prod with (L := L); eauto.
    intros x Hx; eapply H1; eauto.
    intros y f B0 Hb; apply binds_push_inv in Hb;
      destruct Hb as [[-> Heq] | [Hneq Hb]].
    + inversion Heq; subst; eauto.
    + destruct (Hmove _ _ _ Hb); eauto.
Qed.

Lemma shape_change_type : forall G x e A C s t,
  shape_sub (G & x ~ bind_sub e A) s t ->
  shape_sub (G & x ~ bind_sub e C) s t.
Proof.
  intros; eapply shape_move; [eassumption|].
  intros y f B Hb; apply binds_push_inv in Hb;
    destruct Hb as [[-> Heq] | [Hneq Hb]].
  - inversion Heq; subst; eauto.
  - eauto.
Qed.

Ltac shape_predecessor K :=
  match type of K with shape_sub _ _ ?m => remember m as middle in K end;
  induction K; try solve [discriminate]; inversion Heqmiddle; subst;
  try solve [eauto 6].

(* Compose in both directions so the product domain can use the
   induction hypothesis in the opposite order. *)
Lemma shape_compose : forall G s t, shape_sub G s t ->
  (forall u, shape_sub G t u -> shape_sub G s u) /\
  (forall u, shape_sub G u s -> shape_sub G u t).
Proof.
  induction 1; split_hyps; split; intros u K; try solve [eauto 6].
  - inversion K; subst; eauto.
  - shape_predecessor K.
  - inversion K; subst; eauto.
    eapply shape_abs with (L := L \u L0).
    intros x Hx; destruct (H0 x ltac:(notin_solve)); eauto.
  - shape_predecessor K.
    eapply shape_abs with (L := L \u L0).
    intros x Hx; destruct (H0 x ltac:(notin_solve)); eauto.
  - inversion K; subst; eauto.
  - shape_predecessor K.
  - inversion K; subst; eauto.
    eapply shape_prod with (L := L \u L0); eauto.
    intros x Hx.
    match goal with
    | IH : forall y, y \notin L -> _ /\ _ |- _ =>
        destruct (IH x ltac:(notin_solve)) as [Hpost _]
    end.
    eapply shape_change_type; apply Hpost.
    eapply shape_change_type; eauto.
  - shape_predecessor K.
    eapply shape_prod with (L := L \u L0); eauto.
    intros x Hx.
    match goal with
    | IH : forall y, y \notin L -> _ /\ _ |- _ =>
        destruct (IH x ltac:(notin_solve)) as [_ Hpre]
    end.
    apply Hpre; eapply shape_change_type; eauto.
  - inversion K; subst; eauto.
  - shape_predecessor K.
  - inversion K; subst; eauto.
  - shape_predecessor K.
Qed.

Lemma shape_typed : forall G s t, shape_sub G s t ->
  forall T, sub G s s T -> (exists r U, sub G r t U) -> sub G s t T.
Proof.
  induction 1; intros T Hleft (r & U & Hright).
  - exact Hleft.
  - eauto.
  - pose proof (sub_left_parts Hleft) as Hl; simpl in Hl.
    destruct Hl as (f & B & Hb & Hlift).
    pose proof (binds_functional H Hb) as Heq; inversion Heq; subst.
    destruct (wf_binds_typing (sub_wf Hleft) H) as [He HA].
    apply Hlift; eapply sub_var_trans; eauto.
  - apply sub_left_parts in Hleft; apply sub_right_parts in Hright.
    simpl in *.
    destruct Hleft as (K & B & He & HA & Hb & HB & Hlift).
    destruct Hright as (J & Hc).
    apply Hlift; eapply sub_abs with (L := L \u K \u J); eauto.
  - apply sub_left_parts in Hleft; apply sub_right_parts in Hright.
    simpl in *.
    destruct Hleft as (e & B & C & Hf & Ha & Hlift).
    apply Hlift; eauto.
  - apply sub_left_parts in Hleft; apply sub_right_parts in Hright.
    simpl in *.
    destruct Hleft as (K & HeA & HA & HB & Hlift).
    destruct Hright as (HeC & HC & J & HD).
    assert (HCA : sub G C A trm_star) by eauto.
    apply Hlift; eapply sub_prod with (L := L \u K \u J); eauto.
    intros x Hx; eapply H1; eauto.
    + eapply sub_narrow_push; eauto.
    + destruct (HD x ltac:(notin_solve)) as [s Hs]; eauto.
  - apply sub_left_parts in Hleft; apply sub_right_parts in Hright.
    simpl in *.
    destruct Hleft as (T0 & HA & He & Hred & Hlift).
    apply Hlift; eauto.
  - apply sub_left_parts in Hleft; apply sub_right_parts in Hright.
    simpl in *.
    destruct Hleft as (T0 & B & HB & He & Hred & Hlift).
    apply Hlift; eauto.
Qed.

Definition substitutes G D x u :=
  forall y e A, binds y (bind_sub e A) G ->
    (y = x -> sub D u (subst_trm u x e) (subst_trm u x A)) /\
    (y <> x -> binds y (bind_sub (subst_trm u x e) (subst_trm u x A)) D).

Lemma substitutes_push : forall G D x u y e A,
  substitutes G D x u -> y <> x ->
  wf (D & y ~ bind_sub (subst_trm u x e) (subst_trm u x A)) ->
  substitutes (G & y ~ bind_sub e A)
    (D & y ~ bind_sub (subst_trm u x e) (subst_trm u x A)) x u.
Proof.
  unfold substitutes; intros G D x u y e A HS Hneq HW z f B Hb.
  apply binds_push_inv in Hb; destruct Hb as [[-> Heq] | [Hzy Hb]].
  - inversion Heq; subst; split; [congruence|eauto].
  - destruct (HS _ _ _ Hb); split; intros; eauto using sub_weaken_push.
Qed.

Lemma sub_substitute : forall G s t A, sub G s t A ->
  forall x u D, lc_trm u -> wf D -> substitutes G D x u ->
  sub D (subst_trm u x s) (subst_trm u x t) (subst_trm u x A).
Proof.
  induction 1; intros x u D0 Hu HW HS; simpl.
  - eauto.
  - destruct (HS _ _ _ H0) as [Hyes Hno].
    case_if; eauto using sub_left_refl.
  - destruct (HS _ _ _ H) as [Hyes Hno].
    specialize (IHsub _ _ _ Hu HW HS).
    case_if.
    + specialize (Hyes ltac:(assumption)).
      eapply shape_typed; [|eapply sub_left_refl; exact Hyes|eauto].
      exact (proj1 (shape_compose (sub_shape Hyes)) _ (sub_shape IHsub)).
    + eauto.
  - eauto.
  - eauto.
  - eapply sub_abs with (L := L \u \{x} \u dom D0); eauto.
    all: intros y Hy; repeat rewrite <- subst_open_var by (assumption || notin_solve);
      first [solve [eapply H2; eauto 8 using substitutes_push] |
             solve [eapply H4; eauto 8 using substitutes_push]].
  - rewrite subst_open by assumption; eauto.
  - assert (Hdom : sub D0 (subst_trm u x A') (subst_trm u x A) trm_star) by eauto.
    assert (He : sub D0 (subst_trm u x e) (subst_trm u x e) (subst_trm u x A')) by eauto.
    assert (HA : sub D0 (subst_trm u x A) (subst_trm u x A) trm_star) by eauto.
    eapply sub_prod with (L := L \u \{x} \u dom D0); eauto.
    + intros y Hy; repeat rewrite <- subst_open_var by (assumption || notin_solve).
      eapply H3; eauto 8 using substitutes_push.
    + intros y Hy; repeat rewrite <- subst_open_var by (assumption || notin_solve).
      eapply H5; eauto 8 using substitutes_push, sub_left_refl.
  - eauto using reduct_subst.
  - eauto using reduct_subst.
  - eauto.
Qed.

Lemma substitutes_single : forall G e B a x,
  sub G a e B -> x # G -> x \notin fv_trm e -> x \notin fv_trm B ->
  substitutes (G & x ~ bind_sub e B) G x a.
Proof.
  intros G e B a x Ha Hdom Hxe HxB.
  unfold substitutes; intros y f A Hb.
  apply binds_push_inv in Hb; destruct Hb as [[-> Heq] | [Hneq Hb]].
  - inversion Heq; subst; split; [|congruence].
    intros _; rewrite !subst_fresh by assumption; exact Ha.
  - destruct (scope_binds (sub_wf Ha) Hb) as [Hf HA].
    assert (Hxf : x \notin fv_trm f) by (intro H; exact (Hdom (Hf _ H))).
    assert (HxA : x \notin fv_trm A) by (intro H; exact (Hdom (HA _ H))).
    split; [congruence|].
    intros _; rewrite !subst_fresh by assumption; exact Hb.
Qed.

Lemma sub_instantiate : forall L G e B C a,
  (forall x, x \notin L -> sub (G & x ~ bind_sub e B) (C ^ x) (C ^ x) trm_star) ->
  sub G a e B -> sub G (C ^^ a) (C ^^ a) trm_star.
Proof.
  intros L G e B C a Hbody Ha.
  destruct (var_fresh (L \u dom G \u fv_trm C \u fv_trm e \u fv_trm B)) as [x Hx].
  pose proof (sub_wf Ha) as HW.
  destruct (sub_lc Ha) as [HaLC _].
  pose proof (Hbody x ltac:(notin_solve)) as HC.
  pose proof (@substitutes_single G e B a x Ha ltac:(notin_solve)
    ltac:(notin_solve) ltac:(notin_solve)) as HS.
  pose proof (sub_substitute HC HaLC HW HS) as H.
  rewrite !subst_intro in H by (assumption || notin_solve).
  exact H.
Qed.

Lemma sub_regularity : forall G s t A, sub G s t A ->
  sub G t t A /\ sub G A A trm_star.
Proof.
  induction 1; split_hyps; split; eauto using sub_wf, sub_left_refl.
  - eapply (proj2 (wf_binds_typing H H0)).
  - eapply sub_abs with (L := L); eauto.
    intros x Hx; exact (proj1 (H2 x Hx)).
  - match goal with H : sub G (trm_prod e3 B C) (trm_prod e3 B C) trm_star |- _ =>
      apply sub_left_parts in H; simpl in H;
      destruct H as (L & _ & _ & Hbody & _);
      eapply sub_instantiate; eauto
    end.
  - eapply sub_prod with (L := L); eauto.
    all: intros x Hx; exact (proj1 (H5 x Hx)).
Qed.

Lemma erase_open_var : forall t x, [#t ^ x#] = [#t#] ^ x.
Proof. intros; apply (erase_open t (trm_var_f x)). Qed.

Lemma dsub_erased_shape : forall G s t,
  dsub G s t -> shape_sub {#G#} [#s#] [#t#].
Proof.
  induction 1; simpl; eauto.
  - eapply shape_var; [apply (binds_map rem_anno_env H)|eauto].
  - eapply shape_abs with (L := L).
    intros x Hx. specialize (H1 x Hx).
    rewrite map_push in H1; simpl in H1.
    rewrite !erase_idem, !erase_open_var in H1; exact H1.
  - eapply shape_prod with (L := L); eauto.
    intros x Hx. specialize (H1 x Hx).
    rewrite map_push in H1; simpl in H1.
    rewrite !erase_idem, !erase_open_var in H1; exact H1.
Qed.

Scheme dtyping_ind_mut := Induction for dtyping Sort Prop
with dwf_ind_mut := Induction for dwf Sort Prop.
Combined Scheme dtyping_dwf_ind from dtyping_ind_mut, dwf_ind_mut.

Lemma dtyping_erased :
  (forall d G e A, dtyping d G e A -> sub {#G#} [#e#] [#e#] [#A#]) /\
  (forall G, dwf G -> wf {#G#}).
Proof.
  apply dtyping_dwf_ind; intros; simpl in *; rewrite ?erase_idem in *; eauto.
  - eapply sub_var_refl; eauto.
    apply (binds_map rem_anno_env b).
  - eapply sub_abs with (L := L); eauto.
    + intros x Hx. specialize (H1 x Hx).
      rewrite map_push in H1; simpl in H1.
      rewrite !erase_idem, !erase_open_var in H1; exact H1.
    + intros x Hx. specialize (H1 x Hx).
      rewrite map_push in H1; simpl in H1.
      rewrite !erase_idem, !erase_open_var in H1.
      exact (proj2 (sub_regularity H1)).
  - rewrite erase_open, erase_idem.
    eapply sub_app; [eassumption|].
    pose proof (dsub_erased_shape d0) as HS; rewrite erase_idem in HS.
    eapply shape_typed; [exact HS|exact H|].
    match goal with Hf : sub _ _ _ (trm_prod _ _ _) |- _ =>
      pose proof (sub_left_parts (proj2 (sub_regularity Hf))) as Hp;
      simpl in Hp; destruct Hp as (K & He & _); eauto
    end.
  - eapply sub_prod with (L := L); eauto.
    all: intros x Hx; specialize (H1 x Hx); rewrite map_push in H1; simpl in H1;
      rewrite !erase_idem, erase_open_var in H1; exact H1.
  - eapply sub_sub; [eassumption|].
    pose proof (dsub_erased_shape d0) as HS; rewrite erase_idem in HS.
    eapply shape_typed; [exact HS | exact (proj2 (sub_regularity H)) | eauto].
  - rewrite map_empty; constructor.
  - rewrite map_push; simpl; rewrite !erase_idem; eauto.
Qed.

Fixpoint annotation_free (t : trm) : Prop :=
  match t with
  | trm_anno _ _ => False
  | trm_app s t | trm_castup s t => annotation_free s /\ annotation_free t
  | trm_abs e A b | trm_prod e A b =>
      annotation_free e /\ annotation_free A /\ annotation_free b
  | trm_castdn e => annotation_free e
  | _ => True
  end.

Lemma annotation_free_erase : forall t, annotation_free t -> [#t#] = t.
Proof. induction t; simpl; intros; split_hyps; try contradiction; f_equal; auto. Qed.

Lemma annotation_free_open : forall t k u, annotation_free u ->
  annotation_free (open_trm_wrt_trm_rec k u t) <-> annotation_free t.
Proof.
  induction t; intros; simpl; try case_if; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3 by assumption;
    tauto.
Qed.

Lemma annotation_free_body : forall L t,
  (forall x, x \notin L -> annotation_free (t ^ x)) -> annotation_free t.
Proof.
  intros L t H.
  destruct (var_fresh L) as [x Hx].
  eapply (proj1 (@annotation_free_open t 0 (trm_var_f x) I)); eauto.
Qed.

Definition clean_env G :=
  forall x e A, binds x (bind_sub e A) G -> annotation_free e /\ annotation_free A.

Lemma sub_clean :
  (forall G s t A, sub G s t A ->
    clean_env G /\ annotation_free s /\ annotation_free t /\ annotation_free A) /\
  (forall G, wf G -> clean_env G).
Proof.
  apply sub_wf_ind; intros; split_hyps;
    try (split; [assumption|]); simpl;
    try solve [auto].
  - match goal with H : clean_env ?G, Hb : binds ?x (bind_sub ?e ?A) ?G |- _ =>
      destruct (H _ _ _ Hb); auto
    end.
  - repeat split; auto.
    all: eapply annotation_free_body with (L := L); intros;
      match goal with IH : forall x, x \notin ?K -> clean_env _ /\ _ |- _ =>
        pose proof (IH _ ltac:(eassumption)); split_hyps; assumption
      end.
  - simpl in *; split_hyps; repeat split; auto.
    apply (proj2 (@annotation_free_open C 0 A ltac:(assumption))); assumption.
  - repeat split; auto.
    all: eapply annotation_free_body with (L := L); intros;
      match goal with IH : forall x, x \notin ?K -> clean_env _ /\ _ |- _ =>
        pose proof (IH _ ltac:(eassumption)); split_hyps; assumption
      end.
  - unfold clean_env; intros; exfalso; eapply binds_empty_inv; eassumption.
  - unfold clean_env; intros y f B Hb.
    apply binds_push_inv in Hb; destruct Hb as [[-> Heq] | [Hneq Hb]].
    + inversion Heq; subst; auto.
    + eauto.
Qed.

Lemma sub_erase_type : forall G s t A, sub G s t A -> [#A#] = A.
Proof.
  intros; pose proof (proj1 sub_clean _ _ _ _ H); split_hyps; auto using annotation_free_erase.
Qed.

Lemma sub_erase_left : forall G s t A, sub G s t A -> [#s#] = s.
Proof.
  intros; pose proof (proj1 sub_clean _ _ _ _ H); split_hyps; auto using annotation_free_erase.
Qed.

(* Unary typing records the formation premises needed to insert annotations. *)
Inductive utyping : env -> trm -> trm -> Prop :=
  | u_star : forall G, wf G -> utyping G trm_star trm_star
  | u_var : forall G x e A, wf G -> binds x (bind_sub e A) G ->
      utyping G (trm_var_f x) A
  | u_top : forall G A, utyping G A trm_star -> utyping G trm_top A
  | u_abs : forall L G e A b B,
      utyping G e A -> utyping G A trm_star ->
      (forall x, x \notin L -> utyping (G & x ~ bind_sub e A) (b ^ x) (B ^ x)) ->
      (forall x, x \notin L -> utyping (G & x ~ bind_sub e A) (B ^ x) trm_star) ->
      utyping G (trm_abs e A b) (trm_prod e A B)
  | u_app : forall G e B C f a,
      utyping G f (trm_prod e B C) -> utyping G a B -> sub G a e B ->
      utyping G (trm_app f a) (C ^^ a)
  | u_prod : forall L G e A B,
      utyping G e A -> utyping G A trm_star ->
      (forall x, x \notin L -> utyping (G & x ~ bind_sub e A) (B ^ x) trm_star) ->
      utyping G (trm_prod e A B) trm_star
  | u_up : forall G A B e, utyping G B trm_star -> utyping G e A ->
      reduct B A -> utyping G (trm_castup B e) B
  | u_down : forall G A B e, utyping G B trm_star -> utyping G e A ->
      reduct A B -> utyping G (trm_castdn e) B
  | u_sub : forall G e A B,
      utyping G e A -> sub G A B trm_star -> utyping G B trm_star ->
      utyping G e B.

#[local] Hint Constructors utyping : core.

Lemma utyping_sub : forall G e A, utyping G e A -> sub G e e A.
Proof.
  induction 1; eauto.
Qed.

Lemma utyping_weaken : forall G e A, utyping G e A ->
  forall D, wf D -> preserves_bindings G D -> utyping D e A.
Proof.
  induction 1; intros D0 HW HP; eauto using sub_weaken.
  - eapply u_abs with (L := L \u dom D0); eauto.
    + intros x Hx; eapply H2; eauto 8 using utyping_sub, preserves_push.
    + intros x Hx; eapply H4; eauto 8 using utyping_sub, preserves_push.
  - eapply u_prod with (L := L \u dom D0); eauto.
    intros x Hx; eapply H2; eauto 8 using utyping_sub, preserves_push.
Qed.

Lemma utyping_weaken_push : forall G e A x b,
  utyping G e A -> wf (G & x ~ b) -> utyping (G & x ~ b) e A.
Proof.
  intros; eapply utyping_weaken; eauto.
  unfold preserves_bindings; intros; eapply binds_concat_left_ok; eauto using wf_ok.
Qed.

Definition u_substitutes G D x u :=
  forall e A, binds x (bind_sub e A) G -> utyping D u (subst_trm u x A).

Lemma u_substitutes_push : forall G D x u y e A,
  u_substitutes G D x u -> y <> x ->
  wf (D & y ~ bind_sub (subst_trm u x e) (subst_trm u x A)) ->
  u_substitutes (G & y ~ bind_sub e A)
    (D & y ~ bind_sub (subst_trm u x e) (subst_trm u x A)) x u.
Proof.
  unfold u_substitutes; intros.
  eapply utyping_weaken_push; eauto using binds_push_neq_inv.
Qed.

Lemma utyping_substitute : forall G e A, utyping G e A ->
  forall x u D, lc_trm u -> wf D -> substitutes G D x u ->
  u_substitutes G D x u ->
  utyping D (subst_trm u x e) (subst_trm u x A).
Proof.
  induction 1; intros x0 u D0 Hu HW HS HT; simpl; eauto using sub_substitute, reduct_subst.
  - destruct (HS _ _ _ H0); case_if; subst; eauto.
  - eapply u_abs with (L := L \u \{x0} \u dom D0); eauto.
    + intros y Hy; repeat rewrite <- subst_open_var by (assumption || notin_solve).
      eapply H2; eauto 9 using utyping_sub, substitutes_push, u_substitutes_push.
    + intros y Hy; repeat rewrite <- subst_open_var by (assumption || notin_solve).
      eapply H4; eauto 9 using utyping_sub, substitutes_push, u_substitutes_push.
  - rewrite subst_open by assumption; eauto using sub_substitute.
  - eapply u_prod with (L := L \u \{x0} \u dom D0); eauto.
    intros y Hy; repeat rewrite <- subst_open_var by (assumption || notin_solve).
    eapply H2; eauto 9 using utyping_sub, substitutes_push, u_substitutes_push.
  - eapply u_sub; [eapply IHutyping1 | exact (sub_substitute H0 Hu HW HS) | eapply IHutyping2]; eauto.
Qed.

Lemma utyping_instantiate : forall L G e B C a,
  (forall x, x \notin L -> utyping (G & x ~ bind_sub e B) (C ^ x) trm_star) ->
  utyping G a B -> sub G a e B -> utyping G (C ^^ a) trm_star.
Proof.
  intros L G e B C a Hbody Hu Ha.
  destruct (var_fresh (L \u dom G \u fv_trm C \u fv_trm e \u fv_trm B)) as [x Hx].
  pose proof (sub_wf Ha) as HW.
  destruct (sub_lc Ha) as [HaLC _].
  pose proof (@substitutes_single G e B a x Ha ltac:(notin_solve)
    ltac:(notin_solve) ltac:(notin_solve)) as HS.
  assert (HT : u_substitutes (G & x ~ bind_sub e B) G x a).
  { unfold u_substitutes; intros f A Hb.
    apply binds_push_eq_inv in Hb; inversion Hb; subst.
    rewrite subst_fresh by notin_solve; exact Hu. }
  pose proof (utyping_substitute (Hbody x ltac:(notin_solve)) HaLC HW HS HT) as H.
  rewrite subst_intro in H by (assumption || notin_solve).
  exact H.
Qed.

Lemma utyping_prod_body : forall G e A B T,
  utyping G (trm_prod e A B) T ->
  exists L, forall x, x \notin L -> utyping (G & x ~ bind_sub e A) (B ^ x) trm_star.
Proof.
  intros G e A B T H. remember (trm_prod e A B) as p in H.
  induction H; inversion Heqp; subst; eauto.
Qed.

Definition utyped_bindings G :=
  forall x e A, binds x (bind_sub e A) G -> utyping G A trm_star.

Lemma sub_unary :
  (forall G s t A, sub G s t A ->
    utyped_bindings G /\ utyping G s A /\ utyping G t A /\ utyping G A trm_star) /\
  (forall G, wf G -> utyped_bindings G).
Proof.
  apply sub_wf_ind; intros; split_hyps;
    try (split; [assumption|]); repeat split; eauto using sub_wf.
  - eapply u_abs with (L := L); eauto.
    all: intros x Hx; specialize (H1 x Hx); specialize (H2 x Hx); tauto.
  - eapply u_abs with (L := L); eauto.
    all: intros x Hx; specialize (H1 x Hx); specialize (H2 x Hx); tauto.
  - eapply u_prod with (L := L); eauto.
    intros x Hx; specialize (H2 x Hx); tauto.
  - match goal with H : utyping G (trm_prod e3 B C) trm_star |- _ =>
      destruct (utyping_prod_body H) as (K & HK)
    end.
    eauto using utyping_instantiate.
  - eapply u_prod with (L := L); eauto.
    intros x Hx; specialize (H2 x Hx); tauto.
  - eapply u_prod with (L := L); eauto.
    intros x Hx; specialize (H3 x Hx); tauto.
  - unfold utyped_bindings; intros; exfalso; eapply binds_empty_inv; eassumption.
  - unfold utyped_bindings; intros y f B Hb.
    apply binds_push_inv in Hb; destruct Hb as [[-> Heq] | [Hneq Hb]].
    + inversion Heq; subst; eauto using utyping_weaken_push.
    + match goal with H : utyped_bindings G |- _ =>
        pose proof (H _ _ _ Hb)
      end.
      eauto using utyping_weaken_push.
Qed.

Fixpoint close_var_rec (k : nat) (x : var) (t : trm) : trm :=
  match t with
  | trm_var_f z => If z = x then trm_var_b k else t
  | trm_app s t => trm_app (close_var_rec k x s) (close_var_rec k x t)
  | trm_abs e A b => trm_abs (close_var_rec k x e) (close_var_rec k x A) (close_var_rec (S k) x b)
  | trm_prod e A b => trm_prod (close_var_rec k x e) (close_var_rec k x A) (close_var_rec (S k) x b)
  | trm_castup A e => trm_castup (close_var_rec k x A) (close_var_rec k x e)
  | trm_castdn e => trm_castdn (close_var_rec k x e)
  | trm_anno e A => trm_anno (close_var_rec k x e) (close_var_rec k x A)
  | _ => t
  end.

Lemma erase_close : forall t k x, [#close_var_rec k x t#] = close_var_rec k x [#t#].
Proof. induction t; intros; simpl; try case_if; try reflexivity; congruence. Qed.

Lemma close_open_var : forall t k x, x \notin fv_trm t ->
  close_var_rec k x (open_trm_wrt_trm_rec k (trm_var_f x) t) = t.
Proof.
  induction t; intros; simpl in *; try solve [f_equal; eauto].
  - case_if; simpl; try case_if; congruence.
  - case_if; [subst; notin_false|reflexivity].
Qed.

Fixpoint rename_trm (f : var -> var) (t : trm) : trm :=
  match t with
  | trm_var_f z => trm_var_f (f z)
  | trm_app s t => trm_app (rename_trm f s) (rename_trm f t)
  | trm_abs e A b => trm_abs (rename_trm f e) (rename_trm f A) (rename_trm f b)
  | trm_prod e A b => trm_prod (rename_trm f e) (rename_trm f A) (rename_trm f b)
  | trm_castup A e => trm_castup (rename_trm f A) (rename_trm f e)
  | trm_castdn e => trm_castdn (rename_trm f e)
  | trm_anno e A => trm_anno (rename_trm f e) (rename_trm f A)
  | _ => t
  end.

Lemma rename_erase : forall f t, rename_trm f [#t#] = [#rename_trm f t#].
Proof. induction t; simpl; congruence. Qed.

Lemma rename_open_rec : forall f t k u,
  rename_trm f (open_trm_wrt_trm_rec k u t) =
  open_trm_wrt_trm_rec k (rename_trm f u) (rename_trm f t).
Proof. induction t; intros; simpl; try case_if; try reflexivity; congruence. Qed.

Lemma rename_open : forall f t u, rename_trm f (t ^^ u) = rename_trm f t ^^ rename_trm f u.
Proof. intros; apply rename_open_rec. Qed.

#[local] Hint Constructors dsub dtyping dwf : core.

Section Swapping.
Variables x0 y0 : var.

Definition swap_var z := If z = x0 then y0 else If z = y0 then x0 else z.
Local Notation swap := (rename_trm swap_var).
Local Notation swap_fresh := (\{x0} \u \{y0}).

Lemma swap_fixed : forall z, z \notin swap_fresh -> swap_var z = z.
Proof. unfold swap_var; intros; repeat case_if; subst; try notin_false; reflexivity. Qed.

Lemma swap_involutive : forall z, swap_var (swap_var z) = z.
Proof. unfold swap_var; intros; repeat case_if; congruence. Qed.

Lemma swap_injective : forall x y, swap_var x = swap_var y -> x = y.
Proof. intros x y H; rewrite <- (swap_involutive x), <- (swap_involutive y), H; reflexivity. Qed.

Lemma swap_term_fixed : forall t, x0 \notin fv_trm t -> y0 \notin fv_trm t -> swap t = t.
Proof.
  induction t; simpl; intros; try solve [f_equal; eauto].
  f_equal; apply swap_fixed; notin_solve.
Qed.

Lemma open_closed_var : forall t k, closed_at k t -> y0 \notin fv_trm t ->
  open_trm_wrt_trm_rec k (trm_var_f y0) (close_var_rec k x0 t) = swap t.
Proof.
  induction t; simpl; intros; split_hyps; try solve [f_equal; eauto].
  - case_if; subst; lia || reflexivity.
  - unfold swap_var; repeat case_if; subst; try notin_false; simpl; try case_if; congruence.
Qed.

Definition swap_binding b :=
  match b with bind_sub e A => bind_sub (swap e) (swap A) end.
Definition swap_env (G : env) : env :=
  LibList.map (fun p => (swap_var (fst p), swap_binding (snd p))) G.

Lemma swap_env_empty : swap_env empty = empty.
Proof. unfold swap_env; rewrite empty_def; reflexivity. Qed.

Lemma swap_env_push : forall G x b,
  swap_env (G & x ~ b) = swap_env G & swap_var x ~ swap_binding b.
Proof. intros; unfold swap_env; rewrite <- !cons_to_push; reflexivity. Qed.

Lemma swap_env_dom : forall G z, swap_var z \in dom (swap_env G) -> z \in dom G.
Proof.
  induction G using env_ind; intros z H.
  - rewrite swap_env_empty, dom_empty in H; rewrite in_empty in H; contradiction.
  - rewrite swap_env_push, !dom_push, in_union, in_singleton in H.
    rewrite dom_push, in_union, in_singleton.
    destruct H; eauto using swap_injective.
Qed.

Lemma swap_env_fresh : forall G z, z # G -> swap_var z # swap_env G.
Proof. intros G z Hfresh Hin; apply Hfresh; eapply swap_env_dom; eassumption. Qed.

Lemma swap_env_ok : forall G, ok G -> ok (swap_env G).
Proof. induction 1; rewrite ?swap_env_empty, ?swap_env_push; eauto using swap_env_fresh. Qed.

Lemma swap_binds : forall G z b, binds z b G -> binds (swap_var z) (swap_binding b) (swap_env G).
Proof.
  induction G using env_ind; intros z b Hb.
  - exfalso; eapply binds_empty_inv; eassumption.
  - rewrite swap_env_push.
    apply binds_push_inv in Hb; destruct Hb as [[-> ->] | [Hneq Hb]].
    + apply binds_push_eq.
    + apply binds_push_neq; [eauto|intro Heq; apply Hneq; apply swap_injective; exact Heq].
Qed.

Lemma swap_env_fixed : forall G, wf G -> x0 # G -> y0 # G -> swap_env G = G.
Proof.
  assert (H : (forall G e f A, sub G e f A -> x0 # G -> y0 # G -> swap_env G = G) /\
              (forall G, wf G -> x0 # G -> y0 # G -> swap_env G = G)).
  { apply sub_wf_ind; intros; try solve [eauto]; try exact swap_env_empty.
    assert (HW : wf (G & x5 ~ bind_sub e A)) by eauto.
    destruct (scope_binds HW (binds_push_eq x5 (bind_sub e A) G)) as [He HA].
    assert (Heq : swap e = e) by
      (apply swap_term_fixed; intro Hin; match goal with H : _ # _ |- False =>
        exact (H (He _ Hin)) end).
    assert (HAq : swap A = A) by
      (apply swap_term_fixed; intro Hin; match goal with H : _ # _ |- False =>
        exact (H (HA _ Hin)) end).
    rewrite swap_env_push; simpl; rewrite Heq, HAq.
    match goal with Hx : x0 # ?G0, Hy : y0 # ?G0 |- _ =>
      rewrite dom_push in Hx, Hy
    end.
    rewrite swap_fixed by notin_solve.
    f_equal; eauto.
  }
  exact (proj2 H).
Qed.

Lemma swap_lc : forall t, lc_trm t -> lc_trm (swap t).
Proof.
  induction 1; simpl; eauto;
    [eapply lc_trm_abs with (L := L \u swap_fresh) |
     eapply lc_trm_prod with (L := L \u swap_fresh)]; eauto;
    intros z Hz;
    specialize (H2 z ltac:(notin_solve)); rewrite rename_open in H2; simpl in H2;
    rewrite swap_fixed in H2 by notin_solve; exact H2.
Qed.

Lemma swap_reduct : forall s t, reduct s t -> reduct (swap s) (swap t).
Proof.
  induction 1; simpl; eauto using reduct_app, reduct_castdn, reduct_castelim, swap_lc.
  rewrite rename_open; apply reduct_beta; eauto using swap_lc.
  exact (swap_lc H1).
Qed.

Lemma swap_dsub : forall G s t, dsub G s t -> dsub (swap_env G) (swap s) (swap t).
Proof.
  induction 1; simpl; eauto using swap_env_ok, swap_lc.
  - eapply dsub_var_refl; eauto using swap_env_ok.
    apply (swap_binds H0).
  - eapply dsub_var_trans; [apply (swap_binds H)|eauto].
  - eapply dsub_lam with (L := L \u swap_fresh); eauto using swap_env_ok.
    intros z Hz; specialize (H1 z ltac:(notin_solve)).
    rewrite swap_env_push, !rename_open in H1; simpl in H1.
    rewrite !rename_erase, swap_fixed in H1 by notin_solve; exact H1.
  - eapply dsub_pi with (L := L \u swap_fresh); eauto.
    intros z Hz; specialize (H1 z ltac:(notin_solve)).
    rewrite swap_env_push, !rename_open in H1; simpl in H1.
    rewrite !rename_erase, swap_fixed in H1 by notin_solve; exact H1.
Qed.

Lemma swap_dtyping :
  (forall d G s T, dtyping d G s T -> dtyping d (swap_env G) (swap s) (swap T)) /\
  (forall G, dwf G -> dwf (swap_env G)).
Proof.
  apply dtyping_dwf_ind; intros; simpl in *; rewrite ?rename_erase in *; eauto using swap_reduct.
  - eapply dtyping_var; eauto. apply (swap_binds b).
  - eapply dtyping_lam with (L := L \u swap_fresh); eauto.
    intros z Hz; specialize (H1 z ltac:(notin_solve)).
    rewrite swap_env_push, !rename_open in H1; simpl in H1.
    rewrite !rename_erase, swap_fixed in H1 by notin_solve; exact H1.
  - rewrite rename_open, rename_erase.
    eapply dtyping_app; eauto.
    pose proof (swap_dsub d0) as HS; rewrite rename_erase in HS; exact HS.
  - eapply dtyping_pi with (L := L \u swap_fresh); eauto.
    intros z Hz; specialize (H1 z ltac:(notin_solve)).
    rewrite swap_env_push, rename_open in H1; simpl in H1.
    rewrite !rename_erase, swap_fixed in H1 by notin_solve; exact H1.
  - pose proof (swap_reduct r) as Hr; rewrite !rename_erase in Hr.
    eapply dtyping_castup; eauto.
  - pose proof (swap_reduct r) as Hr; rewrite !rename_erase in Hr.
    eapply dtyping_castdn; eauto.
  - eapply dtyping_sub; eauto.
    pose proof (swap_dsub d0) as HS; rewrite rename_erase in HS; exact HS.
  - rewrite swap_env_empty; constructor.
  - rewrite swap_env_push; simpl; rewrite !rename_erase; eauto using swap_env_fresh.
Qed.
End Swapping.

Lemma dtyping_lc : forall d G t T, dtyping d G t T -> lc_trm t.
Proof.
  induction 1; eauto.
Qed.

(* Close a witness chosen at one fresh variable, then use swapping to
   obtain its typing after opening at any sufficiently fresh variable. *)
Lemma reabstract_inf : forall G e A b T x q,
  wf G -> x # G -> x \notin fv_trm e -> x \notin fv_trm A ->
  x \notin fv_trm b -> x \notin fv_trm T ->
  dtyping inf (G & x ~ bind_sub e A) q (T ^ x) -> [#q#] = b ^ x ->
  exists K p, [#p#] = b /\
    forall y, y \notin K -> dtyping inf (G & y ~ bind_sub e A) (p ^ y) (T ^ y).
Proof.
  intros G e A b T x q HW HxG Hxe HxA Hxb HxT Hq Hqe.
  exists (fv_trm q \u dom G \u fv_trm e \u fv_trm A \u fv_trm T \u \{x}),
    (close_var_rec 0 x q).
  split.
  - rewrite erase_close, Hqe; apply close_open_var; assumption.
  - intros y Hy.
    pose proof (proj1 (swap_dtyping x y) _ _ _ _ Hq) as H.
    rewrite swap_env_push in H; simpl in H.
    assert (Hxy : swap_var x y x = y) by (unfold swap_var; case_if; congruence).
    rewrite Hxy, swap_env_fixed in H by (assumption || notin_solve).
    rewrite rename_open in H; simpl in H; rewrite Hxy in H.
    rewrite (@swap_term_fixed x y e), (@swap_term_fixed x y A), (@swap_term_fixed x y T) in H
      by (assumption || notin_solve).
    unfold open_trm_wrt_trm at 1.
    rewrite open_closed_var by (eauto using dtyping_lc, lc_closed || notin_solve).
    exact H.
Qed.

Lemma sub_dsub : forall G s t A, sub G s t A -> dsub G s t.
Proof.
  induction 1; eauto using wf_ok, sub_wf.
  - apply dsub_top; eauto using wf_ok, sub_wf.
    exact (proj1 (sub_lc H)).
  - eapply dsub_lam with (L := L); eauto using wf_ok, sub_wf.
    rewrite (sub_erase_left H), (sub_erase_type H); eauto.
  - eapply dsub_app; eauto.
    exact (proj1 (sub_lc H0)).
  - eapply dsub_pi with (L := L); eauto.
    rewrite (sub_erase_left H0), (sub_erase_left H); eauto.
  - eapply dsub_castup; eauto.
    exact (proj1 (sub_lc H)).
Qed.

Lemma utyping_inf : forall G t T, utyping G t T -> dwf G ->
  exists t', dtyping inf G t' T /\ [#t'#] = t.
Proof.
  induction 1; intros HW.
  - exists trm_star; simpl; eauto.
  - exists (trm_var_f x); simpl; eauto.
  - destruct (IHutyping HW) as (A' & HA & HAr).
    exists (trm_anno trm_top A'); simpl.
    split; [|reflexivity]. rewrite <- HAr.
    apply dtyping_anno; [apply dtyping_top |]; apply dtyping_chk; exact HA.
  - destruct (IHutyping1 HW) as (e' & He & Her).
    destruct (IHutyping2 HW) as (A' & HA & HAr).
    pose proof (sub_wf (utyping_sub H)) as Hwf.
    destruct (var_fresh (L \u dom G \u fv_trm e \u fv_trm A \u fv_trm b \u fv_trm B)) as [x Hx].
    assert (HWx : dwf (G & x ~ bind_sub e A)).
    { rewrite <- Her, <- HAr; eapply dwf_cons; rewrite ?HAr; eauto. }
    destruct (H2 x ltac:(notin_solve) HWx) as (q & Hq & Hqr).
    destruct (@reabstract_inf G e A b B x q Hwf ltac:(notin_solve)
      ltac:(notin_solve) ltac:(notin_solve) ltac:(notin_solve) ltac:(notin_solve) Hq Hqr)
      as (K & p & Hpr & Hp).
    exists (trm_abs e' A' p); split; [|simpl; congruence].
    rewrite <- Her at 1; rewrite <- HAr at 1.
    eapply dtyping_lam with (L := K); try rewrite Her; try rewrite HAr; eauto.
  - destruct (IHutyping1 HW) as (f' & Hf & Hfr).
    destruct (IHutyping2 HW) as (a' & Ha & Har).
    exists (trm_app f' a'); split; [|simpl; congruence].
    rewrite <- Har at 1.
    eapply dtyping_app with (e3 := e) (B := B); eauto using sub_dsub.
    rewrite Har; eauto using sub_dsub.
  - destruct (IHutyping1 HW) as (e' & He & Her).
    destruct (IHutyping2 HW) as (A' & HA & HAr).
    pose proof (sub_wf (utyping_sub H)) as Hwf.
    destruct (var_fresh (L \u dom G \u fv_trm e \u fv_trm A \u fv_trm B)) as [x Hx].
    assert (HWx : dwf (G & x ~ bind_sub e A)).
    { rewrite <- Her, <- HAr; eapply dwf_cons; rewrite ?HAr; eauto. }
    destruct (H2 x ltac:(notin_solve) HWx) as (q & Hq & Hqr).
    destruct (@reabstract_inf G e A B trm_star x q Hwf ltac:(notin_solve)
      ltac:(notin_solve) ltac:(notin_solve) ltac:(notin_solve) (@notin_empty var x) Hq Hqr)
      as (K & p & Hpr & Hp).
    exists (trm_prod e' A' p); split; [|simpl; congruence].
    eapply dtyping_pi with (L := K); rewrite ?Her, ?HAr; eauto.
  - destruct (IHutyping1 HW) as (B' & HB & HBr).
    destruct (IHutyping2 HW) as (e' & He & Her).
    exists (trm_castup B' e'); split; [|simpl; congruence].
    rewrite <- HBr at 1.
    eapply dtyping_castup with (A := A); eauto.
    rewrite HBr, (sub_erase_type (utyping_sub H0)); assumption.
  - destruct (IHutyping1 HW) as (B' & HB & HBr).
    destruct (IHutyping2 HW) as (e' & He & Her).
    exists (trm_anno (trm_castdn e') B'); split; [|simpl; congruence].
    rewrite <- HBr at 1.
    apply dtyping_anno; eauto.
    eapply dtyping_castdn with (A := A); eauto.
    rewrite HBr, (sub_erase_type (utyping_sub H0)); assumption.
  - destruct (IHutyping1 HW) as (e' & He & Her).
    destruct (IHutyping2 HW) as (B' & HB & HBr).
    exists (trm_anno e' B'); split; [|simpl; assumption].
    rewrite <- HBr at 1.
    apply dtyping_anno; eauto.
    eapply dtyping_sub with (A := A); eauto.
    rewrite HBr; eauto using sub_dsub.
Qed.

Lemma wf_dwf : forall G, wf G -> dwf G.
Proof.
  induction G as [|G x b IH] using env_ind; intros HW.
  - constructor.
  - remember (G & x ~ b) as D eqn:HD in HW.
    destruct HW as [|D y e A He HA Hy].
    + rewrite empty_def, <- cons_to_push in HD; discriminate.
    + apply eq_push_inv in HD; destruct HD as (-> & <- & ->).
      specialize (IH (sub_wf He)).
      destruct (proj1 sub_unary _ _ _ _ He) as (_ & Hue & _).
      destruct (proj1 sub_unary _ _ _ _ HA) as (_ & HuA & _).
      destruct (utyping_inf Hue IH) as (e' & He' & Her).
      destruct (utyping_inf HuA IH) as (A' & HA' & HAr).
      rewrite <- Her, <- HAr; eapply dwf_cons; rewrite ?HAr; eauto.
Qed.

Theorem sub_to_bidir : forall G e1 e2 A,
  sub G e1 e2 A ->
  dsub G e1 e2 /\
  exists e1' e2',
    dtyping inf G e1' A /\ dtyping inf G e2' A /\
    [#e1'#] = e1 /\ [#e2'#] = e2.
Proof.
  intros G e1 e2 A H.
  split; [eapply sub_dsub; exact H|].
  destruct (proj1 sub_unary _ _ _ _ H) as (_ & H1 & H2 & _).
  pose proof (wf_dwf (sub_wf H)) as HW.
  destruct (utyping_inf H1 HW) as (e1' & H1' & He1).
  destruct (utyping_inf H2 HW) as (e2' & H2' & He2).
  exists e1', e2'; auto.
Qed.

Theorem bidir_to_sub : forall G d e1 e2 A,
  dtyping d G e1 A ->
  dtyping d G e2 A ->
  dsub G e1 e2 ->
  sub {#G#} [#e1#] [#e2#] [#A#].
Proof.
  intros G d e1 e2 A H1 H2 HS.
  eapply shape_typed.
  - exact (dsub_erased_shape HS).
  - exact (proj1 dtyping_erased _ _ _ _ H1).
  - exists [#e2#], [#A#].
    exact (proj1 dtyping_erased _ _ _ _ H2).
Qed.
