Set Implicit Arguments.

From TLC Require Import LibLN.

Require Import Main_ott Main_Infra.
From Stdlib Require Import Lia.
From Stdlib Require Import Program.Equality.
From TLC Require Import LibTactics.
Open Scope list_scope.

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


(* ================= basic annotation lemmas ================= *)

Lemma remove_anno_idem : forall e, [# [# e #] #] = [# e #].
Proof.
  induction e; simpl.
  - reflexivity. - reflexivity. - reflexivity. - reflexivity.
  - f_equal; assumption. - f_equal; assumption. - f_equal; assumption.
  - f_equal; assumption. - f_equal; assumption.
  - rewrite IHe1. reflexivity.
Qed.

Lemma remove_anno_not_anno : forall e a b, [# e #] <> trm_anno a b.
Proof.
  induction e; simpl; intros; try discriminate; auto.
Qed.

Lemma remove_anno_classic : forall (P:Prop) (t1 t2:trm),
  [# match classicT P with left _ => t1 | right _ => t2 end #] =
  match classicT P with left _ => [# t1 #] | right _ => [# t2 #] end.
Proof. intros. destruct (classicT P); reflexivity. Qed.

Lemma remove_anno_open_rec : forall k v e,
  [# open_trm_wrt_trm_rec k v e #] =
  open_trm_wrt_trm_rec k [# v #] [# e #].
Proof.
  intros k v e. revert k v. induction e; intros k0 v0; simpl.
  - rewrite remove_anno_classic. reflexivity.
  - reflexivity. - reflexivity. - reflexivity.
  - f_equal; [ apply IHe1 | apply IHe2 ].
  - f_equal; [ apply IHe1 | apply IHe2 | apply IHe3 ].
  - f_equal; [ apply IHe1 | apply IHe2 | apply IHe3 ].
  - f_equal; [ apply IHe1 | apply IHe2 ].
  - f_equal; apply IHe.
  - rewrite IHe1. reflexivity.
Qed.

Lemma remove_anno_open : forall e v,
  [# open_trm_wrt_trm e v #] = open_trm_wrt_trm [# e #] [# v #].
Proof. intros. unfold open_trm_wrt_trm. apply remove_anno_open_rec. Qed.

Lemma remove_anno_open_var : forall e x,
  [# open_trm_wrt_trm e (trm_var_f x) #] =
  open_trm_wrt_trm [# e #] (trm_var_f x).
Proof. intros. rewrite remove_anno_open. simpl. reflexivity. Qed.

Lemma remove_anno_subst : forall v x e,
  [# subst_trm v x e #] = subst_trm [# v #] x [# e #].
Proof.
  intros v x e. revert v x. induction e; intros v0 x0; simpl.
  - reflexivity.
  - rewrite remove_anno_classic. reflexivity.
  - reflexivity. - reflexivity.
  - f_equal; [ apply IHe1 | apply IHe2 ].
  - f_equal; [ apply IHe1 | apply IHe2 | apply IHe3 ].
  - f_equal; [ apply IHe1 | apply IHe2 | apply IHe3 ].
  - f_equal; [ apply IHe1 | apply IHe2 ].
  - f_equal; apply IHe.
  - rewrite IHe1. reflexivity.
Qed.

(* ---------------- locally closed at level n ---------------- *)

Fixpoint lc_rec (n:nat) (e:trm) : Prop :=
  match e with
  | trm_var_b i => i < n
  | trm_var_f _ => True
  | trm_star => True
  | trm_top => True
  | trm_app a b => lc_rec n a /\ lc_rec n b
  | trm_abs a A b => lc_rec n a /\ lc_rec n A /\ lc_rec (S n) b
  | trm_prod a A b => lc_rec n a /\ lc_rec n A /\ lc_rec (S n) b
  | trm_castup A a => lc_rec n A /\ lc_rec n a
  | trm_castdn a => lc_rec n a
  | trm_anno a A => lc_rec n a /\ lc_rec n A
  end.

Lemma lc_rec_mono : forall n m e, n <= m -> lc_rec n e -> lc_rec m e.
Proof.
  intros n m e. revert n m. induction e; intros n0 m0 Le H; simpl in *.
  - lia.
  - auto. - auto. - auto.
  - destruct H as [H1 H2]; split; [apply (IHe1 n0 m0 Le H1)|apply (IHe2 n0 m0 Le H2)].
  - destruct H as [H1 [H2 H3]]; split; [apply (IHe1 n0 m0 Le H1)|split;[apply (IHe2 n0 m0 Le H2)|]].
    apply (IHe3 (S n0) (S m0)); [lia|assumption].
  - destruct H as [H1 [H2 H3]]; split; [apply (IHe1 n0 m0 Le H1)|split;[apply (IHe2 n0 m0 Le H2)|]].
    apply (IHe3 (S n0) (S m0)); [lia|assumption].
  - destruct H as [H1 H2]; split; [apply (IHe1 n0 m0 Le H1)|apply (IHe2 n0 m0 Le H2)].
  - apply (IHe n0 m0 Le H).
  - destruct H as [H1 H2]; split; [apply (IHe1 n0 m0 Le H1)|apply (IHe2 n0 m0 Le H2)].
Qed.

Lemma lc_rec_open_var_inv : forall k x e,
  lc_rec k (open_trm_wrt_trm_rec k (trm_var_f x) e) -> lc_rec (S k) e.
Proof.
  intros k x e. revert k x. induction e; intros k0 x0 H; simpl in *.
  - destruct (classicT (k0 = n)) as [Heq|Hneq]; simpl in *; lia.
  - auto. - auto. - auto.
  - destruct H as [H1 H2]; split; [apply (IHe1 k0 x0 H1)|apply (IHe2 k0 x0 H2)].
  - destruct H as [H1 [H2 H3]]; split; [apply (IHe1 k0 x0 H1)|split;[apply (IHe2 k0 x0 H2)|]].
    apply (IHe3 (S k0) x0 H3).
  - destruct H as [H1 [H2 H3]]; split; [apply (IHe1 k0 x0 H1)|split;[apply (IHe2 k0 x0 H2)|]].
    apply (IHe3 (S k0) x0 H3).
  - destruct H as [H1 H2]; split; [apply (IHe1 k0 x0 H1)|apply (IHe2 k0 x0 H2)].
  - apply (IHe k0 x0 H).
  - destruct H as [H1 H2]; split; [apply (IHe1 k0 x0 H1)|apply (IHe2 k0 x0 H2)].
Qed.

Lemma lc_rec_open_inv : forall k v e, lc_rec k v -> lc_rec k (open_trm_wrt_trm_rec k v e) -> lc_rec (S k) e.
Proof.
  intros k v e. revert k v. induction e; intros k0 v0 Hv H; simpl in *.
  - destruct (classicT (k0 = n)) as [Heq|Hneq]; simpl in *; lia.
  - auto. - auto. - auto.
  - destruct H as [H1 H2]; split; [apply (IHe1 k0 v0 Hv H1)|apply (IHe2 k0 v0 Hv H2)].
  - destruct H as [H1 [H2 H3]]; split; [apply (IHe1 k0 v0 Hv H1)|split;[apply (IHe2 k0 v0 Hv H2)|]].
    apply (IHe3 (S k0) v0); [apply lc_rec_mono with (n:=k0); [lia|assumption]|assumption].
  - destruct H as [H1 [H2 H3]]; split; [apply (IHe1 k0 v0 Hv H1)|split;[apply (IHe2 k0 v0 Hv H2)|]].
    apply (IHe3 (S k0) v0); [apply lc_rec_mono with (n:=k0); [lia|assumption]|assumption].
  - destruct H as [H1 H2]; split; [apply (IHe1 k0 v0 Hv H1)|apply (IHe2 k0 v0 Hv H2)].
  - apply (IHe k0 v0 Hv H).
  - destruct H as [H1 H2]; split; [apply (IHe1 k0 v0 Hv H1)|apply (IHe2 k0 v0 Hv H2)].
Qed.

Lemma lc_rec_open : forall k v e, lc_rec k v -> lc_rec (S k) e -> lc_rec k (open_trm_wrt_trm_rec k v e).
Proof.
  intros k v e. revert k v. induction e; intros k0 v0 Hv H; simpl in *.
  - destruct (classicT (k0 = n)) as [Heq|Hneq]; simpl; [assumption|lia].
  - auto. - auto. - auto.
  - destruct H as [H1 H2]; split; [apply (IHe1 k0 v0 Hv H1)|apply (IHe2 k0 v0 Hv H2)].
  - destruct H as [H1 [H2 H3]]; split; [apply (IHe1 k0 v0 Hv H1)|split;[apply (IHe2 k0 v0 Hv H2)|]].
    apply (IHe3 (S k0) v0); [apply lc_rec_mono with (n:=k0); [lia|assumption]|assumption].
  - destruct H as [H1 [H2 H3]]; split; [apply (IHe1 k0 v0 Hv H1)|split;[apply (IHe2 k0 v0 Hv H2)|]].
    apply (IHe3 (S k0) v0); [apply lc_rec_mono with (n:=k0); [lia|assumption]|assumption].
  - destruct H as [H1 H2]; split; [apply (IHe1 k0 v0 Hv H1)|apply (IHe2 k0 v0 Hv H2)].
  - apply (IHe k0 v0 Hv H).
  - destruct H as [H1 H2]; split; [apply (IHe1 k0 v0 Hv H1)|apply (IHe2 k0 v0 Hv H2)].
Qed.

Lemma lc_trm_lc_rec : forall e, lc_trm e -> lc_rec 0 e.
Proof.
  intros e H. induction H; simpl.
  - auto. - auto. - auto.
  - split; assumption.
  - split; [assumption|split;[assumption|]].
    pick_fresh_gen L x. apply (lc_rec_open_var_inv 0 x). apply H2. auto.
  - split; [assumption|split;[assumption|]].
    pick_fresh_gen L x. apply (lc_rec_open_var_inv 0 x). apply H2. auto.
  - split; assumption.
  - assumption.
  - split; assumption.
Qed.

Lemma lc_rec_open_id : forall k v e, lc_rec k e -> open_trm_wrt_trm_rec k v e = e.
Proof.
  intros k v e. revert k v. induction e; intros k0 v0 H; simpl in *.
  - destruct (classicT (k0 = n)) as [Heq|Hneq]; [lia|reflexivity].
  - reflexivity. - reflexivity. - reflexivity.
  - destruct H as [H1 H2]. rewrite (IHe1 k0 v0 H1). rewrite (IHe2 k0 v0 H2). reflexivity.
  - destruct H as [H1 [H2 H3]]. rewrite (IHe1 k0 v0 H1). rewrite (IHe2 k0 v0 H2).
    rewrite (IHe3 (S k0) v0 H3). reflexivity.
  - destruct H as [H1 [H2 H3]]. rewrite (IHe1 k0 v0 H1). rewrite (IHe2 k0 v0 H2).
    rewrite (IHe3 (S k0) v0 H3). reflexivity.
  - destruct H as [H1 H2]. rewrite (IHe1 k0 v0 H1). rewrite (IHe2 k0 v0 H2). reflexivity.
  - rewrite (IHe k0 v0 H). reflexivity.
  - destruct H as [H1 H2]. rewrite (IHe1 k0 v0 H1). rewrite (IHe2 k0 v0 H2). reflexivity.
Qed.

Lemma lc_trm_open_id : forall e v, lc_trm e -> open_trm_wrt_trm e v = e.
Proof.
  intros e v H. unfold open_trm_wrt_trm. apply lc_rec_open_id. apply lc_trm_lc_rec. assumption.
Qed.

Lemma lc_trm_remove_anno : forall e, lc_trm e -> lc_trm [# e #].
Proof.
  intros e H. induction H; simpl.
  - constructor.
  - constructor.
  - constructor.
  - constructor; assumption.
  - eapply lc_trm_abs with (L:=L); [assumption|assumption|].
    intros x Hx. rewrite <- (remove_anno_open_var e2 x). apply H2. assumption.
  - eapply lc_trm_prod with (L:=L); [assumption|assumption|].
    intros x Hx. rewrite <- (remove_anno_open_var B x). apply H2. assumption.
  - constructor; assumption.
  - constructor; assumption.
  - assumption.
Qed.

Fixpoint tsize (e:trm) : nat :=
  match e with
  | trm_var_b _ => 1
  | trm_var_f _ => 1
  | trm_star => 1
  | trm_top => 1
  | trm_app a b => S (tsize a + tsize b)
  | trm_abs a A b => S (tsize a + tsize A + tsize b)
  | trm_prod a A b => S (tsize a + tsize A + tsize b)
  | trm_castup A a => S (tsize A + tsize a)
  | trm_castdn a => S (tsize a)
  | trm_anno a A => S (tsize a + tsize A)
  end.

Lemma tsize_open_var : forall k x e, tsize (open_trm_wrt_trm_rec k (trm_var_f x) e) = tsize e.
Proof.
  intros k x e. revert k. induction e; intros k0; simpl.
  - destruct (classicT (k0 = n)); reflexivity.
  - reflexivity. - reflexivity. - reflexivity.
  - rewrite IHe1. rewrite IHe2. reflexivity.
  - rewrite IHe1. rewrite IHe2. rewrite IHe3. reflexivity.
  - rewrite IHe1. rewrite IHe2. rewrite IHe3. reflexivity.
  - rewrite IHe1. rewrite IHe2. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

Lemma lc_rec_0_lc_trm_aux : forall n e, tsize e <= n -> lc_rec 0 e -> lc_trm e.
Proof.
  induction n as [|n IH]; intros e E H.
  - destruct e; simpl in E; lia.
  - destruct e; simpl in H.
    + simpl in E; lia.
    + constructor. + constructor. + constructor.
    + destruct H as [H1 H2]. constructor.
      * apply IH; [simpl in E; lia|assumption].
      * apply IH; [simpl in E; lia|assumption].
    + destruct H as [H1 [H2 H3]]. eapply lc_trm_abs with (L:=\{}).
      * apply IH; [simpl in E; lia|assumption].
      * apply IH; [simpl in E; lia|assumption].
      * intros x Hx. apply IH.
        -- unfold open_trm_wrt_trm. rewrite tsize_open_var. simpl in E. lia.
        -- apply lc_rec_open; [exact I|assumption].
    + destruct H as [H1 [H2 H3]]. eapply lc_trm_prod with (L:=\{}).
      * apply IH; [simpl in E; lia|assumption].
      * apply IH; [simpl in E; lia|assumption].
      * intros x Hx. apply IH.
        -- unfold open_trm_wrt_trm. rewrite tsize_open_var. simpl in E. lia.
        -- apply lc_rec_open; [exact I|assumption].
    + destruct H as [H1 H2]. constructor.
      * apply IH; [simpl in E; lia|assumption].
      * apply IH; [simpl in E; lia|assumption].
    + constructor. apply IH; [simpl in E; lia|assumption].
    + destruct H as [H1 H2]. constructor.
      * apply IH; [simpl in E; lia|assumption].
      * apply IH; [simpl in E; lia|assumption].
Qed.

Lemma lc_rec_0_lc_trm : forall e, lc_rec 0 e -> lc_trm e.
Proof. intros e H. apply (@lc_rec_0_lc_trm_aux (tsize e) e); [lia|assumption]. Qed.

Lemma lc_trm_lc_rec_iff : forall e, lc_trm e <-> lc_rec 0 e.
Proof. split; [apply lc_trm_lc_rec|apply lc_rec_0_lc_trm]. Qed.

Lemma length_push : forall (G:env) x (v:binding),
  LibList.length (G & x ~ v) = S (LibList.length G).
Proof.
  intros. rewrite concat_def. rewrite LibList.length_app. rewrite single_def.
  rewrite LibList.length_cons. rewrite LibList.length_nil. lia.
Qed.

Lemma dtyping_dwf : forall d G e A, dtyping d G e A -> dwf G.
Proof. intros d G e A H. induction H; eauto using dwf. Qed.

Lemma dwf_ok : forall G, dwf G -> ok G.
Proof.
  intros G. remember (LibList.length G) as n eqn:E. revert G E.
  induction n as [|n IH]; intros G E H.
  - symmetry in E. apply LibList.length_zero_inv in E. subst G.
    rewrite <- (empty_def binding). apply (ok_empty binding).
  - inversion H as [| G0 x e A0 Hx Ht1 Ht2].
    + apply (ok_empty binding).
    + subst G. rewrite length_push in E. injection E as E'.
      assert (Hdwf : dwf G0) by exact (@dtyping_dwf chk G0 e [#A0#] Ht1).
      assert (Hok : ok G0) by (apply IH; assumption).
      apply ok_push; assumption.
Qed.

Lemma cons_eq_push : forall (G:env) x b, List.cons (x,b) G = G & x ~ b.
Proof. intros. rewrite concat_def. rewrite single_def. reflexivity. Qed.

Lemma rem_bind_idem : forall b, rem_anno_env (rem_anno_env b) = rem_anno_env b.
Proof. intros [e A]. simpl. rewrite remove_anno_idem. rewrite remove_anno_idem. reflexivity. Qed.

Lemma rem_env_push : forall G x b,
  {# G & x ~ b #} = {#G#} & x ~ rem_anno_env b.
Proof. intros. rewrite map_push. reflexivity. Qed.

Lemma rem_env_idem : forall G, {# {#G#} #} = {#G#}.
Proof.
  intros G. induction G as [| [y b] G' IH].
  - rewrite map_def. rewrite LibList.map_nil. reflexivity.
  - rewrite cons_eq_push. rewrite rem_env_push. rewrite rem_env_push. rewrite IH. rewrite rem_bind_idem. reflexivity.
Qed.

Lemma ok_rem : forall G, ok G -> ok {#G#}.
Proof. intros. apply ok_map. assumption. Qed.

Lemma dom_rem : forall G, dom {#G#} = dom G.
Proof. intros. apply dom_map. Qed.

Lemma binds_rem : forall G x b, binds x b G -> binds x (rem_anno_env b) {#G#}.
Proof. intros. apply binds_map. assumption. Qed.

Lemma binds_rem_bind : forall G x e A,
  binds x (bind_sub e A) G -> binds x (bind_sub [#e#] [#A#]) {#G#}.
Proof.
  intros. assert (Hb : binds x (rem_anno_env (bind_sub e A)) {#G#}).
  { apply binds_map. assumption. }
  simpl in Hb. exact Hb.
Qed.

Lemma rem_bind_erased : forall e A, rem_anno_env (bind_sub [#e#] [#A#]) = bind_sub [#e#] [#A#].
Proof. intros. simpl. rewrite remove_anno_idem. rewrite remove_anno_idem. reflexivity. Qed.

Lemma dsub_erase : forall G e1 e2, dsub G e1 e2 -> dsub {#G#} [#e1#] [#e2#].
Proof.
  intros G e1 e2 H. induction H.
  - simpl. apply dsub_star. apply ok_rem. assumption.
  - simpl. apply (dsub_var_refl (G:={#G#}) (x:=x) (e:=[#e#]) (A:=[#A#])).
    + apply ok_rem. assumption.
    + eapply binds_rem_bind. exact H0.
  - simpl. eapply dsub_var_trans.
    + eapply binds_rem_bind. exact H.
    + apply IHdsub; exact Hy.
  - simpl. eapply dsub_top.
    + apply ok_rem. assumption.
    + apply lc_trm_remove_anno. assumption.
  - simpl. eapply dsub_lam with (L:=L).
    + apply ok_rem. assumption.
    + intros x Hx. rewrite remove_anno_idem. rewrite remove_anno_idem.
      pose proof (H1 x Hx) as Hx'.
      rewrite rem_env_push in Hx'. rewrite rem_bind_erased in Hx'.
      rewrite remove_anno_open_var in Hx'. rewrite remove_anno_open_var in Hx'.
      exact Hx'.
  - simpl. eapply dsub_app.
    + apply lc_trm_remove_anno. assumption.
    + apply IHdsub; exact Hy.
  - simpl. eapply dsub_pi with (L:=L).
    + apply IHdsub; exact Hy.
    + intros x Hx. rewrite remove_anno_idem. rewrite remove_anno_idem.
      pose proof (H1 x Hx) as Hx'.
      rewrite rem_env_push in Hx'. rewrite rem_bind_erased in Hx'.
      rewrite remove_anno_open_var in Hx'. rewrite remove_anno_open_var in Hx'.
      exact Hx'.
  - simpl. eapply dsub_castup.
    + apply lc_trm_remove_anno. assumption.
    + apply IHdsub; exact Hy.
  - simpl. eapply dsub_castdn. apply IHdsub; exact Hy.
Qed.

(* ================= annotation-freeness ================= *)

Definition Et (e:trm) : Prop := [# e #] = e.

Lemma Et_star : Et trm_star. Proof. unfold Et. reflexivity. Qed.
Lemma Et_top : Et trm_top. Proof. unfold Et. reflexivity. Qed.
Lemma Et_var : forall x, Et (trm_var_f x). Proof. intro. unfold Et. reflexivity. Qed.

Lemma Et_open : forall e v, Et e -> Et v -> Et (open_trm_wrt_trm e v).
Proof.
  intros e v He Hv. unfold Et in *. rewrite remove_anno_open. rewrite He. rewrite Hv. reflexivity.
Qed.

Lemma open_var_head_not_anno : forall e,
  (forall a b, e <> trm_anno a b) ->
  forall k x a b, open_trm_wrt_trm_rec k (trm_var_f x) e <> trm_anno a b.
Proof.
  intros e H k x a b. destruct e; simpl; try discriminate.
  - destruct (classicT (k = n)); discriminate.
  - exfalso. apply (H e1 e2). reflexivity.
Qed.

Lemma Et_open_rec_inv : forall k x e, Et (open_trm_wrt_trm_rec k (trm_var_f x) e) -> Et e.
Proof.
  intros k x e. revert k. induction e; intros k0 H; simpl in H; unfold Et in *; simpl in *.
  - reflexivity.
  - reflexivity. - reflexivity. - reflexivity.
  - injection H as H1 H2. simpl. rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2). reflexivity.
  - injection H as H1 H2 H3. simpl.
    rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2). rewrite (IHe3 (S k0) H3). reflexivity.
  - injection H as H1 H2 H3. simpl.
    rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2). rewrite (IHe3 (S k0) H3). reflexivity.
  - injection H as H1 H2. simpl. rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2). reflexivity.
  - injection H as H1. simpl. rewrite (IHe k0 H1). reflexivity.
  - exfalso. rewrite remove_anno_open_rec in H. simpl in H.
    refine (@open_var_head_not_anno [#e1#] (remove_anno_not_anno e1) k0 x
             (open_trm_wrt_trm_rec k0 (trm_var_f x) e1)
             (open_trm_wrt_trm_rec k0 (trm_var_f x) e2) H).
Qed.

Lemma Et_open_var_inv : forall e x, Et (open_trm_wrt_trm e (trm_var_f x)) -> Et e.
Proof. intros. unfold open_trm_wrt_trm in H. apply (Et_open_rec_inv 0 x). exact H. Qed.

Definition Eenv (G:env) : Prop := forall x b, binds x b G -> rem_anno_env b = b.

Lemma Eenv_push : forall G x e A,
  Eenv G -> Et e -> Et A -> Eenv (G & x ~ bind_sub e A).
Proof.
  intros G x e A HE He HA y b Hb. unfold Eenv in HE. unfold Et in He, HA.
  apply binds_push_inv in Hb as [[Heq Hb] | [Hneq Hb]].
  - inversion Heq. subst. simpl. rewrite He. rewrite HA. reflexivity.
  - exact (HE y b Hb).
Qed.

(* ================= local closedness of environments ================= *)

Definition lc_env (G:env) : Prop :=
  forall x b, binds x b G -> lc_binding b.

Lemma lc_env_push : forall G x e A,
  lc_env G -> lc_trm e -> lc_trm A -> lc_env (G & x ~ bind_sub e A).
Proof.
  intros G x e A HE He HA y b Hb. unfold lc_env in HE.
  apply binds_push_inv in Hb as [[Heq Hb] | [Hneq Hb]].
  - inversion Heq. subst. constructor; assumption.
  - exact (HE y b Hb).
Qed.

Lemma lc_env_push_erased : forall G x e A,
  lc_env G -> lc_trm e -> lc_trm A ->
  lc_env (G & x ~ bind_sub [#e#] [#A#]).
Proof.
  intros. apply lc_env_push; auto using lc_trm_remove_anno.
Qed.

Lemma lc_env_ok_binds : forall G x e A,
  lc_env G -> binds x (bind_sub e A) G -> lc_trm e /\ lc_trm A.
Proof. intros. apply H in H0. inversion H0. auto. Qed.

Lemma dtyping_lc : forall d G e A, dtyping d G e A -> lc_env G -> lc_trm e /\ lc_trm A.
Proof.
  intros d G e A H. induction H; intros HE.
  - split; constructor.
  - split; [constructor|].
    pose proof (@lc_env_ok_binds G x e A HE H0) as [_ HA]. exact HA.
  - split; [constructor|]. exact (proj1 (IHdtyping HE)).
  - split.
    + eapply lc_trm_abs with (L:=L).
      * exact (proj1 (IHdtyping1 HE)).
      * exact (proj1 (IHdtyping2 HE)).
      * intros x0 Hx.
        assert (HEext : lc_env (G & x0 ~ bind_sub [#e1#] [#A#])).
        { apply lc_env_push_erased; [exact HE|exact (proj1 (IHdtyping1 HE))|exact (proj1 (IHdtyping2 HE))]. }
        exact (proj1 (H2 x0 Hx HEext)).
    + eapply lc_trm_prod with (L:=L).
      * apply lc_trm_remove_anno. exact (proj1 (IHdtyping1 HE)).
      * exact (proj2 (IHdtyping1 HE)).
      * intros x0 Hx.
        assert (HEext : lc_env (G & x0 ~ bind_sub [#e1#] [#A#])).
        { apply lc_env_push_erased; [exact HE|exact (proj1 (IHdtyping1 HE))|exact (proj1 (IHdtyping2 HE))]. }
        exact (proj2 (H2 x0 Hx HEext)).
  - split.
    + constructor; [exact (proj1 (IHdtyping2 HE))|exact (proj1 (IHdtyping1 HE))].
    + apply lc_trm_lc_rec_iff. apply lc_rec_open.
      * apply lc_trm_lc_rec. apply lc_trm_remove_anno. exact (proj1 (IHdtyping1 HE)).
      * assert (Hrec : lc_rec 0 (trm_prod e3 B C)) by (apply lc_trm_lc_rec; exact (proj2 (IHdtyping2 HE))).
        destruct Hrec as [_ [_ HC]]. exact HC.
  - split.
    + eapply lc_trm_prod with (L:=L).
      * exact (proj1 (IHdtyping1 HE)).
      * exact (proj1 (IHdtyping2 HE)).
      * intros x0 Hx.
        assert (HEext : lc_env (G & x0 ~ bind_sub [#e#] [#A#])).
        { apply lc_env_push_erased; [exact HE|exact (proj1 (IHdtyping1 HE))|exact (proj1 (IHdtyping2 HE))]. }
        exact (proj1 (H2 x0 Hx HEext)).
    + constructor.
  - split.
    + constructor; [exact (proj1 (IHdtyping1 HE))|exact (proj1 (IHdtyping2 HE))].
    + apply lc_trm_remove_anno. exact (proj1 (IHdtyping1 HE)).
  - split.
    + constructor. exact (proj1 (IHdtyping2 HE)).
    + exact (proj1 (IHdtyping1 HE)).
  - split.
    + constructor; [exact (proj1 (IHdtyping1 HE))|exact (proj1 (IHdtyping2 HE))].
    + apply lc_trm_remove_anno. exact (proj1 (IHdtyping2 HE)).
  - split; [exact (proj1 (IHdtyping1 HE))|exact (proj1 (IHdtyping2 HE))].
  - apply IHdtyping. exact HE.
Qed.

Lemma dwf_lc_env : forall G, dwf G -> lc_env G.
Proof.
  intros G. remember (LibList.length G) as n eqn:E. revert G E.
  induction n as [|n IH]; intros G E H.
  - symmetry in E. apply LibList.length_zero_inv in E. subst G.
    unfold lc_env. intros x b Hb. try (rewrite <- (empty_def binding) in Hb). apply binds_empty_inv in Hb. contradiction.
  - inversion H as [| G0 x e A0 Hx Ht1 Ht2].
    + unfold lc_env. intros y b Hb. try (rewrite <- (empty_def binding) in Hb). apply binds_empty_inv in Hb. contradiction.
    + subst G. rewrite length_push in E. injection E as E'.
      assert (Hdwf : dwf G0) by exact (@dtyping_dwf chk G0 e [#A0#] Ht1).
      assert (Hlc : lc_env G0) by (apply IH; assumption).
      assert (Hlc1 : lc_trm e /\ lc_trm [#A0#]) by exact (@dtyping_lc chk G0 e [#A0#] Ht1 Hlc).
      assert (Hlc2 : lc_trm A0 /\ lc_trm trm_star) by exact (@dtyping_lc chk G0 A0 trm_star Ht2 Hlc).
      apply (@lc_env_push_erased G0 x e A0 Hlc (proj1 Hlc1) (proj1 Hlc2)).
Qed.

Lemma dwf_E : forall G, dwf G -> {#G#} = G.
Proof.
  intros G. remember (LibList.length G) as n eqn:E. revert G E.
  induction n as [|n IH]; intros G E H.
  - symmetry in E. apply LibList.length_zero_inv in E. subst G.
    rewrite map_def. rewrite LibList.map_nil. reflexivity.
  - inversion H as [| G0 x e A0 Hx Ht1 Ht2].
    + subst G. rewrite (empty_def binding). rewrite map_def. rewrite LibList.map_nil. reflexivity.
    + subst G. rewrite length_push in E. injection E as E'.
      assert (Hdwf : dwf G0) by exact (@dtyping_dwf chk G0 e [#A0#] Ht1).
      assert (HE : {#G0#} = G0) by (apply IH; assumption).
      rewrite rem_env_push. rewrite HE. rewrite rem_bind_erased. reflexivity.
Qed.

(* ================= properties of the unified system ================= *)

Lemma sub_wf : forall G e1 e2 A, sub G e1 e2 A -> wf G.
Proof. intros G e1 e2 A H. induction H; auto. Qed.

Lemma sub_E : forall G e1 e2 A, sub G e1 e2 A -> Eenv G -> Et e1 /\ Et e2 /\ Et A.
Proof.
  intros G e1 e2 A H. induction H; intros HE.
  - split; [apply Et_star|split; apply Et_star].
  - assert (HA : Et A).
    { unfold Et. unfold Eenv in HE. pose proof (HE x5 (bind_sub e A) H0) as Hb.
      simpl in Hb. injection Hb as _ HAe. exact HAe. }
    split; [apply Et_var|split; [apply Et_var|exact HA]].
  - destruct (IHsub HE) as [_ [He2 HA]].
    split; [apply Et_var|split; assumption].
  - destruct (IHsub HE) as [He [_ HA]].
    split; [exact He|split; [apply Et_top|exact HA]].
  - destruct (IHsub HE) as [HA _].
    split; [apply Et_top|split; [apply Et_top|exact HA]].
  - destruct (IHsub1 HE) as [He1 [_ HA1]].
    destruct (IHsub2 HE) as [HA _].
    pick_fresh_gen L x0.
    assert (HEext : Eenv (G & x0 ~ bind_sub e1 A)).
    { apply Eenv_push; assumption. }
    destruct (H2 x0 Fr HEext) as [He2 [He2' HB]].
    assert (He2E : Et e2) by (apply Et_open_var_inv with (x:=x0); exact He2).
    assert (He2'E : Et e2') by (apply Et_open_var_inv with (x:=x0); exact He2').
    assert (HBE : Et B) by (apply Et_open_var_inv with (x:=x0); exact HB).
    split; [|split].
    + unfold Et. simpl. f_equal; [exact He1|exact HA1|exact He2E].
    + unfold Et. simpl. f_equal; [exact He1|exact HA1|exact He2'E].
    + unfold Et. simpl. f_equal; [exact He1|exact HA1|exact HBE].
  - destruct (IHsub1 HE) as [He1 [He2 Hprod]].
    destruct (IHsub2 HE) as [HA [_ _]].
    unfold Et in Hprod. simpl in Hprod. injection Hprod as He3 HB HC.
    split; [|split].
    + unfold Et. simpl. f_equal; assumption.
    + unfold Et. simpl. f_equal; assumption.
    + apply Et_open; assumption.
  - destruct (IHsub1 HE) as [HA' [HA _]].
    destruct (IHsub2 HE) as [He _].
    pick_fresh_gen L x0.
    assert (HEext1 : Eenv (G & x0 ~ bind_sub e A)).
    { apply Eenv_push; [exact HE|exact He|exact HA]. }
    destruct (H3 x0 Fr HEext1) as [HB _].
    assert (HBE : Et B) by (apply Et_open_var_inv with (x:=x0); exact HB).
    assert (HEext2 : Eenv (G & x0 ~ bind_sub e A')).
    { apply Eenv_push; [exact HE|exact He|exact HA']. }
    destruct (H5 x0 Fr HEext2) as [_ [HB' _]].
    assert (HB'E : Et B') by (apply Et_open_var_inv with (x:=x0); exact HB').
    split; [|split].
    + unfold Et. simpl. f_equal; [exact He|exact HA|exact HBE].
    + unfold Et. simpl. f_equal; [exact He|exact HA'|exact HB'E].
    + apply Et_star.
  - destruct (IHsub1 HE) as [HB [_ _]].
    destruct (IHsub2 HE) as [He1 [He2 _]].
    split; [|split].
    + unfold Et. simpl. f_equal; assumption.
    + unfold Et. simpl. f_equal; assumption.
    + exact HB.
  - destruct (IHsub1 HE) as [HB [_ _]].
    destruct (IHsub2 HE) as [He1 [He2 _]].
    split; [|split].
    + unfold Et. simpl. f_equal; assumption.
    + unfold Et. simpl. f_equal; assumption.
    + exact HB.
  - destruct (IHsub1 HE) as [He1 [He2 _]].
    destruct (IHsub2 HE) as [_ [HB _]].
    split; [exact He1|split; [exact He2|exact HB]].
Qed.

Lemma sub_lc : forall G e1 e2 A, sub G e1 e2 A -> lc_env G -> lc_trm e1 /\ lc_trm e2 /\ lc_trm A.
Proof.
  intros G e1 e2 A H. induction H; intros HE.
  - split; [constructor|split; constructor].
  - pose proof (@lc_env_ok_binds G x5 e A HE H0) as [He HA].
    split; [constructor|split; [constructor|exact HA]].
  - destruct (IHsub HE) as [He1 [He2 HA]].
    split; [constructor|split; assumption].
  - destruct (IHsub HE) as [He [_ HA]].
    split; [exact He|split; [constructor|exact HA]].
  - destruct (IHsub HE) as [HA _].
    split; [constructor|split; [constructor|exact HA]].
  - destruct (IHsub1 HE) as [He1 [_ HA1]].
    destruct (IHsub2 HE) as [HA _].
    split; [|split].
    + eapply lc_trm_abs with (L:=L).
      * exact He1. * exact HA1.
      * intros x Hx. assert (HEext : lc_env (G & x ~ bind_sub e1 A)).
        { apply lc_env_push; assumption. }
        exact (proj1 (H2 x Hx HEext)).
    + eapply lc_trm_abs with (L:=L).
      * exact He1. * exact HA1.
      * intros x Hx. assert (HEext : lc_env (G & x ~ bind_sub e1 A)).
        { apply lc_env_push; assumption. }
        exact (proj1 (proj2 (H2 x Hx HEext))).
    + eapply lc_trm_prod with (L:=L).
      * exact He1. * exact HA1.
      * intros x Hx. assert (HEext : lc_env (G & x ~ bind_sub e1 A)).
        { apply lc_env_push; assumption. }
        exact (proj2 (proj2 (H2 x Hx HEext))).
  - destruct (IHsub1 HE) as [He1 [He2 Hprod]].
    destruct (IHsub2 HE) as [HA [_ _]].
    split; [|split].
    + constructor; assumption.
    + constructor; assumption.
    + apply lc_trm_lc_rec_iff. apply lc_rec_open.
      * apply lc_trm_lc_rec. exact HA.
      * assert (Hrec : lc_rec 0 (trm_prod e3 B C)) by (apply lc_trm_lc_rec; exact Hprod).
        destruct Hrec as [_ [_ HC]]. exact HC.
  - destruct (IHsub1 HE) as [HA' [HA _]].
    destruct (IHsub2 HE) as [He _].
    split; [|split].
    + eapply lc_trm_prod with (L:=L).
      * exact He. * exact HA.
      * intros x Hx. assert (HEext1 : lc_env (G & x ~ bind_sub e A)).
        { apply lc_env_push; [exact HE|exact He|exact HA]. }
        exact (proj1 (H3 x Hx HEext1)).
    + eapply lc_trm_prod with (L:=L).
      * exact He. * exact HA'.
      * intros x Hx. assert (HEext2 : lc_env (G & x ~ bind_sub e A')).
        { apply lc_env_push; [exact HE|exact He|exact HA']. }
        exact (proj1 (proj2 (H5 x Hx HEext2))).
    + constructor.
  - destruct (IHsub1 HE) as [HB _].
    destruct (IHsub2 HE) as [He1 [He2 _]].
    split; [|split].
    + constructor; assumption.
    + constructor; assumption.
    + exact HB.
  - destruct (IHsub1 HE) as [HB _].
    destruct (IHsub2 HE) as [He1 [He2 _]].
    split; [|split].
    + constructor; assumption.
    + constructor; assumption.
    + exact HB.
  - destruct (IHsub1 HE) as [He1 [He2 _]].
    destruct (IHsub2 HE) as [_ [HB _]].
    split; [exact He1|split; [exact He2|exact HB]].
Qed.

Lemma dwf_Eenv : forall G, dwf G -> Eenv G.
Proof.
  intros G. remember (LibList.length G) as n eqn:E. revert G E.
  induction n as [|n IH]; intros G E H.
  - symmetry in E. apply LibList.length_zero_inv in E. subst G.
    unfold Eenv. intros x b Hb. try (rewrite <- (empty_def binding) in Hb). apply binds_empty_inv in Hb. contradiction.
  - inversion H as [| G0 x e A0 Hx Ht1 Ht2].
    + unfold Eenv. intros y b Hb. try (rewrite <- (empty_def binding) in Hb). apply binds_empty_inv in Hb. contradiction.
    + subst G. rewrite length_push in E. injection E as E'.
      assert (Hdwf : dwf G0) by exact (@dtyping_dwf chk G0 e [#A0#] Ht1).
      assert (HE : Eenv G0) by (apply IH; assumption).
      eapply Eenv_push with (e:=[#e#]) (A:=[#A0#]).
      * exact HE.
      * unfold Et. apply remove_anno_idem.
      * unfold Et. apply remove_anno_idem.
Qed.

Lemma wf_Eenv : forall G, wf G -> Eenv G.
Proof.
  intros G. remember (LibList.length G) as n eqn:E. revert G E.
  induction n as [|n IH]; intros G E H.
  - symmetry in E. apply LibList.length_zero_inv in E. subst G.
    unfold Eenv. intros x b Hb. try (rewrite <- (empty_def binding) in Hb). apply binds_empty_inv in Hb. contradiction.
  - inversion H as [| G0 x e A Hse Hsa Hx].
    + unfold Eenv. intros y b Hb. try (rewrite <- (empty_def binding) in Hb). apply binds_empty_inv in Hb. contradiction.
    + subst G. rewrite length_push in E. injection E as E'.
      assert (Hwf : wf G0) by (eapply sub_wf; exact Hse).
      assert (HE : Eenv G0) by (apply IH; assumption).
      destruct (@sub_E G0 e e A Hse HE) as [He [_ HA]].
      eapply Eenv_push; assumption.
Qed.

Lemma wf_ok : forall G, wf G -> ok G.
Proof.
  intros G. remember (LibList.length G) as n eqn:E. revert G E.
  induction n as [|n IH]; intros G E H.
  - symmetry in E. apply LibList.length_zero_inv in E. subst G.
    rewrite <- (empty_def binding). apply (ok_empty binding).
  - inversion H as [| G0 x e A Hse Hsa Hx].
    + apply (ok_empty binding).
    + subst G. rewrite length_push in E. injection E as E'.
      assert (Hwf : wf G0) by (eapply sub_wf; exact Hse).
      assert (Hok : ok G0) by (apply IH; assumption).
      apply ok_push; assumption.
Qed.

Lemma wf_lc_env : forall G, wf G -> lc_env G.
Proof.
  intros G. remember (LibList.length G) as n eqn:E. revert G E.
  induction n as [|n IH]; intros G E H.
  - symmetry in E. apply LibList.length_zero_inv in E. subst G.
    unfold lc_env. intros x b Hb. try (rewrite <- (empty_def binding) in Hb). apply binds_empty_inv in Hb. contradiction.
  - inversion H as [| G0 x e A Hse Hsa Hx].
    + unfold lc_env. intros y b Hb. try (rewrite <- (empty_def binding) in Hb). apply binds_empty_inv in Hb. contradiction.
    + subst G. rewrite length_push in E. injection E as E'.
      assert (Hwf : wf G0) by (eapply sub_wf; exact Hse).
      assert (HE : lc_env G0) by (apply IH; assumption).
      destruct (@sub_lc G0 e e A Hse HE) as [He [_ HA]].
      apply lc_env_push; assumption.
Qed.

(* ================= closing and renaming ================= *)

Fixpoint close_rec (x:var) (k:nat) (e:trm) : trm :=
  match e with
  | trm_var_b i => trm_var_b i
  | trm_var_f y => match classicT (y = x) with left _ => trm_var_b k | right _ => trm_var_f y end
  | trm_star => trm_star
  | trm_top => trm_top
  | trm_app a b => trm_app (close_rec x k a) (close_rec x k b)
  | trm_abs a A b => trm_abs (close_rec x k a) (close_rec x k A) (close_rec x (S k) b)
  | trm_prod a A b => trm_prod (close_rec x k a) (close_rec x k A) (close_rec x (S k) b)
  | trm_castup A a => trm_castup (close_rec x k A) (close_rec x k a)
  | trm_castdn a => trm_castdn (close_rec x k a)
  | trm_anno a A => trm_anno (close_rec x k a) (close_rec x k A)
  end.

Lemma close_open : forall x k e, lc_rec k e -> open_trm_wrt_trm_rec k (trm_var_f x) (close_rec x k e) = e.
Proof.
  intros x k e. revert k. induction e; intros k0 H; simpl in *.
  - destruct (classicT (k0 = n)) as [Heq|Hneq].
    + subst n. exfalso; lia.
    + simpl. destruct (classicT (k0 = n)) as [H1|H2]; [congruence|reflexivity].
  - destruct (classicT (x5 = x)) as [Heq|Hneq].
    + subst x5. simpl. destruct (classicT (k0 = k0)) as [H1|H2]; [reflexivity|exfalso; apply H2; reflexivity].
    + simpl. destruct (classicT (x5 = x)) as [H1|H2]; [congruence|reflexivity].
  - reflexivity. - reflexivity.
  - destruct H as [H1 H2]. simpl. rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2). reflexivity.
  - destruct H as [H1 [H2 H3]]. simpl.
    rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2). rewrite (IHe3 (S k0) H3). reflexivity.
  - destruct H as [H1 [H2 H3]]. simpl.
    rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2). rewrite (IHe3 (S k0) H3). reflexivity.
  - destruct H as [H1 H2]. simpl. rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2). reflexivity.
  - simpl. rewrite (IHe k0 H). reflexivity.
  - destruct H as [H1 H2]. simpl. rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2). reflexivity.
Qed.

Lemma open_close : forall x k e,
  x \notin fv_trm e -> close_rec x k (open_trm_wrt_trm_rec k (trm_var_f x) e) = e.
Proof.
  intros x k e. revert k. induction e; intros k0 H; simpl in *.
  - destruct (classicT (k0 = n)) as [Heq|Hneq].
    + subst n. simpl. destruct (classicT (x = x)) as [H1|H2]; [reflexivity|exfalso; apply H2; reflexivity].
    + simpl. destruct (classicT (k0 = n)) as [H1|H2]; [congruence|reflexivity].
  - destruct (classicT (x5 = x)) as [Heq|Hneq].
    + subst x5. exfalso. apply H. apply in_singleton_self.
    + simpl. destruct (classicT (x5 = x)) as [H1|H2]; [congruence|reflexivity].
  - reflexivity. - reflexivity.
  - apply notin_union_r in H as [H1 H2]. simpl.
    rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2). reflexivity.
  - apply notin_union_r in H as [H1 H2]. apply notin_union_r in H2 as [H2a H2b]. simpl.
    rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2a). rewrite (IHe3 (S k0) H2b). reflexivity.
  - apply notin_union_r in H as [H1 H2]. apply notin_union_r in H2 as [H2a H2b]. simpl.
    rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2a). rewrite (IHe3 (S k0) H2b). reflexivity.
  - apply notin_union_r in H as [H1 H2]. simpl.
    rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2). reflexivity.
  - simpl. rewrite (IHe k0 H). reflexivity.
  - apply notin_union_r in H as [H1 H2]. simpl.
    rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2). reflexivity.
Qed.

Lemma remove_anno_close : forall x k e,
  [# close_rec x k e #] = close_rec x k [# e #].
Proof.
  intros x k e. revert k. induction e; intros k0; simpl.
  - reflexivity.
  - rewrite remove_anno_classic. reflexivity.
  - reflexivity. - reflexivity.
  - f_equal; [exact (IHe1 k0)|exact (IHe2 k0)].
  - f_equal; [exact (IHe1 k0)|exact (IHe2 k0)|exact (IHe3 (S k0))].
  - f_equal; [exact (IHe1 k0)|exact (IHe2 k0)|exact (IHe3 (S k0))].
  - f_equal; [exact (IHe1 k0)|exact (IHe2 k0)].
  - f_equal; exact (IHe k0).
  - apply IHe1.
Qed.

Definition rename (x y:var) (e:trm) : trm := subst_trm (trm_var_f y) x e.

Definition rename_binding (x y:var) (b:binding) : binding :=
  match b with bind_sub e A => bind_sub (rename x y e) (rename x y A) end.

Fixpoint rename_env (x y:var) (G:env) : env :=
  match G with
  | nil => nil
  | (z,b) :: G' =>
      (match classicT (z = x) with left _ => y | right _ => z end,
       rename_binding x y b) :: rename_env x y G'
  end.

Lemma rename_env_cons : forall x y (G:env) z b,
  rename_env x y (List.cons (z,b) G) =
  List.cons (match classicT (z = x) with left _ => y | right _ => z end,
             rename_binding x y b) (rename_env x y G).
Proof. intros. reflexivity. Qed.

Lemma rename_env_push : forall x y (G:env) z b,
  rename_env x y (G & z ~ b) =
  rename_env x y G & (match classicT (z = x) with left _ => y | right _ => z end) ~ rename_binding x y b.
Proof.
  intros. rewrite <- cons_eq_push. rewrite rename_env_cons. rewrite <- cons_eq_push. reflexivity.
Qed.

Lemma in_dom_push_self : forall (G:env) x b, x \in dom (G & x ~ b).
Proof. intros. eapply get_some_inv. apply binds_get. apply binds_tail. Qed.

Lemma binds_rename_env : forall x y (G:env) z b,
  y # G -> binds z b G ->
  binds (match classicT (z = x) with left _ => y | right _ => z end)
         (rename_binding x y b) (rename_env x y G).
Proof.
  intros x y G. induction G as [| [zz bb] G' IH]; intros z b Hy Hb.
  - try (rewrite <- (empty_def binding) in Hb). apply binds_empty_inv in Hb. contradiction.
  - assert (Hy' : y \notin dom (G' & zz ~ bb)) by (rewrite <- cons_eq_push; exact Hy).
    rewrite dom_push in Hy'.
    apply notin_union_r in Hy' as [Hyz HyG].
    assert (Hzzdom : zz \in dom ((zz,bb)::G')).
    { rewrite cons_eq_push. apply in_dom_push_self. }
    assert (Hyzz : y <> zz) by (intro Heq; apply Hy; subst zz; exact Hzzdom).
    assert (Hzdom : z \in dom ((zz,bb)::G')).
    { eapply get_some_inv. apply binds_get. exact Hb. }
    assert (Hzy : z <> y) by (intro Heq; apply Hy; subst y; exact Hzdom).
    rewrite cons_eq_push in Hb. apply binds_push_inv in Hb as [[Heq Hb]|[Hneq Hb]].
    + inversion Heq. subst zz bb. rewrite cons_eq_push. rewrite rename_env_push.
      destruct (classicT (z = x)) as [H1|H2]; apply binds_tail.
    + rewrite cons_eq_push. rewrite rename_env_push.
      assert (Hkey : (match classicT (z = x) with left _ => y | right _ => z end)
                  <> (match classicT (zz = x) with left _ => y | right _ => zz end)).
      { intro Heqk.
        destruct (classicT (z = x)) as [Hzx|Hzx]; destruct (classicT (zz = x)) as [Hzzx|Hzzx];
        simpl in Heqk; try discriminate.
        - apply Hneq. transitivity x; [assumption|symmetry; assumption].
        - apply Hyzz. exact Heqk.
        - apply Hzy. exact Heqk.
        - apply Hneq. exact Heqk. }
      destruct (classicT ((match classicT (z = x) with left _ => y | right _ => z end) =
                         (match classicT (zz = x) with left _ => y | right _ => zz end)))
        as [Heqk|Hneqk].
      * exfalso. apply Hkey. exact Heqk.
      * apply binds_concat_left.
        -- apply IH; assumption.
        -- rewrite dom_single. apply notin_singleton_l. exact Hneqk.
Qed.

Lemma remove_anno_rename : forall x y e,
  [# rename x y e #] = rename x y [# e #].
Proof.
  intros. unfold rename. rewrite remove_anno_subst. simpl. reflexivity.
Qed.

Lemma lc_rec_rename : forall n x y e, lc_rec n (rename x y e) <-> lc_rec n e.
Proof.
  intros n x y e. revert n. induction e; intros n0; simpl.
  - reflexivity.
  - unfold rename. simpl. destruct (classicT (x5 = x)); simpl; tauto.
  - reflexivity. - reflexivity.
  - unfold rename. simpl. rewrite IHe1, IHe2. tauto.
  - unfold rename. simpl. rewrite IHe1, IHe2, IHe3. tauto.
  - unfold rename. simpl. rewrite IHe1, IHe2, IHe3. tauto.
  - unfold rename. simpl. rewrite IHe1, IHe2. tauto.
  - unfold rename. simpl. rewrite IHe. tauto.
  - unfold rename. simpl. rewrite IHe1, IHe2. tauto.
Qed.

Lemma lc_rename : forall e x y, lc_trm e -> lc_trm (rename x y e).
Proof.
  intros. apply lc_rec_0_lc_trm. apply lc_rec_rename. apply lc_trm_lc_rec. assumption.
Qed.

Lemma Et_rename : forall e x y, Et e -> Et (rename x y e).
Proof.
  intros e x y H. unfold Et in *. rewrite remove_anno_rename. rewrite H. reflexivity.
Qed.

Lemma subst_open_var : forall x0 x z k e,
  z <> x0 ->
  subst_trm (trm_var_f x) x0 (open_trm_wrt_trm_rec k (trm_var_f z) e) =
  open_trm_wrt_trm_rec k (trm_var_f z) (subst_trm (trm_var_f x) x0 e).
Proof.
  intros x0 x z k e. revert k. induction e; intros k0 Hneq; simpl.
  - destruct (classicT (k0 = n)) as [Heq|Hneq2].
    + subst n. simpl. destruct (classicT (z = x0)) as [Hzx|Hzx]; simpl.
      * exfalso. apply Hneq. exact Hzx.
      * reflexivity.
    + destruct (classicT (k0 = n)) as [H1|H2]; [congruence|reflexivity].
  - destruct (classicT (x5 = x0)) as [Heq|Hneq2]; simpl; reflexivity.
  - reflexivity. - reflexivity.
  - f_equal; [apply IHe1|apply IHe2]; exact Hneq.
  - f_equal; [apply IHe1|apply IHe2|apply IHe3]; exact Hneq.
  - f_equal; [apply IHe1|apply IHe2|apply IHe3]; exact Hneq.
  - f_equal; [apply IHe1|apply IHe2]; exact Hneq.
  - f_equal; apply IHe; exact Hneq.
  - f_equal; [apply IHe1|apply IHe2]; exact Hneq.
Qed.

Lemma rename_open_var : forall x0 x z k e,
  z <> x0 -> rename x0 x (open_trm_wrt_trm_rec k (trm_var_f z) e) =
             open_trm_wrt_trm_rec k (trm_var_f z) (rename x0 x e).
Proof. intros. unfold rename. apply subst_open_var. assumption. Qed.

Lemma notin_union_split : forall (x:var) (E F:fset var), x \notin E \u F -> x \notin E /\ x \notin F.
Proof. intros. apply notin_union_r. assumption. Qed.

Lemma rename_key_fresh : forall x y (E:env) z,
  x <> y -> z <> y -> z # E -> y # E ->
  (match classicT (z = x) with left _ => y | right _ => z end) # rename_env x y E.
Proof.
  intros x y E. induction E as [| [zz bb] E' IH]; intros z Hxy Hzy HzE HyE.
  - simpl. rewrite <- (empty_def binding). rewrite (dom_empty binding). apply notin_empty.
  - rewrite cons_eq_push in HzE. rewrite dom_push in HzE.
    rewrite cons_eq_push in HyE. rewrite dom_push in HyE.
    apply notin_union_split in HzE as [Hzz HzE'].
    apply notin_union_split in HyE as [Hyzz0 HyE'].
    assert (Hzz' : z <> zz) by (apply notin_singleton_r; exact Hzz).
    assert (Hyzz : y <> zz) by (apply notin_singleton_r; exact Hyzz0).
    rewrite rename_env_cons. rewrite cons_eq_push. rewrite dom_push.
    apply notin_union_l.
    + apply notin_singleton_l.
      intro Heqk.
      destruct (classicT (z = x)) as [Hzx|Hzx]; destruct (classicT (zz = x)) as [Hzzx|Hzzx];
      simpl in Heqk; try discriminate.
      * apply Hzz'. transitivity x; [assumption|symmetry; assumption].
      * apply Hyzz. exact Heqk.
      * apply Hzy. exact Heqk.
      * apply Hzz'. exact Heqk.
    + apply IH; assumption.
Qed.

Lemma ok_rename_env : forall G x y, x <> y -> y # G -> ok G -> ok (rename_env x y G).
Proof.
  intros G x y Hxy HyG Hok. revert x y Hxy HyG.
  induction Hok using ok_ind with
    (P := fun E => forall x y, x <> y -> y # E -> ok (rename_env x y E)).
  - intros x0 y0 Hxy0 Hy0. rewrite (empty_def binding). simpl.
    rewrite <- (empty_def binding). apply (ok_empty binding).
  - intros x0 y0 Hxy0 Hy0.
    rewrite dom_push in Hy0. apply notin_union_r in Hy0 as [Hyx HyE0].
    rewrite rename_env_push.
    apply ok_push.
    + apply IHHok; assumption.
    + eapply rename_key_fresh; [exact Hxy0| |exact H|exact HyE0].
      apply notin_singleton_r in Hyx. symmetry. exact Hyx.
Qed.

Lemma binds_rename_env_same : forall x y (G:env) b,
  y # G -> binds x b G -> binds y (rename_binding x y b) (rename_env x y G).
Proof.
  intros. pose proof (@binds_rename_env x y G x b H H0) as Hb.
  destruct (classicT (x = x)) as [H1|H2].
  - simpl in Hb. exact Hb.
  - exfalso. apply H2. reflexivity.
Qed.

Lemma binds_rename_env_diff : forall x y (G:env) z b,
  z <> x -> y # G -> binds z b G -> binds z (rename_binding x y b) (rename_env x y G).
Proof.
  intros. pose proof (@binds_rename_env x y G z b H0 H1) as Hb.
  destruct (classicT (z = x)) as [Heq|Hneq].
  - exfalso. apply H. exact Heq.
  - simpl in Hb. exact Hb.
Qed.
Lemma rename_open_var' : forall x y z e,
  z <> x ->
  rename x y (open_trm_wrt_trm e (trm_var_f z)) =
  open_trm_wrt_trm (rename x y e) (trm_var_f z).
Proof. intros. unfold open_trm_wrt_trm. apply rename_open_var. assumption. Qed.

Lemma dsub_rename : forall G e1 e2 x y,
  x <> y -> y # G -> dsub G e1 e2 ->
  dsub (rename_env x y G) (rename x y e1) (rename x y e2).
Proof.
  intros G e1 e2 x y Hxy Hy H. induction H.
  - unfold rename. simpl. apply dsub_star. apply (ok_rename_env Hxy Hy H).
  - unfold rename. simpl. destruct (classicT (x0 = x)) as [Heq|Hneq]; simpl.
    + subst x0. eapply (dsub_var_refl (G:=rename_env x y G)).
      * apply (ok_rename_env Hxy Hy H).
      * apply (binds_rename_env_same Hy H0).
    + eapply (dsub_var_refl (G:=rename_env x y G)).
      * apply (ok_rename_env Hxy Hy H).
      * apply (binds_rename_env_diff Hneq Hy H0).
  - unfold rename. simpl. destruct (classicT (x0 = x)) as [Heq|Hneq]; simpl.
    + subst x0. eapply dsub_var_trans.
      * apply (binds_rename_env_same Hy H).
      * apply IHdsub; exact Hy.
    + eapply dsub_var_trans.
      * apply (binds_rename_env_diff Hneq Hy H).
      * apply IHdsub; exact Hy.
  - unfold rename. simpl. eapply dsub_top.
    + apply (ok_rename_env Hxy Hy H).
    + apply lc_rename. assumption.
  - (* lam *)
    unfold rename. simpl. set (Lf := union (union L (singleton x)) (singleton y)).
    eapply dsub_lam with (L := Lf).
    + apply (ok_rename_env Hxy Hy H).
    + intros x0 Hx.
      unfold Lf in Hx. apply notin_union_r in Hx as [HxLx Hx0ys].
      apply notin_union_r in HxLx as [HxL Hxx0].
      assert (Hx0x : x0 <> x) by (apply notin_singleton_r; exact Hxx0).
      assert (Hx0y : x0 <> y) by (apply notin_singleton_r; exact Hx0ys).
      assert (Hyx0 : y # (G & x0 ~ bind_sub [#e3#] [#A#])).
      { rewrite dom_push. apply notin_union_l.
        - apply notin_singleton_l. symmetry. exact Hx0y.
        - exact Hy. }
      pose proof (H1 x0 HxL Hyx0) as Hx'.
      rewrite rename_env_push in Hx'. unfold rename_binding in Hx'.
      assert (Hkey : (match classicT (x0 = x) with left _ => y | right _ => x0 end) = x0)
        by (destruct (classicT (x0 = x)) as [Heq|Hneq]; [congruence|reflexivity]).
      rewrite Hkey in Hx'.
      rewrite (@rename_open_var' x y x0 e1 Hx0x) in Hx'.
      rewrite (@rename_open_var' x y x0 e2 Hx0x) in Hx'.
      rewrite <- remove_anno_rename in Hx'. rewrite <- remove_anno_rename in Hx'.
      exact Hx'.
  - unfold rename. simpl. eapply dsub_app.
    + apply lc_rename. assumption.
    + apply IHdsub; exact Hy.
  - (* pi *)
    unfold rename. simpl. set (Lf := union (union L (singleton x)) (singleton y)).
    eapply dsub_pi with (L := Lf).
    + apply IHdsub; exact Hy.
    + intros x0 Hx.
      unfold Lf in Hx. apply notin_union_r in Hx as [HxLx Hx0ys].
      apply notin_union_r in HxLx as [HxL Hxx0].
      assert (Hx0x : x0 <> x) by (apply notin_singleton_r; exact Hxx0).
      assert (Hx0y : x0 <> y) by (apply notin_singleton_r; exact Hx0ys).
      assert (Hyx0 : y # (G & x0 ~ bind_sub [#e#] [#C#])).
      { rewrite dom_push. apply notin_union_l.
        - apply notin_singleton_l. symmetry. exact Hx0y.
        - exact Hy. }
      pose proof (H1 x0 HxL Hyx0) as Hx'.
      rewrite rename_env_push in Hx'. unfold rename_binding in Hx'.
      assert (Hkey : (match classicT (x0 = x) with left _ => y | right _ => x0 end) = x0)
        by (destruct (classicT (x0 = x)) as [Heq|Hneq]; [congruence|reflexivity]).
      rewrite Hkey in Hx'.
      rewrite (@rename_open_var' x y x0 B Hx0x) in Hx'.
      rewrite (@rename_open_var' x y x0 D Hx0x) in Hx'.
      rewrite <- remove_anno_rename in Hx'. rewrite <- remove_anno_rename in Hx'.
      exact Hx'.
  - unfold rename. simpl. eapply dsub_castup.
    + apply lc_rename. assumption.
    + apply IHdsub; exact Hy.
  - unfold rename. simpl. eapply dsub_castdn. apply IHdsub; exact Hy.
Qed.



Lemma subst_classic : forall v x (P:Prop) (t1 t2:trm),
  subst_trm v x (match classicT P with left _ => t1 | right _ => t2 end) =
  match classicT P with left _ => subst_trm v x t1 | right _ => subst_trm v x t2 end.
Proof. intros. destruct (classicT P); reflexivity. Qed.

Lemma rename_open : forall x y k v e,
  rename x y (open_trm_wrt_trm_rec k v e) =
  open_trm_wrt_trm_rec k (rename x y v) (rename x y e).
Proof.
  intros x y k v e. revert k v. induction e; intros k0 v0; simpl.
  - unfold rename. simpl. rewrite subst_classic.
    destruct (classicT (k0 = n)); simpl; reflexivity.
  - unfold rename. simpl. destruct (classicT (x5 = x)); simpl; reflexivity.
  - reflexivity. - reflexivity.
  - unfold rename. simpl. f_equal; [exact (IHe1 k0 v0)|exact (IHe2 k0 v0)].
  - unfold rename. simpl.
    f_equal; [exact (IHe1 k0 v0)|exact (IHe2 k0 v0)|exact (IHe3 (S k0) v0)].
  - unfold rename. simpl.
    f_equal; [exact (IHe1 k0 v0)|exact (IHe2 k0 v0)|exact (IHe3 (S k0) v0)].
  - unfold rename. simpl. f_equal; [exact (IHe1 k0 v0)|exact (IHe2 k0 v0)].
  - unfold rename. simpl. f_equal; exact (IHe k0 v0).
  - unfold rename. simpl. f_equal; [exact (IHe1 k0 v0)|exact (IHe2 k0 v0)].
Qed.

Lemma rename_open' : forall x y v e,
  rename x y (open_trm_wrt_trm e v) = open_trm_wrt_trm (rename x y e) (rename x y v).
Proof. intros. unfold open_trm_wrt_trm. apply rename_open. Qed.

Lemma lc_rename_inv : forall e x y, lc_trm (rename x y e) -> lc_trm e.
Proof. intros. apply lc_rec_0_lc_trm. apply (proj1 (@lc_rec_rename 0 x y e)). apply lc_trm_lc_rec. assumption. Qed.


Lemma reduct_rename : forall a b x y, reduct a b -> reduct (rename x y a) (rename x y b).
Proof.
  intros a b x y H. induction H.
  - simpl. rewrite rename_open'. eapply reduct_beta.
    + change (lc_trm (rename x y e3)). apply lc_rename. assumption.
    + change (lc_trm (rename x y A)). apply lc_rename. assumption.
    + change (lc_trm (rename x y (trm_abs e3 A e1))). apply lc_rename. assumption.
    + change (lc_trm (rename x y e2)). apply lc_rename. assumption.
  - simpl. eapply reduct_app.
    + change (lc_trm (rename x y e2)). apply lc_rename. assumption.
    + exact IHreduct.
  - simpl. apply reduct_castdn. exact IHreduct.
  - simpl. eapply reduct_castelim.
    + change (lc_trm (rename x y A)). apply lc_rename. assumption.
    + change (lc_trm (rename x y e)). apply lc_rename. assumption.
Qed.

Scheme dtyping_mut := Induction for dtyping Sort Prop
  with dwf_mut := Induction for dwf Sort Prop.

Scheme sub_wf_mut := Induction for sub Sort Prop
  with wf_sub_mut := Induction for wf Sort Prop.

Lemma sub_Et_uncond : forall G e1 e2 A, sub G e1 e2 A -> Et e1 /\ Et e2 /\ Et A.
Proof.
  intros G e1 e2 A H.
  exact (sub_E H (wf_Eenv (sub_wf H))).
Qed.

Lemma wf_binds_erased : forall G x b, wf G -> binds x b G -> rem_anno_env b = b.
Proof. intros G x b Hwf Hb. exact (wf_Eenv Hwf Hb). Qed.

Lemma remove_anno_rename_subst : forall x y e,
  [# subst_trm (trm_var_f y) x e #] = subst_trm (trm_var_f y) x [# e #].
Proof. intros. rewrite remove_anno_subst. simpl. reflexivity. Qed.

Lemma subst_open_any : forall x y v e,
  subst_trm (trm_var_f y) x (open_trm_wrt_trm e v) =
  open_trm_wrt_trm (subst_trm (trm_var_f y) x e) (subst_trm (trm_var_f y) x v).
Proof.
  intros. change (rename x y (open_trm_wrt_trm e v) = open_trm_wrt_trm (rename x y e) (rename x y v)).
  apply rename_open'.
Qed.

Lemma dtyping_rename : forall d G e A, dtyping d G e A -> forall x y, x <> y -> y # G -> dtyping d (rename_env x y G) (rename x y e) (rename x y A).
Proof.
  intros d G e A H.
  apply (dtyping_mut
    (fun d G e A (H:dtyping d G e A) => forall x y, x <> y -> y # G -> dtyping d (rename_env x y G) (rename x y e) (rename x y A))
    (fun G (H:dwf G) => forall x y, x <> y -> y # G -> dwf (rename_env x y G))).
  - (* star *) intros G0 Hd IH x y Hxy Hy. unfold rename. simpl.
    apply dtyping_star. apply IH; assumption.
  - (* var *) intros e0 G0 xx A0 Hd IH b x y Hxy Hy. unfold rename. simpl.
    destruct (classicT (xx = x)) as [Heq|Hneq]; simpl.
    + subst xx. eapply dtyping_var.
      * apply IH; assumption.
      * apply (binds_rename_env_same Hy b).
    + eapply dtyping_var.
      * apply IH; assumption.
      * apply (binds_rename_env_diff Hneq Hy b).
  - (* top *) intros G0 A0 d1 IH1 x y Hxy Hy. unfold rename. simpl.
    apply dtyping_top. apply IH1; assumption.
  - (* lam *) intros L G0 e1 e2 A0 B d1 IH1 d2 IH2 d3 IH3 x y Hxy Hy.
    unfold rename. simpl.
    set (Lf := union (union L (singleton x)) (singleton y)).
    rewrite <- remove_anno_rename_subst. rewrite <- remove_anno_rename_subst.
    eapply dtyping_lam with (L := Lf).
    + rewrite remove_anno_rename_subst. apply IH1; assumption.
    + apply IH2; assumption.
    + intros x0 Hx.
      unfold Lf in Hx. apply notin_union_r in Hx as [HxLx Hx0y].
      apply notin_union_r in HxLx as [HxL Hxx0].
      assert (Hx0x : x0 <> x) by (apply notin_singleton_r; exact Hxx0).
      assert (Hx0y' : x0 <> y) by (apply notin_singleton_r; exact Hx0y).
      assert (Hyx0 : y # (G0 & x0 ~ bind_sub [#e1#] [#A0#])).
      { rewrite dom_push. apply notin_union_l.
        - apply notin_singleton_l. symmetry. exact Hx0y'.
        - exact Hy. }
      pose proof (IH3 x0 HxL x y Hxy Hyx0) as Hx'.
      rewrite rename_env_push in Hx'. unfold rename_binding in Hx'.
      assert (Hkey : (match classicT (x0 = x) with left _ => y | right _ => x0 end) = x0)
        by (destruct (classicT (x0 = x)) as [Heq|Hneq]; [congruence|reflexivity]).
      rewrite Hkey in Hx'.
      rewrite (@rename_open_var' x y x0 e2 Hx0x) in Hx'.
      rewrite (@rename_open_var' x y x0 B Hx0x) in Hx'.
      rewrite <- remove_anno_rename in Hx'. rewrite <- remove_anno_rename in Hx'.
      exact Hx'.
  - (* app *) intros e3 G0 e0 A0 B C d1 IH1 dsub0 d2 IH2 x y Hxy Hy.
    unfold rename. simpl. rewrite subst_open_any. rewrite <- remove_anno_rename_subst.
    eapply dtyping_app with (B := rename x y B) (C := rename x y C) (e3 := rename x y e3).
    + apply IH1; assumption.
    + pose proof (@dsub_rename G0 [#A0#] e3 x y Hxy Hy dsub0) as Hd.
      unfold rename in Hd. rewrite <- remove_anno_rename_subst in Hd. exact Hd.
    + apply IH2; assumption.
  - (* pi *) intros L G0 e0 A0 B d1 IH1 d2 IH2 d3 IH3 x y Hxy Hy.
    unfold rename. simpl.
    set (Lf := union (union L (singleton x)) (singleton y)).
    eapply dtyping_pi with (L := Lf).
    + rewrite remove_anno_rename_subst. apply IH1; assumption.
    + apply IH2; assumption.
    + intros x0 Hx.
      unfold Lf in Hx. apply notin_union_r in Hx as [HxLx Hx0y].
      apply notin_union_r in HxLx as [HxL Hxx0].
      assert (Hx0x : x0 <> x) by (apply notin_singleton_r; exact Hxx0).
      assert (Hx0y' : x0 <> y) by (apply notin_singleton_r; exact Hx0y).
      assert (Hyx0 : y # (G0 & x0 ~ bind_sub [#e0#] [#A0#])).
      { rewrite dom_push. apply notin_union_l.
        - apply notin_singleton_l. symmetry. exact Hx0y'.
        - exact Hy. }
      pose proof (IH3 x0 HxL x y Hxy Hyx0) as Hx'.
      rewrite rename_env_push in Hx'. unfold rename_binding in Hx'.
      assert (Hkey : (match classicT (x0 = x) with left _ => y | right _ => x0 end) = x0)
        by (destruct (classicT (x0 = x)) as [Heq|Hneq]; [congruence|reflexivity]).
      rewrite Hkey in Hx'.
      rewrite (@rename_open_var' x y x0 B Hx0x) in Hx'.
      rewrite <- remove_anno_rename in Hx'. rewrite <- remove_anno_rename in Hx'.
      exact Hx'.
  - (* castup *) intros G0 e0 A0 B d1 IH1 d2 IH2 r x y Hxy Hy.
    unfold rename. simpl. rewrite <- remove_anno_rename_subst.
    eapply dtyping_castup with (A := rename x y A0) (B := rename x y B).
    + apply IH1; assumption.
    + apply IH2; assumption.
    + pose proof (@reduct_rename [#B#] [#A0#] x y r) as Hr.
      unfold rename in Hr. rewrite <- remove_anno_rename_subst in Hr. rewrite <- remove_anno_rename_subst in Hr. exact Hr.
  - (* castdn *) intros G0 e0 A0 B d1 IH1 d2 IH2 r x y Hxy Hy.
    unfold rename. simpl.
    eapply dtyping_castdn with (A := rename x y A0) (B := rename x y B).
    + apply IH1; assumption.
    + apply IH2; assumption.
    + pose proof (@reduct_rename [#A0#] [#B#] x y r) as Hr.
      unfold rename in Hr. rewrite <- remove_anno_rename_subst in Hr. rewrite <- remove_anno_rename_subst in Hr. exact Hr.
  - (* anno *) intros G0 e0 A0 d1 IH1 d2 IH2 x y Hxy Hy.
    unfold rename. simpl. rewrite <- remove_anno_rename_subst.
    eapply dtyping_anno with (A := rename x y A0).
    + apply IH1; assumption.
    + apply IH2; assumption.
  - (* sub *) intros A0 G0 e0 B d1 IH1 dsub0 d2 IH2 x y Hxy Hy.
    unfold rename. simpl.
    eapply dtyping_sub with (A := rename x y A0) (B := rename x y B).
    + apply IH1; assumption.
    + pose proof (@dsub_rename G0 A0 [#B#] x y Hxy Hy dsub0) as Hd.
      unfold rename in Hd. rewrite <- remove_anno_rename_subst in Hd. exact Hd.
    + apply IH2; assumption.
  - (* chk *) intros G0 e0 A0 d1 IH1 x y Hxy Hy. unfold rename. simpl.
    apply dtyping_chk. apply IH1; assumption.
  - (* dwf_nil *) intros x y Hxy Hy. rewrite (empty_def binding). simpl.
    rewrite <- (empty_def binding). apply dwf_nil.
  - (* dwf_cons *) intros G0 k e0 A0 Hk d1 IH1 d2 IH2 x y Hxy Hy.
    rewrite dom_push in Hy. apply notin_union_r in Hy as [Hyk HyG].
    rewrite rename_env_push. unfold rename_binding.
    rewrite <- remove_anno_rename. rewrite <- remove_anno_rename.
    eapply dwf_cons.
    + eapply rename_key_fresh; [exact Hxy| |exact Hk|exact HyG].
      apply notin_singleton_r in Hyk. symmetry. exact Hyk.
    + unfold rename. rewrite remove_anno_rename_subst. apply IH1; assumption.
    + unfold rename. apply IH2; assumption.
  - exact H.
Qed.

Lemma dwf_rename : forall G, dwf G -> forall x y, x <> y -> y # G -> dwf (rename_env x y G).
Proof.
  intros G H x y Hxy Hy. induction H as [| G0 k e A Hk d1 d2].
  - rewrite (empty_def binding). simpl. rewrite <- (empty_def binding). apply dwf_nil.
  - rewrite dom_push in Hy. apply notin_union_r in Hy as [Hyk HyG].
    rewrite rename_env_push. unfold rename_binding.
    rewrite <- remove_anno_rename. rewrite <- remove_anno_rename.
    eapply dwf_cons.
    + eapply rename_key_fresh; [exact Hxy| |exact Hk|exact HyG].
      apply notin_singleton_r in Hyk. symmetry. exact Hyk.
    + unfold rename. rewrite remove_anno_rename_subst.
      apply (dtyping_rename d1); assumption.
    + unfold rename. apply (dtyping_rename d2); assumption.
Qed.


(* ================= environment extension / weakening ================= *)

Lemma extends_push_both : forall G G' x b,
  extends G G' -> x # G' -> extends (G & x ~ b) (G' & x ~ b).
Proof.
  intros G G' x b Hext Hx y v Hyb.
  apply binds_push_inv in Hyb as [[Heq Hyb]|[Hneq Hyb]].
  - inversion Heq. subst y v. apply binds_tail.
  - assert (HyG : binds y v G) by assumption.
    assert (HyG' : binds y v G') by (apply Hext; exact HyG).
    apply binds_push_neq; [exact HyG'|].
    intro Heq. subst y. apply Hx.
    eapply get_some_inv. apply binds_get. exact HyG'.
Qed.

Lemma dsub_weaken_ext : forall G e1 e2,
  dsub G e1 e2 -> forall G', ok G' -> extends G G' -> dsub G' e1 e2.
Proof.
  intros G e1 e2 H. induction H; intros G' Hok Hext.
  - apply dsub_star. exact Hok.
  - eapply dsub_var_refl. + exact Hok. + apply Hext; exact H0.
  - eapply dsub_var_trans. + apply Hext; exact H. + apply IHdsub; assumption.
  - eapply dsub_top. + exact Hok. + exact H0.
  - (* lam *)
    eapply dsub_lam with (L := L \u dom G').
    + exact Hok.
    + intros x Hx.
      apply notin_union_r in Hx as [HxL HxG'].
      assert (Hokx : ok (G' & x ~ bind_sub [#e3#] [#A#])) by (apply ok_push; assumption).
      assert (Hextx : extends (G & x ~ bind_sub [#e3#] [#A#]) (G' & x ~ bind_sub [#e3#] [#A#]))
        by (apply extends_push_both; assumption).
      apply (H1 x HxL (G' & x ~ bind_sub [#e3#] [#A#]) Hokx Hextx).
  - eapply dsub_app. + exact H. + apply IHdsub; assumption.
  - (* pi *)
    eapply dsub_pi with (L := L \u dom G').
    + apply IHdsub; assumption.
    + intros x Hx.
      apply notin_union_r in Hx as [HxL HxG'].
      assert (Hokx : ok (G' & x ~ bind_sub [#e#] [#C#])) by (apply ok_push; assumption).
      assert (Hextx : extends (G & x ~ bind_sub [#e#] [#C#]) (G' & x ~ bind_sub [#e#] [#C#]))
        by (apply extends_push_both; assumption).
      apply (H1 x HxL (G' & x ~ bind_sub [#e#] [#C#]) Hokx Hextx).
  - eapply dsub_castup. + exact H. + apply IHdsub; assumption.
  - eapply dsub_castdn. apply IHdsub; assumption.
Qed.


Definition binds_equiv (G G':env) : Prop := forall x b, binds x b G <-> binds x b G'.

Lemma binds_add_fresh : forall G y v z c,
  binds y v G -> z # G -> binds y v (G & z ~ c).
Proof.
  intros. apply binds_push_neq; [assumption|].
  intro Heq. subst y. apply H0.
  eapply get_some_inv. apply binds_get. exact H.
Qed.

Lemma binds_equiv_push : forall G G' y d,
  binds_equiv G G' -> y # G -> y # G' -> binds_equiv (G & y ~ d) (G' & y ~ d).
Proof.
  intros G G' y d Hbe Hy Hy' u v. split; intro Hu.
  - apply binds_push_inv in Hu as [[Heq Hu]|[Hneq Hu]].
    + inversion Heq. subst u v. apply binds_tail.
    + apply binds_push_neq; [|exact Hneq].
      apply (Hbe u v). exact Hu.
  - apply binds_push_inv in Hu as [[Heq Hu]|[Hneq Hu]].
    + inversion Heq. subst u v. apply binds_tail.
    + apply binds_push_neq; [|exact Hneq].
      apply (Hbe u v). exact Hu.
Qed.

Lemma get_binds : forall y b G, get y G = Some b -> binds y b G.
Proof. intros. unfold binds. exact H. Qed.

Lemma binds_equiv_fresh : forall G G' y,
  binds_equiv G G' -> y # G -> y # G'.
Proof.
  intros G G' y Hbe Hy Hb.
  apply get_some in Hb as [b Hb]. apply Hy.
  eapply get_some_inv. apply binds_get.
  exact (proj2 (Hbe y b) (get_binds Hb)).
Qed.

Lemma binds_equiv_fresh_inv : forall G G' y,
  binds_equiv G G' -> y # G' -> y # G.
Proof.
  intros G G' y Hbe Hy Hb.
  apply get_some in Hb as [b Hb]. apply Hy.
  eapply get_some_inv. apply binds_get.
  exact (proj1 (Hbe y b) (get_binds Hb)).
Qed.


Lemma dsub_env_irrel : forall G e1 e2,
  dsub G e1 e2 -> forall G', binds_equiv G G' -> ok G' -> dsub G' e1 e2.
Proof.
  intros G e1 e2 H. induction H; intros G' Hbe Hok.
  - apply dsub_star. exact Hok.
  - eapply dsub_var_refl. + exact Hok. + apply (Hbe x (bind_sub e A)). exact H0.
  - eapply dsub_var_trans.
    + apply (Hbe x (bind_sub e1 A)). exact H.
    + apply IHdsub; assumption.
  - eapply dsub_top. + exact Hok. + exact H0.
  - (* lam *)
    eapply dsub_lam with (L := L \u dom G \u dom G').
    + exact Hok.
    + intros x Hx.
      apply notin_union_r in Hx as [HxL HxGG'].
      apply notin_union_r in HxGG' as [HxG HxG'].
      assert (Hbe_x : binds_equiv (G & x ~ bind_sub [#e3#] [#A#])
                                  (G' & x ~ bind_sub [#e3#] [#A#]))
        by (apply binds_equiv_push; assumption).
      assert (Hokx : ok (G' & x ~ bind_sub [#e3#] [#A#])) by (apply ok_push; assumption).
      apply (H1 x HxL (G' & x ~ bind_sub [#e3#] [#A#]) Hbe_x Hokx).
  - eapply dsub_app. + exact H. + apply IHdsub; assumption.
  - (* pi *)
    eapply dsub_pi with (L := L \u dom G \u dom G').
    + apply IHdsub; assumption.
    + intros x Hx.
      apply notin_union_r in Hx as [HxL HxGG'].
      apply notin_union_r in HxGG' as [HxG HxG'].
      assert (Hbe_x : binds_equiv (G & x ~ bind_sub [#e#] [#C#])
                                  (G' & x ~ bind_sub [#e#] [#C#]))
        by (apply binds_equiv_push; assumption).
      assert (Hokx : ok (G' & x ~ bind_sub [#e#] [#C#])) by (apply ok_push; assumption).
      apply (H1 x HxL (G' & x ~ bind_sub [#e#] [#C#]) Hbe_x Hokx).
  - eapply dsub_castup. + exact H. + apply IHdsub; assumption.
  - eapply dsub_castdn. apply IHdsub; assumption.
Qed.


Lemma dtyping_env_irrel : forall d G e A,
  dtyping d G e A ->
  forall G', binds_equiv G G' -> ok G' -> dwf G' -> dtyping d G' e A.
Proof.
  intros d G e A H.
  apply (dtyping_mut
    (fun d G e A (H:dtyping d G e A) =>
       forall G', binds_equiv G G' -> ok G' -> dwf G' -> dtyping d G' e A)
    (fun G (H:dwf G) => True)).
  - (* star *) intros G0 Hd IH G' Hbe Hok Hdwf. apply dtyping_star. exact Hdwf.
  - (* var *) intros e0 G0 xx A0 Hd IH b G' Hbe Hok Hdwf. eapply dtyping_var.
    + exact Hdwf.
    + apply (Hbe xx (bind_sub e0 A0)). exact b.
  - (* top *) intros G0 A0 d1 IH1 G' Hbe Hok Hdwf. apply dtyping_top. apply IH1; assumption.
  - (* lam *) intros L G0 e1 e2 A0 B d1 IH1 d2 IH2 d3 IH3 G' Hbe Hok Hdwf.
    set (Lf := L \u dom G0 \u dom G').
    eapply dtyping_lam with (L := Lf).
    + apply IH1; assumption.
    + apply IH2; assumption.
    + intros x Hx.
      apply notin_union_r in Hx as [HxL HxGG'].
      apply notin_union_r in HxGG' as [HxG HxG'].
      assert (Hbe_x : binds_equiv (G0 & x ~ bind_sub [#e1#] [#A0#])
                                  (G' & x ~ bind_sub [#e1#] [#A0#]))
        by (apply binds_equiv_push; assumption).
      assert (Hdwfx : dwf (G' & x ~ bind_sub [#e1#] [#A0#])).
      { eapply dwf_cons.
        - exact HxG'.
        - apply IH1; assumption.
        - apply IH2; assumption. }
      assert (Hokx : ok (G' & x ~ bind_sub [#e1#] [#A0#])) by (apply ok_push; assumption).
      apply (IH3 x HxL (G' & x ~ bind_sub [#e1#] [#A0#]) Hbe_x Hokx Hdwfx).
  - (* app *) intros e3 G0 e0 A0 B C d1 IH1 ds d2 IH2 G' Hbe Hok Hdwf.
    eapply dtyping_app.
    + apply IH1; assumption.
    + apply (dsub_env_irrel ds Hbe Hok).
    + apply IH2; assumption.
  - (* pi *) intros L G0 e0 A0 B d1 IH1 d2 IH2 d3 IH3 G' Hbe Hok Hdwf.
    set (Lf := L \u dom G0 \u dom G').
    eapply dtyping_pi with (L := Lf).
    + apply IH1; assumption.
    + apply IH2; assumption.
    + intros x Hx.
      apply notin_union_r in Hx as [HxL HxGG'].
      apply notin_union_r in HxGG' as [HxG HxG'].
      assert (Hbe_x : binds_equiv (G0 & x ~ bind_sub [#e0#] [#A0#])
                                  (G' & x ~ bind_sub [#e0#] [#A0#]))
        by (apply binds_equiv_push; assumption).
      assert (Hdwfx : dwf (G' & x ~ bind_sub [#e0#] [#A0#])).
      { eapply dwf_cons.
        - exact HxG'.
        - apply IH1; assumption.
        - apply IH2; assumption. }
      assert (Hokx : ok (G' & x ~ bind_sub [#e0#] [#A0#])) by (apply ok_push; assumption).
      apply (IH3 x HxL (G' & x ~ bind_sub [#e0#] [#A0#]) Hbe_x Hokx Hdwfx).
  - (* castup *) intros G0 e0 A0 B d1 IH1 d2 IH2 r G' Hbe Hok Hdwf.
    eapply dtyping_castup. + apply IH1; assumption. + apply IH2; assumption. + exact r.
  - (* castdn *) intros G0 e0 A0 B d1 IH1 d2 IH2 r G' Hbe Hok Hdwf.
    eapply dtyping_castdn. + apply IH1; assumption. + apply IH2; assumption. + exact r.
  - (* anno *) intros G0 e0 A0 d1 IH1 d2 IH2 G' Hbe Hok Hdwf.
    eapply dtyping_anno. + apply IH1; assumption. + apply IH2; assumption.
  - (* sub *) intros A0 G0 e0 B d1 IH1 ds d2 IH2 G' Hbe Hok Hdwf.
    eapply dtyping_sub.
    + apply IH1; assumption.
    + apply (dsub_env_irrel ds Hbe Hok).
    + apply IH2; assumption.
  - (* chk *) intros G0 e0 A0 d1 IH1 G' Hbe Hok Hdwf. apply dtyping_chk. apply IH1; assumption.
  - (* dwf_nil *) exact I.
  - (* dwf_cons *) intros; exact I.
  - exact H.
Qed.


Lemma binds_equiv_swap : forall G x b z c,
  x # G -> z # G -> x <> z ->
  binds_equiv ((G & x ~ b) & z ~ c) ((G & z ~ c) & x ~ b).
Proof.
  intros G x b z c HxG HzG Hxz u v. split; intro H.
  - apply binds_push_inv in H as [[Heq H]|[Hneq H]].
    + inversion Heq. subst u v.
      exact (@binds_push_neq binding z x c b (G & z ~ c)
               (@binds_tail binding z c G) (fun Heq => Hxz (eq_sym Heq))).
    + apply binds_push_inv in H as [[Heq H]|[Hneq2 H]].
      * inversion Heq. subst u v. apply binds_tail.
      * assert (Huz : u <> z)
          by (intro Heq; subst u; apply HzG; eapply get_some_inv; apply binds_get; exact H).
        exact (@binds_push_neq binding u x v b (G & z ~ c)
                (@binds_push_neq binding u z v c G H Huz) Hneq2).
  - apply binds_push_inv in H as [[Heq H]|[Hneq H]].
    + inversion Heq. subst u v.
      exact (@binds_push_neq binding x z b c (G & x ~ b)
               (@binds_tail binding x b G) (fun Heq => Hxz Heq)).
    + apply binds_push_inv in H as [[Heq H]|[Hneq2 H]].
      * inversion Heq. subst u v. apply binds_tail.
      * assert (Huz : u <> z)
          by (intro Heq; subst u; apply HzG; eapply get_some_inv; apply binds_get; exact H).
        exact (@binds_push_neq binding u z v c (G & x ~ b)
                (@binds_push_neq binding u x v b G H Hneq) Huz).
Qed.


Lemma dsub_weaken_add : forall G e1 e2,
  dsub G e1 e2 -> forall z c, z # G -> ok (G & z ~ c) -> dsub (G & z ~ c) e1 e2.
Proof.
  intros G e1 e2 H. induction H; intros z c Hz Hok.
  - apply dsub_star. exact Hok.
  - eapply dsub_var_refl. + exact Hok. + exact (@binds_add_fresh G x (bind_sub e A) z c H0 Hz).
  - eapply dsub_var_trans.
    + exact (@binds_add_fresh G x (bind_sub e1 A) z c H Hz).
    + apply IHdsub; assumption.
  - eapply dsub_top. + exact Hok. + exact H0.
  - (* lam *)
    assert (HokG : ok G) by (exact (proj1 (ok_push_inv Hok))).
    eapply dsub_lam with (L := L \u dom G \u dom (G & z ~ c)).
    + exact Hok.
    + intros x Hx.
      apply notin_union_r in Hx as [HxL HxGG].
      apply notin_union_r in HxGG as [HxG HxGz].
      assert (Hxz : x <> z) by (intro Heq; subst x; apply HxGz; apply in_dom_push_self).
      assert (Hzx : z # (G & x ~ bind_sub [#e3#] [#A#])).
      { rewrite dom_push. apply notin_union_l; [apply notin_singleton_l; symmetry; exact Hxz|exact Hz]. }
      assert (HokxG : ok (G & x ~ bind_sub [#e3#] [#A#])) by
        exact (@ok_push binding G x (bind_sub [#e3#] [#A#]) HokG HxG).
      assert (Hokx : ok ((G & x ~ bind_sub [#e3#] [#A#]) & z ~ c)) by
        exact (@ok_push binding (G & x ~ bind_sub [#e3#] [#A#]) z c HokxG Hzx).
      pose proof (H1 x HxL z c Hzx Hokx) as Hd.
      assert (Hok_xz : ok ((G & z ~ c) & x ~ bind_sub [#e3#] [#A#])) by
        exact (@ok_push binding (G & z ~ c) x (bind_sub [#e3#] [#A#]) Hok HxGz).
      exact (dsub_env_irrel Hd (@binds_equiv_swap G x (bind_sub [#e3#] [#A#]) z c HxG Hz Hxz) Hok_xz).
  - eapply dsub_app. + exact H. + apply IHdsub; assumption.
  - (* pi *)
    assert (HokG : ok G) by (exact (proj1 (ok_push_inv Hok))).
    eapply dsub_pi with (L := L \u dom G \u dom (G & z ~ c)).
    + apply IHdsub; assumption.
    + intros x Hx.
      apply notin_union_r in Hx as [HxL HxGG].
      apply notin_union_r in HxGG as [HxG HxGz].
      assert (Hxz : x <> z) by (intro Heq; subst x; apply HxGz; apply in_dom_push_self).
      assert (Hzx : z # (G & x ~ bind_sub [#e#] [#C#])).
      { rewrite dom_push. apply notin_union_l; [apply notin_singleton_l; symmetry; exact Hxz|exact Hz]. }
      assert (HokxG : ok (G & x ~ bind_sub [#e#] [#C#])) by
        exact (@ok_push binding G x (bind_sub [#e#] [#C#]) HokG HxG).
      assert (Hokx : ok ((G & x ~ bind_sub [#e#] [#C#]) & z ~ c)) by
        exact (@ok_push binding (G & x ~ bind_sub [#e#] [#C#]) z c HokxG Hzx).
      pose proof (H1 x HxL z c Hzx Hokx) as Hd.
      assert (Hok_xz : ok ((G & z ~ c) & x ~ bind_sub [#e#] [#C#])) by
        exact (@ok_push binding (G & z ~ c) x (bind_sub [#e#] [#C#]) Hok HxGz).
      exact (dsub_env_irrel Hd (@binds_equiv_swap G x (bind_sub [#e#] [#C#]) z c HxG Hz Hxz) Hok_xz).
  - eapply dsub_castup. + exact H. + apply IHdsub; assumption.
  - eapply dsub_castdn. apply IHdsub; assumption.
Qed.


Lemma dtyping_weaken_ext : forall d G e A,
  dtyping d G e A ->
  forall G', extends G G' -> dwf G' -> dtyping d G' e A.
Proof.
  intros d G e A H.
  apply (dtyping_mut
    (fun d G e A (H:dtyping d G e A) =>
       forall G', extends G G' -> dwf G' -> dtyping d G' e A)
    (fun G (H:dwf G) => True)).
  - (* star *) intros G0 Hd IH G' Hext Hdwf. apply dtyping_star. exact Hdwf.
  - (* var *) intros e0 G0 xx A0 Hd IH b G' Hext Hdwf. eapply dtyping_var.
    + exact Hdwf.
    + apply (Hext xx (bind_sub e0 A0)). exact b.
  - (* top *) intros G0 A0 d1 IH1 G' Hext Hdwf. apply dtyping_top. apply IH1; assumption.
  - (* lam *) intros L G0 e1 e2 A0 B d1 IH1 d2 IH2 d3 IH3 G' Hext Hdwf.
    set (Lf := L \u dom G0 \u dom G').
    eapply dtyping_lam with (L := Lf).
    + apply IH1; assumption.
    + apply IH2; assumption.
    + intros x Hx.
      apply notin_union_r in Hx as [HxL HxGG'].
      apply notin_union_r in HxGG' as [HxG HxG'].
      assert (Hdwfx : dwf (G' & x ~ bind_sub [#e1#] [#A0#])).
      { eapply dwf_cons.
        - exact HxG'.
        - apply IH1; assumption.
        - apply IH2; assumption. }
      apply (IH3 x HxL (G' & x ~ bind_sub [#e1#] [#A0#])
               (extends_push_both Hext HxG') Hdwfx).
  - (* app *) intros e3 G0 e0 A0 B C d1 IH1 ds d2 IH2 G' Hext Hdwf.
    eapply dtyping_app.
    + apply IH1; assumption.
    + eapply dsub_weaken_ext; [exact ds|apply dwf_ok; exact Hdwf|exact Hext].
    + apply IH2; assumption.
  - (* pi *) intros L G0 e0 A0 B d1 IH1 d2 IH2 d3 IH3 G' Hext Hdwf.
    set (Lf := L \u dom G0 \u dom G').
    eapply dtyping_pi with (L := Lf).
    + apply IH1; assumption.
    + apply IH2; assumption.
    + intros x Hx.
      apply notin_union_r in Hx as [HxL HxGG'].
      apply notin_union_r in HxGG' as [HxG HxG'].
      assert (Hdwfx : dwf (G' & x ~ bind_sub [#e0#] [#A0#])).
      { eapply dwf_cons.
        - exact HxG'.
        - apply IH1; assumption.
        - apply IH2; assumption. }
      apply (IH3 x HxL (G' & x ~ bind_sub [#e0#] [#A0#])
               (extends_push_both Hext HxG') Hdwfx).
  - (* castup *) intros G0 e0 A0 B d1 IH1 d2 IH2 r G' Hext Hdwf.
    eapply dtyping_castup. + apply IH1; assumption. + apply IH2; assumption. + exact r.
  - (* castdn *) intros G0 e0 A0 B d1 IH1 d2 IH2 r G' Hext Hdwf.
    eapply dtyping_castdn. + apply IH1; assumption. + apply IH2; assumption. + exact r.
  - (* anno *) intros G0 e0 A0 d1 IH1 d2 IH2 G' Hext Hdwf.
    eapply dtyping_anno. + apply IH1; assumption. + apply IH2; assumption.
  - (* sub *) intros A0 G0 e0 B d1 IH1 ds d2 IH2 G' Hext Hdwf.
    eapply dtyping_sub.
    + apply IH1; assumption.
    + eapply dsub_weaken_ext; [exact ds|apply dwf_ok; exact Hdwf|exact Hext].
    + apply IH2; assumption.
  - (* chk *) intros G0 e0 A0 d1 IH1 G' Hext Hdwf. apply dtyping_chk. apply IH1; assumption.
  - (* dwf_nil *) exact I.
  - (* dwf_cons *) intros; exact I.
  - exact H.
Qed.


Lemma dwf_binds_star_wit : forall G x e A,
  dwf G -> binds x (bind_sub e A) G ->
  exists X, [# X #] = A /\ dtyping chk G X trm_star.
Proof.
  intros G x e A Hdwf Hb. remember (LibList.length G) as n eqn:E. revert G E Hdwf Hb.
  induction n as [|n IH]; intros G E Hdwf Hb.
  - symmetry in E. apply LibList.length_zero_inv in E. subst G.
    rewrite <- (empty_def binding) in Hb. exfalso.
    exact (@binds_empty_inv binding x (bind_sub e A) Hb).
  - inversion Hdwf as [| G0 z e0 A0 Hz Hd1 Hd2].
    + exfalso. subst G. exact (@binds_empty_inv binding x (bind_sub e A) Hb).
    + subst G. rewrite length_push in E. injection E as E'.
      apply binds_push_inv in Hb as [[Heq Hb]|[Hneq Hb]].
      * inversion Heq. subst z. inversion Hb. simpl in *.
        exists A0. split; [reflexivity|].
        eapply dtyping_weaken_ext.
        -- exact Hd2.
        -- apply extends_push. exact Hz.
        -- eapply dwf_cons; [exact Hz|exact Hd1|exact Hd2].
      * assert (Hdwf0 : dwf G0) by exact (@dtyping_dwf chk G0 e0 [#A0#] Hd1).
        destruct (IH G0 E' Hdwf0 Hb) as [X [HeqX HX]].
        exists X. split; [exact HeqX|].
        eapply dtyping_weaken_ext.
        -- exact HX.
        -- apply extends_push. exact Hz.
        -- eapply dwf_cons; [exact Hz|exact Hd1|exact Hd2].
Qed.


(* ================= inversion lemmas for dsub ================= *)

Lemma dsub_lhs_star_gen : forall G e1 e2, dsub G e1 e2 ->
  e1 = trm_star -> e2 = trm_star \/ e2 = trm_top.
Proof.
  intros G e1 e2 H. induction H; intros Heq; try discriminate Heq.
  - left. reflexivity.
  - right. reflexivity.
Qed.

Lemma dsub_lhs_star : forall G e, dsub G trm_star e -> e = trm_star \/ e = trm_top.
Proof. intros G e H. exact (dsub_lhs_star_gen H eq_refl). Qed.

Lemma dsub_lhs_var_gen : forall G x e1 e2, dsub G e1 e2 -> e1 = trm_var_f x ->
  e2 = trm_var_f x \/ e2 = trm_top \/
  exists e1' e2' A, binds x (bind_sub e1' A) G /\ dsub G e1' e2' /\ e2 = e2'.
Proof.
  intros G x e1 e2 H. induction H; intros Heq; try discriminate Heq.
  - left. inversion Heq. reflexivity.
  - right. right. inversion Heq; subst.
    exists e1, e2, A. split; [exact H|]. split; [exact H0|reflexivity].
  - right. left. reflexivity.
Qed.

Lemma dsub_lhs_var : forall G x e, dsub G (trm_var_f x) e ->
  e = trm_var_f x \/ e = trm_top \/
  exists e1' e2' A, binds x (bind_sub e1' A) G /\ dsub G e1' e2' /\ e = e2'.
Proof. intros G x e H. exact (dsub_lhs_var_gen H eq_refl). Qed.

Lemma dsub_lhs_abs_gen : forall G e1 e2, dsub G e1 e2 ->
  forall e3typ Atyp b, e1 = trm_abs e3typ Atyp b ->
  e2 = trm_top \/
  (ok G /\ exists L b', e2 = trm_abs e3typ Atyp b' /\
     (forall x, x \notin L -> dsub (G & x ~ bind_sub [#e3typ#] [#Atyp#]) (b ^ x) (b' ^ x))).
Proof.
  intros G e1 e2 H. induction H; intros e3typ Atyp b Heq; try discriminate Heq.
  - left. reflexivity.
  - right. split; [exact H|]. eexists. eexists. split.
    + inversion Heq. reflexivity.
    + inversion Heq. subst. exact H0.
Qed.

Lemma dsub_lhs_abs : forall G e3typ Atyp b e, dsub G (trm_abs e3typ Atyp b) e ->
  e = trm_top \/
  (ok G /\ exists L b', e = trm_abs e3typ Atyp b' /\
     (forall x, x \notin L -> dsub (G & x ~ bind_sub [#e3typ#] [#Atyp#]) (b ^ x) (b' ^ x))).
Proof. intros G e3typ Atyp b e H. exact (dsub_lhs_abs_gen H eq_refl). Qed.

Lemma dsub_lhs_app_gen : forall G e1 e2, dsub G e1 e2 ->
  forall aa AA, e1 = trm_app aa AA ->
  e2 = trm_top \/ (lc_trm AA /\ exists bb, e2 = trm_app bb AA /\ dsub G aa bb).
Proof.
  intros G e1 e2 H. induction H; intros aa AA Heq; try discriminate Heq.
  - left. reflexivity.
  - right. injection Heq as Ha HA. subst.
    split; [exact H|]. exists e2. split; [reflexivity|exact H0].
Qed.

Lemma dsub_lhs_app : forall G aa AA e, dsub G (trm_app aa AA) e ->
  e = trm_top \/ (lc_trm AA /\ exists bb, e = trm_app bb AA /\ dsub G aa bb).
Proof. intros G aa AA e H. exact (dsub_lhs_app_gen H eq_refl). Qed.

Lemma dsub_lhs_prod_gen : forall G e1 e2, dsub G e1 e2 ->
  forall ee AA BB, e1 = trm_prod ee AA BB ->
  e2 = trm_top \/
  exists L CC DD, e2 = trm_prod ee CC DD /\
    dsub G CC AA /\
    (forall x, x \notin L -> dsub (G & x ~ bind_sub [#ee#] [#CC#]) (BB ^ x) (DD ^ x)).
Proof.
  intros G e1 e2 H. induction H; intros ee AA BB Heq; try discriminate Heq.
  - left. reflexivity.
  - right. injection Heq as He HA HB. subst.
    eexists. eexists. eexists. split; [reflexivity|]. split; [exact H|exact H0].
Qed.

Lemma dsub_lhs_prod : forall G ee AA BB e, dsub G (trm_prod ee AA BB) e ->
  e = trm_top \/
  exists L CC DD, e = trm_prod ee CC DD /\
    dsub G CC AA /\
    (forall x, x \notin L -> dsub (G & x ~ bind_sub [#ee#] [#CC#]) (BB ^ x) (DD ^ x)).
Proof. intros G ee AA BB e H. exact (dsub_lhs_prod_gen H eq_refl). Qed.

Lemma dsub_lhs_castup_gen : forall G e1 e2, dsub G e1 e2 ->
  forall AA aa, e1 = trm_castup AA aa ->
  e2 = trm_top \/ (lc_trm AA /\ exists bb, e2 = trm_castup AA bb /\ dsub G aa bb).
Proof.
  intros G e1 e2 H. induction H; intros AA aa Heq; try discriminate Heq.
  - left. reflexivity.
  - right. injection Heq as HA Ha. subst.
    split; [exact H|]. exists e2. split; [reflexivity|exact H0].
Qed.

Lemma dsub_lhs_castup : forall G AA aa e, dsub G (trm_castup AA aa) e ->
  e = trm_top \/ (lc_trm AA /\ exists bb, e = trm_castup AA bb /\ dsub G aa bb).
Proof. intros G AA aa e H. exact (dsub_lhs_castup_gen H eq_refl). Qed.

Lemma dsub_lhs_castdn_gen : forall G e1 e2, dsub G e1 e2 ->
  forall aa, e1 = trm_castdn aa ->
  e2 = trm_top \/ exists bb, e2 = trm_castdn bb /\ dsub G aa bb.
Proof.
  intros G e1 e2 H. induction H; intros aa Heq; try discriminate Heq.
  - left. reflexivity.
  - right. injection Heq as Ha. subst.
    exists e2. split; [reflexivity|assumption].
Qed.

Lemma dsub_lhs_castdn : forall G aa e, dsub G (trm_castdn aa) e ->
  e = trm_top \/ exists bb, e = trm_castdn bb /\ dsub G aa bb.
Proof. intros G aa e H. exact (dsub_lhs_castdn_gen H eq_refl). Qed.


(* ================= inversion lemmas for dtyping ================= *)

Lemma dtyping_inf_star_inv : forall G A, dtyping inf G trm_star A -> A = trm_star.
Proof. intros G A H. inversion H. reflexivity. Qed.

Lemma dtyping_inf_var_inv : forall G x A, dtyping inf G (trm_var_f x) A ->
  exists e, dwf G /\ binds x (bind_sub e A) G.
Proof. intros G x A H. inversion H. eexists. split; eassumption. Qed.

Lemma dtyping_inf_abs_inv : forall G e1 A0 body T,
  dtyping inf G (trm_abs e1 A0 body) T ->
  exists L B, T = trm_prod [#e1#] [#A0#] B /\
    dtyping chk G e1 [#A0#] /\
    dtyping chk G A0 trm_star /\
    (forall x, x \notin L -> dtyping inf (G & x ~ bind_sub [#e1#] [#A0#]) (body ^ x) (B ^ x)).
Proof.
  intros G e1 A0 body T H. inversion H; subst.
  eexists. eexists. split; [reflexivity|].
  split; [exact H3|]. split; [exact H5|].
  intros x Hx. apply H7. exact Hx.
Qed.

Lemma dtyping_inf_app_inv : forall G a Aarg T,
  dtyping inf G (trm_app a Aarg) T ->
  exists e3 B C, T = C ^^ [#Aarg#] /\ dtyping chk G Aarg B /\
    dsub G [#Aarg#] e3 /\ dtyping inf G a (trm_prod e3 B C).
Proof.
  intros G a Aarg T H. inversion H; subst.
  eexists. eexists. eexists. split; [reflexivity|].
  split; [eassumption|]. split; eassumption.
Qed.

Lemma dtyping_inf_pi_inv : forall G ee AA BB T,
  dtyping inf G (trm_prod ee AA BB) T ->
  T = trm_star /\ dtyping chk G ee [#AA#] /\ dtyping chk G AA trm_star /\
  exists L, forall x, x \notin L -> dtyping chk (G & x ~ bind_sub [#ee#] [#AA#]) (BB ^ x) trm_star.
Proof.
  intros G ee AA BB T H. inversion H; subst.
  split; [reflexivity|]. split; [eassumption|]. split; [eassumption|].
  eexists. intros x Hx. apply H7. exact Hx.
Qed.

Lemma dtyping_inf_castup_inv : forall G BB ee T,
  dtyping inf G (trm_castup BB ee) T ->
  T = [#BB#] /\ dtyping chk G BB trm_star /\
  exists A, dtyping inf G ee A /\ reduct [#BB#] [#A#].
Proof.
  intros G BB ee T H. inversion H; subst.
  split; [reflexivity|]. split; [eassumption|].
  eexists. split; eassumption.
Qed.

Lemma dtyping_inf_anno_inv : forall G ee AA T,
  dtyping inf G (trm_anno ee AA) T ->
  T = [#AA#] /\ dtyping chk G ee AA /\ dtyping chk G AA trm_star.
Proof. intros G ee AA T H. inversion H; subst. split; [reflexivity|]. split; eassumption. Qed.

Lemma dtyping_inf_top_absurd : forall G A, dtyping inf G trm_top A -> False.
Proof. intros G A H. inversion H. Qed.

Lemma dtyping_chk_top_inv : forall G T, dtyping chk G trm_top T -> dtyping chk G T trm_star.
Proof.
  intros G T H. inversion H; subst.
  - assumption.
  - exfalso. match goal with Hinf : dtyping inf _ trm_top _ |- _ => exact (dtyping_inf_top_absurd Hinf) end.
  - exfalso. match goal with Hinf : dtyping inf _ trm_top _ |- _ => exact (dtyping_inf_top_absurd Hinf) end.
Qed.

Lemma dtyping_chk_castdn_inv : forall G ee T, dtyping chk G (trm_castdn ee) T ->
  exists A B, T = B /\ dtyping chk G B trm_star /\ dtyping inf G ee A /\ reduct [#A#] [#B#].
Proof.
  intros G ee T H. inversion H; subst.
  - eexists. eexists. split; [reflexivity|]. split; [eassumption|]. split; eassumption.
  - exfalso. match goal with Hinf : dtyping inf _ (trm_castdn _) _ |- _ => inversion Hinf end.
  - exfalso. match goal with Hinf : dtyping inf _ (trm_castdn _) _ |- _ => inversion Hinf end.
Qed.

Lemma dtyping_chk_general_inv : forall G e T, dtyping chk G e T ->
  e <> trm_top ->
  (forall a, e <> trm_castdn a) ->
  dtyping inf G e T \/
  exists A, dtyping inf G e A /\ dsub G A [#T#] /\ dtyping chk G T trm_star.
Proof.
  intros G e T H Htop Hcast. inversion H; subst.
  - exfalso. apply Htop. reflexivity.
  - exfalso. apply (Hcast e0). reflexivity.
  - right. eexists. split; [eassumption|]. split; [eassumption|eassumption].
  - left. assumption.
Qed.


(* ================= fresh substitution lemmas ================= *)

Lemma subst_open_fresh_rec : forall a x k e,
  x \notin fv_trm e ->
  subst_trm a x (open_trm_wrt_trm_rec k (trm_var_f x) e) =
  open_trm_wrt_trm_rec k a e.
Proof.
  intros a x k e. revert k. induction e; intros k0 Hfv; simpl in *.
  - destruct (classicT (k0 = n)) as [Heq|Hneq]; simpl.
    + subst n. destruct (classicT (x = x)) as [H|H]; [reflexivity|exfalso; apply H; reflexivity].
    + destruct (classicT (k0 = n)) as [H1|H2]; [congruence|reflexivity].
  - destruct (classicT (x5 = x)) as [Heq|Hneq].
    + exfalso. apply Hfv. rewrite Heq. apply in_singleton_self.
    + simpl. destruct (classicT (x5 = x)) as [H1|H2]; [congruence|reflexivity].
  - reflexivity. - reflexivity.
  - apply notin_union_r in Hfv as [H1 H2]. simpl.
    rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2). reflexivity.
  - apply notin_union_r in Hfv as [H1 H2]. apply notin_union_r in H2 as [H2a H2b].
    simpl. rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2a). rewrite (IHe3 (S k0) H2b). reflexivity.
  - apply notin_union_r in Hfv as [H1 H2]. apply notin_union_r in H2 as [H2a H2b].
    simpl. rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2a). rewrite (IHe3 (S k0) H2b). reflexivity.
  - apply notin_union_r in Hfv as [H1 H2]. simpl.
    rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2). reflexivity.
  - simpl. rewrite (IHe k0 Hfv). reflexivity.
  - apply notin_union_r in Hfv as [H1 H2]. simpl.
    rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2). reflexivity.
Qed.

Lemma subst_open_fresh : forall a x e,
  x \notin fv_trm e ->
  subst_trm a x (open_trm_wrt_trm e (trm_var_f x)) =
  open_trm_wrt_trm e a.
Proof. intros. unfold open_trm_wrt_trm. apply subst_open_fresh_rec. assumption. Qed.

Lemma fv_remove_anno_notin : forall e x, x \notin fv_trm e -> x \notin fv_trm [# e #].
Proof.
  induction e; simpl; intros xx H.
  - exact H. - exact H. - exact H. - exact H.
  - apply notin_union_r in H as [H1 H2].
    apply notin_union_l; [exact (IHe1 xx H1)|exact (IHe2 xx H2)].
  - apply notin_union_r in H as [H1 H2]. apply notin_union_r in H2 as [H2a H2b].
    apply notin_union_l; [exact (IHe1 xx H1)|].
    apply notin_union_l; [exact (IHe2 xx H2a)|exact (IHe3 xx H2b)].
  - apply notin_union_r in H as [H1 H2]. apply notin_union_r in H2 as [H2a H2b].
    apply notin_union_l; [exact (IHe1 xx H1)|].
    apply notin_union_l; [exact (IHe2 xx H2a)|exact (IHe3 xx H2b)].
  - apply notin_union_r in H as [H1 H2].
    apply notin_union_l; [exact (IHe1 xx H1)|exact (IHe2 xx H2)].
  - exact (IHe xx H).
  - apply notin_union_r in H as [H1 H2]. exact (IHe1 xx H1).
Qed.

Lemma open_fresh_inj : forall x e1 e2,
  x \notin fv_trm e1 -> x \notin fv_trm e2 ->
  open_trm_wrt_trm e1 (trm_var_f x) = open_trm_wrt_trm e2 (trm_var_f x) -> e1 = e2.
Proof.
  intros x e1 e2 H1 H2 H.
  rewrite <- (@open_close x 0 e1 H1). rewrite <- (@open_close x 0 e2 H2).
  f_equal. exact H.
Qed.


Lemma dwf_push_tail : forall G x b, dwf (G & x ~ b) -> dwf G.
Proof.
  intros G x b H. inversion H; subst.
  - exfalso.
    assert (Hb : binds x b empty).
    { rewrite H1. apply binds_push_eq. }
    exact (@binds_empty_inv binding x b Hb).
  - rewrite concat_def in H0. rewrite single_def in H0.
    change ((x0, bind_sub [#e#] [#A#]) :: G0 = (x, b) :: G) in H0.
    injection H0 as Hpair HG.
    subst G0. exact (@dtyping_dwf chk _ e [#A#] H2).
Qed.


Lemma dwf_binds_Et : forall G x e A, dwf G -> binds x (bind_sub e A) G ->
  Et e /\ Et A.
Proof.
  intros G x e A Hw Hb.
  assert (Hmap : map rem_anno_env G = G) by (apply dwf_E; exact Hw).
  assert (Hb' : binds x (rem_anno_env (bind_sub e A)) G).
  { rewrite <- Hmap. apply binds_map. exact Hb. }
  assert (Heq : rem_anno_env (bind_sub e A) = bind_sub e A)
    by (eapply binds_functional; [exact Hb'|exact Hb]).
  simpl in Heq. injection Heq as He HA. split; unfold Et; assumption.
Qed.

Lemma dwf_binds_star_wit_inf : forall G x e A, dwf G -> binds x (bind_sub e A) G ->
  exists X, dtyping inf G X trm_star /\ [#X#] = A.
Proof.
  intros G x e A Hw Hb.
  destruct (@dwf_binds_star_wit G x e A Hw Hb) as [X [He Hchk]].
  exists (trm_anno X trm_star). split.
  - apply dtyping_anno.
    + exact Hchk.
    + apply dtyping_chk. apply dtyping_star. exact Hw.
  - simpl. exact He.
Qed.


Lemma Et_prod_inv : forall e A B, Et (trm_prod e A B) -> Et e /\ Et A /\ Et B.
Proof. intros e A B H. unfold Et in *. simpl in H. injection H as He HA HB. split; [exact He|split; assumption]. Qed.

Lemma Et_abs_inv : forall e A B, Et (trm_abs e A B) -> Et e /\ Et A /\ Et B.
Proof. intros e A B H. unfold Et in *. simpl in H. injection H as He HA HB. split; [exact He|split; assumption]. Qed.

Lemma Et_app_inv : forall e1 e2, Et (trm_app e1 e2) -> Et e1 /\ Et e2.
Proof. intros e1 e2 H. unfold Et in *. simpl in H. injection H as H1 H2. split; assumption. Qed.

Lemma Et_castup_inv : forall A e, Et (trm_castup A e) -> Et A /\ Et e.
Proof. intros A e H. unfold Et in *. simpl in H. injection H as H1 H2. split; assumption. Qed.

Lemma Et_castdn_inv : forall e, Et (trm_castdn e) -> Et e.
Proof. intros e H. unfold Et in *. simpl in H. injection H as H1. exact H1. Qed.

Lemma Et_anno_absurd : forall e A, Et (trm_anno e A) -> False.
Proof. intros e A H. unfold Et in H. simpl in H. eapply remove_anno_not_anno. exact H. Qed.


(* rename identity lemmas *)
Lemma rename_trm_id : forall x y e, x \notin fv_trm e -> y \notin fv_trm e -> rename x y e = e.
Proof.
  intros x y e. revert x y. induction e; intros x0 y0 Hx Hy; simpl in *.
  - reflexivity. 
  - unfold rename. simpl. destruct (classicT (x5 = x0)) as [Heq|Hneq].
    + exfalso. apply Hx. rewrite Heq. apply in_singleton_self.
    + reflexivity.
  - reflexivity. - reflexivity.
  - apply notin_union_r in Hx as [Hx1 Hx2]. apply notin_union_r in Hy as [Hy1 Hy2].
    change (trm_app (rename x0 y0 e1) (rename x0 y0 e2) = trm_app e1 e2).
    rewrite (IHe1 x0 y0 Hx1 Hy1). rewrite (IHe2 x0 y0 Hx2 Hy2). reflexivity.
  - apply notin_union_r in Hx as [Hx1 Hx2]. apply notin_union_r in Hx2 as [Hx2a Hx2b].
    apply notin_union_r in Hy as [Hy1 Hy2]. apply notin_union_r in Hy2 as [Hy2a Hy2b].
    change (trm_abs (rename x0 y0 e1) (rename x0 y0 e2) (rename x0 y0 e3) = trm_abs e1 e2 e3).
    rewrite (IHe1 x0 y0 Hx1 Hy1). rewrite (IHe2 x0 y0 Hx2a Hy2a). rewrite (IHe3 x0 y0 Hx2b Hy2b). reflexivity.
  - apply notin_union_r in Hx as [Hx1 Hx2]. apply notin_union_r in Hx2 as [Hx2a Hx2b].
    apply notin_union_r in Hy as [Hy1 Hy2]. apply notin_union_r in Hy2 as [Hy2a Hy2b].
    change (trm_prod (rename x0 y0 e1) (rename x0 y0 e2) (rename x0 y0 e3) = trm_prod e1 e2 e3).
    rewrite (IHe1 x0 y0 Hx1 Hy1). rewrite (IHe2 x0 y0 Hx2a Hy2a). rewrite (IHe3 x0 y0 Hx2b Hy2b). reflexivity.
  - apply notin_union_r in Hx as [Hx1 Hx2]. apply notin_union_r in Hy as [Hy1 Hy2].
    change (trm_castup (rename x0 y0 e1) (rename x0 y0 e2) = trm_castup e1 e2).
    rewrite (IHe1 x0 y0 Hx1 Hy1). rewrite (IHe2 x0 y0 Hx2 Hy2). reflexivity.
  - change (trm_castdn (rename x0 y0 e) = trm_castdn e).
    rewrite (IHe x0 y0 Hx Hy). reflexivity.
  - apply notin_union_r in Hx as [Hx1 Hx2]. apply notin_union_r in Hy as [Hy1 Hy2].
    change (trm_anno (rename x0 y0 e1) (rename x0 y0 e2) = trm_anno e1 e2).
    rewrite (IHe1 x0 y0 Hx1 Hy1). rewrite (IHe2 x0 y0 Hx2 Hy2). reflexivity.
Qed.



Lemma rename_binding_id : forall x y b,
  x \notin fv_binding b -> y \notin fv_binding b -> rename_binding x y b = b.
Proof.
  intros x y [e A] Hx Hy. simpl in *. apply notin_union_r in Hx as [Hx1 Hx2].
  apply notin_union_r in Hy as [Hy1 Hy2]. unfold rename_binding. simpl.
  f_equal; [apply rename_trm_id; assumption|apply rename_trm_id; assumption].
Qed.

Lemma rename_env_id : forall G x y,
  x # G -> y # G ->
  x \notin fv_in_values fv_binding G ->
  y \notin fv_in_values fv_binding G ->
  rename_env x y G = G.
Proof.
  intros G. induction G as [| [z b] G' IH]; intros x y Hx Hy Hxv Hyv.
  - reflexivity.
  - rewrite cons_eq_push in Hx, Hy.
    rewrite cons_eq_push.
    rewrite dom_push in Hx. rewrite dom_push in Hy.
    apply notin_union_r in Hx as [Hxz HxG].
    apply notin_union_r in Hy as [Hyz HyG].
    apply notin_singleton_r in Hxz. apply notin_singleton_r in Hyz.
    unfold fv_in_values in Hxv, Hyv. rewrite values_def in Hxv, Hyv.
    rewrite LibList.map_cons in Hxv, Hyv. rewrite LibList.fold_right_cons in Hxv, Hyv.
    apply notin_union_r in Hxv as [Hxb HxGv].
    apply notin_union_r in Hyv as [Hyb HyGv].
    rewrite <- values_def in HxGv, HyGv.
    simpl in Hxb, Hyb.
    rewrite <- cons_eq_push. rewrite rename_env_cons.
    destruct (classicT (z = x)) as [Heq|Hneq].
    + exfalso. apply Hxz. symmetry. exact Heq.
    + assert (Hb : rename_binding x y b = b) by (apply rename_binding_id; assumption).
      rewrite Hb. rewrite (IH x y HxG HyG HxGv HyGv). reflexivity.
Qed.

(* close/open = rename *)
Lemma open_close_rename_rec : forall x0 y k e,
  lc_rec k e ->
  open_trm_wrt_trm_rec k (trm_var_f y) (close_rec x0 k e) = rename x0 y e.
Proof.
  intros x0 y k e. revert k. induction e; intros k0 Hlc; simpl in *.
  - (* var_b *) simpl. destruct (classicT (k0 = n)) as [Heq|Hneq]; simpl.
    + exfalso. subst n. lia.
    + reflexivity.
  - (* var_f *) destruct (classicT (x5 = x0)) as [Heq|Hneq].
    + subst x5. simpl. unfold rename. simpl.
      destruct (classicT (x0 = x0)) as [H1|H1]; [|exfalso; apply H1; reflexivity].
      destruct (classicT (k0 = k0)) as [H2|H2]; [reflexivity|exfalso; apply H2; reflexivity].
    + simpl. unfold rename. simpl. destruct (classicT (x5 = x0)) as [H1|H2]; [congruence|reflexivity].
  - reflexivity. - reflexivity.
  - destruct Hlc as [H1 H2]. simpl. rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2). reflexivity.
  - destruct Hlc as [H1 [H2 H3]]. simpl.
    rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2). rewrite (IHe3 (S k0) H3). reflexivity.
  - destruct Hlc as [H1 [H2 H3]]. simpl.
    rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2). rewrite (IHe3 (S k0) H3). reflexivity.
  - destruct Hlc as [H1 H2]. simpl. rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2). reflexivity.
  - simpl. rewrite (IHe k0 Hlc). reflexivity.
  - destruct Hlc as [H1 H2]. simpl. rewrite (IHe1 k0 H1). rewrite (IHe2 k0 H2). reflexivity.
Qed.

Lemma open_close_rename : forall x0 y e, lc_rec 0 e ->
  open_trm_wrt_trm (close_rec x0 0 e) (trm_var_f y) = rename x0 y e.
Proof. intros. unfold open_trm_wrt_trm. apply open_close_rename_rec. assumption. Qed.

(* star witness for a lambda type *)
Lemma star_wit_lam_cons : forall G e1 A B L,
  dtyping chk G e1 [#A#] ->
  dtyping chk G A trm_star ->
  (forall x, x \notin L -> exists Y,
     dtyping inf (G & x ~ bind_sub [#e1#] [#A#]) Y trm_star /\ [#Y#] = B ^ x) ->
  exists X, dtyping inf G X trm_star /\ [#X#] = trm_prod [#e1#] [#A#] B.
Proof.
  intros G e1 A B L H1 H2 Hfam.
  set (Lf := union (union (union (union (union L (dom G)) (fv_in_values fv_binding G)) (fv_trm e1)) (fv_trm A)) (fv_trm B)).
  pick_fresh_gen Lf x0.
  apply notin_union_r in Fr as [Fr1 Hx0B].
  apply notin_union_r in Fr1 as [Fr2 Hx0A].
  apply notin_union_r in Fr2 as [Fr3 Hx0e1].
  apply notin_union_r in Fr3 as [Fr4 Hx0vals].
  apply notin_union_r in Fr4 as [Hx0L Hx0G].
  destruct (Hfam x0 Hx0L) as [Y0 [HY0 HeY0]].
  assert (HdwfE0 : dwf (G & x0 ~ bind_sub [#e1#] [#A#])) by (exact (@dtyping_dwf inf (G & x0 ~ bind_sub [#e1#] [#A#]) Y0 trm_star HY0)).
  assert (HlcE0 : lc_env (G & x0 ~ bind_sub [#e1#] [#A#])) by (apply dwf_lc_env; exact HdwfE0).
  destruct (@dtyping_lc inf (G & x0 ~ bind_sub [#e1#] [#A#]) Y0 trm_star HY0 HlcE0) as [HlcY0 _].
  assert (HlcRec : lc_rec 0 Y0) by (apply lc_trm_lc_rec; exact HlcY0).
  set (Bw := close_rec x0 0 Y0).
  assert (HeBw : [# Bw #] = B).
  { unfold Bw. rewrite remove_anno_close. rewrite HeY0.
    exact (@open_close x0 0 B Hx0B). }
  exists (trm_prod e1 A Bw). split.
  - eapply dtyping_pi with (L := Lf).
    + exact H1.
    + exact H2.
    + intros y Hy.
      apply notin_union_r in Hy as [Hy1 HyB].
      apply notin_union_r in Hy1 as [Hy2 HyA].
      apply notin_union_r in Hy2 as [Hy3 Hye1].
      apply notin_union_r in Hy3 as [Hy4 Hyvals].
      apply notin_union_r in Hy4 as [HyL HyG].
      destruct (classicT (y = x0)) as [Heq|Hneq].
      * subst y. unfold Bw. unfold open_trm_wrt_trm. rewrite (@close_open x0 0 Y0 HlcRec).
        apply dtyping_chk. exact HY0.
      * assert (Hx0y : x0 <> y) by (intro He; apply Hneq; symmetry; exact He).
        assert (HyE0 : y # (G & x0 ~ bind_sub [#e1#] [#A#])).
        { rewrite dom_push. apply notin_union_l.
          - apply notin_singleton_l. exact Hneq.
          - exact HyG. }
        pose proof (@dtyping_rename inf (G & x0 ~ bind_sub [#e1#] [#A#]) Y0 trm_star HY0 x0 y Hx0y HyE0) as Hren.
        assert (Henv : rename_env x0 y (G & x0 ~ bind_sub [#e1#] [#A#]) = G & y ~ bind_sub [#e1#] [#A#]).
        { rewrite rename_env_push.
          assert (HrenG : rename_env x0 y G = G)
            by (exact (@rename_env_id G x0 y Hx0G HyG Hx0vals Hyvals)).
          rewrite HrenG.
          destruct (classicT (x0 = x0)) as [Heq2|Hne2]; [|exfalso; apply Hne2; reflexivity].
          assert (Hrb : rename_binding x0 y (bind_sub [#e1#] [#A#]) = bind_sub [#e1#] [#A#]).
          { apply rename_binding_id.
            - simpl. apply notin_union_l.
              + apply fv_remove_anno_notin. exact Hx0e1.
              + apply fv_remove_anno_notin. exact Hx0A.
            - simpl. apply notin_union_l.
              + apply fv_remove_anno_notin. exact Hye1.
              + apply fv_remove_anno_notin. exact HyA. }
          rewrite Hrb. reflexivity. }
        assert (Hterm : rename x0 y Y0 = Bw ^ y).
        { symmetry. unfold Bw. apply open_close_rename. exact HlcRec. }
        rewrite Henv, Hterm in Hren.
        apply dtyping_chk. exact Hren.
  - simpl. rewrite HeBw. reflexivity.
Qed.

(* erasure self-subtyping of typings *)
Definition dsub_refl_P (d:dir) (G:env) (e A:trm) (H:dtyping d G e A) : Prop := dsub G [#e#] [#e#].
Definition dsub_refl_P0 (G:env) (H:dwf G) : Prop := True.

Lemma dtyping_dsub_refl : forall d G e A (H:dtyping d G e A), dsub_refl_P H.
Proof.
  intros d G e A H.
  apply (@dtyping_mut dsub_refl_P dsub_refl_P0).
  - (* star *) intros G0 Hd IH. simpl. apply dsub_star. apply dwf_ok. exact Hd.
  - (* var *) intros e0 G0 xx A0 Hd IH b. simpl. eapply dsub_var_refl.
    + apply dwf_ok. exact Hd.
    + exact b.
  - (* top *) intros G0 A0 d1 IH1. simpl. eapply dsub_top.
    + apply dwf_ok. exact (@dtyping_dwf chk G0 A0 trm_star d1).
    + constructor.
  - (* lam *) intros L G0 e1 e2 A0 B d1 IH1 d2 IH2 d3 IH3. simpl.
    eapply dsub_lam.
    + apply dwf_ok. exact (@dtyping_dwf chk G0 e1 [#A0#] d1).
    + intros x Hx. specialize (IH3 x Hx). unfold dsub_refl_P in IH3.
      repeat rewrite remove_anno_idem. rewrite remove_anno_open_var in IH3. exact IH3.
  - (* app *) intros e3 G0 e0 A0 B C d1 IH1 dsub0 d2 IH2. simpl.
    eapply dsub_app.
    + assert (Hdwf : dwf G0) by (exact (@dtyping_dwf chk G0 A0 B d1)).
      assert (HlcE : lc_env G0) by (apply dwf_lc_env; exact Hdwf).
      destruct (@dtyping_lc chk G0 A0 B d1 HlcE) as [HlcA _].
      apply lc_trm_remove_anno. exact HlcA.
    + exact IH2.
  - (* pi *) intros L G0 e0 A0 B d1 IH1 d2 IH2 d3 IH3. simpl.
    eapply dsub_pi.
    + exact IH2.
    + intros x Hx. specialize (IH3 x Hx). unfold dsub_refl_P in IH3.
      repeat rewrite remove_anno_idem. rewrite remove_anno_open_var in IH3. exact IH3.
  - (* castup *) intros G0 e0 A0 B d1 IH1 d2 IH2 r. simpl.
    eapply dsub_castup.
    + assert (Hdwf : dwf G0) by (exact (@dtyping_dwf chk G0 B trm_star d1)).
      assert (HlcE : lc_env G0) by (apply dwf_lc_env; exact Hdwf).
      destruct (@dtyping_lc chk G0 B trm_star d1 HlcE) as [HlcB _].
      apply lc_trm_remove_anno. exact HlcB.
    + exact IH2.
  - (* castdn *) intros G0 e0 A0 B d1 IH1 d2 IH2 r. simpl.
    eapply dsub_castdn. exact IH2.
  - (* anno *) intros G0 e0 A0 d1 IH1 d2 IH2. simpl. exact IH1.
  - (* sub *) intros A0 G0 e0 B d1 IH1 dsub0 d2 IH2. simpl. exact IH1.
  - (* chk *) intros G0 e0 A0 d1 IH1. simpl. exact IH1.
  - intros. exact I.
  - intros. exact I.
Qed.

(* substitution on environments *)
Fixpoint subst_env (a:trm) (x:var) (G:env) : env :=
  match G with
  | nil => nil
  | (y,b) :: G' => (y, subst_binding a x b) :: subst_env a x G'
  end.

Lemma subst_env_nil : forall a x, subst_env a x empty = empty.
Proof. intros. rewrite (empty_def binding). simpl. rewrite <- (empty_def binding). reflexivity. Qed.

Lemma subst_env_push : forall a x (G:env) y b,
  subst_env a x (G & y ~ b) = subst_env a x G & y ~ subst_binding a x b.
Proof.
  intros. rewrite <- cons_eq_push. simpl. rewrite <- cons_eq_push. reflexivity.
Qed.


Lemma dsub_lhs_top_gen : forall G e1 e2, dsub G e1 e2 -> e1 = trm_top -> e2 = trm_top.
Proof.
  intros G e1 e2 H. induction H; intros Heq; try discriminate Heq.
  - reflexivity.
Qed.
Lemma dsub_lhs_top : forall G e, dsub G trm_top e -> e = trm_top.
Proof. intros G e H. exact (dsub_lhs_top_gen H eq_refl). Qed.

Lemma dsub_rhs_star_gen : forall G e1 e2, dsub G e1 e2 -> e2 = trm_star ->
  e1 = trm_star \/
  exists x e1' A, e1 = trm_var_f x /\ binds x (bind_sub e1' A) G /\ dsub G e1' trm_star.
Proof.
  intros G e1 e2 H. induction H; intros Heq; try discriminate Heq.
  - left. reflexivity.
  - right. eexists. eexists. eexists. split; [reflexivity|]. split; [exact H|].
    subst e2. exact H0.
Qed.
Lemma dsub_rhs_star : forall G e, dsub G e trm_star -> e = trm_star \/
  exists x e1 A, e = trm_var_f x /\ binds x (bind_sub e1 A) G /\ dsub G e1 trm_star.
Proof. intros G e H. exact (dsub_rhs_star_gen H eq_refl). Qed.


(* inf result types are annotation-free *)
Definition Et_type_P (d:dir) (G:env) (e A:trm) (H:dtyping d G e A) : Prop := d = inf -> Et A.
Definition Et_type_P0 (G:env) (H:dwf G) : Prop := True.

Lemma dtyping_inf_Et_type : forall d G e A, dtyping d G e A -> d = inf -> Et A.
Proof.
  intros d G e A H.
  change (Et_type_P H).
  apply (@dtyping_mut Et_type_P Et_type_P0).
  - intros G0 Hd IH E0. unfold Et. reflexivity.
  - intros e0 G0 xx A0 Hd IH b E0. apply dwf_binds_Et in b; [|exact Hd]. apply b.
  - intros G0 A0 d1 IH1 E0. exfalso. discriminate E0.
  - intros L G0 e1 e2 A0 B d1 IH1 d2 IH2 d3 IH3 E0.
    unfold Et. simpl. rewrite remove_anno_idem. rewrite remove_anno_idem.
    pick_fresh_gen L x.
    assert (HB : Et B) by (apply (@Et_open_var_inv B x); apply (IH3 x Fr); reflexivity).
    unfold Et in HB. rewrite HB. reflexivity.
  - intros e3 G0 e0 A0 B C d1 IH1 dsub0 d2 IH2 E0.
    apply Et_open.
    + destruct (@Et_prod_inv e3 B C (IH2 eq_refl)) as [He Hrest]. destruct Hrest as [HB HC]. exact HC.
    + unfold Et. rewrite remove_anno_idem. reflexivity.
  - intros L G0 e0 A0 B d1 IH1 d2 IH2 d3 IH3 E0. unfold Et. reflexivity.
  - intros G0 e0 A0 B d1 IH1 d2 IH2 r E0. unfold Et. rewrite remove_anno_idem. reflexivity.
  - intros G0 e0 A0 B d1 IH1 d2 IH2 r E0. exfalso. discriminate E0.
  - intros G0 e0 A0 d1 IH1 d2 IH2 E0. unfold Et. rewrite remove_anno_idem. reflexivity.
  - intros A0 G0 e0 B d1 IH1 dsub0 d2 IH2 E0. exfalso. discriminate E0.
  - intros G0 e0 A0 d1 IH1 E0. exfalso. discriminate E0.
  - intros. exact I.
  - intros. exact I.
Qed.

(* chk-mode inversions for non-special terms *)
Lemma dtyping_chk_star_inv : forall G A, dtyping chk G trm_star A ->
  A = trm_star \/ (dsub G trm_star [#A#] /\ dtyping chk G A trm_star).
Proof.
  intros G A H.
  assert (Htop : trm_star <> trm_top) by discriminate.
  assert (Hcast : forall a, trm_star <> trm_castdn a) by (intros a Heq; discriminate Heq).
  destruct (@dtyping_chk_general_inv G trm_star A H Htop Hcast) as [Hinf|Hex].
  - left. exact (@dtyping_inf_star_inv G A Hinf).
  - right. destruct Hex as [A0 [Hinf [Hd Hchk]]].
    assert (Heq : A0 = trm_star) by (exact (@dtyping_inf_star_inv G A0 Hinf)).
    subst A0. split; assumption.
Qed.

Lemma dtyping_chk_var_inv : forall G x A, dtyping chk G (trm_var_f x) A ->
  (exists e, dwf G /\ binds x (bind_sub e A) G) \/
  exists A0 e, binds x (bind_sub e A0) G /\ dsub G A0 [#A#] /\ dtyping chk G A trm_star.
Proof.
  intros G x A H.
  assert (Htop : trm_var_f x <> trm_top) by discriminate.
  assert (Hcast : forall a, trm_var_f x <> trm_castdn a) by (intros a Heq; discriminate Heq).
  destruct (@dtyping_chk_general_inv G (trm_var_f x) A H Htop Hcast) as [Hinf|Hex].
  - left. exact (@dtyping_inf_var_inv G x A Hinf).
  - right. destruct Hex as [A0 [Hinf [Hd Hchk]]].
    destruct (@dtyping_inf_var_inv G x A0 Hinf) as [e [Hdwf Hb]].
    exists A0, e. split; [exact Hb|]. split; assumption.
Qed.

(* chk-mode shape inversions *)
Lemma dtyping_chk_abs_inv : forall G e1 A0 body T, dtyping chk G (trm_abs e1 A0 body) T ->
  dtyping inf G (trm_abs e1 A0 body) T \/
  exists A0ty, dtyping inf G (trm_abs e1 A0 body) A0ty /\ dsub G A0ty [#T#] /\ dtyping chk G T trm_star.
Proof.
  intros G e1 A0 body T H.
  assert (Htop : trm_abs e1 A0 body <> trm_top) by discriminate.
  assert (Hcast : forall a, trm_abs e1 A0 body <> trm_castdn a) by (intros a Heq; discriminate Heq).
  destruct (@dtyping_chk_general_inv G (trm_abs e1 A0 body) T H Htop Hcast) as [Hinf|Hex]; [left;exact Hinf|right;exact Hex].
Qed.

Lemma dtyping_chk_app_inv : forall G a Aarg T, dtyping chk G (trm_app a Aarg) T ->
  dtyping inf G (trm_app a Aarg) T \/
  exists A0ty, dtyping inf G (trm_app a Aarg) A0ty /\ dsub G A0ty [#T#] /\ dtyping chk G T trm_star.
Proof.
  intros G a Aarg T H.
  assert (Htop : trm_app a Aarg <> trm_top) by discriminate.
  assert (Hcast : forall b, trm_app a Aarg <> trm_castdn b) by (intros b Heq; discriminate Heq).
  destruct (@dtyping_chk_general_inv G (trm_app a Aarg) T H Htop Hcast) as [Hinf|Hex]; [left;exact Hinf|right;exact Hex].
Qed.

Lemma dtyping_chk_pi_inv : forall G e A B T, dtyping chk G (trm_prod e A B) T ->
  dtyping inf G (trm_prod e A B) T \/
  exists A0ty, dtyping inf G (trm_prod e A B) A0ty /\ dsub G A0ty [#T#] /\ dtyping chk G T trm_star.
Proof.
  intros G e A B T H.
  assert (Htop : trm_prod e A B <> trm_top) by discriminate.
  assert (Hcast : forall a, trm_prod e A B <> trm_castdn a) by (intros a Heq; discriminate Heq).
  destruct (@dtyping_chk_general_inv G (trm_prod e A B) T H Htop Hcast) as [Hinf|Hex]; [left;exact Hinf|right;exact Hex].
Qed.

Lemma dtyping_chk_anno_inv : forall G e A T, dtyping chk G (trm_anno e A) T ->
  dtyping inf G (trm_anno e A) T \/
  exists A0ty, dtyping inf G (trm_anno e A) A0ty /\ dsub G A0ty [#T#] /\ dtyping chk G T trm_star.
Proof.
  intros G e A T H.
  assert (Htop : trm_anno e A <> trm_top) by discriminate.
  assert (Hcast : forall a, trm_anno e A <> trm_castdn a) by (intros a Heq; discriminate Heq).
  destruct (@dtyping_chk_general_inv G (trm_anno e A) T H Htop Hcast) as [Hinf|Hex]; [left;exact Hinf|right;exact Hex].
Qed.

Lemma dtyping_chk_castup_inv : forall G B e T, dtyping chk G (trm_castup B e) T ->
  dtyping inf G (trm_castup B e) T \/
  exists A0ty, dtyping inf G (trm_castup B e) A0ty /\ dsub G A0ty [#T#] /\ dtyping chk G T trm_star.
Proof.
  intros G B e T H.
  assert (Htop : trm_castup B e <> trm_top) by discriminate.
  assert (Hcast : forall a, trm_castup B e <> trm_castdn a) by (intros a Heq; discriminate Heq).
  destruct (@dtyping_chk_general_inv G (trm_castup B e) T H Htop Hcast) as [Hinf|Hex]; [left;exact Hinf|right;exact Hex].
Qed.

(* substitution environment algebra *)
Lemma concat_assoc_r : forall (A B:env) y c, A & (B & y ~ c) = (A & B) & y ~ c.
Proof.
  intros. rewrite concat_def. rewrite single_def. simpl. rewrite LibList.app_assoc. reflexivity.
Qed.

Lemma subst_env_concat : forall a x (E1 E2:env),
  subst_env a x (E1 & E2) = subst_env a x E1 & subst_env a x E2.
Proof.
  intros a x E1 E2. revert E1. induction E2 as [| [z c] E2' IH]; intros E1.
  - rewrite <- (empty_def binding). rewrite concat_empty_r. rewrite subst_env_nil. rewrite concat_empty_r. reflexivity.
  - rewrite cons_eq_push. rewrite subst_env_push.
    rewrite concat_assoc_r. rewrite subst_env_push. rewrite IH.
    symmetry. apply concat_assoc_r.
Qed.

Lemma binds_subst_env : forall a x (G:env) y b,
  binds y b G -> y <> x -> binds y (subst_binding a x b) (subst_env a x G).
Proof.
  intros a x G. induction G as [| [z c] G' IH]; intros y b Hb Hneq.
  - rewrite <- (empty_def binding) in Hb. exfalso. exact (@binds_empty_inv binding y b Hb).
  - rewrite cons_eq_push in Hb. rewrite cons_eq_push.
    rewrite subst_env_push. apply binds_push_inv in Hb as [[Heq Hb]|[Hneqz Hb]].
    + inversion Heq. subst y c. apply binds_push_eq.
    + apply binds_push_neq; [apply IH; assumption|]. exact Hneqz.
Qed.

(* substitution/open commutation and local closure *)
Lemma subst_open_neq_lc_rec : forall a x y k e,
  x <> y -> lc_trm a ->
  subst_trm a x (open_trm_wrt_trm_rec k (trm_var_f y) e) =
  open_trm_wrt_trm_rec k (trm_var_f y) (subst_trm a x e).
Proof.
  intros a x y k e Hxy Hlca. revert k. induction e; intros k0; simpl.
  - (* var_b *) destruct (classicT (k0 = n)) as [Heq|Hneq].
    + subst n. destruct (classicT (k0 = k0)) as [H0|H0]; [|exfalso;apply H0;reflexivity].
      destruct (classicT (y = x)) as [Hyx|Hnx].
      * exfalso. apply Hxy. symmetry. exact Hyx.
      * simpl. destruct (classicT (y = x)) as [H1|H1]; [congruence|reflexivity].
    + destruct (classicT (k0 = n)) as [H0|H0]; [congruence|reflexivity].
  - (* var_f *) destruct (classicT (x5 = x)) as [Heq|Hneq].
    + subst x5. simpl. symmetry.
      apply (@lc_rec_open_id k0 (trm_var_f y) a).
      apply (lc_rec_mono (n:=0) (m:=k0)); [lia|apply lc_trm_lc_rec; exact Hlca].
    + simpl. reflexivity.
  - reflexivity. - reflexivity.
  - f_equal; [apply IHe1|apply IHe2]; assumption.
  - f_equal; [apply IHe1|apply IHe2|apply IHe3]; assumption.
  - f_equal; [apply IHe1|apply IHe2|apply IHe3]; assumption.
  - f_equal; [apply IHe1|apply IHe2]; assumption.
  - f_equal; apply IHe; assumption.
  - f_equal; [apply IHe1|apply IHe2]; assumption.
Qed.

Lemma subst_open_neq_lc : forall a x y e,
  x <> y -> lc_trm a ->
  subst_trm a x (open_trm_wrt_trm e (trm_var_f y)) =
  open_trm_wrt_trm (subst_trm a x e) (trm_var_f y).
Proof. intros. unfold open_trm_wrt_trm. apply subst_open_neq_lc_rec; assumption. Qed.

Lemma lc_rec_subst : forall e n v x, lc_rec n v -> lc_rec n e -> lc_rec n (subst_trm v x e).
Proof.
  intros e. induction e; intros n0 v x Hv He; simpl in *.
  - exact He.
  - destruct (classicT (x5 = x)) as [Heq|Hneq]; [exact Hv|exact He].
  - exact He. - exact He.
  - destruct He as [H1 H2]. split; [apply IHe1|apply IHe2]; assumption.
  - destruct He as [H1 [H2 H3]]. split; [apply IHe1; assumption|]. split; [apply IHe2; assumption|].
    apply (IHe3 (S n0) v x).
    + apply lc_rec_mono with (n:=n0); [lia|exact Hv].
    + exact H3.
  - destruct He as [H1 [H2 H3]]. split; [apply IHe1; assumption|]. split; [apply IHe2; assumption|].
    apply (IHe3 (S n0) v x).
    + apply lc_rec_mono with (n:=n0); [lia|exact Hv].
    + exact H3.
  - destruct He as [H1 H2]. split; [apply IHe1|apply IHe2]; assumption.
  - simpl. apply IHe; [exact Hv|exact He].
  - destruct He as [H1 H2]. split; [apply IHe1|apply IHe2]; assumption.
Qed.

Lemma lc_trm_subst : forall v x e, lc_trm e -> lc_trm v -> lc_trm (subst_trm v x e).
Proof.
  intros v x e He Hv.
  apply lc_rec_0_lc_trm. apply (@lc_rec_subst e 0 v x).
  - apply lc_trm_lc_rec; exact Hv.
  - apply lc_trm_lc_rec; exact He.
Qed.
Lemma extends_trans : forall (E F G:env), extends E F -> extends F G -> extends E G.
Proof. intros E F G H1 H2 x v Hb. apply H2. apply H1. exact Hb. Qed.


(* combined mutual system U for structural mutual induction *)
Inductive dtypingU : dir -> env -> trm -> trm -> Prop :=
  | du_star : forall G, dwfU G -> dtypingU inf G trm_star trm_star
  | du_var : forall e G x A,
      dwfU G -> binds x (bind_sub e A) G -> dtypingU inf G (trm_var_f x) A
  | du_top : forall G A,
      dtypingU chk G A trm_star -> dtypingU chk G trm_top A
  | du_lam : forall L G e1 e2 A B,
      dtypingU chk G e1 [#A#] ->
      dtypingU chk G A trm_star ->
      (forall x, x \notin L -> dtypingU inf (G & x ~ bind_sub [#e1#] [#A#]) (e2 ^ x) (B ^ x)) ->
      dtypingU inf G (trm_abs e1 A e2) (trm_prod [#e1#] [#A#] B)
  | du_app : forall e3 G e A B C,
      dtypingU chk G A B ->
      dsubU G [#A#] e3 ->
      dtypingU inf G e (trm_prod e3 B C) ->
      dtypingU inf G (trm_app e A) (C ^^ [#A#])
  | du_pi : forall L G e A B,
      dtypingU chk G e [#A#] ->
      dtypingU chk G A trm_star ->
      (forall x, x \notin L -> dtypingU chk (G & x ~ bind_sub [#e#] [#A#]) (B ^ x) trm_star) ->
      dtypingU inf G (trm_prod e A B) trm_star
  | du_castup : forall G e A B,
      dtypingU chk G B trm_star ->
      dtypingU inf G e A ->
      reduct [#B#] [#A#] ->
      dtypingU inf G (trm_castup B e) [#B#]
  | du_castdn : forall G e A B,
      dtypingU chk G B trm_star ->
      dtypingU inf G e A ->
      reduct [#A#] [#B#] ->
      dtypingU chk G (trm_castdn e) B
  | du_anno : forall G e A,
      dtypingU chk G e A ->
      dtypingU chk G A trm_star ->
      dtypingU inf G (trm_anno e A) [#A#]
  | du_sub : forall A G e B,
      dtypingU inf G e A ->
      dsubU G A [#B#] ->
      dtypingU chk G B trm_star ->
      dtypingU chk G e B
  | du_chk : forall G e A,
      dtypingU inf G e A ->
      dtypingU chk G e A
with dwfU : env -> Prop :=
  | duwf_nil : dwfU empty
  | duwf_cons : forall G x e A,
      x # G ->
      dtypingU chk G e [#A#] ->
      dtypingU chk G A trm_star ->
      dwfU (G & x ~ bind_sub [#e#] [#A#])
with dsubU : env -> trm -> trm -> Prop :=
  | dus_star : forall G, ok G -> dsubU G trm_star trm_star
  | dus_var_refl : forall G x e A,
      ok G -> binds x (bind_sub e A) G -> dsubU G (trm_var_f x) (trm_var_f x)
  | dus_var_trans : forall e1 A G x e2,
      binds x (bind_sub e1 A) G -> dsubU G e1 e2 ->
      dsubU G (trm_var_f x) e2
  | dus_top : forall G e,
      ok G -> lc_trm e -> dsubU G e trm_top
  | dus_lam : forall L G e1 e2 e3 A,
      ok G ->
      (forall x, x \notin L -> dsubU (G & x ~ bind_sub [#e3#] [#A#]) (e1 ^ x) (e2 ^ x)) ->
      dsubU G (trm_abs e3 A e1) (trm_abs e3 A e2)
  | dus_app : forall G e1 e2 A,
      lc_trm A ->
      dsubU G e1 e2 -> dsubU G (trm_app e1 A) (trm_app e2 A)
  | dus_pi : forall L G e A B C D,
      dsubU G C A ->
      (forall x, x \notin L -> dsubU (G & x ~ bind_sub [#e#] [#C#]) (B ^ x) (D ^ x)) ->
      dsubU G (trm_prod e A B) (trm_prod e C D)
  | dus_castup : forall G A e1 e2,
      lc_trm A -> dsubU G e1 e2 -> dsubU G (trm_castup A e1) (trm_castup A e2)
  | dus_castdn : forall G e1 e2,
      dsubU G e1 e2 -> dsubU G (trm_castdn e1) (trm_castdn e2).

Scheme dtypingU_mut := Induction for dtypingU Sort Prop
  with dwfU_mut := Induction for dwfU Sort Prop
  with dsubU_mut := Induction for dsubU Sort Prop.

Lemma dtypingU_dtyping : forall d G e A, dtypingU d G e A -> dtyping d G e A.
Proof.
  intros d G e A H.
  apply (dtypingU_mut
    (fun d G e A H => dtyping d G e A)
    (fun G H => dwf G)
    (fun G e1 e2 H => dsub G e1 e2)).
  - intros G0 Hd IH. exact (dtyping_star IH).
  - intros e0 G0 x A0 Hd IH b. exact (dtyping_var IH b).
  - intros G0 A0 d1 IH1. exact (dtyping_top IH1).
  - intros L G0 e1 e2 A0 B d1 IH1 d2 IH2 d3 IH3.
    eapply dtyping_lam; [exact IH1|exact IH2|intros x Hx; apply IH3; exact Hx].
  - intros e3 G0 e0 A0 B C d1 IH1 dsub0 IHd d2 IH2.
    eapply dtyping_app; [exact IH1|exact IHd|exact IH2].
  - intros L G0 e0 A0 B d1 IH1 d2 IH2 d3 IH3.
    eapply dtyping_pi; [exact IH1|exact IH2|intros x Hx; apply IH3; exact Hx].
  - intros G0 e0 A0 B d1 IH1 d2 IH2 r. eapply dtyping_castup; [exact IH1|exact IH2|exact r].
  - intros G0 e0 A0 B d1 IH1 d2 IH2 r. eapply dtyping_castdn; [exact IH1|exact IH2|exact r].
  - intros G0 e0 A0 d1 IH1 d2 IH2. eapply dtyping_anno; [exact IH1|exact IH2].
  - intros A0 G0 e0 B d1 IH1 dsub0 IHd d2 IH2. eapply dtyping_sub; [exact IH1|exact IHd|exact IH2].
  - intros G0 e0 A0 d1 IH1. exact (dtyping_chk IH1).
  - exact dwf_nil.
  - intros G0 k e0 A0 Hk d1 IH1 d2 IH2. eapply dwf_cons; [exact Hk|exact IH1|exact IH2].
  - intros G0 Hok. exact (dsub_star Hok).
  - intros G0 x e0 A0 Hok Hb. exact (dsub_var_refl Hok Hb).
  - intros e1 A0 G0 x e2 Hb Hd IH. exact (dsub_var_trans Hb IH).
  - intros G0 e0 Hok Hlc. exact (dsub_top Hok Hlc).
  - intros L G0 e1 e2 e3 A0 Hok Hbody IHbody.
    eapply dsub_lam; [exact Hok|intros x Hx; apply IHbody; exact Hx].
  - intros G0 e1 e2 A0 Hlc Hd IH. exact (dsub_app Hlc IH).
  - intros L G0 e0 A0 B C D Hd IHd Hbody IHbody.
    eapply dsub_pi; [exact IHd|intros x Hx; apply IHbody; exact Hx].
  - intros G0 A0 e1 e2 Hlc Hd IH. exact (dsub_castup Hlc IH).
  - intros G0 e1 e2 Hd IH. exact (dsub_castdn IH).
  - exact H.
Qed.

Lemma dsub_dsubU : forall G e1 e2, dsub G e1 e2 -> dsubU G e1 e2.
Proof.
  intros G e1 e2 H. induction H.
  - exact (dus_star H).
  - exact (dus_var_refl H H0).
  - exact (dus_var_trans H IHdsub).
  - exact (dus_top H H0).
  - eapply dus_lam; [exact H|intros x Hx; apply H1; exact Hx].
  - exact (dus_app H IHdsub).
  - eapply dus_pi; [exact IHdsub|intros x Hx; apply H1; exact Hx].
  - exact (dus_castup H IHdsub).
  - exact (dus_castdn IHdsub).
Qed.

Lemma dtyping_dtypingU : forall d G e A, dtyping d G e A -> dtypingU d G e A.
Proof.
  intros d G e A H.
  apply (dtyping_mut
    (fun d G e A H => dtypingU d G e A)
    (fun G H => dwfU G)).
  - intros G0 Hd IH. exact (du_star IH).
  - intros e0 G0 x A0 Hd IH b. exact (du_var IH b).
  - intros G0 A0 d1 IH1. exact (du_top IH1).
  - intros L G0 e1 e2 A0 B d1 IH1 d2 IH2 d3 IH3.
    eapply du_lam; [exact IH1|exact IH2|intros x Hx; apply IH3; exact Hx].
  - intros e3 G0 e0 A0 B C d1 IH1 dsub0 d2 IH2.
    eapply du_app; [exact IH1|apply dsub_dsubU; exact dsub0|exact IH2].
  - intros L G0 e0 A0 B d1 IH1 d2 IH2 d3 IH3.
    eapply du_pi; [exact IH1|exact IH2|intros x Hx; apply IH3; exact Hx].
  - intros G0 e0 A0 B d1 IH1 d2 IH2 r. eapply du_castup; [exact IH1|exact IH2|exact r].
  - intros G0 e0 A0 B d1 IH1 d2 IH2 r. eapply du_castdn; [exact IH1|exact IH2|exact r].
  - intros G0 e0 A0 d1 IH1 d2 IH2. eapply du_anno; [exact IH1|exact IH2].
  - intros A0 G0 e0 B d1 IH1 dsub0 d2 IH2. eapply du_sub; [exact IH1|apply dsub_dsubU; exact dsub0|exact IH2].
  - intros G0 e0 A0 d1 IH1. exact (du_chk IH1).
  - exact duwf_nil.
  - intros G0 k e0 A0 Hk d1 IH1 d2 IH2. eapply duwf_cons; [exact Hk|exact IH1|exact IH2].
  - exact H.
Qed.

Lemma dwf_dwfU : forall G, dwf G -> dwfU G.
Proof.
  intros G H. induction H as [| G0 k e A Hk d1 d2].
  - exact duwf_nil.
  - eapply duwf_cons; [exact Hk|apply dtyping_dtypingU; exact d1|apply dtyping_dtypingU; exact d2].
Qed.

Lemma dwfU_dwf : forall G, dwfU G -> dwf G.
Proof.
  intros G H. induction H as [| G0 k e A Hk d1 d2].
  - exact dwf_nil.
  - eapply dwf_cons; [exact Hk|apply dtypingU_dtyping; exact d1|apply dtypingU_dtyping; exact d2].
Qed.

(* transfer lemmas for the combined system *)
Lemma dsubU_dsub : forall G e1 e2, dsubU G e1 e2 -> dsub G e1 e2.
Proof.
  intros G e1 e2 H. induction H.
  - exact (dsub_star H).
  - exact (dsub_var_refl H H0).
  - exact (dsub_var_trans H IHdsubU).
  - exact (dsub_top H H0).
  - eapply dsub_lam; [exact H|intros x Hx; apply H1; exact Hx].
  - exact (dsub_app H IHdsubU).
  - eapply dsub_pi; [exact IHdsubU|intros x Hx; apply H1; exact Hx].
  - exact (dsub_castup H IHdsubU).
  - exact (dsub_castdn IHdsubU).
Qed.

Lemma dtypingU_weaken_ext : forall d G e A,
  dtypingU d G e A -> forall G', extends G G' -> dwfU G' -> dtypingU d G' e A.
Proof.
  intros d G e A H G' Hext Hw.
  apply dtyping_dtypingU.
  apply (dtyping_weaken_ext (dtypingU_dtyping H) Hext).
  apply dwfU_dwf. exact Hw.
Qed.

Lemma dsubU_weaken_ext : forall G e1 e2,
  dsubU G e1 e2 -> forall G', ok G' -> extends G G' -> dsubU G' e1 e2.
Proof.
  intros G e1 e2 H G' Hok Hext.
  apply dsub_dsubU.
  eapply dsub_weaken_ext; [apply dsubU_dsub; exact H|exact Hok|exact Hext].
Qed.

Lemma dsubU_erase : forall G e1 e2, dsubU G e1 e2 -> dsubU {#G#} [#e1#] [#e2#].
Proof.
  intros. apply dsub_dsubU. apply dsub_erase. apply dsubU_dsub. exact H.
Qed.

Lemma dtypingU_lc : forall d G e A, dtypingU d G e A -> lc_env G -> lc_trm e /\ lc_trm A.
Proof.
  intros d G e A H H0. exact (@dtyping_lc d G e A (dtypingU_dtyping H) H0).
Qed.

(* combined-system reflexivity/inversion transfers *)
Lemma dtypingU_dsub_refl : forall d G e A, dtypingU d G e A -> dsubU G [# e #] [# e #].
Proof.
  intros d G e A H. apply dsub_dsubU. exact (@dtyping_dsub_refl d G e A (dtypingU_dtyping H)).
Qed.
Lemma dsubU_lhs_star : forall G e, dsubU G trm_star e -> e = trm_star \/ e = trm_top.
Proof. intros G e H. exact (@dsub_lhs_star G e (dsubU_dsub H)). Qed.

(* combined-system left-shape transfers *)
Lemma dsubU_lhs_var : forall G x e, dsubU G (trm_var_f x) e ->
  e = trm_var_f x \/ e = trm_top \/
  exists e1' e2' A, binds x (bind_sub e1' A) G /\ dsubU G e1' e2' /\ e = e2'.
Proof.
  intros G x e H. destruct (@dsub_lhs_var G x e (dsubU_dsub H)) as [He|[He|[e1' [e2' [A [Hb [Hd Heq]]]]]]].
  - left; exact He.
  - right; left; exact He.
  - right; right. exists e1', e2', A. split; [exact Hb|]. split; [apply dsub_dsubU; exact Hd|exact Heq].
Qed.
Lemma dsubU_lhs_abs : forall G e3 A b e, dsubU G (trm_abs e3 A b) e ->
  e = trm_top \/
  (ok G /\ exists L b', e = trm_abs e3 A b' /\ (forall x, x \notin L -> dsubU (G & x ~ bind_sub [#e3#] [#A#]) (b ^ x) (b' ^ x))).
Proof.
  intros G e3 A b e H. destruct (@dsub_lhs_abs G e3 A b e (dsubU_dsub H)) as [He|[Hok [L [b' [Heq Hbody]]]]].
  - left; exact He.
  - right. split; [exact Hok|]. exists L, b'. split; [exact Heq|]. intros x Hx. apply dsub_dsubU. apply Hbody. exact Hx.
Qed.
Lemma dsubU_lhs_app : forall G a A e, dsubU G (trm_app a A) e ->
  e = trm_top \/ (lc_trm A /\ exists b, e = trm_app b A /\ dsubU G a b).
Proof.
  intros G a A e H. destruct (@dsub_lhs_app G a A e (dsubU_dsub H)) as [He|[Hlc [b [Heq Hd]]]].
  - left; exact He.
  - right. split; [exact Hlc|]. exists b. split; [exact Heq|apply dsub_dsubU; exact Hd].
Qed.
Lemma dsubU_lhs_prod : forall G ee AA BB e, dsubU G (trm_prod ee AA BB) e ->
  e = trm_top \/
  exists L CC DD, e = trm_prod ee CC DD /\ dsubU G CC AA /\
    (forall x, x \notin L -> dsubU (G & x ~ bind_sub [#ee#] [#CC#]) (BB ^ x) (DD ^ x)).
Proof.
  intros G ee AA BB e H. destruct (@dsub_lhs_prod G ee AA BB e (dsubU_dsub H)) as [He|[L [CC [DD [Heq [Hd Hbody]]]]]].
  - left; exact He.
  - right. exists L, CC, DD. split; [exact Heq|]. split; [apply dsub_dsubU; exact Hd|]. intros x Hx. apply dsub_dsubU. apply Hbody. exact Hx.
Qed.
Lemma dsubU_lhs_castup : forall G AA aa e, dsubU G (trm_castup AA aa) e ->
  e = trm_top \/ (lc_trm AA /\ exists bb, e = trm_castup AA bb /\ dsubU G aa bb).
Proof.
  intros G AA aa e H. destruct (@dsub_lhs_castup G AA aa e (dsubU_dsub H)) as [He|[Hlc [bb [Heq Hd]]]].
  - left; exact He.
  - right. split; [exact Hlc|]. exists bb. split; [exact Heq|apply dsub_dsubU; exact Hd].
Qed.
Lemma dsubU_lhs_castdn : forall G aa e, dsubU G (trm_castdn aa) e ->
  e = trm_top \/ exists bb, e = trm_castdn bb /\ dsubU G aa bb.
Proof.
  intros G aa e H. destruct (@dsub_lhs_castdn G aa e (dsubU_dsub H)) as [He|[bb [Heq Hd]]].
  - left; exact He.
  - right. exists bb. split; [exact Heq|apply dsub_dsubU; exact Hd].
Qed.

(* local-closure destructors for binders *)
Lemma lc_trm_abs_inv : forall e A b, lc_trm (trm_abs e A b) ->
  lc_trm e /\ lc_trm A /\ (forall x, lc_trm (b ^ x)).
Proof.
  intros e A b H.
  assert (Hr : lc_rec 0 (trm_abs e A b)) by (apply lc_trm_lc_rec; exact H).
  simpl in Hr. destruct Hr as [He [HA Hb]].
  split; [apply lc_rec_0_lc_trm; exact He|]. split; [apply lc_rec_0_lc_trm; exact HA|].
  intros x. apply lc_rec_0_lc_trm.
  unfold open_trm_wrt_trm. apply lc_rec_open.
  - simpl. constructor.
  - exact Hb.
Qed.

Lemma lc_trm_prod_inv : forall e A b, lc_trm (trm_prod e A b) ->
  lc_trm e /\ lc_trm A /\ (forall x, lc_trm (b ^ x)).
Proof.
  intros e A b H.
  assert (Hr : lc_rec 0 (trm_prod e A b)) by (apply lc_trm_lc_rec; exact H).
  simpl in Hr. destruct Hr as [He [HA Hb]].
  split; [apply lc_rec_0_lc_trm; exact He|]. split; [apply lc_rec_0_lc_trm; exact HA|].
  intros x. apply lc_rec_0_lc_trm.
  unfold open_trm_wrt_trm. apply lc_rec_open.
  - simpl. constructor.
  - exact Hb.
Qed.

(* right-shape inversion for dsub *)
Lemma dsub_rhs_var_gen : forall G e1 e2, dsub G e1 e2 -> forall xx, e2 = trm_var_f xx ->
  e1 = trm_var_f xx \/
  exists y e1' A, e1 = trm_var_f y /\ binds y (bind_sub e1' A) G /\ dsub G e1' (trm_var_f xx).
Proof.
  intros G e1 e2 H. induction H; intros xx Heq; try discriminate Heq.
  - (* var_refl *) left. injection Heq as Heq. subst. reflexivity.
  - (* var_trans *) right. eexists. eexists. eexists. split; [reflexivity|]. split; [exact H|].
    inversion Heq. subst e2. exact H0.
Qed.

Lemma dsub_rhs_var : forall G e xx, dsub G e (trm_var_f xx) ->
  e = trm_var_f xx \/
  exists y e1 A, e = trm_var_f y /\ binds y (bind_sub e1 A) G /\ dsub G e1 (trm_var_f xx).
Proof. intros G e xx H. exact (dsub_rhs_var_gen H eq_refl). Qed.

(* remaining right-shape inversions for dsub *)
Lemma dsub_rhs_top_gen : forall G e1 e2, dsub G e1 e2 -> e2 = trm_top ->
  (ok G /\ lc_trm e1) \/
  exists y e1' A, e1 = trm_var_f y /\ binds y (bind_sub e1' A) G /\ dsub G e1' trm_top.
Proof.
  intros G e1 e2 H. induction H; intros Heq; try discriminate Heq.
  - (* var_trans *) right. eexists. eexists. eexists. split; [reflexivity|]. split; [exact H|].
    inversion Heq. subst e2. exact H0.
  - (* top *) left. split; assumption.
Qed.

Lemma dsub_rhs_top : forall G e, dsub G e trm_top ->
  (ok G /\ lc_trm e) \/
  exists y e1 A, e = trm_var_f y /\ binds y (bind_sub e1 A) G /\ dsub G e1 trm_top.
Proof. intros G e H. exact (dsub_rhs_top_gen H eq_refl). Qed.

Lemma dsub_rhs_abs_gen : forall G e1 e2, dsub G e1 e2 ->
  forall e3typ Atyp b0, e2 = trm_abs e3typ Atyp b0 ->
  (exists y e1' A', e1 = trm_var_f y /\ binds y (bind_sub e1' A') G /\
     dsub G e1' (trm_abs e3typ Atyp b0)) \/
  (ok G /\ exists L b', e1 = trm_abs e3typ Atyp b' /\
     (forall x, x \notin L -> dsub (G & x ~ bind_sub [#e3typ#] [#Atyp#]) (b' ^ x) (b0 ^ x))).
Proof.
  intros G e1 e2 H. induction H; intros e3typ Atyp b0 Heq; try discriminate Heq.
  - (* var_trans *) left. eexists. eexists. eexists. split; [reflexivity|]. split; [exact H|].
    inversion Heq. subst e2. exact H0.
  - (* lam *) inversion Heq; subst. right. split; [exact H|]. eexists. eexists. split; [reflexivity|].
    exact H0.
Qed.

Lemma dsub_rhs_abs : forall G e3 A b e, dsub G e (trm_abs e3 A b) ->
  (exists y e1' A', e = trm_var_f y /\ binds y (bind_sub e1' A') G /\
     dsub G e1' (trm_abs e3 A b)) \/
  (ok G /\ exists L b', e = trm_abs e3 A b' /\
     (forall x, x \notin L -> dsub (G & x ~ bind_sub [#e3#] [#A#]) (b' ^ x) (b ^ x))).
Proof. intros G e3 A b e H. exact (dsub_rhs_abs_gen H eq_refl). Qed.

Lemma dsub_rhs_app_gen : forall G e1 e2, dsub G e1 e2 ->
  forall a0 AA, e2 = trm_app a0 AA ->
  (exists y e1' A', e1 = trm_var_f y /\ binds y (bind_sub e1' A') G /\ dsub G e1' (trm_app a0 AA)) \/
  (lc_trm AA /\ exists f, e1 = trm_app f AA /\ dsub G f a0).
Proof.
  intros G e1 e2 H. induction H; intros a0 AA Heq; try discriminate Heq.
  - (* var_trans *) left. eexists. eexists. eexists. split; [reflexivity|]. split; [exact H|].
    inversion Heq. subst e2. exact H0.
  - (* app *) inversion Heq; subst. right. split; [exact H|]. eexists. split; [reflexivity|exact H0].
Qed.

Lemma dsub_rhs_app : forall G a A e, dsub G e (trm_app a A) ->
  (exists y e1' A', e = trm_var_f y /\ binds y (bind_sub e1' A') G /\ dsub G e1' (trm_app a A)) \/
  (lc_trm A /\ exists f, e = trm_app f A /\ dsub G f a).
Proof. intros G a A e H. exact (dsub_rhs_app_gen H eq_refl). Qed.

Lemma dsub_rhs_prod_gen : forall G e1 e2, dsub G e1 e2 ->
  forall e3t Ct Dt, e2 = trm_prod e3t Ct Dt ->
  (exists y e1' A', e1 = trm_var_f y /\ binds y (bind_sub e1' A') G /\ dsub G e1' (trm_prod e3t Ct Dt)) \/
  (exists L A B, e1 = trm_prod e3t A B /\ dsub G Ct A /\
     (forall x, x \notin L -> dsub (G & x ~ bind_sub [#e3t#] [#Ct#]) (B ^ x) (Dt ^ x))).
Proof.
  intros G e1 e2 H. induction H; intros e3t Ct Dt Heq; try discriminate Heq.
  - (* var_trans *) left. eexists. eexists. eexists. split; [reflexivity|]. split; [exact H|].
    inversion Heq. subst e2. exact H0.
  - (* pi *) inversion Heq; subst. right. eexists. eexists. eexists. split; [reflexivity|].
    split; [exact H|exact H0].
Qed.

Lemma dsub_rhs_prod : forall G e3 C D e, dsub G e (trm_prod e3 C D) ->
  (exists y e1' A', e = trm_var_f y /\ binds y (bind_sub e1' A') G /\ dsub G e1' (trm_prod e3 C D)) \/
  (exists L A B, e = trm_prod e3 A B /\ dsub G C A /\
     (forall x, x \notin L -> dsub (G & x ~ bind_sub [#e3#] [#C#]) (B ^ x) (D ^ x))).
Proof. intros G e3 C D e H. exact (dsub_rhs_prod_gen H eq_refl). Qed.

Lemma dsub_rhs_castup_gen : forall G e1 e2, dsub G e1 e2 ->
  forall A0 a, e2 = trm_castup A0 a ->
  (exists y e1' A', e1 = trm_var_f y /\ binds y (bind_sub e1' A') G /\ dsub G e1' (trm_castup A0 a)) \/
  (lc_trm A0 /\ exists f, e1 = trm_castup A0 f /\ dsub G f a).
Proof.
  intros G e1 e2 H. induction H; intros A0 a Heq; try discriminate Heq.
  - (* var_trans *) left. eexists. eexists. eexists. split; [reflexivity|]. split; [exact H|].
    inversion Heq. subst e2. exact H0.
  - (* castup *) inversion Heq; subst. right. split; [exact H|]. eexists. split; [reflexivity|exact H0].
Qed.

Lemma dsub_rhs_castup : forall G A0 a e, dsub G e (trm_castup A0 a) ->
  (exists y e1' A', e = trm_var_f y /\ binds y (bind_sub e1' A') G /\ dsub G e1' (trm_castup A0 a)) \/
  (lc_trm A0 /\ exists f, e = trm_castup A0 f /\ dsub G f a).
Proof. intros G A0 a e H. exact (dsub_rhs_castup_gen H eq_refl). Qed.

Lemma dsub_rhs_castdn_gen : forall G e1 e2, dsub G e1 e2 ->
  forall a, e2 = trm_castdn a ->
  (exists y e1' A', e1 = trm_var_f y /\ binds y (bind_sub e1' A') G /\ dsub G e1' (trm_castdn a)) \/
  (exists f, e1 = trm_castdn f /\ dsub G f a).
Proof.
  intros G e1 e2 H. induction H; intros a Heq; try discriminate Heq.
  - (* var_trans *) left. eexists. eexists. eexists. split; [reflexivity|]. split; [exact H|].
    inversion Heq. subst e2. exact H0.
  - (* castdn *) inversion Heq; subst. right. eexists. split; [reflexivity|assumption].
Qed.

Lemma dsub_rhs_castdn : forall G a e, dsub G e (trm_castdn a) ->
  (exists y e1' A', e = trm_var_f y /\ binds y (bind_sub e1' A') G /\ dsub G e1' (trm_castdn a)) \/
  (exists f, e = trm_castdn f /\ dsub G f a).
Proof. intros G a e H. exact (dsub_rhs_castdn_gen H eq_refl). Qed.

(* combined-system right-shape transfers *)
Lemma dsubU_rhs_star : forall G e, dsubU G e trm_star -> e = trm_star \/
  exists x e1 A, e = trm_var_f x /\ binds x (bind_sub e1 A) G /\ dsubU G e1 trm_star.
Proof.
  intros G e H. destruct (@dsub_rhs_star G e (dsubU_dsub H)) as [He|[x [e1 [A [Hv [Hd Heq]]]]]].
  - left; exact He.
  - right. exists x,e1,A. split; [exact Hv|]. split; [exact Hd|apply dsub_dsubU; exact Heq].
Qed.
Lemma dsubU_rhs_var : forall G e x, dsubU G e (trm_var_f x) ->
  e = trm_var_f x \/
  exists y e1 A, e = trm_var_f y /\ binds y (bind_sub e1 A) G /\ dsubU G e1 (trm_var_f x).
Proof.
  intros G e x H. destruct (@dsub_rhs_var G e x (dsubU_dsub H)) as [He|[y [e1 [A [Hv [Hd Heq]]]]]].
  - left; exact He.
  - right. exists y,e1,A. split; [exact Hv|]. split; [exact Hd|apply dsub_dsubU; exact Heq].
Qed.
Lemma dsubU_rhs_top : forall G e, dsubU G e trm_top ->
  (ok G /\ lc_trm e) \/
  exists y e1 A, e = trm_var_f y /\ binds y (bind_sub e1 A) G /\ dsubU G e1 trm_top.
Proof.
  intros G e H. destruct (@dsub_rhs_top G e (dsubU_dsub H)) as [[Hok Hlc]|[y [e1 [A [Hv [Hd Heq]]]]]].
  - left; split; assumption.
  - right. exists y,e1,A. split; [exact Hv|]. split; [exact Hd|apply dsub_dsubU; exact Heq].
Qed.
Lemma dsubU_rhs_app : forall G a A e, dsubU G e (trm_app a A) ->
  (exists y e1 A', e = trm_var_f y /\ binds y (bind_sub e1 A') G /\ dsubU G e1 (trm_app a A)) \/
  (lc_trm A /\ exists f, e = trm_app f A /\ dsubU G f a).
Proof.
  intros G a A e H. destruct (@dsub_rhs_app G a A e (dsubU_dsub H)) as [[y [e1 [A' [Hv [Hd Heq]]]]]|[Hlc [f [Heq Hd]]]].
  - left. exists y,e1,A'. split; [exact Hv|]. split; [exact Hd|apply dsub_dsubU; exact Heq].
  - right. split; [exact Hlc|]. exists f. split; [exact Heq|apply dsub_dsubU; exact Hd].
Qed.
Lemma dsubU_rhs_prod : forall G e3 C D e, dsubU G e (trm_prod e3 C D) ->
  (exists y e1 A', e = trm_var_f y /\ binds y (bind_sub e1 A') G /\ dsubU G e1 (trm_prod e3 C D)) \/
  (exists L A B, e = trm_prod e3 A B /\ dsubU G C A /\
    (forall x, x \notin L -> dsubU (G & x ~ bind_sub [#e3#] [#C#]) (B ^ x) (D ^ x))).
Proof.
  intros G e3 C D e H. destruct (@dsub_rhs_prod G e3 C D e (dsubU_dsub H)) as [[y [e1 [A' [Hv [Hd Heq]]]]]|[L [A [B [Heq [Hd Hbody]]]]]].
  - left. exists y,e1,A'. split; [exact Hv|]. split; [exact Hd|apply dsub_dsubU; exact Heq].
  - right. exists L,A,B. split; [exact Heq|]. split; [apply dsub_dsubU; exact Hd|]. intros x Hx. apply dsub_dsubU. apply Hbody. exact Hx.
Qed.

(* combined-system cast right-shape transfers *)
Lemma dsubU_rhs_castup : forall G A0 a e, dsubU G e (trm_castup A0 a) ->
  (exists y e1 A, e = trm_var_f y /\ binds y (bind_sub e1 A) G /\ dsubU G e1 (trm_castup A0 a)) \/
  (lc_trm A0 /\ exists f, e = trm_castup A0 f /\ dsubU G f a).
Proof.
  intros G A0 a e H. destruct (@dsub_rhs_castup G A0 a e (dsubU_dsub H)) as [[y [e1 [A [Hv [Hd Heq]]]]]|[Hlc [f [Heq Hd]]]].
  - left. exists y,e1,A. split; [exact Hv|]. split; [exact Hd|apply dsub_dsubU; exact Heq].
  - right. split; [exact Hlc|]. exists f. split; [exact Heq|apply dsub_dsubU; exact Hd].
Qed.
Lemma dsubU_rhs_castdn : forall G a e, dsubU G e (trm_castdn a) ->
  (exists y e1 A, e = trm_var_f y /\ binds y (bind_sub e1 A) G /\ dsubU G e1 (trm_castdn a)) \/
  (exists f, e = trm_castdn f /\ dsubU G f a).
Proof.
  intros G a e H. destruct (@dsub_rhs_castdn G a e (dsubU_dsub H)) as [[y [e1 [A [Hv [Hd Heq]]]]]|[f [Heq Hd]]].
  - left. exists y,e1,A. split; [exact Hv|]. split; [exact Hd|apply dsub_dsubU; exact Heq].
  - right. exists f. split; [exact Heq|apply dsub_dsubU; exact Hd].
Qed.

(* fresh-binder presentation of dsub for structural composition proofs *)
Inductive dsubR : env -> trm -> trm -> Prop :=
  | dr_star : forall G, ok G -> dsubR G trm_star trm_star
  | dr_var_refl : forall G x e A,
      ok G -> binds x (bind_sub e A) G -> dsubR G (trm_var_f x) (trm_var_f x)
  | dr_var_trans : forall e1 A G x e2,
      binds x (bind_sub e1 A) G -> dsubR G e1 e2 ->
      dsubR G (trm_var_f x) e2
  | dr_top : forall G e,
      ok G -> lc_trm e -> dsubR G e trm_top
  | dr_lam : forall G x e3 A e1 e2,
      ok G -> x # G -> x \notin fv_in_values fv_binding G ->
      x \notin fv_trm e3 -> x \notin fv_trm A ->
      x \notin fv_trm e1 -> x \notin fv_trm e2 ->
      dsubR (G & x ~ bind_sub [#e3#] [#A#]) (e1 ^ x) (e2 ^ x) ->
      dsubR G (trm_abs e3 A e1) (trm_abs e3 A e2)
  | dr_app : forall G e1 e2 A,
      lc_trm A -> dsubR G e1 e2 -> dsubR G (trm_app e1 A) (trm_app e2 A)
  | dr_pi : forall G x e A B C D,
      x # G -> x \notin fv_in_values fv_binding G ->
      x \notin fv_trm e -> x \notin fv_trm C ->
      x \notin fv_trm B -> x \notin fv_trm D ->
      dsubR G C A ->
      dsubR (G & x ~ bind_sub [#e#] [#C#]) (B ^ x) (D ^ x) ->
      dsubR G (trm_prod e A B) (trm_prod e C D)
  | dr_castup : forall G A e1 e2,
      lc_trm A -> dsubR G e1 e2 -> dsubR G (trm_castup A e1) (trm_castup A e2)
  | dr_castdn : forall G e1 e2,
      dsubR G e1 e2 -> dsubR G (trm_castdn e1) (trm_castdn e2).

(* basic inversion for the fresh-binder dsub presentation *)
Lemma dsubR_lhs_star_gen : forall G e1 e2, dsubR G e1 e2 -> e1 = trm_star -> e2 = trm_star \/ e2 = trm_top.
Proof.
  intros G e1 e2 H. induction H; intros Heq; try discriminate Heq.
  - left. reflexivity.
  - right. reflexivity.
Qed.
Lemma dsubR_lhs_star : forall G e, dsubR G trm_star e -> e = trm_star \/ e = trm_top.
Proof. intros G e H. exact (dsubR_lhs_star_gen H eq_refl). Qed.

(* finite-support renaming maps and basic commutation *)
Fixpoint ren (f:var -> var) (e:trm) : trm :=
  match e with
  | trm_var_b i => trm_var_b i
  | trm_var_f x => trm_var_f (f x)
  | trm_star => trm_star
  | trm_top => trm_top
  | trm_app a b => trm_app (ren f a) (ren f b)
  | trm_abs a A b => trm_abs (ren f a) (ren f A) (ren f b)
  | trm_prod a A b => trm_prod (ren f a) (ren f A) (ren f b)
  | trm_castup A a => trm_castup (ren f A) (ren f a)
  | trm_castdn a => trm_castdn (ren f a)
  | trm_anno a A => trm_anno (ren f a) (ren f A)
  end.

Definition ren_binding (f:var -> var) (b:binding) : binding :=
  match b with bind_sub e A => bind_sub (ren f e) (ren f A) end.

Fixpoint ren_env (f:var -> var) (G:env) : env :=
  match G with
  | nil => nil
  | (y,b) :: G' => (f y, ren_binding f b) :: ren_env f G'
  end.

Lemma ren_remove_anno : forall f e, ren f [# e #] = [# ren f e #].
Proof.
  intros f e. induction e; simpl.
  - reflexivity. - reflexivity. - reflexivity. - reflexivity.
  - f_equal; assumption. - f_equal; assumption. - f_equal; assumption.
  - f_equal; assumption. - f_equal; assumption. - assumption.
Qed.

Lemma ren_open_rec : forall f k v e,
  ren f (open_trm_wrt_trm_rec k v e) =
  open_trm_wrt_trm_rec k (ren f v) (ren f e).
Proof.
  intros f k v e. revert k v. induction e; intros k0 v0; simpl.
  - destruct (classicT (k0 = n)) as [Heq|Hneq].
    + subst n. simpl. destruct (classicT (k0 = k0)) as [H|H]; [reflexivity|exfalso; apply H; reflexivity].
    + simpl. destruct (classicT (k0 = n)) as [H0|H0]; [congruence|reflexivity].
  - reflexivity. - reflexivity. - reflexivity.
  - f_equal; [apply IHe1|apply IHe2].
  - f_equal; [apply IHe1|apply IHe2|apply IHe3].
  - f_equal; [apply IHe1|apply IHe2|apply IHe3].
  - f_equal; [apply IHe1|apply IHe2].
  - f_equal; apply IHe.
  - f_equal; [apply IHe1|apply IHe2].
Qed.

Lemma ren_open : forall f v e,
  ren f (open_trm_wrt_trm e v) = open_trm_wrt_trm (ren f e) (ren f v).
Proof. intros. unfold open_trm_wrt_trm. apply ren_open_rec. Qed.

Lemma ren_open_var : forall f x e,
  ren f (e ^ x) = (ren f e) ^ (f x).
Proof. intros. unfold open_trm_wrt_trm. apply ren_open_rec. Qed.

Lemma ren_env_nil : forall f, ren_env f empty = empty.
Proof. intros. rewrite (empty_def binding). simpl. rewrite <- (empty_def binding). reflexivity. Qed.

Lemma ren_env_push : forall f (G:env) y b,
  ren_env f (G & y ~ b) = ren_env f G & f y ~ ren_binding f b.
Proof. intros. rewrite <- cons_eq_push. simpl. rewrite <- cons_eq_push. reflexivity. Qed.

(* renaming-map free-variable and closure lemmas *)
Lemma fv_ren_inv : forall f e y, y \in fv_trm (ren f e) ->
  exists x, f x = y /\ x \in fv_trm e.
Proof.
  intros f e. induction e; intros y Hy; simpl in *.
  - exfalso. exact (@in_empty_inv var y Hy).
  - rewrite in_singleton in Hy. subst y. exists x5. split; [reflexivity|apply in_singleton_self].
  - exfalso. exact (@in_empty_inv var y Hy).
  - exfalso. exact (@in_empty_inv var y Hy).
  - rewrite in_union in Hy. destruct Hy as [Hy|Hy].
    + destruct (IHe1 y Hy) as [x [Hf Hx]]. exists x. split; [exact Hf|].
      repeat rewrite in_union. tauto.
    + destruct (IHe2 y Hy) as [x [Hf Hx]]. exists x. split; [exact Hf|].
      repeat rewrite in_union. tauto.
  - rewrite in_union in Hy. destruct Hy as [Hy|Hy].
    + destruct (IHe1 y Hy) as [x [Hf Hx]]. exists x. split; [exact Hf|].
      repeat rewrite in_union. tauto.
    + rewrite in_union in Hy. destruct Hy as [Hy|Hy].
      * destruct (IHe2 y Hy) as [x [Hf Hx]]. exists x. split; [exact Hf|].
        repeat rewrite in_union. tauto.
      * destruct (IHe3 y Hy) as [x [Hf Hx]]. exists x. split; [exact Hf|].
        repeat rewrite in_union. tauto.
  - rewrite in_union in Hy. destruct Hy as [Hy|Hy].
    + destruct (IHe1 y Hy) as [x [Hf Hx]]. exists x. split; [exact Hf|].
      repeat rewrite in_union. tauto.
    + rewrite in_union in Hy. destruct Hy as [Hy|Hy].
      * destruct (IHe2 y Hy) as [x [Hf Hx]]. exists x. split; [exact Hf|].
        repeat rewrite in_union. tauto.
      * destruct (IHe3 y Hy) as [x [Hf Hx]]. exists x. split; [exact Hf|].
        repeat rewrite in_union. tauto.
  - rewrite in_union in Hy. destruct Hy as [Hy|Hy].
    + destruct (IHe1 y Hy) as [x [Hf Hx]]. exists x. split; [exact Hf|].
      repeat rewrite in_union. tauto.
    + destruct (IHe2 y Hy) as [x [Hf Hx]]. exists x. split; [exact Hf|].
      repeat rewrite in_union. tauto.
  - destruct (IHe y Hy) as [x [Hf Hx]]. exists x. split; [exact Hf|exact Hx].
  - rewrite in_union in Hy. destruct Hy as [Hy|Hy].
    + destruct (IHe1 y Hy) as [x [Hf Hx]]. exists x. split; [exact Hf|].
      repeat rewrite in_union. tauto.
    + destruct (IHe2 y Hy) as [x [Hf Hx]]. exists x. split; [exact Hf|].
      repeat rewrite in_union. tauto.
Qed.

Lemma notin_ren : forall f, (forall x y, f x = f y -> x = y) ->
  forall e x, x \notin fv_trm e -> f x \notin fv_trm (ren f e).
Proof.
  intros f Hinj e x Hx Hy.
  destruct (@fv_ren_inv f e (f x) Hy) as [z [Hf Hz]].
  apply Hx. assert (z = x) by (apply (Hinj z x); exact Hf). subst z. exact Hz.
Qed.

Lemma lc_rec_ren : forall e n f, lc_rec n e -> lc_rec n (ren f e).
Proof.
  intros e. induction e; intros n0 f H; simpl in *.
  - exact H. - exact I. - exact I. - exact I.
  - destruct H as [H1 H2]. split; [apply IHe1|apply IHe2]; assumption.
  - destruct H as [H1 [H2 H3]]. split; [apply IHe1; assumption|]. split; [apply IHe2; assumption|].
    apply (IHe3 (S n0) f). exact H3.
  - destruct H as [H1 [H2 H3]]. split; [apply IHe1; assumption|]. split; [apply IHe2; assumption|].
    apply (IHe3 (S n0) f). exact H3.
  - destruct H as [H1 H2]. split; [apply IHe1|apply IHe2]; assumption.
  - apply IHe. exact H.
  - destruct H as [H1 H2]. split; [apply IHe1|apply IHe2]; assumption.
Qed.

Lemma lc_trm_ren : forall e f, lc_trm e -> lc_trm (ren f e).
Proof.
  intros e f H. apply lc_rec_0_lc_trm. apply (@lc_rec_ren e 0 f). apply lc_trm_lc_rec. exact H.
Qed.

(* renaming-map environment lemmas *)
Lemma binds_ren_env : forall f, (forall x y, f x = f y -> x = y) ->
  forall G x b, binds x b G -> binds (f x) (ren_binding f b) (ren_env f G).
Proof.
  intros f Hinj G. induction G as [| [z c] G' IH]; intros x b Hb.
  - rewrite <- (empty_def binding) in Hb. exfalso. exact (@binds_empty_inv binding x b Hb).
  - rewrite cons_eq_push in Hb. rewrite cons_eq_push. rewrite ren_env_push.
    apply binds_push_inv in Hb as [[Heq Hb]|[Hneq Hb]].
    + inversion Heq. subst z c. apply binds_push_eq.
    + apply binds_push_neq; [apply IH; exact Hb|]. intro Hf. apply Hneq. apply (Hinj x z). exact Hf.
Qed.

Lemma binds_ren_env_inv : forall f, (forall x y, f x = f y -> x = y) ->
  forall G y c, binds y c (ren_env f G) ->
  exists x b, y = f x /\ c = ren_binding f b /\ binds x b G.
Proof.
  intros f Hinj G. induction G as [| [z b] G' IH]; intros y c Hb.
  - simpl in Hb. rewrite <- (empty_def binding) in Hb. exfalso. exact (@binds_empty_inv binding y c Hb).
  - rewrite cons_eq_push in Hb. rewrite ren_env_push in Hb.
    apply binds_push_inv in Hb as [[Heq Hb]|[Hneq Hb]].
    + inversion Heq. subst y c. exists z, b. split; [reflexivity|]. split; [reflexivity|]. rewrite cons_eq_push. apply binds_push_eq.
    + destruct (IH y c Hb) as [x [b' [Hy [Hc Hb']]]].
      exists x, b'. split; [exact Hy|]. split; [exact Hc|].
      rewrite cons_eq_push. apply binds_push_neq; [exact Hb'|].
      intro Hxz. apply Hneq. subst x. rewrite Hy. reflexivity.
Qed.

Lemma notin_dom_ren_env : forall f, (forall x y, f x = f y -> x = y) ->
  forall G x, x \notin dom G -> f x \notin dom (ren_env f G).
Proof.
  intros f Hinj G x Hx Hin.
  apply get_some in Hin as [c Hc]. apply get_binds in Hc.
  destruct (@binds_ren_env_inv f Hinj G (f x) c Hc) as [z [b [Hy [Hc' Hb]]]].
  apply Hx. assert (z = x) by (apply (Hinj z x); symmetry; exact Hy). subst z.
  eapply get_some_inv. apply binds_get. exact Hb.
Qed.

Lemma ok_ren_env : forall f, (forall x y, f x = f y -> x = y) ->
  forall G, ok G -> ok (ren_env f G).
Proof.
  intros f Hinj G Hok. induction Hok as [| E x v HE IH Hx].
  - rewrite ren_env_nil. apply ok_empty.
  - rewrite ren_env_push. apply ok_push; [exact IH|]. apply notin_dom_ren_env; [exact Hinj|exact Hx].
Qed.

Lemma ren_binding_erased : forall f e A,
  ren_binding f (bind_sub [#e#] [#A#]) = bind_sub [#ren f e#] [#ren f A#].
Proof. intros. simpl. rewrite ren_remove_anno. rewrite ren_remove_anno. reflexivity. Qed.

(* renaming for the fresh-binder dsub presentation *)
Lemma fv_in_values_cons_binding : forall (z:var) (b:binding) G,
  fv_in_values fv_binding ((z,b) :: G) = fv_binding b \u fv_in_values fv_binding G.
Proof.
  intros. unfold fv_in_values. rewrite values_def. rewrite LibList.map_cons.
  rewrite LibList.fold_right_cons. reflexivity.
Qed.

Lemma fv_binding_ren_inv : forall f b y,
  y \in fv_binding (ren_binding f b) -> exists x, f x = y /\ x \in fv_binding b.
Proof.
  intros f [e A] y H. simpl in *. rewrite in_union in H. destruct H as [H|H].
  - destruct (@fv_ren_inv f e y H) as [x [Hf Hx]]. exists x. split; [exact Hf|].
    repeat rewrite in_union. tauto.
  - destruct (@fv_ren_inv f A y H) as [x [Hf Hx]]. exists x. split; [exact Hf|].
    repeat rewrite in_union. tauto.
Qed.

Lemma notin_values_ren_env : forall f, (forall x y, f x = f y -> x = y) ->
  forall G x, x \notin fv_in_values fv_binding G ->
  f x \notin fv_in_values fv_binding (ren_env f G).
Proof.
  intros f Hinj G. induction G as [| [z b] G' IH]; intros x Hx.
  - intro H. unfold fv_in_values in H. rewrite values_def in H. simpl in H. exact (@in_empty_inv var (f x) H).
  - rewrite fv_in_values_cons_binding in Hx. apply notin_union_r in Hx as [Hxb HxG].
    simpl. rewrite fv_in_values_cons_binding.
    apply notin_union_l.
    + intro H. destruct (@fv_binding_ren_inv f b (f x) H) as [w [Hf Hw]].
      apply Hxb. assert (w = x) by (apply (Hinj w x); exact Hf). subst w. exact Hw.
    + apply IH. exact HxG.
Qed.
Lemma dsubR_ren : forall f, (forall x y, f x = f y -> x = y) ->
  forall G e1 e2, dsubR G e1 e2 -> dsubR (ren_env f G) (ren f e1) (ren f e2).
Proof.
  intros f Hinj G e1 e2 H. induction H; simpl.
  - apply dr_star. apply ok_ren_env; assumption.
  - eapply dr_var_refl with (e := ren f e) (A := ren f A).
    + apply ok_ren_env; assumption.
    + change (binds (f x) (ren_binding f (bind_sub e A)) (ren_env f G)). apply binds_ren_env; assumption.
  - eapply dr_var_trans with (e1 := ren f e1) (A := ren f A).
    + change (binds (f x) (ren_binding f (bind_sub e1 A)) (ren_env f G)). apply binds_ren_env; assumption.
    + exact IHdsubR.
  - apply dr_top.
    + apply ok_ren_env; assumption.
    + apply lc_trm_ren. assumption.
  - eapply dr_lam with (x := f x) (e3 := ren f e3) (A := ren f A)
      (e1 := ren f e1) (e2 := ren f e2).
    + apply ok_ren_env; assumption.
    + apply notin_dom_ren_env; assumption.
    + apply notin_values_ren_env; assumption.
    + apply notin_ren; assumption.
    + apply notin_ren; assumption.
    + apply notin_ren; assumption.
    + apply notin_ren; assumption.
    + rewrite ren_env_push in IHdsubR. rewrite ren_binding_erased in IHdsubR.
      rewrite ren_open_var in IHdsubR. rewrite ren_open_var in IHdsubR. exact IHdsubR.
  - apply dr_app.
    + apply lc_trm_ren. assumption.
    + exact IHdsubR.
  - eapply dr_pi with (x := f x) (e := ren f e) (A := ren f A) (B := ren f B)
      (C := ren f C) (D := ren f D).
    + apply notin_dom_ren_env; assumption.
    + apply notin_values_ren_env; assumption.
    + apply notin_ren; assumption.
    + apply notin_ren; assumption.
    + apply notin_ren; assumption.
    + apply notin_ren; assumption.
    + exact IHdsubR1.
    + rewrite ren_env_push in IHdsubR2. rewrite ren_binding_erased in IHdsubR2.
      rewrite ren_open_var in IHdsubR2. rewrite ren_open_var in IHdsubR2. exact IHdsubR2.
  - apply dr_castup.
    + apply lc_trm_ren. assumption.
    + exact IHdsubR.
  - apply dr_castdn. exact IHdsubR.
Qed.

(* variable swap map *)
Definition swap (x y:var) (z:var) : var :=
  match classicT (z = x) with left _ => y | right _ =>
    match classicT (z = y) with left _ => x | right _ => z end end.

Lemma swap_same_left : forall x y, x <> y -> swap x y x = y.
Proof. intros. unfold swap. rewrite (classicT_l (eq_refl x)). reflexivity. Qed.

Lemma swap_same_right : forall x y, x <> y -> swap x y y = x.
Proof. intros x y H. unfold swap. rewrite (classicT_r (fun Hxy => H (eq_sym Hxy))). rewrite (classicT_l (eq_refl y)). reflexivity. Qed.

Lemma swap_other : forall x y z, z <> x -> z <> y -> swap x y z = z.
Proof. intros. unfold swap. rewrite (classicT_r H). rewrite (classicT_r H0). reflexivity. Qed.

Lemma swap_invol : forall x y z, x <> y -> swap x y (swap x y z) = z.
Proof.
  intros x y z Hxy. destruct (classicT (z = x)) as [Hzx|Hzx].
  - subst z. rewrite swap_same_left; [|exact Hxy]. rewrite swap_same_right; [|exact Hxy]. reflexivity.
  - destruct (classicT (z = y)) as [Hzy|Hzy].
    + subst z. rewrite swap_same_right; [|exact Hxy]. rewrite swap_same_left; [|exact Hxy]. reflexivity.
    + assert (Hinner : swap x y z = z) by (apply swap_other; assumption).
      rewrite Hinner. apply swap_other; assumption.
Qed.

Lemma swap_inj : forall x y, x <> y -> forall a b, swap x y a = swap x y b -> a = b.
Proof.
  intros x y Hxy a b H.
  pose proof (f_equal (swap x y) H) as H2.
  rewrite (@swap_invol x y a Hxy) in H2. rewrite (@swap_invol x y b Hxy) in H2. exact H2.
Qed.

(* swap agrees with single-variable renaming on fresh terms *)
Lemma ren_swap_rename : forall x y e, x <> y -> y \notin fv_trm e ->
  ren (swap x y) e = rename x y e.
Proof.
  intros x y e Hxy Hy. induction e; simpl.
  - reflexivity.
  - unfold rename. simpl. destruct (classicT (x5 = x)) as [Heq|Hneq].
    + subst x5. rewrite swap_same_left; [|exact Hxy]. reflexivity.
    + destruct (classicT (x5 = y)) as [Hxy'|Hxy'].
      * exfalso. apply Hy. rewrite Hxy'. apply in_singleton_self.
      * rewrite swap_other; [|exact Hneq|exact Hxy']. reflexivity.
  - reflexivity. - reflexivity.
  - apply notin_union_r in Hy as [H1 H2].
    change (trm_app (ren (swap x y) e1) (ren (swap x y) e2) =
            trm_app (rename x y e1) (rename x y e2)).
    rewrite (IHe1 H1). rewrite (IHe2 H2). reflexivity.
  - apply notin_union_r in Hy as [H1 H2]. apply notin_union_r in H2 as [H2a H2b].
    change (trm_abs (ren (swap x y) e1) (ren (swap x y) e2) (ren (swap x y) e3) =
            trm_abs (rename x y e1) (rename x y e2) (rename x y e3)).
    rewrite (IHe1 H1). rewrite (IHe2 H2a). rewrite (IHe3 H2b). reflexivity.
  - apply notin_union_r in Hy as [H1 H2]. apply notin_union_r in H2 as [H2a H2b].
    change (trm_prod (ren (swap x y) e1) (ren (swap x y) e2) (ren (swap x y) e3) =
            trm_prod (rename x y e1) (rename x y e2) (rename x y e3)).
    rewrite (IHe1 H1). rewrite (IHe2 H2a). rewrite (IHe3 H2b). reflexivity.
  - apply notin_union_r in Hy as [H1 H2].
    change (trm_castup (ren (swap x y) e1) (ren (swap x y) e2) =
            trm_castup (rename x y e1) (rename x y e2)).
    rewrite (IHe1 H1). rewrite (IHe2 H2). reflexivity.
  - change (trm_castdn (ren (swap x y) e) = trm_castdn (rename x y e)).
    rewrite (IHe Hy). reflexivity.
  - apply notin_union_r in Hy as [H1 H2].
    change (trm_anno (ren (swap x y) e1) (ren (swap x y) e2) =
            trm_anno (rename x y e1) (rename x y e2)).
    rewrite (IHe1 H1). rewrite (IHe2 H2). reflexivity.
Qed.

(* swap agrees with rename on fresh bindings and environments *)
Lemma ren_binding_swap_rename : forall x y b, x <> y ->
  y \notin fv_binding b ->
  ren_binding (swap x y) b = rename_binding x y b.
Proof.
  intros x y [e A] Hxy Hy. simpl in *. apply notin_union_r in Hy as [Hye HyA].
  unfold ren_binding, rename_binding. simpl.
  f_equal; [apply ren_swap_rename|apply ren_swap_rename]; auto.
Qed.

Lemma ren_env_swap_rename : forall G x y, x <> y ->
  y \notin fv_in_values fv_binding G -> y # G ->
  ren_env (swap x y) G = rename_env x y G.
Proof.
  intros G. induction G as [| [z b] G' IH]; intros x y Hxy Hyval Hy.
  - reflexivity.
  - rewrite cons_eq_push in Hy. rewrite dom_push in Hy.
    apply notin_union_r in Hy as [Hyz HyG].
    apply notin_singleton_r in Hyz.
    unfold fv_in_values in Hyval. rewrite values_def in Hyval.
    rewrite LibList.map_cons in Hyval. rewrite LibList.fold_right_cons in Hyval.
    apply notin_union_r in Hyval as [Hyb HyvalG].
    rewrite <- values_def in HyvalG.
    rewrite cons_eq_push. rewrite ren_env_push. rewrite rename_env_push.
    assert (Hb : ren_binding (swap x y) b = rename_binding x y b).
    { apply ren_binding_swap_rename; [exact Hxy|exact Hyb]. }
    rewrite Hb.
    destruct (classicT (z = x)) as [Hz|Hz].
    + subst z. rewrite (swap_same_left Hxy). rewrite (IH x y Hxy HyvalG HyG). reflexivity.
    + rewrite (swap_other Hz (fun Hzy => Hyz (eq_sym Hzy))). rewrite (IH x y Hxy HyvalG HyG). reflexivity.
Qed.

(* single-variable renaming for dsubR *)
Lemma dsubR_rename : forall G e1 e2, dsubR G e1 e2 ->
  forall x y, x <> y -> y # G -> y \notin fv_in_values fv_binding G ->
  y \notin fv_trm e1 -> y \notin fv_trm e2 ->
  dsubR (rename_env x y G) (rename x y e1) (rename x y e2).
Proof.
  intros G e1 e2 H x y Hxy Hy Hyval Hfe1 Hfe2.
  pose proof (@dsubR_ren (swap x y) (swap_inj Hxy) G e1 e2 H) as Hr.
  rewrite (@ren_env_swap_rename G x y Hxy Hyval Hy) in Hr.
  rewrite (@ren_swap_rename x y e1 Hxy Hfe1) in Hr.
  rewrite (@ren_swap_rename x y e2 Hxy Hfe2) in Hr.
  exact Hr.
Qed.

(* freshness of binding values under renaming *)

(* dsubR embeds into dsub *)
Lemma rename_var_same : forall x y, rename x y (trm_var_f x) = trm_var_f y.
Proof.
  intros. unfold rename. simpl. destruct (classicT (x = x)) as [H|H]; [reflexivity|exfalso; apply H; reflexivity].
Qed.

Lemma dsubR_dsub : forall G e1 e2, dsubR G e1 e2 -> dsub G e1 e2.
Proof.
  intros G e1 e2 H. induction H.
  - exact (dsub_star H).
  - exact (dsub_var_refl H H0).
  - exact (dsub_var_trans H IHdsubR).
  - exact (dsub_top H H0).
  - (* lam *) set (L := union (dom G) (union (singleton x) (union (fv_in_values fv_binding G) (union (fv_trm e3) (union (fv_trm A) (union (fv_trm e1) (fv_trm e2))))))).
    eapply dsub_lam with (L := L).
    + exact H.
    + intros y Hy. unfold L in Hy.
      apply notin_union_r in Hy as [HyG Hy].
      apply notin_union_r in Hy as [Hyx Hy].
      apply notin_union_r in Hy as [Hyv Hy].
      apply notin_union_r in Hy as [Hye3 Hy].
      apply notin_union_r in Hy as [HyA Hy].
      apply notin_union_r in Hy as [Hye1 Hye2].
      apply notin_singleton_r in Hyx.
      set (b := bind_sub [#e3#] [#A#]).
      assert (Hxy : x <> y) by (intro He; apply Hyx; symmetry; exact He).
      assert (HyE : y # (G & x ~ b)) by (rewrite dom_push; apply notin_union_l; [apply notin_singleton_l; exact Hyx|exact HyG]).
      pose proof (@dsub_rename (G & x ~ b) (e1 ^ x) (e2 ^ x) x y Hxy HyE IHdsubR) as Hren.
      unfold b in Hren. rewrite rename_env_push in Hren.
      assert (Henv : rename_env x y G = G).
      { exact (@rename_env_id G x y H0 HyG H1 Hyv). }
      (* x # G is Hx, x notin values Hxval *)
      rewrite Henv in Hren.
      assert (Hrb : rename_binding x y (bind_sub [#e3#] [#A#]) = bind_sub [#e3#] [#A#]).
      { apply rename_binding_id.
        - simpl. apply notin_union_l; [apply fv_remove_anno_notin; exact H2|apply fv_remove_anno_notin; exact H3].
        - simpl. apply notin_union_l; [apply fv_remove_anno_notin; exact Hye3|apply fv_remove_anno_notin; exact HyA]. }
      rewrite Hrb in Hren.
      rewrite (classicT_l (eq_refl x)) in Hren.
      rewrite (rename_open' x y (trm_var_f x) e1) in Hren.
      rewrite (rename_open' x y (trm_var_f x) e2) in Hren.
      simpl in Hren.
      rewrite (@rename_trm_id x y e1 H4 Hye1) in Hren.
      rewrite (@rename_trm_id x y e2 H5 Hye2) in Hren.
      rewrite (rename_var_same x y) in Hren. exact Hren.
  - apply dsub_app; [exact H|exact IHdsubR].
  - (* pi *) set (L := union (dom G) (union (singleton x) (union (fv_in_values fv_binding G) (union (fv_trm e) (union (fv_trm C) (union (fv_trm B) (fv_trm D))))))).
    eapply dsub_pi with (L := L).
    + exact IHdsubR1.
    + intros y Hy. unfold L in Hy.
      apply notin_union_r in Hy as [HyG Hy].
      apply notin_union_r in Hy as [Hyx Hy].
      apply notin_union_r in Hy as [Hyv Hy].
      apply notin_union_r in Hy as [Hye Hy].
      apply notin_union_r in Hy as [HyC Hy].
      apply notin_union_r in Hy as [HyB HyD].
      apply notin_singleton_r in Hyx.
      set (b := bind_sub [#e#] [#C#]).
      assert (Hxy : x <> y) by (intro He; apply Hyx; symmetry; exact He).
      assert (HyE : y # (G & x ~ b)) by (rewrite dom_push; apply notin_union_l; [apply notin_singleton_l; exact Hyx|exact HyG]).
      pose proof (@dsub_rename (G & x ~ b) (B ^ x) (D ^ x) x y Hxy HyE IHdsubR2) as Hren.
      unfold b in Hren. rewrite rename_env_push in Hren.
      assert (Henv : rename_env x y G = G).
      { exact (@rename_env_id G x y H HyG H0 Hyv). }
      rewrite Henv in Hren.
      assert (Hrb : rename_binding x y (bind_sub [#e#] [#C#]) = bind_sub [#e#] [#C#]).
      { apply rename_binding_id.
        - simpl. apply notin_union_l; [apply fv_remove_anno_notin; exact H1|apply fv_remove_anno_notin; exact H2].
        - simpl. apply notin_union_l; [apply fv_remove_anno_notin; exact Hye|apply fv_remove_anno_notin; exact HyC]. }
      rewrite Hrb in Hren.
      rewrite (classicT_l (eq_refl x)) in Hren.
      rewrite (rename_open' x y (trm_var_f x) B) in Hren.
      rewrite (rename_open' x y (trm_var_f x) D) in Hren.
      simpl in Hren.
      rewrite (rename_var_same x y) in Hren.
      rewrite (@rename_trm_id x y B H3 HyB) in Hren.
      rewrite (@rename_trm_id x y D H4 HyD) in Hren.
      exact Hren.
  - apply dsub_castup; [exact H|exact IHdsubR].
  - apply dsub_castdn. exact IHdsubR.
Qed.


(* dsub embeds into dsubR *)
Lemma dsub_dsubR : forall G e1 e2, dsub G e1 e2 -> dsubR G e1 e2.
Proof.
  intros G e1 e2 H. induction H.
  - exact (dr_star H).
  - exact (dr_var_refl H H0).
  - exact (dr_var_trans H IHdsub).
  - exact (dr_top H H0).
  - (* lam *) set (Lf := union L (union (dom G) (union (fv_in_values fv_binding G) (union (fv_trm e3) (union (fv_trm A) (union (fv_trm e1) (fv_trm e2))))))).
    pick_fresh_gen Lf x.
    unfold Lf in Fr. apply notin_union_r in Fr as [HxL Fr].
    apply notin_union_r in Fr as [HxG Fr].
    apply notin_union_r in Fr as [Hxval Fr].
    apply notin_union_r in Fr as [Hxe3 Fr].
    apply notin_union_r in Fr as [HxA Fr].
    apply notin_union_r in Fr as [Hxe1 Hxe2].
    eapply dr_lam with (x := x); [exact H|exact HxG|exact Hxval|exact Hxe3|exact HxA|exact Hxe1|exact Hxe2|].
    apply H1. exact HxL.
  - exact (dr_app H IHdsub).
  - (* pi *) set (Lf := union L (union (dom G) (union (fv_in_values fv_binding G) (union (fv_trm e) (union (fv_trm C) (union (fv_trm B) (fv_trm D))))))).
    pick_fresh_gen Lf x.
    unfold Lf in Fr. apply notin_union_r in Fr as [HxL Fr].
    apply notin_union_r in Fr as [HxG Fr].
    apply notin_union_r in Fr as [Hxval Fr].
    apply notin_union_r in Fr as [Hxe Fr].
    apply notin_union_r in Fr as [HxC Fr].
    apply notin_union_r in Fr as [HxB HxD].
    eapply dr_pi with (x := x); [exact HxG|exact Hxval|exact Hxe|exact HxC|exact HxB|exact HxD|exact IHdsub|].
    apply H1. exact HxL.
  - exact (dr_castup H IHdsub).
  - exact (dr_castdn IHdsub).
Qed.
(* ============================================================ *)

Definition Psub (G : env) (e1 e2 A : trm) : Prop :=
  dsub G e1 e2 /\
  exists e1' e2',
    dtyping inf G e1' A /\ dtyping inf G e2' A /\
    [# e1' #] = e1 /\ [# e2' #] = e2.

Definition Pwf (G : env) : Prop := dwf G.

(* Support set used by the closing lemma. *)
Definition fam_bound (G : env) (P Q : trm) (L : vars) (b T : trm) : vars :=
  union (union (union (union (union (union L (dom G))
          (fv_in_values fv_binding G)) (fv_trm P)) (fv_trm Q)) (fv_trm b)) (fv_trm T).

(* ============================================================ *)
(* Basic helpers                                                *)
(* ============================================================ *)

Lemma mk_Psub : forall G e1 e2 A e1' e2',
  dsub G e1 e2 ->
  dtyping inf G e1' A ->
  dtyping inf G e2' A ->
  [# e1' #] = e1 ->
  [# e2' #] = e2 ->
  Psub G e1 e2 A.
Proof.
  intros. unfold Psub. split; [assumption|].
  exists e1'. exists e2'. repeat split; assumption.
Qed.

Lemma dwf_bind_sub_Et : forall G x e A,
  dwf (G & x ~ bind_sub e A) -> Et e /\ Et A.
Proof.
  intros G x e A H.
  apply (@dwf_binds_Et (G & x ~ bind_sub e A) x e A H).
  apply binds_push_eq.
Qed.

Lemma lc_erase_of_inf : forall G e A,
  dtyping inf G e A -> lc_trm [# e #].
Proof.
  intros G e A H.
  assert (Hdwf : dwf G) by (exact (@dtyping_dwf inf G e A H)).
  assert (HlcE : lc_env G) by (apply dwf_lc_env; exact Hdwf).
  destruct (@dtyping_lc inf G e A H HlcE) as [Hlc _].
  apply lc_trm_remove_anno. exact Hlc.
Qed.

Lemma dtyping_anno_sub : forall G e A0 z,
  dtyping inf G e A0 ->
  dsub G A0 [# z #] ->
  dtyping chk G z trm_star ->
  dtyping inf G (trm_anno e z) [# z #].
Proof.
  intros G e A0 z Hinf Hsub Hchk.
  apply dtyping_anno.
  - apply dtyping_sub with (A := A0); assumption.
  - exact Hchk.
Qed.

Lemma inf_top_wit :
  (forall G e A,
     dtyping inf G e A -> exists X, dtyping inf G X trm_star /\ [# X #] = A) ->
  forall G e A, dtyping inf G e A ->
    exists T, dtyping inf G T A /\ [# T #] = trm_top.
Proof.
  intros SW G e A H.
  destruct (SW G e A H) as [X [HX HeX]].
  exists (trm_anno trm_top X). split.
  - rewrite <- HeX.
    apply dtyping_anno.
    + apply dtyping_top. apply dtyping_chk. exact HX.
    + apply dtyping_chk. exact HX.
  - simpl. reflexivity.
Qed.

(* ============================================================ *)
(* Closing a family of open typed witnesses                     *)
(* ============================================================ *)

Lemma close_inf_family : forall (G : env) (P Q : trm) (L : vars) (b T : trm),
  (forall x, x \notin L ->
     exists Y,
       dtyping inf (G & x ~ bind_sub P Q) Y (T ^ x) /\
       [# Y #] = b ^ x) ->
  exists Y,
    [# Y #] = b /\
    forall x, x \notin fam_bound G P Q L b T ->
      dtyping inf (G & x ~ bind_sub P Q) (Y ^ x) (T ^ x).
Proof.
  intros G P Q L b T Hfam.
  pick_fresh_gen (fam_bound G P Q L b T) x0.
  unfold fam_bound in Fr.
  apply notin_union_r in Fr as [Fr1 Hx0T].
  apply notin_union_r in Fr1 as [Fr2 Hx0b].
  apply notin_union_r in Fr2 as [Fr3 Hx0Q].
  apply notin_union_r in Fr3 as [Fr4 Hx0P].
  apply notin_union_r in Fr4 as [Fr5 Hx0vals].
  apply notin_union_r in Fr5 as [Hx0L Hx0G].
  destruct (Hfam x0 Hx0L) as [Y0 [HY0 HeY0]].
  assert (Hdwf0 : dwf (G & x0 ~ bind_sub P Q))
    by (exact (@dtyping_dwf inf (G & x0 ~ bind_sub P Q) Y0 (T ^ x0) HY0)).
  assert (HlcE0 : lc_env (G & x0 ~ bind_sub P Q)) by (apply dwf_lc_env; exact Hdwf0).
  destruct (@dtyping_lc inf (G & x0 ~ bind_sub P Q) Y0 (T ^ x0) HY0 HlcE0) as [HlcY0 _].
  assert (HlcRec : lc_rec 0 Y0) by (apply lc_trm_lc_rec; exact HlcY0).
  set (Y := close_rec x0 0 Y0).
  exists Y. split.
  - unfold Y. rewrite remove_anno_close. rewrite HeY0.
    exact (@open_close x0 0 b Hx0b).
  - intros y Hy.
    unfold fam_bound in Hy.
    apply notin_union_r in Hy as [Hy1 HyT].
    apply notin_union_r in Hy1 as [Hy2 Hyb].
    apply notin_union_r in Hy2 as [Hy3 HyQ].
    apply notin_union_r in Hy3 as [Hy4 HyP].
    apply notin_union_r in Hy4 as [Hy5 Hyvals].
    apply notin_union_r in Hy5 as [HyL HyG].
    destruct (classicT (y = x0)) as [Heq|Hneq].
    + subst y. unfold Y. unfold open_trm_wrt_trm.
      rewrite (@close_open x0 0 Y0 HlcRec). exact HY0.
    + assert (Hx0y : x0 <> y) by (intro He; apply Hneq; symmetry; exact He).
      assert (HyE0 : y # (G & x0 ~ bind_sub P Q)).
      { rewrite dom_push. apply notin_union_l.
        - apply notin_singleton_l. exact Hneq.
        - exact HyG. }
      pose proof (@dtyping_rename inf (G & x0 ~ bind_sub P Q) Y0 (T ^ x0)
                    HY0 x0 y Hx0y HyE0) as Hren.
      assert (Henv : rename_env x0 y (G & x0 ~ bind_sub P Q)
                     = G & y ~ bind_sub P Q).
      { rewrite rename_env_push.
        assert (HrenG : rename_env x0 y G = G)
          by (apply rename_env_id; [exact Hx0G|exact HyG|exact Hx0vals|exact Hyvals]).
        rewrite HrenG.
        destruct (classicT (x0 = x0)) as [Heq2|Hne2];
          [|exfalso; apply Hne2; reflexivity].
        assert (Hrb : rename_binding x0 y (bind_sub P Q) = bind_sub P Q).
        { apply rename_binding_id.
          - simpl. apply notin_union_l; [exact Hx0P|exact Hx0Q].
          - simpl. apply notin_union_l; [exact HyP|exact HyQ]. }
        rewrite Hrb. reflexivity. }
      assert (Hterm : rename x0 y Y0 = Y ^ y).
      { symmetry. unfold Y. apply open_close_rename. exact HlcRec. }
      assert (Htype : rename x0 y (T ^ x0) = T ^ y).
      { rewrite rename_open'.
        rewrite (@rename_trm_id x0 y T Hx0T HyT).
        rewrite rename_var_same. reflexivity. }
      rewrite Henv, Hterm, Htype in Hren.
      exact Hren.
Qed.


(* ============================================================ *)
(* Main result                                                  *)
(* ============================================================ *)

Lemma sub_to_bidir_from_SW :
  (forall G e A,
     dtyping inf G e A -> exists X, dtyping inf G X trm_star /\ [# X #] = A) ->
  forall G e1 e2 A, sub G e1 e2 A ->
    dsub G e1 e2 /\
    exists e1' e2',
      dtyping inf G e1' A /\ dtyping inf G e2' A /\
      [# e1' #] = e1 /\ [# e2' #] = e2.
Proof.
  intros SW.
  change (forall G e1 e2 A (s : sub G e1 e2 A), Psub G e1 e2 A).
  apply (@sub_wf_mut
           (fun G e1 e2 A (_ : sub G e1 e2 A) => Psub G e1 e2 A)
           (fun G (_ : wf G) => Pwf G)).
  - (* sub_ax *) intros G w IHw. unfold Pwf in IHw. unfold Psub.
    split.
    + apply dsub_star. apply dwf_ok. exact IHw.
    + exists trm_star. exists trm_star. simpl.
      split.
      * apply dtyping_star. exact IHw.
      * split.
        -- apply dtyping_star. exact IHw.
        -- split; reflexivity.
  - (* sub_var_refl *) intros G x A e w IHw b.
    unfold Pwf in IHw. unfold Psub.
    split.
    + eapply dsub_var_refl.
      * apply dwf_ok. exact IHw.
      * exact b.
    + exists (trm_var_f x). exists (trm_var_f x). simpl.
      split.
      * apply (@dtyping_var e G x A IHw b).
      * split.
        -- apply (@dtyping_var e G x A IHw b).
        -- split; reflexivity.
  - (* sub_var_trans *) intros G x e2 A e1 b s IHs.
    unfold Psub in IHs.
    destruct IHs as [Hd [u1 [u2 [Hu1 [Hu2 [He1 He2]]]]]].
    assert (Hdwf : dwf G) by (exact (@dtyping_dwf inf G u1 A Hu1)).
    unfold Psub. split.
    + eapply dsub_var_trans; [exact b|exact Hd].
    + exists (trm_var_f x). exists u2. simpl.
      split.
      * apply (@dtyping_var e1 G x A Hdwf b).
      * split.
        -- exact Hu2.
        -- split; [reflexivity|exact He2].
  - (* sub_top *) intros G e A s IHs.
    unfold Psub in IHs.
    destruct IHs as [Hd [u1 [u2 [Hu1 [Hu2 [He1 He2]]]]]].
    assert (Hdwf : dwf G) by (exact (@dtyping_dwf inf G u1 A Hu1)).
    destruct (@inf_top_wit SW G u1 A Hu1) as [T [HT HeT]].
    unfold Psub. split.
    + eapply dsub_top.
      * apply dwf_ok. exact Hdwf.
      * rewrite <- He1. exact (@lc_erase_of_inf G u1 A Hu1).
    + exists u1. exists T. simpl.
      split.
      * exact Hu1.
      * split.
        -- exact HT.
        -- split; [exact He1|exact HeT].
  - (* sub_top_refl *) intros G A s IHs.
    unfold Psub in IHs.
    destruct IHs as [Hd [u1 [u2 [Hu1 [Hu2 [He1 He2]]]]]].
    assert (Hdwf : dwf G) by (exact (@dtyping_dwf inf G u1 trm_star Hu1)).
    unfold Psub. split.
    + eapply dsub_top.
      * apply dwf_ok. exact Hdwf.
      * constructor.
    + exists (trm_anno trm_top u1). exists (trm_anno trm_top u2). simpl.
      split.
      * rewrite <- He1. apply dtyping_anno.
        -- apply dtyping_top. apply dtyping_chk. exact Hu1.
        -- apply dtyping_chk. exact Hu1.
      * split.
        -- rewrite <- He2. apply dtyping_anno.
           ++ apply dtyping_top. apply dtyping_chk. exact Hu2.
           ++ apply dtyping_chk. exact Hu2.
        -- split; reflexivity.
  - (* sub_abs *) intros L G e1 A e2 e2' B s1 IH1 s2 IH2 s3 IH3 s4 IH4.
    unfold Psub in IH1, IH2, IH3, IH4.
    destruct IH1 as [d1 [w1 [w1' [Hw1 [Hw1' [He1w1 He1w1']]]]]].
    destruct IH2 as [d2 [a1 [a2 [Ha1 [Ha2 [HAa1 HAa2]]]]]].
    (* extract erasedness of e1 and A from a fresh instance of IH3 *)
    pick_fresh_gen L x0.
    pose proof (IH3 x0 Fr) as Hx0P. unfold Psub in Hx0P.
    destruct Hx0P as [d3 [v1 [v2 [Hv1 [Hv2 [Hev1 Hev2]]]]]].
    assert (HdwfE : dwf (G & x0 ~ bind_sub e1 A))
      by (exact (@dtyping_dwf inf (G & x0 ~ bind_sub e1 A) v1 (B ^ x0) Hv1)).
    destruct (@dwf_bind_sub_Et G x0 e1 A HdwfE) as [He1e HAE].
    unfold Et in He1e, HAE.
    assert (HokG : ok G) by (apply dwf_ok; exact (@dtyping_dwf inf G w1 A Hw1)).
    unfold Psub. split.
    + (* dsub *)
      eapply dsub_lam with (L := L).
      * exact HokG.
      * intros x Hx.
        pose proof (IH3 x Hx) as HxP. unfold Psub in HxP.
        destruct HxP as [d3x _].
        rewrite He1e, HAE. exact d3x.
    + (* witnesses *)
      destruct (@close_inf_family G [# w1 #] [# a1 #] L e2 B)
        as [Y [HeY HYfam]].
      { intros x Hx.
        pose proof (IH3 x Hx) as HxP. unfold Psub in HxP.
        destruct HxP as [_ [v1x [v2x [Hv1x [Hv2x [Hev1x Hev2x]]]]]].
        exists v1x. split.
        - rewrite He1w1, HAa1. exact Hv1x.
        - exact Hev1x. }
      destruct (@close_inf_family G [# w1 #] [# a1 #] L e2' B)
        as [Y' [HeY' HYfam']].
      { intros x Hx.
        pose proof (IH3 x Hx) as HxP. unfold Psub in HxP.
        destruct HxP as [_ [v1x [v2x [Hv1x [Hv2x [Hev1x Hev2x]]]]]].
        exists v2x. split.
        - rewrite He1w1, HAa1. exact Hv2x.
        - exact Hev2x. }
      exists (trm_abs w1 a1 Y). exists (trm_abs w1 a1 Y'). simpl.
      split.
      * rewrite <- He1w1, <- HAa1.
        eapply dtyping_lam with
          (L := fam_bound G [# w1 #] [# a1 #] L e2 B).
        -- rewrite HAa1. apply dtyping_chk. exact Hw1.
        -- apply dtyping_chk. exact Ha1.
        -- intros x Hx. apply HYfam. exact Hx.
      * split.
        -- rewrite <- He1w1, <- HAa1.
           eapply dtyping_lam with
             (L := fam_bound G [# w1 #] [# a1 #] L e2' B).
           ++ rewrite HAa1. apply dtyping_chk. exact Hw1.
           ++ apply dtyping_chk. exact Ha1.
           ++ intros x Hx. apply HYfam'. exact Hx.
        -- split.
           ++ rewrite He1w1, HAa1, HeY. reflexivity.
           ++ rewrite He1w1, HAa1, HeY'. reflexivity.
  - (* sub_app *) intros G e1 A e2 C e3 B s1 IH1 s2 IH2.
    unfold Psub in IH1, IH2.
    destruct IH1 as [d1 [f1 [f2 [Hf1 [Hf2 [Hef1 Hef2]]]]]].
    destruct IH2 as [d2 [w1 [w2 [Hw1 [Hw2 [Hew1 Hew2]]]]]].
    unfold Psub. split.
    + eapply dsub_app.
      * rewrite <- Hew1. exact (@lc_erase_of_inf G w1 B Hw1).
      * exact d1.
    + exists (trm_app f1 w1). exists (trm_app f2 w1). simpl.
      split.
      * rewrite <- Hew1.
        eapply dtyping_app with (e3 := e3) (B := B) (C := C).
        -- apply dtyping_chk. exact Hw1.
        -- rewrite Hew1. exact d2.
        -- exact Hf1.
      * split.
        -- rewrite <- Hew1.
           eapply dtyping_app with (e3 := e3) (B := B) (C := C).
           ++ apply dtyping_chk. exact Hw1.
           ++ rewrite Hew1. exact d2.
           ++ exact Hf2.
        -- split.
           ++ rewrite Hef1, Hew1. reflexivity.
           ++ rewrite Hef2, Hew1. reflexivity.
  - (* sub_prod *) intros L G e A B A' B' s1 IH1 s2 IH2 s3 IH3 s4 IH4 s5 IH5.
    unfold Psub in IH1, IH2, IH3, IH4, IH5.
    destruct IH1 as [d1 [z1 [z2 [Hz1 [Hz2 [Hez1 Hez2]]]]]].
    destruct IH2 as [de [we1 [we2 [Hwe1 [Hwe2 [Hewe1 Hewe2]]]]]].
    destruct IH3 as [d3 [za1 [za2 [Hza1 [Hza2 [Heza1 Heza2]]]]]].
    (* extract erasedness of e and A' from a fresh instance of IH5 *)
    pick_fresh_gen (union L (dom G)) x0.
    apply notin_union_r in Fr as [Hx0L Hx0G].
    pose proof (IH5 x0 Hx0L) as Hx0P. unfold Psub in Hx0P.
    destruct Hx0P as [d5 [p1 [p2 [Hp1 [Hp2 [Hep1 Hep2]]]]]].
    assert (Hdwf5 : dwf (G & x0 ~ bind_sub e A'))
      by (exact (@dtyping_dwf inf (G & x0 ~ bind_sub e A') p1 trm_star Hp1)).
    destruct (@dwf_bind_sub_Et G x0 e A' Hdwf5) as [Hee HEA'].
    unfold Et in Hee, HEA'.
    unfold Psub. split.
    + (* dsub *)
      eapply dsub_pi with (L := L).
      * exact d1.
      * intros x Hx.
        pose proof (IH5 x Hx) as HxP. unfold Psub in HxP.
        destruct HxP as [d5x _].
        rewrite Hee, HEA'. exact d5x.
    + (* witnesses *)
      (* LHS: product annotated with e and A *)
      assert (Hanno1 : dtyping inf G (trm_anno we1 za1) [# za1 #]).
      { apply (@dtyping_anno_sub G we1 A' za1 Hwe1).
        - rewrite Heza1. exact d1.
        - apply dtyping_chk. exact Hza1. }
      destruct (@close_inf_family G [# (trm_anno we1 za1) #] [# za1 #]
                   L B trm_star) as [Y [HeY HYfam]].
      { intros x Hx.
        pose proof (IH4 x Hx) as HxP. unfold Psub in HxP.
        destruct HxP as [_ [v1x [v2x [Hv1x [Hv2x [Hev1x Hev2x]]]]]].
        exists v1x. split.
        - simpl. rewrite Hewe1, Heza1. exact Hv1x.
        - exact Hev1x. }
      destruct (@close_inf_family G [# we2 #] [# z1 #]
                   L B' trm_star) as [Y' [HeY' HYfam']].
      { intros x Hx.
        pose proof (IH5 x Hx) as HxP. unfold Psub in HxP.
        destruct HxP as [_ [v1x [v2x [Hv1x [Hv2x [Hev1x Hev2x]]]]]].
        exists v2x. split.
        - rewrite Hewe2, Hez1. exact Hv2x.
        - exact Hev2x. }
      exists (trm_prod (trm_anno we1 za1) za1 Y).
      exists (trm_prod we2 z1 Y'). simpl.
      split.
      * eapply dtyping_pi with
          (L := fam_bound G [# (trm_anno we1 za1) #] [# za1 #] L B trm_star)
          (e := trm_anno we1 za1) (A := za1) (B := Y).
        -- apply dtyping_chk. exact Hanno1.
        -- apply dtyping_chk. exact Hza1.
        -- intros x Hx. apply dtyping_chk. apply HYfam. exact Hx.
      * split.
        -- eapply dtyping_pi with
             (L := fam_bound G [# we2 #] [# z1 #] L B' trm_star)
             (e := we2) (A := z1) (B := Y').
           ++ rewrite Hez1. apply dtyping_chk. exact Hwe2.
           ++ apply dtyping_chk. exact Hz1.
           ++ intros x Hx. apply dtyping_chk. apply HYfam'. exact Hx.
        -- split.
           ++ rewrite Hewe1, Heza1, HeY. reflexivity.
           ++ rewrite Hewe2, Hez1, HeY'. reflexivity.
  - (* sub_castup *) intros G B e1 e2 A s1 IH1 s2 IH2 r.
    unfold Psub in IH1, IH2.
    destruct IH1 as [d1 [b1 [b2 [Hb1 [Hb2 [Heb1 Heb2]]]]]].
    destruct IH2 as [d2 [u1 [u2 [Hu1 [Hu2 [Heu1 Heu2]]]]]].
    assert (HEtA : Et A)
      by (exact (@dtyping_inf_Et_type inf G u1 A Hu1 eq_refl)).
    unfold Et in HEtA.
    unfold Psub. split.
    + eapply dsub_castup.
      * rewrite <- Heb1. exact (@lc_erase_of_inf G b1 trm_star Hb1).
      * exact d2.
    + exists (trm_castup b1 u1). exists (trm_castup b2 u2). simpl.
      split.
      * rewrite <- Heb1.
        eapply dtyping_castup with (A := A) (B := b1).
        -- apply dtyping_chk. exact Hb1.
        -- exact Hu1.
        -- rewrite Heb1, HEtA. exact r.
      * split.
        -- rewrite <- Heb2.
           eapply dtyping_castup with (A := A) (B := b2).
           ++ apply dtyping_chk. exact Hb2.
           ++ exact Hu2.
           ++ rewrite Heb2, HEtA. exact r.
        -- split.
           ++ rewrite Heb1, Heu1. reflexivity.
           ++ rewrite Heb2, Heu2. reflexivity.
  - (* sub_castdn *) intros G e1 e2 B A s1 IH1 s2 IH2 r.
    unfold Psub in IH1, IH2.
    destruct IH1 as [d1 [b1 [b2 [Hb1 [Hb2 [Heb1 Heb2]]]]]].
    destruct IH2 as [d2 [u1 [u2 [Hu1 [Hu2 [Heu1 Heu2]]]]]].
    assert (HEtA : Et A)
      by (exact (@dtyping_inf_Et_type inf G u1 A Hu1 eq_refl)).
    unfold Et in HEtA.
    unfold Psub. split.
    + eapply dsub_castdn. exact d2.
    + exists (trm_anno (trm_castdn u1) b1).
      exists (trm_anno (trm_castdn u2) b2). simpl.
      split.
      * rewrite <- Heb1. apply dtyping_anno.
        -- eapply dtyping_castdn with (A := A) (B := b1).
           ++ apply dtyping_chk. exact Hb1.
           ++ exact Hu1.
           ++ rewrite HEtA, Heb1. exact r.
        -- apply dtyping_chk. exact Hb1.
      * split.
        -- rewrite <- Heb2. apply dtyping_anno.
           ++ eapply dtyping_castdn with (A := A) (B := b2).
              ** apply dtyping_chk. exact Hb2.
              ** exact Hu2.
              ** rewrite HEtA, Heb2. exact r.
           ++ apply dtyping_chk. exact Hb2.
        -- split.
           ++ rewrite Heu1. reflexivity.
           ++ rewrite Heu2. reflexivity.
  - (* sub_sub *) intros G e1 e2 B A s1 IH1 s2 IH2.
    unfold Psub in IH1, IH2.
    destruct IH1 as [d1 [u1 [u2 [Hu1 [Hu2 [Heu1 Heu2]]]]]].
    destruct IH2 as [d2 [z1 [z2 [Hz1 [Hz2 [Hez1 Hez2]]]]]].
    unfold Psub. split.
    + exact d1.
    + exists (trm_anno u1 z2). exists (trm_anno u2 z2). simpl.
      split.
      * rewrite <- Hez2.
        apply (@dtyping_anno_sub G u1 A z2 Hu1).
        -- rewrite Hez2. exact d2.
        -- apply dtyping_chk. exact Hz2.
      * split.
        -- rewrite <- Hez2.
           apply (@dtyping_anno_sub G u2 A z2 Hu2).
           ++ rewrite Hez2. exact d2.
           ++ apply dtyping_chk. exact Hz2.
        -- split.
           ++ rewrite Heu1. reflexivity.
           ++ rewrite Heu2. reflexivity.
  - (* wf_nil *) unfold Pwf. apply dwf_nil.
  - (* wf_cons *) intros G x e A s1 IH1 s2 IH2 n.
    unfold Pwf. unfold Psub in IH1, IH2.
    destruct IH1 as [d1 [u1 [u2 [Hu1 [Hu2 [Heu1 Heu2]]]]]].
    destruct IH2 as [d2 [a1 [a2 [Ha1 [Ha2 [Hea1 Hea2]]]]]].
    rewrite <- Heu1, <- Hea1.
    apply dwf_cons with (e := u1) (A := a1).
    + exact n.
    + rewrite Hea1. apply dtyping_chk. exact Hu1.
    + apply dtyping_chk. exact Ha1.
Qed.

Unset Implicit Arguments.
(* ===== conditional star-witness invariant (STARSUBST still open) ===== *)

Lemma chk_star_wit : forall G e,
  dtyping chk G e trm_star ->
  exists X, dtyping inf G X trm_star /\ [# X #] = [# e #].
Proof.
  intros G e H.
  exists (trm_anno e trm_star). split.
  - apply dtyping_anno.
    + exact H.
    + apply dtyping_chk. apply dtyping_star.
      apply (@dtyping_dwf chk G e trm_star H).
  - simpl. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The single missing substitution ingredient.                          *)
(* ------------------------------------------------------------------ *)

Definition STARSUBST : Prop :=
  forall G x e0 A0 B0 u,
    x # G ->
    x \notin fv_trm e0 ->
    x \notin fv_trm A0 ->
    x \notin fv_trm B0 ->
    dtyping chk (G & x ~ bind_sub [# e0 #] [# A0 #]) (B0 ^ x) trm_star ->
    dtyping chk G u [# A0 #] ->
    dsub G [# u #] [# e0 #] ->
    exists Y, dtyping inf G Y trm_star /\ [# Y #] = [# B0 #] ^^ [# u #].

(* ------------------------------------------------------------------ *)
(* Propagating a star witness through an opened codomain.              *)
(* ------------------------------------------------------------------ *)

Lemma prod_open_from_subst : STARSUBST ->
  forall d G X T,
    dtyping d G X T ->
    forall e3 B C Aarg,
      [# X #] = trm_prod e3 B C ->
      dtyping chk G Aarg B ->
      dsub G [# Aarg #] e3 ->
      exists Y, dtyping inf G Y trm_star /\ [# Y #] = C ^^ [# Aarg #].
Proof.
  intros HS d G X T H.
  pose (P := fun d G e A (H:dtyping d G e A) =>
       forall e3 B C Aarg,
         [# e #] = trm_prod e3 B C ->
         dtyping chk G Aarg B ->
         dsub G [# Aarg #] e3 ->
         exists Y, dtyping inf G Y trm_star /\ [# Y #] = C ^^ [# Aarg #]).
  change (P d G X T H).
  apply (dtyping_mut P (fun G (H:dwf G) => True)).
  - (* star *) intros G0 Hd IH e3 B0 C0 Aarg Heq HA Hsub.
    simpl in Heq. discriminate Heq.
  - (* var *) intros e0 G0 xx A0 Hd IH b e3 B0 C0 Aarg Heq HA Hsub.
    simpl in Heq. discriminate Heq.
  - (* top *) intros G0 A0 d1 IH1 e3 B0 C0 Aarg Heq HA Hsub.
    simpl in Heq. discriminate Heq.
  - (* lam *) intros L G0 e1 e2 A0 B0 d1 IH1 d2 IH2 d3 IH3 e3 B0' C0 Aarg Heq HA Hsub.
    simpl in Heq. discriminate Heq.
  - (* app *) intros e3 G0 e0 A0 B0 C0 d1 IH1 ds d2 IH2 e3' B0' C0' Aarg Heq HA Hsub.
    simpl in Heq. discriminate Heq.
  - (* pi *)
    intros L G0 e0 A0 B0 d1 IH1 d2 IH2 d3 IH3 e3 B0' C0 Aarg Heq HA Hsub.
    simpl in Heq. injection Heq as He3 HB HC. subst e3. subst B0'. subst C0.
    set (Lf := union L (union (dom G0)
       (union (fv_trm e0) (union (fv_trm A0) (fv_trm B0))))).
    pick_fresh_gen Lf x.
    unfold Lf in Fr.
    apply notin_union_r in Fr as [HxL Fr].
    apply notin_union_r in Fr as [HxG Fr].
    apply notin_union_r in Fr as [Hxe0 Fr].
    apply notin_union_r in Fr as [HxA0 HxB0].
    exact (@HS G0 x e0 A0 B0 Aarg HxG Hxe0 HxA0 HxB0
             (d3 x HxL) HA Hsub).
  - (* castup *) intros G0 e0 A0 B0 d1 IH1 d2 IH2 r e3 B0' C0 Aarg Heq HA Hsub.
    simpl in Heq. discriminate Heq.
  - (* castdn *) intros G0 e0 A0 B0 d1 IH1 d2 IH2 r e3 B0' C0 Aarg Heq HA Hsub.
    simpl in Heq. discriminate Heq.
  - (* anno *) intros G0 e0 A0 d1 IH1 d2 IH2 e3 B0' C0 Aarg Heq HA Hsub.
    simpl in Heq.
    exact (IH1 e3 B0' C0 Aarg Heq HA Hsub).
  - (* sub *) intros A0 G0 e0 B0 d1 IH1 ds d2 IH2 e3 B0' C0 Aarg Heq HA Hsub.
    exact (IH1 e3 B0' C0 Aarg Heq HA Hsub).
  - (* chk *) intros G0 e0 A0 d1 IH1 e3 B0' C0 Aarg Heq HA Hsub.
    exact (IH1 e3 B0' C0 Aarg Heq HA Hsub).
  - (* dwf_nil *) exact I.
  - (* dwf_cons *) intros; exact I.
Qed.

(* ------------------------------------------------------------------ *)
(* The star-witness invariant, reduced to STARSUBST.                   *)
(* ------------------------------------------------------------------ *)

Lemma dtyping_inf_star_wit_gen : STARSUBST ->
  forall d G e A, dtyping d G e A -> d = inf ->
    exists X, dtyping inf G X trm_star /\ [# X #] = A.
Proof.
  intros HS d G e A H.
  pose (P := fun d G e A (H:dtyping d G e A) =>
       d = inf -> exists X, dtyping inf G X trm_star /\ [# X #] = A).
  change (P d G e A H).
  apply (dtyping_mut P (fun G (H:dwf G) => True)).
  - (* star *) intros G0 Hd IH Heq.
    exists trm_star. split.
    + apply dtyping_star. exact Hd.
    + reflexivity.
  - (* var *) intros e0 G0 xx A0 Hd IH b Heq.
    apply (@dwf_binds_star_wit_inf G0 xx e0 A0 Hd b).
  - (* top *) intros G0 A0 d1 IH1 Heq. discriminate Heq.
  - (* lam *) intros L G0 e1 e2 A0 B0 d1 IH1 d2 IH2 d3 IH3 Heq.
    eapply star_wit_lam_cons with (L := L).
    + exact d1.
    + exact d2.
    + intros x Hx. exact (IH3 x Hx eq_refl).
  - (* app *) intros e3 G0 e0 A0 B0 C0 d1 IH1 ds d2 IH2 Heq.
    destruct (IH2 eq_refl) as [X [HX HXeq]].
    exact (@prod_open_from_subst HS inf G0 X trm_star HX
             e3 B0 C0 A0 HXeq d1 ds).
  - (* pi *) intros L G0 e0 A0 B0 d1 IH1 d2 IH2 d3 IH3 Heq.
    exists trm_star. split.
    + apply dtyping_star. apply (@dtyping_dwf chk G0 A0 trm_star d2).
    + reflexivity.
  - (* castup *) intros G0 e0 A0 B0 d1 IH1 d2 IH2 r Heq.
    exact (@chk_star_wit G0 B0 d1).
  - (* castdn *) intros G0 e0 A0 B0 d1 IH1 d2 IH2 r Heq. discriminate Heq.
  - (* anno *) intros G0 e0 A0 d1 IH1 d2 IH2 Heq.
    exact (@chk_star_wit G0 A0 d2).
  - (* sub *) intros A0 G0 e0 B0 d1 IH1 ds d2 IH2 Heq. discriminate Heq.
  - (* chk *) intros G0 e0 A0 d1 IH1 Heq. discriminate Heq.
  - (* dwf_nil *) exact I.
  - (* dwf_cons *) intros; exact I.
Qed.

Lemma dtyping_inf_star_wit_from_subst : STARSUBST ->
  forall G e A, dtyping inf G e A ->
    exists X, dtyping inf G X trm_star /\ [# X #] = A.
Proof.
  intros HS G e A H.
  exact (@dtyping_inf_star_wit_gen HS inf G e A H eq_refl).
Qed.

Set Implicit Arguments.
(* ===== bidir helper progress ===== *)

Definition binds_incl (G G':env) : Prop :=
  forall x b, binds x b G -> binds x b G'.

Lemma binds_incl_push : forall G G' x b,
  binds_incl G G' -> x # G -> x # G' ->
  binds_incl (G & x ~ b) (G' & x ~ b).
Proof.
  intros G G' x b Hin HxG HxG' y c Hy.
  apply binds_push_inv in Hy as [[Heq Hy']|[Hneq Hy']].
  - inversion Heq. subst. apply binds_push_eq.
  - apply binds_push_neq; [apply Hin; exact Hy'|exact Hneq].
Qed.

Lemma binds_incl_add : forall G z c,
  z # G -> binds_incl G (G & z ~ c).
Proof.
  intros G z c Hz y b Hy.
  apply (@binds_add_fresh G y b z c Hy Hz).
Qed.

Lemma wf_cons_inv : forall G x e A,
  wf (G & x ~ bind_sub e A) ->
  sub G e e A /\ sub G A A trm_star /\ x # G.
Proof.
  intros G x e A H.
  inversion H as [| G0 x5 e0 A0 Hse Hsa Hx H0]; subst.
  - rewrite (empty_def binding) in H0.
    rewrite concat_def in H0. rewrite single_def in H0.
    discriminate H0.
  - rewrite concat_def in H0. rewrite single_def in H0.
    change ((x5, bind_sub e0 A0) :: G0 = (x, bind_sub e A) :: G) in H0.
    injection H0 as HG HA He Hxeq; subst; auto.
Qed.

(* ============================================================ *)
(* BLOCKED ATTEMPT (kept out of the compiling prefix)            *)
(* ============================================================ *)
(*
   The next natural helper is monotonicity of [sub] under a wf
   environment extension:

     Lemma sub_binds_incl : forall G e1 e2 A,
       sub G e1 e2 A ->
       forall G', binds_incl G G' -> wf G' -> sub G' e1 e2 A.

   The direct [sub_wf_mut] induction fails in [sub_prod]: the body
   hypothesis has the pushed environment [G0 & x ~ bind_sub e0 A'],
   and [wf_cons_inv] of its source wf derivation gives
   [sub G0 A' A' trm_star].  The induction hypothesis available for
   the first [sub_prod] premise is for [sub G0 A' A0 trm_star], so it
   cannot weaken that [sub G0 A' A' trm_star] to [G'].  This is the
   genuine mutual-recursion/transport circularity, not a tactic bug.
*)

(* ============================================================ *)
(* A genuinely useful, unconditional fact: [sub] is left-reflexive. *)
(* ============================================================ *)

Lemma sub_left_self : forall G e1 e2 A,
  sub G e1 e2 A -> sub G e1 e1 A.
Proof.
  intros G e1 e2 A H. induction H.
  - apply sub_ax. assumption.
  - eapply sub_var_refl; eassumption.
  - eapply sub_var_refl.
    + exact (@sub_wf G e1 e2 A H0).
    + exact H.
  - exact IHsub.
  - apply sub_top_refl. exact H.
  - (* sub_abs *) eapply sub_abs.
    + exact H.
    + exact H0.
    + intros x Hx. apply H2. exact Hx.
    + exact H3.
  - (* sub_app *) eapply sub_app.
    + exact IHsub1.
    + exact H0.
  - (* sub_prod *) eapply sub_prod.
    + exact H1.
    + eapply sub_sub; [exact H0|exact H].
    + exact H1.
    + exact H2.
    + exact H2.
  - (* sub_castup *) eapply sub_castup.
    + exact IHsub1.
    + exact IHsub2.
    + exact H1.
  - (* sub_castdn *) eapply sub_castdn.
    + exact IHsub1.
    + exact IHsub2.
    + exact H1.
  - (* sub_sub *) eapply sub_sub.
    + exact IHsub1.
    + exact H0.
Qed.


(* ============================================================ *)
(* Environment irrelevance for [sub] (Qed) *)
(* ============================================================ *)

Ltac use_ih :=
  match goal with
  | IH : forall G', binds_equiv ?G G' -> wf G' -> sub G' ?e1 ?e2 ?A
    |- sub ?G' ?e1 ?e2 ?A => apply IH; assumption
  end.

Ltac use_ih_x x Hx :=
  match goal with
  | IH : forall y, y \notin ?L ->
           forall G', binds_equiv (?G & y ~ ?b) G' -> wf G' ->
             sub G' ?e1 ?e2 ?A
    |- sub ?G' ?e1 ?e2 ?A => apply (IH x Hx); assumption
  end.

Ltac prep_body Hb G e A G' Hbe Hwf x Hx :=
  let b := constr:(bind_sub e A) in
  let Hw := fresh "Hw" in
  let HxG := fresh "HxG" in
  let HxG' := fresh "HxG'" in
  let Hbe' := fresh "Hbe'" in
  let Hwf' := fresh "Hwf'" in
  idtac "PB1"; assert (HxG : x # G);
  [ pose proof (@wf_cons_inv G x e A (sub_wf (Hb x Hx))) as Hw;
    exact (proj2 (proj2 Hw))
  | idtac "PB2"; assert (HxG' : x # G');
    [ exact (@binds_equiv_fresh G G' x Hbe HxG)
    | idtac "PB3"; assert (Hbe' : binds_equiv (G & x ~ b) (G' & x ~ b));
      [ apply binds_equiv_push; assumption
      | idtac "PB4"; assert (Hwf' : wf (G' & x ~ b));
        [ eapply wf_cons; [ use_ih | use_ih | exact HxG' ]
        | idtac ] ] ] ].

Ltac prep_body_auto G' Hbe Hwf x Hx :=
  match goal with
  | Hb : (forall y, y \notin ?L -> sub (?G & y ~ bind_sub ?e ?A) _ _ _) |- _ =>
      prep_body Hb G e A G' Hbe Hwf x Hx
  end.

Lemma sub_env_irrel : forall G e1 e2 A,
  sub G e1 e2 A ->
  forall G', binds_equiv G G' -> wf G' -> sub G' e1 e2 A.
Proof.
  intros G e1 e2 A H.
  induction H; intros G' Hbe Hwf.
  - apply sub_ax. exact Hwf.
  - eapply sub_var_refl.
    + exact Hwf.
    + match goal with
      | Hb : binds ?x (bind_sub ?e ?A) G |- _ =>
          exact (proj1 (Hbe x (bind_sub e A)) Hb)
      end.
  - eapply sub_var_trans.
    + match goal with
      | Hb : binds ?x (bind_sub ?e ?A) G |- _ =>
          exact (proj1 (Hbe x (bind_sub e A)) Hb)
      end.
    + use_ih.
  - apply sub_top. use_ih.
  - apply sub_top_refl. use_ih.
  - (* sub_abs *)
    eapply sub_abs with (L := L).
    + use_ih.
    + use_ih.
    + intros x Hx.
      assert (HxG : x # G).
      { pose proof (@wf_cons_inv G x e1 A (sub_wf (H1 x Hx))) as Hw.
        exact (proj2 (proj2 Hw)). }
      assert (HxG' : x # G').
      { exact (@binds_equiv_fresh G G' x Hbe HxG). }
      assert (Hbe' : binds_equiv (G & x ~ bind_sub e1 A)
                                 (G' & x ~ bind_sub e1 A))
        by (apply binds_equiv_push; assumption).
      assert (Hwf' : wf (G' & x ~ bind_sub e1 A)).
      { eapply wf_cons.
        - apply IHsub1; assumption.
        - apply IHsub2; assumption.
        - exact HxG'. }
      apply (H2 x Hx). exact Hbe'. exact Hwf'.
    + intros x Hx.
      assert (HxG : x # G).
      { pose proof (@wf_cons_inv G x e1 A (sub_wf (H1 x Hx))) as Hw.
        exact (proj2 (proj2 Hw)). }
      assert (HxG' : x # G').
      { exact (@binds_equiv_fresh G G' x Hbe HxG). }
      assert (Hbe' : binds_equiv (G & x ~ bind_sub e1 A)
                                 (G' & x ~ bind_sub e1 A))
        by (apply binds_equiv_push; assumption).
      assert (Hwf' : wf (G' & x ~ bind_sub e1 A)).
      { eapply wf_cons.
        - apply IHsub1; assumption.
        - apply IHsub2; assumption.
        - exact HxG'. }
      apply (H4 x Hx). exact Hbe'. exact Hwf'.
  - eapply sub_app.
    + apply IHsub1; assumption.
    + apply IHsub2; assumption.
  - (* sub_prod *)
    eapply sub_prod with (L := L).
    + apply IHsub1; assumption.
    + apply IHsub2; assumption.
    + apply IHsub3; assumption.
    + intros x Hx.
      assert (HxG : x # G).
      { pose proof (@wf_cons_inv G x e A (sub_wf (H2 x Hx))) as Hw.
        exact (proj2 (proj2 Hw)). }
      assert (HxG' : x # G').
      { exact (@binds_equiv_fresh G G' x Hbe HxG). }
      assert (Hbe' : binds_equiv (G & x ~ bind_sub e A)
                                 (G' & x ~ bind_sub e A))
        by (apply binds_equiv_push; assumption).
      assert (Hwf' : wf (G' & x ~ bind_sub e A)).
      { eapply wf_cons.
        - eapply sub_sub.
          + apply IHsub2; assumption.
          + apply IHsub1; assumption.
        - apply IHsub3; assumption.
        - exact HxG'. }
      apply (H3 x Hx). exact Hbe'. exact Hwf'.
    + intros x Hx.
      assert (HxG : x # G).
      { pose proof (@wf_cons_inv G x e A' (sub_wf (H4 x Hx))) as Hw.
        exact (proj2 (proj2 Hw)). }
      assert (HxG' : x # G').
      { exact (@binds_equiv_fresh G G' x Hbe HxG). }
      assert (Hbe' : binds_equiv (G & x ~ bind_sub e A')
                                 (G' & x ~ bind_sub e A'))
        by (apply binds_equiv_push; assumption).
      assert (Hwf' : wf (G' & x ~ bind_sub e A')).
      { eapply wf_cons.
        - apply IHsub2; assumption.
        - apply sub_left_self with (e2 := A).
          apply IHsub1; assumption.
        - exact HxG'. }
      apply (H5 x Hx). exact Hbe'. exact Hwf'.
  - eapply sub_castup.
    + apply IHsub1; assumption.
    + apply IHsub2; assumption.
    + match goal with Hred : reduct ?B ?A |- reduct ?B ?A => exact Hred end.
  - eapply sub_castdn.
    + apply IHsub1; assumption.
    + apply IHsub2; assumption.
    + match goal with Hred : reduct ?B ?A |- reduct ?B ?A => exact Hred end.
  - eapply sub_sub.
    + apply IHsub1; assumption.
    + apply IHsub2; assumption.
Qed.

Unset Implicit Arguments.
(* ===== sub weakening/product/var-coercion helpers ===== *)

Lemma sub_weaken_ext : forall G e1 e2 A,
  sub G e1 e2 A ->
  forall G', extends G G' -> wf G' -> sub G' e1 e2 A.
Proof.
  intros G e1 e2 A H.
  induction H; intros G' Hext Hwf.
  - apply sub_ax. exact Hwf.
  - eapply sub_var_refl.
    + exact Hwf.
    + apply Hext. exact H0.
  - eapply sub_var_trans.
    + apply Hext. exact H.
    + apply IHsub. exact Hext. exact Hwf.
  - apply sub_top. apply IHsub. exact Hext. exact Hwf.
  - apply sub_top_refl. apply IHsub. exact Hext. exact Hwf.
  - (* sub_abs *)
    eapply sub_abs with (L := L \u dom G').
    + apply IHsub1. exact Hext. exact Hwf.
    + apply IHsub2. exact Hext. exact Hwf.
    + intros y Hy.
      apply notin_union_r in Hy as [HyL HyDom].
      assert (HyG : y # G).
      { pose proof (@wf_cons_inv G y e1 A (sub_wf (H1 y HyL))) as Hw.
        exact (proj2 (proj2 Hw)). }
      assert (HextY : extends (G & y ~ bind_sub e1 A)
                              (G' & y ~ bind_sub e1 A))
        by (apply extends_push_both; assumption).
      assert (HwfY : wf (G' & y ~ bind_sub e1 A)).
      { eapply wf_cons.
        - apply IHsub1. exact Hext. exact Hwf.
        - apply IHsub2. exact Hext. exact Hwf.
        - exact HyDom. }
      apply (H2 y HyL). exact HextY. exact HwfY.
    + intros y Hy.
      apply notin_union_r in Hy as [HyL HyDom].
      assert (HyG : y # G).
      { pose proof (@wf_cons_inv G y e1 A (sub_wf (H1 y HyL))) as Hw.
        exact (proj2 (proj2 Hw)). }
      assert (HextY : extends (G & y ~ bind_sub e1 A)
                              (G' & y ~ bind_sub e1 A))
        by (apply extends_push_both; assumption).
      assert (HwfY : wf (G' & y ~ bind_sub e1 A)).
      { eapply wf_cons.
        - apply IHsub1. exact Hext. exact Hwf.
        - apply IHsub2. exact Hext. exact Hwf.
        - exact HyDom. }
      apply (H4 y HyL). exact HextY. exact HwfY.
  - eapply sub_app.
    + apply IHsub1. exact Hext. exact Hwf.
    + apply IHsub2. exact Hext. exact Hwf.
  - (* sub_prod *)
    eapply sub_prod with (L := L \u dom G').
    + apply IHsub1. exact Hext. exact Hwf.
    + apply IHsub2. exact Hext. exact Hwf.
    + apply IHsub3. exact Hext. exact Hwf.
    + intros y Hy.
      apply notin_union_r in Hy as [HyL HyDom].
      assert (HyG : y # G).
      { pose proof (@wf_cons_inv G y e A (sub_wf (H2 y HyL))) as Hw.
        exact (proj2 (proj2 Hw)). }
      assert (HextY : extends (G & y ~ bind_sub e A)
                              (G' & y ~ bind_sub e A))
        by (apply extends_push_both; assumption).
      assert (HwfY : wf (G' & y ~ bind_sub e A)).
      { eapply wf_cons.
        - eapply sub_sub.
          + apply IHsub2. exact Hext. exact Hwf.
          + apply IHsub1. exact Hext. exact Hwf.
        - apply IHsub3. exact Hext. exact Hwf.
        - exact HyDom. }
      apply (H3 y HyL). exact HextY. exact HwfY.
    + intros y Hy.
      apply notin_union_r in Hy as [HyL HyDom].
      assert (HyG : y # G).
      { pose proof (@wf_cons_inv G y e A' (sub_wf (H4 y HyL))) as Hw.
        exact (proj2 (proj2 Hw)). }
      assert (HextY : extends (G & y ~ bind_sub e A')
                              (G' & y ~ bind_sub e A'))
        by (apply extends_push_both; assumption).
      assert (HwfY : wf (G' & y ~ bind_sub e A')).
      { eapply wf_cons.
        - apply IHsub2. exact Hext. exact Hwf.
        - apply sub_left_self with (e2 := A).
          apply IHsub1. exact Hext. exact Hwf.
        - exact HyDom. }
      apply (H5 y HyL). exact HextY. exact HwfY.
  - eapply sub_castup.
    + apply IHsub1. exact Hext. exact Hwf.
    + apply IHsub2. exact Hext. exact Hwf.
    + exact H1.
  - eapply sub_castdn.
    + apply IHsub1. exact Hext. exact Hwf.
    + apply IHsub2. exact Hext. exact Hwf.
    + exact H1.
  - eapply sub_sub.
    + apply IHsub1. exact Hext. exact Hwf.
    + apply IHsub2. exact Hext. exact Hwf.
Qed.

(* The type stored in a well-formed (sub-level) environment is a star type,
   in that same environment. *)
Lemma wf_binds_type_star : forall G x e A,
  wf G -> binds x (bind_sub e A) G -> sub G A A trm_star.
Proof.
  intros G x e A Hw Hb.
  remember (LibList.length G) as n eqn:E.
  revert G E Hw Hb.
  induction n as [|n IH]; intros G E Hw Hb.
  - symmetry in E. apply LibList.length_zero_inv in E. subst G.
    rewrite <- (empty_def binding) in Hb.
    exfalso. exact (@binds_empty_inv binding x (bind_sub e A) Hb).
  - inversion Hw as [| G0 z e0 A0 Hse Hsa Hz]; subst G.
    + exfalso. exact (@binds_empty_inv binding x (bind_sub e A) Hb).
    + rewrite length_push in E. injection E as E'.
      apply binds_push_inv in Hb as [[Heq Hb]|[Hneq Hb]].
      * subst z. injection Hb as He HA. subst e0 A0.
        eapply sub_weaken_ext with (G := G0).
        -- exact Hsa.
        -- apply extends_push. exact Hz.
        -- exact Hw.
      * assert (Hw0 : wf G0) by exact (@sub_wf G0 e0 e0 A0 Hse).
        assert (Ht : sub G0 A A trm_star)
          by (apply (IH G0 E' Hw0 Hb)).
        eapply sub_weaken_ext with (G := G0).
        -- exact Ht.
        -- apply extends_push. exact Hz.
        -- exact Hw.
Qed.

(* The value stored in a well-formed (sub-level) environment is self-subtyping
   at its stored type.  This is the binding-soundness component needed for the
   [dsub_var_trans] case of the master induction. *)
Lemma wf_binds_self : forall G x e A,
  wf G -> binds x (bind_sub e A) G -> sub G e e A.
Proof.
  intros G x e A Hw Hb.
  remember (LibList.length G) as n eqn:E.
  revert G E Hw Hb.
  induction n as [|n IH]; intros G E Hw Hb.
  - symmetry in E. apply LibList.length_zero_inv in E. subst G.
    rewrite <- (empty_def binding) in Hb.
    exfalso. exact (@binds_empty_inv binding x (bind_sub e A) Hb).
  - inversion Hw as [| G0 z e0 A0 Hse Hsa Hz]; subst G.
    + exfalso. exact (@binds_empty_inv binding x (bind_sub e A) Hb).
    + rewrite length_push in E. injection E as E'.
      apply binds_push_inv in Hb as [[Heq Hb]|[Hneq Hb]].
      * subst z. injection Hb as He HA. subst e0 A0.
        eapply sub_weaken_ext with (G := G0).
        -- exact Hse.
        -- apply extends_push. exact Hz.
        -- exact Hw.
      * assert (Hw0 : wf G0) by exact (@sub_wf G0 e0 e0 A0 Hse).
        assert (Ht : sub G0 e e A)
          by (apply (IH G0 E' Hw0 Hb)).
        eapply sub_weaken_ext with (G := G0).
        -- exact Ht.
        -- apply extends_push. exact Hz.
        -- exact Hw.
Qed.


Lemma sub_prod_star_inv_aux : forall G e1 e2 T,
  sub G e1 e2 T ->
  forall e A B,
    e1 = trm_prod e A B ->
    e2 = trm_prod e A B ->
    sub G e e A /\
    sub G A A trm_star /\
    exists L, forall x, x \notin L ->
      sub (G & x ~ bind_sub e A) (B ^ x) (B ^ x) trm_star.
Proof.
  intros G e1 e2 T H.
  induction H as
    [ G0 Hwf
    | G0 x0 A0 e0 Hwf Hb
    | e2v A0 G0 x0 e1v Hb Hsub IHsub
    | G0 e0 A0 Hsub IHsub
    | G0 A0 Hsub IHsub
    | L G0 e1v A0 e2v e2v' B0 Hsub1 IH1 Hsub2 IH2 Hbody Hbodytype
    | G0 e1v A0 e2v C0 e3v B0 Hsub1 IH1 Hsub2 IH2
    | L G0 e0 A0 B0 A' B' H1 IH1 H2 IH2 H3 IH3 H4 H5
    | G0 B0 e1v e2v A0 H1 IH1 H2 IH2 Hred
    | G0 e1v e2v B0 A0 H1 IH1 H2 IH2 Hred
    | G0 e1v e2v B0 A0 Hsub IHsub Htype IHtype ];
    intros X0 T0 U0 He1 He2; try (discriminate He1); try (discriminate He2).
  - (* sub_prod: the only matching constructor *)
    injection He1 as He HA HB. injection He2 as He' HA' HB'.
    subst X0 T0 U0.
    assert (Hdom : sub G0 e0 e0 A0) by (eapply sub_sub; [exact H2|exact H1]).
    split; [exact Hdom|].
    split; [exact H3|].
    exists L. intros x Hx. apply H4. exact Hx.
  - (* sub_sub: strip the coercion and recurse *)
    eapply IHsub. exact He1. exact He2.
Qed.

Lemma sub_prod_star_inv : forall G e A B,
  sub G (trm_prod e A B) (trm_prod e A B) trm_star ->
  sub G e e A /\
  sub G A A trm_star /\
  exists L, forall x, x \notin L ->
    sub (G & x ~ bind_sub e A) (B ^ x) (B ^ x) trm_star.
Proof.
  intros G e A B H.
  eapply sub_prod_star_inv_aux; [exact H|reflexivity|reflexivity].
Qed.


Lemma sub_var_self_coerce_aux : forall G0 e1 e2 T,
  wf G0 -> sub G0 e1 e2 T ->
  forall G x e A, G0 = G & x ~ bind_sub e A ->
    e1 = trm_var_f x -> e2 = trm_var_f x ->
    forall u, sub G0 u e A -> sub G0 u u T.
Proof.
  intros G0 e1 e2 T Hwf Hsub.
  induction Hsub as
    [ Gs Hwfs
    | Gs x0 A0 e0 Hwfs Hb
    | Gs x0 e2v A0 e1v Hb Hr IHr
    | Gs e0 A0 Hr IHr
    | Gs A0 Hr IHr
    | L Gs e1v A0 e2v e2v' B0 H1 IH1 H2 IH2 Hbody Hbodytype
    | Gs e1v A0 e2v C0 e3v B0 H1 IH1 H2 IH2
    | L Gs e0 A0 B0 A' B' H1 IH1 H2 IH2 H3 IH3 H4 H5
    | Gs B0 e1v e2v A0 H1 IH1 H2 IH2 Hred
    | Gs e1v e2v B0 A0 H1 IH1 H2 IH2 Hred
    | Gs e1v e2v B0 A0 Hr IHr Htype IHtype ];
    intros G x e A HEq HL HR u Hu;
    try (discriminate HL); try (discriminate HR).
  - (* sub_var_refl *)
    subst Gs. injection HL as Hx0. subst x0.
    pose proof (@wf_cons_inv G x e A Hwf) as Hw.
    assert (HxG : x # G) by exact (proj2 (proj2 Hw)).
    assert (Hbind : bind_sub e0 A0 = bind_sub e A).
    { apply binds_push_inv in Hb as [[Heq Hb']|[Hneq Hb']].
      - exact Hb'.
      - exfalso. eapply (@binds_fresh_inv binding x (bind_sub e0 A0) G Hb' HxG). }
    injection Hbind as He HA. subst e0. subst A0.
    exact (@sub_left_self (G & x ~ bind_sub e A) u e A Hu).
  - (* sub_var_trans *)
    subst Gs. injection HL as Hx0. subst x0.
    pose proof (@wf_cons_inv G x e A Hwf) as Hw.
    assert (HxG : x # G) by exact (proj2 (proj2 Hw)).
    assert (Hbind : bind_sub e1v A0 = bind_sub e A).
    { apply binds_push_inv in Hb as [[Heq Hb']|[Hneq Hb']].
      - exact Hb'.
      - exfalso. eapply (@binds_fresh_inv binding x (bind_sub e1v A0) G Hb' HxG). }
    injection Hbind as He HA. subst e1v. subst A0.
    exact (@sub_left_self (G & x ~ bind_sub e A) u e A Hu).
  - (* sub_sub: compose the coercion chain *)
    eapply sub_sub.
    + eapply IHr; [exact Hwf | exact HEq | exact HL | exact HR | exact Hu].
    + exact Htype.
Qed.

Lemma sub_var_star_coerce : forall G x e A,
  wf (G & x ~ bind_sub e A) ->
  sub (G & x ~ bind_sub e A) (trm_var_f x) (trm_var_f x) trm_star ->
  forall u, sub (G & x ~ bind_sub e A) u e A ->
    sub (G & x ~ bind_sub e A) u u trm_star.
Proof.
  intros G x e A Hwf H u Hu.
  eapply sub_var_self_coerce_aux; [exact Hwf|exact H|reflexivity|reflexivity|reflexivity|exact Hu].
Qed.

(* ===== GTerm/dsub transitivity/substitution helper stages ===== *)

(* from /tmp/dsub_trans_stage.v *)
Definition GEnv (G:env) : Prop := ok G /\ lc_env G /\ Eenv G.
Definition GTerm (t:trm) : Prop := Et t /\ lc_trm t.

Lemma GEnv_ok : forall G, GEnv G -> ok G.
Proof. intros G [H _]. exact H. Qed.
Lemma GEnv_lc : forall G, GEnv G -> lc_env G.
Proof. intros G [_ [H _]]. exact H. Qed.
Lemma GEnv_Eenv : forall G, GEnv G -> Eenv G.
Proof. intros G [_ [_ H]]. exact H. Qed.

Lemma Et_rem : forall e, Et [# e #].
Proof. intro e. unfold Et. apply remove_anno_idem. Qed.

Lemma Eenv_push_erased : forall G x e A,
  Eenv G -> Eenv (G & x ~ bind_sub [# e #] [# A #]).
Proof. intros. apply Eenv_push; auto using Et_rem. Qed.

Lemma Eenv_binds : forall G x e A, Eenv G -> binds x (bind_sub e A) G ->
  Et e /\ Et A.
Proof.
  intros G x e A HE Hb. unfold Eenv in HE.
  pose proof (HE x (bind_sub e A) Hb) as Heq. simpl in Heq.
  injection Heq as He HA. unfold Et. split; assumption.
Qed.



Lemma GTerm_app_inv : forall e1 e2, GTerm (trm_app e1 e2) ->
  GTerm e1 /\ GTerm e2.
Proof.
  intros e1 e2 [HE HL].
  assert (Hrec : lc_rec 0 (trm_app e1 e2)) by (apply lc_trm_lc_rec; exact HL).
  simpl in Hrec. destruct Hrec as [Hl1 Hl2].
  destruct (@Et_app_inv e1 e2 HE) as [HE1 HE2].
  split.
  - split; [exact HE1 | apply lc_rec_0_lc_trm; exact Hl1].
  - split; [exact HE2 | apply lc_rec_0_lc_trm; exact Hl2].
Qed.

Lemma GTerm_abs_inv : forall e A b, GTerm (trm_abs e A b) ->
  GTerm e /\ GTerm A /\ (forall x, GTerm (b ^ x)).
Proof.
  intros e A b [HE HL].
  destruct (@Et_abs_inv e A b HE) as [HEe [HEA HEb]].
  destruct (@lc_trm_abs_inv e A b HL) as [Hle [HlA Hlb]].
  split.
  - split; assumption.
  - split.
    + split; assumption.
    + intro x. split.
      * apply Et_open; [exact HEb|apply (Et_var x)].
      * apply Hlb.
Qed.

Lemma GTerm_prod_inv : forall e A b, GTerm (trm_prod e A b) ->
  GTerm e /\ GTerm A /\ (forall x, GTerm (b ^ x)).
Proof.
  intros e A b [HE HL].
  destruct (@Et_prod_inv e A b HE) as [HEe [HEA HEb]].
  destruct (@lc_trm_prod_inv e A b HL) as [Hle [HlA Hlb]].
  split.
  - split; assumption.
  - split.
    + split; assumption.
    + intro x. split.
      * apply Et_open; [exact HEb|apply (Et_var x)].
      * apply Hlb.
Qed.

Lemma GTerm_castup_inv : forall A e, GTerm (trm_castup A e) ->
  GTerm A /\ GTerm e.
Proof.
  intros A e [HE HL].
  assert (Hrec : lc_rec 0 (trm_castup A e)) by (apply lc_trm_lc_rec; exact HL).
  simpl in Hrec. destruct Hrec as [HlA Hle].
  destruct (@Et_castup_inv A e HE) as [HEA HEe].
  split.
  - split; [exact HEA | apply lc_rec_0_lc_trm; exact HlA].
  - split; [exact HEe | apply lc_rec_0_lc_trm; exact Hle].
Qed.

Lemma GTerm_castdn_inv : forall e, GTerm (trm_castdn e) -> GTerm e.
Proof.
  intros e [HE HL].
  assert (Hrec : lc_rec 0 (trm_castdn e)) by (apply lc_trm_lc_rec; exact HL).
  simpl in Hrec.
  pose proof (@Et_castdn_inv e HE) as HEe.
  split; [exact HEe | apply lc_rec_0_lc_trm; exact Hrec].
Qed.

Lemma GEnv_push : forall G x e A, GEnv G -> x # G -> GTerm e -> GTerm A ->
  GEnv (G & x ~ bind_sub e A).
Proof.
  intros G x e A [Hok [Hlc HEE]] Hx [HEe Hle] [HEA HlA].
  split.
  - apply ok_push; [exact Hok|exact Hx].
  - split.
    + apply lc_env_push; assumption.
    + apply Eenv_push; assumption.
Qed.

Lemma GEnv_push_erased : forall G x e A, GEnv G -> x # G ->
  lc_trm e -> lc_trm A -> GEnv (G & x ~ bind_sub [# e #] [# A #]).
Proof.
  intros G x e A [Hok [Hlc HEE]] Hx Hle HlA.
  split.
  - apply ok_push; [exact Hok|exact Hx].
  - split.
    + apply lc_env_push_erased; assumption.
    + apply Eenv_push_erased; assumption.
Qed.

(* [dsub] only looks at the source component of a binding, never at the
   target component.  This invariance lets us compare environments whose
   binders have the same sources but different targets. *)

Definition src_binds (G:env) (x:var) (e:trm) : Prop :=
  exists A, binds x (bind_sub e A) G.

Definition Esrc (G G':env) : Prop :=
  forall x e, src_binds G x e <-> src_binds G' x e.

Lemma Esrc_refl : forall G, Esrc G G.
Proof. intros G x e. split; auto. Qed.

Lemma Esrc_sym : forall G G', Esrc G G' -> Esrc G' G.
Proof. intros G G' H x e. split; intro Hx; apply H; exact Hx. Qed.

Lemma Esrc_fresh : forall G G' x, Esrc G G' -> x # G -> x # G'.
Proof.
  intros G G' x HE Hx Hb.
  apply get_some in Hb as [b Hb].
  destruct b as [e A].
  apply Hx.
  destruct (proj2 (HE x e) (ex_intro _ A Hb)) as [A0 Hb0].
  eapply get_some_inv. apply binds_get. exact Hb0.
Qed.

Lemma Esrc_fresh_inv : forall G G' x, Esrc G G' -> x # G' -> x # G.
Proof.
  intros G G' x HE Hx Hb.
  apply get_some in Hb as [b Hb].
  destruct b as [e A].
  apply Hx.
  destruct (proj1 (HE x e) (ex_intro _ A Hb)) as [A0 Hb0].
  eapply get_some_inv. apply binds_get. exact Hb0.
Qed.

Lemma Esrc_push : forall G G' x e A A',
  Esrc G G' -> x # G -> x # G' ->
  Esrc (G & x ~ bind_sub e A) (G' & x ~ bind_sub e A').
Proof.
  intros G G' x e A A' HE Hx Hx' y f. split; intro H.
  - destruct H as [B HB].
    apply binds_push_inv in HB as [[Heq HB']|[Hneq HB']].
    + inversion Heq; subst. injection HB' as Hf HB. subst f. subst B.
      exists A'. apply binds_push_eq.
    + destruct (proj1 (HE y f) (ex_intro _ B HB')) as [B' HB''].
      exists B'. apply binds_push_neq; [exact HB''|exact Hneq].
  - destruct H as [B HB].
    apply binds_push_inv in HB as [[Heq HB']|[Hneq HB']].
    + inversion Heq; subst. injection HB' as Hf HB. subst f. subst B.
      exists A. apply binds_push_eq.
    + destruct (proj2 (HE y f) (ex_intro _ B HB')) as [B' HB''].
      exists B'. apply binds_push_neq; [exact HB''|exact Hneq].
Qed.

Lemma dsub_src_env_irrel : forall G a b, dsub G a b ->
  forall G', Esrc G G' -> ok G' -> dsub G' a b.
Proof.
  intros G a b H.
  induction H as
    [ G0 Hok0
    | G0 y e0 A0 Hok0 Hb
    | e1 A0 G0 y e2 Hb Hd IHd
    | G0 e0 Hok0 Hlc
    | L0 G0 e1v e2v e3v A0 Hok0 Hbody IHb
    | G0 e1v e2v A0 HlcA Hd IHd
    | L0 G0 e0 A0 B0 C0 D0 Hd IHd Hbody IHb
    | G0 A0 e1v e2v HlcA Hd IHd
    | G0 e1v e2v Hd IHd ];
    intros G' HE HokG.
  - apply dsub_star. exact HokG.
  - destruct (proj1 (HE y e0) (ex_intro _ A0 Hb)) as [A' Hb'].
    eapply dsub_var_refl; eassumption.
  - destruct (proj1 (HE y e1) (ex_intro _ A0 Hb)) as [A' Hb'].
    eapply dsub_var_trans; [exact Hb'|].
    apply IHd. exact HE. exact HokG.
  - eapply dsub_top; [exact HokG|exact Hlc].
  - eapply dsub_lam with (L := L0 \u dom G0 \u dom G').
    + exact HokG.
    + intros y Hy.
      apply notin_union_r in Hy as [HyL HyRest].
      apply notin_union_r in HyRest as [HyG HyG'].
      assert (HEy : Esrc (G0 & y ~ bind_sub [#e3v#] [#A0#])
                         (G' & y ~ bind_sub [#e3v#] [#A0#]))
        by (apply Esrc_push; assumption).
      assert (Hoky : ok (G' & y ~ bind_sub [#e3v#] [#A0#]))
        by (apply ok_push; assumption).
      exact (IHb y HyL (G' & y ~ bind_sub [#e3v#] [#A0#]) HEy Hoky).
  - eapply dsub_app; [exact HlcA|]. apply IHd; assumption.
  - eapply dsub_pi with (L := L0 \u dom G0 \u dom G').
    + apply IHd; assumption.
    + intros y Hy.
      apply notin_union_r in Hy as [HyL HyRest].
      apply notin_union_r in HyRest as [HyG HyG'].
      assert (HEy : Esrc (G0 & y ~ bind_sub [#e0#] [#C0#])
                         (G' & y ~ bind_sub [#e0#] [#C0#]))
        by (apply Esrc_push; assumption).
      assert (Hoky : ok (G' & y ~ bind_sub [#e0#] [#C0#]))
        by (apply ok_push; assumption).
      exact (IHb y HyL (G' & y ~ bind_sub [#e0#] [#C0#]) HEy Hoky).
  - eapply dsub_castup; [exact HlcA|]. apply IHd; assumption.
  - eapply dsub_castdn. apply IHd; assumption.
Qed.

Definition P1 (G:env) (a b:trm) : Prop :=
  forall c, GEnv G -> GTerm a -> GTerm b -> GTerm c ->
    dsub G b c -> dsub G a c.

Definition P2 (G:env) (a b:trm) : Prop :=
  forall L, GEnv G -> GTerm L -> GTerm a -> GTerm b ->
    dsub G L a -> dsub G L b.


Lemma dsub_comp_rhs_var : forall G L x,
  dsub G L (trm_var_f x) ->
  forall e2, dsub G (trm_var_f x) e2 -> dsub G L e2.
Proof.
  intros G L x Hd.
  remember (trm_var_f x) as T eqn:ET.
  revert x ET.
  induction Hd as
    [ G0 Hok
    | G0 y e0 A0 Hok Hb
    | e1 A0 G0 y e2' Hb Hd' IHd'
    | G0 e0 Hok Hlc
    | L0 G0 e1v e2v e3v A0 Hok Hbody IHb
    | G0 e1v e2v A0 HlcA Hd' IHd'
    | L0 G0 e0 A0 B0 C0 D0 Hd' IHd' Hbody IHb
    | G0 A0 e1v e2v HlcA Hd' IHd'
    | G0 e1v e2v Hd' IHd' ];
    intros x0 ET e2z H2.
  - (* star *) discriminate ET.
  - (* var_refl *) injection ET as Hy. subst x0. exact H2.
  - (* var_trans *) eapply dsub_var_trans; [exact Hb|].
    apply (IHd' x0 ET e2z H2).
  - (* top *) discriminate ET.
  - (* lam *) discriminate ET.
  - (* app *) discriminate ET.
  - (* pi *) discriminate ET.
  - (* castup *) discriminate ET.
  - (* castdn *) discriminate ET.
Qed.


Lemma dsub_comp_app_aux : forall G L f A e2,
  GEnv G -> GTerm L ->
  dsub G L (trm_app f A) ->
  (forall L', GTerm L' -> dsub G L' f -> dsub G L' e2) ->
  dsub G L (trm_app e2 A).
Proof.
  intros G L f A e2 HGE HGL HD.
  remember (trm_app f A) as T eqn:ET.
  revert f A ET.
  induction HD as
    [ G0 Hok
    | G0 y e0 A0 Hok Hb
    | d1 A0 G0 y e2' Hb Hd' IHd'
    | G0 e0 Hok Hlc
    | L0 G0 d1 d2 e3v A0 Hok Hbody IHb
    | G0 d1 d2 A0 HlcA Hd' IHd'
    | L0 G0 e0 A0 B0 C0 D0 Hd' IHd' Hbody IHb
    | G0 A0 d1 d2 HlcA Hd' IHd'
    | G0 d1 d2 Hd' IHd' ];
    intros f0 Aann ET HP.
  - (* star *) discriminate ET.
  - (* var_refl *) discriminate ET.
  - (* var_trans *) eapply dsub_var_trans; [exact Hb|].
    assert (HGd1 : GTerm d1).
    { split.
      - apply (proj1 (@Eenv_binds G0 y d1 A0 (GEnv_Eenv G0 HGE) Hb)).
      - apply (proj1 (@lc_env_ok_binds G0 y d1 A0 (GEnv_lc G0 HGE) Hb)). }
    apply (IHd' HGE HGd1 f0 Aann ET HP).
  - (* top *) discriminate ET.
  - (* lam *) discriminate ET.
  - (* app *) injection ET as Hd2 HA. subst d2. subst Aann.
    assert (HGd1 : GTerm d1).
    { destruct (@GTerm_app_inv d1 A0 HGL) as [H1 H2]. exact H1. }
    eapply dsub_app; [exact HlcA|].
    apply (HP d1 HGd1 Hd').
  - (* pi *) discriminate ET.
  - (* castup *) discriminate ET.
  - (* castdn *) discriminate ET.
Qed.


Lemma dsub_comp_castup_aux : forall G L A f e2,
  GEnv G -> GTerm L ->
  dsub G L (trm_castup A f) ->
  (forall L', GTerm L' -> dsub G L' f -> dsub G L' e2) ->
  dsub G L (trm_castup A e2).
Proof.
  intros G L A f e2 HGE HGL HD.
  remember (trm_castup A f) as T eqn:ET.
  revert A f ET.
  induction HD as
    [ G0 Hok
    | G0 y e0 A0 Hok Hb
    | d1 A0 G0 y e2' Hb Hd' IHd'
    | G0 e0 Hok Hlc
    | L0 G0 d1 d2 e3v A0 Hok Hbody IHb
    | G0 d1 d2 A0 HlcA Hd' IHd'
    | L0 G0 e0 A0 B0 C0 D0 Hd' IHd' Hbody IHb
    | G0 A0 d1 d2 HlcA Hd' IHd'
    | G0 d1 d2 Hd' IHd' ];
    intros Ac fc ET HP.
  - (* star *) discriminate ET.
  - (* var_refl *) discriminate ET.
  - (* var_trans *) eapply dsub_var_trans; [exact Hb|].
    assert (HGd1 : GTerm d1).
    { split.
      - apply (proj1 (@Eenv_binds G0 y d1 A0 (GEnv_Eenv G0 HGE) Hb)).
      - apply (proj1 (@lc_env_ok_binds G0 y d1 A0 (GEnv_lc G0 HGE) Hb)). }
    apply (IHd' HGE HGd1 Ac fc ET HP).
  - (* top *) discriminate ET.
  - (* lam *) discriminate ET.
  - (* app *) discriminate ET.
  - (* pi *) discriminate ET.
  - (* castup *) injection ET as HA Hd2. subst d2. subst Ac.
    assert (HGd1 : GTerm d1).
    { destruct (@GTerm_castup_inv A0 d1 HGL) as [_ H1]. exact H1. }
    eapply dsub_castup; [exact HlcA|].
    apply (HP d1 HGd1 Hd').
  - (* castdn *) discriminate ET.
Qed.

Lemma dsub_comp_castdn_aux : forall G L f e2,
  GEnv G -> GTerm L ->
  dsub G L (trm_castdn f) ->
  (forall L', GTerm L' -> dsub G L' f -> dsub G L' e2) ->
  dsub G L (trm_castdn e2).
Proof.
  intros G L f e2 HGE HGL HD.
  remember (trm_castdn f) as T eqn:ET.
  revert f ET.
  induction HD as
    [ G0 Hok
    | G0 y e0 A0 Hok Hb
    | d1 A0 G0 y e2' Hb Hd' IHd'
    | G0 e0 Hok Hlc
    | L0 G0 d1 d2 e3v A0 Hok Hbody IHb
    | G0 d1 d2 A0 HlcA Hd' IHd'
    | L0 G0 e0 A0 B0 C0 D0 Hd' IHd' Hbody IHb
    | G0 A0 d1 d2 HlcA Hd' IHd'
    | G0 d1 d2 Hd' IHd' ];
    intros fc ET HP.
  - (* star *) discriminate ET.
  - (* var_refl *) discriminate ET.
  - (* var_trans *) eapply dsub_var_trans; [exact Hb|].
    assert (HGd1 : GTerm d1).
    { split.
      - apply (proj1 (@Eenv_binds G0 y d1 A0 (GEnv_Eenv G0 HGE) Hb)).
      - apply (proj1 (@lc_env_ok_binds G0 y d1 A0 (GEnv_lc G0 HGE) Hb)). }
    apply (IHd' HGE HGd1 fc ET HP).
  - (* top *) discriminate ET.
  - (* lam *) discriminate ET.
  - (* app *) discriminate ET.
  - (* pi *) discriminate ET.
  - (* castup *) discriminate ET.
  - (* castdn *) injection ET as Hd2. subst d2.
    assert (HGd1 : GTerm d1).
    { apply (@GTerm_castdn_inv d1 HGL). }
    eapply dsub_castdn.
    apply (HP d1 HGd1 Hd').
Qed.


Lemma dsub_comp_abs_aux : forall G L e3 A b1 b2 (Lh:vars),
  GEnv G -> GTerm L ->
  GTerm (trm_abs e3 A b1) -> GTerm (trm_abs e3 A b2) ->
  dsub G L (trm_abs e3 A b1) ->
  (forall y, y # G -> y \notin Lh -> forall L', GTerm L' ->
      dsub (G & y ~ bind_sub [# e3 #] [# A #]) L' (b1 ^ y) ->
      dsub (G & y ~ bind_sub [# e3 #] [# A #]) L' (b2 ^ y)) ->
  dsub G L (trm_abs e3 A b2).
Proof.
  intros G L e3 A b1 b2 Lh HGE HGL HGa HGb HD Hbody.
  destruct (@GTerm_abs_inv e3 A b1 HGa) as [He3 [HA Hb1]].
  clear He3 HA Hb1 HGa HGb.
  remember (trm_abs e3 A b1) as T eqn:ET.
  revert e3 A b1 Hbody ET.
  induction HD as
    [ G0 Hok
    | G0 y e0 A0 Hok Hb
    | d1 A0 G0 y e2' Hb Hd' IHd'
    | G0 e0 Hok Hlc
    | L0 G0 d1 d2 d3 Ad HokD HbodyD IHbD
    | G0 d1 d2 A0 HlcA Hd' IHd'
    | L0 G0 e0 A0 B0 C0 D0 Hd' IHd' HbodyD IHbD
    | G0 A0 d1 d2 HlcA Hd' IHd'
    | G0 d1 d2 Hd' IHd' ];
    intros e3x Ax b1x Hbdy ET.
  - (* star *) discriminate ET.
  - (* var_refl *) discriminate ET.
  - (* var_trans *) eapply dsub_var_trans; [exact Hb|].
    assert (HGd1 : GTerm d1).
    { split.
      - apply (proj1 (@Eenv_binds G0 y d1 A0 (GEnv_Eenv G0 HGE) Hb)).
      - apply (proj1 (@lc_env_ok_binds G0 y d1 A0 (GEnv_lc G0 HGE) Hb)). }
    apply (IHd' HGE HGd1 e3x Ax b1x Hbdy ET).
  - (* top *) discriminate ET.
  - (* lam *) injection ET as He HAA Hbb.
    subst d3. subst Ad. subst d2.
    eapply dsub_lam with (L := L0 \u dom G0 \u Lh).
    + exact HokD.
    + intros y Hy.
      apply notin_union_r in Hy as [HyL HyRest].
      apply notin_union_r in HyRest as [HyG HyLh].
      assert (HGLy : GTerm (d1 ^ y)).
      { destruct (@GTerm_abs_inv e3x Ax d1 HGL) as [_ [_ HbodyL]].
        apply HbodyL. }
      apply (Hbdy y HyG HyLh (d1 ^ y) HGLy).
      apply HbodyD. exact HyL.
  - (* app *) discriminate ET.
  - (* pi *) discriminate ET.
  - (* castup *) discriminate ET.
  - (* castdn *) discriminate ET.
Qed.

Lemma dsub_comp_prod_aux : forall G L e A B C D (Lh:vars),
  GEnv G -> GTerm L ->
  dsub G L (trm_prod e A B) ->
  (forall Z, GTerm Z -> dsub G A Z -> dsub G C Z) ->
  (forall y, y # G -> y \notin Lh -> forall L', GTerm L' ->
      dsub (G & y ~ bind_sub [# e #] [# C #]) L' (B ^ y) ->
      dsub (G & y ~ bind_sub [# e #] [# C #]) L' (D ^ y)) ->
  dsub G L (trm_prod e C D).
Proof.
  intros G L e A B C D Lh HGE HGL HD HP1 HP2.
  remember (trm_prod e A B) as T eqn:ET.
  revert e A B HP1 HP2 ET.
  induction HD as
    [ G0 Hok0
    | G0 y e0 A0 Hok0 Hb
    | d1 A0 G0 y e2' Hb Hd' IHd'
    | G0 e0 Hok0 Hlc
    | Lp Gp d1 d2 d3 Ad HokD HbodyD IHbD
    | G0 d1 d2 A0 HlcA Hd' IHd'
    | Lp Gp ee AA BB CC DD HdP IHdP HbodyP IHbP
    | G0 A0 d1 d2 HlcA Hd' IHd'
    | G0 d1 d2 Hd' IHd' ];
    intros ex Ax Bx HP1x HP2x ET.
  - (* star *) discriminate ET.
  - (* var_refl *) discriminate ET.
  - (* var_trans *) eapply dsub_var_trans; [exact Hb|].
    assert (HGd1 : GTerm d1).
    { split.
      - apply (proj1 (@Eenv_binds G0 y d1 A0 (GEnv_Eenv G0 HGE) Hb)).
      - apply (proj1 (@lc_env_ok_binds G0 y d1 A0 (GEnv_lc G0 HGE) Hb)). }
    exact (IHd' HGE HGd1 ex Ax Bx HP1x HP2x ET).
  - (* top *) discriminate ET.
  - (* lam *) discriminate ET.
  - (* app *) discriminate ET.
  - (* pi *) injection ET as Hee HCC HDD. subst ee. subst CC. subst DD.
    destruct (@GTerm_prod_inv ex AA BB HGL) as [HGee [HGAA HGBB]].
    eapply dsub_pi with (L := Lp \u dom Gp \u Lh).
    + apply (HP1x AA HGAA HdP).
    + intros y Hy.
      apply notin_union_r in Hy as [HyL HyRest].
      apply notin_union_r in HyRest as [HyG HyLh].
      assert (HEy : Esrc (Gp & y ~ bind_sub [# ex #] [# Ax #])
                         (Gp & y ~ bind_sub [# ex #] [# C #])).
      { apply Esrc_push; [apply Esrc_refl|exact HyG|exact HyG]. }
      assert (Hoky : ok (Gp & y ~ bind_sub [# ex #] [# C #]))
        by (apply ok_push; [apply (GEnv_ok Gp HGE)|exact HyG]).
      assert (HDy : dsub (Gp & y ~ bind_sub [# ex #] [# C #]) (BB ^ y) (Bx ^ y)).
      { apply (@dsub_src_env_irrel (Gp & y ~ bind_sub [# ex #] [# Ax #])
                 (BB ^ y) (Bx ^ y) (HbodyP y HyL)
                 (Gp & y ~ bind_sub [# ex #] [# C #]) HEy Hoky). }
      exact (HP2x y HyG HyLh (BB ^ y) (HGBB y) HDy).
  - (* castup *) discriminate ET.
  - (* castdn *) discriminate ET.
Qed.

Lemma dsub_trans_aux : forall G a b, dsub G a b -> P1 G a b /\ P2 G a b.
Proof.
  intros G a b H.
  apply (dsub_ind (fun G a b => P1 G a b /\ P2 G a b)).
  - (* star *) split.
    + intros c HG Ha Hta Hc Hbc. exact Hbc.
    + intros L0 HG HL Ha Hta HD. exact HD.
  - (* var_refl *) split.
    + intros c HG Ha Hta Hc Hbc. exact Hbc.
    + intros L0 HG HL Ha Hta HD. exact HD.
  - (* var_trans *) intros e1 A0 G0 x0 e2 Hb Hd IHd. split.
    + (* P1 *) intros c HG Ha Hta Hc Hbc.
      destruct IHd as [IH1d IH2d].
      unfold P1 in IH1d.
      assert (He1 : GTerm e1).
      { split.
        - apply (proj1 (@Eenv_binds G0 x0 e1 A0 (GEnv_Eenv G0 HG) Hb)).
        - apply (proj1 (@lc_env_ok_binds G0 x0 e1 A0 (GEnv_lc G0 HG) Hb)). }
      apply (dsub_var_trans Hb).
      exact (IH1d c HG He1 Hta Hc Hbc).
    + (* P2 *) intros L0 HG HL Ha Hta HD.
      apply (@dsub_comp_rhs_var G0 L0 x0 HD e2 (dsub_var_trans Hb Hd)).
  - (* top *) split.
    + intros c HG Ha Hb Hc Hbc.
      assert (Heqc : c = trm_top) by exact (@dsub_lhs_top G0 c Hbc).
      subst c.
      apply dsub_top; [ apply (GEnv_ok G0 HG) | apply (proj2 Ha) ].
    + intros L0 HG HL Ha Hb HD.
      apply dsub_top; [ apply (GEnv_ok G0 HG) | apply (proj2 HL) ].
  - (* lam *) intros L G0 e1v e2v e3v A0 Hok Hbody IHb. split.
    + (* P1 *) intros c HG Ha Hta Hc Hbc.
      destruct (@dsub_lhs_abs G0 e3v A0 e2v c Hbc) as
        [Heqc | [Hok2 [L2 [b2 [Heqc Hbody2]]]]].
      * subst c. apply dsub_top; [ apply (GEnv_ok G0 HG) | apply (proj2 Ha) ].
      * subst c.
        destruct (@GTerm_abs_inv e3v A0 e1v Ha) as [Ge3 [GA0 Gb1]].
        destruct (@GTerm_abs_inv e3v A0 e2v Hta) as [_ [_ Gb2]].
        destruct (@GTerm_abs_inv e3v A0 b2 Hc) as [_ [_ Gb2']].
        eapply dsub_lam with (L := L \u L2 \u dom G0).
        -- exact Hok2.
        -- intros y Hy.
           apply notin_union_r in Hy as [HyL HyRest].
           apply notin_union_r in HyRest as [HyL2 HyG].
           assert (HGx : GEnv (G0 & y ~ bind_sub [# e3v #] [# A0 #])).
           { apply GEnv_push_erased; [exact HG|exact HyG|apply (proj2 Ge3)|apply (proj2 GA0)]. }
           destruct (IHb y HyL) as [IH1b IH2b]. unfold P1 in IH1b.
           apply (IH1b (b2 ^ y) HGx (Gb1 y) (Gb2 y) (Gb2' y) (Hbody2 y HyL2)).
    + (* P2 *) intros L0 HG HL Ha Hta HD.
      destruct (@GTerm_abs_inv e3v A0 e1v Ha) as [Ge3 [GA0 Gb1]].
      destruct (@GTerm_abs_inv e3v A0 e2v Hta) as [_ [_ Gb2]].
      apply (@dsub_comp_abs_aux G0 L0 e3v A0 e1v e2v L HG HL Ha Hta HD).
      intros y HyG HyL L' GL' HDbody.
      destruct (IHb y HyL) as [IH1b IH2b]. unfold P2 in IH2b.
      assert (HGx : GEnv (G0 & y ~ bind_sub [# e3v #] [# A0 #])).
      { apply GEnv_push_erased; [exact HG|exact HyG|apply (proj2 Ge3)|apply (proj2 GA0)]. }
      apply (IH2b L' HGx GL' (Gb1 y) (Gb2 y) HDbody).
  - (* app *) intros G0 e1v e2v A0 HlcA Hd IHd. split.
    + (* P1 *) intros c HG Ha Hta Hc Hbc.
      destruct (@dsub_lhs_app G0 e2v A0 c Hbc) as
        [Heqc | [HlcA' [b2 [Heqc Hd2]]]].
      * subst c. apply dsub_top; [ apply (GEnv_ok G0 HG) | apply (proj2 Ha) ].
      * subst c.
        destruct IHd as [IH1d IH2d]. unfold P1 in IH1d.
        destruct (@GTerm_app_inv e1v A0 Ha) as [Ge1 _].
        destruct (@GTerm_app_inv e2v A0 Hta) as [Ge2 _].
        destruct (@GTerm_app_inv b2 A0 Hc) as [Gb2 _].
        eapply dsub_app; [exact HlcA'|].
        apply (IH1d b2 HG Ge1 Ge2 Gb2 Hd2).
    + (* P2 *) intros L0 HG HL Ha Hta HD.
      destruct IHd as [IH1d IH2d]. unfold P2 in IH2d.
      destruct (@GTerm_app_inv e1v A0 Ha) as [Ge1 _].
      destruct (@GTerm_app_inv e2v A0 Hta) as [Ge2 _].
      apply (@dsub_comp_app_aux G0 L0 e1v A0 e2v HG HL HD).
      intros L' GL' HD'. exact (IH2d L' HG GL' Ge1 Ge2 HD').
  - (* pi *) intros L G0 e0 A0 B0 C0 D0 Hd IHd Hbody IHb. split.
    + (* P1 *) intros c HG Ha Hta Hc Hbc.
      destruct (@dsub_lhs_prod G0 e0 C0 D0 c Hbc) as
        [Heqc | [L2 [CC [DD [Heqc [Hds Hbody2]]]]]].
      * subst c. apply dsub_top; [ apply (GEnv_ok G0 HG) | apply (proj2 Ha) ].
      * subst c.
        destruct (@GTerm_prod_inv e0 A0 B0 Ha) as [Ge0 [GA0 GB0]].
        destruct (@GTerm_prod_inv e0 C0 D0 Hta) as [_ [GC0 GD0]].
        destruct (@GTerm_prod_inv e0 CC DD Hc) as [_ [GCC GDD]].
        destruct IHd as [IH1d IH2d]. unfold P2 in IH2d.
        eapply dsub_pi with (L := L \u L2 \u dom G0).
        -- exact (IH2d CC HG GCC GC0 GA0 Hds).
        -- intros y Hy.
           apply notin_union_r in Hy as [HyL HyRest].
           apply notin_union_r in HyRest as [HyL2 HyG].
           assert (HGx : GEnv (G0 & y ~ bind_sub [# e0 #] [# C0 #])).
           { apply GEnv_push_erased;
             [exact HG|exact HyG|apply (proj2 Ge0)|apply (proj2 GC0)]. }
           assert (HEy : Esrc (G0 & y ~ bind_sub [# e0 #] [# CC #])
                              (G0 & y ~ bind_sub [# e0 #] [# C0 #])).
           { apply Esrc_push; [apply Esrc_refl|exact HyG|exact HyG]. }
           assert (HD2 : dsub (G0 & y ~ bind_sub [# e0 #] [# C0 #])
                              (D0 ^ y) (DD ^ y)).
           { apply (@dsub_src_env_irrel
                      (G0 & y ~ bind_sub [# e0 #] [# CC #])
                      (D0 ^ y) (DD ^ y) (Hbody2 y HyL2)
                      (G0 & y ~ bind_sub [# e0 #] [# C0 #]) HEy
                      (GEnv_ok (G0 & y ~ bind_sub [# e0 #] [# C0 #]) HGx)). }
           destruct (IHb y HyL) as [IH1b IH2b]. unfold P1 in IH1b.
           assert (Hres : dsub (G0 & y ~ bind_sub [# e0 #] [# C0 #])
                               (B0 ^ y) (DD ^ y)).
           { exact (IH1b (DD ^ y) HGx (GB0 y) (GD0 y) (GDD y) HD2). }
           assert (HGxCC : GEnv (G0 & y ~ bind_sub [# e0 #] [# CC #])).
           { apply GEnv_push_erased;
             [exact HG|exact HyG|apply (proj2 Ge0)|apply (proj2 GCC)]. }
           exact (@dsub_src_env_irrel
                    (G0 & y ~ bind_sub [# e0 #] [# C0 #])
                    (B0 ^ y) (DD ^ y) Hres
                    (G0 & y ~ bind_sub [# e0 #] [# CC #])
                    (Esrc_sym _ _ HEy)
                    (GEnv_ok (G0 & y ~ bind_sub [# e0 #] [# CC #]) HGxCC)).
    + (* P2 *) intros L0 HG HL Ha Hta HD.
      destruct IHd as [IH1d IH2d]. unfold P1 in IH1d.
      destruct (@GTerm_prod_inv e0 A0 B0 Ha) as [Ge0 [GA0 GB0]].
      destruct (@GTerm_prod_inv e0 C0 D0 Hta) as [_ [GC0 GD0]].
      apply (@dsub_comp_prod_aux G0 L0 e0 A0 B0 C0 D0 L HG HL HD).
      * intros Z GZ HAZ. exact (IH1d Z HG GC0 GA0 GZ HAZ).
      * intros y HyG HyL L' GL' HBdy.
        destruct (IHb y HyL) as [IH1b IH2b]. unfold P2 in IH2b.
        assert (HGx : GEnv (G0 & y ~ bind_sub [# e0 #] [# C0 #])).
        { apply GEnv_push_erased;
          [exact HG|exact HyG|apply (proj2 Ge0)|apply (proj2 GC0)]. }
        exact (IH2b L' HGx GL' (GB0 y) (GD0 y) HBdy).
  - (* castup *) intros G0 A0 e1v e2v HlcA Hd IHd. split.
    + (* P1 *) intros c HG Ha Hta Hc Hbc.
      destruct (@dsub_lhs_castup G0 A0 e2v c Hbc) as
        [Heqc | [HlcA' [b2 [Heqc Hd2]]]].
      * subst c. apply dsub_top; [ apply (GEnv_ok G0 HG) | apply (proj2 Ha) ].
      * subst c.
        destruct IHd as [IH1d IH2d]. unfold P1 in IH1d.
        destruct (@GTerm_castup_inv A0 e1v Ha) as [_ Ge1].
        destruct (@GTerm_castup_inv A0 e2v Hta) as [_ Ge2].
        destruct (@GTerm_castup_inv A0 b2 Hc) as [_ Gb2].
        eapply dsub_castup; [exact HlcA'|].
        apply (IH1d b2 HG Ge1 Ge2 Gb2 Hd2).
    + (* P2 *) intros L0 HG HL Ha Hta HD.
      destruct IHd as [IH1d IH2d]. unfold P2 in IH2d.
      destruct (@GTerm_castup_inv A0 e1v Ha) as [_ Ge1].
      destruct (@GTerm_castup_inv A0 e2v Hta) as [_ Ge2].
      apply (@dsub_comp_castup_aux G0 L0 A0 e1v e2v HG HL HD).
      intros L' GL' HD'. exact (IH2d L' HG GL' Ge1 Ge2 HD').
  - (* castdn *) intros G0 e1v e2v Hd IHd. split.
    + (* P1 *) intros c HG Ha Hta Hc Hbc.
      destruct (@dsub_lhs_castdn G0 e2v c Hbc) as
        [Heqc | [b2 [Heqc Hd2]]].
      * subst c. apply dsub_top; [ apply (GEnv_ok G0 HG) | apply (proj2 Ha) ].
      * subst c.
        destruct IHd as [IH1d IH2d]. unfold P1 in IH1d.
        pose proof (@GTerm_castdn_inv e1v Ha) as Ge1.
        pose proof (@GTerm_castdn_inv e2v Hta) as Ge2.
        pose proof (@GTerm_castdn_inv b2 Hc) as Gb2.
        eapply dsub_castdn.
        apply (IH1d b2 HG Ge1 Ge2 Gb2 Hd2).
    + (* P2 *) intros L0 HG HL Ha Hta HD.
      destruct IHd as [IH1d IH2d]. unfold P2 in IH2d.
      pose proof (@GTerm_castdn_inv e1v Ha) as Ge1.
      pose proof (@GTerm_castdn_inv e2v Hta) as Ge2.
      apply (@dsub_comp_castdn_aux G0 L0 e1v e2v HG HL HD).
      intros L' GL' HD'. exact (IH2d L' HG GL' Ge1 Ge2 HD').
  - (* the derivation argument *) exact H.
Qed.


(* from /tmp/EnvProbe2.v *)
Lemma concat_cons : forall (G:env) y b (F:env),
  G & ((y,b) :: F) = (G & F) & y ~ b.
Proof. intros. rewrite cons_eq_push. rewrite concat_assoc_r. reflexivity. Qed.

Lemma GEnv_tail : forall (G:env) y b, GEnv (G & y ~ b) -> GEnv G.
Proof.
  intros G y b [Hok [Hlc HE]].
  destruct (@ok_push_inv binding G y b Hok) as [HokG HyG].
  split; [exact HokG|]. split.
  - unfold lc_env in *. intros z c Hb.
    assert (Hzy : z <> y). { intro Heq. apply HyG. rewrite <- Heq.
      exact (@get_some_inv binding z c G (binds_get Hb)). }
    exact (Hlc z c (@binds_push_neq binding z y c b G Hb Hzy)).
  - unfold Eenv in *. intros z c Hb.
    assert (Hzy : z <> y). { intro Heq. apply HyG. rewrite <- Heq.
      exact (@get_some_inv binding z c G (binds_get Hb)). }
    exact (HE z c (@binds_push_neq binding z y c b G Hb Hzy)).
Qed.

Lemma Et_subst : forall v x e, Et v -> Et e -> Et (subst_trm v x e).
Proof.
  intros v x e Hv He. unfold Et in *. rewrite remove_anno_subst.
  rewrite Hv, He. reflexivity.
Qed.

Lemma GTerm_subst : forall v x e, GTerm v -> GTerm e -> GTerm (subst_trm v x e).
Proof.
  intros v x e [HEv HLv] [HEe HLe]. split.
  - apply Et_subst; assumption.
  - apply lc_trm_subst; assumption.
Qed.

Lemma GTerm_rem : forall e, GTerm e -> GTerm [# e #].
Proof.
  intros e [HE HL]. split.
  - apply Et_rem.
  - apply lc_trm_remove_anno. exact HL.
Qed.

Definition GBinding (b:binding) : Prop :=
  match b with bind_sub e A => GTerm e /\ GTerm A end.

Lemma GEnv_binds_binding : forall G y b, GEnv G -> binds y b G -> GBinding b.
Proof.
  intros G y b HG Hb. destruct b as [e A]. unfold GBinding.
  destruct HG as [_ [Hlc HE]].
  assert (HlcB : lc_trm e /\ lc_trm A).
  { exact (@lc_env_ok_binds G y e A Hlc Hb). }
  assert (HEB : Et e /\ Et A).
  { exact (@Eenv_binds G y e A HE Hb). }
  split; split.
  - exact (proj1 HEB). - exact (proj1 HlcB).
  - exact (proj2 HEB). - exact (proj2 HlcB).
Qed.

Lemma GBinding_subst : forall a x b, GTerm a -> GBinding b ->
  GBinding (subst_binding a x b).
Proof.
  intros a x [e A] Ha [He HA]. simpl in *. unfold GBinding. simpl.
  split.
  - apply GTerm_subst; assumption.
  - apply GTerm_subst; assumption.
Qed.

Lemma dom_subst_env : forall a x (F:env), dom (subst_env a x F) = dom F.
Proof.
  intros a x F. induction F as [| [y c] F' IH].
  - simpl. reflexivity.
  - simpl. rewrite cons_eq_push. rewrite dom_push.
    rewrite cons_eq_push. rewrite dom_push. rewrite IH. reflexivity.
Qed.

Lemma GEnv_subst_env : forall a x (G0 F:env),
  GEnv (G0 & F) -> GTerm a -> GEnv (G0 & subst_env a x F).
Proof.
  intros a x G0 F. revert G0. induction F as [| [y c] F' IH]; intros G0 HG Ha.
  - simpl. exact HG.
  - rewrite concat_cons in HG.
    assert (HGtail : GEnv (G0 & F')).
    { apply GEnv_tail in HG. exact HG. }
    assert (Hc : GBinding c).
    { apply (@GEnv_binds_binding (G0 & F' & y ~ c) y c HG).
      apply binds_push_eq. }
    assert (Hcsub : GBinding (subst_binding a x c)).
    { apply GBinding_subst; assumption. }
    destruct c as [e A]; simpl in Hcsub. unfold GBinding in Hcsub.
    destruct Hcsub as [[HEe HLe] [HEA HLA]].
    assert (GTe : GTerm (subst_trm a x e)) by (split; assumption).
    assert (GTA : GTerm (subst_trm a x A)) by (split; assumption).
    pose proof (GTerm_rem _ GTe) as HEe'.
    pose proof (GTerm_rem _ GTA) as HEA'.
    assert (HyG : y # (G0 & F')).
    { destruct (@ok_push_inv binding (G0 & F') y (bind_sub e A) (GEnv_ok _ HG))
        as [_ Hy]. exact Hy. }
    assert (HyT : y # (G0 & subst_env a x F')).
    { unfold notin in *. intro Hin.
      rewrite dom_concat in Hin. rewrite dom_subst_env in Hin.
      apply HyG. rewrite dom_concat. exact Hin. }
    simpl. rewrite concat_cons.
    apply GEnv_push; [exact (IH G0 HGtail Ha)|exact HyT|exact GTe|exact GTA].
Qed.


(* from /tmp/FvProbe.v *)
Lemma subst_trm_id : forall v x e, x \notin fv_trm e -> subst_trm v x e = e.
Proof.
  intros v x e. revert x. induction e; intros x0 H; simpl.
  - reflexivity.
  - (* var_f *) unfold subst_trm. simpl.
    destruct (classicT (x5 = x0)) as [Heq|Hneq].
    + exfalso. apply H. rewrite Heq. apply in_singleton_self.
    + reflexivity.
  - reflexivity. - reflexivity.
  - apply notin_union_r in H as [H1 H2]. f_equal; [apply IHe1|apply IHe2]; assumption.
  - apply notin_union_r in H as [H1 H2]. apply notin_union_r in H2 as [H2a H2b].
    f_equal; [apply IHe1|apply IHe2|apply IHe3]; assumption.
  - apply notin_union_r in H as [H1 H2]. apply notin_union_r in H2 as [H2a H2b].
    f_equal; [apply IHe1|apply IHe2|apply IHe3]; assumption.
  - apply notin_union_r in H as [H1 H2]. f_equal; [apply IHe1|apply IHe2]; assumption.
  - f_equal. apply IHe. exact H.
  - apply notin_union_r in H as [H1 H2]. f_equal; [apply IHe1|apply IHe2]; assumption.
Qed.

Lemma subst_binding_id : forall v x b, x \notin fv_binding b -> subst_binding v x b = b.
Proof.
  intros v x [e A] H. simpl in *. apply notin_union_r in H as [H1 H2].
  unfold subst_binding. simpl. f_equal; apply subst_trm_id; assumption.
Qed.

Lemma subst_env_id : forall v x (G:env), x \notin fv_in_values fv_binding G ->
  subst_env v x G = G.
Proof.
  intros v x G. induction G as [| [y b] G' IH]; intro H.
  - simpl. reflexivity.
  - rewrite cons_eq_push. rewrite subst_env_push.
    rewrite fv_in_values_cons_binding in H.
    apply notin_union_r in H as [Hb HG].
    rewrite (subst_binding_id v x b Hb). rewrite (IH HG). reflexivity.
Qed.

Lemma fv_open_rec_subset : forall x k e y,
  y \in fv_trm e -> y \in fv_trm (open_trm_wrt_trm_rec k (trm_var_f x) e).
Proof.
  intros x k e. revert k. induction e; intros k0 y Hy; simpl in *.
  - exfalso. exact (@in_empty_inv var y Hy).
  - exact Hy.
  - exfalso. exact (@in_empty_inv var y Hy).
  - exfalso. exact (@in_empty_inv var y Hy).
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|H2].
    + left. apply IHe1. exact H1.
    + right. apply IHe2. exact H2.
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|[H2|H3]].
    + left. apply IHe1. exact H1.
    + right. left. apply IHe2. exact H2.
    + right. right. apply IHe3. exact H3.
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|[H2|H3]].
    + left. apply IHe1. exact H1.
    + right. left. apply IHe2. exact H2.
    + right. right. apply IHe3. exact H3.
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|H2].
    + left. apply IHe1. exact H1.
    + right. apply IHe2. exact H2.
  - apply IHe. exact Hy.
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|H2].
    + left. apply IHe1. exact H1.
    + right. apply IHe2. exact H2.
Qed.

Lemma fv_open_rec_inv : forall x k e y,
  y \in fv_trm (open_trm_wrt_trm_rec k (trm_var_f x) e) ->
  y \in fv_trm e \/ y = x.
Proof.
  intros x k e. revert k. induction e; intros k0 y Hy; simpl in *.
  - destruct (classicT (k0 = n)) as [Heq|Hneq]; subst.
    + right. simpl in Hy. rewrite in_singleton in Hy. exact Hy.
    + exfalso. exact (@in_empty_inv var y Hy).
  - left. exact Hy.
  - exfalso. exact (@in_empty_inv var y Hy).
  - exfalso. exact (@in_empty_inv var y Hy).
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|H2].
    + destruct (IHe1 k0 y H1) as [L|R]; [left; left; exact L|right; exact R].
    + destruct (IHe2 k0 y H2) as [L|R]; [left; right; exact L|right; exact R].
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|[H2|H3]].
    + destruct (IHe1 k0 y H1) as [L|R].
      * left. left. exact L.
      * right. exact R.
    + destruct (IHe2 k0 y H2) as [L|R].
      * left. right. left. exact L.
      * right. exact R.
    + destruct (IHe3 (S k0) y H3) as [L|R].
      * left. right. right. exact L.
      * right. exact R.
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|[H2|H3]].
    + destruct (IHe1 k0 y H1) as [L|R].
      * left. left. exact L.
      * right. exact R.
    + destruct (IHe2 k0 y H2) as [L|R].
      * left. right. left. exact L.
      * right. exact R.
    + destruct (IHe3 (S k0) y H3) as [L|R].
      * left. right. right. exact L.
      * right. exact R.
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|H2].
    + destruct (IHe1 k0 y H1) as [L|R]; [left; left; exact L|right; exact R].
    + destruct (IHe2 k0 y H2) as [L|R]; [left; right; exact L|right; exact R].
  - destruct (IHe k0 y Hy) as [L|R]; [left; exact L|right; exact R].
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|H2].
    + destruct (IHe1 k0 y H1) as [L|R]; [left; left; exact L|right; exact R].
    + destruct (IHe2 k0 y H2) as [L|R]; [left; right; exact L|right; exact R].
Qed.

Lemma binds_fv_in_values : forall (G:env) x b, binds x b G ->
  forall y, y \in fv_binding b -> y \in fv_in_values fv_binding G.
Proof.
  intros G. induction G as [| [z c] G' IH]; intros x b Hb y Hy.
  - rewrite <- (empty_def binding) in Hb. exfalso. exact (@binds_empty_inv binding x b Hb).
  - rewrite cons_eq_push in Hb. apply binds_push_inv in Hb as [[Heq Hb']|[Hneq Hb']].
    + inversion Heq; subst x c. rewrite fv_in_values_cons_binding. rewrite in_union. left. exact Hy.
    + rewrite fv_in_values_cons_binding. rewrite in_union. right.
      apply (IH x b Hb' y Hy).
Qed.

Lemma fv_remove_anno_subset : forall e y, y \in fv_trm [# e #] -> y \in fv_trm e.
Proof.
  intros e. induction e; intros y Hy; simpl in *.
  - exfalso. exact (@in_empty_inv var y Hy).
  - exact Hy.
  - exfalso. exact (@in_empty_inv var y Hy).
  - exfalso. exact (@in_empty_inv var y Hy).
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|H2].
    + left. apply IHe1. exact H1.
    + right. apply IHe2. exact H2.
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|[H2|H3]].
    + left. apply IHe1. exact H1.
    + right. left. apply IHe2. exact H2.
    + right. right. apply IHe3. exact H3.
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|[H2|H3]].
    + left. apply IHe1. exact H1.
    + right. left. apply IHe2. exact H2.
    + right. right. apply IHe3. exact H3.
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|H2].
    + left. apply IHe1. exact H1.
    + right. apply IHe2. exact H2.
  - apply IHe. exact Hy.
  - rewrite in_union. left. apply IHe1. exact Hy.
Qed.

Lemma fv_open_rec_subset_gen : forall v k e y,
  y \in fv_trm e -> y \in fv_trm (open_trm_wrt_trm_rec k v e).
Proof.
  intros v k e. revert k. induction e; intros k0 y Hy; simpl in *.
  - exfalso. exact (@in_empty_inv var y Hy).
  - exact Hy.
  - exfalso. exact (@in_empty_inv var y Hy).
  - exfalso. exact (@in_empty_inv var y Hy).
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|H2].
    + left. apply IHe1. exact H1.
    + right. apply IHe2. exact H2.
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|[H2|H3]].
    + left. apply IHe1. exact H1.
    + right. left. apply IHe2. exact H2.
    + right. right. apply IHe3. exact H3.
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|[H2|H3]].
    + left. apply IHe1. exact H1.
    + right. left. apply IHe2. exact H2.
    + right. right. apply IHe3. exact H3.
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|H2].
    + left. apply IHe1. exact H1.
    + right. apply IHe2. exact H2.
  - apply IHe. exact Hy.
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|H2].
    + left. apply IHe1. exact H1.
    + right. apply IHe2. exact H2.
Qed.

Lemma fv_open_rec_inv_gen : forall v k e y,
  y \in fv_trm (open_trm_wrt_trm_rec k v e) ->
  y \in fv_trm e \/ y \in fv_trm v.
Proof.
  intros v k e. revert k. induction e; intros k0 y Hy; simpl in *.
  - destruct (classicT (k0 = n)) as [Heq|Hneq]; subst.
    + right. simpl in Hy. exact Hy.
    + exfalso. exact (@in_empty_inv var y Hy).
  - left. exact Hy.
  - exfalso. exact (@in_empty_inv var y Hy).
  - exfalso. exact (@in_empty_inv var y Hy).
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|H2].
    + destruct (IHe1 k0 y H1) as [L|R].
      * left. left. exact L.
      * right. exact R.
    + destruct (IHe2 k0 y H2) as [L|R].
      * left. right. exact L.
      * right. exact R.
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|[H2|H3]].
    + destruct (IHe1 k0 y H1) as [L|R].
      * left. left. exact L.
      * right. exact R.
    + destruct (IHe2 k0 y H2) as [L|R].
      * left. right. left. exact L.
      * right. exact R.
    + destruct (IHe3 (S k0) y H3) as [L|R].
      * left. right. right. exact L.
      * right. exact R.
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|[H2|H3]].
    + destruct (IHe1 k0 y H1) as [L|R].
      * left. left. exact L.
      * right. exact R.
    + destruct (IHe2 k0 y H2) as [L|R].
      * left. right. left. exact L.
      * right. exact R.
    + destruct (IHe3 (S k0) y H3) as [L|R].
      * left. right. right. exact L.
      * right. exact R.
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|H2].
    + destruct (IHe1 k0 y H1) as [L|R].
      * left. left. exact L.
      * right. exact R.
    + destruct (IHe2 k0 y H2) as [L|R].
      * left. right. exact L.
      * right. exact R.
  - destruct (IHe k0 y Hy) as [L|R]; [left; exact L|right; exact R].
  - repeat rewrite in_union in Hy. repeat rewrite in_union.
    destruct Hy as [H1|H2].
    + destruct (IHe1 k0 y H1) as [L|R].
      * left. left. exact L.
      * right. exact R.
    + destruct (IHe2 k0 y H2) as [L|R].
      * left. right. exact L.
      * right. exact R.
Qed.


(* from /tmp/SW_stage_fv.v *)
Definition WFenv (G:env) : Prop :=
  forall y, y \in fv_in_values fv_binding G -> y \in dom G.

Definition Pfv_d (d:dir) (G:env) (e A:trm) (H:dtyping d G e A) : Prop :=
  WFenv G /\
  (forall y, y \in fv_trm e -> y \in dom G) /\
  (forall y, y \in fv_trm A -> y \in dom G).

Definition Pfv_w (G:env) (H:dwf G) : Prop := WFenv G.

Lemma WFenv_push : forall G x e A,
  WFenv G -> x # G ->
  (forall y, y \in fv_trm e -> y \in dom G) ->
  (forall y, y \in fv_trm [# A #] -> y \in dom G) ->
  WFenv (G & x ~ bind_sub [# e #] [# A #]).
Proof.
  intros G x e A HW Hx He HA. unfold WFenv in *.
  intros y Hy. rewrite <- cons_eq_push in Hy. rewrite fv_in_values_cons_binding in Hy.
  rewrite in_union in Hy. destruct Hy as [Hyb|HyG].
  - simpl in Hyb. rewrite in_union in Hyb. destruct Hyb as [Hye|HyA].
    + rewrite dom_push. rewrite in_union. right. apply He. apply fv_remove_anno_subset. exact Hye.
    + rewrite dom_push. rewrite in_union. right. exact (HA y HyA).
  - rewrite dom_push. rewrite in_union. right. exact (HW y HyG).
Qed.

Lemma fv_open_dom_inv : forall L G d e y,
  (forall z, z \notin L ->
     y \in fv_trm (open_trm_wrt_trm e (trm_var_f z)) ->
     y \in dom (G & z ~ d)) ->
  y \in fv_trm e -> y \in dom G.
Proof.
  intros L G d e y Hbody Hy.
  set (Lf := union L (union (dom G) (union (fv_trm e) (singleton y)))).
  pick_fresh_gen Lf z.
  unfold Lf in Fr.
  apply notin_union_r in Fr as [HzL Fr].
  apply notin_union_r in Fr as [HzG Fr].
  apply notin_union_r in Fr as [Hze Hyz].
  assert (Hyop : y \in fv_trm (open_trm_wrt_trm e (trm_var_f z)))
    by (exact (@fv_open_rec_subset_gen (trm_var_f z) 0 e y Hy)).
  pose proof (Hbody z HzL Hyop) as Hdom.
  rewrite dom_push in Hdom. rewrite in_union in Hdom.
  destruct Hdom as [Hyz'|HyG].
  - rewrite in_singleton in Hyz'. subst y.
    exfalso. apply Hyz. apply in_singleton_self.
  - exact HyG.
Qed.

Lemma dtyping_fv_and_wf : forall d G e A (H:dtyping d G e A),
  Pfv_d d G e A H.
Proof.
  intros d G e A H.
  apply (dtyping_mut Pfv_d Pfv_w).
  - (* star *) intros G0 Hd IH. unfold Pfv_d. split; [exact IH|split].
    + intros y Hy. exfalso. exact (@in_empty_inv var y Hy).
    + intros y Hy. exfalso. exact (@in_empty_inv var y Hy).
  - (* var *) intros e0 G0 xx A0 Hd IH b. unfold Pfv_d. split; [exact IH|split].
    + intros y Hy. simpl in Hy. rewrite in_singleton in Hy. subst y.
      exact (@get_some_inv binding xx (bind_sub e0 A0) G0 (binds_get b)).
    + intros y Hy. unfold WFenv in IH.
      assert (Hyb : y \in fv_binding (bind_sub e0 A0)) by (simpl; rewrite in_union; right; exact Hy).
      exact (IH y (@binds_fv_in_values G0 xx (bind_sub e0 A0) b y Hyb)).
  - (* top *) intros G0 A0 d1 IH1. destruct IH1 as [HG [He HA]].
    unfold Pfv_d. split; [exact HG|split].
    + intros y Hy. exfalso. exact (@in_empty_inv var y Hy).
    + exact He.
  - (* lam *) intros L G0 e1 e2 A0 B d1 IH1 d2 IH2 d3 IH3.
    destruct IH1 as [HG [He1 HAer]].
    destruct IH2 as [_ [HA0 Hstar]].
    unfold Pfv_d. split; [exact HG|split].
    + intros y Hy. simpl in Hy. repeat rewrite in_union in Hy.
      destruct Hy as [Hy1|[Hy2|Hy3]].
      * exact (He1 y Hy1).
      * exact (HA0 y Hy2).
      * apply (@fv_open_dom_inv L G0 (bind_sub [#e1#] [#A0#]) e2 y).
        -- intros z Hz Hyz. destruct (IH3 z Hz) as [_ [Hbody _]]. exact (Hbody y Hyz).
        -- exact Hy3.
    + intros y Hy. simpl in Hy. repeat rewrite in_union in Hy.
      destruct Hy as [Hy1|[Hy2|Hy3]].
      * apply He1. apply fv_remove_anno_subset. exact Hy1.
      * exact (HAer y Hy2).
      * apply (@fv_open_dom_inv L G0 (bind_sub [#e1#] [#A0#]) B y).
        -- intros z Hz Hyz. destruct (IH3 z Hz) as [_ [_ Hbody]]. exact (Hbody y Hyz).
        -- exact Hy3.
  - (* app *) intros e3 G0 e0 A0 B C d1 IH1 ds d2 IH2.
    destruct IH1 as [HG [HA HB]].
    destruct IH2 as [_ [He Hprod]].
    unfold Pfv_d. split; [exact HG|split].
    + intros y Hy. simpl in Hy. repeat rewrite in_union in Hy.
      destruct Hy as [Hye|HyA].
      * exact (He y Hye).
      * exact (HA y HyA).
    + intros y Hy.
      destruct (@fv_open_rec_inv_gen [#A0#] 0 C y Hy) as [HyC|HyA].
      * apply Hprod. simpl. repeat rewrite in_union. right. right. exact HyC.
      * apply HA. apply fv_remove_anno_subset. exact HyA.
  - (* pi *) intros L G0 e0 A0 B d1 IH1 d2 IH2 d3 IH3.
    destruct IH1 as [HG [He HAer]].
    destruct IH2 as [_ [HA0 Hstar]].
    unfold Pfv_d. split; [exact HG|split].
    + intros y Hy. simpl in Hy. repeat rewrite in_union in Hy.
      destruct Hy as [Hy1|[Hy2|Hy3]].
      * exact (He y Hy1).
      * exact (HA0 y Hy2).
      * apply (@fv_open_dom_inv L G0 (bind_sub [#e0#] [#A0#]) B y).
        -- intros z Hz Hyz. destruct (IH3 z Hz) as [_ [Hbody _]]. exact (Hbody y Hyz).
        -- exact Hy3.
    + intros y Hy. exfalso. exact (@in_empty_inv var y Hy).
  - (* castup *) intros G0 e0 A0 B d1 IH1 d2 IH2 r.
    destruct IH1 as [HG [HB Hstar]].
    destruct IH2 as [_ [He HA]].
    unfold Pfv_d. split; [exact HG|split].
    + intros y Hy. simpl in Hy. repeat rewrite in_union in Hy.
      destruct Hy as [HyB|Hye].
      * exact (HB y HyB).
      * exact (He y Hye).
    + intros y Hy. apply HB. apply fv_remove_anno_subset. exact Hy.
  - (* castdn *) intros G0 e0 A0 B d1 IH1 d2 IH2 r.
    destruct IH1 as [HG [HB Hstar]].
    destruct IH2 as [_ [He HA]].
    unfold Pfv_d. split; [exact HG|split].
    + intros y Hy. exact (He y Hy).
    + exact HB.
  - (* anno *) intros G0 e0 A0 d1 IH1 d2 IH2.
    destruct IH1 as [HG [He HA]].
    destruct IH2 as [_ [HA0 Hstar]].
    unfold Pfv_d. split; [exact HG|split].
    + intros y Hy. simpl in Hy. repeat rewrite in_union in Hy.
      destruct Hy as [Hye|HyA].
      * exact (He y Hye).
      * exact (HA y HyA).
    + intros y Hy. apply HA. apply fv_remove_anno_subset. exact Hy.
  - (* sub *) intros A0 G0 e0 B d1 IH1 ds d2 IH2.
    destruct IH1 as [HG [He HA]].
    destruct IH2 as [_ [HB Hstar]].
    unfold Pfv_d. split; [exact HG|split].
    + exact He.
    + exact HB.
  - (* chk *) intros G0 e0 A0 d1 IH1.
    destruct IH1 as [HG [He HA]].
    unfold Pfv_d. split; [exact HG|split]; assumption.
  - (* dwf_nil *) unfold Pfv_w, WFenv. intros y Hy.
    unfold fv_in_values in Hy. rewrite values_def in Hy.
    rewrite (empty_def binding) in Hy. simpl in Hy.
    exfalso. exact (@in_empty_inv var y Hy).
  - (* dwf_cons *) intros G0 x ee AA Hx d1 IH1 d2 IH2.
    destruct IH1 as [HG [He HAer]].
    unfold Pfv_w. apply (@WFenv_push G0 x ee AA HG Hx He HAer).
Qed.

Lemma dwf_WFenv : forall G, dwf G -> WFenv G.
Proof.
  intros G Hwf. induction Hwf as [| G0 x e A Hx d1 d2].
  - unfold WFenv. intros y Hy.
    unfold fv_in_values in Hy. rewrite values_def in Hy.
    rewrite (empty_def binding) in Hy. simpl in Hy.
    exfalso. exact (@in_empty_inv var y Hy).
  - destruct (dtyping_fv_and_wf chk G0 e [#A#] d1) as [HG [He HA]].
    eapply (@WFenv_push G0 x e A HG Hx He HA).
Qed.

Lemma fresh_values : forall G x,
  WFenv G -> x # G -> x \notin fv_in_values fv_binding G.
Proof.
  intros G x HWF Hx Hy. apply HWF in Hy. exact (Hx Hy).
Qed.


(* from /tmp/SW_stage_subst_helpers.v *)
Lemma GTerm_var : forall x, GTerm (trm_var_f x).
Proof. intros. split; [apply Et_var|constructor]. Qed.
Lemma GTerm_star : GTerm trm_star.
Proof. split; [apply Et_star|constructor]. Qed.
Lemma GTerm_top : GTerm trm_top.
Proof. split; [apply Et_top|constructor]. Qed.
Lemma GTerm_open : forall e x, GTerm e -> GTerm (e ^ x).
Proof.
  intros e x [HE HL]. split.
  - apply Et_open; [exact HE|apply Et_var].
  - apply lc_rec_0_lc_trm. unfold open_trm_wrt_trm.
    apply lc_rec_open.
    + simpl. constructor.
    + apply lc_rec_mono with (n:=0); [lia|apply lc_trm_lc_rec; exact HL].
Qed.

Lemma GBinding_bind : forall e A, GBinding (bind_sub e A) -> GBinding (bind_sub [#e#] [#A#]).
Proof.
  intros e A [He HA]. unfold GBinding. split.
  - apply GTerm_rem; exact He.
  - apply GTerm_rem; exact HA.
Qed.

Lemma GBinding_env_push : forall H y e A,
  (forall z c, binds z c H -> GBinding c) ->
  GBinding (bind_sub [#e#] [#A#]) ->
  (forall z c, binds z c (H & y ~ bind_sub [#e#] [#A#]) -> GBinding c).
Proof.
  intros H y e A HB Hc z c Hb.
  apply binds_push_inv in Hb as [[Heq Hb]|[Hneq Hb]].
  - destruct Heq as [Hzy HcEq]. subst. exact Hc.
  - exact (HB z c Hb).
Qed.

Lemma ok_subst_env : forall u x H, ok H -> ok (subst_env u x H).
Proof.
  intros u x H. induction H as [| [y b] H' IH]; intros Hok; simpl.
  - rewrite <- (empty_def binding). apply (ok_empty binding).
  - rewrite cons_eq_push in Hok.
    apply ok_push_inv in Hok as [Hok' Hy].
    rewrite cons_eq_push. apply ok_push.
    + apply IH; exact Hok'.
    + rewrite dom_subst_env. exact Hy.
Qed.


Set Implicit Arguments.
(* ===== conditional Q_typing/bidir master induction ===== *)
Unset Implicit Arguments.

Definition SUBOPEN : Prop :=
  forall G e A B L,
    (forall x, x \notin L ->
       sub (G & x ~ bind_sub e A) (B ^ x) (B ^ x) trm_star) ->
    forall u, sub G u e A ->
      sub G (B ^^ u) (B ^^ u) trm_star.

(* The direction-free dsub soundness statement, kept as an explicit
   hypothesis in this stage so that Q_typing can be established
   independently.  It is the object of the later master induction. *)
Definition DSUB_AT : Prop :=
  forall G e1 e2 T,
    dsubU G e1 e2 ->
    sub {# G #} [# e1 #] [# e1 #] T ->
    sub {# G #} [# e2 #] [# e2 #] T ->
    sub {# G #} [# e1 #] [# e2 #] T.

(* ============================================================ *)
(* Erasing a typing derivation.                                  *)
(* ============================================================ *)

(* ============================================================ *)
(* wf of the erased typing environment.                          *)
(* ============================================================ *)

(* Q_wf is proved mutually; no external dwf-to-wf conversion is used. *)

(* A well-formed environment types the value stored at any binding, in
   the *same* environment, at the stored type.  The wf rule types the
   un-erased source value, so the erasure lemma is used first. *)
(* ============================================================ *)
(* Q_typing: every typed term is self-subtyping at its erased
   type, and its erased type is self-star.                       *)
(* ============================================================ *)

Definition Q_typing_P (d:dir) (G:env) (e A:trm) (H:dtypingU d G e A) : Prop :=
  sub {# G #} [# e #] [# e #] [# A #] /\
  sub {# G #} [# A #] [# A #] trm_star.

Definition Q_typing_wf_P (G:env) (H:dwfU G) : Prop := wf {# G #}.
Definition Q_typing_dsub_P (G:env) (e1 e2:trm) (H:dsubU G e1 e2) : Prop := True.

Lemma dtypingU_self_and_star : SUBOPEN -> DSUB_AT ->
  forall d G e A (H:dtypingU d G e A), Q_typing_P d G e A H.
Proof.
  intros HSUB HDSUB d G e A H.
  apply (@dtypingU_mut Q_typing_P Q_typing_wf_P Q_typing_dsub_P).
  - (* du_star *)
    intros G0 Hd IH. unfold Q_typing_P. simpl.
    split; apply sub_ax; exact IH.
  - (* du_var *)
    intros e0 G0 x A0 Hd IH Hb. unfold Q_typing_P. simpl.
    assert (Hb' : binds x (bind_sub [# e0 #] [# A0 #]) {# G0 #})
      by (apply binds_rem_bind; exact Hb).
    split.
    + eapply sub_var_refl; eassumption.
    + eapply wf_binds_type_star; eassumption.
  - (* du_top *)
    intros G0 A0 d1 IH1. unfold Q_typing_P in *. simpl in *.
    destruct IH1 as [Hself Hstar]. simpl in *.
    split.
    + eapply sub_top_refl. exact Hself.
    + exact Hself.
  - (* du_lam *)
    intros L G0 e1 e2 A0 B d1 IH1 d2 IH2 d3 IH3.
    unfold Q_typing_P in *. simpl in *.
    destruct IH1 as [Hself1 Hstar1].
    destruct IH2 as [Hself2 Hstar2].
    assert (HidemA : [# [# A0 #] #] = [# A0 #]) by apply remove_anno_idem.
    assert (HidemE1 : [# [# e1 #] #] = [# e1 #]) by apply remove_anno_idem.
    assert (HidemB : [# [# B #] #] = [# B #]) by apply remove_anno_idem.
    rewrite HidemA in Hself1, Hstar1.
    rewrite HidemA, HidemE1.
    split.
    + eapply sub_abs with (L := L) (B := [# B #]).
      * exact Hself1.
      * exact Hself2.
      * intros x Hx.
        specialize (IH3 x Hx). destruct IH3 as [Hbself _].
        rewrite rem_env_push in Hbself.
        rewrite rem_bind_erased in Hbself.
        rewrite (remove_anno_open_var e2 x) in Hbself.
        rewrite (remove_anno_open_var B x) in Hbself.
        exact Hbself.
      * intros x Hx.
        specialize (IH3 x Hx). destruct IH3 as [_ Hbstar].
        rewrite rem_env_push in Hbstar.
        rewrite rem_bind_erased in Hbstar.
        rewrite (remove_anno_open_var B x) in Hbstar.
        exact Hbstar.
    + eapply sub_prod with (L := L) (A' := [# A0 #]) (B := [# B #]) (B' := [# B #]).
      * exact Hstar1.
      * exact Hself1.
      * exact Hself2.
      * intros x Hx.
        specialize (IH3 x Hx). destruct IH3 as [_ Hbstar].
        rewrite rem_env_push in Hbstar. rewrite rem_bind_erased in Hbstar.
        rewrite (remove_anno_open_var B x) in Hbstar. exact Hbstar.
      * intros x Hx.
        specialize (IH3 x Hx). destruct IH3 as [_ Hbstar].
        rewrite rem_env_push in Hbstar. rewrite rem_bind_erased in Hbstar.
        rewrite (remove_anno_open_var B x) in Hbstar. exact Hbstar.
  - (* du_app *)
    intros e3 G0 e0 A0 B C d1 IH1 dsub0 IHsub d2 IH2.
    unfold Q_typing_P in *. simpl in *.
    destruct IH1 as [Hargself Hargstar].
    destruct IH2 as [Hfun Hfunstar].
    assert (HidemA : [# [# A0 #] #] = [# A0 #]) by apply remove_anno_idem.
    rewrite <- HidemA in Hargself.
    destruct (sub_prod_star_inv {# G0 #} [# e3 #] [# B #] [# C #] Hfunstar)
      as [Hdom [Hdomstar [Lfam Hfam]]].
    assert (Harg : sub {# G0 #} [# A0 #] [# e3 #] [# B #]).
    { assert (Hres : sub {# G0 #} [#[# A0 #]#] [# e3 #] [# B #]).
      { eapply (HDSUB G0 [# A0 #] e3 [# B #]).
        - exact dsub0.
        - exact Hargself.
        - exact Hdom. }
      rewrite HidemA in Hres. exact Hres. }
    split.
    + rewrite remove_anno_open. rewrite HidemA.
      eapply sub_app with (e3 := [# e3 #]) (B := [# B #]) (C := [# C #]).
      * exact Hfun.
      * exact Harg.
    + rewrite remove_anno_open. rewrite HidemA.
      eapply (HSUB {# G0 #} [# e3 #] [# B #] [# C #] Lfam).
      * intros x Hx. exact (Hfam x Hx).
      * exact Harg.
  - (* du_pi *)
    intros L G0 e0 A0 B d1 IH1 d2 IH2 d3 IH3.
    unfold Q_typing_P in *. simpl in *.
    destruct IH1 as [Hself1 Hstar1].
    destruct IH2 as [Hself2 Hstar2].
    assert (HidemA : [# [# A0 #] #] = [# A0 #]) by apply remove_anno_idem.
    rewrite HidemA in Hself1, Hstar1.
    split.
    + (* the product itself is star-valid *)
      eapply sub_prod with (L := L) (A' := [# A0 #]) (B := [# B #]) (B' := [# B #]).
      * exact Hstar1.
      * exact Hself1.
      * exact Hself2.
      * intros x Hx.
        specialize (IH3 x Hx). destruct IH3 as [Hbstar _].
        rewrite rem_env_push in Hbstar. rewrite rem_bind_erased in Hbstar.
        rewrite (remove_anno_open_var B x) in Hbstar. exact Hbstar.
      * intros x Hx.
        specialize (IH3 x Hx). destruct IH3 as [Hbstar _].
        rewrite rem_env_push in Hbstar. rewrite rem_bind_erased in Hbstar.
        rewrite (remove_anno_open_var B x) in Hbstar. exact Hbstar.
    + apply sub_ax. exact (sub_wf Hself1).
  - (* du_castup *)
    intros G0 e0 A0 B d1 IH1 d2 IH2 r. unfold Q_typing_P in *. simpl in *.
    destruct IH1 as [HselfB HstarB].
    destruct IH2 as [HselfE HstarA].
    split.
    + rewrite remove_anno_idem.
      eapply sub_castup with (B := [# B #]) (A := [# A0 #]).
      * exact HselfB.
      * exact HselfE.
      * exact r.
    + rewrite remove_anno_idem. exact HselfB.
  - (* du_castdn *)
    intros G0 e0 A0 B d1 IH1 d2 IH2 r. unfold Q_typing_P in *. simpl in *.
    destruct IH1 as [HselfB HstarB].
    destruct IH2 as [HselfE HstarA].
    split.
    + eapply sub_castdn with (B := [# B #]) (A := [# A0 #]).
      * exact HselfB.
      * exact HselfE.
      * exact r.
    + exact HselfB.
  - (* du_anno *)
    intros G0 e0 A0 d1 IH1 d2 IH2. unfold Q_typing_P in *. simpl in *.
    destruct IH1 as [HselfE HstarE].
    destruct IH2 as [HselfA HstarA].
    split.
    + rewrite remove_anno_idem. exact HselfE.
    + rewrite remove_anno_idem. exact HselfA.
  - (* du_sub *)
    intros A0 G0 e0 B d1 IH1 dsub0 IHsub d2 IH2.
    unfold Q_typing_P in *. simpl in *.
    destruct IH1 as [Hself HstarA].
    destruct IH2 as [HselfB HstarB]. simpl in *.
    split.
    + eapply sub_sub.
      * exact Hself.
      * assert (Hres : sub {# G0 #} [# A0 #] [#[# B #]#] trm_star).
        { eapply (HDSUB G0 A0 [# B #] trm_star).
          - exact dsub0.
          - exact HstarA.
          - rewrite (remove_anno_idem B). exact HselfB. }
        rewrite (remove_anno_idem B) in Hres. exact Hres.
    + exact HselfB.
  - (* du_chk *)
    intros G0 e0 A0 d1 IH1. unfold Q_typing_P in *. simpl in *.
    exact IH1.
  - (* dwfU nil *) unfold Q_typing_wf_P. simpl.
    rewrite map_def. rewrite (empty_def binding). rewrite LibList.map_nil.
    rewrite <- (empty_def binding). apply wf_nil.
  - (* dwfU cons *) intros G0 k e0 A0 Hk d1 IH1 d2 IH2.
    destruct IH1 as [Hself1 _]. destruct IH2 as [Hself2 _].
    rewrite remove_anno_idem in Hself1.
    unfold Q_typing_wf_P. simpl. rewrite rem_env_push. rewrite rem_bind_erased.
    eapply wf_cons.
    + exact Hself1.
    + exact Hself2.
    + rewrite dom_rem. exact Hk.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
Qed.

(* ============================================================ *)
(* Final assembler for the requested intermediate target.  The  *)
(* star-witness premise is kept in the statement for compatibility
   with [bidir_to_sub_from_SW], but the master induction proves
   self-subtyping for every typing, so it is not used.          *)
(* ============================================================ *)

Lemma bidir_to_sub_from_SW :
  SUBOPEN -> DSUB_AT ->
  (forall G e A, dtyping inf G e A ->
     exists X, dtyping inf G X trm_star /\ [# X #] = A) ->
  forall G d e1 e2 A,
    dtyping d G e1 A -> dtyping d G e2 A -> dsub G e1 e2 ->
    sub {# G #} [# e1 #] [# e2 #] [# A #].
Proof.
  intros HSUB HDSUB HSW G d e1 e2 A H1 H2 Hsub.
  assert (H1U : dtypingU d G e1 A) by (apply dtyping_dtypingU; exact H1).
  assert (H2U : dtypingU d G e2 A) by (apply dtyping_dtypingU; exact H2).
  assert (HsubU : dsubU G e1 e2) by (apply dsub_dsubU; exact Hsub).
  destruct (dtypingU_self_and_star HSUB HDSUB d G e1 A H1U) as [Hself1 _].
  destruct (dtypingU_self_and_star HSUB HDSUB d G e2 A H2U) as [Hself2 _].
  exact (HDSUB G e1 e2 [# A #] HsubU Hself1 Hself2).
Qed.

(* ============================================================ *)
(* Exposed Q_wf component and stored-binding self-subtyping.    *)
(* ============================================================ *)

Lemma dwfU_wf_erased : SUBOPEN -> DSUB_AT ->
  forall G, dwfU G -> wf {# G #}.
Proof.
  intros HSUB HDSUB G H. induction H as [| G0 x e A Hx d1 d2].
  - simpl. rewrite map_def. rewrite (empty_def binding).
    rewrite LibList.map_nil. rewrite <- (empty_def binding). apply wf_nil.
  - destruct (dtypingU_self_and_star HSUB HDSUB chk G0 e [# A #] d1)
      as [Hself1 _].
    destruct (dtypingU_self_and_star HSUB HDSUB chk G0 A trm_star d2)
      as [Hself2 _].
    rewrite remove_anno_idem in Hself1.
    simpl. rewrite rem_env_push. rewrite rem_bind_erased.
    eapply wf_cons.
    + exact Hself1.
    + exact Hself2.
    + rewrite dom_rem. exact Hx.
Qed.

Lemma dwfU_binds_self : SUBOPEN -> DSUB_AT ->
  forall G x e A,
    dwfU G -> binds x (bind_sub e A) {# G #} -> sub {# G #} e e A.
Proof.
  intros HSUB HDSUB G x e A HwfU Hb.
  eapply wf_binds_self.
  - apply dwfU_wf_erased; assumption.
  - exact Hb.
Qed.

(* ============================================================ *)
(* STATUS (2026-11-22).                                          *)
(*                                                              *)
(* Proved with Qed:                                             *)
(*   dtypingU_self_and_star  (Q_typing + Q_wf master induction)  *)
(*   dwfU_wf_erased          (Q_wf component, exposed)           *)
(*   dwfU_binds_self         (binding self-subtyping in {#G#})   *)
(*   bidir_to_sub_from_SW    (conditional assembler)             *)
(*                                                              *)
(* The assembler is parametric in the two explicit propositions  *)
(* [SUBOPEN] and [DSUB_AT] above.  The Q_typing proof uses       *)
(* [DSUB_AT] in the [du_app] and [du_sub] branches and [SUBOPEN] *)
(* in the result-star branch of [du_app].                        *)
(*                                                              *)
(* Remaining exact cycles (no forbidden escapes are used):       *)
(* 1. [DSUB_AT]'s [dus_var_trans] branch needs, with              *)
(*       Hb : binds x (bind_sub e1 A) G,                         *)
(*       Hself1 : sub {#G#} (var x) (var x) T,                   *)
(*    either [sub {#G#} [#e2#] [#e2#] [#A#]] (to use            *)
(*    [sub_var_trans] at the stored type A) or                  *)
(*    [sub {#G#} [#A#] T trm_star] (to use [sub_sub]).  The      *)
(*    only source of the latter from [Hself1] is a chain of      *)
(*    [sub_sub] coercions, whose composition is transitivity of  *)
(*    [sub] at star; [sub_sub] cannot compose two star-typed     *)
(*    coercions without an additional [sub A A B] premise.       *)
(*    See /tmp/QdsubCycle.v, lemma [q_dsub_var_trans_blocked].    *)
(* 2. [SUBOPEN] and Q_typing are mutually recursive: STARSUBST    *)
(*    returns a typing of [B^^u] at star, and converting that    *)
(*    typing back to [sub] needs Q_typing; Q_typing's app case    *)
(*    is exactly [SUBOPEN].  See /tmp/SubOpenProbe.v.             *)
(* ============================================================ *)

(* ===== sub-star transitivity and SUBSUBST reductions ===== *)

(* from /tmp/SubStarTrans.v *)
Lemma sub_top_rhs : forall G C T, sub G trm_top C T -> C = trm_top.
Proof.
  intros G C T H.
  dependent induction H.
  all: try reflexivity.
  all: try assumption.
  all: try (match goal with IH : _ = trm_top -> _ = _ |- _ => apply IH; reflexivity end).
  all: try discriminate.
Qed.


Definition SUBSTARTRANS : Prop :=
  forall G A B C, sub G A B trm_star -> sub G B C trm_star -> sub G A C trm_star.

(* The binding-type/common-type coercion needed in the [dus_var_trans]
   branch, reduced to the explicit star-transitivity hypothesis.  This
   part is complete and kernel-checked; the remaining obstruction is
   [SUBSTARTRANS] itself, in particular its [sub_app] case. *)
Lemma sub_var_self_type_coerce : SUBSTARTRANS ->
  forall G x e A T,
    wf G -> binds x (bind_sub e A) G ->
    sub G (trm_var_f x) (trm_var_f x) T ->
    sub G A T trm_star.
Proof.
  intros Htrans G x e A T Hwf Hb Hself.
  dependent induction Hself.
  - (* sub_var_refl *)
    assert (Heq : bind_sub e0 A0 = bind_sub e A)
      by (eapply binds_functional; [exact H0|exact Hb]).
    injection Heq as He HA. subst e0 A0.
    eapply wf_binds_type_star; [exact Hwf|exact Hb].
  - (* sub_var_trans *)
    assert (Heq : bind_sub e1 A0 = bind_sub e A)
      by (eapply binds_functional; [exact H|exact Hb]).
    injection Heq as He HA. subst e1 A0.
    eapply wf_binds_type_star; [exact Hwf|exact Hb].
  - (* sub_sub: compose the two star coercions *)
    eapply Htrans.
    + apply (IHHself1 x Hwf Hb eq_refl eq_refl).
    + exact Hself2.
Qed.

(* ============================================================ *)
(* STATUS: [sub_star_trans] is not proved here.                  *)
(*                                                              *)
(* A [dependent induction] on the first derivation at type        *)
(* [trm_star] leaves ten goals.  The [sub_app] case reduces to    *)
(* the following composition:                                    *)
(*                                                              *)
(*   H1_  : sub G e1 e2 (trm_prod e3 B C)                        *)
(*   H1_0 : sub G A e3 B                                         *)
(*   x    : C ^^ A = trm_star                                    *)
(*   H2   : sub G (trm_app e2 A) C0 trm_star                     *)
(*   goal : sub G (trm_app e1 A) C0 trm_star                     *)
(*                                                              *)
(* Inverting [H2]'s [sub_app] constructor gives                   *)
(*                                                              *)
(*   H2_  : sub G e2 e2' (trm_prod e3' B' C')                    *)
(*   H2_0 : sub G A e3' B'                                       *)
(*   y    : C' ^^ A = trm_star                                   *)
(*                                                              *)
(* The single induction hypothesis from [H1_] is transitivity at *)
(* the fixed product type [trm_prod e3 B C].  Composing with      *)
(* [H2_] therefore needs the equality                          *)
(*                                                              *)
(*   trm_prod e3 B C = trm_prod e3' B' C',                       *)
(*                                                              *)
(* which is not implied by [x] and [y]: those only constrain the *)
(* opened codomains.  Even if [C = C'] were recovered (e.g. from   *)
(* local closure), the first components [e3] and [e3'] and the    *)
(* domains [B] and [B'] are still unrelated.  A [sub_prod]        *)
(* coercion cannot bridge the gap because [sub_prod] keeps the    *)
(* first component syntactically equal.  Hence this branch        *)
(* genuinely requires transitivity at arbitrary compatible product *)
(* types, not only at [trm_star].  The [sub_prod] and cast branches *)
(* exhibit the same obstruction.  The [sub_sub] branches are      *)
(* handled by composing with the coercion, and the remaining      *)
(* cases are either immediate or use [sub_top_rhs].               *)
(* ============================================================ *)

(* The complete [dus_var_trans] conclusion, assuming the recursive
   soundness result at the binding type [A] and star-transitivity. *)
Lemma dsub_var_trans_case : SUBSTARTRANS ->
  forall G x e A e2 T,
    wf G -> binds x (bind_sub e A) G ->
    sub G (trm_var_f x) (trm_var_f x) T ->
    sub G e e2 A ->
    sub G (trm_var_f x) e2 T.
Proof.
  intros Htrans G x e A e2 T Hwf Hb Hself Hrec.
  eapply sub_sub.
  - eapply sub_var_trans; [exact Hb | exact Hrec].
  - eapply sub_var_self_type_coerce; [exact Htrans|exact Hwf|exact Hb|exact Hself].
Qed.


(* from /tmp/SubSubst.v *)
Definition SUBSUBST : Prop :=
  forall G x e A u,
    x # G ->
    x \notin fv_in_values fv_binding G ->
    x \notin fv_trm e ->
    x \notin fv_trm A ->
    lc_trm u ->
    sub G u e A ->
    forall a b T,
      sub (G & x ~ bind_sub e A) a b T ->
      sub G (subst_trm u x a) (subst_trm u x b) (subst_trm u x T).

(* ============================================================ *)
(* [SUBSUBST] implies the opening lemma used by the master       *)
(* induction.  This reduction is complete and Qed.               *)
(* ============================================================ *)

Lemma sub_open_from_subst : SUBSUBST -> SUBOPEN.
Proof.
  intros HS G e A B L Hfam u Hu.
  set (Lf := L \u dom G \u fv_in_values fv_binding G
                \u fv_trm e \u fv_trm A \u fv_trm B).
  pick_fresh_gen Lf x.
  unfold Lf in Fr.
  apply notin_union_r in Fr as [HxL HxRest].
  apply notin_union_r in HxRest as [HxG HxRest].
  apply notin_union_r in HxRest as [Hxvals HxRest].
  apply notin_union_r in HxRest as [Hxe HxRest].
  apply notin_union_r in HxRest as [HxA HxB].
  assert (Hself : sub (G & x ~ bind_sub e A) (B ^ x) (B ^ x) trm_star)
    by (apply Hfam; exact HxL).
  assert (HwfSrc : wf (G & x ~ bind_sub e A))
    by (eapply sub_wf; exact Hself).
  destruct (@wf_cons_inv G x e A HwfSrc) as [Hse [_ _]].
  assert (HwfG : wf G) by (eapply sub_wf; exact Hse).
  assert (HlcG : lc_env G) by (apply wf_lc_env; exact HwfG).
  destruct (@sub_lc G u e A Hu HlcG) as [Hlu _].
  assert (Hres := HS G x e A u HxG Hxvals Hxe HxA Hlu Hu
                    (B ^ x) (B ^ x) trm_star Hself).
  simpl in Hres.
  rewrite (subst_open_fresh u B HxB) in Hres.
  exact Hres.
Qed.


(* from /tmp/MasterSubst.v *)
Lemma dtypingU_self_and_star_from_subst : SUBSUBST -> DSUB_AT ->
  forall d G e A (H:dtypingU d G e A), Q_typing_P d G e A H.
Proof.
  intros HS HD.
  apply (dtypingU_self_and_star (sub_open_from_subst HS) HD).
Qed.

Lemma bidir_to_sub_from_SUBSUBST :
  SUBSUBST -> DSUB_AT ->
  (forall G e A, dtyping inf G e A ->
     exists X, dtyping inf G X trm_star /\ [# X #] = A) ->
  forall G d e1 e2 A,
    dtyping d G e1 A -> dtyping d G e2 A -> dsub G e1 e2 ->
    sub {# G #} [# e1 #] [# e2 #] [# A #].
Proof.
  intros HS HD HSW.
  apply (bidir_to_sub_from_SW (sub_open_from_subst HS) HD HSW).
Qed.


Set Implicit Arguments.

Theorem sub_to_bidir : forall G e1 e2 A,
  sub G e1 e2 A ->
  dsub G e1 e2 /\
  exists e1' e2',
    dtyping inf G e1' A /\ dtyping inf G e2' A /\
    [#e1'#] = e1 /\ [#e2'#] = e2.

Theorem bidir_to_sub : forall G d e1 e2 A,
  dtyping d G e1 A ->
  dtyping d G e2 A ->
  dsub G e1 e2 ->
  sub {#G#} [#e1#] [#e2#] [#A#].
