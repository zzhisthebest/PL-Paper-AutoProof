From cgraphs.locks.lambdalock Require Import definitions.
From Stdlib Require Import Lia Lists.List Sorting.Permutation Logic.Eqdep_dec.
From stdpp Require Import list fin_sets fin_map_dom.

Local Open Scope list_scope.

(* Runtime typing counts literal references. Each branch of a match
   accounts for the same ports, since execution selects just one branch. *)
Definition ports := list (nat * type).

Inductive runtime_typed : env -> ports -> expr -> type -> Prop :=
| RT_var G x t :
    env_var G x t -> runtime_typed G [] (Var x) t
| RT_fun G G' x e a b l R :
    env_bind G' x a G -> (l = Unr -> env_unr G ∧ R = []) ->
    runtime_typed G' R e b -> runtime_typed G R (Fun x e) (FunT l a b)
| RT_app G G1 G2 e1 e2 a b l R R1 R2 :
    env_split G G1 G2 -> R ≡ₚ R1 ++ R2 ->
    runtime_typed G1 R1 e1 (FunT l a b) -> runtime_typed G2 R2 e2 a ->
    runtime_typed G R (App e1 e2) b
| RT_unit G :
    env_unr G -> runtime_typed G [] Unit UnitT
| RT_pair G G1 G2 e1 e2 a b R R1 R2 :
    env_split G G1 G2 -> R ≡ₚ R1 ++ R2 ->
    runtime_typed G1 R1 e1 a -> runtime_typed G2 R2 e2 b ->
    runtime_typed G R (Pair e1 e2) (PairT a b)
| RT_let G G1 G2 e1 e2 a b t R R1 R2 :
    env_split G G1 G2 -> R ≡ₚ R1 ++ R2 ->
    runtime_typed G1 R1 e1 (PairT a b) ->
    runtime_typed G2 R2 e2 (FunT Lin a (FunT Lin b t)) ->
    runtime_typed G R (LetPair e1 e2) t
| RT_sum G n (ts : fin n -> type) i e R :
    runtime_typed G R e (ts i) -> runtime_typed G R (Sum i e) (SumT n ts)
| RT_match n G G1 G2 t (ts : fin n -> type) es e R R1 R2 :
    env_split G G1 G2 -> R ≡ₚ R1 ++ R2 ->
    (n = 0 -> env_unr G2 ∧ R2 = []) ->
    runtime_typed G1 R1 e (SumT n ts) ->
    (∀ i, runtime_typed G2 R2 (es i) (FunT Lin (ts i) t)) ->
    runtime_typed G R (MatchSum n e es) t
| RT_fork G e a b R :
    runtime_typed G R e (FunT Lin (FunT Lin b a) UnitT) ->
    runtime_typed G R (ForkBarrier e) (FunT Lin a b)
| RT_new G e t R :
    runtime_typed G R e t ->
    runtime_typed G R (NewLock e) (LockT (Owner, Closed) t)
| RT_forklock G G1 G2 e1 e2 t c1 c2 c3 R R1 R2 :
    env_split G G1 G2 -> R ≡ₚ R1 ++ R2 -> lockcap_split c1 c2 c3 ->
    runtime_typed G1 R1 e1 (LockT c1 t) ->
    runtime_typed G2 R2 e2 (FunT Lin (LockT c2 t) UnitT) ->
    runtime_typed G R (ForkLock e1 e2) (LockT c3 t)
| RT_acquire G e t o R :
    runtime_typed G R e (LockT (o, Closed) t) ->
    runtime_typed G R (Acquire e) (PairT (LockT (o, Opened) t) t)
| RT_release G G1 G2 e1 e2 t o R R1 R2 :
    env_split G G1 G2 -> R ≡ₚ R1 ++ R2 ->
    runtime_typed G1 R1 e1 (LockT (o, Opened) t) ->
    runtime_typed G2 R2 e2 t ->
    runtime_typed G R (Release e1 e2) (LockT (o, Closed) t)
| RT_wait G e t R :
    runtime_typed G R e (LockT (Owner, Closed) t) ->
    runtime_typed G R (Wait e) t
| RT_drop G e t R :
    runtime_typed G R e (LockT (Client, Closed) t) ->
    runtime_typed G R (Drop e) UnitT
| RT_funv G x e a b l R :
    env_unr G -> (l = Unr -> R = []) ->
    runtime_typed (<[x:=a]> ∅) R e b -> runtime_typed G R (Val (FunV x e)) (FunT l a b)
| RT_unitv G :
    env_unr G -> runtime_typed G [] (Val UnitV) UnitT
| RT_pairv G G1 G2 v1 v2 a b R R1 R2 :
    env_split G G1 G2 -> R ≡ₚ R1 ++ R2 ->
    runtime_typed G1 R1 (Val v1) a -> runtime_typed G2 R2 (Val v2) b ->
    runtime_typed G R (Val (PairV v1 v2)) (PairT a b)
| RT_sumv G n (ts : fin n -> type) i v R :
    runtime_typed G R (Val v) (ts i) ->
    runtime_typed G R (Val (SumV i v)) (SumT n ts)
| RT_barrierv G i a b R :
    env_unr G -> R ≡ₚ [(i, FunT Lin a b)] ->
    runtime_typed G R (Val (BarrierV i)) (FunT Lin a b)
| RT_lockv G i c t R :
    env_unr G -> R ≡ₚ [(i, LockT c t)] ->
    runtime_typed G R (Val (LockV i)) (LockT c t).

Local Hint Constructors runtime_typed : rt.

Lemma source_runtime G e t :
  typed G e t -> runtime_typed G [] e t.
Proof.
  induction 1; try solve [econstructor; eauto with rt; intros H; split; eauto].
  all: econstructor; try eassumption; try (intros H; split; eauto);
    try solve [match goal with |- [] ≡ₚ ?A ++ ?B => unify A (@nil (nat * type)); unify B (@nil (nat * type)); reflexivity end]; eauto.
Qed.

Lemma runtime_perm G R S e t :
  R ≡ₚ S -> runtime_typed G R e t -> runtime_typed G S e t.
Proof.
  intros Hp H; revert S Hp. induction H; intros S Hp;
    try (apply Permutation_nil in Hp; subst; eauto with rt).
  all: try solve [econstructor; eauto using Permutation_sym, Permutation_trans].
  all: try solve [eapply RT_fun; eauto; intros ->; destruct (H0 eq_refl) as [? ->];
    split; [assumption|now apply Permutation_nil in Hp]].
  all: eapply RT_funv; eauto; intros ->; specialize (H0 eq_refl); subst; now apply Permutation_nil in Hp.
Qed.

Local Definition env_lookup_empty := lookup_empty (M:=gmap String.string) (A:=type).
Local Definition env_lookup_insert_eq := lookup_insert_eq (M:=gmap String.string) (A:=type).
Local Definition env_insert_delete := insert_delete (M:=gmap String.string) (A:=type).
Local Definition env_insert_id := insert_id (M:=gmap String.string) (A:=type).
Local Definition env_lookup_delete_eq := lookup_delete_eq (M:=gmap String.string) (A:=type).
Local Definition env_lookup_delete_ne := lookup_delete_ne (M:=gmap String.string) (A:=type).
Local Definition env_lookup_insert_ne := lookup_insert_ne (M:=gmap String.string) (A:=type).
Local Definition env_lookup_union_r := lookup_union_r (M:=gmap String.string) (A:=type).
Local Definition env_lookup_union := lookup_union (M:=gmap String.string) (A:=type).
Local Definition env_lookup_difference := lookup_difference (M:=gmap String.string) (A:=type).

Lemma empty_env_unr : env_unr ∅.
Proof. intros x t H. unfold env in *. rewrite env_lookup_empty in H. discriminate. Qed.

Lemma split_empty G1 G2 : env_split ∅ G1 G2 -> G1 = ∅ ∧ G2 = ∅.
Proof.
  intros [H _]. symmetry in H. assert (G1 = ∅) by (eapply map_positive_l; eauto).
  subst G1. split; [reflexivity|]. etransitivity; [|exact H]. symmetry. by apply map_empty_union.
Qed.

Lemma empty_env_split : env_split ∅ ∅ ∅.
Proof.
  split; [symmetry; apply map_empty_union|].
  intros ? ? ? H; unfold env in *; rewrite env_lookup_empty in H; discriminate.
Qed.

Local Hint Resolve empty_env_split empty_env_unr : rt.

Lemma runtime_unr_value G R v t :
  runtime_typed G R (Val v) t -> unr t -> R = [].
Proof.
  intros HT. remember (Val v) as e eqn:He in HT. revert v He.
  induction HT; intros w He Hu; try discriminate; inversion Hu; subst;
    eauto using Permutation_nil.
  - specialize (IHHT1 _ eq_refl ltac:(eassumption)).
    specialize (IHHT2 _ eq_refl ltac:(eassumption)).
    subst. simpl in *. now apply Permutation_sym, Permutation_nil in H0.
  - eapply IHHT; [reflexivity|eauto].
    apply (inj_pair2_eq_dec nat Nat.eq_dec) in H1. congruence || (subst; eauto).
Qed.

Definition env_ext (G D : env) :=
  (∀ x t, G !! x = Some t -> D !! x = Some t) ∧
  (∀ x t, D !! x = Some t -> G !! x = None -> unr t).

Lemma env_ext_unr G D : env_ext G D -> env_unr G -> env_unr D.
Proof.
  intros [Hsub Hextra] Hu x t Ht.
  destruct (G !! x) as [a|] eqn:Ha; eauto.
  specialize (Hsub _ _ Ha); congruence || (assert (a = t) by congruence; subst; eauto).
Qed.

Lemma env_ext_var G D x t : env_ext G D -> env_var G x t -> env_var D x t.
Proof.
  intros [Hsub Hextra] (G' & -> & Hu). unfold env in *.
  assert (Hx : D !! x = Some t) by (apply Hsub; apply env_lookup_insert_eq).
  exists (delete x D). split; [rewrite env_insert_delete, decide_True by reflexivity; symmetry; by apply env_insert_id|].
  intros y a Ha. destruct (decide (x = y)) as [->|Hne].
  - rewrite env_lookup_delete_eq in Ha; discriminate.
  - rewrite env_lookup_delete_ne in Ha by congruence.
    destruct (G' !! y) eqn:Hy.
    + assert (D !! y = Some t0) by (apply Hsub; by rewrite env_lookup_insert_ne).
      assert (a = t0) by congruence. subst. eauto.
    + eapply Hextra; [exact Ha|by rewrite env_lookup_insert_ne].
Qed.

Lemma env_ext_bind G G' D x t :
  env_ext G D -> env_bind G' x t G ->
  env_bind (<[x:=t]> D) x t D ∧ env_ext G' (<[x:=t]> D).
Proof.
  intros [Hsub Hextra] [-> Hu]. unfold env in *. split.
  - split; [reflexivity|]. intros a Ha. unfold env in *.
    destruct (G !! x) as [b|] eqn:Hb.
    + specialize (Hsub _ _ Hb). rewrite Ha in Hsub. injection Hsub as ->. apply Hu. reflexivity.
    + eauto.
  - split; intros y a; unfold env in *; destruct (decide (x = y)) as [->|Hne];
      rewrite ?env_lookup_insert_eq, ?env_lookup_insert_ne by congruence; eauto; congruence.
Qed.

Lemma env_ext_split G G1 G2 D :
  env_ext G D -> env_split G G1 G2 ->
  ∃ D1 D2, env_split D D1 D2 ∧ env_ext G1 D1 ∧ env_ext G2 D2.
Proof.
  intros [Hsub Hextra] [-> Hd]. unfold env in *.
  exists (G1 ∪ D ∖ G2), G2.
  assert (H1 : ∀ x t, G1 !! x = Some t -> D !! x = Some t).
  { intros x t Ht. apply Hsub. rewrite env_lookup_union, Ht. apply union_Some_l. }

  assert (H2 : ∀ x t, G2 !! x = Some t -> D !! x = Some t).
  { intros x t Ht. apply Hsub.
    destruct (G1 !! x) as [a|] eqn:Ha.
    - destruct (Hd _ _ _ Ha Ht) as [-> _]. rewrite env_lookup_union, Ha. apply union_Some_l.
    - by rewrite env_lookup_union_r by exact Ha. }
  split.
  - split.
    + apply map_eq. intros x.
      rewrite !env_lookup_union, env_lookup_difference.
      destruct (G1 !! x) as [a|] eqn:Ha, (G2 !! x) as [b|] eqn:Hb;
        simpl; rewrite ?union_Some_l, ?(left_id None union), ?(H1 _ _ Ha), ?(H2 _ _ Hb); try reflexivity; symmetry; apply (right_id None union).
    + intros x a b Ha Hb. unfold env in *.
      rewrite env_lookup_union, env_lookup_difference, Hb in Ha.
      destruct (G1 !! x) eqn:H; rewrite ?union_Some_l, ?(left_id None union) in Ha; try discriminate.
      injection Ha as <-. eauto.
  - split; [split|split; congruence].
    + intros x t Ht. unfold env in *. rewrite env_lookup_union, Ht. apply union_Some_l.
    + intros x t Hd' Hnone. unfold env in *. rewrite env_lookup_union_r in Hd' by exact Hnone.
      rewrite env_lookup_difference in Hd'. destruct (G2 !! x) eqn:Hb;
        simpl in Hd'; try discriminate.
      eapply Hextra; [exact Hd'|by rewrite env_lookup_union_r by exact Hnone].
Qed.

Local Ltac weaken_split :=
  match goal with
  | Hs : env_split ?G ?G1 ?G2, Hext : env_ext ?G ?D |- _ =>
      destruct (env_ext_split _ _ _ _ Hext Hs) as (? & ? & ? & ? & ?)
  end.

Lemma runtime_weaken G R e t :
  runtime_typed G R e t -> ∀ D, env_ext G D -> runtime_typed D R e t.
Proof.
  induction 1; intros D Hd;
    try solve [econstructor; eauto using env_ext_var, env_ext_unr with rt];
    try solve [weaken_split; econstructor; eauto using env_ext_unr with rt;
      intros ->; edestruct H1; eauto using env_ext_unr].
  all: match goal with
    | Hb : env_bind _ _ _ _, Hext : env_ext _ _ |- _ =>
        destruct (env_ext_bind _ _ _ _ _ Hext Hb) as [? ?];
        econstructor; eauto; intros ->; edestruct H0; eauto using env_ext_unr
    end.
Qed.

Lemma runtime_weaken_closed G R e t :
  env_unr G -> runtime_typed ∅ R e t -> runtime_typed G R e t.
Proof.
  intros Hu Ht. eapply runtime_weaken; [exact Ht|].
  split; intros; unfold env in *; rewrite env_lookup_empty in *; eauto; discriminate.
Qed.

Local Ltac list_chunks l :=
  lazymatch l with
  | [] => let T := type of l in constr:([] : list T)
  | ?a :: ?b =>
      let bs := list_chunks b in constr:([a] :: bs)
  | ?a ++ ?b =>
      let xs := list_chunks a in let ys := list_chunks b in
      eval cbn in (xs ++ ys)
  | _ => constr:([l])
  end.

Lemma concat_permutation {A} (xs ys : list (list A)) :
  xs ≡ₚ ys -> concat xs ≡ₚ concat ys.
Proof.
  induction 1; simpl; try reflexivity.
  - now apply Permutation_app_head.
  - rewrite !app_assoc. apply Permutation_app_tail, Permutation_app_comm.
  - etransitivity; eauto.
Qed.

Local Ltac move_chunk a l prefix :=
  lazymatch l with
  | ?x :: ?xs =>
      lazymatch x with
      | a => constr:((prefix, xs))
      | _ => let p := eval cbn in (prefix ++ [x]) in move_chunk a xs p
      end
  end.

Local Ltac chunks_perm :=
  tryif reflexivity then idtac else
    lazymatch goal with
    | |- ?a :: ?xs ≡ₚ ?ys =>
        let T := type of a in let p0 := constr:(@nil T) in
        let found := move_chunk a ys p0 in
        lazymatch found with
        | (?p, ?q) =>
            let mid := eval cbn in (p ++ q) in
            let ys' := eval cbn in (p ++ a :: q) in
            change (a :: xs ≡ₚ ys');
            transitivity (a :: mid);
            [apply perm_skip; change (xs ≡ₚ mid); chunks_perm
            |exact (Permutation_middle p q a)]
        end
    end.

Local Ltac ports_perm :=
  rewrite <- ?app_assoc; rewrite ?app_nil_r;
  tryif reflexivity then idtac else
    lazymatch goal with
    | |- ?l ≡ₚ ?r =>
        let a := list_chunks l in let b := list_chunks r in
        replace l with (concat a) by (cbn; rewrite ?app_nil_r; reflexivity);
        replace r with (concat b) by (cbn; rewrite ?app_nil_r; reflexivity);
        apply concat_permutation; chunks_perm
    end.

Local Definition env_delete_union := delete_union (M:=gmap String.string) (A:=type).
Local Definition env_delete_insert := delete_insert (M:=gmap String.string) (A:=type).
Local Definition env_delete_id := delete_id (M:=gmap String.string) (A:=type).

Definition subst_at (G : env) (x : String.string) a (V S : ports) :=
  (G !! x = Some a ∧ S = V) ∨ (G !! x = None ∧ S = []).

Lemma delete_unr G x : env_unr G -> env_unr (delete x G).
Proof.
  intros Hu y t Hy. unfold env in *. destruct (decide (x = y)) as [->|Hne].
  - rewrite env_lookup_delete_eq in Hy. discriminate.
  - rewrite env_lookup_delete_ne in Hy by congruence. eauto.
Qed.

Lemma subst_at_unr G x a V S v :
  subst_at G x a V S -> env_unr G -> runtime_typed ∅ V (Val v) a -> S = [].
Proof. intros [[H ->]|[_ ->]] Hu Hv; eauto using runtime_unr_value. Qed.

Lemma subst_env_split G G1 G2 x a V S v :
  env_split G G1 G2 -> subst_at G x a V S -> runtime_typed ∅ V (Val v) a ->
  ∃ S1 S2, S = S1 ++ S2 ∧
    env_split (delete x G) (delete x G1) (delete x G2) ∧
    subst_at G1 x a V S1 ∧ subst_at G2 x a V S2.
Proof.
  intros [-> Hd] Hat Hv.
  assert (Hs : env_split (delete x (G1 ∪ G2)) (delete x G1) (delete x G2)).
  { split; [unfold env in *; apply env_delete_union|].
    intros y t u Ht Hu. unfold env in *. destruct (decide (x = y)) as [->|Hne].
    - rewrite env_lookup_delete_eq in Ht. discriminate.
    - rewrite env_lookup_delete_ne in Ht, Hu by congruence. eauto. }
  unfold subst_at, env in *.
  rewrite env_lookup_union in Hat.
  destruct (G1 !! x) as [a1|] eqn:H1, (G2 !! x) as [a2|] eqn:H2;
    rewrite ?union_Some_l, ?(left_id None union) in Hat;
    destruct Hat as [[Ha ->]|[Ha ->]]; try discriminate; try (injection Ha as ->).
  - destruct (Hd _ _ _ H1 H2) as [-> Hu].
    assert (V = []) by eauto using runtime_unr_value.
    subst V. exists [], []. split; [reflexivity|]; split; [exact Hs|]; tauto.
  - exists V, []. rewrite app_nil_r. split; [reflexivity|]; split; [exact Hs|]; tauto.
  - exists [], V. split; [reflexivity|]; split; [exact Hs|]; tauto.
  - exists [], []. split; [reflexivity|]; split; [exact Hs|]; tauto.
Qed.

Lemma subst_bind_same G G' x a b V S v :
  env_bind G' x b G -> subst_at G x a V S -> runtime_typed ∅ V (Val v) a ->
  S = [] ∧ env_bind G' x b (delete x G).
Proof.
  intros [-> Hu] Hat Hv. split.
  - destruct Hat as [[Ha ->]|[_ ->]]; eauto using runtime_unr_value.
  - split; unfold env in *.
    + rewrite env_insert_delete, decide_True by reflexivity. reflexivity.
    + intros t Ht. unfold env in Ht. rewrite env_lookup_delete_eq in Ht. discriminate.
Qed.

Lemma subst_bind_other G G' x y a b V S :
  x ≠ y -> env_bind G' y b G -> subst_at G x a V S ->
  env_bind (delete x G') y b (delete x G) ∧ subst_at G' x a V S.
Proof.
  intros Hne [-> Hu] Hat. unfold subst_at, env in *.
  rewrite env_lookup_insert_ne by congruence. split; [|exact Hat].
  split; unfold env in *.
  - rewrite env_delete_insert, decide_False by congruence. reflexivity.
  - intros t Ht. unfold env in Ht. rewrite env_lookup_delete_ne in Ht by congruence. eauto.
Qed.

Lemma subst_runtime_var G x y a b V S v :
  env_var G y b -> subst_at G x a V S -> runtime_typed ∅ V (Val v) a ->
  runtime_typed (delete x G) S (if decide (x = y) then Val v else Var y) b.
Proof.
  intros (D & -> & Hu) Hat Hv. unfold subst_at, env in *.
  destruct (decide (x = y)) as [->|Hne].
  - rewrite env_lookup_insert_eq in Hat. destruct Hat as [[H ->]|[H _]]; try discriminate.
    injection H as ->. rewrite env_delete_insert, decide_True by reflexivity.
    eauto using runtime_weaken_closed, delete_unr.
  - rewrite env_lookup_insert_ne in Hat by congruence.
    assert (S = []).
    { destruct Hat as [[H ->]|[_ ->]]; eauto using runtime_unr_value. }
    subst S. rewrite env_delete_insert, decide_False by congruence.
    apply RT_var. exists (delete x D). eauto using delete_unr.
Qed.

Lemma runtime_value_unr_env G R v t :
  runtime_typed G R (Val v) t -> env_unr G.
Proof.
  intros HT. remember (Val v) as e eqn:He in HT. revert v He.
  induction HT; intros w He; try discriminate; auto.
  destruct H as [-> Hd]. intros x u Hu. unfold env in *.
  rewrite env_lookup_union in Hu.
  destruct (G1 !! x) eqn:Hx; rewrite ?union_Some_l, ?(left_id None union) in Hu.
  - injection Hu as <-. eapply IHHT1; [reflexivity|exact Hx].
  - eapply IHHT2; [reflexivity|exact Hu].
  - apply (IHHT _ eq_refl).
Qed.


Lemma runtime_value_env G D R v t :
  runtime_typed G R (Val v) t -> env_unr D -> runtime_typed D R (Val v) t.
Proof.
  intros HT. remember (Val v) as e eqn:He in HT. revert v He D.
  induction HT; intros w He D Hu; try discriminate; inversion He; subst; eauto with rt.
  eapply RT_pairv with (G1:=D) (G2:=∅); [|eassumption|eapply IHHT1; eauto|eapply IHHT2; eauto].
  split; [symmetry; apply map_union_empty|].
  intros y t1 t2 Ha Hb. unfold env in *. rewrite env_lookup_empty in Hb. discriminate.
  apply empty_env_unr.
Qed.

Local Ltac subst_split :=
  match goal with
  | Hs : env_split ?G ?G1 ?G2, Hat : subst_at ?G ?x ?a ?V ?S,
    Hv : runtime_typed ∅ ?V (Val ?v) ?a |- _ =>
      destruct (subst_env_split _ _ _ _ _ _ _ _ Hs Hat Hv)
        as (? & ? & -> & ? & ? & ?)
  end.

Lemma runtime_subst G R e t x a V v :
  runtime_typed G R e t -> runtime_typed ∅ V (Val v) a ->
  ∀ S, subst_at G x a V S ->
    runtime_typed (delete x G) (R ++ S) (subst x v e) t.
Proof.
  intros HT Hv. induction HT; intros S Hat.
  all: try solve [
    lazymatch goal with
    | Hat : subst_at ?G ?x ?a ?V ?S |- runtime_typed _ (?R ++ ?S) (subst ?x ?v (Val ?w)) ?t =>
        let HT := fresh in
        assert (HT : runtime_typed G R (Val w) t) by (econstructor; eassumption);
        assert (S = []) by eauto using subst_at_unr, runtime_value_unr_env;
        subst S; rewrite app_nil_r; simpl;
        eauto using runtime_value_env, runtime_value_unr_env, delete_unr
    end].
  - simpl. eapply subst_runtime_var; eauto.
  - simpl. destruct (decide (x = x0)) as [->|Hne].
    + destruct (subst_bind_same _ _ _ _ _ _ _ _ H Hat Hv) as [-> Hb].
      rewrite app_nil_r. eapply RT_fun; eauto using delete_unr.
      intros ->. edestruct H0; eauto using delete_unr.
    + destruct (subst_bind_other _ _ _ _ _ _ _ _ Hne H Hat) as [Hb Hat'].
      eapply RT_fun; eauto. intros ->.
      edestruct H0 as [Hu ->]; [reflexivity|].
      assert (S = []) by eauto using subst_at_unr. subst. simpl; eauto using delete_unr.
  - simpl. subst_split.
    eapply RT_app; [eassumption| |eapply IHHT1; eassumption|eapply IHHT2; eassumption].
    etransitivity; [apply Permutation_app_tail; eassumption|ports_perm].
  - assert (S = []) by eauto using subst_at_unr. subst. simpl. eauto using delete_unr with rt.
  - simpl. subst_split.
    eapply RT_pair; [eassumption| |eapply IHHT1; eassumption|eapply IHHT2; eassumption].
    etransitivity; [apply Permutation_app_tail; eassumption|ports_perm].
  - simpl. subst_split.
    eapply RT_let; [eassumption| |eapply IHHT1; eassumption|eapply IHHT2; eassumption].
    etransitivity; [apply Permutation_app_tail; eassumption|ports_perm].
  - simpl. eapply RT_sum; eauto.
  - simpl. subst_split.
    eapply RT_match; [eassumption| | |eapply IHHT; eassumption|].
    3: intros i; unfold compose; eauto.
    + etransitivity; [apply Permutation_app_tail; eassumption|ports_perm].
    + intros ->. edestruct H1 as [Hu ->]; [reflexivity|].
      split; [by apply delete_unr|]. simpl. eauto using subst_at_unr.
  - simpl. eapply RT_fork; eauto.
  - simpl. eapply RT_new; eauto.
  - simpl. subst_split.
    eapply RT_forklock; [eassumption| |eassumption|eapply IHHT1; eassumption|eapply IHHT2; eassumption].
    etransitivity; [apply Permutation_app_tail; eassumption|ports_perm].
  - simpl. eapply RT_acquire; eauto.
  - simpl. subst_split.
    eapply RT_release; [eassumption| |eapply IHHT1; eassumption|eapply IHHT2; eassumption].
    etransitivity; [apply Permutation_app_tail; eassumption|ports_perm].
  - simpl. eapply RT_wait; eauto.
  - simpl. eapply RT_drop; eauto.
Qed.

Lemma fin_list_members {A} n (f : fin n -> A) a :
  In a (fin_list n f) ↔ ∃ i, f i = a.
Proof.
  induction n as [|n IH]; simpl.
  - split; [contradiction|intros [i _]; exact (fin_0_inv _ i)].
  - change ((f 0%fin = a ∨ In a (fin_list n (f ∘ FS))) ↔ ∃ i, f i = a).
    rewrite IH. split.
    + intros [H|[i H]]; [exists 0%fin|exists (FS i)]; exact H.
    + intros [i H]. revert H. induction i using fin_S_inv; simpl; eauto.
Qed.

Lemma in_fin_union n (f : fin n -> gset nat) j :
  j ∈ fin_union n f ↔ ∃ i, j ∈ f i.
Proof.
  assert (H : ∀ X : gset (gset nat), j ∈ big_union X ↔ ∃ Y, Y ∈ X ∧ j ∈ Y).
  { unfold big_union. apply (set_fold_ind_L (λ U X, j ∈ U ↔ ∃ Y, Y ∈ X ∧ j ∈ Y)).
    - set_solver.
    - intros Y X U Hnot IH. rewrite elem_of_union, IH. set_solver. }
  unfold fin_union. rewrite H. unfold fin_gset. split.
  - intros (Y & Hy & Hj). apply elem_of_list_to_set in Hy.
    apply list_elem_of_In in Hy. apply fin_list_members in Hy. destruct Hy as [i <-]. eauto.
  - intros [i Hi]. exists (f i). split; [|assumption].
    apply elem_of_list_to_set, list_elem_of_In, fin_list_members. eauto.
Qed.

Lemma in_permuted {A} (l r : list A) (a : A) :
  l ≡ₚ r -> (In a l ↔ In a r).
Proof. intros H; split; eauto using Permutation_in, Permutation_sym. Qed.

Definition has_port j (R : ports) := ∃ t, In (j,t) R.

Lemma port_perm_mem j R S : R ≡ₚ S -> (has_port j R ↔ has_port j S).
Proof. intros H; unfold has_port; setoid_rewrite (in_permuted _ _ _ H); reflexivity. Qed.

Lemma port_app j R S : has_port j (R ++ S) ↔ has_port j R ∨ has_port j S.
Proof. unfold has_port; setoid_rewrite in_app_iff; firstorder. Qed.

Lemma runtime_refs G R e t :
  runtime_typed G R e t -> ∀ j, j ∈ expr_refs e ↔ has_port j R.
Proof.
  induction 1; intros j; simpl;
    try match goal with Hp : ?R ≡ₚ _ |- _ => rewrite (port_perm_mem j _ _ Hp) end;
    rewrite ?elem_of_union, ?port_app;
    repeat match goal with
    | IH : ∀ j, j ∈ _ ↔ has_port j _ |- _ => progress rewrite (IH j)
    end;
    try solve [tauto | unfold has_port; simpl; setoid_rewrite elem_of_empty; firstorder |
      unfold has_port; simpl; rewrite elem_of_singleton; split;
      [intros ->; eauto|intros (? & H & []); congruence]].
  - rewrite in_fin_union. unfold compose.
    split.
    + intros [Hmem|[i Hmem]]; [now left|right]. by apply H4 in Hmem.
    + intros [Hmem|Hmem]; [now left|right].
      destruct n as [|n].
      * edestruct H1 as [_ ->]; [reflexivity|]. destruct Hmem as [? []].
      * exists 0%fin. by apply H4.
  - unfold has_port. rewrite elem_of_singleton. simpl. split;
      [intros ->; eexists; left; reflexivity|intros (? & [Hu|[]]); inversion Hu; reflexivity].
  - unfold has_port. rewrite elem_of_singleton. simpl. split;
      [intros ->; eexists; left; reflexivity|intros (? & [Hu|[]]); inversion Hu; reflexivity].
Qed.

Local Ltac invert_runtime H :=
  inversion H; clear H; subst;
  repeat match goal with
  | Heq : existT _ _ = existT _ _ |- _ =>
      first [apply (inj_pair2_eq_dec nat Nat.eq_dec) in Heq |
        fail 1]; subst
  | Hsplit : env_split ∅ _ _ |- _ =>
      apply split_empty in Hsplit; destruct Hsplit as [-> ->]
  end.

Definition context_types (k : expr -> expr) a b (F : ports) :=
  ∀ e S, runtime_typed ∅ S e a -> runtime_typed ∅ (S ++ F) (k e) b.

Local Ltac rt_rebuild :=
  first [
    econstructor; [apply empty_env_split| |eassumption|eassumption]; ports_perm |
    eapply RT_forklock; [apply empty_env_split| |eassumption|eassumption|eassumption]; ports_perm |
    eapply RT_match; [apply empty_env_split| |eassumption|eassumption|eassumption]; ports_perm |
    econstructor; eassumption].

Local Ltac finish_ctx h R :=
  match goal with
    | Hh : runtime_typed ∅ ?S h ?a, HP : R ≡ₚ ?R1 ++ ?R2 |- _ =>
        let F := lazymatch S with R1 => R2 | _ => R1 end in
        exists a, S, F; split; [exact Hh|]; split;
        [etransitivity; [exact HP|ports_perm]|
          unfold context_types; intros e' S' HT'; clear Hh HP; rt_rebuild]
    | Hh : runtime_typed ∅ ?S h ?a |- _ =>
        exists a, S, []; split; [exact Hh|]; split; [ports_perm|];
        unfold context_types; intros e' S' HT'; cbn; rewrite app_nil_r;
        econstructor; eassumption
    end.

Lemma context_one_type k : ctx1 k -> ∀ e R b,
  runtime_typed ∅ R (k e) b ->
  ∃ a S F, runtime_typed ∅ S e a ∧ R ≡ₚ S ++ F ∧ context_types k a b F.
Proof.
  intros Hk. destruct Hk; intros h R b HT; invert_runtime HT; finish_ctx h R.
Qed.

Lemma context_type k : ctx k -> ∀ e R b,
  runtime_typed ∅ R (k e) b ->
  ∃ a S F, runtime_typed ∅ S e a ∧ R ≡ₚ S ++ F ∧ context_types k a b F.
Proof.
  induction 1; intros e R b HT.
  - exists b, R, []. split; [exact HT|]. split; [ports_perm|].
    intros ? ? Ht. by rewrite app_nil_r.
  - destruct (context_one_type _ H _ _ _ HT) as (a & S & F & HS & HR & HF).
    destruct (IHctx _ _ _ HS) as (c & T & G & HC & Hperm & HG).
    exists c, T, (G ++ F). split; [exact HC|]. split.
    + etransitivity; [exact HR|].
      etransitivity; [apply Permutation_app_tail; exact Hperm|ports_perm].
    + intros w X Hw. unfold compose. rewrite app_assoc. apply HF, HG, Hw.
Qed.

Local Ltac type_permute H :=
  eapply runtime_perm; [|exact H];
  repeat match goal with H : _ ≡ₚ _ |- _ => progress rewrite H end; ports_perm.

Lemma runtime_sum_value G R n (ts : fin n -> type) (i : fin n) v :
  runtime_typed G R (Val (SumV i v)) (SumT n ts) ->
  runtime_typed G R (Val v) (ts i).
Proof.
  intros HT. remember (Val (SumV i v)) as e eqn:He in HT.
  remember (SumT n ts) as t eqn:Ht in HT.
  destruct HT; try discriminate.
  injection Ht as Hn Hts. subst n0.
  apply (inj_pair2_eq_dec nat Nat.eq_dec) in Hts. subst ts0.
  injection He as Hi ->.
  assert (i0 = i) by (eapply (inj fin_to_nat); eauto). subst i0. assumption.
Qed.

Lemma runtime_pure e e' R t :
  pure_step e e' -> runtime_typed ∅ R e t -> runtime_typed ∅ R e' t.
Proof.
  intros Hs HT. destruct Hs; invert_runtime HT.
  - match goal with Hb : env_bind _ _ _ _ |- _ => destruct Hb as [-> _] end.
    eapply RT_funv; eauto with rt. intros ->. firstorder.
  - match goal with Hf : runtime_typed _ _ (Val (FunV _ _)) _ |- _ => invert_runtime Hf end.
    assert (Hat : subst_at (<[x:=a0]> ∅) x a0 R2 R2).
    { left. split; [apply env_lookup_insert_eq|reflexivity]. }
    pose proof (runtime_subst _ _ _ _ _ _ _ _ H11 H7 _ Hat) as HT.
    assert (Hd : delete x (<[x:=a0]> ∅ : env) = ∅).
    { unfold env. rewrite env_delete_insert, decide_True by reflexivity.
      apply env_delete_id, env_lookup_empty. }
    rewrite Hd in HT. type_permute HT.
  - apply RT_unitv, empty_env_unr.
  - eapply RT_pairv; eauto with rt.
  - match goal with Hp : runtime_typed _ _ (Val (PairV _ _)) _ |- _ => invert_runtime Hp end.
    eapply RT_app; [apply empty_env_split| | |eassumption].
    2: eapply RT_app; [apply empty_env_split|reflexivity|eassumption|eassumption].
    repeat match goal with H : _ ≡ₚ _ |- _ => progress rewrite H end. ports_perm.
  - eapply RT_sumv; eauto with rt.
  - pose proof (runtime_sum_value _ _ _ _ _ _ H8) as HV.
    eapply RT_app; [apply empty_env_split| |exact (H9 i)|exact HV].
    repeat match goal with H : _ ≡ₚ _ |- _ => progress rewrite H end. ports_perm.
Qed.

(* A forest has fewer internal edges than vertices in every nonempty set.
   Edges are counted with multiplicity, even when they have the same endpoints. *)
Definition edges := list (nat * nat).
Definition count_where {A} (p : A -> bool) (l : list A) := length (List.filter p l).
Definition inside (X : gset nat) (e : nat * nat) :=
  bool_decide (e.1 ∈ X ∧ e.2 ∈ X).
Definition edge_count X E := count_where (inside X) E.
Definition forest_on (X : gset nat) (E : edges) :=
  ∀ Y : gset nat, Y ⊆ X -> Y ≠ ∅ -> edge_count Y E < size Y.

Lemma count_where_app {A} (p : A -> bool) l r :
  count_where p (l ++ r) = count_where p l + count_where p r.
Proof. unfold count_where. by rewrite List.filter_app, length_app. Qed.

Lemma count_where_perm {A} (p : A -> bool) l r :
  l ≡ₚ r -> count_where p l = count_where p r.
Proof.
  induction 1; unfold count_where in *; simpl in *; auto.
  - destruct (p x); simpl; lia.
  - destruct (p x), (p y); reflexivity.
  - congruence.
Qed.

Lemma count_where_le {A} (p q : A -> bool) l :
  (∀ a, In a l -> p a = true -> q a = true) ->
  count_where p l <= count_where q l.
Proof.
  induction l as [|a l IH]; intros H; [reflexivity|].
  specialize (IH ltac:(eauto with datatypes)).
  pose proof (H a (or_introl eq_refl)) as Ha.
  unfold count_where in *; simpl. destruct (p a), (q a); simpl in *; lia || congruence.
Qed.

Lemma count_where_full {A} (p : A -> bool) l :
  (∀ a, In a l -> p a = true) -> count_where p l = length l.
Proof. induction l as [|a l IH]; intros H; [reflexivity|].
  unfold count_where in *. simpl. rewrite (H a (or_introl eq_refl)). simpl. f_equal. apply IH. intros b Hb. apply H. right. exact Hb. Qed.

Lemma count_where_zero {A} (p : A -> bool) l :
  (∀ a, In a l -> p a = false) -> count_where p l = 0.
Proof.
  induction l as [|a l IH]; intros H; [reflexivity|].
  unfold count_where in *. simpl. rewrite (H a (or_introl eq_refl)).
  apply IH. intros b Hb. apply H. right. exact Hb.
Qed.

Lemma count_where_positive {A} (p : A -> bool) l a :
  In a l -> p a = true -> 0 < count_where p l.
Proof.
  induction l as [|b l IH]; [contradiction|]; intros [<-|H] Hp; unfold count_where in *; simpl.
  - rewrite Hp. simpl. lia.
  - specialize (IH H Hp). destruct (p b); simpl; lia.
Qed.

Lemma count_where_map {A B} (p : B -> bool) (f : A -> B) l :
  count_where p (map f l) = count_where (p ∘ f) l.
Proof.
  induction l; unfold count_where in *; simpl; [reflexivity|].
  unfold compose in *. destruct (p (f a)); simpl; lia.
Qed.

Lemma edge_count_app X E F : edge_count X (E ++ F) = edge_count X E + edge_count X F.
Proof. apply count_where_app. Qed.

Lemma edge_count_perm X E F : E ≡ₚ F -> edge_count X E = edge_count X F.
Proof. apply count_where_perm. Qed.

Lemma edge_count_mono X Y E :
  (∀ i j, In (i,j) E -> i ∈ X -> j ∈ X -> i ∈ Y ∧ j ∈ Y) ->
  edge_count X E <= edge_count Y E.
Proof.
  intros H. apply count_where_le. intros [i j] Hin. unfold inside. simpl.
  rewrite !bool_decide_eq_true. intros [Hi Hj]. eauto.
Qed.

Lemma size_cut (X B : gset nat) :
  size X = size (X ∖ B) + size (X ∩ B).
Proof.
  assert (X = (X ∖ B) ∪ (X ∩ B)) as H.
  { apply set_eq. intros i. destruct (decide (i ∈ B)); set_solver. }
  rewrite H at 1. apply size_union; set_solver.
Qed.

(* The old fragment uses its full internal edge budget. Reassigning its
   external references preserves sparsity when the new fragment is a forest. *)
Lemma forest_replace (A B F : gset nat) E I J U V :
  A ## F -> B ## F -> A ≠ ∅ ->
  (∀ i j, In (i,j) E -> i ∈ F ∧ j ∈ A ∪ F) ->
  (∀ i j, In (i,j) I -> i ∈ A ∧ j ∈ A) ->
  (∀ i j, In (i,j) J -> i ∈ B ∧ j ∈ B) ->
  (∀ i j, In (i,j) U -> i ∈ A ∧ j ∈ A ∪ F) ->
  (∀ i j, In (i,j) V -> i ∈ B) ->
  map snd U ≡ₚ map snd V ->
  S (length I) = size A ->
  forest_on B J ->
  forest_on (A ∪ F) (I ++ U ++ E) ->
  forest_on (B ∪ F) (J ++ V ++ E).
Proof.
  intros HAF HBF HAn HE HI HJ HU HV Hperm Hsize Hforest Hbefore.
  assert (Hfull : ∀ X : gset nat, A ⊆ X -> edge_count X I = length I).
  { intros X HX. apply count_where_full. intros [i j] Hij.
    unfold inside; simpl. apply bool_decide_eq_true. specialize (HI _ _ Hij). set_solver. }
  assert (Houtside : ∀ i j, In (i,j) U -> j ∈ F).
  { intros i j Hij. specialize (HU _ _ Hij) as [Hi Hj].
    destruct (decide (j ∈ A)) as [Hja|Hja]; [|set_solver].
    specialize (Hbefore A ltac:(set_solver) HAn).
    rewrite !edge_count_app, Hfull in Hbefore by set_solver.
    assert (0 < edge_count A U).
    { eapply count_where_positive; [exact Hij|]. apply bool_decide_eq_true. exact (conj Hi Hja). }
    lia. }
  assert (Hout' : ∀ i j, In (i,j) V -> j ∈ F).
  { intros i j Hin. assert (In j (map snd V)) by (apply in_map with (f:=snd) in Hin; exact Hin).
    apply (in_permuted _ _ _ Hperm) in H. apply in_map_iff in H as ([p q] & <- & Hpq).
    eauto. }
  intros X HX Hnon.
  rewrite !edge_count_app.
  destruct (decide (X ∩ B = ∅)) as [HZ|HZ].
  - assert (HX' : X ⊆ F) by (clear - HX HZ; set_solver).
    assert (edge_count X J = 0).
    { apply count_where_zero. intros [i j] H. specialize (HJ _ _ H).
      apply bool_decide_eq_false. simpl. set_solver. }
    assert (edge_count X V = 0).
    { apply count_where_zero. intros [i j] Hin. specialize (HV _ _ Hin).
      apply bool_decide_eq_false. simpl. set_solver. }
    specialize (Hbefore X ltac:(set_solver) Hnon). rewrite !edge_count_app in Hbefore. lia.
  - set (Y := (X ∖ B) ∪ A).
    specialize (Hbefore Y ltac:(unfold Y; set_solver) ltac:(unfold Y; set_solver)).
    rewrite !edge_count_app, Hfull in Hbefore by (unfold Y; set_solver).
    assert (Hcap : edge_count X J <= edge_count (X ∩ B) J).
    { apply edge_count_mono. intros i j Hin. specialize (HJ _ _ Hin). set_solver. }
    specialize (Hforest (X ∩ B) ltac:(set_solver) HZ).
    assert (Hframe : edge_count X E <= edge_count Y E).
    { apply edge_count_mono. intros i j H. specialize (HE _ _ H). unfold Y. set_solver. }
    assert (Htransfer : edge_count X V <= edge_count Y U).
    { pose (p := λ j : nat, bool_decide (j ∈ X ∖ B)).
      assert (Heq : edge_count Y U = count_where p (map snd U)).
      { rewrite count_where_map. apply Nat.le_antisymm; apply count_where_le;
          intros [i j] Hin; specialize (HU _ _ Hin) as [Ha _];
          specialize (Houtside _ _ Hin); unfold inside, compose, p, Y; simpl;
          rewrite !bool_decide_eq_true; set_solver. }
      rewrite Heq, (count_where_perm p _ _ Hperm), count_where_map.
      apply count_where_le. intros [i j] Hin. specialize (Hout' _ _ Hin).
      unfold inside, compose, p; simpl. rewrite !bool_decide_eq_true. set_solver. }
    assert (Hcard : size Y = size (X ∖ B) + size A).
    { apply size_union. unfold Y. clear - HAF HBF HX. set_solver. }
    pose proof (size_cut X B). lia.
Qed.

(* Each row records the references stored by one object and the references
   allowed to point to it. Balance matches these lists across the configuration. *)
Record object_row := Row {
  row_id : nat;
  row_obj : obj;
  row_uses : ports;
  row_offers : ports
}.

Definition owner_mark (c : lockcap) :=
  match c.1 with Owner => true | Client => false end.
Definition open_mark (c : lockcap) :=
  match c.2 with Opened => true | Closed => false end.
Definition open_slots (o : option val) := if o then 0 else 1.
Definition lock_ports (n : nat) t := map (λ c, (n, LockT c t)).

Definition lock_caps k o (cs : list lockcap) :=
  length cs = S k ∧
  count_where owner_mark cs = 1 ∧
  count_where open_mark cs = open_slots o.

Definition stored_value o R t :=
  match o with
  | Some v => runtime_typed ∅ R (Val v) t
  | None => R = []
  end.

Definition row_typed r : Prop :=
  match row_obj r with
  | Thread e => runtime_typed ∅ (row_uses r) e UnitT ∧ row_offers r = []
  | Barrier => row_uses r = [] ∧ ∃ a b,
      row_offers r ≡ₚ [(row_id r, FunT Lin a b); (row_id r, FunT Lin b a)]
  | Lock k o => ∃ t cs,
      stored_value o (row_uses r) t ∧ lock_caps k o cs ∧
      row_offers r ≡ₚ lock_ports (row_id r) t cs
  end.

Definition row_names (L : list object_row) : gset nat :=
  list_to_set (map row_id L).
Definition all_uses := flat_map row_uses.
Definition all_offers := flat_map row_offers.
Definition out_edges i (R : ports) : edges := map (λ p, (i, p.1)) R.
Definition row_edges L := flat_map (λ r, out_edges (row_id r) (row_uses r)) L.

Definition row_rep (ρ : cfg) L :=
  NoDup (map row_id L) ∧
  (∀ i o, ρ !! i = Some o ↔ ∃ r, In r L ∧ row_id r = i ∧ row_obj r = o).

Definition network L :=
  Forall row_typed L ∧ all_uses L ≡ₚ all_offers L ∧
  forest_on (row_names L) (row_edges L).

Lemma in_row_names L i : i ∈ row_names L ↔ ∃ r, In r L ∧ row_id r = i.
Proof. unfold row_names. rewrite elem_of_list_to_set, list_elem_of_In, in_map_iff. firstorder. Qed.

Lemma row_names_app A F : row_names (A ++ F) = row_names A ∪ row_names F.
Proof. unfold row_names. rewrite map_app. apply list_to_set_app_L. Qed.

Lemma row_names_cons r L : row_names (r :: L) = {[row_id r]} ∪ row_names L.
Proof. change (row_names ([r] ++ L) = {[row_id r]} ∪ row_names L). rewrite row_names_app. unfold row_names at 1; cbn [map]; rewrite list_to_set_singleton_L; reflexivity. Qed.

Lemma row_rep_member ρ L r :
  row_rep ρ L -> In r L -> ρ !! row_id r = Some (row_obj r).
Proof. intros [_ H] Hr. apply H. eauto. Qed.

Lemma row_names_disjoint A F :
  NoDup (map row_id (A ++ F)) -> row_names A ## row_names F.
Proof.
  rewrite map_app. intros H. apply elem_of_disjoint. intros i.
  unfold row_names. rewrite !elem_of_list_to_set, !list_elem_of_In.
  induction A as [|a A IH]; simpl in *; [tauto|].
  inversion H as [|? ? Hnot Hnd]; subst.
  intros [<-|Hi] HF; [apply Hnot, list_elem_of_In, in_app_iff; auto|eauto].
Qed.

Local Definition cfg_lookup_empty := lookup_empty (M:=gmap nat) (A:=obj).
Local Definition cfg_lookup_insert_eq := lookup_insert_eq (M:=gmap nat) (A:=obj).
Local Definition cfg_lookup_insert_ne := lookup_insert_ne (M:=gmap nat) (A:=obj).
Local Definition cfg_lookup_union := lookup_union (M:=gmap nat) (A:=obj).

Lemma rows_insert ρ L i x R P :
  row_rep ρ L -> ρ !! i = None ->
  row_rep (<[i:=x]> ρ) (Row i x R P :: L).
Proof.
  intros [Hnd Hr] Hnone. split.
  - constructor; [|exact Hnd]. intros Hi. apply list_elem_of_In, in_map_iff in Hi as (r & Hi & Hin).
    assert (ρ !! i = Some (row_obj r)) by (apply Hr; eauto). congruence.
  - intros j y. unfold cfg in *. destruct (decide (i = j)) as [->|Hne].
    + rewrite cfg_lookup_insert_eq. split.
      * intros H. injection H as <-. eexists; simpl; eauto.
      * intros (r & [<-|Hin] & Hid & Hobj); simpl in *; [congruence|].
        assert (ρ !! j = Some y) by (apply Hr; eauto). congruence.
    + rewrite cfg_lookup_insert_ne by exact Hne. rewrite Hr.
      split.
      * intros (r & Hin & Hid & Hobj). exists r. simpl. tauto.
      * intros (r & [<-|Hin] & Hid & Hobj); [simpl in Hid; contradiction|eauto].
Qed.

Lemma rows_empty : row_rep ∅ [].
Proof.
  split; [constructor|]. intros i o. unfold cfg in *. rewrite cfg_lookup_empty. simpl.
  split; [discriminate|intros (? & H & _); contradiction].
Qed.

Lemma rows_perm ρ L L' : L ≡ₚ L' -> row_rep ρ L -> row_rep ρ L'.
Proof.
  intros H [Hnd Hr]. split.
  - apply NoDup_ListNoDup; eapply Permutation_NoDup; [by apply Permutation_map|now apply NoDup_ListNoDup].
  - intros i o. rewrite Hr. setoid_rewrite (in_permuted _ _ _ H). reflexivity.
Qed.

Lemma rows_take ρ L i x :
  row_rep (<[i:=x]>ρ) L -> ρ !! i = None ->
  ∃ R P F, L ≡ₚ Row i x R P :: F ∧ row_rep ρ F.
Proof.
  intros [Hnd Hrep] Hnone. unfold cfg in *.
  assert (Hi : <[i:=x]> ρ !! i = Some x) by apply cfg_lookup_insert_eq.
  apply Hrep in Hi as ([j y R P] & Hin & Hj & Hy). simpl in *. subst j y.
  apply in_split in Hin as (P1 & P2 & ->).
  exists R, P, (P1 ++ P2). split; [symmetry; apply Permutation_middle|].
  assert (row_rep (<[i:=x]> ρ) (Row i x R P :: P1 ++ P2)) as [Hnd' Hrep'].
  { eapply rows_perm; [symmetry; apply Permutation_middle|]. split; eassumption. }
  inversion Hnd' as [|? ? Hnot Hndf]; subst. split; [assumption|].
  intros j y. unfold cfg in *. destruct (decide (i = j)) as [->|Hne].
  - rewrite Hnone. split; [discriminate|].
    intros (r & Hin & Hid & _). exfalso. apply Hnot, list_elem_of_In. rewrite <- Hid. now apply in_map.
  - rewrite <- cfg_lookup_insert_ne with (i:=i) (x:=x) by exact Hne.
    rewrite Hrep'. split.
    + intros (r & [<-|Hin] & Hid & Ho); [simpl in Hid; contradiction|eauto].
    + intros (r & Hin & Hid & Ho). exists r. simpl. tauto.
Qed.

Lemma network_perm L L' : L ≡ₚ L' -> network L -> network L'.
Proof.
  intros Hp (Ht & Hb & Hf).
  assert (Hnames : row_names L = row_names L').
  { apply set_eq. intros i. rewrite !in_row_names.
    setoid_rewrite (in_permuted _ _ _ Hp). reflexivity. }
  split; [eapply Permutation_Forall; eauto|]. split.
  - unfold all_uses, all_offers in *. rewrite <- !(Permutation_flat_map _ Hp). exact Hb.
  - unfold forest_on in *. intros X HX Hn.
    unfold row_edges. rewrite <- (edge_count_perm X _ _ (Permutation_flat_map _ Hp)).
    apply Hf; [now rewrite Hnames|assumption].
Qed.

Lemma row_offer_source r j t :
  row_typed r -> In (j,t) (row_offers r) -> j = row_id r.
Proof.
  destruct r as [i x R P], x; cbn [row_typed row_id row_obj row_uses row_offers]; intros Ht Hin.
  - destruct Ht as [_ ->]. contradiction.
  - destruct Ht as (_ & a & b & Hp).
    apply (in_permuted _ _ _ Hp) in Hin. destruct Hin as [He|[He|[]]]; congruence.
  - destruct Ht as (a & cs & _ & _ & Hp).
    apply (in_permuted _ _ _ Hp) in Hin. apply in_map_iff in Hin as (c & He & _).
    congruence.
Qed.

Lemma row_edge_member L i j :
  In (i,j) (row_edges L) ↔ ∃ r t, In r L ∧ row_id r = i ∧ In (j,t) (row_uses r).
Proof.
  unfold row_edges, out_edges. rewrite in_flat_map. split.
  - intros (r & Hr & Hin). apply in_map_iff in Hin as ([p t] & He & Hmem).
    simpl in He. inversion He; subst. eauto.
  - intros (r & t & Hr & <- & Ht). exists r. split; [exact Hr|].
    apply in_map_iff. exists (j,t). auto.
Qed.

Lemma network_edge_end L i j :
  network L -> In (i,j) (row_edges L) -> j ∈ row_names L.
Proof.
  intros (Ht & Hb & Hf) Hin.
  apply row_edge_member in Hin as (r & t & Hr & Hid & Hj).
  assert (In (j,t) (all_uses L)) as Huse by (apply in_flat_map; eauto).
  apply (in_permuted _ _ _ Hb) in Huse.
  apply in_flat_map in Huse as (s & Hs & Ht').
  assert (row_typed s) by (eapply List.Forall_forall; eauto).
  apply in_row_names. exists s. split; [exact Hs|]. symmetry. eauto using row_offer_source.
Qed.

Lemma network_rewire A B F I J U V :
  network (A ++ F) ->
  NoDup (map row_id (A ++ F)) -> NoDup (map row_id (B ++ F)) ->
  A ≠ [] ->
  Forall row_typed B ->
  all_uses A ++ all_offers B ≡ₚ all_uses B ++ all_offers A ->
  row_edges A ≡ₚ I ++ U ->
  row_edges B ≡ₚ J ++ V ->
  (∀ i j, In (i,j) I -> j ∈ row_names A) ->
  (∀ i j, In (i,j) J -> j ∈ row_names B) ->
  map snd U ≡ₚ map snd V ->
  S (length I) = length A ->
  forest_on (row_names B) J ->
  network (B ++ F).
Proof.
  intros Hnet HdA HdB Hnon Htyped Hbal Hedges Hedges' HI HJ Hboundary Hsize Htree.
  destruct Hnet as (Ht & Hb & Hf).
  rewrite Forall_app in Ht. destruct Ht as [HA HF].
  split; [apply Forall_app; auto|]. split.
  - unfold all_uses, all_offers in *. rewrite !flat_map_app in *.
    apply Permutation_app_inv_l with (l := flat_map row_offers A).
    transitivity ((flat_map row_uses B ++ flat_map row_offers A) ++ flat_map row_uses F);
      [ports_perm|].
    rewrite <- Hbal.
    transitivity (flat_map row_offers B ++ (flat_map row_uses A ++ flat_map row_uses F));
      [ports_perm|].
    rewrite Hb. ports_perm.
  - assert (HA' : row_names A ≠ ∅).
    { destruct A as [|a A]; [contradiction|].
      rewrite row_names_cons. set_solver. }
    assert (Hcard : S (length I) = size (row_names A)).
    { rewrite Hsize. unfold row_names. rewrite size_list_to_set, length_map; [reflexivity|].
      rewrite map_app in HdA. apply NoDup_app in HdA. tauto. }
    assert (Hsource : ∀ L i j, In (i,j) (row_edges L) -> i ∈ row_names L).
    { intros L i j Hin. apply row_edge_member in Hin as (r & t & Hr & Hid & Hj).
      apply in_row_names. eauto. }
    assert (Htarget : ∀ i j, In (i,j) (row_edges (A ++ F)) -> j ∈ row_names A ∪ row_names F).
    { intros i j Hin. rewrite <- row_names_app. eapply network_edge_end; [|exact Hin].
      split; [apply Forall_app; auto|auto]. }
    assert (HEA : ∀ i j, In (i,j) (I ++ U) ->
      i ∈ row_names A ∧ j ∈ row_names A ∪ row_names F).
    { intros i j Hin. apply (in_permuted _ _ _ Hedges) in Hin. split; [eauto|].
      eapply (Htarget i j). unfold row_edges. rewrite flat_map_app. apply in_app_iff; auto. }
    assert (HEB : ∀ i j, In (i,j) (J ++ V) -> i ∈ row_names B).
    { intros i j Hin. apply (in_permuted _ _ _ Hedges') in Hin. eauto. }
    pose proof (row_names_disjoint _ _ HdA) as HAF.
    pose proof (row_names_disjoint _ _ HdB) as HBF.
    rewrite row_names_app. unfold forest_on in *. intros X HX Hn.
    assert (Hp : row_edges (B ++ F) ≡ₚ J ++ V ++ row_edges F).
    { unfold row_edges in *. rewrite flat_map_app, Hedges', <- app_assoc. reflexivity. }
    rewrite (edge_count_perm X _ _ Hp).
    eapply (forest_replace (row_names A) (row_names B) (row_names F)
      (row_edges F) I J U V); try eassumption.
    + intros i j Hin. split; [eauto|].
      eapply (Htarget i j). unfold row_edges. rewrite flat_map_app. apply in_app_iff; auto.
    + intros i j Hin. split.
      * eapply HEA, in_app_iff. left; exact Hin.
      * eauto.
    + intros i j Hin. split.
      * eapply HEB, in_app_iff. left; exact Hin.
      * eauto.
    + intros i j Hin. eapply HEA, in_app_iff. right; exact Hin.
    + intros i j Hin. eapply HEB, in_app_iff. right; exact Hin.
    + intros Y HY HYn. rewrite <- (row_names_app A F) in HY.
      assert (Hperm : row_edges (A ++ F) ≡ₚ I ++ U ++ row_edges F).
      { unfold row_edges in *. rewrite flat_map_app, Hedges, <- app_assoc. reflexivity. }
      rewrite <- (edge_count_perm Y _ _ Hperm). eauto.
Qed.

Lemma filter_permutation {A} (p : A -> bool) l m :
  l ≡ₚ m -> List.filter p l ≡ₚ List.filter p m.
Proof.
  induction 1; simpl; try reflexivity.
  - destruct (p x); eauto using perm_skip.
  - destruct (p x), (p y); simpl; auto using perm_swap, Permutation_refl.
  - etransitivity; eauto.
Qed.

Lemma filter_all {A} (p : A -> bool) L :
  (∀ a, In a L -> p a = true) -> List.filter p L = L.
Proof. intros H. apply forallb_filter_id, forallb_forall. exact H. Qed.

Lemma filter_none {A} (p : A -> bool) L :
  (∀ a, In a L -> p a = false) -> List.filter p L = [].
Proof.
  intros H. rewrite (List.filter_ext_in _ (λ _, false) _ H).
  apply filter_false.
Qed.

Definition port_at n (p : nat * type) := Nat.eqb p.1 n.

Lemma offers_filter L r :
  Forall row_typed L -> NoDup (map row_id L) -> In r L ->
  List.filter (port_at (row_id r)) (all_offers L) = row_offers r.
Proof.
  intros Ht Hd Hr. induction L as [|s L IH]; [contradiction|].
  inversion Ht as [|? ? Hs Hrest]; subst.
  inversion Hd as [|? ? Hnd Htail]; subst.
  unfold all_offers. simpl. rewrite List.filter_app.
  destruct Hr as [<-|Hr].
  - rewrite filter_all.
    + rewrite filter_none, app_nil_r; [reflexivity|].
      intros [j t] Hin. apply in_flat_map in Hin as (a & Ha & Hoffer).
      apply Nat.eqb_neq. simpl.
      assert (j = row_id a) by (eapply row_offer_source; [eapply List.Forall_forall; eauto|exact Hoffer]).
      subst j. intros He. apply Hnd, list_elem_of_In. rewrite <- He. now apply in_map.
    + intros [j t] H. apply Nat.eqb_eq. simpl. eauto using row_offer_source.
  - rewrite filter_none.
    + simpl. exact (IH Hrest Htail Hr).
    + intros [j t] Hin. apply Nat.eqb_neq. simpl.
      assert (j = row_id s) by eauto using row_offer_source.
      subst j. intros He. apply Hnd, list_elem_of_In. rewrite He. now apply in_map.
Qed.

Lemma selected_offers L r P Q :
  network L -> NoDup (map row_id L) -> In r L ->
  (∀ p, In p P -> p.1 = row_id r) ->
  all_uses L ≡ₚ P ++ Q ->
  ∃ D, row_offers r ≡ₚ P ++ D.
Proof.
  intros (Ht & Hb & _) Hnd Hr HP HQ.
  pose proof (filter_permutation (port_at (row_id r)) _ _
    (Permutation_trans (Permutation_sym Hb) HQ)) as H.
  rewrite (offers_filter _ _ Ht Hnd Hr), List.filter_app in H.
  rewrite (filter_all _ P) in H.
  - eauto.
  - intros p Hp. apply Nat.eqb_eq, HP, Hp.
Qed.

Lemma offer_used L r j t :
  network L -> In r L -> In (j,t) (row_offers r) ->
  ∃ s, In s L ∧ In (j,t) (row_uses s).
Proof.
  intros (_ & H & _) Hr Hp.
  assert (In (j,t) (all_offers L)) by (apply in_flat_map; eauto).
  apply (in_permuted _ _ _ H) in H0. now apply in_flat_map in H0.
Qed.

Lemma lock_pick n k o R P t c :
  row_typed (Row n (Lock k o) R P) -> In (n, LockT c t) P ->
  ∃ cs,
    stored_value o R t ∧ lock_caps k o (c :: cs) ∧
    P ≡ₚ lock_ports n t (c :: cs).
Proof.
  intros (a & caps & Hval & Hcaps & Hp) Hin. simpl in Hp.
  apply (in_permuted _ _ _ Hp) in Hin. apply in_map_iff in Hin as (d & He & Hd).
  injection He as Hdt Hd1. subst d a.
  apply in_split in Hd as (L & M & ->).
  assert (Hmove : L ++ c :: M ≡ₚ c :: L ++ M) by (symmetry; apply Permutation_middle).
  exists (L ++ M). split; [exact Hval|]. split.
  - destruct Hcaps as (Hlen & Howner & Hopen). unfold lock_caps.
    rewrite <- (Permutation_length Hmove), <- !(count_where_perm _ _ _ Hmove). auto.
  - etransitivity; [exact Hp|]. now apply Permutation_map.
Qed.

Lemma lock_split_update c a b k o cs :
  lockcap_split c a b ->
  lock_caps k o (c :: cs) -> lock_caps (S k) o (a :: b :: cs).
Proof.
  destruct c as [co cl], a as [ao al], b as [bo bl].
  intros [Ho Hl]. simpl in *. inversion Ho; inversion Hl; subst;
    unfold lock_caps, count_where in *; simpl in *; intuition lia.
Qed.

Lemma lock_open_update c k v cs :
  lock_caps k (Some v) ((c, Closed) :: cs) ->
  lock_caps k None ((c, Opened) :: cs).
Proof. destruct c; unfold lock_caps, count_where; simpl; intuition lia. Qed.

Lemma lock_close_update c k v cs :
  lock_caps k None ((c, Opened) :: cs) ->
  lock_caps k (Some v) ((c, Closed) :: cs).
Proof. destruct c; unfold lock_caps, count_where; simpl; intuition lia. Qed.

Lemma lock_drop_update k o cs :
  lock_caps (S k) o ((Client, Closed) :: cs) -> lock_caps k o cs.
Proof. unfold lock_caps, count_where; simpl; intuition lia. Qed.

Lemma lock_last v cs :
  lock_caps 0 (Some v) ((Owner, Closed) :: cs) -> cs = [].
Proof. intros (H & _). destruct cs; simpl in *; auto; lia. Qed.

Lemma size_pos (X : gset nat) : X ≠ ∅ -> 0 < size X.
Proof.
  intros H. destruct (size X) eqn:He; [|lia].
  exfalso. apply H, leibniz_equiv, size_empty_inv. exact He.
Qed.

Lemma edge_star_forest X n L :
  NoDup L -> ¬ In n L ->
  forest_on X (map (λ i, (i,n)) L).
Proof.
  intros Hnd Hno Y HY Hnon. unfold edge_count. rewrite count_where_map.
  destruct (decide (n ∈ Y)) as [Hin|Hout].
  - unfold count_where.
    set (F := List.filter (inside Y ∘ (λ i, (i,n))) L).
    assert (Hsub : list_to_set F ⊆ (Y ∖ {[n]} : gset nat)).
    { intros i. rewrite elem_of_list_to_set, list_elem_of_In.
      unfold F. rewrite filter_In. unfold compose, inside; simpl. rewrite bool_decide_eq_true.
      intros [Hi [Hiy _]]. assert (i ≠ n) by (intros ->; contradiction). set_solver. }
    assert (HndF : NoDup F) by (unfold F; apply NoDup_ListNoDup, List.NoDup_filter, NoDup_ListNoDup; exact Hnd).
    assert (size (list_to_set F : gset nat) = length F).
    { apply size_list_to_set. exact HndF. }
    pose proof (subseteq_size _ _ Hsub).
    pose proof (size_cut Y ({[n]} : gset nat)) as Hcut.
    assert (Y ∩ {[n]} = {[n]}) as He by set_solver.
    rewrite He in Hcut. rewrite (size_singleton (C:=gset nat)) in Hcut. lia.
  - rewrite count_where_zero.
    + apply size_pos. assumption.
    + intros i _. unfold compose, inside; simpl. apply bool_decide_eq_false. tauto.
Qed.

Lemma empty_forest X : forest_on X [].
Proof. intros Y _ H. change (0 < size Y). apply size_pos. exact H. Qed.

Lemma waiting_under k e j : ctx1 k -> expr_waiting e j -> expr_waiting (k e) j.
Proof.
  intros Hk (K & h & HK & -> & Hh).
  exists (k ∘ K), h. repeat split; eauto using Ctx_comp.
Qed.

Definition head_waits e : list nat :=
  match e with
  | App (Val (BarrierV n)) (Val _)
  | ForkLock (Val (LockV n)) (Val _)
  | Acquire (Val (LockV n))
  | Release (Val (LockV n)) (Val _)
  | Wait (Val (LockV n))
  | Drop (Val (LockV n)) => [n]
  | _ => []
  end.

Lemma head_waits_spec e n : In n (head_waits e) ↔ expr_head_waiting e n.
Proof.
  split; [|destruct 1; simpl; auto].
  destruct e; cbn [head_waits];
    repeat match goal with |- context [match ?x with _ => _ end] => is_var x; destruct x end;
    simpl; try contradiction; intros [<-|[]]; constructor.
Qed.

Fixpoint waiting_indices e : list nat :=
  head_waits e ++
  match e with
  | App a b | Pair a b | ForkLock a b | Release a b =>
      waiting_indices a ++ waiting_indices b
  | LetPair a _ | Sum _ a | MatchSum _ a _
  | ForkBarrier a | NewLock a | Acquire a | Wait a | Drop a => waiting_indices a
  | _ => []
  end.

Lemma waiting_indices_spec e n : In n (waiting_indices e) ↔ expr_waiting e n.
Proof.
  split.
  - revert e. fix IH 1. intros e.
    destruct e; cbn [waiting_indices]; rewrite in_app_iff, head_waits_spec;
      intros [H|H]; try contradiction.
    all: try solve [match goal with Hh : expr_head_waiting ?e _ |- _ =>
      exists id, e; split; [constructor|]; split; [reflexivity|exact Hh] end].
    all: try rewrite in_app_iff in H; try destruct H as [H|H];
      lazymatch goal with
      | Hm : In _ (waiting_indices ?a) |- expr_waiting ?e _ =>
          let ka := eval pattern a at 1 in e in
          lazymatch ka with ?k ?hole =>
            eapply (waiting_under k hole); [constructor|apply IH; exact Hm]
          end
      end.
  - intros (k & h & Hk & -> & Hh). induction Hk.
    + cbn [id]. destruct h; cbn [waiting_indices]; apply in_app_iff; left;
        now apply head_waits_spec.
    + destruct H; cbn [compose waiting_indices]; apply in_app_iff; right;
        try (apply in_app_iff; tauto); assumption.
Qed.

Lemma expr_waiting_dec e n : Decision (expr_waiting e n).
Proof.
  destruct (in_dec Nat.eq_dec n (waiting_indices e)) as [H|H].
  - left. now apply waiting_indices_spec.
  - right. intros H'. apply H. now apply waiting_indices_spec.
Defined.

Definition ready_head e :=
  (∃ e', pure_step e e') ∨ (∃ v, e = ForkBarrier (Val v)) ∨
  (∃ v, e = NewLock (Val v)) ∨ (∃ n, expr_head_waiting e n).

Definition expression_progress e :=
  (∃ v, e = Val v) ∨ ∃ k h, ctx k ∧ e = k h ∧ ready_head h.

Lemma progress_under k e :
  ctx1 k -> (∃ K h, ctx K ∧ e = K h ∧ ready_head h) -> expression_progress (k e).
Proof.
  intros Hk (K & h & HK & -> & Hh). right. exists (k ∘ K), h.
  repeat split; eauto using Ctx_comp.
Qed.

Local Ltac is_head :=
  lazymatch goal with |- expression_progress ?e =>
    right; exists id, e; split; [constructor|]; split; [reflexivity|];
    unfold ready_head; eauto 7 using pure_step, expr_head_waiting
  end.

Local Ltac use_progress IH :=
  lazymatch type of IH with _ -> expression_progress ?arg =>
    lazymatch goal with |- expression_progress ?e =>
      let appk := eval pattern arg at 1 in e in
      lazymatch appk with ?k ?hole =>
        let Hv := fresh "Hv" in let Hnv := fresh "Hnv" in
        destruct (IH eq_refl) as [(? & Hv)|Hnv];
        [rewrite Hv in *|apply (progress_under k hole); [constructor|exact Hnv]]
      end
    end
  end.

Lemma runtime_sum_form G R n (ts : fin n -> type) v :
  runtime_typed G R (Val v) (SumT n ts) -> ∃ (i : fin n) a, v = SumV i a.
Proof.
  intros HT. remember (Val v) as e eqn:He in HT.
  remember (SumT n ts) as t eqn:Ht in HT.
  destruct HT; try discriminate.
  injection Ht as Hn Hts. subst n0.
  injection He as <-. eauto.
Qed.

Lemma runtime_progress G R e t :
  runtime_typed G R e t -> G = ∅ -> expression_progress e.
Proof.
  induction 1; intros ->.
  all: repeat match goal with
  | Hs : env_split ∅ _ _ |- _ =>
      apply split_empty in Hs; destruct Hs as [-> ->]
  end.
  all: try solve [left; eauto].
  - destruct H as (D & HD & _). unfold env in HD.
    assert ((∅ : gmap String.string type) !! x = Some t) by
      (rewrite HD; apply env_lookup_insert_eq).
    rewrite env_lookup_empty in H. discriminate.
  - is_head.
  - use_progress IHruntime_typed1. use_progress IHruntime_typed2.
    match goal with Ht : runtime_typed _ _ (Val _) (FunT _ _ _) |- _ =>
      invert_runtime Ht
    end; is_head.
  - is_head.
  - use_progress IHruntime_typed1. use_progress IHruntime_typed2. is_head.
  - use_progress IHruntime_typed1.
    match goal with Ht : runtime_typed _ _ (Val _) (PairT _ _) |- _ => invert_runtime Ht end.
    is_head.
  - use_progress IHruntime_typed. is_head.
  - use_progress IHruntime_typed.
    match goal with Ht : runtime_typed _ _ (Val _) (SumT _ _) |- _ =>
      destruct (runtime_sum_form _ _ _ _ _ Ht) as (? & ? & ->)
    end; is_head.
  - use_progress IHruntime_typed. is_head.
  - use_progress IHruntime_typed. is_head.
  - use_progress IHruntime_typed1. use_progress IHruntime_typed2.
    match goal with Ht : runtime_typed _ _ (Val _) (LockT _ _) |- _ =>
      invert_runtime Ht
    end; is_head.
  - use_progress IHruntime_typed. invert_runtime H. is_head.
  - use_progress IHruntime_typed1. use_progress IHruntime_typed2.
    match goal with Ht : runtime_typed _ _ (Val _) (LockT _ _) |- _ =>
      invert_runtime Ht
    end; is_head.
  - use_progress IHruntime_typed. invert_runtime H. is_head.
  - use_progress IHruntime_typed. invert_runtime H. is_head.
Qed.

Local Definition cfg_insert_union_l := insert_union_l (M:=gmap nat) (A:=obj).
Local Definition cfg_disjoint_spec := map_disjoint_spec (M:=gmap nat) (A:=obj).
Local Definition cfg_empty_union := map_empty_union (M:=gmap nat) (A:=obj).

Lemma disjoint_missing (A F : cfg) :
  A ##ₘ F -> ∀ i x, A !! i = Some x -> F !! i = None.
Proof.
  intros Hd i x Hi. destruct (F !! i) as [y|] eqn:Hy; [|reflexivity].
  exfalso. eapply cfg_disjoint_spec; eauto.
Qed.

Local Instance network_respects_permutation : Proper (Permutation ==> iff) network.
Proof. intros ? ? H. split; eauto using network_perm, Permutation_sym. Qed.

Local Instance rows_respect_permutation ρ : Proper (Permutation ==> iff) (row_rep ρ).
Proof. intros ? ? H. split; eauto using rows_perm, Permutation_sym. Qed.

Definition well_network ρ := ∃ L, row_rep ρ L ∧ network L.

Local Ltac cfg_compute :=
  repeat first [rewrite cfg_lookup_insert_ne by congruence |
    rewrite cfg_lookup_insert_eq | rewrite cfg_lookup_empty].

Local Ltac cfg_fresh :=
  unfold cfg in *; cfg_compute;
  first [reflexivity |
    match goal with
    | Hf : ∀ i x, _ !! i = Some x -> _ !! i = None |- _ =>
        eapply Hf; cfg_compute; reflexivity
    end].

Local Ltac take_rows Htake Hwhole Hnet :=
  lazymatch type of Htake with
  | row_rep (<[?i:=?x]> ?F) ?L =>
      let HR := fresh "HR" in let HP := fresh "HP" in
      let R := fresh "R" in let P := fresh "P" in let LF := fresh "LF" in
      let Hfresh := fresh in
      assert (Hfresh : F !! i = None) by cfg_fresh;
      destruct (rows_take _ _ _ _ Htake Hfresh) as (R & P & LF & HP & HR);
      clear Htake Hfresh; rewrite HP in Hwhole, Hnet; clear HP;
      take_rows HR Hwhole Hnet
  | _ => idtac
  end.

Local Ltac unfold_rows :=
  cbn [all_uses all_offers flat_map row_edges row_id row_obj row_uses row_offers app].

Local Ltac rewrite_ports :=
  repeat match goal with H : ?X ≡ₚ _ |- _ =>
    is_var X; progress rewrite H
  end.

Local Ltac solve_ports :=
  unfold_rows; unfold out_edges; rewrite_ports;
  cbn [lock_ports map]; rewrite ?map_app; cbn [map fst snd app]; ports_perm.

Lemma out_edges_targets i R : map snd (out_edges i R) = map fst R.
Proof. unfold out_edges. rewrite map_map. reflexivity. Qed.

Local Ltac solve_boundary :=
  rewrite ?map_app, ?out_edges_targets, ?map_app; ports_perm.

Local Ltac solve_core :=
  intros u w Hu; simpl in Hu; repeat destruct Hu as [Hu|Hu]; try contradiction;
  inversion Hu; subst; unfold row_names; rewrite elem_of_list_to_set, list_elem_of_In;
  simpl; tauto.

Local Ltac solve_star n leaves :=
  lazymatch goal with |- forest_on ?X _ =>
    change (forest_on X (map (λ i, (i,n)) leaves))
  end;
  apply edge_star_forest; [apply NoDup_ListNoDup; repeat (first [apply List.NoDup_nil | apply List.NoDup_cons]); simpl; intuition congruence |
    simpl; intuition congruence].

Local Ltac assemble_rows :=
  repeat (apply rows_insert; [|cfg_fresh]); assumption.

Local Ltac rows_typed :=
  repeat match goal with H : Forall row_typed (_ :: _) |- _ =>
    let HH := fresh "Hrow" in let HT := fresh "Hrows" in
    inversion H as [|? ? HH HT]; clear H; subst
  end.

Local Ltac unfold_thread_rows :=
  repeat match goal with H : row_typed (Row _ (Thread _) _ _) |- _ =>
    cbn [row_typed row_id row_obj row_uses row_offers] in H; destruct H as [H ->]
  end.

Local Ltac invert_handles :=
  repeat match goal with
  | Hv : runtime_typed _ _ (Val (LockV _)) _ |- _ => invert_runtime Hv
  | Hv : runtime_typed _ _ (Val (BarrierV _)) _ |- _ => invert_runtime Hv
  end.

Lemma closed_app R S e f a b l :
  runtime_typed ∅ R e (FunT l a b) -> runtime_typed ∅ S f a ->
  runtime_typed ∅ (R ++ S) (App e f) b.
Proof. intros. eapply RT_app; eauto with rt. Qed.

Lemma closed_lock n c t : runtime_typed ∅ [(n,LockT c t)] (Val (LockV n)) (LockT c t).
Proof. apply RT_lockv; [apply empty_env_unr|reflexivity]. Qed.

Lemma closed_barrier n a b :
  runtime_typed ∅ [(n, FunT Lin a b)] (Val (BarrierV n)) (FunT Lin a b).
Proof. apply RT_barrierv; [apply empty_env_unr|reflexivity]. Qed.

Lemma barrier_exchange (n : nat) a b c d a' b' Q :
  [(n, FunT Lin a' b'); (n, FunT Lin b' a')] ≡ₚ
  [(n, FunT Lin a b); (n, FunT Lin c d)] ++ Q ->
  Q = [] ∧ a = d ∧ b = c.
Proof.
  intros HP. pose proof (Permutation_length HP) as Hlen.
  simpl in Hlen. destruct Q as [|? Q]; [|simpl in Hlen; lia].
  simpl in HP. split; [reflexivity|].
  assert (In (n,FunT Lin a b) [(n, FunT Lin a' b'); (n, FunT Lin b' a')])
    by (eapply Permutation_in; [symmetry; exact HP|simpl; auto]).
  destruct H as [He|[He|[]]]; inversion He; subst.
  - apply Permutation_cons_inv in HP. apply Permutation_length_1 in HP. inversion HP; auto.
  - apply Permutation_sym in HP.
    assert (HQ : [(n, FunT Lin a b); (n, FunT Lin c d)] ≡ₚ
      [(n, FunT Lin a b); (n, FunT Lin b a)]) by
      (etransitivity; [exact HP|apply perm_swap]).
    apply Permutation_cons_inv in HQ. apply Permutation_length_1 in HQ. inversion HQ; auto.
Qed.

Local Notation thread_row i e R := (Row i (Thread e) R []).

Local Ltac collect_context k head T S C HT HP HC :=
  let E := constr:(k head) in
  match goal with
  | Hk : ctx ?k0, Ht : runtime_typed _ ?R ?ee UnitT |- _ =>
      constr_eq k k0; constr_eq E ee;
      destruct (context_type k Hk head R UnitT Ht) as (T & S & C & HT & HP & HC);
      clear Ht
  end.

Local Ltac front_rows L F :=
  lazymatch L with
  | F => constr:([] : list object_row)
  | ?r :: ?L' =>
      let A := front_rows L' F in constr:(r :: A)
  end.

Local Ltac finish_reduction B I J U V :=
  match goal with
  | HF : row_rep ?frame ?F, Hwhole : row_rep _ ?L, Hnet : network ?L |- well_network ?rho =>
      let A := front_rows L F in
      let Hnew := fresh "Hnew" in
      assert (Hnew : row_rep rho (B ++ F)) by (cbn [app]; assemble_rows);
      exists (B ++ F); split; [exact Hnew|];
      eapply (network_rewire A B F I J U V);
      [exact Hnet|exact (proj1 Hwhole)|exact (proj1 Hnew)|discriminate| |
        try solve_ports|try solve_ports|try solve_ports|try solve_core|try solve_core|try solve_boundary|reflexivity|]
  end.

Local Ltac pick_lock n c t :=
  lazymatch goal with
  | Hlock : row_typed (Row n (Lock ?k ?o) ?R ?P),
    Hnet : network ?L, Hwhole : row_rep _ ?L |- _ =>
      let Hin := fresh "Hin" in
      assert (Hin : In (n, LockT c t) (all_uses L)) by
        (lazymatch goal with
         | Hp : ?S ≡ₚ [(n, LockT c t)] |- _ =>
           let HS := fresh in
           assert (HS : In (n, LockT c t) S) by
             (apply (in_permuted _ _ _ Hp); simpl; auto);
           unfold_rows;
           repeat first [rewrite in_app_iff |
             match goal with H : ?X ≡ₚ ?Y |- _ =>
               is_var X; progress setoid_rewrite (in_permuted _ _ (n,LockT c t) H)
             end];
           simpl; tauto
         end);
      let caps := fresh "caps" in let Hv := fresh "Hstored" in
      let Hcaps := fresh "Hcaps" in let Hp := fresh "Hoffer" in
      let Hmem := fresh "Hmem" in
      assert (Hmem : In (n, LockT c t) P) by
        (destruct Hnet as (Hall & Hbal & _);
         apply (in_permuted _ _ _ Hbal) in Hin;
         pose proof (offers_filter L (Row n (Lock k o) R P) Hall (proj1 Hwhole)
           ltac:(simpl; auto)) as Hfilter;
         cbn [row_id row_offers] in Hfilter;
         rewrite <- Hfilter; apply filter_In; split; [exact Hin|apply Nat.eqb_refl]);
      destruct (lock_pick n k o R P t c Hlock Hmem) as (caps & Hv & Hcaps & Hp);
      clear Hlock Hin Hmem
  end.

Lemma network_step ρ ρ' i :
  step i ρ ρ' -> well_network ρ -> well_network ρ'.
Proof.
  intros Hstep (L & Hrep & Hnet).
  destruct Hstep as [A B F id' HdA HdB Hlocal].
  pose proof (disjoint_missing _ _ HdA) as Hstart.
  pose proof (disjoint_missing _ _ HdB) as Hfinish.
  clear HdA HdB. destruct Hlocal; unfold cfg in *.
  all: unfold singletonM, map_singleton in *.
  all: repeat first [rewrite <- cfg_insert_union_l in Hrep | rewrite <- cfg_insert_union_l].
  all: rewrite ?cfg_empty_union in Hrep |- *.
  all: pose proof Hrep as Hwhole; take_rows Hrep Hwhole Hnet.
  all: pose proof (proj1 Hnet) as Hrows; rows_typed; unfold_thread_rows.
  - destruct (context_type _ H _ _ _ Hrow) as (a & S & C & Hhead & Hperm & Hctx).
    assert (Hnew : runtime_typed ∅ (S ++ C) (k e') UnitT)
      by (apply Hctx; eapply runtime_pure; eauto).
    finish_reduction [thread_row i (k e') (S ++ C)]
      ([] : edges) ([] : edges) (out_edges i (S ++ C)) (out_edges i (S ++ C)).
    + constructor; [split; [exact Hnew|reflexivity]|constructor].
    + apply empty_forest.
  - match goal with HT : runtime_typed _ _ (Val UnitV) _ |- _ => invert_runtime HT end.
    finish_reduction ([] : list object_row) ([] : edges) ([] : edges) ([] : edges) ([] : edges).
    + constructor.
    + apply empty_forest.
  - collect_context k (ForkBarrier (Val v)) t Rs C Hhead Hperm Hctx.
    invert_runtime Hhead.
    match goal with Hv : runtime_typed _ Rs (Val v) (FunT Lin (FunT Lin ?b ?a) UnitT) |- _ =>
      rename a into A, b into B
    end.
    assert (Hparent : runtime_typed ∅ ([(n,FunT Lin A B)] ++ C)
      (k (Val (BarrierV n))) UnitT) by (apply Hctx, closed_barrier).
    assert (Hchild : runtime_typed ∅ (Rs ++ [(n,FunT Lin B A)])
      (App (Val v) (Val (BarrierV n))) UnitT) by
      (eapply closed_app; [eassumption|apply closed_barrier]).
    finish_reduction
      [thread_row i (k (Val (BarrierV n))) ([(n,FunT Lin A B)] ++ C);
       thread_row j (App (Val v) (Val (BarrierV n))) (Rs ++ [(n,FunT Lin B A)]);
       Row n Barrier [] [(n,FunT Lin A B); (n,FunT Lin B A)]]
      ([] : edges) [(i,n);(j,n)] (out_edges i (Rs ++ C))
      (out_edges i C ++ out_edges j Rs).
    + repeat constructor; simpl; eauto 6.
    + solve_star n [i;j].
  - collect_context k1 (App (Val (BarrierV n)) (Val v1)) t1 S1 C1 Hd1 Hp1 Hc1.
    collect_context k2 (App (Val (BarrierV n)) (Val v2)) t2 S2 C2 Hd2 Hp2 Hc2.
    invert_runtime Hd1. invert_runtime Hd2. invert_handles.
    match goal with Hv : runtime_typed _ ?V (Val v1) ?a |- _ => rename V into V1, a into A1 end.
    match goal with Hv : runtime_typed _ ?V (Val v2) ?a |- _ => rename V into V2, a into A2 end.
    cbn [row_typed row_id row_obj row_uses row_offers] in Hrow1.
    destruct Hrow1 as [-> (a & b & Hoffer)].
    match type of Hnet with network ?L' =>
      destruct (selected_offers L' (Row n Barrier [] P1)
        [(n,FunT Lin A1 t1);(n,FunT Lin A2 t2)]
        (V1 ++ C1 ++ V2 ++ C2 ++ all_uses LF1) Hnet (proj1 Hwhole)
        ltac:(simpl; auto) ltac:(intros p [<-|[<-|[]]]; reflexivity)
        ltac:(solve_ports)) as (Q & HQ)
    end.
    cbn [row_offers] in HQ. rewrite Hoffer in HQ.
    destruct (barrier_exchange _ _ _ _ _ _ _ _ HQ) as (-> & -> & ->).
    assert (HpBarrier : P1 ≡ₚ [(n,FunT Lin t2 A2);(n,FunT Lin A2 t2)]) by
      (etransitivity; [exact Hoffer|exact HQ]).
    clear Hoffer HQ.
    assert (HT1 : runtime_typed ∅ (V2 ++ C1) (k1 (Val v2)) UnitT) by (apply Hc1; assumption).
    assert (HT2 : runtime_typed ∅ (V1 ++ C2) (k2 (Val v1)) UnitT) by (apply Hc2; assumption).
    finish_reduction [thread_row i (k1 (Val v2)) (V2 ++ C1);
      thread_row j (k2 (Val v1)) (V1 ++ C2)]
      [(i,n);(j,n)] ([] : edges)
      (out_edges i (V1 ++ C1) ++ out_edges j (V2 ++ C2))
      (out_edges i (V2 ++ C1) ++ out_edges j (V1 ++ C2)).
    + repeat constructor; simpl; auto.
    + apply empty_forest.
  - collect_context k (NewLock (Val v)) t Rs C Hhead Hperm Hctx.
    invert_runtime Hhead.
    match goal with Hv : runtime_typed _ Rs (Val v) ?a |- _ => rename a into A end.
    assert (HT : runtime_typed ∅ ([(n,LockT (Owner,Closed) A)] ++ C)
      (k (Val (LockV n))) UnitT) by (apply Hctx, closed_lock).
    finish_reduction
      [thread_row i (k (Val (LockV n))) ([(n,LockT (Owner,Closed) A)] ++ C);
       Row n (Lock 0 (Some v)) Rs (lock_ports n A [(Owner,Closed)])]
      ([] : edges) [(i,n)] (out_edges i (Rs ++ C))
      (out_edges i C ++ out_edges n Rs).
    + constructor; [split; [exact HT|reflexivity]|].
      constructor; [|constructor].
      exists A, [(Owner,Closed)]. repeat split; eauto.
    + solve_star n [i].
  - collect_context k (ForkLock (Val (LockV n)) (Val v)) t Rs C Hhead Hperm Hctx.
    invert_runtime Hhead. invert_handles.
    match goal with
    | Hv : runtime_typed _ ?V (Val v) (FunT Lin (LockT ?c2 ?a) UnitT),
      Hs : lockcap_split ?c1 ?c2 ?c3 |- _ =>
        rename V into Vp, c1 into c_in, c2 into c_child, c3 into c_parent, a into A
    end.
    pick_lock n c_in A.
    assert (Hupd : lock_caps (S refcnt) o (c_child :: c_parent :: caps))
      by (eapply lock_split_update; eauto).
    assert (Hparent : runtime_typed ∅ ([(n,LockT c_parent A)] ++ C)
      (k (Val (LockV n))) UnitT) by (apply Hctx, closed_lock).
    assert (Hchild : runtime_typed ∅ (Vp ++ [(n,LockT c_child A)])
      (App (Val v) (Val (LockV n))) UnitT) by
      (eapply closed_app; [eassumption|apply closed_lock]).
    finish_reduction
      [thread_row i (k (Val (LockV n))) ([(n,LockT c_parent A)] ++ C);
       thread_row j (App (Val v) (Val (LockV n))) (Vp ++ [(n,LockT c_child A)]);
       Row n (Lock (S refcnt) o) R0 (lock_ports n A (c_child :: c_parent :: caps))]
      [(i,n)] [(i,n);(j,n)]
      (out_edges i (Vp ++ C) ++ out_edges n R0)
      (out_edges i C ++ out_edges j Vp ++ out_edges n R0).
    + constructor; [split; [exact Hparent|reflexivity]|].
      constructor; [split; [exact Hchild|reflexivity]|].
      constructor; [|constructor].
      exists A, (c_child :: c_parent :: caps). split; [exact Hstored|]. auto.
    + solve_star n [i;j].
  - collect_context k (Acquire (Val (LockV n))) t Rs C Hhead Hperm Hctx.
    invert_runtime Hhead. invert_handles.
    match goal with Hp : _ ≡ₚ [(n,LockT (?ow,Closed) ?a)] |- _ =>
      rename ow into own, a into A
    end.
    pick_lock n (own,Closed) A.
    assert (Hval : runtime_typed ∅ ([(n,LockT (own,Opened) A)] ++ R0)
      (Val (PairV (LockV n) v)) (PairT (LockT (own,Opened) A) A)).
    { eapply RT_pairv; [apply empty_env_split|reflexivity|apply closed_lock|exact Hstored]. }
    finish_reduction
      [thread_row i (k (Val (PairV (LockV n) v))) (([(n,LockT (own,Opened) A)] ++ R0) ++ C);
       Row n (Lock refcnt None) [] (lock_ports n A ((own,Opened) :: caps))]
      [(i,n)] [(i,n)] (out_edges i C ++ out_edges n R0) (out_edges i (R0 ++ C)).
    + constructor; [split; [apply Hctx, Hval|reflexivity]|].
      constructor; [|constructor].
      exists A, ((own,Opened) :: caps). split; [reflexivity|].
      split; [eapply lock_open_update; exact Hcaps|reflexivity].
    + solve_star n [i].
  - collect_context k (Release (Val (LockV n)) (Val v)) t Rs C Hhead Hperm Hctx.
    invert_runtime Hhead. invert_handles.
    match goal with Hp : _ ≡ₚ [(n,LockT (?ow,Opened) ?a)],
      Hv : runtime_typed _ ?V (Val v) ?a |- _ =>
      rename ow into own, a into A, V into Vp
    end.
    pick_lock n (own,Opened) A.
    change (R0 = []) in Hstored. subst R0.
    finish_reduction
      [thread_row i (k (Val (LockV n))) ([(n,LockT (own,Closed) A)] ++ C);
       Row n (Lock refcnt (Some v)) Vp (lock_ports n A ((own,Closed) :: caps))]
      [(i,n)] [(i,n)] (out_edges i (Vp ++ C)) (out_edges i C ++ out_edges n Vp).
    + constructor; [split; [apply Hctx, closed_lock|reflexivity]|].
      constructor; [|constructor].
      exists A, ((own,Closed) :: caps). split; [eassumption|].
      split; [eapply lock_close_update; exact Hcaps|reflexivity].
    + solve_star n [i].
  - collect_context k (Wait (Val (LockV n))) t Rs C Hhead Hperm Hctx.
    invert_runtime Hhead. invert_handles.
    pick_lock n (Owner,Closed) t.
    apply lock_last in Hcaps. subst caps.
    finish_reduction
      [thread_row i (k (Val v)) (R0 ++ C)]
      [(i,n)] ([] : edges) (out_edges i C ++ out_edges n R0)
      (out_edges i (R0 ++ C)).
    + constructor; [split; [apply Hctx; exact Hstored|reflexivity]|constructor].
    + apply empty_forest.
  - collect_context k (Drop (Val (LockV n))) t Rs C Hhead Hperm Hctx.
    invert_runtime Hhead. invert_handles.
    match goal with Hp : _ ≡ₚ [(n,LockT (Client,Closed) ?a)] |- _ =>
      rename a into A
    end.
    pick_lock n (Client,Closed) A.
    finish_reduction
      [thread_row i (k (Val UnitV)) ([] ++ C);
       Row n (Lock refcnt o) R0 (lock_ports n A caps)]
      [(i,n)] ([] : edges) (out_edges i C ++ out_edges n R0)
      (out_edges i C ++ out_edges n R0).
    + constructor; [split; [apply Hctx; auto with rt|reflexivity]|].
      constructor; [|constructor].
      exists A, caps. split; [exact Hstored|].
      split; [eapply lock_drop_update; exact Hcaps|reflexivity].
    + apply empty_forest.
Qed.

Lemma simple_edge_bound X E i j :
  forest_on X E -> i ∈ X -> j ∈ X ->
  edge_count ({[i]} ∪ {[j]}) E <= 1.
Proof.
  intros HF Hi Hj.
  pose proof (HF ({[i]} ∪ {[j]}) ltac:(set_solver) ltac:(set_solver)) as HB.
  assert (size ({[i]} ∪ {[j]} : gset nat) <= 2).
  { rewrite size_union_alt, (size_singleton (C:=gset nat)).
    pose proof (subseteq_size ({[j]} ∖ {[i]} : gset nat) ({[j]} : gset nat)
      ltac:(set_solver)) as HS.
    rewrite (size_singleton (C:=gset nat)) in HS. lia. }
  lia.
Qed.

Lemma network_loop_free L i :
  network L -> ¬ In (i,i) (row_edges L).
Proof.
  intros HN Hin. pose proof (network_edge_end _ _ _ HN Hin) as Hi.
  destruct HN as (_ & _ & HF).
  specialize (HF ({[i]} : gset nat) ltac:(set_solver) ltac:(set_solver)).
  rewrite (size_singleton (C:=gset nat)) in HF.
  assert (0 < edge_count ({[i]} : gset nat) (row_edges L)).
  { eapply count_where_positive; [exact Hin|].
    apply bool_decide_eq_true. simpl. set_solver. }
  lia.
Qed.

Lemma edge_count_cons_true X p E :
  inside X p = true -> edge_count X (p :: E) = S (edge_count X E).
Proof. intros H. unfold edge_count, count_where. simpl. rewrite H. reflexivity. Qed.

Lemma network_no_parallel L :
  network L -> NoDup (row_edges L).
Proof.
  intros HN. assert (HB : ∀ i j, In (i,j) (row_edges L) ->
    edge_count ({[i]} ∪ {[j]}) (row_edges L) <= 1).
  { intros i j He. pose proof (network_edge_end _ _ _ HN He) as Hj.
    apply row_edge_member in He as (r & t & Hr & Hid & Ht).
    eapply simple_edge_bound; [exact (proj2 (proj2 HN))| |exact Hj].
    apply in_row_names. eauto. }
  set (E := row_edges L) in *. clearbody E. clear HN L. revert HB.
  induction E as [|[i j] E IH]; intros HB; [constructor|].
  constructor.
  - intros Hmem. apply list_elem_of_In in Hmem.
    specialize (HB i j (or_introl eq_refl)).
    assert (inside ({[i]} ∪ {[j]}) (i,j) = true) as He.
    { apply bool_decide_eq_true. simpl. set_solver. }
    rewrite (edge_count_cons_true _ _ _ He) in HB.
    pose proof (count_where_positive (inside ({[i]} ∪ {[j]})) _ _ Hmem He).
    change (0 < edge_count ({[i]} ∪ {[j]}) E) in H. lia.
  - apply IH. intros p q Hp.
    specialize (HB p q (or_intror Hp)). change (edge_count ({[p]} ∪ {[q]}) ([(i,j)] ++ E) <= 1) in HB.
    rewrite edge_count_app in HB. lia.
Qed.

Lemma network_no_reverse L i j :
  network L -> In (i,j) (row_edges L) -> ¬ In (j,i) (row_edges L).
Proof.
  intros HN Hi Hj. destruct (decide (i = j)) as [->|Hne].
  { eapply network_loop_free; eauto. }
  pose proof (network_edge_end _ _ _ HN Hi) as Hjm.
  pose proof (network_edge_end _ _ _ HN Hj) as Him.
  pose proof (simple_edge_bound _ _ _ _ (proj2 (proj2 HN)) Him Hjm) as Hbound.
  apply in_split in Hi as (A & B & He).
  rewrite He in Hj, Hbound. apply in_app_iff in Hj.
  assert (inside ({[i]} ∪ {[j]}) (i,j) = true) as H1 by
    (apply bool_decide_eq_true; simpl; set_solver).
  assert (inside ({[i]} ∪ {[j]}) (j,i) = true) as H2 by
    (apply bool_decide_eq_true; simpl; set_solver).
  rewrite edge_count_app in Hbound.
  rewrite (edge_count_cons_true _ _ _ H1) in Hbound.
  destruct Hj as [Ha|[Heq|Hb]].
  - pose proof (count_where_positive _ _ _ Ha H2) as Hpos.
    change (0 < edge_count ({[i]} ∪ {[j]}) A) in Hpos. lia.
  - congruence.
  - pose proof (count_where_positive _ _ _ Hb H2) as Hpos.
    change (0 < edge_count ({[i]} ∪ {[j]}) B) in Hpos. lia.
Qed.

Definition labelled_uses L := flat_map (λ r, map (pair r) (row_uses r)) L.
Definition labelled_edge (p : object_row * (nat * type)) :=
  (row_id p.1, p.2.1).

Lemma labelled_uses_ports L : map snd (labelled_uses L) = all_uses L.
Proof.
  induction L as [|r L IH]; [reflexivity|].
  unfold labelled_uses, all_uses in *. simpl. rewrite map_app, IH, map_map.
  f_equal. apply map_id.
Qed.

Lemma labelled_uses_edges L : map labelled_edge (labelled_uses L) = row_edges L.
Proof.
  induction L as [|r L IH]; [reflexivity|].
  unfold labelled_uses, row_edges in *. simpl. rewrite map_app, IH, map_map. reflexivity.
Qed.

Lemma labelled_member L r p :
  In (r,p) (labelled_uses L) ↔ In r L ∧ In p (row_uses r).
Proof.
  unfold labelled_uses. rewrite in_flat_map. split.
  - intros (s & Hr & Hp). apply in_map_iff in Hp as (q & He & Hq).
    inversion He; subst. auto.
  - intros [Hr Hp]. exists r. split; [exact Hr|now apply in_map].
Qed.

Lemma nodup_images_equal {A B} (f : A -> B) L p q :
  NoDup (map f L) -> In p L -> In q L -> f p = f q -> p = q.
Proof.
  induction L as [|a L IH]; [intros _ []|].
  intros Hnd [<-|Hp] [<-|Hq] He; auto.
  all: inversion Hnd as [|? ? Hnot Hrest]; subst.
  - exfalso. apply Hnot, list_elem_of_In. rewrite He. now apply in_map.
  - exfalso. apply Hnot, list_elem_of_In. rewrite <- He. now apply in_map.
  - eauto.
Qed.

Lemma port_type_unique L r n a b :
  network L -> In r L -> In (n,a) (row_uses r) -> In (n,b) (row_uses r) -> a = b.
Proof.
  intros HN Hr Ha Hb. pose proof (network_no_parallel _ HN) as Hnd.
  rewrite <- labelled_uses_edges in Hnd.
  assert ((r,(n,a)) = (r,(n,b))) by
    (eapply nodup_images_equal; [exact Hnd|apply labelled_member; auto|
      apply labelled_member; auto|reflexivity]).
  congruence.
Qed.

Lemma map_permutation_pick {A B} (f : A -> B) L p Q :
  map f L ≡ₚ p :: Q ->
  ∃ a R, f a = p ∧ L ≡ₚ a :: R ∧ map f R ≡ₚ Q.
Proof.
  intros HP.
  assert (In p (map f L)) by (eapply Permutation_in; [symmetry; exact HP|simpl; auto]).
  apply in_map_iff in H as (a & Ha & Hin).
  apply in_split in Hin as (M & N & ->).
  exists a, (M ++ N). split; [exact Ha|]. split; [symmetry; apply Permutation_middle|].
  apply Permutation_cons_inv with (a := p).
  etransitivity; [|exact HP].
  rewrite !map_app. simpl. rewrite Ha. apply Permutation_middle.
Qed.

Local Definition cfg_lookup_insert := lookup_insert (M:=gmap nat) (A:=obj).
Local Definition cfg_lookup_difference := lookup_difference (M:=gmap nat) (A:=obj).
Local Definition cfg_not_elem_of_dom := not_elem_of_dom (M:=gmap nat) (A:=obj).

Lemma frame_local ρ A B i :
  (∀ j x, A !! j = Some x -> ρ !! j = Some x) ->
  (∀ j x, B !! j = Some x -> ρ !! j = None ∨ ∃ y, A !! j = Some y) ->
  local_step i A B -> can_step ρ i.
Proof.
  intros HA HB HS. unfold cfg in *.
  set (F := ρ ∖ A).
  assert (HdA : A ##ₘ F).
  { apply cfg_disjoint_spec. intros j x y Hx Hy.
    unfold F in Hy. rewrite cfg_lookup_difference, Hx in Hy. discriminate. }
  assert (HdB : B ##ₘ F).
  { apply cfg_disjoint_spec. intros j x y Hx Hy.
    unfold F in Hy. rewrite cfg_lookup_difference in Hy.
    destruct (HB _ _ Hx) as [H|[z H]].
    - rewrite H in Hy. destruct (A !! j); discriminate.
    - rewrite H in Hy. discriminate. }
  assert (He : A ∪ F = ρ).
  { apply map_eq. intros j. rewrite cfg_lookup_union. unfold F.
    rewrite cfg_lookup_difference. destruct (A !! j) as [x|] eqn:Hx.
    - rewrite union_Some_l. symmetry. auto.
    - apply (left_id None union). }
  exists (B ∪ F). rewrite <- He at 1. econstructor; eauto.
Qed.

Lemma fresh_in_cfg (ρ : cfg) (D : gset nat) :
  ∃ n, ρ !! n = None ∧ n ∉ D.
Proof.
  set (S := dom ρ ∪ D).
  exists (fresh S). pose proof (is_fresh S) as H.
  unfold S in H. split.
  - apply cfg_not_elem_of_dom. set_solver.
  - set_solver.
Qed.

Local Ltac fragment_lookups :=
  let Hz := fresh "Hz" in let w := fresh "w" in let x := fresh "x" in
  intros w x Hz; unfold cfg in *; unfold singletonM, map_singleton in *;
  repeat rewrite cfg_lookup_insert in Hz;
  repeat match type of Hz with
    | context [decide ?P] => destruct (decide P); cbn in Hz
  end;
  try rewrite cfg_lookup_empty in Hz; try discriminate;
  inversion Hz; subst;
  first [congruence | left; congruence | right; eexists; cfg_compute; reflexivity].

Local Ltac can_step_by h :=
  refine (frame_local _ _ _ _ _ _ h); fragment_lookups.

Inductive typed_head_wait (n : nat) : expr -> type -> Prop :=
| TH_barrier v a b :
    typed_head_wait n (App (Val (BarrierV n)) (Val v)) (FunT Lin a b)
| TH_fork v c t :
    typed_head_wait n (ForkLock (Val (LockV n)) (Val v)) (LockT c t)
| TH_acquire c t :
    typed_head_wait n (Acquire (Val (LockV n))) (LockT (c,Closed) t)
| TH_release v c t :
    typed_head_wait n (Release (Val (LockV n)) (Val v)) (LockT (c,Opened) t)
| TH_wait t :
    typed_head_wait n (Wait (Val (LockV n))) (LockT (Owner,Closed) t)
| TH_drop t :
    typed_head_wait n (Drop (Val (LockV n))) (LockT (Client,Closed) t).

Lemma runtime_wait_head e n R t :
  runtime_typed ∅ R e t -> expr_waiting e n ->
  ∃ k h a, ctx k ∧ e = k h ∧ typed_head_wait n h a ∧ In (n,a) R.
Proof.
  intros HT (k & h & Hk & -> & Hh).
  destruct (context_type _ Hk _ _ _ HT) as (u & S & C & Hd & HP & HC).
  clear HT HC. destruct Hh; invert_runtime Hd; invert_handles.
  all: match goal with Hp : ?X ≡ₚ [(?n,?a)] |- _ =>
    eexists k, _, a; split; [exact Hk|]; split; [reflexivity|];
    split; [constructor|];
    repeat first [rewrite in_app_iff |
       match goal with H : ?Y ≡ₚ _ |- _ =>
         is_var Y; progress setoid_rewrite (in_permuted _ _ (n,a) H)
       end]; simpl; tauto
  end.
Qed.

Lemma row_reference r j :
  row_typed r -> j ∈ obj_refs (row_obj r) ↔ has_port j (row_uses r).
Proof.
  destruct r as [i x R P], x; cbn [row_typed row_id row_obj row_uses row_offers obj_refs].
  - intros [Ht _]. eapply runtime_refs; exact Ht.
  - intros [-> _]. unfold has_port. simpl. set_solver.
  - intros (t & cs & Hval & Hcaps & Hp). destruct o as [v|].
    + exact (runtime_refs _ _ _ _ Hval j).
    + change (R = []) in Hval. subst R. unfold has_port. simpl. set_solver.
Qed.

Lemma port_or_head ρ L n r t :
  row_rep ρ L -> network L -> In r L -> In (n,t) (row_uses r) ->
  waiting ρ n (row_id r) ∨
    ∃ k h, ctx k ∧ ρ !! row_id r = Some (Thread (k h)) ∧ typed_head_wait n h t.
Proof.
  intros HR HN Hr Hp.
  pose proof (row_rep_member _ _ _ HR Hr) as Hlookup.
  assert (Ht : row_typed r) by (eapply List.Forall_forall; [exact (proj1 HN)|exact Hr]).
  assert (Hrefs : n ∈ obj_refs (row_obj r)) by (apply row_reference; eauto; exists t; exact Hp).
  destruct (row_obj r) as [e| |k o] eqn:Ho.
  - destruct (expr_waiting_dec e n) as [Hw|Hw].
    + assert (HE : runtime_typed ∅ (row_uses r) e UnitT).
      { unfold row_typed in Ht. rewrite Ho in Ht. exact (proj1 Ht). }
      destruct (runtime_wait_head _ _ _ _ HE Hw) as (K & h & a & Hk & -> & Hh & Ha).
      assert (a = t) by (eapply port_type_unique; eauto). subst a.
      right. exists K, h. auto.
    + left. right. exists (Thread e). repeat split; eauto. intros e' He'. injection He' as <-. exact Hw.
  - left. right. exists Barrier. repeat split; eauto. discriminate.
  - left. right. exists (Lock k o). repeat split; eauto. discriminate.
Qed.

Lemma in_edge_from_port L r n t :
  In r L -> In (n,t) (row_uses r) -> In (row_id r,n) (row_edges L).
Proof. intros Hr Hp. apply row_edge_member. eauto. Qed.

Lemma two_offers_used L r p q :
  network L -> In r L -> row_offers r ≡ₚ [p;q] ->
  ∃ s t, In s L ∧ In t L ∧ In p (row_uses s) ∧ In q (row_uses t) ∧
    (p.1 = q.1 -> row_id s ≠ row_id t).
Proof.
  intros HN Hr Hp.
  assert (∃ Q, all_offers L ≡ₚ p :: q :: Q) as [Q Hoffer].
  { apply in_split in Hr as (A & B & ->).
    exists (all_offers (A ++ B)).
    unfold all_offers. rewrite !flat_map_app. simpl.
    transitivity (row_offers r ++ flat_map row_offers A ++ flat_map row_offers B);
      [ports_perm|].
    rewrite Hp. reflexivity. }
  assert (map snd (labelled_uses L) ≡ₚ p :: q :: Q) as Huse.
  { rewrite labelled_uses_ports, (proj1 (proj2 HN)). exact Hoffer. }
  destruct (map_permutation_pick snd _ _ _ Huse) as ([s sp] & ls1 & Hsp & HS & HpS).
  simpl in Hsp; subst sp.
  destruct (map_permutation_pick snd _ _ _ HpS) as ([t tq] & T & Htq & HT & HqT).
  simpl in Htq; subst tq.
  assert (labelled_uses L ≡ₚ (s,p) :: (t,q) :: T) as Hboth
    by (etransitivity; [exact HS|now apply perm_skip]).
  assert (In (s,p) (labelled_uses L)) as Hs by (apply (in_permuted _ _ _ Hboth); simpl; auto).
  assert (In (t,q) (labelled_uses L)) as Ht by (apply (in_permuted _ _ _ Hboth); simpl; auto).
  apply labelled_member in Hs as [Hs Hps].
  apply labelled_member in Ht as [Ht Hqt].
  exists s, t. repeat split; try assumption.
  intros Hkeys Hids.
  pose proof (network_no_parallel _ HN) as Hnd.
  rewrite <- labelled_uses_edges in Hnd.
  assert (NoDup (map labelled_edge ((s,p) :: (t,q) :: T))) as Hnd'
    by (apply NoDup_ListNoDup; eapply Permutation_NoDup with
          (l:=map labelled_edge (labelled_uses L));
        [apply Permutation_map; exact Hboth|apply NoDup_ListNoDup; exact Hnd]).
  inversion Hnd' as [|? ? Hnot _].
  apply Hnot, list_elem_of_In. left.
  unfold labelled_edge; simpl. congruence.
Qed.

Lemma thread_value_form R v :
  runtime_typed ∅ R (Val v) UnitT -> v = UnitV.
Proof. intros H. inversion H; reflexivity. Qed.

Lemma thread_row_progress ρ L i e R P :
  row_rep ρ L -> network L -> In (Row i (Thread e) R P) L ->
  row_typed (Row i (Thread e) R P) ->
  can_step ρ i ∨ ∃ j, j ∈ row_names L ∧ waiting ρ i j.
Proof.
  intros HR HN Hi [Ht _].
  pose proof (row_rep_member _ _ _ HR Hi) as Hl. cbn [row_id row_obj] in Hl.
  destruct (runtime_progress _ _ _ _ Ht eq_refl) as [(v & ->)|(K & h & HK & -> & HH)].
  - apply thread_value_form in Ht as ->. left. can_step_by (Exit_step i).
  - destruct HH as [(h' & Hh)|[(v & ->)|[(v & ->)|(n & Hh)]]].
    + left. can_step_by (Pure_step i K h h' HK Hh).
    + left.
      destruct (fresh_in_cfg ρ ({[i]} : gset nat)) as (j & Hj & Hji).
      destruct (fresh_in_cfg ρ ({[i]} ∪ {[j]} : gset nat)) as (n & Hn & Hnij).
      assert (i ≠ j) by set_solver. assert (i ≠ n) by set_solver. assert (j ≠ n) by set_solver.
      can_step_by (Fork_step i j n K v ltac:(assumption) ltac:(assumption) ltac:(assumption) HK).
    + left.
      destruct (fresh_in_cfg ρ ({[i]} : gset nat)) as (n & Hn & Hni).
      assert (i ≠ n) by set_solver.
      can_step_by (NewLock_step v K n i ltac:(assumption) HK).
    + assert (Hw : expr_waiting (K h) n) by (exists K, h; auto).
      destruct (runtime_wait_head _ _ _ _ Ht Hw) as (K' & h' & t & _ & _ & _ & Hp).
      right. exists n. split.
      * eapply network_edge_end; [exact HN|].
        exact (in_edge_from_port _ _ _ _ Hi Hp).
      * left. exists (K h). auto.
Qed.

Lemma barrier_row_progress ρ L n R P :
  row_rep ρ L -> network L -> In (Row n Barrier R P) L ->
  row_typed (Row n Barrier R P) ->
  can_step ρ n ∨ ∃ j, j ∈ row_names L ∧ waiting ρ n j.
Proof.
  intros HR HN Hn (_ & a & b & HP).
  cbn [row_id row_offers] in HP.
  destruct (two_offers_used L _ _ _ HN Hn HP) as (r & s & Hr & Hs & Hpr & Hps & Hne).
  pose proof (row_rep_member _ _ _ HR Hn) as Hbar. cbn [row_id row_obj] in Hbar.
  specialize (Hne eq_refl).
  assert (Hrname : row_id r ∈ row_names L) by (apply in_row_names; eauto).
  assert (Hsname : row_id s ∈ row_names L) by (apply in_row_names; eauto).
  destruct (port_or_head _ _ _ _ _ HR HN Hr Hpr) as [Hw|(K & h & HK & He & Hth)].
  { right. eauto. }
  destruct (port_or_head _ _ _ _ _ HR HN Hs Hps) as [Hw|(K' & h' & HK' & He' & Hth')].
  { right. eauto. }
  assert (Hrn : row_id r ≠ n).
  { intros H. pose proof (in_edge_from_port _ _ _ _ Hr Hpr) as Hin.
    rewrite H in Hin. eapply network_loop_free; eauto. }
  assert (Hsn : row_id s ≠ n).
  { intros H. pose proof (in_edge_from_port _ _ _ _ Hs Hps) as Hin.
    rewrite H in Hin. eapply network_loop_free; eauto. }
  inversion Hth; inversion Hth'; subst. left.
  can_step_by (Sync_step (row_id r) (row_id s) n K K' v v0 Hne Hrn Hsn HK HK').
Qed.

Lemma count_where_witness {A} (p : A -> bool) L :
  0 < count_where p L -> ∃ a, In a L ∧ p a = true.
Proof.
  unfold count_where. destruct (List.filter p L) as [|a l] eqn:H; simpl; [lia|].
  intros _. exists a. apply filter_In. rewrite H. now left.
Qed.

Lemma count_where_complement {A} (p : A -> bool) L :
  count_where p L + count_where (λ a, negb (p a)) L = length L.
Proof.
  induction L; unfold count_where in *; simpl; [reflexivity|].
  destruct (p a); simpl; lia.
Qed.

Inductive enabling_cap : nat -> option val -> lockcap -> Prop :=
| Enable_open k c : enabling_cap k None (c,Opened)
| Enable_last v : enabling_cap 0 (Some v) (Owner,Closed)
| Enable_client k v : enabling_cap (S k) (Some v) (Client,Closed).

Lemma lock_choose_cap k o cs :
  lock_caps k o cs -> ∃ c, In c cs ∧ enabling_cap k o c.
Proof.
  intros (Hlen & Howner & Hopen).
  destruct o as [v|].
  - assert (HC : ∀ c, In c cs -> c.2 = Closed).
    { intros [ow st] Hin. destruct st; [|reflexivity].
      pose proof (count_where_positive open_mark _ _ Hin eq_refl).
      simpl in Hopen. lia. }
    destruct k as [|k].
    + assert (0 < count_where owner_mark cs) by lia.
      apply count_where_witness in H as ([ow st] & Hin & Hmark).
      destruct ow; [|discriminate]. specialize (HC _ Hin). simpl in HC. subst st.
      exists (Owner,Closed). split; [assumption|constructor].
    + pose proof (count_where_complement owner_mark cs).
      assert (0 < count_where (λ a, negb (owner_mark a)) cs) by lia.
      apply count_where_witness in H0 as ([ow st] & Hin & Hmark).
      destruct ow; [discriminate|]. specialize (HC _ Hin). simpl in HC. subst st.
      exists (Client,Closed). split; [assumption|constructor].
  - assert (0 < count_where open_mark cs) by (simpl in Hopen; lia).
    apply count_where_witness in H as ([ow st] & Hin & Hmark).
    destruct st; [|discriminate]. exists (ow,Opened). split; [assumption|constructor].
Qed.

Lemma lock_action_step ρ n i k o c t K h :
  enabling_cap k o c -> typed_head_wait n h (LockT c t) ->
  ρ !! n = Some (Lock k o) -> ρ !! i = Some (Thread (K h)) ->
  i ≠ n -> ctx K -> can_step ρ n.
Proof.
  intros Hcan Hh Hl Ht Hin HK.
  destruct Hcan; inversion Hh; subst.
  all: match goal with
  | Hl : ?rho !! ?n = Some (Lock ?k ?o),
    Ht : ?rho !! ?i = Some (Thread (?K ?head)),
    Hin : ?i ≠ ?n, HK : ctx ?K |- _ =>
      lazymatch head with
      | ForkLock (Val (LockV n)) (Val ?v) =>
          let j := fresh "j" in let Hj := fresh in let Hjne := fresh in
          destruct (fresh_in_cfg rho ({[i]} ∪ {[n]} : gset nat)) as (j & Hj & Hjne);
          assert (i ≠ j) by set_solver; assert (j ≠ n) by set_solver;
          can_step_by (ForkLock_step v o K i j n k ltac:(assumption) Hin ltac:(assumption) HK)
      | Acquire (Val (LockV n)) =>
          lazymatch o with Some ?v => can_step_by (Acquire_step v K i n k Hin HK) end
      | Release (Val (LockV n)) (Val ?v) =>
          can_step_by (Release_step v K i n k Hin HK)
      | Wait (Val (LockV n)) =>
          lazymatch o with Some ?v => can_step_by (Wait_step v K i n Hin HK) end
      | Drop (Val (LockV n)) =>
          lazymatch k with S ?k' => can_step_by (Drop_step o K i n k' Hin HK) end
      end
  end.
Qed.

Lemma lock_row_progress ρ L n k o R P :
  row_rep ρ L -> network L -> In (Row n (Lock k o) R P) L ->
  row_typed (Row n (Lock k o) R P) ->
  can_step ρ n ∨ ∃ j, j ∈ row_names L ∧ waiting ρ n j.
Proof.
  intros HR HN Hn (t & cs & _ & HC & HP).
  cbn [row_id row_offers] in HP.
  destruct (lock_choose_cap _ _ _ HC) as (c & Hc & Hcan).
  assert (In (n,LockT c t) P) as Hmem
    by (apply (in_permuted _ _ _ HP); apply in_map_iff; exists c; auto).
  destruct (offer_used _ _ _ _ HN Hn Hmem) as (r & Hr & Hpr).
  destruct (port_or_head _ _ _ _ _ HR HN Hr Hpr) as [Hw|(K & h & HK & Hth & Hhead)].
  - right. exists (row_id r). split; [apply in_row_names; eauto|exact Hw].
  - left. eapply lock_action_step; try eassumption.
    + exact (row_rep_member _ _ _ HR Hn).
    + intros Hid. pose proof (in_edge_from_port _ _ _ _ Hr Hpr) as Hin.
      rewrite Hid in Hin. eapply network_loop_free; eauto.
Qed.

Lemma network_local_progress ρ L i :
  row_rep ρ L -> network L -> i ∈ row_names L ->
  can_step ρ i ∨ ∃ j, j ∈ row_names L ∧ waiting ρ i j.
Proof.
  intros HR HN Hi. apply in_row_names in Hi as ([j x R P] & Hmem & Hid).
  simpl in Hid. subst j.
  pose proof (proj1 HN) as HF.
  apply List.Forall_forall with (x:=Row i x R P) in HF; [|exact Hmem].
  destruct x; eauto using thread_row_progress, barrier_row_progress, lock_row_progress.
Qed.

Lemma waiting_edges ρ L i j :
  row_rep ρ L -> network L -> waiting ρ i j ->
  (In (i,j) (row_edges L) ∧ ∃ e, ρ !! i = Some (Thread e) ∧ expr_waiting e j) ∨
  (In (j,i) (row_edges L) ∧ ∀ e, ρ !! j = Some (Thread e) -> ¬ expr_waiting e i).
Proof.
  intros HR HN [[e [He Hw]]|(y & Hy & Href & Hwait)].
  - left. split; [|eauto].
    apply (proj2 HR) in He as ([a o R P] & Hin & Hid & Ho).
    simpl in Hid, Ho. subst a o.
    assert (row_typed (Row i (Thread e) R P)) as [Ht _]
      by (eapply List.Forall_forall; [exact (proj1 HN)|exact Hin]).
    destruct (runtime_wait_head _ _ _ _ Ht Hw) as (k & h & t & _ & _ & _ & Hp).
    exact (in_edge_from_port _ _ _ _ Hin Hp).
  - right. split.
    + apply (proj2 HR) in Hy as ([a o R P] & Hin & Hid & Ho).
      simpl in Hid, Ho. subst a o.
      assert (row_typed (Row j y R P)) as Ht
        by (eapply List.Forall_forall; [exact (proj1 HN)|exact Hin]).
      apply (row_reference (Row j y R P) i Ht) in Href as (t & Hm).
      exact (in_edge_from_port _ _ _ _ Hin Hm).
    + intros e He. apply Hwait. congruence.
Qed.

Lemma waiting_asymmetric ρ L i j :
  row_rep ρ L -> network L -> waiting ρ i j -> ¬ waiting ρ j i.
Proof.
  intros HR HN Hij Hji.
  destruct (waiting_edges _ _ _ _ HR HN Hij) as [(H1 & e & He & Hw)|(H1 & Hu)];
  destruct (waiting_edges _ _ _ _ HR HN Hji) as [(H2 & e' & He' & Hw')|(H2 & Hu')].
  - eapply network_no_reverse; eauto.
  - exact (Hu' _ He Hw).
  - exact (Hu _ He' Hw').
  - eapply network_no_reverse; eauto.
Qed.

Definition edge_connects i j (ed : nat * nat) := ed = (i,j) ∨ ed = (j,i).

Lemma choose_inside_or_exit (W : nat -> nat -> Prop) (P : nat -> Prop)
    (X V : gset nat) (E : edges) xs :
  (∀ i, In i xs -> i ∈ X) ->
  (∀ i, In i xs -> P i ∨ ∃ j, j ∈ V ∧ W i j) ->
  (∀ i j, W i j -> ∃ ed, In ed E ∧ edge_connects i j ed) ->
  (∃ i, In i xs ∧ (P i ∨ ∃ j, j ∈ V ∧ j ∉ X ∧ W i j)) ∨
  ∃ es, Forall2 (λ i ed, ∃ j, j ∈ X ∧ W i j ∧ In ed E ∧ edge_connects i j ed) xs es.
Proof.
  intros Hsub Hnext Hedge. induction xs as [|i xs IH].
  - right. exists []. constructor.
  - destruct (Hnext i (or_introl eq_refl)) as [HP|(j & Hj & HW)].
    { left. exists i. split; [now left|now left]. }
    destruct (decide (j ∈ X)) as [HjX|HjX].
    2: { left. exists i. split; [now left|right; eauto]. }
    destruct (IH ltac:(intros w Hw; apply Hsub; right; exact Hw)
      ltac:(intros w Hw; apply Hnext; right; exact Hw)) as [(w & Hin & Hout)|(es & Hes)].
    + left. exists w. split; [now right|exact Hout].
    + destruct (Hedge _ _ HW) as (ed & He & Hconn).
      right. exists (ed :: es). constructor; [eauto 8|exact Hes].
Qed.

Lemma Forall2_right_member {A B} (P : A -> B -> Prop) xs es e :
  Forall2 P xs es -> In e es -> ∃ i, In i xs ∧ P i e.
Proof. induction 1; intros Hm; simpl in Hm; [contradiction|].
  destruct Hm as [<-|Hm]; [exists x; auto with datatypes|].
  destruct (IHForall2 Hm) as (i & Hi & HP). exists i. auto with datatypes.
Qed.

Lemma chosen_edge_bound W X E xs es :
  (∀ i j, W i j -> ¬ W j i) ->
  (∀ i, In i xs -> i ∈ X) ->
  NoDup xs ->
  Forall2 (λ i ed, ∃ j, j ∈ X ∧ W i j ∧ In ed E ∧ edge_connects i j ed) xs es ->
  length xs <= edge_count X E.
Proof.
  intros Has Hsub Hnd Hsel.
  assert (Hlen : length xs = length es) by (clear Hsub Hnd; induction Hsel; simpl; congruence).
  assert (Hsimple : List.NoDup es).
  { clear Hlen Hsub. induction Hsel as [|i ed xs es (j & Hj & Hij & He & Hc) HS IH].
    - constructor.
    - inversion Hnd as [|? ? Hnot Hnd']; subst.
      constructor; [|eauto].
      intros Hin. destruct (Forall2_right_member _ _ _ _ HS Hin)
        as (i' & Hi' & j' & Hj' & Hij' & _ & Hc').
      assert (i ≠ i') by (intros ->; apply Hnot, list_elem_of_In; exact Hi').
      unfold edge_connects in *. destruct Hc, Hc'.
      all: assert (i = i' ∨ i = j' ∧ j = i') as Hsame
        by (first [left; congruence|right; split; congruence]).
      all: destruct Hsame as [Heq|[Hu Hv]]; [contradiction|subst; exact (Has _ _ Hij Hij')].
  }
  rewrite Hlen. unfold edge_count, count_where. apply NoDup_incl_length; [exact Hsimple|].
  intros ed Hin. apply filter_In.
  destruct (Forall2_right_member _ _ _ _ Hsel Hin) as (i & Hi & j & Hj & Hij & He & Hc).
  split; [exact He|]. apply bool_decide_eq_true. specialize (Hsub _ Hi).
  unfold edge_connects in Hc. destruct Hc as [-> | ->]; simpl; auto.
Qed.

(* If every vertex chose a waiting edge within xs, asymmetry would make
   those edges distinct and violate the forest bound on xs. *)
Lemma forest_has_exit W P V E xs :
  forest_on V E ->
  (∀ i j, W i j -> ¬ W j i) ->
  (∀ i, i ∈ V -> P i ∨ ∃ j, j ∈ V ∧ W i j) ->
  (∀ i j, W i j -> ∃ ed, In ed E ∧ edge_connects i j ed) ->
  NoDup xs -> (∀ i, In i xs -> i ∈ V) -> xs ≠ [] ->
  ∃ i, In i xs ∧ (P i ∨ ∃ j, j ∈ V ∧ ¬ In j xs ∧ W i j).
Proof.
  intros HF Has Hnext He Hnd Hsub Hnon.
  set (X := list_to_set xs : gset nat).
  assert (HX : ∀ i, i ∈ X ↔ In i xs).
  { intros i. unfold X. rewrite elem_of_list_to_set, list_elem_of_In. reflexivity. }
  assert (HXsub : X ⊆ V) by (intros i Hi; apply Hsub, HX, Hi).
  assert (HXnon : X ≠ ∅).
  { destruct xs as [|i xs]; [contradiction|].
    assert (i ∈ X) by (apply HX; now left). set_solver. }
  destruct (choose_inside_or_exit W P X V E xs ltac:(intros ? ?; now apply HX)
    ltac:(eauto) He) as [(i & Hi & HP)|(es & HS)].
  - exists i. split; [exact Hi|].
    destruct HP as [HP|(j & Hj & Hnot & HW)]; [now left|right].
    exists j. rewrite <- HX. auto.
  - exfalso. pose proof (chosen_edge_bound W X E xs es Has
      ltac:(intros ? ?; now apply HX) Hnd HS) as Hle.
    specialize (HF X HXsub HXnon).
    unfold X in HF, Hle. rewrite size_list_to_set in HF by exact Hnd. lia.
Qed.

Lemma network_reachable ρ L :
  row_rep ρ L -> network L -> ∀ i, i ∈ row_names L -> reachable ρ i.
Proof.
  intros HR HN.
  assert (Hedges : ∀ i j, waiting ρ i j ->
      ∃ ed, In ed (row_edges L) ∧ edge_connects i j ed).
  { intros i j H. destruct (waiting_edges _ _ _ _ HR HN H) as [[He _]|[He _]];
      [exists (i,j)|exists (j,i)]; unfold edge_connects; auto. }
  assert (Hprune : ∀ n xs, length xs = n -> NoDup xs ->
    (∀ i, In i xs -> i ∈ row_names L) ->
    (∀ i, i ∈ row_names L -> ¬ In i xs -> reachable ρ i) ->
    ∀ i, i ∈ row_names L -> reachable ρ i).
  { intros n. induction n using lt_wf_ind.
    intros xs Hlen Hnd Hin Hout i Hi.
    destruct xs as [|a xs].
    - apply Hout; [exact Hi|simpl; tauto].
    - destruct (forest_has_exit (waiting ρ) (can_step ρ) _ _ (a :: xs)
        (proj2 (proj2 HN)) (λ j k, waiting_asymmetric ρ L j k HR HN)
        ltac:(intros; eapply network_local_progress; eauto)
        Hedges Hnd Hin ltac:(discriminate)) as (v & Hv & Hstop).
      assert (Hreach : reachable ρ v).
      { destruct Hstop as [HC|(j & Hj & Hnot & HW)].
        - now apply Can_step_reachable.
        - eapply Waiting_reachable; [exact HW|eauto]. }
      apply in_split in Hv as (A & B & He).
      apply (H (length (A ++ B)) ltac:(rewrite He in Hlen; rewrite !length_app in *;
        simpl in *; lia) (A ++ B)); [reflexivity| | | |exact Hi].
      * rewrite He in Hnd. apply NoDup_ListNoDup. eapply NoDup_remove_1 with (a:=v).
        apply NoDup_ListNoDup in Hnd. exact Hnd.
      * intros j Hj. apply Hin. rewrite He. apply in_app_iff in Hj. apply in_app_iff. simpl. tauto.
      * intros j Hj Hnot. destruct (decide (j = v)) as [->|Hne]; [exact Hreach|].
        apply Hout; [exact Hj|]. rewrite He. rewrite in_app_iff in *. simpl. intuition congruence. }
  apply (Hprune (length (elements (row_names L))) (elements (row_names L))); [reflexivity|apply NoDup_elements| |].
  - intros i Hi. now apply elem_of_elements, list_elem_of_In.
  - intros i Hi Hout. exfalso. apply Hout. now apply list_elem_of_In, elem_of_elements.
Qed.

Lemma well_network_fully_reachable ρ :
  well_network ρ -> fully_reachable ρ.
Proof.
  intros (L & HR & HN) i.
  destruct (ρ !! i) as [o|] eqn:Hi; [right|now left].
  eapply network_reachable; [exact HR|exact HN|].
  apply (proj2 HR) in Hi as (r & Hr & Hid & Ho).
  apply in_row_names. eauto.
Qed.

Lemma initial_network e :
  typed ∅ e UnitT -> well_network {[0 := Thread e]}.
Proof.
  intros H. exists [thread_row 0 e []]. split.
  - apply rows_insert; [apply rows_empty|apply cfg_lookup_empty].
  - split.
    + constructor; [split; [now apply source_runtime|reflexivity]|constructor].
    + split; [reflexivity|apply empty_forest].
Qed.

Theorem typed_full_reachability e ρ :
  typed ∅ e UnitT -> steps {[ 0 := Thread e ]} ρ -> fully_reachable ρ.
Proof.
  intros HT Hsteps. apply well_network_fully_reachable.
  pose proof (initial_network _ HT) as HI.
  revert HI. induction Hsteps as [x|x y z [i HS] Hpath IH].
  - auto.
  - intros HX. apply IH. eapply network_step; eauto.
Qed.
