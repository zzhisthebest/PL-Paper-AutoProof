From Stdlib Require Import List Bool PeanoNat Lia Sorting.Permutation.
Require Import pi_syntax type_system type_system_rules semantics.
Require Import pairEq.
Import ListNotations.

(* Represent list environments by pointwise lookups. *)
Local Lemma pair_eq_true x y : pair_eq x y = true <-> x = y.
Proof.
  destruct x, y; unfold pair_eq; cbn.
  rewrite andb_true_iff, !Nat.eqb_eq.
  split; [intros [-> ->] | intros E; inversion E]; auto.
Qed.

Local Lemma pair_eq_false x y : pair_eq x y = false <-> x <> y.
Proof. rewrite <- pair_eq_true. destruct (pair_eq x y); intuition discriminate. Qed.

Local Definition key := (nat * nat)%type.
Local Definition entry := (flag * piType)%type.
Local Definition env := key -> option entry.

Local Definition fetch (g : typeEnv) : env :=
  fun k => let '(v,b) := InB k g in if b then Some v else None.

Local Definition update (e : env) (k : key) (v : option entry) : env :=
  fun x => if pair_eq x k then v else e x.

Local Lemma update_eq e k v : update e k v k = v.
Proof. unfold update; rewrite (proj2 (pair_eq_true _ _) eq_refl); reflexivity. Qed.

Local Lemma update_neq e k x v : x <> k -> update e k v x = e x.
Proof. intros N. unfold update; rewrite (proj2 (pair_eq_false _ _) N); reflexivity. Qed.

Local Lemma fetch_empty x : fetch [] x = None.
Proof. reflexivity. Qed.

Local Lemma fetch_cons g k f t x :
  fetch ((k,f,t)::g) x = update (fetch g) k (Some (f,t)) x.
Proof. unfold fetch, update; cbn; destruct (pair_eq x k); reflexivity. Qed.

Local Lemma fetch_sound g k f t :
  fetch g k = Some (f,t) -> In (k,f,t) g.
Proof.
  induction g as [|[[j h] s] g IH]; [discriminate|].
  rewrite fetch_cons. unfold update. destruct (pair_eq k j) eqn:E.
  - apply pair_eq_true in E. subst. intros H; inversion H; subst; left; reflexivity.
  - right; auto.
Qed.

Local Lemma fetch_complete g (M : isMap g) k f t :
  In (k,f,t) g -> fetch g k = Some (f,t).
Proof.
  induction g as [|[[j h] s] g IH]; [contradiction|].
  intros I. rewrite fetch_cons. unfold update. destruct (pair_eq k j) eqn:E.
  - apply pair_eq_true in E. subst j.
    destruct (M k h s f t) as [-> ->]; auto with datatypes.
  - apply IH.
    + intros x f1 t1 f2 t2 [H1 H2]. apply (M x f1 t1 f2 t2); auto with datatypes.
    + destruct I as [I|I]; auto. inversion I; subst.
      apply pair_eq_false in E. contradiction.
Qed.

Local Lemma domain_spec g k : In k (domain g) <-> exists f t, In (k,f,t) g.
Proof.
  induction g as [|[[j h] s] g IH]; simpl.
  - firstorder.
  - rewrite IH. split.
    + intros [<-|[f [t I]]]; eauto.
    + intros [f [t [I|I]]]; [inversion I|]; eauto.
Qed.

Local Lemma fetch_domain g k : In k (domain g) <-> exists v, fetch g k = Some v.
Proof.
  induction g as [|[[j h] s] g IH]; [simpl; split; [contradiction|intros [? E]; discriminate]|].
  rewrite fetch_cons. simpl. rewrite IH. unfold update.
  destruct (pair_eq k j) eqn:E.
  - apply pair_eq_true in E. subst. split; [intros; eauto | auto].
  - apply pair_eq_false in E. intuition congruence.
Qed.

Local Lemma removeEntry_other g k j f t : j <> k ->
  In (j,f,t) (removeEntry k g) <-> In (j,f,t) g.
Proof.
  intros N. induction g as [|[[i h] s] g IH]; simpl; [tauto|].
  destruct (pair_eq i k) eqn:E; simpl.
  - apply pair_eq_true in E. subst. intuition congruence.
  - rewrite IH. tauto.
Qed.

Local Lemma removeEntry_subset g k x :
  In x (removeEntry k g) -> In x g.
Proof.
  induction g as [|[[j f] t] g IH]; simpl; [tauto|].
  destruct (pair_eq j k); simpl; tauto.
Qed.

Local Lemma removeEntry_map g k : isMap g -> isMap (removeEntry k g).
Proof. intros M x f1 t1 f2 t2 [H1 H2]. apply (M x f1 t1 f2 t2); eauto using removeEntry_subset. Qed.

Local Lemma removeEntry_domain g k : NoDup (domain g) ->
  forall x, In x (domain (removeEntry k g)) <-> x <> k /\ In x (domain g).
Proof.
  intros ND x. induction g as [|[[j f] t] g IH]; simpl in *; [tauto|].
  inversion ND as [|? ? H1 H2]; subst.
  destruct (pair_eq j k) eqn:E; simpl.
  - apply pair_eq_true in E. subst. intuition congruence.
  - apply pair_eq_false in E. rewrite IH by assumption. intuition congruence.
Qed.

Local Lemma removeEntry_nodup g k :
  NoDup (domain g) -> NoDup (domain (removeEntry k g)).
Proof.
  induction g as [|[[j f] t] g IH]; cbn; auto.
  intros ND. inversion ND as [|? ? H1 H2]; subst.
  destruct (pair_eq j k); cbn; auto.
  constructor; auto.
  rewrite removeEntry_domain by assumption. tauto.
Qed.

Local Lemma nodup_map g : NoDup (domain g) -> isMap g.
Proof.
  induction g as [|[[j f] t] g IH]; [unfold isMap; simpl; tauto|].
  intros ND x f1 t1 f2 t2 [I1 I2]. inversion ND as [|? ? H1 H2]; subst.
  destruct I1 as [I1|I1], I2 as [I2|I2]; try solve [eapply IH; eauto].
  - inversion I1; inversion I2; subst; auto.
  - inversion I1; subst. exfalso. apply H1, domain_spec. eauto.
  - inversion I2; subst. exfalso. apply H1, domain_spec. eauto.
Qed.

Local Lemma fetch_remove g k j : NoDup (domain g) ->
  fetch (removeEntry k g) j = update (fetch g) k None j.
Proof.
  intros ND. destruct (pair_eq j k) eqn:E.
  - apply pair_eq_true in E. subst. rewrite update_eq.
    destruct (fetch (removeEntry k g) k) as [v|] eqn:F; auto.
    exfalso. assert (In k (domain (removeEntry k g))) by (apply fetch_domain; eauto).
    apply removeEntry_domain in H; tauto.
  - apply pair_eq_false in E. rewrite update_neq by assumption.
    destruct (fetch g j) as [[f t]|] eqn:F.
    + apply fetch_complete, removeEntry_other; eauto using nodup_map, removeEntry_map, fetch_sound.
    + destruct (fetch (removeEntry k g) j) as [[f t]|] eqn:G; auto.
      apply fetch_sound, removeEntry_other in G; auto.
      apply (fetch_complete g (nodup_map g ND)) in G. congruence.
Qed.

Local Definition set (e : env) (k : key) (f : flag) (t : piType) :=
  update e k (Some (f,t)).

Local Definition mapped (g : typeEnv) (e : env) :=
  forall k, fetch g k = e k.

Local Lemma set_list g e k f t (ND : NoDup (domain g)) :
  mapped g e -> mapped ((k,f,t)::removeEntry k g) (set e k f t).
Proof.
  intros E x. rewrite fetch_cons. unfold set, update.
  destruct (pair_eq x k) eqn:P; auto.
  rewrite fetch_remove by assumption. unfold update. rewrite P. apply E.
Qed.

Local Lemma add_list g e k f t :
  mapped g e -> mapped ((k,f,t)::g) (set e k f t).
Proof. intros E x; rewrite fetch_cons; unfold set, update; rewrite E; reflexivity. Qed.

Local Lemma set_nodup g k f t :
  NoDup (domain g) -> NoDup (domain ((k,f,t)::removeEntry k g)).
Proof.
  intros ND. simpl. constructor; auto using removeEntry_nodup.
  rewrite removeEntry_domain by assumption. tauto.
Qed.

Local Lemma set_domain g k f t :
  NoDup (domain g) -> In k (domain g) ->
  forall x, In x (domain ((k,f,t)::removeEntry k g)) <-> In x (domain g).
Proof.
  intros ND I x. simpl. rewrite removeEntry_domain by assumption.
  destruct (pair_eq x k) eqn:P.
  - apply pair_eq_true in P; subst; tauto.
  - apply pair_eq_false in P; intuition congruence.
Qed.

Local Lemma max_upper l k : In k l -> snd k <= max l.
Proof.
  induction l as [|[x n] l IH]; simpl; [contradiction|].
  destruct (n <? max l) eqn:E.
  - apply Nat.ltb_lt in E. intros [<-|I]; cbn; auto using Nat.lt_le_incl.
  - apply Nat.ltb_ge in E. intros [<-|I]; cbn; auto.
    specialize (IH I). lia.
Qed.

Local Lemma max_le l m :
  (forall k, In k l -> snd k <= m) -> max l <= m.
Proof.
  induction l as [|[x n] l IH]; simpl; [lia|].
  intros B. specialize (IH ltac:(eauto)).
  destruct (n <? max l); auto. exact (B (x,n) (or_introl eq_refl)).
Qed.

Local Lemma max_equiv l r :
  (forall k, In k l <-> In k r) -> max l = max r.
Proof.
  intros E. apply Nat.le_antisymm; apply max_le; intros k I;
    apply max_upper; apply E; assumption.
Qed.

Local Lemma max_add l k : snd k <= max l -> max (k::l) = max l.
Proof.
  intros B. apply Nat.le_antisymm; [apply max_le|].
  - intros j [<-|I]; auto using max_upper.
  - apply max_le. intros j I. apply max_upper. right; auto.
Qed.

(* An unused linear channel must have empty polarity. *)
Local Definition discardable t :=
  match t with Chan lin p _ => p = empty | _ => True end.

Local Lemma cons_all g (M : isMap g) :
  cons g M <-> forall k f t, In (k,f,t) g -> discardable t.
Proof.
  split.
  - intros C. induction C as [g M E|g M n P H C IH|g M n p s P H C IH|g M n s P H C IH].
    all: try solve [subst; contradiction].
    all: intros k f t I; destruct (pair_eq k n) eqn:F.
    all: try (apply pair_eq_false in F; apply (IH k f t); now apply removeEntry_other).
    all: apply pair_eq_true in F; subst k; inversion H as [?? h ? J]; subst;
      let u := match type of J with In (_,_,?s) _ => s end in
      destruct (M n f t h u (conj I J)) as [_ ->]; reflexivity || exact I.
  - revert M. induction g as [|[[k f] s] g IH]; intros M H.
    + constructor; reflexivity.
    + assert (R : removeEntry k ((k,f,s)::g) = g).
      { cbn. rewrite (proj2 (pair_eq_true _ _) eq_refl). reflexivity. }
      assert (C : exists N, cons (removeEntry k ((k,f,s)::g)) N).
      { rewrite R. assert (N : isMap g).
        { intros x f1 t1 f2 t2 [I J]. apply (M x f1 t1 f2 t2); auto with datatypes. }
        exists N. apply IH. intros x j t I. apply (H x j t); right; exact I. }
      destruct C as [N C].
      assert (I : In (k,f,s) ((k,f,s)::g)) by (left; reflexivity).
      specialize (H _ _ _ I). destruct s as [[|] p t|]; cbn in H.
      * subst. eapply Co_lin with (n:=k); [econstructor; eauto|exact C].
      * eapply Co_un with (n:=k); [econstructor; eauto|exact C].
      * eapply Co_top with (n:=k); [econstructor; eauto|exact C].
Qed.

Inductive join_entry : entry -> entry -> entry -> Prop :=
| join_top f1 f2 f :
    flag_plus f1 f2 f -> join_entry (f1,Top) (f2,Top) (f,Top)
| join_linear f1 f2 f p1 p2 p t :
    flag_plus f1 f2 f -> pol_plus p1 p2 p ->
    join_entry (f1,Chan lin p1 t) (f2,Chan lin p2 t) (f,Chan lin p t)
| join_un f1 f2 f p t :
    flag_plus f1 f2 f ->
    join_entry (f1,Chan un p t) (f2,Chan un p t) (f,Chan un p t).

Inductive join_option : option entry -> option entry -> option entry -> Prop :=
| join_none : join_option None None None
| join_some v1 v2 v : join_entry v1 v2 v ->
    join_option (Some v1) (Some v2) (Some v).

Local Definition join_env (E1 E2 E : env) := forall k, join_option (E1 k) (E2 k) (E k).

Local Lemma join_set E1 E2 E k v1 v2 v :
  join_env E1 E2 E -> join_option v1 v2 v ->
  join_env (update E1 k v1) (update E2 k v2) (update E k v).
Proof.
  intros J V x. unfold update. destruct (pair_eq x k); auto.
Qed.

Local Lemma domain_peel g k :
  In k (domain g) -> Permutation (domain g) (k :: domain (removeEntry k g)).
Proof.
  induction g as [|[[x f] t] g IH]; simpl; [contradiction|].
  destruct (pair_eq x k) eqn:E; simpl.
  - apply pair_eq_true in E. subst; reflexivity.
  - apply pair_eq_false in E. intros [I|I]; [contradiction|].
    transitivity (x :: k :: domain (removeEntry k g)); auto using perm_skip, perm_swap.
Qed.

Local Lemma flag_type_in g (M : isMap g) k f t :
  flagOf g k f -> typeOf g k t -> In (k,f,t) g.
Proof.
  intros F T. inversion F as [??? t' I]; subst. inversion T as [?? f' ? J]; subst.
  destruct (M k f t' f' t (conj I J)) as [_ <-]. exact I.
Qed.

Local Lemma split_domains g1 g2 g M1 M2 M :
  tEnv_split g1 g2 g M1 M2 M ->
  Permutation (domain g1) (domain g) /\ Permutation (domain g2) (domain g).
Proof.
  intros S. induction S; subst; [split; reflexivity| | |].
  all: destruct IHS as [E1 E2].
  all: assert (I1 : In n (domain g1)) by (apply domain_spec; eauto).
  all: assert (I2 : In n (domain g2)) by (apply domain_spec; eauto).
  all: assert (I3 : In n (domain g3)) by (apply domain_spec; eauto using flag_type_in).
  all: split.
  all: eapply Permutation_trans; [apply domain_peel; eassumption|].
  all: eapply Permutation_trans; [apply perm_skip; eassumption|symmetry; apply domain_peel; eassumption].
Qed.

Local Lemma fetch_remove_neq g k j : isMap g -> j <> k ->
  fetch (removeEntry k g) j = fetch g j.
Proof.
  intros M N. destruct (fetch g j) as [[f t]|] eqn:F.
  - apply fetch_complete, removeEntry_other; eauto using removeEntry_map, fetch_sound.
  - destruct (fetch (removeEntry k g) j) as [[f t]|] eqn:G; auto.
    apply fetch_sound, removeEntry_other in G; auto.
    pose proof (fetch_complete _ M _ _ _ G). congruence.
Qed.

Local Lemma split_join g1 g2 g M1 M2 M :
  tEnv_split g1 g2 g M1 M2 M ->
  join_env (fetch g1) (fetch g2) (fetch g).
Proof.
  intros S. induction S; subst; [intros k; constructor| | |].
  all: intros k; destruct (pair_eq k n) eqn:E.
  all: try solve [apply pair_eq_false in E; specialize (IHS k);
    repeat rewrite fetch_remove_neq in IHS by assumption; exact IHS].
  all: apply pair_eq_true in E; subst k.
  all: match goal with FF : flagOf ?gg ?nn ?ff, TT : typeOf ?gg ?nn ?tt, M : isMap ?gg |- _ =>
    rewrite (fetch_complete gg M nn ff tt (flag_type_in gg M nn ff tt FF TT)) end.
  all: repeat match goal with H : In (?k,?ff,?tt) ?g, M : isMap ?g |- context [fetch ?g ?k] =>
    rewrite (fetch_complete g M k ff tt H) end.
  all: constructor; constructor; assumption.
Qed.

Local Lemma head_remove g k f t : removeEntry k ((k,f,t)::g) = g.
Proof. simpl. rewrite (proj2 (pair_eq_true _ _) eq_refl). reflexivity. Qed.

Local Lemma split_prepend g1 g2 g k f1 f2 f t1 t2 t M1 M2 M
    N1 N2 N :
  tEnv_split g1 g2 g M1 M2 M ->
  join_entry (f1,t1) (f2,t2) (f,t) ->
  tEnv_split ((k,f1,t1)::g1) ((k,f2,t2)::g2) ((k,f,t)::g) N1 N2 N.
Proof.
  intros S J.
  assert (R : exists U1 U2,
    tEnv_split (removeEntry k ((k,f1,t1)::g1))
      (removeEntry k ((k,f2,t2)::g2)) g U1 U2 M).
  { rewrite !head_remove. eauto. }
  destruct R as [U1 [U2 R]]. inversion J; subst.
  - eapply SpTop with (n:=k); eauto using head_remove, F_Entry, T_Entry with datatypes.
  - eapply SpLin with (n:=k); eauto using head_remove, F_Entry, T_Entry with datatypes.
  - eapply SpUn with (n:=k); eauto using head_remove, F_Entry, T_Entry with datatypes.
Qed.

Local Lemma split_realize g e1 e2 M :
  NoDup (domain g) -> join_env e1 e2 (fetch g) ->
  exists g1 g2 M1 M2,
    mapped g1 e1 /\ mapped g2 e2 /\ tEnv_split g1 g2 g M1 M2 M.
Proof.
  revert e1 e2 M. induction g as [|[[k f] t] g IH]; intros e1 e2 M ND J.
  - assert (E : isMap []) by (unfold isMap; simpl; tauto).
    exists [], [], E, E. repeat split.
    + intros x. specialize (J x). rewrite fetch_empty in *. inversion J; reflexivity.
    + intros x. specialize (J x). rewrite fetch_empty in *. inversion J; reflexivity.
    + constructor; reflexivity.
  - inversion ND as [|? ? N NDg]; subst.
    pose proof (J k) as Jk. rewrite fetch_cons, update_eq in Jk.
    inversion Jk as [|[f1 t1] [f2 t2] [f0 t0] JP E1 E2 E3]; subst.
    assert (T : join_env (update e1 k None) (update e2 k None) (fetch g)).
    { intros x. destruct (pair_eq x k) eqn:P.
      - apply pair_eq_true in P. subst x. rewrite !update_eq.
        destruct (fetch g k) eqn:F; [exfalso; apply N, fetch_domain; eauto|constructor].
      - apply pair_eq_false in P. rewrite !update_neq by assumption.
        specialize (J x). rewrite fetch_cons, update_neq in J by assumption. exact J. }
    destruct (IH _ _ (nodup_map _ NDg) NDg T) as [g1 [g2 [M1 [M2 [G1 [G2 S]]]]]].
    assert (N1 : NoDup (domain ((k,f1,t1)::g1))).
    { simpl. constructor.
      - intro I. apply fetch_domain in I. destruct I as [v V]. rewrite G1, update_eq in V; discriminate.
      - destruct (split_domains _ _ _ _ _ _ S) as [A B].
        eapply Permutation_NoDup; [symmetry; exact A|assumption]. }
    assert (N2 : NoDup (domain ((k,f2,t2)::g2))).
    { simpl. constructor.
      - intro I. apply fetch_domain in I. destruct I as [v V]. rewrite G2, update_eq in V; discriminate.
      - destruct (split_domains _ _ _ _ _ _ S) as [A B].
        eapply Permutation_NoDup; [symmetry; exact B|assumption]. }
    exists ((k,f1,t1)::g1), ((k,f2,t2)::g2), (nodup_map _ N1), (nodup_map _ N2).
    split; [|split].
    + intros x. rewrite fetch_cons. destruct (pair_eq x k) eqn:P.
      * apply pair_eq_true in P. subst. rewrite update_eq. now symmetry.
      * apply pair_eq_false in P. rewrite update_neq, G1, update_neq by assumption. reflexivity.
    + intros x. rewrite fetch_cons. destruct (pair_eq x k) eqn:P.
      * apply pair_eq_true in P. subst. rewrite update_eq. now symmetry.
      * apply pair_eq_false in P. rewrite update_neq, G2, update_neq by assumption. reflexivity.
    + eapply split_prepend; eassumption.
Qed.

Local Definition nonhidden_cons (E : env) :=
  forall k f t, E k = Some (f,t) -> f <> hid -> discardable t.

Local Lemma projected_in g k f t :
  In (k,f,t) (vis_proj g ++ ill_proj g) <-> In (k,f,t) g /\ f <> hid.
Proof.
  rewrite in_app_iff.
  induction g as [|[[[a b] h] s] g IH]; simpl; [tauto|].
  destruct h; simpl in *; destruct f; intuition congruence.
Qed.

Local Lemma projected_map g : isMap g -> isMap (vis_proj g ++ ill_proj g).
Proof.
  intros M x f1 t1 f2 t2 [I J]. apply (M x f1 t1 f2 t2).
  apply projected_in in I, J. tauto.
Qed.

Local Lemma nonhidden_cons_projected g (M : isMap g) :
  nonhidden_cons (fetch g) <->
  forall N, cons (vis_proj g ++ ill_proj g) N.
Proof.
  split.
  - intros C N. apply cons_all.
    intros k f t I. apply projected_in in I as [I F]. eapply C; eauto using fetch_complete.
  - intros C k f t E F.
    apply ((proj1 (cons_all _ _)) (C (projected_map _ M))) with (k:=k) (f:=f).
    apply projected_in. eauto using fetch_sound.
Qed.

(* Pointwise typing is equivalent to the list-based rules on unique domains. *)
Inductive mtyped (m : nat) : env -> dproc -> Prop :=
| mt_zero E :
    (forall k f t, E k = Some (f,t) -> discardable t) ->
    mtyped m E dZero
| mt_nu E k t q :
    E k = Some (hid,t) ->
    mtyped m (set E k vis t) q ->
    mtyped m E (dNu (fst k) (snd k) q)
| mt_par E E1 E2 p q :
    join_env E1 E2 E ->
    mtyped m E1 p -> mtyped m E2 q ->
    mtyped m E (dPar p q)
| mt_out_lin E a b p t s r u q :
    E a = Some (vis,Chan lin p t) -> E b = Some (vis,s) ->
    type_remove (Chan lin p t) (Chan lin out t) r ->
    type_remove s t u ->
    mtyped m (set (set E a vis r) b vis u) q ->
    mtyped m E (dOut (fst a) (snd a) (fst b) (snd b) q)
| mt_out_un E a b p t s u q :
    E a = Some (vis,Chan un p t) -> E b = Some (vis,s) ->
    (p = io \/ p = out) ->
    type_remove s t u ->
    mtyped m (set E b vis u) q ->
    mtyped m E (dOut (fst a) (snd a) (fst b) (snd b) q)
| mt_in_lin E a b p t r q :
    E a = Some (vis,Chan lin p t) -> E b = None -> snd b < m ->
    type_remove (Chan lin p t) (Chan lin inp t) r ->
    mtyped m (set (set E a vis r) b vis t) q ->
    mtyped m E (dInp (fst a) (snd a) (fst b) (snd b) q)
| mt_in_un E a b p t q :
    E a = Some (vis,Chan un p t) -> E b = None -> snd b < m ->
    (p = io \/ p = inp) ->
    mtyped m (set E b vis t) q ->
    mtyped m E (dInp (fst a) (snd a) (fst b) (snd b) q)
| mt_bang E a b p t q :
    E a = Some (vis,Chan un p t) -> E b = None -> snd b < m ->
    (p = io \/ p = inp) ->
    nonhidden_cons E ->
    mtyped m (set E b vis t) q ->
    mtyped m E (dBang (fst a) (snd a) (fst b) (snd b) q).

Local Lemma fetch_none g k : fetch g k = None <-> ~ In k (domain g).
Proof.
  rewrite fetch_domain. destruct (fetch g k) eqn:E; firstorder congruence.
Qed.

Local Lemma type_sub_not_payload m p t : ~ type_sub t (Chan m p t).
Proof.
  revert m p. induction t as [m' p' s IH|]; intros m p S.
  - inversion S; subst; try congruence.
    all: match goal with E : ?u = Chan ?mode ?p ?u |- _ =>
      eapply (IH mode p); rewrite <- E; constructor end.
  - inversion S.
Qed.

Local Lemma out_distinct (e : env) a b m p t s r :
  e a = Some (vis,Chan m p t) ->
  e b = Some (vis,s) ->
  type_remove s t r -> a <> b.
Proof.
  intros A B [S _] <-. rewrite A in B. inversion B; subst.
  eapply type_sub_not_payload; eassumption.
Qed.

Local Lemma list_two_set g E a b fa ta fb tb :
  NoDup (domain g) -> mapped g E -> a <> b ->
  mapped ((a,fa,ta)::(b,fb,tb)::removeEntry b (removeEntry a g))
    (set (set E a fa ta) b fb tb).
Proof.
  intros ND Map Diff x. rewrite fetch_cons.
  unfold set, update. destruct (pair_eq x a) eqn:A.
  - destruct (pair_eq x b) eqn:B; auto. apply pair_eq_true in A, B; congruence.
  - rewrite fetch_cons. unfold update. destruct (pair_eq x b) eqn:B; auto.
    apply pair_eq_false in A, B. rewrite !fetch_remove_neq by eauto using nodup_map, removeEntry_map. apply Map.
Qed.

Local Lemma list_two_set_domain g a b fa ta fb tb :
  NoDup (domain g) -> In a (domain g) -> In b (domain g) -> a <> b ->
  NoDup (domain ((a,fa,ta)::(b,fb,tb)::removeEntry b (removeEntry a g))) /\
  forall x, In x (domain ((a,fa,ta)::(b,fb,tb)::removeEntry b (removeEntry a g))) <->
            In x (domain g).
Proof.
  intros ND A B N.
  assert (R : NoDup (domain (removeEntry a g))) by now apply removeEntry_nodup.
  split.
  - simpl. constructor.
    + simpl. rewrite !removeEntry_domain by assumption. intuition congruence.
    + exact (set_nodup _ b fb tb R).
  - simpl. intros x. rewrite !removeEntry_domain by assumption. destruct (pair_eq x a) eqn:F; [apply pair_eq_true in F; subst; tauto|];
    destruct (pair_eq x b) eqn:G; [apply pair_eq_true in G; subst; tauto|];
    apply pair_eq_false in F, G; intuition congruence.
Qed.

Local Lemma list_in_set g E a b ta tb :
  NoDup (domain g) -> mapped g E -> a <> b ->
  mapped ((a,vis,ta)::(b,vis,tb)::removeEntry a g) (set (set E a vis ta) b vis tb).
Proof.
  intros ND Map Diff x. rewrite fetch_cons.
  unfold set, update. destruct (pair_eq x a) eqn:A.
  - destruct (pair_eq x b) eqn:B; auto. apply pair_eq_true in A, B; congruence.
  - rewrite fetch_cons. unfold update. destruct (pair_eq x b) eqn:B; auto.
    apply pair_eq_false in A. rewrite fetch_remove_neq by eauto using nodup_map. apply Map.
Qed.

Local Lemma list_in_set_domain g a b ta tb :
  NoDup (domain g) -> In a (domain g) -> ~ In b (domain g) ->
  NoDup (domain ((a,vis,ta)::(b,vis,tb)::removeEntry a g)) /\
  forall x, In x (domain ((a,vis,ta)::(b,vis,tb)::removeEntry a g)) <->
            In x (b :: domain g).
Proof.
  intros ND A B. split.
  - simpl. constructor; simpl.
    + rewrite removeEntry_domain by assumption. intuition congruence.
    + constructor; [rewrite removeEntry_domain by assumption; tauto|now apply removeEntry_nodup].
  - simpl. intros x. rewrite removeEntry_domain by assumption. destruct (pair_eq x a) eqn:F; [apply pair_eq_true in F; subst; tauto|]; apply pair_eq_false in F; intuition congruence.
Qed.

Local Lemma mtyped_ext m E p :
  mtyped m E p -> forall D, (forall x, E x = D x) -> mtyped m D p.
Proof.
  intros T. induction T; intros D EQ.
  - apply mt_zero. intros k f t V. apply (H k f t). now rewrite EQ.
  - eapply mt_nu with (t:=t); [now rewrite <- EQ|].
    apply IHT. intros x. unfold set, update. now rewrite EQ.
  - eapply mt_par with (E1:=E1) (E2:=E2); eauto.
    intros x. now rewrite <- EQ.
  - eapply mt_out_lin with (p:=p) (t:=t) (s:=s) (r:=r) (u:=u); eauto.
    all: try (now rewrite <- EQ).
    apply IHT. intros x. unfold set, update. now rewrite EQ.
  - eapply mt_out_un with (p:=p) (t:=t) (s:=s) (u:=u); eauto.
    all: try (now rewrite <- EQ).
    apply IHT. intros x. unfold set, update. now rewrite EQ.
  - eapply mt_in_lin with (p:=p) (t:=t) (r:=r); eauto.
    all: try (now rewrite <- EQ).
    apply IHT. intros x. unfold set, update. now rewrite EQ.
  - eapply mt_in_un with (p:=p) (t:=t); eauto.
    all: try (now rewrite <- EQ).
    apply IHT. intros x. unfold set, update. now rewrite EQ.
  - eapply mt_bang with (p:=p) (t:=t); eauto.
    all: try (now rewrite <- EQ).
    + intros k f u V N. apply (H3 k f u); [now rewrite EQ|exact N].
    + apply IHT. intros x. unfold set, update. now rewrite EQ.
Qed.

Local Lemma typeCheck_to_m g M p :
  typeCheck g M p -> NoDup (domain g) ->
  mtyped (max (domain g)) (fetch g) p.
Proof.
  intros C. induction C; intro ND.
  - constructor. intros k f t E. eapply (proj1 (cons_all _ _) H).
    eapply fetch_sound; eauto.
  - eapply mt_nu.
    + eapply fetch_complete; eauto.
    + specialize (IHC (set_nodup _ _ _ _ ND)).
      rewrite (max_equiv _ _ (set_domain _ _ _ _ ND ltac:(apply domain_spec; eauto))) in IHC.
      eapply mtyped_ext; [exact IHC|].
      eapply set_list; eauto. intro k; reflexivity.
  - destruct (split_domains _ _ _ _ _ _ H) as [P1 P2].
    assert (N1 : NoDup (domain g1)) by (eapply Permutation_NoDup; [symmetry; exact P1|assumption]).
    assert (N2 : NoDup (domain g2)) by (eapply Permutation_NoDup; [symmetry; exact P2|assumption]).
    specialize (IHC1 N1). specialize (IHC2 N2).
    assert (E1 : max (domain g1) = max (domain g)).
    { apply max_equiv; intro k. split; apply Permutation_in; [exact P1|symmetry; exact P1]. }
    assert (E2 : max (domain g2) = max (domain g)).
    { apply max_equiv; intro k. split; apply Permutation_in; [exact P2|symmetry; exact P2]. }
    rewrite E1 in IHC1. rewrite E2 in IHC2.
    eapply mt_par; eauto using split_join.
  - assert (A := fetch_complete _ pf _ _ _ H1).
    assert (B := fetch_complete _ pf _ _ _ H2).
    assert (N : u <> v) by (eapply out_distinct; eauto).
    destruct (list_two_set_domain g u v vis t1 vis t2 ND
      ltac:(apply domain_spec; eauto) ltac:(apply domain_spec; eauto) N) as [ND' EQ].
    specialize (IHC ND'). rewrite (max_equiv _ _ EQ) in IHC.
    eapply mt_out_lin; try eassumption. eapply mtyped_ext; [exact IHC|].
    eapply list_two_set; eauto. intro k; reflexivity.
  - specialize (IHC (set_nodup _ _ _ _ ND)).
    rewrite (max_equiv _ _ (set_domain _ _ _ _ ND ltac:(apply domain_spec; eauto))) in IHC.
    eapply mt_out_un; eauto using fetch_complete.
    eapply mtyped_ext; [exact IHC|]. eapply set_list; eauto. intro k; reflexivity.
  - destruct (list_in_set_domain g u x t1 t ND
      ltac:(apply domain_spec; eauto) H1) as [ND' EQ].
    specialize (IHC ND'). rewrite (max_equiv _ _ EQ), max_add in IHC by lia.
    assert (F : fetch g x = None) by (apply fetch_none; assumption).
    eapply mt_in_lin; eauto using fetch_complete, fetch_none.
    eapply mtyped_ext; [exact IHC|].
    eapply list_in_set; [exact ND|intro k; reflexivity|].
    intros <-. apply H1, domain_spec; eauto.
  - assert (ND' : NoDup (domain ((x,vis,t)::g))) by (simpl; constructor; assumption).
    specialize (IHC ND').
    change (mtyped (max (x :: domain g)) (fetch ((x,vis,t)::g)) q) in IHC. rewrite max_add in IHC by lia.
    assert (F : fetch g x = None) by (apply fetch_none; assumption).
    eapply mt_in_un; eauto using fetch_complete, fetch_none.
    eapply mtyped_ext; [exact IHC|]. apply add_list. intro k; reflexivity.
  - assert (ND' : NoDup (domain ((x,vis,t)::g))) by (simpl; constructor; assumption).
    specialize (IHC ND').
    change (mtyped (max (x :: domain g)) (fetch ((x,vis,t)::g)) q) in IHC. rewrite max_add in IHC by lia.
    assert (F : fetch g x = None) by (apply fetch_none; assumption).
    eapply mt_bang; eauto using fetch_complete, fetch_none.
    + intros k f s V Hf. apply (proj1 (cons_all _ _) H3) with (k:=k) (f:=f).
      apply projected_in. eauto using fetch_sound.
    + eapply mtyped_ext; [exact IHC|]. apply add_list. intro k; reflexivity.
Qed.

Local Lemma mapped_has g E k f t :
  mapped g E -> E k = Some (f,t) -> In (k,f,t) g.
Proof. intros EQ V. apply fetch_sound. now rewrite EQ. Qed.

Local Lemma mapped_fresh g E k :
  mapped g E -> E k = None -> ~ In k (domain g).
Proof. intros EQ V. apply fetch_none. now rewrite EQ. Qed.

Local Lemma m_to_typeCheck m E p :
  mtyped m E p ->
  forall g M, NoDup (domain g) -> mapped g E -> m <= max (domain g) ->
  typeCheck g M p.
Proof.
  intros T. induction T; intros g M ND EQ B.
  - constructor. apply cons_all. intros k f t I. apply (H k f t).
    rewrite <- EQ. now apply fetch_complete.
  - assert (I : In (k,hid,t) g) by eauto using mapped_has.
    eapply TNew; [exact I|].
    apply IHT; eauto using set_nodup, set_list.
    rewrite (max_equiv _ _ (set_domain _ _ _ _ ND ltac:(apply domain_spec; eauto))). exact B.
  - assert (J : join_env E1 E2 (fetch g)) by (intro k; rewrite EQ; auto).
    destruct (split_realize _ _ _ M ND J) as [g1 [g2 [M1 [M2 [Q1 [Q2 S]]]]]].
    destruct (split_domains _ _ _ _ _ _ S) as [P1 P2].
    eapply TPar; [exact S|apply IHT1|apply IHT2]; auto.
    + eapply Permutation_NoDup; [symmetry; exact P1|assumption].
    + rewrite (max_equiv (domain g1) (domain g)); auto.
      intro k. split; apply Permutation_in; [exact P1|symmetry; exact P1].
    + eapply Permutation_NoDup; [symmetry; exact P2|assumption].
    + rewrite (max_equiv (domain g2) (domain g)); auto.
      intro k. split; apply Permutation_in; [exact P2|symmetry; exact P2].
  - assert (A : In (a,vis,Chan lin p t) g) by eauto using mapped_has.
    assert (C : In (b,vis,s) g) by eauto using mapped_has.
    assert (N : a <> b) by (eapply out_distinct; eauto).
    destruct (list_two_set_domain g a b vis r vis u ND
      ltac:(apply domain_spec; eauto) ltac:(apply domain_spec; eauto) N) as [ND' D].
    eapply TOutL; eauto.
    apply IHT; eauto using list_two_set. rewrite (max_equiv _ _ D). assumption.
  - assert (A : In (a,vis,Chan un p t) g) by eauto using mapped_has.
    assert (C : In (b,vis,s) g) by eauto using mapped_has.
    eapply TOutUn; eauto.
    apply IHT; eauto using set_nodup, set_list.
    rewrite (max_equiv _ _ (set_domain _ _ _ _ ND ltac:(apply domain_spec; eauto))). exact B.
  - assert (A : In (a,vis,Chan lin p t) g) by eauto using mapped_has.
    assert (C : ~ In b (domain g)) by eauto using mapped_fresh.
    assert (N : a <> b) by (intros <-; congruence).
    destruct (list_in_set_domain g a b r t ND
      ltac:(apply domain_spec; eauto) C) as [ND' D].
    eapply TInL; eauto. lia.
    apply IHT; eauto using list_in_set. rewrite (max_equiv _ _ D), max_add; lia.
  - assert (A : In (a,vis,Chan un p t) g) by eauto using mapped_has.
    assert (C : ~ In b (domain g)) by eauto using mapped_fresh.
    eapply TInUn; eauto. lia.
    apply IHT; eauto using add_list.
    + simpl. constructor; assumption.
    + change (m <= max (b :: domain g)). rewrite max_add; lia.
  - assert (A : In (a,vis,Chan un p t) g) by eauto using mapped_has.
    assert (C : ~ In b (domain g)) by eauto using mapped_fresh.
    eapply TInU; eauto. lia.
    + apply (proj1 (nonhidden_cons_projected g M)).
      intros k f t' V F. apply (H3 k f t'); [now rewrite <- EQ|assumption].
    + apply IHT; eauto using add_list.
      * simpl. constructor; assumption.
      * change (m <= max (b :: domain g)). rewrite max_add; lia.
  Unshelve.
  all: first [apply projected_map; assumption | apply nodup_map; first [assumption | apply set_nodup; assumption | simpl; constructor; assumption]].
Qed.

(* Consuming a permission commutes with carrying a disjoint permission. *)
Local Lemma type_remove_unique t s r1 r2 :
  type_remove t s r1 -> type_remove t s r2 -> r1 = r2.
Proof.
  intros [_ [P1 U1]] [_ [P2 U2]].
  destruct t as [[|] p t|].
  - inversion P1; inversion P2; subst. repeat match goal with H : pol_plus _ _ _ |- _ => inversion H; clear H; subst end;
    congruence.
  - rewrite U1, U2; unfold is_unrestricted; eauto.
  - inversion P1; inversion P2; reflexivity.
Qed.

Local Lemma source_lin_out_remove t :
  type_remove (Chan lin out t) (Chan lin out t) (Chan lin empty t).
Proof.
  split; [constructor|]. split; [constructor; constructor|].
  intros [? [? E]]; discriminate.
Qed.

Local Lemma type_plus_comm a b t : type_plus a b t -> type_plus b a t.
Proof.
  intros P; inversion P; subst; try constructor.
  - inversion H; subst; constructor.
  - clear P. destruct p1,p2; cbn; constructor.
Qed.

Local Lemma remove_add t s r u final :
  type_remove t s r -> type_plus t u final ->
  exists rest, type_remove final s rest /\ type_plus r u rest.
Proof.
  intros [Sub [Add Un]] Plus.
  inversion Plus; subst.
  - inversion Add; subst. exists Top. repeat split; try constructor.
  - inversion Add; subst.
    inversion H; subst; clear H. all: inversion H3; subst; clear H3.
    all: repeat match goal with p : pol |- _ => destruct p end.
    all: try discriminate.
    all: try solve [inversion Sub].
    all: eexists (Chan lin _ _); split; [shelve|constructor; constructor].
    Unshelve.
    all: split; [constructor|split; [constructor; constructor|intros [? [? E]]; discriminate]].
  - inversion Add; subst.
    assert (E : p3 = pol_cup p0 p3).
    { specialize (Un ltac:(unfold is_unrestricted; eauto)). now injection Un. }
    rewrite <- E. exists (Chan un (pol_cup p3 p2) t0). split; [|constructor].
    destruct p0,p3,p2; cbn in *; try discriminate.
    all: unfold type_remove; split.
    all: try solve [apply Ts_id | apply Ts_empty | apply Ts_inp | apply Ts_out].
    all: split; [apply Tp_UnPlus | intros _; reflexivity].
Qed.

Local Lemma set_same E k f t : E k = Some (f,t) -> forall x, set E k f t x = E x.
Proof.
  intros H x; unfold set, update; destruct (pair_eq x k) eqn:P; auto.
  apply pair_eq_true in P; subst; now symmetry.
Qed.

Inductive consumes : env -> key -> piType -> env -> Prop :=
| consume_entry E k t s r : E k = Some (vis,t) -> type_remove t s r ->
    consumes E k s (set E k vis r).

Local Lemma consumes_shape E k w D :
  consumes E k w D -> exists t r, E k = Some (vis,t) /\ type_remove t w r /\ D = set E k vis r.
Proof. intro C; inversion C; subst; eauto. Qed.

Local Lemma consume_port md p pol t r :
  type_remove (Chan md p t) (Chan md pol t) r ->
  md = un -> pol <> empty -> pol <> io ->
  (p = io \/ p = pol) /\ r = Chan md p t.
Proof.
  intros [Sub [Plus U]] -> N1 N2. split.
  - inversion Sub; subst; tauto.
  - apply U. unfold is_unrestricted. eauto.
Qed.

Local Lemma remove_un_port p ph t :
  (p = io \/ p = ph) -> ph <> io -> ph <> empty ->
  type_remove (Chan un p t) (Chan un ph t) (Chan un p t).
Proof.
  intros P N1 N2. destruct P as [ -> | -> ]; destruct ph; try contradiction;
    repeat split; solve [apply Ts_inp | apply Ts_out | apply Ts_id | apply Tp_UnPlus].
Qed.

Local Lemma consumes_out_intro m D a b md t D1 D2 q :
  consumes D a (Chan md out t) D1 ->
  consumes D1 b t D2 ->
  mtyped m D2 q ->
  mtyped m D (dOut (fst a) (snd a) (fst b) (snd b) q).
Proof.
  intros C1 C2 T.
  apply consumes_shape in C1 as [s [r [A [R ->]]]].
  apply consumes_shape in C2 as [u [v [B [S ->]]]].
  pose proof (proj1 (proj2 R)) as P. inversion P; subst.
  - assert (N : b <> a).
    { intros <-. unfold set in B. rewrite update_eq in B. inversion B; subst.
      eapply type_sub_not_payload; exact (proj1 S). }
    unfold set in B. rewrite update_neq in B by assumption.
    eapply mt_out_lin; eassumption.
  - assert (N : b <> a).
    { intros <-. unfold set in B. rewrite update_eq in B. inversion B; subst.
      eapply type_sub_not_payload; exact (proj1 S). }
    unfold set in B. rewrite update_neq in B by assumption.
    destruct (consume_port _ _ _ _ _ R eq_refl ltac:(discriminate) ltac:(discriminate))
      as [Port Eq]. subst.
    eapply mt_out_un; try eassumption.
    eapply mtyped_ext; [exact T|].
    intro k. unfold set at 1 3. unfold update at 1 2.
    destruct (pair_eq k b); auto. apply set_same. now rewrite Eq.
Qed.

Local Lemma consumes_in_intro m E a b md t D q :
  consumes E a (Chan md inp t) D ->
  E b = None -> snd b < m ->
  mtyped m (set D b vis t) q ->
  mtyped m E (dInp (fst a) (snd a) (fst b) (snd b) q).
Proof.
  intros C Fresh B T. apply consumes_shape in C as [s [r [A [R ->]]]].
  pose proof (proj1 (proj2 R)) as P. inversion P; subst.
  - eapply mt_in_lin; eassumption.
  - destruct (consume_port _ _ _ _ _ R eq_refl ltac:(discriminate) ltac:(discriminate))
      as [Port Eq]. subst.
    eapply mt_in_un; try eassumption.
    eapply mtyped_ext; [exact T|].
    intro k. unfold set at 1 3. unfold update at 1 2.
    destruct (pair_eq k b); auto. apply set_same. now rewrite Eq.
Qed.

(* Input substitution merges two visible capabilities at the received name. *)
Local Definition moved (x b k : key) : key := if pair_eq k x then b else k.

Local Lemma mv_moved x b k : mv k x b = moved x b k.
Proof. unfold mv, moved, pair_eq. destruct b, k; simpl. destruct (_ && _); reflexivity. Qed.

Local Definition dropped (E : env) k := update E k None.

Inductive aliases (x b : key) (E : env) : env -> Prop :=
| aliases_intro D f t u r :
    x <> b ->
    E x = Some (vis,t) ->
    E b = Some (f,u) ->
    f <> hid ->
    type_plus t u r ->
    (forall k, D k = set (dropped E x) b vis r k) ->
    aliases x b E D.

Local Lemma aliases_settings x b E D k f t :
  aliases x b E D -> k <> x -> k <> b ->
  aliases x b (set E k f t) (set D k f t).
Proof.
  intros A Kx Kb. destruct A as [D h s u r N X B H P EQ].
  eapply aliases_intro with (f:=h) (t:=s) (u:=u) (r:=r); eauto.
  - unfold set. rewrite update_neq by congruence. exact X.
  - unfold set. rewrite update_neq by congruence. exact B.
  - intro j. unfold set, dropped, update in *. rewrite EQ.
    destruct (pair_eq j k) eqn:K, (pair_eq j x) eqn:J, (pair_eq j b) eqn:L; auto;
      apply pair_eq_true in K; (apply pair_eq_true in J || apply pair_eq_true in L); congruence.
Qed.

Local Lemma aliases_fresh x b E D k :
  aliases x b E D -> E k = None -> k <> x /\ k <> b /\ D k = None.
Proof.
  intros A N. destruct A.
  assert (Kx : k <> x) by (intros <-; congruence).
  assert (Kb : k <> b) by (intros <-; congruence).
  repeat split; auto. rewrite H4. unfold set, dropped. rewrite !update_neq; assumption.
Qed.

Local Lemma aliases_hidden x b E D k t :
  aliases x b E D -> E k = Some (hid,t) -> k <> x /\ k <> b /\ D k = Some (hid,t).
Proof.
  intros A N. destruct A.
  assert (Kx : k <> x) by (intros <-; congruence).
  assert (Kb : k <> b) by (intros <-; congruence).
  repeat split; auto. rewrite H4. unfold set, dropped. rewrite !update_neq; assumption.
Qed.

Local Lemma aliases_consume x b E D k w E' :
  aliases x b E D -> consumes E k w E' ->
  exists D', consumes D (moved x b k) w D' /\ aliases x b E' D'.
Proof.
  intros A C. destruct A as [D f t u r N X B F P EQ].
  apply consumes_shape in C as [s [res [C [R ->]]]].
  unfold moved. destruct (pair_eq k x) eqn:Kx.
  - apply pair_eq_true in Kx; subst k. rewrite X in C. inversion C; subst s.
    destruct (remove_add _ _ _ _ _ R P) as [rr [RR PP]].
    exists (set D b vis rr). split.
    + econstructor; [rewrite EQ; unfold set; apply update_eq|exact RR].
    + eapply aliases_intro with (f:=f) (t:=res) (u:=u) (r:=rr); eauto.
      * unfold set; apply update_eq.
      * unfold set; rewrite update_neq by congruence; exact B.
      * intro k. unfold set, dropped, update in *. rewrite EQ.
        destruct (pair_eq k b), (pair_eq k x); reflexivity.
  - apply pair_eq_false in Kx. destruct (pair_eq k b) eqn:Kb.
    + apply pair_eq_true in Kb; subst k. rewrite B in C. inversion C; subst s f.
      apply type_plus_comm in P.
      destruct (remove_add _ _ _ _ _ R P) as [rr [RR PP]].
      exists (set D b vis rr). split.
      * econstructor; [rewrite EQ; unfold set; apply update_eq|exact RR].
      * eapply aliases_intro with (f:=vis) (t:=t) (u:=res) (r:=rr); eauto using type_plus_comm.
        -- unfold set; rewrite update_neq by congruence; exact X.
        -- unfold set; apply update_eq.
        -- intro k. unfold set, dropped, update in *. rewrite EQ.
           destruct (pair_eq k b), (pair_eq k x); reflexivity.
    + apply pair_eq_false in Kb.
      exists (set D k vis res). split.
      * econstructor; [rewrite EQ; unfold set, dropped; rewrite !update_neq; eassumption|exact R].
      * eapply aliases_settings; eauto. econstructor; eauto.
Qed.

Local Lemma pol_cross p1 p2 p q1 q2 q r :
  pol_plus p1 p2 p -> pol_plus q1 q2 q -> pol_plus p q r ->
  exists r1 r2, pol_plus p1 q1 r1 /\ pol_plus p2 q2 r2 /\ pol_plus r1 r2 r.
Proof.
  intros P Q R.
  inversion P; subst; clear P.
  all: inversion Q; subst; clear Q.
  all: inversion R; subst; clear R.
  all: repeat match goal with p : pol |- _ => destruct p end.
  all: eexists; eexists; repeat split; constructor.
Qed.

Local Lemma join_merge t u r f v1 v2 w1 w2 :
  join_entry v1 v2 (vis,t) ->
  join_entry w1 w2 (f,u) -> f <> hid ->
  type_plus t u r ->
  exists f1 f2 t1 t2 u1 u2 r1 r2,
    v1 = (vis,t1) /\ v2 = (vis,t2) /\
    w1 = (f1,u1) /\ w2 = (f2,u2) /\ f1 <> hid /\ f2 <> hid /\
    type_plus t1 u1 r1 /\ type_plus t2 u2 r2 /\
    join_entry (vis,r1) (vis,r2) (vis,r).
Proof.
  intros V W F P. inversion V; subst.
  all: inversion W; subst.
  all: try solve [inversion P].
  all: repeat match goal with A : flag_plus _ _ _ |- _ => inversion A; subst; clear A end.
  all: try solve [contradiction].
  all: inversion P; subst.
  all: try solve [do 8 eexists; repeat split; try discriminate; try (constructor; constructor)].
  all: match goal with A : pol_plus ?p1 ?p2 ?p, B : pol_plus ?q1 ?q2 ?q, C : pol_plus ?p ?q ?r |- _ =>
    destruct (pol_cross _ _ _ _ _ _ _ A B C) as [r1 [r2 [R1 [R2 R]]]] end.
  all: do 8 eexists; repeat split; try discriminate.
  all: first [eapply Tp_LinPlus; eassumption | eapply join_linear; [constructor|eassumption]].
Qed.

Local Lemma aliases_join x b E1 E2 E D :
  aliases x b E D -> join_env E1 E2 E ->
  exists D1 D2, aliases x b E1 D1 /\ aliases x b E2 D2 /\ join_env D1 D2 D.
Proof.
  intros A J. destruct A as [D f t u r N X B F P EQ].
  pose proof (J x) as XJ. rewrite X in XJ. inversion XJ; subst.
  pose proof (J b) as BJ. rewrite B in BJ. inversion BJ; subst.
  match goal with V : join_entry _ _ (vis,t), W : join_entry _ _ (f,u) |- _ =>
    destruct (join_merge _ _ _ _ _ _ _ _ V W F P)
      as [f1 [f2 [t1 [t2 [u1 [u2 [r1 [r2 [-> [-> [-> [-> [N1 [N2 [A1 [A2 R]]]]]]]]]]]]]]]]
  end.
  exists (set (dropped E1 x) b vis r1), (set (dropped E2 x) b vis r2).
  repeat split.
  - eapply aliases_intro; eauto.
  - eapply aliases_intro; eauto.
  - intro k. rewrite EQ. unfold set, dropped, update.
    destruct (pair_eq k b), (pair_eq k x); auto using join_some, join_none.
Qed.

Local Lemma type_plus_discardable a b c :
  type_plus a b c -> discardable a -> discardable b -> discardable c.
Proof.
  intros P. inversion P; subst; simpl; auto.
  intros -> ->. inversion H; reflexivity.
Qed.

Local Lemma aliases_consistency x b E D (F : flag -> Prop) :
  aliases x b E D ->
  (F vis -> forall f, f <> hid -> F f) ->
  (forall k f t, E k = Some (f,t) -> F f -> discardable t) ->
  forall k f t, D k = Some (f,t) -> F f -> discardable t.
Proof.
  intros A NF C k f t Dk FC. destruct A as [D h s u r N X B H P EQ].
  rewrite EQ in Dk. unfold set, dropped, update in Dk.
  destruct (pair_eq k b) eqn:KB.
  - inversion Dk; subst. eapply type_plus_discardable; [exact P| |].
    + eapply (C x); eauto.
    + eapply (C b); eauto.
  - destruct (pair_eq k x); try discriminate. eapply (C k); eauto.
Qed.

Local Lemma aliases_source_ext x b E D E' :
  aliases x b E D -> (forall k, E k = E' k) -> aliases x b E' D.
Proof.
  intros A EQ. destruct A.
  econstructor; try eassumption; try (now rewrite <- EQ).
  intro k. unfold set,dropped,update in *. now rewrite <- EQ.
Qed.

Local Lemma aliases_un_port x b E D k p ph t :
  aliases x b E D -> E k = Some (vis,Chan un p t) ->
  (p = io \/ p = ph) -> ph <> empty -> ph <> io ->
  exists q, D (moved x b k) = Some (vis,Chan un q t) /\ (q = io \/ q = ph).
Proof.
  intros A V P N1 N2.
  assert (C : consumes E k (Chan un ph t) (set E k vis (Chan un p t)))
    by (econstructor; eauto using remove_un_port).
  destruct (aliases_consume _ _ _ _ _ _ _ A C) as [D' [K L]].
  apply consumes_shape in K as [s [r [J [R _]]]].
  pose proof (proj1 (proj2 R)) as PP. inversion PP; subst.
  eexists. split; [exact J|].
  destruct (consume_port _ _ _ _ _ R eq_refl N1 N2) as [Q _]. exact Q.
Qed.

Local Definition replace_refs p (x b : key) :=
  pmap p (fst x) (snd x) (fst b) (snd b).

Local Lemma replace_nu p a x b :
  replace_refs (dNu (fst a) (snd a) p) x b =
  dNu (fst a) (snd a) (replace_refs p x b).
Proof. reflexivity. Qed.

Local Lemma replace_out p a k x b :
  replace_refs (dOut (fst a) (snd a) (fst k) (snd k) p) x b =
  dOut (fst (moved x b a)) (snd (moved x b a))
    (fst (moved x b k)) (snd (moved x b k)) (replace_refs p x b).
Proof. destruct a, k, x, b; cbn [replace_refs fst snd pmap]; now rewrite !mv_moved.
Qed.

Local Lemma replace_in p a k x b :
  replace_refs (dInp (fst a) (snd a) (fst k) (snd k) p) x b =
  dInp (fst (moved x b a)) (snd (moved x b a))
    (fst k) (snd k) (replace_refs p x b).
Proof. destruct a, x, b; cbn [replace_refs fst snd pmap]; now rewrite !mv_moved.
Qed.

Local Lemma replace_bang p a k x b :
  replace_refs (dBang (fst a) (snd a) (fst k) (snd k) p) x b =
  dBang (fst (moved x b a)) (snd (moved x b a))
    (fst k) (snd k) (replace_refs p x b).
Proof. destruct a, x, b; cbn [replace_refs fst snd pmap]; now rewrite !mv_moved.
Qed.

Local Lemma aliases_preserve m E p x y :
  mtyped m E p ->
  forall D, aliases x y E D -> mtyped m D (replace_refs p x y).
Proof.
  intros T. induction T; intros D A.
  - apply mt_zero. intros k f u V.
    eapply (aliases_consistency x y E D (fun _ => True)); eauto.
  - destruct (aliases_hidden _ _ _ _ _ _ A H) as [Kx [Ky V]].
    rewrite replace_nu. eapply mt_nu; eauto using aliases_settings.
  - destruct (aliases_join _ _ _ _ _ _ A H) as [D1 [D2 [A1 [A2 J]]]].
    apply mt_par with (E1:=D1) (E2:=D2); eauto.
  - assert (C1 : consumes E a (Chan lin out t) (set E a vis r)) by (econstructor; eauto).
    assert (N : b <> a) by (intro C; symmetry in C; eapply out_distinct; eassumption).
    assert (C2 : consumes (set E a vis r) b t (set (set E a vis r) b vis u)).
    { econstructor; [unfold set; rewrite update_neq; eassumption|exact H2]. }
    destruct (aliases_consume _ _ _ _ _ _ _ A C1) as [D1 [R1 A1]].
    destruct (aliases_consume _ _ _ _ _ _ _ A1 C2) as [D2 [R2 A2]].
    rewrite replace_out. eapply consumes_out_intro; eauto.
  - assert (C1 : consumes E a (Chan un out t) (set E a vis (Chan un p t))).
    { econstructor; [eassumption|apply remove_un_port; tauto || discriminate]. }
    assert (C2 : consumes (set E a vis (Chan un p t)) b t (set (set E a vis (Chan un p t)) b vis u)).
    { econstructor; [rewrite set_same; eassumption|exact H2]. }
    destruct (aliases_consume _ _ _ _ _ _ _ A C1) as [D1 [R1 A1]].
    destruct (aliases_consume _ _ _ _ _ _ _ A1 C2) as [D2 [R2 A2]].
    rewrite replace_out. eapply consumes_out_intro; [exact R1|exact R2|].
    apply IHT. eapply aliases_source_ext; [exact A2|].
    unfold set at 1 3. unfold update at 1 2. intro k.
    destruct (pair_eq k b); [reflexivity|apply set_same; assumption].
  - destruct (aliases_fresh _ _ _ _ _ A H0) as [Kx [Ky Fresh]].
    assert (C : consumes E a (Chan lin inp t) (set E a vis r)) by (econstructor; eauto).
    destruct (aliases_consume _ _ _ _ _ _ _ A C) as [D1 [R A1]].
    rewrite replace_in. eapply consumes_in_intro; eauto using aliases_settings.
  - destruct (aliases_fresh _ _ _ _ _ A H0) as [Kx [Ky Fresh]].
    assert (C : consumes E a (Chan un inp t) (set E a vis (Chan un p t))).
    { econstructor; [eassumption|apply remove_un_port; tauto || discriminate]. }
    destruct (aliases_consume _ _ _ _ _ _ _ A C) as [D1 [R A1]].
    rewrite replace_in. eapply consumes_in_intro; [exact R|exact Fresh|assumption|].
    apply IHT. eapply aliases_source_ext; [eapply aliases_settings; eauto|].
    unfold set at 1 3. unfold update at 1 2. intro k.
    destruct (pair_eq k b); [reflexivity|apply set_same; assumption].
  - destruct (aliases_fresh _ _ _ _ _ A H0) as [Kx [Ky Fresh]].
    destruct (aliases_un_port _ _ _ _ _ _ inp _ A H H2 ltac:(discriminate) ltac:(discriminate))
      as [v [V P]].
    rewrite replace_bang. eapply mt_bang; eauto using aliases_settings.
    unfold nonhidden_cons in *. eapply aliases_consistency; eauto.
Qed.

Local Lemma unused_linear m E p :
  mtyped m E p ->
  forall k f t,
    E k = Some (f,t) ->
    (f = ill \/ (f = hid /\ ~ In k (secLabs p))) ->
    discardable t.
Proof.
  intros T. induction T; intros j f ty V U.
  - eapply H; eassumption.
  - simpl in U. assert (N : j <> k).
    { intros <-. rewrite H in V. inversion V; subst.
      destruct U as [C|[_ C]]; [discriminate|].
      apply C, in_app_iff. right. destruct j; simpl; tauto. }
    eapply IHT; [unfold set; rewrite update_neq; eassumption|].
    destruct U as [C|[F C]]; auto. right. split; auto.
    intro I. apply C, in_app_iff; auto.
  - pose proof (H j) as J. rewrite V in J. inversion J; subst.
    match goal with K : join_entry _ _ (f,ty) |- _ => inversion K; subst; cbn; auto end.
    assert (W1 : f1 = ill \/ (f1 = hid /\ ~ In j (secLabs p))).
    { destruct U as [F|[F N]]; subst; inversion H7; subst; auto.
      right; split; auto. intro I. apply N; simpl; apply in_app_iff; auto. }
    assert (W2 : f2 = ill \/ (f2 = hid /\ ~ In j (secLabs q))).
    { destruct U as [F|[F N]]; subst; inversion H7; subst; auto.
      right; split; auto. intro I. apply N; simpl; apply in_app_iff; auto. }
    specialize (IHT1 _ _ _ (eq_sym H0) W1). specialize (IHT2 _ _ _ (eq_sym H1) W2).
    simpl in *. subst. inversion H8; reflexivity.
  - assert (J1 : j <> a) by (intros <-; rewrite H in V; inversion V; subst; intuition discriminate).
    assert (J2 : j <> b) by (intros <-; rewrite H0 in V; inversion V; subst; intuition discriminate).
    eapply IHT; [unfold set; rewrite !update_neq; eassumption|exact U].
  - assert (J2 : j <> b) by (intros <-; rewrite H0 in V; inversion V; subst; intuition discriminate).
    eapply IHT; [unfold set; rewrite !update_neq; eassumption|exact U].
  - assert (J1 : j <> a) by (intros <-; rewrite H in V; inversion V; subst; intuition discriminate).
    assert (J2 : j <> b) by (intros <-; congruence).
    eapply IHT; [unfold set; rewrite !update_neq; eassumption|exact U].
  - assert (J2 : j <> b) by (intros <-; congruence).
    eapply IHT; [unfold set; rewrite !update_neq; eassumption|exact U].
  - assert (J2 : j <> b) by (intros <-; congruence).
    eapply IHT; [unfold set; rewrite !update_neq; eassumption|exact U].
Qed.

(* Inactive branches may gain visibility, unrestricted permissions, and
   fresh entries with no linear permissions. *)
Inductive raised_type : piType -> piType -> Prop :=
| raised_same t : raised_type t t
| raised_un p q t :
    type_sub (Chan un p t) (Chan un q t) ->
    raised_type (Chan un p t) (Chan un q t).

Inductive raised_flag : flag -> flag -> Prop :=
| raised_flag_same f : raised_flag f f
| raised_vis : raised_flag ill vis.

Inductive raised_entry (m : nat) (k : key) : option entry -> option entry -> Prop :=
| raised_none : raised_entry m k None None
| raised_fresh f t :
    m <= snd k -> f <> hid -> discardable t -> raised_entry m k None (Some (f,t))
| raised_one f1 f2 t1 t2 :
    raised_flag f1 f2 -> raised_type t1 t2 ->
    raised_entry m k (Some (f1,t1)) (Some (f2,t2)).

Local Definition raised_env m (E D : env) := forall k, raised_entry m k (E k) (D k).

Local Lemma raised_copy E D m k f t :
  raised_env m E D -> raised_env m (set E k f t) (set D k f t).
Proof.
  intros R x. unfold set, update. destruct (pair_eq x k); auto. constructor; constructor.
Qed.

Local Lemma raised_hidden m E D k t :
  raised_env m E D -> E k = Some (hid,t) ->
  exists u, D k = Some (hid,u) /\ raised_type t u.
Proof.
  intros R H. specialize (R k). rewrite H in R. inversion R; subst.
  match goal with F : raised_flag hid _ |- _ => inversion F; subst end. eauto.
Qed.

Local Lemma raised_empty m E D k :
  raised_env m E D -> E k = None -> snd k < m -> D k = None.
Proof.
  intros R F B. specialize (R k). rewrite F in R. inversion R; [reflexivity|lia].
Qed.

Local Lemma raised_discardable t u : raised_type t u -> discardable t -> discardable u.
Proof. intros R; inversion R; simpl; auto. Qed.

Local Lemma raised_remove t u s r :
  raised_type t u -> type_remove t s r ->
  exists v, type_remove u s v /\ raised_type r v.
Proof.
  intros H R. inversion H; subst.
  - exists r. split; [assumption|constructor].
  - assert (P : type_plus (Chan un p t0) (Chan un q t0) (Chan un q t0)).
    { inversion H0; subst; repeat match goal with p : pol |- _ => destruct p end;
      apply Tp_UnPlus. }
    destruct (remove_add _ _ _ _ _ R P) as [rr [RR PP]].
    assert (D : r = Chan un p t0) by (apply (proj2 (proj2 R)); unfold is_unrestricted; eauto).
    assert (D2 : rr = Chan un q t0) by (apply (proj2 (proj2 RR)); unfold is_unrestricted; eauto).
    subst. eexists. split; [exact RR|constructor; assumption].
Qed.

Local Lemma raised_consumes m E D k t E' :
  raised_env m E D -> consumes E k t E' ->
  exists D', consumes D k t D' /\ raised_env m E' D'.
Proof.
  intros H C. apply consumes_shape in C as [s [r [E0 [R ->]]]].
  pose proof (H k) as K. rewrite E0 in K. inversion K; subst.
  match goal with F : raised_flag vis _ |- _ => inversion F; subst end.
  match goal with T : raised_type _ _ |- _ => destruct (raised_remove _ _ _ _ T R) as [w [W RS]] end.
  exists (set D k vis w). split; [econstructor; [symmetry; eassumption|eassumption]|].
  intro j. unfold set, update. destruct (pair_eq j k); auto. constructor; [constructor|assumption].
Qed.

Local Lemma raised_consistent m E D (F : flag -> Prop) :
  raised_env m E D ->
  (forall f1 f2, raised_flag f1 f2 -> F f2 -> F f1) ->
  (forall k f t, E k = Some (f,t) -> F f -> discardable t) ->
  forall k f t, D k = Some (f,t) -> F f -> discardable t.
Proof.
  intros R Fback C k f t V H. specialize (R k). rewrite V in R.
  inversion R; subst; auto.
  eapply raised_discardable; eauto.
Qed.

Local Definition lift_under (left : bool) (old d sub : option entry) : option entry :=
  match old, d, sub with
  | Some (f,_), Some (g,t), Some (h,s) =>
      Some (match f,g with ill,vis => vis | _,_ => h end,
        match t with Chan un _ _ => t | _ => s end)
  | None, Some (f,t), None =>
      Some (if left then f else match f with hid => ill | _ => f end,t)
  | _, _, _ => None
  end.

Local Lemma raised_join_entry m k u v w d :
  join_option u v w -> raised_entry m k w d ->
  let u' := lift_under true w d u in
  let v' := lift_under false w d v in
  join_option u' v' d /\ raised_entry m k u u' /\ raised_entry m k v v'.
Proof.
  intros J R. inversion J; subst.
  - inversion R; subst.
    + simpl. repeat split; constructor.
    + destruct f; [contradiction| |].
      all: simpl.
      all: split; [|split; apply raised_fresh; assumption].
      all: constructor; destruct t as [[|] p t|]; simpl in *; try subst p; constructor; constructor.
  - inversion R; subst.
    match goal with
    | J1 : join_entry _ _ _ |- _ => inversion J1; subst
    end.
    all: match goal with T : raised_type _ _ |- _ => inversion T; subst end.
    all: match goal with F : raised_flag _ _ |- _ => inversion F; subst end.
    all: repeat match goal with F : flag_plus _ _ _ |- _ => inversion F; subst; clear F end.
    all: simpl; repeat split; try (constructor; assumption); try (constructor; constructor; eassumption); try solve [repeat constructor].
    all: try solve [apply join_some; apply join_linear; [constructor|assumption]].
    all: eapply raised_one; [constructor|apply raised_un; assumption].
Qed.

Local Lemma raised_join m E E1 E2 D :
  raised_env m E D -> join_env E1 E2 E ->
  exists D1 D2, raised_env m E1 D1 /\ raised_env m E2 D2 /\ join_env D1 D2 D.
Proof.
  intros R J.
  exists (fun k => lift_under true (E k) (D k) (E1 k)).
  exists (fun k => lift_under false (E k) (D k) (E2 k)).
  repeat split; intro k; destruct (raised_join_entry _ _ _ _ _ _ (J k) (R k)) as [? [? ?]]; assumption.
Qed.

Local Lemma raised_updates E D m k f t u :
  raised_env m E D -> raised_type t u ->
  raised_env m (set E k f t) (set D k f u).
Proof.
  intros R H x. unfold set, update. destruct (pair_eq x k); auto. constructor; [constructor|assumption].
Qed.

Local Lemma raised_source_ext m E D E' :
  raised_env m E D -> (forall k, E k = E' k) -> raised_env m E' D.
Proof. intros R EQ k; rewrite <- EQ; auto. Qed.

Local Lemma raised_un_port m E D a p ph t :
  raised_env m E D -> E a = Some (vis,Chan un p t) ->
  (p = io \/ p = ph) -> ph <> empty -> ph <> io ->
  exists q, D a = Some (vis,Chan un q t) /\ (q = io \/ q = ph).
Proof.
  intros A V P N1 N2.
  assert (C : consumes E a (Chan un ph t) (set E a vis (Chan un p t)))
    by (econstructor; eauto using remove_un_port).
  destruct (raised_consumes _ _ _ _ _ _ A C) as [D' [K L]].
  apply consumes_shape in K as [s [r [J [R _]]]].
  pose proof (proj1 (proj2 R)) as PP. inversion PP; subst.
  eexists. split; [exact J|].
  destruct (consume_port _ _ _ _ _ R eq_refl N1 N2) as [Q _]. exact Q.
Qed.

Local Lemma raised_preserves m E p :
  mtyped m E p -> forall D, raised_env m E D -> mtyped m D p.
Proof.
  intros T. induction T; intros D A.
  - apply mt_zero. intros k f u V.
    eapply (raised_consistent m E D (fun _ => True)); eauto.
  - destruct (raised_hidden _ _ _ _ _ A H) as [v [V R]].
    eapply mt_nu; eauto using raised_updates.
  - destruct (raised_join _ _ _ _ _ A H) as [D1 [D2 [A1 [A2 J]]]].
    apply mt_par with (E1:=D1) (E2:=D2); eauto.
  - assert (C1 : consumes E a (Chan lin out t) (set E a vis r)) by (econstructor; eauto).
    assert (N : b <> a) by (intro C; symmetry in C; eapply out_distinct; eassumption).
    assert (C2 : consumes (set E a vis r) b t (set (set E a vis r) b vis u)).
    { econstructor; [unfold set; rewrite update_neq; eassumption|exact H2]. }
    destruct (raised_consumes _ _ _ _ _ _ A C1) as [D1 [R1 A1]].
    destruct (raised_consumes _ _ _ _ _ _ A1 C2) as [D2 [R2 A2]].
    eapply consumes_out_intro; eauto.
  - assert (C1 : consumes E a (Chan un out t) (set E a vis (Chan un p t))).
    { econstructor; [eassumption|apply remove_un_port; tauto || discriminate]. }
    assert (C2 : consumes (set E a vis (Chan un p t)) b t (set (set E a vis (Chan un p t)) b vis u)).
    { econstructor; [rewrite set_same; eassumption|exact H2]. }
    destruct (raised_consumes _ _ _ _ _ _ A C1) as [D1 [R1 A1]].
    destruct (raised_consumes _ _ _ _ _ _ A1 C2) as [D2 [R2 A2]].
    eapply consumes_out_intro; [exact R1|exact R2|].
    apply IHT. eapply raised_source_ext; [exact A2|].
    unfold set at 1 3. unfold update at 1 2. intro k.
    destruct (pair_eq k b); [reflexivity|apply set_same; assumption].
  - assert (C : consumes E a (Chan lin inp t) (set E a vis r)) by (econstructor; eauto).
    destruct (raised_consumes _ _ _ _ _ _ A C) as [D1 [R A1]].
    eapply consumes_in_intro; eauto using raised_empty, raised_copy.
  - assert (C : consumes E a (Chan un inp t) (set E a vis (Chan un p t))).
    { econstructor; [eassumption|apply remove_un_port; tauto || discriminate]. }
    destruct (raised_consumes _ _ _ _ _ _ A C) as [D1 [R A1]].
    eapply consumes_in_intro; [exact R|eapply raised_empty; eassumption|assumption|].
    apply IHT. eapply raised_source_ext; [eapply raised_copy; eauto|].
    unfold set at 1 3. unfold update at 1 2. intro k.
    destruct (pair_eq k b); [reflexivity|apply set_same; assumption].
  - destruct (raised_un_port _ _ _ _ _ inp _ A H H2 ltac:(discriminate) ltac:(discriminate))
      as [v [V P]].
    eapply mt_bang; eauto using raised_copy, raised_empty.
    unfold nonhidden_cons in *. eapply raised_consistent; eauto.
    intros f1 f2 RF NF. inversion RF; subst; congruence.
Qed.

Local Lemma transfer_payload m E x b f t u r q :
  E x = None ->
  E b = Some (f,u) ->
  f <> hid -> type_plus u t r ->
  mtyped m (set E x vis t) q ->
  mtyped m (set E b vis r) (replace_refs q x b).
Proof.
  intros F B FH P C.
  assert (N : x <> b) by (intros <-; congruence).
  eapply aliases_preserve; [exact C|].
  eapply aliases_intro with (t:=t) (u:=u) (f:=f); eauto using type_plus_comm.
  - unfold set; apply update_eq.
  - unfold set; rewrite update_neq by congruence; exact B.
  - intro k. unfold set,dropped,update. destruct (pair_eq k b); auto.
    destruct (pair_eq k x) eqn:K; auto. apply pair_eq_true in K. now subst.
Qed.

Local Definition flag_cup f g :=
  match f, g with hid,_ | _,hid => hid | vis,vis => vis | _,_ => ill end.

Local Definition t_cup t u :=
  match t,u with
  | Chan m p s, Chan _ q _ => Chan m (pol_cup p q) s
  | _,_ => Top
  end.

Local Definition o_cup (v w : option entry) :=
  match v,w with
  | Some (f,t), Some (g,u) => Some (flag_cup f g, t_cup t u)
  | _,_ => None
  end.

Local Definition e_cup (E F : env) : env := fun k => o_cup (E k) (F k).

Local Lemma flag_associate a b c ab abc :
  flag_plus a b ab -> flag_plus ab c abc ->
  flag_plus b c (flag_cup b c) /\ flag_plus a (flag_cup b c) abc.
Proof. intros S T. inversion S; subst; inversion T; subst; simpl; split; constructor. Qed.

Local Lemma pol_associate a b c ab abc :
  pol_plus a b ab -> pol_plus ab c abc ->
  pol_plus b c (pol_cup b c) /\ pol_plus a (pol_cup b c) abc.
Proof.
  intros S T. inversion S; subst; inversion T; subst;
    repeat match goal with p : pol |- _ => destruct p end;
    simpl; split; constructor.
Qed.

Local Lemma cup_id p : pol_cup p p = p.
Proof. destruct p; reflexivity. Qed.

Local Lemma entry_associate a b c ab abc :
  join_entry a b ab -> join_entry ab c abc ->
  join_option (Some b) (Some c) (o_cup (Some b) (Some c)) /\
  join_option (Some a) (o_cup (Some b) (Some c)) (Some abc).
Proof.
  intros S T. inversion S; subst; inversion T; subst; simpl.
  all: match goal with A : flag_plus ?f ?g ?h, B : flag_plus ?h ?i ?j |- _ =>
    destruct (flag_associate _ _ _ _ _ A B) as [F1 F2] end.
  - repeat split; constructor; constructor; assumption.
  - match goal with A : pol_plus ?f ?g ?h, B : pol_plus ?h ?i ?j |- _ =>
      destruct (pol_associate _ _ _ _ _ A B) as [P1 P2] end.
    repeat split; constructor; constructor; assumption.
  - rewrite cup_id. repeat split; constructor; constructor; assumption.
Qed.

Local Lemma option_associate a b c ab abc :
  join_option a b ab -> join_option ab c abc ->
  join_option b c (o_cup b c) /\ join_option a (o_cup b c) abc.
Proof.
  intros J1 J2. destruct J1; inversion J2; subst.
  - simpl. split; constructor.
  - eapply entry_associate; eassumption.
Qed.

Local Lemma join_associate A B C AB ABC :
  join_env A B AB -> join_env AB C ABC ->
  join_env B C (e_cup B C) /\ join_env A (e_cup B C) ABC.
Proof.
  intros J1 J2. split; intro k; unfold e_cup;
    destruct (option_associate _ _ _ _ _ (J1 k) (J2 k)); assumption.
Qed.

Local Lemma join_comm_env A B C : join_env A B C -> join_env B A C.
Proof.
  intros J k. specialize (J k). inversion J; subst; constructor.
  match goal with J' : join_entry _ _ _ |- _ => inversion J'; subst end.
  all: constructor; lazymatch goal with
       | |- flag_plus _ _ _ => match goal with H : flag_plus _ _ _ |- _ => inversion H; subst; constructor end
       | |- pol_plus _ _ _ => match goal with H : pol_plus _ _ _ |- _ => inversion H; subst; constructor end
       end.
Qed.

Local Lemma join_reverse_associate A B C BC ABC :
  join_env B C BC -> join_env A BC ABC ->
  join_env A B (e_cup B A) /\ join_env (e_cup B A) C ABC.
Proof.
  intros JB JA. apply join_comm_env in JB,JA.
  destruct (join_associate _ _ _ _ _ JB JA) as [J1 J2].
  split; now apply join_comm_env.
Qed.

Local Definition empty_part t :=
  match t with Chan lin _ u => Chan lin empty u | _ => t end.

Local Definition neutral (E : env) : env := fun k =>
  match E k with
  | None => None
  | Some (f,t) => Some (match f with hid => ill | _ => f end, empty_part t)
  end.

Local Lemma neutral_join E : join_env E (neutral E) E.
Proof.
  intros k. unfold neutral. destruct (E k) as [[f [[|] p t|]]|]; [| | |apply join_none];
    destruct f; apply join_some; constructor; constructor.
Qed.

Local Lemma join_hidden_left A B C k t :
  join_env A B C -> A k = Some (hid,t) ->
  exists u v, B k = Some (ill,u) /\ C k = Some (hid,v).
Proof.
  intros J A0. specialize (J k). rewrite A0 in J.
  inversion J; subst.
  match goal with H : join_entry _ _ _ |- _ => inversion H; subst end.
  all: match goal with H : flag_plus hid _ _ |- _ => inversion H; subst; eauto end.
Qed.

Local Lemma no_dup_append {A} (xs ys : list A) :
  NoDup xs -> NoDup ys ->
  (forall x, In x xs -> ~ In x ys) ->
  NoDup (xs ++ ys).
Proof.
  intros X Y D. induction X; cbn; auto. constructor.
  - rewrite in_app_iff. intros [I|I]; auto. eapply D; [left; reflexivity|assumption].
  - apply IHX. intros y I. apply D. right; assumption.
Qed.

Local Lemma scoped_restrictions m E p :
  mtyped m E p ->
  NoDup (secLabs p) /\ forall k, In k (secLabs p) -> exists t, E k = Some (hid,t).
Proof.
  intros T. induction T.
  all: try solve [
    destruct IHT as [ND R]; split; [exact ND|];
    intros j I; destruct (R j I) as [v S]; exists v;
    unfold set, update in S;
    repeat match type of S with
           | context [if ?b then _ else _] => destruct b; [discriminate|]
           end; exact S].
  - split; [constructor|contradiction].
  - destruct IHT as [ND Scope]. split; simpl.
    + apply no_dup_append; auto.
      * repeat constructor. intros [].
      * intros j I. specialize (Scope j I) as [s S].
        intros [J|[]]. assert (K : k = j) by (destruct k; exact J). rewrite <- K in S.
        unfold set in S. rewrite update_eq in S. discriminate.
    + intros j I. apply in_app_iff in I as [I|I].
      * destruct (Scope j I) as [s S].
        assert (N : j <> k) by (intros <-; unfold set in S; rewrite update_eq in S; discriminate).
        exists s. unfold set in S. now rewrite update_neq in S.
      * destruct I as [I|[]]. destruct k; simpl in I; subst; eauto.
  - destruct IHT1 as [N1 C1]. destruct IHT2 as [N2 C2]. split; simpl.
    + apply no_dup_append; auto.
      intros j I J. destruct (C1 j J) as [s S]. destruct (C2 j I) as [u U].
      destruct (join_hidden_left _ _ _ _ _ H S) as [v [w [V W]]].
      rewrite V in U. discriminate.
    + intros j I. apply in_app_iff in I as [I|I].
      * destruct (C2 j I) as [u U].
        destruct (join_hidden_left _ _ _ _ _ (join_comm_env _ _ _ H) U) as [v [w [V W]]]. eauto.
      * destruct (C1 j I) as [s S].
        destruct (join_hidden_left _ _ _ _ _ H S) as [v [w [V W]]]. eauto.

Qed.

Local Definition frame_safe p (F : env) :=
  forall k f t, In k (secLabs p) -> F k = Some (f,t) -> discardable t.

Local Lemma discardable_sum u v w :
  join_entry u v w -> discardable (snd u) -> discardable (snd v) -> discardable (snd w).
Proof.
  intros J. destruct J; simpl; auto. intros -> ->. inversion H0; reflexivity.
Qed.

Local Lemma sibling_frame m A B E F p q :
  mtyped m A p -> mtyped m B q -> join_env A B E ->
  join_env B F (e_cup B F) ->
  frame_safe p F -> frame_safe p (e_cup B F).
Proof.
  intros X Y J BF Safe k f t I K.
  destruct (scoped_restrictions _ _ _ X) as [_ H].
  destruct (H k I) as [u A0].
  destruct (join_hidden_left _ _ _ _ _ J A0) as [v [w [B0 _]]].
  pose proof (BF k) as BFK. rewrite B0, K in BFK.
  inversion BFK; subst.
  match goal with J0 : join_entry (ill,v) ?fe (f,t), E0 : Some ?fe = F k |- _ =>
    destruct fe as [ff ft];
    eapply (discardable_sum (ill,v) (ff,ft) (f,t)); [exact J0| |];
    simpl;
    [eapply unused_linear; eauto|eapply (Safe k ff); eauto]
  end.
Qed.

(* Track the typing of the active process and the permissions retained
   by its surrounding parallel context. *)
Local Definition frame_transform m (G G' : env) p p' :=
  forall A F, sl_pos p -> mtyped m A p ->
  join_env A F G -> frame_safe p F ->
  exists A' F', mtyped m A' p' /\ raised_env m F F' /\ join_env A' F' G'.

Local Lemma sl_pos_par_left p q : sl_pos (dPar p q) -> sl_pos p.
Proof. intros V x y I; apply (V x y); simpl; apply in_app_iff; auto. Qed.

Local Lemma sl_pos_par_right p q : sl_pos (dPar p q) -> sl_pos q.
Proof. intros V x y I; apply (V x y); simpl; apply in_app_iff; auto. Qed.

Local Lemma frame_safe_par_left p q F : frame_safe (dPar p q) F -> frame_safe p F.
Proof. intros S k f t I V; eapply (S k f); [simpl; apply in_app_iff; auto|exact V]. Qed.

Local Lemma frame_safe_par_right p q F : frame_safe (dPar p q) F -> frame_safe q F.
Proof. intros S k f t I V; eapply (S k f); [simpl; apply in_app_iff; auto|exact V]. Qed.

Local Lemma frames_par_left m G G' p p' q :
  frame_transform m G G' p p' ->
  frame_transform m G G' (dPar p q) (dPar p' q).
Proof.
  intros U E F Pos T J Safety. inversion T; subst.
  match goal with C : join_env ?A ?B E, TA : mtyped m ?A p, TB : mtyped m ?B q |- _ =>
    let JB := fresh "JB" in let K := fresh "K" in
    destruct (join_associate _ _ _ _ _ C J) as [JB K];
    let Safe := fresh "Safe" in
    assert (Safe : frame_safe p (e_cup B F)) by
      (eapply sibling_frame; eauto using frame_safe_par_left);
    destruct (U A _ (sl_pos_par_left _ _ Pos) TA K Safe) as [A' [BF' [TA' [Raise UJ]]]];
    destruct (raised_join _ _ _ _ _ Raise JB) as [B' [F' [RB [RF BF]]]];
    destruct (join_reverse_associate _ _ _ _ _ BF UJ) as [J1 J2];
    exists (e_cup B' A'), F'; split; [eapply mt_par; eauto using raised_preserves|eauto]
  end.
Qed.

Local Lemma frames_par_right m G G' p p' q :
  frame_transform m G G' p p' ->
  frame_transform m G G' (dPar q p) (dPar q p').
Proof.
  intros U E F Pos T J Safety. inversion T; subst.
  match goal with C : join_env ?B ?A E, TA : mtyped m ?A p, TB : mtyped m ?B q |- _ =>
    let CA := fresh "CA" in pose proof (join_comm_env _ _ _ C) as CA;
    let JB := fresh "JB" in let K := fresh "K" in
    destruct (join_associate _ _ _ _ _ CA J) as [JB K];
    let Safe := fresh "Safe" in
    assert (Safe : frame_safe p (e_cup B F)) by
      (eapply sibling_frame; eauto using frame_safe_par_right);
    destruct (U A _ (sl_pos_par_right _ _ Pos) TA K Safe) as [A' [BF' [TA' [Raise UJ]]]];
    destruct (raised_join _ _ _ _ _ Raise JB) as [B' [F' [RB [RF BF]]]];
    destruct (join_reverse_associate _ _ _ _ _ BF UJ) as [J1 J2];
    exists (e_cup B' A'), F'; split; [eapply mt_par with (E1:=B') (E2:=A'); eauto using raised_preserves, join_comm_env|eauto]
  end.
Qed.

Local Lemma raised_type_trans a b c : raised_type a b -> raised_type b c -> raised_type a c.
Proof.
  intros A B. inversion A; subst; auto. inversion B; subst; auto.
  apply raised_un. repeat match goal with H : type_sub _ _ |- _ => inversion H; clear H; subst end; constructor.
Qed.

Local Lemma raised_flag_trans a b c : raised_flag a b -> raised_flag b c -> raised_flag a c.
Proof. intros A B. destruct A; auto. inversion B; subst; constructor. Qed.

Local Lemma raised_trans m A B C :
  raised_env m A B -> raised_env m B C -> raised_env m A C.
Proof.
  intros P Q k. specialize (P k). specialize (Q k). destruct P; auto.
  all: inversion Q; subst.
  - apply raised_fresh; auto.
    + inversion H5; subst; [assumption|discriminate].
    + eapply raised_discardable; eassumption.
  - constructor; eauto using raised_flag_trans, raised_type_trans.
Qed.

Local Lemma join_at G A F k f t :
  join_env A F G -> G k = Some (f,t) ->
  exists a b, A k = Some a /\ F k = Some b /\ join_entry a b (f,t).
Proof.
  intros J V. specialize (J k). rewrite V in J. inversion J; subst; eauto.
Qed.

Local Lemma join_vis G A F k t :
  join_env A F G -> G k = Some (vis,t) ->
  exists s u, A k = Some (vis,s) /\ F k = Some (vis,u) /\
    join_entry (vis,s) (vis,u) (vis,t).
Proof.
  intros J V. destruct (join_at _ _ _ _ _ _ J V) as [a [b [A0 [B0 K]]]].
  inversion K; subst;
    match goal with F : flag_plus _ _ vis |- _ => inversion F; subst; eauto end.
Qed.

Local Lemma join_entry_reflag f1 f2 f s u t g1 g2 g :
  join_entry (f1,s) (f2,u) (f,t) ->
  flag_plus g1 g2 g ->
  join_entry (g1,s) (g2,u) (g,t).
Proof. intros J F. inversion J; subst; constructor; auto. Qed.

Local Lemma join_change G A F k f1 f2 f s1 s2 s g1 g2 g :
  join_env A F G -> join_entry (f1,s1) (f2,s2) (f,s) ->
  flag_plus g1 g2 g ->
  join_env (set A k g1 s1) (set F k g2 s2) (set G k g s).
Proof. intros J K P. apply join_set; auto. constructor; eapply join_entry_reflag; eauto. Qed.

Local Lemma frame_ext m G GS G' GS' p p' :
  (forall k, G k = GS k) -> (forall k, G' k = GS' k) ->
  frame_transform m G G' p p' -> frame_transform m GS GS' p p'.
Proof.
  intros E1 E2 T A F Pos TA J Safe.
  assert (K : join_env A F G) by (intro k; now rewrite E1).
  destruct (T A F Pos TA K Safe) as [A' [F' [T' [R J']]]].
  exists A', F'. repeat split; auto. intro k; now rewrite <- E2.
Qed.

Local Lemma scope_body_pos k p : sl_pos (dNu (fst k) (snd k) p) -> sl_pos p.
Proof. intros P x y I; apply (P x y); simpl; apply in_app_iff; auto. Qed.

Local Lemma scope_frame_safe k m A F p t u :
  mtyped m (set A k vis t) p ->
  frame_safe (dNu (fst k) (snd k) p) F ->
  frame_safe p (set F k vis u).
Proof.
  intros T SF j f s I J.
  assert (N : j <> k).
  { intros <-. destruct (scoped_restrictions _ _ _ T) as [_ C].
    destruct (C j I) as [w W]. unfold set in W. rewrite update_eq in W; discriminate. }
  unfold set in J. rewrite update_neq in J by assumption.
  eapply (SF j f); [simpl; apply in_app_iff; auto|assumption].
Qed.

Local Lemma raised_reflag m A k t :
  A k = Some (ill,t) ->
  raised_env m A (set A k vis t).
Proof.
  intros H x. destruct (pair_eq x k) eqn:P.
  - apply pair_eq_true in P. subst. unfold set; rewrite update_eq, H. repeat constructor.
  - apply pair_eq_false in P. unfold set. rewrite update_neq by assumption.
    destruct (A x) as [[f t']|]; repeat constructor.
Qed.

Local Lemma frames_enter m G k t A F p :
  G k = Some (hid,t) ->
  mtyped m A (dNu (fst k) (snd k) p) ->
  join_env A F G ->
  frame_safe (dNu (fst k) (snd k) p) F ->
  exists s u, F k = Some (ill,u) /\
    mtyped m (set A k vis s) p /\
    join_env (set A k vis s) (set F k vis u) (set G k vis t) /\
    frame_safe p (set F k vis u).
Proof.
  intros GC T J Safe.
  inversion T; subst.
  match goal with
  | K : A ?j = Some (hid,?u), H : mtyped m (set A ?j vis ?u) p |- _ =>
    assert (E : j = k) by (destruct j,k; simpl in *; congruence); subst j
  end.
  destruct (join_hidden_left _ _ _ _ _ J H2) as [u [v [F0 V]]].
  pose proof (J k) as C. rewrite H2, F0, GC in C. inversion C; subst.
  exists t0, u. repeat split; auto.
  - eapply join_change; [exact J|eassumption|constructor].
  - eapply scope_frame_safe; eassumption.
Qed.

Local Lemma frames_open m G G' p p' k t :
  G k = Some (hid,t) ->
  frame_transform m (set G k vis t) G' p p' ->
  frame_transform m G G' (dNu (fst k) (snd k) p) p'.
Proof.
  intros GC U A F Pos T J Safe.
  destruct (frames_enter _ _ _ _ _ _ _ GC T J Safe) as [s [u [F0 [C [K S]]]]].
  destruct (U _ _ (scope_body_pos _ _ Pos) C K S) as [A' [F' [C' [R Q]]]].
  exists A', F'. repeat split; auto. eapply raised_trans; [eapply raised_reflag; eassumption|eassumption].
Qed.

Local Lemma frames_hide m G G' p p' k t t' :
  G k = Some (hid,t) -> G' k = Some (vis,t') ->
  frame_transform m (set G k vis t) G' p p' ->
  frame_transform m G (set G' k hid t') (dNu (fst k) (snd k) p) (dNu (fst k) (snd k) p').
Proof.
  intros GC G'C U A F Pos T J Safe.
  destruct (frames_enter _ _ _ _ _ _ _ GC T J Safe) as [s [u [F0 [C [K S]]]]].
  destruct (U _ _ (scope_body_pos _ _ Pos) C K S) as [A' [F' [C' [R Q]]]].
  destruct (join_vis _ _ _ _ _ Q G'C) as [v [w [X [Y V]]]].
  exists (set A' k hid v), (set F' k ill w). repeat split.
  - eapply mt_nu with (t:=v); [unfold set; apply update_eq|].
    eapply mtyped_ext; [exact C'|].
    intro j. unfold set, update. destruct (pair_eq j k) eqn:P; auto.
    apply pair_eq_true in P; subst; assumption.
  - intro j. destruct (pair_eq j k) eqn:P.
    + apply pair_eq_true in P. subst.
      specialize (R k). unfold set in *. rewrite update_eq, Y in R. rewrite update_eq, F0.
      inversion R; subst. constructor; [constructor|assumption].
    + apply pair_eq_false in P. specialize (R j).
      unfold set in *. rewrite update_neq in R |- * by assumption. exact R.
  - eapply join_change; eauto using Fp_hi.
Qed.

Local Lemma set_congr E D k f t :
  (forall x, E x = D x) -> forall x, set E k f t x = set D k f t x.
Proof. intros H x; unfold set, update; destruct (pair_eq x k); auto. Qed.

Local Lemma typed_out_inv m A a b q :
  mtyped m A (dOut (fst a) (snd a) (fst b) (snd b) q) ->
  exists md t A1 A2,
    consumes A a (Chan md out t) A1 /\ consumes A1 b t A2 /\ mtyped m A2 q.
Proof.
  intros T. inversion T; subst.
  all: match goal with
       | H1 : fst ?x = fst ?a, H2 : snd ?x = snd ?a,
         H3 : fst ?y = fst ?b, H4 : snd ?y = snd ?b |- _ =>
           assert (E1 : x = a) by (destruct x,a; simpl in *; congruence); subst x;
           assert (E2 : y = b) by (destruct y,b; simpl in *; congruence); subst y
       end.
  - do 4 eexists. split; [econstructor; eassumption|].
    split; [|eassumption]. econstructor; [|eassumption].
    unfold set. rewrite update_neq; [assumption|].
    intro F; symmetry in F; eapply out_distinct; eassumption.
  - exists un, t, (set A a vis (Chan un p t)), (set (set A a vis (Chan un p t)) b vis u).
    split; [econstructor; [eassumption|apply remove_un_port; tauto || discriminate]|].
    split.
    + econstructor; [rewrite set_same; eassumption|eassumption].
    + eapply mtyped_ext; [eassumption|].
      apply set_congr. intro k. symmetry. apply set_same; assumption.
Qed.

Local Lemma typed_in_inv m A a x q :
  mtyped m A (dInp (fst a) (snd a) (fst x) (snd x) q) ->
  exists md t A1,
    consumes A a (Chan md inp t) A1 /\ A1 x = None /\ mtyped m (set A1 x vis t) q.
Proof.
  intros T. inversion T; subst.
  all: match goal with
       | H1 : fst ?j = fst ?a, H2 : snd ?j = snd ?a,
         H3 : fst ?k = fst ?x, H4 : snd ?k = snd ?x |- _ =>
           assert (E1 : j = a) by (destruct j,a; simpl in *; congruence); subst j;
           assert (E2 : k = x) by (destruct k,x; simpl in *; congruence); subst k
       end.
  - do 3 eexists. split; [econstructor; eassumption|].
    split; [|eassumption]. unfold set. rewrite update_neq; [assumption|].
    intros <-. congruence.
  - exists un, t, (set A a vis (Chan un p t)).
    split; [econstructor; [eassumption|apply remove_un_port; tauto || discriminate]|].
    split.
    + rewrite set_same; assumption.
    + eapply mtyped_ext; [eassumption|].
      apply set_congr. intro k. symmetry. apply set_same; assumption.
Qed.

Local Lemma consumption_agrees G A F a md md' ph t t' G1 A1 :
  join_env A F G ->
  consumes G a (Chan md ph t) G1 ->
  consumes A a (Chan md' ph t') A1 ->
  md = md' /\ t = t'.
Proof.
  intros J C D. apply consumes_shape in C as [u [v [U [R1 _]]]].
  apply consumes_shape in D as [s [r [S [R2 _]]]].
  destruct (join_vis _ _ _ _ _ J U) as [s' [u' [W [Z P]]]].
  rewrite S in W. inversion W; subst.
  pose proof (proj1 (proj2 R1)) as RR1.
  pose proof (proj1 (proj2 R2)) as RR2.
  inversion RR1; subst; inversion RR2; subst; inversion P; subst; auto.
Qed.

Local Lemma join_removed f1 f2 f a b t r1 r w :
  join_entry (f1,a) (f2,b) (f,t) ->
  type_remove a w r1 -> type_remove t w r ->
  join_entry (f1,r1) (f2,b) (f,r).
Proof.
  intros J R1 R. inversion J; subst.
  - pose proof (proj1 (proj2 R1)) as X. inversion X; subst.
    pose proof (proj1 (proj2 R)) as Y. inversion Y; subst. constructor; assumption.
  - assert (P : type_plus (Chan lin p1 t0) (Chan lin p2 t0) (Chan lin p t0)) by (constructor; assumption).
    destruct (remove_add _ _ _ _ _ R1 P) as [res [R' P']].
    assert (res = r) by (eapply type_remove_unique; eassumption). subst.
    inversion P'; subst. constructor; assumption.
  - assert (r1 = Chan un p t0) by (apply (proj2 (proj2 R1)); unfold is_unrestricted; eauto).
    assert (r = Chan un p t0) by (apply (proj2 (proj2 R)); unfold is_unrestricted; eauto).
    subst. assumption.
Qed.

Local Lemma join_consumed G G' A A' F k w :
  join_env A F G -> consumes G k w G' -> consumes A k w A' ->
  join_env A' F G'.
Proof.
  intros J C D. apply consumes_shape in C as [t [r [V [R ->]]]].
  apply consumes_shape in D as [a [r1 [U [R1 ->]]]].
  destruct (join_vis _ _ _ _ _ J V) as [a' [b [X [Y K]]]].
  rewrite U in X. inversion X; subst.
  intro x. unfold set, update. destruct (pair_eq x k) eqn:E; auto.
  apply pair_eq_true in E; subst. rewrite Y. constructor. eapply join_removed; eassumption.
Qed.

Local Lemma pol_plus_comm a b c : pol_plus a b c -> pol_plus b a c.
Proof. intro P; inversion P; subst; constructor. Qed.

Local Lemma join_added f1 f2 f a b t w r :
  join_entry (f1,a) (f2,b) (f,t) -> f <> hid -> type_plus t w r ->
  exists a' b', f1 <> hid /\ raised_flag f2 vis /\
    type_plus a w a' /\ raised_type b b' /\ join_entry (vis,a') (vis,b') (vis,r).
Proof.
  intros J NF P.
  inversion J; subst.
  all: match goal with F : flag_plus _ _ _ |- _ => inversion F; subst; clear F end.
  all: try solve [contradiction].
  all: inversion P; subst.
  all: try solve [exists Top,Top; repeat split; try discriminate; repeat constructor].
  all: try solve [
    match goal with A : pol_plus ?p1 ?p2 ?p, B : pol_plus ?p ?p3 ?pr,
                    J : join_entry (_,Chan lin ?p1 ?s) _ _ |- _ =>
      destruct (pol_associate _ _ _ _ _ (pol_plus_comm _ _ _ A) B) as [C D];
      exists (Chan lin (pol_cup p1 p3) s), (Chan lin p2 s)
    end;
    repeat split; try discriminate;
    solve [constructor | apply Tp_LinPlus; exact C |
           apply join_linear; [constructor|apply pol_plus_comm; exact D]]].
  all: match goal with A : type_plus (Chan un ?p ?s) (Chan un ?q ?s) _ |- _ =>
    exists (Chan un (pol_cup p q) s), (Chan un (pol_cup p q) s)
  end.
  all: repeat split; try discriminate;
    solve [constructor | apply raised_un; destruct p,p2; cbn; constructor | apply join_un; constructor].
Qed.

Local Lemma frames_output m G G1 G2 a b md t q :
  consumes G a (Chan md out t) G1 ->
  consumes G1 b t G2 ->
  frame_transform m G G2 (dOut (fst a) (snd a) (fst b) (snd b) q) q.
Proof.
  intros R1 R2 A F P C J Safe.
  destruct (typed_out_inv _ _ _ _ _ C) as [md' [u [A1 [A2 [S1 [S2 T]]]]]].
  destruct (consumption_agrees _ _ _ _ _ _ _ _ _ _ _ J R1 S1) as [<- <-].
  exists A2, F. repeat split; auto.
  - intro k. destruct (F k) as [[f s]|]; repeat constructor.
  - eapply join_consumed; [eapply join_consumed; eassumption|eassumption|eassumption].
Qed.

Local Lemma frames_input m G G1 a b x md t f u r q :
  consumes G a (Chan md inp t) G1 ->
  G1 b = Some (f,u) -> f <> hid -> type_plus u t r ->
  frame_transform m G (set G1 b vis r)
    (dInp (fst a) (snd a) (fst x) (snd x) q) (replace_refs q x b).
Proof.
  intros C V NF P A F Pos TA J Safe.
  destruct (typed_in_inv _ _ _ _ _ TA) as [md' [w [A1 [S [Fresh T]]]]].
  destruct (consumption_agrees _ _ _ _ _ _ _ _ _ _ _ J C S) as [<- <-].
  pose proof (join_consumed _ _ _ _ _ _ _ J C S) as K.
  destruct (join_at _ _ _ _ _ _ K V) as [[fa ta] [[ff tf] [VA [VF E]]]].
  destruct (join_added _ _ _ _ _ _ _ _ E NF P) as [a' [b' [NA [RF [Plus [RT J']]]]]].
  exists (set A1 b vis a'), (set F b vis b').
  split; [eapply transfer_payload; eassumption|]. split.
  - intro k. unfold set, update. destruct (pair_eq k b) eqn:B.
    + apply pair_eq_true in B. subst. rewrite VF. constructor; assumption.
    + destruct (F k) as [[f0 s]|]; repeat constructor.
  - apply join_set; auto. constructor; assumption.
Qed.

Local Lemma raised_safe m p F F' :
  raised_env m F F' -> frame_safe p F -> frame_safe p F'.
Proof.
  intros R S k f t I K. specialize (R k). rewrite K in R.
  inversion R; subst; auto. eapply raised_discardable; [eassumption|eapply (S k); eauto].
Qed.

Local Lemma mtyped_par_swap m E p q :
  mtyped m E (dPar p q) -> mtyped m E (dPar q p).
Proof.
  intro T. inversion T; subst. eapply mt_par; [apply join_comm_env; eassumption|eassumption|eassumption].
Qed.

Local Lemma frames_swap_par m G G' p p' q q' :
  frame_transform m G G' (dPar p q) (dPar p' q') ->
  frame_transform m G G' (dPar q p) (dPar q' p').
Proof.
  intros U A F Pos C J Safe.
  assert (P : sl_pos (dPar p q)).
  { intros x y I. apply (Pos x y). simpl in *. apply in_app_iff in I. apply in_app_iff. tauto. }
  assert (S : frame_safe (dPar p q) F).
  { intros k f t I K. eapply (Safe k); [|eassumption].
    simpl in *. apply in_app_iff in I. apply in_app_iff. tauto. }
  destruct (U _ _ P (mtyped_par_swap _ _ _ _ C) J S) as [D [F' [T [R V]]]].
  exists D, F'. repeat split; auto using mtyped_par_swap.
Qed.

Local Lemma frames_com m G G1 G' p p' q q' :
  frame_transform m G G1 p p' -> frame_transform m G1 G' q q' ->
  frame_transform m G G' (dPar p q) (dPar p' q').
Proof.
  intros Out In A F Pos T J Safe. inversion T; subst.
  lazymatch goal with C : join_env ?P ?Q A, TP : mtyped m ?P p, TQ : mtyped m ?Q q |- _ =>
    destruct (join_associate _ _ _ _ _ C J) as [JQF JP];
    assert (SP : frame_safe p (e_cup Q F)) by
      (eapply sibling_frame; eauto using frame_safe_par_left);
    destruct (Out _ _ (sl_pos_par_left _ _ Pos) TP JP SP) as [P' [QF' [TP' [Raise Jout]]]];
    destruct (raised_join _ _ _ _ _ Raise JQF) as [Q1 [F1 [RQ [RF JQF']]]];
    assert (TQ1 : mtyped m Q1 q) by (eapply raised_preserves; eassumption)
  end.
  destruct (join_reverse_associate _ _ _ _ _ JQF' Jout) as [J1 J2].
  apply join_comm_env in J1.
  destruct (join_associate _ _ _ _ _ J1 J2) as [JP'F1 JQ1].
  assert (SQ : frame_safe q (e_cup P' F1)).
  { eapply sibling_frame; eauto.
    eapply raised_safe; [eassumption|eapply frame_safe_par_right; eassumption]. }
  destruct (In _ _ (sl_pos_par_right _ _ Pos) TQ1 JQ1 SQ) as [Q' [P'F' [TQ' [RP'F' Jin]]]].
  destruct (raised_join _ _ _ _ _ RP'F' JP'F1) as [P'' [F' [RP [RF' JPF]]]].
  destruct (join_reverse_associate _ _ _ _ _ JPF Jin) as [J3 J4].
  exists (e_cup P'' Q'), F'. repeat split.
  - eapply mt_par; [apply join_comm_env; exact J3|eapply raised_preserves; eassumption|exact TQ'].
  - eapply raised_trans; eassumption.
  - exact J4.
Qed.

(* Relabel a replicated body by exchanging its restriction names with
   fresh names above the source bound. *)
Local Definition mentions (p : dproc) :=
  let fix loop p :=
    match p with
    | dZero => []
    | dNu a b q | dInp a b _ _ q | dBang a b _ _ q => (a,b) :: loop q
    | dOut a b c d q => (a,b) :: (c,d) :: loop q
    | dPar q r => loop q ++ loop r
    end
  in loop p.

Local Fixpoint rename_refs (r : key -> key) (p : dproc) : dproc :=
  match p with
  | dZero => dZero
  | dNu a b q =>
      dNu (fst (r (a,b))) (snd (r (a,b))) (rename_refs r q)
  | dInp a b c d q =>
      dInp (fst (r (a,b))) (snd (r (a,b))) c d (rename_refs r q)
  | dBang a b c d q =>
      dBang (fst (r (a,b))) (snd (r (a,b))) c d (rename_refs r q)
  | dOut a b c d q =>
      dOut (fst (r (a,b))) (snd (r (a,b)))
        (fst (r (c,d))) (snd (r (c,d))) (rename_refs r q)
  | dPar q r' => dPar (rename_refs r q) (rename_refs r r')
  end.

Local Lemma rename_agrees p r s :
  (forall k, In k (mentions p) -> r k = s k) ->
  rename_refs r p = rename_refs s p.
Proof.
  induction p; simpl; intros H; try reflexivity.
  all: try solve [f_equal; [apply IHp1|apply IHp2]; intros k K; apply H, in_app_iff; auto].
  all: rewrite (H (_,_) (or_introl eq_refl));
    try rewrite (H (_,_) (or_intror (or_introl eq_refl)));
    f_equal; apply IHp; intros k K; apply H; auto.
Qed.

Local Lemma rename_compose p r s :
  rename_refs r (rename_refs s p) = rename_refs (fun k => r (s k)) p.
Proof.
  induction p; simpl; try rewrite IHp; try rewrite IHp1, IHp2;
    repeat match goal with |- context [(fst ?k, snd ?k)] =>
      replace (fst k, snd k) with k by (destruct k; reflexivity)
    end; reflexivity.
Qed.

Local Lemma rename_set (r : key -> key) E k f t :
  (forall x, r (r x) = x) ->
  forall j, set E k f t (r j) = set (fun x => E (r x)) (r k) f t j.
Proof.
  intros Inv j. unfold set, update.
  destruct (pair_eq (r j) k) eqn:P, (pair_eq j (r k)) eqn:Q; auto.
  - apply pair_eq_true in P; apply pair_eq_false in Q. apply (f_equal r) in P.
    rewrite Inv in P; contradiction.
  - apply pair_eq_false in P; apply pair_eq_true in Q. subst. rewrite Inv in P; contradiction.
Qed.

Local Lemma renamed_typing m E p (r : key -> key) :
  mtyped m E p ->
  (forall x, r (r x) = x) ->
  (forall k, In k (bv p) -> r k = k) ->
  mtyped m (fun x => E (r x)) (rename_refs r p).
Proof.
  intros T R BV. induction T; simpl in *.
  all: repeat match goal with |- context [(fst ?k, snd ?k)] =>
      replace (fst k, snd k) with k by (destruct k; reflexivity)
    end.
  - constructor. intros k f t K. eapply (H (r k)); eassumption.
  - eapply mt_nu with (t:=t); [now rewrite R|].
    eapply mtyped_ext; [apply IHT; exact BV|apply rename_set; exact R].
  - eapply mt_par with (E1:=fun k => E1 (r k)) (E2:=fun k => E2 (r k)).
    + intro k. apply H.
    + apply IHT1. intros k K. apply BV, in_app_iff; auto.
    + apply IHT2. intros k K. apply BV, in_app_iff; auto.
  - eapply mt_out_lin with (p:=p) (t:=t) (s:=s) (r:=r0) (u:=u); try assumption;
      try (now rewrite R).
    eapply mtyped_ext; [apply IHT; exact BV|].
    intro j. cbn beta. rewrite rename_set by assumption. apply set_congr. apply rename_set; assumption.
  - eapply mt_out_un with (p:=p) (t:=t) (s:=s) (u:=u); try assumption; try (now rewrite R).
    eapply mtyped_ext; [apply IHT; exact BV|apply rename_set; assumption].
  - assert (B : r b = b) by (apply BV; left; destruct b; reflexivity).
    eapply mt_in_lin with (p:=p) (t:=t) (r:=r0); try assumption; try (now rewrite R); try (now rewrite B).
    eapply mtyped_ext; [apply IHT; intros j K; apply BV; right; exact K|].
    intro j. cbn beta. rewrite rename_set by assumption. rewrite B. apply set_congr. apply rename_set; assumption.
  - assert (B : r b = b) by (apply BV; left; destruct b; reflexivity).
    eapply mt_in_un with (p:=p) (t:=t); try assumption; try (now rewrite R); try (now rewrite B).
    eapply mtyped_ext; [apply IHT; intros j K; apply BV; right; exact K|].
    intro j. cbn beta. rewrite rename_set by assumption. now rewrite B.
  - assert (B : r b = b) by (apply BV; left; destruct b; reflexivity).
    eapply mt_bang with (p:=p) (t:=t); try assumption; try (now rewrite R); try (now rewrite B).
    + intros k f s V NF. eapply (H3 (r k)); eassumption.
    + eapply mtyped_ext; [apply IHT; intros j K; apply BV; right; exact K|].
      intro j. cbn beta. rewrite rename_set by assumption. now rewrite B.
Qed.

Local Lemma none_set E k f t j :
  set E k f t j = None -> E j = None.
Proof. unfold set, update. destruct (pair_eq j k); congruence. Qed.

Local Lemma join_none_left A B E k : join_env A B E -> A k = None -> E k = None.
Proof. intros H K. specialize (H k). rewrite K in H. inversion H; reflexivity. Qed.

Local Lemma binders_fresh m E p :
  mtyped m E p ->
  forall k, In k (bv p) -> E k = None /\ snd k < m.
Proof.
  intros T. induction T; intros j I; simpl in I; try contradiction.
  - specialize (IHT j I) as [V B]. split; eauto using none_set.
  - apply in_app_iff in I as [I|I].
    + specialize (IHT1 j I) as [V B]. split; eauto using join_none_left.
    + specialize (IHT2 j I) as [V B]. split; eauto using join_none_left, join_comm_env.
  - specialize (IHT j I) as [V B]. split; eauto using none_set.
  - specialize (IHT j I) as [V B]. split; eauto using none_set.
  - destruct I as [V|I].
    + destruct b; simpl in V; subst; auto.
    + specialize (IHT j I) as [V B]. split; eauto using none_set.
  - destruct I as [V|I].
    + destruct b; simpl in V; subst; auto.
    + specialize (IHT j I) as [V B]. split; eauto using none_set.
  - destruct I as [V|I].
    + destruct b; simpl in V; subst; auto.
    + specialize (IHT j I) as [V B]. split; eauto using none_set.
Qed.

Local Lemma binder_not_here m E p k f t :
  mtyped m E p -> E k = Some (f,t) -> ~ In k (bv p).
Proof. intros T H I. destruct (binders_fresh _ _ _ T _ I); congruence. Qed.

Local Lemma binder_set_avoid m E p k f t D f' t' :
  mtyped m (set E k f t) p ->
  (forall j, In j (bv p) -> D j = None) ->
  forall j, In j (bv p) -> set D k f' t' j = None.
Proof.
  intros T H j I. unfold set. rewrite update_neq; auto.
  intros <-. eapply binder_not_here; [exact T|unfold set; apply update_eq|assumption].
Qed.

Local Lemma bound_set m E k f t :
  (forall j v, E j = Some v -> snd j <= m) -> snd k <= m ->
  forall j v, set E k f t j = Some v -> snd j <= m.
Proof.
  intros A B j v F. unfold set, update in F.
  destruct (pair_eq j k) eqn:P; eauto. apply pair_eq_true in P. congruence.
Qed.

Local Lemma bound_mentions m E p :
  mtyped m E p ->
  (forall j v, E j = Some v -> snd j <= m) ->
  forall j, In j (mentions p) -> snd j <= m.
Proof.
  intros T. induction T; intros B j I; simpl in I; try contradiction.
  all: try solve [
    destruct I as [I|I]; [destruct k; simpl in I; subst; eauto|];
    apply IHT; eauto using bound_set].
  all: try solve [
    destruct I as [I|I]; [destruct a; simpl in I; subst; eauto|];
    apply IHT; eauto using bound_set, Nat.lt_le_incl].
  - apply in_app_iff in I as [I|I].
    + apply IHT1; [|assumption].
      intros k v V.
      specialize (H k). rewrite V in H. inversion H; subst; eapply (B k); symmetry; eassumption.
    + apply IHT2; [|assumption].
      intros k v V.
      specialize (H k). rewrite V in H. inversion H; subst; eapply (B k); symmetry; eassumption.
  - destruct I as [I|[I|I]].
    + destruct a; simpl in I; subst; eauto.
    + destruct b; simpl in I; subst; eauto.
    + apply IHT; eauto using bound_set.
  - destruct I as [I|[I|I]].
    + destruct a; simpl in I; subst; eauto.
    + destruct b; simpl in I; subst; eauto.
    + apply IHT; eauto using bound_set.

Qed.

Local Lemma mentions_ill m E p :
  mtyped m E p ->
  forall k t, E k = Some (ill,t) -> ~ In k (mentions p).
Proof.
  intros T. induction T; intros j ty V I; simpl in I; try contradiction.
  all: try solve [
    destruct I as [I|I]; [destruct k; simpl in I; subst; congruence|];
    apply (IHT j ty); [unfold set; rewrite update_neq by (intros <-; congruence); exact V|exact I]].
  all: try solve [
    destruct I as [I|I]; [destruct a; simpl in I; subst; congruence|];
    apply (IHT j ty); [unfold set; rewrite !update_neq by (intros <-; congruence); exact V|exact I]].
  - destruct (join_at _ _ _ _ _ _ H V) as [[f1 t1] [[f2 t2] [A [B J]]]].
    inversion J; subst;
      repeat match goal with K : flag_plus _ _ ill |- _ => inversion K; clear K; subst end;
      apply in_app_iff in I as [I|I]; first [eapply (IHT1 j); eassumption | eapply (IHT2 j); eassumption].
  - destruct I as [I|[I|I]].
    + destruct a; simpl in I; subst; congruence.
    + destruct b; simpl in I; subst; congruence.
    + apply (IHT j ty); [unfold set; rewrite !update_neq by (intros <-; congruence); exact V|exact I].
  - destruct I as [I|[I|I]].
    + destruct a; simpl in I; subst; congruence.
    + destruct b; simpl in I; subst; congruence.
    + apply (IHT j ty); [unfold set; rewrite update_neq by (intros <-; congruence); exact V|exact I].

Qed.

Local Lemma In2_spec k l : In2 k l = true <-> In k l.
Proof.
  induction l as [|j l IH]; simpl; [firstorder discriminate|].
  destruct (pair_eq k j) eqn:E.
  - apply pair_eq_true in E. subst. tauto.
  - apply pair_eq_false in E. rewrite IH. intuition congruence.
Qed.

Local Lemma In2_no k l : In2 k l = false <-> ~ In k l.
Proof. rewrite <- In2_spec. destruct (In2 k l); intuition discriminate. Qed.

Local Definition shift_key m (k : key) : key := (fst k, snd k + m).
Local Definition unshift_key m (k : key) : key := (fst k, snd k - m).

Local Definition lab_forward m L k :=
  if In2 k L then shift_key m k else k.

Local Definition lab_swap m L (k : key) :=
  if m <? snd k then
    if In2 (unshift_key m k) L then unshift_key m k else k
  else lab_forward m L k.

Local Lemma shift_inverse m k : unshift_key m (shift_key m k) = k.
Proof. destruct k. unfold shift_key, unshift_key; simpl. f_equal; lia. Qed.

Local Lemma unshift_inverse m k : m <= snd k -> shift_key m (unshift_key m k) = k.
Proof. destruct k. unfold shift_key, unshift_key; simpl. intros. f_equal; lia. Qed.

Local Lemma shift_large m k : 0 < snd k -> m < snd (shift_key m k).
Proof. unfold shift_key; simpl; lia. Qed.

Local Lemma lab_swap_below m L k : snd k <= m -> lab_swap m L k = lab_forward m L k.
Proof. intros B. unfold lab_swap. rewrite (proj2 (Nat.ltb_ge _ _) B). reflexivity. Qed.

Local Lemma lab_swap_involutive m L :
  (forall k, In k L -> 0 < snd k <= m) ->
  forall k, lab_swap m L (lab_swap m L k) = k.
Proof.
  intros B k. unfold lab_swap at 2.
  destruct (m <? snd k) eqn:E.
  - destruct (In2 (unshift_key m k) L) eqn:U.
    + apply In2_spec in U as UI. apply Nat.ltb_lt in E.
      rewrite lab_swap_below by (specialize (B _ UI); lia).
      unfold lab_forward. rewrite U, unshift_inverse by lia. reflexivity.
    + unfold lab_swap. rewrite E,U. reflexivity.
  - unfold lab_forward. destruct (In2 k L) eqn:K.
    + apply In2_spec in K as KI. specialize (B _ KI).
      unfold lab_swap. rewrite (proj2 (Nat.ltb_lt _ _) (shift_large m k (proj1 B))).
      rewrite shift_inverse,K. reflexivity.
    + unfold lab_swap. rewrite E. unfold lab_forward. rewrite K. reflexivity.
Qed.

Local Lemma labs_rename_refs r p : secLabs (rename_refs r p) = map r (secLabs p).
Proof.
  induction p; simpl; auto.
  - rewrite IHp1, IHp2, map_app. reflexivity.
  - rewrite IHp, map_app. simpl. f_equal. destruct (r (n,n0)); reflexivity.
Qed.

Local Lemma replace_is_rename p a b :
  ~ In a (secLabs p) ->
  replace_refs p a b = rename_refs (moved a b) p.
Proof.
  induction p; intros N; simpl; try reflexivity.
  - match goal with |- _ = ?rhs => change (replace_refs (dBang (fst (n,n0)) (snd (n,n0)) (fst (n1,n2)) (snd (n1,n2)) p) a b = rhs) end.
    rewrite replace_bang, IHp by exact N. reflexivity.
  - match goal with |- _ = ?rhs => change (dPar (replace_refs p1 a b) (replace_refs p2 a b) = rhs) end.
    rewrite IHp1, IHp2; auto; intros I; apply N; simpl; apply in_app_iff; auto.
  - match goal with |- _ = ?rhs => change (dNu n n0 (replace_refs p a b) = rhs) end.
    unfold moved at 1 2. destruct (pair_eq (n,n0) a) eqn:E.
    + apply pair_eq_true in E. exfalso. apply N; simpl; apply in_app_iff; right; simpl; auto.
    + rewrite IHp; auto. intros I; apply N; simpl; apply in_app_iff; auto.
  - match goal with |- _ = ?rhs => change (replace_refs (dInp (fst (n,n0)) (snd (n,n0)) (fst (n1,n2)) (snd (n1,n2)) p) a b = rhs) end.
    rewrite replace_in, IHp by exact N. reflexivity.
  - match goal with |- _ = ?rhs => change (replace_refs (dOut (fst (n,n0)) (snd (n,n0)) (fst (n1,n2)) (snd (n1,n2)) p) a b = rhs) end.
    rewrite replace_out, IHp by exact N. reflexivity.
Qed.

Local Fixpoint relabel m p :=
  match p with
  | dZero => dZero
  | dPar p q => dPar (relabel m p) (relabel m q)
  | dNu a b q => dNu a (b+m) (replace_refs (relabel m q) (a,b) (a,b+m))
  | dOut a b c d q => dOut a b c d (relabel m q)
  | dInp a b c d q => dInp a b c d (relabel m q)
  | dBang a b c d q => dBang a b c d (relabel m q)
  end.

Local Lemma dep_relabel_view p L pf :
  dep_relabel p L pf = relabel (max L) p.
Proof. induction p; simpl; unfold replace_refs; simpl; congruence. Qed.

Local Lemma secLabs_relabel m p : secLabs (relabel m p) = map (shift_key m) (secLabs p).
Proof.
  assert (P : forall q a b, secLabs (replace_refs q a b) = secLabs q).
  { induction q; intros a b; unfold replace_refs in *; simpl;
      try rewrite IHq; try rewrite IHq1, IHq2; reflexivity. }
  induction p; simpl; auto.
  - rewrite IHp1, IHp2, map_app. reflexivity.
  - rewrite P, IHp, map_app. reflexivity.
Qed.

Local Lemma forward_append m L k :
  snd k <= m -> (forall j, In j L -> 0 < snd j) ->
  forall j, moved k (shift_key m k) (lab_forward m L j) =
    lab_forward m (L ++ [k]) j.
Proof.
  intros B Pos j. unfold lab_forward.
  destruct (In2 j L) eqn:J.
  - apply In2_spec in J as I.
    assert (E : In2 j (L ++ [k]) = true) by (apply In2_spec, in_app_iff; auto).
    rewrite E. unfold moved.
    rewrite (proj2 (pair_eq_false _ _)).
    + reflexivity.
    + assert (M := shift_large m j (Pos _ I)). intros K; rewrite K in M; lia.
  - apply In2_no in J.
    unfold moved. destruct (pair_eq j k) eqn:K.
    + apply pair_eq_true in K. subst.
      assert (I : In k (L ++ [k])) by (apply in_app_iff; right; now left).
      rewrite (proj2 (In2_spec _ _) I). reflexivity.
    + apply pair_eq_false in K.
      assert (I : ~ In j (L ++ [k])) by (rewrite in_app_iff; simpl; intuition congruence).
      rewrite (proj2 (In2_no _ _) I). reflexivity.
Qed.

Local Lemma forward_fixes m L k : ~ In k L -> lab_forward m L k = k.
Proof. intros I. unfold lab_forward. rewrite (proj2 (In2_no _ _) I). reflexivity. Qed.

Local Lemma forward_moves m L k : In k L -> lab_forward m L k = shift_key m k.
Proof. intros I. unfold lab_forward. rewrite (proj2 (In2_spec _ _) I). reflexivity. Qed.

Local Lemma scoped_visible m E p k t :
  mtyped m E p -> E k = Some (vis,t) -> ~ In k (secLabs p).
Proof.
  intros T H I. destruct (scoped_restrictions _ _ _ T) as [_ C].
  destruct (C k I) as [v V]. congruence.
Qed.

Local Lemma forward_par_l m E1 E2 E p q :
  mtyped m E2 q -> join_env E1 E2 E ->
  forall k, In k (mentions p) ->
  mtyped m E1 p ->
  lab_forward m (secLabs q ++ secLabs p) k = lab_forward m (secLabs p) k.
Proof.
  intros C J k I T.
  assert (N : ~ In k (secLabs q)).
  { intro Q. destruct (scoped_restrictions _ _ _ C) as [_ U].
    destruct (U k Q) as [t H].
    destruct (join_hidden_left _ _ _ _ _ (join_comm_env _ _ _ J) H) as [u [v [U1 _]]].
    eapply mentions_ill; [exact T|exact U1|exact I]. }
  destruct (In2 k (secLabs p)) eqn:P.
  - apply In2_spec in P. rewrite !forward_moves by (assumption || (apply in_app_iff; auto)); reflexivity.
  - apply In2_no in P. rewrite !forward_fixes by (assumption || (rewrite in_app_iff; tauto)); reflexivity.
Qed.

Local Lemma forward_par_r m E1 E2 E p q :
  mtyped m E1 p -> join_env E1 E2 E ->
  forall k, In k (mentions q) ->
  mtyped m E2 q ->
  lab_forward m (secLabs q ++ secLabs p) k = lab_forward m (secLabs q) k.
Proof.
  intros C J k I T.
  assert (N : ~ In k (secLabs p)).
  { intro Q. destruct (scoped_restrictions _ _ _ C) as [_ U].
    destruct (U k Q) as [t H].
    destruct (join_hidden_left _ _ _ _ _ J H) as [u [v [U1 _]]].
    eapply mentions_ill; [exact T|exact U1|exact I]. }
  destruct (In2 k (secLabs q)) eqn:P.
  - apply In2_spec in P. rewrite !forward_moves by (assumption || (apply in_app_iff; auto)); reflexivity.
  - apply In2_no in P. rewrite !forward_fixes by (assumption || (rewrite in_app_iff; tauto)); reflexivity.
Qed.

Local Lemma relabel_forward m E p :
  mtyped m E p -> sl_pos p ->
  (forall k, In k (secLabs p) -> snd k <= m) ->
  relabel m p = rename_refs (lab_forward m (secLabs p)) p.
Proof.
  intros T. induction T; intros Pos B.
  - reflexivity.
  - destruct k as [a b]; simpl in *.
    rewrite forward_moves with (k:=(a,b)) by (apply in_app_iff; right; now left).
    cbn [shift_key fst snd].
    assert (P : sl_pos q) by (apply (scope_body_pos (a,b)); exact Pos).
    assert (Bq : forall j, In j (secLabs q) -> snd j <= m).
    { intros j I. apply B, in_app_iff. auto. }
    assert (Positive : forall j, In j (secLabs q) -> 0 < snd j).
    { intros [x y] I; exact (P x y I). }
    rewrite IHT by assumption.
    rewrite replace_is_rename.
    + rewrite rename_compose. f_equal.
      apply rename_agrees. intros j I. apply forward_append; auto.
      apply B, in_app_iff. right; now left.
    + rewrite labs_rename_refs. intros I. apply in_map_iff in I as [j [J L]].
      rewrite forward_moves in J by assumption.
      pose proof (shift_large m j (Positive j L)) as Lg.
      assert (Bb : snd (a,b) <= m) by (apply B, in_app_iff; right; now left).
      rewrite J in Lg. lia.
  - simpl.
    rewrite (IHT1 (sl_pos_par_left _ _ Pos)), (IHT2 (sl_pos_par_right _ _ Pos))
      by (intros j I; apply B; simpl; apply in_app_iff; auto).
    f_equal; apply rename_agrees; intros j I; symmetry.
    + eapply forward_par_l; eassumption.
    + eapply forward_par_r; eassumption.
  - assert (C : mtyped m E (dOut (fst a) (snd a) (fst b) (snd b) q)) by (eapply mt_out_lin; eassumption).
    assert (Na : ~ In a (secLabs q)).
    { eapply scoped_visible with (p:=dOut (fst a) (snd a) (fst b) (snd b) q); eassumption. }
    assert (Nb : ~ In b (secLabs q)).
    { eapply scoped_visible with (p:=dOut (fst a) (snd a) (fst b) (snd b) q); eassumption. }
    destruct a, b; simpl in *. rewrite !forward_fixes by assumption.
    rewrite IHT by assumption. reflexivity.
  - assert (C : mtyped m E (dOut (fst a) (snd a) (fst b) (snd b) q)) by (eapply mt_out_un; eassumption).
    assert (Na : ~ In a (secLabs q)).
    { eapply scoped_visible with (p:=dOut (fst a) (snd a) (fst b) (snd b) q); eassumption. }
    assert (Nb : ~ In b (secLabs q)).
    { eapply scoped_visible with (p:=dOut (fst a) (snd a) (fst b) (snd b) q); eassumption. }
    destruct a, b; simpl in *. rewrite !forward_fixes by assumption.
    rewrite IHT by assumption. reflexivity.
  - assert (C : mtyped m E (dInp (fst a) (snd a) (fst b) (snd b) q)) by (eapply mt_in_lin; eassumption).
    assert (Na : ~ In a (secLabs q)).
    { eapply scoped_visible with (p:=dInp (fst a) (snd a) (fst b) (snd b) q); eassumption. }
    destruct a; simpl in *. rewrite !forward_fixes by assumption.
    rewrite IHT by assumption. reflexivity.
  - assert (C : mtyped m E (dInp (fst a) (snd a) (fst b) (snd b) q)) by (eapply mt_in_un; eassumption).
    assert (Na : ~ In a (secLabs q)).
    { eapply scoped_visible with (p:=dInp (fst a) (snd a) (fst b) (snd b) q); eassumption. }
    destruct a; simpl in *. rewrite !forward_fixes by assumption.
    rewrite IHT by assumption. reflexivity.
  - assert (C : mtyped m E (dBang (fst a) (snd a) (fst b) (snd b) q)) by (eapply mt_bang; eassumption).
    assert (Na : ~ In a (secLabs q)).
    { eapply scoped_visible with (p:=dBang (fst a) (snd a) (fst b) (snd b) q); eassumption. }
    destruct a; simpl in *. rewrite !forward_fixes by assumption.
    rewrite IHT by assumption. reflexivity.
Qed.

Local Lemma labs_bound m E p :
  mtyped m E p -> (forall j v, E j = Some v -> snd j <= m) ->
  forall j, In j (secLabs p) -> snd j <= m.
Proof.
  intros T B j I. destruct (scoped_restrictions _ _ _ T) as [_ R].
  destruct (R j I) as [s S]. eapply B; eassumption.
Qed.

Local Lemma typed_relabel m E p :
  mtyped m E p ->
  (forall j v, E j = Some v -> snd j <= m) ->
  sl_pos p ->
  mtyped m (fun j => E (lab_swap m (secLabs p) j)) (relabel m p).
Proof.
  intros C B P.
  pose proof (labs_bound _ _ _ C B) as S.
  assert (Range : forall k, In k (secLabs p) -> 0 < snd k <= m).
  { intros k I. split; [destruct k as [x y]; exact (P x y I)|auto]. }
  rewrite (relabel_forward _ _ _ C P S).
  replace (rename_refs (lab_forward m (secLabs p)) p) with
    (rename_refs (lab_swap m (secLabs p)) p).
  - apply renamed_typing; [exact C|auto using lab_swap_involutive|].
    intros k I. destruct (binders_fresh _ _ _ C _ I) as [N F].
    rewrite lab_swap_below by lia. apply forward_fixes. intro H.
    destruct (scoped_restrictions _ _ _ C) as [_ R].
    destruct (R k H) as [s V]. congruence.
  - apply rename_agrees. intros k I. apply lab_swap_below. eapply bound_mentions; eassumption.
Qed.

Local Lemma consumes_none E D k t j : consumes E k t D -> E j = None -> D j = None.
Proof.
  intros C H. apply consumes_shape in C as [s [u [B [_ ->]]]].
  unfold set. rewrite update_neq; auto. intros <-; congruence.
Qed.

Local Lemma raised_preserves_avoiding m n E p :
  mtyped m E p -> forall D, raised_env n E D ->
  (forall k, In k (bv p) -> D k = None) -> mtyped m D p.
Proof.
  intros T. induction T; intros D A Avoid.
  - apply mt_zero. intros k f u V.
    eapply (raised_consistent n E D (fun _ => True)); eauto.
  - destruct (raised_hidden _ _ _ _ _ A H) as [v [V R]].
    eapply mt_nu; eauto using raised_updates, binder_set_avoid.
  - destruct (raised_join _ _ _ _ _ A H) as [D1 [D2 [A1 [A2 J]]]].
    apply mt_par with (E1:=D1) (E2:=D2); auto.
    + apply IHT1; [assumption|].
      intros k I. specialize (J k). rewrite Avoid in J by (simpl; apply in_app_iff; auto).
      inversion J; reflexivity.
    + apply IHT2; [assumption|].
      intros k I. specialize (J k). rewrite Avoid in J by (simpl; apply in_app_iff; auto).
      inversion J; reflexivity.
  - assert (C1 : consumes E a (Chan lin out t) (set E a vis r)) by (econstructor; eauto).
    assert (N : b <> a) by (intro C; symmetry in C; eapply out_distinct; eassumption).
    assert (C2 : consumes (set E a vis r) b t (set (set E a vis r) b vis u)).
    { econstructor; [unfold set; rewrite update_neq; eassumption|exact H2]. }
    destruct (raised_consumes _ _ _ _ _ _ A C1) as [D1 [R1 A1]].
    destruct (raised_consumes _ _ _ _ _ _ A1 C2) as [D2 [R2 A2]].
    eapply consumes_out_intro; [exact R1|exact R2|].
    apply IHT; [assumption|].
    intros j I. eapply consumes_none; [exact R2|].
    eapply consumes_none; [exact R1|auto].
  - assert (C1 : consumes E a (Chan un out t) (set E a vis (Chan un p t))).
    { econstructor; [eassumption|apply remove_un_port; tauto || discriminate]. }
    assert (C2 : consumes (set E a vis (Chan un p t)) b t (set (set E a vis (Chan un p t)) b vis u)).
    { econstructor; [rewrite set_same; eassumption|exact H2]. }
    destruct (raised_consumes _ _ _ _ _ _ A C1) as [D1 [R1 A1]].
    destruct (raised_consumes _ _ _ _ _ _ A1 C2) as [D2 [R2 A2]].
    eapply consumes_out_intro; [exact R1|exact R2|].
    apply IHT.
    + eapply raised_source_ext; [exact A2|]. apply set_congr. apply set_same; assumption.
    + intros j I. eapply consumes_none; [exact R2|].
      eapply consumes_none; [exact R1|auto].
  - assert (C : consumes E a (Chan lin inp t) (set E a vis r)) by (econstructor; eauto).
    destruct (raised_consumes _ _ _ _ _ _ A C) as [D1 [R A1]].
    eapply consumes_in_intro; [exact R|apply Avoid; simpl; left; destruct b; reflexivity|assumption|].
    apply IHT; [apply raised_copy; assumption|].
    eapply binder_set_avoid; [exact T|].
    intros j I. eapply consumes_none; [exact R|apply Avoid; simpl; auto].
  - assert (C : consumes E a (Chan un inp t) (set E a vis (Chan un p t))).
    { econstructor; [eassumption|apply remove_un_port; tauto || discriminate]. }
    destruct (raised_consumes _ _ _ _ _ _ A C) as [D1 [R A1]].
    eapply consumes_in_intro; [exact R|apply Avoid; simpl; left; destruct b; reflexivity|assumption|].
    apply IHT.
    + eapply raised_source_ext; [eapply raised_copy; eauto|]. apply set_congr. apply set_same; assumption.
    + eapply binder_set_avoid; [exact T|].
      intros j I. eapply consumes_none; [exact R|apply Avoid; simpl; auto].
  - destruct (raised_un_port _ _ _ _ _ inp _ A H H2 ltac:(discriminate) ltac:(discriminate))
      as [v [V P]].
    eapply mt_bang; [exact V|apply Avoid; simpl; left; destruct b; reflexivity|assumption|exact P| |].
    + unfold nonhidden_cons in *. eapply raised_consistent; eauto.
      intros f1 f2 RF NF. inversion RF; subst; congruence.
    + apply IHT; [eapply raised_copy; eassumption|].
      eapply binder_set_avoid; [exact T|].
      intros j I. apply Avoid; simpl; auto.
Qed.

Local Definition demote_flag (b : bool) f :=
  match b, f with true, hid => ill | _,_ => f end.

Local Definition demote (test : key -> bool) (E : env) : env :=
  fun k => option_map (fun '(f,t) => (demote_flag (test k) f,t)) (E k).

Local Lemma demote_vis test E k t :
  E k = Some (vis,t) -> demote test E k = Some (vis,t).
Proof. intros H. unfold demote. rewrite H. destruct (test k); reflexivity. Qed.

Local Lemma demote_update test E k f t :
  (f = vis \/ test k = false) ->
  forall j, demote test (set E k f t) j = set (demote test E) k f t j.
Proof.
  intros P j. unfold demote, set, update.
  destruct (pair_eq j k) eqn:H; auto. apply pair_eq_true in H; subst.
  destruct P as [->|F]; [destruct (test k)|rewrite F]; reflexivity.
Qed.

Local Lemma demote_join test A B E :
  join_env A B E -> join_env (demote test A) (demote test B) (demote test E).
Proof.
  intros J k. unfold demote. specialize (J k). destruct J.
  - constructor.
  - constructor. destruct H; simpl; destruct (test k);
      match goal with H : flag_plus _ _ _ |- _ => inversion H; subst end;
      simpl; constructor; (constructor || assumption).
Qed.

Local Lemma demote_preserve m E p :
  mtyped m E p -> forall test,
  (forall j, In j (secLabs p) -> test j = false) ->
  mtyped m (demote test E) p.
Proof.
  intros C. induction C; intros P OK.
  - constructor. intros k f t V. unfold demote in V.
    destruct (E k) as [[f1 t1]|] eqn:E0; inversion V; subst. eapply (H k); eassumption.
  - assert (Pk : P k = false).
    { apply OK. simpl. apply in_app_iff. right. destruct k; simpl; auto. }
    eapply mt_nu with (t:=t).
    + unfold demote. rewrite H, Pk. reflexivity.
    + eapply mtyped_ext; [apply IHC|apply demote_update; auto].
      intros k0 I; apply OK; simpl; apply in_app_iff; auto.
  - eapply mt_par with (E1:=demote P E1) (E2:=demote P E2); eauto using demote_join.
    + apply IHC1. intros j I; apply OK; simpl; apply in_app_iff; auto.
    + apply IHC2. intros j I; apply OK; simpl; apply in_app_iff; auto.
  - eapply mt_out_lin; eauto using demote_vis.
    eapply mtyped_ext; [apply IHC; exact OK|].
    intro j. rewrite demote_update by auto. apply set_congr, demote_update; auto.
  - eapply mt_out_un; eauto using demote_vis.
    eapply mtyped_ext; [apply IHC; exact OK|apply demote_update; auto].
  - eapply mt_in_lin; eauto using demote_vis.
    + unfold demote; now rewrite H0.
    + eapply mtyped_ext; [apply IHC; exact OK|].
      intro j. rewrite demote_update by auto. apply set_congr, demote_update; auto.
  - eapply mt_in_un; eauto using demote_vis.
    + unfold demote; now rewrite H0.
    + eapply mtyped_ext; [apply IHC; exact OK|apply demote_update; auto].
  - eapply mt_bang; eauto using demote_vis.
    + unfold demote; now rewrite H0.
    + unfold nonhidden_cons. intros j f ty V NF.
      unfold demote in V. destruct (E j) as [[f0 t0]|] eqn:D; inversion V; subst.
      destruct f0; cbn in *.
      * destruct (P j) eqn:K; [|contradiction].
        apply (unused_linear _ _ _ C j hid ty); [|right; split; [reflexivity|]].
        -- unfold set; rewrite update_neq by (intros <-; congruence). exact D.
        -- intros I. specialize (OK j I). congruence.
      * apply (H3 j ill); auto; discriminate.
      * apply (H3 j vis); auto; discriminate.
    + eapply mtyped_ext; [apply IHC; exact OK|apply demote_update; auto].
Qed.

Local Definition overlay (new old : env) : env :=
  fun k => match new k with Some v => Some v | None => old k end.

Local Definition copy_slots m L (G : env) : env :=
  fun k => if (m <? snd k) && In2 (unshift_key m k) L
           then G (unshift_key m k) else None.

Local Definition bounded_at m (E : env) := forall k v, E k = Some v -> snd k <= m.

Local Lemma bounded_none m E k : bounded_at m E -> m < snd k -> E k = None.
Proof. intros H B. destruct (E k) eqn:E0; auto. specialize (H _ _ E0). lia. Qed.

Local Lemma join_bounded m G A F :
  bounded_at m G -> join_env A F G -> bounded_at m A /\ bounded_at m F.
Proof.
  intros B J. split; intros k v V; specialize (J k); rewrite V in J;
    inversion J; subst; eapply (B k); symmetry; eassumption.
Qed.

Local Lemma copy_slots_below m L G k : snd k <= m -> copy_slots m L G k = None.
Proof. unfold copy_slots. intros B; rewrite (proj2 (Nat.ltb_ge _ _) B); reflexivity. Qed.

Local Lemma copy_slots_origin m L G k v :
  copy_slots m L G k = Some v ->
  m < snd k /\ In (unshift_key m k) L /\ G (unshift_key m k) = Some v.
Proof.
  unfold copy_slots. destruct (_ && _) eqn:E; [|discriminate].
  apply andb_true_iff in E as [A B]. intros C. repeat split; auto.
  - now apply Nat.ltb_lt in A.
  - now apply In2_spec in B.
Qed.

Local Lemma empty_part_discardable t : discardable (empty_part t).
Proof. destruct t as [[|] p t|]; simpl; auto. Qed.

Local Lemma empty_part_same t : discardable t -> empty_part t = t.
Proof. destruct t as [[|] p t|]; simpl; auto. intros ->; reflexivity. Qed.

Local Lemma neutral_none E k : neutral E k = None <-> E k = None.
Proof. unfold neutral. destruct (E k) as [[f t]|]; split; congruence. Qed.

Local Lemma overlay_add m L G E :
  bounded_at m E -> raised_env m E (overlay (neutral (copy_slots m L G)) E).
Proof.
  intros B k. unfold overlay, neutral.
  destruct (copy_slots m L G k) as [[f t]|] eqn:C.
  - apply copy_slots_origin in C as [High _]. rewrite (bounded_none _ _ _ B High).
    apply raised_fresh; [lia|destruct f; discriminate|apply empty_part_discardable].
  - destruct (E k) as [[f t]|]; repeat constructor.
Qed.

Local Lemma join_hidden_whole A F G k t f u :
  join_env A F G -> A k = Some (hid,t) -> F k = Some (f,u) ->
  discardable u -> G k = A k.
Proof.
  intros J H U D. specialize (J k). rewrite H,U in J. inversion J; subst.
  match goal with C : join_entry _ _ _ |- _ => inversion C; subst end.
  all: repeat match goal with C : flag_plus hid _ _ |- _ => inversion C; clear C; subst end.
  all: try (symmetry; assumption).
  simpl in D. subst.
  match goal with C : pol_plus _ empty _ |- _ => inversion C; subst; symmetry; assumption end.
Qed.

Local Lemma plus_part_old t u r :
  type_plus t u r -> discardable t -> raised_type t (empty_part r).
Proof.
  intros P C. inversion P; subst; cbn in *; auto using raised_same.
  - subst; constructor.
  - apply raised_un. destruct p1,p2; cbn; constructor.
Qed.

Local Lemma relabel_binders m p : bv (relabel m p) = bv p.
Proof.
  assert (P : forall q x y, bv (replace_refs q x y) = bv q).
  { induction q; intros a b; unfold replace_refs in *; simpl; congruence. }
  induction p; simpl; try rewrite P; congruence.
Qed.

(* Assign the old restrictions to the spawned continuation and their
   copies to the retained server. *)
Local Lemma replication_keep m G A p b f t u acc :
  mtyped m A p ->
  nonhidden_cons A -> sl_pos p ->
  bounded_at m A ->
  (forall k, In k (secLabs p) -> A k = G k) ->
  A b = Some (f,t) -> f <> hid -> type_plus t u acc ->
  mtyped m (overlay (copy_slots m (secLabs p) G) (neutral (set A b vis acc)))
    (relabel m p).
Proof.
  intros T Q Pos Bound Agree B NF Plus.
  assert (Bb : snd b <= m) by (eapply Bound; eassumption).
  assert (Na : ~ In b (secLabs p)).
  { intro H. destruct (scoped_restrictions _ _ _ T) as [_ S].
    destruct (S b H) as [s V]. rewrite B in V; inversion V; subst; contradiction. }
  pose proof (typed_relabel _ _ _ T Bound Pos) as Rel.
  set (L := secLabs p).
  set (D0 := fun k => A (lab_swap m L k)) in *.
  set (dem := fun k : key => negb (m <? snd k)).
  pose proof (demote_preserve _ _ _ Rel dem) as Pull.
  assert (K : forall j, In j (secLabs (relabel m p)) -> dem j = false).
  { intros j I. rewrite secLabs_relabel in I. apply in_map_iff in I as [k [<- H]].
    unfold dem. rewrite (proj2 (Nat.ltb_lt _ _)).
    - reflexivity.
    - apply shift_large. destruct k as [x y]; exact (Pos x y H). }
  specialize (Pull K).
  eapply (raised_preserves_avoiding m 0); [exact Pull| |].
  - intros k. unfold overlay, demote, dem, D0, lab_swap. fold L.
    destruct (m <? snd k) eqn:High; cbn.
    + unfold copy_slots. rewrite High; cbn.
      destruct (In2 (unshift_key m k) L) eqn:U.
      * apply In2_spec in U. rewrite <- (Agree _ U).
        destruct (scoped_restrictions _ _ _ T) as [_ Scope].
        destruct (Scope _ U) as [s S]. rewrite S. repeat constructor.
      * apply Nat.ltb_lt in High. rewrite (bounded_none _ _ _ Bound High).
        unfold neutral, set. rewrite update_neq by (intros <-; lia). rewrite (bounded_none _ _ _ Bound High).
        constructor.
    + assert (Lo : snd k <= m) by (now apply Nat.ltb_ge in High).
      rewrite copy_slots_below by assumption. unfold lab_forward.
      destruct (In2 k L) eqn:Lab.
      * apply In2_spec in Lab. destruct (scoped_restrictions _ _ _ T) as [_ Sc].
        destruct (Sc k Lab) as [s S].
        rewrite (bounded_none m A (shift_key m k)) by
          (try assumption; apply shift_large; destruct k as [x y]; exact (Pos x y Lab)).
        unfold neutral, set. rewrite update_neq by (intros <-; contradiction).
        rewrite S. apply raised_fresh; [lia|discriminate|apply empty_part_discardable].
      * destruct (pair_eq k b) eqn:Keq.
        -- apply pair_eq_true in Keq; subst. rewrite B. unfold neutral, set. rewrite update_eq.
           constructor.
           ++ destruct f; simpl; try contradiction; constructor.
           ++ destruct f; simpl; try contradiction; apply plus_part_old with (u:=u);
                auto; eapply Q; eassumption.
        -- apply pair_eq_false in Keq. unfold neutral, set. rewrite update_neq by assumption.
           destruct (A k) as [[ff ty]|] eqn:Ak; [|constructor].
           rewrite empty_part_same.
           ++ destruct ff; repeat constructor.
           ++ destruct ff.
              ** apply (unused_linear _ _ _ T k hid ty); auto. right. split; auto. now apply In2_no in Lab.
              ** eapply Q; [exact Ak|discriminate].
              ** eapply Q; [exact Ak|discriminate].
  - intros k I. rewrite relabel_binders in I.
    destruct (binders_fresh _ _ _ T _ I) as [V U].
    unfold overlay. rewrite copy_slots_below by lia.
    apply neutral_none. unfold set. rewrite update_neq; [assumption|intros <-; congruence].
Qed.

Local Lemma join_overlay N A F G :
  join_env A F G ->
  join_env (overlay N A) (overlay (neutral N) F) (overlay N G).
Proof.
  intros J k. unfold overlay. pose proof (neutral_join N k) as Z.
  unfold neutral in *. destruct (N k) as [[f t]|]; [exact Z|apply J].
Qed.

Local Lemma join_copy N A :
  join_env (overlay (neutral N) A) (overlay N (neutral A)) (overlay N A).
Proof.
  intros k. unfold overlay. pose proof (neutral_join N k) as J.
  destruct (N k) as [[f t]|] eqn:Q.
  - pose proof (join_comm_env _ _ _ (neutral_join N) k) as L. rewrite Q in L.
    unfold neutral in *. rewrite Q in *. exact L.
  - unfold neutral at 1. rewrite Q. apply (neutral_join A k).
Qed.

Local Lemma frames_replication m G a b x p t f u r q :
  bounded_at m G ->
  G a = Some (vis,Chan un p t) ->
  G b = Some (f,u) -> f <> hid -> type_plus u t r ->
  frame_transform m G (overlay (copy_slots m (secLabs q) G) (set G b vis r))
    (dBang (fst a) (snd a) (fst x) (snd x) q)
    (dPar (replace_refs q x b) (dBang (fst a) (snd a) (fst x) (snd x) (relabel m q))).
Proof.
  intros Bound V W NF Plus A F Pos T J Safe.
  destruct (join_bounded _ _ _ _ Bound J) as [BA BF].
  inversion T; subst.
  match goal with H1 : fst ?j = fst ?a, H2 : snd ?j = snd ?a,
                 H3 : fst ?k = fst ?x, H4 : snd ?k = snd ?x |- _ =>
    assert (E1 : j = a) by (destruct j,a; simpl in *; congruence); subst j;
    assert (E2 : k = x) by (destruct k,x; simpl in *; congruence); subst k end.
  destruct (join_vis _ _ _ _ _ J V) as [va [vf [Va [Vf K]]]].
  match goal with A0 : A a = Some (vis,Chan un ?pol ?ty) |- _ =>
    rewrite A0 in Va; inversion Va; subst va
  end.
  inversion K; subst.
  destruct (join_at _ _ _ _ _ _ J W) as [[fa ta] [[ff tf] [Ak [Fk Spl]]]].
  destruct (join_added _ _ _ _ _ _ _ _ Spl NF Plus) as [ta' [tf' [NA [RF [Add [RT Rj]]]]]].
  set (D := set A b vis ta').
  set (F0 := set F b vis tf').
  set (N := copy_slots m (secLabs q) G).
  assert (Bb : snd b <= m) by (eapply Bound; eassumption).
  assert (BD : bounded_at m D) by (exact (bound_set _ _ _ _ _ BA Bb)).
  assert (BF0 : bounded_at m F0) by (exact (bound_set _ _ _ _ _ BF Bb)).
  assert (Agree : forall k, In k (secLabs q) -> A k = G k).
  { intros k I. destruct (scoped_restrictions _ _ _ T) as [_ Scope].
    destruct (Scope k I) as [s S]. destruct (join_hidden_left _ _ _ _ _ J S) as [v [w [Gf GG]]].
    symmetry. eapply join_hidden_whole; [exact J|exact S|exact Gf|].
    eapply (Safe k); eassumption. }
  exists (overlay N D), (overlay (neutral N) F0).
  split; [|split].
  - eapply mt_par with (E1:=overlay (neutral N) D) (E2:=overlay N (neutral D)).
    + apply join_copy.
    + eapply raised_preserves; [|unfold N; apply overlay_add; assumption].
      unfold D. eapply transfer_payload; eassumption.
    + change (mtyped m (overlay N (neutral D))
        (relabel m (dBang (fst a) (snd a) (fst x) (snd x) q))).
      unfold N, D. eapply (replication_keep m G A (dBang (fst a) (snd a) (fst x) (snd x) q)); eassumption.
  - eapply raised_trans with (B:=F0).
    + intro k. unfold F0, set, update. destruct (pair_eq k b) eqn:Eq.
      * apply pair_eq_true in Eq. subst. rewrite Fk. constructor; assumption.
      * destruct (F k) as [[j v]|]; repeat constructor.
    + unfold N. apply overlay_add; assumption.
  - apply join_overlay. unfold D, F0. apply join_set; auto. constructor; assumption.
Qed.

Local Definition action_port (a : key) ph act :=
  match act with
  | aOut a1 a2 _ _ => a = (a1,a2) /\ ph = out
  | aIn a1 a2 _ _ => a = (a1,a2) /\ ph = inp
  | _ => False
  end.

Local Lemma consumed_linear_port A D a ph md t p u :
  consumes A a (Chan md ph t) D ->
  A a = Some (vis,Chan lin p u) -> ph <> empty ->
  p = ph \/ p = io.
Proof.
  intros C V NF. apply consumes_shape in C as [s [r [X [R _]]]].
  rewrite V in X; inversion X; subst. destruct R as [Sub _]. inversion Sub; subst; tauto.
Qed.

Local Lemma port_plus_left ph a b c :
  pol_plus a b c -> (a = ph \/ a = io) -> ph <> empty -> c = ph \/ c = io.
Proof. intros P S NF. inversion P; subst; destruct ph; intuition congruence. Qed.

Local Lemma typed_nu_inv m A k p :
  mtyped m A (dNu (fst k) (snd k) p) ->
  exists t, A k = Some (hid,t) /\ mtyped m (set A k vis t) p.
Proof.
  intros T. inversion T; subst.
  match goal with
  | K : A ?j = Some (hid,?u), H : mtyped m (set A ?j vis ?u) p |- _ =>
    assert (E : j = k) by (destruct j,k; simpl in *; congruence); subst j
  end. eauto.
Qed.

Local Lemma lts_uses_port g p act g' p' nd :
  lts g p act g' p' nd ->
  forall m A a ph p0 t,
    action_port a ph act ->
    mtyped m A p -> A a = Some (vis,Chan lin p0 t) ->
    p0 = ph \/ p0 = io.
Proof.
  intros L. induction L; intros m A k ph p0 t0 Act Tp V; simpl in Act; try contradiction.
  all: try solve [
    destruct Act as [-> ->];
    match type of Tp with
    | mtyped _ _ (dOut ?a1 ?a2 ?b1 ?b2 ?q) =>
      let C := fresh "C" in
      let S := constr:(typed_out_inv m A (a1,a2) (b1,b2) q Tp) in
      destruct S as [? [? [? [? [C _]]]]];
      eapply consumed_linear_port; [exact C|exact V|discriminate]
    | mtyped _ _ (dInp ?a1 ?a2 ?x1 ?x2 ?q) =>
      let C := fresh "C" in
      let S := constr:(typed_in_inv m A (a1,a2) (x1,x2) q Tp) in
      destruct S as [? [? [? [C _]]]];
      eapply consumed_linear_port; [exact C|exact V|discriminate]
    | mtyped _ _ (dBang _ _ _ _ _) =>
      inversion Tp; subst;
      match goal with U : ?AA ?j = Some (vis,Chan un _ _),
                      W : ?AA ?k = Some (vis,Chan lin _ _) |- _ =>
        assert (Q : j = k) by (destruct j; destruct k; simpl in *; congruence); congruence
      end
    end].
  all: try solve [
    match type of Tp with
    | mtyped _ _ (dNu ?a1 ?a2 ?q) =>
      destruct (typed_nu_inv m A (a1,a2) q Tp) as [u [A0 T0]];
      apply (IHL m (set A (a1,a2) vis u) k ph p0 t0);
      [exact Act|exact T0|unfold set; rewrite update_neq; [exact V|intro E; subst; congruence]]
    end].
  all: inversion Tp; subst.
  all: match goal with J : join_env ?B ?C ?AA |- _ =>
    destruct (join_vis _ _ _ _ _ J V) as [v [w [X [Y K]]]];
    inversion K; subst
  end.
  all: assert (N : ph <> empty) by
    (match type of Act with action_port _ _ ?act => destruct act; simpl in Act; intuition congruence end).
  - eapply port_plus_left; [eassumption|eapply IHL; eassumption|assumption].
  - eapply port_plus_left; [apply pol_plus_comm; eassumption|eapply IHL; eassumption|assumption].
Qed.

Local Lemma frames_continue m G G' p q q' P Q F A :
  mtyped m P p -> mtyped m Q q ->
  join_env Q P A -> join_env A F G ->
  sl_pos q -> frame_safe q F ->
  frame_transform m G G' q q' ->
  exists A' F', mtyped m A' (dPar p q') /\ raised_env m F F' /\ join_env A' F' G'.
Proof.
  intros TP TQ J1 J2 Pos Safe Step.
  destruct (join_associate _ _ _ _ _ J1 J2) as [JPF JQ].
  assert (SQ : frame_safe q (e_cup P F)) by (eapply sibling_frame; eassumption).
  destruct (Step _ _ Pos TQ JQ SQ) as [Q' [PF' [TQ' [R Jin]]]].
  destruct (raised_join _ _ _ _ _ R JPF) as [P' [F' [RP [RF JPF']]]].
  destruct (join_reverse_associate _ _ _ _ _ JPF' Jin) as [J3 J4].
  exists (e_cup P' Q'), F'. repeat split; auto.
  eapply mt_par; [apply join_comm_env; exact J3|eapply raised_preserves; eassumption|exact TQ'].
Qed.

Local Lemma linear_ownership m G A F P Q a t p q :
  join_env P Q A -> join_env A F G ->
  G a = Some (vis,Chan lin io t) ->
  mtyped m P p -> mtyped m Q q ->
  (forall A p0, mtyped m A p -> A a = Some (vis,Chan lin p0 t) -> p0 = out \/ p0 = io) ->
  (forall A p0, mtyped m A q -> A a = Some (vis,Chan lin p0 t) -> p0 = inp \/ p0 = io) ->
  P a = Some (vis,Chan lin out t) /\ Q a = Some (vis,Chan lin inp t) /\
  F a = Some (vis,Chan lin empty t).
Proof.
  intros L J G0 TP TQ Out In.
  destruct (join_vis _ _ _ _ _ J G0) as [u [v [U [V UV]]]].
  inversion UV; subst.
  destruct (join_vis _ _ _ _ _ L U) as [s [w [S [W SW]]]].
  inversion SW; subst.
  match goal with S : P a = Some (vis,Chan lin ?p1 t), W : Q a = Some (vis,Chan lin ?p2 t) |- _ =>
    destruct (Out _ _ TP S) as [D1|D1]; destruct (In _ _ TQ W) as [D2|D2]; subst
  end.
  all: repeat match goal with H : pol_plus _ _ _ |- _ => inversion H; clear H; subst end.
  all: auto.
Qed.

Local Lemma raise_masked_lin m R R' a pol t :
  R a = Some (vis,Chan lin pol t) ->
  raised_env m (set R a vis (Chan lin empty t)) R' ->
  R' a = Some (vis,Chan lin empty t) /\
  raised_env m R (set R' a vis (Chan lin pol t)).
Proof.
  intros X Rho. pose proof (Rho a) as J. unfold set in J. rewrite update_eq in J. inversion J; subst.
  repeat match goal with H : raised_flag _ _ |- _ => inversion H; clear H; subst end.
  repeat match goal with H : raised_type (Chan lin _ _) _ |- _ => inversion H; clear H; subst end.
  split; [now symmetry|].
  intro k. destruct (pair_eq k a) eqn:E.
  - apply pair_eq_true in E; subst. unfold set. rewrite X, update_eq. repeat constructor.
  - apply pair_eq_false in E. specialize (Rho k). unfold set in *. rewrite update_neq in Rho |- * by assumption. exact Rho.
Qed.

Local Lemma linear_sender m G Gout a t p p' q A F VP VQ :
  G a = Some (vis,Chan lin io t) -> Gout a = Some (vis,Chan lin empty t) ->
  (forall A p0, mtyped m A p -> A a = Some (vis,Chan lin p0 t) -> p0 = out \/ p0 = io) ->
  (forall A p0, mtyped m A q -> A a = Some (vis,Chan lin p0 t) -> p0 = inp \/ p0 = io) ->
  frame_transform m (set G a vis (Chan lin out t)) Gout p p' ->
  mtyped m VP p -> mtyped m VQ q -> join_env VP VQ A -> join_env A F G ->
  sl_pos p -> frame_safe p (e_cup VQ F) ->
  exists P' R', mtyped m P' p' /\ raised_env m (e_cup VQ F) R' /\
    join_env P' R' (set Gout a vis (Chan lin inp t)).
Proof.
  intros G0 G1 OP IP Out Ts Tr Split J Pos Safe.
  destruct (linear_ownership _ _ _ _ _ _ _ _ _ _ Split J G0 Ts Tr OP IP) as [AP [AQ AF]].
  destruct (join_associate _ _ _ _ _ Split J) as [JQF JP].
  set (R := e_cup VQ F) in *.
  assert (R0 : R a = Some (vis,Chan lin inp t)).
  { unfold R, e_cup. rewrite AQ,AF. reflexivity. }
  assert (MP : join_env VP (set R a vis (Chan lin empty t)) (set G a vis (Chan lin out t))).
  { intro k. unfold set, update.
    destruct (pair_eq k a) eqn:E; [|apply JP].
    apply pair_eq_true in E; subst. rewrite AP. repeat constructor. }
  assert (SM : frame_safe p (set R a vis (Chan lin empty t))).
  { intros k f u I K. unfold set, update in K. destruct (pair_eq k a);
      [inversion K; subst; reflexivity|eapply (Safe k); eassumption]. }
  destruct (Out _ _ Pos Ts MP SM) as [P' [R' [TP' [Raise Jout]]]].
  destruct (raise_masked_lin _ _ _ _ _ _ R0 Raise) as [R1 R2].
  assert (P1 : P' a = Some (vis,Chan lin empty t)).
  { destruct (join_vis _ _ _ _ _ Jout G1) as [c [d [X [Y V]]]].
    inversion V; subst. match goal with H : pol_plus _ _ empty |- _ => inversion H; subst; assumption end. }
  assert (Jrestore : join_env P' (set R' a vis (Chan lin inp t)) (set Gout a vis (Chan lin inp t))).
  { intro k. unfold set, update. destruct (pair_eq k a) eqn:E; [|apply Jout].
    apply pair_eq_true in E; subst. rewrite P1. repeat constructor. }
  exists P', (set R' a vis (Chan lin inp t)). repeat split; assumption.
Qed.

Local Lemma linear_frame_communication m G Gout G' a t p p' q q' :
  G a = Some (vis,Chan lin io t) -> Gout a = Some (vis,Chan lin empty t) ->
  (forall A p0, mtyped m A p -> A a = Some (vis,Chan lin p0 t) -> p0 = out \/ p0 = io) ->
  (forall A p0, mtyped m A q -> A a = Some (vis,Chan lin p0 t) -> p0 = inp \/ p0 = io) ->
  frame_transform m (set G a vis (Chan lin out t)) Gout p p' ->
  frame_transform m (set Gout a vis (Chan lin inp t)) G' q q' ->
  frame_transform m G G' (dPar p q) (dPar p' q').
Proof.
  intros G0 G1 OP IP Out In A F Pos T J Safety. inversion T; subst.
  match goal with C : join_env ?P ?Q A, TP : mtyped m ?P p, TQ : mtyped m ?Q q |- _ =>
    rename P into VP; rename Q into VQ; rename C into Split; rename TP into Ts; rename TQ into Tr
  end.
  destruct (join_associate _ _ _ _ _ Split J) as [JQF JP].
  assert (SP : frame_safe p (e_cup VQ F))
    by (eapply sibling_frame; eauto using frame_safe_par_left).
  destruct (linear_sender _ _ _ _ _ _ _ _ _ _ _ _ G0 G1 OP IP Out Ts Tr Split J
             (sl_pos_par_left _ _ Pos) SP) as [P' [R' [TP' [Raise Jout]]]].
  destruct (raised_join _ _ _ _ _ Raise JQF) as [Q1 [F1 [RQ [RF JQF']]]].
  destruct (join_reverse_associate _ _ _ _ _ JQF' Jout) as [J1 J2].
  assert (TQ1 : mtyped m Q1 q) by (eapply raised_preserves; eassumption).
  assert (SQ : frame_safe q F1).
  { eapply raised_safe; [exact RF|eapply frame_safe_par_right; eassumption]. }
  apply join_comm_env in J1.
  destruct (frames_continue _ _ _ _ _ _ _ _ _ _ TP' TQ1 J1 J2 (sl_pos_par_right _ _ Pos) SQ In)
    as [A' [F' [TA [Rend K]]]].
  exists A', F'. repeat split; auto. eapply raised_trans; eassumption.
Qed.

Local Lemma raised_ill_revert m A D k v w :
  raised_env m A D ->
  A k = Some (ill,v) -> D k = Some (vis,w) ->
  raised_env m A (set D k ill w).
Proof.
  intros R X Y j. destruct (pair_eq j k) eqn:E.
  - apply pair_eq_true in E; subst. unfold set; rewrite X, update_eq.
    specialize (R k). rewrite X,Y in R. inversion R; subst. constructor; auto using raised_flag_same.
  - apply pair_eq_false in E. unfold set. rewrite update_neq by assumption. apply R.
Qed.

Local Lemma raised_vis_restore m A D k v w :
  raised_env m (set A k ill v) D ->
  A k = Some (vis,v) -> D k = Some (vis,w) ->
  raised_env m A D.
Proof.
  intros R X Y j. destruct (pair_eq j k) eqn:E.
  - apply pair_eq_true in E; subst. rewrite X,Y.
    specialize (R k). unfold set in R. rewrite Y, update_eq in R.
    inversion R; subst. constructor; auto using raised_flag_same.
  - apply pair_eq_false in E. specialize (R j). unfold set in R. rewrite update_neq in R by assumption. exact R.
Qed.

Local Lemma hidden_frame_ill m G P R R' k t u :
  join_env P R G -> G k = Some (hid,t) ->
  raised_env m R R' -> R' k = Some (vis,u) ->
  exists v, R k = Some (ill,v).
Proof.
  intros J X R0 R1.
  destruct (join_at _ _ _ _ _ _ J X) as [[fp tp] [[fr tr] [P0 [Q0 K]]]].
  specialize (R0 k). rewrite Q0,R1 in R0. inversion R0; subst.
  match goal with H : raised_flag fr vis |- _ => inversion H; subst; eauto end.
  inversion K; subst; match goal with C : flag_plus _ vis hid |- _ => inversion C end.
Qed.

Local Lemma join_ill G A F k t :
  join_env A F G -> G k = Some (ill,t) ->
  exists u v, A k = Some (ill,u) /\ F k = Some (ill,v) /\ join_entry (ill,u) (ill,v) (ill,t).
Proof.
  intros J V. destruct (join_at _ _ _ _ _ _ J V) as [a [b [A0 [B0 K]]]].
  inversion K; subst;
    match goal with F : flag_plus _ _ ill |- _ => inversion F; subst; eauto end.
Qed.

Local Lemma flag_update_safe p A k f old t :
  frame_safe p A -> A k = Some (old,t) -> frame_safe p (set A k f t).
Proof.
  intros C V j g s I W. unfold set,update in W. destruct (pair_eq j k) eqn:E.
  - apply pair_eq_true in E; subst. inversion W; subst. eapply (C k); eassumption.
  - eapply (C j); eassumption.
Qed.

Local Lemma close_into_frame m G Gs A F Fs p k t v :
  mtyped m A p -> join_env A F G ->
  G k = Some (vis,t) -> Fs k = Some (ill,v) -> raised_env m Fs F ->
  (forall x, Gs x = set G k hid t x) ->
  exists A' F', mtyped m A' (dNu (fst k) (snd k) p) /\
    raised_env m Fs F' /\ join_env A' F' Gs.
Proof.
  intros T J GC X R EQ.
  destruct (join_vis _ _ _ _ _ J GC) as [w [u [A0 F0]]].
  destruct F0 as [D K].
  exists (set A k hid w), (set F k ill u). split; [|split].
  - eapply mt_nu with (t:=w); [unfold set; apply update_eq|].
    eapply mtyped_ext; [exact T|].
    intro x. unfold set, update. destruct (pair_eq x k) eqn:Y; auto.
    apply pair_eq_true in Y; subst. assumption.
  - eapply raised_ill_revert; eassumption.
  - intros x. rewrite EQ. eapply join_change; [exact J|exact K|constructor].
Qed.

Local Lemma frames_closed_com_context m G Gout G' b s s1 p p' q q' :
  G b = Some (hid,s) -> Gout b = Some (vis,s1) -> G' b = Some (vis,s) ->
  (forall P Q A F, mtyped m P p -> mtyped m Q q ->
    join_env P Q A -> join_env A F G ->
    sl_pos p -> frame_safe p (e_cup Q F) ->
    exists P' R', mtyped m P' p' /\ raised_env m (e_cup Q F) R' /\ join_env P' R' Gout) ->
  frame_transform m (set Gout b ill s1) G' q q' ->
  frame_transform m G (set G' b hid s) (dPar p q)
    (dNu (fst b) (snd b) (dPar p' q')).
Proof.
  intros G0 G1 G2 Out In A F Pos T J Safe. inversion T; subst.
  match goal with C : join_env ?P ?Q A, TP : mtyped m ?P p, TQ : mtyped m ?Q q |- _ =>
    rename P into VP; rename Q into VQ; rename C into Split; rename TP into Ts; rename TQ into Tr
  end.
  destruct (join_associate _ _ _ _ _ Split J) as [JQF JP].
  set (R := e_cup VQ F) in *.
  assert (SP : frame_safe p R) by (unfold R; eapply sibling_frame; eauto using frame_safe_par_left).
  destruct (Out _ _ _ _ Ts Tr Split J (sl_pos_par_left _ _ Pos) SP) as [P' [R' [TP' [Raise Jout]]]].
  destruct (join_vis _ _ _ _ _ Jout G1) as [sP [sR [P0 [R0 K0]]]].
  destruct (hidden_frame_ill _ _ _ _ _ _ _ _ JP G0 Raise R0) as [u Rold].
  destruct (join_ill _ _ _ _ _ JQF Rold) as [tQ [tF [AQ [AF _]]]].
  destruct (raised_join _ _ _ _ _ Raise JQF) as [Q1 [F1 [RQ [RF JQF']]]].
  destruct (join_vis _ _ _ _ _ JQF' R0) as [sQ [sF [Q0 [F0 K1]]]].
  pose proof (raised_ill_revert _ _ _ _ _ _ RQ AQ Q0) as RQill.
  pose proof (raised_ill_revert _ _ _ _ _ _ RF AF F0) as RFill.
  set (Qill := set Q1 b ill sQ) in *.
  set (Fill := set F1 b ill sF) in *.
  set (Pill := set P' b ill sP) in *.
  assert (TQ1 : mtyped m Q1 q) by (eapply raised_preserves; eassumption).
  assert (TQill : mtyped m Qill q) by (exact (raised_preserves _ _ _ Tr _ RQill)).
  destruct (join_reverse_associate _ _ _ _ _ JQF' Jout) as [J1 J2].
  apply join_comm_env in J1.
  destruct (join_associate _ _ _ _ _ J1 J2) as [JPF JQ].
  set (R2 := e_cup P' F1) in *.
  destruct (join_vis _ _ _ _ _ JQ G1) as [t0 [tR [YQ [YR K2]]]].
  rewrite Q0 in YQ. inversion YQ; subst t0.
  destruct (join_vis _ _ _ _ _ JPF YR) as [t1 [t2 [YP [YF K3]]]].
  rewrite P0 in YP. inversion YP; subst t1.
  rewrite F0 in YF. inversion YF; subst t2.
  set (Rill := set R2 b ill tR) in *.
  assert (JPF0 : join_env Pill Fill Rill).
  { unfold Pill,Fill,Rill. eapply join_change; [exact JPF|exact K3|constructor]. }
  assert (Jin : join_env Qill Rill (set Gout b ill s1)).
  { unfold Qill,Rill. eapply join_change; [exact JQ|exact K2|constructor]. }
  assert (SQ : frame_safe q R2).
  { unfold R2. eapply sibling_frame; [exact TQ1|exact TP'|exact J1|exact JPF|].
    eapply raised_safe; [exact RF|eapply frame_safe_par_right; eassumption]. }
  assert (SQill : frame_safe q Rill) by (unfold Rill; eapply flag_update_safe; eassumption).
  destruct (In _ _ (sl_pos_par_right _ _ Pos) TQill Jin SQill) as [Q' [H [TQ' [Raised Jend]]]].
  destruct (raised_join _ _ _ _ _ Raised JPF0) as [P'' [F'' [RP' [RF' JPF']]]].
  destruct (join_vis _ _ _ _ _ Jend G2) as [w [h [Vq [Vf K4]]]].
  destruct (join_vis _ _ _ _ _ JPF' Vf) as [dp [df [Vp [VF K5]]]].
  assert (RP : raised_env m P' P'') by (unfold Pill in RP'; eapply raised_vis_restore; eassumption).
  assert (TP'' : mtyped m P'' p') by (eapply raised_preserves; eassumption).
  destruct (join_reverse_associate _ _ _ _ _ JPF' Jend) as [J5 J6].
  eapply close_into_frame; [|exact J6|exact G2|eassumption| |reflexivity].
  - eapply mt_par; [apply join_comm_env; exact J5|exact TP''|exact TQ'].
  - eapply raised_trans; eassumption.
Qed.

Local Lemma frames_closed_com m G Gout G' b s s1 p p' q q' :
  G b = Some (hid,s) -> Gout b = Some (vis,s1) -> G' b = Some (vis,s) ->
  frame_transform m G Gout p p' ->
  frame_transform m (set Gout b ill s1) G' q q' ->
  frame_transform m G (set G' b hid s) (dPar p q)
    (dNu (fst b) (snd b) (dPar p' q')).
Proof.
  intros G0 G1 G2 U V. eapply frames_closed_com_context with (Gout:=Gout); try eassumption.
  intros P Q A F TP TQ J K Pos Safe.
  destruct (join_associate _ _ _ _ _ J K) as [_ JL].
  exact (U _ _ Pos TP JL Safe).
Qed.

Local Lemma frames_swap_closed m G G' p p' q q' k :
  frame_transform m G G' (dPar p q) (dNu (fst k) (snd k) (dPar p' q')) ->
  frame_transform m G G' (dPar q p) (dNu (fst k) (snd k) (dPar q' p')).
Proof.
  intros U A F Pos C J Safe.
  assert (P : sl_pos (dPar p q)).
  { intros x y I. apply (Pos x y). simpl in *. apply in_app_iff in I. apply in_app_iff. tauto. }
  assert (S : frame_safe (dPar p q) F).
  { intros x f t I K. eapply (Safe x); [|eassumption].
    simpl in *. apply in_app_iff in I. apply in_app_iff. tauto. }
  destruct (U _ _ P (mtyped_par_swap _ _ _ _ C) J S) as [D [F' [T [R V]]]].
  destruct (typed_nu_inv _ _ _ _ T) as [t [D0 TD]].
  exists D, F'. repeat split; auto.
  eapply mt_nu; [exact D0|eauto using mtyped_par_swap].
Qed.

Local Lemma fetch_bounded g : bounded_at (max (domain g)) (fetch g).
Proof.
  intros k v V. apply max_upper, fetch_domain. eauto.
Qed.

Local Lemma fresh_shift_miss m g k :
  bounded_at m (fetch g) -> 0 < snd k ->
  snd (shift_key m k) > m /\ fetch g (shift_key m k) = None.
Proof.
  intros V B. split; [apply shift_large; assumption|apply bounded_none with (m:=m); auto using shift_large].
Qed.

Local Lemma new_entries_shift_cons g m k tail :
  bounded_at m (fetch g) -> 0 < snd k ->
  exists f t, newEntries g (shift_key m k :: tail) m =
    (shift_key m k,f,t) :: newEntries g tail m /\
    (forall v, fetch g k = Some v -> v = (f,t)).
Proof.
  intros B P. destruct (fresh_shift_miss _ _ _ B P) as [_ NoneShift].
  unfold fetch in NoneShift.
  destruct (InB (shift_key m k) g) as [[fh sh] present] eqn:E.
  destruct present; [discriminate|].
  destruct k as [x y]. unfold shift_key in *. simpl fst in *. simpl snd in *.
  simpl newEntries. rewrite E.
  replace (y + m - m) with y by lia.
  destruct (InB (x,y) g) as [[f t] present'] eqn:V.
  exists f,t. split; [reflexivity|].
  intros v W. unfold fetch in W. rewrite V in W. destruct present'; congruence.
Qed.

Local Lemma new_entries_domain g m L :
  bounded_at m (fetch g) -> (forall k, In k L -> 0 < snd k) ->
  domain (newEntries g (map (shift_key m) L) m) = map (shift_key m) L.
Proof.
  intros B P. induction L as [|k L IH]; cbn [map]; auto.
  destruct (new_entries_shift_cons g m k (map (shift_key m) L) B ltac:(apply P; now left))
    as [f [t [E _]]].
  rewrite E. simpl. rewrite IH; [reflexivity|intros; apply P; now right].
Qed.

Local Lemma new_entries_fetch g m L tail :
  bounded_at m (fetch g) ->
  (forall k, In k L -> 0 < snd k) ->
  (forall k, In k L -> exists v, fetch g k = Some v) ->
  mapped (newEntries g (map (shift_key m) L) m ++ tail)
    (overlay (copy_slots m L (fetch g)) (fetch tail)).
Proof.
  intros B P K. induction L as [|k L IH]; intro j; cbn [map].
  - unfold overlay, copy_slots; simpl.
    destruct (m <? snd j); reflexivity.
  - destruct (new_entries_shift_cons g m k (map (shift_key m) L) B ltac:(apply P; now left))
      as [f [t [Eq A]]].
    destruct (K k ltac:(now left)) as [v V]. specialize (A _ V). subst v.
    rewrite Eq. simpl app. rewrite fetch_cons.
    assert (M : 0 < snd k) by (apply P; now left).
    unfold update. destruct (pair_eq j (shift_key m k)) eqn:E.
    + apply pair_eq_true in E. subst j.
      unfold overlay, copy_slots at 1.
      rewrite (proj2 (Nat.ltb_lt _ _) (shift_large m k M)), shift_inverse.
      simpl. rewrite (proj2 (pair_eq_true _ _) eq_refl), V. reflexivity.
    + rewrite IH by (intros; first [apply P|apply K]; now right).
      unfold overlay, copy_slots.
      destruct (m <? snd j) eqn:J; simpl; [|reflexivity].
      destruct (pair_eq (unshift_key m j) k) eqn:U; [|reflexivity].
      apply pair_eq_true in U. apply pair_eq_false in E. apply Nat.ltb_lt in J.
      exfalso. apply E. rewrite <- U, unshift_inverse by lia. reflexivity.
Qed.

Local Lemma domains_append g h : domain (g ++ h) = domain g ++ domain h.
Proof. induction g as [|[[k f] t] g IH]; simpl; congruence. Qed.

Local Lemma shift_nodup m L : NoDup L -> NoDup (map (shift_key m) L).
Proof.
  intros D. induction D; simpl; constructor; auto.
  intros I. apply in_map_iff in I as [y [E I]].
  apply (f_equal (unshift_key m)) in E. rewrite !shift_inverse in E. subst. contradiction.
Qed.

Local Lemma new_entries_nodup m g L tail :
  bounded_at m (fetch g) -> bounded_at m (fetch tail) ->
  (forall k, In k L -> 0 < snd k) ->
  NoDup L -> NoDup (domain tail) ->
  NoDup (domain (newEntries g (map (shift_key m) L) m ++ tail)).
Proof.
  intros G T P N NT. rewrite domains_append, new_entries_domain by assumption.
  apply no_dup_append; eauto using shift_nodup.
  intros k I J. apply in_map_iff in I as [j [<- I]].
  apply fetch_domain in J as [v V]. specialize (T _ _ V).
  pose proof (shift_large m j (P _ I)). lia.
Qed.

Local Lemma fetch_rehead g k f t h s x :
  fetch ((k,h,s)::g) x = set (fetch ((k,f,t)::g)) k h s x.
Proof.
  rewrite fetch_cons. unfold set, update. destruct (pair_eq x k) eqn:E; auto.
  rewrite fetch_cons. unfold update. now rewrite E.
Qed.

Local Lemma fetch_middle h1 h2 k f h t u :
  NoDup (domain (h1 ++ (k,f,t)::h2)) ->
  forall x, fetch (h1 ++ (k,h,u)::h2) x =
    set (fetch (h1 ++ (k,f,t)::h2)) k h u x.
Proof.
  induction h1 as [|[[j ff] ss] h1 IH].
  - simpl. intros. apply fetch_rehead.
  - intros ND x. simpl app in *. simpl domain in ND. inversion ND as [|? ? Fresh D]; subst.
    assert (N : j <> k) by (intros ->; apply Fresh; rewrite domains_append; apply in_app_iff; right; simpl; auto).
    assert (IK := IH D x). rewrite fetch_cons.
    unfold set,update. destruct (pair_eq x j) eqn:E.
    + destruct (pair_eq x k) eqn:F.
      * apply pair_eq_true in E,F; congruence.
      * rewrite fetch_cons. unfold update. now rewrite E.
    + rewrite fetch_cons. unfold update. rewrite E. exact IK.
Qed.

Local Lemma fetch_two_reversed g a b fa fb ta tb :
  isMap g -> a <> b ->
  forall x, fetch ((a,fa,ta)::(b,fb,tb)::removeEntry a (removeEntry b g)) x =
    set (set (fetch g) a fa ta) b fb tb x.
Proof.
  intros M N x. rewrite fetch_cons. unfold set,update.
  destruct (pair_eq x a) eqn:A.
  - destruct (pair_eq x b) eqn:B; auto. apply pair_eq_true in A,B; congruence.
  - rewrite fetch_cons. unfold update. destruct (pair_eq x b) eqn:B; auto.
    apply pair_eq_false in A,B. rewrite !fetch_remove_neq by eauto using removeEntry_map. reflexivity.
Qed.

Local Lemma domain_two_reversed g a b fa fb ta tb :
  NoDup (domain g) -> In a (domain g) -> In b (domain g) -> a <> b ->
  NoDup (domain ((a,fa,ta)::(b,fb,tb)::removeEntry a (removeEntry b g))) /\
  forall x, In x (domain ((a,fa,ta)::(b,fb,tb)::removeEntry a (removeEntry b g))) <-> In x (domain g).
Proof.
  intros ND A B N.
  assert (R : NoDup (domain (removeEntry b g))) by now apply removeEntry_nodup.
  split.
  - simpl. constructor; simpl.
    + rewrite !removeEntry_domain by assumption. intuition congruence.
    + constructor; auto using removeEntry_nodup.
      rewrite !removeEntry_domain by assumption. tauto.
  - intros x. simpl. rewrite !removeEntry_domain by assumption.
    destruct (pair_eq x a) eqn:P; [apply pair_eq_true in P; subst; tauto|].
    destruct (pair_eq x b) eqn:Q; [apply pair_eq_true in Q; subst; tauto|].
    apply pair_eq_false in P,Q; intuition congruence.
Qed.

Local Lemma type_plus_not_payload md p t s : ~ type_plus (Chan md p t) t s.
Proof.
  intros H. inversion H; subst.
  all: match goal with H : Chan ?m ?p ?u = ?u |- _ =>
    apply (type_sub_not_payload m p u); rewrite H; constructor end.
Qed.

Local Lemma dup_head_distinct {X} (a b : X) L : NoDup (a::b::L) -> a <> b.
Proof. intros D ->. inversion D; subst. apply H1. left; reflexivity. Qed.

Local Lemma nodup_app_parts {X} (xs ys : list X) :
  NoDup (xs ++ ys) -> NoDup xs /\ NoDup ys.
Proof.
  induction xs as [|x xs IH]; simpl; intros N; [split; auto using NoDup_nil|].
  inversion N as [|? ? F R]; subst.
  destruct (IH R) as [A B]; split; auto. constructor; auto.
  intros I. apply F, in_app_iff; auto.
Qed.

Local Lemma input_distinct (G : env) a b f md p t u r :
  G a = Some (vis,Chan md p t) -> G b = Some (f,u) ->
  type_plus u t r -> a <> b.
Proof.
  intros A B P <-. rewrite A in B. inversion B; subst.
  eapply type_plus_not_payload; eassumption.
Qed.

Local Lemma fetch_replaced g k f t x :
  fetch ((k,f,t)::removeEntry k g) x = set (fetch g) k f t x.
Proof.
  rewrite fetch_cons. unfold set,update. destruct (pair_eq x k) eqn:E; auto.
  apply pair_eq_false in E. induction g as [|[[a h] u] g IH]; simpl; auto.
  destruct (pair_eq a k) eqn:K.
  - apply pair_eq_true in K. subst a. rewrite fetch_cons, update_neq by assumption. reflexivity.
  - rewrite !fetch_cons. unfold update. destruct (pair_eq x a); auto.
Qed.

Local Lemma set_bounded_unchanged g k f t :
  NoDup (domain g) -> In k (domain g) ->
  max (domain ((k,f,t)::removeEntry k g)) = max (domain g).
Proof. intros ND I. apply max_equiv. eapply set_domain; eassumption. Qed.

Local Lemma lts_nodup g p act g' p' nd :
  lts g p act g' p' nd ->
  NoDup (secLabs p) -> sl_pos p -> NoDup (domain g').
Proof.
  intros L. induction L; intros S P.
  all: try solve [
    eapply IHL; [simpl in S; apply nodup_app_parts in S; tauto|
      first [eapply sl_pos_par_left; exact P | eapply sl_pos_par_right; exact P]]].
  all: try solve [apply set_nodup; assumption].
  all: try solve [
    simpl in S; apply nodup_app_parts in S as [B _];
    eapply IHL; [exact B|intros x y I; apply (P x y); simpl; apply in_app_iff; auto]].
  all: try solve [
    assert (D : (a1,a2) <> (b1,b2)) by
      (solve [apply (dup_head_distinct _ _ _ pf1) |
       eapply out_distinct with (e:=fetch g); eauto using fetch_complete, nodup_map |
       eapply input_distinct with (G:=fetch g); eauto using fetch_complete, nodup_map]);
    eapply (proj1 (domain_two_reversed g (a1,a2) (b1,b2) _ _ _ _ pf
       ltac:(apply domain_spec; eauto) ltac:(apply domain_spec; eauto) D))].
  all: try solve [
    simpl in S; apply nodup_app_parts in S as [B _];
    assert (R : NoDup (domain (h' ++ (b1,b2,vis,t')::h'')))
      by (eapply IHL; [exact B|intros x y I; apply (P x y); simpl; apply in_app_iff; auto]);
    rewrite domains_append in R |- *; exact R].
  all: try solve [
    apply nodup_app_parts in S as [S1 S2];
    try apply set_nodup;
    eapply IHL2; [first [exact S1|exact S2]|
    first [eapply sl_pos_par_left; exact P|eapply sl_pos_par_right; exact P]]].
  unfold q. rewrite dep_relabel_view, secLabs_relabel.
  apply new_entries_nodup.
  - apply fetch_bounded.
  - rewrite <- (set_bounded_unchanged g (b1,b2) vis t2 pf) at 1.
    + apply fetch_bounded.
    + apply domain_spec; eauto.
  - intros [x y] I. exact (P x y I).
  - exact S.
  - apply set_nodup; exact pf.
Qed.

Local Lemma frames_target_list m G g G' p p' :
  mapped g G' -> frame_transform m G G' p p' ->
  frame_transform m G (fetch g) p p'.
Proof. intros H U. eapply frame_ext; [reflexivity|intros k; symmetry; apply H|exact U]. Qed.

Local Lemma ordinary_linear_communication g a b t s s1 p p' q q' d1 d2 :
  let base := removeEntry a (removeEntry b g) in
  let send := (a,vis,Chan lin out t)::(b,vis,s)::base in
  let mid := (a,vis,Chan lin empty t)::(b,vis,s1)::base in
  let recv := (a,vis,Chan lin inp t)::(b,vis,s1)::base in
  let dst := (a,vis,Chan lin empty t)::(b,vis,s)::base in
  NoDup (domain g) -> In (a,vis,Chan lin io t) g -> In (b,vis,s) g ->
  lts send p (aOut (fst a) (snd a) (fst b) (snd b)) mid p' d1 ->
  lts recv q (aIn (fst a) (snd a) (fst b) (snd b)) dst q' d2 ->
  frame_transform (max (domain send)) (fetch send) (fetch mid) p p' ->
  frame_transform (max (domain recv)) (fetch recv) (fetch dst) q q' ->
  frame_transform (max (domain g)) (fetch g) (fetch dst) (dPar p q) (dPar p' q').
Proof.
  intros base send mid recv dst ND A B Send Recv FS FR.
  assert (N : a <> b) by (apply (dup_head_distinct _ _ _ d1)).
  assert (Da : In a (domain g)) by (apply domain_spec; eauto).
  assert (Db : In b (domain g)) by (apply domain_spec; eauto).
  assert (E1 : max (domain send) = max (domain g)).
  { apply max_equiv. unfold send, base.
    apply (proj2 (domain_two_reversed _ _ _ _ _ _ _ ND Da Db N)). }
  assert (E2 : max (domain recv) = max (domain g)).
  { apply max_equiv. unfold recv, base.
    apply (proj2 (domain_two_reversed _ _ _ _ _ _ _ ND Da Db N)). }
  rewrite E1 in FS. rewrite E2 in FR.
  eapply linear_frame_communication with (Gout:=fetch mid) (a:=a) (t:=t).
  - apply fetch_complete; eauto using nodup_map.
  - unfold mid. rewrite fetch_cons, update_eq. reflexivity.
  - intros D p0 TD V. eapply lts_uses_port; [exact Send| |exact TD|exact V].
    destruct a,b; simpl; auto.
  - intros D p0 TD V. eapply lts_uses_port; [exact Recv| |exact TD|exact V].
    destruct a,b; simpl; auto.
  - eapply frame_ext; [|reflexivity|exact FS].
    intros k. unfold send,base. rewrite fetch_two_reversed by eauto using nodup_map.
    apply set_same. unfold set. rewrite update_neq by congruence.
    eapply fetch_complete; eauto using nodup_map.
  - eapply frame_ext; [|reflexivity|exact FR].
    unfold recv,mid. apply fetch_rehead.
Qed.

Local Lemma fetch_second g a b f t fo to fn tn x :
  a <> b ->
  fetch ((a,f,t)::(b,fn,tn)::g) x =
    set (fetch ((a,f,t)::(b,fo,to)::g)) b fn tn x.
Proof.
  intros N. unfold set, update. rewrite fetch_cons. unfold update.
  destruct (pair_eq x a) eqn:A, (pair_eq x b) eqn:B.
  - apply pair_eq_true in A,B; congruence.
  - rewrite fetch_cons. unfold update. now rewrite A.
  - rewrite fetch_cons. unfold update. now rewrite B.
  - rewrite !fetch_cons. unfold update. rewrite A,B.
    rewrite fetch_cons. unfold update. now rewrite B.
Qed.

Local Lemma ordinary_linear_close g a b t s s1 p p' q q' d1 d2 :
  let base := removeEntry a (removeEntry b g) in
  let send := (a,vis,Chan lin out t)::(b,hid,s)::base in
  let mid := (a,vis,Chan lin empty t)::(b,vis,s1)::base in
  let recv := (a,vis,Chan lin inp t)::(b,ill,s1)::base in
  let dst := (a,vis,Chan lin empty t)::(b,vis,s)::base in
  let ext := (a,vis,Chan lin empty t)::(b,hid,s)::base in
  NoDup (domain g) -> In (a,vis,Chan lin io t) g -> In (b,hid,s) g ->
  lts send p (aOut (fst a) (snd a) (fst b) (snd b)) mid p' d1 ->
  lts recv q (aIn (fst a) (snd a) (fst b) (snd b)) dst q' d2 ->
  frame_transform (max (domain send)) (fetch send) (fetch mid) p p' ->
  frame_transform (max (domain recv)) (fetch recv) (fetch dst) q q' ->
  frame_transform (max (domain g)) (fetch g) (fetch ext)
    (dPar p q) (dNu (fst b) (snd b) (dPar p' q')).
Proof.
  intros base send mid recv dst ext ND A B Send Recv FS FR.
  assert (N : a <> b) by (apply (dup_head_distinct _ _ _ d1)).
  assert (Da : In a (domain g)) by (apply domain_spec; eauto).
  assert (Db : In b (domain g)) by (apply domain_spec; eauto).
  assert (E1 : max (domain send) = max (domain g)).
  { apply max_equiv. unfold send, base.
    apply (proj2 (domain_two_reversed _ _ _ _ _ _ _ ND Da Db N)). }
  assert (E2 : max (domain recv) = max (domain g)).
  { apply max_equiv. unfold recv, base.
    apply (proj2 (domain_two_reversed _ _ _ _ _ _ _ ND Da Db N)). }
  rewrite E1 in FS. rewrite E2 in FR.
  set (M := set (fetch mid) a vis (Chan lin inp t)).
  eapply frames_target_list with (G':=set (fetch dst) b hid s).
  - intros k. unfold ext, dst. apply fetch_second. exact N.
  - eapply frames_closed_com_context with (Gout:=M) (s1:=s1).
    + apply fetch_complete; eauto using nodup_map.
    + unfold M, set. rewrite update_neq by congruence.
      unfold mid. rewrite fetch_cons, update_neq, fetch_cons, update_eq by congruence. reflexivity.
    + unfold dst. rewrite fetch_cons, update_neq, fetch_cons, update_eq by congruence. reflexivity.
    + intros VP VQ A0 F TP TQ J K Pos Safe. unfold M.
      refine (linear_sender _ _ _ a t p p' q A0 F VP VQ _ _ _ _ _ TP TQ J K Pos Safe).
      * apply fetch_complete; eauto using nodup_map.
      * unfold mid. rewrite fetch_cons, update_eq. reflexivity.
      * intros D p0 TD V. eapply lts_uses_port; [exact Send| |exact TD|exact V].
        destruct a,b; simpl; auto.
      * intros D p0 TD V. eapply lts_uses_port; [exact Recv| |exact TD|exact V].
        destruct a,b; simpl; auto.
      * eapply frame_ext; [|reflexivity|exact FS].
        intro k. unfold send,base. rewrite fetch_two_reversed by eauto using nodup_map.
        apply set_same. unfold set. rewrite update_neq by congruence.
        eapply fetch_complete; eauto using nodup_map.
    + eapply frame_ext; [|reflexivity|exact FR]. intro k.
      unfold recv, M, mid.
      rewrite fetch_second with (fo:=vis) (to:=s1) by assumption.
      apply set_congr. apply fetch_rehead.
Qed.

Local Lemma ordinary_un_communication g b s s1 p p' q q' dst :
  let mid := (b,vis,s1)::removeEntry b g in
  NoDup (domain g) -> In (b,vis,s) g ->
  frame_transform (max (domain g)) (fetch g) (fetch mid) p p' ->
  frame_transform (max (domain mid)) (fetch mid) (fetch dst) q q' ->
  frame_transform (max (domain g)) (fetch g) (fetch dst) (dPar p q) (dPar p' q').
Proof.
  intros mid ND H FS FR. eapply frames_com; [exact FS|].
  unfold mid in FR. rewrite (set_bounded_unchanged _ _ _ _ ND) in FR by (apply domain_spec; eauto).
  exact FR.
Qed.

Local Lemma ordinary_un_close g a b s s1 p p' q q' dst d2 :
  let gout := (b,vis,s1)::removeEntry b g in
  let gin := (b,ill,s1)::removeEntry b g in
  NoDup (domain g) -> In (b,hid,s) g -> In (b,vis,s) dst ->
  lts gin q (aIn (fst a) (snd a) (fst b) (snd b)) dst q' d2 ->
  frame_transform (max (domain g)) (fetch g) (fetch gout) p p' ->
  frame_transform (max (domain gin)) (fetch gin) (fetch dst) q q' ->
  frame_transform (max (domain g)) (fetch g)
    (fetch ((b,hid,s)::removeEntry b dst)) (dPar p q) (dNu (fst b) (snd b) (dPar p' q')).
Proof.
  intros gout gin ND H B L U V A F Pos C J Safe.
  destruct (scoped_restrictions _ _ _ C) as [NQ _].
  apply nodup_app_parts in NQ as [NQ _].
  assert (D : NoDup (domain dst)) by (eapply lts_nodup; [exact L|exact NQ|eapply sl_pos_par_right; exact Pos]).
  assert (D0 : fetch g b = Some (hid,s)) by (eapply fetch_complete; eauto using nodup_map).
  assert (D1 : fetch gout b = Some (vis,s1)) by (unfold gout; rewrite fetch_cons, update_eq; reflexivity).
  assert (D2 : fetch dst b = Some (vis,s)) by (eapply fetch_complete; eauto using nodup_map).
  assert (E : frame_transform (max (domain g)) (set (fetch gout) b ill s1) (fetch dst) q q').
  { unfold gin in V. rewrite (set_bounded_unchanged _ _ _ _ ND) in V by (apply domain_spec; eauto).
    eapply frame_ext; [|reflexivity|exact V]. unfold gout. apply fetch_rehead. }
  pose proof (frames_closed_com _ _ _ _ _ _ _ _ _ _ _ D0 D1 D2 U E) as T.
  eapply frames_target_list; [intros k; apply fetch_replaced|exact T|exact Pos|exact C|exact J|exact Safe].
Qed.

Local Lemma source_lin_in_remove t :
  type_remove (Chan lin inp t) (Chan lin inp t) (Chan lin empty t).
Proof.
  split; [constructor|]. split; [constructor; constructor|].
  intros [? [? E]]. discriminate.
Qed.

(* Relate the list environments of each transition to its pointwise effect. *)
Local Lemma lts_frames g p act g' p' nd :
  lts g p act g' p' nd ->
  frame_transform (max (domain g)) (fetch g) (fetch g') p p'.
Proof.
  intro L. induction L.
  - apply frames_par_left. exact IHL.
  - set (a := (a1,a2)) in *. set (b := (b1,b2)) in *.
    pose proof (fetch_complete _ (nodup_map _ pf) _ _ _ H0) as A.
    pose proof (fetch_complete _ (nodup_map _ pf) _ _ _ H1) as B.
    assert (N : a <> b) by (eapply out_distinct; eassumption).
    set (D := set (fetch g) a vis (Chan lin empty t)).
    eapply frames_target_list with (G':=set D b vis t2).
    + intros k. unfold D. apply fetch_two_reversed; auto using nodup_map.
    + eapply frames_output with (G1:=D) (a:=a) (b:=b) (md:=lin) (t:=t).
      * unfold D. econstructor; eauto using source_lin_out_remove.
      * econstructor; [unfold D,set; rewrite update_neq by congruence; exact B|exact H].
  - set (a := (a1,a2)) in *. set (b := (b1,b2)) in *.
    pose proof (fetch_complete _ (nodup_map _ pf) _ _ _ H1) as A.
    pose proof (fetch_complete _ (nodup_map _ pf) _ _ _ H2) as B.
    set (D := set (fetch g) a vis (Chan un pol t)).
    eapply frames_target_list with (G':=set D b vis t2).
    + intros k. rewrite fetch_replaced. apply set_congr. intro j. unfold D. symmetry. apply set_same. exact A.
    + eapply frames_output with (G1:=D) (a:=a) (b:=b) (md:=un) (t:=t).
      * unfold D. econstructor; [exact A|apply remove_un_port; tauto || discriminate].
      * econstructor; [unfold D; rewrite set_same; eassumption|exact H0].
  - set (a := (a1,a2)) in *. set (b := (b1,b2)) in *. set (x := (x1,x2)) in *.
    pose proof (fetch_complete _ (nodup_map _ pf) _ _ _ H1) as A.
    pose proof (fetch_complete _ (nodup_map _ pf) _ _ _ H2) as B.
    assert (N : a <> b) by (eapply input_distinct; eassumption).
    set (D := set (fetch g) a vis (Chan lin empty t)).
    eapply frames_target_list with (G':=set D b vis t2).
    + intros k. unfold D. apply fetch_two_reversed; auto using nodup_map.
    + eapply frames_input with (G1:=D) (a:=a) (b:=b) (x:=x) (md:=lin) (t:=t) (f:=f); try eassumption.
      * unfold D. econstructor; eauto using source_lin_in_remove.
      * unfold D,set. rewrite update_neq by congruence. exact B.
  - set (a := (a1,a2)) in *. set (b := (b1,b2)) in *. set (x := (x1,x2)) in *.
    pose proof (fetch_complete _ (nodup_map _ pf) _ _ _ H2) as A.
    pose proof (fetch_complete _ (nodup_map _ pf) _ _ _ H3) as B.
    set (D := set (fetch g) a vis (Chan un pol t)).
    eapply frames_target_list with (G':=set D b vis t2).
    + intros k. rewrite fetch_replaced. apply set_congr. intro j. unfold D. symmetry. apply set_same. exact A.
    + eapply frames_input with (G1:=D) (a:=a) (b:=b) (x:=x) (md:=un) (t:=t) (f:=f); try eassumption.
      * unfold D. econstructor; [exact A|apply remove_un_port; tauto || discriminate].
      * unfold D. rewrite set_same; eassumption.
  - set (a := (a1,a2)) in *. set (b := (b1,b2)) in *. set (x := (x1,x2)) in *.
    pose proof (fetch_complete _ (nodup_map _ pf) _ _ _ H2) as A.
    pose proof (fetch_complete _ (nodup_map _ pf) _ _ _ H3) as B.
    set (m := max (domain g)) in *.
    unfold q. rewrite dep_relabel_view, secLabs_relabel. fold m.
    intros D F Pos TD J Safe.
    assert (M : mapped (newEntries g (map (shift_key m) (secLabs p)) m ++
                           ((b,vis,t2)::removeEntry b g))
      (overlay (copy_slots m (secLabs p) (fetch g)) (set (fetch g) b vis t2))).
    { intro k. erewrite new_entries_fetch by
        (try apply fetch_bounded; try (intros [j l] K; exact (Pos j l K));
         intros j K; destruct (scoped_restrictions _ _ _ TD) as [_ S];
         destruct (S j K) as [v V]; destruct (join_hidden_left _ _ _ _ _ J V) as [u [t' [_ W]]]; eauto).
      unfold overlay. destruct (copy_slots m (secLabs p) (fetch g) k);
        [reflexivity|apply fetch_replaced]. }
    eapply frames_target_list; [exact M| |exact Pos|exact TD|exact J|exact Safe].
    eapply frames_replication with (a:=a) (x:=x) (p:=pol) (t:=t) (f:=f) (u:=t1); eauto using fetch_bounded.
  - eapply ordinary_linear_communication with (a:=(a1,a2)) (b:=(b1,b2)) (s1:=s1) (t:=t); eassumption.
  - eapply ordinary_linear_close with (a:=(a1,a2)) (b:=(b1,b2)) (s1:=s1) (t:=t); eassumption.
  - eapply ordinary_un_communication with (b:=(b1,b2)) (s1:=s1); eassumption.
  - eapply ordinary_un_close with (a:=(a1,a2)) (b:=(b1,b2)) (s1:=s1); eassumption.
  - set (b := (b1,b2)) in *.
    rewrite (set_bounded_unchanged _ _ _ _ pf) in IHL by (apply domain_spec; eauto).
    eapply frames_open with (k:=b) (t:=t).
    + eapply fetch_complete; eauto using nodup_map.
    + eapply frame_ext; [|reflexivity|exact IHL]. intro k. apply fetch_replaced.
  - subst g. set (b := (b1,b2)) in *.
    assert (M : max (domain (h1 ++ (b,vis,t)::h2)) = max (domain (h1 ++ (b,hid,t)::h2))).
    { rewrite !domains_append. reflexivity. }
    rewrite M in IHL.
    intros D F Pos TD J Safe.
    destruct (scoped_restrictions _ _ _ TD) as [N _]. simpl in N.
    apply nodup_app_parts in N as [N _].
    assert (N' : NoDup (domain (h' ++ (b,vis,t')::h''))).
    { eapply lts_nodup; [exact L|exact N|eapply scope_body_pos with (k:=b); exact Pos]. }
    eapply frames_target_list; [intros k; apply fetch_middle; exact N'| |exact Pos|exact TD|exact J|exact Safe].
    eapply frames_hide with (k:=b) (t:=t) (G':=fetch (h' ++ (b,vis,t')::h'')) (t':=t').
    + apply fetch_complete; [exact (nodup_map _ pf)|apply in_app_iff; right; now left].
    + apply fetch_complete; [exact (nodup_map _ N')|apply in_app_iff; right; now left].
    + eapply frame_ext; [|reflexivity|exact IHL]. intro k. apply fetch_middle; exact pf.
  - apply frames_par_right. exact IHL.
  - apply frames_swap_par.
    eapply ordinary_linear_communication with (a:=(a1,a2)) (b:=(b1,b2)) (s1:=s1) (t:=t); eassumption.
  - eapply frames_swap_closed with (k:=(b1,b2)).
    eapply ordinary_linear_close with (a:=(a1,a2)) (b:=(b1,b2)) (s1:=s1) (t:=t); eassumption.
  - apply frames_swap_par.
    eapply ordinary_un_communication with (b:=(b1,b2)) (s1:=s1); eassumption.
  - eapply frames_swap_closed with (k:=(b1,b2)).
    eapply ordinary_un_close with (a:=(a1,a2)) (b:=(b1,b2)) (s1:=s1); eassumption.
Qed.

Theorem sr :
  forall g p a g' p' nd_pf pf pf',
    sl_pos p ->
    typeCheck g pf p ->
    lts g p a g' p' nd_pf ->
    typeCheck g' pf' p'.
Proof.
  intros g p a g' p' nd_pf pf pf' Pos Typ Step.
  pose proof (typeCheck_to_m _ _ _ Typ nd_pf) as T.
  assert (Safe : frame_safe p (neutral (fetch g))).
  { intros k f t _ H. unfold neutral in H.
    destruct (fetch g k) as [[q s]|]; inversion H; subst.
    apply empty_part_discardable. }
  destruct (lts_frames _ _ _ _ _ _ Step _ _ Pos T (neutral_join _) Safe)
    as [A [F [T' [R J]]]].
  destruct (scoped_restrictions _ _ _ T) as [S _].
  assert (ND : NoDup (domain g')) by (eapply lts_nodup; eassumption).
  assert (B : max (domain g) <= max (domain g')).
  { apply max_le. intros k K. apply max_upper, fetch_domain.
    apply fetch_domain in K as [[f t] E].
    specialize (R k). specialize (J k).
    unfold neutral in R. rewrite E in R. inversion R; subst.
    repeat match goal with E : Some _ = F k |- _ => rewrite <- E in J; clear E end.
    inversion J; subst; eauto. }
  assert (Frame : forall k f t, F k = Some (f,t) -> f <> hid /\ discardable t).
  { intros k f t V. specialize (R k). rewrite V in R.
    inversion R; subst; auto. unfold neutral in *.
    destruct (fetch g k) as [[ff ty]|] eqn:W; try discriminate.
    assert (C : discardable (empty_part ty)) by apply empty_part_discardable.
    destruct ff; simpl in *;
      repeat match goal with H : Some _ = Some _ |- _ => inversion H; clear H; subst end;
      repeat match goal with H : raised_flag _ _ |- _ => inversion H; clear H; subst end;
      split; try discriminate; eauto using raised_discardable. }
  assert (E : forall k, A k = fetch g' k).
  { intro k. specialize (J k). inversion J; subst; auto.
    match goal with C : join_entry _ ?w _ , K : Some ?w = F k |- _ =>
      destruct w as [f t]; destruct (Frame k f t (eq_sym K)) as [NF DF];
      inversion C; subst
    end.
    all: repeat match goal with H : flag_plus _ _ _ |- _ => inversion H; clear H; subst end.
    all: try solve [contradiction|reflexivity].
    all: cbn in DF; subst.
    all: match goal with H : pol_plus _ empty _ |- _ => inversion H; subst; reflexivity end. }
  apply (m_to_typeCheck _ _ _ T' g' pf'); auto.
  intro k; symmetry; apply E.
Qed.

