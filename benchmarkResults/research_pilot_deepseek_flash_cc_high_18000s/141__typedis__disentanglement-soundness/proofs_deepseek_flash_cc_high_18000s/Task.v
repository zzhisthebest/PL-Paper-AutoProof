From stdpp Require Import relations gmap.
From dislog.lang Require Import syntax semantics reducible disentangled.
From dislog.types Require Import typing syntactical.
From stdpp Require Import binders.
From Stdlib Require Import Lia RelationClasses.
From stdpp Require Import sets strings.

(* Pure operational definitions from src/logic/wpg_adequacy.v. *)
Definition step '(σ,α,G,T,e) '(σ',α',G',T',e') :=
  lang.semantics.step σ α G T e σ' α' G' T' e'.

Definition safe he σ α G T e :=
  (is_val e /\ is_leaf T) \/ reducible he σ α G T e.

Definition always_safe_and_disentangled (allow_oob:bool) (e:expr) :=
  forall t0 σ' α' G' T' e',
  rtc step (∅,∅,{[(t0,t0)]},(Leaf t0),e) (σ',α',G',T',e') ->
  safe allow_oob σ' α' G' T' e' /\ disentangled G' α' T' e'.


(* ------------------------------------------------------------------ *)
(* Auxiliary lemmas for the soundness proof (added; definitions above  *)
(* are unchanged).                                                     *)
(* ------------------------------------------------------------------ *)

Lemma reachable_trans : forall (G:graph) x y z,
  reachable G x y -> reachable G y z -> reachable G x z.
Proof. intros; eapply rtc_trans; eauto. Qed.

Lemma reachable_mono : forall (G G':graph) x y,
  G ⊆ G' -> reachable G x y -> reachable G' x y.
Proof.
  intros G G' x y Hsub H. induction H as [z|z w u Hzw Hwu IH].
  - apply rtc_refl.
  - eapply rtc_l; [|eassumption]. unfold edge in *. apply Hsub; auto.
Qed.

Lemma abef_mono : forall (G G':graph) α t l,
  G ⊆ G' -> abef G α t l -> abef G' α t l.
Proof.
  intros G G' α t l Hsub H. unfold abef in *.
  destruct (α !! l) as [v'|] eqn:E; [|contradiction].
  apply reachable_mono with (G:=G); auto.
Qed.

Lemma abef_mono_α : forall (G:graph) α α' t l,
  α ⊆ α' -> abef G α t l -> abef G α' t l.
Proof.
  intros G α α' t l Hsub H. unfold abef in *.
  destruct (α !! l) as [v|] eqn:E; [|contradiction].
  rewrite map_subseteq_spec in Hsub. specialize (Hsub l v E).
  rewrite Hsub. exact H.
Qed.

Lemma graph_fork_edge_l : forall (G:graph) t0 t1 t2,
  edge (graph_fork G t0 t1 t2) t0 t1.
Proof. intros. unfold graph_fork, graph_upd, edges, edge. set_solver. Qed.

Lemma graph_fork_edge_r : forall (G:graph) t0 t1 t2,
  edge (graph_fork G t0 t1 t2) t0 t2.
Proof. intros. unfold graph_fork, graph_upd, edges, edge. set_solver. Qed.

Lemma graph_join_edge_l : forall (G:graph) t1 t2 t3,
  edge (graph_join G t1 t2 t3) t1 t3.
Proof. intros. unfold graph_join, graph_upd, edges, edge. set_solver. Qed.

Lemma graph_join_edge_r : forall (G:graph) t1 t2 t3,
  edge (graph_join G t1 t2 t3) t2 t3.
Proof. intros. unfold graph_join, graph_upd, edges, edge. set_solver. Qed.

Lemma graph_upd_subset : forall (G:graph) x X, G ⊆ graph_upd G x X.
Proof. intros. unfold graph_upd. set_solver. Qed.

Lemma graph_fork_subset : forall (G:graph) t v w, G ⊆ graph_fork G t v w.
Proof. intros. apply graph_upd_subset. Qed.

Lemma graph_join_subset : forall (G:graph) t v w, G ⊆ graph_join G t v w.
Proof. intros. unfold graph_join. transitivity (graph_upd G t {[w]}).
  - apply graph_upd_subset. - apply graph_upd_subset. Qed.


(* ---------- root timestamp and the graph invariant ---------- *)
Fixpoint root (T:task_tree) : timestamp :=
  match T with Leaf t => t | Node t _ _ => t end.

Fixpoint GInv (G:graph) (T:task_tree) : Prop :=
  match T with
  | Leaf _ => True
  | Node t T1 T2 => reachable G t (root T1) /\ reachable G t (root T2)
                    /\ GInv G T1 /\ GInv G T2
  end.

Lemma GInv_root_frontier : forall G T, GInv G T ->
  forall l, l ∈ frontier T -> reachable G (root T) l.
Proof.
  intros G T. induction T as [t|t T1 IH1 T2 IH2]; simpl; intros HI l Hl.
  - apply elem_of_singleton in Hl. subst. apply rtc_refl.
  - destruct HI as (H1 & H2 & HI1 & HI2).
    apply elem_of_union in Hl as [Hl|Hl].
    + eapply reachable_trans; [exact H1 | apply IH1; auto].
    + eapply reachable_trans; [exact H2 | apply IH2; auto].
Qed.

Lemma GInv_mono : forall (G G':graph) T, G ⊆ G' -> GInv G T -> GInv G' T.
Proof.
  intros G G' T. induction T as [t|t T1 IH1 T2 IH2]; simpl; intros Hsub HI; auto.
  destruct HI as (H1 & H2 & HI1 & HI2). repeat split; auto;
    eapply reachable_mono; eauto.
Qed.

Lemma sched_step_G : forall σ α G T e σ' α' G' T' e',
  sched_step σ α G T e σ' α' G' T' e' -> G ⊆ G' /\ root T' = root T.
Proof.
  intros σ α G T e σ' α' G' T' e' Hs. inversion Hs; subst; simpl; split; auto.
  - apply graph_fork_subset.
  - apply graph_join_subset.
Qed.

Lemma sched_step_GInv : forall σ α G T e σ' α' G' T' e',
  sched_step σ α G T e σ' α' G' T' e' -> GInv G T -> GInv G' T'.
Proof.
  intros σ α G T e σ' α' G' T' e' Hs. inversion Hs; subst; simpl; intros HI; auto.
  repeat split; try exact I;
    apply rtc_once; [apply graph_fork_edge_l | apply graph_fork_edge_r].
Qed.

Lemma step_G : forall σ α G T e σ' α' G' T' e',
  lang.semantics.step σ α G T e σ' α' G' T' e' -> G ⊆ G' /\ root T' = root T.
Proof.
  intros σ α G T e σ' α' G' T' e' Hs. induction Hs.
  - exact (sched_step_G σ α G T2 e2 σ' α' G' T2' e2' H).
  - destruct IHHs as (Hsub & Hr). split; auto.
  - destruct IHHs as (Hsub & Hr). split; auto.
  - destruct IHHs as (Hsub & Hr). split; auto.
Qed.

Lemma step_GInv : forall σ α G T e σ' α' G' T' e',
  lang.semantics.step σ α G T e σ' α' G' T' e' -> GInv G T -> GInv G' T'.
Proof.
  intros σ α G T e σ' α' G' T' e' Hs. induction Hs; simpl; intros HI.
  - exact (sched_step_GInv σ α G T2 e2 σ' α' G' T2' e2' H HI).
  - exact (IHHs HI).
  - destruct HI as (H1 & H2 & HI1 & HI2).
    destruct (step_G σ α G T1 e1 σ' α' G' T1' e1' Hs) as (Hsub & Hr). rewrite Hr.
    split; [ | split; [ | split ] ].
    + eapply reachable_mono; eauto.
    + eapply reachable_mono; eauto.
    + apply IHHs; auto.
    + apply GInv_mono with (G:=G); auto.
  - destruct HI as (H1 & H2 & HI1 & HI2).
    destruct (step_G σ α G T2 e2 σ' α' G' T2' e2' Hs) as (Hsub & Hr). rewrite Hr.
    split; [ | split; [ | split ] ].
    + eapply reachable_mono; eauto.
    + eapply reachable_mono; eauto.
    + apply GInv_mono with (G:=G); auto.
    + apply IHHs; auto.
Qed.


Lemma head_step_α_sub : forall G t σ α e σ' α' e',
  head_step G t σ α e σ' α' e' -> α ⊆ α'.
Proof.
  intros G t σ α e σ' α' e' H. induction H; try reflexivity;
    try subst α';
    try (apply insert_subseteq; apply not_elem_of_dom; assumption).
Qed.

Fixpoint locs_storable (st:storable) : gset loc :=
  match st with
  | SBlock vs => ⋃ (locs <$> vs)
  | SProd v1 v2 => locs v1 ∪ locs v2
  | SInL v => locs v
  | SInR v => locs v
  | SClo b bs e => locs e
  end.

Lemma locs_vals_expr : forall (vs:list val),
  ⋃ (locs <$> ((fun v => Val v) <$> vs)) = ⋃ (locs <$> vs).
Proof.
  induction vs as [|v vs IH]; cbn [list_fmap].
  - reflexivity.
  - change (locs_val v ∪ ⋃ (locs <$> ((fun v => Val v) <$> vs)) =
            locs_val v ∪ ⋃ (locs <$> vs)).
    rewrite IH. reflexivity.
Qed.

Lemma locs_fill_item_eq : forall (K:ctx) (e:expr),
  locs (fill_item K e) = locs K ∪ locs e.
Proof.
  intros K e. destruct K; unfold locs, location_expr, location_ctx, location_val;
    cbn [fill_item locs_expr locs_ctx locs_val].
  all: try (rewrite fmap_app).
  all: try (rewrite union_list_app).
  all: try (rewrite union_list_cons).
  all: try (rewrite locs_vals_expr).
  all: try set_solver.
  change (locs_val v ∪ ⋃ ((locs_expr <$> (Val <$> l)) ++ (locs_expr <$> e :: l0))
          = locs_val v ∪ ⋃ (locs_val <$> l) ∪ ⋃ (locs_expr <$> l0) ∪ locs_expr e).
  rewrite union_list_app_L.
  change (locs_val v ∪ (⋃ (locs_expr <$> (Val <$> l)) ∪ ⋃ (locs_expr e :: (locs_expr <$> l0)))
          = locs_val v ∪ ⋃ (locs_val <$> l) ∪ ⋃ (locs_expr <$> l0) ∪ locs_expr e).
  rewrite union_list_cons.
  rewrite locs_vals_expr.
  set_solver.
Qed.

Definition store_locs (σ:store) : gset loc :=
  ⋃ ((fun '(_,st) => locs_storable st) <$> map_to_list σ).

Lemma elem_of_store_locs : forall (σ:store) l0,
  l0 ∈ store_locs σ <->
  exists l st, σ !! l = Some st /\ l0 ∈ locs_storable st.
Proof.
  intros σ l0. unfold store_locs. rewrite elem_of_union_list. split.
  - intros (X & HX & Hx). apply list_elem_of_fmap in HX.
    destruct HX as (p & Heq & Hp). destruct p as [l st]. cbn in Heq. subst X. cbn in Hx.
    exists l, st. split; [|exact Hx]. apply elem_of_map_to_list. exact Hp.
  - intros (l & st & Hl & Hx). exists (locs_storable st). split.
    + apply list_elem_of_fmap. exists (l,st). split; [reflexivity|apply elem_of_map_to_list; exact Hl].
    + exact Hx.
Qed.

Lemma store_locs_empty : store_locs (∅ : store) = ∅.
Proof.
  unfold store_locs. rewrite map_to_list_empty. cbn [list_fmap]. apply union_list_nil.
Qed.

Lemma elem_of_list_insert_inv : forall (A:Type) (l:list A) i (x y:A),
  y ∈ <[i:=x]> l -> y = x \/ y ∈ l.
Proof.
  intros A l i x y H. apply list_elem_of_lookup_1 in H.
  destruct H as (j & Hj).
  rewrite list_lookup_insert in Hj.
  destruct (decide (i = j /\ i < length l)) as [[e _]|_].
  - left. cbn in Hj. injection Hj as <-. reflexivity.
  - right. cbn in Hj. exact (list_elem_of_lookup_2 l j y Hj).
Qed.

Lemma locs_storable_block_update : forall (bs:list val) i v,
  locs_storable (SBlock (<[i:=v]> bs)) ⊆ locs_storable (SBlock bs) ∪ locs v.
Proof.
  intros bs i v l0 H. cbn [locs_storable] in *.
  apply elem_of_union_list in H. destruct H as (X & HX & Hx).
  apply list_elem_of_fmap in HX. destruct HX as (y & Heq & Hy). subst X.
  destruct (elem_of_list_insert_inv _ _ _ _ _ Hy) as [e|Hy'].
  - subst y. apply elem_of_union. right. exact Hx.
  - apply elem_of_union. left. apply elem_of_union_list. exists (locs y).
    split; [|exact Hx]. apply list_elem_of_fmap. exists y. split; [reflexivity|exact Hy'].
Qed.

Lemma locs_storable_block_replicate : forall n (v:val),
  locs_storable (SBlock (replicate n v)) ⊆ locs v.
Proof.
  induction n as [|n IH]; intros v; cbn [replicate locs_storable list_fmap].
  - set_solver.
  - pose proof (IH v). set_solver.
Qed.

Lemma store_locs_insert_subset : forall (σ:store) l st,
  store_locs (<[l:=st]> σ) ⊆ store_locs σ ∪ locs_storable st.
Proof.
  intros σ l st l0 H. apply elem_of_store_locs in H.
  destruct H as (l' & st' & Hlook & Hmem).
  destruct (decide (l' = l)) as [e|ne].
  - subst l'. rewrite lookup_insert_eq in Hlook. injection Hlook as <-.
    apply elem_of_union. right. exact Hmem.
  - rewrite lookup_insert_ne in Hlook by auto.
    apply elem_of_union. left. apply elem_of_store_locs. exists l', st'. auto.
Qed.

Lemma locs_storable_store_subset : forall (σ:store) l st,
  σ !! l = Some st -> locs_storable st ⊆ store_locs σ.
Proof.
  intros σ l st Hl l0 Hx. apply elem_of_store_locs. exists l, st. auto.
Qed.

Lemma head_step_σ_dom_sub : forall G t σ α e σ' α' e',
  head_step G t σ α e σ' α' e' -> dom σ ⊆ dom σ'.
Proof.
  intros G t σ α e σ' α' e' H. induction H; try reflexivity.
  all: try (rewrite dom_insert; set_solver).
  all: try (subst σ'; rewrite dom_insert; set_solver).
  all: try (subst σ'; destruct (bool_decide (v = v0)); [rewrite dom_insert; set_solver|reflexivity]).
Qed.

Lemma sched_step_σ_dom_sub : forall σ α G T e σ' α' G' T' e',
  sched_step σ α G T e σ' α' G' T' e' -> dom σ ⊆ dom σ'.
Proof.
  intros σ α G T e σ' α' G' T' e' Hs. inversion Hs; subst.
  - eapply head_step_σ_dom_sub; eauto.
  - reflexivity.
  - rewrite dom_insert. set_solver.
Qed.

Lemma sched_step_α_sub : forall σ α G T e σ' α' G' T' e',
  sched_step σ α G T e σ' α' G' T' e' -> α ⊆ α'.
Proof.
  intros σ α G T e σ' α' G' T' e' Hs. inversion Hs; subst; simpl; auto.
  - eapply head_step_α_sub; eauto.
  - apply insert_subseteq. apply not_elem_of_dom; eauto.
Qed.

Lemma step_α_sub : forall σ α G T e σ' α' G' T' e',
  lang.semantics.step σ α G T e σ' α' G' T' e' -> α ⊆ α'.
Proof.
  intros σ α G T e σ' α' G' T' e' Hs. induction Hs.
  - exact (sched_step_α_sub σ α G T2 e2 σ' α' G' T2' e2' H).
  - exact IHHs.
  - exact IHHs.
  - exact IHHs.
Qed.


(* ------------------------------------------------------------------ *)
(* Semantic core: fuel-indexed value interpretation (work in progress).*)
(* ------------------------------------------------------------------ *)
Record world : Type := World { wst : store; wam : amap; wgr : graph }.

Definition tsval := gmap string timestamp.
Definition tget (τ:tsval) (x:string) : timestamp := default (to_timestamp 0) (τ !! x).
Definition tyval := gmap string typ.

Definition bupd (x:binder) (ρ:typ) (σ:tyval) : tyval :=
  match x with BAnon => σ | BNamed x' => <[x' := ρ]> σ end.

Lemma bupd_overwrite : forall (x:binder) ρ ρ' (σ:tyval),
  bupd x ρ' (bupd x ρ σ) = bupd x ρ' σ.
Proof.
  intros [|x] ρ ρ' σ; simpl.
  - reflexivity.
  - unfold bupd. simpl. apply insert_insert_eq.
Qed.

Lemma bupd_comm : forall (x y:binder) ρx ρy (σ:tyval), x ≠ y ->
  bupd x ρx (bupd y ρy σ) = bupd y ρy (bupd x ρx σ).
Proof.
  intros [|x] [|y] ρx ρy σ H; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold bupd. simpl. symmetry. apply insert_insert_ne.
    intro e. congruence.
Qed.

Fixpoint semroot (m:nat) (τ:tsval) (ρ:typ) {struct m} : option timestamp :=
  match m with
  | 0 => None
  | S m' =>
    match ρ with
    | TTypat _ δ | TRec _ _ δ => Some (tget τ δ)
    | TApp ρ0 δ => match ρ0 with
                   | TLam (BNamed x) ρ0' => semroot m' τ (tsubst_typ {[x:=δ]} ρ0')
                   | _ => None
                   end
    | _ => None
    end
  end.

Definition csat (W:world) (τ:tsval) (Δ:constraints) : Prop :=
  forall x y, (x,y) ∈ Δ -> reachable (wgr W) (tget τ x) (tget τ y).

Lemma csat_empty : forall W τ, csat W τ ∅.
Proof. intros W τ x y H. set_solver. Qed.

Lemma csat_mono : forall W τ Δ Δ', Δ ⊆ Δ' -> csat W τ Δ' -> csat W τ Δ.
Proof.
  intros W τ Δ Δ' Hsub H x y Hxy.
  apply H. apply elem_of_subseteq in Hsub. apply Hsub. exact Hxy.
Qed.

Lemma csat_union : forall W τ Δ1 Δ2,
  (csat W τ (Δ1 ∪ Δ2) <-> csat W τ Δ1 /\ csat W τ Δ2).
Proof.
  intros W τ Δ1 Δ2. split.
  - intros H. split; intros x y Hxy; apply H; set_solver.
  - intros (H1 & H2) x y Hxy. apply elem_of_union in Hxy as [Hxy|Hxy]; [apply H1|apply H2]; exact Hxy.
Qed.

Lemma csat_mono_G : forall (σ:store) α G G' τ Δ,
  G ⊆ G' -> csat (World σ α G) τ Δ -> csat (World σ α G') τ Δ.
Proof.
  intros σ α G G' τ Δ Hsub H x y Hxy.
  unfold csat in *. apply H in Hxy.
  eapply reachable_mono; eauto.
Qed.

Lemma csat_singleton : forall W τ (x y:string),
  csat W τ ({[(x,y)]} : constraints) <-> reachable (wgr W) (tget τ x) (tget τ y).
Proof.
  intros W τ x y. split.
  - intros H. apply H. rewrite elem_of_singleton. reflexivity.
  - intros H x' y' Hxy. rewrite elem_of_singleton in Hxy.
    injection Hxy as e1 e2. subst x'. subst y'. exact H.
Qed.

Lemma csat_add : forall W τ (x y:string) (Δ:constraints),
  (csat W τ ({[(x,y)]} ∪ Δ) <-> reachable (wgr W) (tget τ x) (tget τ y) /\ csat W τ Δ).
Proof.
  intros W τ x y Δ. rewrite csat_union, csat_singleton. tauto.
Qed.

Definition tcomp (τ:tsval) (m:gmap string string) : tsval :=
  ((fun v => tget τ v) <$> m) ∪ (τ ∖ ((fun _ => to_timestamp 0) <$> m)).

Lemma tget_tcomp_find_opt : forall τ m x,
  tget (tcomp τ m) x = tget τ (find_opt m x).
Proof.
  intros. unfold tget, tcomp, find_opt.
  rewrite (lookup_union ((fun v => tget τ v) <$> m) (τ ∖ ((fun _ => to_timestamp 0) <$> m)) x).
  rewrite (lookup_difference τ ((fun _ => to_timestamp 0) <$> m) x).
  rewrite (lookup_fmap (fun v => tget τ v) m x).
  rewrite (lookup_fmap (fun _ => to_timestamp 0) m x).
  destruct (m !! x) as [v|] eqn:E.
  - simpl; reflexivity.
  - simpl. f_equal. apply option_union_left_id.
Qed.

Lemma csat_tsubst : forall W τ (m:gmap string string) (Δ:constraints),
  csat W (tcomp τ m) Δ <-> csat W τ (tsubst_constraints m Δ).
Proof.
  intros W τ m Δ. unfold csat, tsubst_constraints. split.
  - intros H x y Hxy. apply elem_of_map in Hxy.
    destruct Hxy as (q & Hq & Hqin). destruct q as [a b]. simpl in Hq.
    injection Hq as e1 e2. subst x. subst y.
    pose proof (H a b Hqin) as Hr.
    rewrite !tget_tcomp_find_opt in Hr. exact Hr.
  - intros H x y Hxy.
    rewrite !tget_tcomp_find_opt.
    apply H. apply elem_of_map. exists (x,y). split; [reflexivity|exact Hxy].
Qed.

Lemma reachable_of_csat : forall W τ (Δ:constraints) x y,
  csat W τ Δ -> graph.reachable Δ x y -> reachable (wgr W) (tget τ x) (tget τ y).
Proof.
  intros W τ Δ x y Hcs Hr.
  induction Hr as [z | a b c Hab Hbc IH].
  - apply rtc_refl.
  - eapply reachable_trans.
    + apply Hcs. exact Hab.
    + exact IH.
Qed.

Lemma csat_all_reachable : forall W τ (Δ Δ':constraints),
  csat W τ Δ -> all_reachable Δ Δ' -> csat W τ Δ'.
Proof.
  intros W τ Δ Δ' Hcs Ha x y Hxy.
  unfold all_reachable, set_Forall in Ha.
  specialize (Ha (x,y) Hxy).
  eapply reachable_of_csat; eauto.
Qed.

Definition root_reaches (W:world) τ (ρ:typ) (δ:timestamp) : Prop :=
  forall m r, semroot m τ ρ = Some r -> reachable (wgr W) r δ.

Lemma root_reaches_mono_G : forall (σ:store) α G G' τ ρ δ,
  G ⊆ G' -> root_reaches (World σ α G) τ ρ δ -> root_reaches (World σ α G') τ ρ δ.
Proof.
  intros σ α G G' τ ρ δ Hsub H m r Hs. unfold root_reaches in *.
  eapply reachable_mono.
  - exact Hsub.
  - apply (H m r Hs).
Qed.

Lemma root_reaches_simple_root : forall W τ ρ δ,
  simple_root ρ = Some δ -> root_reaches W τ ρ (tget τ δ).
Proof.
  intros W τ ρ δ Hs m r Hr. unfold root_reaches. fold (root_reaches W τ ρ (tget τ δ)).
  destruct ρ as [x|b|σt δ0|bd ρ0|ρ0 d|x k ρ0|x σt δ0]; cbn [simple_root] in Hs; try discriminate.
  - injection Hs as e. subst δ0. destruct m as [|m']; [discriminate Hr|].
    cbn [semroot] in Hr. injection Hr as e. subst r. apply rtc_refl.
  - injection Hs as e. subst δ0. destruct m as [|m']; [discriminate Hr|].
    cbn [semroot] in Hr. injection Hr as e. subst r. apply rtc_refl.
Qed.

Lemma root_reaches_trans : forall W τ ρ δ δ',
  reachable (wgr W) δ δ' -> root_reaches W τ ρ δ -> root_reaches W τ ρ δ'.
Proof.
  intros W τ ρ δ δ' Hr H m r Hs.
  unfold root_reaches in H.
  eapply reachable_trans with (y := δ).
  - apply (H m r). exact Hs.
  - exact Hr.
Qed.


Fixpoint Real (n:nat) (W:world) (Ω:gmap string nat) (τ:tsval) (σ:tyval) (ρ:typ) (v:val) {struct n} : Prop :=
  match n with
  | 0 => True
  | S n' =>
    match ρ with
    | TVar x => match σ !! x with Some ρ' => Real n' W Ω τ σ ρ' v | None => True end
    | TBase TBUnit => v = VUnit
    | TBase TBInt => exists z, v = VInt z
    | TBase TBBool => exists b, v = VBool b
    | TForall x k ρ0 =>
        forall ρ', wk_typ (binsert x k Ω) ρ' k ->
          Real n' W Ω τ (bupd x ρ' σ) ρ0 v
    | TLam _ _ => True
    | TApp ρ0 δ => match ρ0 with
                   | TLam (BNamed x) ρ0' => Real n' W Ω τ σ (tsubst_typ {[x:=δ]} ρ0') v
                   | _ => True
                   end
    | TRec x σt δ =>
        exists v', v = VFold v' /\
          Real n' W Ω τ σ (TTypat (vsubst_typat x (TRec x σt δ) σt) δ) v'
    | TTypat σt δ =>
        match σt with
        | TArray ρ0 =>
            exists l bs, v = VLoc l /\ (wst W) !! l = Some (SBlock bs) /\
              abef (wgr W) (wam W) (tget τ δ) l /\
              (forall b, b ∈ bs -> Real n' W Ω τ σ ρ0 b) /\
              root_reaches W τ ρ0 (tget τ δ)
        | TProd ρ1 ρ2 =>
            exists l v1 v2, v = VLoc l /\ (wst W) !! l = Some (SProd v1 v2) /\
              abef (wgr W) (wam W) (tget τ δ) l /\
              Real n' W Ω τ σ ρ1 v1 /\ Real n' W Ω τ σ ρ2 v2
        | TSum ρ1 ρ2 =>
            (exists l v1, v = VLoc l /\ (wst W) !! l = Some (SInL v1) /\
                abef (wgr W) (wam W) (tget τ δ) l /\ Real n' W Ω τ σ ρ1 v1)
            \/
            (exists l v2, v = VLoc l /\ (wst W) !! l = Some (SInR v2) /\
                abef (wgr W) (wam W) (tget τ δ) l /\ Real n' W Ω τ σ ρ2 v2)
        | TArrow _ _ _ _ _ =>
            (exists c, v = VCode c)
            \/ (exists l b a e, v = VLoc l /\ (wst W) !! l = Some (SClo b a e) /\
                  abef (wgr W) (wam W) (tget τ δ) l)
        end
    end
  end.



(* one-step unfolding of Real, with the recursive instance abstracted *)
Definition RealF
  (rec : world -> gmap string nat -> tsval -> tyval -> typ -> val -> Prop)
  (W:world) (Ω:gmap string nat) (τ:tsval) (σ:tyval) (ρ:typ) (v:val) : Prop :=
  match ρ with
  | TVar x => match σ !! x with Some ρ' => rec W Ω τ σ ρ' v | None => True end
  | TBase TBUnit => v = VUnit
  | TBase TBInt => exists z, v = VInt z
  | TBase TBBool => exists b, v = VBool b
  | TForall x k ρ0 =>
      forall ρ', wk_typ (binsert x k Ω) ρ' k -> rec W Ω τ (bupd x ρ' σ) ρ0 v
  | TLam _ _ => True
  | TApp ρ0 δ => match ρ0 with
                 | TLam (BNamed x) ρ0' => rec W Ω τ σ (tsubst_typ {[x:=δ]} ρ0') v
                 | _ => True
                 end
  | TRec x σt δ =>
      exists v', v = VFold v' /\
        rec W Ω τ σ (TTypat (vsubst_typat x (TRec x σt δ) σt) δ) v'
  | TTypat σt δ =>
      match σt with
      | TArray ρ0 =>
          exists l bs, v = VLoc l /\ (wst W) !! l = Some (SBlock bs) /\
            abef (wgr W) (wam W) (tget τ δ) l /\
            (forall b, b ∈ bs -> rec W Ω τ σ ρ0 b) /\
            root_reaches W τ ρ0 (tget τ δ)
      | TProd ρ1 ρ2 =>
          exists l v1 v2, v = VLoc l /\ (wst W) !! l = Some (SProd v1 v2) /\
            abef (wgr W) (wam W) (tget τ δ) l /\
            rec W Ω τ σ ρ1 v1 /\ rec W Ω τ σ ρ2 v2
      | TSum ρ1 ρ2 =>
          (exists l v1, v = VLoc l /\ (wst W) !! l = Some (SInL v1) /\
              abef (wgr W) (wam W) (tget τ δ) l /\ rec W Ω τ σ ρ1 v1)
          \/
          (exists l v2, v = VLoc l /\ (wst W) !! l = Some (SInR v2) /\
              abef (wgr W) (wam W) (tget τ δ) l /\ rec W Ω τ σ ρ2 v2)
      | TArrow _ _ _ _ _ =>
          (exists c, v = VCode c)
          \/ (exists l b a e, v = VLoc l /\ (wst W) !! l = Some (SClo b a e) /\
                abef (wgr W) (wam W) (tget τ δ) l)
      end
  end.

Lemma Real_S_eq : forall n W Ω τ σ ρ v,
  Real (S n) W Ω τ σ ρ v = RealF (Real n) W Ω τ σ ρ v.
Proof. intros. reflexivity. Qed.

Lemma RealF_anti :
  forall (rec1 rec2 : world -> gmap string nat -> tsval -> tyval -> typ -> val -> Prop),
  (forall W Ω τ σ ρ v, rec1 W Ω τ σ ρ v -> rec2 W Ω τ σ ρ v) ->
  forall W Ω τ σ ρ v, RealF rec1 W Ω τ σ ρ v -> RealF rec2 W Ω τ σ ρ v.
Proof.
  intros rec1 rec2 Hrec W Ω τ σ ρ v.
  destruct ρ as [x|b|x d|xb ρ0|ρ0 d|x k ρ0|x σt d]; simpl.
  - destruct (σ !! x) as [ρ'|]; auto.
  - destruct b; auto.
  - destruct x as [ρ0|ρ1 ρ2|ρ1 ρ2| _ _ _ _ _]; simpl.
    + intros (l & bs & He & Hs & Hab & Hbs & Hr). exists l, bs.
      split; [exact He|]. split; [exact Hs|]. split; [exact Hab|]. split.
      * intros b Hb. apply Hrec. apply Hbs; auto.
      * exact Hr.
    + intros (l & v1 & v2 & He & Hs & Hab & H1 & H2). exists l, v1, v2.
      split; [exact He|]. split; [exact Hs|]. split; [exact Hab|].
      split; [apply Hrec; exact H1 | apply Hrec; exact H2].
    + intros [(l & v1 & He & Hs & Hab & H1)|(l & v2 & He & Hs & Hab & H2)].
      * left. exists l, v1. split; [exact He|]. split; [exact Hs|].
        split; [exact Hab | apply Hrec; exact H1].
      * right. exists l, v2. split; [exact He|]. split; [exact Hs|].
        split; [exact Hab | apply Hrec; exact H2].
    + intros [(c & He)|(l & bd & a & e & He & Hs & Hab)].
      * left. exists c. exact He.
      * right. exists l, bd, a, e. split; [exact He|]. split; [exact Hs|]. exact Hab.
  - auto.
  - destruct ρ0 as [y|bb|y d'| yb ρ1|ρ1 d'|y kk ρ1|y σt' d']; simpl; auto;
      try (destruct yb as [| yy]; simpl; auto; apply Hrec; auto).
  - intros H1 ρ' Hwk. apply Hrec. apply H1; auto.
  - intros (v' & He & H). exists v'. split; [exact He | apply Hrec; exact H].
Qed.

Lemma Real_anti : forall n W Ω τ σ ρ v,
  Real (S n) W Ω τ σ ρ v -> Real n W Ω τ σ ρ v.
Proof.
  induction n as [|n IH].
  - intros. exact I.
  - intros W Ω τ σ ρ v H.
    rewrite Real_S_eq in H.
    rewrite Real_S_eq.
    eapply RealF_anti; [ | exact H].
    intros W' Ω' τ' σ' ρ' v' H'. apply IH. exact H'.
Qed.


Lemma RealF_mono_G :
  forall (rec : world -> gmap string nat -> tsval -> tyval -> typ -> val -> Prop),
  (forall W W' Ω τ σ ρ v, wst W = wst W' -> wam W = wam W' -> wgr W ⊆ wgr W' ->
     rec W Ω τ σ ρ v -> rec W' Ω τ σ ρ v) ->
  forall W W' Ω τ σ ρ v, wst W = wst W' -> wam W = wam W' -> wgr W ⊆ wgr W' ->
     RealF rec W Ω τ σ ρ v -> RealF rec W' Ω τ σ ρ v.
Proof.
  intros rec Hrec W W' Ω τ σ ρ v Hst Ham HG H.
  destruct W as [σW αW GW]; destruct W' as [σW' αW' GW']; simpl in *.
  destruct ρ as [x|b|x d|xb ρ0|ρ0 d|x k ρ0|x σt d]; simpl in *.
  - destruct (σ !! x) as [ρ'|]; auto. apply (Hrec (World σW αW GW) (World σW' αW' GW') Ω τ σ ρ' v); auto.
  - destruct b; simpl in *; auto.
  - destruct x as [ρ0|ρ1 ρ2|ρ1 ρ2|bs Δ0 d0 ρs ρf]; simpl in *.
    + destruct H as (l & bl & He & Hs & Hab & Hbs & Hr). exists l, bl.
      split; [exact He|]. split.
      * rewrite <- Hst. exact Hs.
      * split.
        -- rewrite <- Ham. apply abef_mono with (G:=GW); auto.
        -- split.
           ++ intros bb Hb. apply (Hrec (World σW αW GW) (World σW' αW' GW') Ω τ σ ρ0 bb); auto.
           ++ apply root_reaches_mono_G with (σ:=σW) (α:=αW) (G:=GW) (G':=GW'); auto.
    + destruct H as (l & v1 & v2 & He & Hs & Hab & H1 & H2). exists l, v1, v2.
      split; [exact He|]. split.
      * rewrite <- Hst. exact Hs.
      * split.
        -- rewrite <- Ham. apply abef_mono with (G:=GW); auto.
        -- split.
           ++ apply (Hrec (World σW αW GW) (World σW' αW' GW') Ω τ σ ρ1 v1); auto.
           ++ apply (Hrec (World σW αW GW) (World σW' αW' GW') Ω τ σ ρ2 v2); auto.
    + destruct H as [(l & v1 & He & Hs & Hab & H1)|(l & v2 & He & Hs & Hab & H2)].
      * left. exists l, v1. split; [exact He|]. split.
        { rewrite <- Hst. exact Hs. }
        split.
        { rewrite <- Ham. apply abef_mono with (G:=GW); auto. }
        apply (Hrec (World σW αW GW) (World σW' αW' GW') Ω τ σ ρ1 v1); auto.
      * right. exists l, v2. split; [exact He|]. split.
        { rewrite <- Hst. exact Hs. }
        split.
        { rewrite <- Ham. apply abef_mono with (G:=GW); auto. }
        apply (Hrec (World σW αW GW) (World σW' αW' GW') Ω τ σ ρ2 v2); auto.
    + destruct H as [(c & He)|(l & bd & a & e & He & Hs & Hab)].
      * left. exists c. exact He.
      * right. exists l, bd, a, e. split; [exact He|]. split.
        -- rewrite <- Hst. exact Hs.
        -- rewrite <- Ham. apply abef_mono with (G:=GW); auto.
  - auto.
  - destruct ρ0 as [y|bb|y d'|yb ρ1|ρ1 d'|y kk ρ1|y σt' d']; simpl; auto.
    destruct yb as [|yy]; simpl; auto.
    apply (Hrec (World σW αW GW) (World σW' αW' GW') Ω τ σ (tsubst_typ {[yy:=d]} ρ1) v); auto.
  - intros ρ' Hwk. apply (Hrec (World σW αW GW) (World σW' αW' GW') Ω τ (bupd x ρ' σ) ρ0 v); auto.
  - destruct H as (v' & He & Hv). exists v'. split; [exact He|].
    apply (Hrec (World σW αW GW) (World σW' αW' GW') Ω τ σ (TTypat (vsubst_typat x (TRec x σt d) σt) d) v'); auto.
Qed.

Lemma Real_mono_G : forall n W W' Ω τ σ ρ v,
  wst W = wst W' -> wam W = wam W' -> wgr W ⊆ wgr W' ->
  Real n W Ω τ σ ρ v -> Real n W' Ω τ σ ρ v.
Proof.
  intros n. induction n as [|n IH]; intros W W' Ω τ σ ρ v Hst Ham HG H.
  - exact I.
  - rewrite Real_S_eq in H. rewrite Real_S_eq.
    eapply RealF_mono_G.
    + intros W0 W1 Ω0 τ0 σ0 ρ0 v0 Hst0 Ham0 HG0 Hr.
      exact (IH W0 W1 Ω0 τ0 σ0 ρ0 v0 Hst0 Ham0 HG0 Hr).
    + exact Hst.
    + exact Ham.
    + exact HG.
    + exact H.
Qed.

Lemma RealF_mono_α :
  forall (rec : world -> gmap string nat -> tsval -> tyval -> typ -> val -> Prop),
  (forall W W' Ω τ σ ρ v, wst W = wst W' -> wam W ⊆ wam W' -> wgr W = wgr W' ->
     rec W Ω τ σ ρ v -> rec W' Ω τ σ ρ v) ->
  forall W W' Ω τ σ ρ v, wst W = wst W' -> wam W ⊆ wam W' -> wgr W = wgr W' ->
     RealF rec W Ω τ σ ρ v -> RealF rec W' Ω τ σ ρ v.
Proof.
  intros rec Hrec W W' Ω τ σ ρ v Hst Hsub HG H.
  destruct W as [σW αW GW]; destruct W' as [σW' αW' GW']; simpl in *.
  subst σW'. subst GW'.
  destruct ρ as [x|b|x d|xb ρ0|ρ0 d|x k ρ0|x σt d]; simpl in *.
  - destruct (σ !! x) as [ρ'|]; auto.
    apply (Hrec (World σW αW GW) (World σW αW' GW) Ω τ σ ρ' v eq_refl Hsub eq_refl); auto.
  - destruct b; simpl in *; auto.
  - destruct x as [ρ0|ρ1 ρ2|ρ1 ρ2|bs Δ0 d0 ρs ρf]; simpl in *.
    + destruct H as (l & bl & He & Hs & Hab & Hbs & Hr). exists l, bl.
      split; [exact He|]. split; [exact Hs|]. split.
      * apply abef_mono_α with (α:=αW); auto.
      * split.
        -- intros bb Hb. apply (Hrec (World σW αW GW) (World σW αW' GW) Ω τ σ ρ0 bb eq_refl Hsub eq_refl); auto.
        -- exact Hr.
    + destruct H as (l & v1 & v2 & He & Hs & Hab & H1 & H2). exists l, v1, v2.
      split; [exact He|]. split; [exact Hs|]. split.
      * apply abef_mono_α with (α:=αW); auto.
      * split.
        -- apply (Hrec (World σW αW GW) (World σW αW' GW) Ω τ σ ρ1 v1 eq_refl Hsub eq_refl); auto.
        -- apply (Hrec (World σW αW GW) (World σW αW' GW) Ω τ σ ρ2 v2 eq_refl Hsub eq_refl); auto.
    + destruct H as [(l & v1 & He & Hs & Hab & H1)|(l & v2 & He & Hs & Hab & H2)].
      * left. exists l, v1. split; [exact He|]. split; [exact Hs|]. split.
        { apply abef_mono_α with (α:=αW); auto. }
        apply (Hrec (World σW αW GW) (World σW αW' GW) Ω τ σ ρ1 v1 eq_refl Hsub eq_refl); auto.
      * right. exists l, v2. split; [exact He|]. split; [exact Hs|]. split.
        { apply abef_mono_α with (α:=αW); auto. }
        apply (Hrec (World σW αW GW) (World σW αW' GW) Ω τ σ ρ2 v2 eq_refl Hsub eq_refl); auto.
    + destruct H as [(c & He)|(l & bd & a & e & He & Hs & Hab)].
      * left. exists c. exact He.
      * right. exists l, bd, a, e. split; [exact He|]. split; [exact Hs|].
        apply abef_mono_α with (α:=αW); auto.
  - auto.
  - destruct ρ0 as [y|bb|y d'|yb ρ1|ρ1 d'|y kk ρ1|y σt' d']; simpl; auto.
    destruct yb as [|yy]; simpl; auto.
    apply (Hrec (World σW αW GW) (World σW αW' GW) Ω τ σ (tsubst_typ {[yy:=d]} ρ1) v eq_refl Hsub eq_refl); auto.
  - intros ρ' Hwk.
    apply (Hrec (World σW αW GW) (World σW αW' GW) Ω τ (bupd x ρ' σ) ρ0 v eq_refl Hsub eq_refl); auto.
  - destruct H as (v' & He & Hv). exists v'. split; [exact He|].
    apply (Hrec (World σW αW GW) (World σW αW' GW) Ω τ σ (TTypat (vsubst_typat x (TRec x σt d) σt) d) v' eq_refl Hsub eq_refl); auto.
Qed.

Lemma Real_mono_α : forall n W W' Ω τ σ ρ v,
  wst W = wst W' -> wam W ⊆ wam W' -> wgr W = wgr W' ->
  Real n W Ω τ σ ρ v -> Real n W' Ω τ σ ρ v.
Proof.
  intros n. induction n as [|n IH]; intros W W' Ω τ σ ρ v Hst Hsub HG H.
  - exact I.
  - rewrite Real_S_eq in H. rewrite Real_S_eq.
    eapply RealF_mono_α.
    + intros W0 W1 Ω0 τ0 σ0 ρ0 v0 Hst0 Hsub0 HG0 Hr.
      exact (IH W0 W1 Ω0 τ0 σ0 ρ0 v0 Hst0 Hsub0 HG0 Hr).
    + exact Hst.
    + exact Hsub.
    + exact HG.
    + exact H.
Qed.

Lemma lookup_store_mono : forall (σ σ':store) l v,
  σ ⊆ σ' -> σ !! l = Some v -> σ' !! l = Some v.
Proof.
  intros σ σ' l v Hsub H. rewrite map_subseteq_spec in Hsub. apply Hsub. exact H.
Qed.

Lemma RealF_mono :
  forall (rec : world -> gmap string nat -> tsval -> tyval -> typ -> val -> Prop),
  (forall W W' Ω τ σ ρ v, wst W ⊆ wst W' -> wam W ⊆ wam W' -> wgr W ⊆ wgr W' ->
     rec W Ω τ σ ρ v -> rec W' Ω τ σ ρ v) ->
  forall W W' Ω τ σ ρ v, wst W ⊆ wst W' -> wam W ⊆ wam W' -> wgr W ⊆ wgr W' ->
     RealF rec W Ω τ σ ρ v -> RealF rec W' Ω τ σ ρ v.
Proof.
  intros rec Hrec W W' Ω τ σ ρ v Hst Hsub HG H.
  destruct W as [σW αW GW]; destruct W' as [σW' αW' GW']; simpl in *.
  destruct ρ as [x|b|x d|xb ρ0|ρ0 d|x k ρ0|x σt d]; simpl in *.
  - destruct (σ !! x) as [ρ'|]; auto.
    apply (Hrec (World σW αW GW) (World σW' αW' GW') Ω τ σ ρ' v); auto.
  - destruct b; simpl in *; auto.
  - destruct x as [ρ0|ρ1 ρ2|ρ1 ρ2|bs Δ0 d0 ρs ρf]; simpl in *.
    + destruct H as (l & bl & He & Hs & Hab & Hbs & Hr). exists l, bl.
      split; [exact He|]. split.
      * apply (lookup_store_mono σW σW' l (SBlock bl)); auto.
      * split.
        -- apply abef_mono_α with (α:=αW); auto. apply abef_mono with (G:=GW); auto.
        -- split.
           ++ intros bb Hb. apply (Hrec (World σW αW GW) (World σW' αW' GW') Ω τ σ ρ0 bb); auto.
           ++ apply root_reaches_mono_G with (σ:=σW) (α:=αW) (G:=GW) (G':=GW'); auto.
    + destruct H as (l & v1 & v2 & He & Hs & Hab & H1 & H2). exists l, v1, v2.
      split; [exact He|]. split.
      * apply (lookup_store_mono σW σW' l (SProd v1 v2)); auto.
      * split.
        -- apply abef_mono_α with (α:=αW); auto. apply abef_mono with (G:=GW); auto.
        -- split.
           ++ apply (Hrec (World σW αW GW) (World σW' αW' GW') Ω τ σ ρ1 v1); auto.
           ++ apply (Hrec (World σW αW GW) (World σW' αW' GW') Ω τ σ ρ2 v2); auto.
    + destruct H as [(l & v1 & He & Hs & Hab & H1)|(l & v2 & He & Hs & Hab & H2)].
      * left. exists l, v1. split; [exact He|]. split.
        { apply (lookup_store_mono σW σW' l (SInL v1)); auto. }
        split.
        { apply abef_mono_α with (α:=αW); auto. apply abef_mono with (G:=GW); auto. }
        apply (Hrec (World σW αW GW) (World σW' αW' GW') Ω τ σ ρ1 v1); auto.
      * right. exists l, v2. split; [exact He|]. split.
        { apply (lookup_store_mono σW σW' l (SInR v2)); auto. }
        split.
        { apply abef_mono_α with (α:=αW); auto. apply abef_mono with (G:=GW); auto. }
        apply (Hrec (World σW αW GW) (World σW' αW' GW') Ω τ σ ρ2 v2); auto.
    + destruct H as [(c & He)|(l & bd & a & e & He & Hs & Hab)].
      * left. exists c. exact He.
      * right. exists l, bd, a, e. split; [exact He|]. split.
        -- apply (lookup_store_mono σW σW' l (SClo bd a e)); auto.
        -- apply abef_mono_α with (α:=αW); auto. apply abef_mono with (G:=GW); auto.
  - auto.
  - destruct ρ0 as [y|bb|y d'|yb ρ1|ρ1 d'|y kk ρ1|y σt' d']; simpl; auto.
    destruct yb as [|yy]; simpl; auto.
    apply (Hrec (World σW αW GW) (World σW' αW' GW') Ω τ σ (tsubst_typ {[yy:=d]} ρ1) v); auto.
  - intros ρ' Hwk.
    apply (Hrec (World σW αW GW) (World σW' αW' GW') Ω τ (bupd x ρ' σ) ρ0 v); auto.
  - destruct H as (v' & He & Hv). exists v'. split; [exact He|].
    apply (Hrec (World σW αW GW) (World σW' αW' GW') Ω τ σ (TTypat (vsubst_typat x (TRec x σt d) σt) d) v'); auto.
Qed.

Lemma Real_mono : forall n W W' Ω τ σ ρ v,
  wst W ⊆ wst W' -> wam W ⊆ wam W' -> wgr W ⊆ wgr W' ->
  Real n W Ω τ σ ρ v -> Real n W' Ω τ σ ρ v.
Proof.
  intros n. induction n as [|n IH]; intros W W' Ω τ σ ρ v Hst Hsub HG H.
  - exact I.
  - rewrite Real_S_eq in H. rewrite Real_S_eq.
    eapply RealF_mono.
    + intros W0 W1 Ω0 τ0 σ0 ρ0 v0 Hst0 Hsub0 HG0 Hr.
      exact (IH W0 W1 Ω0 τ0 σ0 ρ0 v0 Hst0 Hsub0 HG0 Hr).
    + exact Hst.
    + exact Hsub.
    + exact HG.
    + exact H.
Qed.

Lemma Real_array_inv : forall n W Ω τ σ ρ0 δ v,
  Real (S n) W Ω τ σ (TTypat (TArray ρ0) δ) v ->
  exists l bs, v = VLoc l /\ (wst W) !! l = Some (SBlock bs) /\
    abef (wgr W) (wam W) (tget τ δ) l /\
    (forall b, b ∈ bs -> Real n W Ω τ σ ρ0 b) /\
    root_reaches W τ ρ0 (tget τ δ).
Proof. intros. simpl in H. exact H. Qed.

Lemma Real_prod_inv : forall n W Ω τ σ ρ1 ρ2 δ v,
  Real (S n) W Ω τ σ (TTypat (TProd ρ1 ρ2) δ) v ->
  exists l v1 v2, v = VLoc l /\ (wst W) !! l = Some (SProd v1 v2) /\
    abef (wgr W) (wam W) (tget τ δ) l /\
    Real n W Ω τ σ ρ1 v1 /\ Real n W Ω τ σ ρ2 v2.
Proof. intros. simpl in H. exact H. Qed.

Lemma Real_sum_inv : forall n W Ω τ σ ρ1 ρ2 δ v,
  Real (S n) W Ω τ σ (TTypat (TSum ρ1 ρ2) δ) v ->
  (exists l v1, v = VLoc l /\ (wst W) !! l = Some (SInL v1) /\
      abef (wgr W) (wam W) (tget τ δ) l /\ Real n W Ω τ σ ρ1 v1)
  \/ (exists l v2, v = VLoc l /\ (wst W) !! l = Some (SInR v2) /\
      abef (wgr W) (wam W) (tget τ δ) l /\ Real n W Ω τ σ ρ2 v2).
Proof. intros. simpl in H. exact H. Qed.

Lemma Real_arrow_inv : forall n W Ω τ σ bs Δ δs ρs ρf δ v,
  Real (S n) W Ω τ σ (TTypat (TArrow bs Δ δs ρs ρf) δ) v ->
  (exists c, v = VCode c) \/
  (exists l b a e, v = VLoc l /\ (wst W) !! l = Some (SClo b a e) /\
      abef (wgr W) (wam W) (tget τ δ) l).
Proof. intros. simpl in H. exact H. Qed.

Lemma Real_rec_inv : forall n W Ω τ σ x σt δ v,
  Real (S n) W Ω τ σ (TRec x σt δ) v ->
  exists v', v = VFold v' /\
    Real n W Ω τ σ (TTypat (vsubst_typat x (TRec x σt δ) σt) δ) v'.
Proof. intros. simpl in H. exact H. Qed.

(* ------------------------------------------------------------------ *)
(* Semantic value interpretation (list-based, fuel-indexed).           *)
(* ------------------------------------------------------------------ *)
Definition SType := list timestamp -> world -> val -> Prop.
Definition SemF := nat -> SType.
Definition valenv := gmap string SemF.

Definition venv0 : valenv := ∅.

Definition vget (ξ:valenv) (n:nat) (x:string) : SType :=
  match ξ !! x with Some Sf => Sf n | None => fun _ _ _ => True end.

Definition vupd (ξ:valenv) (x:string) (S:SemF) : valenv := <[x := S]> ξ.

Definition bupdS (ξ:valenv) (x:binder) (S:SemF) : valenv :=
  match x with BAnon => ξ | BNamed x' => vupd ξ x' S end.

Definition tupd (τ:tsval) (x:binder) (t:timestamp) : tsval :=
  match x with BAnon => τ | BNamed x' => <[x' := t]> τ end.

Fixpoint interp (n:nat) (ξ:valenv) (τ:tsval) (ρ:typ) (ts:list timestamp) (W:world) (v:val) {struct n} : Prop :=
  match n with
  | 0 => True
  | S n' =>
    match ρ with
    | TVar x => vget ξ n x ts W v
    | TBase TBUnit => v = VUnit
    | TBase TBInt => exists z, v = VInt z
    | TBase TBBool => exists b, v = VBool b
    | TForall x k0 ρ0 => forall S : SemF, interp n' (bupdS ξ x S) τ ρ0 [] W v
    | TLam x ρ0 => match ts with
                   | t :: ts' => interp n' ξ (tupd τ x t) ρ0 ts' W v
                   | nil => True
                   end
    | TApp ρ0 δ => interp n' ξ τ ρ0 (tget τ δ :: ts) W v
    | TRec x σt δ =>
        exists v', v = VFold v' /\
          interp n' ξ τ (TTypat (vsubst_typat x (TRec x σt δ) σt) δ) [] W v'
    | TTypat σt δ =>
        match σt with
        | TArray ρ0 =>
            exists l bs, v = VLoc l /\ (wst W) !! l = Some (SBlock bs) /\
              abef (wgr W) (wam W) (tget τ δ) l /\
              (forall b, b ∈ bs -> interp n' ξ τ ρ0 [] W b) /\
              root_reaches W τ ρ0 (tget τ δ)
        | TProd ρ1 ρ2 =>
            exists l v1 v2, v = VLoc l /\ (wst W) !! l = Some (SProd v1 v2) /\
              abef (wgr W) (wam W) (tget τ δ) l /\
              interp n' ξ τ ρ1 [] W v1 /\ interp n' ξ τ ρ2 [] W v2
        | TSum ρ1 ρ2 =>
            (exists l v1, v = VLoc l /\ (wst W) !! l = Some (SInL v1) /\
                abef (wgr W) (wam W) (tget τ δ) l /\ interp n' ξ τ ρ1 [] W v1)
            \/
            (exists l v2, v = VLoc l /\ (wst W) !! l = Some (SInR v2) /\
                abef (wgr W) (wam W) (tget τ δ) l /\ interp n' ξ τ ρ2 [] W v2)
        | TArrow _ _ _ _ _ =>
            (exists c, v = VCode c)
            \/ (exists l b a e, v = VLoc l /\ (wst W) !! l = Some (SClo b a e) /\
                  abef (wgr W) (wam W) (tget τ δ) l)
        end
    end
  end.

Definition RealS (n:nat) (ξ:valenv) (τ:tsval) (W:world) (ρ:typ) (v:val) : Prop :=
  interp n ξ τ ρ [] W v.

Lemma interp_unit_eq : forall n ξ τ ts W v,
  interp (S n) ξ τ (TBase TBUnit) ts W v = (v = VUnit).
Proof. intros. reflexivity. Qed.

Lemma interp_bool_eq : forall n ξ τ ts W v,
  interp (S n) ξ τ (TBase TBBool) ts W v = (exists b, v = VBool b).
Proof. intros. reflexivity. Qed.


Lemma interp_typat_abef : forall n ξ τ σt δ W v,
  interp (S n) ξ τ (TTypat σt δ) [] W v ->
  all_abef (wgr W) (wam W) (tget τ δ) (locs_val v).
Proof.
  intros n ξ τ σt δ W v H.
  destruct σt as [ρ0|ρ1 ρ2|ρ1 ρ2|bs Δ δs ρs ρf]; simpl in H.
  - destruct H as (l & bl & He & Hs & Hab & Hbs & Hr). subst v. simpl.
    unfold all_abef, set_Forall. intros x Hx. rewrite elem_of_singleton in Hx.
    subst x. exact Hab.
  - destruct H as (l & v1 & v2 & He & Hs & Hab & H1 & H2). subst v. simpl.
    unfold all_abef, set_Forall. intros x Hx. rewrite elem_of_singleton in Hx.
    subst x. exact Hab.
  - destruct H as [(l & v1 & He & Hs & Hab & H1)|(l & v2 & He & Hs & Hab & H2)].
    + subst v. simpl. unfold all_abef, set_Forall. intros x Hx.
      rewrite elem_of_singleton in Hx. subst x. exact Hab.
    + subst v. simpl. unfold all_abef, set_Forall. intros x Hx.
      rewrite elem_of_singleton in Hx. subst x. exact Hab.
  - destruct H as [(c & He)|(l & bd & a & e & He & Hs & Hab)].
    + subst v. simpl. unfold all_abef, set_Forall. intros x Hx.
      rewrite elem_of_empty in Hx. contradiction.
    + subst v. simpl. unfold all_abef, set_Forall. intros x Hx.
      rewrite elem_of_singleton in Hx. subst x. exact Hab.
Qed.

Lemma interp_array_inv : forall n ξ τ ρ0 δ W v,
  interp (S n) ξ τ (TTypat (TArray ρ0) δ) [] W v ->
  exists l bs, v = VLoc l /\ (wst W) !! l = Some (SBlock bs) /\
    abef (wgr W) (wam W) (tget τ δ) l /\
    (forall b, b ∈ bs -> interp n ξ τ ρ0 [] W b) /\
    root_reaches W τ ρ0 (tget τ δ).
Proof. intros. simpl in H. exact H. Qed.

Lemma interp_prod_inv : forall n ξ τ ρ1 ρ2 δ W v,
  interp (S n) ξ τ (TTypat (TProd ρ1 ρ2) δ) [] W v ->
  exists l v1 v2, v = VLoc l /\ (wst W) !! l = Some (SProd v1 v2) /\
    abef (wgr W) (wam W) (tget τ δ) l /\
    interp n ξ τ ρ1 [] W v1 /\ interp n ξ τ ρ2 [] W v2.
Proof. intros. simpl in H. exact H. Qed.

Lemma interp_sum_inv : forall n ξ τ ρ1 ρ2 δ W v,
  interp (S n) ξ τ (TTypat (TSum ρ1 ρ2) δ) [] W v ->
  (exists l v1, v = VLoc l /\ (wst W) !! l = Some (SInL v1) /\
      abef (wgr W) (wam W) (tget τ δ) l /\ interp n ξ τ ρ1 [] W v1)
  \/ (exists l v2, v = VLoc l /\ (wst W) !! l = Some (SInR v2) /\
      abef (wgr W) (wam W) (tget τ δ) l /\ interp n ξ τ ρ2 [] W v2).
Proof. intros. simpl in H. exact H. Qed.

Lemma interp_arrow_inv : forall n ξ τ bs Δ δs ρs ρf δ W v,
  interp (S n) ξ τ (TTypat (TArrow bs Δ δs ρs ρf) δ) [] W v ->
  (exists c, v = VCode c) \/
  (exists l bd a e, v = VLoc l /\ (wst W) !! l = Some (SClo bd a e) /\
      abef (wgr W) (wam W) (tget τ δ) l).
Proof. intros. simpl in H. exact H. Qed.

Lemma interp_rec_inv : forall n ξ τ x σt δ W v,
  interp (S n) ξ τ (TRec x σt δ) [] W v ->
  exists v', v = VFold v' /\
    interp n ξ τ (TTypat (vsubst_typat x (TRec x σt δ) σt) δ) [] W v'.
Proof. intros. simpl in H. exact H. Qed.

Lemma bupdS_overwrite : forall ξ (x:binder) S,
  bupdS (bupdS ξ x S) x S = bupdS ξ x S.
Proof.
  intros ξ [|x] S; simpl.
  - reflexivity.
  - unfold vupd. apply insert_insert_eq.
Qed.

Lemma bupdS_comm : forall ξ (x y:binder) Sx Sy, x ≠ y ->
  bupdS (bupdS ξ x Sx) y Sy = bupdS (bupdS ξ y Sy) x Sx.
Proof.
  intros ξ [|x] [|y] Sx Sy Hneq; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - symmetry. apply insert_insert_ne.
    intro e. apply Hneq. f_equal. exact e.
Qed.

Lemma tget_tupd_ne : forall τ (y z:string) t,
  y ≠ z -> tget (tupd τ (BNamed y) t) z = tget τ z.
Proof. intros. unfold tget. cbn [tupd].
  rewrite (lookup_insert_ne τ y z t); auto. Qed.

Lemma tget_insert_ne : forall τ (y z:string) t,
  y ≠ z -> tget (<[y:=t]> τ) z = tget τ z.
Proof. intros. unfold tget. rewrite (lookup_insert_ne τ y z t); auto. Qed.

Lemma tupd_overwrite : forall τ (x:binder) t t',
  tupd (tupd τ x t) x t' = tupd τ x t'.
Proof.
  intros τ [|x] t t'; simpl.
  - reflexivity.
  - unfold tupd. simpl. apply insert_insert_eq.
Qed.

Lemma tupd_comm : forall τ (x y:binder) tx ty, x ≠ y ->
  tupd (tupd τ x tx) y ty = tupd (tupd τ y ty) x tx.
Proof.
  intros τ [|x] [|y] tx ty H; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold tupd. simpl. symmetry. apply insert_insert_ne.
    intro e. congruence.
Qed.

Lemma vget_vupd_eq : forall ξ x S n ts W v,
  vget (vupd ξ x S) n x ts W v <-> S n ts W v.
Proof.
  intros. unfold vget, vupd. rewrite (lookup_insert_eq ξ x S). tauto.
Qed.

Lemma vget_vupd_ne : forall ξ x y S n ts W v, x ≠ y ->
  vget (vupd ξ x S) n y ts W v <-> vget ξ n y ts W v.
Proof.
  intros. unfold vget, vupd. rewrite (lookup_insert_ne ξ x y S) by auto. tauto.
Qed.

Lemma vget_bupdS_named : forall ξ x S n ts W v,
  vget (bupdS ξ (BNamed x) S) n x ts W v <-> S n ts W v.
Proof. intros. cbn [bupdS]. apply vget_vupd_eq. Qed.

Lemma vget_bupdS_named_ne : forall ξ x y S n ts W v, x ≠ y ->
  vget (bupdS ξ (BNamed x) S) n y ts W v <-> vget ξ n y ts W v.
Proof. intros. cbn [bupdS]. apply vget_vupd_ne; auto. Qed.

Lemma vget_bupdS_anon : forall ξ x S n ts W v,
  vget (bupdS ξ BAnon S) n x ts W v <-> vget ξ n x ts W v.
Proof. intros. reflexivity. Qed.


(* ---------- disentanglement is monotone in the graph ---------- *)


Lemma dom_subseteq_of_map_sub : forall (α α':amap), α ⊆ α' -> dom α ⊆ dom α'.
Proof.
  intros α α' Hsub. rewrite map_subseteq_spec in Hsub.
  intros l Hl. apply elem_of_dom in Hl. destruct Hl as (v & Hv).
  apply elem_of_dom. exists v. exact (Hsub l v Hv).
Qed.

Lemma step_σ_dom_sub : forall σ α G T e σ' α' G' T' e',
  lang.semantics.step σ α G T e σ' α' G' T' e' -> dom σ ⊆ dom σ'.
Proof.
  intros σ α G T e σ' α' G' T' e' Hs. induction Hs.
  - eapply sched_step_σ_dom_sub; eauto.
  - exact IHHs.
  - exact IHHs.
  - exact IHHs.
Qed.

Lemma all_abef_mono_G : forall (G G':graph) α t L,
  G ⊆ G' -> all_abef G α t L -> all_abef G' α t L.
Proof.
  intros G G' α t L Hsub H. unfold all_abef in *.
  eapply set_Forall_impl; [exact H|].
  intros l Hl. apply abef_mono with (G:=G); auto.
Qed.

Lemma all_abef_mono_α : forall (G:graph) α α' t L,
  α ⊆ α' -> all_abef G α t L -> all_abef G α' t L.
Proof.
  intros G α α' t L Hsub H. unfold all_abef in *.
  eapply set_Forall_impl; [exact H|].
  intros l Hl. unfold abef in *.
  destruct (α !! l) as [v|] eqn:E; [|contradiction].
  rewrite map_subseteq_spec in Hsub. specialize (Hsub l v E).
  rewrite Hsub. exact Hl.
Qed.

Lemma all_abef_union : forall (G:graph) α t (L1 L2:gset loc),
  all_abef G α t (L1 ∪ L2) <-> all_abef G α t L1 /\ all_abef G α t L2.
Proof.
  intros G α t L1 L2. unfold all_abef, set_Forall. split.
  - intros H. split; intros l Hl; apply H; apply elem_of_union; auto.
  - intros (H1 & H2) l Hl. apply elem_of_union in Hl as [Hl|Hl]; auto.
Qed.

Lemma all_abef_subseteq : forall (G:graph) α t (L1 L2:gset loc),
  L1 ⊆ L2 -> all_abef G α t L2 -> all_abef G α t L1.
Proof.
  intros G α t L1 L2 Hsub H. unfold all_abef, set_Forall in *.
  intros l Hl. apply H. apply Hsub. exact Hl.
Qed.

Lemma all_abef_trans : forall (G:graph) α t t' L,
  reachable G t t' -> all_abef G α t L -> all_abef G α t' L.
Proof.
  intros G α t t' L Hr H. unfold all_abef, abef in *.
  eapply set_Forall_impl; [exact H|].
  intros l Hl. unfold abef in Hl. unfold abef.
  destruct (α !! l) as [v|] eqn:E; [|contradiction].
  eapply reachable_trans; eauto.
Qed.

Lemma sForall_all_abef_mono_G : forall (G G':graph) α (L:gset loc) (TS:gset timestamp),
  G ⊆ G' -> set_Forall (fun t => all_abef G α t L) TS ->
  set_Forall (fun t => all_abef G' α t L) TS.
Proof.
  intros G G' α L TS Hsub H.
  eapply set_Forall_impl; [exact H|].
  intros t Ht. apply all_abef_mono_G with (G:=G); auto.
Qed.

Lemma disentangled_mono_G : forall (G G':graph) α T e,
  G ⊆ G' -> disentangled G α T e -> disentangled G' α T e.
Proof.
  intros G G' α T e Hsub H. induction H as
    [G0 α0 t0 e0 Hab | G0 α0 t0 T1 T2 K e0 Hd IHd Hsf | G0 α0 T1 T2 e1 e2 t0 H1 IH1 H2 IH2].
  - apply DELeaf. apply all_abef_mono_G with (G:=G0); auto.
  - apply DEBind.
    + apply IHd. auto.
    + apply sForall_all_abef_mono_G with (G:=G0); auto.
  - apply DEPar; auto.
Qed.


Inductive DInv (G:graph) (α:amap) : task_tree -> expr -> Prop :=
| DI_leaf : forall t e, all_abef G α t (locs e) -> DInv G α (Leaf t) e
| DI_par : forall t T1 T2 e1 e2,
    DInv G α T1 e1 -> DInv G α T2 e2 -> DInv G α (Node t T1 T2) (RunPar e1 e2)
| DI_bind : forall t T1 T2 K e,
    DInv G α (Node t T1 T2) e -> all_abef G α t (locs K) ->
    DInv G α (Node t T1 T2) (fill_item K e).

Lemma DInv_disentangled : forall G α T e,
  GInv G T -> DInv G α T e -> disentangled G α T e.
Proof.
  intros G α T e HG HD. induction HD.
  - apply DELeaf; auto.
  - simpl in HG. destruct HG as (Hr1 & Hr2 & HG1 & HG2). apply DEPar; eauto.
  - simpl in HG.
    apply DEBind.
    + apply IHHD. exact HG.
    + unfold set_Forall. intros t' Ht'.
      destruct HG as (Hr1 & Hr2 & HG1 & HG2).
      apply elem_of_union in Ht' as [Ht'|Ht'].
    * apply all_abef_trans with (t:=t).
      -- apply reachable_trans with (y := root T1); [exact Hr1 | ].
         apply GInv_root_frontier; auto.
      -- exact H.
    * apply all_abef_trans with (t:=t).
      -- apply reachable_trans with (y := root T2); [exact Hr2 | ].
         apply GInv_root_frontier; auto.
      -- exact H.
Qed.


Lemma disentangled_mono_α : forall (G:graph) α α' T e,
  α ⊆ α' -> disentangled G α T e -> disentangled G α' T e.
Proof.
  intros G α α' T e Hsub H. revert α' Hsub.
  induction H as [G0 α0 t0 e0 Hab | G0 α0 t0 T1 T2 K e0 Hd IHd Hsf | G0 α0 T1 T2 e1 e2 t0 H1 IH1 H2 IH2];
    intros α' Hsub.
  - apply DELeaf. apply all_abef_mono_α with (α:=α0); auto.
  - apply DEBind.
    + apply IHd. exact Hsub.
    + unfold set_Forall in *. intros t Ht. apply all_abef_mono_α with (α:=α0); auto.
  - apply DEPar; auto.
Qed.

Lemma DInv_mono_G : forall (G G':graph) α T e,
  G ⊆ G' -> DInv G α T e -> DInv G' α T e.
Proof.
  intros G G' α T e Hsub H. revert G' Hsub.
  induction H as [t e Hab | t T1 T2 e1 e2 H1 IH1 H2 IH2 | t T1 T2 K e Hd IHd Hab];
    intros G' Hsub.
  - apply DI_leaf. apply all_abef_mono_G with (G:=G); auto.
  - apply DI_par; auto.
  - apply DI_bind.
    + apply IHd. exact Hsub.
    + apply all_abef_mono_G with (G:=G); auto.
Qed.

Lemma DInv_mono_α : forall (G:graph) α α' T e,
  α ⊆ α' -> DInv G α T e -> DInv G α' T e.
Proof.
  intros G α α' T e Hsub H. revert α' Hsub.
  induction H as [t e Hab | t T1 T2 e1 e2 H1 IH1 H2 IH2 | t T1 T2 K e Hd IHd Hab];
    intros α' Hsub.
  - apply DI_leaf. apply all_abef_mono_α with (α:=α); auto.
  - apply DI_par; auto.
  - apply DI_bind.
    + apply IHd. exact Hsub.
    + apply all_abef_mono_α with (α:=α); auto.
Qed.

(* ---------- per-task invariant implies disentangled ---------- *)
Lemma DInv_fork : forall (G:graph) α t0 t1 t2 (v1 v2:val),
  DInv G α (Leaf t0) (Par v1 v2) ->
  DInv (graph_fork G t0 t1 t2) α
       (Node t0 (Leaf t1) (Leaf t2))
       (RunPar (Call v1 [Val VUnit]) (Call v2 [Val VUnit])).
Proof.
  intros G α t0 t1 t2 v1 v2 H. inversion H as [t e Hab | t T1 T2 e1 e2 H1 H2 | t T1 T2 K e Hd Hab];
    subst; clear H.
  apply DI_par.
  - apply DI_leaf.
    assert (Hl : locs (Par v1 v2) = locs v1 ∪ locs v2).
    { unfold locs, location_expr, location_val; cbn [locs_expr locs_val]. set_solver. }
    rewrite Hl in Hab.
    apply all_abef_union in Hab. destruct Hab as (Hab1 & Hab2).
    assert (Hl1 : locs (Call v1 [Val VUnit]) = locs v1).
    { unfold locs, location_expr, location_val; cbn [locs_expr locs_val]. set_solver. }
    rewrite Hl1.
    apply all_abef_trans with (t:=t0).
    + apply rtc_once. apply graph_fork_edge_l.
    + apply all_abef_mono_G with (G:=G); [apply graph_fork_subset | exact Hab1].
  - apply DI_leaf.
    assert (Hl : locs (Par v1 v2) = locs v1 ∪ locs v2).
    { unfold locs, location_expr, location_val; cbn [locs_expr locs_val]. set_solver. }
    rewrite Hl in Hab.
    apply all_abef_union in Hab. destruct Hab as (Hab1 & Hab2).
    assert (Hl2 : locs (Call v2 [Val VUnit]) = locs v2).
    { unfold locs, location_expr, location_val; cbn [locs_expr locs_val]. set_solver. }
    rewrite Hl2.
    apply all_abef_trans with (t:=t0).
    + apply rtc_once. apply graph_fork_edge_r.
    + apply all_abef_mono_G with (G:=G); [apply graph_fork_subset | exact Hab2].
Qed.

Lemma DInv_join : forall (G:graph) α t1 t2 t3 (v1 v2:val) (l:loc),
  l ∉ dom α ->
  DInv (graph_join G t1 t2 t3) (<[l:=t3]> α) (Leaf t3) l.
Proof.
  intros G α t1 t2 t3 v1 v2 l Hfresh.
  apply DI_leaf.
  unfold all_abef, set_Forall.
  intros l' Hl'. change (l' ∈ ({[l]} : gset loc)) in Hl'. rewrite elem_of_singleton in Hl'. subst l'.
  unfold abef. rewrite (lookup_insert_eq α l t3). apply rtc_refl.
Qed.

(* ---------- safety-side per-task invariant ---------- *)
Lemma fill_item_not_val : forall K e, is_val (fill_item K e) = false.
Proof. intros K. destruct K; reflexivity. Qed.

Lemma is_val_spec : forall e, is_val e = true -> exists v, e = Val v.
Proof. intros e H. destruct e; simpl in *; try discriminate; eauto. Qed.

Inductive SInv (σ:store) (α:amap) (G:graph) : task_tree -> expr -> Prop :=
| SI_leaf : forall t e, (is_val e \/ reducible true σ α G (Leaf t) e) -> SInv σ α G (Leaf t) e
| SI_par : forall t T1 T2 e1 e2,
    SInv σ α G T1 e1 -> SInv σ α G T2 e2 -> SInv σ α G (Node t T1 T2) (RunPar e1 e2)
| SI_bind : forall t T1 T2 K e,
    SInv σ α G (Node t T1 T2) e -> SInv σ α G (Node t T1 T2) (fill_item K e).

Lemma SInv_val_leaf : forall σ α G T e,
  SInv σ α G T e -> is_val e = true -> exists t, T = Leaf t.
Proof.
  intros σ α G T e H. induction H; intros Hv.
  - eauto.
  - cbv [is_val] in Hv. discriminate Hv.
  - rewrite fill_item_not_val in Hv. discriminate Hv.
Qed.

Lemma DInv_val_leaf : forall (G:graph) α T e,
  DInv G α T e -> is_val e = true -> exists t, T = Leaf t.
Proof.
  intros G α T e H. induction H; intros Hv.
  - eauto.
  - cbv [is_val] in Hv. discriminate Hv.
  - rewrite fill_item_not_val in Hv. discriminate Hv.
Qed.

Lemma DInv_leaf_inv : forall (G:graph) α t e,
  DInv G α (Leaf t) e -> all_abef G α t (locs e).
Proof.
  intros G α t e H. inversion H; subst; auto.
Qed.

Lemma SInv_leaf_inv : forall σ α (G:graph) t e,
  SInv σ α G (Leaf t) e -> is_val e \/ reducible true σ α G (Leaf t) e.
Proof.
  intros σ α G t e H. inversion H; subst; auto.
Qed.

Lemma fill_item_inj : forall (K:ctx) (e1 e2:expr),
  fill_item K e1 = fill_item K e2 -> e1 = e2.
Proof.
  intros K e1 e2 H. destruct K; cbn [fill_item] in H.
  all: try (injection H; congruence).
  injection H as Hl. apply app_inv_head in Hl. injection Hl. auto.
Qed.

Lemma fill_item_not_val_expr : forall (K:ctx) (e:expr) (v:val),
  fill_item K e ≠ Val v.
Proof. intros K e v. destruct K; cbn [fill_item]; discriminate. Qed.

Lemma fill_item_not_runpar : forall (K:ctx) (e e1 e2:expr),
  fill_item K e ≠ RunPar e1 e2.
Proof. intros K e e1 e2. destruct K; cbn [fill_item]; discriminate. Qed.

Lemma DInv_par_inv : forall (G:graph) α t T1 T2 e1 e2,
  DInv G α (Node t T1 T2) (RunPar e1 e2) ->
  DInv G α T1 e1 /\ DInv G α T2 e2.
Proof.
  intros G α t T1 T2 e1 e2 H.
  inversion H; subst.
  - auto.
  - exfalso. eapply fill_item_not_runpar. eauto.
Qed.

Lemma SInv_par_inv : forall σ α (G:graph) t T1 T2 e1 e2,
  SInv σ α G (Node t T1 T2) (RunPar e1 e2) ->
  SInv σ α G T1 e1 /\ SInv σ α G T2 e2.
Proof.
  intros σ α G t T1 T2 e1 e2 H.
  inversion H; subst.
  - auto.
  - exfalso. eapply fill_item_not_runpar. eauto.
Qed.

Lemma red_of_disj : forall σ α G T e,
  is_val e = false -> (is_val e \/ reducible true σ α G T e) ->
  reducible true σ α G T e.
Proof.
  intros σ α G T e Ev [Hv|Hr]; auto. exfalso. rewrite Ev in Hv. exact Hv.
Qed.

Lemma SInv_red : forall σ α G T e,
  SInv σ α G T e -> is_val e \/ reducible true σ α G T e.
Proof.
  intros σ α G T e H. induction H.
  - auto.
  - right. simpl.
    destruct (is_val e1) eqn:E1; destruct (is_val e2) eqn:E2.
    + (* both values -> SchedJoin *)
      destruct (SInv_val_leaf σ α G T1 e1 H E1) as [t1 ->].
      destruct (SInv_val_leaf σ α G T2 e2 H0 E2) as [t2 ->].
      destruct (is_val_spec e1 E1) as [v1 ->].
      destruct (is_val_spec e2 E2) as [v2 ->].
      eapply RedSched.
      set (l := fresh (elements (dom σ) ++ elements (dom α))).
      assert (Hl : l ∉ elements (dom σ) ++ elements (dom α)).
      { apply infinite_is_fresh. }
      assert (Hd : l ∉ dom σ).
      { intro Hin. apply Hl. apply elem_of_app. left. apply elem_of_elements. auto. }
      assert (Hd2 : l ∉ dom α).
      { intro Hin. apply Hl. apply elem_of_app. right. apply elem_of_elements. auto. }
      eapply SchedJoin with (G' := graph_join G t1 t2 t) (l := l)
                            (σ' := <[l:=SProd v1 v2]> σ) (α' := <[l:=t]> α); auto.
    + (* e1 value, e2 non-value *)
      eapply RedPar.
      * right. intro Hc. rewrite E2 in Hc. exact Hc.
      * intro Hc. exfalso. apply Hc. rewrite E1. exact I.
      * intro Hc0. destruct IHSInv2 as [Hv|Hr]; [contradiction|exact Hr].
    + (* e1 non-value, e2 value *)
      eapply RedPar.
      * left. intro Hc. rewrite E1 in Hc. exact Hc.
      * intro Hc0. destruct IHSInv1 as [Hv|Hr]; [contradiction|exact Hr].
      * intro Hc. exfalso. apply Hc. rewrite E2. exact I.
    + (* both non-values *)
      eapply RedPar.
      * left. intro Hc. rewrite E1 in Hc. exact Hc.
      * intro Hc0. destruct IHSInv1 as [Hv|Hr]; [contradiction|exact Hr].
      * intro Hc0. destruct IHSInv2 as [Hv|Hr]; [contradiction|exact Hr].
  - right. eapply RedCtx.
    destruct IHSInv as [Hv|Hr]; [|exact Hr].
    exfalso. destruct (is_val e) eqn:E; [|exact Hv].
    destruct (SInv_val_leaf σ α G (Node t T1 T2) e H E) as [t' Hl]. discriminate Hl.
Qed.

Lemma SInv_safe : forall σ α G T e,
  SInv σ α G T e -> safe true σ α G T e.
Proof.
  intros σ α G T e H. destruct (SInv_red σ α G T e H) as [Hv|Hr].
  - left. split.
    + exact Hv.
    + assert (E : is_val e = true) by
        (destruct (is_val e) eqn:E0; [reflexivity|exfalso; exact Hv]).
      destruct (SInv_val_leaf σ α G T e H E) as [t' ->]. exact I.
  - right; auto.
Qed.


(* ---------- assembly: the three per-configuration invariants imply the goal ---------- *)
Lemma Inv_safe_disentangled : forall σ α G T e,
  GInv G T -> DInv G α T e -> SInv σ α G T e ->
  safe true σ α G T e /\ disentangled G α T e.
Proof.
  intros σ α G T e HG HD HS. split.
  - apply SInv_safe; auto.
  - apply DInv_disentangled; auto.
Qed.


(* ---------- initial state satisfies the graph and disentanglement invariants ---------- *)
Lemma initial_GInv : forall t0, GInv {[(t0,t0)]} (Leaf t0).
Proof. intros. exact I. Qed.

Lemma initial_DInv : forall t0 (e:expr), locs e = ∅ -> DInv {[(t0,t0)]} ∅ (Leaf t0) e.
Proof.
  intros t0 e Hl. apply DI_leaf. unfold all_abef. rewrite Hl.
  apply set_Forall_empty.
Qed.


(* ---------- binder deletion algebra (needed for substitution hygiene) ---------- *)
Lemma bdelete_bdelete_comm : forall (A:Type) (b c:binder) (m:gmap string A),
  bdelete b (bdelete c m) = bdelete c (bdelete b m).
Proof.
  intros A [|x] [|y] m; cbn [bdelete]; auto.
  apply delete_delete.
Qed.

Lemma bdeletes_bdelete_comm : forall (A:Type) (bs:list binder) (b:binder) (m:gmap string A),
  bdeletes bs (bdelete b m) = bdelete b (bdeletes bs m).
Proof.
  intros A bs. induction bs as [|c bs IH]; intros b m; cbn [bdeletes].
  - reflexivity.
  - change (bdelete c (bdeletes bs (bdelete b m)) = bdelete b (bdelete c (bdeletes bs m))).
    rewrite (IH b m). rewrite (bdelete_bdelete_comm A c b (bdeletes bs m)). reflexivity.
Qed.

Lemma find_opt_bdelete_ne : forall (m:gmap string string) (b:binder) z,
  z ∉ binder_set b -> find_opt (bdelete b m) z = find_opt m z.
Proof.
  intros m [|y] z Hz; cbn [bdelete binder_set] in *.
  - reflexivity.
  - unfold find_opt. rewrite lookup_delete_ne.
    + reflexivity.
    + intro e. apply Hz. rewrite elem_of_singleton. symmetry. exact e.
Qed.

Lemma find_opt_bdeletes_ne : forall (m:gmap string string) (bs:list binder) z,
  z ∉ binders_set bs -> find_opt (bdeletes bs m) z = find_opt m z.
Proof.
  intros m bs. induction bs as [|c bs IH]; intros z Hz.
  - cbn [bdeletes binders_set]. reflexivity.
  - cbn [bdeletes]. change (z ∉ (binder_set c ∪ binders_set bs)) in Hz.
    assert (Hc : z ∉ binder_set c) by (intro H; apply Hz; apply elem_of_union; left; exact H).
    assert (Hs : z ∉ binders_set bs) by (intro H; apply Hz; apply elem_of_union; right; exact H).
    change (find_opt (bdelete c (bdeletes bs m)) z = find_opt m z).
    rewrite find_opt_bdelete_ne by exact Hc.
    apply IH. exact Hs.
Qed.

Lemma find_opt_delete_ne : forall (m:gmap string string) z y,
  z ≠ y -> find_opt (delete z m) y = find_opt m y.
Proof.
  intros m z y Hne. unfold find_opt. rewrite lookup_delete_ne by auto. reflexivity.
Qed.

Lemma lookup_bdeletes_binders_none : forall (bs:list binder) (m:gmap string string) z,
  z ∈ binders_set bs -> (bdeletes bs m) !! z = None.
Proof.
  induction bs as [|b bs IH]; intros m z Hz.
  - change (z ∈ (∅ : gset string)) in Hz. set_solver.
  - change (z ∈ (binder_set b ∪ binders_set bs)) in Hz.
    destruct b as [|s].
    + cbn [bdeletes bdelete]. apply IH. set_solver.
    + cbn [bdeletes bdelete].
      destruct (decide (z = s)) as [e|ne].
      * subst z. apply lookup_delete_eq.
      * change ((delete s (bdeletes bs m)) !! z = None).
        rewrite lookup_delete_ne by auto. apply IH. set_solver.
Qed.

Lemma bdeletes_delete_mem : forall (bs:list binder) (m:gmap string string) z,
  z ∈ binders_set bs -> bdeletes bs (delete z m) = bdeletes bs m.
Proof.
  intros bs m z Hz.
  change (bdeletes bs (bdelete (BNamed z) m) = bdeletes bs m).
  rewrite (bdeletes_bdelete_comm string bs (BNamed z) m). cbn [bdelete].
  rewrite delete_id.
  - reflexivity.
  - apply lookup_bdeletes_binders_none. exact Hz.
Qed.

Lemma reachable_mono_str : forall (G G':gset (string*string)) x y,
  G ⊆ G' -> graph.reachable G x y -> graph.reachable G' x y.
Proof.
  intros G G' x y Hsub H. induction H as [z|z w u Hzw Hwu IH].
  - apply rtc_refl.
  - eapply rtc_l; [|eassumption]. unfold edge in *. apply Hsub; auto.
Qed.

Lemma all_reachable_mono : forall (Δ Δ':constraints) (T:constraints),
  Δ ⊆ Δ' -> all_reachable Δ T -> all_reachable Δ' T.
Proof.
  intros Δ Δ' T Hsub H. unfold all_reachable, set_Forall in *.
  intros p Hp. destruct p as [x y]. simpl in *.
  eapply reachable_mono_str; [exact Hsub |].
  specialize (H (x,y) Hp). cbn in H. exact H.
Qed.

Lemma all_reachable_union : forall (Δ Δ1 Δ2:constraints),
  all_reachable Δ (Δ1 ∪ Δ2) <-> all_reachable Δ Δ1 /\ all_reachable Δ Δ2.
Proof.
  intros Δ Δ1 Δ2. unfold all_reachable, set_Forall. split.
  - intros H. split.
    + intros [x y] Hp. specialize (H (x,y) ltac:(apply elem_of_union; left; exact Hp)). cbn in H. exact H.
    + intros [x y] Hp. specialize (H (x,y) ltac:(apply elem_of_union; right; exact Hp)). cbn in H. exact H.
  - intros (H1 & H2) [x y] Hp. apply elem_of_union in Hp as [Hp|Hp].
    + specialize (H1 (x,y) Hp). cbn in H1. exact H1.
    + specialize (H2 (x,y) Hp). cbn in H2. exact H2.
Qed.

Lemma all_reachable_empty : forall (Δ:constraints), all_reachable Δ ∅.
Proof. intros Δ. unfold all_reachable, set_Forall. intros [x y] Hp. set_solver. Qed.

Lemma subtime_typ_refl : forall (Δ:constraints) δ ρ, subtime_typ Δ δ ρ ρ.
Proof. intros. apply SRefl. Qed.

Lemma subtime_typat_refl : forall (Δ:constraints) δ σt, subtime_typat Δ δ σt σt.
Proof. intros. apply SARefl. Qed.

Fixpoint valid_variable_typ_mono (Δ:constraints) (x:string) (δ:stimestamp) (ρ:typ) (δ':stimestamp)
  (H:valid_variable_typ Δ x δ ρ δ') {struct H} :
  forall Δ', Δ ⊆ Δ' -> valid_variable_typ Δ' x δ ρ δ'
with valid_variable_typat_mono (Δ:constraints) (x:string) (δ:stimestamp) (σ:typat) (δ':stimestamp)
  (H:valid_variable_typat Δ x δ σ δ') {struct H} :
  forall Δ', Δ ⊆ Δ' -> valid_variable_typat Δ' x δ σ δ'.
Proof.
  - intros Δ' Hsub. destruct H.
    + apply WVar. intros e. eapply reachable_mono_str; [exact Hsub | apply H; exact e].
    + apply WBase.
    + apply WTYpat. apply (valid_variable_typat_mono _ _ _ _ _ H Δ' Hsub).
    + apply WTYForall. intros yne. apply (valid_variable_typ_mono Δ x δ ρ δ' (H yne) Δ' Hsub).
    + apply WTRec. assumption.
  - intros Δ' Hsub. destruct H.
    + apply WProd; [apply (valid_variable_typ_mono _ _ _ _ _ H Δ' Hsub)|apply (valid_variable_typ_mono _ _ _ _ _ H0 Δ' Hsub)].
    + apply WSum; [apply (valid_variable_typ_mono _ _ _ _ _ H Δ' Hsub)|apply (valid_variable_typ_mono _ _ _ _ _ H0 Δ' Hsub)].
    + apply WArray. assumption.
    + apply WFun. assumption.
Qed.

Lemma valid_variable_typat'_mono : forall (Δ Δ':constraints) x (δ:stimestamp) (σ:typat) (δ':stimestamp),
  Δ ⊆ Δ' -> valid_variable_typat' Δ x δ σ δ' -> valid_variable_typat' Δ' x δ σ δ'.
Proof.
  intros Δ Δ' [|x] δ σ δ' Hsub H; cbn in *; auto.
  apply (valid_variable_typat_mono Δ x δ σ δ' H Δ' Hsub).
Qed.

Lemma typed_weak_env : forall δ Δ Ω Γ Γ' e ρ,
  typed δ Δ Ω Γ e ρ -> Γ ⊆ Γ' -> typed δ Δ Ω Γ' e ρ.
Proof. intros. eapply TYWeakEnv; eauto. Qed.

Lemma typed_weak_cons : forall δ Δ Δ' Ω Γ e ρ,
  typed δ Δ Ω Γ e ρ -> Δ ⊆ Δ' -> typed δ Δ' Ω Γ e ρ.
Proof. intros. eapply TYWeakCons; eauto. Qed.

Lemma typed_subtime : forall δ Δ Ω Γ e ρ ρ',
  typed δ Δ Ω Γ e ρ -> subtime_typ Δ δ ρ ρ' -> typed δ Δ Ω Γ e ρ'.
Proof. intros. eapply TYSubtime; eauto. Qed.

Lemma typed_beta : forall δ Δ Ω Γ e ρ ρ',
  (beta_typ ρ ρ' \/ beta_typ ρ' ρ) -> typed δ Δ Ω Γ e ρ' -> typed δ Δ Ω Γ e ρ.
Proof. intros. eapply TYBeta; eauto. Qed.

Lemma typed_alpha : forall δ Δ Ω Γ e ρ ρ',
  alpha_typ ρ ρ' -> typed δ Δ Ω Γ e ρ' -> typed δ Δ Ω Γ e ρ.
Proof. intros. eapply TYAlpha; eauto. Qed.

Lemma typed_alphat : forall δ Δ Ω Γ e ρ ρ',
  alphat_typ ρ ρ' -> typed δ Δ Ω Γ e ρ' -> typed δ Δ Ω Γ e ρ.
Proof. intros. eapply TYAlphat; eauto. Qed.

Lemma typed_var_lookup : forall δ Δ Ω Γ e ρ,
  typed δ Δ Ω Γ e ρ -> forall z, e = Var z -> exists ρ0, Γ !! z = Some ρ0.
Proof.
  intros δ Δ Ω Γ e ρ H. induction H; intros z Hz.
  all: try discriminate Hz.
  all: try (apply (IHtyped z Hz)).
  - injection Hz as e0. subst z. exists ρ. exact H.
  - match goal with IH : (forall z, _ = _ -> exists ρ0, (tsubst_typ ?m <$> Γ) !! z = Some ρ0) |- _ =>
      destruct (IH z Hz) as [ρ0 Hlook] end.
    rewrite lookup_fmap in Hlook.
    assert (Hopt : exists ρ1, Γ !! z = Some ρ1).
    { destruct (Γ !! z) as [ρ1|] eqn:E.
      - exists ρ1. reflexivity.
      - simpl in Hlook. discriminate Hlook. }
    destruct Hopt as [ρ1 E]. exists ρ1. exact E.
  - match goal with IH : (forall z, _ = _ -> exists ρ0, Γ !! z = Some ρ0) |- _ =>
      destruct (IH z Hz) as [ρ0 Hlook] end.
    match goal with Hsub : Γ ⊆ ?G' |- exists ρ0, ?G' !! z = Some ρ0 =>
      exists ρ0; rewrite map_subseteq_spec in Hsub; apply Hsub; exact Hlook end.
Qed.

Lemma lookup_binsert_anon : forall (A:Type) (ρ:A) Γ y,
  (binsert BAnon ρ Γ) !! y = Γ !! y.
Proof. reflexivity. Qed.

Lemma lookup_binsert_named_eq : forall (A:Type) (ρ:A) Γ x,
  (binsert (BNamed x) ρ Γ) !! x = Some ρ.
Proof. intros. cbn [binsert]. apply lookup_insert_eq. Qed.

Lemma lookup_binsert_named_ne : forall (A:Type) (ρ:A) Γ x y,
  x ≠ y -> (binsert (BNamed x) ρ Γ) !! y = Γ !! y.
Proof. intros. cbn [binsert]. apply lookup_insert_ne; auto. Qed.

Lemma dom_binsert_anon : forall (A:Type) (ρ:A) Γ,
  dom (binsert BAnon ρ Γ) = dom Γ.
Proof. reflexivity. Qed.

Lemma dom_binsert_named : forall (A:Type) (ρ:A) Γ x,
  dom (binsert (BNamed x) ρ Γ) = ({[x]} : gset string) ∪ dom Γ.
Proof. intros. cbn [binsert]. apply leibniz_equiv_iff. apply dom_insert. Qed.

Lemma lookup_bdelete_anon : forall (A:Type) Γ y,
  (@bdelete A BAnon Γ) !! y = Γ !! y.
Proof. reflexivity. Qed.

Lemma lookup_bdelete_named_eq : forall (A:Type) Γ x,
  (@bdelete A (BNamed x) Γ) !! x = None.
Proof. intros. cbn [bdelete]. apply lookup_delete_eq. Qed.

Lemma lookup_bdelete_named_ne : forall (A:Type) Γ x y,
  x ≠ y -> (@bdelete A (BNamed x) Γ) !! y = Γ !! y.
Proof. intros. cbn [bdelete]. apply lookup_delete_ne; auto. Qed.

Lemma dom_bdelete_anon : forall (A:Type) Γ,
  dom (@bdelete A BAnon Γ) = dom Γ.
Proof. reflexivity. Qed.

Lemma dom_bdelete_named : forall (A:Type) Γ x,
  dom (@bdelete A (BNamed x) Γ) = dom Γ ∖ ({[x]} : gset string).
Proof. intros. cbn [bdelete]. apply leibniz_equiv_iff. apply dom_delete. Qed.

Lemma pos_expr_size : forall e, 1 <= expr_size e.
Proof. intros. destruct e; cbn [expr_size]; lia. Qed.
Lemma call_arg_size : forall (e1:expr) (l:list expr) fuel,
  expr_size (Call e1 l) <= S fuel -> expr_size e1 <= fuel.
Proof. intros. cbn [expr_size] in H. simpl in H. apply le_S_n in H. lia. Qed.
Lemma call_list_size : forall (e1:expr) (l:list expr) fuel,
  expr_size (Call e1 l) <= S fuel -> S (list_sum (list_fmap expr nat expr_size l)) <= fuel.
Proof. intros. cbn [expr_size] in H. simpl in H.
  change (S (expr_size e1 + list_sum (list_fmap expr nat expr_size l)) <= S fuel) in H.
  apply le_S_n in H. pose proof (pos_expr_size e1).
  assert (Hb : S (list_sum (list_fmap expr nat expr_size l)) <= expr_size e1 + list_sum (list_fmap expr nat expr_size l)) by lia.
  transitivity (expr_size e1 + list_sum (list_fmap expr nat expr_size l)).
  - exact Hb. - exact H.
Qed.
Lemma list_head_size : forall (t:expr) (ts:list expr) fuel,
  S (list_sum (expr_size <$> (t::ts))) <= S fuel -> expr_size t <= fuel.
Proof. intros. simpl in H. cbn [list_sum list_fmap] in H. apply le_S_n in H. lia. Qed.
Lemma list_tail_size : forall (t:expr) (ts:list expr) fuel,
  S (list_sum (expr_size <$> (t::ts))) <= S fuel -> S (list_sum (list_fmap expr nat expr_size ts)) <= fuel.
Proof. intros. simpl in H. cbn [list_sum list_fmap] in H.
  change (S (expr_size t + list_sum (list_fmap expr nat expr_size ts)) <= S fuel) in H.
  apply le_S_n in H. pose proof (pos_expr_size t). lia. Qed.

Lemma locs_subst_fuel : forall fuel,
  (forall x v e, expr_size e <= fuel -> locs (subst x v e) ⊆ locs e ∪ locs v)
  /\ (forall x v es, S (list_sum (expr_size <$> es)) <= fuel ->
      ⋃ (locs <$> (subst x v <$> es)) ⊆ ⋃ (locs <$> es) ∪ locs v).
Proof.
  induction fuel as [|fuel IH].
  - split.
    + intros x v e H. exfalso. destruct e; cbn [expr_size] in H; lia.
    + intros x v es H. exfalso. destruct es; cbn [list_sum] in H; lia.
  - destruct IH as (IHt & IHl). split.
    + intros x v e H.
      destruct e as [vv|g|y|e1 l|p e1 e2|e1 e2 e3|b e1 e2|e1 e2|e1|e1|e1|e1
                    |e0 b1 e1 b2 e2|e1 e2|e1 e2|e1 e2 e3|e1|e1 e2|e1 e2|e1 e2 e3 e4|e1|e1];
        cbn [subst expr_size].
      * cbn [locs_expr locs_val]. set_solver.
      * destruct g as [b bs body]. unfold subst_clo.
        destruct (decide (x ∈ binder_set b ∪ ⋃ (binder_set <$> bs))); cbn [locs_expr locs_func].
        -- set_solver.
        -- assert (Hb : expr_size body <= fuel) by (cbn [expr_size clo_size] in H; lia).
           pose proof (IHt x v body Hb). set_solver.
      * destruct (decide (x = y)); cbn [locs_expr locs_val]; set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (apply (call_arg_size e1 l fuel); exact H).
        assert (H2 : S (list_sum (expr_size <$> l)) <= fuel) by (apply (call_list_size e1 l fuel); exact H).
        pose proof (IHt x v e1 H1). pose proof (IHl x v l H2). cbn [locs_expr]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H2 : expr_size e2 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). pose proof (IHt x v e2 H2). cbn [locs_expr]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H2 : expr_size e2 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H3 : expr_size e3 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). pose proof (IHt x v e2 H2). pose proof (IHt x v e3 H3).
        cbn [locs_expr]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H2 : expr_size e2 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). pose proof (IHt x v e2 H2).
        destruct (decide (b = BNamed x)); cbn [locs_expr]. set_solver. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H2 : expr_size e2 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). pose proof (IHt x v e2 H2). cbn [locs_expr]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). cbn [locs_expr]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). cbn [locs_expr]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). cbn [locs_expr]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). cbn [locs_expr]. set_solver.
      * assert (H1 : expr_size e0 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H2 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H3 : expr_size e2 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e0 H1). pose proof (IHt x v e1 H2). pose proof (IHt x v e2 H3).
        destruct (decide (BNamed x = b1)); cbn [locs_expr];
          destruct (decide (BNamed x = b2)); cbn [locs_expr]; set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H2 : expr_size e2 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). pose proof (IHt x v e2 H2). cbn [locs_expr]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H2 : expr_size e2 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). pose proof (IHt x v e2 H2). cbn [locs_expr]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H2 : expr_size e2 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H3 : expr_size e3 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). pose proof (IHt x v e2 H2). pose proof (IHt x v e3 H3).
        cbn [locs_expr]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). cbn [locs_expr]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H2 : expr_size e2 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). pose proof (IHt x v e2 H2). cbn [locs_expr]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H2 : expr_size e2 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). pose proof (IHt x v e2 H2). cbn [locs_expr]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H2 : expr_size e2 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H3 : expr_size e3 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H4 : expr_size e4 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). pose proof (IHt x v e2 H2). pose proof (IHt x v e3 H3). pose proof (IHt x v e4 H4).
        cbn [locs_expr]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). cbn [locs_expr]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). cbn [locs_expr]. set_solver.
    + intros x v es H. destruct es as [|t ts]; cbn [list_sum].
      * cbn. set_solver.
      * simpl in H. cbn [list_sum list_fmap] in H.
        assert (H1 : expr_size t <= fuel) by (apply (list_head_size t ts fuel); exact H).
        assert (H2 : S (list_sum (expr_size <$> ts)) <= fuel) by (apply (list_tail_size t ts fuel); exact H).
        pose proof (IHt x v t H1). pose proof (IHl x v ts H2). cbn. set_solver.
Qed.

Lemma fv_subst_fuel : forall fuel,
  (forall x v e, expr_size e <= fuel -> fv (subst x v e) ⊆ fv e ∖ ({[x]} : gset string))
  /\ (forall x v es, S (list_sum (expr_size <$> es)) <= fuel ->
      ⋃ (fv <$> (subst x v <$> es)) ⊆ ⋃ (fv <$> es) ∖ ({[x]} : gset string)).
Proof.
  induction fuel as [|fuel IH].
  - split.
    + intros x v e H. exfalso. destruct e; cbn [expr_size] in H; lia.
    + intros x v es H. exfalso. destruct es; cbn [list_sum] in H; lia.
  - destruct IH as (IHt & IHl). split.
    + intros x v e H.
      destruct e as [vv|g|y|e1 l|p e1 e2|e1 e2 e3|b e1 e2|e1 e2|e1|e1|e1|e1
                    |e0 b1 e1 b2 e2|e1 e2|e1 e2|e1 e2 e3|e1|e1 e2|e1 e2|e1 e2 e3 e4|e1|e1];
        cbn [subst expr_size].
      * cbn [fv]. set_solver.
      * destruct g as [b bs body]. unfold subst_clo.
        destruct (decide (x ∈ binder_set b ∪ ⋃ (binder_set <$> bs))) as [Hb|Hb];
          cbn [fv_func].
        -- set_solver.
        -- assert (Hbody : expr_size body <= fuel) by (cbn [expr_size clo_size] in H; lia).
           pose proof (IHt x v body Hbody). set_solver.
      * destruct (decide (x = y)); cbn [fv]; set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (apply (call_arg_size e1 l fuel); exact H).
        assert (H2 : S (list_sum (expr_size <$> l)) <= fuel) by (apply (call_list_size e1 l fuel); exact H).
        pose proof (IHt x v e1 H1). pose proof (IHl x v l H2). cbn [fv]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H2 : expr_size e2 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). pose proof (IHt x v e2 H2). cbn [fv]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H2 : expr_size e2 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H3 : expr_size e3 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). pose proof (IHt x v e2 H2). pose proof (IHt x v e3 H3).
        cbn [fv]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H2 : expr_size e2 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). pose proof (IHt x v e2 H2).
        destruct (decide (b = BNamed x)) as [e|ne0].
        -- subst b. cbn [fv]. set_solver.
        -- cbn [fv]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H2 : expr_size e2 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). pose proof (IHt x v e2 H2). cbn [fv]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). cbn [fv]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). cbn [fv]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). cbn [fv]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). cbn [fv]. set_solver.
      * assert (H1 : expr_size e0 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H2 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H3 : expr_size e2 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e0 H1). pose proof (IHt x v e1 H2). pose proof (IHt x v e2 H3).
        destruct (decide (BNamed x = b1)) as [e1b|ne1].
        -- subst b1. destruct (decide (BNamed x = b2)) as [e2b|ne2].
           ++ subst b2. cbn [fv]. set_solver.
           ++ cbn [fv]. set_solver.
        -- destruct (decide (BNamed x = b2)) as [e2b|ne2].
           ++ subst b2. cbn [fv]. set_solver.
           ++ cbn [fv]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H2 : expr_size e2 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). pose proof (IHt x v e2 H2). cbn [fv]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H2 : expr_size e2 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). pose proof (IHt x v e2 H2). cbn [fv]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H2 : expr_size e2 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H3 : expr_size e3 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). pose proof (IHt x v e2 H2). pose proof (IHt x v e3 H3).
        cbn [fv]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). cbn [fv]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H2 : expr_size e2 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). pose proof (IHt x v e2 H2). cbn [fv]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H2 : expr_size e2 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). pose proof (IHt x v e2 H2). cbn [fv]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H2 : expr_size e2 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H3 : expr_size e3 <= fuel) by (cbn [expr_size] in H; lia).
        assert (H4 : expr_size e4 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). pose proof (IHt x v e2 H2). pose proof (IHt x v e3 H3). pose proof (IHt x v e4 H4).
        cbn [fv]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). cbn [fv]. set_solver.
      * assert (H1 : expr_size e1 <= fuel) by (cbn [expr_size] in H; lia).
        pose proof (IHt x v e1 H1). cbn [fv]. set_solver.
    + intros x v es H. destruct es as [|t ts]; cbn [list_sum].
      * cbn. set_solver.
      * simpl in H. cbn [list_sum list_fmap] in H.
        assert (H1 : expr_size t <= fuel) by (apply (list_head_size t ts fuel); exact H).
        assert (H2 : S (list_sum (expr_size <$> ts)) <= fuel) by (apply (list_tail_size t ts fuel); exact H).
        pose proof (IHt x v t H1). pose proof (IHl x v ts H2). cbn. set_solver.
Qed.

Lemma fv_subst_subset : forall x v e, fv (subst x v e) ⊆ fv e.
Proof.
  intros. transitivity (fv e ∖ ({[x]} : gset string)).
  - apply (proj1 (fv_subst_fuel (expr_size e)) x v e (le_n _)).
  - set_solver.
Qed.

Lemma fv_subst'_subset : forall (b:binder) v e, fv (subst' b v e) ⊆ fv e.
Proof.
  intros [|x] v e; cbn [subst']; [reflexivity|apply fv_subst_subset].
Qed.

Lemma fv_substs'_subset : forall (xlvs:list (binder*val)) e,
  fv (substs' xlvs e) ⊆ fv e.
Proof.
  induction xlvs as [|p xlvs IH]; intros e.
  - cbn [substs']. reflexivity.
  - destruct p as [b v]. cbn [substs'].
    transitivity (fv (substs' xlvs e)); [apply fv_subst'_subset|apply IH].
Qed.

Lemma locs_subst_subset : forall x v e, locs (subst x v e) ⊆ locs e ∪ locs v.
Proof.
  intros. apply (proj1 (locs_subst_fuel (expr_size e)) x v e (le_n _)).
Qed.

Lemma locs_subst'_subset : forall (b:binder) v e,
  locs (subst' b v e) ⊆ locs e ∪ locs v.
Proof.
  intros [|x] v e; cbn [subst']; [set_solver|apply locs_subst_subset].
Qed.

Lemma locs_substs'_subset : forall (xlvs:list (binder*val)) e,
  locs (substs' xlvs e) ⊆ locs e ∪ ⋃ (locs <$> (snd <$> xlvs)).
Proof.
  induction xlvs as [|p xlvs IH]; intros e.
  - cbn [substs']. cbn. set_solver.
  - destruct p as [b v]. cbn [substs'].
    transitivity (locs (substs' xlvs e) ∪ locs v).
    + apply locs_subst'_subset.
    + pose proof (IH e). cbn [list_fmap]. set_solver.
Qed.

Lemma head_step_locs_bound : forall G t σ α e σ' α' e',
  head_step G t σ α e σ' α' e' ->
  locs e' ⊆ locs e ∪ store_locs σ ∪ dom α'.
Proof.
  intros G t σ α e σ' α' e' H. induction H.
  - destruct b; cbn [locs_expr]; set_solver.
  - pose proof (locs_subst'_subset x v e) as Hb. cbn [locs_expr locs_val]. set_solver.
  - (* Call VCode *)
    pose proof (locs_substs'_subset (zip (self::args) (VCode (Lam self args code)::vs)) code) as Hb.
    rewrite H1 in Hb.
    assert (Hts : length ts = length vs) by (rewrite H; apply length_fmap).
    assert (Hlen : length vs <= length args) by lia.
    assert (Hz : ⋃ (locs <$> (snd <$> zip (self :: args) (VCode (Lam self args code) :: vs)))
               ⊆ ⋃ (locs <$> vs)).
    { cbn [zip].
      change (⋃ (locs <$> (VCode (Lam self args code) :: (zip args vs).*2)) ⊆ ⋃ (locs <$> vs)).
      rewrite (snd_zip args vs Hlen).
      cbn [list_fmap locs_val]. set_solver. }
    transitivity (∅ ∪ ⋃ (locs <$> (snd <$> zip (self :: args) (VCode (Lam self args code) :: vs)))).
    + exact Hb.
    + rewrite H.
      assert (Hcall : locs (Call (VCode (Lam self args code)) (Val <$> vs)) = ∅ ∪ ⋃ (locs <$> vs)).
      { unfold locs, location_expr. cbn [locs_expr locs_val]. rewrite locs_vals_expr. reflexivity. }
      rewrite Hcall.
      apply elem_of_subseteq in Hz. set_solver.
  - (* Call Clo *)
    pose proof (locs_substs'_subset (zip (self::args) (VLoc l :: vs)) body) as Hb.
    assert (Hts : length ts = length vs) by (rewrite H0; apply length_fmap).
    assert (Hlen : length vs <= length args) by lia.
    assert (Hz : ⋃ (locs <$> (snd <$> zip (self :: args) (VLoc l :: vs)))
               ⊆ ({[l]} : gset loc) ∪ ⋃ (locs <$> vs)).
    { cbn [zip].
      change (⋃ (locs <$> (VLoc l :: (zip args vs).*2)) ⊆ ({[l]} ∪ ⋃ (locs <$> vs))).
      rewrite (snd_zip args vs Hlen).
      cbn [list_fmap locs_val]. set_solver. }
    transitivity (locs body ∪ ⋃ (locs <$> (snd <$> zip (self :: args) (VLoc l :: vs)))).
    + exact Hb.
    + rewrite H0.
      assert (Hcall : locs (Call l (Val <$> vs)) = ({[l]} : gset loc) ∪ ⋃ (locs <$> vs)).
      { unfold locs, location_expr, location_val. cbn [locs_expr locs_val]. rewrite locs_vals_expr. reflexivity. }
      rewrite Hcall.
      pose proof (locs_storable_store_subset σ l (SClo self args body) H) as Hs.
      cbn [locs_storable] in Hs.
      apply elem_of_subseteq in Hs. apply elem_of_subseteq in Hz. set_solver.
  - (* CallPrim *)
    destruct p, v1, v2; cbn [eval_call_prim] in H.
    all: try discriminate H.
    all: try (injection H as <-); cbn [locs_val]; set_solver.
  - (* Func *) subst α'. rewrite dom_insert. unfold locs, location_expr, location_val. cbn [locs_expr locs_val]. set_solver.
  - (* Alloc *) subst α'. rewrite dom_insert. unfold locs, location_expr, location_val. cbn [locs_expr locs_val]. set_solver.
  - (* Load *)
    pose proof (locs_storable_store_subset σ l (SBlock bs) H) as Hs.
    cbn [locs_storable] in Hs.
    assert (Hv : locs v ⊆ ⋃ (locs <$> bs)).
    { apply elem_of_subseteq. intros l0 Hl0. apply elem_of_union_list.
      exists (locs v). split; [|exact Hl0].
      apply list_elem_of_fmap. exists v. split; [reflexivity|].
      eapply list_elem_of_lookup_2. exact H1. }
    cbn [locs_expr locs_val]. set_solver.
  - (* Store *) unfold locs, location_expr, location_val. cbn [locs_expr locs_val]. set_solver.
  - (* Prod *) rewrite dom_insert. unfold locs, location_expr, location_val. cbn [locs_expr locs_val]. set_solver.
  - (* Proj *)
    destruct b; unfold locs, location_expr, location_val; cbn [locs_expr locs_val];
      pose proof (locs_storable_store_subset σ l (SProd v1 v2) H) as Hs;
      cbn [locs_storable] in Hs; set_solver.
  - (* Length *) unfold locs, location_expr, location_val. cbn [locs_expr locs_val]. set_solver.
  - (* CAS *) unfold locs, location_expr, location_val. cbn [locs_expr locs_val]. set_solver.
  - (* Fold *) unfold locs, location_expr, location_val. cbn [locs_expr locs_val]. set_solver.
  - (* UnfoldFold *) unfold locs, location_expr, location_val. cbn [locs_expr locs_val]. set_solver.
  - (* In *) rewrite dom_insert. unfold locs, location_expr, location_val. cbn [locs_expr locs_val]. set_solver.
  - (* Case *)
    destruct b; cbn [locs_expr locs_val].
    + pose proof (locs_storable_store_subset σ l (SInL vl) H) as Hs. cbn [locs_storable] in Hs.
      pose proof (locs_subst'_subset xl vl el) as Hb. set_solver.
    + pose proof (locs_storable_store_subset σ l (SInR vr) H) as Hs. cbn [locs_storable] in Hs.
      pose proof (locs_subst'_subset xr vr er) as Hb. set_solver.
Qed.

Lemma sched_step_locs_bound : forall σ α G T e σ' α' G' T' e',
  sched_step σ α G T e σ' α' G' T' e' ->
  locs e' ⊆ locs e ∪ store_locs σ ∪ dom α'.
Proof.
  intros σ α G T e σ' α' G' T' e' Hs. inversion Hs; subst.
  - eapply head_step_locs_bound; eauto.
  - cbn [locs_expr locs_val]. set_solver.
  - rewrite dom_insert. unfold locs, location_expr, location_val. cbn [locs_expr locs_val]. set_solver.
Qed.

Lemma step_locs_bound : forall σ α G T e σ' α' G' T' e',
  lang.semantics.step σ α G T e σ' α' G' T' e' ->
  locs e' ⊆ locs e ∪ store_locs σ ∪ dom α'.
Proof.
  intros σ α G T e σ' α' G' T' e' Hs. induction Hs.
  - eapply sched_step_locs_bound; eauto.
  - rewrite !locs_fill_item_eq. set_solver.
  - cbn [locs_expr]. set_solver.
  - cbn [locs_expr]. set_solver.
Qed.

Lemma head_step_store_locs_bound : forall G t σ α e σ' α' e',
  head_step G t σ α e σ' α' e' ->
  store_locs σ' ⊆ store_locs σ ∪ locs e ∪ dom α'.
Proof.
  intros G t σ α e σ' α' e' H. induction H.
  all: try (subst σ'; set_solver).
  all: try set_solver.
  - (* Func *) subst σ'.
    transitivity (store_locs σ ∪ locs_storable (SClo self args code)).
    + apply store_locs_insert_subset.
    + unfold locs, location_expr. cbn [locs_expr locs_func locs_storable]. set_solver.
  - (* Alloc *) subst σ'.
    transitivity (store_locs σ ∪ locs_storable (SBlock (replicate (Z.to_nat n) v))).
    + apply store_locs_insert_subset.
    + pose proof (locs_storable_block_replicate (Z.to_nat n) v) as Hrep.
      unfold locs, location_expr, location_val. cbn [locs_expr locs_val locs_storable]. set_solver.
  - (* Store *) subst σ'.
    transitivity (store_locs σ ∪ locs_storable (SBlock (<[Z.to_nat i:=v]> bs))).
    + apply store_locs_insert_subset.
    + pose proof (locs_storable_store_subset σ l (SBlock bs) H) as Hold.
      cbn [locs_storable] in Hold.
      pose proof (locs_storable_block_update bs (Z.to_nat i) v) as Hupd.
      unfold locs, location_expr, location_val. cbn [locs_expr locs_val]. set_solver.
  - (* Prod *)
    transitivity (store_locs σ ∪ locs_storable (SProd v1 v2)).
    + apply store_locs_insert_subset.
    + unfold locs, location_expr, location_val. cbn [locs_expr locs_val locs_storable]. set_solver.
  - (* CAS *) subst σ'. destruct (bool_decide (v = v0)).
    + transitivity (store_locs σ ∪ locs_storable (SBlock (<[Z.to_nat i:=v']> bs))).
      * apply store_locs_insert_subset.
      * pose proof (locs_storable_store_subset σ l (SBlock bs) H0) as Hold.
        cbn [locs_storable] in Hold.
        pose proof (locs_storable_block_update bs (Z.to_nat i) v') as Hupd.
        unfold locs, location_expr, location_val. cbn [locs_expr locs_val]. set_solver.
    + unfold locs, location_expr, location_val. cbn [locs_expr locs_val]. set_solver.
  - (* In *) destruct b; cbn [locs_storable].
    + transitivity (store_locs σ ∪ locs_storable (SInL v)).
      * apply store_locs_insert_subset.
      * unfold locs, location_expr, location_val. cbn [locs_expr locs_val locs_storable]. set_solver.
    + transitivity (store_locs σ ∪ locs_storable (SInR v)).
      * apply store_locs_insert_subset.
      * unfold locs, location_expr, location_val. cbn [locs_expr locs_val locs_storable]. set_solver.
Qed.

Lemma sched_step_store_locs_bound : forall σ α G T e σ' α' G' T' e',
  sched_step σ α G T e σ' α' G' T' e' ->
  store_locs σ' ⊆ store_locs σ ∪ locs e ∪ dom α'.
Proof.
  intros σ α G T e σ' α' G' T' e' Hs. inversion Hs; subst.
  - eapply head_step_store_locs_bound; eauto.
  - set_solver.
  - transitivity (store_locs σ ∪ locs_storable (SProd v1 v2)).
    + apply store_locs_insert_subset.
    + unfold locs, location_expr, location_val. cbn [locs_expr locs_val locs_storable]. set_solver.
Qed.

Lemma step_store_locs_bound : forall σ α G T e σ' α' G' T' e',
  lang.semantics.step σ α G T e σ' α' G' T' e' ->
  store_locs σ' ⊆ store_locs σ ∪ locs e ∪ dom α'.
Proof.
  intros σ α G T e σ' α' G' T' e' Hs. induction Hs.
  - eapply sched_step_store_locs_bound; eauto.
  - rewrite locs_fill_item_eq. set_solver.
  - cbn [locs_expr]. set_solver.
  - cbn [locs_expr]. set_solver.
Qed.

Lemma all_abef_fill_item : forall (G:graph) α t (K:ctx) e,
  all_abef G α t (locs K ∪ locs e) -> all_abef G α t (locs (fill_item K e)).
Proof.
  intros. apply all_abef_subseteq with (locs K ∪ locs e); [|exact H].
  rewrite locs_fill_item_eq. set_solver.
Qed.

Lemma all_abef_subst : forall (G:graph) α t x v e,
  all_abef G α t (locs e ∪ locs v) -> all_abef G α t (locs (subst x v e)).
Proof.
  intros. apply all_abef_subseteq with (locs e ∪ locs v); [apply locs_subst_subset|exact H].
Qed.

Lemma all_abef_subst' : forall (G:graph) α t (b:binder) v e,
  all_abef G α t (locs e ∪ locs v) -> all_abef G α t (locs (subst' b v e)).
Proof.
  intros. apply all_abef_subseteq with (locs e ∪ locs v); [apply locs_subst'_subset|exact H].
Qed.

Lemma all_abef_substs' : forall (G:graph) α t (xlvs:list (binder*val)) e,
  all_abef G α t (locs e ∪ ⋃ (locs <$> (snd <$> xlvs))) ->
  all_abef G α t (locs (substs' xlvs e)).
Proof.
  intros. apply all_abef_subseteq with (locs e ∪ ⋃ (locs <$> (snd <$> xlvs)));
    [apply locs_substs'_subset|exact H].
Qed.

Definition StoreAbeInv (G:graph) (α:amap) (σ:store) (t:timestamp) : Prop :=
  forall l st, σ !! l = Some st -> all_abef G α t (locs_storable st).

Lemma all_abef_store_locs : forall (G:graph) α t (σ:store),
  StoreAbeInv G α σ t -> all_abef G α t (store_locs σ).
Proof.
  intros G α t σ H l0 Hl0. apply elem_of_store_locs in Hl0.
  destruct Hl0 as (l & st & Hlook & Hmem).
  unfold StoreAbeInv in H. unfold all_abef, set_Forall in *.
  specialize (H l st Hlook). apply H. exact Hmem.
Qed.

Lemma head_step_all_abef : forall G t σ α e σ' α' e' New,
  head_step G t σ α e σ' α' e' ->
  locs e' ⊆ locs e ∪ store_locs σ ∪ New ->
  (forall l, l ∈ New -> α' !! l = Some t) ->
  all_abef G α t (locs e) ->
  StoreAbeInv G α σ t ->
  all_abef G α' t (locs e').
Proof.
  intros G t σ α e σ' α' e' New Hs Hb Hnew He Hstore.
  pose proof (head_step_α_sub _ _ _ _ _ _ _ _ Hs) as Hasub.
  apply all_abef_subseteq with (locs e ∪ store_locs σ ∪ New); [exact Hb|].
  apply all_abef_union. split.
  - apply all_abef_union. split.
    + eapply all_abef_mono_α; eauto.
    + eapply all_abef_mono_α; [exact Hasub|]. apply all_abef_store_locs. exact Hstore.
  - unfold all_abef, set_Forall. intros l Hl. unfold abef.
    rewrite (Hnew l Hl). apply rtc_refl.
Qed.

(* ---------- type size facts ---------- *)
Lemma pos_typ_size : forall ρ, 1 <= typ_size ρ.
Proof. intros. destruct ρ; simpl; lia. Qed.
Lemma pos_typat_size : forall σt, 1 <= typat_size σt.
Proof. intros. destruct σt; simpl; lia. Qed.


(* ---------- fvv_typ/fvv_typat monotone under type-variable substitution ---------- *)
Lemma diff_subseteq_mono : forall (A B C:gset string), A ⊆ B -> A ∖ C ⊆ B ∖ C.
Proof. intros A B C H. apply elem_of_subseteq. intros z Hz.
  rewrite elem_of_difference in Hz. rewrite elem_of_difference.
  destruct Hz as [H1 H2]. split; [|exact H2]. rewrite elem_of_subseteq in H. auto. Qed.


Lemma fvv_subst_all : forall fuel,
  (forall x ρ' ρ, typ_size ρ <= fuel ->
     fvv_typ (vsubst_typ x ρ' ρ) ⊆ fvv_typ ρ' ∪ (fvv_typ ρ ∖ {[x]}))
  /\ (forall x ρ' σt, typat_size σt <= fuel ->
     fvv_typat (vsubst_typat x ρ' σt) ⊆ fvv_typ ρ' ∪ (fvv_typat σt ∖ {[x]}))
  /\ (forall x ρ' ts, S (list_sum (typ_size <$> ts)) <= fuel ->
     ⋃ (fvv_typ <$> (vsubst_typ x ρ' <$> ts)) ⊆ fvv_typ ρ' ∪ (⋃ (fvv_typ <$> ts) ∖ {[x]})).
Proof.
  induction fuel as [|fuel IH].
  - split; [|split].
    + intros x ρ' ρ H. exfalso. pose proof (pos_typ_size ρ). lia.
    + intros x ρ' σt H. exfalso. pose proof (pos_typat_size σt). lia.
    + intros x ρ' ts H. exfalso. lia.
  - destruct IH as (IHt & IHty & IHl).
    split; [|split].
    + intros x ρ' ρ H. destruct ρ as [y|b|σt δ|y ρ0|ρ0 δ|y k ρ0|y σt δ]; cbn [vsubst_typ fvv_typ typ_size] in *.
      * destruct (decide (x = y)) as [e|ne].
        -- subst. cbn. set_solver.
        -- cbn. set_solver.
      * set_solver.
      * transitivity (fvv_typ ρ' ∪ (fvv_typat σt ∖ {[x]})).
        -- apply (IHty x ρ' σt). lia.
        -- set_solver.
      * transitivity (fvv_typ ρ' ∪ (fvv_typ ρ0 ∖ {[x]})).
        -- apply (IHt x ρ' ρ0). lia.
        -- set_solver.
      * transitivity (fvv_typ ρ' ∪ (fvv_typ ρ0 ∖ {[x]})).
        -- apply (IHt x ρ' ρ0). lia.
        -- set_solver.
      * destruct y as [|y]; cbn [vsubst_typ fvv_typ binder_set typ_size] in *.
        -- destruct (decide (BNamed x = BAnon)) as [e|ne]; [discriminate e|].
           apply elem_of_subseteq. intros z Hz.
           cbn [fvv_typ binder_set] in Hz.
           try (rewrite elem_of_difference in Hz; destruct Hz as [Hz _]).
           assert (Hsub : fvv_typ (vsubst_typ x ρ' ρ0) ⊆ fvv_typ ρ' ∪ (fvv_typ ρ0 ∖ {[x]})) by (apply (IHt x ρ' ρ0); lia).
           apply elem_of_subseteq in Hsub. specialize (Hsub z Hz). set_solver.
        -- destruct (decide (BNamed x = BNamed y)) as [e|ne].
           ++ injection e as e'. subst y. cbn. set_solver.
           ++ cbn. apply elem_of_subseteq. intros z Hz.
              rewrite elem_of_difference in Hz. destruct Hz as [Hz Hny].
              assert (Hsub : fvv_typ (vsubst_typ x ρ' ρ0) ⊆ fvv_typ ρ' ∪ (fvv_typ ρ0 ∖ {[x]})) by (apply (IHt x ρ' ρ0); lia).
              apply elem_of_subseteq in Hsub. pose proof (Hsub z Hz) as Hz2. set_solver.
      * destruct (decide (BNamed x = BNamed y)) as [e|ne].
        -- injection e as e'. subst y. cbn [vsubst_typ fvv_typ fvv_typat binder_set]. set_solver.
        -- cbn [vsubst_typ fvv_typ fvv_typat binder_set].
           apply elem_of_subseteq. intros z Hz.
           rewrite elem_of_difference in Hz. destruct Hz as [Hz Hny].
           assert (Hsub : fvv_typat (vsubst_typat x ρ' σt) ⊆ fvv_typ ρ' ∪ (fvv_typat σt ∖ {[x]})) by (apply (IHty x ρ' σt); lia).
           apply elem_of_subseteq in Hsub. pose proof (Hsub z Hz) as Hz2. set_solver.
    + intros x ρ' σt H. destruct σt as [ρ0|ρ1 ρ2|ρ1 ρ2|bs Δ δ ρs ρf]; cbn [vsubst_typat fvv_typat typat_size] in *.
      * transitivity (fvv_typ ρ' ∪ (fvv_typ ρ0 ∖ {[x]})).
        -- apply (IHt x ρ' ρ0). lia. -- set_solver.
      * rewrite union_subseteq. split.
        -- transitivity (fvv_typ ρ' ∪ (fvv_typ ρ1 ∖ {[x]})). ++ apply (IHt x ρ' ρ1). lia. ++ set_solver.
        -- transitivity (fvv_typ ρ' ∪ (fvv_typ ρ2 ∖ {[x]})). ++ apply (IHt x ρ' ρ2). lia. ++ set_solver.
      * rewrite union_subseteq. split.
        -- transitivity (fvv_typ ρ' ∪ (fvv_typ ρ1 ∖ {[x]})). ++ apply (IHt x ρ' ρ1). lia. ++ set_solver.
        -- transitivity (fvv_typ ρ' ∪ (fvv_typ ρ2 ∖ {[x]})). ++ apply (IHt x ρ' ρ2). lia. ++ set_solver.
      * rewrite union_subseteq. split.
        -- transitivity (fvv_typ ρ' ∪ (fvv_typ ρf ∖ {[x]})). ++ apply (IHt x ρ' ρf). lia. ++ set_solver.
        -- apply elem_of_subseteq. intros z Hz.
           assert (Hsub : ⋃ (fvv_typ <$> (vsubst_typ x ρ' <$> ρs)) ⊆ fvv_typ ρ' ∪ (⋃ (fvv_typ <$> ρs) ∖ {[x]})) by (apply (IHl x ρ' ρs); pose proof (pos_typ_size ρf); lia).
           apply elem_of_subseteq in Hsub. specialize (Hsub z Hz).
           rewrite elem_of_union in Hsub. destruct Hsub as [H1|H1].
           ++ rewrite elem_of_union. left. exact H1.
           ++ rewrite elem_of_difference in H1. destruct H1 as [H1 Hnx].
              rewrite elem_of_union. right. rewrite elem_of_difference. split.
              ** rewrite elem_of_union. right. exact H1.
              ** exact Hnx.
    + intros x ρ' ts H. destruct ts as [|t ts']; cbn [vsubst_typ fvv_typ list_sum list_fmap] in *.
      * set_solver.
      * simpl in H. simpl. rewrite union_subseteq. split.
        -- transitivity (fvv_typ ρ' ∪ (fvv_typ t ∖ {[x]})).
           ++ apply (IHt x ρ' t).
              lia.
           ++ set_solver.
        -- apply elem_of_subseteq. intros z Hz.
           assert (Hs : S (list_sum (list_fmap typ nat typ_size ts')) <= fuel) by (pose proof (pos_typ_size t); lia).
           assert (Hsub : ⋃ (fvv_typ <$> (vsubst_typ x ρ' <$> ts')) ⊆ fvv_typ ρ' ∪ (⋃ (fvv_typ <$> ts') ∖ {[x]})) by (apply (IHl x ρ' ts'); exact Hs).
           apply elem_of_subseteq in Hsub. specialize (Hsub z Hz).
           rewrite elem_of_union in Hsub. destruct Hsub as [H1|H1].
           ++ rewrite elem_of_union. left. exact H1.
           ++ rewrite elem_of_difference in H1. destruct H1 as [H1 Hnx].
              rewrite elem_of_union. right. rewrite elem_of_difference. split.
              ** rewrite elem_of_union. right. exact H1.
              ** exact Hnx.
Qed.


Lemma subseteq_difference_union : forall (A B C D:gset string),
  B ⊆ A ∪ C -> B ∖ D ⊆ A ∪ (C ∖ D).
Proof.
  intros A B C D H. apply elem_of_subseteq. intros z Hz.
  rewrite elem_of_difference in Hz. destruct Hz as [Hz HnD].
  apply elem_of_subseteq in H. specialize (H z Hz).
  rewrite elem_of_union in H. destruct H as [H|H].
  - rewrite elem_of_union. left. exact H.
  - rewrite elem_of_union. right. rewrite elem_of_difference. split; auto.
Qed.

Lemma fv_subst_all : forall fuel,
  (forall x ρ' ρ, typ_size ρ <= fuel ->
     fv_typ (vsubst_typ x ρ' ρ) ⊆ fv_typ ρ' ∪ fv_typ ρ)
  /\ (forall x ρ' σt, typat_size σt <= fuel ->
     fv_typat (vsubst_typat x ρ' σt) ⊆ fv_typ ρ' ∪ fv_typat σt)
  /\ (forall x ρ' ts, S (list_sum (typ_size <$> ts)) <= fuel ->
     ⋃ (fv_typ <$> (vsubst_typ x ρ' <$> ts)) ⊆ fv_typ ρ' ∪ ⋃ (fv_typ <$> ts)).
Proof.
  induction fuel as [|fuel IH].
  - split; [|split].
    + intros x ρ' ρ H. exfalso. pose proof (pos_typ_size ρ). lia.
    + intros x ρ' σt H. exfalso. pose proof (pos_typat_size σt). lia.
    + intros x ρ' ts H. exfalso. lia.
  - destruct IH as (IHt & IHty & IHl). split; [|split].
    + intros x ρ' ρ H. destruct ρ as [y|b|σt δ|y ρ0|ρ0 δ|y k ρ0|y σt δ]; cbn [vsubst_typ fv_typ typ_size] in *.
      * destruct (decide (x = y)) as [e|ne].
        -- subst. cbn. set_solver.
        -- cbn. set_solver.
      * set_solver.
      * assert (Hsub := IHty x ρ' σt ltac:(lia)). apply elem_of_subseteq in Hsub.
        apply elem_of_subseteq. intros z Hz.
        rewrite elem_of_union in Hz. destruct Hz as [Hz|Hz].
        -- assert (Hz2 := Hsub z Hz). set_solver.
        -- set_solver.
      * assert (Hsub := IHt x ρ' ρ0 ltac:(lia)). apply elem_of_subseteq in Hsub.
        apply elem_of_subseteq. intros z Hz.
        rewrite elem_of_difference in Hz. destruct Hz as [Hz Hn].
        assert (Hz2 := Hsub z Hz). set_solver.
      * assert (Hsub := IHt x ρ' ρ0 ltac:(lia)). apply elem_of_subseteq in Hsub.
        apply elem_of_subseteq. intros z Hz.
        rewrite elem_of_union in Hz. destruct Hz as [Hz|Hz].
        -- assert (Hz2 := Hsub z Hz). set_solver.
        -- set_solver.
      * destruct y as [|y]; cbn [vsubst_typ fv_typ typ_size] in *.
        -- apply (IHt x ρ' ρ0); lia.
        -- destruct (decide (BNamed x = BNamed y)) as [e|ne].
           ++ injection e as e'. subst y. cbn. set_solver.
           ++ cbn. apply (IHt x ρ' ρ0); lia.
      * destruct (decide (BNamed x = BNamed y)) as [e|ne].
        -- injection e as e'. subst y. cbn [vsubst_typ fv_typ typ_size]. set_solver.
        -- cbn [vsubst_typ fv_typ typ_size].
           assert (Hsub := IHty x ρ' σt ltac:(lia)). apply elem_of_subseteq in Hsub.
           apply elem_of_subseteq. intros z Hz.
           rewrite elem_of_union in Hz. destruct Hz as [Hz|Hz].
           ++ assert (Hz2 := Hsub z Hz). set_solver.
           ++ set_solver.
    + intros x ρ' σt H. destruct σt as [ρ0|ρ1 ρ2|ρ1 ρ2|bs Δ δ ρs ρf]; cbn [vsubst_typat fv_typat typat_size] in *.
      * apply (IHt x ρ' ρ0); lia.
      * rewrite union_subseteq. split.
        -- transitivity (fv_typ ρ' ∪ fv_typ ρ1). ++ apply (IHt x ρ' ρ1); lia. ++ set_solver.
        -- transitivity (fv_typ ρ' ∪ fv_typ ρ2). ++ apply (IHt x ρ' ρ2); lia. ++ set_solver.
      * rewrite union_subseteq. split.
        -- transitivity (fv_typ ρ' ∪ fv_typ ρ1). ++ apply (IHt x ρ' ρ1); lia. ++ set_solver.
        -- transitivity (fv_typ ρ' ∪ fv_typ ρ2). ++ apply (IHt x ρ' ρ2); lia. ++ set_solver.
      * assert (Hf := IHt x ρ' ρf ltac:(lia)).
        assert (Hl : ⋃ (fv_typ <$> (vsubst_typ x ρ' <$> ρs)) ⊆ fv_typ ρ' ∪ ⋃ (fv_typ <$> ρs))
          by (apply (IHl x ρ' ρs); pose proof (pos_typ_size ρf); lia).
        eapply subseteq_difference_union.
        { apply elem_of_subseteq in Hf. apply elem_of_subseteq in Hl. set_solver. }
    + intros x ρ' ts H. destruct ts as [|t ts']; cbn [vsubst_typ fv_typ list_sum list_fmap] in *.
      * set_solver.
      * simpl in H. simpl. rewrite union_subseteq. split.
        -- transitivity (fv_typ ρ' ∪ fv_typ t).
           ++ apply (IHt x ρ' t). lia.
           ++ set_solver.
        -- apply elem_of_subseteq. intros z Hz.
           assert (Hs : S (list_sum (list_fmap typ nat typ_size ts')) <= fuel) by (pose proof (pos_typ_size t); lia).
           assert (Hsub : ⋃ (fv_typ <$> (vsubst_typ x ρ' <$> ts')) ⊆ fv_typ ρ' ∪ ⋃ (fv_typ <$> ts')) by (apply (IHl x ρ' ts'); exact Hs).
           apply elem_of_subseteq in Hsub. specialize (Hsub z Hz). set_solver.
Qed.

Lemma bv_tsubst_eq : forall fuel,
  (forall (m:gmap string string) ρ, typ_size ρ <= fuel ->
     bv_typ (tsubst_typ m ρ) = bv_typ ρ)
  /\ (forall (m:gmap string string) σt, typat_size σt <= fuel ->
     bv_typat (tsubst_typat m σt) = bv_typat σt)
  /\ (forall (m:gmap string string) ts, S (list_sum (typ_size <$> ts)) <= fuel ->
     ⋃ (bv_typ <$> (tsubst_typ m <$> ts)) = ⋃ (bv_typ <$> ts)).
Proof.
  induction fuel as [|fuel IH].
  - split; [|split].
    + intros m ρ H. exfalso. pose proof (pos_typ_size ρ). lia.
    + intros m σt H. exfalso. pose proof (pos_typat_size σt). lia.
    + intros m ts H. exfalso. lia.
  - destruct IH as (IHt & IHty & IHl). split; [|split].
    + intros m ρ H. destruct ρ as [y|b|σt δ|y ρ0|ρ0 δ|y k ρ0|y σt δ]; cbn [tsubst_typ bv_typ typ_size] in *.
      * reflexivity.
      * reflexivity.
      * apply IHty; lia.
      * rewrite (IHt (bdelete y m) ρ0 ltac:(lia)). reflexivity.
      * apply IHt; lia.
      * apply IHt; lia.
      * apply IHty; lia.
    + intros m σt H. destruct σt as [ρ0|ρ1 ρ2|ρ1 ρ2|bs Δ δ ρs ρf]; cbn [tsubst_typat bv_typat typat_size] in *.
      * apply IHt; lia.
      * rewrite (IHt m ρ1 ltac:(lia)), (IHt m ρ2 ltac:(lia)). reflexivity.
      * rewrite (IHt m ρ1 ltac:(lia)), (IHt m ρ2 ltac:(lia)). reflexivity.
      * rewrite (IHt (bdeletes bs m) ρf ltac:(lia)).
        rewrite (IHl (bdeletes bs m) ρs ltac:(pose proof (pos_typ_size ρf); lia)). reflexivity.
    + intros m ts H. destruct ts as [|t ts']; cbn [tsubst_typ bv_typ list_sum list_fmap] in *.
      * reflexivity.
      * simpl in H. simpl.
        rewrite (IHt m t ltac:(lia)).
        assert (Hs : S (list_sum (list_fmap typ nat typ_size ts')) <= fuel) by (pose proof (pos_typ_size t); lia).
        f_equal. apply (IHl m ts' Hs).
Qed.

Lemma bvv_tsubst_eq : forall fuel,
  (forall (m:gmap string string) ρ, typ_size ρ <= fuel ->
     bvv_typ (tsubst_typ m ρ) = bvv_typ ρ)
  /\ (forall (m:gmap string string) σt, typat_size σt <= fuel ->
     bvv_typat (tsubst_typat m σt) = bvv_typat σt)
  /\ (forall (m:gmap string string) ts, S (list_sum (typ_size <$> ts)) <= fuel ->
     ⋃ (bvv_typ <$> (tsubst_typ m <$> ts)) = ⋃ (bvv_typ <$> ts)).
Proof.
  induction fuel as [|fuel IH].
  - split; [|split].
    + intros m ρ H. exfalso. pose proof (pos_typ_size ρ). lia.
    + intros m σt H. exfalso. pose proof (pos_typat_size σt). lia.
    + intros m ts H. exfalso. lia.
  - destruct IH as (IHt & IHty & IHl). split; [|split].
    + intros m ρ H. destruct ρ as [y|b|σt δ|y ρ0|ρ0 δ|y k ρ0|y σt δ]; cbn [tsubst_typ bvv_typ typ_size] in *.
      * reflexivity.
      * reflexivity.
      * apply IHty; lia.
      * apply IHt; lia.
      * apply IHt; lia.
      * rewrite (IHt m ρ0 ltac:(lia)). reflexivity.
      * rewrite (IHty m σt ltac:(lia)). reflexivity.
    + intros m σt H. destruct σt as [ρ0|ρ1 ρ2|ρ1 ρ2|bs Δ δ ρs ρf]; cbn [tsubst_typat bvv_typat typat_size] in *.
      * apply IHt; lia.
      * rewrite (IHt m ρ1 ltac:(lia)), (IHt m ρ2 ltac:(lia)). reflexivity.
      * rewrite (IHt m ρ1 ltac:(lia)), (IHt m ρ2 ltac:(lia)). reflexivity.
      * rewrite (IHt (bdeletes bs m) ρf ltac:(lia)).
        rewrite (IHl (bdeletes bs m) ρs ltac:(pose proof (pos_typ_size ρf); lia)). reflexivity.
    + intros m ts H. destruct ts as [|t ts']; cbn [tsubst_typ bvv_typ list_sum list_fmap] in *.
      * reflexivity.
      * simpl in H. simpl.
        rewrite (IHt m t ltac:(lia)).
        assert (Hs : S (list_sum (list_fmap typ nat typ_size ts')) <= fuel) by (pose proof (pos_typ_size t); lia).
        f_equal. apply (IHl m ts' Hs).
Qed.

Lemma bv_vsubst_all : forall fuel,
  (forall x ρ' ρ, typ_size ρ <= fuel ->
     bv_typ (vsubst_typ x ρ' ρ) ⊆ bv_typ ρ' ∪ bv_typ ρ)
  /\ (forall x ρ' σt, typat_size σt <= fuel ->
     bv_typat (vsubst_typat x ρ' σt) ⊆ bv_typ ρ' ∪ bv_typat σt)
  /\ (forall x ρ' ts, S (list_sum (typ_size <$> ts)) <= fuel ->
     ⋃ (bv_typ <$> (vsubst_typ x ρ' <$> ts)) ⊆ bv_typ ρ' ∪ ⋃ (bv_typ <$> ts)).
Proof.
  induction fuel as [|fuel IH].
  - split; [|split].
    + intros x ρ' ρ H. exfalso. pose proof (pos_typ_size ρ). lia.
    + intros x ρ' σt H. exfalso. pose proof (pos_typat_size σt). lia.
    + intros x ρ' ts H. exfalso. lia.
  - destruct IH as (IHt & IHty & IHl). split; [|split].
    + intros x ρ' ρ H. destruct ρ as [y|b|σt δ|y ρ0|ρ0 δ|y k ρ0|y σt δ]; cbn [vsubst_typ bv_typ typ_size] in *.
      * destruct (decide (x = y)) as [e|ne].
        -- subst. cbn. set_solver.
        -- cbn. set_solver.
      * set_solver.
      * assert (Hsub := IHty x ρ' σt ltac:(lia)). apply elem_of_subseteq in Hsub.
        apply elem_of_subseteq. intros z Hz. apply Hsub in Hz.
        rewrite elem_of_union in *. destruct Hz as [Hz|Hz]; auto.
      * assert (Hsub := IHt x ρ' ρ0 ltac:(lia)). apply elem_of_subseteq in Hsub.
        apply elem_of_subseteq. intros z Hz.
        rewrite elem_of_union in Hz. destruct Hz as [Hz|Hz].
        -- rewrite elem_of_union. right. rewrite elem_of_union. left. exact Hz.
        -- apply Hsub in Hz. rewrite elem_of_union in Hz. destruct Hz as [Hz|Hz].
           ++ rewrite elem_of_union. left. exact Hz.
           ++ rewrite elem_of_union. right. rewrite elem_of_union. right. exact Hz.
      * assert (Hsub := IHt x ρ' ρ0 ltac:(lia)). apply elem_of_subseteq in Hsub.
        apply elem_of_subseteq. intros z Hz. apply Hsub in Hz.
        rewrite elem_of_union in *. destruct Hz as [Hz|Hz]; auto.
      * destruct y as [|y]; cbn [vsubst_typ bv_typ typ_size] in *.
        -- apply (IHt x ρ' ρ0); lia.
        -- destruct (decide (BNamed x = BNamed y)) as [e|ne].
           ++ injection e as e'. subst y. cbn. set_solver.
           ++ cbn. apply (IHt x ρ' ρ0); lia.
      * destruct (decide (BNamed x = BNamed y)) as [e|ne].
        -- injection e as e'. subst y. cbn [vsubst_typ bv_typ typ_size]. set_solver.
        -- cbn [vsubst_typ bv_typ typ_size].
           assert (Hsub := IHty x ρ' σt ltac:(lia)). apply elem_of_subseteq in Hsub.
           apply elem_of_subseteq. intros z Hz. apply Hsub in Hz.
           rewrite elem_of_union in *. destruct Hz as [Hz|Hz]; auto.
    + intros x ρ' σt H. destruct σt as [ρ0|ρ1 ρ2|ρ1 ρ2|bs Δ δ ρs ρf]; cbn [vsubst_typat bv_typat typat_size] in *.
      * apply (IHt x ρ' ρ0); lia.
      * rewrite union_subseteq. split.
        -- transitivity (bv_typ ρ' ∪ bv_typ ρ1). apply (IHt x ρ' ρ1); lia. set_solver.
        -- transitivity (bv_typ ρ' ∪ bv_typ ρ2). apply (IHt x ρ' ρ2); lia. set_solver.
      * rewrite union_subseteq. split.
        -- transitivity (bv_typ ρ' ∪ bv_typ ρ1). apply (IHt x ρ' ρ1); lia. set_solver.
        -- transitivity (bv_typ ρ' ∪ bv_typ ρ2). apply (IHt x ρ' ρ2); lia. set_solver.
      * assert (Hf := IHt x ρ' ρf ltac:(lia)).
        assert (Hl : ⋃ (bv_typ <$> (vsubst_typ x ρ' <$> ρs)) ⊆ bv_typ ρ' ∪ ⋃ (bv_typ <$> ρs))
          by (apply (IHl x ρ' ρs); pose proof (pos_typ_size ρf); lia).
        apply elem_of_subseteq in Hf. apply elem_of_subseteq in Hl.
        apply elem_of_subseteq. intros z Hz.
        rewrite elem_of_union in *. set_solver.
    + intros x ρ' ts H. destruct ts as [|t ts']; cbn [vsubst_typ bv_typ list_sum list_fmap] in *.
      * set_solver.
      * simpl in H. simpl. rewrite union_subseteq. split.
        -- transitivity (bv_typ ρ' ∪ bv_typ t). apply (IHt x ρ' t); lia. set_solver.
        -- apply elem_of_subseteq. intros z Hz.
           assert (Hs : S (list_sum (list_fmap typ nat typ_size ts')) <= fuel) by (pose proof (pos_typ_size t); lia).
           assert (Hsub : ⋃ (bv_typ <$> (vsubst_typ x ρ' <$> ts')) ⊆ bv_typ ρ' ∪ ⋃ (bv_typ <$> ts')) by (apply (IHl x ρ' ts'); exact Hs).
           apply elem_of_subseteq in Hsub. specialize (Hsub z Hz). set_solver.
Qed.

Definition mvalues (m:gmap string string) : gset string := map_img m.

Lemma find_opt_mem : forall (m:gmap string string) x,
  find_opt m x = x \/ find_opt m x ∈ mvalues m.
Proof.
  intros m x. unfold find_opt. destruct (m !! x) as [v|] eqn:E; simpl.
  - right. unfold mvalues. eapply elem_of_map_img_2. exact E.
  - left. reflexivity.
Qed.

Lemma elem_of_fv_fold : forall (l:list (stimestamp * stimestamp)) z,
  z ∈ foldr (fun '(a,b) acc => {[a;b]} ∪ acc) (∅ : gset string) l <->
  exists p, p ∈ l /\ (z = fst p \/ z = snd p).
Proof.
  induction l as [|p l IH]; intros z.
  - simpl. split; [set_solver|]. intros (q & Hq & _). apply elem_of_nil in Hq. contradiction.
  - destruct p as [a b]. simpl. rewrite elem_of_union. rewrite IH. split.
    + intros [Hz|(q & Hq & Hz)].
      * exists (a,b). split; [set_solver|]. set_solver.
      * exists q. split; [set_solver|]. exact Hz.
    + intros (q & Hq & Hz). apply elem_of_cons in Hq. destruct Hq as [->|Hq].
      * left. set_solver.
      * right. exists q. split; auto.
Qed.

Lemma elem_of_fv_constraints : forall (Δ:constraints) z,
  z ∈ fv_constraints Δ <-> exists p, p ∈ Δ /\ (z = fst p \/ z = snd p).
Proof.
  intros Δ z.
  change (z ∈ foldr (fun '(a,b) acc => {[a;b]} ∪ acc) (∅ : gset string) (elements Δ) <->
          exists p, p ∈ Δ /\ (z = fst p \/ z = snd p)).
  rewrite elem_of_fv_fold.
  split.
  - intros (p & Hp & Hz). exists p. split.
    + exact (proj1 (elem_of_elements Δ p) Hp).
    + exact Hz.
  - intros (p & Hp & Hz). exists p. split.
    + exact (proj2 (elem_of_elements Δ p) Hp).
    + exact Hz.
Qed.

Lemma fv_constraints_not_mem : forall (Δ:constraints) z,
  z ∉ fv_constraints Δ -> forall x y, (x,y) ∈ Δ -> z ≠ x /\ z ≠ y.
Proof.
  intros Δ z Hz x y Hxy. split.
  - intro e. apply Hz. apply elem_of_fv_constraints.
    exists (x,y). split; [exact Hxy|]. left. exact e.
  - intro e. apply Hz. apply elem_of_fv_constraints.
    exists (x,y). split; [exact Hxy|]. right. exact e.
Qed.

Lemma tsubst_constraints_delete_irrel : forall (Δ:constraints) (m:gmap string string) z,
  z ∉ fv_constraints Δ ->
  tsubst_constraints (delete z m) Δ = tsubst_constraints m Δ.
Proof.
  intros Δ m z Hz. unfold tsubst_constraints.
  apply leibniz_equiv_iff. rewrite set_equiv. intros [a b].
  rewrite !elem_of_map. split.
  - intros (q & Heq & Hq). destruct q as [c d]. simpl in Heq.
    destruct (fv_constraints_not_mem Δ z Hz c d Hq) as (Hc & Hd).
    exists (c,d). split.
    + rewrite (find_opt_delete_ne m z c Hc) in Heq.
      rewrite (find_opt_delete_ne m z d Hd) in Heq.
      exact Heq.
    + exact Hq.
  - intros (q & Heq & Hq). destruct q as [c d]. simpl in Heq.
    destruct (fv_constraints_not_mem Δ z Hz c d Hq) as (Hc & Hd).
    exists (c,d). split.
    + rewrite (find_opt_delete_ne m z c Hc).
      rewrite (find_opt_delete_ne m z d Hd).
      exact Heq.
    + exact Hq.
Qed.

Lemma tsubst_delete_fv_irrel : forall fuel,
  (forall (m:gmap string string) z ρ, typ_size ρ <= fuel -> z ∉ fv_typ ρ ->
     tsubst_typ (delete z m) ρ = tsubst_typ m ρ)
  /\ (forall (m:gmap string string) z σt, typat_size σt <= fuel -> z ∉ fv_typat σt ->
     tsubst_typat (delete z m) σt = tsubst_typat m σt)
  /\ (forall (m:gmap string string) z ts, S (list_sum (typ_size <$> ts)) <= fuel ->
     z ∉ ⋃ (fv_typ <$> ts) ->
     (tsubst_typ (delete z m) <$> ts) = (tsubst_typ m <$> ts)).
Proof.
  induction fuel as [|fuel IH].
  - split; [|split].
    + intros m z ρ H. exfalso. pose proof (pos_typ_size ρ). lia.
    + intros m z σt H. exfalso. pose proof (pos_typat_size σt). lia.
    + intros m z ts H. exfalso. lia.
  - destruct IH as (IHt & IHty & IHl). split; [|split].
    + intros m z ρ H Hz.
      destruct ρ as [y|b|σt δ|y ρ0|ρ0 δ|x k ρ0|x σt δ]; cbn [tsubst_typ fv_typ typ_size] in *.
      * reflexivity.
      * reflexivity.
      * rewrite (IHty m z σt ltac:(lia) ltac:(set_solver)).
        rewrite (find_opt_delete_ne m z δ ltac:(intro e; apply Hz; set_solver)).
        reflexivity.
      * cbn [tsubst_typ].
        destruct y as [|y].
        -- cbn [bdelete]. apply (f_equal (TLam BAnon)). apply IHt; [lia|]. set_solver.
        -- apply (f_equal (TLam (BNamed y))).
           destruct (decide (z = y)) as [e|ne].
           ++ subst z. change (tsubst_typ (delete y (delete y m)) ρ0 = tsubst_typ (delete y m) ρ0).
              rewrite delete_delete_eq. reflexivity.
           ++ change (tsubst_typ (bdelete (BNamed y) (bdelete (BNamed z) m)) ρ0
                        = tsubst_typ (bdelete (BNamed y) m) ρ0).
              rewrite (bdelete_bdelete_comm string (BNamed y) (BNamed z) m).
              change (tsubst_typ (delete z (bdelete (BNamed y) m)) ρ0
                        = tsubst_typ (bdelete (BNamed y) m) ρ0).
              apply IHt; [lia|]. set_solver.
      * cbn [tsubst_typ].
        rewrite (IHt m z ρ0 ltac:(lia) ltac:(set_solver)).
        rewrite (find_opt_delete_ne m z δ ltac:(intro e; apply Hz; set_solver)).
        reflexivity.
      * cbn [tsubst_typ].
        rewrite (IHt m z ρ0 ltac:(lia) ltac:(set_solver)). reflexivity.
      * cbn [tsubst_typ].
        rewrite (IHty m z σt ltac:(lia) ltac:(set_solver)).
        rewrite (find_opt_delete_ne m z δ ltac:(intro e; apply Hz; set_solver)).
        reflexivity.
    + intros m z σt H Hz.
      destruct σt as [ρ0|ρ1 ρ2|ρ1 ρ2|bs Δ δ ρs ρf]; cbn [tsubst_typat fv_typat typat_size] in *.
      * cbn [tsubst_typat]. apply (f_equal TArray). apply IHt; [lia|]. set_solver.
      * cbn [tsubst_typat].
        rewrite (IHt m z ρ1 ltac:(lia) ltac:(set_solver)).
        rewrite (IHt m z ρ2 ltac:(lia) ltac:(set_solver)).
        reflexivity.
      * cbn [tsubst_typat].
        rewrite (IHt m z ρ1 ltac:(lia) ltac:(set_solver)).
        rewrite (IHt m z ρ2 ltac:(lia) ltac:(set_solver)).
        reflexivity.
      * destruct (decide (z ∈ binders_set bs)) as [Hzb|Hzb].
        -- rewrite (bdeletes_delete_mem bs m z Hzb). reflexivity.
        -- change (TArrow bs (tsubst_constraints (bdeletes bs (bdelete (BNamed z) m)) Δ)
                     (find_opt (bdeletes bs (bdelete (BNamed z) m)) δ)
                     (tsubst_typ (bdeletes bs (bdelete (BNamed z) m)) <$> ρs)
                     (tsubst_typ (bdeletes bs (bdelete (BNamed z) m)) ρf)
                   = TArrow bs (tsubst_constraints (bdeletes bs m) Δ)
                     (find_opt (bdeletes bs m) δ)
                     (tsubst_typ (bdeletes bs m) <$> ρs)
                     (tsubst_typ (bdeletes bs m) ρf)).
           rewrite (bdeletes_bdelete_comm string bs (BNamed z) m). cbn [bdelete].
           rewrite (tsubst_constraints_delete_irrel Δ (bdeletes bs m) z ltac:(set_solver)).
           rewrite (find_opt_delete_ne (bdeletes bs m) z δ ltac:(set_solver)).
           rewrite (IHt (bdeletes bs m) z ρf ltac:(lia) ltac:(set_solver)).
           rewrite (IHl (bdeletes bs m) z ρs ltac:(pose proof (pos_typ_size ρf); lia) ltac:(set_solver)).
           reflexivity.
    + intros m z ts H Hz.
      destruct ts as [|t ts']; cbn [tsubst_typ list_sum list_fmap] in *.
      * reflexivity.
      * simpl in H. simpl.
        rewrite (IHt m z t ltac:(lia) ltac:(set_solver)).
        assert (Hs : S (list_sum (list_fmap typ nat typ_size ts')) <= fuel)
          by (pose proof (pos_typ_size t); lia).
        apply (f_equal (cons (tsubst_typ m t))).
        apply (IHl m z ts' Hs). set_solver.
Qed.

Lemma vsubst_forall_eq : forall x ρ' (x0:binder) k ρ0,
  BNamed x = x0 -> vsubst_typ x ρ' (TForall x0 k ρ0) = TForall x0 k ρ0.
Proof.
  intros x ρ' x0 k ρ0 e. cbn [vsubst_typ].
  destruct (decide (BNamed x = x0)) as [e'|ne]; auto. contradiction.
Qed.
Lemma vsubst_forall_ne : forall x ρ' (x0:binder) k ρ0,
  BNamed x ≠ x0 -> vsubst_typ x ρ' (TForall x0 k ρ0) = TForall x0 k (vsubst_typ x ρ' ρ0).
Proof.
  intros x ρ' x0 k ρ0 ne. cbn [vsubst_typ].
  destruct (decide (BNamed x = x0)) as [e'|ne']; [contradiction|reflexivity].
Qed.
Lemma vsubst_rec_eq : forall x ρ' (x0:string) σt δ,
  BNamed x = x0 -> vsubst_typ x ρ' (TRec x0 σt δ) = TRec x0 σt δ.
Proof.
  intros x ρ' x0 σt δ e. cbn [vsubst_typ].
  destruct (decide (BNamed x = x0)) as [e'|ne]; auto. contradiction.
Qed.
Lemma vsubst_rec_ne : forall x ρ' (x0:string) σt δ,
  BNamed x ≠ x0 -> vsubst_typ x ρ' (TRec x0 σt δ) = TRec x0 (vsubst_typat x ρ' σt) δ.
Proof.
  intros x ρ' x0 σt δ ne. cbn [vsubst_typ].
  destruct (decide (BNamed x = x0)) as [e'|ne']; [contradiction|reflexivity].
Qed.

Lemma tsubst_bdeletes_fv_irrel : forall (bs:list binder) (m:gmap string string) ρ,
  fv_typ ρ ## binders_set bs -> tsubst_typ (bdeletes bs m) ρ = tsubst_typ m ρ.
Proof.
  induction bs as [|b bs IH]; intros m ρ Hd.
  - cbn [bdeletes]. reflexivity.
  - change (fv_typ ρ ## (binder_set b ∪ binders_set bs)) in Hd.
    destruct b as [|z].
    + cbn [bdeletes bdelete]. apply IH. set_solver.
    + cbn [bdeletes bdelete].
      change (tsubst_typ (delete z (bdeletes bs m)) ρ = tsubst_typ m ρ).
      assert (Hzv : z ∉ fv_typ ρ) by set_solver.
      rewrite (proj1 (tsubst_delete_fv_irrel (typ_size ρ)) (bdeletes bs m) z ρ (le_n _) Hzv).
      apply IH. set_solver.
Qed.

Lemma tsubst_vsubst_comm : forall fuel,
  (forall (m:gmap string string) x ρ' ρ, typ_size ρ <= fuel ->
     fv_typ ρ' ## bv_typ ρ ->
     tsubst_typ m (vsubst_typ x ρ' ρ) =
     vsubst_typ x (tsubst_typ m ρ') (tsubst_typ m ρ))
  /\ (forall (m:gmap string string) x ρ' σt, typat_size σt <= fuel ->
     fv_typ ρ' ## bv_typat σt ->
     tsubst_typat m (vsubst_typat x ρ' σt) =
     vsubst_typat x (tsubst_typ m ρ') (tsubst_typat m σt))
  /\ (forall (m:gmap string string) x ρ' ts, S (list_sum (typ_size <$> ts)) <= fuel ->
     fv_typ ρ' ## (⋃ (bv_typ <$> ts)) ->
     (tsubst_typ m <$> (vsubst_typ x ρ' <$> ts)) =
     (vsubst_typ x (tsubst_typ m ρ') <$> (tsubst_typ m <$> ts))).
Proof.
  induction fuel as [|fuel IH].
  - split; [|split].
    + intros m x ρ' ρ H. exfalso. pose proof (pos_typ_size ρ). lia.
    + intros m x ρ' σt H. exfalso. pose proof (pos_typat_size σt). lia.
    + intros m x ρ' ts H. exfalso. lia.
  - destruct IH as (IHt & IHty & IHl). split; [|split].
    + intros m x ρ' ρ H Hd.
      destruct ρ as [y|b|σt δ|y ρ0|ρ0 δ|x0 k ρ0|x0 σt δ];
        cbn [fv_typ typ_size bv_typ] in *.
      * cbn [vsubst_typ tsubst_typ].
        destruct (decide (x = y)) as [e|ne]; cbn; reflexivity.
      * cbn [vsubst_typ tsubst_typ]. reflexivity.
      * cbn [vsubst_typ tsubst_typ].
        apply (f_equal (fun st => TTypat st (find_opt m δ))).
        apply IHty; [lia|]. set_solver.
      * cbn [vsubst_typ tsubst_typ].
        apply (f_equal (fun rb => TLam y rb)).
        rewrite (IHt (bdelete y m) x ρ' ρ0 ltac:(lia) ltac:(set_solver)).
        destruct y as [|y].
        -- cbn [bdelete]. reflexivity.
        -- cbn [bdelete].
           assert (Hyv : y ∉ fv_typ ρ') by set_solver.
           rewrite (proj1 (tsubst_delete_fv_irrel (typ_size ρ')) m y ρ' (le_n _) Hyv).
           reflexivity.
      * cbn [vsubst_typ tsubst_typ].
        apply (f_equal (fun rb => TApp rb (find_opt m δ))).
        apply IHt; [lia|]. set_solver.
      * cbn [tsubst_typ].
        destruct (decide (BNamed x = x0)) as [e|ne].
        -- rewrite (vsubst_forall_eq x ρ' x0 k ρ0 e).
           rewrite (vsubst_forall_eq x (tsubst_typ m ρ') x0 k (tsubst_typ m ρ0) e).
           cbn [tsubst_typ]. reflexivity.
        -- rewrite (vsubst_forall_ne x ρ' x0 k ρ0 ne).
           rewrite (vsubst_forall_ne x (tsubst_typ m ρ') x0 k (tsubst_typ m ρ0) ne).
           cbn [tsubst_typ]. apply (f_equal (fun rb => TForall x0 k rb)).
           apply IHt; [lia|]. set_solver.
      * cbn [tsubst_typ].
        destruct (decide (BNamed x = x0)) as [e|ne].
        -- rewrite (vsubst_rec_eq x ρ' x0 σt δ e).
           rewrite (vsubst_rec_eq x (tsubst_typ m ρ') x0 (tsubst_typat m σt) (find_opt m δ) e).
           cbn [tsubst_typ]. reflexivity.
        -- rewrite (vsubst_rec_ne x ρ' x0 σt δ ne).
           rewrite (vsubst_rec_ne x (tsubst_typ m ρ') x0 (tsubst_typat m σt) (find_opt m δ) ne).
           cbn [tsubst_typ]. apply (f_equal (fun st => TRec x0 st (find_opt m δ))).
           apply IHty; [lia|]. set_solver.
    + intros m x ρ' σt H Hd.
      destruct σt as [ρ0|ρ1 ρ2|ρ1 ρ2|bs Δ δ ρs ρf];
        cbn [vsubst_typat tsubst_typat fv_typat typat_size bv_typat] in *.
      * apply (f_equal (fun rb => TArray rb)). apply IHt; [lia|]. set_solver.
      * cbn [vsubst_typat tsubst_typat].
        rewrite (IHt m x ρ' ρ1 ltac:(lia) ltac:(set_solver)).
        rewrite (IHt m x ρ' ρ2 ltac:(lia) ltac:(set_solver)).
        reflexivity.
      * cbn [vsubst_typat tsubst_typat].
        rewrite (IHt m x ρ' ρ1 ltac:(lia) ltac:(set_solver)).
        rewrite (IHt m x ρ' ρ2 ltac:(lia) ltac:(set_solver)).
        reflexivity.
      * cbn [vsubst_typat tsubst_typat].
        assert (Hm : tsubst_typ (bdeletes bs m) ρ' = tsubst_typ m ρ')
          by (apply tsubst_bdeletes_fv_irrel; set_solver).
        rewrite (IHt (bdeletes bs m) x ρ' ρf ltac:(lia) ltac:(set_solver)).
        rewrite (IHl (bdeletes bs m) x ρ' ρs ltac:(pose proof (pos_typ_size ρf); lia) ltac:(set_solver)).
        rewrite Hm. reflexivity.
    + intros m x ρ' ts H Hd.
      destruct ts as [|t ts']; cbn [list_sum list_fmap].
      * reflexivity.
      * simpl in H. simpl.
        rewrite (IHt m x ρ' t ltac:(lia) ltac:(set_solver)).
        assert (Hs : S (list_sum (list_fmap typ nat typ_size ts')) <= fuel)
          by (pose proof (pos_typ_size t); lia).
        apply (f_equal (cons (vsubst_typ x (tsubst_typ m ρ') (tsubst_typ m t)))).
        apply (IHl m x ρ' ts' Hs). set_solver.
Qed.

Lemma fv_constraints_tsubst : forall (m:gmap string string) (Δ:constraints),
  fv_constraints (tsubst_constraints m Δ) ⊆ fv_constraints Δ ∪ mvalues m.
Proof.
  intros m Δ. apply elem_of_subseteq. intros z Hz.
  apply elem_of_fv_constraints in Hz.
  destruct Hz as (p & Hp & Hz).
  unfold tsubst_constraints in Hp.
  apply elem_of_map in Hp. destruct Hp as (q & Hpq & Hq).
  subst p.
  destruct q as [a b]. simpl in Hz.
  apply elem_of_union.
  destruct Hz as [Hz|Hz].
  - destruct (find_opt_mem m a) as [Ha|Ha].
    + left. apply elem_of_fv_constraints. exists (a,b). split; [exact Hq|]. left. rewrite Ha in Hz. exact Hz.
    + right. rewrite Hz. exact Ha.
  - destruct (find_opt_mem m b) as [Hb|Hb].
    + left. apply elem_of_fv_constraints. exists (a,b). split; [exact Hq|]. right. rewrite Hb in Hz. exact Hz.
    + right. rewrite Hz. exact Hb.
Qed.

Lemma mvalues_bdeletes : forall (bs:list binder) (m:gmap string string),
  mvalues (bdeletes bs m) ⊆ mvalues m.
Proof.
  induction bs as [|b bs IH]; intros m.
  - simpl. reflexivity.
  - simpl. destruct b.
    + apply IH.
    + transitivity (mvalues (bdeletes bs m)).
      * unfold mvalues. apply map_img_delete_subseteq.
      * apply IH.
Qed.

Lemma find_opt_dom : forall (m:gmap string string) x,
  x ∈ dom m -> find_opt m x ∈ mvalues m.
Proof.
  intros m x Hx. unfold find_opt. destruct (m !! x) as [v|] eqn:E.
  - unfold mvalues. eapply elem_of_map_img_2. exact E.
  - exfalso. exact ((proj2 (not_elem_of_dom m x) E) Hx).
Qed.

Lemma find_opt_ndom : forall (m:gmap string string) x,
  x ∉ dom m -> find_opt m x = x.
Proof.
  intros m x Hx. unfold find_opt. destruct (m !! x) as [v|] eqn:E; [|reflexivity].
  exfalso. apply Hx. eapply elem_of_dom_2. exact E.
Qed.

Lemma fv_constraints_tsubst_sharp : forall (m:gmap string string) (Δ:constraints),
  fv_constraints (tsubst_constraints m Δ) ⊆ (fv_constraints Δ ∖ dom m) ∪ mvalues m.
Proof.
  intros m Δ. apply elem_of_subseteq. intros z Hz.
  apply elem_of_fv_constraints in Hz. destruct Hz as (p & Hp & Hz).
  unfold tsubst_constraints in Hp. apply elem_of_map in Hp.
  destruct Hp as (q & Hpq & Hq). subst p.
  destruct q as [a b]. simpl in Hz.
  rewrite elem_of_union.
  destruct Hz as [Hz|Hz].
  - destruct (decide (a ∈ dom m)) as [Ha|Ha].
    + right. rewrite Hz. apply find_opt_dom; exact Ha.
    + left. assert (Ha' : find_opt m a = a) by (apply find_opt_ndom; exact Ha).
      rewrite Ha' in Hz. subst z. rewrite elem_of_difference. split.
      * apply elem_of_fv_constraints. exists (a,b). split; [exact Hq|]. left. reflexivity.
      * exact Ha.
  - destruct (decide (b ∈ dom m)) as [Hb|Hb].
    + right. rewrite Hz. apply find_opt_dom; exact Hb.
    + left. assert (Hb' : find_opt m b = b) by (apply find_opt_ndom; exact Hb).
      rewrite Hb' in Hz. subst z. rewrite elem_of_difference. split.
      * apply elem_of_fv_constraints. exists (a,b). split; [exact Hq|]. right. reflexivity.
      * exact Hb.
Qed.

Lemma elem_of_dom_bdelete : forall (m:gmap string string) (y:binder) x,
  x ∈ dom m -> x ∉ binder_set y -> x ∈ dom (bdelete y m).
Proof.
  intros m [|s] x Hx Hn; simpl in *.
  - exact Hx.
  - rewrite dom_delete. rewrite elem_of_difference. split; [exact Hx|exact Hn].
Qed.

Lemma dom_bdelete_subseteq : forall (m:gmap string string) (y:binder),
  dom (bdelete y m) ⊆ dom m.
Proof.
  intros m [|s]; simpl.
  - reflexivity.
  - rewrite dom_delete. set_solver.
Qed.

Lemma dom_bdeletes_subseteq : forall (bs:list binder) (m:gmap string string),
  dom (bdeletes bs m) ⊆ dom m.
Proof.
  induction bs as [|b bs IH]; intros m.
  - cbn [bdeletes]. reflexivity.
  - cbn [bdeletes]. destruct b.
    + cbn [bdelete]. apply IH.
    + cbn [bdelete]. transitivity (dom (bdeletes bs m)).
      * change (dom (delete s (bdeletes bs m)) ⊆ dom (bdeletes bs m)).
        rewrite dom_delete. set_solver.
      * apply IH.
Qed.

Lemma elem_of_dom_bdeletes : forall (bs:list binder) (m:gmap string string) x,
  x ∈ dom m -> x ∉ dom (bdeletes bs m) -> x ∈ binders_set bs.
Proof.
  induction bs as [|b bs IH]; intros m x Hx Hn.
  - change (x ∉ dom m) in Hn. exfalso. exact (Hn Hx).
  - change (x ∉ dom (bdelete b (bdeletes bs m))) in Hn.
    destruct b as [|s].
    + change (x ∉ dom (bdeletes bs m)) in Hn.
      specialize (IH m x Hx Hn).
      change (x ∈ (∅ : gset string) ∪ binders_set bs). set_solver.
    + change (x ∉ dom (delete s (bdeletes bs m))) in Hn.
      destruct (decide (x = s)) as [e|ne].
      * subst x. change (s ∈ ({[s]} : gset string) ∪ binders_set bs). set_solver.
      * assert (Hn' : x ∉ dom (bdeletes bs m)).
        { intro HxM. apply Hn. rewrite dom_delete. rewrite elem_of_difference. split.
          - exact HxM.
          - rewrite elem_of_singleton. exact ne. }
        specialize (IH m x Hx Hn').
        change (x ∈ ({[s]} : gset string) ∪ binders_set bs). set_solver.
Qed.

Lemma elem_of_binder_set_of_dom_bdelete : forall (m:gmap string string) (y:binder) x,
  x ∈ dom m -> x ∉ dom (bdelete y m) -> x ∈ binder_set y.
Proof.
  intros m y x Hx Hn.
  destruct (decide (x ∈ binder_set y)) as [Hin|Hout]; [exact Hin|].
  exfalso. apply Hn. apply elem_of_dom_bdelete; auto.
Qed.

Lemma fv_tsubst_all_sharp : forall fuel,
  (forall (m:gmap string string) ρ, typ_size ρ <= fuel ->
     fv_typ (tsubst_typ m ρ) ⊆ (fv_typ ρ ∖ dom m) ∪ mvalues m)
  /\ (forall (m:gmap string string) σt, typat_size σt <= fuel ->
     fv_typat (tsubst_typat m σt) ⊆ (fv_typat σt ∖ dom m) ∪ mvalues m)
  /\ (forall (m:gmap string string) ts, S (list_sum (typ_size <$> ts)) <= fuel ->
     ⋃ (fv_typ <$> (tsubst_typ m <$> ts)) ⊆ (⋃ (fv_typ <$> ts) ∖ dom m) ∪ mvalues m).
Proof.
  induction fuel as [|fuel IH].
  - split; [|split].
    + intros m ρ H. exfalso. pose proof (pos_typ_size ρ). lia.
    + intros m σt H. exfalso. pose proof (pos_typat_size σt). lia.
    + intros m ts H. exfalso. lia.
  - destruct IH as (IHt & IHty & IHl). split; [|split].
    + intros m ρ H. destruct ρ as [y|b|σt δ|y ρ0|ρ0 δ|y k ρ0|y σt δ]; cbn [tsubst_typ fv_typ typ_size] in *.
      * set_solver.
      * set_solver.
      * assert (Hsub := IHty m σt ltac:(lia)). apply elem_of_subseteq in Hsub.
        apply elem_of_subseteq. intros z Hz. rewrite elem_of_union in Hz. destruct Hz as [Hz|Hz].
        -- specialize (Hsub z Hz). rewrite elem_of_union in Hsub. destruct Hsub as [Hsub|Hsub].
           ++ rewrite elem_of_union. left. rewrite elem_of_difference in Hsub. destruct Hsub as [H1 H2].
              rewrite elem_of_difference. split; [set_solver|exact H2].
           ++ rewrite elem_of_union. right. exact Hsub.
        -- rewrite elem_of_singleton in Hz. subst z.
           destruct (decide (δ ∈ dom m)) as [Hd|Hd].
           ++ rewrite elem_of_union. right. apply find_opt_dom; exact Hd.
           ++ rewrite (find_opt_ndom m δ Hd). rewrite elem_of_union. left.
              rewrite elem_of_difference. split.
              ** rewrite elem_of_union. right. rewrite elem_of_singleton. reflexivity.
              ** exact Hd.
      * assert (Hsub := IHt (bdelete y m) ρ0 ltac:(lia)). apply elem_of_subseteq in Hsub.
        assert (Hmv0 : mvalues (bdelete y m) ⊆ mvalues m).
        { change (mvalues (bdeletes [y] m) ⊆ mvalues m). apply mvalues_bdeletes. }
        apply elem_of_subseteq in Hmv0.
        apply elem_of_subseteq. intros z Hz. rewrite elem_of_difference in Hz. destruct Hz as [Hz Hnb].
        specialize (Hsub z Hz). rewrite elem_of_union in Hsub. destruct Hsub as [Hsub|Hsub].
        -- rewrite elem_of_difference in Hsub. destruct Hsub as [H1 Hnd'].
           rewrite elem_of_union. left. rewrite elem_of_difference. split.
           ++ rewrite elem_of_difference. split; [exact H1|exact Hnb].
           ++ intro Hdom. apply Hnb. eapply elem_of_binder_set_of_dom_bdelete; eauto.
        -- rewrite elem_of_union. right. apply Hmv0. exact Hsub.
      * assert (Hsub := IHt m ρ0 ltac:(lia)). apply elem_of_subseteq in Hsub.
        apply elem_of_subseteq. intros z Hz. rewrite elem_of_union in Hz. destruct Hz as [Hz|Hz].
        -- specialize (Hsub z Hz). rewrite elem_of_union in Hsub. destruct Hsub as [Hsub|Hsub].
           ++ rewrite elem_of_union. left. rewrite elem_of_difference in Hsub. destruct Hsub as [H1 H2].
              rewrite elem_of_difference. split; [set_solver|exact H2].
           ++ rewrite elem_of_union. right. exact Hsub.
        -- rewrite elem_of_singleton in Hz. subst z.
           destruct (decide (δ ∈ dom m)) as [Hd|Hd].
           ++ rewrite elem_of_union. right. apply find_opt_dom; exact Hd.
           ++ rewrite (find_opt_ndom m δ Hd). rewrite elem_of_union. left.
              rewrite elem_of_difference. split.
              ** rewrite elem_of_union. right. rewrite elem_of_singleton. reflexivity.
              ** exact Hd.
      * apply (IHt m ρ0); lia.
      * assert (Hsub := IHty m σt ltac:(lia)). apply elem_of_subseteq in Hsub.
        apply elem_of_subseteq. intros z Hz. rewrite elem_of_union in Hz. destruct Hz as [Hz|Hz].
        -- specialize (Hsub z Hz). rewrite elem_of_union in Hsub. destruct Hsub as [Hsub|Hsub].
           ++ rewrite elem_of_union. left. rewrite elem_of_difference in Hsub. destruct Hsub as [H1 H2].
              rewrite elem_of_difference. split; [set_solver|exact H2].
           ++ rewrite elem_of_union. right. exact Hsub.
        -- rewrite elem_of_singleton in Hz. subst z.
           destruct (decide (δ ∈ dom m)) as [Hd|Hd].
           ++ rewrite elem_of_union. right. apply find_opt_dom; exact Hd.
           ++ rewrite (find_opt_ndom m δ Hd). rewrite elem_of_union. left.
              rewrite elem_of_difference. split.
              ** rewrite elem_of_union. right. rewrite elem_of_singleton. reflexivity.
              ** exact Hd.
    + intros m σt H. destruct σt as [ρ0|ρ1 ρ2|ρ1 ρ2|bs Δ δ ρs ρf]; cbn [tsubst_typat fv_typat typat_size] in *.
      * apply (IHt m ρ0); lia.
      * rewrite union_subseteq. split.
        -- transitivity ((fv_typ ρ1 ∖ dom m) ∪ mvalues m). ++ apply (IHt m ρ1); lia. ++ set_solver.
        -- transitivity ((fv_typ ρ2 ∖ dom m) ∪ mvalues m). ++ apply (IHt m ρ2); lia. ++ set_solver.
      * rewrite union_subseteq. split.
        -- transitivity ((fv_typ ρ1 ∖ dom m) ∪ mvalues m). ++ apply (IHt m ρ1); lia. ++ set_solver.
        -- transitivity ((fv_typ ρ2 ∖ dom m) ∪ mvalues m). ++ apply (IHt m ρ2); lia. ++ set_solver.
      * assert (Hmv0 : mvalues (bdeletes bs m) ⊆ mvalues m) by apply mvalues_bdeletes.
        apply elem_of_subseteq in Hmv0.
        assert (Hfind : ({[find_opt (bdeletes bs m) δ]} : gset string) ⊆
          ((({[δ]} ∪ fv_constraints Δ ∪ fv_typ ρf ∪ ⋃ (fv_typ <$> ρs)) ∖ binders_set bs) ∖ dom m) ∪ mvalues m ∪ binders_set bs).
        { apply elem_of_subseteq. intros z Hz. rewrite elem_of_singleton in Hz. subst z.
          destruct (decide (δ ∈ dom m)) as [Hd|Hd].
          - destruct (decide (δ ∈ dom (bdeletes bs m))) as [Hd'|Hnd'].
            + rewrite elem_of_union. left. rewrite elem_of_union. right. apply Hmv0. apply find_opt_dom. exact Hd'.
            + rewrite (find_opt_ndom (bdeletes bs m) δ Hnd'). rewrite elem_of_union. right. apply (elem_of_dom_bdeletes bs m δ); [exact Hd|exact Hnd'].
          - assert (Hnd' : δ ∉ dom (bdeletes bs m)).
            { intro Hin. apply Hd. apply (dom_bdeletes_subseteq bs m). exact Hin. }
            rewrite (find_opt_ndom (bdeletes bs m) δ Hnd').
            destruct (decide (δ ∈ binders_set bs)) as [Hb|Hb].
            + rewrite elem_of_union. right. exact Hb.
            + rewrite elem_of_union. left. rewrite elem_of_union. left.
              rewrite elem_of_difference. split.
              * rewrite elem_of_difference. split; [set_solver|exact Hb].
              * exact Hd. }
        apply elem_of_subseteq in Hfind.
        assert (Hfc : fv_constraints (tsubst_constraints (bdeletes bs m) Δ) ⊆
          ((({[δ]} ∪ fv_constraints Δ ∪ fv_typ ρf ∪ ⋃ (fv_typ <$> ρs)) ∖ binders_set bs) ∖ dom m) ∪ mvalues m ∪ binders_set bs).
        { apply elem_of_subseteq. intros z Hz.
          assert (Hsub := fv_constraints_tsubst_sharp (bdeletes bs m) Δ). apply elem_of_subseteq in Hsub.
          specialize (Hsub z Hz). rewrite elem_of_union in Hsub. destruct Hsub as [Hsub|Hsub].
          - rewrite elem_of_difference in Hsub. destruct Hsub as [Hsub Hnd'].
            destruct (decide (z ∈ binders_set bs)) as [Hb|Hb].
            + rewrite elem_of_union. right. exact Hb.
            + rewrite elem_of_union. left. rewrite elem_of_union. left.
              rewrite elem_of_difference. split.
              * rewrite elem_of_difference. split; [set_solver|exact Hb].
              * intro Hdom. apply Hb. eapply (elem_of_dom_bdeletes bs m z); eauto.
          - rewrite elem_of_union. left. rewrite elem_of_union. right. apply Hmv0. exact Hsub. }
        apply elem_of_subseteq in Hfc.
        assert (Hf : fv_typ (tsubst_typ (bdeletes bs m) ρf) ⊆
          ((({[δ]} ∪ fv_constraints Δ ∪ fv_typ ρf ∪ ⋃ (fv_typ <$> ρs)) ∖ binders_set bs) ∖ dom m) ∪ mvalues m ∪ binders_set bs).
        { apply elem_of_subseteq. intros z Hz.
          assert (Hsub := IHt (bdeletes bs m) ρf ltac:(lia)). apply elem_of_subseteq in Hsub.
          specialize (Hsub z Hz). rewrite elem_of_union in Hsub. destruct Hsub as [Hsub|Hsub].
          - rewrite elem_of_difference in Hsub. destruct Hsub as [Hsub Hnd'].
            destruct (decide (z ∈ binders_set bs)) as [Hb|Hb].
            + rewrite elem_of_union. right. exact Hb.
            + rewrite elem_of_union. left. rewrite elem_of_union. left.
              rewrite elem_of_difference. split.
              * rewrite elem_of_difference. split; [set_solver|exact Hb].
              * intro Hdom. apply Hb. eapply (elem_of_dom_bdeletes bs m z); eauto.
          - rewrite elem_of_union. left. rewrite elem_of_union. right. apply Hmv0. exact Hsub. }
        apply elem_of_subseteq in Hf.
        assert (Hl : ⋃ (fv_typ <$> (tsubst_typ (bdeletes bs m) <$> ρs)) ⊆
          ((({[δ]} ∪ fv_constraints Δ ∪ fv_typ ρf ∪ ⋃ (fv_typ <$> ρs)) ∖ binders_set bs) ∖ dom m) ∪ mvalues m ∪ binders_set bs).
        { apply elem_of_subseteq. intros z Hz.
          assert (Hsub := IHl (bdeletes bs m) ρs ltac:(pose proof (pos_typ_size ρf); lia)). apply elem_of_subseteq in Hsub.
          specialize (Hsub z Hz). rewrite elem_of_union in Hsub. destruct Hsub as [Hsub|Hsub].
          - rewrite elem_of_difference in Hsub. destruct Hsub as [Hsub Hnd'].
            destruct (decide (z ∈ binders_set bs)) as [Hb|Hb].
            + rewrite elem_of_union. right. exact Hb.
            + rewrite elem_of_union. left. rewrite elem_of_union. left.
              rewrite elem_of_difference. split.
              * rewrite elem_of_difference. split; [set_solver|exact Hb].
              * intro Hdom. apply Hb. eapply (elem_of_dom_bdeletes bs m z); eauto.
          - rewrite elem_of_union. left. rewrite elem_of_union. right. apply Hmv0. exact Hsub. }
        apply elem_of_subseteq in Hl.
        assert (HbaseA : ({[find_opt (bdeletes bs m) δ]} ∪ fv_constraints (tsubst_constraints (bdeletes bs m) Δ) ∪ fv_typ (tsubst_typ (bdeletes bs m) ρf) ∪ ⋃ (fv_typ <$> (tsubst_typ (bdeletes bs m) <$> ρs)))
          ⊆ ((({[δ]} ∪ fv_constraints Δ ∪ fv_typ ρf ∪ ⋃ (fv_typ <$> ρs)) ∖ binders_set bs) ∖ dom m) ∪ mvalues m ∪ binders_set bs).
        { rewrite !union_subseteq. repeat split; assumption. }
        apply elem_of_subseteq in HbaseA.
        apply elem_of_subseteq. intros z Hz.
        rewrite elem_of_difference in Hz. destruct Hz as [Hz HnB].
        specialize (HbaseA z Hz).
        rewrite elem_of_union. rewrite elem_of_union in HbaseA. destruct HbaseA as [HbaseA|HbaseA].
        -- rewrite elem_of_union in HbaseA. destruct HbaseA as [HbaseA|HbaseA].
           ++ left. exact HbaseA.
           ++ right. exact HbaseA.
        -- exfalso. apply HnB. exact HbaseA.
    + intros m ts H. destruct ts as [|t ts']; cbn [tsubst_typ fv_typ list_sum list_fmap] in *.
      * set_solver.
      * simpl in H. simpl. rewrite union_subseteq. split.
        -- transitivity ((fv_typ t ∖ dom m) ∪ mvalues m). ++ apply (IHt m t); lia. ++ set_solver.
        -- apply elem_of_subseteq. intros z Hz.
           assert (Hs : S (list_sum (list_fmap typ nat typ_size ts')) <= fuel) by (pose proof (pos_typ_size t); lia).
           assert (Hsub : ⋃ (fv_typ <$> (tsubst_typ m <$> ts')) ⊆ (⋃ (fv_typ <$> ts') ∖ dom m) ∪ mvalues m) by (apply (IHl m ts'); exact Hs).
           apply elem_of_subseteq in Hsub. specialize (Hsub z Hz).
           rewrite elem_of_union in Hsub. destruct Hsub as [Hsub|Hsub].
           ++ rewrite elem_of_union. left. rewrite elem_of_difference in Hsub. destruct Hsub as [H1 H2].
              rewrite elem_of_difference. split; [set_solver|exact H2].
           ++ rewrite elem_of_union. right. exact Hsub.
Qed.

Lemma fvv_tsubst_eq : forall fuel,
  (forall (m:gmap string string) ρ, typ_size ρ <= fuel ->
     fvv_typ (tsubst_typ m ρ) = fvv_typ ρ)
  /\ (forall (m:gmap string string) σt, typat_size σt <= fuel ->
     fvv_typat (tsubst_typat m σt) = fvv_typat σt)
  /\ (forall (m:gmap string string) ts, S (list_sum (typ_size <$> ts)) <= fuel ->
     ⋃ (fvv_typ <$> (tsubst_typ m <$> ts)) = ⋃ (fvv_typ <$> ts)).
Proof.
  induction fuel as [|fuel IH].
  - split; [|split].
    + intros m ρ H. exfalso. pose proof (pos_typ_size ρ). lia.
    + intros m σt H. exfalso. pose proof (pos_typat_size σt). lia.
    + intros m ts H. exfalso. lia.
  - destruct IH as (IHt & IHty & IHl). split; [|split].
    + intros m ρ H. destruct ρ as [y|b|σt δ|y ρ0|ρ0 δ|y k ρ0|y σt δ]; cbn [tsubst_typ fvv_typ typ_size] in *.
      * reflexivity.
      * reflexivity.
      * apply IHty; lia.
      * apply IHt; lia.
      * apply IHt; lia.
      * rewrite (IHt m ρ0 ltac:(lia)). reflexivity.
      * rewrite (IHty m σt ltac:(lia)). set_solver.
    + intros m σt H. destruct σt as [ρ0|ρ1 ρ2|ρ1 ρ2|bs Δ δ ρs ρf]; cbn [tsubst_typat fvv_typat typat_size] in *.
      * apply IHt; lia.
      * rewrite !(IHt m ρ1 ltac:(lia)), !(IHt m ρ2 ltac:(lia)). reflexivity.
      * rewrite !(IHt m ρ1 ltac:(lia)), !(IHt m ρ2 ltac:(lia)). reflexivity.
      * rewrite (IHt (bdeletes bs m) ρf ltac:(lia)).
        rewrite (IHl (bdeletes bs m) ρs ltac:(pose proof (pos_typ_size ρf); lia)). reflexivity.
    + intros m ts H. destruct ts as [|t ts']; cbn [tsubst_typ fvv_typ list_sum list_fmap] in *.
      * reflexivity.
      * simpl in H. simpl.
        rewrite (IHt m t ltac:(lia)).
        assert (Hs : S (list_sum (list_fmap typ nat typ_size ts')) <= fuel) by (pose proof (pos_typ_size t); lia).
        f_equal. apply (IHl m ts' Hs).
Qed.

Lemma fv_tsubst_all : forall fuel,
  (forall (m:gmap string string) ρ, typ_size ρ <= fuel ->
     fv_typ (tsubst_typ m ρ) ⊆ fv_typ ρ ∪ mvalues m)
  /\ (forall (m:gmap string string) σt, typat_size σt <= fuel ->
     fv_typat (tsubst_typat m σt) ⊆ fv_typat σt ∪ mvalues m)
  /\ (forall (m:gmap string string) ts, S (list_sum (typ_size <$> ts)) <= fuel ->
     ⋃ (fv_typ <$> (tsubst_typ m <$> ts)) ⊆ ⋃ (fv_typ <$> ts) ∪ mvalues m).
Proof.
  induction fuel as [|fuel IH].
  - split; [|split].
    + intros m ρ H. exfalso. pose proof (pos_typ_size ρ). lia.
    + intros m σt H. exfalso. pose proof (pos_typat_size σt). lia.
    + intros m ts H. exfalso. lia.
  - destruct IH as (IHt & IHty & IHl). split; [|split].
    + intros m ρ H. destruct ρ as [y|b|σt δ|y ρ0|ρ0 δ|y k ρ0|y σt δ]; cbn [tsubst_typ fv_typ typ_size] in *.
      * set_solver.
      * set_solver.
      * assert (Hsub := IHty m σt ltac:(lia)). apply elem_of_subseteq in Hsub.
        apply elem_of_subseteq. intros z Hz.
        rewrite elem_of_union in Hz. destruct Hz as [Hz|Hz].
        -- assert (Hz2 : z ∈ fv_typat σt ∪ mvalues m) by (apply Hsub; exact Hz). set_solver.
        -- destruct (find_opt_mem m δ) as [He|Hm].
           ++ rewrite He in Hz. set_solver.
           ++ set_solver.
      * assert (Hsub := IHt (bdelete y m) ρ0 ltac:(lia)). apply elem_of_subseteq in Hsub.
        assert (Hmv : mvalues (bdelete y m) ⊆ mvalues m).
        { change (mvalues (bdeletes [y] m) ⊆ mvalues m). apply mvalues_bdeletes. }
        apply elem_of_subseteq in Hmv.
        apply elem_of_subseteq. intros z Hz.
        rewrite elem_of_difference in Hz. destruct Hz as [Hz Hnb].
        assert (Hz2 := Hsub z Hz).
        assert (Hz3 : z ∈ fv_typ ρ0 ∪ mvalues m).
        { rewrite elem_of_union in Hz2. destruct Hz2 as [H1|H2].
          - rewrite elem_of_union. left. exact H1.
          - rewrite elem_of_union. right. apply Hmv. exact H2. }
        set_solver.
      * assert (Hsub := IHt m ρ0 ltac:(lia)). apply elem_of_subseteq in Hsub.
        apply elem_of_subseteq. intros z Hz.
        rewrite elem_of_union in Hz. destruct Hz as [Hz|Hz].
        -- assert (Hz2 : z ∈ fv_typ ρ0 ∪ mvalues m) by (apply Hsub; exact Hz). set_solver.
        -- destruct (find_opt_mem m δ) as [He|Hm].
           ++ rewrite He in Hz. set_solver.
           ++ set_solver.
      * apply (IHt m ρ0); lia.
      * assert (Hsub := IHty m σt ltac:(lia)). apply elem_of_subseteq in Hsub.
        apply elem_of_subseteq. intros z Hz.
        rewrite elem_of_union in Hz. destruct Hz as [Hz|Hz].
        -- assert (Hz2 : z ∈ fv_typat σt ∪ mvalues m) by (apply Hsub; exact Hz). set_solver.
        -- destruct (find_opt_mem m δ) as [He|Hm].
           ++ rewrite He in Hz. set_solver.
           ++ set_solver.
    + intros m σt H. destruct σt as [ρ0|ρ1 ρ2|ρ1 ρ2|bs Δ δ ρs ρf]; cbn [tsubst_typat fv_typat typat_size] in *.
      * apply (IHt m ρ0); lia.
      * rewrite union_subseteq. split.
        -- transitivity (fv_typ ρ1 ∪ mvalues m). ++ apply (IHt m ρ1); lia. ++ set_solver.
        -- transitivity (fv_typ ρ2 ∪ mvalues m). ++ apply (IHt m ρ2); lia. ++ set_solver.
      * rewrite union_subseteq. split.
        -- transitivity (fv_typ ρ1 ∪ mvalues m). ++ apply (IHt m ρ1); lia. ++ set_solver.
        -- transitivity (fv_typ ρ2 ∪ mvalues m). ++ apply (IHt m ρ2); lia. ++ set_solver.
      * assert (Hmv : mvalues (bdeletes bs m) ⊆ mvalues m) by apply mvalues_bdeletes.
        apply elem_of_subseteq in Hmv.
        assert (Hfind : ({[find_opt (bdeletes bs m) δ]} : gset string)
                        ⊆ ({[δ]} ∪ fv_constraints Δ ∪ fv_typ ρf ∪ ⋃ (fv_typ <$> ρs)) ∪ mvalues m).
        { apply elem_of_subseteq. intros z Hz. rewrite elem_of_singleton in Hz. subst z.
          destruct (find_opt_mem (bdeletes bs m) δ) as [He|Hm].
          - rewrite elem_of_union. left. rewrite He. set_solver.
          - rewrite elem_of_union. right. apply Hmv; exact Hm. }
        apply elem_of_subseteq in Hfind.
        assert (Hfc : fv_constraints (tsubst_constraints (bdeletes bs m) Δ)
                      ⊆ ({[δ]} ∪ fv_constraints Δ ∪ fv_typ ρf ∪ ⋃ (fv_typ <$> ρs)) ∪ mvalues m).
        { transitivity (fv_constraints Δ ∪ mvalues (bdeletes bs m)).
          - apply fv_constraints_tsubst.
          - apply elem_of_subseteq. intros z Hz. rewrite elem_of_union in Hz. destruct Hz as [Hz|Hz].
            + rewrite elem_of_union. left. set_solver.
            + rewrite elem_of_union. right. apply Hmv; exact Hz. }
        apply elem_of_subseteq in Hfc.
        assert (Hf : fv_typ (tsubst_typ (bdeletes bs m) ρf)
                     ⊆ ({[δ]} ∪ fv_constraints Δ ∪ fv_typ ρf ∪ ⋃ (fv_typ <$> ρs)) ∪ mvalues m).
        { transitivity (fv_typ ρf ∪ mvalues (bdeletes bs m)).
          - apply (IHt (bdeletes bs m) ρf); lia.
          - apply elem_of_subseteq. intros z Hz. rewrite elem_of_union in Hz. destruct Hz as [Hz|Hz].
            + rewrite elem_of_union. left. set_solver.
            + rewrite elem_of_union. right. apply Hmv; exact Hz. }
        apply elem_of_subseteq in Hf.
        assert (Hl : ⋃ (fv_typ <$> (tsubst_typ (bdeletes bs m) <$> ρs))
                     ⊆ ({[δ]} ∪ fv_constraints Δ ∪ fv_typ ρf ∪ ⋃ (fv_typ <$> ρs)) ∪ mvalues m).
        { transitivity (⋃ (fv_typ <$> ρs) ∪ mvalues (bdeletes bs m)).
          - apply (IHl (bdeletes bs m) ρs); pose proof (pos_typ_size ρf); lia.
          - apply elem_of_subseteq. intros z Hz. rewrite elem_of_union in Hz. destruct Hz as [Hz|Hz].
            + rewrite elem_of_union. left. set_solver.
            + rewrite elem_of_union. right. apply Hmv; exact Hz. }
        apply elem_of_subseteq in Hl.
        apply elem_of_subseteq. intros z Hz.
        rewrite elem_of_difference in Hz. destruct Hz as [Hz Hnb].
        assert (Hzbase : z ∈ ({[δ]} ∪ fv_constraints Δ ∪ fv_typ ρf ∪ ⋃ (fv_typ <$> ρs)) ∪ mvalues m).
        { rewrite elem_of_union in Hz. destruct Hz as [Hz|Hz].
          - rewrite elem_of_union in Hz. destruct Hz as [Hz|Hz].
            + rewrite elem_of_union in Hz. destruct Hz as [Hz|Hz].
              * apply Hfind. exact Hz.
              * apply Hfc. exact Hz.
            + apply Hf. exact Hz.
          - apply Hl. exact Hz. }
        rewrite elem_of_union. rewrite elem_of_union in Hzbase. destruct Hzbase as [Hzbase|Hzbase].
        -- left. rewrite elem_of_difference. split; [exact Hzbase|exact Hnb].
        -- right. exact Hzbase.
    + intros m ts H. destruct ts as [|t ts']; cbn [tsubst_typ fv_typ list_sum list_fmap] in *.
      * set_solver.
      * simpl in H. simpl. rewrite union_subseteq. split.
        -- transitivity (fv_typ t ∪ mvalues m). ++ apply (IHt m t); lia. ++ set_solver.
        -- apply elem_of_subseteq. intros z Hz.
           assert (Hs : S (list_sum (list_fmap typ nat typ_size ts')) <= fuel) by (pose proof (pos_typ_size t); lia).
           assert (Hsub : ⋃ (fv_typ <$> (tsubst_typ m <$> ts')) ⊆ ⋃ (fv_typ <$> ts') ∪ mvalues m) by (apply (IHl m ts'); exact Hs).
           apply elem_of_subseteq in Hsub. specialize (Hsub z Hz). set_solver.
Qed.

Lemma mvalues_singleton : forall (x v:string),
  mvalues ({[x:=v]} : gmap string string) ⊆ ({[v]} : gset string).
Proof.
  intros. unfold mvalues. etransitivity.
  - apply map_img_insert_subseteq.
  - rewrite map_img_empty. set_solver.
Qed.

Lemma semroot_tupd_irrel : forall m τ (y:string) t ρ,
  y ∉ fv_typ ρ -> semroot m (tupd τ (BNamed y) t) ρ = semroot m τ ρ.
Proof.
  induction m as [|m IH]; intros τ y t ρ Hy.
  - reflexivity.
  - destruct ρ as [z|b|σt δ|bd ρ0|ρ0 δ|x k ρ0|x σt δ]; simpl in *.
    + reflexivity.
    + destruct b; reflexivity.
    + assert (Hne : y ≠ δ) by (intro e; subst δ; apply Hy; set_solver).
      rewrite (tget_insert_ne τ y δ t Hne). reflexivity.
    + reflexivity.
    + destruct ρ0 as [z|b|σt' δ'|bd ρ0'|ρ0' δ'|x k ρ0'|x σt' δ']; simpl; try reflexivity.
      destruct bd as [|x]; simpl; [reflexivity|].
      apply IH. simpl in Hy.
      assert (Hsub := proj1 (fv_tsubst_all_sharp (typ_size ρ0')) ({[x:=δ]} : gmap string string) ρ0' ltac:(lia)).
      apply elem_of_subseteq in Hsub.
      assert (Hdom : (dom ({[x:=δ]} : gmap string string)) ≡ ({[x]} : gset string)) by apply dom_singleton.
      assert (Hmv := mvalues_singleton x δ). apply elem_of_subseteq in Hmv.
      intro Hmem. specialize (Hsub y Hmem). rewrite elem_of_union in Hsub. destruct Hsub as [Hsub|Hsub].
      * rewrite elem_of_difference in Hsub. destruct Hsub as [Hf Hnd].
        rewrite Hdom in Hnd.
        exfalso. apply Hy. rewrite elem_of_union. left. rewrite elem_of_difference. split; assumption.
      * exfalso. apply Hy. rewrite elem_of_union. right. apply Hmv. exact Hsub.
    + reflexivity.
    + assert (Hne : y ≠ δ) by (intro e; subst δ; apply Hy; set_solver).
      rewrite (tget_insert_ne τ y δ t Hne). reflexivity.
Qed.

Lemma root_reaches_tupd_irrel : forall W τ (y:string) t ρ δ,
  y ∉ fv_typ ρ ->
  (root_reaches W (tupd τ (BNamed y) t) ρ δ <-> root_reaches W τ ρ δ).
Proof.
  intros W τ y t ρ δ Hy. unfold root_reaches. split; intros H m r Hs.
  - apply (H m r). rewrite (semroot_tupd_irrel m τ y t ρ Hy). exact Hs.
  - apply (H m r). rewrite <- (semroot_tupd_irrel m τ y t ρ Hy). exact Hs.
Qed.

Lemma interp_tupd_irrel : forall n ξ τ (y:string) t ρ ts W v,
  y ∉ fv_typ ρ ->
  (interp n ξ (tupd τ (BNamed y) t) ρ ts W v <-> interp n ξ τ ρ ts W v).
Proof.
  intros n. induction n as [|n IH]; intros ξ τ y t ρ ts W v Hy.
  - simpl. tauto.
  - destruct ρ as [z|b|σt δ|bd ρ0|ρ0 δ|x k ρ0|x σt δ]; simpl in *.
    + tauto.
    + destruct b; simpl; tauto.
    + destruct σt as [ρ0|ρ1 ρ2|ρ1 ρ2|bs Δ δs ρs ρf]; simpl in *.
      * assert (Hne : y ≠ δ) by (intro e; subst δ; apply Hy; set_solver).
        rewrite (tget_insert_ne τ y δ t Hne).
        split.
        -- intros (l & bl & He & Hs & Hab & Hbs & Hr). exists l, bl.
           split; [exact He|]. split; [exact Hs|]. split; [exact Hab|]. split.
           ++ intros b Hb. apply (proj1 (IH ξ τ y t ρ0 [] W b ltac:(set_solver))). apply Hbs; auto.
           ++ apply (proj1 (root_reaches_tupd_irrel W τ y t ρ0 (tget τ δ) ltac:(set_solver))); exact Hr.
        -- intros (l & bl & He & Hs & Hab & Hbs & Hr). exists l, bl.
           split; [exact He|]. split; [exact Hs|]. split; [exact Hab|]. split.
           ++ intros b Hb. apply (proj2 (IH ξ τ y t ρ0 [] W b ltac:(set_solver))). apply Hbs; auto.
           ++ apply (proj2 (root_reaches_tupd_irrel W τ y t ρ0 (tget τ δ) ltac:(set_solver))); exact Hr.
      * assert (Hne : y ≠ δ) by (intro e; subst δ; apply Hy; set_solver).
        rewrite (tget_insert_ne τ y δ t Hne).
        split.
        -- intros (l & v1 & v2 & He & Hs & Hab & H1 & H2). exists l, v1, v2.
           split; [exact He|]. split; [exact Hs|]. split; [exact Hab|]. split.
           ++ apply (proj1 (IH ξ τ y t ρ1 [] W v1 ltac:(set_solver))). exact H1.
           ++ apply (proj1 (IH ξ τ y t ρ2 [] W v2 ltac:(set_solver))). exact H2.
        -- intros (l & v1 & v2 & He & Hs & Hab & H1 & H2). exists l, v1, v2.
           split; [exact He|]. split; [exact Hs|]. split; [exact Hab|]. split.
           ++ apply (proj2 (IH ξ τ y t ρ1 [] W v1 ltac:(set_solver))). exact H1.
           ++ apply (proj2 (IH ξ τ y t ρ2 [] W v2 ltac:(set_solver))). exact H2.
      * assert (Hne : y ≠ δ) by (intro e; subst δ; apply Hy; set_solver).
        rewrite (tget_insert_ne τ y δ t Hne).
        split.
        -- intros [(l & v1 & He & Hs & Hab & H1)|(l & v2 & He & Hs & Hab & H2)].
           ++ left; exists l, v1; split; [exact He|]; split; [exact Hs|]; split; [exact Hab|].
              apply (proj1 (IH ξ τ y t ρ1 [] W v1 ltac:(set_solver))); exact H1.
           ++ right; exists l, v2; split; [exact He|]; split; [exact Hs|]; split; [exact Hab|].
              apply (proj1 (IH ξ τ y t ρ2 [] W v2 ltac:(set_solver))); exact H2.
        -- intros [(l & v1 & He & Hs & Hab & H1)|(l & v2 & He & Hs & Hab & H2)].
           ++ left; exists l, v1; split; [exact He|]; split; [exact Hs|]; split; [exact Hab|].
              apply (proj2 (IH ξ τ y t ρ1 [] W v1 ltac:(set_solver))); exact H1.
           ++ right; exists l, v2; split; [exact He|]; split; [exact Hs|]; split; [exact Hab|].
              apply (proj2 (IH ξ τ y t ρ2 [] W v2 ltac:(set_solver))); exact H2.
      * assert (Hne : y ≠ δ) by (intro e; subst δ; apply Hy; set_solver).
        rewrite (tget_insert_ne τ y δ t Hne). tauto.
    + destruct ts as [|t0 ts']; simpl; [tauto|].
      destruct bd as [|z]; simpl in *.
      * apply (IH ξ τ y t ρ0 ts' W v). set_solver.
      * destruct (decide (y = z)) as [e|ne].
        -- subst z. rewrite (insert_insert_eq τ y t0 t). tauto.
        -- assert (Hcomm := insert_insert_ne τ z y t0 t
                          ltac:(intro e; apply ne; symmetry; exact e)).
           rewrite (insert_insert_ne τ z y t0 t) by (intro e; apply ne; symmetry; exact e).
           apply (IH ξ (tupd τ (BNamed z) t0) y t ρ0 ts' W v). set_solver.
    + assert (Hne : y ≠ δ) by (intro e; subst δ; apply Hy; set_solver).
      rewrite (tget_insert_ne τ y δ t Hne).
      apply (IH ξ τ y t ρ0 (tget τ δ :: ts) W v). set_solver.
    + split.
      * intros H S'. apply (proj1 (IH (bupdS ξ x S') τ y t ρ0 [] W v ltac:(set_solver))). apply (H S').
      * intros H S'. apply (proj2 (IH (bupdS ξ x S') τ y t ρ0 [] W v ltac:(set_solver))). apply (H S').
    + split.
      * intros (v' & He & Hv). exists v'. split; [exact He|].
        assert (Hhyg : y ∉ fv_typ (TTypat (vsubst_typat x (TRec x σt δ) σt) δ)).
        { assert (Hsub := proj1 (proj2 (fv_subst_all (typat_size σt))) x (TRec x σt δ) σt ltac:(lia)).
          simpl in Hsub. intro Hmem. apply elem_of_subseteq in Hsub.
          cbn [fv_typ] in Hmem. rewrite elem_of_union in Hmem. destruct Hmem as [Hmem|Hmem].
          - specialize (Hsub y Hmem). simpl in Hy. set_solver.
          - simpl in Hy. set_solver. }
        apply (proj1 (IH ξ τ y t (TTypat (vsubst_typat x (TRec x σt δ) σt) δ) [] W v' Hhyg)).
        exact Hv.
      * intros (v' & He & Hv). exists v'. split; [exact He|].
        assert (Hhyg : y ∉ fv_typ (TTypat (vsubst_typat x (TRec x σt δ) σt) δ)).
        { assert (Hsub := proj1 (proj2 (fv_subst_all (typat_size σt))) x (TRec x σt δ) σt ltac:(lia)).
          simpl in Hsub. intro Hmem. apply elem_of_subseteq in Hsub.
          cbn [fv_typ] in Hmem. rewrite elem_of_union in Hmem. destruct Hmem as [Hmem|Hmem].
          - specialize (Hsub y Hmem). simpl in Hy. set_solver.
          - simpl in Hy. set_solver. }
        apply (proj2 (IH ξ τ y t (TTypat (vsubst_typat x (TRec x σt δ) σt) δ) [] W v' Hhyg)).
        exact Hv.
Qed.

Lemma bupdS_none_agree : forall (ξ1 ξ2:valenv) (x:binder) S,
  (forall y, ξ1 !! y = None <-> ξ2 !! y = None) ->
  forall y, (bupdS ξ1 x S) !! y = None <-> (bupdS ξ2 x S) !! y = None.
Proof.
  intros ξ1 ξ2 [|z] S H y; simpl.
  - apply H.
  - change ((<[z:=S]> ξ1) !! y = None <-> (<[z:=S]> ξ2) !! y = None).
    rewrite (lookup_insert_None ξ1 z y S). rewrite (lookup_insert_None ξ2 z y S).
    split; intros (Hn & Hne); split.
    + exact (proj1 (H y) Hn).
    + exact Hne.
    + exact (proj2 (H y) Hn).
    + exact Hne.
Qed.

Lemma bupdS_some_agree : forall (ξ1 ξ2:valenv) (x:binder) S,
  (forall y S1 S2, ξ1 !! y = Some S1 -> ξ2 !! y = Some S2 ->
     forall m ts W v, S1 m ts W v <-> S2 m ts W v) ->
  forall y S1 S2, (bupdS ξ1 x S) !! y = Some S1 -> (bupdS ξ2 x S) !! y = Some S2 ->
     forall m ts W v, S1 m ts W v <-> S2 m ts W v.
Proof.
  intros ξ1 ξ2 [|z] S H y S1v S2v E1 E2; simpl in *.
  - eapply H; eauto.
  - change ((<[z:=S]> ξ1) !! y = Some S1v) in E1.
    change ((<[z:=S]> ξ2) !! y = Some S2v) in E2.
    rewrite (lookup_insert_Some ξ1 z y S S1v) in E1.
    rewrite (lookup_insert_Some ξ2 z y S S2v) in E2.
    destruct (decide (z = y)) as [e|n].
    + destruct E1 as [[_ h1]|[n1 _]]; [|exfalso; apply n1; exact e].
      destruct E2 as [[_ h2]|[n2 _]]; [|exfalso; apply n2; exact e].
      subst S1v. subst S2v. tauto.
    + destruct E1 as [[e1 _]|[_ h1]]; [exfalso; apply n; exact e1|].
      destruct E2 as [[e2 _]|[_ h2]]; [exfalso; apply n; exact e2|].
      eapply H; eauto.
Qed.

Lemma interp_agree : forall n ξ1 ξ2 τ ρ ts W v,
  (forall y, ξ1 !! y = None <-> ξ2 !! y = None) ->
  (forall y S1 S2, ξ1 !! y = Some S1 -> ξ2 !! y = Some S2 ->
     forall m ts W v, S1 m ts W v <-> S2 m ts W v) ->
  (interp n ξ1 τ ρ ts W v <-> interp n ξ2 τ ρ ts W v).
Proof.
  intros n. induction n as [|n IH]; intros ξ1 ξ2 τ ρ ts W v Hnone Hsome.
  - simpl. tauto.
  - destruct ρ as [z|b|σt δ|bd ρ0|ρ0 δ|x k ρ0|x σt δ]; simpl in *.
    + unfold vget. destruct (ξ1 !! z) as [S1|] eqn:E1; destruct (ξ2 !! z) as [S2|] eqn:E2.
      * apply (Hsome z S1 S2 E1 E2).
      * exfalso. pose proof (proj2 (Hnone z) E2) as Hn.
        assert (Hbad : Some S1 = None) by (rewrite <- E1; exact Hn). discriminate Hbad.
      * exfalso. pose proof (proj1 (Hnone z) E1) as Hn.
        assert (Hbad : Some S2 = None) by (rewrite <- E2; exact Hn). discriminate Hbad.
      * tauto.
    + destruct b; simpl; tauto.
    + destruct σt as [ρ0|ρ1 ρ2|ρ1 ρ2|bs Δ δs ρs ρf]; simpl in *.
      * split.
        -- intros (l & bl & He & Hs & Hab & Hbs & Hr). exists l, bl.
           split; [exact He|]. split; [exact Hs|]. split; [exact Hab|]. split.
           ++ intros b Hb. apply (proj1 (IH ξ1 ξ2 τ ρ0 [] W b Hnone Hsome)). apply Hbs; auto.
           ++ exact Hr.
        -- intros (l & bl & He & Hs & Hab & Hbs & Hr). exists l, bl.
           split; [exact He|]. split; [exact Hs|]. split; [exact Hab|]. split.
           ++ intros b Hb. apply (proj2 (IH ξ1 ξ2 τ ρ0 [] W b Hnone Hsome)). apply Hbs; auto.
           ++ exact Hr.
      * split.
        -- intros (l & v1 & v2 & He & Hs & Hab & H1 & H2). exists l, v1, v2.
           split; [exact He|]. split; [exact Hs|]. split; [exact Hab|]. split.
           ++ apply (proj1 (IH ξ1 ξ2 τ ρ1 [] W v1 Hnone Hsome)). exact H1.
           ++ apply (proj1 (IH ξ1 ξ2 τ ρ2 [] W v2 Hnone Hsome)). exact H2.
        -- intros (l & v1 & v2 & He & Hs & Hab & H1 & H2). exists l, v1, v2.
           split; [exact He|]. split; [exact Hs|]. split; [exact Hab|]. split.
           ++ apply (proj2 (IH ξ1 ξ2 τ ρ1 [] W v1 Hnone Hsome)). exact H1.
           ++ apply (proj2 (IH ξ1 ξ2 τ ρ2 [] W v2 Hnone Hsome)). exact H2.
      * split.
        -- intros [(l & v1 & He & Hs & Hab & H1)|(l & v2 & He & Hs & Hab & H2)].
           ++ left; exists l, v1; split; [exact He|]; split; [exact Hs|]; split; [exact Hab|].
              apply (proj1 (IH ξ1 ξ2 τ ρ1 [] W v1 Hnone Hsome)); exact H1.
           ++ right; exists l, v2; split; [exact He|]; split; [exact Hs|]; split; [exact Hab|].
              apply (proj1 (IH ξ1 ξ2 τ ρ2 [] W v2 Hnone Hsome)); exact H2.
        -- intros [(l & v1 & He & Hs & Hab & H1)|(l & v2 & He & Hs & Hab & H2)].
           ++ left; exists l, v1; split; [exact He|]; split; [exact Hs|]; split; [exact Hab|].
              apply (proj2 (IH ξ1 ξ2 τ ρ1 [] W v1 Hnone Hsome)); exact H1.
           ++ right; exists l, v2; split; [exact He|]; split; [exact Hs|]; split; [exact Hab|].
              apply (proj2 (IH ξ1 ξ2 τ ρ2 [] W v2 Hnone Hsome)); exact H2.
      * simpl. tauto.
    + destruct ts as [|t0 ts']; simpl; [tauto|].
      apply (IH ξ1 ξ2 (tupd τ bd t0) ρ0 ts' W v Hnone Hsome).
    + apply (IH ξ1 ξ2 τ ρ0 (tget τ δ :: ts) W v Hnone Hsome).
    + split.
      * intros H S'. apply (proj1 (IH (bupdS ξ1 x S') (bupdS ξ2 x S') τ ρ0 [] W v
          (bupdS_none_agree ξ1 ξ2 x S' Hnone)
          (bupdS_some_agree ξ1 ξ2 x S' Hsome))). apply (H S').
      * intros H S'. apply (proj2 (IH (bupdS ξ1 x S') (bupdS ξ2 x S') τ ρ0 [] W v
          (bupdS_none_agree ξ1 ξ2 x S' Hnone)
          (bupdS_some_agree ξ1 ξ2 x S' Hsome))). apply (H S').
    + split.
      * intros (v' & He & Hv). exists v'. split; [exact He|].
        apply (proj1 (IH ξ1 ξ2 τ (TTypat (vsubst_typat x (TRec x σt δ) σt) δ) [] W v' Hnone Hsome)).
        exact Hv.
      * intros (v' & He & Hv). exists v'. split; [exact He|].
        apply (proj2 (IH ξ1 ξ2 τ (TTypat (vsubst_typat x (TRec x σt δ) σt) δ) [] W v' Hnone Hsome)).
        exact Hv.
Qed.

Fixpoint wk_typs (Ω:kinds) (ts:list typ) : Prop :=
  match ts with
  | nil => True
  | ρ :: ρs => wk_typ Ω ρ 0 /\ wk_typs Ω ρs
  end.

Lemma inline_wk_eq : forall Ω ts,
  ((fix f xs := match xs with nil => True | z :: zs => wk_typ Ω z 0 /\ f zs end) ts)
  <-> wk_typs Ω ts.
Proof.
  intros Ω ts. induction ts as [|t ts IH]; simpl.
  - tauto.
  - rewrite IH. tauto.
Qed.

Lemma kinds_insert_subseteq : forall (Ω Ω':kinds) x k, Ω ⊆ Ω' -> <[x:=k]> Ω ⊆ <[x:=k]> Ω'.
Proof.
  intros Ω Ω' x k Hsub. rewrite map_subseteq_spec in *. intros y v Hy.
  destruct (decide (y = x)) as [e|ne].
  - subst y. rewrite lookup_insert_eq in Hy. injection Hy as <-. rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne in Hy by auto. rewrite lookup_insert_ne by auto. apply Hsub; exact Hy.
Qed.
Lemma kinds_binsert_subseteq : forall (Ω Ω':kinds) (b:binder) k, Ω ⊆ Ω' -> binsert b k Ω ⊆ binsert b k Ω'.
Proof. intros Ω Ω' [|x] k Hsub; cbn [binsert]; auto. apply kinds_insert_subseteq; exact Hsub. Qed.
Lemma wk_typ_mono_Ω : forall fuel,
  (forall (Ω Ω':kinds) ρ k, typ_size ρ <= fuel -> Ω ⊆ Ω' -> wk_typ Ω ρ k -> wk_typ Ω' ρ k)
  /\ (forall (Ω Ω':kinds) σt, typat_size σt <= fuel -> Ω ⊆ Ω' -> wk_typat Ω σt -> wk_typat Ω' σt)
  /\ (forall (Ω Ω':kinds) ts, S (list_sum (typ_size <$> ts)) <= fuel -> Ω ⊆ Ω' -> wk_typs Ω ts -> wk_typs Ω' ts).
Proof.
  induction fuel as [|fuel IH].
  - split; [|split].
    + intros Ω Ω' ρ k H. exfalso. pose proof (pos_typ_size ρ). lia.
    + intros Ω Ω' σt H. exfalso. pose proof (pos_typat_size σt). lia.
    + intros Ω Ω' ts H. exfalso. lia.
  - destruct IH as (IHt & IHty & IHl). split; [|split].
    + intros Ω Ω' ρ k H Hsub Hwk.
      destruct ρ as [y|b|σt d|xb ρ0|ρ0 d|x k' ρ0|x σt d]; cbn [wk_typ typ_size] in *.
      * rewrite map_subseteq_spec in Hsub. eapply Hsub; eauto.
      * exact Hwk.
      * destruct Hwk as (Hk & Hw). split; [exact Hk|]. apply (IHty Ω Ω' σt); auto; try lia.
      * destruct k as [|k]; [exact Hwk|]. apply (IHt Ω Ω' ρ0); auto; try lia.
      * apply (IHt Ω Ω' ρ0); auto; try lia.
      * destruct Hwk as (Hk & Hw). split; [exact Hk|].
        exact (IHt (binsert x k' Ω) (binsert x k' Ω') ρ0 0
                 ltac:(lia) ltac:(apply kinds_binsert_subseteq; exact Hsub) Hw).
      * destruct Hwk as (Hk & Hw). split; [exact Hk|].
        exact (IHty (binsert x 0 Ω) (binsert x 0 Ω') σt
                 ltac:(lia) ltac:(apply kinds_binsert_subseteq; exact Hsub) Hw).
    + intros Ω Ω' σt H Hsub Hwk.
      destruct σt as [ρ0|ρ1 ρ2|ρ1 ρ2|bs Δ δ ρs ρf]; cbn [wk_typat typat_size] in *.
      * apply (IHt Ω Ω' ρ0); auto; try lia.
      * destruct Hwk as (H1 & H2). split; [apply (IHt Ω Ω' ρ1); auto; try lia|apply (IHt Ω Ω' ρ2); auto; try lia]; auto.
      * destruct Hwk as (H1 & H2). split; [apply (IHt Ω Ω' ρ1); auto; try lia|apply (IHt Ω Ω' ρ2); auto; try lia]; auto.
      * destruct Hwk as (Hl & Hf).
        rewrite inline_wk_eq in Hl. rewrite inline_wk_eq.
        split.
        -- apply (IHl Ω Ω' ρs).
           ++ pose proof (pos_typ_size ρf). simpl in H.
              change (S (list_sum (list_fmap typ nat typ_size ρs) + typ_size ρf) <= S fuel) in H.
              change (S (list_sum (list_fmap typ nat typ_size ρs)) <= fuel). lia.
           ++ exact Hsub.
           ++ exact Hl.
        -- apply (IHt Ω Ω' ρf).
           ++ pose proof (pos_typ_size ρf). lia.
           ++ exact Hsub.
           ++ exact Hf.
    + intros Ω Ω' ts H Hsub Hwk.
      destruct ts as [|t ts']; cbn [list_sum list_fmap] in *.
      * exact I.
      * simpl in H. destruct Hwk as (H1 & H2). simpl. split.
        -- apply (IHt Ω Ω' t 0); [lia|exact Hsub|exact H1].
        -- apply (IHl Ω Ω' ts'); [pose proof (pos_typ_size t); simpl in H;
              change (S (list_sum (list_fmap typ nat typ_size ts')) <= fuel); lia|exact Hsub|exact H2].
Qed.

Fixpoint typed_mono_Ω (δ:stimestamp) (Δ:constraints) (Ω:kinds) (Γ:env) (e:expr) (ρ:typ)
  (H:typed δ Δ Ω Γ e ρ) {struct H} :
  forall Ω', Ω ⊆ Ω' -> typed δ Δ Ω' Γ e ρ
with Forall2_typed_mono_Ω (δ:stimestamp) (Δ:constraints) (Ω:kinds) (Γ:env) (es:list expr) (ρs:list typ)
  (H:Forall2_typed δ Δ Ω Γ es ρs) {struct H} :
  forall Ω', Ω ⊆ Ω' -> Forall2_typed δ Δ Ω' Γ es ρs.
Proof.
  - intros Ω' Hsub. destruct H.
    all: try (econstructor; eauto; fail).
    + eapply TYTAbs; [exact H|exact H0|].
      exact (typed_mono_Ω δ Δ (binsert x k Ω) Γ e ρ H1 (binsert x k Ω')
               ltac:(apply kinds_binsert_subseteq; exact Hsub)).
    + eapply TYTApp;
        [exact H|exact H0|
         exact (proj1 (wk_typ_mono_Ω (typ_size ρ')) Ω Ω' ρ' k (le_n _) Hsub H1)|
         exact (typed_mono_Ω δ Δ Ω Γ e (TForall x k ρ) H2 Ω' Hsub)].
    + eapply TYFold;
        [exact H|exact H0|exact H1|exact H2|
         exact (proj1 (proj2 (wk_typ_mono_Ω (typat_size σ))) (<[x:=0]>Ω) (<[x:=0]>Ω') σ (le_n _) (kinds_insert_subseteq Ω Ω' x 0 Hsub) H3)|
         exact (typed_mono_Ω δ Δ Ω Γ e (TTypat (vsubst_typat x (TRec x σ δ') σ) δ') H4 Ω' Hsub)].
    + eapply TYUnfold;
        [exact H|exact H0|exact H1|
         exact (proj1 (proj2 (wk_typ_mono_Ω (typat_size σ))) (<[x:=0]>Ω) (<[x:=0]>Ω') σ (le_n _) (kinds_insert_subseteq Ω Ω' x 0 Hsub) H2)|
         exact H3|exact (typed_mono_Ω δ Δ Ω Γ e (TRec x σ δ') H4 Ω' Hsub)].
  - intros Ω' Hsub. destruct H.
    + apply FTNil.
    + eapply FTCons.
      * match goal with Ht : typed _ _ _ _ _ _ |- typed _ _ _ _ _ _ =>
          exact (typed_mono_Ω _ _ _ _ _ _ Ht Ω' Hsub) end.
      * match goal with Ht : Forall2_typed _ _ _ _ _ _ |- Forall2_typed _ _ _ _ _ _ =>
          exact (Forall2_typed_mono_Ω _ _ _ _ _ _ Ht Ω' Hsub) end.
Qed.

Lemma typed_binsert_anon_kind : forall δ Δ Ω k Γ e ρ,
  typed δ Δ Ω Γ e ρ -> typed δ Δ (binsert BAnon k Ω) Γ e ρ.
Proof. intros. cbn [binsert]. exact H. Qed.

Lemma typed_insert_kind_fresh : forall δ Δ Ω x k Γ e ρ,
  x ∉ dom Ω -> typed δ Δ Ω Γ e ρ -> typed δ Δ (<[x:=k]> Ω) Γ e ρ.
Proof.
  intros δ Δ Ω x k Γ e ρ Hx H.
  exact (typed_mono_Ω δ Δ Ω Γ e ρ H (<[x:=k]> Ω)
           ltac:(apply insert_subseteq; apply not_elem_of_dom; exact Hx)).
Qed.

Lemma typed_binsert_named_kind_fresh : forall δ Δ Ω x k Γ e ρ,
  x ∉ dom Ω -> typed δ Δ Ω Γ e ρ -> typed δ Δ (binsert (BNamed x) k Ω) Γ e ρ.
Proof. intros. cbn [binsert]. eapply typed_insert_kind_fresh; eauto. Qed.

Lemma wk_typ_fvv : forall fuel,
  (forall (Ω:kinds) ρ k, typ_size ρ <= fuel -> wk_typ Ω ρ k -> fvv_typ ρ ⊆ dom Ω)
  /\ (forall (Ω:kinds) σt, typat_size σt <= fuel -> wk_typat Ω σt -> fvv_typat σt ⊆ dom Ω)
  /\ (forall (Ω:kinds) ts, S (list_sum (list_fmap typ nat typ_size ts)) <= fuel ->
        wk_typs Ω ts -> ⋃ (list_fmap typ (gset string) fvv_typ ts) ⊆ dom Ω).
Proof.
  induction fuel as [|fuel IH].
  - split; [|split].
    + intros Ω ρ k H. exfalso. pose proof (pos_typ_size ρ). lia.
    + intros Ω σt H. exfalso. pose proof (pos_typat_size σt). lia.
    + intros Ω ts H. exfalso. lia.
  - destruct IH as (IHt & IHty & IHl). split; [|split].
    + intros Ω ρ k H Hwk. destruct ρ as [y|b|σt d|xb ρ0|ρ0 d|x k' ρ0|x σt d]; cbn [wk_typ fvv_typ typ_size] in *.
      * apply elem_of_subseteq. intros z Hz. rewrite elem_of_singleton in Hz. subst z.
        eapply elem_of_dom_2. exact Hwk.
      * set_solver.
      * destruct Hwk as (_ & Hwk). apply (IHty Ω σt ltac:(lia) Hwk).
      * destruct k as [|k']; [contradiction|]. apply (IHt Ω ρ0 k' ltac:(lia) Hwk).
      * apply (IHt Ω ρ0 (S k) ltac:(lia) Hwk).
      * destruct Hwk as (_ & Hwk). destruct x as [|y]; cbn [fvv_typ binder_set] in *.
        -- apply (IHt Ω ρ0 0 ltac:(lia)) in Hwk. set_solver.
        -- assert (HIH := IHt _ ρ0 0 ltac:(lia) Hwk). apply elem_of_subseteq in HIH.
           apply elem_of_subseteq. intros z Hz.
           rewrite elem_of_difference in Hz. destruct Hz as [Hz Hny].
           specialize (HIH z Hz).
           assert (Hd : dom (<[y:=k']> Ω) ≡ ({[y]} : gset string) ∪ dom Ω) by apply dom_insert.
           rewrite Hd in HIH. rewrite elem_of_union in HIH. destruct HIH as [Hzy|Hdom].
           ++ exfalso. apply Hny. exact Hzy.
           ++ exact Hdom.
      * destruct Hwk as (_ & Hwk).
        assert (HIH := IHty _ σt ltac:(lia) Hwk). apply elem_of_subseteq in HIH.
        apply elem_of_subseteq. intros z Hz.
        rewrite elem_of_difference in Hz. destruct Hz as [Hz Hny].
        specialize (HIH z Hz).
        assert (Hd : dom (binsert (BNamed x) 0 Ω) ≡ ({[x]} : gset string) ∪ dom Ω).
        { unfold binsert. cbn. apply dom_insert. }
        rewrite Hd in HIH. rewrite elem_of_union in HIH. destruct HIH as [Hzy|Hdom].
        ++ exfalso. apply Hny. exact Hzy.
        ++ exact Hdom.
    + intros Ω σt H Hwk. destruct σt as [ρ0|ρ1 ρ2|ρ1 ρ2|bs Δ0 d0 ρs ρf]; cbn [wk_typat fvv_typat typat_size] in *.
      * apply (IHt Ω ρ0 0 ltac:(lia) Hwk).
      * destruct Hwk as (H1 & H2). rewrite union_subseteq. split.
        -- apply (IHt Ω ρ1 0 ltac:(lia) H1).
        -- apply (IHt Ω ρ2 0 ltac:(lia) H2).
      * destruct Hwk as (H1 & H2). rewrite union_subseteq. split.
        -- apply (IHt Ω ρ1 0 ltac:(lia) H1).
        -- apply (IHt Ω ρ2 0 ltac:(lia) H2).
      * destruct Hwk as (H1 & H2). rewrite union_subseteq. split.
        -- apply (IHt Ω ρf 0 ltac:(lia) H2).
        -- assert (Hs : S (list_sum (typ_size <$> ρs)) <= fuel) by (pose proof (pos_typ_size ρf); lia).
           apply (IHl Ω ρs Hs). apply (proj1 (inline_wk_eq Ω ρs)). exact H1.
    + intros Ω ts H Hwk. destruct ts as [|t ts']; cbn [wk_typs fvv_typ list_sum list_fmap] in *.
      * set_solver.
      * destruct Hwk as (Hw & Hrest). simpl in H. simpl. rewrite union_subseteq; split.
        -- apply (IHt Ω t 0 ltac:(lia) Hw).
        -- apply (IHl Ω ts' ltac:(pose proof (pos_typ_size t); lia) Hrest).
Qed.

Definition env_avoids (z:string) (σ:tyval) : Prop :=
  forall y ρ, σ !! y = Some ρ -> z ∉ fvv_typ ρ.

Lemma env_avoids_bupd : forall (σ:tyval) z (y:binder) ρ,
  env_avoids z σ -> z ∉ fvv_typ ρ -> env_avoids z (bupd y ρ σ).
Proof.
  intros σ z y ρ H Hav y0 ρ0 Hlook. unfold env_avoids in H.
  destruct y as [|w]; simpl in *.
  - apply (H y0 ρ0). exact Hlook.
  - destruct (decide (y0 = w)) as [e|ne].
    + subst y0. change ((<[w:=ρ]> σ) !! w = Some ρ0) in Hlook.
      rewrite (lookup_insert_eq σ w ρ) in Hlook. injection Hlook as e. subst ρ0. exact Hav.
    + change ((<[w:=ρ]> σ) !! y0 = Some ρ0) in Hlook.
      rewrite (lookup_insert_ne σ w y0 ρ) in Hlook by (intro e; apply ne; symmetry; exact e).
      apply (H y0 ρ0). exact Hlook.
Qed.

Lemma wk_notin_fvv : forall (Ω:kinds) (y:binder) k ρ z,
  z ∉ dom Ω -> z ∉ binder_set y -> wk_typ (binsert y k Ω) ρ k -> z ∉ fvv_typ ρ.
Proof.
  intros Ω y k ρ z Hdom Hbs Hwk.
  pose proof (proj1 (wk_typ_fvv (typ_size ρ)) (binsert y k Ω) ρ k (le_n _) Hwk) as Hsub.
  apply elem_of_subseteq in Hsub. intro Hmem. apply Hsub in Hmem.
  destruct y as [|w]; simpl in *.
  - apply Hdom. exact Hmem.
  - assert (Hd : dom (binsert (BNamed w) k Ω) ≡ ({[w]} : gset string) ∪ dom Ω).
    { unfold binsert. cbn. apply dom_insert. }
    rewrite Hd in Hmem. rewrite elem_of_union in Hmem. destruct Hmem as [H1|H1].
    + apply Hbs. exact H1.
    + apply Hdom. exact H1.
Qed.

Lemma RealF_bupd_irrel :
  forall (rec : world -> gmap string nat -> tsval -> tyval -> typ -> val -> Prop),
  (forall W Ω τ σ z S ρ v, z ∉ dom Ω -> z ∉ fvv_typ ρ -> env_avoids z σ ->
     (rec W Ω τ (bupd (BNamed z) S σ) ρ v <-> rec W Ω τ σ ρ v)) ->
  forall W Ω τ σ (z:string) S ρ v, z ∉ dom Ω -> z ∉ fvv_typ ρ -> env_avoids z σ ->
     (RealF rec W Ω τ (bupd (BNamed z) S σ) ρ v <-> RealF rec W Ω τ σ ρ v).
Proof.
  intros rec IHrec W Ω τ σ z S ρ v Hzdom Hy Henv.
  unfold env_avoids in Henv.
  destruct ρ as [y|b|x d|xb ρ0|ρ0 d|x k ρ0|x σt d]; simpl in *.
  - assert (Hzy : z ≠ y) by (intro e; subst y; apply Hy; set_solver).
    assert (Hlook : (<[z:=S]> σ) !! y = σ !! y).
    { apply (lookup_insert_ne σ z y S); auto. }
    rewrite Hlook. destruct (σ !! y) as [ρy|] eqn:E; simpl.
    + apply (IHrec W Ω τ σ z S ρy v Hzdom (Henv y ρy E) Henv).
    + tauto.
  - destruct b; simpl; tauto.
  - destruct x as [ρ0|ρ1 ρ2|ρ1 ρ2|bs Δ0 d0 ρs ρf]; simpl in *.
    + split.
      { intros (l & bl & He & Hs & Hab & Hbs & Hr). exists l, bl.
        split; [exact He|]. split; [exact Hs|]. split; [exact Hab|]. split.
        - intros bb Hb. apply (proj1 (IHrec W Ω τ σ z S ρ0 bb Hzdom ltac:(set_solver) Henv)). apply Hbs; auto.
        - exact Hr. }
      { intros (l & bl & He & Hs & Hab & Hbs & Hr). exists l, bl.
        split; [exact He|]. split; [exact Hs|]. split; [exact Hab|]. split.
        - intros bb Hb. apply (proj2 (IHrec W Ω τ σ z S ρ0 bb Hzdom ltac:(set_solver) Henv)). apply Hbs; auto.
        - exact Hr. }
    + split.
      { intros (l & v1 & v2 & He & Hs & Hab & H1 & H2). exists l, v1, v2.
        split; [exact He|]. split; [exact Hs|]. split; [exact Hab|]. split.
        - apply (proj1 (IHrec W Ω τ σ z S ρ1 v1 Hzdom ltac:(set_solver) Henv)). exact H1.
        - apply (proj1 (IHrec W Ω τ σ z S ρ2 v2 Hzdom ltac:(set_solver) Henv)). exact H2. }
      { intros (l & v1 & v2 & He & Hs & Hab & H1 & H2). exists l, v1, v2.
        split; [exact He|]. split; [exact Hs|]. split; [exact Hab|]. split.
        - apply (proj2 (IHrec W Ω τ σ z S ρ1 v1 Hzdom ltac:(set_solver) Henv)). exact H1.
        - apply (proj2 (IHrec W Ω τ σ z S ρ2 v2 Hzdom ltac:(set_solver) Henv)). exact H2. }
    + split.
      { intros [(l & v1 & He & Hs & Hab & H1)|(l & v2 & He & Hs & Hab & H2)].
        - left; exists l, v1; split; [exact He|]; split; [exact Hs|]; split; [exact Hab|].
          apply (proj1 (IHrec W Ω τ σ z S ρ1 v1 Hzdom ltac:(set_solver) Henv)). exact H1.
        - right; exists l, v2; split; [exact He|]; split; [exact Hs|]; split; [exact Hab|].
          apply (proj1 (IHrec W Ω τ σ z S ρ2 v2 Hzdom ltac:(set_solver) Henv)). exact H2. }
      { intros [(l & v1 & He & Hs & Hab & H1)|(l & v2 & He & Hs & Hab & H2)].
        - left; exists l, v1; split; [exact He|]; split; [exact Hs|]; split; [exact Hab|].
          apply (proj2 (IHrec W Ω τ σ z S ρ1 v1 Hzdom ltac:(set_solver) Henv)). exact H1.
        - right; exists l, v2; split; [exact He|]; split; [exact Hs|]; split; [exact Hab|].
          apply (proj2 (IHrec W Ω τ σ z S ρ2 v2 Hzdom ltac:(set_solver) Henv)). exact H2. }
    + simpl. tauto.
  - tauto.
  - destruct ρ0 as [y|bb|y d'|yb ρ1|ρ1 d'|y kk ρ1|y σt' d']; simpl; try tauto.
    destruct yb as [|x]; simpl; try tauto.
    split.
    + intro H. apply (proj1 (IHrec W Ω τ σ z S (tsubst_typ {[x:=d]} ρ1) v Hzdom
        ltac:(rewrite (proj1 (fvv_tsubst_eq (typ_size ρ1)) {[x:=d]} ρ1 (le_n _)); exact Hy) Henv)). exact H.
    + intro H. apply (proj2 (IHrec W Ω τ σ z S (tsubst_typ {[x:=d]} ρ1) v Hzdom
        ltac:(rewrite (proj1 (fvv_tsubst_eq (typ_size ρ1)) {[x:=d]} ρ1 (le_n _)); exact Hy) Henv)). exact H.
  - split.
    + intros H ρ'' Hwk. destruct x as [|w]; simpl in *.
      * apply (proj1 (IHrec W Ω τ σ z S ρ0 v Hzdom ltac:(simpl in Hy; set_solver) Henv)).
        apply (H ρ'' Hwk).
      * destruct (decide (w = z)) as [e|ne].
        -- subst w. assert (Hc := H ρ'' Hwk).
           unfold bupd in Hc. cbn in Hc.
           assert (Heq : <[z:=ρ'']> (<[z:=S]> σ) = <[z:=ρ'']> σ) by apply insert_insert_eq.
           rewrite Heq in Hc. exact Hc.
        -- assert (Hc := H ρ'' Hwk).
           assert (Heq : <[w:=ρ'']> (<[z:=S]> σ) = <[z:=S]> (<[w:=ρ'']> σ)).
           { apply (bupd_comm (BNamed w) (BNamed z) ρ'' S σ). intro e. apply ne. injection e. auto. }
           rewrite Heq in Hc.
           assert (Henv' : env_avoids z (bupd (BNamed w) ρ'' σ)).
           { apply env_avoids_bupd; [exact Henv|].
             apply (wk_notin_fvv Ω (BNamed w) k ρ'' z Hzdom).
             + simpl. intro e. apply ne. symmetry. rewrite elem_of_singleton in e. exact e.
             + exact Hwk. }
           apply (proj1 (IHrec W Ω τ (bupd (BNamed w) ρ'' σ) z S ρ0 v Hzdom ltac:(simpl in Hy; set_solver) Henv')). exact Hc.
    + intros H ρ'' Hwk. destruct x as [|w]; simpl in *.
      * apply (proj2 (IHrec W Ω τ σ z S ρ0 v Hzdom ltac:(simpl in Hy; set_solver) Henv)).
        apply (H ρ'' Hwk).
      * destruct (decide (w = z)) as [e|ne].
        -- subst w. assert (Hc := H ρ'' Hwk).
           assert (Heq : <[z:=ρ'']> (<[z:=S]> σ) = <[z:=ρ'']> σ) by apply insert_insert_eq.
           unfold bupd. cbn. rewrite Heq. exact Hc.
        -- assert (Henv' : env_avoids z (bupd (BNamed w) ρ'' σ)).
           { apply env_avoids_bupd; [exact Henv|].
             apply (wk_notin_fvv Ω (BNamed w) k ρ'' z Hzdom).
             + simpl. intro e. apply ne. symmetry. rewrite elem_of_singleton in e. exact e.
             + exact Hwk. }
           assert (Heq : <[w:=ρ'']> (<[z:=S]> σ) = <[z:=S]> (<[w:=ρ'']> σ)).
           { apply (bupd_comm (BNamed w) (BNamed z) ρ'' S σ). intro e. apply ne. injection e. auto. }
           rewrite Heq.
           apply (proj2 (IHrec W Ω τ (bupd (BNamed w) ρ'' σ) z S ρ0 v Hzdom ltac:(simpl in Hy; set_solver) Henv')).
           exact (H ρ'' Hwk).
  - split.
    + intros (v' & He & Hv). exists v'; split; [exact He|].
      apply (proj1 (IHrec W Ω τ σ z S (TTypat (vsubst_typat x (TRec x σt d) σt) d) v' Hzdom
        ltac:(assert (Hsub := proj1 (proj2 (fvv_subst_all (typat_size σt))) x (TRec x σt d) σt (le_n _));
              simpl in Hsub; intro Hmem; apply elem_of_subseteq in Hsub;
              specialize (Hsub z Hmem); simpl in Hy; set_solver) Henv)). exact Hv.
    + intros (v' & He & Hv). exists v'; split; [exact He|].
      apply (proj2 (IHrec W Ω τ σ z S (TTypat (vsubst_typat x (TRec x σt d) σt) d) v' Hzdom
        ltac:(assert (Hsub := proj1 (proj2 (fvv_subst_all (typat_size σt))) x (TRec x σt d) σt (le_n _));
              simpl in Hsub; intro Hmem; apply elem_of_subseteq in Hsub;
              specialize (Hsub z Hmem); simpl in Hy; set_solver) Henv)). exact Hv.
Qed.

Lemma semroot_τ_agree : forall m τ τ' ρ,
  (forall x, x ∈ fv_typ ρ -> tget τ x = tget τ' x) ->
  semroot m τ ρ = semroot m τ' ρ.
Proof.
  induction m as [|m IH]; intros τ τ' ρ Hag.
  - reflexivity.
  - destruct ρ as [y|b|σt δ|xb ρ0|ρ0 δ|x k ρ0|x σt δ]; cbn [semroot fv_typ].
    + reflexivity.
    + destruct b; reflexivity.
    + f_equal. apply Hag. set_solver.
    + reflexivity.
    + destruct ρ0 as [y|bb|σt δ0|yb ρ1|ρ1 δ0|y kk ρ1|y σt' δ0]; simpl; try reflexivity.
      destruct yb as [|z]; simpl; try reflexivity.
      apply IH. intros w Hw.
      pose proof (fv_tsubst_all_sharp (typ_size ρ1)) as Hfv.
      destruct Hfv as (Hf & _ & _).
      pose proof (Hf ({[z:=δ]}) ρ1 (le_n _)) as Hsub.
      apply elem_of_subseteq in Hsub. specialize (Hsub w Hw).
      rewrite elem_of_union in Hsub. destruct Hsub as [Hd|Hv].
      * rewrite elem_of_difference in Hd. apply Hag. cbn [fv_typ]. set_solver.
      * pose proof (mvalues_singleton z δ) as Hm.
        apply elem_of_subseteq in Hm. specialize (Hm w Hv).
        apply elem_of_singleton in Hm. subst w. apply Hag. cbn [fv_typ]. set_solver.
    + reflexivity.
    + f_equal. apply Hag. set_solver.
Qed.

Lemma root_reaches_τ_agree : forall W τ τ' ρ δ,
  (forall x, x ∈ fv_typ ρ -> tget τ x = tget τ' x) ->
  root_reaches W τ ρ δ -> root_reaches W τ' ρ δ.
Proof.
  intros W τ τ' ρ δ Hag H m r Hs.
  apply (H m r). rewrite (semroot_τ_agree m τ τ' ρ Hag). exact Hs.
Qed.

Lemma root_reaches_τ_ext : forall W τ τ' ρ δ,
  (forall x, tget τ x = tget τ' x) ->
  root_reaches W τ ρ δ -> root_reaches W τ' ρ δ.
Proof.
  intros W τ τ' ρ δ H.
  apply root_reaches_τ_agree. intros x Hx. apply H.
Qed.

Lemma Real_τ_ext : forall n W Ω τ τ' σ ρ v,
  (forall x, tget τ x = tget τ' x) ->
  (Real n W Ω τ σ ρ v <-> Real n W Ω τ' σ ρ v).
Proof.
  intros n. induction n as [|n IH]; intros W Ω τ τ' σ ρ v H.
  - cbn [Real]. tauto.
  - rewrite !Real_S_eq.
    destruct ρ as [y|b|σt δ|xb ρ0|ρ0 δ|x k ρ0|x σt δ]; cbn [RealF].
    + destruct (σ !! y) as [ρy|] eqn:E; cbn.
      * apply (IH W Ω τ τ' σ ρy v H).
      * tauto.
    + destruct b; simpl; tauto.
    + destruct σt as [ρ0|ρ1 ρ2|ρ1 ρ2|bs Δ0 δ0 ρs ρf]; cbn [RealF].
      * split.
        -- intros (l & bs' & He & Hs & Hab & Hbs & Hr). exists l, bs'.
           split; [exact He|]. split; [exact Hs|]. split.
           ++ rewrite <- (H δ). exact Hab.
           ++ split.
              ** intros bb Hb. apply (proj1 (IH W Ω τ τ' σ ρ0 bb H)). exact (Hbs bb Hb).
              ** rewrite <- (H δ). apply (root_reaches_τ_ext W τ τ' ρ0 (tget τ δ) H). exact Hr.
        -- intros (l & bs' & He & Hs & Hab & Hbs & Hr). exists l, bs'.
           split; [exact He|]. split; [exact Hs|]. split.
           ++ rewrite <- (H δ) in Hab. exact Hab.
           ++ split.
              ** intros bb Hb. apply (proj2 (IH W Ω τ τ' σ ρ0 bb H)). exact (Hbs bb Hb).
              ** rewrite <- (H δ) in Hr. apply (root_reaches_τ_ext W τ' τ ρ0 (tget τ δ) ltac:(intro x; symmetry; apply H)). exact Hr.
      * split.
        -- intros (l & v1 & v2 & He & Hs & Hab & H1r & H2r). exists l, v1, v2.
           split; [exact He|]. split; [exact Hs|]. split.
           ++ rewrite <- (H δ). exact Hab.
           ++ split; [apply (proj1 (IH W Ω τ τ' σ ρ1 v1 H))|apply (proj1 (IH W Ω τ τ' σ ρ2 v2 H))]; auto.
        -- intros (l & v1 & v2 & He & Hs & Hab & H1r & H2r). exists l, v1, v2.
           split; [exact He|]. split; [exact Hs|]. split.
           ++ rewrite <- (H δ) in Hab. exact Hab.
           ++ split; [apply (proj2 (IH W Ω τ τ' σ ρ1 v1 H))|apply (proj2 (IH W Ω τ τ' σ ρ2 v2 H))]; auto.
      * split.
        -- intros [(l & v1 & He & Hs & Hab & Hr)|(l & v2 & He & Hs & Hab & Hr)].
           ++ left. exists l, v1. split; [exact He|]. split; [exact Hs|]. split.
              ** rewrite <- (H δ). exact Hab.
              ** apply (proj1 (IH W Ω τ τ' σ ρ1 v1 H)). exact Hr.
           ++ right. exists l, v2. split; [exact He|]. split; [exact Hs|]. split.
              ** rewrite <- (H δ). exact Hab.
              ** apply (proj1 (IH W Ω τ τ' σ ρ2 v2 H)). exact Hr.
        -- intros [(l & v1 & He & Hs & Hab & Hr)|(l & v2 & He & Hs & Hab & Hr)].
           ++ left. exists l, v1. split; [exact He|]. split; [exact Hs|]. split.
              ** rewrite <- (H δ) in Hab. exact Hab.
              ** apply (proj2 (IH W Ω τ τ' σ ρ1 v1 H)). exact Hr.
           ++ right. exists l, v2. split; [exact He|]. split; [exact Hs|]. split.
              ** rewrite <- (H δ) in Hab. exact Hab.
              ** apply (proj2 (IH W Ω τ τ' σ ρ2 v2 H)). exact Hr.
      * split.
        -- intros [(c & He)|(l & bd & a & e & He & Hs & Hab)].
           ++ left. exists c. exact He.
           ++ right. exists l, bd, a, e. split; [exact He|]. split; [exact Hs|].
              rewrite <- (H δ). exact Hab.
        -- intros [(c & He)|(l & bd & a & e & He & Hs & Hab)].
           ++ left. exists c. exact He.
           ++ right. exists l, bd, a, e. split; [exact He|]. split; [exact Hs|].
              rewrite <- (H δ) in Hab. exact Hab.
    + cbn. tauto.
    + destruct ρ0 as [y|bb|σt δ0|yb ρ1|ρ1 δ0|y kk ρ1|y σt' δ0]; simpl; try tauto.
      destruct yb as [|z]; simpl; try tauto.
      apply IH. exact H.
    + split.
      * intros F ρ' Hwk. apply (proj1 (IH W Ω τ τ' (bupd x ρ' σ) ρ0 v H)). apply (F ρ' Hwk).
      * intros F ρ' Hwk. apply (proj2 (IH W Ω τ τ' (bupd x ρ' σ) ρ0 v H)). apply (F ρ' Hwk).
    + split.
      * intros (v' & He & Hv). exists v'; split; [exact He|].
        apply (proj1 (IH W Ω τ τ' σ (TTypat (vsubst_typat x (TRec x σt δ) σt) δ) v' H)). exact Hv.
      * intros (v' & He & Hv). exists v'; split; [exact He|].
        apply (proj2 (IH W Ω τ τ' σ (TTypat (vsubst_typat x (TRec x σt δ) σt) δ) v' H)). exact Hv.
Qed.

Lemma abef_tsub : forall (G:graph) α t t' l,
  reachable G t t' -> abef G α t l -> abef G α t' l.
Proof.
  intros G α t t' l Hr H. unfold abef in *.
  destruct (α !! l) as [v'|] eqn:E; [|contradiction].
  eapply reachable_trans; eauto.
Qed.

Lemma Real_typat_tsub : forall n W Ω τ σ (σt:typat) δ δ' v,
  reachable (wgr W) (tget τ δ) (tget τ δ') ->
  Real n W Ω τ σ (TTypat σt δ) v ->
  Real n W Ω τ σ (TTypat σt δ') v.
Proof.
  intros n. induction n as [|n IH]; intros W Ω τ σ σt δ δ' v Hr H.
  - cbn [Real]. exact I.
  - rewrite Real_S_eq in H. rewrite Real_S_eq.
    destruct σt as [ρ0|ρ1 ρ2|ρ1 ρ2|bs Δ0 δ0 ρs ρf]; cbn [RealF] in *.
    + destruct H as (l & bl & He & Hs & Hab & Hbs & Hrch). exists l, bl.
      split; [exact He|]. split; [exact Hs|]. split.
      * apply (abef_tsub (wgr W) (wam W) (tget τ δ) (tget τ δ') l); auto.
      * split; [exact Hbs|].
        eapply root_reaches_trans; eauto.
    + destruct H as (l & v1 & v2 & He & Hs & Hab & H1 & H2). exists l, v1, v2.
      split; [exact He|]. split; [exact Hs|]. split.
      * apply (abef_tsub (wgr W) (wam W) (tget τ δ) (tget τ δ') l); auto.
      * split; auto.
    + destruct H as [(l & v1 & He & Hs & Hab & H1)|(l & v2 & He & Hs & Hab & H2)].
      * left. exists l, v1. split; [exact He|]. split; [exact Hs|]. split.
        { apply (abef_tsub (wgr W) (wam W) (tget τ δ) (tget τ δ') l); auto. }
        exact H1.
      * right. exists l, v2. split; [exact He|]. split; [exact Hs|]. split.
        { apply (abef_tsub (wgr W) (wam W) (tget τ δ) (tget τ δ') l); auto. }
        exact H2.
    + destruct H as [(c & He)|(l & bd & a & e & He & Hs & Hab)].
      * left. exists c. exact He.
      * right. exists l, bd, a, e. split; [exact He|]. split; [exact Hs|].
        apply (abef_tsub (wgr W) (wam W) (tget τ δ) (tget τ δ') l); auto.
Qed.

Lemma Real_bupd_irrel : forall n W Ω τ σ (z:string) S ρ v,
  z ∉ dom Ω -> z ∉ fvv_typ ρ -> env_avoids z σ ->
  (Real n W Ω τ (bupd (BNamed z) S σ) ρ v <-> Real n W Ω τ σ ρ v).
Proof.
  intros n. induction n as [|n IH]; intros W Ω τ σ z S ρ v Hzdom Hy Henv.
  - simpl. tauto.
  - rewrite !Real_S_eq.
    eapply RealF_bupd_irrel.
    + intros W0 Ω0 τ0 σ0 z0 S0 ρ0 v0 Hd Hv He. apply IH; auto.
    + exact Hzdom.
    + exact Hy.
    + exact Henv.
Qed.

Lemma interp_bupdS_irrel : forall n ξ τ (y:string) S ρ ts W v,
  y ∉ fvv_typ ρ ->
  (interp n (bupdS ξ (BNamed y) S) τ ρ ts W v <-> interp n ξ τ ρ ts W v).
Proof.
  intros n. induction n as [|n IH]; intros ξ τ y S ρ ts W v Hy.
  - simpl. tauto.
  - destruct ρ as [z|b|σt δ|bd ρ0|ρ0 δ|x k ρ0|x σt δ]; simpl in *.
    + apply vget_bupdS_named_ne. intro e. subst z. apply Hy.
      rewrite elem_of_singleton. reflexivity.
    + destruct b; simpl; tauto.
    + destruct σt as [ρ0|ρ1 ρ2|ρ1 ρ2|bs Δ δs ρs ρf]; simpl in *.
      * split.
        -- intros (l & bl & He & Hs & Hab & Hbs & Hr). exists l, bl.
           split; [exact He|]. split; [exact Hs|]. split; [exact Hab|]. split.
           ++ intros b Hb. apply (proj1 (IH ξ τ y S ρ0 [] W b Hy)). apply Hbs; auto.
           ++ exact Hr.
        -- intros (l & bl & He & Hs & Hab & Hbs & Hr). exists l, bl.
           split; [exact He|]. split; [exact Hs|]. split; [exact Hab|]. split.
           ++ intros b Hb. apply (proj2 (IH ξ τ y S ρ0 [] W b Hy)). apply Hbs; auto.
           ++ exact Hr.
      * split.
        -- intros (l & v1 & v2 & He & Hs & Hab & H1 & H2). exists l, v1, v2.
           split; [exact He|]. split; [exact Hs|]. split; [exact Hab|]. split.
           ++ apply (proj1 (IH ξ τ y S ρ1 [] W v1 ltac:(set_solver))). exact H1.
           ++ apply (proj1 (IH ξ τ y S ρ2 [] W v2 ltac:(set_solver))). exact H2.
        -- intros (l & v1 & v2 & He & Hs & Hab & H1 & H2). exists l, v1, v2.
           split; [exact He|]. split; [exact Hs|]. split; [exact Hab|]. split.
           ++ apply (proj2 (IH ξ τ y S ρ1 [] W v1 ltac:(set_solver))). exact H1.
           ++ apply (proj2 (IH ξ τ y S ρ2 [] W v2 ltac:(set_solver))). exact H2.
      * split.
        -- intros [(l & v1 & He & Hs & Hab & H1)|(l & v2 & He & Hs & Hab & H2)].
           ++ left; exists l, v1; split; [exact He|]; split; [exact Hs|]; split; [exact Hab|].
              apply (proj1 (IH ξ τ y S ρ1 [] W v1 ltac:(set_solver))); exact H1.
           ++ right; exists l, v2; split; [exact He|]; split; [exact Hs|]; split; [exact Hab|].
              apply (proj1 (IH ξ τ y S ρ2 [] W v2 ltac:(set_solver))); exact H2.
        -- intros [(l & v1 & He & Hs & Hab & H1)|(l & v2 & He & Hs & Hab & H2)].
           ++ left; exists l, v1; split; [exact He|]; split; [exact Hs|]; split; [exact Hab|].
              apply (proj2 (IH ξ τ y S ρ1 [] W v1 ltac:(set_solver))); exact H1.
           ++ right; exists l, v2; split; [exact He|]; split; [exact Hs|]; split; [exact Hab|].
              apply (proj2 (IH ξ τ y S ρ2 [] W v2 ltac:(set_solver))); exact H2.
      * simpl. tauto.
    + destruct ts as [|t ts']; simpl; [tauto|]. apply (IH ξ (tupd τ bd t) y S ρ0 ts' W v Hy).
    + apply (IH ξ τ y S ρ0 (tget τ δ :: ts) W v Hy).
    + split.
      * intros H S'. destruct x as [|z]; simpl in *.
        -- apply (proj1 (IH ξ τ y S ρ0 [] W v ltac:(set_solver))). apply (H S').
        -- destruct (decide (y = z)) as [e|ne].
           ++ subst z.
              assert (Hc := H S').
              assert (Heq : vupd (vupd ξ y S) y S' = vupd ξ y S')
                by (unfold vupd; apply insert_insert_eq).
              rewrite Heq in Hc. exact Hc.
           ++ assert (Hc := H S').
              assert (Hcomm := bupdS_comm ξ (BNamed y) (BNamed z) S S'
                              ltac:(intro e; apply ne; injection e; auto)).
              change (vupd (vupd ξ y S) z S' = vupd (vupd ξ z S') y S) in Hcomm.
              rewrite Hcomm in Hc.
              apply (proj1 (IH (bupdS ξ (BNamed z) S') τ y S ρ0 [] W v ltac:(set_solver))).
              exact Hc.
      * intros H S'. destruct x as [|z]; simpl in *.
        -- apply (proj2 (IH ξ τ y S ρ0 [] W v ltac:(set_solver))). apply (H S').
        -- destruct (decide (y = z)) as [e|ne].
           ++ subst z.
              assert (Heq : vupd (vupd ξ y S) y S' = vupd ξ y S')
                by (unfold vupd; apply insert_insert_eq).
              rewrite Heq. exact (H S').
           ++ assert (Hc := H S').
              assert (Hcomm := bupdS_comm ξ (BNamed y) (BNamed z) S S'
                              ltac:(intro e; apply ne; injection e; auto)).
              change (vupd (vupd ξ y S) z S' = vupd (vupd ξ z S') y S) in Hcomm.
              rewrite Hcomm.
              apply (proj2 (IH (bupdS ξ (BNamed z) S') τ y S ρ0 [] W v ltac:(set_solver))).
              exact Hc.
    + split.
      * intros (v' & He & Hv). exists v'. split; [exact He|].
        assert (Hhyg : y ∉ fvv_typ (TTypat (vsubst_typat x (TRec x σt δ) σt) δ)).
        { assert (Hsub := proj1 (proj2 (fvv_subst_all (typat_size σt))) x (TRec x σt δ) σt (le_n _)).
          simpl in Hsub. intro Hmem. apply elem_of_subseteq in Hsub.
          specialize (Hsub y Hmem). simpl in Hy. set_solver. }
        apply (proj1 (IH ξ τ y S (TTypat (vsubst_typat x (TRec x σt δ) σt) δ) [] W v' Hhyg)).
        exact Hv.
      * intros (v' & He & Hv). exists v'. split; [exact He|].
        assert (Hhyg : y ∉ fvv_typ (TTypat (vsubst_typat x (TRec x σt δ) σt) δ)).
        { assert (Hsub := proj1 (proj2 (fvv_subst_all (typat_size σt))) x (TRec x σt δ) σt (le_n _)).
          simpl in Hsub. intro Hmem. apply elem_of_subseteq in Hsub.
          specialize (Hsub y Hmem). simpl in Hy. set_solver. }
        apply (proj2 (IH ξ τ y S (TTypat (vsubst_typat x (TRec x σt δ) σt) δ) [] W v' Hhyg)).
        exact Hv.
Qed.

Definition sem (ξ:valenv) (τ:tsval) (ρ:typ) : SemF :=
  fun n ts W v => interp n ξ τ ρ ts W v.

Lemma sem_τ_agree : forall ξ τ (y:string) t ρ, y ∉ fv_typ ρ ->
  forall m ts W v, sem ξ τ ρ m ts W v <-> sem ξ (tupd τ (BNamed y) t) ρ m ts W v.
Proof.
  intros ξ τ y t ρ Hhyg m ts W v. unfold sem. split.
  - intro H. apply (proj2 (interp_tupd_irrel m ξ τ y t ρ ts W v Hhyg)). exact H.
  - intro H. apply (proj1 (interp_tupd_irrel m ξ τ y t ρ ts W v Hhyg)). exact H.
Qed.

Lemma sem_ξ_agree : forall ξ (z:string) S τ ρ, z ∉ fvv_typ ρ ->
  forall m ts W v, sem (bupdS ξ (BNamed z) S) τ ρ m ts W v <-> sem ξ τ ρ m ts W v.
Proof.
  intros ξ z S τ ρ Hhyg m ts W v. unfold sem.
  apply (interp_bupdS_irrel m ξ τ z S ρ ts W v Hhyg).
Qed.

Lemma bupdS_none_agree2 : forall (ξ:valenv) (x:binder) S S' y,
  (bupdS ξ x S) !! y = None <-> (bupdS ξ x S') !! y = None.
Proof.
  intros ξ [|z] S S' y; simpl.
  - reflexivity.
  - change ((<[z:=S]> ξ) !! y = None <-> (<[z:=S']> ξ) !! y = None).
    rewrite (lookup_insert_None ξ z y S). rewrite (lookup_insert_None ξ z y S'). tauto.
Qed.

Lemma bupdS_some_agree2 : forall (ξ:valenv) (x:binder) S S',
  (forall m ts W v, S m ts W v <-> S' m ts W v) ->
  forall y T1 T2, (bupdS ξ x S) !! y = Some T1 -> (bupdS ξ x S') !! y = Some T2 ->
    forall m ts W v, T1 m ts W v <-> T2 m ts W v.
Proof.
  intros ξ [|z] S S' HS y T1 T2 E1 E2; simpl in *.
  - assert (T1 = T2) by (rewrite E1 in E2; injection E2; auto). subst T2. tauto.
  - change ((<[z:=S]> ξ) !! y = Some T1) in E1.
    change ((<[z:=S']> ξ) !! y = Some T2) in E2.
    rewrite (lookup_insert_Some ξ z y S T1) in E1.
    rewrite (lookup_insert_Some ξ z y S' T2) in E2.
    destruct (decide (z = y)) as [e|n].
    + destruct E1 as [[_ h1]|[n1 _]]; [|exfalso; apply n1; exact e].
      destruct E2 as [[_ h2]|[n2 _]]; [|exfalso; apply n2; exact e].
      subst T1. subst T2. apply HS.
    + destruct E1 as [[e1 _]|[_ h1]]; [exfalso; apply n; exact e1|].
      destruct E2 as [[e2 _]|[_ h2]]; [exfalso; apply n; exact e2|].
      assert (T1 = T2) by (rewrite h1 in h2; injection h2; auto). subst T2. tauto.
Qed.



(* ---------- step-indexed strong safety and its reduction ---------- *)
Definition State := (store * amap * graph * task_tree * expr)%type.

Definition cfg_good (s:State) : Prop :=
  let '(σ,α,G,T,e) := s in
  safe true σ α G T e /\ disentangled G α T e.

Fixpoint SafeN (n:nat) (s:State) : Prop :=
  match n with
  | 0 => True
  | S m => cfg_good s /\ (forall s', step s s' -> SafeN m s')
  end.

Inductive steps_at_most : nat -> State -> State -> Prop :=
| sam_zero : forall s, steps_at_most 0 s s
| sam_step : forall n s s' s'',
    step s s' -> steps_at_most n s' s'' -> steps_at_most (S n) s s''.

Lemma rtc_steps_at_most : forall s s',
  rtc step s s' -> exists k, steps_at_most k s s'.
Proof.
  intros s s' H. induction H as [x | x y z Hstep Hrtc IH].
  - exists 0. constructor.
  - destruct IH as [k Hk]. exists (S k). eapply sam_step; eauto.
Qed.

Definition st_store (s:State) : store := let '(σ,_,_,_,_) := s in σ.
Definition st_amap (s:State) : amap := let '(_,α,_,_,_) := s in α.
Definition st_graph (s:State) : graph := let '(_,_,G,_,_) := s in G.
Definition st_tree (s:State) : task_tree := let '(_,_,_,T,_) := s in T.
Definition st_expr (s:State) : expr := let '(_,_,_,_,e) := s in e.

Lemma step_tuple_inv : forall σ α G T e σ' α' G' T' e',
  step (σ,α,G,T,e) (σ',α',G',T',e') ->
  lang.semantics.step σ α G T e σ' α' G' T' e'.
Proof. intros. exact H. Qed.

Lemma gmap_subseteq_trans : forall (A:Type) (m1 m2 m3:gmap loc A),
  m1 ⊆ m2 -> m2 ⊆ m3 -> m1 ⊆ m3.
Proof.
  intros A m1 m2 m3 H1 H2.
  rewrite map_subseteq_spec in *. intros k v Hv. eauto.
Qed.

Definition LiveInv (s:State) : Prop :=
  locs (st_expr s) ⊆ dom (st_amap s) /\ store_locs (st_store s) ⊆ dom (st_amap s).

Lemma step_LiveInv : forall s s', step s s' -> LiveInv s -> LiveInv s'.
Proof.
  intros s s' Hs HL.
  destruct s as [[[[σ α] G] T] e]; destruct s' as [[[[σ' α'] G'] T'] e'].
  destruct HL as (Hle & Hls).
  pose proof (step_tuple_inv _ _ _ _ _ _ _ _ _ _ Hs) as Hsem.
  pose proof (dom_subseteq_of_map_sub _ _ (step_α_sub _ _ _ _ _ _ _ _ _ _ Hsem)) as Hdom.
  split.
  - pose proof (step_locs_bound _ _ _ _ _ _ _ _ _ _ Hsem) as Hb.
    cbn [st_expr st_amap] in *. set_solver.
  - pose proof (step_store_locs_bound _ _ _ _ _ _ _ _ _ _ Hsem) as Hb.
    cbn [st_store st_amap] in *. set_solver.
Qed.

Lemma initial_LiveInv : forall t0 e {Hl : locs e = ∅},
  LiveInv (∅,∅,{[(t0,t0)]},Leaf t0,e).
Proof.
  intros t0 e Hl. unfold LiveInv, st_expr, st_amap, st_store. cbn.
  split.
  - rewrite Hl. set_solver.
  - rewrite store_locs_empty. set_solver.
Qed.

Lemma rtc_step_LiveInv : forall s s', rtc step s s' -> LiveInv s -> LiveInv s'.
Proof.
  intros s s' H. induction H as [x | x y z Hxy Hyz IH]; intros HL.
  - exact HL.
  - apply IH. eapply step_LiveInv; eauto.
Qed.

Lemma reachable_LiveInv : forall t0 e σ' α' G' T' e',
  locs e = ∅ ->
  rtc step (∅,∅,{[(t0,t0)]},Leaf t0,e) (σ',α',G',T',e') ->
  LiveInv (σ',α',G',T',e').
Proof.
  intros t0 e σ' α' G' T' e' Hl H.
  eapply rtc_step_LiveInv; [exact H |]. apply initial_LiveInv. exact Hl.
Qed.

Lemma reachable_locs_dom : forall t0 e σ' α' G' T' e',
  locs e = ∅ ->
  rtc step (∅,∅,{[(t0,t0)]},Leaf t0,e) (σ',α',G',T',e') ->
  locs e' ⊆ dom α'.
Proof.
  intros. pose proof (reachable_LiveInv _ _ _ _ _ _ _ H H0) as HL.
  exact (proj1 HL).
Qed.

Lemma reachable_store_locs_dom : forall t0 e σ' α' G' T' e',
  locs e = ∅ ->
  rtc step (∅,∅,{[(t0,t0)]},Leaf t0,e) (σ',α',G',T',e') ->
  store_locs σ' ⊆ dom α'.
Proof.
  intros. pose proof (reachable_LiveInv _ _ _ _ _ _ _ H H0) as HL.
  exact (proj2 HL).
Qed.

Lemma rtc_step_root : forall s s',
  rtc step s s' -> root (st_tree s') = root (st_tree s).
Proof.
  intros s s' H. revert s H.
  refine (rtc_ind_l (fun x => root (st_tree s') = root (st_tree x)) s' _ _).
  - reflexivity.
  - intros x y Hxy Hyz IH.
    destruct x as [[[[σ α] G] T] e]; destruct y as [[[[σ' α'] G'] T'] e'].
    pose proof (step_tuple_inv _ _ _ _ _ _ _ _ _ _ Hxy) as Hs.
    pose proof (step_G _ _ _ _ _ _ _ _ _ _ Hs) as (Hsub & Hr).
    cbn [st_tree] in *. rewrite IH. exact Hr.
Qed.

Lemma rtc_step_G_sub : forall s s',
  rtc step s s' -> st_graph s ⊆ st_graph s'.
Proof.
  intros s s' H. revert s H.
  refine (rtc_ind_l (fun x => st_graph x ⊆ st_graph s') s' _ _).
  - reflexivity.
  - intros x y Hxy Hyz IH.
    destruct x as [[[[σ α] G] T] e]; destruct y as [[[[σ' α'] G'] T'] e'].
    pose proof (step_tuple_inv _ _ _ _ _ _ _ _ _ _ Hxy) as Hs.
    pose proof (step_G _ _ _ _ _ _ _ _ _ _ Hs) as (Hsub & Hr).
    cbn [st_graph] in *.
    transitivity G'; [exact Hsub | exact IH].
Qed.

Lemma rtc_step_σ_dom_sub : forall s s',
  rtc step s s' -> dom (st_store s) ⊆ dom (st_store s').
Proof.
  intros s s' H. revert s H.
  refine (rtc_ind_l (fun x => dom (st_store x) ⊆ dom (st_store s')) s' _ _).
  - reflexivity.
  - intros x y Hxy Hyz IH.
    destruct x as [[[[σ α] G] T] e]; destruct y as [[[[σ' α'] G'] T'] e'].
    pose proof (step_tuple_inv _ _ _ _ _ _ _ _ _ _ Hxy) as Hs.
    pose proof (step_σ_dom_sub _ _ _ _ _ _ _ _ _ _ Hs) as Hsub.
    cbn [st_store] in *.
    transitivity (dom σ'); [exact Hsub | exact IH].
Qed.

Lemma rtc_step_α_sub : forall s s',
  rtc step s s' -> st_amap s ⊆ st_amap s'.
Proof.
  intros s s' H. revert s H.
  refine (rtc_ind_l (fun x => st_amap x ⊆ st_amap s') s' _ _).
  - reflexivity.
  - intros x y Hxy Hyz IH.
    destruct x as [[[[σ α] G] T] e]; destruct y as [[[[σ' α'] G'] T'] e'].
    pose proof (step_tuple_inv _ _ _ _ _ _ _ _ _ _ Hxy) as Hs.
    pose proof (step_α_sub _ _ _ _ _ _ _ _ _ _ Hs) as Hsub.
    cbn [st_amap] in *.
    eapply gmap_subseteq_trans; [exact Hsub | exact IH].
Qed.

Lemma rtc_step_GInv : forall s s',
  rtc step s s' -> GInv (st_graph s) (st_tree s) -> GInv (st_graph s') (st_tree s').
Proof.
  intros s s' H. revert s H.
  refine (rtc_ind_l (fun x => GInv (st_graph x) (st_tree x) ->
                           GInv (st_graph s') (st_tree s')) s' _ _).
  - auto.
  - intros x y Hxy Hyz IH Hx.
    destruct x as [[[[σ α] G] T] e]; destruct y as [[[[σ' α'] G'] T'] e'].
    pose proof (step_tuple_inv _ _ _ _ _ _ _ _ _ _ Hxy) as Hs.
    cbn [st_graph st_tree] in *.
    apply IH. eapply step_GInv; eauto.
Qed.

Lemma reachable_root_t0 : forall t0 e σ' α' G' T' e',
  rtc step (∅,∅,{[(t0,t0)]},Leaf t0,e) (σ',α',G',T',e') -> root T' = t0.
Proof.
  intros t0 e σ' α' G' T' e' H.
  pose proof (rtc_step_root (∅,∅,{[(t0,t0)]},Leaf t0,e) (σ',α',G',T',e') H) as Hr.
  cbn [st_tree root] in Hr. exact Hr.
Qed.

Lemma reachable_GInv : forall t0 e σ' α' G' T' e',
  rtc step (∅,∅,{[(t0,t0)]},Leaf t0,e) (σ',α',G',T',e') -> GInv G' T'.
Proof.
  intros t0 e σ' α' G' T' e' H.
  exact (rtc_step_GInv (∅,∅,{[(t0,t0)]},Leaf t0,e) (σ',α',G',T',e') H I).
Qed.

Lemma reachable_G_initial : forall t0 e σ' α' G' T' e',
  rtc step (∅,∅,{[(t0,t0)]},Leaf t0,e) (σ',α',G',T',e') -> {[(t0,t0)]} ⊆ G'.
Proof.
  intros t0 e σ' α' G' T' e' H.
  exact (rtc_step_G_sub (∅,∅,{[(t0,t0)]},Leaf t0,e) (σ',α',G',T',e') H).
Qed.

Lemma SafeN_steps_at_most : forall k s s',
  steps_at_most k s s' -> forall n, SafeN n s -> k < n -> cfg_good s'.
Proof.
  intros k s s' Hk. induction Hk as [s0 | n0 s0 s1 s2 Hstep Hrest IH].
  - intros n Hn Hlt. destruct n as [|m]; [lia|]. simpl in Hn. exact (proj1 Hn).
  - intros n Hn Hlt. destruct n as [|m]; [lia|]. simpl in Hn.
    destruct Hn as (Hg & Hnext).
    apply (IH m); [apply Hnext; exact Hstep | lia].
Qed.

(* The single remaining obligation: the initial configuration is strongly safe
   for every fuel.  This is exactly the progress/preservation ("fundamental")
   theorem for the type system. *)
Lemma soundness_of_SafeN : forall e,
  (forall n t0, SafeN n (∅,∅,{[(t0,t0)]},Leaf t0,e)) ->
  always_safe_and_disentangled true e.
Proof.
  intros e H t0 σ' α' G' T' e' Hrtc.
  destruct (rtc_steps_at_most (∅,∅,{[(t0,t0)]},(Leaf t0),e)
                              (σ',α',G',T',e') Hrtc) as [k Hk].
  pose proof (H (S k) t0) as Hn.
  pose proof (SafeN_steps_at_most k (∅,∅,{[(t0,t0)]},(Leaf t0),e)
                (σ',α',G',T',e') Hk (S k) Hn ltac:(lia)) as Hg.
  unfold cfg_good in Hg. simpl in Hg. exact Hg.
Qed.


Theorem soundness δ e ρ :
  locs e = ∅ ->
  syntactical.typed δ ∅ ∅ ∅ e ρ ->
  always_safe_and_disentangled true e.
