From stdpp Require Import relations gmap.
From dislog.lang Require Import syntax semantics reducible disentangled.
From dislog.types Require Import syntactical.
From stdpp Require Import binders strings fin_sets.
From dislog.types Require Import typing.
From Stdlib Require Import Lia.

(* Pure operational definitions from src/logic/wpg_adequacy.v. *)
Definition step '(σ,α,G,T,e) '(σ',α',G',T',e') :=
  lang.semantics.step σ α G T e σ' α' G' T' e'.

Definition safe he σ α G T e :=
  (is_val e /\ is_leaf T) \/ reducible he σ α G T e.

Definition always_safe_and_disentangled (allow_oob:bool) (e:expr) :=
  forall t0 σ' α' G' T' e',
  rtc step (∅,∅,{[(t0,t0)]},(Leaf t0),e) (σ',α',G',T',e') ->
  safe allow_oob σ' α' G' T' e' /\ disentangled G' α' T' e'.

(* Scalar types describe values that are independent of the heap. *)
Local Definition source_base (v : val) (b : tbase) : Prop :=
  match v with
  | VUnit => b = TBUnit
  | VInt _ => b = TBInt
  | VBool _ => b = TBBool
  | _ => False
  end.

Local Lemma value_form e : is_val e -> exists v, e = Val v.
Proof. unfold is_val. destruct e; intros Hv; try solve [exfalso; exact Hv]. eexists; reflexivity. Qed.

Local Lemma reduce_head σ α G t e σ' α' e' :
  head_step G t σ α e σ' α' e' -> reducible true σ α G (Leaf t) e.
Proof. intros H. exact (RedSched true σ α G (Leaf t) e σ' α' G (Leaf t) e' (SchedHead σ α G t e σ' α' e' H)). Qed.

Local Ltac fresh_source_location σ α :=
  let L := fresh "L" in let l := fresh "l" in let Hl := fresh "Hl" in
  pose (L := dom σ ∪ dom α : gset loc);
  pose (l := fresh L);
  assert (Hl : l ∉ L) by apply is_fresh;
  assert (l ∉ dom σ) by (unfold L in Hl; set_solver);
  assert (l ∉ dom α) by (unfold L in Hl; set_solver).

Local Lemma locs_fill_item K e : locs (fill_item K e) = locs K ∪ locs e.
Proof.
  destruct K; cbn [locs location_expr location_ctx location_list locs_expr locs_ctx fill_item];
    try set_solver.
  rewrite fmap_app, fmap_cons, union_list_app_L, union_list_cons, <-list_fmap_compose.
  cbn [locs_expr]. set_solver.
Qed.

Local Lemma fill_item_nonvalue K e : ¬ is_val (fill_item K e).
Proof. destruct K; exact (fun H => H). Qed.

Local Lemma call_argument_unique vs ws (e f : expr) es fs :
  ¬ is_val e -> ¬ is_val f ->
  (Val <$> vs) ++ e :: es = (Val <$> ws) ++ f :: fs ->
  vs = ws /\ e = f /\ es = fs.
Proof.
  intros He Hf. revert ws. induction vs; intros [|w ws] Heq; simpl in Heq.
  - injection Heq as -> ->. auto.
  - injection Heq as Heq _. subst e. exfalso. apply He. exact I.
  - injection Heq as Heq _. subst f. exfalso. apply Hf. exact I.
  - injection Heq as Hv Hs. subst w. destruct (IHvs ws Hs) as (-> & -> & ->). auto.
Qed.

Local Lemma fill_item_unique K J e f :
  ¬ is_val e -> ¬ is_val f -> fill_item K e = fill_item J f -> K = J /\ e = f.
Proof.
  intros He Hf Hfill. destruct K, J; simpl in Hfill; try discriminate;
    try solve [inversion Hfill; subst; auto];
    try solve [inversion Hfill; subst; exfalso; first [exact (He I)|exact (Hf I)]].
  inversion Hfill. subst.
  match goal with
  | H : (Val <$> _) ++ _ :: _ = (Val <$> _) ++ _ :: _ |- _ =>
      destruct (call_argument_unique _ _ _ _ _ _ He Hf H) as (-> & -> & ->); auto
  end.
Qed.

Local Lemma locs_list_cons {A} `{Location A} (v : A) (vs : list A) :
  locs (v :: vs) = locs v ∪ locs vs.
Proof.
  change (⋃ (locs <$> v :: vs) = locs v ∪ ⋃ (locs <$> vs)).
  now rewrite fmap_cons, union_list_cons.
Qed.

Local Lemma head_origins_extend σ α G t e σ' α' e' :
  head_step G t σ α e σ' α' e' -> α ⊆ α'.
Proof.
  intros Hstep. destruct Hstep; subst; try reflexivity;
    apply insert_subseteq, not_elem_of_dom; assumption.
Qed.

Local Lemma graph_upd_include (G : graph) t ts : G ⊆ graph_upd G t ts.
Proof. unfold graph_upd. set_solver. Qed.

Local Lemma graph_upd_reach (G : graph) t ts u :
  u ∈ ts -> reachable (graph_upd G t ts) t u.
Proof.
  intros H. apply rtc_once. unfold edge, graph_upd, edges.
  apply elem_of_union_l, elem_of_map. exists u. auto.
Qed.

Local Lemma reach_mono (G G' : graph) t u : G ⊆ G' -> reachable G t u -> reachable G' t u.
Proof.
  intros HG Hreach. induction Hreach; [apply rtc_refl|].
  eapply rtc_l; [apply HG; eassumption|eassumption].
Qed.

Local Definition frontier_forward (G : graph) (T T' : task_tree) :=
  forall u, u ∈ frontier T' -> exists t, t ∈ frontier T /\ reachable G t u.

Local Lemma frontier_forward_refl (G : graph) T : frontier_forward G T T.
Proof. intros t Ht. exists t. split; [exact Ht|apply rtc_refl]. Qed.

Local Lemma sched_access_extension σ α G T e σ' α' G' T' e' :
  sched_step σ α G T e σ' α' G' T' e' ->
  G ⊆ G' /\ α ⊆ α' /\ frontier_forward G' T T'.
Proof.
  intros Hsched. destruct Hsched; subst.
  - split; [reflexivity|]. split; [eapply head_origins_extend; eassumption|apply frontier_forward_refl].
  - split; [apply graph_upd_include|]. split; [reflexivity|].
    intros u Hu. exists t0. split; [apply elem_of_singleton; reflexivity|].
    apply graph_upd_reach. exact Hu.
  - split.
    + unfold graph_join. etransitivity; apply graph_upd_include.
    + split; [apply insert_subseteq, not_elem_of_dom; assumption|].
      intros u Hu. cbn [frontier] in Hu. apply elem_of_singleton in Hu. subst u.
      exists t2. split; [simpl; set_solver|apply graph_upd_reach; set_solver].
Qed.

Local Lemma step_access_extension σ α G T e σ' α' G' T' e' :
  semantics.step σ α G T e σ' α' G' T' e' ->
  G ⊆ G' /\ α ⊆ α' /\ frontier_forward G' T T'.
Proof.
  intros Hstep. induction Hstep.
  - eapply sched_access_extension. exact H.
  - exact IHHstep.
  - destruct IHHstep as (HG & Hα & HT). split; [exact HG|]. split; [exact Hα|].
    intros u Hu. simpl in *. apply elem_of_union in Hu. destruct Hu as [Hu|Hu].
    + destruct (HT u Hu) as (s & Hs & Hsu). exists s. split; [set_solver|exact Hsu].
    + exists u. split; [set_solver|apply rtc_refl].
  - destruct IHHstep as (HG & Hα & HT). split; [exact HG|]. split; [exact Hα|].
    intros u Hu. simpl in *. apply elem_of_union in Hu. destruct Hu as [Hu|Hu].
    + exists u. split; [set_solver|apply rtc_refl].
    + destruct (HT u Hu) as (s & Hs & Hsu). exists s. split; [set_solver|exact Hsu].
Qed.

Local Lemma step_nonvalue σ α G T e σ' α' G' T' e' :
  semantics.step σ α G T e σ' α' G' T' e' -> ¬ is_val e.
Proof.
  intros Hstep. destruct Hstep.
  - destruct H; [destruct H; try destruct b| |]; exact (fun H => H).
  - apply fill_item_nonvalue.
  - exact (fun H => H).
  - exact (fun H => H).
Qed.

Local Lemma disentangled_fill (G : graph) (α : amap) T K e :
  disentangled G α T e ->
  set_Forall (fun t => all_abef G α t (locs K)) (frontier T) ->
  disentangled G α T (fill_item K e).
Proof.
  intros Hde HK. destruct T as [t|t T1 T2]; [|now apply DEBind].
  inversion Hde; subst. apply DELeaf. rewrite locs_fill_item.
  intros l Hl. apply elem_of_union in Hl. destruct Hl as [Hl|Hl]; [|auto].
  apply HK; [apply elem_of_singleton; reflexivity|exact Hl].
Qed.

(* Canonical forms for expressions at the active position of a task. *)
Inductive head_ready (σ : store) : expr -> Prop :=
| ReadyIf (b : bool) e1 e2 : head_ready σ (If b e1 e2)
| ReadyLet x (v : val) e : head_ready σ (Let x v e)
| ReadyCode self args code vs :
    length args = length vs -> locs code = ∅ ->
    head_ready σ (Call (VCode (Lam self args code)) (Val <$> vs))
| ReadyCall l self args code vs :
    σ !! l = Some (SClo self args code) -> length args = length vs ->
    head_ready σ (Call (VLoc l) (Val <$> vs))
| ReadyEq (v w : val) : head_ready σ (CallPrim PrimEq v w)
| ReadyBool op (v w : bool) : head_ready σ (CallPrim (PrimBoolOp op) v w)
| ReadyInt op (v w : Z) : head_ready σ (CallPrim (PrimIntOp op) v w)
| ReadyCmp op (v w : Z) : head_ready σ (CallPrim (PrimIntCmp op) v w)
| ReadyClo self args code : head_ready σ (Clo (Lam self args code))
| ReadyAlloc (n : Z) (v : val) : head_ready σ (Alloc n v)
| ReadyLoad l (i : Z) vs :
    σ !! l = Some (SBlock vs) -> head_ready σ (Load (VLoc l) i)
| ReadyStore l (i : Z) (v : val) vs :
    σ !! l = Some (SBlock vs) -> head_ready σ (Store (VLoc l) i v)
| ReadyCAS l (i : Z) (v w : val) vs :
    σ !! l = Some (SBlock vs) -> head_ready σ (CAS (VLoc l) i v w)
| ReadyLength l vs :
    σ !! l = Some (SBlock vs) -> head_ready σ (Length (VLoc l))
| ReadyProd (v w : val) : head_ready σ (Prod v w)
| ReadyProj (b : bool) l v w :
    σ !! l = Some (SProd v w) -> head_ready σ (if b then Fst (VLoc l) else Snd (VLoc l))
| ReadyFold (v : val) : head_ready σ (Fold v)
| ReadyUnfold (v : val) : head_ready σ (Unfold (VFold v))
| ReadyIn (b : bool) (v : val) : head_ready σ (if b then InL v else InR v)
| ReadyCase (b : bool) l v w x lhs y rhs :
    σ !! l = Some (if b then SInL v else SInR w) ->
    head_ready σ (Case (VLoc l) x lhs y rhs).

Local Lemma lookup_in_bounds (vs : list val) i :
  (0 <= i < Z.of_nat (length vs))%Z -> exists v, vs !! Z.to_nat i = Some v.
Proof.
  intros [Hlower Hupper]. apply lookup_lt_is_Some_2.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id by exact Hlower. exact Hupper.
Qed.

Local Lemma head_ready_reducible σ α G t e :
  head_ready σ e -> reducible true σ α G (Leaf t) e.
Proof.
  destruct 1.
  - eapply reduce_head. apply HeadIf.
  - eapply reduce_head. apply HeadLet.
  - eapply reduce_head. eapply HeadCall; [reflexivity|now rewrite length_fmap|assumption].
  - eapply reduce_head. eapply HeadCallClo; [eassumption|reflexivity|now rewrite length_fmap].
  - eapply reduce_head. apply HeadCallPrim. reflexivity.
  - eapply reduce_head. apply HeadCallPrim. reflexivity.
  - eapply reduce_head. apply HeadCallPrim. reflexivity.
  - eapply reduce_head. apply HeadCallPrim. reflexivity.
  - fresh_source_location σ α. eapply reduce_head. eapply HeadFunc; eauto.
  - destruct (decide (0 < n)%Z) as [Hyes|Hno].
    + fresh_source_location σ α. eapply reduce_head. eapply HeadAlloc; eauto.
    + apply RedOOB, OOBAlloc, Hno.
  - destruct (decide (0 <= i < Z.of_nat (length vs))%Z) as [Hyes|Hno].
    + destruct (lookup_in_bounds vs i Hyes) as [v Hv].
      eapply reduce_head. eapply HeadLoad; eassumption.
    + apply RedOOB. eapply OOBLoad; eassumption.
  - destruct (decide (0 <= i < Z.of_nat (length vs))%Z) as [Hyes|Hno].
    + eapply reduce_head. eapply HeadStore; [eassumption|eassumption|reflexivity].
    + apply RedOOB. eapply OOBStore; eassumption.
  - destruct (decide (0 <= i < Z.of_nat (length vs))%Z) as [Hyes|Hno].
    + destruct (lookup_in_bounds vs i Hyes) as [v0 Hv].
      eapply reduce_head. eapply HeadCAS; [eassumption|eassumption|eassumption|reflexivity].
    + apply RedOOB. eapply OOBCAS; eassumption.
  - eapply reduce_head. eapply HeadLength; eassumption.
  - fresh_source_location σ α. eapply reduce_head. eapply HeadProd; eauto.
  - eapply reduce_head. eapply (HeadProj b); eassumption.
  - eapply reduce_head. apply HeadFold.
  - eapply reduce_head. apply HeadUnfoldFold.
  - fresh_source_location σ α. eapply reduce_head. eapply (HeadIn b); eauto.
  - eapply reduce_head. eapply (HeadCase b); eassumption.
Qed.

Inductive runtime_ready (σ : store) : task_tree -> expr -> Prop :=
| ReadyValue t (v : val) : runtime_ready σ (Leaf t) v
| ReadyHead t e : head_ready σ e -> runtime_ready σ (Leaf t) e
| ReadyFork t (v w : val) : runtime_ready σ (Leaf t) (Par v w)
| ReadyContext T K e :
    ¬ is_val e -> runtime_ready σ T e -> runtime_ready σ T (fill_item K e)
| ReadyParallel t T1 T2 e1 e2 :
    runtime_ready σ T1 e1 -> runtime_ready σ T2 e2 ->
    runtime_ready σ (Node t T1 T2) (RunPar e1 e2).

Local Lemma reducible_nonvalue b σ α G T e : reducible b σ α G T e -> ¬ is_val e.
Proof.
  destruct 1.
  - eapply step_nonvalue. apply StepHead. eassumption.
  - destruct H; exact (fun H => H).
  - apply fill_item_nonvalue.
  - exact (fun H => H).
Qed.

Local Lemma safe_runpar σ α G t T1 T2 e1 e2 :
  safe true σ α G T1 e1 -> safe true σ α G T2 e2 ->
  safe true σ α G (Node t T1 T2) (RunPar e1 e2).
Proof.
  intros [[Hv1 HL1]|HR1] [[Hv2 HL2]|HR2]; right.
  - destruct T1 as [t1|]; [|exfalso; exact HL1].
    destruct T2 as [t2|]; [|exfalso; exact HL2].
    apply value_form in Hv1 as [v1 ->]. apply value_form in Hv2 as [v2 ->].
    fresh_source_location σ α. eapply RedSched. eapply SchedJoin; eauto.
  - eapply RedPar; [right; eapply reducible_nonvalue; eassumption|contradiction|auto].
  - eapply RedPar; [left; eapply reducible_nonvalue; eassumption|auto|contradiction].
  - eapply RedPar; [left; eapply reducible_nonvalue; eassumption|auto|auto].
Qed.

Local Lemma runtime_ready_safe σ α G T e : runtime_ready σ T e -> safe true σ α G T e.
Proof.
  induction 1.
  - left. split; exact I.
  - right. now apply head_ready_reducible.
  - right.
    pose (u := fresh (vertices G)).
    pose (w' := fresh ({[u]} ∪ vertices G)).
    pose proof (is_fresh (vertices G)) as Hu.
    pose proof (is_fresh ({[u]} ∪ vertices G)) as Hw.
    fold u in Hu. fold w' in Hw.
    eapply RedSched. eapply (SchedFork σ α G (graph_fork G t u w') t u w' v w).
    + exact Hu.
    + intros Hmem. apply Hw, elem_of_union_r, Hmem.
    + intros Heq. apply Hw, elem_of_union_l, elem_of_singleton. exact (eq_sym Heq).
    + reflexivity.
  - right. destruct IHruntime_ready as [[Hv _]|Hred]; [contradiction|].
    exact (RedCtx true σ α G T e K Hred).
  - now apply safe_runpar.
Qed.

(* Interpreting symbolic constraints in an allocation graph. *)
Local Definition clock_assignment := stimestamp -> timestamp.

Local Definition clock_constraints (G : graph) (η : clock_assignment) (Δ : constraints) :=
  forall x y, (x,y) ∈ Δ -> reachable G (η x) (η y).

Local Lemma clock_reachable G η Δ x y :
  clock_constraints G η Δ -> reachable Δ x y -> reachable G (η x) (η y).
Proof.
  intros HΔ Hr. induction Hr as [x|x y z Hxy Hyz IH]; [apply rtc_refl|].
  unfold reachable in *. etransitivity; [apply HΔ, Hxy|exact IH].
Qed.

Local Lemma clock_constraints_substitute G η Δ m :
  clock_constraints G η (tsubst_constraints m Δ) <->
  clock_constraints G (fun x => η (find_opt m x)) Δ.
Proof.
  unfold clock_constraints, tsubst_constraints. split.
  - intros H x y Hxy. apply H, elem_of_map_2_alt with (x:=(x,y)); [exact Hxy|reflexivity].
  - intros H x y Hxy. apply elem_of_map_1 in Hxy as [[u v] [Heq Huv]].
    injection Heq as -> ->. now apply H.
Qed.

Local Lemma clock_constraints_union G η Δ Δ' :
  clock_constraints G η (Δ ∪ Δ') <->
  clock_constraints G η Δ /\ clock_constraints G η Δ'.
Proof.
  split.
  - intros H. split; intros x y Hmem; apply H; set_solver.
  - intros [H H'] x y Hmem. apply elem_of_union in Hmem as [Hmem|Hmem]; auto.
Qed.

Local Lemma clock_all_reachable G η Δ Δ' :
  clock_constraints G η Δ -> all_reachable Δ Δ' -> clock_constraints G η Δ'.
Proof.
  intros HΔ HΔ' x y Hxy. eapply clock_reachable; [exact HΔ|exact (HΔ' (x,y) Hxy)].
Qed.

Local Lemma clock_constraints_ext G η θ Δ :
  (forall x y, (x,y) ∈ Δ -> η x = θ x /\ η y = θ y) ->
  (clock_constraints G η Δ <-> clock_constraints G θ Δ).
Proof.
  intros Heq. split; intros H x y Hxy; destruct (Heq x y Hxy) as [Hx Hy].
  - rewrite <-Hx, <-Hy. now apply H.
  - rewrite Hx, Hy. now apply H.
Qed.

Local Definition clock_extend (η : clock_assignment) (m : gmap stimestamp timestamp) : clock_assignment :=
  fun x => default (η x) (m !! x).

Local Lemma binder_lookup_delete {A} (m : gmap string A) b x :
  bdelete b m !! x = if decide (x ∈ binder_set b) then None else m !! x.
Proof.
  destruct b as [|y]; simpl.
  - destruct (decide (x ∈ (∅ : gset string))); [set_solver|reflexivity].
  - destruct (decide (x ∈ ({[y]} : gset string))) as [Hxy|Hxy].
    + apply elem_of_singleton in Hxy. subst x. apply lookup_delete_eq.
    + apply lookup_delete_ne. set_solver.
Qed.

Local Lemma binders_set_cons b bs : binders_set (b :: bs) = binder_set b ∪ binders_set bs.
Proof. unfold binders_set. now rewrite fmap_cons, union_list_cons. Qed.

Local Lemma extend_cons {A} b bs (v : A) vs m :
  extend (b :: bs) (v :: vs) m = extend bs vs (binsert b v m).
Proof. unfold extend, binserts. simpl. now rewrite foldr_app. Qed.

Local Lemma dom_extend {A} bs (vs : list A) m :
  length bs = length vs -> dom (extend bs vs m) = binders_set bs ∪ dom m.
Proof.
  revert vs m. induction bs as [|b bs IH]; intros [|v vs] m Hlen; try discriminate.
  - change (dom m = (∅ : gset string) ∪ dom m). set_solver.
  - rewrite extend_cons, IH by (simpl in Hlen; congruence).
    rewrite binders_set_cons. destruct b as [|b]; cbn [binsert binder_set]; [set_solver|].
    rewrite dom_insert_L. set_solver.
Qed.

Local Lemma dom_bmap {A} bs (vs : list A) :
  length bs = length vs -> dom (bmap bs vs) = binders_set bs.
Proof. intros Hlen. unfold bmap. rewrite dom_extend by exact Hlen. rewrite dom_empty_L. set_solver. Qed.

Local Lemma extend_fmap {A B} (f : A -> B) bs (vs : list A) (m : gmap string A) :
  f <$> extend bs vs m = extend bs (f <$> vs) (f <$> m).
Proof.
  revert vs m. induction bs as [|b bs IH]; intros [|v vs] m; try reflexivity.
  rewrite fmap_cons, !extend_cons, IH. destruct b as [|b]; [reflexivity|].
  cbn [binsert]. now rewrite fmap_insert.
Qed.

Local Lemma clock_extend_actuals η bs δs x :
  clock_extend η (bmap bs (η <$> δs)) x = η (find_opt (bmap bs δs) x).
Proof.
  assert (Hmap : bmap bs (η <$> δs) = η <$> bmap bs δs).
  { unfold bmap. now rewrite extend_fmap, fmap_empty. }
  unfold clock_extend, find_opt. rewrite Hmap, lookup_fmap.
  assert (Hoption : forall o : option stimestamp, default (η x) (η <$> o) = η (default x o)).
  { intros [u|]; reflexivity. }
  apply Hoption.
Qed.

Local Lemma clock_fork_constraint (G : graph) η δ δ' t1 t2 :
  let t0 := η δ in
  clock_constraints (graph_fork G t0 t1 t2) (clock_extend η {[δ':=t1]}) {[(δ,δ')]}.
Proof.
  cbn. intros x y Hxy. apply elem_of_singleton in Hxy. injection Hxy as -> ->.
  unfold clock_extend. rewrite lookup_singleton_eq. simpl.
  destruct (decide (δ = δ')) as [->|Hne].
  - rewrite lookup_singleton_eq. apply rtc_refl.
  - rewrite lookup_singleton_ne by congruence. apply graph_upd_reach. set_solver.
Qed.

Local Lemma binders_lookup_delete {A} (m : gmap string A) bs x :
  bdeletes bs m !! x = if decide (x ∈ binders_set bs) then None else m !! x.
Proof.
  induction bs as [|b bs IH]; simpl.
  - destruct (decide (x ∈ binders_set [])) as [H|H]; [exfalso|reflexivity].
    change (x ∈ (∅ : gset string)) in H. set_solver.
  - rewrite binder_lookup_delete, IH, binders_set_cons.
    destruct (decide (x ∈ binder_set b)), (decide (x ∈ binders_set bs)),
             (decide (x ∈ binder_set b ∪ binders_set bs)); try reflexivity; set_solver.
Qed.

Local Lemma clock_extension_substitute η m (f : gmap stimestamp timestamp) bs :
  dom f = binders_set bs ->
  (forall x y, m !! x = Some y -> y ∉ binders_set bs) ->
  forall x, clock_extend (fun z => η (find_opt m z)) f x =
    clock_extend η f (find_opt (bdeletes bs m) x).
Proof.
  intros Hf Hm x. change ((dom f : gset stimestamp) = binders_set bs) in Hf.
  destruct (decide (x ∈ binders_set bs)) as [Hx|Hx].
  - replace (find_opt (bdeletes bs m) x) with x.
    2: { unfold find_opt. rewrite binders_lookup_delete, decide_True by exact Hx. reflexivity. }
    unfold clock_extend. destruct (f !! x) as [u|] eqn:Hlookup; [reflexivity|].
    exfalso. pose proof (proj2 (not_elem_of_dom f x) Hlookup) as Hndom.
    apply Hndom. now rewrite Hf.
  - replace (find_opt (bdeletes bs m) x) with (find_opt m x).
    2: { unfold find_opt. rewrite binders_lookup_delete, decide_False by exact Hx. reflexivity. }
    unfold clock_extend. assert (Hfx : f !! x = None) by (apply not_elem_of_dom; now rewrite Hf).
    rewrite Hfx. unfold find_opt. destruct (m !! x) as [y|] eqn:Hmxy; simpl.
    + rewrite (proj1 (not_elem_of_dom f y)); [reflexivity|rewrite Hf; eauto].
    + now rewrite Hfx.
Qed.

Local Definition clock_bind (η : clock_assignment) b u : clock_assignment :=
  fun x => if decide (x ∈ binder_set b) then u else η x.

Local Lemma clock_bind_extend η b u x :
  clock_bind η b u x = clock_extend η (binsert b u ∅) x.
Proof.
  destruct b as [|y]; unfold clock_bind, clock_extend; simpl.
  - rewrite lookup_empty. destruct (decide (x ∈ (∅ : gset string))); [set_solver|reflexivity].
  - destruct (decide (x ∈ ({[y]} : gset string))) as [Hxy|Hxy].
    + apply elem_of_singleton in Hxy. subst x. now rewrite lookup_insert_eq.
    + rewrite lookup_insert_ne, lookup_empty by set_solver. reflexivity.
Qed.

Local Lemma clock_bind_singleton η x δ z :
  clock_bind η (BNamed x) (η δ) z = η (find_opt {[x:=δ]} z).
Proof.
  rewrite clock_bind_extend. unfold clock_extend, find_opt. simpl.
  destruct (decide (x = z)) as [->|Hne].
  - now rewrite lookup_insert_eq, lookup_singleton_eq.
  - now rewrite lookup_insert_ne, lookup_singleton_ne, lookup_empty.
Qed.

(* A heap view retains the immutable contents of cells and the size of each
   mutable block. A level adds specifications for block elements. *)
Local Definition cell_view (s : storable) : nat + storable :=
  match s with SBlock vs => inl (length vs) | _ => inr s end.

Local Definition heap_view := gmap loc (timestamp * (nat + storable)).

Local Fixpoint resource (n : nat) : Type :=
  match n with
  | O => heap_view
  | S n => (resource n * gmap loc (resource n -> val -> Prop))%type
  end.

Local Fixpoint resource_view (n : nat) : resource n -> heap_view :=
  match n with O => fun W => W | S n => fun W => resource_view n (fst W) end.

Local Fixpoint resource_extends (n : nat) : resource n -> resource n -> Prop :=
  match n with
  | O => fun W W' : heap_view => W ⊆ W'
  | S n => fun W W' : resource n * gmap loc (resource n -> val -> Prop) =>
      resource_extends n (fst W) (fst W') /\ snd W ⊆ snd W'
  end.

Local Lemma resource_view_extends n (W W' : resource n) :
  resource_extends n W W' -> resource_view n W ⊆ resource_view n W'.
Proof. induction n; simpl; [auto|intros [H _]; auto]. Qed.

Local Definition view_matches (V : heap_view) (σ : store) (α : amap) :=
  (forall l s, σ !! l = Some s -> exists t, α !! l = Some t /\ V !! l = Some (t, cell_view s)) /\
  (forall l t d, V !! l = Some (t,d) -> α !! l = Some t /\
    exists s, σ !! l = Some s /\ cell_view s = d).

Local Definition element_spec := forall n, resource n -> val -> Prop.

Local Definition element_mono_at n (P : resource n -> val -> Prop) : Prop :=
  forall W V v, resource_extends n W V -> P W v -> P V v.

Local Definition element_monotone (E : element_spec) : Prop := forall n, element_mono_at n (E n).

Local Fixpoint elements_fit n : resource n -> element_spec -> list val -> Prop :=
  match n with
  | O => fun _ _ _ => True
  | S n => fun W E vs => elements_fit n (fst W) E vs /\ Forall (E n (fst W)) vs
  end.

Local Fixpoint array_spec_at (n : nat) : resource n -> loc -> element_spec -> Prop :=
  match n with
  | O => fun _ _ _ => True
  | S n => fun W l E =>
      array_spec_at n (fst W) l E /\
      exists P, (snd W) !! l = Some P /\ forall A v, P A v <-> E n A v
  end.

Local Fixpoint store_spec_at (n : nat) : resource n -> store -> amap -> Prop :=
  match n with
  | O => fun W σ α => view_matches W σ α
  | S n => fun W σ α =>
      store_spec_at n (fst W) σ α /\
      (forall l vs, σ !! l = Some (SBlock vs) ->
        exists P, (snd W) !! l = Some P /\ Forall (P (fst W)) vs) /\
      (forall l P, (snd W) !! l = Some P ->
        (exists vs, σ !! l = Some (SBlock vs)) /\ element_mono_at n P)
  end.

Local Lemma store_spec_view n (W : resource n) σ α :
  store_spec_at n W σ α -> view_matches (resource_view n W) σ α.
Proof. induction n; simpl; [auto|intros [H _]; auto]. Qed.

Local Definition value_visible_in_view (G : graph) (V : heap_view) t (v : val) :=
  forall l, l ∈ locs v -> exists u d, V !! l = Some (u,d) /\ reachable G u t.

Local Lemma value_view_access G V σ α t v :
  view_matches V σ α -> value_visible_in_view G V t v -> all_abef G α t (locs v).
Proof.
  intros [_ Hmatch] Hv l Hl. destruct (Hv l Hl) as (u & d & Hlookup & Hreach).
  destruct (Hmatch l u d Hlookup) as [Hα _]. unfold abef. now rewrite Hα.
Qed.

Local Lemma array_load_spec n (W : resource (S n)) σ α l vs (E : element_spec) i v :
  store_spec_at (S n) W σ α -> array_spec_at (S n) W l E ->
  σ !! l = Some (SBlock vs) -> vs !! i = Some v -> E n (fst W) v.
Proof.
  simpl. intros [_ [Hσ _]] [_ (P & HP & Hagree)] Hl Hv.
  specialize (Hσ l vs Hl) as (R & HR & Hvals).
  pose proof (eq_trans (eq_sym HP) HR) as Heq. injection Heq as <-.
  apply (Hagree (fst W) v).
  rewrite Forall_forall in Hvals. apply Hvals. eapply list_elem_of_lookup_2; eassumption.
Qed.

Local Lemma store_replacement_view V σ α l (vs : list val) i (v : val) :
  σ !! l = Some (SBlock vs) -> view_matches V σ α ->
  view_matches V (<[l := SBlock (<[i := v]> vs)]> σ) α.
Proof.
  intros Hl [Hdom Hview]. split.
  - intros k s Hs. apply lookup_insert_Some in Hs as [(Heq & Hblock)|(_ & Hs)].
    + subst k s. specialize (Hdom l _ Hl) as (t & Ht & Hmatch).
      exists t. split; [exact Ht|]. simpl in *. now rewrite length_insert.
    + eauto.
  - intros k t d Hk. destruct (Hview k t d Hk) as [Ht (s & Hs & Hd)].
    split; [exact Ht|]. destruct (decide (l = k)) as [Heq|Hne].
    + subst k. exists (SBlock (<[i := v]> vs)). split; [apply lookup_insert_eq|].
      rewrite Hl in Hs. injection Hs as <-. simpl in *. now rewrite length_insert.
    + exists s. split; [rewrite lookup_insert_ne by done; exact Hs|exact Hd].
Qed.

Local Lemma store_replacement_spec n (W : resource n) (E : element_spec) σ α l vs i v :
  store_spec_at n W σ α -> array_spec_at n W l E ->
  elements_fit n W E [v] ->
  σ !! l = Some (SBlock vs) ->
  store_spec_at n W (<[l := SBlock (<[i := v]> vs)]> σ) α.
Proof.
  induction n; simpl; intros Hσ HE Hv Hl.
  - eapply store_replacement_view; eassumption.
  - destruct Hσ as (Hprev & Harrays & Hregistry). destruct HE as [HEprev (P & HP & Hagree)].
    destruct Hv as [Hvprev Hv]. split.
    + eapply IHn; eassumption.
    + split.
      * intros k ws Hk. apply lookup_insert_Some in Hk as [(Heq & Hws)|(_ & Hk)].
        -- subst k. injection Hws as <-. destruct (Harrays l vs Hl) as (R & HR & Hvals).
           pose proof (eq_trans (eq_sym HP) HR) as Heq. injection Heq as <-.
           exists P. split; [exact HP|].
           apply Forall_insert; [exact Hvals|apply (Hagree (fst W) v); now inversion Hv].
        -- eauto.
      * intros k R HR. destruct (Hregistry k R HR) as [(ws & Hws) Hmono].
        split; [|exact Hmono]. destruct (decide (l = k)) as [Heq|Hne].
        -- subst k. eexists. apply lookup_insert_eq.
        -- exists ws. rewrite lookup_insert_ne by done. exact Hws.
Qed.

Local Fixpoint resource_insert n l t s (E : element_spec) : resource n -> resource n :=
  match n with
  | O => fun W : heap_view => <[l := (t, cell_view s)]> W
  | S n => fun W =>
      (resource_insert n l t s E (fst W),
       match s with SBlock _ => <[l:=E n]> (snd W) | _ => snd W end)
  end.

Local Lemma resource_insert_view n (W : resource n) l t s E :
  resource_view n (resource_insert n l t s E W) = <[l := (t, cell_view s)]> (resource_view n W).
Proof. induction n; simpl; [reflexivity|apply IHn]. Qed.

Local Lemma registry_fresh n (W : resource (S n)) σ α l :
  store_spec_at (S n) W σ α -> σ !! l = None -> snd W !! l = None.
Proof.
  intros (_ & _ & Hreg) Hfresh. destruct (snd W !! l) as [P|] eqn:HP; [|reflexivity].
  destruct (Hreg l P HP) as [(vs & Hvs) _]. congruence.
Qed.

Local Lemma resource_insert_grows n (W : resource n) σ α l t s E :
  store_spec_at n W σ α -> σ !! l = None -> resource_extends n W (resource_insert n l t s E W).
Proof.
  induction n as [|n IH]; intros Hstore Hfresh.
  - cbn [resource_extends resource_insert]. apply insert_subseteq.
    destruct Hstore as [_ Hmatch]. destruct (W !! l) as [[u d]|] eqn:HV; [|exact HV].
    destruct (Hmatch l u d HV) as [_ (c & Hc & _)]. congruence.
  - cbn [resource_extends resource_insert]. split.
    + exact (IH (fst W) (proj1 Hstore) Hfresh).
    + destruct s; try reflexivity. apply insert_subseteq. eapply registry_fresh; eassumption.
Qed.

Local Lemma view_matches_insert W σ α l t s :
  view_matches W σ α ->
  view_matches (<[l := (t,cell_view s)]> W) (<[l:=s]> σ) (<[l:=t]> α).
Proof.
  intros [Hσ HW]. split.
  - intros k c Hc. apply lookup_insert_Some in Hc as [(Heq & Hs)|(Hne & Hc)].
    + subst k c. exists t. split; apply lookup_insert_eq.
    + destruct (Hσ k c Hc) as (u & Hα & Hv). exists u.
      split.
      * etransitivity; [apply lookup_insert_ne, Hne|exact Hα].
      * etransitivity; [apply lookup_insert_ne, Hne|exact Hv].
  - intros k u d Hv. apply lookup_insert_Some in Hv as [(Heq & Hcell)|(Hne & Hv)].
    + subst k. inversion Hcell; subst. split; [apply lookup_insert_eq|].
      exists s. split; [apply lookup_insert_eq|reflexivity].
    + destruct (HW k u d Hv) as [Hα (c & Hc & Hshape)].
      rewrite lookup_insert_ne by exact Hne. split; [exact Hα|].
      exists c. rewrite lookup_insert_ne by exact Hne. exact (conj Hc Hshape).
Qed.

Local Lemma resource_insert_lookup n (W : resource (S n)) l t s E k :
  snd (resource_insert (S n) l t s E W) !! k =
  match s with
  | SBlock _ => if decide (l = k) then Some (E n) else snd W !! k
  | _ => snd W !! k
  end.
Proof. destruct s; cbn [resource_insert]; try reflexivity. apply lookup_insert. Qed.

Local Lemma resource_insert_store n (W : resource n) σ α l t s E :
  store_spec_at n W σ α -> σ !! l = None -> element_monotone E ->
  (forall vs, s = SBlock vs -> elements_fit n W E vs) ->
  store_spec_at n (resource_insert n l t s E W) (<[l:=s]> σ) (<[l:=t]> α).
Proof.
  induction n as [|n IH]; intros Hstore Hfresh Hmono Hvs.
  - now apply view_matches_insert.
  - pose proof (registry_fresh n W σ α l Hstore Hfresh) as Hregnone.
    pose proof (proj1 (resource_insert_grows (S n) W σ α l t s E Hstore Hfresh)) as Hext.
    destruct Hstore as (Hw & Hblocks & Hreg). split.
    + apply IH; [exact Hw|exact Hfresh|exact Hmono|].
      intros vs Heq. exact (proj1 (Hvs vs Heq)).
    + split.
      * intros k vs Hblock. apply lookup_insert_Some in Hblock as [(Heq & Hval)|(Hne & Hblock)].
        -- subst k s. exists (E n). rewrite resource_insert_lookup, decide_True by reflexivity.
           split; [reflexivity|]. pose proof (proj2 (Hvs vs eq_refl)) as Hfits.
           rewrite Forall_forall in *. intros v Hv. eapply Hmono; [exact Hext|now apply Hfits].
        -- destruct (Hblocks k vs Hblock) as (P & HP & Hfits).
           destruct (Hreg k P HP) as [_ HmonoP]. exists P. split.
           ++ rewrite resource_insert_lookup. destruct s; [now rewrite decide_False|assumption..].
           ++ rewrite Forall_forall in *. intros v Hv. eapply HmonoP; [exact Hext|now apply Hfits].
      * intros k P HP. rewrite resource_insert_lookup in HP.
        destruct (decide (l = k)) as [Heq|Hne].
        -- subst k. destruct s as [vs| | | |];
             try solve [pose proof (eq_trans (eq_sym Hregnone) HP) as Hbad; discriminate Hbad].
           injection HP as HeqP. subst P. split; [exists vs; apply lookup_insert_eq|exact (Hmono n)].
        -- assert (Hold : snd W !! k = Some P) by (destruct s; exact HP).
           destruct (Hreg k P Hold) as [(vs & Hlookup) HmonoP].
           split; [exists vs; now rewrite lookup_insert_ne|exact HmonoP].
Qed.

Local Lemma resource_insert_array n (W : resource n) l t vs E :
  array_spec_at n (resource_insert n l t (SBlock vs) E W) l E.
Proof.
  induction n as [|n IH]; [exact I|]. split; [apply IH|]. exists (E n).
  split; [apply lookup_insert_eq|tauto].
Qed.

Local Lemma resource_extends_refl n (W : resource n) : resource_extends n W W.
Proof. induction n; simpl; [reflexivity|split; [apply IHn|reflexivity]]. Qed.

Local Lemma resource_extends_trans n (W W' W'' : resource n) :
  resource_extends n W W' -> resource_extends n W' W'' -> resource_extends n W W''.
Proof.
  induction n; simpl; [etransitivity; eassumption|].
  intros [H1 H2] [H3 H4]. split; [eapply IHn|etransitivity]; eassumption.
Qed.

Local Definition result_spec_at n (W : resource n) (T : task_tree) e (Q : element_spec) :=
  match e with Val v => is_leaf T /\ Q n W v | _ => True end.

(* Each bounded specification quantifies over later heap views of that level.
   The final graph is fixed throughout a trace since all of its edges persist. *)
Local Fixpoint expression_spec (n : nat) (F : graph) :
    resource n -> task_tree -> expr -> element_spec -> Prop :=
  match n with
  | O => fun _ _ _ _ => True
  | S n => fun W T e Q =>
      expression_spec n F (fst W) T e Q /\
      forall (W' : resource (S n)) σ α G,
        resource_extends (S n) W W' -> store_spec_at (S n) W' σ α -> G ⊆ F ->
        safe true σ α G T e /\ disentangled F α T e /\ result_spec_at (S n) W' T e Q /\
        forall σ' α' G' T' e',
          semantics.step σ α G T e σ' α' G' T' e' -> G' ⊆ F ->
          exists W'' : resource n, resource_extends n (fst W') W'' /\
            store_spec_at n W'' σ' α' /\ expression_spec n F W'' T' e' Q
  end.

Local Lemma expression_spec_extend n F (W W' : resource n) T e Q :
  resource_extends n W W' -> expression_spec n F W T e Q -> expression_spec n F W' T e Q.
Proof.
  induction n as [|n IH]; cbn [expression_spec resource_extends]; [tauto|].
  intros [Hext Htables] [Hprev Hnow]. split; [eapply IH; eassumption|].
  intros W'' σ α G Hmore Hw HG. eapply Hnow; [|exact Hw|exact HG].
  eapply (resource_extends_trans (S n)); [split; eassumption|exact Hmore].
Qed.

Local Lemma expression_spec_post n F (W : resource n) T e (Q R : element_spec) :
  (forall k (V : resource k) v, Q k V v -> R k V v) ->
  expression_spec n F W T e Q -> expression_spec n F W T e R.
Proof.
  revert W T e. induction n as [|n IH]; intros W T e Hpost; cbn [expression_spec]; [auto|].
  intros [Hprev Hnow]. split; [now apply IH|].
  intros W' σ α G Hext Hstore HG.
  destruct (Hnow W' σ α G Hext Hstore HG) as (Hsafe & Hde & Hval & Hnext).
  split; [exact Hsafe|]. split; [exact Hde|]. split.
  - destruct e; simpl in *; try exact I. destruct Hval as [Hleaf Hv]. split; [exact Hleaf|now apply Hpost].
  - intros σ' α' G' T' e' Hstep Hgraph.
    destruct (Hnext σ' α' G' T' e' Hstep Hgraph) as (W'' & Hext' & Hstore' & Hcont).
    exists W''. split; [exact Hext'|]. split; [exact Hstore'|now apply IH].
Qed.

Local Lemma expression_spec_value n F (W : resource n) t v (Q : element_spec) :
  (forall k (V : resource k), Q k V v -> value_visible_in_view F (resource_view k V) t v) ->
  (forall V : resource n, resource_extends n W V -> Q n V v) ->
  (forall k (V : resource (S k)), Q (S k) V v -> Q k (fst V) v) ->
  expression_spec n F W (Leaf t) v Q.
Proof.
  induction n as [|n IH]; intros Hvisible Hvalue Hdecrease; cbn [expression_spec]; [exact I|].
  split.
  - apply IH; [exact Hvisible| |exact Hdecrease].
    intros V HV. apply (Hdecrease n (V, snd W)). apply Hvalue.
    split; [exact HV|reflexivity].
  - intros W' σ α G Hext Hstore Hsub.
    specialize (Hvalue W' Hext). split; [left; split; exact I|]. split.
    + apply DELeaf. eapply value_view_access; [eapply store_spec_view; exact Hstore|].
      now apply Hvisible.
    + split; [split; [exact I|exact Hvalue]|].
      intros σ' α' G' T' e' Hstep _. exfalso. eapply step_nonvalue in Hstep. exact (Hstep I).
Qed.

Local Definition runtime_config := (store * amap * graph * task_tree * expr)%type.

Local Definition config_graph (c : runtime_config) := let '(_, _, G, _, _) := c in G.

Local Definition config_specification F Q (c : runtime_config) :=
  let '(σ, α, _, T, e) := c in
  forall n, exists W : resource n, store_spec_at n W σ α /\ expression_spec n F W T e Q.

Local Lemma step_graph_extends c c' : step c c' -> config_graph c ⊆ config_graph c'.
Proof.
  destruct c as [[[[σ α] G] T] e], c' as [[[[σ' α'] G'] T'] e'].
  intros Hstep. exact (proj1 (step_access_extension _ _ _ _ _ _ _ _ _ _ Hstep)).
Qed.

Local Lemma trace_graph_extends c c' : rtc step c c' -> config_graph c ⊆ config_graph c'.
Proof. induction 1; [reflexivity|etransitivity; [eapply step_graph_extends; eassumption|assumption]]. Qed.

Local Lemma config_specification_step F Q c c' :
  step c c' -> config_graph c' ⊆ F -> config_specification F Q c -> config_specification F Q c'.
Proof.
  destruct c as [[[[σ α] G] T] e], c' as [[[[σ' α'] G'] T'] e'].
  intros Hstep HG' Hcfg n. destruct (Hcfg (S n)) as (W & Hstore & Hsem).
  destruct Hsem as [_ Hhead].
  pose proof (step_graph_extends _ _ Hstep) as Hlink.
  assert (HG : G ⊆ F) by (etransitivity; [exact Hlink|exact HG']).
  specialize (Hhead W σ α G (resource_extends_refl (S n) W) Hstore HG) as (_ & _ & _ & Hnext).
  destruct (Hnext σ' α' G' T' e' Hstep HG') as (W' & _ & Hw & Hsem).
  now exists W'.
Qed.

Local Lemma config_specification_trace F Q c c' :
  rtc step c c' -> config_graph c' ⊆ F -> config_specification F Q c -> config_specification F Q c'.
Proof.
  induction 1; intros HF Hspec; [exact Hspec|]. apply IHrtc; [exact HF|].
  eapply config_specification_step; [eassumption| |exact Hspec].
  etransitivity; [eapply trace_graph_extends; eassumption|exact HF].
Qed.

Local Lemma expression_spec_adequacy Q c σ α G T e :
  config_specification G Q c -> rtc step c (σ, α, G, T, e) ->
  safe true σ α G T e /\ disentangled G α T e.
Proof.
  intros Hspec Htrace.
  assert (Hself : G ⊆ G) by reflexivity.
  pose proof (config_specification_trace G Q _ _ Htrace Hself Hspec) as Hfinal.
  destruct (Hfinal 1) as (W & Hw & [_ Hhead]).
  destruct (Hhead W σ α G (resource_extends_refl 1 W) Hw Hself) as (Hsafe & Hde & _).
  now split.
Qed.

Local Fixpoint empty_resource n : resource n :=
  match n with O => (∅ : heap_view) | S n => (empty_resource n, ∅) end.

Local Lemma empty_store_specification n : store_spec_at n (empty_resource n) ∅ ∅.
Proof.
  induction n as [|n IH].
  - split.
    + intros l s H. rewrite lookup_empty in H. discriminate.
    + intros l t d H. change ((∅ : heap_view) !! l = Some (t,d)) in H.
      unfold heap_view in H. rewrite lookup_empty in H. discriminate.
  - split; [exact IH|]. split.
    + intros l vs H. rewrite lookup_empty in H. discriminate.
    + intros l P H. change ((∅ : gmap loc (resource n -> val -> Prop)) !! l = Some P) in H.
      rewrite lookup_empty in H. discriminate.
Qed.

Local Lemma closed_expression_spec_adequacy e :
  (forall F t, exists Q, forall n, expression_spec n F (empty_resource n) (Leaf t) e Q) ->
  always_safe_and_disentangled true e.
Proof.
  intros Hclosed t σ α G T e' Htrace. destruct (Hclosed G t) as [Q HQ].
  eapply expression_spec_adequacy; [|exact Htrace].
  intros n. exists (empty_resource n). split; [apply empty_store_specification|apply HQ].
Qed.

Local Lemma head_context_value σ α G t e σ' α' e' :
  head_step G t σ α e σ' α' e' ->
  forall K f, fill_item K f = e -> is_val f.
Proof.
  intros Hstep. destruct Hstep; subst; try destruct b;
    intros K f He; destruct K; simpl in He; try discriminate;
    try solve [inversion He; subst; exact I].
  all: injection He as _ Hargs; assert (Hf : f ∈ Val <$> vs).
  all: try (rewrite <-Hargs; apply elem_of_app; right; constructor).
  all: apply list_elem_of_fmap in Hf as (? & -> & _); exact I.
Qed.

Local Lemma sched_context_value σ α G T e σ' α' G' T' e' :
  sched_step σ α G T e σ' α' G' T' e' ->
  forall K f, fill_item K f = e -> is_val f.
Proof.
  intros Hstep. destruct Hstep.
  - intros K f Hfill. eapply head_context_value; eassumption.
  - intros K f He. destruct K; simpl in He; try discriminate;
      inversion He; subst; exact I.
  - intros K f He. destruct K; discriminate.
Qed.

Local Lemma step_fill_invert σ α G T K e σ' α' G' T' f :
  ¬ is_val e -> semantics.step σ α G T (fill_item K e) σ' α' G' T' f ->
  exists e', semantics.step σ α G T e σ' α' G' T' e' /\ f = fill_item K e'.
Proof.
  intros Hnv Hstep. remember (fill_item K e) as original eqn:Heq.
  destruct Hstep.
  - exfalso. apply Hnv. eapply sched_context_value; [exact H|symmetry; exact Heq].
  - pose proof (step_nonvalue _ _ _ _ _ _ _ _ _ _ Hstep) as Hother.
    destruct (fill_item_unique _ _ _ _ Hnv Hother (eq_sym Heq)) as [-> ->]. eauto.
  - destruct K; discriminate Heq.
  - destruct K; discriminate Heq.
Qed.

Local Definition task_root (T : task_tree) : timestamp := match T with Leaf t | Node t _ _ => t end.

Local Fixpoint tree_paths (G : graph) (T : task_tree) : Prop :=
  match T with
  | Leaf _ => True
  | Node t T1 T2 => reachable G t (task_root T1) /\ reachable G t (task_root T2) /\
    tree_paths G T1 /\ tree_paths G T2
  end.

Local Lemma tree_paths_frontier G T u :
  tree_paths G T -> u ∈ frontier T -> reachable G (task_root T) u.
Proof.
  induction T as [t|t T1 IH1 T2 IH2]; simpl.
  - intros _ Hu. apply elem_of_singleton in Hu as ->. apply rtc_refl.
  - intros (H1 & H2 & HL & HR) Hu. apply elem_of_union in Hu as [Hu|Hu]; unfold reachable in *.
    + etransitivity; [exact H1|now apply IH1].
    + etransitivity; [exact H2|now apply IH2].
Qed.

Local Lemma step_tree_paths F σ α G T e σ' α' G' T' e' :
  semantics.step σ α G T e σ' α' G' T' e' -> G' ⊆ F -> tree_paths F T ->
  task_root T = task_root T' /\ tree_paths F T'.
Proof.
  intros Hstep. induction Hstep; intros HG HT; simpl in *.
  - destruct H; subst; simpl in *; try (split; [reflexivity|exact I]).
    split; [reflexivity|]. split.
    + eapply reach_mono; [exact HG|apply graph_upd_reach; set_solver].
    + split.
      * eapply reach_mono; [exact HG|apply graph_upd_reach; set_solver].
      * exact (conj I I).
  - now apply IHHstep.
  - destruct HT as (H1 & H2 & HL & HR). destruct (IHHstep HG HL) as [Heq HT].
    split; [reflexivity|]. rewrite <-Heq. auto.
  - destruct HT as (H1 & H2 & HL & HR). destruct (IHHstep HG HR) as [Heq HT].
    split; [reflexivity|]. rewrite <-Heq. auto.
Qed.

Local Fixpoint continuation_spec n F : resource n -> timestamp -> ctx -> element_spec -> element_spec -> Prop :=
  match n with
  | O => fun _ _ _ _ _ => True
  | S n => fun W t K Q R => continuation_spec n F (fst W) t K Q R /\
      forall (V : resource (S n)) v, resource_extends (S n) W V -> Q (S n) V v ->
        expression_spec (S n) F V (Leaf t) (fill_item K v) R
  end.

Local Lemma continuation_spec_extend n F (W V : resource n) t K Q R :
  resource_extends n W V -> continuation_spec n F W t K Q R -> continuation_spec n F V t K Q R.
Proof.
  induction n as [|n IH]; simpl; [auto|]. intros [Hnext Hmap] [Hlow Hhigh].
  split; [eapply IH; eassumption|]. intros V' v Hext Hval.
  apply Hhigh; [|exact Hval]. eapply (resource_extends_trans (S n)); [split; eassumption|eassumption].
Qed.

Local Definition context_support F (V : heap_view) t K :=
  forall l, l ∈ locs K -> exists u d, V !! l = Some (u,d) /\ reachable F u t.

Local Lemma context_support_extend F (V V' : heap_view) t K :
  V ⊆ V' -> context_support F V t K -> context_support F V' t K.
Proof.
  intros HV HK l Hl. destruct (HK l Hl) as (u & d & Hloc & Hreach).
  exists u, d. split; [eapply lookup_weaken; eassumption|exact Hreach].
Qed.

Local Lemma context_support_disentangled F V σ α T K :
  view_matches V σ α -> tree_paths F T -> context_support F V (task_root T) K ->
  set_Forall (fun t => all_abef F α t (locs K)) (frontier T).
Proof.
  intros [_ Hview] HT HK t Ht l Hl. destruct (HK l Hl) as (u & d & Hloc & Hreach).
  destruct (Hview l u d Hloc) as [Hα _]. unfold abef. rewrite Hα.
  pose proof (tree_paths_frontier F T t HT Ht) as Ht'. unfold reachable in *.
  etransitivity; eassumption.
Qed.

Local Lemma expression_spec_bind n F (W : resource n) T K e Q R :
  tree_paths F T -> context_support F (resource_view n W) (task_root T) K ->
  expression_spec n F W T e Q -> continuation_spec n F W (task_root T) K Q R ->
  expression_spec n F W T (fill_item K e) R.
Proof.
  revert W T e. induction n as [|n IH]; intros W T e Htree HK He Hcont;
    cbn [expression_spec] in *; [exact I|].
  destruct He as [He0 He1]. destruct Hcont as [Hcont0 Hcont1]. split.
  - eapply IH; eassumption.
  - intros V σ α G Hext Hstore HG.
    specialize (He1 V σ α G Hext Hstore HG) as (Hsafe & Hde & Hresult & Hstep).
    destruct (decide (is_val e)) as [Hval|Hnv].
    + apply value_form in Hval as [v ->]. destruct Hresult as [Hleaf Hv].
      destruct T as [t|]; [|exfalso; exact Hleaf].
      specialize (Hcont1 V v Hext Hv) as [_ Hnow].
      exact (Hnow V σ α G (resource_extends_refl (S n) V) Hstore HG).
    + split.
      * destruct Hsafe as [[Hv _]|Hr]; [contradiction|right].
        exact (RedCtx true σ α G T e K Hr).
      * split.
        -- apply disentangled_fill; [exact Hde|].
           eapply context_support_disentangled; [eapply store_spec_view; exact Hstore|exact Htree|].
           eapply context_support_extend; [eapply resource_view_extends; exact Hext|exact HK].
        -- split; [destruct K; exact I|].
           intros σ' α' G' T' f Hf HG'.
           destruct (step_fill_invert _ _ _ _ _ _ _ _ _ _ _ Hnv Hf) as (e' & Hbody & ->).
           destruct (Hstep σ' α' G' T' e' Hbody HG') as (V' & HV' & Hstore' & He').
           destruct (step_tree_paths _ _ _ _ _ _ _ _ _ _ _ Hbody HG' Htree) as [Hroot Htree'].
           exists V'. split; [exact HV'|]. split; [exact Hstore'|].
           assert (Hmove : resource_extends n (fst W) V').
           { eapply resource_extends_trans; [exact (proj1 Hext)|exact HV']. }
           eapply IH; [exact Htree'| |exact He'|].
           ++ rewrite <-Hroot. eapply context_support_extend;
                [eapply resource_view_extends; exact Hmove|exact HK].
           ++ rewrite <-Hroot. eapply continuation_spec_extend; eassumption.
Qed.

Local Lemma step_runpar_invert σ α G t T1 T2 e1 e2 σ' α' G' T' e' :
  semantics.step σ α G (Node t T1 T2) (RunPar e1 e2) σ' α' G' T' e' ->
  sched_step σ α G (Node t T1 T2) (RunPar e1 e2) σ' α' G' T' e' \/
  (exists T1' e1', T' = Node t T1' T2 /\ e' = RunPar e1' e2 /\
      semantics.step σ α G T1 e1 σ' α' G' T1' e1') \/
  (exists T2' e2', T' = Node t T1 T2' /\ e' = RunPar e1 e2' /\
      semantics.step σ α G T2 e2 σ' α' G' T2' e2').
Proof.
  intros H. remember (RunPar e1 e2) as src eqn:He. remember (Node t T1 T2) as tree eqn:HT.
  destruct H.
  - auto.
  - destruct K; discriminate He.
  - inversion He; inversion HT; subst. right. left. eauto.
  - inversion He; inversion HT; subst. right. right. eauto.
Qed.

Local Definition join_specification F t t1 t2 (Q1 Q2 R : element_spec) :=
  forall n (V : resource (S n)) σ α G T1 T2 e1 e2 σ' α' G' T' e',
    store_spec_at (S n) V σ α -> tree_paths F (Node t T1 T2) ->
    task_root T1 = t1 -> task_root T2 = t2 ->
    result_spec_at (S n) V T1 e1 Q1 -> result_spec_at (S n) V T2 e2 Q2 ->
    sched_step σ α G (Node t T1 T2) (RunPar e1 e2) σ' α' G' T' e' -> G' ⊆ F ->
    exists V' : resource n, resource_extends n (fst V) V' /\
      store_spec_at n V' σ' α' /\ expression_spec n F V' T' e' R.

Local Lemma expression_spec_parallel n F (W : resource n) t T1 T2 e1 e2 Q1 Q2 R :
  tree_paths F (Node t T1 T2) -> join_specification F t (task_root T1) (task_root T2) Q1 Q2 R ->
  expression_spec n F W T1 e1 Q1 -> expression_spec n F W T2 e2 Q2 ->
  expression_spec n F W (Node t T1 T2) (RunPar e1 e2) R.
Proof.
  revert W T1 T2 e1 e2. induction n as [|n IH]; intros W T1 T2 e1 e2 Htree Hjoin H1 H2;
    cbn [expression_spec] in *; [exact I|].
  destruct H1 as [HL0 HL1], H2 as [HR0 HR1]. split; [eapply IH; eassumption|].
  intros V σ α G Hext Hstore HG.
  destruct (HL1 V σ α G Hext Hstore HG) as (Hs1 & Hd1 & Hv1 & Hstep1).
  destruct (HR1 V σ α G Hext Hstore HG) as (Hs2 & Hd2 & Hv2 & Hstep2).
  split; [now apply safe_runpar|]. split; [now apply DEPar|]. split; [exact I|].
  intros σ' α' G' T' e' Hstep HG'.
  pose proof (proj2 (step_tree_paths _ _ _ _ _ _ _ _ _ _ _ Hstep HG' Htree)) as Htree'.
  destruct (step_runpar_invert _ _ _ _ _ _ _ _ _ _ _ _ _ Hstep) as
    [Hhead|[(T1' & e1' & -> & -> & Hleft)|(T2' & e2' & -> & -> & Hright)]].
  - eapply Hjoin; (eassumption || reflexivity).
  - destruct (Hstep1 σ' α' G' T1' e1' Hleft HG') as (V' & Hext' & Hstore' & Hcont).
    exists V'. split; [exact Hext'|]. split; [exact Hstore'|].
    apply IH; [exact Htree'| |exact Hcont|].
    + rewrite <- (proj1 (step_tree_paths _ _ _ _ _ _ _ _ _ _ _ Hleft HG' (proj1 (proj2 (proj2 Htree))))).
      exact Hjoin.
    + eapply expression_spec_extend; [|exact HR0].
      eapply resource_extends_trans; [exact (proj1 Hext)|exact Hext'].
  - destruct (Hstep2 σ' α' G' T2' e2' Hright HG') as (V' & Hext' & Hstore' & Hcont).
    exists V'. split; [exact Hext'|]. split; [exact Hstore'|].
    apply IH; [exact Htree'| | |exact Hcont].
    + rewrite <- (proj1 (step_tree_paths _ _ _ _ _ _ _ _ _ _ _ Hright HG' (proj2 (proj2 (proj2 Htree))))).
      exact Hjoin.
    + eapply expression_spec_extend; [|exact HL0].
      eapply resource_extends_trans; [exact (proj1 Hext)|exact Hext'].
Qed.

Local Lemma pure_and a b : Is_true (a && b) <-> Is_true a /\ Is_true b.
Proof. destruct a, b; simpl; tauto. Qed.

Local Lemma substitution_preserves_purity x v e : very_pure e -> very_pure (subst x v e).
Proof.
  revert e. fix IH 1. intros e. destruct e; cbn [very_pure subst]; intros Hpure;
    try solve [exact I|exfalso; exact Hpure].
  - destruct (decide (x = s)); exact I.
  - apply pure_and in Hpure as [H1 H2]. apply pure_and. split; now apply IH.
  - apply pure_and in Hpure as [H12 H3]. apply pure_and in H12 as [H1 H2].
    apply pure_and. split; [apply pure_and; split|]; now apply IH.
  - apply pure_and in Hpure as [H1 H2]. apply pure_and. split; [now apply IH|].
    destruct (decide (b = BNamed x)); [exact H2|now apply IH].
  - apply pure_and in Hpure as [H1 H2]. apply pure_and. split; now apply IH.
  - now apply IH.
  - now apply IH.
  - now apply IH.
  - now apply IH.
Qed.

Local Lemma binder_substitution_preserves_purity b v e : very_pure e -> very_pure (subst' b v e).
Proof. destruct b; [auto|apply substitution_preserves_purity]. Qed.

Local Lemma pure_fill_inv K e : very_pure (fill_item K e) -> very_pure e.
Proof. destruct K; cbn [fill_item very_pure]; repeat rewrite pure_and; simpl; tauto. Qed.

Local Lemma pure_fill_replace K e e' :
  very_pure (fill_item K e) -> very_pure e' -> very_pure (fill_item K e').
Proof. destruct K; cbn [fill_item very_pure]; repeat rewrite pure_and; simpl; tauto. Qed.

Local Definition keeps_blocks (σ σ' : store) :=
  forall l vs, σ' !! l = Some (SBlock vs) -> σ !! l = Some (SBlock vs).

Local Lemma pure_head_step σ α G t e σ' α' e' :
  head_step G t σ α e σ' α' e' -> very_pure e -> very_pure e' /\ keeps_blocks σ σ'.
Proof.
  destruct 1; subst; try destruct b; cbn [very_pure]; intros Hp; try solve [exfalso; exact Hp];
    split; try solve [exact I|unfold keeps_blocks; auto].
  all: try solve [repeat rewrite pure_and in Hp; tauto].
  all: try solve [apply binder_substitution_preserves_purity; apply pure_and in Hp; tauto].
  all: intros k vs Hblock; apply lookup_insert_Some in Hblock as [(_ & Hcontra)|(_ & Hblock)];
    [discriminate Hcontra|exact Hblock].
Qed.

Local Lemma pure_step σ α G T e σ' α' G' T' e' t :
  semantics.step σ α G T e σ' α' G' T' e' -> T = Leaf t -> very_pure e ->
  T' = Leaf t /\ very_pure e' /\ keeps_blocks σ σ'.
Proof.
  intros Hstep. induction Hstep; intros Hleaf Hp.
  - destruct H; try discriminate Hleaf.
    + split; [exact Hleaf|]. eapply pure_head_step; eassumption.
    + exfalso. exact Hp.
  - destruct (IHHstep Hleaf (pure_fill_inv K e Hp)) as (Htree & Hpure & Hblock).
    split; [exact Htree|]. split; [eapply pure_fill_replace; eassumption|exact Hblock].
  - discriminate Hleaf.
  - discriminate Hleaf.
Qed.

Local Lemma view_matches_unique V V' σ α :
  view_matches V σ α -> view_matches V' σ α -> V = V'.
Proof.
  intros [HVf HVb] [HV'f HV'b]. apply map_eq. intros l.
  destruct (V !! l) as [[u d]|] eqn:HV.
  - destruct (HVb l u d HV) as [Hu (s & Hs & Hd)].
    destruct (HV'f l s Hs) as (u' & Hu' & HV').
    assert (u' = u) by congruence. subst u' d.
    first [exact (eq_sym HV')|exact (eq_trans HV (eq_sym HV'))].
  - destruct (V' !! l) as [[u d]|] eqn:HV'; [|first [reflexivity|exact (eq_trans HV (eq_sym HV'))]].
    destruct (HV'b l u d HV') as [Hu (s & Hs & Hd)].
    destruct (HVf l s Hs) as (u' & Hu' & Hcontra).
    pose proof (eq_trans (eq_sym HV) Hcontra) as Hbad. discriminate Hbad.
Qed.

Local Lemma resource_unique_after_pure n (W V V' : resource n) σ α σ' α' :
  keeps_blocks σ σ' -> store_spec_at n W σ α ->
  resource_extends n W V -> resource_extends n W V' ->
  store_spec_at n V σ' α' -> store_spec_at n V' σ' α' -> V = V'.
Proof.
  induction n as [|n IH]; intros Hkeep Hbase Hext Hext' Hnew Hnew'.
  - eapply view_matches_unique; eassumption.
  - destruct Hext as [Hlow Htable], Hext' as [Hlow' Htable'].
    destruct Hbase as (Hbase & Hregistered & _), Hnew as (Hnew & _ & HregisteredV),
             Hnew' as (Hnew' & _ & HregisteredV').
    assert (Heq : fst V = fst V') by (eapply IH; eassumption).
    assert (Htable_eq : snd V = snd V').
    { apply map_eq. intros l.
      assert (Hold : (exists vs, σ' !! l = Some (SBlock vs)) -> snd V !! l = snd V' !! l).
      { intros (vs & Hs). destruct (Hregistered l vs (Hkeep l vs Hs)) as (P & HP & _).
        exact (eq_trans (lookup_weaken _ _ _ _ HP Htable)
                        (eq_sym (lookup_weaken _ _ _ _ HP Htable'))). }
      destruct (snd V !! l) as [P|] eqn:HP, (snd V' !! l) as [P'|] eqn:HP'.
      - apply Hold. exact (proj1 (HregisteredV l P HP)).
      - apply Hold. exact (proj1 (HregisteredV l P HP)).
      - apply Hold. exact (proj1 (HregisteredV' l P' HP')).
      - reflexivity. }
    destruct V, V'; simpl in *. now f_equal.
Qed.

Local Lemma expression_spec_pure_forall {A : Type} (a0 : A) (P : A -> element_spec)
    n F (W : resource n) t e :
  very_pure e ->
  (forall a, expression_spec n F W (Leaf t) e (P a)) ->
  expression_spec n F W (Leaf t) e (fun k V v => forall a, P a k V v).
Proof.
  revert W e. induction n as [|n IH]; intros W e Hp Hall;
    cbn [expression_spec] in *; [exact I|].
  split; [apply IH; [exact Hp|intros a; exact (proj1 (Hall a))]|].
  intros V σ α G Hext Hstore HG.
  pose proof (fun a => proj2 (Hall a) V σ α G Hext Hstore HG) as Hcur.
  destruct (Hcur a0) as (Hsafe & Hde & _ & Hnext0).
  split; [exact Hsafe|]. split; [exact Hde|]. split.
  - destruct e; try exact I. cbn [result_spec_at]. split; [exact I|].
    intros a. exact (proj2 (proj1 (proj2 (proj2 (Hcur a))))).
  - intros σ' α' G' T' e' Hstep HG'.
    destruct (pure_step _ _ _ _ _ _ _ _ _ _ _ Hstep eq_refl Hp) as (-> & Hp' & Hblocks).
    destruct (Hnext0 _ _ _ _ _ Hstep HG') as (U & HU & HstoreU & _).
    exists U. split; [exact HU|]. split; [exact HstoreU|].
    apply IH; [exact Hp'|]. intros a.
    destruct (proj2 (proj2 (proj2 (Hcur a))) _ _ _ _ _ Hstep HG') as (V' & HV' & HstoreV' & Hbody).
    assert (Heq : U = V') by (eapply resource_unique_after_pure; [exact Hblocks|exact (proj1 Hstore)|exact HU|exact HV'|exact HstoreU|exact HstoreV']).
    now subst V'.
Qed.

(* Closing a source expression replaces free variables with runtime values. *)
Local Fixpoint close_expr (E : gmap string val) (e : expr) : expr :=
  match e with
  | Val _ => e
  | Var x => match E !! x with Some v => Val v | None => e end
  | Clo (Lam self args body) => Clo (Lam self args (close_expr (bdeletes (self::args) E) body))
  | Call f es => Call (close_expr E f) (close_expr E <$> es)
  | CallPrim p e1 e2 => CallPrim p (close_expr E e1) (close_expr E e2)
  | If e1 e2 e3 => If (close_expr E e1) (close_expr E e2) (close_expr E e3)
  | Let b e1 e2 => Let b (close_expr E e1) (close_expr (bdelete b E) e2)
  | Alloc e1 e2 => Alloc (close_expr E e1) (close_expr E e2)
  | Load e1 e2 => Load (close_expr E e1) (close_expr E e2)
  | Store e1 e2 e3 => Store (close_expr E e1) (close_expr E e2) (close_expr E e3)
  | Length e => Length (close_expr E e)
  | Prod e1 e2 => Prod (close_expr E e1) (close_expr E e2)
  | Fst e => Fst (close_expr E e)
  | Snd e => Snd (close_expr E e)
  | InL e => InL (close_expr E e)
  | InR e => InR (close_expr E e)
  | Case e b e1 c e2 => Case (close_expr E e) b (close_expr (bdelete b E) e1)
                           c (close_expr (bdelete c E) e2)
  | Par e1 e2 => Par (close_expr E e1) (close_expr E e2)
  | RunPar e1 e2 => RunPar (close_expr E e1) (close_expr E e2)
  | CAS e1 e2 e3 e4 => CAS (close_expr E e1) (close_expr E e2) (close_expr E e3) (close_expr E e4)
  | Fold e => Fold (close_expr E e)
  | Unfold e => Unfold (close_expr E e)
  end.

Local Lemma bdeletes_empty {A} bs : bdeletes bs (∅ : gmap string A) = ∅.
Proof.
  apply map_eq. intros x. rewrite binders_lookup_delete, !lookup_empty.
  now destruct (decide (x ∈ binders_set bs)).
Qed.

Local Lemma binder_delete_empty {A} b : bdelete b (∅ : gmap string A) = ∅.
Proof. change (bdeletes [b] (∅ : gmap string A) = ∅). apply bdeletes_empty. Qed.

Local Lemma bdeletes_union {A} bs (E E' : gmap string A) :
  bdeletes bs (E ∪ E') = bdeletes bs E ∪ bdeletes bs E'.
Proof.
  apply map_eq. intros x. rewrite lookup_union, !binders_lookup_delete, lookup_union.
  now destruct (decide (x ∈ binders_set bs)).
Qed.

Local Lemma binder_delete_union {A} b (E E' : gmap string A) :
  bdelete b (E ∪ E') = bdelete b E ∪ bdelete b E'.
Proof.
  change (bdeletes [b] (E ∪ E') = bdeletes [b] E ∪ bdeletes [b] E'). apply bdeletes_union.
Qed.

Local Lemma close_empty e : close_expr ∅ e = e.
Proof.
  revert e. fix IH 1. intros e. destruct e; cbn [close_expr];
    try rewrite !binder_delete_empty; try solve [f_equal; apply IH].
  - destruct f. cbn [close_expr]. rewrite bdeletes_empty. f_equal. f_equal. apply IH.
  - f_equal; [apply IH|]. induction l as [|a es IHes]; [reflexivity|].
    rewrite fmap_cons. f_equal; [apply IH|exact IHes].
Qed.

Local Lemma close_union e E E' : close_expr E' (close_expr E e) = close_expr (E ∪ E') e.
Proof.
  revert E E' e. fix IH 3. intros E E' e. destruct e; cbn [close_expr];
    try rewrite !binder_delete_union; try solve [f_equal; apply IH].
  - destruct f. cbn [close_expr]. rewrite bdeletes_union. f_equal. f_equal. apply IH.
  - rewrite lookup_union. destruct (E !! s); cbn [close_expr]; destruct (E' !! s); reflexivity.
  - f_equal; [apply IH|]. induction l as [|a es IHes]; [reflexivity|].
    rewrite !fmap_cons. f_equal; [apply IH|exact IHes].
Qed.

Local Lemma bdeletes_singleton {A} bs x (v : A) :
  bdeletes bs {[x:=v]} = if decide (x ∈ binders_set bs) then ∅ else {[x:=v]}.
Proof.
  apply map_eq. intros y. rewrite binders_lookup_delete.
  destruct (decide (x ∈ binders_set bs)) as [Hx|Hx];
    destruct (decide (y ∈ binders_set bs)) as [Hy|Hy]; try reflexivity.
  - rewrite lookup_empty. apply lookup_singleton_ne. congruence.
  - symmetry. apply lookup_singleton_ne. congruence.
Qed.

Local Lemma binder_delete_singleton {A} b x (v : A) :
  bdelete b {[x:=v]} = if decide (b = BNamed x) then ∅ else {[x:=v]}.
Proof.
  destruct b as [|y]; [reflexivity|].
  destruct (decide (BNamed y = BNamed x)) as [H|H].
  - injection H as ->. simpl. apply map_eq. intros z. rewrite lookup_empty, lookup_delete.
    destruct (decide (x = z)); [reflexivity|now rewrite lookup_singleton_ne].
  - simpl. apply map_eq. intros z. rewrite lookup_delete.
    destruct (decide (y = z)); [subst z; symmetry; apply lookup_singleton_ne; congruence|reflexivity].
Qed.

Local Lemma close_singleton x v e : close_expr {[x:=v]} e = subst x v e.
Proof.
  revert e. fix IH 1. intros e. destruct e; cbn [close_expr subst];
    try solve [f_equal; apply IH].
  - destruct f. cbn [close_expr subst_clo]. rewrite bdeletes_singleton, binders_set_cons.
    fold (binders_set l).
    destruct (decide (x ∈ binder_set b ∪ binders_set l)); f_equal; f_equal;
      [apply close_empty|apply IH].
  - destruct (decide (x = s)); [subst s; now rewrite lookup_singleton_eq|now rewrite lookup_singleton_ne].
  - f_equal; [apply IH|]. induction l as [|a es IHes]; [reflexivity|].
    rewrite !fmap_cons. f_equal; [apply IH|exact IHes].
  - f_equal; [apply IH|]. rewrite binder_delete_singleton.
    destruct (decide (b = BNamed x)); [apply close_empty|apply IH].
  - f_equal; try apply IH;
      rewrite binder_delete_singleton;
      match goal with
      | |- context [decide (?b = BNamed x)] =>
          destruct (decide (b = BNamed x));
          [subst b; rewrite decide_True by reflexivity; apply close_empty|
           rewrite decide_False by congruence; apply IH]
      end.
Qed.

Local Lemma close_binder b v e : close_expr (binsert b v ∅) e = subst' b v e.
Proof.
  destruct b as [|x]; [apply close_empty|].
  change (close_expr {[x:=v]} e = subst x v e). apply close_singleton.
Qed.

Local Lemma close_single_binding b v E e :
  subst' b v (close_expr (bdelete b E) e) = close_expr (binsert b v E) e.
Proof.
  rewrite <-close_binder, close_union. f_equal. destruct b; simpl.
  - apply map_eq. intros x. now rewrite lookup_union, lookup_empty; destruct (E !! x).
  - apply map_eq. intros x. rewrite lookup_union, lookup_delete, !lookup_insert, lookup_empty.
    destruct (decide (s = x)), (E !! x); reflexivity.
Qed.

Local Lemma binsert_union_left {A} b v (E F : gmap string A) :
  binsert b v (E ∪ F) = binsert b v E ∪ F.
Proof.
  destruct b as [|x]; [reflexivity|]. cbn [binsert]. apply map_eq. intros z.
  repeat first [rewrite lookup_insert | rewrite lookup_union].
  destruct (decide (x = z)), (E !! z), (F !! z); reflexivity.
Qed.

Local Lemma binserts_app {A} (xs ys : list (binder * A)) (E : gmap string A) :
  binserts (xs ++ ys) E = binserts xs (binserts ys E).
Proof. unfold binserts. apply foldr_app. Qed.

Local Lemma binserts_union_empty {A} (xs : list (binder * A)) (E : gmap string A) :
  binserts xs E = binserts xs ∅ ∪ E.
Proof.
  induction xs as [|[b v] xs IH]; cbn [binserts foldr].
  - apply map_eq. intros x. rewrite lookup_union, lookup_empty. now destruct (E !! x).
  - change (binsert b v (binserts xs E) = binsert b v (binserts xs ∅) ∪ E).
    now rewrite IH, binsert_union_left.
Qed.

Local Lemma close_substs xs e E :
  substs' xs (close_expr E e) = close_expr (E ∪ binserts (rev xs) ∅) e.
Proof.
  induction xs as [|[b v] xs IH].
  - change (close_expr E e = close_expr (E ∪ ∅) e).
    f_equal. apply map_eq. intros x.
    rewrite lookup_union, lookup_empty. now destruct (E !! x).
  - change (subst' b v (substs' xs (close_expr E e)) =
      close_expr (E ∪ binserts (rev xs ++ [(b,v)]) ∅) e).
    rewrite IH, <-close_binder, close_union, binserts_app.
    change (close_expr (E ∪ binserts (rev xs) ∅ ∪ binsert b v ∅) e =
      close_expr (E ∪ binserts (rev xs) (binsert b v ∅)) e).
    rewrite (binserts_union_empty (rev xs) (binsert b v ∅)). f_equal. apply map_eq. intros x.
    rewrite !lookup_union. now destruct (E !! x), (binserts (rev xs) ∅ !! x), (binsert b v ∅ !! x).
Qed.

Local Lemma extend_delete_union {A} bs (vs : list A) E :
  length bs = length vs -> bdeletes bs E ∪ bmap bs vs = extend bs vs E.
Proof.
  intros Hlen. pose proof (dom_bmap bs vs Hlen) as HD.
  assert (Hext : extend bs vs E = bmap bs vs ∪ E) by (unfold extend, bmap; apply binserts_union_empty).
  rewrite Hext. apply map_eq. intros x. rewrite !lookup_union, binders_lookup_delete.
  destruct (decide (x ∈ binders_set bs)) as [Hin|Hout].
  - assert (Hsome : exists v, bmap bs vs !! x = Some v).
    { apply elem_of_dom. now rewrite HD. }
    destruct Hsome as (v & Hv). rewrite Hv. now destruct (E !! x).
  - assert (Hnone : bmap bs vs !! x = None) by (apply not_elem_of_dom; now rewrite HD).
    rewrite Hnone. now destruct (E !! x).
Qed.

Local Lemma close_call_bindings bs vs E e :
  length bs = length vs ->
  substs' (zip bs vs) (close_expr (bdeletes bs E) e) = close_expr (extend bs vs E) e.
Proof. intros Hlen. rewrite close_substs. apply f_equal with (f:=fun M => close_expr M e).
  now apply extend_delete_union.
Qed.

Local Definition env_locs (E : gmap string val) (L : gset loc) :=
  forall x v, E !! x = Some v -> locs v ⊆ L.

Local Lemma env_locs_delete E L bs : env_locs E L -> env_locs (bdeletes bs E) L.
Proof.
  intros H x v Hx. rewrite binders_lookup_delete in Hx.
  destruct (decide (x ∈ binders_set bs)); [discriminate|]. now apply H in Hx.
Qed.

Local Lemma close_locations E e L : env_locs E L -> locs (close_expr E e) ⊆ locs e ∪ L.
Proof.
  revert E e. fix IH 2. intros E e HE. destruct e; cbn [close_expr locs location_expr locs_expr].
  - clear IH. set_solver.
  - destruct f as [self args body]. cbn [close_expr locs_func].
    apply IH. now apply env_locs_delete.
  - destruct (E !! s) as [v|] eqn:Hv; cbn [locs_expr].
    + pose proof (HE s v Hv). clear IH. set_solver.
    + clear IH. set_solver.
  - pose proof (IH E e HE).
    assert (Hargs : ⋃ (locs <$> (close_expr E <$> l)) ⊆ ⋃ (locs <$> l) ∪ L).
    { induction l as [|arg args IHargs].
      - clear IH. set_solver.
      - rewrite !fmap_cons, !union_list_cons. pose proof (IH E arg HE). clear IH. set_solver. }
    clear IH. set_solver.
  - pose proof (IH E e1 HE). pose proof (IH E e2 HE). clear IH. set_solver.
  - pose proof (IH E e1 HE). pose proof (IH E e2 HE). pose proof (IH E e3 HE).
    clear IH. set_solver.
  - pose proof (IH E e1 HE). pose proof (IH (bdeletes [b] E) e2 (env_locs_delete E L [b] HE)).
    clear IH. change (locs (close_expr (bdelete b E) e2) ⊆ locs e2 ∪ L) in H0. set_solver.
  - pose proof (IH E e1 HE). pose proof (IH E e2 HE). clear IH. set_solver.
  - now apply IH.
  - now apply IH.
  - now apply IH.
  - now apply IH.
  - pose proof (IH E e1 HE).
    pose proof (IH (bdeletes [b] E) e2 (env_locs_delete E L [b] HE)).
    pose proof (IH (bdeletes [b0] E) e3 (env_locs_delete E L [b0] HE)).
    clear IH. change (locs (close_expr (bdelete b E) e2) ⊆ locs e2 ∪ L) in H0.
    change (locs (close_expr (bdelete b0 E) e3) ⊆ locs e3 ∪ L) in H1. set_solver.
  - pose proof (IH E e1 HE). pose proof (IH E e2 HE). clear IH. set_solver.
  - pose proof (IH E e1 HE). pose proof (IH E e2 HE). clear IH. set_solver.
  - pose proof (IH E e1 HE). pose proof (IH E e2 HE). pose proof (IH E e3 HE).
    clear IH. set_solver.
  - now apply IH.
  - pose proof (IH E e1 HE). pose proof (IH E e2 HE). clear IH. set_solver.
  - pose proof (IH E e1 HE). pose proof (IH E e2 HE). clear IH. set_solver.
  - pose proof (IH E e1 HE). pose proof (IH E e2 HE). pose proof (IH E e3 HE). pose proof (IH E e4 HE).
    clear IH. set_solver.
  - now apply IH.
  - now apply IH.
Qed.

Local Lemma close_preserves_purity E e : very_pure e -> very_pure (close_expr E e).
Proof.
  revert E e. fix IH 2. intros E e. destruct e; cbn [close_expr very_pure];
    intros Hpure; try solve [exact I|exfalso; exact Hpure|now apply IH].
  - destruct f. exact I.
  - destruct (E !! s); exact I.
  - apply pure_and in Hpure as [H1 H2]. apply pure_and. split; now apply IH.
  - apply pure_and in Hpure as [H12 H3]. apply pure_and in H12 as [H1 H2].
    apply pure_and. split; [apply pure_and; split|]; now apply IH.
  - apply pure_and in Hpure as [H1 H2]. apply pure_and. split; now apply IH.
  - apply pure_and in Hpure as [H1 H2]. apply pure_and. split; now apply IH.
Qed.

Local Definition element_downward (E : element_spec) :=
  forall n (W : resource (S n)) v, E (S n) W v -> E n (fst W) v.

Local Definition empty_element : element_spec := fun _ _ _ => False.

Local Definition location_spec F t (P : forall n, resource n -> loc -> (nat + storable) -> Prop) : element_spec :=
  fun n W v => exists l u d, v = VLoc l /\ resource_view n W !! l = Some (u,d) /\
    reachable F u t /\ P n W l d.

Local Lemma location_spec_visible F t P n W v :
  location_spec F t P n W v -> value_visible_in_view F (resource_view n W) t v.
Proof.
  intros (l & u & d & -> & Hlook & Hreach & _) k Hk.
  change (k ∈ ({[l]} : gset loc)) in Hk. apply elem_of_singleton in Hk. subst k.
  exists u, d. now split.
Qed.

Local Lemma location_spec_monotone F t P :
  (forall n (W V : resource n) l d, resource_extends n W V -> P n W l d -> P n V l d) ->
  element_monotone (location_spec F t P).
Proof.
  intros HP n W V v Hext (l & u & d & Hv & Hw & Hreach & Hshape).
  exists l, u, d. split; [exact Hv|]. split.
  - exact (lookup_weaken _ _ _ _ Hw (resource_view_extends _ _ _ Hext)).
  - split; [exact Hreach|eapply HP; eassumption].
Qed.

Local Lemma location_spec_downward F t P :
  (forall n (W : resource (S n)) l d, P (S n) W l d -> P n (fst W) l d) ->
  element_downward (location_spec F t P).
Proof.
  intros HP n W v (l & u & d & Hv & Hw & Hreach & Hshape).
  exists l, u, d. split; [exact Hv|]. split; [exact Hw|]. split; [exact Hreach|].
  now apply HP in Hshape.
Qed.

Local Definition product_result F t (P Q : element_spec) :=
  location_spec F t (fun n W _ d =>
    exists v w, d = inr (SProd v w) /\ P n W v /\ Q n W w).

Local Lemma product_result_monotone F t P Q :
  element_monotone P -> element_monotone Q -> element_monotone (product_result F t P Q).
Proof.
  intros Hp Hq. apply location_spec_monotone.
  intros n W V l d Hext (v & w & Hd & Hv & Hw). exists v, w. split; [exact Hd|].
  split; [eapply Hp|eapply Hq]; eassumption.
Qed.

Local Lemma product_result_downward F t P Q :
  element_downward P -> element_downward Q -> element_downward (product_result F t P Q).
Proof.
  intros Hp Hq. apply location_spec_downward.
  intros n W l d (v & w & Hd & Hv & Hw). exists v, w. split; [exact Hd|].
  split; [now apply Hp|now apply Hq].
Qed.

Local Lemma join_post_paths (F G : graph) t t1 t2 : graph_join G t1 t2 t ⊆ F ->
  reachable F t1 t /\ reachable F t2 t.
Proof.
  intros H. split.
  - eapply reach_mono; [exact H|]. unfold graph_join.
    eapply reach_mono; [apply graph_upd_include|apply graph_upd_reach; set_solver].
  - eapply reach_mono; [exact H|]. apply graph_upd_reach. set_solver.
Qed.

Local Lemma product_join_specification F t t1 t2 Q1 Q2 P1 P2 :
  element_monotone P1 -> element_monotone P2 -> element_downward P1 -> element_downward P2 ->
  (forall n (W : resource (S n)) v, reachable F t t1 -> reachable F t1 t ->
    Q1 (S n) W v -> P1 n (fst W) v) ->
  (forall n (W : resource (S n)) v, reachable F t t2 -> reachable F t2 t ->
    Q2 (S n) W v -> P2 n (fst W) v) ->
  join_specification F t t1 t2 Q1 Q2 (product_result F t P1 P2).
Proof.
  intros Hmono1 Hmono2 Hdown1 Hdown2 Hret1 Hret2.
  intros n W σ α G T1 T2 e1 e2 σ' α' G' T' e' Hstore Htree Ht1 Ht2 Hv1 Hv2 Hstep Hgraph.
  inversion Hstep as [ | | σ0 α0 G0 G1 u1 u2 u v w σ1 α1 l Hgraph_eq Hfresh Hfreshα Hσ Hα ]; subst.
  destruct Hv1 as [_ Hv1], Hv2 as [_ Hv2].
  destruct Htree as (Hreach1 & Hreach2 & _).
  destruct (join_post_paths _ _ _ _ _ Hgraph) as [Hback1 Hback2].
  assert (Hempty : σ !! l = None) by (apply not_elem_of_dom; assumption).
  set (V := resource_insert n l t (SProd v w) empty_element (fst W)).
  assert (Hext : resource_extends n (fst W) V).
  { unfold V. eapply resource_insert_grows; [exact (proj1 Hstore)|exact Hempty]. }
  exists V. split; [exact Hext|]. split.
  - unfold V. apply resource_insert_store; [exact (proj1 Hstore)|exact Hempty| |discriminate].
    intros k A B q _ Hbad. destruct Hbad.
  - assert (Hpair : product_result F t P1 P2 n V (VLoc l)).
    { exists l, t, (inr (SProd v w)). split; [reflexivity|]. split.
      - unfold V. rewrite resource_insert_view. apply lookup_insert_eq.
      - split; [apply rtc_refl|]. exists v, w. split; [reflexivity|]. split.
        + eapply Hmono1; [exact Hext|eapply Hret1; eassumption].
        + eapply Hmono2; [exact Hext|eapply Hret2; eassumption]. }
    apply expression_spec_value.
    + intros k A Hvalue. eapply location_spec_visible; exact Hvalue.
    + intros A Hinter. eapply (product_result_monotone F t P1 P2 Hmono1 Hmono2); eassumption.
    + intros k A Hvalue. eapply (product_result_downward F t P1 P2 Hdown1 Hdown2); eassumption.
Qed.

Local Lemma head_ready_context_value σ e : head_ready σ e ->
  forall K f, fill_item K f = e -> is_val f.
Proof.
  destruct 1; try destruct b; intros K f He; destruct K; simpl in He; try discriminate;
    try solve [inversion He; subst; exact I].
  all: injection He as _ Hargs; assert (Hf : f ∈ Val <$> vs).
  all: try (rewrite <-Hargs; apply elem_of_app; right; constructor).
  all: apply list_elem_of_fmap in Hf as (? & -> & _); exact I.
Qed.

Local Lemma head_ready_not_val σ e : head_ready σ e -> ¬ is_val e.
Proof. destruct 1; try destruct b; exact (fun H => H). Qed.

Local Lemma head_ready_not_par σ (v w : val) : ¬ head_ready σ (Par v w).
Proof.
  intros H. remember (Par v w) as e eqn:He. destruct H; try destruct b; discriminate He.
Qed.

Local Lemma ready_step_head σ α G t e σ' α' G' T' e' :
  head_ready σ e ->
  semantics.step σ α G (Leaf t) e σ' α' G' T' e' ->
  G' = G /\ T' = Leaf t /\ head_step G t σ α e σ' α' e'.
Proof.
  intros Hr Hstep. remember (Leaf t) as T eqn:HT.
  destruct Hstep; try discriminate HT.
  - destruct H; try discriminate HT.
    + injection HT as ->. auto.
    + exfalso. eapply head_ready_not_par. exact Hr.
  - exfalso. eapply step_nonvalue; [exact Hstep|].
    exact (head_ready_context_value _ _ Hr K e eq_refl).
Qed.

Local Lemma expression_spec_atomic n F (W : resource (S n)) t e (Q : element_spec) :
  expression_spec n F (fst W) (Leaf t) e Q ->
  (forall (V : resource (S n)) σ α G,
      resource_extends (S n) W V -> store_spec_at (S n) V σ α -> G ⊆ F ->
      head_ready σ e /\ all_abef F α t (locs e) /\
      forall σ' α' e', head_step G t σ α e σ' α' e' ->
        exists U : resource n, resource_extends n (fst V) U /\
          store_spec_at n U σ' α' /\ expression_spec n F U (Leaf t) e' Q) ->
  expression_spec (S n) F W (Leaf t) e Q.
Proof.
  intros Hprev Hnow. split; [exact Hprev|].
  intros V σ α G Hext Hstore Hgraph.
  destruct (Hnow V σ α G Hext Hstore Hgraph) as (Hready & Haccess & Hnext).
  split; [right; now apply head_ready_reducible|].
  split; [now apply DELeaf|]. split.
  - destruct e; try exact I. exfalso. exact (head_ready_not_val _ _ Hready I).
  - intros σ' α' G' T' e' Hstep _.
    destruct (ready_step_head _ _ _ _ _ _ _ _ _ _ Hready Hstep) as (-> & -> & Hhead).
    now apply Hnext.
Qed.

Local Lemma array_spec_extend n (W V : resource n) l E :
  resource_extends n W V -> array_spec_at n W l E -> array_spec_at n V l E.
Proof.
  induction n as [|n IH]; cbn [array_spec_at resource_extends]; [tauto|].
  intros [Hlow Htable] [Harray (P & HP & Hagree)]. split; [eapply IH; eassumption|].
  exists P. split; [exact (lookup_weaken _ _ _ _ HP Htable)|exact Hagree].
Qed.

Local Lemma head_load_invert G t σ α l (i : Z) σ' α' e' :
  head_step G t σ α (Load (VLoc l) i) σ' α' e' ->
  exists vs v, σ' = σ /\ α' = α /\ e' = Val v /\
    σ !! l = Some (SBlock vs) /\ vs !! Z.to_nat i = Some v.
Proof.
  intros Hstep. remember (Load (VLoc l) i) as e eqn:He.
  destruct Hstep; try destruct b; try discriminate He.
  inversion He; subst. eauto 8.
Qed.

Local Lemma expression_spec_load n F (W : resource n) t l (i : Z) o size E :
  resource_view n W !! l = Some (o, inl size) -> reachable F o t ->
  array_spec_at n W l E -> element_monotone E -> element_downward E ->
  (forall k (V : resource k) v, E k V v -> value_visible_in_view F (resource_view k V) t v) ->
  expression_spec n F W (Leaf t) (Load (VLoc l) i) E.
Proof.
  induction n as [|n IH]; intros Hloc Hreach Harray Hmono Hdown Hvisible; [exact I|].
  apply expression_spec_atomic.
  - apply IH; [exact Hloc|exact Hreach|exact (proj1 Harray)|exact Hmono|exact Hdown|exact Hvisible].
  - intros V σ α G Hext Hstore Hgraph.
    assert (Hentry : resource_view (S n) V !! l = Some (o,inl size)).
    { exact (lookup_weaken _ _ _ _ Hloc (resource_view_extends _ _ _ Hext)). }
    destruct (proj2 (store_spec_view _ _ _ _ Hstore) l o _ Hentry) as [Hα (s & Hσ & Hs)].
    destruct s as [vs| | | |]; try discriminate Hs.
    split; [eapply ReadyLoad; eassumption|]. split.
    + intros l' Hl'. change (l' ∈ ({[l]} : gset loc) ∪ ∅) in Hl'.
      assert (l' = l) by set_solver. subst l'. unfold abef. now rewrite Hα.
    + intros σ' α' e' Hhead.
      destruct (head_load_invert _ _ _ _ _ _ _ _ _ Hhead) as (bs & v & -> & -> & -> & Hb & Hv).
      exists (fst V). split; [apply resource_extends_refl|]. split; [exact (proj1 Hstore)|].
      assert (HEv : E n (fst V) v) by
        (eapply array_load_spec; [exact Hstore|eapply array_spec_extend; eassumption|exact Hb|exact Hv]).
      apply expression_spec_value.
      * intros k A Hvalue. eapply Hvisible; eassumption.
      * intros A HV. eapply Hmono; eassumption.
      * exact (fun k A => Hdown k A v).
Qed.

Local Definition unit_element : element_spec := fun _ _ v => v = VUnit.

Local Lemma expression_spec_unit n F (W : resource n) t :
  expression_spec n F W (Leaf t) VUnit unit_element.
Proof.
  apply expression_spec_value.
  - intros k V _ l Hl. change (l ∈ (∅ : gset loc)) in Hl. set_solver.
  - intros V _. reflexivity.
  - intros k V. exact (fun H => H).
Qed.

Local Lemma element_fits_one n (W : resource n) E v :
  element_downward E -> E n W v -> elements_fit n W E [v].
Proof.
  induction n as [|n IH]; intros Hdown Hvalue; [exact I|].
  pose proof (Hdown n W v Hvalue) as Hprev.
  split; [now apply IH|constructor; [exact Hprev|constructor]].
Qed.

Local Lemma head_store_invert G t σ α l (i : Z) (v : val) σ' α' e' :
  head_step G t σ α (Store (VLoc l) i v) σ' α' e' ->
  exists vs, σ !! l = Some (SBlock vs) /\
    σ' = <[l:=SBlock (<[Z.to_nat i:=v]> vs)]>σ /\ α' = α /\ e' = Val VUnit.
Proof.
  intros Hstep. remember (Store (VLoc l) i v) as src eqn:He.
  destruct Hstep; try destruct b; try discriminate He.
  inversion He; subst. eauto 8.
Qed.

Local Lemma expression_spec_store n F (W : resource n) t l (i : Z) (v : val) o size E :
  resource_view n W !! l = Some (o, inl size) -> reachable F o t ->
  array_spec_at n W l E -> element_downward E ->
  (forall V : resource n, resource_extends n W V -> E n V v) ->
  (forall k (V : resource k) w, E k V w -> value_visible_in_view F (resource_view k V) t w) ->
  expression_spec n F W (Leaf t) (Store (VLoc l) i v) unit_element.
Proof.
  induction n as [|n IH]; intros Hloc Hreach Harray Hdown Hvalue Hvisible; [exact I|].
  apply expression_spec_atomic.
  - apply IH; [exact Hloc|exact Hreach|exact (proj1 Harray)|exact Hdown| |exact Hvisible].
    intros V Hext. apply (Hdown n (V, snd W)). apply Hvalue. exact (conj Hext (reflexivity _)).
  - intros V σ α G Hext Hstore Hgraph.
    pose proof (Hvalue V Hext) as Hv.
    assert (Hentry : resource_view (S n) V !! l = Some (o,inl size)).
    { exact (lookup_weaken _ _ _ _ Hloc (resource_view_extends _ _ _ Hext)). }
    pose proof (store_spec_view _ _ _ _ Hstore) as Hvw.
    destruct (proj2 Hvw l o _ Hentry) as [Hα (s & Hσ & Hs)].
    destruct s as [vs| | | |]; try discriminate Hs.
    split; [eapply ReadyStore; eassumption|]. split.
    + pose proof (value_view_access _ _ _ _ _ _ Hvw (Hvisible (S n) V v Hv)) as Hvalue_access.
      intros l' Hl'. change (l' ∈ (({[l]} : gset loc) ∪ ∅) ∪ locs v) in Hl'.
      apply elem_of_union in Hl' as [Hl'|Hl']; [|now apply Hvalue_access].
      assert (l' = l) by set_solver. subst l'. unfold abef. now rewrite Hα.
    + intros σ' α' e' Hhead.
      destruct (head_store_invert _ _ _ _ _ _ _ _ _ _ Hhead) as (bs & Hb & -> & -> & ->).
      exists (fst V). split; [apply resource_extends_refl|]. split; [|apply expression_spec_unit].
      eapply store_replacement_spec; [exact (proj1 Hstore)| |apply element_fits_one|exact Hb].
      * destruct (array_spec_extend _ _ _ _ _ Hext Harray) as [Hprev _]. exact Hprev.
      * exact Hdown.
      * exact (Hdown n V v Hv).
Qed.

Local Definition array_result F t (A : timestamp -> Prop) (E : element_spec) :=
  location_spec F t (fun n W l d =>
    exists o size, d = inl size /\ resource_view n W !! l = Some (o,d) /\
      A o /\ array_spec_at n W l E).

Local Lemma array_result_monotone F t A E : element_monotone (array_result F t A E).
Proof.
  apply location_spec_monotone. intros n W V l d Hext (o & size & Hd & Hview & HA & HE).
  exists o, size. split; [exact Hd|]. split.
  - exact (lookup_weaken _ _ _ _ Hview (resource_view_extends _ _ _ Hext)).
  - split; [exact HA|eapply array_spec_extend; eassumption].
Qed.

Local Lemma array_result_downward F t A E : element_downward (array_result F t A E).
Proof.
  apply location_spec_downward. intros n W l d (o & size & Hd & Hview & HA & HE).
  exists o, size. split; [exact Hd|]. split; [exact Hview|]. split; [exact HA|exact (proj1 HE)].
Qed.

Local Lemma element_fits_replicate n (W : resource n) E (v : val) m :
  element_downward E -> E n W v -> elements_fit n W E (replicate m v).
Proof.
  induction n as [|n IH]; intros Hdown Hval; [exact I|].
  pose proof (Hdown n W v Hval) as Hprev.
  split; [now apply IH|].
  clear IH.
  induction m as [|m IHm]; cbn [replicate].
  - exact (proj2 (Forall_nil (E n (fst W))) I).
  - constructor; assumption.
Qed.

Local Lemma head_alloc_invert G t σ α (i : Z) (v : val) σ' α' e' :
  head_step G t σ α (Alloc i v) σ' α' e' ->
  exists l, l ∉ dom σ /\ l ∉ dom α /\
    σ' = <[l:=SBlock (replicate (Z.to_nat i) v)]>σ /\ α' = <[l:=t]>α /\ e' = Val (VLoc l).
Proof.
  intros Hstep. remember (Alloc i v) as src eqn:He.
  destruct Hstep; try destruct b; try discriminate He.
  inversion He; subst. eauto 8.
Qed.

Local Lemma expression_spec_alloc n F (W : resource n) t (i : Z) (v : val) A E :
  A t -> element_monotone E -> element_downward E ->
  (forall V : resource n, resource_extends n W V -> E n V v) ->
  (forall k (V : resource k) w, E k V w -> value_visible_in_view F (resource_view k V) t w) ->
  expression_spec n F W (Leaf t) (Alloc i v) (array_result F t A E).
Proof.
  induction n as [|n IH]; intros Htime Hmono Hdown Hvalue Hvisible; [exact I|].
  apply expression_spec_atomic.
  - apply IH; [exact Htime|exact Hmono|exact Hdown| |exact Hvisible].
    intros V Hext. apply (Hdown n (V, snd W)). apply Hvalue. exact (conj Hext (reflexivity _)).
  - intros V σ α G Hext Hstore Hgraph. pose proof (Hvalue V Hext) as Hv.
    split; [apply ReadyAlloc|]. split.
    + pose proof (value_view_access _ _ _ _ _ _ (store_spec_view _ _ _ _ Hstore)
        (Hvisible (S n) V v Hv)) as Haccess.
      intros l Hl. apply Haccess. change (l ∈ (∅ : gset loc) ∪ locs v) in Hl. set_solver.
    + intros σ' α' e' Hhead.
      destruct (head_alloc_invert _ _ _ _ _ _ _ _ _ Hhead) as (l & Hσ & Hα & -> & -> & ->).
      assert (Hempty : σ !! l = None) by (apply not_elem_of_dom; exact Hσ).
      set (vs := replicate (Z.to_nat i) v).
      set (U := resource_insert n l t (SBlock vs) E (fst V)).
      assert (Hext' : resource_extends n (fst V) U).
      { unfold U. eapply resource_insert_grows; [exact (proj1 Hstore)|exact Hempty]. }
      exists U. split; [exact Hext'|]. split.
      * unfold U. apply resource_insert_store; [exact (proj1 Hstore)|exact Hempty|exact Hmono|].
        intros ws Heq. injection Heq as <-. unfold vs. apply element_fits_replicate;
          [exact Hdown|exact (Hdown n V v Hv)].
      * assert (Hentry : resource_view n U !! l = Some (t,inl (length vs))).
        { unfold U. rewrite resource_insert_view. apply lookup_insert_eq. }
        assert (Hval : array_result F t A E n U (VLoc l)).
        { exists l, t, (inl (length vs)). split; [reflexivity|]. split; [exact Hentry|].
          split; [apply rtc_refl|]. exists t, (length vs). split; [reflexivity|].
          split; [exact Hentry|]. split; [exact Htime|apply resource_insert_array]. }
        apply expression_spec_value.
        -- intros k B HB. eapply location_spec_visible; exact HB.
        -- intros B HB. eapply (array_result_monotone F t A E); eassumption.
        -- intros k B HB. eapply (array_result_downward F t A E); eassumption.
Qed.

Local Fixpoint all_lower_resources n : resource n -> (forall k, resource k -> Prop) -> Prop :=
  match n with
  | O => fun _ _ => True
  | S n => fun W P => P n (fst W) /\ all_lower_resources n (fst W) P
  end.

Local Lemma all_lower_resources_mono n (W V : resource n) (P : forall k, resource k -> Prop) :
  (forall k A B, resource_extends k A B -> P k A -> P k B) ->
  resource_extends n W V -> all_lower_resources n W P -> all_lower_resources n V P.
Proof.
  induction n as [|n IH]; intros HP Hext Hlevel; [exact I|].
  destruct Hext as [Hext _], Hlevel as [Hnow Hlower]. split.
  - eapply HP; eassumption.
  - eapply IH; eassumption.
Qed.

Record call_signature := {
  time_arity : nat;
  call_constraints : list timestamp -> Prop;
  call_time : list timestamp -> timestamp;
  call_parameters : list timestamp -> list element_spec;
  call_result : list timestamp -> element_spec
}.

Local Definition clock_equivalent (F : graph) u v := reachable F u v /\ reachable F v u.

Local Lemma clock_equivalent_refl F t : clock_equivalent F t t.
Proof. split; apply rtc_refl. Qed.

Local Lemma clock_equivalent_sym F u v : clock_equivalent F u v -> clock_equivalent F v u.
Proof. unfold clock_equivalent; tauto. Qed.

Local Lemma clock_equivalent_trans F u v w :
  clock_equivalent F u v -> clock_equivalent F v w -> clock_equivalent F u w.
Proof.
  unfold clock_equivalent, reachable. intros [H1 H2] [H3 H4].
  split; etransitivity; eassumption.
Qed.

Local Lemma clock_equivalent_reach F u u' v v' :
  clock_equivalent F u u' -> clock_equivalent F v v' ->
  (reachable F u v <-> reachable F u' v').
Proof.
  unfold clock_equivalent, reachable. intros [Hu Hu'] [Hv Hv'].
  split; intros H.
  - etransitivity; [exact Hu'|]. etransitivity; [exact H|exact Hv].
  - etransitivity; [exact Hu|]. etransitivity; [exact H|exact Hv'].
Qed.

Local Definition accepts_args sig ts n (W : resource n) (vs : list val) :=
  Forall2 (fun E v => E n W v) (call_parameters sig ts) vs.

Local Definition closure_body_specification F t sig l self bs body n (W : resource n) :=
  forall (V : resource n) ts vs caller,
    resource_extends n W V ->
    length ts = time_arity sig -> call_constraints sig ts ->
    clock_equivalent F (call_time sig ts) caller ->
    reachable F t caller -> accepts_args sig ts n V vs ->
    expression_spec n F V (Leaf caller)
      (substs' (zip (self::bs) (VLoc l::vs)) body) (call_result sig ts).

Local Definition function_result F t sig :=
  location_spec F t (fun n W l d =>
    exists self bs body, d = inr (SClo self bs body) /\
      (forall ts, length ts = time_arity sig -> length bs = length (call_parameters sig ts)) /\
      all_lower_resources n W (closure_body_specification F t sig l self bs body)).

Local Lemma function_result_monotone F t sig : element_monotone (function_result F t sig).
Proof.
  apply location_spec_monotone.
  intros n W V l d Hext (self & bs & body & Hd & Harity & Hbody).
  exists self, bs, body. split; [exact Hd|]. split; [exact Harity|].
  eapply all_lower_resources_mono; [|exact Hext|exact Hbody].
  intros k A B HAB Hspec C ts vs caller HBC Hlen HΔ Hclock Hbefore Hargs.
  apply Hspec; [|exact Hlen|exact HΔ|exact Hclock|exact Hbefore|exact Hargs].
  eapply resource_extends_trans; eassumption.
Qed.

Local Lemma function_result_downward F t sig : element_downward (function_result F t sig).
Proof.
  apply location_spec_downward.
  intros n W l d (self & bs & body & Hd & Harity & Hbody). exists self, bs, body.
  split; [exact Hd|]. split; [exact Harity|exact (proj2 Hbody)].
Qed.

Local Lemma head_call_loc_invert G t σ α l vs σ' α' e' :
  head_step G t σ α (Call (VLoc l) (Val <$> vs)) σ' α' e' ->
  exists self bs body, σ !! l = Some (SClo self bs body) /\ σ' = σ /\ α' = α /\
    e' = substs' (zip (self::bs) (VLoc l::vs)) body.
Proof.
  intros Hstep. remember (Call (VLoc l) (Val <$> vs)) as src eqn:He.
  destruct Hstep; try destruct b; try discriminate He.
  subst ts. inversion He. subst.
  assert (vs0 = vs) by (eapply (list_fmap_eq_inj Val); [intros ? ? Hval; now injection Hval|eassumption]).
  subst vs0. eauto 8.
Qed.

Local Lemma arguments_step_index n (V : resource (S n)) Es vs :
  Forall element_downward Es -> Forall2 (fun E v => E (S n) V v) Es vs ->
  Forall2 (fun E v => E n (fst V) v) Es vs.
Proof.
  intros Hdown Hvs. revert Hdown. induction Hvs; intros Hdown.
  - constructor.
  - inversion Hdown; subst. constructor; [eapply H2; exact H|now apply IHHvs].
Qed.

Local Lemma argument_value_spec n (V : resource n) (Es : list element_spec) (vs : list val) (v : val) :
  Forall2 (fun E w => E n V w) Es vs -> v ∈ vs -> exists E, E ∈ Es /\ E n V v.
Proof.
  intros Hall. induction Hall; intros Hv; [inversion Hv|].
  apply elem_of_cons in Hv as [->|Hv].
  - exists x. split; [constructor|exact H].
  - destruct (IHHall Hv) as (E & Hmem & HE). exists E. split; [now constructor 2|exact HE].
Qed.

Local Lemma expression_spec_call n F (W : resource n) t caller l vs sig ts :
  length ts = time_arity sig -> call_constraints sig ts ->
  clock_equivalent F (call_time sig ts) caller -> reachable F t caller ->
  function_result F t sig n W (VLoc l) ->
  Forall element_downward (call_parameters sig ts) ->
  (forall V : resource n, resource_extends n W V -> accepts_args sig ts n V vs) ->
  (forall k (V : resource k) E v, E ∈ call_parameters sig ts -> E k V v ->
    value_visible_in_view F (resource_view k V) caller v) ->
  expression_spec n F W (Leaf caller) (Call (VLoc l) (Val <$> vs)) (call_result sig ts).
Proof.
  induction n as [|n IH]; intros Htime HΔ Hclock Hreachable Hfn Hdown Hargs Hvisible; [exact I|].
  assert (Hdescend : forall V : resource (S n), accepts_args sig ts (S n) V vs ->
    accepts_args sig ts n (fst V) vs).
  { intros V Hvs. eapply arguments_step_index; eassumption. }
  apply expression_spec_atomic.
  - apply IH; [exact Htime|exact HΔ|exact Hclock|exact Hreachable|now apply function_result_downward|exact Hdown| |exact Hvisible].
    intros V Hext. apply (Hdescend (V, snd W)). apply Hargs. exact (conj Hext (reflexivity _)).
  - intros V σ α G Hext Hstore Hgraph. pose proof (Hargs V Hext) as Hvals.
    pose proof (function_result_monotone F t sig (S n) W V (VLoc l) Hext Hfn) as Hcalled.
    destruct Hcalled as (l' & o & d & Heq & Hlook & Hbefore & self & bs & body & Hd & Harity & Hbody).
    injection Heq as Heq. subst l' d.
    pose proof (store_spec_view _ _ _ _ Hstore) as Hview.
    destruct (proj2 Hview l o _ Hlook) as [Hα (s & Hσ & Hshape)].
    destruct s; try discriminate Hshape. inversion Hshape; subst.
    split.
    + eapply ReadyCall; [exact Hσ|]. rewrite (Harity ts Htime).
      exact (Forall2_length _ _ _ Hvals).
    + split.
      * intros k Hk. cbn [locs location_expr locs_expr locs_val] in Hk.
        apply elem_of_union in Hk as [Hk|Hk].
        -- apply elem_of_singleton in Hk. subst k. unfold abef. rewrite Hα.
           unfold reachable in *. etransitivity; eassumption.
        -- rewrite <-list_fmap_compose in Hk. apply elem_of_union_list in Hk as (L & HL & Hk).
           apply list_elem_of_fmap in HL as (v & -> & Hvs).
           destruct (argument_value_spec _ _ _ _ _ Hvals Hvs) as (E & HE & Hv).
           eapply value_view_access; [exact Hview|eapply Hvisible; eassumption|exact Hk].
      * intros σ' α' e' Hhead.
        destruct (head_call_loc_invert _ _ _ _ _ _ _ _ _ Hhead) as (self' & bs' & body' & Hσ' & -> & -> & ->).
        pose proof (eq_trans (eq_sym Hσ') Hσ) as Hsame. inversion Hsame. subst.
        exists (fst V). split; [apply resource_extends_refl|]. split; [exact (proj1 Hstore)|].
        apply (proj1 Hbody); [apply resource_extends_refl|exact Htime|exact HΔ|exact Hclock|exact Hreachable|].
        now apply Hdescend.
Qed.

Local Definition closure_body_assumption F t sig self bs body k (W : resource k) :=
  forall (V : resource k) l, resource_extends k W V ->
    resource_view k V !! l = Some (t,inr (SClo self bs body)) ->
    function_result F t sig k V (VLoc l) ->
    closure_body_specification F t sig l self bs body k V.

Local Lemma closure_checks_at_lower_levels n (W : resource n) F t sig l self bs body :
  resource_view n W !! l = Some (t,inr (SClo self bs body)) ->
  (forall ts, length ts = time_arity sig -> length bs = length (call_parameters sig ts)) ->
  all_lower_resources n W (closure_body_assumption F t sig self bs body) ->
  all_lower_resources n W (closure_body_specification F t sig l self bs body).
Proof.
  induction n as [|n IH]; intros Hlook Harity Hassume; [exact I|].
  destruct Hassume as [Hnow Hprev].
  pose proof (IH (fst W) Hlook Harity Hprev) as Hchecks.
  split; [|exact Hchecks].
  apply (Hnow (fst W) l); [apply resource_extends_refl|exact Hlook|].
  exists l, t, (inr (SClo self bs body)). split; [reflexivity|].
  split; [exact Hlook|]. split; [apply rtc_refl|].
  exists self, bs, body. split; [reflexivity|]. now split.
Qed.

Local Lemma head_closure_invert G t σ α self bs body σ' α' e' :
  head_step G t σ α (Clo (Lam self bs body)) σ' α' e' ->
  exists l, l ∉ dom σ /\ l ∉ dom α /\
    σ' = <[l:=SClo self bs body]>σ /\ α' = <[l:=t]>α /\ e' = Val (VLoc l).
Proof.
  intros Hstep. remember (Clo (Lam self bs body)) as e eqn:He.
  destruct Hstep; try destruct b; try discriminate He.
  inversion He; subst. eauto 8.
Qed.

Local Lemma expression_spec_closure n F (W : resource n) t sig self bs body :
  (forall ts, length ts = time_arity sig -> length bs = length (call_parameters sig ts)) ->
  (forall l, l ∈ locs body ->
    exists o d, resource_view n W !! l = Some (o,d) /\ reachable F o t) ->
  all_lower_resources n W (closure_body_assumption F t sig self bs body) ->
  expression_spec n F W (Leaf t) (Clo (Lam self bs body)) (function_result F t sig).
Proof.
  induction n as [|n IH]; intros Harity Hvisible Hassume; [exact I|].
  apply expression_spec_atomic.
  - apply IH; [exact Harity|exact Hvisible|exact (proj2 Hassume)].
  - intros V σ α G Hext Hstore Hgraph.
    split; [apply ReadyClo|]. split.
    + intros l Hl. destruct (Hvisible l Hl) as (o & d & Hlook & Hreach).
      pose proof (lookup_weaken _ _ _ _ Hlook (resource_view_extends _ _ _ Hext)) as Hentry.
      destruct (proj2 (store_spec_view _ _ _ _ Hstore) l o d Hentry) as [Hα _].
      unfold abef. now rewrite Hα.
    + intros σ' α' e' Hhead.
      destruct (head_closure_invert _ _ _ _ _ _ _ _ _ _ Hhead) as (l & Hfresh & Hfreshα & -> & -> & ->).
      assert (Hempty : σ !! l = None) by (apply not_elem_of_dom; exact Hfresh).
      set (U := resource_insert n l t (SClo self bs body) empty_element (fst V)).
      assert (Hnew : resource_extends n (fst V) U).
      { unfold U. eapply resource_insert_grows; [exact (proj1 Hstore)|exact Hempty]. }
      exists U. split; [exact Hnew|]. split.
      * unfold U. apply resource_insert_store; [exact (proj1 Hstore)|exact Hempty| |discriminate].
        intros k A B q _ Hbad. destruct Hbad.
      * assert (Hentry : resource_view n U !! l = Some (t,inr (SClo self bs body))).
        { unfold U. rewrite resource_insert_view. apply lookup_insert_eq. }
        assert (Hframe : resource_extends n (fst W) U).
        { eapply resource_extends_trans; [exact (proj1 Hext)|exact Hnew]. }
        assert (Hbody : all_lower_resources n U (closure_body_assumption F t sig self bs body)).
        { eapply all_lower_resources_mono; [|exact Hframe|exact (proj2 Hassume)].
          intros k A B HAB Hcase C q HBC.
          apply Hcase. eapply resource_extends_trans; eassumption. }
        pose proof (closure_checks_at_lower_levels n U F t sig l self bs body Hentry Harity Hbody) as Hchecks.
        assert (Hfn : function_result F t sig n U (VLoc l)).
        { exists l, t, (inr (SClo self bs body)). split; [reflexivity|].
          split; [exact Hentry|]. split; [apply rtc_refl|].
          exists self, bs, body. split; [reflexivity|]. now split. }
        apply expression_spec_value.
        -- intros k A Hval. eapply location_spec_visible; exact Hval.
        -- intros A HA. eapply (function_result_monotone F t sig); eassumption.
        -- intros k A Hval. eapply (function_result_downward F t sig); eassumption.
Qed.

(* A type specifies when it is available and which values it accepts. The
   availability component is independent of the heap and of the value. *)
Local Definition interpreted_type := ((timestamp -> Prop) * element_spec)%type.
Local Definition type_family := list timestamp -> interpreted_type.
Local Definition type_assignment := string -> type_family.

Local Definition usable_at (A : interpreted_type) t : element_spec :=
  fun n W v => fst A t /\ snd A n W v.

Local Definition anchored F t (E : element_spec) : interpreted_type :=
  (fun u => reachable F t u, E).

Local Definition unavailable : interpreted_type := (fun _ => False, empty_element).

Local Definition type_assume (X : type_assignment) b (A : type_family) : type_assignment :=
  fun x => if decide (x ∈ binder_set b) then A else X x.

Local Definition type_shape (F : graph) (A : interpreted_type) : Prop :=
  (forall t u, reachable F t u -> fst A t -> fst A u) /\
  element_monotone (snd A) /\
  element_downward (snd A) /\
  (forall n (W : resource n) t v, fst A t -> snd A n W v ->
    value_visible_in_view F (resource_view n W) t v).

Local Definition type_agrees (A B : interpreted_type) : Prop :=
  (forall t, fst A t <-> fst B t) /\
  (forall n (W : resource n) v, snd A n W v <-> snd B n W v).

Local Definition family_shape F (A : type_family) : Prop :=
  (forall ts, type_shape F (A ts)) /\
  (forall ts us, Forall2 (clock_equivalent F) ts us -> type_agrees (A ts) (A us)).

Local Definition universal_type F (body : type_family -> interpreted_type) : interpreted_type :=
  (fun t => forall A, family_shape F A -> fst (body A) t,
   fun n W v => forall A, family_shape F A -> snd (body A) n W v).

Local Definition scalar_element (b : tbase) : element_spec := fun _ _ v => source_base v b.

Local Definition scalar_type b : interpreted_type := (fun _ => True, scalar_element b).

Local Definition sum_result F t (P Q : element_spec) :=
  location_spec F t (fun n W _ d =>
    (exists v, d = inr (SInL v) /\ P n W v) \/
    (exists v, d = inr (SInR v) /\ Q n W v)).

Local Definition delayed_element (P : element_spec) n : resource n -> val -> Prop :=
  match n with
  | O => fun _ _ => True
  | S n => fun W v => P n (fst W) v
  end.

Local Definition folded_result F t (P : element_spec) : element_spec :=
  fun n W v => exists u, v = VFold u /\
    location_spec F t (fun k V l _ => delayed_element P k V (VLoc l)) n W u.

Local Fixpoint recursive_approximation F t (B : element_spec -> element_spec) (bound : nat) : element_spec :=
  match bound with
  | O => empty_element
  | S k => fun i W v =>
      if decide (i = k) then folded_result F t (B (recursive_approximation F t B k)) i W v
      else recursive_approximation F t B k i W v
  end.

Local Definition recursive_element F t (B : element_spec -> element_spec) : element_spec :=
  fun n W v => recursive_approximation F t B (S n) n W v.

Local Fixpoint interpret_type (F : graph) (ρ : typ) (η : clock_assignment) (X : type_assignment)
    (actuals : list timestamp) {struct ρ} : interpreted_type :=
  match ρ with
  | TVar x => X x actuals
  | TBase b => scalar_type b
  | TTypat σ δ => anchored F (η δ) (interpret_at F σ η X (η δ))
  | TLam b ρ =>
      match actuals with
      | [] => unavailable
      | t::ts => interpret_type F ρ (clock_bind η b t) X ts
      end
  | TApp ρ δ => interpret_type F ρ η X (η δ :: actuals)
  | TForall b _ ρ =>
      universal_type F (fun A => interpret_type F ρ η (type_assume X b A) actuals)
  | TRec x σ δ =>
      let t := η δ in
      anchored F t (recursive_element F t (fun E =>
        interpret_at F σ η (type_assume X (BNamed x) (fun _ => anchored F t E)) t))
  end
with interpret_at (F : graph) (σ : typat) (η : clock_assignment) (X : type_assignment)
    (t : timestamp) {struct σ} : element_spec :=
  match σ with
  | TArray ρ =>
      let A := interpret_type F ρ η X [] in array_result F t (fst A) (snd A)
  | TProd ρ1 ρ2 =>
      product_result F t (usable_at (interpret_type F ρ1 η X []) t)
                         (usable_at (interpret_type F ρ2 η X []) t)
  | TSum ρ1 ρ2 =>
      sum_result F t (usable_at (interpret_type F ρ1 η X []) t)
                     (usable_at (interpret_type F ρ2 η X []) t)
  | TArrow bs Δ δ ρs ρ =>
      let instantiate := fun ts => clock_extend η (bmap bs ts) in
      function_result F t {|
        time_arity := length bs;
        call_constraints := fun ts => clock_constraints F (instantiate ts) Δ;
        call_time := fun ts => instantiate ts δ;
        call_parameters := fun ts =>
          let θ := instantiate ts in
          (fun r => usable_at (interpret_type F r θ X []) (θ δ)) <$> ρs;
        call_result := fun ts =>
          let θ := instantiate ts in usable_at (interpret_type F ρ θ X []) (θ δ)
      |}
  end.

Local Definition element_prefix n (P Q : element_spec) : Prop :=
  forall k, (k <= n)%nat -> forall (W : resource k) v, P k W v <-> Q k W v.

Local Definition type_prefix n (A B : interpreted_type) : Prop :=
  (forall t, fst A t <-> fst B t) /\ element_prefix n (snd A) (snd B).

Local Lemma element_prefix_weaken n m P Q :
  (m <= n)%nat -> element_prefix n P Q -> element_prefix m P Q.
Proof. intros Hle H k HK W v. apply H. lia. Qed.

Local Lemma type_prefix_weaken n m A B :
  (m <= n)%nat -> type_prefix n A B -> type_prefix m A B.
Proof. intros Hle [Hscope Hvalue]. split; [exact Hscope|eapply element_prefix_weaken; eassumption]. Qed.

Local Lemma recursive_approximation_agrees F t B bound k (W : resource k) v :
  (k < bound)%nat -> recursive_approximation F t B bound k W v <-> recursive_element F t B k W v.
Proof.
  induction bound as [|bound IH]; intros Hk; [lia|].
  destruct (decide (k = bound)) as [->|Hne]; [reflexivity|].
  cbn [recursive_approximation]. rewrite decide_False by exact Hne.
  apply IH. lia.
Qed.

Local Lemma recursive_approximation_outside F t B bound k (W : resource k) v :
  (bound <= k)%nat -> ~ recursive_approximation F t B bound k W v.
Proof.
  induction bound as [|bound IH]; intros Hk.
  - exact (fun H => H).
  - cbn [recursive_approximation]. rewrite decide_False by lia. apply IH. lia.
Qed.

Local Lemma folded_result_compare F t u P Q n (W : resource n) v :
  clock_equivalent F t u ->
  (forall l, delayed_element P n W (VLoc l) <-> delayed_element Q n W (VLoc l)) ->
  (folded_result F t P n W v <-> folded_result F u Q n W v).
Proof.
  intros Htu Hdelay.
  unfold folded_result, location_spec.
  assert (Hscope : forall owner, reachable F owner t <-> reachable F owner u).
  { intros owner. apply clock_equivalent_reach; [apply clock_equivalent_refl|exact Htu]. }
  split.
  - intros (w & Hv & l & o & d & Hw & Hlook & Hreach & Hf).
    exists w. split; [exact Hv|]. exists l, o, d. split; [exact Hw|]. split; [exact Hlook|].
    split; [now apply Hscope|now apply Hdelay].
  - intros (w & Hv & l & o & d & Hw & Hlook & Hreach & Hf).
    exists w. split; [exact Hv|]. exists l, o, d. split; [exact Hw|]. split; [exact Hlook|].
    split; [now apply Hscope|now apply Hdelay].
Qed.

Local Lemma recursive_element_unfold F t B n (W : resource n) v :
  (forall k P Q, element_prefix k P Q -> element_prefix k (B P) (B Q)) ->
  (recursive_element F t B n W v <-> folded_result F t (B (recursive_element F t B)) n W v).
Proof.
  intros HB. unfold recursive_element at 1. cbn [recursive_approximation].
  rewrite decide_True by reflexivity. apply folded_result_compare; [apply clock_equivalent_refl|].
  destruct n as [|n]; intros l; [tauto|]. change
    (B (recursive_approximation F t B (S n)) n (fst W) (VLoc l) <->
     B (recursive_element F t B) n (fst W) (VLoc l)).
  assert (Happrox : element_prefix n (recursive_approximation F t B (S n)) (recursive_element F t B)).
  { intros k Hk V u. apply recursive_approximation_agrees. lia. }
  exact (HB n _ _ Happrox n (Nat.le_refl n) (fst W) (VLoc l)).
Qed.

Local Lemma recursive_element_compare F t u B C n :
  clock_equivalent F t u ->
  (forall k, (k <= n)%nat -> forall P Q, element_prefix k P Q -> element_prefix k (B P) (C Q)) ->
  element_prefix n (recursive_element F t B) (recursive_element F u C).
Proof.
  intros Htu HBC k Hk W v. unfold recursive_element.
  assert (Happrox : forall fuel, element_prefix n (recursive_approximation F t B fuel)
                                               (recursive_approximation F u C fuel)).
  { induction fuel as [|fuel IH]; intros i Hi V w; [tauto|].
    cbn [recursive_approximation]. destruct (decide (i = fuel)) as [Heq|Hne]; [|now apply IH].
    apply folded_result_compare; [exact Htu|].
    destruct i as [|i]; intros l; [tauto|].
    cbn [delayed_element].
    assert (Hle : (i <= n)%nat) by lia.
    exact (HBC i Hle _ _ (element_prefix_weaken _ _ _ _ Hle IH)
      i (Nat.le_refl i) (fst V) (VLoc l)). }
  now apply Happrox.
Qed.

Local Lemma folded_result_visible F t P n (W : resource n) u v :
  reachable F t u -> folded_result F t P n W v ->
  value_visible_in_view F (resource_view n W) u v.
Proof.
  intros Hreach (w & -> & l & o & d & -> & Hview & Ho & Hdelay) k Hk.
  change (k ∈ ({[l]} : gset loc)) in Hk. apply elem_of_singleton in Hk. subst k.
  exists o, d. split; [exact Hview|]. unfold reachable in *. etransitivity; eassumption.
Qed.

Local Lemma element_prefix_refl n P : element_prefix n P P.
Proof. intros k Hk W v. reflexivity. Qed.

Local Lemma element_prefix_sym n P Q : element_prefix n P Q -> element_prefix n Q P.
Proof. intros H k Hk W v. symmetry. now apply H. Qed.

Local Lemma type_agrees_prefix n A B : type_agrees A B -> type_prefix n A B.
Proof. intros [Ht Hv]. split; [exact Ht|intros k _ W v; apply Hv]. Qed.

Local Lemma type_prefix_usable F n A B t u :
  (forall x y, reachable F x y -> fst A x -> fst A y) ->
  type_prefix n A B -> clock_equivalent F t u ->
  element_prefix n (usable_at A t) (usable_at B u).
Proof.
  intros Hmono [Ht Hv] [Htu Hut] k Hk W v. unfold usable_at.
  rewrite <- (Ht u), (Hv k Hk W v).
  split; intros [? ?]; split; try assumption; eapply Hmono; eassumption.
Qed.

Local Lemma usable_prefix_same n A B t :
  type_prefix n A B -> element_prefix n (usable_at A t) (usable_at B t).
Proof. intros [Ht Hv] k Hk W v. unfold usable_at. rewrite (Ht t), (Hv k Hk W v). reflexivity. Qed.

Local Lemma expression_spec_post_prefix n F (W : resource n) T e P Q :
  element_prefix n P Q -> expression_spec n F W T e P -> expression_spec n F W T e Q.
Proof.
  revert W T e. induction n as [|n IH]; intros W T e Hrel;
    cbn [expression_spec]; [tauto|].
  assert (Hlow : element_prefix n P Q) by (eapply (element_prefix_weaken (S n) n); [lia|exact Hrel]).
  intros [Hprev Hnow]. split; [now apply IH|].
  intros V σ α G Hext Hstore HG.
  destruct (Hnow V σ α G Hext Hstore HG) as (Hsafe & Hde & Hv & Hnext).
  split; [exact Hsafe|]. split; [exact Hde|]. split.
  - destruct e; try exact I. destruct Hv as [Hleaf Hv]. split; [exact Hleaf|].
    apply (Hrel (S n) (Nat.le_refl _) V v), Hv.
  - intros σ' α' G' T' e' Hstep HG'.
    destruct (Hnext _ _ _ _ _ Hstep HG') as (V' & Hext' & Hstore' & Hcont).
    exists V'. split; [exact Hext'|]. split; [exact Hstore'|now apply IH].
Qed.

Local Lemma location_spec_compare F t u P Q n (W : resource n) v :
  clock_equivalent F t u ->
  (forall l d, P n W l d <-> Q n W l d) ->
  (location_spec F t P n W v <-> location_spec F u Q n W v).
Proof.
  intros Htu HP. unfold location_spec.
  assert (HR : forall o, reachable F o t <-> reachable F o u).
  { intros o. apply clock_equivalent_reach; [apply clock_equivalent_refl|exact Htu]. }
  split; intros (l & o & d & Hv & Hw & Hreach & HC); exists l, o, d;
    refine (conj Hv (conj Hw _)).
  all: split; [apply (HR o), Hreach|apply (HP l d), HC].
Qed.

Local Lemma array_spec_compare n (W : resource n) l P Q :
  element_prefix n P Q -> (array_spec_at n W l P <-> array_spec_at n W l Q).
Proof.
  induction n as [|n IH]; intros Hrel; [tauto|].
  assert (Hlow : element_prefix n P Q) by (eapply (element_prefix_weaken (S n) n); [lia|exact Hrel]).
  cbn [array_spec_at]. rewrite (IH _ Hlow).
  split; intros [Harr (R & HR & HE)]; (split; [exact Harr|exists R; split; [exact HR|]]).
  - intros V v. rewrite (HE V v). exact (Hlow n (Nat.le_refl n) V v).
  - intros V v. rewrite (HE V v). symmetry. exact (Hlow n (Nat.le_refl n) V v).
Qed.

Local Lemma product_result_compare F t u P Q P' Q' n :
  clock_equivalent F t u -> element_prefix n P P' -> element_prefix n Q Q' ->
  element_prefix n (product_result F t P Q) (product_result F u P' Q').
Proof.
  intros Htu HP HQ k Hk W v. apply location_spec_compare; [exact Htu|].
  intros l d. unfold product_result in *.
  split; intros (v1 & v2 & Hd & H1 & H2); exists v1, v2;
    refine (conj Hd _).
  all: split; [apply (HP k Hk W v1), H1|apply (HQ k Hk W v2), H2].
Qed.

Local Lemma sum_result_compare F t u P Q P' Q' n :
  clock_equivalent F t u -> element_prefix n P P' -> element_prefix n Q Q' ->
  element_prefix n (sum_result F t P Q) (sum_result F u P' Q').
Proof.
  intros Htu HP HQ k Hk W v. apply location_spec_compare; [exact Htu|].
  intros l d. split; intros [(w & Hd & Hleft)|(w & Hd & Hright)];
    [left|right|left|right]; exists w; split; try exact Hd;
    first [apply (HP k Hk W w), Hleft|apply (HQ k Hk W w), Hright].
Qed.

Local Lemma array_result_compare F t u A B P Q n :
  clock_equivalent F t u -> (forall o, A o <-> B o) -> element_prefix n P Q ->
  element_prefix n (array_result F t A P) (array_result F u B Q).
Proof.
  intros Htu Hscope HP k Hk W v. apply location_spec_compare; [exact Htu|].
  intros l d. assert (Harray : array_spec_at k W l P <-> array_spec_at k W l Q).
  { apply array_spec_compare. eapply element_prefix_weaken; eassumption. }
  split; intros (o & size & Hd & Hw & Ho & Hspec); exists o, size;
    refine (conj Hd (conj Hw _)).
  all: split; [apply (Hscope o), Ho|apply Harray, Hspec].
Qed.

Local Lemma all_lower_resources_transform n (W : resource n) (P Q : forall k, resource k -> Prop) :
  (forall k, (k <= n)%nat -> forall A, P k A -> Q k A) ->
  all_lower_resources n W P -> all_lower_resources n W Q.
Proof.
  induction n as [|n IH]; intros HP HW; [exact I|].
  destruct HW as [Hnow Hlow]. split.
  - apply HP; [lia|exact Hnow].
  - apply IH; [|exact Hlow]. intros k Hk V HV. apply HP; [lia|exact HV].
Qed.

Local Lemma arguments_prefix n k (W : resource k) (Ps Qs : list element_spec) (vs : list val) :
  (k <= n)%nat -> Forall2 (element_prefix n) Ps Qs ->
  (Forall2 (fun E v => E k W v) Ps vs <-> Forall2 (fun E v => E k W v) Qs vs).
Proof.
  intros Hk Hrel. revert vs. induction Hrel as [|P Q Ps Qs HP Htail IH]; intros vs.
  - reflexivity.
  - destruct vs as [|v vs].
    + split; inversion 1.
    + rewrite !Forall2_cons, (HP k Hk W v), IH. reflexivity.
Qed.

Local Definition signature_prefix F n sig sig' :=
  time_arity sig = time_arity sig' /\
  forall ts, length ts = time_arity sig ->
    (call_constraints sig ts <-> call_constraints sig' ts) /\
    clock_equivalent F (call_time sig ts) (call_time sig' ts) /\
    Forall2 (element_prefix n) (call_parameters sig ts) (call_parameters sig' ts) /\
    element_prefix n (call_result sig ts) (call_result sig' ts).

Local Lemma signature_prefix_sym F n sig sig' :
  signature_prefix F n sig sig' -> signature_prefix F n sig' sig.
Proof.
  intros [Har Hrel]. split; [symmetry; exact Har|].
  intros ts Hlen. destruct (Hrel ts (eq_trans Hlen (eq_sym Har))) as (Hc & Htime & Hargs & Hout).
  split; [symmetry; exact Hc|]. split; [now apply clock_equivalent_sym|].
  split; [|now apply element_prefix_sym].
  induction Hargs; constructor; auto using element_prefix_sym.
Qed.

Local Lemma closure_body_specification_transfer F n t u sig sig' l self bs body k (W : resource k) :
  (k <= n)%nat -> clock_equivalent F t u -> signature_prefix F n sig sig' ->
  closure_body_specification F t sig l self bs body k W ->
  closure_body_specification F u sig' l self bs body k W.
Proof.
  intros Hk Htu [Har Hsig] Hbody A ts vs caller Hext Hlen Hc Htime Hcurrent Hvals.
  assert (Hlen' : length ts = time_arity sig) by (rewrite Har; exact Hlen).
  destruct (Hsig ts Hlen') as (Hpre & Hcall & Hargs & Hresult).
  eapply expression_spec_post_prefix; [exact (element_prefix_weaken _ _ _ _ Hk Hresult)|].
  eapply Hbody; [exact Hext|exact Hlen'|now apply Hpre| | |].
  - eapply clock_equivalent_trans; eassumption.
  - apply (clock_equivalent_reach F t u caller caller Htu (clock_equivalent_refl F caller)).
    exact Hcurrent.
  - apply (arguments_prefix n k A _ _ vs Hk Hargs), Hvals.
Qed.

Local Lemma function_result_compare F t u sig sig' n :
  clock_equivalent F t u -> signature_prefix F n sig sig' ->
  element_prefix n (function_result F t sig) (function_result F u sig').
Proof.
  intros Htu Hsig k Hk W v. apply location_spec_compare; [exact Htu|].
  intros l d. split; intros (self & bs & body & Hd & Harity & Hbody);
    exists self, bs, body; refine (conj Hd _); split.
  - intros ts Hlen. pose proof (proj1 Hsig) as Har.
    destruct (proj2 Hsig ts (eq_trans Hlen (eq_sym Har))) as (_ & _ & Hargs & _).
    rewrite (Harity ts (eq_trans Hlen (eq_sym Har))). exact (Forall2_length _ _ _ Hargs).
  - eapply all_lower_resources_transform; [|exact Hbody].
    intros j Hj A Hcheck. eapply (closure_body_specification_transfer F n t u sig sig');
      [lia|exact Htu|exact Hsig|exact Hcheck].
  - intros ts Hlen. pose proof (proj1 Hsig) as Har.
    destruct (proj2 Hsig ts Hlen) as (_ & _ & Hargs & _).
    rewrite (Harity ts (eq_trans Hlen Har)). symmetry. exact (Forall2_length _ _ _ Hargs).
  - eapply all_lower_resources_transform; [|exact Hbody].
    intros j Hj A Hcheck. eapply (closure_body_specification_transfer F n u t sig' sig);
      [lia|now apply clock_equivalent_sym|now apply signature_prefix_sym|exact Hcheck].
Qed.

Local Lemma constraint_endpoints Δ x y :
  (x,y) ∈ Δ -> x ∈ fv_constraints Δ /\ y ∈ fv_constraints Δ.
Proof.
  revert x y. unfold fv_constraints.
  apply (set_fold_ind_L (fun (X : gset string) (C : constraints) =>
    forall x y, (x,y) ∈ C -> x ∈ X /\ y ∈ X)).
  - intros x y H. set_solver.
  - intros [a b] C X Hfresh IH x y H. apply elem_of_union in H as [H|H].
    + apply elem_of_singleton in H. inversion H; subst. set_solver.
    + destruct (IH x y H). set_solver.
Qed.

Local Lemma clock_constraints_compare F Δ η θ :
  (forall x, x ∈ fv_constraints Δ -> clock_equivalent F (η x) (θ x)) ->
  (clock_constraints F η Δ <-> clock_constraints F θ Δ).
Proof.
  intros Hrel. split; intros H x y Hmem;
    destruct (constraint_endpoints Δ x y Hmem) as [Hx Hy];
    apply (clock_equivalent_reach F _ _ _ _ (Hrel x Hx) (Hrel y Hy)); now apply H.
Qed.

Local Lemma clock_bind_related F b t u η θ x :
  clock_equivalent F t u ->
  (x ∉ binder_set b -> clock_equivalent F (η x) (θ x)) ->
  clock_equivalent F (clock_bind η b t x) (clock_bind θ b u x).
Proof.
  intros Htu Hscope. unfold clock_bind.
  destruct (decide (x ∈ binder_set b)); [exact Htu|now apply Hscope].
Qed.

Local Lemma clock_extend_cons η b bs t ts x :
  clock_extend η (bmap (b::bs) (t::ts)) x =
  clock_extend (clock_bind η b t) (bmap bs ts) x.
Proof.
  assert (Heq : bmap (b::bs) (t::ts) = bmap bs ts ∪ binsert b t ∅).
  { unfold bmap. rewrite extend_cons. unfold extend. apply binserts_union_empty. }
  rewrite Heq. unfold clock_extend. rewrite clock_bind_extend. unfold clock_extend. rewrite lookup_union.
  assert (Hoption : forall a b : option timestamp, default (η x) (a ∪ b) = default (default (η x) b) a).
  { intros [] []; reflexivity. }
  apply Hoption.
Qed.

Local Lemma clock_extend_related F bs ts us η θ x :
  length bs = length ts -> Forall2 (clock_equivalent F) ts us ->
  (x ∉ binders_set bs -> clock_equivalent F (η x) (θ x)) ->
  clock_equivalent F (clock_extend η (bmap bs ts) x) (clock_extend θ (bmap bs us) x).
Proof.
  revert ts us η θ. induction bs as [|b bs IH]; intros ts us η θ Hlen Hactuals Hscope.
  - destruct ts; [|discriminate Hlen]. inversion Hactuals; subst.
    change (clock_equivalent F (η x) (θ x)). apply Hscope.
    change (x ∉ (∅ : gset string)). set_solver.
  - destruct ts as [|t ts]; [discriminate Hlen|]. destruct us as [|u us]; [now inversion Hactuals|].
    apply Forall2_cons in Hactuals as [Htu Hrest].
    rewrite !clock_extend_cons. apply IH; [now injection Hlen|exact Hrest|].
    intros Hout. apply clock_bind_related; [exact Htu|].
    intros Hnot. apply Hscope. rewrite binders_set_cons. set_solver.
Qed.

Local Definition monotone_scopes F (X : type_assignment) :=
  forall x ts t u, reachable F t u -> fst (X x ts) t -> fst (X x ts) u.

Local Lemma type_assume_monotone_scopes F X b A :
  monotone_scopes F X ->
  (forall ts t u, reachable F t u -> fst (A ts) t -> fst (A ts) u) ->
  monotone_scopes F (type_assume X b A).
Proof.
  intros HX HA x ts t u Htu. unfold type_assume.
  destruct (decide (x ∈ binder_set b)); [now apply HA|now apply HX].
Qed.

Local Lemma family_scope_monotone F A :
  family_shape F A -> forall ts t u, reachable F t u -> fst (A ts) t -> fst (A ts) u.
Proof. intros [Hshape _] ts. exact (proj1 (Hshape ts)). Qed.

Local Lemma interpret_scope_monotone F ρ η X ts t u :
  monotone_scopes F X -> reachable F t u ->
  fst (interpret_type F ρ η X ts) t -> fst (interpret_type F ρ η X ts) u.
Proof.
  revert η X ts. induction ρ as [x|b|σ d|b ρ IH|ρ IH d|b k ρ IH|x σ d];
    intros η X ts HX Htu Htype; cbn [interpret_type anchored scalar_type unavailable universal_type fst] in *.
  - eapply HX; eassumption.
  - exact I.
  - unfold reachable in *. etransitivity; eassumption.
  - destruct ts as [|s ts]; [exact Htype|]. apply IH; assumption.
  - apply IH; assumption.
  - intros A HA. eapply IH; [|exact Htu|exact (Htype A HA)].
    apply type_assume_monotone_scopes; [exact HX|now apply family_scope_monotone].
  - unfold reachable in *. etransitivity; eassumption.
Qed.

Local Definition related_families F n (A B : type_family) :=
  forall ts us, Forall2 (clock_equivalent F) ts us -> type_prefix n (A ts) (B us).

Local Definition related_types F n (L : gset string) (X Y : type_assignment) :=
  forall x, x ∈ L -> related_families F n (X x) (Y x).

Local Lemma type_assume_related F n L b X Y A B :
  related_types F n (L ∖ binder_set b) X Y -> related_families F n A B ->
  related_types F n L (type_assume X b A) (type_assume Y b B).
Proof.
  intros Henv Hbody x Hx. unfold type_assume.
  destruct (decide (x ∈ binder_set b)); [exact Hbody|]. apply Henv. set_solver.
Qed.

Local Lemma family_shape_related F n A : family_shape F A -> related_families F n A A.
Proof. intros [_ Hscope] ts us Hrel. apply type_agrees_prefix, Hscope, Hrel. Qed.

Local Lemma list_clocks_refl F ts : Forall2 (clock_equivalent F) ts ts.
Proof. induction ts; constructor; auto using clock_equivalent_refl. Qed.

Local Lemma anchored_prefix F n t u P Q :
  clock_equivalent F t u -> element_prefix n P Q ->
  type_prefix n (anchored F t P) (anchored F u Q).
Proof.
  intros Htu HP. split; [|exact HP]. intros v.
  apply clock_equivalent_reach; [exact Htu|apply clock_equivalent_refl].
Qed.

Local Lemma universal_prefix F n P Q :
  (forall A, family_shape F A -> type_prefix n (P A) (Q A)) ->
  type_prefix n (universal_type F P) (universal_type F Q).
Proof.
  intros HE. split.
  - intros t. split; intros H A HA; apply (proj1 (HE A HA) t), (H A HA).
  - intros k Hk W v. split; intros H A HA; apply (proj2 (HE A HA) k Hk W v), (H A HA).
Qed.

Local Definition type_comparable F ρ :=
  forall n η θ X Y ts us,
    monotone_scopes F X -> monotone_scopes F Y ->
    (forall x, x ∈ fv_typ ρ -> clock_equivalent F (η x) (θ x)) ->
    related_types F n (fvv_typ ρ) X Y ->
    Forall2 (clock_equivalent F) ts us ->
    type_prefix n (interpret_type F ρ η X ts) (interpret_type F ρ θ Y us).

Local Definition atom_comparable F σ :=
  forall n η θ X Y t u,
    monotone_scopes F X -> monotone_scopes F Y ->
    (forall x, x ∈ fv_typat σ -> clock_equivalent F (η x) (θ x)) ->
    related_types F n (fvv_typat σ) X Y ->
    clock_equivalent F t u ->
    element_prefix n (interpret_at F σ η X t) (interpret_at F σ θ Y u).

Section TypeComparison.
Context (F : graph).

Local Fixpoint interpret_comparable_type (ρ : typ) {struct ρ} : type_comparable F ρ
with interpret_comparable_atom (σ : typat) {struct σ} : atom_comparable F σ.
Proof.
  - rename interpret_comparable_type into CT. rename interpret_comparable_atom into CA.
    destruct ρ as [x|base|σ d|b ρ|ρ d|b k ρ|x σ d];
      intros n η θ X Y ts us HX HY Htime Hvars Hargs; cbn [interpret_type].
    + apply Hvars; [clear CT CA; simpl; set_solver|exact Hargs].
    + split; [intros; reflexivity|apply element_prefix_refl].
    + assert (Hd : clock_equivalent F (η d) (θ d)).
      { apply Htime. clear CT CA. cbn [fv_typ]. set_solver. }
      apply anchored_prefix; [exact Hd|].
      eapply (CA σ); [exact HX|exact HY| |exact Hvars|exact Hd].
      intros y Hy. apply Htime. clear CT CA. cbn [fv_typ]. set_solver.
    + destruct ts as [|t ts], us as [|u us].
      * split; [intros; reflexivity|apply element_prefix_refl].
      * inversion Hargs.
      * inversion Hargs.
      * apply Forall2_cons in Hargs as [Htu Htail].
        apply (CT ρ); [exact HX|exact HY| |exact Hvars|exact Htail].
        intros y Hy. apply clock_bind_related; [exact Htu|].
        intros Hnot. apply Htime. clear CT CA. cbn [fv_typ]. set_solver.
    + apply (CT ρ); [exact HX|exact HY| |exact Hvars|].
      * intros y Hy. apply Htime. clear CT CA. cbn [fv_typ]. set_solver.
      * constructor; [apply Htime|exact Hargs].
        clear CT CA. cbn [fv_typ]. set_solver.
    + apply universal_prefix. intros A HA. apply (CT ρ).
      * apply type_assume_monotone_scopes; [exact HX|now apply family_scope_monotone].
      * apply type_assume_monotone_scopes; [exact HY|now apply family_scope_monotone].
      * exact Htime.
      * apply type_assume_related; [exact Hvars|now apply family_shape_related].
      * exact Hargs.
    + assert (Hd : clock_equivalent F (η d) (θ d)).
      { apply Htime. clear CT CA. cbn [fv_typ]. set_solver. }
      apply anchored_prefix; [exact Hd|].
      apply recursive_element_compare; [exact Hd|].
      intros j Hj P Q HP. apply (CA σ).
      * apply type_assume_monotone_scopes; [exact HX|].
        cbn [anchored fst]. unfold reachable. intros ? ? ? ?. etransitivity; eassumption.
      * apply type_assume_monotone_scopes; [exact HY|].
        cbn [anchored fst]. unfold reachable. intros ? ? ? ?. etransitivity; eassumption.
      * intros z Hz. apply Htime. clear CT CA. cbn [fv_typ]. set_solver.
      * apply type_assume_related.
        -- intros y Hy ats aus Hrel. eapply type_prefix_weaken; [exact Hj|].
           exact (Hvars y Hy ats aus Hrel).
        -- intros ats aus _. now apply anchored_prefix.
      * exact Hd.
  - rename interpret_comparable_type into CT. rename interpret_comparable_atom into CA.
    destruct σ as [ρ|ρ1 ρ2|ρ1 ρ2|bs Δ d ρs ρ];
      intros n η θ X Y t u HX HY Htime Hvars Htu; cbn [interpret_at].
    + pose proof (CT ρ n η θ X Y [] [] HX HY Htime Hvars (list_clocks_refl F [])) as HA.
      apply array_result_compare; [exact Htu|exact (proj1 HA)|exact (proj2 HA)].
    + apply product_result_compare; [exact Htu| |];
        (apply (type_prefix_usable F); [intros; eapply interpret_scope_monotone; eassumption| |exact Htu]).
      * apply (CT ρ1); [exact HX|exact HY| | |constructor].
        -- intros y Hy. apply Htime. clear CT CA. cbn [fv_typat]. set_solver.
        -- intros y Hy. apply Hvars. clear CT CA. cbn [fvv_typat]. set_solver.
      * apply (CT ρ2); [exact HX|exact HY| | |constructor].
        -- intros y Hy. apply Htime. clear CT CA. cbn [fv_typat]. set_solver.
        -- intros y Hy. apply Hvars. clear CT CA. cbn [fvv_typat]. set_solver.
    + apply sum_result_compare; [exact Htu| |];
        (apply (type_prefix_usable F); [intros; eapply interpret_scope_monotone; eassumption| |exact Htu]).
      * apply (CT ρ1); [exact HX|exact HY| | |constructor].
        -- intros y Hy. apply Htime. clear CT CA. cbn [fv_typat]. set_solver.
        -- intros y Hy. apply Hvars. clear CT CA. cbn [fvv_typat]. set_solver.
      * apply (CT ρ2); [exact HX|exact HY| | |constructor].
        -- intros y Hy. apply Htime. clear CT CA. cbn [fv_typat]. set_solver.
        -- intros y Hy. apply Hvars. clear CT CA. cbn [fvv_typat]. set_solver.
    + apply function_result_compare; [exact Htu|].
      split; [reflexivity|]. intros ts Hlen.
      set (η' := clock_extend η (bmap bs ts)).
      set (θ' := clock_extend θ (bmap bs ts)).
      assert (Hbound : forall x,
        x ∈ ({[d]} ∪ fv_constraints Δ ∪ fv_typ ρ ∪ ⋃ (fv_typ <$> ρs) : gset string) ->
        clock_equivalent F (η' x) (θ' x)).
      { intros x Hmem. apply clock_extend_related; [symmetry; exact Hlen|apply list_clocks_refl|].
        intros Hx. apply Htime. clear CT CA. cbn [fv_typat]. set_solver. }
      assert (Hd : clock_equivalent F (η' d) (θ' d)).
      { apply Hbound. clear CT CA. set_solver. }
      split; [apply clock_constraints_compare; intros x Hx; apply Hbound; clear CT CA; set_solver|].
      split; [exact Hd|]. split.
      * change (Forall2 (element_prefix n)
          ((fun r => usable_at (interpret_type F r η' X []) (η' d)) <$> ρs)
          ((fun r => usable_at (interpret_type F r θ' Y []) (θ' d)) <$> ρs)).
        assert (Htimes : forall x, x ∈ ⋃ (fv_typ <$> ρs) -> clock_equivalent F (η' x) (θ' x)).
        { intros x Hx. apply Hbound. clear CT CA. set_solver. }
        assert (Hrel : related_types F n (⋃ (fvv_typ <$> ρs)) X Y).
        { intros x Hx. apply Hvars. clear CT CA. cbn [fvv_typat]. set_solver. }
        clear Htime Hvars Hbound Hlen. revert Htimes Hrel.
        induction ρs as [|r rs IH]; intros Htimes Hrel.
        -- constructor.
        -- rewrite !fmap_cons. constructor.
           ++ apply (type_prefix_usable F).
              ** intros; eapply interpret_scope_monotone; eassumption.
              ** apply (CT r); [exact HX|exact HY| | |constructor].
                 --- intros x Hx. apply Htimes. clear CT CA.
                     rewrite fmap_cons, union_list_cons. set_solver.
                 --- intros x Hx. apply Hrel. clear CT CA.
                     rewrite fmap_cons, union_list_cons. set_solver.
              ** exact Hd.
           ++ apply IH.
              ** intros x Hx. apply Htimes. clear CT CA.
                 rewrite fmap_cons, union_list_cons. set_solver.
              ** intros x Hx. apply Hrel. clear CT CA.
                 rewrite fmap_cons, union_list_cons. set_solver.
      * apply (type_prefix_usable F).
        -- intros; eapply interpret_scope_monotone; eassumption.
        -- apply (CT ρ); [exact HX|exact HY| | |constructor].
           ++ intros x Hx. apply Hbound. clear CT CA. set_solver.
           ++ intros x Hx. apply Hvars. clear CT CA. cbn [fvv_typat]. set_solver.
        -- exact Hd.
Defined.
End TypeComparison.

Local Lemma view_visible_later F W t u v :
  reachable F t u -> value_visible_in_view F W t v -> value_visible_in_view F W u v.
Proof.
  intros Htu H vloc Hvloc. destruct (H vloc Hvloc) as (o & d & Hview & Htime).
  exists o, d. split; [exact Hview|]. unfold reachable in *. etransitivity; eassumption.
Qed.

Local Lemma anchored_type_shape F t E :
  element_monotone E -> element_downward E ->
  (forall n W v, E n W v -> value_visible_in_view F (resource_view n W) t v) ->
  type_shape F (anchored F t E).
Proof.
  intros Hmono Hdown Hvisible. split.
  - cbn [anchored fst]. unfold reachable. intros ? ? ? ?. etransitivity; eassumption.
  - split; [exact Hmono|]. split; [exact Hdown|].
    intros n W u v Htu Hv. eapply view_visible_later; [exact Htu|now apply Hvisible].
Qed.

Local Lemma shape_usable_monotone F A t : type_shape F A -> element_monotone (usable_at A t).
Proof.
  intros (_ & Hmono & _). intros n W V v Hext [Ht Hv].
  split; [exact Ht|eapply Hmono; eassumption].
Qed.

Local Lemma shape_usable_downward F A t : type_shape F A -> element_downward (usable_at A t).
Proof.
  intros (_ & _ & Hdown & _). intros n W v [Ht Hv].
  split; [exact Ht|now apply Hdown].
Qed.

Local Lemma unavailable_shape F : type_shape F unavailable.
Proof. unfold type_shape, unavailable, empty_element, element_monotone, element_mono_at, element_downward. simpl. tauto. Qed.

Local Lemma unavailable_family_shape F : family_shape F (fun _ => unavailable).
Proof. split; [intros; apply unavailable_shape|intros; split; intros; reflexivity]. Qed.

Local Lemma scalar_type_shape F b : type_shape F (scalar_type b).
Proof.
  split; [intros; exact I|]. split; [intros n W V v _ Hv; exact Hv|].
  split; [intros n W v Hv; exact Hv|].
  intros n W t v _ Hv. destruct v; simpl in Hv; try contradiction;
    intros l Hl; change (l ∈ (∅ : gset loc)) in Hl; set_solver.
Qed.

Local Lemma universal_type_shape F P :
  (forall A, family_shape F A -> type_shape F (P A)) ->
  type_shape F (universal_type F P).
Proof.
  intros Htype. split.
  - intros t u Htu Hav A HA. exact (proj1 (Htype A HA) t u Htu (Hav A HA)).
  - split.
    + intros n W V v Hext Hv A HA.
      exact (proj1 (proj2 (Htype A HA)) n W V v Hext (Hv A HA)).
    + split.
      * intros n W v Hv A HA.
        exact (proj1 (proj2 (proj2 (Htype A HA))) n W v (Hv A HA)).
      * intros n W t v Hav Hv.
        set (A := fun _ : list timestamp => unavailable).
        assert (HA : family_shape F A) by apply unavailable_family_shape.
        exact (proj2 (proj2 (proj2 (Htype A HA))) n W t v (Hav A HA) (Hv A HA)).
Qed.

Local Lemma sum_result_monotone F t P Q :
  element_monotone P -> element_monotone Q -> element_monotone (sum_result F t P Q).
Proof.
  intros HP HQ. apply location_spec_monotone.
  intros n W V l d Hext [(v & Hd & Hv)|(v & Hd & Hv)].
  - left. exists v. split; [exact Hd|eapply HP; eassumption].
  - right. exists v. split; [exact Hd|eapply HQ; eassumption].
Qed.

Local Lemma sum_result_downward F t P Q :
  element_downward P -> element_downward Q -> element_downward (sum_result F t P Q).
Proof.
  intros HP HQ. apply location_spec_downward.
  intros n W l d [(v & Hd & Hv)|(v & Hd & Hv)].
  - left. exists v. split; [exact Hd|now apply HP].
  - right. exists v. split; [exact Hd|now apply HQ].
Qed.

Local Lemma folded_result_monotone F t P :
  element_monotone P -> element_monotone (folded_result F t P).
Proof.
  intros HP n W V v Hext (w & Hv & Hw). exists w. split; [exact Hv|].
  eapply location_spec_monotone; [|exact Hext|exact Hw].
  intros k A B l d HAB HA. destruct k as [|k]; [exact I|].
  apply (HP k (fst A) (fst B)); [exact (proj1 HAB)|exact HA].
Qed.

Local Lemma folded_result_downward F t P :
  element_downward P -> element_downward (folded_result F t P).
Proof.
  intros HP n W v (w & Hv & Hw). exists w. split; [exact Hv|].
  eapply location_spec_downward; [|exact Hw].
  intros k A l d HA. destruct k as [|k]; [exact I|].
  exact (HP k (fst A) (VLoc l) HA).
Qed.

Local Lemma recursive_approximation_shape F t B bound :
  (forall k P Q, element_prefix k P Q -> element_prefix k (B P) (B Q)) ->
  (forall P, type_shape F (anchored F t P) -> type_shape F (anchored F t (B P))) ->
  type_shape F (anchored F t (recursive_approximation F t B bound)).
Proof.
  intros Hprefix HB. induction bound as [|bound IH].
  - apply anchored_type_shape.
    + intros n W V v _ H. exact H.
    + intros n W v H. exact H.
    + intros n W v H. exfalso. exact H.
  - destruct (HB _ IH) as (_ & Hmono & Hdown & _).
    destruct IH as (_ & HmonoOld & HdownOld & Hvisible).
    apply anchored_type_shape.
    + intros n W V v Hext. cbn [recursive_approximation].
      destruct (decide (n = bound)); [now apply folded_result_monotone|eapply HmonoOld; eassumption].
    + intros k W v Hv. cbn [recursive_approximation] in *.
      destruct (decide (S k = bound)) as [Hnew|Hold].
      * subst bound. rewrite decide_False by lia.
        cbn [recursive_approximation]. rewrite decide_True by reflexivity.
        pose proof (folded_result_downward _ _ _ Hdown k W v Hv) as Hprev.
        assert (Hcompare :
          folded_result F t (B (recursive_approximation F t B (S k))) k (fst W) v <->
          folded_result F t (B (recursive_approximation F t B k)) k (fst W) v).
        { apply folded_result_compare; [apply clock_equivalent_refl|].
          destruct k as [|k]; intros l; [tauto|].
          assert (Happrox : element_prefix k (recursive_approximation F t B (S (S k)))
                                             (recursive_approximation F t B (S k))).
          { intros i Hi V w. etransitivity; [apply recursive_approximation_agrees; lia|].
            symmetry. apply recursive_approximation_agrees. lia. }
          exact (Hprefix k _ _ Happrox k (Nat.le_refl k) (fst (fst W)) (VLoc l)). }
        now apply Hcompare.
      * destruct (decide (k = bound)) as [Hbad|Hok].
        -- subst k. exfalso. eapply (recursive_approximation_outside F t B bound (S bound) W v); [lia|exact Hv].
        -- exact (HdownOld k W v Hv).
    + intros n W v Hv. cbn [recursive_approximation] in Hv.
      destruct (decide (n = bound)); [eapply folded_result_visible; [apply rtc_refl|exact Hv]|].
      exact (Hvisible n W t v (rtc_refl _ t) Hv).
Qed.

Local Lemma recursive_element_shape F t B :
  (forall k P Q, element_prefix k P Q -> element_prefix k (B P) (B Q)) ->
  (forall P, type_shape F (anchored F t P) -> type_shape F (anchored F t (B P))) ->
  type_shape F (anchored F t (recursive_element F t B)).
Proof.
  intros Hprefix HB. apply anchored_type_shape.
  - intros n W V v Hext Hv.
    exact (proj1 (proj2 (recursive_approximation_shape F t B (S n) Hprefix HB)) n W V v Hext Hv).
  - intros n W v Hv.
    pose proof (proj1 (proj2 (proj2 (recursive_approximation_shape F t B (S (S n)) Hprefix HB)))
      n W v Hv) as Hprev.
    assert (Hlt : (n < S (S n))%nat) by lia.
    exact (proj1 (recursive_approximation_agrees F t B (S (S n)) n (fst W) v Hlt) Hprev).
  - intros n W v Hv.
    exact (proj2 (proj2 (proj2 (recursive_approximation_shape F t B (S n) Hprefix HB)))
      n W t v (rtc_refl _ t) Hv).
Qed.

Local Definition admissible_assignment F (X : type_assignment) : Prop := forall x, family_shape F (X x).

Local Lemma admissible_scope_monotone F X :
  admissible_assignment F X -> monotone_scopes F X.
Proof. intros HX x. exact (family_scope_monotone F (X x) (HX x)). Qed.

Local Lemma admissible_assignment_related F X n L :
  admissible_assignment F X -> related_types F n L X X.
Proof. intros HX x Hx. now apply family_shape_related. Qed.

Local Lemma admissible_type_assume F X b A :
  admissible_assignment F X -> family_shape F A -> admissible_assignment F (type_assume X b A).
Proof.
  intros HX HA x. unfold type_assume. destruct (decide (x ∈ binder_set b)); [exact HA|apply HX].
Qed.

Local Lemma constant_family_shape F A :
  type_shape F A -> family_shape F (fun _ => A).
Proof. intros HA. split; [intros; exact HA|intros; split; intros; reflexivity]. Qed.

Section InterpretationShape.
Context (F : graph).

Local Fixpoint interpret_type_shape (ρ : typ) {struct ρ} :
  forall η X ts, admissible_assignment F X -> type_shape F (interpret_type F ρ η X ts)
with interpret_atom_shape (σ : typat) {struct σ} :
  forall η X t, admissible_assignment F X -> type_shape F (anchored F t (interpret_at F σ η X t)).
Proof.
  - destruct ρ as [x|b|σ d|b ρ|ρ d|b k ρ|x σ d]; intros η X ts HX; cbn [interpret_type].
    + exact (proj1 (HX x) ts).
    + apply scalar_type_shape.
    + now apply (interpret_atom_shape σ).
    + destruct ts as [|t ts]; [apply unavailable_shape|now apply (interpret_type_shape ρ)].
    + now apply (interpret_type_shape ρ).
    + apply universal_type_shape. intros A HA.
      apply (interpret_type_shape ρ). now apply admissible_type_assume.
    + apply recursive_element_shape.
      * intros j P Q HP.
        apply (interpret_comparable_atom F σ).
        -- apply type_assume_monotone_scopes; [now apply admissible_scope_monotone|].
           cbn [anchored fst]. unfold reachable. intros ? ? ? ?. etransitivity; eassumption.
        -- apply type_assume_monotone_scopes; [now apply admissible_scope_monotone|].
           cbn [anchored fst]. unfold reachable. intros ? ? ? ?. etransitivity; eassumption.
        -- intros. apply clock_equivalent_refl.
        -- apply type_assume_related.
           ++ now apply admissible_assignment_related.
           ++ intros ats aus _. apply anchored_prefix; [apply clock_equivalent_refl|exact HP].
        -- apply clock_equivalent_refl.
      * intros P HP. apply (interpret_atom_shape σ).
        apply admissible_type_assume; [exact HX|now apply constant_family_shape].
  - destruct σ as [ρ|ρ1 ρ2|ρ1 ρ2|bs Δ d ρs ρ]; intros η X t HX; cbn [interpret_at];
      apply anchored_type_shape.
    + apply array_result_monotone.
    + apply array_result_downward.
    + intros n W v Hv. eapply location_spec_visible; exact Hv.
    + apply product_result_monotone; apply (shape_usable_monotone F);
        (now apply (interpret_type_shape ρ1) || now apply (interpret_type_shape ρ2)).
    + apply product_result_downward; apply (shape_usable_downward F);
        (now apply (interpret_type_shape ρ1) || now apply (interpret_type_shape ρ2)).
    + intros n W v Hv. eapply location_spec_visible; exact Hv.
    + apply sum_result_monotone; apply (shape_usable_monotone F);
        (now apply (interpret_type_shape ρ1) || now apply (interpret_type_shape ρ2)).
    + apply sum_result_downward; apply (shape_usable_downward F);
        (now apply (interpret_type_shape ρ1) || now apply (interpret_type_shape ρ2)).
    + intros n W v Hv. eapply location_spec_visible; exact Hv.
    + apply function_result_monotone.
    + apply function_result_downward.
    + intros n W v Hv. eapply location_spec_visible; exact Hv.
Defined.
End InterpretationShape.

Local Lemma interpret_family_shape F ρ η X :
  admissible_assignment F X ->
  family_shape F (fun ts => interpret_type F ρ η X ts).
Proof.
  intros HX. split.
  - intros ts. now apply interpret_type_shape.
  - intros ts us Htime. split.
    + pose proof (interpret_comparable_type F ρ 0 η η X X ts us
        (admissible_scope_monotone F X HX) (admissible_scope_monotone F X HX)
        (fun x _ => clock_equivalent_refl F (η x))
        (admissible_assignment_related F X 0 _ HX) Htime) as H.
      exact (proj1 H).
    + intros n W v. pose proof (interpret_comparable_type F ρ n η η X X ts us
        (admissible_scope_monotone F X HX) (admissible_scope_monotone F X HX)
        (fun x _ => clock_equivalent_refl F (η x))
        (admissible_assignment_related F X n _ HX) Htime) as H.
      exact (proj2 H n (Nat.le_refl n) W v).
Qed.

Combined Scheme typed_mutual_ind from typed_rec, Forall2_typed_rec.

Local Lemma typed_locations_empty :
  (forall δ Δ Ω Γ e ρ, typed δ Δ Ω Γ e ρ -> locs e = ∅) /\
  (forall δ Δ Ω Γ es ρs, Forall2_typed δ Δ Ω Γ es ρs -> locs es = ∅).
Proof.
  apply typed_mutual_ind; intros;
    try apply locs_list_cons;
    cbn [locs location_expr locs_expr locs_func locs_val] in *;
    try reflexivity; try assumption.
  all: try match goal with
       | |- context [⋃ (locs_expr <$> ?es)] => change (locs_expr _ ∪ locs es = ∅)
       | |- ?H ∪ ⋃ (locs <$> ?es) = _ => change (H ∪ locs es = ∅)
       end.
  all: try rewrite locs_list_cons.
  all: repeat match goal with
       | H : ?L = ∅ |- _ => rewrite H || clear H
       end.
  all: set_solver.
Qed.

Local Definition typed_value_env F n (W : resource n) t η X (Γ : env) (E : gmap string val) :=
  (forall x ρ, Γ !! x = Some ρ -> exists v, E !! x = Some v /\
    usable_at (interpret_type F ρ η X []) t n W v) /\
  (forall x v, E !! x = Some v -> value_visible_in_view F (resource_view n W) t v).

Local Lemma view_value_visible_extend F (V V' : heap_view) t v :
  V ⊆ V' -> value_visible_in_view F V t v -> value_visible_in_view F V' t v.
Proof.
  intros Hext Hvisible l Hl. destruct (Hvisible l Hl) as (o & d & Hlook & Ho).
  exists o, d. split; [exact (lookup_weaken _ _ _ _ Hlook Hext)|exact Ho].
Qed.

Local Lemma typed_value_env_mono F n (W V : resource n) t η X Γ E :
  admissible_assignment F X -> resource_extends n W V ->
  typed_value_env F n W t η X Γ E -> typed_value_env F n V t η X Γ E.
Proof.
  intros HX Hext [Henv Hvalues]. split.
  - intros x ρ Hρ. destruct (Henv x ρ Hρ) as (v & Hlook & Hv).
    exists v. split; [exact Hlook|].
    eapply (shape_usable_monotone F); [now apply interpret_type_shape|exact Hext|exact Hv].
  - intros x v Hv. eapply view_value_visible_extend;
      [eapply resource_view_extends; exact Hext|now apply (Hvalues x)].
Qed.

Local Lemma typed_value_env_down F n (W : resource (S n)) t η X Γ E :
  admissible_assignment F X ->
  typed_value_env F (S n) W t η X Γ E -> typed_value_env F n (fst W) t η X Γ E.
Proof.
  intros HX [Henv Hvalues]. split; [|exact Hvalues].
  intros x ρ Hρ. destruct (Henv x ρ Hρ) as (v & Hlook & Hv).
  exists v. split; [exact Hlook|].
  eapply (shape_usable_downward F); [now apply interpret_type_shape|exact Hv].
Qed.

Local Lemma typed_value_env_insert F n (W : resource n) t η X Γ E b ρ v :
  admissible_assignment F X ->
  typed_value_env F n W t η X Γ E ->
  usable_at (interpret_type F ρ η X []) t n W v ->
  typed_value_env F n W t η X (binsert b ρ Γ) (binsert b v E).
Proof.
  intros HX Henv Hv. destruct b as [|x]; [exact Henv|].
  destruct Henv as [Henv Hvalues]. split; cbn [binsert].
  - intros y r Hy. apply lookup_insert_Some in Hy as [(Heq & Htype)|(Hne & Htype)].
    + subst y r. exists v. split; [apply lookup_insert_eq|exact Hv].
    + destruct (Henv y r Htype) as (w & Hw & Hcheck).
      exists w. split; [now rewrite lookup_insert_ne|exact Hcheck].
  - intros y w Hy. apply lookup_insert_Some in Hy as [(Heq & Hval)|(Hne & Hlook)].
    + subst y w. destruct Hv as [Havailable Hvalue].
      exact (proj2 (proj2 (proj2 (interpret_type_shape F ρ η X [] HX))) n W t v Havailable Hvalue).
    + now apply (Hvalues y).
Qed.

Local Lemma interp_value_spec F ρ η X t n (W : resource n) v :
  admissible_assignment F X ->
  usable_at (interpret_type F ρ η X []) t n W v ->
  expression_spec n F W (Leaf t) v (usable_at (interpret_type F ρ η X []) t).
Proof.
  intros HX Hv.
  pose proof (interpret_type_shape F ρ η X [] HX) as Hshape.
  apply expression_spec_value.
  - intros k V [Havailable Hvalue]. exact (proj2 (proj2 (proj2 Hshape)) k V t v Havailable Hvalue).
  - intros V Hext. eapply (shape_usable_monotone F); eassumption.
  - intros k V. exact (fun H => shape_usable_downward F _ t Hshape k V v H).
Qed.

Local Definition expression_typing_model δ Δ Γ e ρ :=
  forall F η X n (W : resource n) E,
    admissible_assignment F X -> clock_constraints F η Δ ->
    typed_value_env F n W (η δ) η X Γ E ->
    expression_spec n F W (Leaf (η δ)) (close_expr E e)
      (usable_at (interpret_type F ρ η X []) (η δ)).

Local Lemma model_var δ Δ Γ x ρ :
  Γ !! x = Some ρ -> expression_typing_model δ Δ Γ (Var x) ρ.
Proof.
  intros Hlookup F η X n W E HX _ [Henv _].
  destruct (Henv x ρ Hlookup) as (v & Hv & Htyped).
  cbn [close_expr]. rewrite Hv. now apply interp_value_spec.
Qed.

Local Lemma model_literal δ Δ Γ v b :
  source_base v b -> expression_typing_model δ Δ Γ (Val v) (TBase b).
Proof.
  intros Hv F η X n W E HX _ _. cbn [close_expr].
  apply interp_value_spec; [exact HX|]. split; [exact I|exact Hv].
Qed.

Local Lemma model_weak_constraints δ Δ Δ' Γ e ρ :
  Δ ⊆ Δ' -> expression_typing_model δ Δ Γ e ρ -> expression_typing_model δ Δ' Γ e ρ.
Proof.
  intros Hsub Hmodel F η X n W E HX HΔ Henv. apply Hmodel; try assumption.
  intros x y Hxy. apply HΔ, Hsub, Hxy.
Qed.

Local Lemma model_weak_value_env δ Δ Γ Γ' e ρ :
  Γ ⊆ Γ' -> expression_typing_model δ Δ Γ e ρ -> expression_typing_model δ Δ Γ' e ρ.
Proof.
  intros Hsub Hmodel F η X n W E HX HΔ [Henv Hvalues].
  apply Hmodel; try assumption. split; [|exact Hvalues].
  intros x r Hlook. apply Henv, (lookup_weaken _ _ _ _ Hlook Hsub).
Qed.

Local Lemma model_get_info δ Δ Γ x ρ' ρ δ' e :
  Γ !! x = Some ρ' -> simple_root ρ' = Some δ' ->
  expression_typing_model δ (Δ ∪ {[(δ', δ)]}) Γ e ρ ->
  expression_typing_model δ Δ Γ e ρ.
Proof.
  intros Hx Hroot Hmodel F η X n W E HX HΔ Henv.
  destruct ((proj1 Henv) x ρ' Hx) as (v & Hv & [Hvisible Hvalid]).
  apply Hmodel; try assumption. apply clock_constraints_union. split; [exact HΔ|].
  intros a b Hab. apply elem_of_singleton in Hab. inversion Hab; subst.
  destruct ρ'; try discriminate Hroot; inversion Hroot; subst; exact Hvisible.
Qed.

Local Lemma closed_code_visible F (V : heap_view) t E e :
  locs e = ∅ ->
  (forall x v, E !! x = Some v -> value_visible_in_view F V t v) ->
  forall l, l ∈ locs (close_expr E e) -> exists o d, V !! l = Some (o,d) /\ reachable F o t.
Proof.
  intros Hsource Henv.
  set (L := ⋃ ((fun xv => locs (snd xv)) <$> map_to_list E)).
  assert (HE : env_locs E L).
  { intros x v Hval l Hl. unfold L. apply elem_of_union_list.
    exists (locs v). split; [|exact Hl]. apply list_elem_of_fmap.
    exists (x,v). split; [reflexivity|now apply elem_of_map_to_list]. }
  intros l Hl. apply (close_locations E e L HE) in Hl.
  rewrite Hsource in Hl. apply elem_of_union in Hl as [Hl|Hl]; [set_solver|].
  unfold L in Hl. apply elem_of_union_list in Hl as (Lv & Hlist & Hl).
  apply list_elem_of_fmap in Hlist as ((x,v) & -> & Hmap).
  apply elem_of_map_to_list in Hmap. exact (Henv x v Hmap l Hl).
Qed.

Local Lemma let_step_invert G t σ α b (v : val) body σ' α' e' :
  head_step G t σ α (Let b v body) σ' α' e' ->
  σ' = σ /\ α' = α /\ e' = subst' b v body.
Proof.
  intros Hstep. remember (Let b v body) as e eqn:He.
  destruct Hstep; try match goal with q : bool |- _ => destruct q end; try discriminate He.
  all: inversion He; subst; auto.
Qed.

Local Lemma expression_spec_let_value n F (W : resource n) t b (v : val) body Q :
  (forall l, l ∈ locs (Let b v body) ->
    exists o d, resource_view n W !! l = Some (o,d) /\ reachable F o t) ->
  expression_spec n F W (Leaf t) (subst' b v body) Q ->
  expression_spec n F W (Leaf t) (Let b v body) Q.
Proof.
  induction n as [|n IH]; intros Hvisible Hbody; [exact I|].
  apply expression_spec_atomic.
  - apply IH; [exact Hvisible|exact (proj1 Hbody)].
  - intros V σ α G Hext Hheap HG.
    split; [apply ReadyLet|]. split.
    + intros l Hl. destruct (Hvisible l Hl) as (o & d & Hlook & Htime).
      pose proof (lookup_weaken _ _ _ _ Hlook (resource_view_extends _ _ _ Hext)) as Hfound.
      destruct (proj2 (store_spec_view _ _ _ _ Hheap) l o d Hfound) as [Hα _].
      unfold abef. now rewrite Hα.
    + intros σ' α' e' Hhead.
      destruct (let_step_invert _ _ _ _ _ _ _ _ _ _ Hhead) as (-> & -> & ->).
      exists (fst V). split; [apply resource_extends_refl|]. split; [exact (proj1 Hheap)|].
      eapply expression_spec_extend; [exact (proj1 Hext)|exact (proj1 Hbody)].
Qed.

Local Lemma model_let δ Δ Γ b e1 e2 ρ1 ρ2 :
  locs e2 = ∅ ->
  expression_typing_model δ Δ Γ e1 ρ1 ->
  expression_typing_model δ Δ (binsert b ρ1 Γ) e2 ρ2 ->
  expression_typing_model δ Δ Γ (Let b e1 e2) ρ2.
Proof.
  intros Hsource Hfirst Hsecond F η X n W E HX HΔ Henv.
  set (t := η δ).
  set (K := CtxLet b (close_expr (bdelete b E) e2)).
  set (P := usable_at (interpret_type F ρ1 η X []) t).
  set (Q := usable_at (interpret_type F ρ2 η X []) t).
  assert (Hvisible : forall k (V : resource k), typed_value_env F k V t η X Γ E ->
       context_support F (resource_view k V) t K).
  { intros k V [Htypes Hva] l Hl. unfold K in Hl.
    eapply closed_code_visible; [exact Hsource| |exact Hl].
    intros x v Hlookup. rewrite binder_lookup_delete in Hlookup.
    destruct (decide (x ∈ binder_set b)); [discriminate|exact (Hva x v Hlookup)]. }
  change (expression_spec n F W (Leaf t) (fill_item K (close_expr E e1)) Q).
  eapply expression_spec_bind.
  - exact I.
  - now apply Hvisible.
  - exact (Hfirst F η X n W E HX HΔ Henv).
  - revert W Henv. induction n as [|n IH]; intros W Henv; [exact I|].
    split.
    + apply IH. now apply typed_value_env_down.
    + intros V v Hext Hv.
      pose proof (typed_value_env_mono F (S n) W V t η X Γ E HX Hext Henv) as HenvV.
      change (expression_spec (S n) F V (Leaf t) (Let b v (close_expr (bdelete b E) e2)) Q).
      apply expression_spec_let_value.
      * intros l Hl. cbn [locs location_expr locs_expr] in Hl.
        apply elem_of_union in Hl as [Hvloc|Hbody].
        -- pose proof (interpret_type_shape F ρ1 η X [] HX) as Hshape.
           destruct Hv as [Hscope Hspec].
           exact (proj2 (proj2 (proj2 Hshape)) (S n) V t v Hscope Hspec l Hvloc).
        -- exact (Hvisible (S n) V HenvV l Hbody).
      * rewrite close_single_binding. apply Hsecond; [exact HX|exact HΔ|].
        now apply typed_value_env_insert.
Qed.

Local Lemma type_env_mentions (f : typ -> gset string) (Γ : env) x ρ :
  Γ !! x = Some ρ -> f ρ ⊆ map_fold (fun _ r L => f r ∪ L) ∅ Γ.
Proof.
  induction Γ as [|y p Γ Hfresh IH] using map_ind.
  - intros H. rewrite lookup_empty in H. discriminate.
  - rewrite map_fold_insert_L; [|intros; set_solver|exact Hfresh].
    intros H. apply lookup_insert_Some in H as [(Heq & Hp)|(_ & Hlookup)].
    + subst y p. set_solver.
    + pose proof (IH Hlookup). set_solver.
Qed.

Local Lemma typed_value_env_change F n (W : resource n) t η θ X Y Γ E :
  (forall x ρ, Γ !! x = Some ρ ->
    type_prefix n (interpret_type F ρ η X []) (interpret_type F ρ θ Y [])) ->
  typed_value_env F n W t η X Γ E -> typed_value_env F n W t θ Y Γ E.
Proof.
  intros Htypes [Henv Hview]. split; [|exact Hview].
  intros x ρ Hlook. destruct (Henv x ρ Hlook) as (v & Hv & Hval).
  exists v. split; [exact Hv|].
  apply (usable_prefix_same n _ _ t (Htypes x ρ Hlook) n (Nat.le_refl n) W v), Hval.
Qed.

Local Lemma model_type_forall δ Δ Γ b k e ρ :
  very_pure e -> binder_set b ## fvv_env Γ ->
  expression_typing_model δ Δ Γ e ρ ->
  expression_typing_model δ Δ Γ e (TForall b k ρ).
Proof.
  intros Hpure Hfresh Hmodel F η X n W E HX HΔ Henv.
  set (t := η δ).
  set (J := { A : type_family | family_shape F A }).
  set (j0 := exist _ (fun _ : list timestamp => unavailable) (unavailable_family_shape F)).
  assert (Hbody : forall j : J, expression_spec n F W (Leaf t) (close_expr E e)
    (usable_at (interpret_type F ρ η (type_assume X b (proj1_sig j)) []) t)).
  { intros [A HA]. cbn [proj1_sig].
    assert (HX' : admissible_assignment F (type_assume X b A)) by now apply admissible_type_assume.
    apply Hmodel; [exact HX'|exact HΔ|].
    eapply typed_value_env_change; [|exact Henv].
    intros x r Hlook. apply (interpret_comparable_type F r).
    - now apply admissible_scope_monotone.
    - now apply admissible_scope_monotone.
    - intros; apply clock_equivalent_refl.
    - intros y Hy. unfold type_assume.
      destruct (decide (y ∈ binder_set b)) as [Hbound|Hbound].
      + exfalso. pose proof (type_env_mentions fvv_typ Γ x r Hlook y Hy) as Hmentioned.
        change (y ∈ fvv_env Γ) in Hmentioned. set_solver.
      + now apply family_shape_related.
    - constructor. }
  eapply expression_spec_post; [|eapply (expression_spec_pure_forall j0); [now apply close_preserves_purity|exact Hbody]].
  intros i V v H. split.
  - intros A HA. exact (proj1 (H (exist _ A HA))).
  - intros A HA. exact (proj2 (H (exist _ A HA))).
Qed.

Local Lemma element_prefix_trans n P Q R :
  element_prefix n P Q -> element_prefix n Q R -> element_prefix n P R.
Proof. intros HP HQ k Hk W v. etransitivity; [apply (HP k Hk W v)|apply (HQ k Hk W v)]. Qed.

Local Lemma type_prefix_trans n A B C :
  type_prefix n A B -> type_prefix n B C -> type_prefix n A C.
Proof.
  intros [H1 H2] [H3 H4]. split; [|eapply element_prefix_trans; eassumption].
  intros t. etransitivity; [apply H1|apply H3].
Qed.

Local Definition substitution_avoids (m : gmap string string) (S : gset string) :=
  forall x y, m !! x = Some y -> y ∉ S.

Local Lemma substitution_avoids_subset m S T : S ⊆ T -> substitution_avoids m T -> substitution_avoids m S.
Proof. intros Hsub Htime x y Hy Hmem. apply (Htime x y Hy), Hsub, Hmem. Qed.

Local Lemma substitution_avoids_deletes m bs S :
  substitution_avoids m S -> substitution_avoids (bdeletes bs m) S.
Proof.
  intros H x y Hy. rewrite binders_lookup_delete in Hy.
  destruct (decide (x ∈ binders_set bs)); [discriminate|]. now apply (H x y).
Qed.

Local Lemma substitution_avoids_delete m b S :
  substitution_avoids m S -> substitution_avoids (bdelete b m) S.
Proof. apply (substitution_avoids_deletes m [b] S). Qed.

Local Definition regular_at F n X :=
  monotone_scopes F X /\ forall x, related_families F n (X x) (X x).

Local Lemma regular_weaken F n k X :
  (k <= n)%nat -> regular_at F n X -> regular_at F k X.
Proof.
  intros Hkn [Htime Htypes]. split; [exact Htime|].
  intros x ts us Hrel. eapply type_prefix_weaken; [exact Hkn|exact (Htypes x ts us Hrel)].
Qed.

Local Lemma regular_assume F n X b A :
  regular_at F n X ->
  (forall ts t u, reachable F t u -> fst (A ts) t -> fst (A ts) u) ->
  related_families F n A A ->
  regular_at F n (type_assume X b A).
Proof.
  intros [Hscope Hfamily] HA Hproper. split.
  - now apply type_assume_monotone_scopes.
  - intros x. unfold type_assume. destruct (decide (x ∈ binder_set b)); auto.
Qed.

Local Lemma anchored_scope_mono F s E t u :
  reachable F t u -> fst (anchored F s E) t -> fst (anchored F s E) u.
Proof. cbn [anchored fst]. unfold reachable. intros. etransitivity; eassumption. Qed.

Local Lemma regular_assume_anchor F n X b t E :
  regular_at F n X -> regular_at F n (type_assume X b (fun _ => anchored F t E)).
Proof.
  intros HX. apply regular_assume; [exact HX| |].
  - intros ts a u Hreach Hav. exact (anchored_scope_mono F t E a u Hreach Hav).
  - intros ats aus Htimes. apply anchored_prefix; [apply clock_equivalent_refl|apply element_prefix_refl].
Qed.

Local Lemma compare_clock_assignments F n ρ η θ X ts :
  regular_at F n X -> (forall x, η x = θ x) ->
  type_prefix n (interpret_type F ρ η X ts) (interpret_type F ρ θ X ts).
Proof.
  intros [Hscope Htypes] Hclock. apply (interpret_comparable_type F ρ);
    [exact Hscope|exact Hscope| |intros x _; apply Htypes|apply list_clocks_refl].
  intros x _. rewrite Hclock. apply clock_equivalent_refl.
Qed.

Local Lemma clock_bind_substitute η b t m :
  substitution_avoids m (binder_set b) ->
  forall x, clock_bind η b t (find_opt (bdelete b m) x) =
    clock_bind (fun y => η (find_opt m y)) b t x.
Proof.
  intros Hsafe x. rewrite !clock_bind_extend. symmetry.
  change (clock_extend (fun y => η (find_opt m y)) (binsert b t ∅) x =
    clock_extend η (binsert b t ∅) (find_opt (bdeletes [b] m) x)).
  apply clock_extension_substitute.
  - change (dom (bmap [b] [t]) = binders_set [b]). apply dom_bmap. reflexivity.
  - intros q r Hr Hmem. apply (Hsafe q r Hr).
    rewrite binders_set_cons in Hmem. apply elem_of_union in Hmem as [Hmem|Hmem]; [exact Hmem|].
    change (r ∈ (∅ : gset string)) in Hmem. set_solver.
Qed.

Section InterpretSubstitution.
Context (F : graph).

Local Fixpoint interpret_type_substitution (ρ : typ) {struct ρ} :
  forall n m η X ts, regular_at F n X ->
    substitution_avoids m (bv_typ ρ) ->
    type_prefix n (interpret_type F (tsubst_typ m ρ) η X ts)
                  (interpret_type F ρ (fun x => η (find_opt m x)) X ts)
with interpret_atom_substitution (σ : typat) {struct σ} :
  forall n m η X t, regular_at F n X ->
    substitution_avoids m (bv_typat σ) ->
    element_prefix n (interpret_at F (tsubst_typat m σ) η X t)
                     (interpret_at F σ (fun x => η (find_opt m x)) X t).
Proof.
  - rename interpret_type_substitution into ST. rename interpret_atom_substitution into SA.
    destruct ρ as [x|b|σ d|b ρ|ρ d|b k ρ|x σ d]; intros n m η X ts HX Hsafe;
      cbn [tsubst_typ interpret_type] in *.
    + split; [intros; reflexivity|apply element_prefix_refl].
    + split; [intros; reflexivity|apply element_prefix_refl].
    + apply anchored_prefix; [apply clock_equivalent_refl|now apply (SA σ)].
    + destruct ts as [|t ts]; [split; [intros; reflexivity|apply element_prefix_refl]|].
      eapply type_prefix_trans.
      * apply (ST ρ); [exact HX|].
        apply substitution_avoids_delete. eapply substitution_avoids_subset; [|exact Hsafe].
        clear ST SA. set_solver.
      * apply compare_clock_assignments; [exact HX|].
        apply clock_bind_substitute. eapply substitution_avoids_subset; [|exact Hsafe].
        clear ST SA. set_solver.
    + now apply (ST ρ).
    + apply universal_prefix. intros A HA. apply (ST ρ); [|exact Hsafe].
      apply regular_assume; [exact HX|now apply family_scope_monotone|now apply family_shape_related].
    + set (t := η (find_opt m d)). apply anchored_prefix; [apply clock_equivalent_refl|].
      apply recursive_element_compare; [apply clock_equivalent_refl|].
      intros j Hj P Q HP. pose proof (regular_weaken F n j X Hj HX) as HXsmall.
      eapply element_prefix_trans.
      * apply (SA σ); [now apply regular_assume_anchor|exact Hsafe].
      * apply (interpret_comparable_atom F σ).
        -- exact (proj1 (regular_assume_anchor F j X (BNamed x) t P HXsmall)).
        -- exact (proj1 (regular_assume_anchor F j X (BNamed x) t Q HXsmall)).
        -- intros; apply clock_equivalent_refl.
        -- apply type_assume_related.
           ++ intros s _. exact (proj2 HXsmall s).
           ++ intros ats aus Htimes. apply anchored_prefix; [apply clock_equivalent_refl|exact HP].
        -- apply clock_equivalent_refl.
  - rename interpret_type_substitution into ST. rename interpret_atom_substitution into SA.
    destruct σ as [ρ|ρ1 ρ2|ρ1 ρ2|bs Δ d ρs ρ]; intros n m η X t HX Hsafe;
      cbn [tsubst_typat interpret_at] in *.
    + pose proof (ST ρ n m η X [] HX Hsafe) as Htype.
      apply array_result_compare; [apply clock_equivalent_refl|exact (proj1 Htype)|exact (proj2 Htype)].
    + apply product_result_compare; [apply clock_equivalent_refl| |]; apply usable_prefix_same.
      * apply (ST ρ1); [exact HX|]. eapply substitution_avoids_subset; [|exact Hsafe].
        clear ST SA. set_solver.
      * apply (ST ρ2); [exact HX|]. eapply substitution_avoids_subset; [|exact Hsafe].
        clear ST SA. set_solver.
    + apply sum_result_compare; [apply clock_equivalent_refl| |]; apply usable_prefix_same.
      * apply (ST ρ1); [exact HX|]. eapply substitution_avoids_subset; [|exact Hsafe].
        clear ST SA. set_solver.
      * apply (ST ρ2); [exact HX|]. eapply substitution_avoids_subset; [|exact Hsafe].
        clear ST SA. set_solver.
    + apply function_result_compare; [apply clock_equivalent_refl|].
      split; [reflexivity|]. intros ts Hlen.
      set (η' := clock_extend η (bmap bs ts)).
      set (θ' := clock_extend (fun x => η (find_opt m x)) (bmap bs ts)).
      set (m' := bdeletes bs m).
      assert (Hclock : forall x, η' (find_opt m' x) = θ' x).
      { intros x. symmetry. apply clock_extension_substitute.
        - apply dom_bmap. symmetry. exact Hlen.
        - eapply substitution_avoids_subset; [|exact Hsafe]. clear ST SA. set_solver. }
      split.
      * cbn [call_constraints]. rewrite clock_constraints_substitute.
        apply clock_constraints_ext. intros; split; apply Hclock.
      * cbn [call_time call_parameters call_result]. fold η' θ' m'.
        rewrite (Hclock d). split; [apply clock_equivalent_refl|]. split.
        -- rewrite <-list_fmap_compose. unfold compose.
           assert (HsafeList : substitution_avoids m (⋃ (bv_typ <$> ρs))).
           { eapply substitution_avoids_subset; [|exact Hsafe]. clear ST SA. set_solver. }
           clear Hsafe Hlen. revert HsafeList.
           induction ρs as [|r rs IH]; intros HsafeList.
           ++ constructor.
           ++ rewrite !fmap_cons. constructor.
              ** apply usable_prefix_same. eapply type_prefix_trans.
                 --- apply (ST r); [exact HX|]. apply substitution_avoids_deletes.
                     eapply substitution_avoids_subset; [|exact HsafeList].
                     clear ST SA. rewrite fmap_cons, union_list_cons. set_solver.
                 --- now apply compare_clock_assignments.
              ** apply IH. eapply substitution_avoids_subset; [|exact HsafeList].
                 clear ST SA. rewrite fmap_cons, union_list_cons. set_solver.
        -- apply usable_prefix_same. eapply type_prefix_trans.
           ++ apply (ST ρ); [exact HX|]. apply substitution_avoids_deletes.
              eapply substitution_avoids_subset; [|exact Hsafe]. clear ST SA. set_solver.
           ++ now apply compare_clock_assignments.
Defined.
End InterpretSubstitution.

Local Lemma type_prefix_refl n A : type_prefix n A A.
Proof. split; [intros; reflexivity|apply element_prefix_refl]. Qed.

Local Lemma type_prefix_sym n A B : type_prefix n A B -> type_prefix n B A.
Proof. intros [Htime Hval]. split; [intros; symmetry; apply Htime|now apply element_prefix_sym]. Qed.

Combined Scheme beta_mutual_ind from beta_typ_rec, beta_typat_rec, beta_list_rec.

Local Lemma interpretation_beta F :
  (forall ρ τ, beta_typ ρ τ -> forall n η X ts, regular_at F n X ->
    type_prefix n (interpret_type F ρ η X ts) (interpret_type F τ η X ts)) /\
  (forall σ σ', beta_typat σ σ' -> forall n η X t, regular_at F n X ->
    element_prefix n (interpret_at F σ η X t) (interpret_at F σ' η X t)) /\
  (forall rs qs, beta_list rs qs -> forall n η X t, regular_at F n X ->
    Forall2 (element_prefix n)
      ((fun r => usable_at (interpret_type F r η X []) t) <$> rs)
      ((fun r => usable_at (interpret_type F r η X []) t) <$> qs)).
Proof.
  apply beta_mutual_ind.
  - intros. apply type_prefix_refl.
  - intros. apply type_prefix_refl.
  - intros σ σ' d Hβ IH n η X ts HX. cbn [interpret_type].
    apply anchored_prefix; [apply clock_equivalent_refl|now apply IH].
  - intros b ρ τ Hβ IH n η X ts HX. destruct ts as [|t ts]; cbn [interpret_type].
    + apply type_prefix_refl.
    + now apply IH.
  - intros ρ τ d Hβ IH n η X ts HX. cbn [interpret_type]. now apply IH.
  - intros ρ τ d x Hfresh Hβ IH n η X ts HX. cbn [interpret_type].
    pose proof (IH n η X (η d :: ts) HX) as Hlambda.
    change (type_prefix n (interpret_type F ρ η X (η d :: ts))
      (interpret_type F τ (clock_bind η (BNamed x) (η d)) X ts)) in Hlambda.
    eapply type_prefix_trans; [exact Hlambda|].
    eapply type_prefix_trans with (B:=interpret_type F τ (fun z => η (find_opt {[x:=d]} z)) X ts).
    + apply compare_clock_assignments; [exact HX|apply clock_bind_singleton].
    + apply type_prefix_sym, interpret_type_substitution; [exact HX|].
      intros y z Hlookup. apply lookup_singleton_Some in Hlookup as [_ ->]. exact Hfresh.
  - intros b k ρ τ Hβ IH n η X ts HX. cbn [interpret_type]. apply universal_prefix.
    intros A HA. apply IH, regular_assume; [exact HX|now apply family_scope_monotone|now apply family_shape_related].
  - intros x σ d σ' Hβ IH n η X ts HX. cbn [interpret_type].
    apply anchored_prefix; [apply clock_equivalent_refl|].
    apply recursive_element_compare; [apply clock_equivalent_refl|].
    intros j Hj P Q HP. pose proof (regular_weaken F n j X Hj HX) as HXj.
    eapply element_prefix_trans.
    + apply IH, regular_assume_anchor, HXj.
    + apply (interpret_comparable_atom F σ').
      * exact (proj1 (regular_assume_anchor F j X (BNamed x) (η d) P HXj)).
      * exact (proj1 (regular_assume_anchor F j X (BNamed x) (η d) Q HXj)).
      * intros. apply clock_equivalent_refl.
      * apply type_assume_related.
        -- intros y _. exact (proj2 HXj y).
        -- intros ats aus Htimes. apply anchored_prefix; [apply clock_equivalent_refl|exact HP].
      * apply clock_equivalent_refl.
  - intros ρ τ Hβ IH n η X t HX. cbn [interpret_at].
    destruct (IH n η X [] HX) as [Hscope Hval].
    apply array_result_compare; [apply clock_equivalent_refl|exact Hscope|exact Hval].
  - intros ρ1 τ1 ρ2 τ2 Hβ1 IH1 Hβ2 IH2 n η X t HX. cbn [interpret_at].
    apply product_result_compare; [apply clock_equivalent_refl| |];
      apply usable_prefix_same; [now apply IH1|now apply IH2].
  - intros ρ1 τ1 ρ2 τ2 Hβ1 IH1 Hβ2 IH2 n η X t HX. cbn [interpret_at].
    apply sum_result_compare; [apply clock_equivalent_refl| |];
      apply usable_prefix_same; [now apply IH1|now apply IH2].
  - intros bs Δ ρ τ rs qs d Hlist IHargs Hβ IHresult n η X t HX. cbn [interpret_at].
    apply function_result_compare; [apply clock_equivalent_refl|].
    split; [reflexivity|]. intros ts Hlen.
    cbn [call_constraints call_time call_parameters call_result].
    split; [reflexivity|]. split; [apply clock_equivalent_refl|]. split.
    + now apply IHargs.
    + apply usable_prefix_same. now apply IHresult.
  - intros ρ τ rs qs Hβ IH Hlist IHlist n η X t HX. rewrite !fmap_cons.
    apply Forall2_cons. split.
    + apply element_prefix_refl.
    + exact (IHlist n η X t HX).
  - intros. constructor.
Qed.

Local Lemma model_beta δ Δ Γ e ρ τ :
  (beta_typ ρ τ \/ beta_typ τ ρ) ->
  expression_typing_model δ Δ Γ e τ -> expression_typing_model δ Δ Γ e ρ.
Proof.
  intros Hβ Hmodel F η X n W E HX HΔ Henv.
  assert (Hregular : regular_at F n X).
  { split; [now apply admissible_scope_monotone|intros x; now apply family_shape_related]. }
  eapply expression_spec_post_prefix; [|exact (Hmodel F η X n W E HX HΔ Henv)].
  apply usable_prefix_same. destruct Hβ as [Hβ|Hβ].
  - apply type_prefix_sym. exact (proj1 (interpretation_beta F) _ _ Hβ n η X [] Hregular).
  - exact (proj1 (interpretation_beta F) _ _ Hβ n η X [] Hregular).
Qed.

Local Lemma closed_typing_model_sound δ e ρ :
  expression_typing_model δ ∅ ∅ e ρ -> always_safe_and_disentangled true e.
Proof.
  intros Hmodel. apply closed_expression_spec_adequacy.
  intros F t.
  set (η := fun _ : stimestamp => t).
  set (X := fun (_ : string) (_ : list timestamp) => unavailable).
  exists (usable_at (interpret_type F ρ η X []) t). intros n.
  rewrite <- (close_empty e) at 1.
  apply (Hmodel F η X n (empty_resource n) ∅).
  - intros x. apply unavailable_family_shape.
  - intros a b Hmem. set_solver.
  - split.
    + intros x τ Hlookup. rewrite lookup_empty in Hlookup. discriminate.
    + intros x v Hlookup. rewrite lookup_empty in Hlookup. discriminate.
Qed.

Local Definition models_replacement F n x τ L η X Y :=
  related_types F n L
    (type_assume X (BNamed x) (fun ts => interpret_type F τ η X ts)) Y.

Local Lemma type_assume_named X x A y :
  type_assume X (BNamed x) A y = if decide (x = y) then A else X y.
Proof.
  unfold type_assume. cbn [binder_set].
  destruct (decide (x = y)) as [->|Hne].
  - rewrite decide_True by set_solver. reflexivity.
  - rewrite decide_False by set_solver. reflexivity.
Qed.

Local Lemma type_assume_present X b A y : y ∈ binder_set b -> type_assume X b A y = A.
Proof. intros H. unfold type_assume. now rewrite decide_True. Qed.

Local Lemma type_assume_absent X b A y : y ∉ binder_set b -> type_assume X b A y = X y.
Proof. intros H. unfold type_assume. now rewrite decide_False. Qed.

Local Lemma replacement_weaken F n k x τ L η X Y :
  (k <= n)%nat -> models_replacement F n x τ L η X Y ->
  models_replacement F k x τ L η X Y.
Proof.
  intros Hkn Hmodel y Hy ts us Hts.
  eapply type_prefix_weaken; [exact Hkn|exact (Hmodel y Hy ts us Hts)].
Qed.

Local Lemma replacement_restrict F n x τ L L' η X Y :
  L' ⊆ L -> models_replacement F n x τ L η X Y ->
  models_replacement F n x τ L' η X Y.
Proof. intros Hin Hmodel y Hy. apply Hmodel, Hin, Hy. Qed.

Local Lemma replacement_shadowed F n x τ L η X Y :
  x ∉ L -> models_replacement F n x τ L η X Y ->
  related_types F n L X Y.
Proof.
  intros Hout Hmodel y Hy. specialize (Hmodel y Hy).
  rewrite type_assume_named in Hmodel.
  destruct (decide (x = y)) as [->|]; [contradiction|exact Hmodel].
Qed.

Local Lemma replacement_clock_scope F n x τ L η θ X Y :
  regular_at F n X ->
  (forall y, y ∈ fv_typ τ -> clock_equivalent F (θ y) (η y)) ->
  models_replacement F n x τ L η X Y ->
  models_replacement F n x τ L θ X Y.
Proof.
  intros [HX Hfamilies] Htime Hmodel y Hy ts us Hts.
  specialize (Hmodel y Hy ts us Hts).
  rewrite type_assume_named in *. destruct (decide (x = y)); [|exact Hmodel].
  eapply type_prefix_trans; [|exact Hmodel].
  apply (interpret_comparable_type F τ); [exact HX|exact HX|exact Htime| |apply list_clocks_refl].
  intros z _. apply Hfamilies.
Qed.

Local Lemma replacement_under_binder F n x τ L η X Y b P Q :
  regular_at F n X ->
  monotone_scopes F (type_assume X b P) ->
  b ≠ BNamed x -> binder_set b ## fvv_typ τ ->
  related_families F n P Q ->
  models_replacement F n x τ (L ∖ binder_set b) η X Y ->
  models_replacement F n x τ L η (type_assume X b P) (type_assume Y b Q).
Proof.
  intros [HX Hfamilies] Hscope Hne Hfresh Hpq Hmodel y Hy ts us Hts.
  rewrite type_assume_named.
  destruct (decide (y ∈ binder_set b)) as [Hbound|Hbound].
  - assert (Hxy : x ≠ y).
    { intros ->. apply Hne. destruct b; simpl in Hbound; [set_solver|].
      apply elem_of_singleton in Hbound. now subst. }
    rewrite decide_False by exact Hxy. rewrite !type_assume_present by exact Hbound.
    now apply Hpq.
  - rewrite (type_assume_absent Y b Q y Hbound).
    assert (Hout : y ∈ L ∖ binder_set b) by set_solver.
    specialize (Hmodel y Hout ts us Hts). rewrite type_assume_named in Hmodel.
    destruct (decide (x = y)) as [->|Hxy].
    + eapply type_prefix_trans; [|exact Hmodel].
      apply (interpret_comparable_type F τ); [exact Hscope|exact HX| | |apply list_clocks_refl].
      * intros z _. apply clock_equivalent_refl.
      * intros z Hz. unfold type_assume. rewrite decide_False by set_solver. apply Hfamilies.
    + rewrite (type_assume_absent X b P y Hbound). exact Hmodel.
Qed.

Local Lemma variable_replacement_clock_fresh b η t y :
  y ∉ binder_set b -> clock_bind η b t y = η y.
Proof. intros Hout. unfold clock_bind. now rewrite decide_False. Qed.

Local Lemma variable_replacement_arrow_clock_fresh bs η ts y :
  length bs = length ts -> y ∉ binders_set bs ->
  clock_extend η (bmap bs ts) y = η y.
Proof.
  intros Hlen Hout. unfold clock_extend.
  assert (Hnone : bmap bs ts !! y = None).
  { apply not_elem_of_dom. now rewrite dom_bmap. }
  exact (f_equal (default (η y)) Hnone).
Qed.

Local Lemma substitution_disjoint_part (L S T : gset string) :
  S ⊆ T -> L ## T -> L ## S.
Proof. set_solver. Qed.

Local Lemma interpret_without_replacement F n x ρ τ η X Y ts :
  x ∉ fvv_typ ρ -> regular_at F n X -> regular_at F n Y ->
  models_replacement F n x τ (fvv_typ ρ) η X Y ->
  type_prefix n (interpret_type F ρ η X ts) (interpret_type F ρ η Y ts).
Proof.
  intros Hfresh HX HY H.
  apply (interpret_comparable_type F ρ);
    [exact (proj1 HX)|exact (proj1 HY)|intros; apply clock_equivalent_refl| |apply list_clocks_refl].
  eapply replacement_shadowed; eassumption.
Qed.

Section InterpretTypeReplacement.
Context (F : graph) (x : string) (τ : typ).

Local Fixpoint interpret_replaced_type (ρ : typ) {struct ρ} :
  forall n η X Y ts, regular_at F n X -> regular_at F n Y ->
    fv_typ τ ## bv_typ ρ -> fvv_typ τ ## bvv_typ ρ ->
    models_replacement F n x τ (fvv_typ ρ) η X Y ->
    type_prefix n (interpret_type F (vsubst_typ x τ ρ) η X ts)
                  (interpret_type F ρ η Y ts)
with interpret_replaced_atom (σ : typat) {struct σ} :
  forall n η X Y t, regular_at F n X -> regular_at F n Y ->
    fv_typ τ ## bv_typat σ -> fvv_typ τ ## bvv_typat σ ->
    models_replacement F n x τ (fvv_typat σ) η X Y ->
    element_prefix n (interpret_at F (vsubst_typat x τ σ) η X t)
                     (interpret_at F σ η Y t).
Proof.
  - rename interpret_replaced_type into ST. rename interpret_replaced_atom into SA.
    destruct ρ as [y|b|σ d|b ρ|ρ d|b k ρ|y σ d]; intros n η X Y ts HX HY Htime Hvars HR;
      cbn [vsubst_typ interpret_type];
      cbn [fv_typ bv_typ fvv_typ bvv_typ] in Htime, Hvars, HR.
    + assert (Hy : y ∈ ({[y]} : gset string)) by (apply elem_of_singleton; reflexivity).
      specialize (HR y Hy ts ts (list_clocks_refl F ts)).
      rewrite type_assume_named in HR. destruct (decide (x = y)); exact HR.
    + apply type_prefix_refl.
    + apply anchored_prefix; [apply clock_equivalent_refl|now apply (SA σ)].
    + destruct ts as [|t ts]; [apply type_prefix_refl|].
      apply (ST ρ); [exact HX|exact HY| |exact Hvars|].
      * eapply substitution_disjoint_part; [|exact Htime]. clear ST SA. set_solver.
      * eapply replacement_clock_scope; [exact HX| |exact HR].
        intros y Hy. rewrite variable_replacement_clock_fresh; [apply clock_equivalent_refl|].
        clear ST SA. set_solver.
    + now apply (ST ρ).
    + destruct (decide (BNamed x = b)) as [Heq|Hne].
      * subst b. apply (interpret_without_replacement F n x (TForall (BNamed x) k ρ) τ η X Y ts);
          try assumption.
        clear ST SA. cbn [fvv_typ binder_set]. set_solver.
      * apply universal_prefix. intros A HA.
        assert (HXA : regular_at F n (type_assume X b A)).
        { apply regular_assume; [exact HX|now apply family_scope_monotone|now apply family_shape_related]. }
        assert (HYA : regular_at F n (type_assume Y b A)).
        { apply regular_assume; [exact HY|now apply family_scope_monotone|now apply family_shape_related]. }
        apply (ST ρ); [exact HXA|exact HYA|exact Htime| |].
        -- eapply substitution_disjoint_part; [|exact Hvars]. clear ST SA. set_solver.
        -- apply replacement_under_binder;
             [exact HX|exact (proj1 HXA)|congruence| |now apply family_shape_related|exact HR].
           clear ST SA. set_solver.
    + destruct (decide (BNamed x = BNamed y)) as [Heq|Hne].
      * injection Heq as Hxy. subst y.
        apply (interpret_without_replacement F n x (TRec x σ d) τ η X Y ts); try assumption.
        clear ST SA. cbn [fvv_typ binder_set]. set_solver.
      * apply anchored_prefix; [apply clock_equivalent_refl|].
        apply recursive_element_compare; [apply clock_equivalent_refl|].
        intros j Hj P Q HP.
        assert (HXj : regular_at F j X) by (apply (regular_weaken F n); assumption).
        assert (HYj : regular_at F j Y) by (apply (regular_weaken F n); assumption).
        apply (SA σ).
        -- now apply regular_assume_anchor.
        -- now apply regular_assume_anchor.
        -- exact Htime.
        -- eapply substitution_disjoint_part; [|exact Hvars]. clear ST SA. set_solver.
        -- apply replacement_under_binder;
             [exact HXj|exact (proj1 (regular_assume_anchor F j X _ _ _ HXj))|congruence| | |].
           ++ clear ST SA. set_solver.
           ++ intros ats aus _. apply anchored_prefix; [apply clock_equivalent_refl|exact HP].
           ++ eapply (replacement_weaken F n); eassumption.
  - rename interpret_replaced_type into ST. rename interpret_replaced_atom into SA.
    destruct σ as [ρ|ρ1 ρ2|ρ1 ρ2|bs Δ d rs ρ]; intros n η X Y t HX HY Htime Hvars HR;
      cbn [vsubst_typat interpret_at];
      cbn [bv_typat fvv_typat bvv_typat] in Htime, Hvars, HR.
    + pose proof (ST ρ n η X Y [] HX HY Htime Hvars HR) as HA.
      apply array_result_compare; [apply clock_equivalent_refl|exact (proj1 HA)|exact (proj2 HA)].
    + apply product_result_compare; [apply clock_equivalent_refl| |]; apply usable_prefix_same.
      * apply (ST ρ1); [exact HX|exact HY| | |].
        all: first [eapply substitution_disjoint_part; [|eassumption]|
                    eapply replacement_restrict; [|exact HR]]; clear ST SA; set_solver.
      * apply (ST ρ2); [exact HX|exact HY| | |].
        all: first [eapply substitution_disjoint_part; [|eassumption]|
                    eapply replacement_restrict; [|exact HR]]; clear ST SA; set_solver.
    + apply sum_result_compare; [apply clock_equivalent_refl| |]; apply usable_prefix_same.
      * apply (ST ρ1); [exact HX|exact HY| | |].
        all: first [eapply substitution_disjoint_part; [|eassumption]|
                    eapply replacement_restrict; [|exact HR]]; clear ST SA; set_solver.
      * apply (ST ρ2); [exact HX|exact HY| | |].
        all: first [eapply substitution_disjoint_part; [|eassumption]|
                    eapply replacement_restrict; [|exact HR]]; clear ST SA; set_solver.
    + apply function_result_compare; [apply clock_equivalent_refl|].
      split; [reflexivity|]. intros ts Hlen.
      set (η' := clock_extend η (bmap bs ts)).
      assert (Hclock : forall y, y ∈ fv_typ τ -> clock_equivalent F (η' y) (η y)).
      { intros y Hy. unfold η'. rewrite variable_replacement_arrow_clock_fresh.
        - apply clock_equivalent_refl.
        - symmetry. exact Hlen.
        - clear ST SA. set_solver. }
      split; [reflexivity|]. split; [apply clock_equivalent_refl|]. split.
      * cbn [call_parameters]. fold η'. rewrite <-list_fmap_compose. unfold compose.
        assert (HQtime : fv_typ τ ## ⋃ (bv_typ <$> rs)).
        { eapply substitution_disjoint_part; [|exact Htime]. clear ST SA. set_solver. }
        assert (HQvars : fvv_typ τ ## ⋃ (bvv_typ <$> rs)).
        { eapply substitution_disjoint_part; [|exact Hvars]. clear ST SA. set_solver. }
        assert (HQ : models_replacement F n x τ (⋃ (fvv_typ <$> rs)) η' X Y).
        { eapply replacement_clock_scope; [exact HX|exact Hclock|].
          eapply replacement_restrict; [|exact HR]. clear ST SA. set_solver. }
        clear Hlen Htime Hvars HR. revert HQtime HQvars HQ.
        induction rs as [|r rs IH]; intros HQtime HQvars HQ.
        -- constructor.
        -- rewrite !fmap_cons. constructor.
           ++ apply usable_prefix_same. apply (ST r); [exact HX|exact HY| | |].
              ** eapply substitution_disjoint_part; [|exact HQtime].
                 clear ST SA. rewrite fmap_cons, union_list_cons. set_solver.
              ** eapply substitution_disjoint_part; [|exact HQvars].
                 clear ST SA. rewrite fmap_cons, union_list_cons. set_solver.
              ** eapply replacement_restrict; [|exact HQ].
                 clear ST SA. rewrite fmap_cons, union_list_cons. set_solver.
           ++ apply IH.
              ** eapply substitution_disjoint_part; [|exact HQtime].
                 clear ST SA. rewrite fmap_cons, union_list_cons. set_solver.
              ** eapply substitution_disjoint_part; [|exact HQvars].
                 clear ST SA. rewrite fmap_cons, union_list_cons. set_solver.
              ** eapply replacement_restrict; [|exact HQ].
                 clear ST SA. rewrite fmap_cons, union_list_cons. set_solver.
      * cbn [call_result]. fold η'. apply usable_prefix_same. apply (ST ρ); [exact HX|exact HY| | |].
        -- eapply substitution_disjoint_part; [|exact Htime]. clear ST SA. set_solver.
        -- eapply substitution_disjoint_part; [|exact Hvars]. clear ST SA. set_solver.
        -- eapply replacement_clock_scope; [exact HX|exact Hclock|].
           eapply replacement_restrict; [|exact HR]. clear ST SA. set_solver.
Defined.
End InterpretTypeReplacement.

Local Lemma admissible_regular F n X : admissible_assignment F X -> regular_at F n X.
Proof.
  intros HX. split; [now apply admissible_scope_monotone|intros x; now apply family_shape_related].
Qed.

Local Definition element_inclusion n (P Q : element_spec) :=
  forall k, (k <= n)%nat -> forall (W : resource k) v, P k W v -> Q k W v.

Local Lemma expression_spec_post_inclusion n F (W : resource n) T e P Q :
  element_inclusion n P Q -> expression_spec n F W T e P -> expression_spec n F W T e Q.
Proof.
  revert W T e. induction n as [|n IH]; intros W T e Hrel; cbn [expression_spec]; [tauto|].
  assert (Hlow : element_inclusion n P Q) by (intros k Hk; apply Hrel; lia).
  intros [Hprev Hnow]. split; [now apply IH|].
  intros V σ α G Hext Hstore HG.
  destruct (Hnow V σ α G Hext Hstore HG) as (Hsafe & Hde & Hv & Hnext).
  split; [exact Hsafe|]. split; [exact Hde|]. split.
  - destruct e; try exact I. destruct Hv as [Hleaf Hv]. split; [exact Hleaf|].
    exact (Hrel (S n) (Nat.le_refl _) V v Hv).
  - intros σ' α' G' T' e' Hstep HG'.
    destruct (Hnext _ _ _ _ _ Hstep HG') as (U & HU & Hstore' & Hcont).
    exists U. split; [exact HU|]. split; [exact Hstore'|now apply IH].
Qed.

Local Lemma model_type_apply δ Δ Γ x k e ρ τ :
  fv_typ τ ## bv_typ ρ -> fvv_typ τ ## bvv_typ ρ ->
  expression_typing_model δ Δ Γ e (TForall (BNamed x) k ρ) ->
  expression_typing_model δ Δ Γ e (vsubst_typ x τ ρ).
Proof.
  intros Htime Hvars Hmodel F η X n W E HX HΔ Henv.
  set (A := fun ts => interpret_type F τ η X ts).
  assert (HA : family_shape F A) by now apply interpret_family_shape.
  assert (HX' := admissible_type_assume F X (BNamed x) A HX HA).
  assert (Hsub : type_prefix n (interpret_type F (vsubst_typ x τ ρ) η X [])
     (interpret_type F ρ η (type_assume X (BNamed x) A) [])).
  { apply interpret_replaced_type; [now apply admissible_regular|now apply admissible_regular|
       exact Htime|exact Hvars|].
    intros y _. apply family_shape_related. exact (HX' y). }
  eapply expression_spec_post_inclusion; [|exact (Hmodel F η X n W E HX HΔ Henv)].
  intros i Hi V v [Hscope Hvalue].
  apply (usable_prefix_same n _ _ (η δ) (type_prefix_sym _ _ _ Hsub) i Hi V v).
  split; [exact (Hscope A HA)|exact (Hvalue A HA)].
Qed.

Local Lemma recursive_body_congruence F t n x σ σ' η X :
  regular_at F n X ->
  (forall i η Z t, regular_at F i Z ->
     element_prefix i (interpret_at F σ η Z t) (interpret_at F σ' η Z t)) ->
  element_prefix n
    (recursive_element F t (fun P =>
       interpret_at F σ η (type_assume X (BNamed x) (fun _ => anchored F t P)) t))
    (recursive_element F t (fun P =>
       interpret_at F σ' η (type_assume X (BNamed x) (fun _ => anchored F t P)) t)).
Proof.
  intros HX Hbody. apply recursive_element_compare; [apply clock_equivalent_refl|].
  intros j Hj P Q HP. pose proof (regular_weaken F n j X Hj HX) as HXj.
  eapply element_prefix_trans.
  - apply Hbody, regular_assume_anchor, HXj.
  - apply (interpret_comparable_atom F σ').
    + exact (proj1 (regular_assume_anchor F j X _ _ _ HXj)).
    + exact (proj1 (regular_assume_anchor F j X _ _ _ HXj)).
    + intros; apply clock_equivalent_refl.
    + apply type_assume_related.
      * intros y _. exact (proj2 HXj y).
      * intros ats aus _. apply anchored_prefix; [apply clock_equivalent_refl|exact HP].
    + apply clock_equivalent_refl.
Qed.

Local Lemma element_prefix_list_refl n es : Forall2 (element_prefix n) es es.
Proof. induction es; constructor; auto using element_prefix_refl. Qed.

Local Lemma returned_type_congruence F n bs Δ d rs ρ τ η X t :
  regular_at F n X ->
  (forall i η Z ts, regular_at F i Z ->
     type_prefix i (interpret_type F ρ η Z ts) (interpret_type F τ η Z ts)) ->
  element_prefix n (interpret_at F (TArrow bs Δ d rs ρ) η X t)
                   (interpret_at F (TArrow bs Δ d rs τ) η X t).
Proof.
  intros HX Hreturn. apply function_result_compare; [apply clock_equivalent_refl|].
  split; [reflexivity|]. intros ts Hlen. cbn [call_constraints call_time call_parameters call_result].
  split; [reflexivity|]. split; [apply clock_equivalent_refl|]. split.
  - apply element_prefix_list_refl.
  - apply usable_prefix_same. now apply Hreturn.
Qed.

Local Lemma type_renaming_environment F n x y L η X A B :
  y ∉ L -> regular_at F n X -> related_families F n A B ->
  models_replacement F n x (TVar y) L η
    (type_assume X (BNamed y) A) (type_assume X (BNamed x) B).
Proof.
  intros Hfresh HX HAB z Hz ts us Hts. rewrite !type_assume_named.
  destruct (decide (x = z)).
  - cbn [interpret_type]. rewrite type_assume_named, decide_True by reflexivity. now apply HAB.
  - rewrite decide_False by congruence.
    exact (proj2 HX z ts us Hts).
Qed.

Combined Scheme alpha_mutual_ind from alpha_typ_rec, alpha_typat_rec, alpha_list_rec.

Local Lemma interpretation_alpha F :
  (forall ρ τ, alpha_typ ρ τ -> forall n η X ts, regular_at F n X ->
    type_prefix n (interpret_type F ρ η X ts) (interpret_type F τ η X ts)) /\
  (forall σ σ', alpha_typat σ σ' -> forall n η X t, regular_at F n X ->
    element_prefix n (interpret_at F σ η X t) (interpret_at F σ' η X t)) /\
  (forall rs qs, alpha_list rs qs -> rs = qs).
Proof.
  apply alpha_mutual_ind.
  - intros. apply type_prefix_refl.
  - intros. apply type_prefix_refl.
  - intros σ σ' d Hα IH n η X ts HX. cbn [interpret_type].
    apply anchored_prefix; [apply clock_equivalent_refl|now apply IH].
  - intros b ρ τ Hα IH n η X ts HX. destruct ts as [|t ts]; cbn [interpret_type].
    + apply type_prefix_refl.
    + now apply IH.
  - intros ρ τ d Hα IH n η X ts HX. cbn [interpret_type]. now apply IH.
  - intros b k ρ τ Hα IH n η X ts HX. cbn [interpret_type]. apply universal_prefix.
    intros A HA. apply IH, regular_assume; [exact HX|now apply family_scope_monotone|now apply family_shape_related].
  - intros x y k ρ τ Hα IH Hfresh n η X ts HX. cbn [interpret_type].
    apply universal_prefix. intros A HA.
    assert (HXA : regular_at F n (type_assume X (BNamed x) A)).
    { apply regular_assume; [exact HX|now apply family_scope_monotone|now apply family_shape_related]. }
    assert (HYA : regular_at F n (type_assume X (BNamed y) A)).
    { apply regular_assume; [exact HX|now apply family_scope_monotone|now apply family_shape_related]. }
    eapply type_prefix_trans; [exact (IH n η _ ts HXA)|].
    apply type_prefix_sym, interpret_replaced_type; [exact HYA|exact HXA| | |].
    + simpl. set_solver.
    + simpl. set_solver.
    + apply type_renaming_environment; [set_solver|exact HX|now apply family_shape_related].
  - intros x σ d σ' Hα IH n η X ts HX. cbn [interpret_type].
    apply anchored_prefix; [apply clock_equivalent_refl|now apply recursive_body_congruence].
  - intros x y σ d σ' Hα IH Hfresh n η X ts HX. cbn [interpret_type].
    apply anchored_prefix; [apply clock_equivalent_refl|].
    apply recursive_element_compare; [apply clock_equivalent_refl|].
    intros j Hj P Q HP. pose proof (regular_weaken F n j X Hj HX) as HXj.
    eapply element_prefix_trans.
    + apply IH, regular_assume_anchor, HXj.
    + apply element_prefix_sym, interpret_replaced_atom.
      * now apply regular_assume_anchor.
      * now apply regular_assume_anchor.
      * simpl. set_solver.
      * simpl. set_solver.
      * apply type_renaming_environment; [set_solver|exact HXj|].
        intros ts' us' _. apply anchored_prefix; [apply clock_equivalent_refl|now apply element_prefix_sym].
  - intros ρ τ Hα IH n η X t HX. cbn [interpret_at].
    destruct (IH n η X [] HX) as [Hscope Hval].
    apply array_result_compare; [apply clock_equivalent_refl|exact Hscope|exact Hval].
  - intros ρ1 τ1 ρ2 τ2 Hα1 IH1 Hα2 IH2 n η X t HX. cbn [interpret_at].
    apply product_result_compare; [apply clock_equivalent_refl| |];
      apply usable_prefix_same; [now apply IH1|now apply IH2].
  - intros ρ1 τ1 ρ2 τ2 Hα1 IH1 Hα2 IH2 n η X t HX. cbn [interpret_at].
    apply sum_result_compare; [apply clock_equivalent_refl| |];
      apply usable_prefix_same; [now apply IH1|now apply IH2].
  - intros bs Δ ρ τ rs qs d Hlist IHargs Hα IH n η X t HX.
    subst qs. now apply returned_type_congruence.
  - intros. congruence.
  - reflexivity.
Qed.

Local Lemma model_type_conversion δ Δ Γ e ρ τ :
  (forall F n η X, regular_at F n X ->
     type_prefix n (interpret_type F ρ η X []) (interpret_type F τ η X [])) ->
  expression_typing_model δ Δ Γ e τ -> expression_typing_model δ Δ Γ e ρ.
Proof.
  intros Hconvert Hmodel F η X n W E HX HΔ Henv.
  eapply expression_spec_post_prefix; [|exact (Hmodel F η X n W E HX HΔ Henv)].
  apply usable_prefix_same, type_prefix_sym. apply Hconvert, admissible_regular, HX.
Qed.

Local Lemma model_alpha δ Δ Γ e ρ τ :
  alpha_typ ρ τ -> expression_typing_model δ Δ Γ e τ -> expression_typing_model δ Δ Γ e ρ.
Proof. intros H. apply model_type_conversion. intros F n η X HX. exact (proj1 (interpretation_alpha F) _ _ H n η X [] HX). Qed.

Local Lemma clock_bind_named η x t z :
  clock_bind η (BNamed x) t z = if decide (x = z) then t else η z.
Proof.
  unfold clock_bind. cbn [binder_set].
  destruct (decide (x = z)) as [->|Hne];
    [rewrite decide_True by set_solver|rewrite decide_False by set_solver]; reflexivity.
Qed.

Local Lemma find_opt_named (x y z : string) :
  find_opt {[x:=y]} z = if decide (x = z) then y else z.
Proof.
  unfold find_opt. destruct (decide (x = z)) as [->|Hne].
  - now rewrite lookup_singleton_eq.
  - now rewrite lookup_singleton_ne.
Qed.

Local Lemma renamed_clock_assignment (η : clock_assignment) (x y : string) t (L : gset string) :
  y ∉ (L ∖ {[x]}) ->
  forall z, z ∈ L ->
    clock_bind η (BNamed x) t z = clock_bind η (BNamed y) t (find_opt {[x:=y]} z).
Proof.
  intros Hfresh z Hz. rewrite find_opt_named, clock_bind_named.
  destruct (decide (x = z)) as [->|Hne].
  - now rewrite clock_bind_named, decide_True by reflexivity.
  - rewrite clock_bind_named, decide_False; [reflexivity|set_solver].
Qed.

Local Lemma renamed_clock_type F n ρ η X ts t x y :
  regular_at F n X -> y ∉ bv_typ ρ -> y ∉ fv_typ ρ ∖ {[x]} ->
  type_prefix n (interpret_type F ρ (clock_bind η (BNamed x) t) X ts)
     (interpret_type F (tsubst_typ {[x:=y]} ρ) (clock_bind η (BNamed y) t) X ts).
Proof.
  intros HX Hbound Hfree. eapply type_prefix_trans.
  - apply (interpret_comparable_type F ρ);
      [exact (proj1 HX)|exact (proj1 HX)| |intros z _; apply (proj2 HX z)|apply list_clocks_refl].
    intros z Hz. rewrite (renamed_clock_assignment _ _ _ _ _ Hfree z Hz). apply clock_equivalent_refl.
  - apply type_prefix_sym, interpret_type_substitution; [exact HX|].
    intros p q Hpq. apply lookup_singleton_Some in Hpq as [_ ->]. exact Hbound.
Qed.

Local Lemma renamed_clock_constraints F Δ η x y t :
  y ∉ fv_constraints Δ ∖ {[x]} ->
  (clock_constraints F (clock_bind η (BNamed x) t) Δ <->
   clock_constraints F (clock_bind η (BNamed y) t) (tsubst_constraints {[x:=y]} Δ)).
Proof.
  intros Hfresh. rewrite clock_constraints_substitute. apply clock_constraints_ext.
  intros a b Hmem. destruct (constraint_endpoints Δ a b Hmem) as [Ha Hb].
  split; now apply (renamed_clock_assignment η x y t (fv_constraints Δ)).
Qed.

Local Lemma clock_extend_single η x t z :
  clock_extend η (bmap [BNamed x] [t]) z = clock_bind η (BNamed x) t z.
Proof.
  rewrite clock_extend_cons. change (clock_extend (clock_bind η (BNamed x) t) ∅ z = clock_bind η (BNamed x) t z).
  unfold clock_extend. now rewrite lookup_empty.
Qed.

Local Lemma bound_single_clock x : binders_set [BNamed x] = {[x]}.
Proof.
  rewrite binders_set_cons. change (({[x]} : gset string) ∪ ∅ = {[x]}). set_solver.
Qed.

Local Lemma renamed_arrow_clocks F n η X t x y Δ d rs ρ :
  regular_at F n X ->
  y ∉ fv_typat (TArrow [BNamed x] Δ d rs ρ) ->
  y ∉ ⋃ (bv_typ <$> rs) ∪ bv_typ ρ ->
  element_prefix n
    (interpret_at F (TArrow [BNamed x] Δ d rs ρ) η X t)
    (interpret_at F (TArrow [BNamed y] (tsubst_constraints {[x:=y]} Δ)
      (find_opt {[x:=y]} d) (tsubst_typ {[x:=y]} <$> rs) (tsubst_typ {[x:=y]} ρ)) η X t).
Proof.
  intros HX Hfree Hbound. cbn [interpret_at]. apply function_result_compare; [apply clock_equivalent_refl|].
  cbn [fv_typat] in Hfree. rewrite bound_single_clock in Hfree.
  split; [reflexivity|]. intros [|u [|v vs]] Hlen; try discriminate Hlen.
  cbn [call_constraints call_time call_parameters call_result].
  set (ηx := clock_bind η (BNamed x) u). set (ηy := clock_bind η (BNamed y) u).
  assert (Hix : forall z, clock_extend η (bmap [BNamed x] [u]) z = ηx z) by apply clock_extend_single.
  assert (Hiy : forall z, clock_extend η (bmap [BNamed y] [u]) z = ηy z) by apply clock_extend_single.
  assert (Hcur : ηx d = ηy (find_opt {[x:=y]} d)).
  { apply (renamed_clock_assignment η x y u ({[d]} : gset string)); set_solver. }
  split.
  - transitivity (clock_constraints F ηx Δ).
    + apply clock_constraints_ext. intros; split; apply Hix.
    + transitivity (clock_constraints F ηy (tsubst_constraints {[x:=y]} Δ)).
      * apply (renamed_clock_constraints F Δ η x y u). set_solver.
      * apply clock_constraints_ext. intros; split; symmetry; apply Hiy.
  - rewrite (Hix d), (Hiy (find_opt {[x:=y]} d)), <-Hcur.
    split; [apply clock_equivalent_refl|]. split.
    + rewrite <-list_fmap_compose. unfold compose.
      assert (Hrfree : y ∉ ⋃ (fv_typ <$> rs) ∖ {[x]}).
      { set_solver. }
      assert (Hrbound : y ∉ ⋃ (bv_typ <$> rs)) by set_solver.
      clear Hfree Hbound Hlen. revert Hrfree Hrbound.
      induction rs as [|r rs IH]; intros Hf Hb.
      * constructor.
      * rewrite !fmap_cons. apply Forall2_cons. split.
        -- apply usable_prefix_same. eapply type_prefix_trans.
           ++ apply compare_clock_assignments; [exact HX|exact Hix].
           ++ eapply type_prefix_trans with (B:=interpret_type F (tsubst_typ {[x:=y]} r) ηy X []).
              ** apply (renamed_clock_type F n r η X [] u x y); [exact HX| |];
                   [rewrite fmap_cons, union_list_cons in Hb|rewrite fmap_cons, union_list_cons in Hf]; set_solver.
              ** apply compare_clock_assignments; [exact HX|intros; symmetry; apply Hiy].
        -- apply IH; [rewrite fmap_cons, union_list_cons in Hf|rewrite fmap_cons, union_list_cons in Hb]; set_solver.
    + apply usable_prefix_same. eapply type_prefix_trans with (B:=interpret_type F ρ ηx X []).
      * apply compare_clock_assignments; [exact HX|exact Hix].
      * eapply type_prefix_trans with (B:=interpret_type F (tsubst_typ {[x:=y]} ρ) ηy X []).
        -- apply (renamed_clock_type F n ρ η X [] u x y); [exact HX|set_solver|set_solver].
        -- apply compare_clock_assignments; [exact HX|intros; symmetry; apply Hiy].
Qed.

Combined Scheme alphat_mutual_ind from alphat_typ_rec, alphat_typat_rec, alphat_list_rec.

Local Lemma interpretation_alphat F :
  (forall ρ τ, alphat_typ ρ τ -> forall n η X ts, regular_at F n X ->
    type_prefix n (interpret_type F ρ η X ts) (interpret_type F τ η X ts)) /\
  (forall σ σ', alphat_typat σ σ' -> forall n η X t, regular_at F n X ->
    element_prefix n (interpret_at F σ η X t) (interpret_at F σ' η X t)) /\
  (forall rs qs, alphat_list rs qs -> rs = qs).
Proof.
  apply alphat_mutual_ind.
  - intros. apply type_prefix_refl.
  - intros. apply type_prefix_refl.
  - intros σ σ' d Hα IH n η X ts HX. cbn [interpret_type].
    apply anchored_prefix; [apply clock_equivalent_refl|now apply IH].
  - intros b ρ τ Hα IH n η X ts HX. destruct ts as [|t ts]; cbn [interpret_type].
    + apply type_prefix_refl.
    + now apply IH.
  - intros x y ρ τ Hα IH Hfresh n η X [|t ts] HX; cbn [interpret_type].
    + apply type_prefix_refl.
    + eapply type_prefix_trans; [apply IH; exact HX|].
      apply renamed_clock_type; [exact HX|set_solver|set_solver].
  - intros ρ τ d Hα IH n η X ts HX. cbn [interpret_type]. now apply IH.
  - intros b k ρ τ Hα IH n η X ts HX. cbn [interpret_type]. apply universal_prefix.
    intros A HA. apply IH, regular_assume; [exact HX|now apply family_scope_monotone|now apply family_shape_related].
  - intros x σ d σ' Hα IH n η X ts HX. cbn [interpret_type].
    apply anchored_prefix; [apply clock_equivalent_refl|now apply recursive_body_congruence].
  - intros ρ τ Hα IH n η X t HX. cbn [interpret_at].
    destruct (IH n η X [] HX) as [Hscope Hval].
    apply array_result_compare; [apply clock_equivalent_refl|exact Hscope|exact Hval].
  - intros ρ1 τ1 ρ2 τ2 Hα1 IH1 Hα2 IH2 n η X t HX. cbn [interpret_at].
    apply product_result_compare; [apply clock_equivalent_refl| |];
      apply usable_prefix_same; [now apply IH1|now apply IH2].
  - intros ρ1 τ1 ρ2 τ2 Hα1 IH1 Hα2 IH2 n η X t HX. cbn [interpret_at].
    apply sum_result_compare; [apply clock_equivalent_refl| |];
      apply usable_prefix_same; [now apply IH1|now apply IH2].
  - intros bs Δ ρ τ rs qs d Hlist IHargs Hα IH n η X t HX.
    subst qs. now apply returned_type_congruence.
  - intros x y Δ ρ τ rs qs d m Hlist IHargs Hα IH Hfree Hbound Heq n η X t HX.
    subst qs m. eapply element_prefix_trans.
    + apply returned_type_congruence; eassumption.
    + now apply renamed_arrow_clocks.
  - intros. congruence.
  - reflexivity.
Qed.

Local Lemma model_alphat δ Δ Γ e ρ τ :
  alphat_typ ρ τ -> expression_typing_model δ Δ Γ e τ -> expression_typing_model δ Δ Γ e ρ.
Proof. intros H. apply model_type_conversion. intros F n η X HX. exact (proj1 (interpretation_alphat F) _ _ H n η X [] HX). Qed.

Local Lemma element_inclusion_refl n P : element_inclusion n P P.
Proof. intros k Hk W v H. exact H. Qed.

Local Lemma element_inclusion_trans n P Q R :
  element_inclusion n P Q -> element_inclusion n Q R -> element_inclusion n P R.
Proof. intros HP HQ k Hk W v H. exact (HQ k Hk W v (HP k Hk W v H)). Qed.

Local Lemma element_inclusion_weaken n m P Q :
  (m <= n)%nat -> element_inclusion n P Q -> element_inclusion m P Q.
Proof. intros Hle H k Hk. apply H. lia. Qed.

Local Lemma usable_reanchor F n A t u :
  type_shape F A -> reachable F t u -> element_inclusion n (usable_at A t) (usable_at A u).
Proof. intros [Hscope _] Htu k Hk W v [Ht Hv]. split; [exact (Hscope t u Htu Ht)|exact Hv]. Qed.

Local Lemma location_spec_subsumes F n t u P Q :
  reachable F t u ->
  (forall k, (k <= n)%nat -> forall (W : resource k) l d, P k W l d -> Q k W l d) ->
  element_inclusion n (location_spec F t P) (location_spec F u Q).
Proof.
  intros Htu Hshape k Hk W v (l & o & d & Hv & Hloc & Hreach & HP).
  exists l, o, d. refine (conj Hv (conj Hloc _)). split.
  - unfold reachable in *. etransitivity; eassumption.
  - exact (Hshape k Hk W l d HP).
Qed.

Local Lemma product_result_subsumes F n t u P Q P' Q' :
  reachable F t u -> element_inclusion n P P' -> element_inclusion n Q Q' ->
  element_inclusion n (product_result F t P Q) (product_result F u P' Q').
Proof.
  intros Htu HP HQ. apply location_spec_subsumes; [exact Htu|].
  intros k Hk W l d (v & w & Hd & Hv & Hw). exists v, w. split; [exact Hd|].
  split; [exact (HP k Hk W v Hv)|exact (HQ k Hk W w Hw)].
Qed.

Local Lemma sum_result_subsumes F n t u P Q P' Q' :
  reachable F t u -> element_inclusion n P P' -> element_inclusion n Q Q' ->
  element_inclusion n (sum_result F t P Q) (sum_result F u P' Q').
Proof.
  intros Htu HP HQ. apply location_spec_subsumes; [exact Htu|].
  intros k Hk W l d [(v & Hd & Hv)|(w & Hd & Hw)].
  - left. exists v. split; [exact Hd|exact (HP k Hk W v Hv)].
  - right. exists w. split; [exact Hd|exact (HQ k Hk W w Hw)].
Qed.

Local Lemma arguments_inclusion n k (W : resource k) (Ps Qs : list element_spec) (vs : list val) :
  (k <= n)%nat -> Forall2 (element_inclusion n) Ps Qs ->
  Forall2 (fun E v => E k W v) Ps vs -> Forall2 (fun E v => E k W v) Qs vs.
Proof.
  intros Hk Hrel. revert vs. induction Hrel; intros vs Hvs; [exact Hvs|].
  destruct vs as [|v vs]; [inversion Hvs|].
  apply Forall2_cons in Hvs as [Hv Htail]. apply Forall2_cons. split.
  - exact (H k Hk W v Hv).
  - now apply IHHrel.
Qed.

Local Definition signature_subsumes F n sig sig' :=
  time_arity sig = time_arity sig' /\
  (forall ts, length (call_parameters sig ts) = length (call_parameters sig' ts)) /\
  forall ts, length ts = time_arity sig -> call_constraints sig' ts ->
    call_constraints sig ts /\
    clock_equivalent F (call_time sig ts) (call_time sig' ts) /\
    Forall2 (element_inclusion n) (call_parameters sig' ts) (call_parameters sig ts) /\
    element_inclusion n (call_result sig ts) (call_result sig' ts).

Local Lemma signature_subsumes_refl F n sig : signature_subsumes F n sig sig.
Proof.
  split; [reflexivity|]. split; [intros; reflexivity|]. intros ts Hlen Hc. split; [exact Hc|].
  split; [apply clock_equivalent_refl|]. split; [|apply element_inclusion_refl].
  induction (call_parameters sig ts); constructor; auto using element_inclusion_refl.
Qed.

Local Lemma closure_body_specification_subsumes F n t u sig sig' l self bs body k (W : resource k) :
  (k <= n)%nat -> reachable F t u -> signature_subsumes F n sig sig' ->
  closure_body_specification F t sig l self bs body k W ->
  closure_body_specification F u sig' l self bs body k W.
Proof.
  intros Hk Htu (Harity & _ & Hsub) Hbody A ts vs caller Hext Hlen Hc Htime Hcurrent Hvals.
  assert (Hlen' : length ts = time_arity sig) by (rewrite Harity; exact Hlen).
  destruct (Hsub ts Hlen' Hc) as (Hpre & Hclock & Hargs & Hret).
  eapply expression_spec_post_inclusion; [exact (element_inclusion_weaken _ _ _ _ Hk Hret)|].
  eapply Hbody; [exact Hext|exact Hlen'|exact Hpre| | |].
  - eapply clock_equivalent_trans; eassumption.
  - unfold reachable in *. etransitivity; eassumption.
  - eapply arguments_inclusion; [exact Hk|exact Hargs|exact Hvals].
Qed.

Local Lemma function_result_subsumes F n t u sig sig' :
  reachable F t u -> signature_subsumes F n sig sig' ->
  element_inclusion n (function_result F t sig) (function_result F u sig').
Proof.
  intros Htu Hsig. apply location_spec_subsumes; [exact Htu|].
  intros k Hk W l d (self & bs & body & Hd & Harity & Hbody).
  exists self, bs, body. split; [exact Hd|]. split.
  - intros ts Hlen. pose proof (proj1 Hsig) as Har.
    rewrite (Harity ts (eq_trans Hlen (eq_sym Har))). exact (proj1 (proj2 Hsig) ts).
  - eapply all_lower_resources_transform; [|exact Hbody].
    intros j Hj A Hcheck. eapply (closure_body_specification_subsumes F n t u sig sig');
      [lia|exact Htu|exact Hsig|exact Hcheck].
Qed.

Local Lemma interpret_atom_reanchor F n σ η X s t :
  admissible_assignment F X -> reachable F s t ->
  element_inclusion n (interpret_at F σ η X s) (interpret_at F σ η X t).
Proof.
  intros HX Hst. destruct σ; cbn [interpret_at].
  - apply location_spec_subsumes; [exact Hst|auto].
  - apply product_result_subsumes; [exact Hst| |]; eapply usable_reanchor;
      [now apply interpret_type_shape|exact Hst|now apply interpret_type_shape|exact Hst].
  - apply sum_result_subsumes; [exact Hst| |]; eapply usable_reanchor;
      [now apply interpret_type_shape|exact Hst|now apply interpret_type_shape|exact Hst].
  - apply function_result_subsumes; [exact Hst|apply signature_subsumes_refl].
Qed.

Local Lemma prefix_inclusion n P Q : element_prefix n P Q -> element_inclusion n P Q.
Proof. intros H k Hk W v Hv. now apply (H k Hk W v). Qed.

Local Definition covariant_update F n x t (X Y : type_assignment) :=
  (forall y, y ≠ x -> related_families F n (X y) (Y y)) /\
  fst (Y x []) t /\ element_inclusion n (snd (X x [])) (snd (Y x [])).

Local Lemma assumed_anchor_covariant F n x s t X P Q :
  admissible_assignment F X -> element_inclusion n P Q ->
  covariant_update F n x t
    (type_assume X (BNamed x) (fun _ => anchored F s P))
    (type_assume X (BNamed x) (fun _ => anchored F t Q)).
Proof.
  intros HX Hinc. split.
  - intros y Hy. rewrite !type_assume_named, !decide_False by congruence. now apply family_shape_related.
  - rewrite !type_assume_named, !decide_True by reflexivity. split; [apply rtc_refl|exact Hinc].
Qed.

Local Lemma binder_excludes_name b x : b ≠ BNamed x -> x ∉ binder_set b.
Proof. destruct b; simpl; intros Hne Hx; [set_solver|]. apply elem_of_singleton in Hx. congruence. Qed.

Local Lemma covariance_under_other_binder F n x t X Y b A :
  covariant_update F n x t X Y -> family_shape F A -> b ≠ BNamed x ->
  covariant_update F n x t (type_assume X b A) (type_assume Y b A).
Proof.
  intros [Hother Hx] HA Hne. split.
  - intros z Hz. unfold type_assume. destruct (decide (z ∈ binder_set b));
      [now apply family_shape_related|now apply Hother].
  - rewrite !type_assume_absent by now apply binder_excludes_name. exact Hx.
Qed.

Local Lemma variable_not_read_type F n x t η X Y ρ:
  admissible_assignment F X -> admissible_assignment F Y ->
  (forall y, y ≠ x -> related_families F n (X y) (Y y)) ->
  x ∉ fvv_typ ρ ->
  element_inclusion n (usable_at (interpret_type F ρ η X []) t)
                     (usable_at (interpret_type F ρ η Y []) t).
Proof.
  intros HX HY Hothers Hfresh. apply prefix_inclusion, usable_prefix_same.
  apply (interpret_comparable_type F ρ);
    [now apply admissible_scope_monotone|now apply admissible_scope_monotone|
      intros; apply clock_equivalent_refl| |constructor].
  intros z Hz. apply Hothers. congruence.
Qed.

Local Lemma variable_not_read_atom F n x t η X Y σ:
  admissible_assignment F X -> admissible_assignment F Y ->
  (forall y, y ≠ x -> related_families F n (X y) (Y y)) ->
  x ∉ fvv_typat σ ->
  element_inclusion n (interpret_at F σ η X t) (interpret_at F σ η Y t).
Proof.
  intros HX HY Hothers Hfresh. apply prefix_inclusion.
  apply (interpret_comparable_atom F σ);
    [now apply admissible_scope_monotone|now apply admissible_scope_monotone|
      intros; apply clock_equivalent_refl| |apply clock_equivalent_refl].
  intros z Hz. apply Hothers. congruence.
Qed.

Local Lemma usable_universal F C t k (W : resource k) v :
  usable_at (universal_type F C) t k W v <->
  forall A, family_shape F A -> usable_at (C A) t k W v.
Proof.
  unfold usable_at, universal_type. simpl. split.
  - intros [Hscope Hvalues] A HA. exact (conj (Hscope A HA) (Hvalues A HA)).
  - intros H. split; intros A HA; apply (H A HA).
Qed.

Combined Scheme valid_variable_mutual from valid_variable_typ_rec, valid_variable_typat_rec.

Local Lemma validity_interpretation F :
  (forall Δ x d ρ u, valid_variable_typ Δ x d ρ u -> forall n η X Y,
    clock_constraints F η Δ -> admissible_assignment F X -> admissible_assignment F Y ->
    covariant_update F n x (η d) X Y ->
    element_inclusion n (usable_at (interpret_type F ρ η X []) (η u))
                        (usable_at (interpret_type F ρ η Y []) (η u))) /\
  (forall Δ x d σ u, valid_variable_typat Δ x d σ u -> forall n η X Y,
    clock_constraints F η Δ -> admissible_assignment F X -> admissible_assignment F Y ->
    covariant_update F n x (η d) X Y ->
    element_inclusion n (interpret_at F σ η X (η u)) (interpret_at F σ η Y (η u))).
Proof.
  apply valid_variable_mutual.
  - intros Δ x d y u Hvar n η X Y HΔ HX HY [Hothers [Hscope Hvalues]].
    cbn [interpret_type]. destruct (decide (x = y)) as [->|Hne].
    + intros k Hk W v [_ Hv]. split.
      * eapply (family_scope_monotone F (Y y) (HY y)); [|exact Hscope].
        apply (clock_reachable F η Δ d u HΔ), Hvar. reflexivity.
      * exact (Hvalues k Hk W v Hv).
    + apply prefix_inclusion, usable_prefix_same.
      apply Hothers; [congruence|constructor].
  - intros. apply element_inclusion_refl.
  - intros Δ x d σ u w Hv IH n η X Y HΔ HX HY Hupd k Hk W v [Hscope Hval].
    split; [exact Hscope|exact (IH n η X Y HΔ HX HY Hupd k Hk W v Hval)].
  - intros Δ x b k d ρ u Hv IH n η X Y HΔ HX HY Hupd.
    destruct (decide (b = BNamed x)) as [->|Hne].
    + apply (variable_not_read_type F n x); [exact HX|exact HY|exact (proj1 Hupd)|].
      cbn [fvv_typ binder_set]. set_solver.
    + intros i Hi W v H. cbn [interpret_type]. apply usable_universal. intros A HA.
      cbn [interpret_type] in H.
      pose proof (proj1 (usable_universal F _ (η u) i W v) H A HA) as Hvalue.
      eapply (IH Hne n η (type_assume X b A) (type_assume Y b A)); [exact HΔ|now apply admissible_type_assume|
        now apply admissible_type_assume|now apply covariance_under_other_binder|exact Hi|exact Hvalue].
  - intros Δ x y σ r d u Hfresh n η X Y HΔ HX HY Hupd.
    apply (variable_not_read_type F n x); [exact HX|exact HY|exact (proj1 Hupd)|exact Hfresh].
  - intros Δ x d ρ1 ρ2 u H1 IH1 H2 IH2 n η X Y HΔ HX HY Hupd. cbn [interpret_at].
    apply product_result_subsumes; [apply rtc_refl|now apply IH1|now apply IH2].
  - intros Δ x d ρ1 ρ2 u H1 IH1 H2 IH2 n η X Y HΔ HX HY Hupd. cbn [interpret_at].
    apply sum_result_subsumes; [apply rtc_refl|now apply IH1|now apply IH2].
  - intros Δ x d ρ u Hfresh n η X Y HΔ HX HY Hupd.
    now apply (variable_not_read_atom F n x); [| |exact (proj1 Hupd)|].
  - intros Δ x d bs Δ' w rs ρ u Hfresh n η X Y HΔ HX HY Hupd.
    now apply (variable_not_read_atom F n x); [| |exact (proj1 Hupd)|].
Qed.

Local Lemma interpretation_recursive_operator F σ η X t x :
  admissible_assignment F X ->
  forall n P Q, element_prefix n P Q ->
    element_prefix n
      (interpret_at F σ η (type_assume X (BNamed x) (fun _ => anchored F t P)) t)
      (interpret_at F σ η (type_assume X (BNamed x) (fun _ => anchored F t Q)) t).
Proof.
  intros HX n P Q HP.
  pose proof (admissible_regular F n X HX) as HR.
  apply (interpret_comparable_atom F σ).
  - exact (proj1 (regular_assume_anchor F n X _ _ _ HR)).
  - exact (proj1 (regular_assume_anchor F n X _ _ _ HR)).
  - intros; apply clock_equivalent_refl.
  - apply type_assume_related.
    + intros y _. exact (proj2 HR y).
    + intros ts us _. apply anchored_prefix; [apply clock_equivalent_refl|exact HP].
  - apply clock_equivalent_refl.
Qed.

Local Lemma folded_result_reanchor F s t P Q k (W : resource k) v :
  reachable F s t ->
  (forall l, delayed_element P k W (VLoc l) -> delayed_element Q k W (VLoc l)) ->
  folded_result F s P k W v -> folded_result F t Q k W v.
Proof.
  intros Hst HQ (w & Hv & l & o & d & -> & Hlook & Hreach & HP).
  exists (VLoc l). split; [exact Hv|]. exists l, o, d.
  split; [reflexivity|]. split; [exact Hlook|]. split.
  - unfold reachable in *. etransitivity; eassumption.
  - now apply HQ.
Qed.

Local Lemma recursive_elements_subsume F s t B C :
  reachable F s t ->
  (forall k P Q, element_prefix k P Q -> element_prefix k (B P) (B Q)) ->
  (forall k P Q, element_prefix k P Q -> element_prefix k (C P) (C Q)) ->
  (forall k, element_inclusion k (recursive_element F s B) (recursive_element F t C) ->
    element_inclusion k (B (recursive_element F s B)) (C (recursive_element F t C))) ->
  forall n, element_inclusion n (recursive_element F s B) (recursive_element F t C).
Proof.
  intros Hst HB HC Hnext. induction n as [|n IH]; intros k Hk W v Hv.
  - assert (k = 0)%nat by lia. subst k.
    apply (recursive_element_unfold F t C _ W v HC).
    eapply (folded_result_reanchor F s t (B (recursive_element F s B)) (C (recursive_element F t C)));
      [exact Hst|intros; exact I|].
    now apply (recursive_element_unfold F s B _ W v HB).
  - destruct (decide (k <= n)%nat) as [Hkn|Hkn]; [exact (IH k Hkn W v Hv)|].
    assert (k = S n) by lia. subst k.
    apply (recursive_element_unfold F t C _ W v HC).
    eapply (folded_result_reanchor F s t (B (recursive_element F s B)) (C (recursive_element F t C)));
      [exact Hst| |].
    + intros l. exact (Hnext n IH n (Nat.le_refl n) (fst W) (VLoc l)).
    + now apply (recursive_element_unfold F s B _ W v HB).
Qed.

Local Lemma extend_preserves_constraints F η Δ bs ts :
  length bs = length ts -> binders_set bs ## fv_constraints Δ ->
  clock_constraints F η Δ ->
  clock_constraints F (clock_extend η (bmap bs ts)) Δ.
Proof.
  intros Hlen Hfresh HΔ.
  apply (clock_constraints_ext F η _ Δ); [|exact HΔ].
  intros x y Hxy. destruct (constraint_endpoints Δ x y Hxy) as [Hx Hy].
  split; symmetry; apply variable_replacement_arrow_clock_fresh; [exact Hlen|set_solver|exact Hlen|set_solver].
Qed.

Local Lemma subtime_scope_result F η Δ from to current u :
  clock_constraints F η Δ -> reachable F (η current) u ->
  (from ≠ to -> reachable Δ to current) -> reachable F (η from) u -> reachable F (η to) u.
Proof.
  intros HΔ Hcurrent Hif Hfrom. destruct (decide (from = to)) as [->|Hne]; [exact Hfrom|].
  unfold reachable in *. etransitivity; [|exact Hcurrent].
  apply (clock_reachable F η Δ to current HΔ), Hif, Hne.
Qed.

Local Lemma subtime_arguments_length Δ d rs qs : subtime_forall2 Δ d rs qs -> length rs = length qs.
Proof. induction 1; simpl; congruence. Qed.

Combined Scheme subtime_mutual_ind from subtime_typ_rec, subtime_typat_rec, subtime_forall2_rec.

Local Lemma interpretation_subtime F : forall Δ,
  (forall d ρ τ, subtime_typ Δ d ρ τ ->
    forall n η X t, admissible_assignment F X -> clock_constraints F η Δ ->
      reachable F (η d) t ->
      element_inclusion n (usable_at (interpret_type F ρ η X []) t)
                          (usable_at (interpret_type F τ η X []) t)) /\
  (forall d σ σ', subtime_typat Δ d σ σ' ->
    forall n η X s, admissible_assignment F X -> clock_constraints F η Δ ->
      reachable F s (η d) ->
      element_inclusion n (interpret_at F σ η X s) (interpret_at F σ' η X (η d))) /\
  (forall d rs qs, subtime_forall2 Δ d rs qs ->
    forall n η X t, admissible_assignment F X -> clock_constraints F η Δ ->
      reachable F (η d) t ->
      Forall2 (element_inclusion n)
        ((fun r => usable_at (interpret_type F r η X []) t) <$> rs)
        ((fun r => usable_at (interpret_type F r η X []) t) <$> qs)).
Proof.
  apply subtime_mutual_ind.
  - intros. apply element_inclusion_refl.
  - intros Δ current σ σ' d d' Hreach Hscope Hsub IH n η X u HX HΔ Hcurrent k Hk W v [Ha Hv].
    split.
    + eapply (subtime_scope_result F η Δ d d' current u); eassumption.
    + eapply (IH n η X (η d)); [exact HX|exact HΔ|now apply (clock_reachable F η Δ)|exact Hk|exact Hv].
  - intros Δ d b k ρ τ Hsub IH n η X t HX HΔ Htime i Hi W v Hv.
    cbn [interpret_type] in Hv |- *. apply usable_universal. intros A HA.
    pose proof (proj1 (usable_universal F _ t i W v) Hv A HA) as Hval.
    eapply (IH n η (type_assume X b A)); [now apply admissible_type_assume|exact HΔ|exact Htime|exact Hi|exact Hval].
  - intros Δ current x σ d σ' d' Hreach Hvalid Hscope Hsub IH n η X u HX HΔ Hcurrent k Hk W v [Ha Hv].
    split; [eapply (subtime_scope_result F η Δ d d' current u); eassumption|].
    assert (Hdd : reachable F (η d) (η d')) by now apply (clock_reachable F η Δ).
    set (B := fun P => interpret_at F σ η (type_assume X (BNamed x) (fun _ => anchored F (η d) P)) (η d)).
    set (C := fun P => interpret_at F σ' η (type_assume X (BNamed x) (fun _ => anchored F (η d') P)) (η d')).
    change (recursive_element F (η d') C k W v). change (recursive_element F (η d) B k W v) in Hv.
    eapply (recursive_elements_subsume F (η d) (η d') B C); [exact Hdd| | | |exact Hk|exact Hv].
    + unfold B. now apply interpretation_recursive_operator.
    + unfold C. now apply interpretation_recursive_operator.
    + intros j Hrecursive.
      assert (HX1 : admissible_assignment F
          (type_assume X (BNamed x) (fun _ => anchored F (η d) (recursive_element F (η d) B)))).
      { apply admissible_type_assume; [exact HX|]. apply constant_family_shape.
        exact (interpret_type_shape F (TRec x σ d) η X [] HX). }
      assert (HX2 : admissible_assignment F
          (type_assume X (BNamed x) (fun _ => anchored F (η d') (recursive_element F (η d') C)))).
      { apply admissible_type_assume; [exact HX|]. apply constant_family_shape.
        exact (interpret_type_shape F (TRec x σ' d') η X [] HX). }
      unfold B at 1. unfold C at 1. eapply element_inclusion_trans.
      * apply (IH j η); eassumption.
      * eapply (proj2 (validity_interpretation F) Δ x d' σ' d');
          [exact Hvalid|exact HΔ|exact HX1|exact HX2|].
        now apply assumed_anchor_covariant.
  - intros. now apply interpret_atom_reanchor.
  - intros Δ d ρ1 ρ2 τ1 τ2 H1 IH1 H2 IH2 n η X s HX HΔ Hreach.
    cbn [interpret_at]. apply product_result_subsumes; [exact Hreach| |].
    + eapply element_inclusion_trans; [|apply (IH1 n η X); [exact HX|exact HΔ|apply rtc_refl]].
      eapply usable_reanchor; [now apply interpret_type_shape|exact Hreach].
    + eapply element_inclusion_trans; [|apply (IH2 n η X); [exact HX|exact HΔ|apply rtc_refl]].
      eapply usable_reanchor; [now apply interpret_type_shape|exact Hreach].
  - intros Δ d ρ1 ρ2 τ1 τ2 H1 IH1 H2 IH2 n η X s HX HΔ Hreach.
    cbn [interpret_at]. apply sum_result_subsumes; [exact Hreach| |].
    + eapply element_inclusion_trans; [|apply (IH1 n η X); [exact HX|exact HΔ|apply rtc_refl]].
      eapply usable_reanchor; [now apply interpret_type_shape|exact Hreach].
    + eapply element_inclusion_trans; [|apply (IH2 n η X); [exact HX|exact HΔ|apply rtc_refl]].
      eapply usable_reanchor; [now apply interpret_type_shape|exact Hreach].
  - intros Δ r bs Δ1 Δ2 d rs qs ρ τ Hfresh Hpre Hargs IHargs Hret IHret n η X s HX HΔ Hreach.
    cbn [interpret_at]. apply function_result_subsumes; [exact Hreach|].
    split; [reflexivity|]. split.
    { intros ts. cbn [call_parameters]. rewrite !length_fmap. symmetry.
      exact (subtime_arguments_length _ _ _ _ Hargs). }
    intros ts Hlen Hc.
    set (θ := clock_extend η (bmap bs ts)).
    assert (Hbase : clock_constraints F θ Δ).
    { apply extend_preserves_constraints; [symmetry; exact Hlen|exact Hfresh|exact HΔ]. }
    assert (Hnew : clock_constraints F θ (Δ ∪ Δ2)).
    { apply clock_constraints_union. split; [exact Hbase|exact Hc]. }
    cbn [call_constraints call_time call_parameters call_result]. fold θ.
    split.
    + exact (clock_all_reachable F θ (Δ ∪ Δ2) Δ1 Hnew Hpre).
    + split; [apply clock_equivalent_refl|]. split.
      * apply (IHargs n θ X); [exact HX|exact Hnew|apply rtc_refl].
      * apply (IHret n θ X); [exact HX|exact Hnew|apply rtc_refl].
  - intros. constructor.
  - intros Δ d ρ τ rs qs H1 IH1 H2 IH2 n η X t HX HΔ Htime.
    rewrite !fmap_cons. apply Forall2_cons. split; [now apply IH1|now apply IH2].
Qed.

Local Lemma model_subtime δ Δ Γ e ρ τ :
  subtime_typ Δ δ ρ τ -> expression_typing_model δ Δ Γ e ρ -> expression_typing_model δ Δ Γ e τ.
Proof.
  intros Hsub Hmodel F η X n W E HX HΔ Henv.
  eapply expression_spec_post_inclusion; [|exact (Hmodel F η X n W E HX HΔ Henv)].
  exact (proj1 (interpretation_subtime F Δ) _ _ _ Hsub n η X (η δ) HX HΔ (rtc_refl _ (η δ))).
Qed.

Local Lemma typed_value_env_translate F n (W : resource n) t η θ X Y Γ Γ' E :
  (forall x ρ', Γ' !! x = Some ρ' -> exists ρ, Γ !! x = Some ρ /\
    type_prefix n (interpret_type F ρ η X []) (interpret_type F ρ' θ Y [])) ->
  typed_value_env F n W t η X Γ E -> typed_value_env F n W t θ Y Γ' E.
Proof.
  intros Htypes [Henv Hview]. split; [|exact Hview].
  intros x ρ' Hlook. destruct (Htypes x ρ' Hlook) as (ρ & Hlookup & HE).
  destruct (Henv x ρ Hlookup) as (v & Hv & Htype). exists v. split; [exact Hv|].
  apply (usable_prefix_same n _ _ t HE n (Nat.le_refl n) W v), Htype.
Qed.

Local Lemma typed_value_env_later F n (W : resource n) t u η X Γ E :
  admissible_assignment F X -> reachable F t u ->
  typed_value_env F n W t η X Γ E -> typed_value_env F n W u η X Γ E.
Proof.
  intros HX Htu [Henv Hview]. split.
  - intros x ρ Hlook. destruct (Henv x ρ Hlook) as (v & Hv & Htype).
    exists v. split; [exact Hv|].
    eapply (usable_reanchor F n); [now apply interpret_type_shape|exact Htu|lia|exact Htype].
  - intros x v Hlookup. eapply view_visible_later; [exact Htu|now apply (Hview x)].
Qed.

Local Lemma judgment_clock_restore η d d' z :
  z ≠ d' ->
  clock_bind η (BNamed d') (η d) (find_opt {[d:=d']} z) = η z.
Proof.
  intros Hne. rewrite find_opt_named. destruct (decide (d = z)) as [Heq|Hout].
  - subst z. try rewrite decide_True by reflexivity.
    now rewrite clock_bind_named, decide_True by reflexivity.
  - try rewrite decide_False by congruence.
    now rewrite clock_bind_named, decide_False by congruence.
Qed.

Local Lemma judgment_clock_type F n η X d d' ρ :
  regular_at F n X -> d' ∉ fv_typ ρ -> d' ∉ bv_typ ρ ->
  type_prefix n (interpret_type F ρ η X [])
    (interpret_type F (tsubst_typ {[d:=d']} ρ) (clock_bind η (BNamed d') (η d)) X []).
Proof.
  intros HX Hfree Hbound.
  eapply type_prefix_trans with
    (B:=interpret_type F ρ (fun z => clock_bind η (BNamed d') (η d) (find_opt {[d:=d']} z)) X []).
  - apply (interpret_comparable_type F ρ);
      [exact (proj1 HX)|exact (proj1 HX)| |intros z _; apply (proj2 HX z)|constructor].
    intros z Hz. assert (Hne : z ≠ d') by (intros ->; contradiction).
    exact (eq_ind_r (fun w => clock_equivalent F (η z) w) (clock_equivalent_refl F (η z))
      (judgment_clock_restore η d d' z Hne)).
  - apply type_prefix_sym, interpret_type_substitution; [exact HX|].
    intros x y Hxy. apply lookup_singleton_Some in Hxy as [_ ->]. exact Hbound.
Qed.

Local Lemma model_clock_judgment δ' δ Δ Γ e ρ :
  δ' ∉ ({[δ]} ∪ fv_constraints Δ ∪ fv_env Γ ∪ fv_typ ρ) ->
  δ' ∉ (bv_env Γ ∪ bv_typ ρ) ->
  expression_typing_model δ' (tsubst_constraints {[δ:=δ']} Δ)
    (tsubst_typ {[δ:=δ']} <$> Γ) e (tsubst_typ {[δ:=δ']} ρ) ->
  expression_typing_model δ Δ Γ e ρ.
Proof.
  intros Hfree Hbound Hmodel F η X n W E HX HΔ Henv.
  set (θ := clock_bind η (BNamed δ') (η δ)).
  assert (Htime : θ δ' = η δ).
  { unfold θ. now rewrite clock_bind_named, decide_True by reflexivity. }
  assert (HΔ' : clock_constraints F θ (tsubst_constraints {[δ:=δ']} Δ)).
  { apply clock_constraints_substitute. apply (clock_constraints_ext F η _ Δ); [|exact HΔ].
    intros x y Hxy. destruct (constraint_endpoints Δ x y Hxy) as [Hx Hy].
    split; symmetry; [apply (judgment_clock_restore η δ δ' x)|apply (judgment_clock_restore η δ δ' y)];
      set_solver. }
  assert (Henv' : typed_value_env F n W (θ δ') θ X (tsubst_typ {[δ:=δ']} <$> Γ) E).
  { rewrite Htime. eapply typed_value_env_translate; [|exact Henv].
    intros x ρ' Hlook. rewrite lookup_fmap in Hlook.
    destruct (Γ !! x) as [τ|] eqn:Hτ; simpl in Hlook; [|discriminate].
    injection Hlook as <-. exists τ. split; [reflexivity|].
    apply judgment_clock_type; [now apply admissible_regular| |].
    - intros Hbad. pose proof (type_env_mentions fv_typ Γ x τ Hτ δ' Hbad) as Hmention.
      change (δ' ∈ fv_env Γ) in Hmention. set_solver.
    - intros Hbad. pose proof (type_env_mentions bv_typ Γ x τ Hτ δ' Hbad) as Hmention.
      change (δ' ∈ bv_env Γ) in Hmention. set_solver. }
  pose proof (Hmodel F θ X n W E HX HΔ' Henv') as Htyped.
  rewrite Htime in Htyped. eapply expression_spec_post_prefix; [|exact Htyped].
  apply usable_prefix_same, type_prefix_sym, judgment_clock_type; [now apply admissible_regular|set_solver|set_solver].
Qed.

Local Definition world_assertion := forall n, resource n -> Prop.

Local Definition assertion_stable (P : world_assertion) :=
  (forall n (W : resource (S n)), P (S n) W -> P n (fst W)) /\
  (forall n (W U : resource n), resource_extends n W U -> P n W -> P n U).

Local Lemma assertion_stable_and (P Q : world_assertion) :
  assertion_stable P -> assertion_stable Q ->
  assertion_stable (fun n W => P n W /\ Q n W).
Proof.
  intros [HP1 HP2] [HQ1 HQ2]. split.
  - intros n W [HP HQ]. split; [now apply HP1|now apply HQ1].
  - intros n W U Hext [HP HQ]. split; [eapply HP2|eapply HQ2]; eassumption.
Qed.

Local Lemma env_assertion_stable F t η X Γ E :
  admissible_assignment F X -> assertion_stable (fun n W => typed_value_env F n W t η X Γ E).
Proof. intros HX. split; [intros; now apply typed_value_env_down|intros; eapply typed_value_env_mono; eassumption]. Qed.

Local Lemma usable_assertion_stable F A t v :
  type_shape F A -> assertion_stable (fun n W => usable_at A t n W v).
Proof.
  intros HA. split.
  - intros n W Hv. exact (shape_usable_downward F A t HA n W v Hv).
  - intros n W U Hext Hv. exact (shape_usable_monotone F A t HA n W U v Hext Hv).
Qed.

Local Lemma continuation_from_assertion n F (W : resource n) t K P Q (Inv : world_assertion) :
  assertion_stable Inv -> Inv n W ->
  (forall k (U : resource k) (v : val), Inv k U -> P k U v ->
     expression_spec k F U (Leaf t) (fill_item K v) Q) ->
  continuation_spec n F W t K P Q.
Proof.
  induction n as [|n IH]; intros Hstable HInv Hbody; [exact I|].
  destruct Hstable as [Hdown Hext]. split.
  - apply IH; [now split|now apply Hdown|exact Hbody].
  - intros U v Hgrow HP. apply Hbody; [eapply Hext; eassumption|exact HP].
Qed.

Local Lemma expression_spec_evaluate n F (W : resource n) t K e P Q Inv :
  assertion_stable Inv -> Inv n W -> context_support F (resource_view n W) t K ->
  expression_spec n F W (Leaf t) e P ->
  (forall k (U : resource k) (v : val), Inv k U -> P k U v ->
     expression_spec k F U (Leaf t) (fill_item K v) Q) ->
  expression_spec n F W (Leaf t) (fill_item K e) Q.
Proof.
  intros Hstable HInv Hscope He Hbody.
  eapply expression_spec_bind; [exact I|exact Hscope|exact He|].
  exact (continuation_from_assertion n F W t K P Q Inv Hstable HInv Hbody).
Qed.

Local Definition readable_in_view F (V : heap_view) t (L : gset loc) :=
  forall l, l ∈ L -> exists o d, V !! l = Some (o,d) /\ reachable F o t.

Local Lemma readable_none F V t : readable_in_view F V t ∅.
Proof. intros l H. set_solver. Qed.

Local Lemma readable_union F V t L R :
  readable_in_view F V t L -> readable_in_view F V t R -> readable_in_view F V t (L ∪ R).
Proof. intros HL HR l H. apply elem_of_union in H as [H|H]; auto. Qed.

Local Lemma readable_closed_code F n (W : resource n) t η X Γ E e :
  typed_value_env F n W t η X Γ E -> locs e = ∅ ->
  readable_in_view F (resource_view n W) t (locs (close_expr E e)).
Proof. intros [_ Hview] Hloc l Hl. exact (closed_code_visible F (resource_view n W) t E e Hloc Hview l Hl). Qed.

Local Lemma readable_typed_value F n (W : resource n) t η X ρ v :
  admissible_assignment F X -> usable_at (interpret_type F ρ η X []) t n W v ->
  readable_in_view F (resource_view n W) t (locs v).
Proof.
  intros HX [Hscope Hvalue]. exact (proj2 (proj2 (proj2 (interpret_type_shape F ρ η X [] HX))) n W t v Hscope Hvalue).
Qed.

Local Lemma readable_access F n (W : resource n) t σ α L :
  store_spec_at n W σ α -> readable_in_view F (resource_view n W) t L ->
  all_abef F α t L.
Proof.
  intros Hstore Hread l Hl. destruct (Hread l Hl) as (o & d & Hloc & Hreach).
  destruct (proj2 (store_spec_view _ _ _ _ Hstore) l o d Hloc) as [Hα _].
  unfold abef. now rewrite Hα.
Qed.

Local Lemma expression_spec_readonly n F (W : resource n) t e (Q : element_spec) (Inv : world_assertion) :
  assertion_stable Inv -> Inv n W ->
  (forall k (U : resource k), Inv k U -> readable_in_view F (resource_view k U) t (locs e)) ->
  (forall k (U : resource k) σ α, Inv k U -> store_spec_at k U σ α -> head_ready σ e) ->
  (forall k (U : resource (S k)) G σ α σ' α' e', Inv (S k) U -> store_spec_at (S k) U σ α ->
     head_step G t σ α e σ' α' e' ->
     σ' = σ /\ α' = α /\ expression_spec k F (fst U) (Leaf t) e' Q) ->
  expression_spec n F W (Leaf t) e Q.
Proof.
  intros [Hdown Hmono]. induction n as [|n IH]; intros HInv Hread Hready Hstep; [exact I|].
  apply expression_spec_atomic.
  - apply IH; [now apply Hdown|exact Hread|exact Hready|exact Hstep].
  - intros V σ α G Hext Hstore HG. pose proof (Hmono _ _ _ Hext HInv) as HV.
    split; [exact (Hready _ _ _ _ HV Hstore)|]. split.
    + eapply readable_access; [exact Hstore|now apply Hread].
    + intros σ' α' e' Hhead.
      destruct (Hstep _ _ _ _ _ _ _ _ HV Hstore Hhead) as [-> [-> Hew]].
      exists (fst V). split; [apply resource_extends_refl|]. split; [exact (proj1 Hstore)|exact Hew].
Qed.

Local Lemma model_unary δ Δ Γ e ρ τ (op : expr -> expr) K :
  (forall E e, close_expr E (op e) = op (close_expr E e)) ->
  (forall e, op e = fill_item K e) ->
  locs K = ∅ ->
  expression_typing_model δ Δ Γ e ρ ->
  (forall F η X n (W : resource n) (v : val),
    admissible_assignment F X -> usable_at (interpret_type F ρ η X []) (η δ) n W v ->
    expression_spec n F W (Leaf (η δ)) (op v) (usable_at (interpret_type F τ η X []) (η δ))) ->
  expression_typing_model δ Δ Γ (op e) τ.
Proof.
  intros Hclose Hop Hloc He Hopv F η X n W E HX HΔ Henv.
  rewrite Hclose, Hop.
  eapply (expression_spec_evaluate n F W (η δ) K _ _ _
    (fun k U => typed_value_env F k U (η δ) η X Γ E)).
  - now apply env_assertion_stable.
  - exact Henv.
  - unfold context_support. rewrite Hloc. apply readable_none.
  - now apply He.
  - intros k U v _ Hv. rewrite <-Hop. eapply Hopv; eassumption.
Qed.

Local Lemma model_binary δ Δ Γ e1 e2 ρ1 ρ2 τ
    (op : expr -> expr -> expr) (K1 : expr -> ctx) (K2 : val -> ctx) :
  (forall E e f, close_expr E (op e f) = op (close_expr E e) (close_expr E f)) ->
  (forall e f, op e f = fill_item (K1 f) e) ->
  (forall (v : val) f, op v f = fill_item (K2 v) f) ->
  (forall f, locs (K1 f) = locs f) ->
  (forall v, locs (K2 v) = locs v) ->
  locs e2 = ∅ ->
  expression_typing_model δ Δ Γ e1 ρ1 ->
  expression_typing_model δ Δ Γ e2 ρ2 ->
  (forall F η X n (W : resource n) (v w : val),
    admissible_assignment F X ->
    usable_at (interpret_type F ρ1 η X []) (η δ) n W v ->
    usable_at (interpret_type F ρ2 η X []) (η δ) n W w ->
    expression_spec n F W (Leaf (η δ)) (op v w) (usable_at (interpret_type F τ η X []) (η δ))) ->
  expression_typing_model δ Δ Γ (op e1 e2) τ.
Proof.
  intros Hclose HK1 HK2 HL1 HL2 Hloc H1 H2 Hop F η X n W E HX HΔ Henv.
  set (t := η δ).
  set (A := interpret_type F ρ1 η X []).
  set (Inv := fun k U => typed_value_env F k U t η X Γ E).
  assert (HI : assertion_stable Inv) by (unfold Inv; now apply env_assertion_stable).
  rewrite Hclose, HK1.
  eapply (expression_spec_evaluate n F W t (K1 (close_expr E e2)) _ (usable_at A t) _ Inv).
  - exact HI.
  - exact Henv.
  - unfold context_support. rewrite HL1. eapply readable_closed_code; eassumption.
  - now apply H1.
  - intros k U v HU Hv. rewrite <-HK1, HK2.
    eapply (expression_spec_evaluate k F U t (K2 v) _ _ _
      (fun i V => Inv i V /\ usable_at A t i V v)).
    + apply assertion_stable_and; [exact HI|]. apply (usable_assertion_stable F).
      unfold A. now apply interpret_type_shape.
    + now split.
    + unfold context_support. rewrite HL2. exact (readable_typed_value F k U t η X ρ1 v HX Hv).
    + now apply H2.
    + intros i V w [_ Hv'] Hw. rewrite <-HK2. eapply Hop; eassumption.
Qed.

Local Lemma interpret_array_forms F δ d η X ρ n (W : resource n) v :
  admissible_assignment F X ->
  usable_at (interpret_type F (TTypat (TArray ρ) d) η X []) (η δ) n W v ->
  exists l o size, v = VLoc l /\ resource_view n W !! l = Some (o,inl size) /\
    reachable F o (η δ) /\ fst (interpret_type F ρ η X []) (η δ) /\
    array_spec_at n W l (snd (interpret_type F ρ η X [])).
Proof.
  intros HX [Hs (l & o & info & -> & Hl & Ho & o' & size & -> & Hl' & HA & Harray)].
  rewrite Hl in Hl'. injection Hl' as <-.
  assert (Hr : reachable F o (η δ)) by (unfold reachable in *; etransitivity; eassumption).
  exists l, o, size. repeat split; try assumption.
  eapply (proj1 (interpret_type_shape F ρ η X [] HX)); eassumption.
Qed.

Local Lemma model_alloc δ Δ Γ e1 e2 ρ :
  locs e2 = ∅ ->
  expression_typing_model δ Δ Γ e1 TBInt ->
  expression_typing_model δ Δ Γ e2 ρ ->
  expression_typing_model δ Δ Γ (Alloc e1 e2) (TTypat (TArray ρ) δ).
Proof.
  intros Hloc H1 H2.
  eapply (model_binary δ Δ Γ e1 e2 _ _ _ Alloc CtxAlloc1 CtxAlloc2);
    try reflexivity; try eassumption.
  intros F η X n W v w HX [_ Hv] [Ht Hw]. destruct v; cbn in Hv; try contradiction; try discriminate.
  pose proof (interpret_type_shape F ρ η X [] HX) as (_ & Hmono & Hdown & Hvisible).
  eapply expression_spec_post_inclusion.
  - intros k Hk U u Hu. split; [apply rtc_refl|exact Hu].
  - apply expression_spec_alloc; [exact Ht|exact Hmono|exact Hdown| |].
    + intros V Hext. eapply Hmono; eassumption.
    + intros k V u Hu. now apply Hvisible.
Qed.

Local Lemma model_load δ Δ Γ e1 e2 ρ d :
  locs e2 = ∅ ->
  expression_typing_model δ Δ Γ e1 (TTypat (TArray ρ) d) ->
  expression_typing_model δ Δ Γ e2 TBInt ->
  expression_typing_model δ Δ Γ (Load e1 e2) ρ.
Proof.
  intros Hloc H1 H2.
  eapply (model_binary δ Δ Γ e1 e2 _ _ _ Load CtxLoad1 CtxLoad2);
    try reflexivity; try eassumption.
  intros F η X n W v w HX Hv [_ Hw]. destruct w; cbn in Hw; try contradiction; try discriminate.
  destruct (interpret_array_forms F δ d η X ρ n W v HX Hv) as (l & o & size & -> & Hl & Ho & Ht & Harr).
  pose proof (interpret_type_shape F ρ η X [] HX) as (_ & Hmono & Hdown & Hvisible).
  eapply expression_spec_post_inclusion with (P := snd (interpret_type F ρ η X [])).
  - intros k Hk U u Hu. now split.
  - eapply expression_spec_load; [exact Hl|exact Ho|exact Harr|exact Hmono|exact Hdown|].
    intros k V u Hu. now apply Hvisible.
Qed.

Local Lemma model_length δ Δ Γ e ρ d :
  expression_typing_model δ Δ Γ e (TTypat (TArray ρ) d) ->
  expression_typing_model δ Δ Γ (Length e) TBInt.
Proof.
  intros He. eapply (model_unary δ Δ Γ e _ _ Length CtxLength); try reflexivity; [exact He|].
  intros F η X n W v HX Hv.
  set (A := interpret_type F (TTypat (TArray ρ) d) η X []).
  set (t := η δ).
  unshelve eapply (expression_spec_readonly n F W t (Length v) _
    (fun k U => usable_at A t k U v)).
  - apply (usable_assertion_stable F). unfold A. now apply interpret_type_shape.
  - exact Hv.
  - intros k U Htyped. exact (readable_typed_value F k U t η X (TTypat (TArray ρ) d) v HX Htyped).
  - intros k U σ α Htyped Hstore.
    destruct (interpret_array_forms F δ d η X ρ k U v HX Htyped) as (l & o & size & -> & Hl & _).
    destruct (proj2 (store_spec_view _ _ _ _ Hstore) l o _ Hl) as [_ (s & Hσ & Hs)].
    destruct s; try discriminate Hs. eapply ReadyLength; eassumption.
  - intros k U G σ α σ' α' e' _ _ Hstep. inversion Hstep; subst;
      try match goal with H : (if ?b then _ else _) = _ |- _ => destruct b; discriminate H end.
    split; [reflexivity|]. split; [reflexivity|].
    apply (interp_value_spec F TBInt η X t k (fst U)); [exact HX|]. split; [exact I|reflexivity].
Qed.

Local Lemma model_if δ Δ Γ e1 e2 e3 ρ :
  locs e2 = ∅ -> locs e3 = ∅ ->
  expression_typing_model δ Δ Γ e1 TBBool ->
  expression_typing_model δ Δ Γ e2 ρ ->
  expression_typing_model δ Δ Γ e3 ρ ->
  expression_typing_model δ Δ Γ (If e1 e2 e3) ρ.
Proof.
  intros Hl2 Hl3 H1 H2 H3 F η X n W E HX HΔ Henv.
  set (t := η δ).
  set (Inv := fun k U => typed_value_env F k U t η X Γ E).
  assert (HI : assertion_stable Inv) by (unfold Inv; now apply env_assertion_stable).
  set (Q := usable_at (interpret_type F ρ η X []) t).
  change (expression_spec n F W (Leaf t)
    (fill_item (CtxIf (close_expr E e2) (close_expr E e3)) (close_expr E e1)) Q).
  eapply (expression_spec_evaluate n F W t _ _ _ _ Inv).
  - exact HI.
  - exact Henv.
  - change (readable_in_view F (resource_view n W) t (locs (close_expr E e2) ∪ locs (close_expr E e3))).
    apply readable_union; eapply readable_closed_code; eassumption.
  - now apply H1.
  - intros k U v HU [_ Hv]. destruct v; cbn in Hv; try contradiction; try discriminate.
    cbn [fill_item]. eapply (expression_spec_readonly k F U t _ Q Inv).
    + exact HI.
    + exact HU.
    + intros i V HV. change (readable_in_view F (resource_view i V) t
        (∅ ∪ locs (close_expr E e2) ∪ locs (close_expr E e3))).
      repeat apply readable_union; [apply readable_none| |]; eapply readable_closed_code; eassumption.
    + intros. apply ReadyIf.
    + intros i V G σ α σ' α' e' HV Hstore Hhead. inversion Hhead; subst;
      try match goal with H : (if ?b then _ else _) = _ |- _ => destruct b; discriminate H end.
      split; [reflexivity|]. split; [reflexivity|].
      destruct b; [apply H2|apply H3]; try assumption; exact (proj1 HI i V HV).
Qed.

Local Lemma primitive_typed_value p ρ1 ρ2 ρ :
  prim_typed p ρ1 ρ2 ρ ->
  forall F η X t n (W : resource n) v w,
    usable_at (interpret_type F ρ1 η X []) t n W v ->
    usable_at (interpret_type F ρ2 η X []) t n W w ->
    exists u, eval_call_prim p v w = Some u /\
      (forall σ, head_ready σ (CallPrim p v w)) /\
      forall k (U : resource k), usable_at (interpret_type F ρ η X []) t k U u.
Proof.
  destruct p; simpl; intros (-> & H) F η X t n W v w Hv Hw.
  all: try solve [subst ρ; exists (VBool (bool_decide (v=w))); split; [reflexivity|];
    split; [intros; apply ReadyEq|intros; now split]].
  all: destruct H as [-> ->]; destruct Hv as [_ Hv], Hw as [_ Hw];
    destruct v, w; cbn in Hv, Hw; try contradiction; try discriminate.
  all: eexists; split; [reflexivity|]; split; [intros; constructor|intros; now split].
Qed.

Local Lemma model_primitive δ Δ Γ e1 e2 ρ1 ρ2 ρ p :
  prim_typed p ρ1 ρ2 ρ -> locs e2 = ∅ ->
  expression_typing_model δ Δ Γ e1 ρ1 ->
  expression_typing_model δ Δ Γ e2 ρ2 ->
  expression_typing_model δ Δ Γ (CallPrim p e1 e2) ρ.
Proof.
  intros Hp Hloc H1 H2.
  eapply (model_binary δ Δ Γ e1 e2 _ _ _ (CallPrim p) (CtxCallPrim1 p) (CtxCallPrim2 p));
    try reflexivity; try eassumption.
  intros F η X n W v w HX Hv Hw.
  set (A := interpret_type F ρ1 η X []).
  set (B := interpret_type F ρ2 η X []).
  set (t := η δ).
  destruct (primitive_typed_value p ρ1 ρ2 ρ Hp F η X t n W v w Hv Hw) as (u & Hu & Hr & Htype).
  eapply (expression_spec_readonly n F W t _ _
    (fun k U => usable_at A t k U v /\ usable_at B t k U w)).
  - apply assertion_stable_and; apply (usable_assertion_stable F); now apply interpret_type_shape.
  - now split.
  - intros k U [HV HW]. change (readable_in_view F (resource_view k U) t (locs v ∪ locs w)).
    apply readable_union; eapply readable_typed_value; eassumption.
  - intros; apply Hr.
  - intros k U G σ α σ' α' e' _ _ Hhead. inversion Hhead; subst;
      try match goal with H : (if ?b then _ else _) = _ |- _ => destruct b; discriminate H end.
    match goal with H : eval_call_prim _ _ _ = Some _ |- _ => rewrite Hu in H; injection H as <- end.
    split; [reflexivity|]. split; [reflexivity|].
    apply (interp_value_spec F ρ η X t k (fst U)); [exact HX|apply Htype].
Qed.

Local Lemma expression_spec_allocate_cell n F (W : resource n) t e Q s (Inv : world_assertion) :
  assertion_stable Inv -> Inv n W ->
  (forall k (U : resource k), Inv k U -> readable_in_view F (resource_view k U) t (locs e)) ->
  (forall σ, head_ready σ e) ->
  (forall G σ α σ' α' e', head_step G t σ α e σ' α' e' ->
    exists l, σ !! l = None /\ σ' = <[l:=s]>σ /\ α' = <[l:=t]>α /\ e' = Val (VLoc l)) ->
  (forall vs, s ≠ SBlock vs) ->
  (forall k (U : resource k) l, Inv k U ->
    resource_extends k U (resource_insert k l t s empty_element U) ->
    expression_spec k F (resource_insert k l t s empty_element U) (Leaf t) (VLoc l) Q) ->
  expression_spec n F W (Leaf t) e Q.
Proof.
  intros [Hdown Hmono]. induction n as [|n IH]; intros HInv Hread Hready Hstep Hcell Hresult; [exact I|].
  apply expression_spec_atomic.
  - apply IH; [now apply Hdown|exact Hread|exact Hready|exact Hstep|exact Hcell|exact Hresult].
  - intros V σ α G Hext Hstore HG. pose proof (Hmono _ _ _ Hext HInv) as HV.
    split; [apply Hready|]. split.
    + eapply readable_access; [exact Hstore|now apply Hread].
    + intros σ' α' e' Hhead. destruct (Hstep _ _ _ _ _ _ Hhead) as (l & Hl & -> & -> & ->).
      assert (Hgrow : resource_extends n (fst V) (resource_insert n l t s empty_element (fst V)))
        by (apply resource_insert_grows with (σ := σ) (α := α); [exact (proj1 Hstore)|exact Hl]).
      eexists. split; [exact Hgrow|]. split.
      * apply resource_insert_store; [exact (proj1 Hstore)|exact Hl| |].
        -- intros k A B v _ Hbad. destruct Hbad.
        -- intros vs Hbad. exact (False_rect _ (Hcell vs Hbad)).
      * apply Hresult; [now apply Hdown|exact Hgrow].
Qed.

Local Lemma inserted_cell_has_type n (W : resource n) F t l s (P : forall k, resource k -> loc -> nat + storable -> Prop) :
  P n (resource_insert n l t s empty_element W) l (cell_view s) ->
  usable_at (anchored F t (location_spec F t P)) t n (resource_insert n l t s empty_element W) (VLoc l).
Proof.
  intros H. split; [apply rtc_refl|]. exists l, t, (cell_view s).
  split; [reflexivity|]. split; [rewrite resource_insert_view; apply lookup_insert_eq|].
  split; [apply rtc_refl|exact H].
Qed.

Local Lemma model_pair δ Δ Γ e1 e2 ρ1 ρ2 :
  locs e2 = ∅ ->
  expression_typing_model δ Δ Γ e1 ρ1 ->
  expression_typing_model δ Δ Γ e2 ρ2 ->
  expression_typing_model δ Δ Γ (Prod e1 e2) (TTypat (TProd ρ1 ρ2) δ).
Proof.
  intros Hloc H1 H2.
  eapply (model_binary δ Δ Γ e1 e2 _ _ _ Prod CtxPair1 CtxPair2);
    try reflexivity; try eassumption.
  intros F η X n W v w HX Hv Hw.
  set (t := η δ).
  set (A := interpret_type F ρ1 η X []).
  set (B := interpret_type F ρ2 η X []).
  set (Inv := fun k U => usable_at A t k U v /\ usable_at B t k U w).
  assert (HA : type_shape F A) by (unfold A; now apply interpret_type_shape).
  assert (HB : type_shape F B) by (unfold B; now apply interpret_type_shape).
  eapply (expression_spec_allocate_cell n F W t _ _ (SProd v w) Inv).
  - apply assertion_stable_and; now apply (usable_assertion_stable F).
  - now split.
  - intros k U [HV HW]. change (readable_in_view F (resource_view k U) t (locs v ∪ locs w)).
    apply readable_union; eapply readable_typed_value; eassumption.
  - intros. apply ReadyProd.
  - intros G σ α σ' α' e' Hstep. inversion Hstep; subst;
      try match goal with H : (if ?b then _ else _) = _ |- _ => destruct b; discriminate H end.
    eexists. split; [apply not_elem_of_dom; eassumption|]. repeat split; reflexivity.
  - discriminate.
  - intros k U l [HV HW] Hgrow.
    apply (interp_value_spec F (TTypat (TProd ρ1 ρ2) δ) η X t k); [exact HX|].
    apply inserted_cell_has_type. exists v, w. split; [reflexivity|]. split.
    + eapply (shape_usable_monotone F A t HA); eassumption.
    + eapply (shape_usable_monotone F B t HB); eassumption.
Qed.

Local Lemma model_projection δ Δ Γ e ρ1 ρ2 d (b : bool) :
  expression_typing_model δ Δ Γ e (TTypat (TProd ρ1 ρ2) d) ->
  expression_typing_model δ Δ Γ ((if b then Fst else Snd) e) (if b then ρ1 else ρ2).
Proof.
  intros He.
  eapply (model_unary δ Δ Γ e _ _ (if b then Fst else Snd) (if b then CtxFst else CtxSnd));
    try (destruct b; reflexivity); [exact He|].
  intros F η X n W v HX Hv.
  set (A := interpret_type F (TTypat (TProd ρ1 ρ2) d) η X []).
  set (t := η δ).
  eapply (expression_spec_readonly n F W t _ _ (fun k U => usable_at A t k U v)).
  - apply (usable_assertion_stable F). unfold A. now apply interpret_type_shape.
  - exact Hv.
  - intros k U HV. destruct b; exact (readable_typed_value F k U t η X (TTypat (TProd ρ1 ρ2) d) v HX HV).
  - intros k U σ α [_ (l & o & info & -> & Hl & _ & v1 & v2 & -> & _)] Hstore.
    destruct (proj2 (store_spec_view _ _ _ _ Hstore) l o _ Hl) as [_ (s & Hσ & Hs)].
    destruct s; cbn [cell_view] in Hs; try discriminate Hs.
    injection Hs as -> ->. destruct b; [exact (ReadyProj σ true l v1 v2 Hσ)|exact (ReadyProj σ false l v1 v2 Hσ)].
  - intros k U G σ α σ' α' e' [Hd (l & o & info & -> & Hl & _ & v1 & v2 & -> & H1 & H2)] Hstore Hstep.
    destruct (proj2 (store_spec_view _ _ _ _ Hstore) l o _ Hl) as [_ (s & Hσ & Hs)].
    destruct s; cbn [cell_view] in Hs; try discriminate Hs.
    injection Hs as -> ->.
    remember ((if b then Fst else Snd) (VLoc l)) as src eqn:Heq.
    destruct Hstep; destruct b; simpl in Heq; try discriminate Heq;
      destruct b0; simpl in Heq; try discriminate Heq; inversion Heq; subst.
    all: match goal with H : ?heap !! ?addr = Some (SProd _ _) |- _ =>
      first [constr_eq H Hσ; fail 1 | rewrite Hσ in H; inversion H; subst]
    end.
    all: split; [reflexivity|]; split; [reflexivity|].
    all: apply (interp_value_spec F _ η X t k (fst U)); [exact HX|].
    all: refine (usable_reanchor F k _ (η d) t _ Hd k (Nat.le_refl k) (fst U) _ _).
    all: try solve [now apply interpret_type_shape].
    all: eapply (shape_usable_downward F); [now apply interpret_type_shape|eassumption].
Qed.

Local Lemma model_injection δ Δ Γ e ρ1 ρ2 (b : bool) :
  expression_typing_model δ Δ Γ e (if b then ρ1 else ρ2) ->
  expression_typing_model δ Δ Γ ((if b then InL else InR) e) (TTypat (TSum ρ1 ρ2) δ).
Proof.
  intros He.
  eapply (model_unary δ Δ Γ e _ _ (if b then InL else InR) (if b then CtxInL else CtxInR));
    try (destruct b; reflexivity); [exact He|].
  intros F η X n W v HX Hv.
  set (t := η δ).
  set (ρ := if b then ρ1 else ρ2).
  set (A := interpret_type F ρ η X []).
  set (s := if b then SInL v else SInR v).
  assert (HA : type_shape F A) by (unfold A; now apply interpret_type_shape).
  eapply (expression_spec_allocate_cell n F W t _ _ s (fun k U => usable_at A t k U v)).
  - now apply (usable_assertion_stable F).
  - exact Hv.
  - intros k U HV. destruct b; exact (readable_typed_value F k U t η X ρ v HX HV).
  - intros σ. destruct b; [exact (ReadyIn σ true v)|exact (ReadyIn σ false v)].
  - intros G σ α σ' α' e' Hstep.
    remember ((if b then InL else InR) (Val v)) as src eqn:Heq.
    destruct Hstep; try (destruct b; discriminate Heq).
    all: destruct b0, b; inversion Heq; subst; clear Heq.
    all: eexists; split; [apply not_elem_of_dom; eassumption|]; repeat split; reflexivity.
  - destruct b; discriminate.
  - intros k U l HV Hgrow.
    apply (interp_value_spec F (TTypat (TSum ρ1 ρ2) δ) η X t k); [exact HX|].
    apply inserted_cell_has_type. pose proof (shape_usable_monotone F A t HA k U _ v Hgrow HV) as Hnew.
    destruct b; [left|right]; exists v; now split.
Qed.

Local Definition modeled_arguments δ Δ Γ :=
  Forall2 (fun e ρ => locs e = ∅ /\ expression_typing_model δ Δ Γ e ρ).

Local Definition valued_arguments F η X t n (W : resource n) :=
  Forall2 (fun (v : val) ρ => usable_at (interpret_type F ρ η X []) t n W v).

Local Lemma valued_arguments_stable F η X t vs rs :
  admissible_assignment F X ->
  assertion_stable (fun n W => valued_arguments F η X t n W vs rs).
Proof.
  intros HX. split.
  - intros n W H. induction H as [|v r vs rs Hv Hr IH]; [constructor|].
    constructor; [eapply (shape_usable_downward F); [now apply interpret_type_shape|exact Hv]|exact IH].
  - intros n W U Hext H. induction H as [|v r vs rs Hv Hr IH]; [constructor|].
    constructor; [eapply (shape_usable_monotone F); [now apply interpret_type_shape|exact Hext|exact Hv]|exact IH].
Qed.

Local Lemma readable_val_list F η X t n (W : resource n) vs rs :
  admissible_assignment F X -> valued_arguments F η X t n W vs rs ->
  readable_in_view F (resource_view n W) t (locs vs).
Proof.
  intros HX H. induction H as [|v r vs rs Hv Hr IH].
  - apply readable_none.
  - change (readable_in_view F (resource_view n W) t (locs v ∪ locs vs)).
    apply readable_union; [exact (readable_typed_value F n W t η X r v HX Hv)|exact IH].
Qed.

Local Lemma readable_code_list δ Δ Γ F η X n (W : resource n) E es rs :
  typed_value_env F n W (η δ) η X Γ E ->
  modeled_arguments δ Δ Γ es rs ->
  readable_in_view F (resource_view n W) (η δ) (locs (close_expr E <$> es)).
Proof.
  intros Henv H. induction H as [|e r es rs [Hl He] Hrest IH].
  - apply readable_none.
  - change (readable_in_view F (resource_view n W) (η δ)
      (locs (close_expr E e) ∪ locs (close_expr E <$> es))).
    apply readable_union; [exact (readable_closed_code F n W (η δ) η X Γ E e Henv Hl)|exact IH].
Qed.

Local Lemma expression_spec_evaluate_arguments δ Δ Γ F η X E
    (Inv : world_assertion) (op : list expr -> expr) (K : list val -> list expr -> ctx)
    (Q : element_spec) arity es rs :
  admissible_assignment F X -> clock_constraints F η Δ ->
  assertion_stable Inv ->
  (forall n (W : resource n), Inv n W -> typed_value_env F n W (η δ) η X Γ E) ->
  (forall vs e tail, (length vs + S (length tail) = arity)%nat ->
    op ((Val <$> vs) ++ e :: tail) = fill_item (K vs tail) e) ->
  (forall n (W : resource n) vs tail, Inv n W ->
    (length vs + S (length tail) = arity)%nat ->
    readable_in_view F (resource_view n W) (η δ) (locs vs) ->
    readable_in_view F (resource_view n W) (η δ) (locs tail) ->
    context_support F (resource_view n W) (η δ) (K vs tail)) ->
  modeled_arguments δ Δ Γ es rs ->
  forall n (W : resource n) vs ss,
    Inv n W -> valued_arguments F η X (η δ) n W vs ss ->
    (length vs + length es = arity)%nat ->
    (forall k (U : resource k) ws, Inv k U ->
      valued_arguments F η X (η δ) k U ws (ss ++ rs) ->
      expression_spec k F U (Leaf (η δ)) (op (Val <$> ws)) Q) ->
    expression_spec n F W (Leaf (η δ)) (op ((Val <$> vs) ++ (close_expr E <$> es))) Q.
Proof.
  intros HX HΔ HI Henv Hfill Hread Hargs.
  induction Hargs as [|e r es rs [Hloc He] Hrest IH]; intros n W vs ss HW Hvs Hlen Hfinish.
  - cbn [fmap list_fmap]. rewrite app_nil_r. apply Hfinish; [exact HW|now rewrite app_nil_r].
  - set (t := η δ).
    set (tail := close_expr E <$> es).
    set (A := interpret_type F r η X []).
    assert (Hlength : (length vs + S (length tail) = arity)%nat) by (unfold tail; now rewrite length_fmap).
    change (expression_spec n F W (Leaf t) (op ((Val <$> vs) ++ close_expr E e :: tail)) Q).
    rewrite Hfill by exact Hlength.
    eapply (expression_spec_evaluate n F W t _ _ (usable_at A t) _
      (fun k U => Inv k U /\ valued_arguments F η X t k U vs ss)).
    + apply assertion_stable_and; [exact HI|now apply valued_arguments_stable].
    + now split.
    + apply Hread; [exact HW|exact Hlength|eapply readable_val_list; eassumption|].
      eapply (readable_code_list δ Δ Γ F η X n W E es rs); [now apply Henv|exact Hrest].
    + apply He; [exact HX|exact HΔ|now apply Henv].
    + intros k U v [HU Hvals] Hv. rewrite <-Hfill by exact Hlength.
      replace ((Val <$> vs) ++ (Val v :: tail)) with ((Val <$> (vs ++ [v])) ++ tail)
        by (rewrite fmap_app, <-app_assoc; reflexivity).
      eapply (IH k U (vs ++ [v]) (ss ++ [r])).
      * exact HU.
      * unfold valued_arguments. apply Forall2_app; [exact Hvals|].
        constructor; [exact Hv|constructor].
      * rewrite length_app. simpl. simpl in Hlen. lia.
      * intros i V ws HV Hws. apply Hfinish; [exact HV|].
        rewrite <-app_assoc in Hws. exact Hws.
Qed.

Local Definition store_expressions (es : list expr) :=
  match es with [a;i;v] => Store a i v | _ => Val VUnit end.

Local Definition store_context (vs : list val) (es : list expr) :=
  match vs, es with
  | [], [i;v] => CtxStore1 i v
  | [a], [v] => CtxStore2 a v
  | [a;i], [] => CtxStore3 a i
  | _, _ => CtxLength
  end.

Local Lemma store_context_length vs es :
  (length vs + S (length es) = 3)%nat ->
  (forall e, store_expressions ((Val <$> vs) ++ e :: es) = fill_item (store_context vs es) e) /\
  locs (store_context vs es) ⊆ locs vs ∪ locs es.
Proof.
  destruct vs as [|a [|i [|v vs]]], es as [|e [|f [|g es]]]; simpl; try lia.
  all: intros _; split; [reflexivity|].
  all: cbn [locs_ctx]; repeat rewrite locs_list_cons; set_solver.
Qed.

Local Lemma model_store δ Δ Γ e1 e2 e3 ρ d :
  locs e1 = ∅ -> locs e2 = ∅ -> locs e3 = ∅ ->
  expression_typing_model δ Δ Γ e1 (TTypat (TArray ρ) d) ->
  expression_typing_model δ Δ Γ e2 TBInt ->
  expression_typing_model δ Δ Γ e3 ρ ->
  expression_typing_model δ Δ Γ (Store e1 e2 e3) TBUnit.
Proof.
  intros HL1 HL2 HL3 H1 H2 H3 F η X n W E HX HΔ Henv.
  set (t := η δ).
  set (Q := usable_at (interpret_type F TBUnit η X []) t).
  set (Inv := fun k U => typed_value_env F k U t η X Γ E).
  change (expression_spec n F W (Leaf t)
    (store_expressions ((Val <$> []) ++ (close_expr E <$> [e1;e2;e3]))) Q).
  refine (expression_spec_evaluate_arguments δ Δ Γ F η X E Inv store_expressions store_context Q
    3 [e1;e2;e3] [TTypat (TArray ρ) d; TBase TBInt; ρ] HX HΔ _ _ _ _ _ n W [] [] _ _ _ _).
  - now apply env_assertion_stable.
  - intros; assumption.
  - intros vs e es Hlen. exact (proj1 (store_context_length vs es Hlen) e).
  - intros k U vs es _ Hlen Hvs Hes l Hl.
    eapply readable_union; [exact Hvs|exact Hes|].
    exact (proj2 (store_context_length vs es Hlen) l Hl).
  - repeat constructor; assumption.
  - exact Henv.
  - constructor.
  - reflexivity.
  - intros k U ws _ Hws.
    inversion Hws as [|a r ws' rs Ha Hrest]; subst. clear Hws.
    inversion Hrest as [|i r ws'' rs Hi Hrest']; subst. clear Hrest.
    inversion Hrest' as [|v r ws''' rs Hv Hnil]; subst. inversion Hnil; subst.
    destruct Hi as [_ Hi]. destruct i; cbn in Hi; try contradiction; try discriminate.
    destruct (interpret_array_forms F δ d η X ρ k U a HX Ha) as (l & o & size & -> & Hl & Ho & Ht & Harr).
    pose proof (interpret_type_shape F ρ η X [] HX) as (_ & Hmono & Hdown & Hvisible).
    eapply expression_spec_post_inclusion with (P := unit_element).
    + intros j Hj V w Hw. unfold unit_element in Hw. subst w. split; [exact I|reflexivity].
    + cbn [store_expressions]. eapply expression_spec_store; [exact Hl|exact Ho|exact Harr|exact Hdown| |].
      * intros V Hext. apply (Hmono k U V v Hext). exact (proj2 Hv).
      * intros j V w Hw. now apply Hvisible.
Qed.

Local Lemma expression_spec_cas n F (W : resource n) t l (i : Z) (v w : val) o size A E :
  resource_view n W !! l = Some (o,inl size) -> reachable F o t ->
  array_spec_at n W l E ->
  type_shape F (A,E) -> A t -> E n W v -> E n W w ->
  expression_spec n F W (Leaf t) (CAS (VLoc l) i v w) (usable_at (scalar_type TBBool) t).
Proof.
  intros Hl Ho Harr Hshape Ht Hv Hw.
  induction n as [|n IH]; [exact I|].
  destruct Hshape as (Hscope & Hmono & Hdown & Hvis).
  apply expression_spec_atomic.
  - exact (IH (fst W) Hl (proj1 Harr) (Hdown n W v Hv) (Hdown n W w Hw)).
  - intros U σ α G Hext Hstore HG.
    assert (Hentry : resource_view (S n) U !! l = Some (o,inl size))
      by exact (lookup_weaken _ _ _ _ Hl (resource_view_extends _ _ _ Hext)).
    destruct (proj2 (store_spec_view _ _ _ _ Hstore) l o _ Hentry) as [_ (s & Hσ & Hs)].
    destruct s; try discriminate Hs.
    assert (HV : E (S n) U v) by (eapply Hmono; eassumption).
    assert (HW : E (S n) U w) by (eapply Hmono; eassumption).
    split; [eapply ReadyCAS; exact Hσ|]. split.
    + eapply readable_access; [exact Hstore|].
      change (readable_in_view F (resource_view (S n) U) t ((({[l]} : gset loc) ∪ ∅) ∪ locs v ∪ locs w)).
      repeat apply readable_union.
      * intros l' Hl'. apply elem_of_singleton in Hl' as ->. exists o, (inl size). now split.
      * apply readable_none.
      * exact (Hvis (S n) U t v Ht HV).
      * exact (Hvis (S n) U t w Ht HW).
    + intros σ' α' e' Hstep. inversion Hstep; subst;
        try match goal with H : (if ?b then _ else _) = _ |- _ => destruct b; discriminate H end.
      exists (fst U). split; [apply resource_extends_refl|]. split.
      * match goal with |- store_spec_at _ _ (if ?b then _ else _) _ => destruct b end; [|exact (proj1 Hstore)].
        eapply store_replacement_spec; [exact (proj1 Hstore)| |apply element_fits_one|eassumption].
        -- exact (proj1 (array_spec_extend _ _ _ _ _ Hext Harr)).
        -- exact Hdown.
        -- now apply Hdown.
      * apply expression_spec_value.
        -- intros k V _ l' Hl'. change (l' ∈ (∅ : gset loc)) in Hl'. set_solver.
        -- intros V _. split; [exact I|reflexivity].
        -- intros k V. exact (fun H => H).
Qed.

Local Definition cas_expressions (es : list expr) :=
  match es with [a;i;v;w] => CAS a i v w | _ => Val VUnit end.

Local Definition cas_context (vs : list val) (es : list expr) :=
  match vs, es with
  | [], [i;v;w] => CtxCas1 i v w
  | [a], [v;w] => CtxCas2 a v w
  | [a;i], [w] => CtxCas3 a i w
  | [a;i;v], [] => CtxCas4 a i v
  | _, _ => CtxLength
  end.

Local Lemma cas_context_length vs es :
  (length vs + S (length es) = 4)%nat ->
  (forall e, cas_expressions ((Val <$> vs) ++ e :: es) = fill_item (cas_context vs es) e) /\
  locs (cas_context vs es) ⊆ locs vs ∪ locs es.
Proof.
  destruct vs as [|a [|i [|v [|w vs]]]], es as [|e [|f [|g [|h es]]]];
    simpl; try lia.
  all: intros _; split; [reflexivity|].
  all: cbn [locs_ctx]; repeat rewrite locs_list_cons; set_solver.
Qed.

Local Lemma model_cas δ Δ Γ e1 e2 e3 e4 ρ d :
  locs e1 = ∅ -> locs e2 = ∅ -> locs e3 = ∅ -> locs e4 = ∅ ->
  expression_typing_model δ Δ Γ e1 (TTypat (TArray ρ) d) ->
  expression_typing_model δ Δ Γ e2 TBInt ->
  expression_typing_model δ Δ Γ e3 ρ ->
  expression_typing_model δ Δ Γ e4 ρ ->
  expression_typing_model δ Δ Γ (CAS e1 e2 e3 e4) TBBool.
Proof.
  intros HL1 HL2 HL3 HL4 H1 H2 H3 H4 F η X n W E HX HΔ Henv.
  set (t := η δ).
  set (Q := usable_at (interpret_type F TBBool η X []) t).
  set (Inv := fun k U => typed_value_env F k U t η X Γ E).
  change (expression_spec n F W (Leaf t)
    (cas_expressions ((Val <$> []) ++ (close_expr E <$> [e1;e2;e3;e4]))) Q).
  refine (expression_spec_evaluate_arguments δ Δ Γ F η X E Inv cas_expressions cas_context Q
    4 [e1;e2;e3;e4] [TTypat (TArray ρ) d; TBase TBInt; ρ; ρ] HX HΔ _ _ _ _ _ n W [] [] _ _ _ _).
  - now apply env_assertion_stable.
  - intros; assumption.
  - intros vs e es Hlen. exact (proj1 (cas_context_length vs es Hlen) e).
  - intros k U vs es _ Hlen Hvs Hes l Hl.
    eapply readable_union; [exact Hvs|exact Hes|].
    exact (proj2 (cas_context_length vs es Hlen) l Hl).
  - repeat constructor; assumption.
  - exact Henv.
  - constructor.
  - reflexivity.
  - intros k U ws _ Hws.
    inversion Hws as [|a r ws' rs Ha Hrest]; subst. clear Hws.
    inversion Hrest as [|i r ws'' rs Hi Hrest']; subst. clear Hrest.
    inversion Hrest' as [|v r ws''' rs Hv Hrest'']; subst. clear Hrest'.
    inversion Hrest'' as [|w r ws'''' rs Hw Hnil]; subst. inversion Hnil; subst.
    destruct Hi as [_ Hi]. destruct i; cbn in Hi; try contradiction; try discriminate.
    destruct (interpret_array_forms F δ d η X ρ k U a HX Ha) as (l & o & size & -> & Hl & Ho & Ht & Harr).
    cbn [cas_expressions]. eapply expression_spec_cas;
      [exact Hl|exact Ho|exact Harr| |exact Ht|exact (proj2 Hv)|exact (proj2 Hw)].
    pose proof (interpret_type_shape F ρ η X [] HX) as Hshape.
    destruct (interpret_type F ρ η X []). exact Hshape.
Qed.

Local Lemma readable_bound_code F n (W : resource n) t η X Γ E e b :
  typed_value_env F n W t η X Γ E -> locs e = ∅ ->
  readable_in_view F (resource_view n W) t (locs (close_expr (bdelete b E) e)).
Proof.
  intros [_ Henv] Hl. unfold readable_in_view.
  apply closed_code_visible; [exact Hl|].
  intros x v Hx. rewrite binder_lookup_delete in Hx.
  destruct (decide (x ∈ binder_set b)); [discriminate|eauto].
Qed.

Local Lemma model_case δ Δ Γ e e1 e2 x1 x2 ρ1 ρ2 d ρ :
  locs e1 = ∅ -> locs e2 = ∅ ->
  expression_typing_model δ Δ Γ e (TTypat (TSum ρ1 ρ2) d) ->
  expression_typing_model δ Δ (binsert x1 ρ1 Γ) e1 ρ ->
  expression_typing_model δ Δ (binsert x2 ρ2 Γ) e2 ρ ->
  expression_typing_model δ Δ Γ (Case e x1 e1 x2 e2) ρ.
Proof.
  intros Hl1 Hl2 He H1 H2 F η X n W E HX HΔ Henv.
  set (t := η δ).
  set (Inv := fun k U => typed_value_env F k U t η X Γ E).
  set (A := interpret_type F (TTypat (TSum ρ1 ρ2) d) η X []).
  set (Q := usable_at (interpret_type F ρ η X []) t).
  set (K := CtxCase x1 (close_expr (bdelete x1 E) e1) x2 (close_expr (bdelete x2 E) e2)).
  assert (HI : assertion_stable Inv) by (unfold Inv; now apply env_assertion_stable).
  assert (HK : forall k (U : resource k), Inv k U -> context_support F (resource_view k U) t K).
  { intros k U HU. unfold context_support, K. change (readable_in_view F (resource_view k U) t
      (locs (close_expr (bdelete x1 E) e1) ∪ locs (close_expr (bdelete x2 E) e2))).
    apply readable_union; eapply readable_bound_code; eassumption. }
  change (expression_spec n F W (Leaf t) (fill_item K (close_expr E e)) Q).
  eapply (expression_spec_evaluate n F W t K _ (usable_at A t) Q Inv);
    [exact HI|exact Henv|now apply HK|now apply He|].
  intros k U v HU Hv.
  eapply (expression_spec_readonly k F U t _ Q (fun i V => Inv i V /\ usable_at A t i V v)).
  - apply assertion_stable_and; [exact HI|]. apply (usable_assertion_stable F). unfold A. now apply interpret_type_shape.
  - now split.
  - intros i V [HV Hv']. unfold K.
    change (readable_in_view F (resource_view i V) t
      (locs v ∪ locs (close_expr (bdelete x1 E) e1) ∪ locs (close_expr (bdelete x2 E) e2))).
    repeat apply readable_union.
    + exact (readable_typed_value F i V t η X (TTypat (TSum ρ1 ρ2) d) v HX Hv').
    + eapply readable_bound_code; eassumption.
    + eapply readable_bound_code; eassumption.
  - intros i V σ α [_ [_ (l & o & info & -> & Hl & _ & [(v1 & -> & Hval)|(v2 & -> & Hval)])]] Hstore.
    + destruct (proj2 (store_spec_view _ _ _ _ Hstore) l o _ Hl) as [_ (s & Hσ & Hs)].
      destruct s; cbn [cell_view] in Hs; try discriminate Hs. injection Hs as ->.
      exact (ReadyCase σ true l v1 VUnit _ _ _ _ Hσ).
    + destruct (proj2 (store_spec_view _ _ _ _ Hstore) l o _ Hl) as [_ (s & Hσ & Hs)].
      destruct s; cbn [cell_view] in Hs; try discriminate Hs. injection Hs as ->.
      exact (ReadyCase σ false l VUnit v2 _ _ _ _ Hσ).
  - intros i V G σ α σ' α' e' [HV [Hd (l & o & info & -> & Hl & _ & Hshape)]] Hstore Hstep.
    destruct (proj2 (store_spec_view _ _ _ _ Hstore) l o _ Hl) as [_ (s & Hσ & Hs)].
    cbn [K fill_item] in Hstep. inversion Hstep; subst;
      try match goal with H : (if ?b then _ else _) = _ |- _ => destruct b; discriminate H end.
    split; [reflexivity|]. split; [reflexivity|].
    match goal with H : _ !! _ = Some (if _ then _ else _) |- _ => rewrite Hσ in H; injection H as -> end.
    destruct b; cbn [cell_view] in Hshape;
      destruct Hshape as [(payload & Heq & Hvalue)|(payload & Heq & Hvalue)];
      try discriminate Heq; injection Heq as ->; rewrite close_single_binding.
    + apply H1; [exact HX|exact HΔ|]. apply typed_value_env_insert; [exact HX|exact (proj1 HI i V HV)|].
      refine (usable_reanchor F i _ (η d) t _ Hd i (Nat.le_refl i) (fst V) _ _).
      * now apply interpret_type_shape.
      * eapply (shape_usable_downward F); [now apply interpret_type_shape|exact Hvalue].
    + apply H2; [exact HX|exact HΔ|]. apply typed_value_env_insert; [exact HX|exact (proj1 HI i V HV)|].
      refine (usable_reanchor F i _ (η d) t _ Hd i (Nat.le_refl i) (fst V) _ _).
      * now apply interpret_type_shape.
      * eapply (shape_usable_downward F); [now apply interpret_type_shape|exact Hvalue].
Qed.

Local Lemma atom_location F σ η X t n (W : resource n) v :
  interpret_at F σ η X t n W v ->
  exists l o d, v = VLoc l /\ resource_view n W !! l = Some (o,d) /\ reachable F o t.
Proof.
  destruct σ; intros (addr & orig & info & -> & Hl & Ho & _); exists addr,orig,info; auto.
Qed.

Local Lemma recursive_type_substitution F σ η X d x n :
  admissible_assignment F X ->
  d ∉ bv_typat σ -> fv_typat σ ## bv_typat σ -> fvv_typat σ ## bvv_typat σ ->
  let t := η d in
  let τ := TRec x σ d in
  let B := fun E => interpret_at F σ η (type_assume X (BNamed x) (fun _ => anchored F t E)) t in
  element_prefix n (interpret_at F (vsubst_typat x τ σ) η X t) (B (recursive_element F t B)).
Proof.
  intros HX Hd Hf Hfv t τ B.
  set (Y := type_assume X (BNamed x) (fun ts => interpret_type F τ η X ts)).
  change (element_prefix n (interpret_at F (vsubst_typat x τ σ) η X t) (interpret_at F σ η Y t)).
  assert (HY : admissible_assignment F Y)
    by (unfold Y; apply admissible_type_assume; [exact HX|now apply interpret_family_shape]).
  apply interpret_replaced_atom;
    [now apply admissible_regular|now apply admissible_regular|cbn [τ fv_typ]; set_solver|cbn [τ fvv_typ]; set_solver|].
  intros y _. apply family_shape_related. exact (HY y).
Qed.

Local Lemma model_fold δ Δ Γ x σ d e :
  d ∉ bv_typat σ -> fv_typat σ ## bv_typat σ -> fvv_typat σ ## bvv_typat σ ->
  expression_typing_model δ Δ Γ e (TTypat (vsubst_typat x (TRec x σ d) σ) d) ->
  expression_typing_model δ Δ Γ (Fold e) (TRec x σ d).
Proof.
  intros Hd Hf Hfv He.
  eapply (model_unary δ Δ Γ e _ _ Fold CtxFold); try reflexivity; [exact He|].
  intros F η X n W v HX Hv.
  set (τ := TRec x σ d).
  set (σ' := vsubst_typat x τ σ).
  set (ρ := TTypat σ' d).
  set (A := interpret_type F ρ η X []).
  set (t := η δ). set (s := η d).
  set (B := fun E => interpret_at F σ η (type_assume X (BNamed x) (fun _ => anchored F s E)) s).
  assert (HB : forall i P Q, element_prefix i P Q -> element_prefix i (B P) (B Q))
    by (unfold B; now apply interpretation_recursive_operator).
  eapply (expression_spec_readonly n F W t _ _ (fun k U => usable_at A t k U v)).
  - apply (usable_assertion_stable F). unfold A. now apply interpret_type_shape.
  - exact Hv.
  - intros k U HV. exact (readable_typed_value F k U t η X ρ v HX HV).
  - intros. apply ReadyFold.
  - intros k U G μ α μ' α' e' [Ht HE] _ Hstep. inversion Hstep; subst;
      try match goal with H : (if ?b then _ else _) = _ |- _ => destruct b; discriminate H end.
    split; [reflexivity|]. split; [reflexivity|].
    apply (interp_value_spec F τ η X t k (fst U)); [exact HX|].
    split; [exact Ht|]. change (recursive_element F s B k (fst U) (VFold v)).
    apply (proj2 (recursive_element_unfold F s B k (fst U) _ HB)).
    destruct (atom_location F σ' η X s (S k) U v HE) as (l & o & info & -> & Hl & Ho).
    exists (VLoc l). split; [reflexivity|]. exists l,o,info.
    split; [reflexivity|]. split; [exact Hl|]. split; [exact Ho|].
    destruct k as [|k]; [exact I|]. cbn [delayed_element].
    apply (proj1 (recursive_type_substitution F σ η X d x k HX Hd Hf Hfv k (Nat.le_refl _) _ _)).
    pose proof (interpret_type_shape F ρ η X [] HX) as (_ & _ & Hdown & _).
    apply Hdown. apply Hdown. exact HE.
Qed.

Local Lemma model_unfold δ Δ Γ x σ d e :
  d ∉ bv_typat σ -> fv_typat σ ## bv_typat σ -> fvv_typat σ ## bvv_typat σ ->
  expression_typing_model δ Δ Γ e (TRec x σ d) ->
  expression_typing_model δ Δ Γ (Unfold e) (TTypat (vsubst_typat x (TRec x σ d) σ) d).
Proof.
  intros Hd Hf Hfv He.
  eapply (model_unary δ Δ Γ e _ _ Unfold CtxUnfold); try reflexivity; [exact He|].
  intros F η X n W v HX Hv.
  set (τ := TRec x σ d).
  set (ρ := TTypat (vsubst_typat x τ σ) d).
  set (A := interpret_type F τ η X []).
  set (t := η δ). set (s := η d).
  set (B := fun E => interpret_at F σ η (type_assume X (BNamed x) (fun _ => anchored F s E)) s).
  assert (HB : forall i P Q, element_prefix i P Q -> element_prefix i (B P) (B Q))
    by (unfold B; now apply interpretation_recursive_operator).
  eapply (expression_spec_readonly n F W t _ _ (fun k U => usable_at A t k U v)).
  - apply (usable_assertion_stable F). unfold A. now apply interpret_type_shape.
  - exact Hv.
  - intros k U HV. exact (readable_typed_value F k U t η X τ v HX HV).
  - intros k U μ α [_ HE] _.
    apply (proj1 (recursive_element_unfold F s B k U v HB)) in HE.
    destruct HE as (w & -> & _). apply ReadyUnfold.
  - intros k U G μ α μ' α' e' [Ht HE] _ Hstep.
    apply (proj1 (recursive_element_unfold F s B (S k) U v HB)) in HE.
    destruct HE as (w & -> & l & o & info & -> & Hl & Ho & Hp).
    inversion Hstep; subst;
      try match goal with H : (if ?b then _ else _) = _ |- _ => destruct b; discriminate H end.
    split; [reflexivity|]. split; [reflexivity|].
    apply (interp_value_spec F ρ η X t k (fst U)); [exact HX|].
    split; [exact Ht|].
    apply (proj2 (recursive_type_substitution F σ η X d x k HX Hd Hf Hfv k (Nat.le_refl _) _ _)).
    exact Hp.
Qed.

Local Definition arrow_signature F η X bs Δ d rs ρ :=
  {| time_arity := length bs;
     call_constraints := fun ts => clock_constraints F (clock_extend η (bmap bs ts)) Δ;
     call_time := fun ts => clock_extend η (bmap bs ts) d;
     call_parameters := fun ts =>
       let θ := clock_extend η (bmap bs ts) in
       (fun r => usable_at (interpret_type F r θ X []) (θ d)) <$> rs;
     call_result := fun ts =>
       let θ := clock_extend η (bmap bs ts) in usable_at (interpret_type F ρ θ X []) (θ d) |}.

Local Lemma call_argument_properties F η X bs Δ d rs ρ ts caller :
  admissible_assignment F X ->
  clock_equivalent F (call_time (arrow_signature F η X bs Δ d rs ρ) ts) caller ->
  let sig := arrow_signature F η X bs Δ d rs ρ in
  Forall element_downward (call_parameters sig ts) /\
  (forall k (W : resource k) E v, E ∈ call_parameters sig ts -> E k W v ->
      value_visible_in_view F (resource_view k W) caller v).
Proof.
  intros HX [Hlater Hearlier] sig. split.
  - apply Forall_forall. intros P HP. apply list_elem_of_fmap in HP as (r & -> & _).
    apply (shape_usable_downward F). now apply interpret_type_shape.
  - intros k W P v HP HV. apply list_elem_of_fmap in HP as (r & -> & _). destruct HV as [Htime Hv].
    pose proof (interpret_type_shape F r (clock_extend η (bmap bs ts)) X [] HX) as (Hscope & _ & _ & Hvisible).
    apply Hvisible; [eapply Hscope; [exact Hlater|exact Htime]|exact Hv].
Qed.

Local Lemma extend_lookup_value bs (ds : list string) (m : gmap string string) x y :
  extend bs ds m !! x = Some y -> y ∈ ds \/ m !! x = Some y.
Proof.
  revert ds m. induction bs as [|b bs IH]; intros [|d ds] m H; try (now right).
  rewrite extend_cons in H. apply IH in H as [H|H]; [left; now constructor 2|].
  destruct b as [|b]; [now right|]. cbn [binsert] in H.
  apply lookup_insert_Some in H as [[_ ->]|[_ H]]; [left; constructor|now right].
Qed.

Local Lemma substitution_from_actuals bs ds L :
  list_to_set ds ## L -> substitution_avoids (bmap bs ds) L.
Proof.
  intros Hfresh x y Hlookup. apply extend_lookup_value in Hlookup as [Hin|Hnone].
  - set_solver.
  - rewrite lookup_empty in Hnone. discriminate.
Qed.

Local Lemma instantiate_call_type F n η X bs ds ρ :
  admissible_assignment F X ->
  substitution_avoids (bmap bs ds) (bv_typ ρ) ->
  type_prefix n (interpret_type F (tsubst_typ (bmap bs ds) ρ) η X [])
    (interpret_type F ρ (clock_extend η (bmap bs (η <$> ds))) X []).
Proof.
  intros HX Hfresh. eapply type_prefix_trans.
  - apply interpret_type_substitution; [now apply admissible_regular|exact Hfresh].
  - apply compare_clock_assignments; [now apply admissible_regular|].
    intros x. symmetry. apply clock_extend_actuals.
Qed.

Local Lemma instantiate_call_arguments F k (W : resource k) η X bs ds Δ d rs ρ vs :
  admissible_assignment F X ->
  list_to_set ds ## ⋃ (bv_typ <$> rs) ->
  valued_arguments F η X (η (find_opt (bmap bs ds) d)) k W vs (tsubst_typ (bmap bs ds) <$> rs) ->
  accepts_args (arrow_signature F η X bs Δ d rs ρ) (η <$> ds) k W vs.
Proof.
  intros HX Hfresh. revert vs Hfresh.
  induction rs as [|r rs IH]; intros vs Hfresh Hvals.
  - inversion Hvals; constructor.
  - inversion Hvals as [|v r' vs' rs' Hv Hvs]; subst.
    constructor.
    + cbn [arrow_signature call_time]. rewrite clock_extend_actuals.
      assert (Hsafe : substitution_avoids (bmap bs ds) (bv_typ r)).
      { apply substitution_from_actuals. intros x Hx Hr. apply (Hfresh x Hx).
        apply elem_of_union_list. exists (bv_typ r). split; [constructor|exact Hr]. }
      apply (usable_prefix_same k _ _ _ (instantiate_call_type F k η X bs ds r HX Hsafe) k (Nat.le_refl _) W v).
      exact Hv.
    + apply IH; [|exact Hvs]. intros x Hx Hr. apply (Hfresh x Hx).
      apply elem_of_union_list in Hr as (l & Hl & Hxl). apply elem_of_union_list. exists l. split; [now constructor 2|exact Hxl].
Qed.

Local Lemma model_app ds δ Δ Γ e bs Δf d rs ρ a es :
  length bs = length ds ->
  list_to_set ds ## bv_typ ρ ∪ ⋃ (bv_typ <$> rs) ->
  δ = find_opt (bmap bs ds) d ->
  all_reachable Δ (tsubst_constraints (bmap bs ds) Δf) ->
  modeled_arguments δ Δ Γ es (tsubst_typ (bmap bs ds) <$> rs) ->
  expression_typing_model δ Δ Γ e (TTypat (TArrow bs Δf d rs ρ) a) ->
  expression_typing_model δ Δ Γ (Call e es) (tsubst_typ (bmap bs ds) ρ).
Proof.
  intros Hlen Hfresh -> Hreach Hes He F η X n W E HX HΔ Henv.
  set (δ := find_opt (bmap bs ds) d).
  set (t := η δ).
  set (τ := TTypat (TArrow bs Δf d rs ρ) a).
  set (A := interpret_type F τ η X []).
  set (Q := usable_at (interpret_type F (tsubst_typ (bmap bs ds) ρ) η X []) t).
  set (Inv := fun k U => typed_value_env F k U t η X Γ E).
  set (ts := η <$> ds).
  set (sig := arrow_signature F η X bs Δf d rs ρ).
  assert (His : assertion_stable Inv) by (unfold Inv; now apply env_assertion_stable).
  assert (Hclock : call_time sig ts = t) by (unfold sig, ts, t, δ; cbn [arrow_signature call_time]; apply clock_extend_actuals).
  assert (Hparams : length ts = time_arity sig) by (unfold ts, sig; cbn [arrow_signature time_arity]; now rewrite length_fmap).
  assert (Hcons : call_constraints sig ts).
  { unfold sig, ts. cbn [arrow_signature call_constraints].
    apply (clock_constraints_ext F (fun x => η (find_opt (bmap bs ds) x))); [intros; split; symmetry; apply clock_extend_actuals|].
    apply clock_constraints_substitute. eapply clock_all_reachable; eassumption. }
  assert (Hret : substitution_avoids (bmap bs ds) (bv_typ ρ)).
  { apply substitution_from_actuals. clear HΔ Hreach. set_solver. }
  assert (Hpars : list_to_set ds ## ⋃ (bv_typ <$> rs)) by (clear HΔ Hreach; set_solver).
  assert (Hc : clock_equivalent F (call_time sig ts) t) by (rewrite Hclock; apply clock_equivalent_refl).
  destruct (call_argument_properties F η X bs Δf d rs ρ ts t HX Hc) as [Hdown Hvisible].
  change (expression_spec n F W (Leaf t) (fill_item (CtxCall2 (close_expr E <$> es)) (close_expr E e)) Q).
  eapply (expression_spec_evaluate n F W t _ _ (usable_at A t) _ Inv).
  - exact His.
  - exact Henv.
  - exact (readable_code_list δ Δ Γ F η X n W E es _ Henv Hes).
  - now apply He.
  - intros k U v HU Hv. cbn [fill_item].
    set (J := fun i V => Inv i V /\ usable_at A t i V v).
    change (expression_spec k F U (Leaf t) (Call (Val v) ((Val <$> []) ++ (close_expr E <$> es))) Q).
    refine (expression_spec_evaluate_arguments δ Δ Γ F η X E J (Call (Val v)) (CtxCall1 v)
      Q (length es) es _ HX HΔ _ _ _ _ Hes k U [] [] _ _ _ _).
    + unfold J. apply assertion_stable_and; [exact His|]. apply (usable_assertion_stable F).
      unfold A. now apply interpret_type_shape.
    + intros i V [H _]. exact H.
    + reflexivity.
    + intros i V vs tail [_ HV] _ Hvs Htail.
      change (readable_in_view F (resource_view i V) t (locs v ∪ locs vs ∪ locs tail)).
      apply readable_union; [apply readable_union|exact Htail]; [exact (readable_typed_value F i V t η X τ v HX HV)|exact Hvs].
    + now split.
    + constructor.
    + reflexivity.
    + intros i V ws [_ [Hreachable Hfn]] Hws.
      change (function_result F (η a) sig i V v) in Hfn.
      destruct Hfn as (l & o & info & -> & Hl & Ho & Hbody).
      eapply expression_spec_post_inclusion with (P := call_result sig ts).
      * intros j Hj B w Hw. unfold Q. apply (usable_prefix_same i _ _ t
          (type_prefix_sym _ _ _ (instantiate_call_type F i η X bs ds ρ HX Hret)) j Hj B w).
        unfold sig in Hclock. cbn [arrow_signature call_time] in Hclock.
        unfold sig, ts in *. cbn [arrow_signature call_result] in Hw. now rewrite Hclock in Hw.
      * apply (expression_spec_call i F V (η a) t l ws sig ts Hparams Hcons Hc Hreachable).
        -- exists l,o,info. repeat split; assumption.
        -- exact Hdown.
        -- intros B Hext. eapply instantiate_call_arguments; [exact HX|exact Hpars|].
           eapply (proj2 (valued_arguments_stable F η X t ws _ HX)); eassumption.
        -- exact Hvisible.
Qed.

Local Lemma interpret_clock_prefix F n ρ η θ X ts us :
  admissible_assignment F X ->
  (forall x, x ∈ fv_typ ρ -> clock_equivalent F (η x) (θ x)) ->
  Forall2 (clock_equivalent F) ts us ->
  type_prefix n (interpret_type F ρ η X ts) (interpret_type F ρ θ X us).
Proof.
  intros HX Hfv Htime. apply (interpret_comparable_type F ρ);
    try now apply admissible_scope_monotone.
  - exact Hfv.
  - intros x _. exact (proj2 (admissible_regular F n X HX) x).
  - exact Htime.
Qed.

Local Lemma value_env_extend F n (W : resource n) t η X bs vs rs Γ E :
  admissible_assignment F X -> length bs = length rs ->
  valued_arguments F η X t n W vs rs ->
  typed_value_env F n W t η X Γ E ->
  typed_value_env F n W t η X (extend bs rs Γ) (extend bs vs E).
Proof.
  intros HX. revert vs rs Γ E. induction bs as [|b bs IH]; intros vs rs Γ E Hlen Hvs Henv.
  - destruct rs; [|discriminate]. inversion Hvs; subst. exact Henv.
  - destruct rs as [|r rs]; [discriminate|].
    inversion Hvs as [|v r' vs' rs' Hv Hrest]; subst.
    rewrite !extend_cons. apply IH; [now injection Hlen|exact Hrest|].
    now apply typed_value_env_insert.
Qed.

Local Lemma values_from_call_arguments F η X bs Δ d rs ρ ts caller n (W : resource n) vs θ :
  admissible_assignment F X ->
  let θ0 := clock_extend η (bmap bs ts) in
  clock_equivalent F (θ0 d) caller ->
  (forall x, clock_equivalent F (θ0 x) (θ x)) ->
  accepts_args (arrow_signature F η X bs Δ d rs ρ) ts n W vs ->
  valued_arguments F θ X caller n W vs rs.
Proof.
  intros HX θ0 Htime Hclocks. revert vs.
  induction rs as [|r rs IH]; intros vs Hvs.
  - inversion Hvs. constructor.
  - inversion Hvs as [|P v Ps vs' Hv Hrest]; subst.
    constructor; [|now apply IH].
    apply (type_prefix_usable F n (interpret_type F r θ0 X []) _ (θ0 d) caller
      (proj1 (interpret_type_shape F r θ0 X [] HX))
      (interpret_clock_prefix F n r θ0 θ X [] [] HX (fun x _ => Hclocks x) (list_clocks_refl F []))
      Htime n (Nat.le_refl _) W v).
    exact Hv.
Qed.

Local Lemma assertions_at_lower_resources n (W : resource n) (Inv P : world_assertion) :
  assertion_stable Inv -> Inv n W ->
  (forall k (U : resource k), Inv k U -> P k U) -> all_lower_resources n W P.
Proof.
  intros [Hdown _]. induction n as [|n IH]; intros HInv Himpl; [exact I|].
  pose proof (Hdown n W HInv) as Hlow. split; [now apply Himpl|now apply IH].
Qed.

Local Lemma model_closure δ Δ Γ bs Δf d ρ self e xs rs :
  length xs = length rs ->
  δ ∉ binders_set bs ->
  binders_set bs ## fv_constraints Δ ->
  binders_set bs ## fv_env Γ ->
  locs e = ∅ ->
  let τ := TTypat (TArrow bs Δf d rs ρ) δ in
  expression_typing_model d ({[(δ,d)]} ∪ Δf ∪ Δ) (extend (self::xs) (τ::rs) Γ) e ρ ->
  expression_typing_model δ Δ Γ (Clo (Lam self xs e)) τ.
Proof.
  intros Hlen Hd HfreshΔ HfreshΓ Hl τ Hbody F η X n W E HX HΔ Henv.
  set (t := η δ).
  set (body := close_expr (bdeletes (self::xs) E) e).
  set (sig := arrow_signature F η X bs Δf d rs ρ).
  change (expression_spec n F W (Leaf t) (Clo (Lam self xs body))
    (usable_at (anchored F t (function_result F t sig)) t)).
  eapply expression_spec_post_inclusion with (P := function_result F t sig).
  - intros k Hk U v Hv. split; [apply rtc_refl|exact Hv].
  - apply expression_spec_closure.
    + intros ts _. unfold sig. cbn [arrow_signature call_parameters]. now rewrite length_fmap.
    + unfold body. apply closed_code_visible; [exact Hl|].
      intros y v Hy. rewrite binders_lookup_delete in Hy.
      destruct (decide (y ∈ binders_set (self::xs))); [discriminate|].
      exact (proj2 Henv y v Hy).
    + eapply (assertions_at_lower_resources n W (fun k U => typed_value_env F k U t η X Γ E)).
      * now apply env_assertion_stable.
      * exact Henv.
      * intros k U HU V l HUV _ Hself B ts vs caller HVB Hts Hpre Hclock Hbefore Hargs.
        set (θ0 := clock_extend η (bmap bs ts)).
        set (θ := clock_bind θ0 (BNamed d) caller).
        assert (Hts' : length bs = length ts) by (symmetry; exact Hts).
        assert (Hclockθ : θ d = caller) by (unfold θ; now rewrite clock_bind_named, decide_True).
        assert (Hcompare : forall x, clock_equivalent F (θ0 x) (θ x)).
        { intros x. unfold θ. rewrite clock_bind_named.
          destruct (decide (d = x)) as [Heq|Hne]; [subst x; rewrite decide_True by reflexivity; exact Hclock|rewrite decide_False by exact Hne; apply clock_equivalent_refl]. }
        assert (Hfresh : forall x, x ∉ binders_set bs -> θ0 x = η x).
        { intros x Hx. unfold θ0. now apply variable_replacement_arrow_clock_fresh. }
        assert (Hθδ : θ0 δ = t) by now apply Hfresh.
        assert (Hb : clock_constraints F θ0 ({[(δ,d)]} ∪ Δf ∪ Δ)).
        { apply clock_constraints_union; split.
          - apply clock_constraints_union; split; [|exact Hpre].
            intros a b Hab. apply elem_of_singleton in Hab. injection Hab as -> ->.
            rewrite Hθδ. destruct Hclock as [_ Hback]. unfold reachable in *. etransitivity; eassumption.
          - eapply extend_preserves_constraints; eassumption. }
        assert (HnewΔ : clock_constraints F θ ({[(δ,d)]} ∪ Δf ∪ Δ)).
        { apply (clock_constraints_compare F _ θ0 θ); [intros x _; apply Hcompare|exact Hb]. }
        assert (HenvB : typed_value_env F k B caller η X Γ E).
        { apply typed_value_env_later with (t:=t); [exact HX|exact Hbefore|].
          eapply typed_value_env_mono; [exact HX| |exact HU]. eapply resource_extends_trans; eassumption. }
        assert (Henvθ : typed_value_env F k B caller θ X Γ E).
        { eapply typed_value_env_change; [|exact HenvB].
          intros y r Hy. apply interpret_clock_prefix; [exact HX| |constructor].
          intros z Hz. pose proof (type_env_mentions fv_typ Γ y r Hy z Hz) as Hfree.
          change (z ∈ fv_env Γ) in Hfree.
          rewrite <-(Hfresh z) by set_solver. apply Hcompare. }
        assert (Hselfη : usable_at (interpret_type F τ η X []) caller k B (VLoc l)).
        { split; [exact Hbefore|].
          apply (function_result_monotone F t sig k V B (VLoc l) HVB Hself). }
        assert (Hself_cast : type_prefix k (interpret_type F τ η X []) (interpret_type F τ θ X [])).
        { apply interpret_clock_prefix; [exact HX| |constructor].
          intros z Hz. rewrite <-(Hfresh z); [apply Hcompare|].
          cbn [τ fv_typ fv_typat] in Hz. set_solver. }
        pose proof (proj1 (usable_prefix_same k _ _ caller Hself_cast k (Nat.le_refl _) B (VLoc l)) Hselfη) as Hselfθ.
        pose proof (values_from_call_arguments F η X bs Δf d rs ρ ts caller k B vs θ
          HX Hclock Hcompare Hargs) as Hvals.
        assert (HvsLen : length xs = length vs).
        { rewrite Hlen. symmetry. exact (Forall2_length _ _ _ Hvals). }
        unfold body. rewrite close_call_bindings by (simpl; congruence).
        eapply expression_spec_post_prefix with (P := usable_at (interpret_type F ρ θ X []) caller).
        -- unfold sig. cbn [arrow_signature call_result]. fold θ0.
           eapply type_prefix_usable.
           ++ exact (proj1 (interpret_type_shape F ρ θ X [] HX)).
           ++ apply interpret_clock_prefix; [exact HX|intros x _; apply clock_equivalent_sym, Hcompare|constructor].
           ++ apply clock_equivalent_sym, Hclock.
        -- specialize (Hbody F θ X k B (extend (self::xs) (VLoc l::vs) E) HX HnewΔ).
           rewrite Hclockθ in Hbody. apply Hbody.
           eapply value_env_extend; [exact HX|simpl; congruence| |exact Henvθ].
           constructor; assumption.
Qed.

Local Lemma fork_step_invert σ α G t (v w : val) σ' α' G' T' e' :
  semantics.step σ α G (Leaf t) (Par v w) σ' α' G' T' e' ->
  exists u1 u2, G' = graph_fork G t u1 u2 /\ σ' = σ /\ α' = α /\
    T' = Node t (Leaf u1) (Leaf u2) /\
    e' = RunPar (Call v [Val VUnit]) (Call w [Val VUnit]).
Proof.
  intros Hstep. remember (Leaf t) as T eqn:HT. remember (Par v w) as src eqn:He.
  destruct Hstep.
  - destruct H.
    + destruct H; try destruct b; discriminate He.
    + inversion HT; inversion He; subst. eauto 9.
    + discriminate HT.
  - exfalso. eapply step_nonvalue; [exact Hstep|].
    destruct K; simpl in He; try discriminate; inversion He; subst; exact I.
  - discriminate HT.
  - discriminate HT.
Qed.

Local Lemma expression_spec_fork n F (W : resource n) t (v w : val) Q (Inv : world_assertion) :
  assertion_stable Inv -> Inv n W ->
  (forall k (U : resource k), Inv k U -> readable_in_view F (resource_view k U) t (locs v ∪ locs w)) ->
  (forall k (U : resource k) G u1 u2, Inv k U -> graph_fork G t u1 u2 ⊆ F ->
    expression_spec k F U (Node t (Leaf u1) (Leaf u2))
      (RunPar (Call v [Val VUnit]) (Call w [Val VUnit])) Q) ->
  expression_spec n F W (Leaf t) (Par v w) Q.
Proof.
  intros [Hdown Hmono]. induction n as [|n IH]; intros HInv Hread Hfork; [exact I|].
  split; [apply IH; [now apply Hdown|exact Hread|exact Hfork]|].
  intros U σ α G Hext Hstore HG.
  pose proof (Hmono _ _ _ Hext HInv) as HU.
  split; [apply runtime_ready_safe, ReadyFork|].
  split; [apply DELeaf; eapply readable_access; [exact Hstore|now apply Hread]|].
  split; [exact I|].
  intros σ' α' G' T' e' Hstep HG'.
  destruct (fork_step_invert _ _ _ _ _ _ _ _ _ _ _ Hstep) as (u1 & u2 & -> & -> & -> & -> & ->).
  exists (fst U). split; [apply resource_extends_refl|]. split; [exact (proj1 Hstore)|].
  eapply Hfork; [now apply Hdown|exact HG'].
Qed.

Local Lemma fork_paths (F G : graph) t u1 u2 :
  graph_fork G t u1 u2 ⊆ F -> reachable F t u1 /\ reachable F t u2.
Proof.
  intros HG. split; eapply reach_mono; [exact HG|apply graph_upd_reach; set_solver|exact HG|apply graph_upd_reach; set_solver].
Qed.

Local Lemma parallel_call F G η X δ a b ψ u1 u2 k (W : resource k) (v : val) :
  admissible_assignment F X -> b ∉ fv_typ ψ ->
  graph_fork G (η δ) u1 u2 ⊆ F ->
  usable_at (interpret_type F (TTypat (TArrow [BNamed b] {[(δ,b)]} b [TBase TBUnit] (TApp ψ b)) a) η X []) (η δ) k W v ->
  expression_spec k F W (Leaf u1) (Call v [Val VUnit])
    (usable_at (interpret_type F ψ η X [u1]) u1).
Proof.
  intros HX Hfree HG [Hbefore Hvalue].
  set (sig := arrow_signature F η X [BNamed b] {[(δ,b)]} b [TBase TBUnit] (TApp ψ b)).
  set (θ := clock_extend η (bmap [BNamed b] [u1])).
  assert (Hmap : bmap [BNamed b] [u1] = {[b:=u1]}) by reflexivity.
  assert (Hcall : θ b = u1).
  { unfold θ. rewrite Hmap. unfold clock_extend. now rewrite lookup_singleton_eq. }
  assert (Htime : clock_equivalent F (call_time sig [u1]) u1).
  { change (clock_equivalent F (θ b) u1). rewrite Hcall. apply clock_equivalent_refl. }
  assert (Hpre : call_constraints sig [u1]).
  { change (clock_constraints F θ {[(δ,b)]}).
    unfold θ. rewrite Hmap. intros x y Hxy.
    eapply reach_mono; [exact HG|].
    exact (clock_fork_constraint G η δ b u1 u2 x y Hxy). }
  destruct (fork_paths F G (η δ) u1 u2 HG) as [Hleft _].
  assert (Hreach : reachable F (η a) u1) by (unfold reachable in *; etransitivity; eassumption).
  change (function_result F (η a) sig k W v) in Hvalue.
  destruct Hvalue as (l & o & info & -> & Hl & Ho & Hbody).
  destruct (call_argument_properties F η X [BNamed b] {[(δ,b)]} b [TBase TBUnit] (TApp ψ b) [u1] u1 HX Htime)
    as [Hdown Hvisible].
  eapply expression_spec_post_prefix with (P := call_result sig [u1]).
  - change (element_prefix k (usable_at (interpret_type F ψ θ X [θ b]) (θ b))
                             (usable_at (interpret_type F ψ η X [u1]) u1)).
    rewrite Hcall. apply usable_prefix_same, interpret_clock_prefix; [exact HX| |apply list_clocks_refl].
    intros x Hx. unfold θ. rewrite clock_extend_single, clock_bind_named, decide_False by congruence.
    apply clock_equivalent_refl.
  - change (expression_spec k F W (Leaf u1) (Call (VLoc l) (Val <$> [VUnit])) (call_result sig [u1])).
    eapply (expression_spec_call k F W (η a) u1 l [VUnit] sig [u1]); try eassumption.
    + reflexivity.
    + exists l,o,info. repeat split; assumption.
    + intros U _. constructor; [split; [exact I|reflexivity]|constructor].
Qed.

Local Lemma graph_fork_swap (G : graph) t u1 u2 : graph_fork G t u1 u2 = graph_fork G t u2 u1.
Proof. unfold graph_fork. f_equal. set_solver. Qed.

Local Lemma parallel_join_value F η X ψ child parent i (V : resource (S i)) v :
  admissible_assignment F X -> reachable F parent child -> reachable F child parent ->
  usable_at (interpret_type F ψ η X [child]) child (S i) V v ->
  usable_at (interpret_type F ψ η X [parent]) parent i (fst V) v.
Proof.
  intros HX Hout Hin Hv.
  assert (Htime : clock_equivalent F child parent) by now split.
  assert (Hcast : type_prefix i (interpret_type F ψ η X [child]) (interpret_type F ψ η X [parent])).
  { apply interpret_clock_prefix; [exact HX|intros; apply clock_equivalent_refl|].
    constructor; [exact Htime|constructor]. }
  pose proof (interpret_type_shape F ψ η X [child] HX) as Hshape.
  apply (type_prefix_usable F i _ _ child parent (proj1 Hshape) Hcast Htime i (Nat.le_refl _) (fst V) v).
  exact (shape_usable_downward F _ child Hshape i V v Hv).
Qed.

Local Lemma model_parallel δ Δ Γ ψ1 ψ2 b a1 a2 e1 e2 :
  b ∉ fv_typ ψ1 -> b ∉ fv_typ ψ2 -> locs e2 = ∅ ->
  expression_typing_model δ Δ Γ e1 (TTypat (TArrow [BNamed b] {[(δ,b)]} b [TBase TBUnit] (TApp ψ1 b)) a1) ->
  expression_typing_model δ Δ Γ e2 (TTypat (TArrow [BNamed b] {[(δ,b)]} b [TBase TBUnit] (TApp ψ2 b)) a2) ->
  expression_typing_model δ Δ Γ (Par e1 e2) (TTypat (TProd (TApp ψ1 δ) (TApp ψ2 δ)) δ).
Proof.
  intros Hf1 Hf2 Hl H1 H2.
  eapply (model_binary δ Δ Γ e1 e2 _ _ _ Par CtxPar1 CtxPar2);
    try reflexivity; try eassumption.
  intros F η X n W v w HX Hv Hw.
  set (t := η δ).
  set (τ1 := TTypat (TArrow [BNamed b] {[(δ,b)]} b [TBase TBUnit] (TApp ψ1 b)) a1).
  set (τ2 := TTypat (TArrow [BNamed b] {[(δ,b)]} b [TBase TBUnit] (TApp ψ2 b)) a2).
  set (A := interpret_type F τ1 η X []).
  set (B := interpret_type F τ2 η X []).
  set (P1 := usable_at (interpret_type F ψ1 η X [t]) t).
  set (P2 := usable_at (interpret_type F ψ2 η X [t]) t).
  eapply (expression_spec_fork n F W t v w _
    (fun k U => usable_at A t k U v /\ usable_at B t k U w)).
  - apply assertion_stable_and; apply (usable_assertion_stable F); now apply interpret_type_shape.
  - now split.
  - intros k U [HV HW]. apply readable_union.
    + exact (readable_typed_value F k U t η X τ1 v HX HV).
    + exact (readable_typed_value F k U t η X τ2 w HX HW).
  - intros k U G u1 u2 [HV HW] HG.
    destruct (fork_paths F G t u1 u2 HG) as [Hleft Hright].
    pose proof (parallel_call F G η X δ a1 b ψ1 u1 u2 k U v HX Hf1 HG HV) as Hspec1.
    rewrite graph_fork_swap in HG.
    pose proof (parallel_call F G η X δ a2 b ψ2 u2 u1 k U w HX Hf2 HG HW) as Hspec2.
    eapply expression_spec_post_inclusion with (P := product_result F t P1 P2).
    + intros j Hj V u HP. split; [apply rtc_refl|exact HP].
    + eapply expression_spec_parallel; [split; [exact Hleft|now split]| |exact Hspec1|exact Hspec2].
      cbn [task_root]. apply product_join_specification.
      * apply (shape_usable_monotone F). now apply interpret_type_shape.
      * apply (shape_usable_monotone F). now apply interpret_type_shape.
      * apply (shape_usable_downward F). now apply interpret_type_shape.
      * apply (shape_usable_downward F). now apply interpret_type_shape.
      * intros i V u Hout Hin Hu. eapply parallel_join_value; eassumption.
      * intros i V u Hout Hin Hu. eapply parallel_join_value; eassumption.
Qed.

Local Lemma typed_expression_locations δ Δ Ω Γ e ρ :
  typed δ Δ Ω Γ e ρ -> locs e = ∅.
Proof. exact (proj1 typed_locations_empty δ Δ Ω Γ e ρ). Qed.

(* The expression and argument models follow the mutual typing derivations. *)
Local Lemma fundamental_typing_model :
  (forall δ Δ Ω Γ e ρ, typed δ Δ Ω Γ e ρ -> expression_typing_model δ Δ Γ e ρ) /\
  (forall δ Δ Ω Γ es rs, Forall2_typed δ Δ Ω Γ es rs -> modeled_arguments δ Δ Γ es rs).
Proof.
  apply typed_mutual_ind; intros.
  - eapply model_var; eassumption.
  - apply model_literal. reflexivity.
  - apply model_literal. reflexivity.
  - apply model_literal. reflexivity.
  - eapply model_alloc; eauto using typed_expression_locations.
  - eapply model_load; eauto using typed_expression_locations.
  - eapply model_store; eauto using typed_expression_locations.
  - eapply model_length; eassumption.
  - eapply model_cas; eauto using typed_expression_locations.
  - eapply model_type_forall; eassumption.
  - eapply model_type_apply; eassumption.
  - eapply model_fold; eassumption.
  - eapply model_unfold; eassumption.
  - eapply model_primitive; eauto using typed_expression_locations.
  - subst. eapply model_app; eassumption || reflexivity.
  - subst. eapply model_closure; eauto using typed_expression_locations.
  - eapply model_let; eauto using typed_expression_locations.
  - eapply model_if; eauto using typed_expression_locations.
  - eapply model_parallel; eauto using typed_expression_locations.
  - eapply model_pair; eauto using typed_expression_locations.
  - eapply (model_projection _ _ _ _ _ _ _ true); eassumption.
  - eapply (model_projection _ _ _ _ _ _ _ false); eassumption.
  - eapply (model_injection _ _ _ _ _ _ true); eassumption.
  - eapply (model_injection _ _ _ _ _ _ false); eassumption.
  - eapply model_case; eauto using typed_expression_locations.
  - eapply model_beta; eassumption.
  - eapply model_alpha; eassumption.
  - eapply model_alphat; eassumption.
  - eapply model_clock_judgment; eassumption.
  - eapply model_weak_constraints; eassumption.
  - eapply model_weak_value_env; eassumption.
  - eapply model_get_info; eassumption.
  - eapply model_subtime; eassumption.
  - constructor.
  - constructor; [split; eauto using typed_expression_locations|assumption].
Qed.

Theorem soundness δ e ρ :
  locs e = ∅ ->
  syntactical.typed δ ∅ ∅ ∅ e ρ ->
  always_safe_and_disentangled true e.
Proof.
  intros Hloc Htyped.
  apply (closed_typing_model_sound δ e ρ).
  eapply (proj1 fundamental_typing_model). exact Htyped.
Qed.
