Require Import Lists.ListSet.

Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions. 
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.SystemFWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.

(*----------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of ENVIRONMENTS / BARE-TYPED ENVIRONMENTS
----------------------------------------------------------------------------*)

Fixpoint concatE (g g'0 : env) : env :=
    match g'0 with
    | Empty          => g
    | (Cons  x t g') => Cons  x t (concatE g g')
    | (ConsT a k g') => ConsT a k (concatE g g')
    end.

Lemma lem_empty_concatE : forall (g : env),
  concatE Empty g = g.
Proof. induction g; simpl; try rewrite IHg; reflexivity. Qed.

Lemma lem_binds_concat : forall (g g' : env),
    Subset (binds (concatE g g')) (union (binds g) (binds g')) /\
    Subset (union (binds g) (binds g')) (binds (concatE g g')).
Proof. intros; induction g'; simpl; unfold Subset; split
  ; try (unfold Subset in IHg'; destruct IHg')
  ; try (apply subset_refl)
  ; intros
  ; try ( apply set_add_elim in H1; apply subset_union_names_add_r;
          apply set_add_intro; destruct H1; try apply H in H1; intuition )
  ; try ( apply set_add_intro; apply subset_union_names_add_r in H1; 
          apply set_add_elim in H1; destruct H1; try apply H0 in H1; intuition ).
  Qed.

Lemma lem_vbinds_concat : forall (g g' : env),
  Subset (union (vbinds g) (vbinds g')) (vbinds (concatE g g')).
Proof. intros; induction g'; simpl; try apply subset_refl;
  try apply subset_trans with (names_add x (union (vbinds g) (vbinds g')));
  try apply subset_union_names_add_r;
  try apply subset_add_both_intro; apply IHg'.
  Qed.

Lemma lem_tvbinds_concat : forall (g g' : env),
  Subset (union (tvbinds g) (tvbinds g')) (tvbinds (concatE g g')).
Proof. intros; induction g'; simpl; try apply subset_refl;
  try apply subset_trans with (names_add a (union (tvbinds g) (tvbinds g')));
  try apply subset_union_names_add_r;
  try apply subset_add_both_intro; apply IHg'.
  Qed.

Lemma lem_vbinds_cons_concat : forall (g g' : env) (x : var_name) (t_x : type),
    Subset (vbinds (concatE g g'))  (vbinds (concatE (Cons x t_x g) g')) /\
    Subset (vbinds (concatE (Cons x t_x g) g')) (names_add x (vbinds (concatE g g'))).
Proof. intros; induction g'; split; simpl;
  try apply subset_add_both_intro; try (apply subset_add_intro; apply subset_refl);
  try apply subset_refl; try apply IHg';
  apply subset_trans with (names_add x0 (names_add x (vbinds (concatE g g'))));
  try apply subset_add_both_intro; try apply subset_add_commute; apply IHg'.
  Qed.

Lemma lem_tvbinds_cons_concat : forall (g g' : env) (x : var_name) (t_x : type),
    Subset (tvbinds (concatE g g')) (tvbinds (concatE (Cons x t_x g) g')) /\
    Subset (tvbinds (concatE (Cons x t_x g) g')) (tvbinds (concatE g g')).
Proof. intros; induction g'; split; simpl;
  try apply subset_refl; try apply subset_add_both_intro; intuition. Qed.

Lemma lem_vbinds_consT_concat : forall (g g' : env) (a : var_name) (k : kind),
    Subset (vbinds (concatE g g'))  (vbinds (concatE (ConsT a k g) g')) /\
    Subset (vbinds (concatE (ConsT a k g) g')) (vbinds (concatE g g')).
Proof. intros; induction g'; split; simpl;
  try apply subset_refl; try apply subset_add_both_intro; intuition. Qed.

Lemma lem_tvbinds_consT_concat : forall (g g' : env) (a : var_name) (k : kind),
    Subset (tvbinds (concatE g g')) (tvbinds (concatE (ConsT a k g) g')) /\
    Subset (tvbinds (concatE (ConsT a k g) g')) (names_add a (tvbinds (concatE g g'))).
Proof. intros; induction g'; split; simpl;
  try apply subset_add_both_intro; try (apply subset_add_intro; apply subset_refl);
  try apply subset_refl; try apply IHg';
  apply subset_trans with (names_add a0 (names_add a (tvbinds (concatE g g'))));
  try apply subset_add_both_intro; try apply subset_add_commute; apply IHg'.
  Qed.

Lemma not_elem_concat_elim : forall (x : var_name) (g g' : env),
    ~ In x (binds (concatE g g')) -> ~ In x (binds g) /\ ~ In x (binds g').
Proof. intros; assert 
    (Subset (union (binds g) (binds g')) (binds (concatE g g'))) 
  by apply lem_binds_concat; pose proof (not_elem_subset x); 
  apply H1 in H0; try assumption. apply not_elem_union_elim in H0; assumption.
  Qed.

Lemma not_elem_concat_intro : forall (x : var_name) (g g' : env),
    ~ In x (binds g) -> ~ In x (binds g') -> ~ In x (binds (concatE g g')).
Proof. intros; pose proof (lem_binds_concat g g'); destruct H1;
  pose proof (not_elem_subset x); apply H3 with (union (binds g) (binds g'));
  apply (not_elem_union_intro x (binds g) (binds g') H) in H0; 
  try assumption.
  Qed.

Lemma unique_concat : forall (g g' : env),
    unique g -> unique g' -> intersect (binds g) (binds g') = empty
             -> unique (concatE g g').
Proof. intros; induction g'; simpl; try assumption; split;
  simpl in H0; destruct H0; simpl in H1;
  apply intersect_names_add_elim_r in H1; destruct H1;
  try (apply not_elem_concat_intro with x g g' in H3 as H4 ||
       apply not_elem_concat_intro with a g g' in H3 as H4 ; assumption);
  apply IHg' in H2; assumption.
  Qed.

Lemma concat_unique : forall (g g' : env),
    unique (concatE g g') 
        -> unique g /\ unique g' /\ intersect (binds g) (binds g') = empty.
Proof. intro g; induction g'; simpl; intros.
  - (* Empty *) repeat split; try apply intersect_empty_r; apply H.
  - (* Cons  *) repeat split; destruct H;
    apply IHg' in H0; destruct H0 as [Hg [Hg' Hi]];
    apply not_elem_concat_elim in H; destruct H;
    try apply intersect_names_add_intro_r; trivial.
  - (* ConsT *) repeat split; destruct H;
    apply IHg' in H0; destruct H0 as [Hg [Hg' Hi]];
    apply not_elem_concat_elim in H; destruct H;
    try apply intersect_names_add_intro_r; trivial.
  Qed.

Lemma lem_boundin_concat : forall (x:var_name) (t:type) (g g':env),
  bound_in x t (concatE g g') <-> bound_in x t g \/ bound_in x t g'.
Proof. intros; induction g'; simpl; intuition. Qed.

Lemma lem_boundin_weaken : forall (x:var_name) (t:type) (g g':env) (y:var_name) (t_y:type),
  bound_in x t (concatE g g') -> bound_in x t (concatE (Cons y t_y g) g').
Proof. intros; apply lem_boundin_concat; simpl; 
  apply lem_boundin_concat in H; intuition. Qed.

Lemma lem_boundin_weaken_tv : forall (x:var_name) (t:type) (g g':env) (a:var_name) (k:kind),
  bound_in x t (concatE g g') -> bound_in x t (concatE (ConsT a k g) g').
Proof. intros; apply lem_boundin_concat; simpl;
  apply lem_boundin_concat in H; intuition. Qed.

Lemma lem_tvboundin_concat : forall (a:var_name) (k:kind) (g g':env),
  tv_bound_in a k (concatE g g') <-> tv_bound_in a k g \/ tv_bound_in a k g'.
Proof. intros; induction g'; simpl; intuition. Qed.

Lemma lem_tvboundin_weaken : forall (a:var_name) (k:kind) (g g':env) (x:var_name) (t:type),
  tv_bound_in a k (concatE g g') -> tv_bound_in a k (concatE (Cons x t g) g').
Proof. intros; apply lem_tvboundin_concat; simpl; 
  apply lem_tvboundin_concat; assumption. Qed.

Lemma lem_tvboundin_weaken_tv : forall (a:var_name) (k:kind) (g g':env) (a':var_name) (k':kind),
  tv_bound_in a k (concatE g g') -> tv_bound_in a k (concatE (ConsT a' k' g) g').
Proof. intros; apply lem_tvboundin_concat; simpl;
  apply lem_tvboundin_concat in H; intuition. Qed.
  
  (* Type Erasure and Substitution *)

Lemma lem_erase_tsubFV : forall (x:var_name) (v:expr) (t:type),
    erase (tsubFV x v t) = erase t.
Proof. intros; induction t; simpl.
  - (* TRefn *) reflexivity.
  - (* TFunc *) apply f_equal2; apply IHt1 || apply IHt2.
  - (* TExis *) apply IHt2.
  - (* TPoly *) apply f_equal; apply IHt.
  Qed.

Lemma lem_erase_openT_at : forall (t:type) (j:index) (x:var_name),
    erase (openT_at j x t) = erase t.
Proof. induction t; intros; simpl.
  - (* TRefn *) reflexivity.
  - (* TFunc *) apply f_equal2; apply IHt1 || apply IHt2.
  - (* TExis *) apply IHt2.
  - (* TPoly *) apply f_equal; apply IHt.
  Qed.

Lemma lem_erase_unbind : forall (x:var_name) (t:type), erase (unbindT x t) = erase t.
Proof. intros; apply lem_erase_openT_at. Qed.

Lemma lem_erase_tsubBV_at : forall (j:index) (v:expr) (t:type), 
    erase (tsubBV_at j v t) = erase t.
Proof. intros j v t; revert j; induction t; intros; simpl.
  - (* TRefn *) reflexivity.
  - (* TFunc *) apply f_equal2; apply IHt1 || apply IHt2.
  - (* TExis *) apply IHt2.
  - (* TPoly *) apply f_equal; apply IHt.
  Qed.

Lemma lem_erase_tsubBV : forall (v:expr) (t:type), erase (tsubBV v t) = erase t.
Proof. intros. apply lem_erase_tsubBV_at. Qed.

Lemma lem_erase_push : forall (ps:preds) (t:type),
    noExists t -> erase (push ps t) = erase t.
Proof. intros ps; destruct t; simpl; intuition. Qed.

Lemma lem_erase_tsubFTV : forall (a:var_name) (t_a:type) (t:type),
    noExists t_a -> erase (tsubFTV a t_a t) = ftsubFV a (erase t_a) (erase t).
Proof. intros; induction t; simpl.
  - (* TRefn *) destruct b; try destruct (Nat.eqb a a0); simpl;
    try apply lem_erase_push; trivial.
  - (* TFunc *) apply f_equal2; apply IHt1 || apply IHt2.
  - (* TExis *) apply IHt2.
  - (* TPoly *) apply f_equal; apply IHt.
  Qed.

Lemma lem_erase_open_tvT_at : forall (t:type) (j:index) (a:var_name),
    erase (open_tvT_at j a t) = openFT_at j a (erase t).
Proof. induction t; intros; simpl.
  - (* TRefn *) destruct b; try destruct (Nat.eqb j i); simpl;
    try apply lem_erase_push; trivial.
  - (* TFunc *) apply f_equal2; apply IHt1 || apply IHt2.
  - (* TExis *) apply IHt2.
  - (* TPoly *) apply f_equal; apply IHt.
  Qed.

Lemma lem_erase_unbind_tvT : forall (a':var_name) (t:type), 
	  erase (unbind_tvT a' t) = unbindFT a' (erase t).
Proof. intros; apply lem_erase_open_tvT_at. Qed.

Lemma lem_erase_tsubBTV_at : forall (t:type) (j:index) (t_a:type),
    noExists t_a -> erase (tsubBTV_at j t_a t) = ftsubBV_at j (erase t_a) (erase t).
Proof. induction t; intros; simpl.
  - (* TRefn *) destruct b; try destruct (Nat.eqb j i); simpl;
    try apply lem_erase_push; trivial.
  - (* TFunc *) apply f_equal2; revert H; apply IHt1 || apply IHt2.
  - (* TExis *) revert H; apply IHt2.
  - (* TPoly *) apply f_equal; revert H; apply IHt.
  Qed.

Lemma lem_erase_tsubBTV : forall (t_a t:type),
    noExists t_a -> erase (tsubBTV t_a t) = ftsubBV (erase t_a) (erase t).
Proof. intros t_a t; apply lem_erase_tsubBTV_at. Qed.

    (* SYSTEM F Versions of the Above *)

Fixpoint concatF (g g'0 : fenv) : fenv :=
    match g'0 with
    | FEmpty          => g
    | (FCons  x t g') => FCons  x t (concatF g g')
    | (FConsT a k g') => FConsT a k (concatF g g')
    end.

Lemma lem_empty_concatF : forall (g : fenv),
  concatF FEmpty g = g.
Proof. induction g; simpl; try rewrite IHg; reflexivity. Qed.

Lemma lem_binds_concatF : forall (g g' : fenv),
    Subset (bindsF (concatF g g')) (union (bindsF g) (bindsF g')) /\
    Subset (union (bindsF g) (bindsF g')) (bindsF (concatF g g')).
Proof. intros; induction g'; simpl; unfold Subset; split
  ; try (unfold Subset in IHg'; destruct IHg')
  ; try (apply subset_refl)
  ; intros
  ; try ( apply set_add_elim in H1; apply subset_union_names_add_r;
          apply set_add_intro; destruct H1; try apply H in H1; intuition )
  ; try ( apply set_add_intro; apply subset_union_names_add_r in H1; 
          apply set_add_elim in H1; destruct H1; try apply H0 in H1; intuition ).
  Qed.

Lemma lem_vbinds_concatF : forall (g g' : fenv),
  Subset (union (vbindsF g) (vbindsF g')) (vbindsF (concatF g g')).
Proof. intros; induction g'; simpl; try apply subset_refl;
  try apply subset_trans with (names_add x (union (vbindsF g) (vbindsF g')));
  try apply subset_union_names_add_r;
  try apply subset_add_both_intro; apply IHg'.
  Qed.

Lemma lem_tvbinds_concatF : forall (g g' : fenv),
  Subset (union (tvbindsF g) (tvbindsF g')) (tvbindsF (concatF g g')).
Proof. intros; induction g'; simpl; try apply subset_refl;
  try apply subset_trans with (names_add a (union (tvbindsF g) (tvbindsF g')));
  try apply subset_union_names_add_r;
  try apply subset_add_both_intro; apply IHg'.
  Qed.

Lemma lem_vbinds_cons_concatF : forall (g g' : fenv) (x : var_name) (t_x : ftype),
    Subset (vbindsF (concatF g g'))  (vbindsF (concatF (FCons x t_x g) g')) /\
    Subset (vbindsF (concatF (FCons x t_x g) g')) (names_add x (vbindsF (concatF g g'))).
Proof. intros; induction g'; split; simpl;
  try apply subset_add_both_intro; try (apply subset_add_intro; apply subset_refl);
  try apply subset_refl; try apply IHg';
  apply subset_trans with (names_add x0 (names_add x (vbindsF (concatF g g'))));
  try apply subset_add_both_intro; try apply subset_add_commute; apply IHg'.
  Qed.

Lemma lem_tvbinds_cons_concatF : forall (g g' : fenv) (x : var_name) (t_x : ftype),
    Subset (tvbindsF (concatF g g')) (tvbindsF (concatF (FCons x t_x g) g')) /\
    Subset (tvbindsF (concatF (FCons x t_x g) g')) (tvbindsF (concatF g g')).
Proof. intros; induction g'; split; simpl;
  try apply subset_refl; try apply subset_add_both_intro; intuition. Qed.

Lemma lem_vbinds_consT_concatF : forall (g g' : fenv) (a : var_name) (k : kind),
    Subset (vbindsF (concatF g g'))  (vbindsF (concatF (FConsT a k g) g')) /\
    Subset (vbindsF (concatF (FConsT a k g) g')) (vbindsF (concatF g g')).
Proof. intros; induction g'; split; simpl;
  try apply subset_refl; try apply subset_add_both_intro; intuition. Qed.

Lemma lem_tvbinds_consT_concatF : forall (g g' : fenv) (a : var_name) (k : kind),
    Subset (tvbindsF (concatF g g')) (tvbindsF (concatF (FConsT a k g) g')) /\
    Subset (tvbindsF (concatF (FConsT a k g) g')) (names_add a (tvbindsF (concatF g g'))).
Proof. intros; induction g'; split; simpl;
  try apply subset_add_both_intro; try (apply subset_add_intro; apply subset_refl);
  try apply subset_refl; try apply IHg';
  apply subset_trans with (names_add a0 (names_add a (tvbindsF (concatF g g'))));
  try apply subset_add_both_intro; try apply subset_add_commute; apply IHg'.
  Qed.

Lemma not_elem_concatF_elim : forall (x : var_name) (g g' : fenv),
    ~ In x (bindsF (concatF g g')) -> ~ In x (bindsF g) /\ ~ In x (bindsF g').
Proof. intros; assert 
    (Subset (union (bindsF g) (bindsF g')) (bindsF (concatF g g'))) 
  by apply lem_binds_concatF; pose proof (not_elem_subset x); 
  apply H1 in H0; try assumption. apply not_elem_union_elim in H0; assumption.
  Qed.

Lemma not_elem_concatF_intro : forall (x : var_name) (g g' : fenv),
    ~ In x (bindsF g) -> ~ In x (bindsF g') -> ~ In x (bindsF (concatF g g')).
Proof. intros; pose proof (lem_binds_concatF g g'); destruct H1;
  pose proof (not_elem_subset x); apply H3 with (union (bindsF g) (bindsF g'));
  apply (not_elem_union_intro x (bindsF g) (bindsF g') H) in H0; 
  try assumption.
  Qed.

Lemma uniqueF_concatF : forall (g g' : fenv),
    uniqueF g -> uniqueF g' -> intersect (bindsF g) (bindsF g') = empty
              -> uniqueF (concatF g g').
Proof. intros; induction g'; simpl; try assumption; split;
  simpl in H0; destruct H0; simpl in H1;
  apply intersect_names_add_elim_r in H1; destruct H1;
  try (apply not_elem_concatF_intro with x g g' in H3 as H4 ||
       apply not_elem_concatF_intro with a g g' in H3 as H4 ; assumption);
  apply IHg' in H2; assumption.
  Qed.

Lemma lem_boundinF_concatF : forall (x:var_name) (t:ftype) (g g':fenv),
  bound_inF x t (concatF g g') <-> bound_inF x t g \/ bound_inF x t g'.
Proof. intros; induction g'; simpl; intuition. Qed.

Lemma lem_boundinF_weaken : forall (x:var_name) (t:ftype) (g g':fenv) (y:var_name) (t_y:ftype),
  bound_inF x t (concatF g g') -> bound_inF x t (concatF (FCons y t_y g) g').
Proof. intros; apply lem_boundinF_concatF; simpl; 
  apply lem_boundinF_concatF in H; intuition. Qed.

Lemma lem_boundinF_weaken_tv : forall (x:var_name) (t:ftype) (g g':fenv) (a:var_name) (k:kind),
  bound_inF x t (concatF g g') -> bound_inF x t (concatF (FConsT a k g) g').
Proof. intros; apply lem_boundinF_concatF; simpl;
  apply lem_boundinF_concatF in H; intuition. Qed.

Lemma lem_tvboundinF_concatF : forall (a:var_name) (k:kind) (g g':fenv),
  tv_bound_inF a k (concatF g g') <-> tv_bound_inF a k g \/ tv_bound_inF a k g'.
Proof. intros; induction g'; simpl; intuition. Qed.

Lemma lem_tvboundinF_weaken : forall (a:var_name) (k:kind) (g g':fenv) (x:var_name) (t:ftype),
  tv_bound_inF a k (concatF g g') -> tv_bound_inF a k (concatF (FCons x t g) g').
Proof. intros; apply lem_tvboundinF_concatF; simpl; 
  apply lem_tvboundinF_concatF; assumption. Qed.

Lemma lem_tvboundinF_weaken_tv : forall (a:var_name) (k:kind) (g g':fenv) (a':var_name) (k':kind),
  tv_bound_inF a k (concatF g g') -> tv_bound_inF a k (concatF (FConsT a' k' g) g').
Proof. intros; apply lem_tvboundinF_concatF; simpl;
  apply lem_tvboundinF_concatF in H; intuition. Qed.

Lemma lem_tvboundinF_strengthen : forall (a:var_name) (k:kind) (g g':fenv) (x:var_name) (t:ftype),
  tv_bound_inF a k (concatF (FCons x t g) g') -> tv_bound_inF a k (concatF g g').
Proof. intros; apply lem_tvboundinF_concatF in H; simpl in H;
  apply lem_tvboundinF_concatF; assumption. Qed.

Lemma lem_erase_concat : forall (g g':env), 
    erase_env (concatE g g') = concatF (erase_env g) (erase_env g').
Proof. intro g; induction g'; simpl; try reflexivity;
  apply f_equal; apply IHg'. Qed. 

Lemma binds_erase_env : forall (g : env),
    binds g = bindsF (erase_env g).
Proof. induction g; simpl; try reflexivity; apply f_equal; apply IHg. Qed.

Lemma vbinds_erase_env : forall (g : env),
    vbinds g = vbindsF (erase_env g).
Proof. induction g; simpl; try reflexivity; try apply f_equal; apply IHg. Qed.

Lemma tvbinds_erase_env : forall (g : env),
    tvbinds g = tvbindsF (erase_env g).
Proof. induction g; simpl; try reflexivity; try apply f_equal; apply IHg. Qed.

Lemma boundin_erase_env : forall (x : var_name) (t : type) (g : env),
    bound_in x t g -> bound_inF x (erase t) (erase_env g).
Proof. intros; induction g; simpl in H; try contradiction; simpl;
  try destruct H; try destruct H; try subst x0; try subst t0; intuition. 
  Qed.

Lemma tvboundin_erase_env : forall (a : var_name) (k : kind) (g : env),
    tv_bound_in a k g -> tv_bound_inF a k (erase_env g).
Proof. intros; induction g; simpl in H; try contradiction; simpl; intuition. Qed.

Lemma unique_erase_env : forall (g : env),
    unique g -> uniqueF (erase_env g).
Proof. intros; induction g; simpl; try assumption; split;
  simpl in H; destruct H; unfold in_env in H; unfold in_envF;
  rewrite binds_erase_env in H; try apply IHg; assumption. Qed.

(* -- -- -- -- -- -- -- -- -- -- -- --
   -- Substitutions in Environments --
   -- -- -- -- -- -- -- -- -- -- -- -- *)

Fixpoint esubFV (x:var_name) (v:expr) (g0:env) : env :=
    match g0 with 
    | Empty           => Empty
    | (Cons  z t_z g) => Cons z (tsubFV x v t_z) (esubFV x v g)
    | (ConsT a1  k g) => ConsT a1 k              (esubFV x v g)
    end.

Lemma esubFV_binds : forall (x:var_name) (v:expr) (g:env),
    binds (esubFV x v g) = binds g.
Proof. intros; induction g; simpl; try (rewrite IHg); reflexivity. Qed.

Lemma concat_esubFV_vbinds : forall (g:env) (x:var_name) (v:expr) (g':env),
    vbinds (concatE g (esubFV x v g')) = vbinds (concatE g g').
Proof. intros; induction g'; simpl; try (rewrite IHg'); reflexivity. Qed.

Lemma concat_esubFV_tvbinds : forall (g:env) (x:var_name) (v:expr) (g':env),
    tvbinds (concatE g (esubFV x v g')) = tvbinds (concatE g g').
Proof. intros; induction g'; simpl; try (rewrite IHg'); reflexivity. Qed.

Lemma esubFV_unique : forall (x:var_name) (v:expr) (g:env),
    unique g -> unique (esubFV x v g).
Proof. intros; induction g; simpl; simpl in H; try reflexivity;
  destruct H; split; unfold in_env; try (rewrite esubFV_binds);
  apply IHg in H0; assumption. Qed.

Lemma lem_boundin_esubFV : forall (x:var_name) (t:type) (y:var_name) (v:expr) (g:env),
    bound_in x t g -> bound_in x (tsubFV y v t) (esubFV y v g).
Proof. intros; induction g; simpl; simpl in H; try contradiction. 
  - destruct H; try destruct H; try subst x0; try subst t0.
    * left; auto.
    * right; apply IHg; assumption.
  - apply IHg; assumption.
  Qed. 

Lemma lem_tvboundin_esubFV : forall (a0:var_name) (k0:kind) (x:var_name) (v:expr) (g:env),
    tv_bound_in a0 k0 g <-> tv_bound_in a0 k0 (esubFV x v g).
Proof. intros; induction g; simpl; intuition. Qed.

Lemma lem_erase_esubFV : forall (x:var_name) (v:expr) (g:env),
    erase_env (esubFV x v g) = erase_env g.
Proof. intros x v; induction g; simpl; try reflexivity;
  try rewrite lem_erase_tsubFV; apply f_equal; apply IHg. Qed.
  

Fixpoint esubFTV (a:var_name) (t_a:type) (g0:env) : env :=
    match g0 with 
    | Empty           => Empty
    | (Cons  z t_z g) => Cons z (tsubFTV a t_a t_z) (esubFTV a t_a g)
    | (ConsT a1  k g) => ConsT a1 k                 (esubFTV a t_a g)
    end.

Lemma esubFTV_binds : forall (a:var_name) (t_a:type) (g:env),
    binds (esubFTV a t_a g) = binds g.
Proof. intros; induction g; simpl; try (rewrite IHg); reflexivity. Qed.

Lemma concat_esubFTV_vbinds : forall (g:env) (a:var_name) (t_a:type) (g':env),
    vbinds (concatE g (esubFTV a t_a g')) = vbinds (concatE g g').
Proof. intros; induction g'; simpl; try (rewrite IHg'); reflexivity. Qed.

Lemma concat_esubFTV_tvbinds : forall (g:env) (a:var_name) (t_a:type) (g':env),
    tvbinds (concatE g (esubFTV a t_a g')) = tvbinds (concatE g g').
Proof. intros; induction g'; simpl; try (rewrite IHg'); reflexivity. Qed.

Lemma esubFTV_unique : forall (a:var_name) (t_a:type) (g:env),
    unique g -> unique (esubFTV a t_a g).
Proof. intros; induction g; simpl; simpl in H; try reflexivity;
  destruct H; split; unfold in_env; try (rewrite esubFTV_binds);
  apply IHg in H0; assumption. Qed.

Lemma lem_boundin_esubFTV : forall (x:var_name) (t:type) (a:var_name) (t_a:type) (g:env),
    bound_in x t g -> bound_in x (tsubFTV a t_a t) (esubFTV a t_a g).
Proof. intros; induction g; simpl; simpl in H; try contradiction. 
  - destruct H; try destruct H; try subst x0; try subst t0.
    * left; auto.
    * right; apply IHg; assumption.
  - apply IHg; assumption.
  Qed. 

Lemma lem_tvboundin_esubFTV : forall (a0:var_name) (k0:kind) (a:var_name) (t:type) (g:env),
    tv_bound_in a0 k0 g <-> tv_bound_in a0 k0 (esubFTV a t g).
Proof. intros; induction g; simpl; intuition. Qed.

(*  -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
    -- Substitutions in Systen F Environments --
    -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- *)

Fixpoint fesubFV (a:var_name) (t_a:ftype) (g0:fenv) : fenv :=
    match g0 with 
    | FEmpty           => FEmpty
    | (FCons  z t_z g) => FCons z (ftsubFV a t_a t_z) (fesubFV a t_a g)
    | (FConsT a1  k g) => FConsT a1 k                 (fesubFV a t_a g)
    end.

Lemma fesubFV_bindsF : forall (a:var_name) (t_a:ftype) (g:fenv),
    bindsF (fesubFV a t_a g) = bindsF g.
Proof. intros; induction g; simpl; try (rewrite IHg); reflexivity. Qed.

Lemma concatF_fesubFV_vbindsF : forall (g:fenv) (a:var_name) (t_a:ftype) (g':fenv),
    vbindsF (concatF g (fesubFV a t_a g')) = vbindsF (concatF g g').
Proof. intros; induction g'; simpl; try (rewrite IHg'); reflexivity. Qed.

Lemma concatF_fesubFV_tvbindsF : forall (g:fenv) (a:var_name) (t_a:ftype) (g':fenv),
  tvbindsF (concatF g (fesubFV a t_a g')) = tvbindsF (concatF g g').
Proof. intros; induction g'; simpl; try (rewrite IHg'); reflexivity. Qed.

Lemma fesubFV_uniqueF : forall (a:var_name) (t_a:ftype) (g:fenv),
    uniqueF g -> uniqueF (fesubFV a t_a g).
Proof. intros; induction g; simpl; simpl in H; try reflexivity;
  destruct H; split; unfold in_envF; try (rewrite fesubFV_bindsF);
  apply IHg in H0; assumption. Qed.

Lemma lem_boundinF_fesubFV : forall (x:var_name) (t:ftype) (a:var_name) (t_a:ftype) (g:fenv),
    bound_inF x t g -> bound_inF x (ftsubFV a t_a t) (fesubFV a t_a g).
Proof. intros; induction g; simpl; simpl in H; try contradiction. 
  - destruct H; try destruct H; try subst x0; try subst t0.
    * left; auto.
    * right; apply IHg; assumption.
  - apply IHg; assumption.
  Qed. 

Lemma lem_tvboundinF_fesubFV : forall (a0:var_name) (k0:kind) (a:var_name) (t:ftype) (g:fenv),
    tv_bound_inF a0 k0 g <-> tv_bound_inF a0 k0 (fesubFV a t g).
Proof. intros; induction g; simpl; intuition. Qed.

Lemma lem_erase_esubFTV : forall (a:var_name) (t_a:type) (g:env),
    noExists t_a -> erase_env (esubFTV a t_a g) = fesubFV a (erase t_a) (erase_env g).
Proof. intros; induction g; simpl; try reflexivity;
  try rewrite lem_erase_tsubFTV; try apply H; try apply f_equal; apply IHg. Qed.
  
(*-----------------------------------------------------------------------------------------
----- | TECHNICAL LEMMAS relating to FREE VARIABLES and SYSTEM F judgments
-----------------------------------------------------------------------------------------*)

(* -- Lemma. All free variables in a (System F) typed expression are bound in the (System F) environment *)
Lemma lem_fv_subset_bindsF : forall (g : fenv) (e : expr) (t : ftype),
    HasFtype g e t -> Subset (fv e) (vbindsF g) /\ Subset (ftv e) (tvbindsF g).
Proof. intros g e t p_e_t. induction p_e_t; simpl; 
  try (simpl in IHp_e_t; destruct IHp_e_t as [IH1 IH2]); 
  (* Bool_constant Int_constant Pr *) try (split; apply subset_empty_l);
  (* FTVar *)    try (split; apply subset_sing_l || apply subset_empty_l; 
                      apply lem_boundin_inenvF with b; assumption );
  (* App/AppT/Ann*) try (intuition; repeat apply subset_union_intro_l; assumption).
  - (* FTAbs *) simpl in H1; 
    pose proof (fresh_varFE_not_elem  nms g e) as Hfr; destruct Hfr as [Hfv Hfr]; 
    destruct Hfr as [Hftv Hfr]; destruct Hfr as [Hnms Hg];
    apply H1 in Hnms; destruct Hnms; split.
      * apply subset_add_elim with (fresh_varFE nms g e); try assumption;
        apply subset_trans with (fv  (unbind (fresh_varFE nms g e) e));
        try (apply fv_unbind_intro); assumption.
      * apply subset_trans with (ftv (unbind (fresh_varFE nms g e) e));
        try (apply ftv_unbind_intro); assumption. 
  - (* FTAbsT *) simpl in H0.
    pose proof (fresh_varFE_not_elem  nms g e) as Hfr; destruct Hfr as [Hfv Hfr]; 
    destruct Hfr as [Hftv Hfr]; destruct Hfr as [Hnms Hg];
    apply H0 in Hnms; destruct Hnms; split.
      * apply subset_trans with (fv (unbind_tv (fresh_varFE nms g e) e));
        try (apply fv_unbind_tv_intro); assumption. 
      * apply subset_add_elim with (fresh_varFE nms g e); try assumption;
        apply subset_trans with (ftv (unbind_tv (fresh_varFE nms g e) e));
        try (apply ftv_unbind_tv_intro); assumption.
  - (* FTLet *) simpl in H0;
    pose proof (fresh_varFE_not_elem  nms g e) as Hfr; destruct Hfr as [Hfv Hfr]; 
    destruct Hfr as [Hftv Hfr]; destruct Hfr as [Hnms Hg];
    apply H0 in Hnms; destruct Hnms; split;
    apply subset_union_intro_l; try assumption.
    * apply subset_add_elim with (fresh_varFE nms g e); try assumption;
      apply subset_trans with (fv  (unbind (fresh_varFE nms g e) e));
      try (apply fv_unbind_intro); assumption.
    * apply subset_trans with (ftv (unbind (fresh_varFE nms g e) e));
      try (apply ftv_unbind_intro); assumption.
  Qed. 
  
Lemma lem_fv_bound_in_fenv : forall (g : fenv) (e : expr) (t : ftype) (x : var_name),
    HasFtype g e t -> ~ (in_envF x g) -> ~ In x (fv e) /\ ~ In x (ftv e).
Proof. intros; unfold in_envF in H0;
  pose proof (vbindsF_subset g) as Hv;
  pose proof (tvbindsF_subset g) as Htv;
  apply lem_fv_subset_bindsF in H; intuition. Qed.

Lemma lem_fvp_subset_bindsF : forall (g : fenv) (ps : preds),  
    PredicatesHaveBoolType g ps -> Subset (fvP ps) (vbindsF g) /\ Subset (ftvP ps) (tvbindsF g).
Proof. intros g ps p_ps_bl. induction p_ps_bl; simpl.
  - split; apply subset_empty_l.
  - split; apply subset_union_intro_l;
    pose proof (lem_fv_subset_bindsF g p (FTBasic TBool) H) as Hp; destruct Hp;
    destruct IHp_ps_bl; assumption.
  Qed.

Lemma lem_fvp_bound_in_fenv : forall (g : fenv) (ps : preds) (x : var_name),
    PredicatesHaveBoolType g ps -> ~ in_envF x g -> ~ In x (fvP ps) /\ ~ In x (ftvP ps).
Proof. intros; unfold in_envF in H0;
  pose proof (vbindsF_subset g) as Hv;
  pose proof (tvbindsF_subset g) as Htv;
  apply lem_fvp_subset_bindsF in H; intuition. Qed.

Lemma lem_ffreeTV_bound_in_fenv : forall (g:fenv) (t:ftype) (k:kind) (a:var_name),
    WFFT g t k -> ~ (in_envF a g) -> ~ In a (ffreeTV t).
Proof. intros g t k a p_g_t Ha; induction p_g_t; simpl.
  - (* WFFTBasic *) destruct b; intuition.
  - (* WFFTFV *) intuition; subst a0; apply lem_tvboundin_inenvF in H;
    apply tvbindsF_subset in H; intuition.
  - (* WFFTFunc *) apply not_elem_union_intro; intuition.
  - (* WFFTPoly *) pose proof (fresh_var_excludingF_not_elem nms g a);
    set (a' := fresh_var_excludingF nms g a) in H1;
    destruct H1; destruct H2.
    apply not_elem_subset with (ffreeTV (unbindFT a' t));
    try apply ffreeTV_openFT_at_intro; apply H0; 
    unfold in_envF; simpl; 
    try apply not_elem_names_add_intro; intuition.
  - (* WFFTKind *) intuition.
  Qed.