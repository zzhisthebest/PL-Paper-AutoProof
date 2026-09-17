Require Import Arith.

Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.Strengthenings. 

(* Lemmas. The set of Values is closed under substitution. *)
Lemma lem_subFV_value : forall (y:var_name) (v_y v: expr),
    isValue v_y -> isValue v -> isValue (subFV y v_y v).
Proof. intros y v_y v val_vy val_v. 
  destruct v; simpl in val_v; try contradiction;
  simpl; try (destruct (Nat.eqb y x)); simpl; assumption. Qed.

Lemma lem_subFTV_value : forall (a:var_name) (t_a: type) (v: expr),
    isValue v -> isValue (subFTV a t_a v).
Proof. intros a t_a v val_v. 
  destruct v; simpl in val_v; try contradiction;
  simpl; try (destruct (Nat.eqb y x)); simpl; assumption. Qed.

Lemma lemma_tsubFV_isMono : forall (y:var_name) (v_y:expr) (t:type),
    isMono t -> isMono (tsubFV y v_y t).
Proof. intros y v_y t mono; induction t;
  simpl in mono; try contradiction;
  simpl; intuition. Qed.

Lemma lemma_tsubFTV_isMono : forall (a:var_name) (t_a:type) (t:type),
    isMono t_a -> noExists t_a -> isMono t -> isMono (tsubFTV a t_a t).
Proof. intros a t_a t monota noexta monot; induction t;
  simpl in monot; try contradiction;
  try destruct b; simpl; try destruct (a =? a0);
  destruct t_a; simpl in monota; simpl in noexta;
  try contradiction; simpl; intuition. Qed.

Lemma lemma_tsubFV_noExists : forall (y:var_name) (v_y:expr) (t:type),
    (*isValue v_y ->*) noExists t -> noExists (tsubFV y v_y t).
Proof. intros y v_y t noex; induction t;
  simpl in noex; try contradiction;
  simpl; intuition. Qed.

Lemma lemma_tsubFTV_noExists : forall (a:var_name) (t_a:type) (t:type),
    noExists t_a -> noExists t -> noExists (tsubFTV a t_a t).
Proof. intros a t_a t noexta noext; induction t;
  simpl in noext; try contradiction;
  try destruct b; simpl; try destruct (a =? a0);
  destruct t_a; simpl in noexta; try contradiction;
  simpl; intuition. Qed.

Lemma lem_subFV_notin : ( forall (e:expr) (x:var_name) (v:expr) ,
    (*isValue v ->*) ~ In x (fv e) -> subFV x v e = e ) * ((
  forall (t:type) (x:var_name) (v:expr),
    (*isValue v ->*) ~ In x (free t) -> tsubFV x v t = t ) * (
  forall (ps:preds) (x:var_name) (v:expr),
    (*isValue v ->*) ~ In x (fvP ps) -> psubFV x v ps = ps )).
Proof.  apply ( syntax_mutind
  ( fun e:expr => forall (x:var_name) (v:expr) ,
      (*isValue v ->*) ~ In x (fv e) -> subFV x v e = e )
  ( fun t:type => forall (x:var_name) (v:expr),
      (*isValue v ->*) ~ In x (free t) -> tsubFV x v t = t)
  ( fun ps:preds => forall (x:var_name) (v:expr),
      (*isValue v ->*) ~ In x (fvP ps) -> psubFV x v ps = ps) )
  ; simpl; try reflexivity; intros
  ; (* 1 IH *) try ( apply f_equal; apply H )
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0;
      apply not_elem_union_elim in H1; destruct H1; assumption )
  ; (* FV *) try (intuition; destruct (Nat.eqb x0 x) eqn:Eq;
      (apply Nat.eqb_eq in Eq; symmetry in Eq; contradiction) 
      || reflexivity ). 
  - (* 3 IH *) apply f_equal3; apply H || apply H0 || apply H1;
      apply not_elem_union_elim in H2; destruct H2;
      apply not_elem_union_elim in H3; destruct H3; assumption.
  Qed.

Lemma lem_subFV_notin' : forall (e:expr) (x:var_name) (v:expr) ,
    ~ In x (fv e) -> subFV x v e = e.
Proof. intros; apply lem_subFV_notin; apply H.  Qed.    

Lemma lem_tsubFV_notin : forall (t:type) (x:var_name) (v:expr),
    ~ In x (free t) -> tsubFV x v t = t.
Proof. intros; apply lem_subFV_notin; apply H.  Qed.

Lemma lem_psubFV_notin : forall (ps:preds) (x:var_name) (v:expr),
    ~ In x (fvP ps) -> psubFV x v ps = ps.
Proof. intros; apply lem_subFV_notin; apply H.  Qed.


Lemma lem_subFTV_notin : (forall (e:expr) (a:var_name) (t_a:type),
    ~ In a (ftv e) -> subFTV a t_a e = e ) * ((
  forall (t:type) (a:var_name) (t_a:type),
    ~ In a (freeTV t) -> tsubFTV a t_a t = t ) * (
  forall (ps:preds) (a:var_name) (t_a:type),
    ~ In a (ftvP ps) -> psubFTV a t_a ps = ps )).
Proof. apply ( syntax_mutind 
  ( fun e : expr => forall (a:var_name) (t_a:type),
      ~ In a (ftv e) -> subFTV a t_a e = e )
  ( fun t : type => forall (a:var_name) (t_a:type),
      ~ In a (freeTV t) -> tsubFTV a t_a t = t )
  ( fun ps : preds => forall (a:var_name) (t_a:type),
      ~ In a (ftvP ps) -> psubFTV a t_a ps = ps))
  ; intros; simpl; try reflexivity
  ; (* TRefn *) try destruct b; try destruct (a =? a0) eqn:A;
                try (simpl in H0; apply not_elem_names_add_elim in H0; destruct H0);
                try (apply Nat.eqb_eq in A; contradiction)
  ; (* 1 IH *) try (f_equal; apply H; simpl in H0; trivial)
  ; (* 2 IH *) try (apply f_equal2; apply H || apply H0; simpl in H1; 
                    apply not_elem_union_elim in H1; destruct H1; trivial).
  - (* 3 IH *) apply f_equal3; apply H || apply H0 || apply H1;
      apply not_elem_union_elim in H2; destruct H2;
      apply not_elem_union_elim in H3; destruct H3; assumption.
  Qed.

Lemma lem_subFTV_notin' : forall (e:expr) (a:var_name) (t_a:type),
    ~ In a (ftv e) -> subFTV a t_a e = e.
Proof. intros; apply lem_subFTV_notin; apply H. Qed.

Lemma lem_tsubFTV_notin : forall (t:type) (a:var_name) (t_a:type),
    ~ In a (freeTV t) -> tsubFTV a t_a t = t.
Proof. intros; apply lem_subFTV_notin; apply H. Qed.  

Lemma lem_psubFTV_notin : forall (ps:preds) (a:var_name) (t_a:type),
    ~ In a (ftvP ps) -> psubFTV a t_a ps = ps.
Proof. intros; apply lem_subFTV_notin; apply H. Qed.  

(*---------------------------------------------------------------------------
-- | TECHNICAL LEMMAS: Reduction of Unbinding to (Bound) Substitution
---------------------------------------------------------------------------*)

Lemma lem_open_at_is_subBV_at :(forall (e:expr) (j:index) (y:var_name),
    open_at j y e = subBV_at j (FV y) e ) * ((
  forall (t:type) (j:index) (y:var_name),
    openT_at j y t = tsubBV_at j (FV y) t ) * (
  forall (ps:preds) (j:index) (y:var_name),
    openP_at j y ps = psubBV_at j (FV y) ps )).
Proof. apply ( syntax_mutind
  (fun e : expr => forall (j:index) (y:var_name),
      open_at j y e = subBV_at j (FV y) e )
  (fun t : type => forall (j:index) (y:var_name),
      openT_at j y t = tsubBV_at j (FV y) t )
  (fun ps : preds => forall (j:index) (y:var_name),
      openP_at j y ps = psubBV_at j (FV y) ps ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H )
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0 ).
  - (* 3 IH *) apply f_equal3; intuition.
  Qed.

Lemma lem_unbind_is_subBV : forall (y:var_name) (e:expr),
    unbind y e = subBV (FV y) e. 
Proof. intros; apply lem_open_at_is_subBV_at. Qed.

Lemma lem_unbindT_is_tsubBV : forall (y:var_name) (t:type),
    unbindT y t = tsubBV (FV y) t. 
Proof. intros; apply lem_open_at_is_subBV_at. Qed.

Lemma lem_unbindP_is_psubBV : forall (y:var_name) (ps:preds),
    unbindP y ps = psubBV (FV y) ps. 
Proof. intros; apply lem_open_at_is_subBV_at. Qed.

Lemma lem_open_tv_at_is_subBTV_at :(forall (e:expr) (j:index) (a:var_name),
    open_tv_at j a e = subBTV_at j (TRefn (FTV a) PEmpty) e ) * ((
  forall (t:type) (j:index) (a:var_name),
    open_tvT_at j a t = tsubBTV_at j (TRefn (FTV a) PEmpty) t ) * (
  forall (ps:preds) (j:index) (a:var_name),
    open_tvP_at j a ps = psubBTV_at j (TRefn (FTV a) PEmpty) ps )).
Proof. apply ( syntax_mutind
  (fun e : expr => forall (j:index) (a:var_name),
      open_tv_at j a e = subBTV_at j (TRefn (FTV a) PEmpty) e )
  (fun t : type => forall (j:index) (a:var_name),
      open_tvT_at j a t = tsubBTV_at j (TRefn (FTV a) PEmpty) t )
  (fun ps : preds => forall (j:index) (a:var_name),
      open_tvP_at j a ps = psubBTV_at j (TRefn (FTV a) PEmpty) ps ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H )
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0 ).
  - (* 3 IH *) apply f_equal3; intuition.
  - (* TRefn *) destruct b; try destruct (j =? i);
    try rewrite lem_strengthen_empty;
    apply f_equal2; reflexivity || apply H.
  Qed.

Lemma lem_unbind_tv_is_subBTV : forall (a:var_name) (e:expr),
    unbind_tv a e = subBTV (TRefn (FTV a) PEmpty) e. 
Proof. intros; apply lem_open_tv_at_is_subBTV_at. Qed.

Lemma lem_unbind_tvT_is_tsubBTV : forall (a:var_name) (t:type),
    unbind_tvT a t = tsubBTV (TRefn (FTV a) PEmpty) t. 
Proof. intros; apply lem_open_tv_at_is_subBTV_at. Qed.

Lemma lem_unbind_tvP_is_psubBTV : forall (a:var_name) (ps:preds),
    unbind_tvP a ps = psubBTV (TRefn (FTV a) PEmpty) ps. 
Proof. intros; apply lem_open_tv_at_is_subBTV_at. Qed.

(*---------------------------------------------------------------------------
-- | TECHNICAL LEMMAS: Local Closure
---------------------------------------------------------------------------*)

Lemma lem_subBV_at_lc_at : (forall (e:expr) (j:index) (v:expr) (kx:index) (ka:index),
    (*isValue v ->*) kx <= j -> isLC_at kx ka e -> subBV_at j v e = e ) * ((
  forall (t:type) (j:index) (v:expr) (kx:index) (ka:index),
    (*isValue v ->*) kx <= j -> isLCT_at kx ka t -> tsubBV_at j v t = t ) * (
  forall (ps:preds) (j:index) (v:expr) (kx:index) (ka:index),
    (*isValue v ->*) kx <= j -> isLCP_at kx ka ps -> psubBV_at j v ps = ps )).
Proof. apply ( syntax_mutind
  (fun e:expr => forall (j:index) (v:expr) (kx:index) (ka:index),
     (*isValue v ->*) kx <= j -> isLC_at kx ka e -> subBV_at j v e = e  )
  (fun t:type => forall (j:index) (v:expr) (kx:index) (ka:index),
     (*isValue v ->*) kx <= j -> isLCT_at kx ka t -> tsubBV_at j v t = t  )
  (fun ps:preds => forall (j:index) (v:expr) (kx:index) (ka:index),
     (*isValue v ->*) kx <= j -> isLCP_at kx ka ps -> psubBV_at j v ps = ps  ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; revert H1; simpl; 
                     apply H; try apply Nat.add_le_mono_r; assumption)
  ; (* 2 IH *) try ( apply f_equal2; simpl in H2; destruct H2; 
                     (revert H2; apply H) || (revert H3; apply H0); 
                     try apply Nat.add_le_mono_r; assumption ).
  - (* BV *) destruct (j =? i) eqn:J; simpl in H0.
      * apply Nat.lt_le_trans with i kx j in H0; try assumption.
        apply Nat.lt_neq in H0; apply Nat.neq_sym in H0;
        apply Nat.eqb_neq in H0. rewrite J in H0. discriminate.
      * reflexivity.
  - (* If *) apply f_equal3; simpl in H3; destruct H3; destruct H4;
    (revert H3; apply H) || (revert H4; apply H0) 
      || (revert H5; apply H1); assumption.
  - (* TRefn *) apply f_equal2; try reflexivity;
    destruct b; simpl in H1; try destruct H1; revert H2 || revert H1;
    apply H; try apply Nat.add_le_mono_r; assumption.
  Qed.
  
Lemma lem_subBV_lc : forall (v:expr) (e:expr),
    (*isValue v ->*) isLC e -> subBV v e = e.
Proof. intros; apply lem_subBV_at_lc_at with 0 0; intuition. Qed.

Lemma lem_tsubBV_lct : forall (v:expr) (t:type),
    (*isValue v ->*) isLCT t -> tsubBV v t = t.
Proof. intros; apply lem_subBV_at_lc_at with 0 0; intuition. Qed.    

Lemma lem_open_at_lc_at : (forall (e:expr) (j k:index) (x:var_name),
    isLC_at j k e -> open_at j x e = e ) * ((
  forall (t:type) (j k:index) (x:var_name),
    isLCT_at j k t -> openT_at j x t = t ) * (
  forall (ps:preds) (j k:index) (x:var_name),
    isLCP_at j k ps -> openP_at j x ps = ps  )).
Proof. repeat split; intros; pose proof lem_open_at_is_subBV_at; 
  destruct H0 as [He Ht]; destruct Ht as [Ht Hps];
  rewrite He || rewrite Ht || rewrite Hps;
  apply lem_subBV_at_lc_at with j k; simpl; intuition. Qed.

Lemma lem_unbind_lc : forall (x:var_name) (e:expr),
    isLC e -> unbind x e = e.
Proof. intros; rewrite lem_unbind_is_subBV; apply lem_subBV_lc; 
  simpl; trivial. Qed.

Lemma lem_unbindT_lct : forall (x:var_name) (t:type),
    isLCT t -> unbindT x t = t.
Proof. intros; rewrite lem_unbindT_is_tsubBV; apply lem_tsubBV_lct; 
  simpl; trivial. Qed.

Lemma lem_subBTV_at_lc_at : (forall (e:expr) (j:index) (t_a:type) (kx:index) (ka:index),
    (*noExists t_a ->*) ka <= j -> isLC_at kx ka e -> subBTV_at j t_a e = e ) * ((
  forall (t:type) (j:index) (t_a:type) (kx:index) (ka:index),
    (*noExists t_a ->*) ka <= j -> isLCT_at kx ka t -> tsubBTV_at j t_a t = t ) * (
  forall (ps:preds) (j:index) (t_a:type) (kx:index) (ka:index),
    (*noExists t_a ->*) ka <= j -> isLCP_at kx ka ps -> psubBTV_at j t_a ps = ps )).
Proof. apply ( syntax_mutind
  (fun e:expr => forall (j:index) (t_a:type) (kx:index) (ka:index),
     (*noExists t_a ->*) ka <= j -> isLC_at kx ka e -> subBTV_at j t_a e = e  )
  (fun t:type => forall (j:index) (t_a:type) (kx:index) (ka:index),
     (*noExists t_a ->*) ka <= j -> isLCT_at kx ka t -> tsubBTV_at j t_a t = t  )
  (fun ps:preds => forall (j:index) (t_a:type) (kx:index) (ka:index),
     (*noExists t_a ->*) ka <= j -> isLCP_at kx ka ps -> psubBTV_at j t_a ps = ps  ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; revert H1; simpl; 
                     apply H; try apply Nat.add_le_mono_r; assumption)
  ; (* 2 IH *) try ( apply f_equal2; simpl in H2; destruct H2; 
                     (revert H2; apply H) || (revert H3; apply H0); 
                     try apply Nat.add_le_mono_r; assumption ).
  - (* 3 IH *) apply f_equal3; simpl in H3; destruct H3; destruct H4;
    (revert H3; apply H) || (revert H4; apply H0) 
      || (revert H5; apply H1); assumption.
  - (* TRefn *) destruct b; try destruct (j =? i) eqn:J; 
    try apply f_equal2; 
    try apply H with (kx+1) ka; simpl in H1; intuition.
    apply Nat.lt_le_trans with i ka j in H2; try assumption.
    apply Nat.lt_neq in H2; apply Nat.neq_sym in H2;
    apply Nat.eqb_neq in H2; rewrite H2 in J; discriminate.
  Qed.

Lemma lem_subBTV_lc : forall (t_a:type) (e:expr),
    (*noExists t_a ->*) isLC e -> subBTV t_a e = e.
Proof. intros; apply lem_subBTV_at_lc_at with 0 0; intuition. Qed.

Lemma lem_tsubBTV_lct : forall (t_a:type) (t:type),
    (*noExists t_a ->*) isLCT t -> tsubBTV t_a t = t.
Proof. intros; apply lem_subBTV_at_lc_at with 0 0; intuition. Qed.    

Lemma lem_unbind_tv_lc : forall (a:var_name) (e:expr),
    isLC e -> unbind_tv a e = e.
Proof. intros; rewrite lem_unbind_tv_is_subBTV; apply lem_subBTV_lc; 
  simpl; trivial. Qed.

Lemma lem_unbind_tvT_lct : forall (a:var_name) (t:type),
    isLCT t -> unbind_tvT a t = t.
Proof. intros; rewrite lem_unbind_tvT_is_tsubBTV; apply lem_tsubBTV_lct; 
  simpl; trivial. Qed.

(*---------------------------------------------------------------------------
-- | BASIC PROPERTIES: Compositional Properties of SUBSTITUTION
---------------------------------------------------------------------------*)

Lemma lem_subFV_open_at : (forall (e:expr) (j:index) (y:var_name) (v:expr),
    (*isValue v ->*) ~ In y (fv e) -> subBV_at j v e = subFV y v (open_at j y e) ) * ((
  forall (t:type) (j:index) (y:var_name) (v:expr),
    (*isValue v ->*) ~ In y (free t) -> tsubBV_at j v t = tsubFV y v (openT_at j y t) ) * (
  forall (ps:preds) (j:index) (y:var_name) (v:expr),
    (*isValue v ->*) ~ In y (fvP ps) -> psubBV_at j v ps = psubFV y v (openP_at j y ps) )).
Proof. apply ( syntax_mutind
  (fun e : expr => forall (j:index) (y:var_name) (v:expr),
      (*isValue v ->*) ~ In y (fv e) -> subBV_at j v e = subFV y v (open_at j y e) )
  (fun t : type => forall (j:index) (y:var_name) (v:expr),
      (*isValue v ->*) ~ In y (free t) -> tsubBV_at j v t = tsubFV y v (openT_at j y t) )
  (fun ps : preds => forall (j:index) (y:var_name) (v:expr),
      (*isValue v ->*) ~ In y (fvP ps) -> psubBV_at j v ps = psubFV y v (openP_at j y ps) ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H; assumption)
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0;
    apply not_elem_union_elim in H1; destruct H1; assumption ).
  - (* BV *) destruct (j =? i); simpl; 
    assert (y =? y = true) by (apply Nat.eqb_eq; reflexivity); try rewrite H0;
    reflexivity.
  - (* FV *) simpl in H; intuition; apply Nat.neq_sym in H0; 
    apply Nat.eqb_neq in H0; rewrite H0; reflexivity.
  - (* If *) apply f_equal3; apply H || apply H0 || apply H1;
      apply not_elem_union_elim in H2; destruct H2;
      apply not_elem_union_elim in H3; destruct H3; assumption.
  Qed.

Lemma lem_subFV_unbind : forall (y:var_name) (v:expr) (e:expr),
    (*isValue v ->*) ~ In y (fv e) -> subBV v e = subFV y v (unbind y e).
Proof. intros; apply lem_subFV_open_at; assumption. Qed.

Lemma lem_tsubFV_unbindT : forall (y:var_name) (v:expr) (t:type),
    (*isValue v ->*) ~ In y (free t) -> tsubBV v t = tsubFV y v (unbindT y t).
Proof. intros; apply lem_subFV_open_at; assumption. Qed.

Lemma lem_psubFV_unbindP : forall (y:var_name) (v:expr) (ps:preds),
    (*isValue v ->*) ~ In y (fvP ps) -> psubBV v ps = psubFV y v (unbindP y ps).
Proof. intros; apply lem_subFV_open_at; assumption. Qed.

Lemma lem_subFTV_open_tv_at : (forall (e:expr) (j:index) (a:var_name) (t_a:type),
    (*noExists t_a ->*) ~ In a (ftv e) 
                 -> subBTV_at j t_a e = subFTV a t_a (open_tv_at j a e) ) * ((
  forall (t:type) (j:index) (a:var_name) (t_a:type),
    (*noExists t_a ->*) ~ In a (freeTV t) 
                 -> tsubBTV_at j t_a t = tsubFTV a t_a (open_tvT_at j a t) ) * (
  forall (ps:preds) (j:index) (a:var_name) (t_a:type),
    (*noExists t_a ->*) ~ In a (ftvP ps) 
                 -> psubBTV_at j t_a ps = psubFTV a t_a (open_tvP_at j a ps) )).
Proof. apply ( syntax_mutind
  (fun e : expr => forall (j:index) (a:var_name) (t_a:type),
      (*noExists t_a ->*) ~ In a (ftv e) 
                   -> subBTV_at j t_a e = subFTV a t_a (open_tv_at j a e))
  (fun t : type => forall (j:index) (a:var_name) (t_a:type),
      (*noExists t_a ->*) ~ In a (freeTV t) 
                   -> tsubBTV_at j t_a t = tsubFTV a t_a (open_tvT_at j a t))
  (fun ps: preds => forall (j:index) (a:var_name) (t_a:type),
      (*noExists t_a ->*) ~ In a (ftvP ps) 
                   -> psubBTV_at j t_a ps = psubFTV a t_a (open_tvP_at j a ps)))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H; assumption)
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0;
    apply not_elem_union_elim in H1; destruct H1; assumption ).
  - (* If *) apply f_equal3; apply H || apply H0 || apply H1;
      apply not_elem_union_elim in H2; destruct H2;
      apply not_elem_union_elim in H3; destruct H3; assumption.
  - (* TRefn *) destruct b; simpl;
    try ( apply f_equal; apply H; assumption).
    * (* BTV *) destruct (j =? i); simpl;
      assert (a =? a = true) by (apply Nat.eqb_eq; reflexivity); try rewrite H1;
      apply f_equal2; try apply H; intuition.
    * (* FTV *) simpl in H0; apply not_elem_names_add_elim in H0;
      destruct H0; apply Nat.eqb_neq in H0; rewrite H0;
      apply f_equal2; try apply H; intuition.
  Qed.

Lemma lem_subFTV_unbind_tv : forall (a:var_name) (t_a:type) (e:expr),
    (*noExists t_a ->*) ~ In a (ftv e) -> subBTV t_a e = subFTV a t_a (unbind_tv a e).
Proof. intros; apply lem_subFTV_open_tv_at; assumption. Qed.

Lemma lem_tsubFTV_unbind_tvT : forall (a:var_name) (t_a:type) (t:type),
    (*noExists t_a ->*) ~ In a (freeTV t) -> tsubBTV t_a t = tsubFTV a t_a (unbind_tvT a t).
Proof. intros; apply lem_subFTV_open_tv_at; assumption. Qed.

Lemma lem_psubFTV_unbind_tvP : forall (a:var_name) (t_a:type) (ps:preds),
    (*noExists t_a ->*) ~ In a (ftvP ps) -> psubBTV t_a ps = psubFTV a t_a (unbind_tvP a ps).
Proof. intros; apply lem_subFTV_open_tv_at; assumption. Qed.

(*---------------------------------------------------------------------------
-- | BASIC PROPERTIES: Commutative Properties of SUBSTITUTION with Push
---------------------------------------------------------------------------*)

Lemma lem_push_empty : forall (t_a:type),
    noExists t_a -> push PEmpty t_a = t_a.
Proof. intros; destruct t_a; simpl in H; try contradiction;
  simpl; reflexivity. Qed.

Lemma lem_push_strengthen : forall (ps:preds) (rs:preds) (t:type),
    noExists t -> push (strengthen ps rs) t = push ps (push rs t).
Proof. intros; destruct t; simpl in H; try contradiction;
  simpl; try rewrite lem_strengthen_assoc; reflexivity. Qed.

Lemma lem_subFV_push : forall (x:var_name) (v:expr) (ps:preds) (t:type), 
    noExists t 
        -> tsubFV x v (push ps t) = push (psubFV x v ps) (tsubFV x v t).
Proof. intros; destruct t; simpl in H; try contradiction;
  simpl; try rewrite lem_psubFV_strengthen; reflexivity. Qed.

Lemma lem_subBV_at_push : forall (j:index) (v:expr) (ps:preds) (t:type),
    (*isValue v ->*) noExists t
        -> tsubBV_at j v (push ps t) = push (psubBV_at (j+1) v ps) (tsubBV_at j v t).
Proof. intros; destruct t; simpl in H; try contradiction;
  simpl; try rewrite lem_psubBV_at_strengthen; reflexivity. Qed.

Lemma lem_subFTV_push : forall (a:var_name) (t_a:type) (ps:preds) (t:type),
    noExists t_a -> noExists t
        -> tsubFTV a t_a (push ps t) = push (psubFTV a t_a ps) (tsubFTV a t_a t).
Proof. intros; destruct t; simpl in H0; try contradiction;
  try destruct b; simpl; try destruct (a =? a0); simpl;
  try rewrite lem_psubFTV_strengthen;
  try rewrite lem_push_strengthen;
  reflexivity || assumption. Qed.

Lemma lem_subBTV_at_push : forall (j:index) (t_a:type) (ps:preds) (t:type),
    noExists t_a -> noExists t
       -> tsubBTV_at j t_a (push ps t) = push (psubBTV_at j t_a ps) (tsubBTV_at j t_a t).
Proof. intros; destruct t; simpl in H0; try contradiction;
  try destruct b; simpl; try destruct (j =? i); simpl;
  try rewrite lem_psubBTV_at_strengthen;
  try rewrite lem_push_strengthen;
  reflexivity || assumption. Qed.

(*---------------------------------------------------------------------------
-- | BASIC PROPERTIES: Commutative Properties of SUBSTITUTION with Itself
---------------------------------------------------------------------------*)

Lemma lem_commute_subFV_subBV_at : (forall (e:expr) (j:index) (v:expr) (y:var_name) (v_y:expr),
    (*isValue v -> isValue v_y ->*) isLC v_y 
      -> subFV y v_y (subBV_at j v e) = subBV_at j (subFV y v_y v) (subFV y v_y e) ) * ((
  forall (t:type) (j:index) (v:expr) (y:var_name) (v_y:expr),
    (*isValue v -> isValue v_y ->*) isLC v_y 
      -> tsubFV y v_y (tsubBV_at j v t) = tsubBV_at j (subFV y v_y v) (tsubFV y v_y t) ) * (
  forall (ps:preds) (j:index) (v:expr) (y:var_name) (v_y:expr),
    (*isValue v -> isValue v_y ->*) isLC v_y 
      -> psubFV y v_y (psubBV_at j v ps) = psubBV_at j (subFV y v_y v) (psubFV y v_y ps) )).
Proof. apply ( syntax_mutind
  (fun e : expr => forall (j:index) (v:expr) (y:var_name) (v_y:expr),
    (*isValue v -> isValue v_y ->*) isLC v_y 
      -> subFV y v_y (subBV_at j v e) = subBV_at j (subFV y v_y v) (subFV y v_y e) )
  (fun t : type => forall (j:index) (v:expr) (y:var_name) (v_y:expr),
    (*isValue v -> isValue v_y ->*) isLC v_y 
      -> tsubFV y v_y (tsubBV_at j v t) = tsubBV_at j (subFV y v_y v) (tsubFV y v_y t) )
  (fun ps : preds => forall (j:index) (v:expr) (y:var_name) (v_y:expr),
    (*isValue v -> isValue v_y ->*) isLC v_y 
      -> psubFV y v_y (psubBV_at j v ps) = psubBV_at j (subFV y v_y v) (psubFV y v_y ps) ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H; assumption)
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0; assumption ).
  - (* BV *) destruct (j =? i); simpl; reflexivity.
  - (* FV *) destruct (y =? x); try reflexivity; symmetry.
    apply lem_subBV_at_lc_at with 0 0; auto with *. 
  - (* If *) rewrite H; try rewrite H0; try rewrite H1; trivial.
  Qed.
    
Lemma lem_commute_subFV_subBV : forall (v:expr) (y:var_name) (v_y:expr) (e:expr),
    (*isValue v -> isValue v_y ->*) isLC v_y 
      -> subFV y v_y (subBV v e) = subBV (subFV y v_y v) (subFV y v_y e).
Proof. intros. apply lem_commute_subFV_subBV_at; assumption. Qed.
      
Lemma lem_commute_tsubFV_tsubBV : forall (v:expr) (y:var_name) (v_y:expr) (t:type),
    (*isValue v -> isValue v_y ->*) isLC v_y 
      -> tsubFV y v_y (tsubBV v t) = tsubBV (subFV y v_y v) (tsubFV y v_y t).
Proof. intros. apply lem_commute_subFV_subBV_at; assumption. Qed.

Lemma lem_commute_psubFV_psubBV : forall (v:expr) (y:var_name) (v_y:expr) (ps:preds),
    (*isValue v -> isValue v_y ->*) isLC v_y 
      -> psubFV y v_y (psubBV v ps) = psubBV (subFV y v_y v) (psubFV y v_y ps).
Proof. intros. apply lem_commute_subFV_subBV_at; assumption. Qed.

Lemma lem_commute_subFV_unbind : forall (y:var_name) (x:var_name) (v:expr) (e:expr),
    x <> y (*-> isValue v*) -> isLC v 
      -> subFV x v (unbind y e) = unbind y (subFV x v e).
Proof. intros; repeat rewrite lem_unbind_is_subBV.
  apply Nat.eqb_neq in H.
  assert (subFV x v (FV y) = FV y) as H2 by (simpl; rewrite H; reflexivity).
  rewrite lem_commute_subFV_subBV; try rewrite H2; simpl; trivial.
  Qed.

Lemma lem_commute_tsubFV_unbindT : forall (y:var_name) (x:var_name) (v:expr) (t:type),
  x <> y (*-> isValue v*) -> isLC v 
    -> tsubFV x v (unbindT y t) = unbindT y (tsubFV x v t).
Proof. intros; repeat rewrite lem_unbindT_is_tsubBV.
  apply Nat.eqb_neq in H.
  assert (subFV x v (FV y) = FV y) as H2 by (simpl; rewrite H; reflexivity).
  rewrite lem_commute_tsubFV_tsubBV; try rewrite H2; simpl; trivial.
  Qed.

Lemma lem_commute_psubFV_unbindP : forall (y:var_name) (x:var_name) (v:expr) (ps:preds),
  x <> y (*-> isValue v*) -> isLC v 
    -> psubFV x v (unbindP y ps) = unbindP y (psubFV x v ps).
Proof. intros; repeat rewrite lem_unbindP_is_psubBV.
  apply Nat.eqb_neq in H.
  assert (subFV x v (FV y) = FV y) as H2 by (simpl; rewrite H; reflexivity).
  rewrite lem_commute_psubFV_psubBV; try rewrite H2; simpl; trivial.
  Qed.


Lemma lem_commute_subFV_subBTV_at : (forall (e:expr) (j:index) (t_a:type) (y:var_name) (v_y:expr),
    noExists t_a -> (*isValue v_y ->*) isLC v_y 
      -> subFV y v_y (subBTV_at j t_a e) = subBTV_at j (tsubFV y v_y t_a) (subFV y v_y e) ) * ((
  forall (t:type) (j:index) (t_a:type) (y:var_name) (v_y:expr),
    noExists t_a -> (*isValue v_y ->*) isLC v_y 
      -> tsubFV y v_y (tsubBTV_at j t_a t) = tsubBTV_at j (tsubFV y v_y t_a) (tsubFV y v_y t) ) * (
  forall (ps:preds) (j:index) (t_a:type) (y:var_name) (v_y:expr),
    noExists t_a -> (*isValue v_y ->*) isLC v_y 
      -> psubFV y v_y (psubBTV_at j t_a ps) = psubBTV_at j (tsubFV y v_y t_a) (psubFV y v_y ps) )).
Proof. apply ( syntax_mutind
  (fun e : expr => forall (j:index) (t_a:type) (y:var_name) (v_y:expr),
    noExists t_a -> (*isValue v_y ->*) isLC v_y 
      -> subFV y v_y (subBTV_at j t_a e) = subBTV_at j (tsubFV y v_y t_a) (subFV y v_y e) )
  (fun t : type => forall (j:index) (t_a:type) (y:var_name) (v_y:expr),
    noExists t_a -> (*isValue v_y ->*) isLC v_y 
      -> tsubFV y v_y (tsubBTV_at j t_a t) = tsubBTV_at j (tsubFV y v_y t_a) (tsubFV y v_y t) )
  (fun ps : preds => forall (j:index) (t_a:type) (y:var_name) (v_y:expr),
    noExists t_a -> (*isValue v_y ->*) isLC v_y 
      -> psubFV y v_y (psubBTV_at j t_a ps) = psubBTV_at j (tsubFV y v_y t_a) (psubFV y v_y ps) ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H; assumption)
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0; assumption ).
  - (* FV *) destruct (y =? x); try reflexivity. 
    apply lemma_tsubFV_noExists with y v_y t_a in H; try assumption; symmetry.
    apply lem_subBTV_at_lc_at with 0 0; auto with *.
  - (* If *) rewrite H; try rewrite H0; try rewrite H1; trivial.
  - (* TRefn *) destruct b; try destruct (j =? i) eqn:J; simpl;
    try apply f_equal; try apply H; try assumption.
    * (* BTV j *) rewrite <- H; try rewrite lem_subFV_push; trivial.
  Qed.

Lemma lem_commute_subFV_subBTV : forall (t_a:type) (y:var_name) (v_y:expr) (e:expr),
    noExists t_a (*-> isValue v_y*) -> isLC v_y 
        -> subFV y v_y (subBTV t_a e) = subBTV (tsubFV y v_y t_a) (subFV y v_y e).
Proof. intros; apply lem_commute_subFV_subBTV_at; assumption. Qed.

Lemma lem_commute_tsubFV_tsubBTV : forall (t_a:type) (y:var_name) (v_y:expr) (t:type),
    noExists t_a (*-> isValue v_y*) -> isLC v_y 
        -> tsubFV y v_y (tsubBTV t_a t) = tsubBTV (tsubFV y v_y t_a) (tsubFV y v_y t).
Proof. intros; apply lem_commute_subFV_subBTV_at; assumption. Qed.

Lemma lem_commute_psubFV_psubBTV : forall (t_a:type) (y:var_name) (v_y:expr) (ps:preds),
    noExists t_a (*-> isValue v_y*) -> isLC v_y 
        -> psubFV y v_y (psubBTV t_a ps) = psubBTV (tsubFV y v_y t_a) (psubFV y v_y ps).
Proof. intros; apply lem_commute_subFV_subBTV_at; assumption. Qed.

Lemma lem_commute_subFV_unbind_tv : forall (a:var_name) (x:var_name) (v:expr) (e:expr),
    x <> a (*-> isValue v*) -> isLC v 
        -> subFV x v (unbind_tv a e) = unbind_tv a (subFV x v e).
Proof. intros; repeat rewrite lem_unbind_tv_is_subBTV.
  apply Nat.eqb_neq in H.
  assert (tsubFV x v (TRefn (FTV a) PEmpty) = (TRefn (FTV a) PEmpty)) by (reflexivity).
  rewrite lem_commute_subFV_subBTV; try rewrite H2; simpl; trivial.
  Qed. 

Lemma lem_commute_tsubFV_unbind_tvT : forall (a:var_name) (x:var_name) (v:expr) (t:type),
    x <> a (*-> isValue v*) -> isLC v 
        -> tsubFV x v (unbind_tvT a t) = unbind_tvT a (tsubFV x v t).
Proof. intros; repeat rewrite lem_unbind_tvT_is_tsubBTV.
  apply Nat.eqb_neq in H.
  assert (tsubFV x v (TRefn (FTV a) PEmpty) = (TRefn (FTV a) PEmpty)) by (reflexivity).
  rewrite lem_commute_tsubFV_tsubBTV; try rewrite H2; simpl; trivial.
  Qed. 

Lemma lem_commute_psubFV_unbind_tvP : forall (a:var_name) (x:var_name) (v:expr) (ps:preds),
    x <> a (*-> isValue v*) -> isLC v 
        -> psubFV x v (unbind_tvP a ps) = unbind_tvP a (psubFV x v ps).
Proof. intros; repeat rewrite lem_unbind_tvP_is_psubBTV.
  apply Nat.eqb_neq in H.
  assert (tsubFV x v (TRefn (FTV a) PEmpty) = (TRefn (FTV a) PEmpty)) by (reflexivity).
  rewrite lem_commute_psubFV_psubBTV; try rewrite H2; simpl; trivial.
  Qed.   


Lemma lem_commute_subFTV_subBV_at : (forall (e:expr) (j:index) (v:expr) (a:var_name) (t_a:type),
    (*isValue v ->*) noExists t_a -> isLCT t_a
      -> subFTV a t_a (subBV_at j v e) = subBV_at j (subFTV a t_a v) (subFTV a t_a e) ) * ((
  forall (t:type) (j:index) (v:expr) (a:var_name) (t_a:type),
    (*isValue v ->*) noExists t_a -> isLCT t_a 
      -> tsubFTV a t_a (tsubBV_at j v t) = tsubBV_at j (subFTV a t_a v) (tsubFTV a t_a t) ) * (
  forall (ps:preds) (j:index) (v:expr) (a:var_name) (t_a:type),
    (*isValue v ->*) noExists t_a -> isLCT t_a
      -> psubFTV a t_a (psubBV_at j v ps) = psubBV_at j (subFTV a t_a v) (psubFTV a t_a ps) )).
Proof. apply ( syntax_mutind
  (fun e : expr => forall (j:index) (v:expr) (a:var_name) (t_a:type),
    (*isValue v ->*) noExists t_a -> isLCT t_a
      -> subFTV a t_a (subBV_at j v e) = subBV_at j (subFTV a t_a v) (subFTV a t_a e) )
  (fun t : type => forall (j:index) (v:expr) (a:var_name) (t_a:type),
    (*isValue v ->*) noExists t_a -> isLCT t_a
      -> tsubFTV a t_a (tsubBV_at j v t) = tsubBV_at j (subFTV a t_a v) (tsubFTV a t_a t) )
  (fun ps : preds => forall (j:index) (v:expr) (a:var_name) (t_a:type),
    (*isValue v ->*) noExists t_a -> isLCT t_a
      -> psubFTV a t_a (psubBV_at j v ps) = psubBV_at j (subFTV a t_a v) (psubFTV a t_a ps) ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H; assumption)
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0; assumption ).
  - (* BV *) destruct (j =? i); reflexivity.
  - (* If *) apply f_equal3; apply H || apply H0 || apply H1; assumption.
  - (* TRefn *) destruct b; try destruct (a =? a0) eqn:A; simpl;
    try apply f_equal; try apply H; try assumption.
    (* FTV a *) symmetry; rewrite lem_subBV_at_push; try rewrite <- H;
      try apply f_equal; try apply lem_subBV_at_lc_at with 0 0; auto with *.
  Qed.
    
Lemma lem_commute_subFTV_subBV : forall (v:expr) (a:var_name) (t_a:type) (e:expr),
    (*isValue v ->*) noExists t_a -> isLCT t_a 
        -> subFTV a t_a (subBV v e) = subBV (subFTV a t_a v) (subFTV a t_a e).
Proof. intros; apply lem_commute_subFTV_subBV_at; assumption. Qed.

Lemma lem_commute_tsubFTV_tsubBV : forall (v:expr) (a:var_name) (t_a:type) (t:type),
    (*isValue v ->*) noExists t_a -> isLCT t_a 
        -> tsubFTV a t_a (tsubBV v t) = tsubBV (subFTV a t_a v) (tsubFTV a t_a t).
Proof. intros; apply lem_commute_subFTV_subBV_at; assumption. Qed.

Lemma lem_commute_psubFTV_psubBV : forall (v:expr) (a:var_name) (t_a:type) (ps:preds),
    (*isValue v ->*) noExists t_a -> isLCT t_a 
        -> psubFTV a t_a (psubBV v ps) = psubBV (subFTV a t_a v) (psubFTV a t_a ps).
Proof. intros; apply lem_commute_subFTV_subBV_at; assumption. Qed.

Lemma lem_commute_subFTV_unbind : forall (x:var_name) (a:var_name) (t_a:type) (e:expr),
    a <> x -> noExists t_a -> isLCT t_a 
        -> subFTV a t_a (unbind x e) = unbind x (subFTV a t_a e).
Proof. intros; repeat rewrite lem_unbind_is_subBV.
  apply Nat.eqb_neq in H.
  assert (subFTV a t_a (FV x) = (FV x)) by (reflexivity).
  rewrite lem_commute_subFTV_subBV; try rewrite H2; simpl; trivial.
  Qed. 

Lemma lem_commute_tsubFTV_unbindT : forall (x:var_name) (a:var_name) (t_a:type) (t:type),
    a <> x -> noExists t_a -> isLCT t_a 
        -> tsubFTV a t_a (unbindT x t) = unbindT x (tsubFTV a t_a t).
Proof. intros; repeat rewrite lem_unbindT_is_tsubBV.
  apply Nat.eqb_neq in H.
  assert (subFTV a t_a (FV x) = (FV x)) by (reflexivity).
  rewrite lem_commute_tsubFTV_tsubBV; try rewrite H2; simpl; trivial.
  Qed. 

Lemma lem_commute_psubFTV_unbindP : forall (x:var_name) (a:var_name) (t_a:type) (ps:preds),
    a <> x -> noExists t_a -> isLCT t_a 
        -> psubFTV a t_a (unbindP x ps) = unbindP x (psubFTV a t_a ps).
Proof. intros; repeat rewrite lem_unbindP_is_psubBV.
  apply Nat.eqb_neq in H.
  assert (subFTV a t_a (FV x) = (FV x)) by (reflexivity).
  rewrite lem_commute_psubFTV_psubBV; try rewrite H2; simpl; trivial.
  Qed. 


Lemma lem_commute_subFTV_subBTV_at : (forall (e:expr) (j:index) (t_j:type) (a:var_name) (t_a:type),
    noExists t_j -> noExists t_a -> isLCT t_a  
      -> subFTV a t_a (subBTV_at j t_j e) = subBTV_at j (tsubFTV a t_a t_j) (subFTV a t_a e) ) * ((
  forall (t:type) (j:index) (t_j:type) (a:var_name) (t_a:type),
    noExists t_j -> noExists t_a -> isLCT t_a 
      -> tsubFTV a t_a (tsubBTV_at j t_j t) = tsubBTV_at j (tsubFTV a t_a t_j) (tsubFTV a t_a t) ) * (
  forall (ps:preds) (j:index) (t_j:type) (a:var_name) (t_a:type),
    noExists t_j -> noExists t_a -> isLCT t_a 
      -> psubFTV a t_a (psubBTV_at j t_j ps) = psubBTV_at j (tsubFTV a t_a t_j) (psubFTV a t_a ps) )).
Proof. apply ( syntax_mutind
  (fun e : expr => forall (j:index) (t_j:type) (a:var_name) (t_a:type),
    noExists t_j -> noExists t_a -> isLCT t_a 
      -> subFTV a t_a (subBTV_at j t_j e) = subBTV_at j (tsubFTV a t_a t_j) (subFTV a t_a e) )
  (fun t : type => forall (j:index) (t_j:type) (a:var_name) (t_a:type),
    noExists t_j -> noExists t_a -> isLCT t_a 
      -> tsubFTV a t_a (tsubBTV_at j t_j t) = tsubBTV_at j (tsubFTV a t_a t_j) (tsubFTV a t_a t) )
  (fun ps : preds => forall (j:index) (t_j:type) (a:var_name) (t_a:type),
    noExists t_j -> noExists t_a -> isLCT t_a 
      -> psubFTV a t_a (psubBTV_at j t_j ps) = psubBTV_at j (tsubFTV a t_a t_j) (psubFTV a t_a ps) ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H; assumption)
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0; assumption ).
  - (* If *) apply f_equal3; apply H || apply H0 || apply H1; assumption.
  - (* TRefn *) destruct b eqn:B; simpl; try destruct (j =? i); try destruct (a =? a0); 
    simpl; try apply f_equal; try apply H; try assumption.
    * (* BTV j *) symmetry; rewrite lem_subFTV_push; try rewrite <- H; trivial.
    * (* FTV a *) symmetry; rewrite lem_subBTV_at_push; try rewrite <- H;
      try apply f_equal; try apply lem_subBTV_at_lc_at with 0 0;
      try apply lemma_tsubFTV_noExists; auto with *.
  Qed.
  
Lemma lem_commute_subFTV_subBTV : forall (t':type) (a:var_name) (t_a:type) (e:expr),
    noExists t' -> noExists t_a -> isLCT t_a 
        -> subFTV a t_a (subBTV t' e) = subBTV (tsubFTV a t_a t') (subFTV a t_a e).
Proof. intros; apply lem_commute_subFTV_subBTV_at; assumption. Qed.

Lemma lem_commute_tsubFTV_tsubBTV : forall (t':type) (a:var_name) (t_a:type) (t:type),
    noExists t' -> noExists t_a -> isLCT t_a 
        -> tsubFTV a t_a (tsubBTV t' t) = tsubBTV (tsubFTV a t_a t') (tsubFTV a t_a t).
Proof. intros; apply lem_commute_subFTV_subBTV_at; assumption. Qed.

Lemma lem_commute_psubFTV_psubBTV : forall (t':type) (a:var_name) (t_a:type) (ps:preds),
    noExists t' -> noExists t_a -> isLCT t_a 
        -> psubFTV a t_a (psubBTV t' ps) = psubBTV (tsubFTV a t_a t') (psubFTV a t_a ps).
Proof. intros; apply lem_commute_subFTV_subBTV_at; assumption. Qed.

Lemma lem_commute_subFTV_unbind_tv : forall (a':var_name) (a:var_name) (t_a:type) (e:expr),
    a <> a' -> noExists t_a -> isLCT t_a
        -> subFTV a t_a (unbind_tv a' e) = unbind_tv a' (subFTV a t_a e).
Proof. intros; repeat rewrite lem_unbind_tv_is_subBTV.
  apply Nat.eqb_neq in H.
  assert (tsubFTV a t_a (TRefn (FTV a') PEmpty) = (TRefn (FTV a') PEmpty)) 
    by (simpl; rewrite H; reflexivity).
  rewrite lem_commute_subFTV_subBTV; try rewrite H2; simpl; trivial.
  Qed. 

Lemma lem_commute_tsubFTV_unbind_tvT : forall (a':var_name) (a:var_name) (t_a:type) (t:type),
    a <> a' -> noExists t_a -> isLCT t_a
        -> tsubFTV a t_a (unbind_tvT a' t) = unbind_tvT a' (tsubFTV a t_a t).
Proof. intros; repeat rewrite lem_unbind_tvT_is_tsubBTV.
  apply Nat.eqb_neq in H.
  assert (tsubFTV a t_a (TRefn (FTV a') PEmpty) = (TRefn (FTV a') PEmpty)) 
    by (simpl; rewrite H; reflexivity).
  rewrite lem_commute_tsubFTV_tsubBTV; try rewrite H2; simpl; trivial.
  Qed. 

Lemma lem_commute_psubFTV_unbind_tvP : forall (a':var_name) (a:var_name) (t_a:type) (ps:preds),
    a <> a' -> noExists t_a -> isLCT t_a
        -> psubFTV a t_a (unbind_tvP a' ps) = unbind_tvP a' (psubFTV a t_a ps).
Proof. intros; repeat rewrite lem_unbind_tvP_is_psubBTV.
  apply Nat.eqb_neq in H.
  assert (tsubFTV a t_a (TRefn (FTV a') PEmpty) = (TRefn (FTV a') PEmpty)) 
    by (simpl; rewrite H; reflexivity).
  rewrite lem_commute_psubFTV_psubBTV; try rewrite H2; simpl; trivial.
  Qed. 

(*---------------------------------------------------------------------------------------
-- | BASIC PROPERTIES: Properties of SUBSTITUTION for TYPE VARIABLES in SYSTEM F TYPES
---------------------------------------------------------------------------------------*)

Lemma lem_ftsubFV_notin : forall (a:var_name) (t_a:ftype) (t:ftype),
    ~ In a (ffreeTV t) ->  ftsubFV a t_a t = t.
Proof. intros; induction t; simpl.
  - destruct b; try destruct (a =? a0) eqn:A; intuition. 
    apply Nat.eqb_eq in A; symmetry in A; subst a0; simpl in H; intuition.
  - simpl in H; apply not_elem_union_elim in H; destruct H;
    rewrite IHt1; try rewrite IHt2; intuition. 
  - simpl in H; rewrite IHt; intuition.
  Qed.

Lemma lem_openFT_at_is_ftsubBV_at : forall (t:ftype) (j:index) (a:var_name),
    openFT_at j a t = ftsubBV_at j (FTBasic (FTV a)) t.
Proof. intro t; induction t; intros; simpl.
  - (* FTBasic *) destruct b; try destruct (j =? i); reflexivity.
  - (* FTFunc *) apply f_equal2; apply IHt1 || apply IHt2.
  - (* FTPoly *) apply f_equal; apply IHt.
  Qed.

Lemma lem_islcft_at_ftsubBV_at : forall (t:ftype) (j:index) (t_j:ftype) (k:index),
    k <= j -> isLCFT_at k t ->  ftsubBV_at j t_j t = t. 
Proof. intros t; induction t; intros; simpl.
  - (* FTBasic *) destruct b; simpl in H0; try reflexivity. 
    apply Nat.lt_le_trans with i k j in H0; try assumption. 
    apply Nat.lt_neq in H0; apply Nat.neq_sym in H0;
    apply Nat.eqb_neq in H0; rewrite H0; reflexivity.
  - (* FTFunc *) simpl in H0; destruct H0.  
    apply (IHt1 j t_j k H) in H0; apply (IHt2 j t_j k H) in H1; 
    rewrite H0; rewrite H1; reflexivity.
  - (* FTPoly *) simpl in H0. apply Nat.add_le_mono_r with k0 j 1 in H.
    apply (IHt (j+1) t_j (k0+1) H) in H0; rewrite H0; reflexivity.
  Qed.

Lemma lem_islcft_at_openFT_at : forall (t:ftype) (j:index) (a:var_name) (k:index),
    k <= j -> isLCFT_at k t -> openFT_at j a t = t.
Proof. intros; rewrite lem_openFT_at_is_ftsubBV_at; 
  apply lem_islcft_at_ftsubBV_at with k; assumption. Qed.

Lemma lem_ftsubFV_openFT_at : forall (t:ftype) (j:index) (a':var_name) (t_a:ftype),
    ~ In a' (ffreeTV t) -> ftsubBV_at j t_a t = ftsubFV a' t_a (openFT_at j a' t).
Proof. induction t; intros; simpl.
  - (* FTBasic *) destruct b; simpl; try reflexivity.
      * (* FTV *) destruct (j =? i); 
        assert (a' =? a' = true) by (apply Nat.eqb_eq; reflexivity); 
        simpl; try rewrite H0; reflexivity.
      * (* BTV *) simpl in H; intuition; apply Nat.neq_sym in H0;
        apply Nat.eqb_neq in H0; rewrite H0; reflexivity.
  - (* FTFunc *) rewrite <- IHt1; try rewrite <- IHt2;
      simpl in H; apply not_elem_union_elim in H; destruct H;   
      trivial.
  - (* FTPoly *) rewrite <- IHt; simpl in H; trivial.
  Qed.

Lemma lem_ftsubFV_unbindFT : forall (a':var_name) (t_a:ftype) (t:ftype),
    ~ In a' (ffreeTV t) -> ftsubBV t_a t = ftsubFV a' t_a (unbindFT a' t).
Proof. intros. apply lem_ftsubFV_openFT_at; assumption. Qed.

Lemma lem_commute_ftsubFV_ftsubBV_at : 
  forall (t:ftype) (a:var_name) (t_a:ftype) (j:index) (t_j:ftype),
    isLCFT t_a 
      -> ftsubFV a t_a (ftsubBV_at j t_j t) = ftsubBV_at j (ftsubFV a t_a t_j) (ftsubFV a t_a t).
Proof. induction t; intros; simpl.
  - (* FTBasic *) destruct b; simpl; try reflexivity.
      * destruct (j =? i); simpl; reflexivity.
      * destruct (a =? a0); simpl;       
        try symmetry; try apply lem_islcft_at_ftsubBV_at with 0; auto with *.
  - (* FTFunc *) simpl; rewrite IHt1; try (rewrite IHt2); trivial.
  - (* FTPoly *) simpl. rewrite IHt; trivial.
  Qed. 

Lemma lem_commute_ftsubFV_ftsubBV : 
  forall (t_j:ftype) (a:var_name) (t_a:ftype) (t:ftype),
    isLCFT t_a 
      -> ftsubFV a t_a (ftsubBV t_j t) = ftsubBV (ftsubFV a t_a t_j) (ftsubFV a t_a t).
Proof. intros; apply lem_commute_ftsubFV_ftsubBV_at; assumption. Qed.

Lemma lem_commute_ftsubFV_openFT_at : 
  forall (t:ftype) (a0:var_name) (t_a0:ftype) (j:index) (a:var_name),
    a0 <> a -> isLCFT t_a0 
            -> ftsubFV a0 t_a0 (openFT_at j a t) = openFT_at j a (ftsubFV a0 t_a0 t).
Proof. intros; repeat rewrite lem_openFT_at_is_ftsubBV_at;
  apply Nat.eqb_neq in H;
  assert (ftsubFV a0 t_a0 (FTBasic (FTV a)) = FTBasic (FTV a))
    by (simpl; rewrite H; reflexivity).
  rewrite lem_commute_ftsubFV_ftsubBV_at; try rewrite H1; trivial.
  Qed. 

Lemma lem_commute_ftsubFV_unbindFT : forall (a0:var_name) (t_a0:ftype) (a:var_name) (t:ftype),
    a0 <> a -> isLCFT t_a0
            -> ftsubFV a0 t_a0 (unbindFT a t) = unbindFT a (ftsubFV a0 t_a0 t) .
Proof. unfold unbindFT; intros; apply lem_commute_ftsubFV_openFT_at; assumption. Qed.