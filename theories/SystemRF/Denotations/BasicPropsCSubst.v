Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.Strengthenings.
Require Import AutoProof.SystemRF.SystemRF.LocalClosure.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsSubstitution.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.Typing.
Require Import AutoProof.SystemRF.Denotations.ClosingSubstitutions.

Require Import Arith.
Require Import ZArith.
Require Import Lists.ListSet.

  (* -- | More Properties of Substitution *)

Lemma lem_commute_subFV' : (forall (e:expr) (x:var_name) (v:expr) (y:var_name) (v_y:expr),
    y <> x -> ~ In x (fv v_y) 
      -> subFV y v_y (subFV x v e) = subFV x (subFV y v_y v) (subFV y v_y e) ) * ((
  forall (t:type) (x:var_name) (v:expr) (y:var_name) (v_y:expr),
    y <> x -> ~ In x (fv v_y)
      -> tsubFV y v_y (tsubFV x v t) = tsubFV x (subFV y v_y v) (tsubFV y v_y t) ) * (
  forall (ps:preds) (x:var_name) (v:expr) (y:var_name) (v_y:expr),
    y <> x -> ~ In x (fv v_y)
      -> psubFV y v_y (psubFV x v ps) = psubFV x (subFV y v_y v) (psubFV y v_y ps) )).
Proof. apply ( syntax_mutind
  (fun e : expr => forall (x:var_name) (v:expr) (y:var_name) (v_y:expr),
    y <> x -> ~ In x (fv v_y) 
      -> subFV y v_y (subFV x v e) = subFV x (subFV y v_y v) (subFV y v_y e) )
  (fun t : type => forall (x:var_name) (v:expr) (y:var_name) (v_y:expr),
    y <> x -> ~ In x (fv v_y) 
      -> tsubFV y v_y (tsubFV x v t) = tsubFV x (subFV y v_y v) (tsubFV y v_y t) )
  (fun ps : preds => forall (x:var_name) (v:expr) (y:var_name) (v_y:expr),
    y <> x -> ~ In x (fv v_y) 
      -> psubFV y v_y (psubFV x v ps) = psubFV x (subFV y v_y v) (psubFV y v_y ps) ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H; assumption)
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0; assumption ).
  - (* FV *) destruct (Nat.eqb x0 x) eqn:E0; 
    destruct (Nat.eqb y x) eqn:E; simpl;
    try rewrite E0; try rewrite E; try reflexivity;
    (* both E0 and E cannot be true *)
    try apply Nat.eqb_eq in E0; try apply Nat.eqb_eq in E;
    try rewrite E0 in H; try rewrite E in H; try contradiction;
    apply lem_subFV_notin || (symmetry; apply lem_subFV_notin); assumption.
  - (* If *) rewrite H; try rewrite H0; try rewrite H1; trivial.
  Qed.  

Lemma lem_commute_subFV_general : 
  forall (e:expr) (x:var_name) (v:expr) (y:var_name) (v_y:expr),
    y <> x -> ~ In x (fv v_y) 
      -> subFV y v_y (subFV x v e) = subFV x (subFV y v_y v) (subFV y v_y e).
Proof. intros; apply lem_commute_subFV'; assumption. Qed.

Lemma lem_commute_tsubFV_general : 
  forall (t:type) (x:var_name) (v:expr) (y:var_name) (v_y:expr),
    y <> x -> ~ In x (fv v_y) 
      -> tsubFV y v_y (tsubFV x v t) = tsubFV x (subFV y v_y v) (tsubFV y v_y t).
Proof. intros; apply lem_commute_subFV'; assumption. Qed.  

Lemma lem_commute_psubFV_general : 
  forall (ps:preds) (x:var_name) (v:expr) (y:var_name) (v_y:expr),
    y <> x -> ~ In x (fv v_y) 
      -> psubFV y v_y (psubFV x v ps) = psubFV x (subFV y v_y v) (psubFV y v_y ps).
Proof. intros; apply lem_commute_subFV'; assumption. Qed.  

Lemma lem_commute_subFV : forall (e:expr) (x:var_name) (v:expr) (y:var_name) (v_y:expr),
    y <> x -> ~ In x (fv v_y) -> ~ In y (fv v)
      -> subFV y v_y (subFV x v e) = subFV x v (subFV y v_y e).
Proof. intros; rewrite <- (lem_subFV_notin' v y v_y) at 2;
   try apply lem_commute_subFV_general; assumption. Qed.

Lemma lem_commute_tsubFV : forall (t:type) (x:var_name) (v:expr) (y:var_name) (v_y:expr),
    y <> x -> ~ In x (fv v_y) -> ~ In y (fv v)
      -> tsubFV y v_y (tsubFV x v t) = tsubFV x v (tsubFV y v_y t).
Proof. intros; rewrite <- (lem_subFV_notin' v y v_y) at 2;
   try apply lem_commute_tsubFV_general; assumption. Qed.

Lemma lem_commute_psubFV : forall (ps:preds) (x:var_name) (v:expr) (y:var_name) (v_y:expr),
    y <> x -> ~ In x (fv v_y) -> ~ In y (fv v)
      -> psubFV y v_y (psubFV x v ps) = psubFV x v (psubFV y v_y ps).
Proof. intros; rewrite <- (lem_subFV_notin' v y v_y) at 2;
   try apply lem_commute_psubFV_general; assumption. Qed.

Lemma lem_commute_subFTV_subFV' : (forall (e:expr) (a:var_name) (t_a:type) (x:var_name) (v:expr),
    noExists t_a -> ~ In x (free t_a)
      -> subFTV a t_a (subFV x v e) = subFV x (subFTV a t_a v) (subFTV a t_a e) ) * ((
  forall (t:type) (a:var_name) (t_a:type) (x:var_name) (v:expr),
    noExists t_a -> ~ In x (free t_a)
      -> tsubFTV a t_a (tsubFV x v t) = tsubFV x (subFTV a t_a v) (tsubFTV a t_a t) ) * (
  forall (ps:preds) (a:var_name) (t_a:type) (x:var_name) (v:expr),
    noExists t_a -> ~ In x (free t_a)
      -> psubFTV a t_a (psubFV x v ps) = psubFV x (subFTV a t_a v) (psubFTV a t_a ps) )).
Proof. apply ( syntax_mutind
  (fun e : expr => forall (a:var_name) (t_a:type) (x:var_name) (v:expr),
    noExists t_a -> ~ In x (free t_a)
      -> subFTV a t_a (subFV x v e) = subFV x (subFTV a t_a v) (subFTV a t_a e) )
  (fun t : type => forall (a:var_name) (t_a:type) (x:var_name) (v:expr),
    noExists t_a -> ~ In x (free t_a)
      -> tsubFTV a t_a (tsubFV x v t) = tsubFV x (subFTV a t_a v) (tsubFTV a t_a t)  )
  (fun ps : preds => forall (a:var_name) (t_a:type) (x:var_name) (v:expr),
    noExists t_a -> ~ In x (free t_a)
      -> psubFTV a t_a (psubFV x v ps) = psubFV x (subFTV a t_a v) (psubFTV a t_a ps) ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H; assumption)
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0; assumption ).
  - (* FV *) destruct (Nat.eqb x0 x) eqn:E; simpl;
    try rewrite E; try reflexivity;
    symmetry; apply lem_subFTV_notin; assumption.
  - (* If *) rewrite H; try rewrite H0; try rewrite H1; trivial.
  - (* TRefn *) destruct b eqn:Eb; simpl; try rewrite H; trivial.
    destruct (a =? a0); simpl; try rewrite lem_subFV_push; try symmetry;
    try rewrite H; try f_equal; try apply lem_tsubFV_notin; trivial.
  Qed. 

Lemma lem_commute_subFTV_subFV_general : 
  forall (e:expr) (a:var_name) (t_a:type) (x:var_name) (v:expr),
    noExists t_a -> ~ In x (free t_a)
      -> subFTV a t_a (subFV x v e) = subFV x (subFTV a t_a v) (subFTV a t_a e).
Proof. intros; apply lem_commute_subFTV_subFV'; assumption. Qed.

Lemma lem_commute_tsubFTV_tsubFV_general : 
  forall (t:type) (a:var_name) (t_a:type) (x:var_name) (v:expr),
    noExists t_a -> ~ In x (free t_a)
      -> tsubFTV a t_a (tsubFV x v t) = tsubFV x (subFTV a t_a v) (tsubFTV a t_a t).
Proof. intros; apply lem_commute_subFTV_subFV'; assumption. Qed.    

Lemma lem_commute_psubFTV_psubFV_general : 
  forall (ps:preds) (a:var_name) (t_a:type) (x:var_name) (v:expr),
    noExists t_a -> ~ In x (free t_a)
      -> psubFTV a t_a (psubFV x v ps) = psubFV x (subFTV a t_a v) (psubFTV a t_a ps).
Proof. intros; apply lem_commute_subFTV_subFV'; assumption. Qed.    


Lemma lem_commute_subFV_subFTV' : (
  forall (e:expr) (a:var_name) (t_a:type) (y:var_name) (v_y:expr),
    noExists t_a -> ~ In a (ftv v_y) 
      -> subFV y v_y (subFTV a t_a e) = subFTV a (tsubFV y v_y t_a) (subFV y v_y e) ) * ((
  forall (t:type) (a:var_name) (t_a:type) (y:var_name) (v_y:expr),
    noExists t_a -> ~ In a (ftv v_y) 
      -> tsubFV y v_y (tsubFTV a t_a t) = tsubFTV a (tsubFV y v_y t_a) (tsubFV y v_y t) ) * (
  forall (ps:preds) (a:var_name) (t_a:type) (y:var_name) (v_y:expr),
    noExists t_a -> ~ In a (ftv v_y) 
      -> psubFV y v_y (psubFTV a t_a ps) = psubFTV a (tsubFV y v_y t_a) (psubFV y v_y ps) )).
Proof. apply ( syntax_mutind
  (fun e : expr => forall (a:var_name) (t_a:type) (y:var_name) (v_y:expr),
    noExists t_a -> ~ In a (ftv v_y) 
      -> subFV y v_y (subFTV a t_a e) = subFTV a (tsubFV y v_y t_a) (subFV y v_y e) )
  (fun t : type => forall (a:var_name) (t_a:type) (y:var_name) (v_y:expr),
    noExists t_a -> ~ In a (ftv v_y) 
      -> tsubFV y v_y (tsubFTV a t_a t) = tsubFTV a (tsubFV y v_y t_a) (tsubFV y v_y t) )
  (fun ps : preds => forall (a:var_name) (t_a:type) (y:var_name) (v_y:expr),
    noExists t_a -> ~ In a (ftv v_y) 
      -> psubFV y v_y (psubFTV a t_a ps) = psubFTV a (tsubFV y v_y t_a) (psubFV y v_y ps) ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H; assumption)
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0; assumption ).
  - (* FV *) destruct (Nat.eqb y x) eqn:E; simpl;
    try rewrite E; try reflexivity;
    symmetry; apply lem_subFTV_notin; assumption.
  - (* If *) rewrite H; try rewrite H0; try rewrite H1; trivial.
  - (* TRefn *) destruct b eqn:Eb; simpl; try rewrite H; trivial.
    destruct (a =? a0); simpl; try rewrite lem_subFV_push;
    try rewrite H; try f_equal; try apply lem_subFV_notin; trivial.
  Qed.
  
Lemma lem_commute_subFV_subFTV_general : 
  forall (e:expr) (a:var_name) (t_a:type) (y:var_name) (v_y:expr),
    noExists t_a -> ~ In a (ftv v_y)
      -> subFV y v_y (subFTV a t_a e) = subFTV a (tsubFV y v_y t_a) (subFV y v_y e).
Proof. intros; apply lem_commute_subFV_subFTV'; assumption. Qed.
  
Lemma lem_commute_tsubFV_tsubFTV_general : 
  forall (t:type) (a:var_name) (t_a:type) (y:var_name) (v_y:expr),
    noExists t_a -> ~ In a (ftv v_y)    
      -> tsubFV y v_y (tsubFTV a t_a t) = tsubFTV a (tsubFV y v_y t_a) (tsubFV y v_y t).
Proof. intros; apply lem_commute_subFV_subFTV'; assumption. Qed.

Lemma lem_commute_psubFV_psubFTV_general : 
  forall (ps:preds) (a:var_name) (t_a:type) (y:var_name) (v_y:expr),
    noExists t_a -> ~ In a (ftv v_y)    
      -> psubFV y v_y (psubFTV a t_a ps) = psubFTV a (tsubFV y v_y t_a) (psubFV y v_y ps).
Proof. intros; apply lem_commute_subFV_subFTV'; assumption. Qed.

Lemma lem_commute_subFV_subFTV : forall (e:expr) (a:var_name) (t_a:type) (y:var_name) (v_y:expr),
    noExists t_a -> ~ In a (ftv v_y) -> ~ In y (free t_a)
      -> subFV y v_y (subFTV a t_a e) = subFTV a t_a (subFV y v_y e).
Proof. intros; rewrite <- (lem_tsubFV_notin t_a y v_y) at 2;
   try apply lem_commute_subFV_subFTV_general; assumption. Qed.

Lemma lem_commute_tsubFV_tsubFTV : 
  forall (t:type) (a:var_name) (t_a:type) (y:var_name) (v_y:expr),
    noExists t_a -> ~ In a (ftv v_y) -> ~ In y (free t_a)
      -> tsubFV y v_y (tsubFTV a t_a t) = tsubFTV a t_a (tsubFV y v_y t).
Proof. intros; rewrite <- (lem_tsubFV_notin t_a y v_y) at 2;
   try apply lem_commute_tsubFV_tsubFTV_general; assumption. Qed.

Lemma lem_commute_psubFV_psubFTV : 
  forall (ps:preds) (a:var_name) (t_a:type) (y:var_name) (v_y:expr),
    noExists t_a -> ~ In a (ftv v_y) -> ~ In y (free t_a)
      -> psubFV y v_y (psubFTV a t_a ps) = psubFTV a t_a (psubFV y v_y ps).
Proof. intros; rewrite <- (lem_tsubFV_notin t_a y v_y) at 2;
   try apply lem_commute_psubFV_psubFTV_general; assumption. Qed.


Lemma lem_commute_subFTV' : (
  forall (e:expr) (a:var_name) (t_a:type) (a':var_name) (t_a':type),
    noExists t_a -> noExists t_a' -> a' <> a -> ~ In a (freeTV t_a') 
      -> subFTV a' t_a' (subFTV a t_a e) = subFTV a (tsubFTV a' t_a' t_a) (subFTV a' t_a' e) ) * ((
  forall (t:type) (a:var_name) (t_a:type) (a':var_name) (t_a':type),
    noExists t_a -> noExists t_a' -> a' <> a -> ~ In a (freeTV t_a') 
      -> tsubFTV a' t_a' (tsubFTV a t_a t) = tsubFTV a (tsubFTV a' t_a' t_a) (tsubFTV a' t_a' t) ) * (
  forall (ps:preds) (a:var_name) (t_a:type) (a':var_name) (t_a':type),
    noExists t_a -> noExists t_a' -> a' <> a -> ~ In a (freeTV t_a')
      -> psubFTV a' t_a' (psubFTV a t_a ps) = psubFTV a (tsubFTV a' t_a' t_a) (psubFTV a' t_a' ps) )).
Proof. apply ( syntax_mutind
  (fun e : expr => forall (a:var_name) (t_a:type) (a':var_name) (t_a':type),
    noExists t_a -> noExists t_a' -> a' <> a -> ~ In a (freeTV t_a') 
      -> subFTV a' t_a' (subFTV a t_a e) = subFTV a (tsubFTV a' t_a' t_a) (subFTV a' t_a' e) )
  (fun t : type => forall (a:var_name) (t_a:type) (a':var_name) (t_a':type),
    noExists t_a -> noExists t_a' -> a' <> a -> ~ In a (freeTV t_a') 
      -> tsubFTV a' t_a' (tsubFTV a t_a t) = tsubFTV a (tsubFTV a' t_a' t_a) (tsubFTV a' t_a' t) )
  (fun ps : preds => forall (a:var_name) (t_a:type) (a':var_name) (t_a':type),
    noExists t_a -> noExists t_a' -> a' <> a -> ~ In a (freeTV t_a') 
      -> psubFTV a' t_a' (psubFTV a t_a ps) = psubFTV a (tsubFTV a' t_a' t_a) (psubFTV a' t_a' ps) ))
  ; intros; simpl; try reflexivity
  ; (* 1 IH *) try ( apply f_equal; apply H; assumption)
  ; (* 2 IH *) try ( apply f_equal2; apply H || apply H0; assumption ).
  - (* If *) rewrite H; try rewrite H0; try rewrite H1; trivial.
  - (* TRefn *) destruct b eqn:Eb; simpl; try rewrite H; trivial.
    destruct (a =? a0) eqn:Ea; destruct (a' =? a0) eqn:Ea'; 
    simpl; try rewrite Ea; try rewrite Ea';
    (* both E0 and E cannot be true *)
      try apply Nat.eqb_eq in Ea; try apply Nat.eqb_eq in Ea';
      try rewrite Ea in H2; try rewrite Ea' in H2; try contradiction;
    try rewrite lem_subFTV_push; try rewrite H; try f_equal;
    try apply lemma_tsubFTV_noExists;
    try (symmetry; apply lem_subFTV_notin);
    try subst a0; trivial.
  Qed.

Lemma lem_commute_subFTV_general : forall (e:expr) (a:var_name) (t_a:type) (a':var_name) (t_a':type),
    noExists t_a -> noExists t_a' -> a' <> a -> ~ In a (freeTV t_a') 
      -> subFTV a' t_a' (subFTV a t_a e) = subFTV a (tsubFTV a' t_a' t_a) (subFTV a' t_a' e).
Proof. intros; apply lem_commute_subFTV'; assumption. Qed.  

Lemma lem_commute_tsubFTV_general : forall (t:type) (a:var_name) (t_a:type) (a':var_name) (t_a':type),
    noExists t_a -> noExists t_a' -> a' <> a -> ~ In a (freeTV t_a') 
      -> tsubFTV a' t_a' (tsubFTV a t_a t) = tsubFTV a (tsubFTV a' t_a' t_a) (tsubFTV a' t_a' t).     
Proof. intros; apply lem_commute_subFTV'; assumption. Qed.  

Lemma lem_commute_psubFTV_general : forall (ps:preds) (a:var_name) (t_a:type) (a':var_name) (t_a':type),
    noExists t_a -> noExists t_a' -> a' <> a -> ~ In a (freeTV t_a') 
      -> psubFTV a' t_a' (psubFTV a t_a ps) = psubFTV a (tsubFTV a' t_a' t_a) (psubFTV a' t_a' ps).     
Proof. intros; apply lem_commute_subFTV'; assumption. Qed.  

Lemma lem_commute_subFTV : forall (e:expr) (a:var_name) (t_a:type) (a':var_name) (t_a':type),
    noExists t_a -> noExists t_a' -> a' <> a 
      -> ~ In a (freeTV t_a') -> ~ In a' (freeTV t_a)
      -> subFTV a' t_a' (subFTV a t_a e) = subFTV a t_a (subFTV a' t_a' e).
Proof. intros; rewrite <- (lem_tsubFTV_notin t_a a' t_a') at 2;
  try apply lem_commute_subFTV'; assumption. Qed.  

Lemma lem_commute_tsubFTV : forall (t:type) (a:var_name) (t_a:type) (a':var_name) (t_a':type),
    noExists t_a -> noExists t_a' -> a' <> a 
      -> ~ In a (freeTV t_a') -> ~ In a' (freeTV t_a)
      -> tsubFTV a' t_a' (tsubFTV a t_a t) = tsubFTV a t_a (tsubFTV a' t_a' t).     
Proof. intros; rewrite <- (lem_tsubFTV_notin t_a a' t_a') at 2;
  try apply lem_commute_subFTV'; assumption. Qed.  

Lemma lem_commute_psubFTV : forall (ps:preds) (a:var_name) (t_a:type) (a':var_name) (t_a':type),
    noExists t_a -> noExists t_a' -> a' <> a 
      -> ~ In a (freeTV t_a') -> ~ In a' (freeTV t_a)
      -> psubFTV a' t_a' (psubFTV a t_a ps) = psubFTV a t_a (psubFTV a' t_a' ps). 
Proof. intros; rewrite <- (lem_tsubFTV_notin t_a a' t_a') at 2;
  try apply lem_commute_subFTV'; assumption. Qed.  

  (* -- | Closing Substitution Properties *)

Lemma lem_unroll_csubst_left : forall (th:csub) (x:var_name) (v_x e:expr),
    ~ in_csubst x th -> fv v_x = empty /\ ftv v_x = empty (*-> isValue v_x*)
        -> closed th -> substitutable th
        -> csubst (CCons x v_x th) e = subFV x v_x (csubst th e).
Proof. induction th; intros; simpl; try reflexivity;
  unfold in_csubst in H; simpl in H; 
  apply not_elem_names_add_elim in H; destruct H.
  - (* CCons *) rewrite <- IHth; simpl; try apply f_equal;
    try apply lem_commute_subFV; 
    simpl in H2; simpl in H1; try apply H0;
    destruct H0; destruct H2; destruct H1; destruct H6;
    try rewrite H0; try rewrite H1; intuition.
  - (* CConsT *) rewrite <- IHth; simpl; try apply f_equal;
    try symmetry; try apply lem_commute_subFV_subFTV;
    simpl in H2; simpl in H1; try apply H0;
    destruct H0; destruct H1; destruct H5;
    try rewrite H1; try rewrite H4; intuition.
  Qed.
 
Lemma lem_unroll_csubst_tv_left : forall (th:csub) (a:var_name) (t_a:type) (e:expr),
    ~ in_csubst a th -> free t_a = empty /\ freeTV t_a = empty -> noExists t_a
        -> closed th -> substitutable th
        -> csubst (CConsT a t_a th) e = subFTV a t_a (csubst th e).
Proof. induction th; intros; simpl; try reflexivity;
  unfold in_csubst in H; simpl in H; 
  apply not_elem_names_add_elim in H; destruct H.
  - (* CCons *) rewrite <- IHth; simpl; try apply f_equal;
    try apply lem_commute_subFV_subFTV;
    simpl in H2; simpl in H3; try apply H0;
    destruct H0; destruct H2; destruct H6; destruct H3;
    try rewrite H0; try rewrite H6; intuition.
  - (* CConsT *) rewrite <- IHth; simpl; try apply f_equal;
    try symmetry; try apply lem_commute_subFTV;
    simpl in H2; simpl in H3; try apply H0;
    destruct H0; destruct H2; destruct H6; destruct H3;
    try rewrite H5; try rewrite H6; intuition.
  Qed.         
   
Lemma lem_unroll_ctsubst_left : forall (th:csub) (x:var_name) (v_x:expr) (t:type),
    ~ in_csubst x th -> fv v_x = empty /\ ftv v_x = empty (*-> isValue v_x*)
        -> closed th -> substitutable th
        -> ctsubst (CCons x v_x th) t = tsubFV x v_x (ctsubst th t).
Proof. induction th; intros; simpl; try reflexivity;
  unfold in_csubst in H; simpl in H; 
  apply not_elem_names_add_elim in H; destruct H.
  - (* CCons *) rewrite <- IHth; simpl; try apply f_equal;
    try apply lem_commute_tsubFV;
    simpl in H1; simpl in H2; try apply H0;
    destruct H0; destruct H1; 
    try rewrite H0; try rewrite H1; intuition.
  - (* CConsT *) rewrite <- IHth; simpl; try apply f_equal;
    try symmetry; try apply lem_commute_tsubFV_tsubFTV;
    simpl in H1; simpl in H2; try apply H0;
    destruct H0; destruct H1;
    try rewrite H1; try rewrite H4; intuition.
  Qed.       

Lemma lem_unroll_ctsubst_tv_left : forall (th:csub) (a:var_name) (t_a t:type),
    ~ in_csubst a th -> free t_a = empty /\ freeTV t_a = empty -> noExists t_a
        -> closed th -> substitutable th
        -> ctsubst (CConsT a t_a th) t = tsubFTV a t_a (ctsubst th t).
Proof. induction th; intros; simpl; try reflexivity;
  unfold in_csubst in H; simpl in H; 
  apply not_elem_names_add_elim in H; destruct H.
  - (* CCons *) rewrite <- IHth; simpl; try apply f_equal;
    try apply lem_commute_tsubFV_tsubFTV;
    simpl in H2; simpl in H3; try apply H0;
    destruct H0; destruct H2; destruct H6; destruct H3;
    try rewrite H0; try rewrite H6; intuition.
  - (* CConsT *) rewrite <- IHth; simpl; try apply f_equal;
    try symmetry; try apply lem_commute_tsubFTV;
    simpl in H2; simpl in H3; try apply H0;
    destruct H0; destruct H2; destruct H6; destruct H3;
    try rewrite H5; try rewrite H6; intuition.
  Qed.         

  (* --- Various properties of csubst/ctsubst and free/bound variables *)

Lemma lem_csubst_nofv : forall (th:csub) (e:expr),
    fv e = empty -> ftv e = empty -> csubst th e = e.
Proof. induction th; intros; simpl; try reflexivity;
  rewrite IHth; try rewrite lem_subFV_notin';
  try rewrite lem_subFTV_notin'; 
  try apply empty_no_elem; trivial. Qed.

Lemma lem_ctsubst_nofree : forall (th:csub) (t:type),
    free t = empty -> freeTV t = empty -> ctsubst th t = t.
Proof. induction th; intros; simpl; try reflexivity;
  rewrite IHth; try rewrite lem_tsubFV_notin; 
  try rewrite lem_tsubFTV_notin; 
  try apply empty_no_elem; trivial. Qed.

Lemma lem_csubst_value : forall (th:csub) (v:expr),
    isValue v -> substitutable th -> isValue (csubst th v).
Proof. induction th; simpl; intros; try apply H; 
  destruct H0; try destruct H1;
  try apply lem_subFV_value with x v_x v in H as H';
  try apply lem_subFTV_value with a t_a v in H as H';
  try apply IHth; assumption. Qed.

Lemma lem_ctsubst_isMono : forall (th:csub) (t_a:type),
    isMono t_a -> substitutable th -> isMono (ctsubst th t_a).
Proof. induction th; simpl; intros; try apply H; 
  destruct H0; try destruct H1;
  try apply lemma_tsubFV_isMono with x v_x t_a in H as H';
  try apply lemma_tsubFTV_isMono with a t_a t_a0 in H as H';
  try apply IHth; assumption. Qed.

Lemma lem_ctsubst_noExists : forall (th:csub) (t_a:type),
    noExists t_a -> substitutable th -> noExists (ctsubst th t_a).
Proof. induction th; simpl; intros; try apply H; 
  destruct H0; try destruct H1;
  try apply lemma_tsubFV_noExists with x v_x t_a in H as H';
  try apply lemma_tsubFTV_noExists with a t_a t_a0 in H as H';
  try apply IHth; assumption. Qed.

  (* --- various distributive properties of csubst and ctsubst *)

Lemma lem_csubst_bc : forall (th:csub) (b:bool) ,
    csubst th (Bool_constant b) = Bool_constant b.
Proof. induction th; simpl; apply IHth || reflexivity. Qed.

Lemma lem_csubst_ic : forall (th:csub) (n:Z),
    csubst th (Int_constant n) = Int_constant n.
Proof. induction th; simpl; apply IHth || reflexivity. Qed.

Lemma lem_csubst_prim : forall (th:csub) (c:prim),
    csubst th (Prim c) = Prim c.
Proof. induction th; simpl; apply IHth || reflexivity. Qed.

Lemma lem_csubst_bv : forall (th:csub) (y:var_name),
    csubst th (BV y) = BV y.
Proof. induction th; simpl; apply IHth || reflexivity. Qed.

Lemma lem_csubst_fv : forall (th:csub) (y:var_name),
    ~ in_csubst y th -> csubst th (FV y) = FV y.
Proof. induction th; unfold in_csubst; intros; simpl; 
  simpl in H; try apply not_elem_names_add_elim in H; 
  try destruct (x =? y) eqn:E;
  try apply Nat.eqb_eq in E; try rewrite E in H;
  try apply IHth; intuition. Qed.

Lemma lem_csubst_lambda : forall (th:csub) (e:expr),
    csubst th (Lambda e) = Lambda (csubst th e).
Proof. induction th; simpl; intro e; apply IHth || reflexivity. Qed.

Lemma lem_csubst_app : forall (th:csub) (e e':expr),
    csubst th (App e e') = App (csubst th e) (csubst th e').
Proof. induction th; simpl; intros e e'; apply IHth || reflexivity. Qed.

Lemma lem_csubst_lambdaT : forall (th:csub) (k:kind) (e:expr),
    csubst th (LambdaT k e) = LambdaT k (csubst th e).
Proof. induction th; simpl; intros k e; apply IHth || reflexivity. Qed.

Lemma lem_csubst_appT : forall (th:csub) (e:expr) (t:type),
    csubst th (AppT e t) = AppT (csubst th e) (ctsubst th t).
Proof. induction th; simpl; intros; apply IHth || reflexivity. Qed.
 
Lemma lem_csubst_let : forall (th:csub) (e_x e:expr), 
    csubst th (Let e_x e) = Let (csubst th e_x) (csubst th e).
Proof. induction th; simpl; intros; apply IHth || reflexivity. Qed.

Lemma lem_csubst_annot : forall (th:csub) (e:expr) (t:type),
    csubst th (Annot e t) = Annot (csubst th e) (ctsubst th t).
Proof. induction th; simpl; intros; apply IHth || reflexivity. Qed.

Lemma lem_csubst_if : forall (th:csub) (e0 e1 e2:expr), 
    csubst th (If e0 e1 e2) = If (csubst th e0) (csubst th e1) (csubst th e2).
Proof. induction th; simpl; intros; apply IHth || reflexivity. Qed.

Lemma lem_cpsubst_pempty : forall (th:csub), cpsubst th PEmpty = PEmpty.
Proof. induction th; simpl; apply IHth || reflexivity. Qed.

Lemma lem_cpsubst_pcons : forall (th:csub) (p:expr) (ps:preds),
    cpsubst th (PCons p ps) = PCons (csubst th p) (cpsubst th ps).
Proof. induction th; simpl; intros; apply IHth || reflexivity. Qed.
 
Lemma lem_cpsubst_strengthen : forall (th:csub) (ps qs:preds),
    cpsubst th (strengthen ps qs) = strengthen (cpsubst th ps) (cpsubst th qs).
Proof. induction th; simpl; intros; 
  try rewrite lem_psubFV_strengthen; try rewrite lem_psubFTV_strengthen; 
  try apply IHth || reflexivity. Qed.

Lemma lem_ctsubst_push : forall (th:csub) (ps:preds) (t_a:type),
    noExists t_a -> substitutable th
        -> ctsubst th (push ps t_a) = push (cpsubst th ps) (ctsubst th t_a).
Proof. induction th; simpl; intros;
  try rewrite lem_subFV_push; try rewrite lem_subFTV_push;
  try rewrite IHth; 
  try apply lemma_tsubFV_noExists; try apply lemma_tsubFTV_noExists;
  intuition. Qed.

Lemma lem_ctsubst_refn : forall (th:csub) (b:basic) (ps:preds),
    isConcreteBasic b \/ isBTV b 
        -> ctsubst th (TRefn b ps) = TRefn b (cpsubst th ps).
Proof. induction th; intros b ps Hb; simpl;
  destruct b; simpl in Hb; try rewrite IHth; intuition. Qed.

Lemma lem_ctsubst_refn_tv_notin : forall (th:csub) (a:var_name) (ps:preds),
    ~ in_csubst a th 
        -> ctsubst th (TRefn (FTV a) ps) = TRefn (FTV a) (cpsubst th ps).
Proof. induction th; intros a0 ps H; simpl.
  - (* CEmpty *) reflexivity.
  - (* CCons *) apply in_csubst_CCons in H; destruct H;
    apply IHth; apply H0.
  - (* CConsT *) apply in_csubst_CConsT in H; destruct H;
    apply Nat.neq_sym in H; apply Nat.eqb_neq in H;
    rewrite H; apply IHth; apply H0.
  Qed.

Lemma lem_ctsubst_refn_tv_notin' : forall (th:csub) (a:var_name) (ps:preds),
    ~ In a (tvbindsC th)
        -> ctsubst th (TRefn (FTV a) ps) = TRefn (FTV a) (cpsubst th ps).
Proof. induction th; intros a0 ps H; simpl.
  - (* CEmpty *) reflexivity.
  - (* CCons *) simpl in H; apply IHth; apply H.
  - (* CConsT *) simpl in H; apply not_elem_names_add_elim in H;
    destruct H; apply Nat.neq_sym in H; apply Nat.eqb_neq in H;
    rewrite H; apply IHth; apply H0.
  Qed.  

Lemma lem_ctsubst_refn_tv : forall (th:csub) (a:var_name) (t_a:type) (ps:preds),
    tv_bound_inC a t_a th -> closed th -> substitutable th -> uniqueC th
        -> ctsubst th (TRefn (FTV a) ps) = push (cpsubst th ps) t_a.
Proof. induction th; simpl; intros.
  - (* CEmpty *) contradiction.
  - (* CCons *) apply IHth; intuition. 
  - (* CConsT *) destruct (a =? a0) eqn:A;
    destruct H0; destruct H1; destruct H2; destruct H3; destruct H4.
    * destruct H; try destruct H.
      + subst t_a0; rewrite lem_ctsubst_push;
        try rewrite lem_ctsubst_nofree; trivial.
      + apply Nat.eqb_eq in A; subst a0;
        apply lem_tvboundinC_incsubst in H; contradiction.
    * destruct H; try destruct H; apply Nat.eqb_neq in A.
      + subst a0; contradiction.
      + apply IHth; trivial.
  Qed.

Lemma lem_ctsubst_func : forall (th:csub) (t_x t:type),
    ctsubst th (TFunc t_x t) = TFunc (ctsubst th t_x) (ctsubst th t).
Proof. induction th; simpl; intros; apply IHth || reflexivity. Qed.
  
Lemma lem_ctsubst_exis : forall (th:csub) (t_x t:type),
    ctsubst th (TExists t_x t) = TExists (ctsubst th t_x) (ctsubst th t).
Proof. induction th; simpl; intros; apply IHth || reflexivity. Qed.
  
Lemma lem_ctsubst_poly : forall (th:csub) (k:kind) (t:type),
    ctsubst th (TPoly k t) = TPoly k (ctsubst th t).
Proof. induction th; simpl; intros; apply IHth || reflexivity. Qed.

Lemma lem_ctsubst_erase_basic : forall (th:csub) (t:type) (b:basic), 
    erase t = FTBasic b -> isConcreteBasic b \/ isBTV b 
        -> erase (ctsubst th t) = FTBasic b.
Proof. intro th; induction t; simpl; intros; try discriminate;
  try injection H as H; try subst b0;
  rewrite lem_ctsubst_refn || rewrite lem_ctsubst_exis;
  simpl; try apply IHt2; trivial. Qed.

Fixpoint isExFTV (t : type) : Prop :=
    match t with
    | (TRefn b ps)    => match b with
                         | (FTV a) => True
                         | _       => False
    end
    | (TFunc tx t')   => False
    | (TExists tx t') => isExFTV t'
    | (TPoly k t')    => False
    end.

Fixpoint matchesExFTV (a : var_name) (t : type) : Prop :=
    match t with
    | (TRefn b ps)    => match b with
                         | (FTV a0) => a = a0
                         | _        => False
    end
    | (TFunc tx t')   => False
    | (TExists tx t') => matchesExFTV a t'
    | (TPoly k t')    => False
    end.

Lemma matchesExFTV_dec : forall (a:var_name) (t:type),
    matchesExFTV a t \/ ~ matchesExFTV a t.
Proof. intro a; induction t; 
  try destruct b; try destruct (a =? a0) eqn:A;
  simpl; unfold not; intuition.
  - apply Nat.eqb_eq in A; left; apply A.
  - apply Nat.eqb_neq in A; right; apply A. Qed. 

Lemma lem_matchesExFTV_both : forall (a0 a:var_name) (t:type),
    matchesExFTV a0 t -> matchesExFTV a t -> a0 = a.  
Proof. intros a0 a; induction t; simpl;
  try destruct b; intuition; subst a; apply H. Qed.

Lemma lem_isNotExFTV_no_match : forall (a:var_name) (t:type),
    ~ isExFTV t -> ~ matchesExFTV a t.
Proof. intro a; induction t; simpl; try destruct b; intuition. Qed.

Lemma lem_tsubFV_matchesExFTV : forall (a x:var_name) (v_x:expr) (t:type),
    matchesExFTV a t -> matchesExFTV a (tsubFV x v_x t).
Proof. intros a x v_x; induction t; simpl;
  try destruct b; trivial. Qed.

Lemma lem_tsubFTV_matchesExFTV : forall (a0 a:var_name) (t_a t:type),
    a0 <> a 
        -> matchesExFTV a0 t -> matchesExFTV a0 (tsubFTV a t_a t).
Proof. intros a a0 t_a; induction t; simpl;
  try destruct b; trivial; intros; subst a1;
  apply Nat.neq_sym in H; apply Nat.eqb_neq in H;
  rewrite H; simpl; reflexivity. Qed.  

Lemma lem_tsubFV_isNotExFTV : forall (x:var_name) (v_x:expr) (t:type),
    ~ isExFTV t -> ~ isExFTV (tsubFV x v_x t).
Proof. intros x v_x; induction t; simpl;
  try destruct b; trivial. Qed.

Lemma lem_tsubFTV_isNotExFTV : forall (a:var_name) (t_a:type) (t:type),
    ~ isExFTV t -> ~ isExFTV (tsubFTV a t_a t).
Proof. intros a t_a; induction t; simpl;
  try destruct b; intuition. Qed.

Lemma lem_push_isNotExFTV : forall (ps:preds) (t_a:type),
    freeTV t_a = empty -> noExists t_a -> ~ isExFTV (push ps t_a).
Proof. intros ps; destruct t_a; simpl; 
  try destruct b; auto; intro H. 
  apply empty_no_elem with (names_add a (ftvP ps0)) a in H;
  apply not_elem_names_add_elim in H; intuition. Qed.

Lemma lem_tsubFTV_matches : forall (a:var_name) (t_a t:type),
    freeTV t_a = empty -> noExists t_a
        -> matchesExFTV a t -> ~ isExFTV (tsubFTV a t_a t).
Proof. intros a t_a; induction t; simpl; 
  try destruct b; try apply IHt2;
  intros; try contradiction. 
  apply Nat.eqb_eq in H1; rewrite H1; 
  apply lem_push_isNotExFTV; assumption. Qed.

Lemma lem_tsubFTV_self_noFTV : forall (a:var_name) (t_a t:type) (v:expr) (k:kind),
    ~ matchesExFTV a t 
      -> tsubFTV a t_a (self t v k) = self (tsubFTV a t_a t) (subFTV a t_a v) k.
Proof. intros a t_a; induction t; intros v k'; destruct k';
  try destruct b; simpl; try destruct (a =? a0) eqn:A; intro H;
  unfold eqlPred; f_equal; try apply IHt2; trivial;
  apply Nat.eqb_eq in A; subst a0; contradiction. Qed.

Lemma lem_ctsubst_self_noFTV : forall (th:csub) (t:type) (v:expr) (k:kind),
    ~ isExFTV t -> ctsubst th (self t v k) = self (ctsubst th t) (csubst th v) k.
Proof. induction th; simpl; intros; try reflexivity.
  - (* CCons *) rewrite lem_tsubFV_self; apply IHth.
    destruct t; try destruct b; simpl; simpl in H; trivial.
    apply lem_tsubFV_isNotExFTV; apply H. 
  - (* CConsT *) destruct t; destruct k; try destruct b; 
    simpl; simpl in H; try contradiction;
    try repeat rewrite lem_ctsubst_refn; 
    try        rewrite lem_ctsubst_func;
    try repeat rewrite lem_ctsubst_exis;
    try rewrite lem_ctsubst_poly; simpl; unfold eqlPred; 
    try rewrite lem_cpsubst_pcons;
    try repeat rewrite lem_csubst_app;
    try rewrite lem_csubst_appT; 
    try rewrite lem_csubst_prim;
    try rewrite lem_ctsubst_refn; 
    try rewrite lem_cpsubst_pempty;
    try rewrite lem_csubst_bv; simpl; auto; f_equal.
    rewrite lem_tsubFTV_self_noFTV; try apply IHth;
    try apply lem_tsubFTV_isNotExFTV;
    try apply lem_isNotExFTV_no_match; apply H. Qed.

Lemma lem_ctsubst_self_FTV : forall (th:csub) (a:var_name) (t:type) (v:expr) (k:kind),
    matchesExFTV a t -> ~ in_csubst a th
        -> ctsubst th (self t v k) = self (ctsubst th t) (csubst th v) k.
Proof.  induction th; simpl; intros; try reflexivity.
  - (* CCons *) rewrite lem_tsubFV_self; apply IHth with a;
    unfold in_csubst in H0; simpl in H0; 
    apply not_elem_names_add_elim in H0; destruct H0;
    try apply lem_tsubFV_matchesExFTV; trivial.
  - (* CConsT *) apply in_csubst_CConsT in H0;  destruct H0;
    destruct t eqn:T; simpl in H; 
    try destruct b; try contradiction; try subst a1;
    rewrite lem_tsubFTV_self_noFTV ;
    try rewrite <- IHth with a0 (tsubFTV a t_a (TRefn (FTV a0) ps)) 
                              (subFTV a t_a v) k;
    try rewrite <- IHth with a0 (tsubFTV a t_a (TExists t0_1 t0_2)) 
                              (subFTV a t_a v) k;
    try assert (a =? a0 = false)
      by (apply Nat.eqb_neq; apply Nat.neq_sym; apply H0);    
    simpl; try rewrite H; simpl;
    try apply Nat.neq_sym;
    try apply lem_tsubFTV_matchesExFTV;
    trivial; unfold not; intros; apply H0;
    apply lem_matchesExFTV_both with t0_2; trivial.
  Qed.

  (* --- Commutative laws relating csubst/ctsubst and substitution operations *)

Lemma lem_csubst_subBV : forall (th:csub) (v e:expr),
    loc_closed th -> substitutable th
        -> csubst th (subBV v e) = subBV (csubst th v) (csubst th e).
Proof. induction th; simpl; intros; try reflexivity;
  try rewrite lem_commute_subFV_subBV;
  try rewrite lem_commute_subFTV_subBV;
  try apply IHth; destruct H; destruct H0; try destruct H2; assumption. Qed.

Lemma lem_csubst_subBTV : forall (th:csub) (t_a:type) (e:expr),
    loc_closed th -> substitutable th -> noExists t_a
          -> csubst th (subBTV t_a e) = subBTV (ctsubst th t_a) (csubst th e).
Proof. induction th; simpl; intros; try reflexivity;
  try rewrite lem_commute_subFV_subBTV;
  try rewrite lem_commute_subFTV_subBTV;
  destruct H; destruct H0; try apply IHth; try destruct H3; 
  try apply lemma_tsubFV_noExists;
  try apply lemma_tsubFTV_noExists; assumption. Qed.

Lemma lem_ctsubst_tsubBV : forall (th:csub) (v:expr) (t:type),
    loc_closed th -> substitutable th 
        -> ctsubst th (tsubBV v t) = tsubBV (csubst th v) (ctsubst th t).
Proof. induction th; simpl; intros; try reflexivity;
  try rewrite lem_commute_tsubFV_tsubBV;
  try rewrite lem_commute_tsubFTV_tsubBV;
  try apply IHth; destruct H; destruct H0; 
  try destruct H2; try assumption. Qed.

Lemma lem_ctsubst_tsubBTV : forall (th:csub) (t_a t:type),
    loc_closed th -> substitutable th -> noExists t_a
        -> ctsubst th (tsubBTV t_a t) = tsubBTV (ctsubst th t_a) (ctsubst th t).
Proof. induction th; simpl; intros; try reflexivity;
  try rewrite lem_commute_tsubFV_tsubBTV;
  try rewrite lem_commute_tsubFTV_tsubBTV;
  destruct H; destruct H0; try apply IHth; try destruct H3;
  try apply lemma_tsubFV_noExists;
  try apply lemma_tsubFTV_noExists; try assumption. Qed.

Lemma lem_cpsubst_psubBV : forall (th:csub) (v:expr) (ps:preds),
    loc_closed th -> substitutable th 
        -> cpsubst th (psubBV v ps) = psubBV (csubst th v) (cpsubst th ps).
Proof. induction th; simpl; intros; try reflexivity;
  try rewrite lem_commute_psubFV_psubBV;
  try rewrite lem_commute_psubFTV_psubBV;
  try apply IHth; destruct H; destruct H0; 
  try destruct H2; try assumption. Qed.

Lemma lem_cpsubst_psubBTV : forall (th:csub) (t_a:type) (ps:preds),
    loc_closed th -> substitutable th -> noExists t_a
        -> cpsubst th (psubBTV t_a ps) = psubBTV (ctsubst th t_a) (cpsubst th ps).
Proof. induction th; simpl; intros; try reflexivity;
  try rewrite lem_commute_psubFV_psubBTV;
  try rewrite lem_commute_psubFTV_psubBTV;
  destruct H; destruct H0; try apply IHth; try destruct H3;
  try apply lemma_tsubFV_noExists;
  try apply lemma_tsubFTV_noExists; try assumption. Qed.
  
  (* --- After applying a closing substitution there are no more free variables remaining *)

Lemma lem_csubst_pres_noftv : forall (th:csub) (v:expr),
    closed th -> ftv v = empty -> ftv (csubst th v) = empty.
Proof. induction th; simpl; trivial; intros; destruct H; destruct H1.
  - (* CCons *) apply IHth. apply H2. 
    assert (Subset (ftv (subFV x v_x v)) (union (ftv v) (ftv v_x)))
      by apply ftv_subFV_elim;
    rewrite H1 in H3; rewrite H0 in H3;
    apply no_elem_empty; unfold not; intros. 
    apply H3 in H4; intuition.
  - (* CConsT *) assert (subFTV a t_a v = v) 
        by (apply lem_subFTV_notin; rewrite H0; auto);
    rewrite H3; apply IHth; assumption. 
  Qed.

Lemma lem_csubst_no_more_fv : forall (th:csub) (v_x:expr),
    Subset (fv v_x) (vbindsC th) -> Subset (ftv v_x) (tvbindsC th)
        -> closed th -> substitutable th
        -> fv (csubst th v_x) = empty /\ ftv (csubst th v_x) = empty.
Proof. induction th; simpl; intros.
  - (* CEmpty *) split; apply no_elem_empty; intros;
    apply not_elem_subset with empty; auto.
  - (* CCons  *) apply IHth; destruct H1 as [Hvx [Hvx' H']];
    pose proof fv_subFV_elim as [Hfv _];
    pose proof ftv_subFV_elim as [Hftv _]; 
    destruct H2; try assumption.
    apply subset_trans with (union (diff (fv v_x0) (singleton x)) (fv v_x));
    try apply Hfv; rewrite Hvx; apply subset_union_intro_l; 
    try apply subset_empty_l; apply subset_add_to_diff; apply H.
    apply subset_trans with (union (ftv v_x0) (ftv v_x));
    try apply Hftv; rewrite Hvx'; apply subset_union_intro_l; 
    try apply subset_empty_l; apply H0.
  - (* CConsT *) apply IHth; destruct H1 as [Hta [Hta' H']];
    pose proof fv_subFTV_elim as [Hfv _];
    pose proof ftv_subFTV_elim as [Hftv _]; 
    repeat destruct H2; try assumption.
    apply subset_trans with (union (fv v_x) (free t_a));
    try apply Hfv; try apply H2; rewrite Hta; 
    apply subset_union_intro_l; try apply subset_empty_l; apply H.
    apply subset_trans with (union (diff (ftv v_x) (singleton a)) (freeTV t_a));
    try apply Hftv; try apply H2; rewrite Hta'; 
    apply subset_union_intro_l; try apply subset_empty_l; 
    apply subset_add_to_diff; apply H0.
  Qed.

Lemma lem_ctsubst_no_more_fv : forall (th:csub) (t:type),
    Subset (free t) (vbindsC th) -> Subset (freeTV t) (tvbindsC th)
        -> closed th -> substitutable th
        -> free (ctsubst th t) = empty /\ freeTV (ctsubst th t) = empty.
Proof. induction th; simpl; intros.
  - (* CEmpty *) split; apply no_elem_empty; intros;
    apply not_elem_subset with empty; auto.
  - (* CCons  *) apply IHth; destruct H1 as [Hvx [Hvx' H']];
    pose proof fv_subFV_elim as [_ [Hfv _]];
    pose proof ftv_subFV_elim as [_ [Hftv _]]; 
    destruct H2; try assumption.
    apply subset_trans with (union (diff (free t) (singleton x)) (fv v_x));
    try apply Hfv; rewrite Hvx; apply subset_union_intro_l; 
    try apply subset_empty_l; apply subset_add_to_diff; apply H.
    apply subset_trans with (union (freeTV t) (ftv v_x));
    try apply Hftv; rewrite Hvx'; apply subset_union_intro_l; 
    try apply subset_empty_l; apply H0.
  - (* CConsT *) apply IHth; destruct H1 as [Hta [Hta' H']];
    pose proof fv_subFTV_elim as [_ [Hfv _]];
    pose proof ftv_subFTV_elim as [_ [Hftv _]]; 
    repeat destruct H2; try assumption.
    apply subset_trans with (union (free t) (free t_a));
    try apply Hfv; try apply H2; rewrite Hta; 
    apply subset_union_intro_l; try apply subset_empty_l; apply H.
    apply subset_trans with (union (diff (freeTV t) (singleton a)) (freeTV t_a));
    try apply Hftv; try apply H2; rewrite Hta'; 
    apply subset_union_intro_l; try apply subset_empty_l; 
    apply subset_add_to_diff; apply H0.
  Qed.
    

Lemma lem_csubst_isLC : forall (th:csub) (v:expr),
    loc_closed th -> substitutable th -> isLC v -> isLC (csubst th v).
Proof. induction th; simpl; trivial; intros; destruct H; destruct H0.
  - (* CCons *) apply IHth; try apply lem_islc_at_subFV; trivial. 
  - (* CConsT *) apply IHth; destruct H3;
    try apply lem_islc_at_subFTV; trivial.
  Qed.

Lemma lem_ctsubst_isLCT : forall (th:csub) (t:type),
    loc_closed th -> substitutable th -> isLCT t -> isLCT (ctsubst th t).
Proof. induction th; simpl; trivial; intros; destruct H; destruct H0.
  - (* CCons *) apply IHth; try apply lem_islc_at_subFV; trivial. 
  - (* CConsT *) apply IHth; destruct H3;
    try apply lem_islc_at_subFTV; trivial.
  Qed.  


Lemma lem_csubst_subFV : forall (th:csub) (y:var_name) (v_y e:expr), 
    ~ (in_csubst y th) -> closed th -> substitutable th -> uniqueC th
        -> Subset (fv v_y) (vbindsC th) -> Subset (ftv v_y) (tvbindsC th)
        -> csubst th (subFV y (csubst th v_y) e) = csubst th (subFV y v_y e).
Proof. induction th as [|y v_y th|a t_a th]; simpl; intros x v_x; intros.
  - (* CEmpty *) reflexivity.
  - (* CCons  *) apply not_elem_names_add_elim in H; destruct H;
    destruct H0; destruct H1; destruct H2; destruct H6. fold bindsC in H5. 
    rewrite lem_commute_subFV; try rewrite IHth;
    try rewrite <- (lem_commute_subFV_general e x v_x y v_y);
    try (apply empty_no_elem; apply H0);
    pose proof fv_subFV_elim as [Hfv _];
    pose proof ftv_subFV_elim as [Hftv _];
    assert (Subset (fv (subFV y v_y v_x)) (vbindsC th))
      by (apply subset_trans with (union (diff (fv v_x) (singleton y)) (fv v_y));
          try apply Hfv; rewrite H0; apply subset_union_intro_l;
          try apply subset_empty_l; apply subset_add_to_diff; auto);
    assert (Subset (ftv (subFV y v_y v_x)) (tvbindsC th))
      by (apply subset_trans with (union (ftv v_x) (ftv v_y));
          try apply Hftv; rewrite H6; apply subset_union_intro_l;
          try apply subset_empty_l; auto);
    pose proof (lem_csubst_no_more_fv th (subFV y v_y v_x));
    apply H12 in H7 as H12'; try destruct H12'; try rewrite H13; auto.
  - (* CConsT *) apply not_elem_names_add_elim in H; destruct H;
    destruct H0; destruct H1; destruct H2; destruct H6;
    destruct H7; fold bindsC in H5.
    rewrite <- lem_commute_subFV_subFTV; try rewrite IHth;
    try rewrite <- lem_commute_subFTV_subFV_general;
    try (apply empty_no_elem; apply H0);
    pose proof fv_subFTV_elim as [Hfv _];
    pose proof ftv_subFTV_elim as [Hftv _];
    assert (Subset (fv (subFTV a t_a v_x)) (vbindsC th))
      by (apply subset_trans with (union (fv v_x) (free t_a));
          try apply Hfv; try rewrite H0; try apply subset_union_intro_l;
          try apply subset_empty_l; auto);
    assert (Subset (ftv (subFTV a t_a v_x)) (tvbindsC th))
      by (apply subset_trans with (union (diff (ftv v_x) (singleton a)) (freeTV t_a));
          try apply Hftv; try rewrite H6; try apply subset_union_intro_l;
          try apply subset_empty_l; try apply subset_add_to_diff; auto);
    pose proof (lem_csubst_no_more_fv th (subFTV a t_a v_x));
    apply H13 in H10 as H13'; try destruct H13'; try rewrite H15; auto.
  Qed.
   
Lemma lem_ctsubst_tsubFV : forall (th:csub) (x:var_name) (v_x:expr) (t:type), 
    ~ (in_csubst x th) -> closed th -> substitutable th -> uniqueC th
        -> Subset (fv v_x) (vbindsC th) -> Subset (ftv v_x) (tvbindsC th)
        -> ctsubst th (tsubFV x (csubst th v_x) t) = ctsubst th (tsubFV x v_x t).
Proof. induction th as [|y v_y th|a t_a th]; simpl; intros x v_x; intros.
  - (* CEmpty *) reflexivity.
  - (* CCons  *) apply not_elem_names_add_elim in H; destruct H;
    destruct H0; destruct H1; destruct H2; destruct H6. fold bindsC in H5. 
    rewrite lem_commute_tsubFV; try rewrite IHth;
    try rewrite <- (lem_commute_tsubFV_general t x v_x y v_y);
    try (apply empty_no_elem; apply H0);
    pose proof fv_subFV_elim as [Hfv _];
    pose proof ftv_subFV_elim as [Hftv _];
    assert (Subset (fv (subFV y v_y v_x)) (vbindsC th))
      by (apply subset_trans with (union (diff (fv v_x) (singleton y)) (fv v_y));
          try apply Hfv; rewrite H0; apply subset_union_intro_l;
          try apply subset_empty_l; apply subset_add_to_diff; auto);
    assert (Subset (ftv (subFV y v_y v_x)) (tvbindsC th))
      by (apply subset_trans with (union (ftv v_x) (ftv v_y));
          try apply Hftv; rewrite H6; apply subset_union_intro_l;
          try apply subset_empty_l; auto);
    pose proof (lem_csubst_no_more_fv th (subFV y v_y v_x));
    apply H12 in H7 as H12'; try destruct H12'; try rewrite H13; auto.
  - (* CConsT *) apply not_elem_names_add_elim in H; destruct H;
    destruct H0; destruct H1; destruct H2; destruct H6;
    destruct H7; fold bindsC in H5.
    rewrite <- lem_commute_tsubFV_tsubFTV; try rewrite IHth;
    try rewrite <- lem_commute_tsubFTV_tsubFV_general;
    try (apply empty_no_elem; apply H0);
    pose proof fv_subFTV_elim as [Hfv _];
    pose proof ftv_subFTV_elim as [Hftv _];
    assert (Subset (fv (subFTV a t_a v_x)) (vbindsC th))
      by (apply subset_trans with (union (fv v_x) (free t_a));
          try apply Hfv; try rewrite H0; try apply subset_union_intro_l;
          try apply subset_empty_l; auto);
    assert (Subset (ftv (subFTV a t_a v_x)) (tvbindsC th))
      by (apply subset_trans with (union (diff (ftv v_x) (singleton a)) (freeTV t_a));
          try apply Hftv; try rewrite H6; try apply subset_union_intro_l;
          try apply subset_empty_l; try apply subset_add_to_diff; auto);
    pose proof (lem_csubst_no_more_fv th (subFTV a t_a v_x));
    apply H13 in H10 as H13'; try destruct H13'; try rewrite H15; auto.
  Qed.        

Lemma lem_cpsubst_psubFV : forall (th:csub) (x:var_name) (v_x:expr) (ps:preds), 
    ~ (in_csubst x th) -> closed th -> substitutable th -> uniqueC th
        -> Subset (fv v_x) (vbindsC th) -> Subset (ftv v_x) (tvbindsC th)
        -> cpsubst th (psubFV x (csubst th v_x) ps) = cpsubst th (psubFV x v_x ps).
Proof. induction th as [|y v_y th|a t_a th]; simpl; intros x v_x; intros.
  - (* CEmpty *) reflexivity.
  - (* CCons  *) apply not_elem_names_add_elim in H; destruct H;
    destruct H0; destruct H1; destruct H2; destruct H6. fold bindsC in H5. 
    rewrite lem_commute_psubFV; try rewrite IHth;
    try rewrite <- (lem_commute_psubFV_general ps x v_x y v_y);
    try (apply empty_no_elem; apply H0);
    pose proof fv_subFV_elim as [Hfv _];
    pose proof ftv_subFV_elim as [Hftv _];
    assert (Subset (fv (subFV y v_y v_x)) (vbindsC th))
      by (apply subset_trans with (union (diff (fv v_x) (singleton y)) (fv v_y));
          try apply Hfv; rewrite H0; apply subset_union_intro_l;
          try apply subset_empty_l; apply subset_add_to_diff; auto);
    assert (Subset (ftv (subFV y v_y v_x)) (tvbindsC th))
      by (apply subset_trans with (union (ftv v_x) (ftv v_y));
          try apply Hftv; rewrite H6; apply subset_union_intro_l;
          try apply subset_empty_l; auto);
    pose proof (lem_csubst_no_more_fv th (subFV y v_y v_x));
    apply H12 in H7 as H12'; try destruct H12'; try rewrite H13; auto.
  - (* CConsT *) apply not_elem_names_add_elim in H; destruct H;
    destruct H0; destruct H1; destruct H2; destruct H6;
    destruct H7; fold bindsC in H5.
    rewrite <- lem_commute_psubFV_psubFTV; try rewrite IHth;
    try rewrite <- lem_commute_psubFTV_psubFV_general;
    try (apply empty_no_elem; apply H0);
    pose proof fv_subFTV_elim as [Hfv _];
    pose proof ftv_subFTV_elim as [Hftv _];
    assert (Subset (fv (subFTV a t_a v_x)) (vbindsC th))
      by (apply subset_trans with (union (fv v_x) (free t_a));
          try apply Hfv; try rewrite H0; try apply subset_union_intro_l;
          try apply subset_empty_l; auto);
    assert (Subset (ftv (subFTV a t_a v_x)) (tvbindsC th))
      by (apply subset_trans with (union (diff (ftv v_x) (singleton a)) (freeTV t_a));
          try apply Hftv; try rewrite H6; try apply subset_union_intro_l;
          try apply subset_empty_l; try apply subset_add_to_diff; auto);
    pose proof (lem_csubst_no_more_fv th (subFTV a t_a v_x));
    apply H13 in H10 as H13'; try destruct H13'; try rewrite H15; auto.
  Qed.        

Lemma lem_csubst_subFTV : forall (th:csub) (a:var_name) (t_a:type) (e:expr), 
    ~ (in_csubst a th) -> noExists t_a -> closed th -> substitutable th -> uniqueC th
        -> Subset (free t_a) (vbindsC th) -> Subset (freeTV t_a) (tvbindsC th)
        -> csubst th (subFTV a (ctsubst th t_a) e) = csubst th (subFTV a t_a e).
Proof. induction th as [|y v_y th|a' t_a' th]; simpl; intros a t_a; intros.
  - (* CEmpty *) reflexivity.
  - (* CCons  *) apply not_elem_names_add_elim in H; destruct H;
    destruct H3; destruct H1; destruct H2; destruct H8. fold bindsC in H6. 
    rewrite lem_commute_subFV_subFTV; try rewrite IHth;
    try rewrite <- (lem_commute_subFV_subFTV_general e a t_a y v_y);
    try (apply empty_no_elem; apply H8);
    pose proof fv_subFV_elim as [_ [Hfv _]];
    pose proof ftv_subFV_elim as [_ [Hftv _]];
    assert (Subset (free (tsubFV y v_y t_a)) (vbindsC th))
      by (apply subset_trans with (union (diff (free t_a) (singleton y)) (fv v_y));
          try apply Hfv; rewrite H1; apply subset_union_intro_l;
          try apply subset_empty_l; apply subset_add_to_diff; auto);
    assert (Subset (freeTV (tsubFV y v_y t_a)) (tvbindsC th))
      by (apply subset_trans with (union (freeTV t_a) (ftv v_y));
          try apply Hftv; rewrite H8; apply subset_union_intro_l;
          try apply subset_empty_l; auto);
    pose proof (lem_ctsubst_no_more_fv th (tsubFV y v_y t_a));
    try apply lem_ctsubst_noExists;
    try apply lemma_tsubFV_noExists;
    apply H13 in H9 as H13'; try destruct H13'; try rewrite H14; auto.
  - (* CConsT *) apply not_elem_names_add_elim in H; destruct H;
    destruct H1; destruct H2; destruct H3; destruct H7;
    destruct H8; fold bindsC in H6.
    rewrite <- lem_commute_subFTV; try rewrite IHth;
    try rewrite <- lem_commute_subFTV_general;
    try (apply empty_no_elem; apply H7);
    pose proof fv_subFTV_elim as [_ [Hfv _]];
    pose proof ftv_subFTV_elim as [_ [Hftv _]];
    assert (Subset (free (tsubFTV a' t_a' t_a)) (vbindsC th))
      by (apply subset_trans with (union (free t_a) (free t_a'));
          try apply Hfv; try rewrite H1; try apply subset_union_intro_l;
          try apply subset_empty_l; auto);
    assert (Subset (freeTV (tsubFTV a' t_a' t_a)) (tvbindsC th))
      by (apply subset_trans with (union (diff (freeTV t_a) (singleton a')) (freeTV t_a'));
          try apply Hftv; try rewrite H7; try apply subset_union_intro_l;
          try apply subset_empty_l; try apply subset_add_to_diff; auto);
    pose proof (lem_ctsubst_no_more_fv th (tsubFTV a' t_a' t_a));
    try apply lem_ctsubst_noExists;
    try apply lemma_tsubFTV_noExists;
    apply H14 in H11 as H14'; try destruct H14'; try rewrite H16; auto.
  Qed.

Lemma lem_ctsubst_tsubFTV : forall (th:csub) (a:var_name) (t_a t:type), 
    ~ (in_csubst a th) -> noExists t_a -> closed th -> substitutable th -> uniqueC th
        -> Subset (free t_a) (vbindsC th) -> Subset (freeTV t_a) (tvbindsC th)
        -> ctsubst th (tsubFTV a (ctsubst th t_a) t) = ctsubst th (tsubFTV a t_a t).
Proof. induction th as [|y v_y th|a' t_a' th]; simpl; intros a t_a; intros.
  - (* CEmpty *) reflexivity.
  - (* CCons  *) apply not_elem_names_add_elim in H; destruct H;
    destruct H3; destruct H1; destruct H2; destruct H8. fold bindsC in H6. 
    rewrite lem_commute_tsubFV_tsubFTV; try rewrite IHth;
    try rewrite <- (lem_commute_tsubFV_tsubFTV_general t a t_a y v_y);
    try (apply empty_no_elem; apply H8);
    pose proof fv_subFV_elim as [_ [Hfv _]];
    pose proof ftv_subFV_elim as [_ [Hftv _]];
    assert (Subset (free (tsubFV y v_y t_a)) (vbindsC th))
      by (apply subset_trans with (union (diff (free t_a) (singleton y)) (fv v_y));
          try apply Hfv; rewrite H1; apply subset_union_intro_l;
          try apply subset_empty_l; apply subset_add_to_diff; auto);
    assert (Subset (freeTV (tsubFV y v_y t_a)) (tvbindsC th))
      by (apply subset_trans with (union (freeTV t_a) (ftv v_y));
          try apply Hftv; rewrite H8; apply subset_union_intro_l;
          try apply subset_empty_l; auto);
    pose proof (lem_ctsubst_no_more_fv th (tsubFV y v_y t_a));
    try apply lem_ctsubst_noExists;
    try apply lemma_tsubFV_noExists;
    apply H13 in H9 as H13'; try destruct H13'; try rewrite H14; auto.
  - (* CConsT *) apply not_elem_names_add_elim in H; destruct H;
    destruct H1; destruct H2; destruct H3; destruct H7;
    destruct H8; fold bindsC in H6.
    rewrite <- lem_commute_tsubFTV; try rewrite IHth;
    try rewrite <- lem_commute_tsubFTV_general;
    try (apply empty_no_elem; apply H7);
    pose proof fv_subFTV_elim as [_ [Hfv _]];
    pose proof ftv_subFTV_elim as [_ [Hftv _]];
    assert (Subset (free (tsubFTV a' t_a' t_a)) (vbindsC th))
      by (apply subset_trans with (union (free t_a) (free t_a'));
          try apply Hfv; try rewrite H1; try apply subset_union_intro_l;
          try apply subset_empty_l; auto);
    assert (Subset (freeTV (tsubFTV a' t_a' t_a)) (tvbindsC th))
      by (apply subset_trans with (union (diff (freeTV t_a) (singleton a')) (freeTV t_a'));
          try apply Hftv; try rewrite H7; try apply subset_union_intro_l;
          try apply subset_empty_l; try apply subset_add_to_diff; auto);
    pose proof (lem_ctsubst_no_more_fv th (tsubFTV a' t_a' t_a));
    try apply lem_ctsubst_noExists;
    try apply lemma_tsubFTV_noExists;
    apply H14 in H11 as H14'; try destruct H14'; try rewrite H16; auto.
  Qed.

Lemma lem_cpsubst_psubFTV : forall (th:csub) (a:var_name) (t_a:type) (ps:preds), 
    ~ (in_csubst a th) -> noExists t_a -> closed th -> substitutable th -> uniqueC th
        -> Subset (free t_a) (vbindsC th) -> Subset (freeTV t_a) (tvbindsC th)
        -> cpsubst th (psubFTV a (ctsubst th t_a) ps) = cpsubst th (psubFTV a t_a ps).
Proof. induction th as [|y v_y th|a' t_a' th]; simpl; intros a t_a; intros.
  - (* CEmpty *) reflexivity.
  - (* CCons  *) apply not_elem_names_add_elim in H; destruct H;
    destruct H3; destruct H1; destruct H2; destruct H8. fold bindsC in H6. 
    rewrite lem_commute_psubFV_psubFTV; try rewrite IHth;
    try rewrite <- (lem_commute_psubFV_psubFTV_general ps a t_a y v_y);
    try (apply empty_no_elem; apply H8);
    pose proof fv_subFV_elim as [_ [Hfv _]];
    pose proof ftv_subFV_elim as [_ [Hftv _]];
    assert (Subset (free (tsubFV y v_y t_a)) (vbindsC th))
      by (apply subset_trans with (union (diff (free t_a) (singleton y)) (fv v_y));
          try apply Hfv; rewrite H1; apply subset_union_intro_l;
          try apply subset_empty_l; apply subset_add_to_diff; auto);
    assert (Subset (freeTV (tsubFV y v_y t_a)) (tvbindsC th))
      by (apply subset_trans with (union (freeTV t_a) (ftv v_y));
          try apply Hftv; rewrite H8; apply subset_union_intro_l;
          try apply subset_empty_l; auto);
    pose proof (lem_ctsubst_no_more_fv th (tsubFV y v_y t_a));
    try apply lem_ctsubst_noExists;
    try apply lemma_tsubFV_noExists;
    apply H13 in H9 as H13'; try destruct H13'; try rewrite H14; auto.
  - (* CConsT *) apply not_elem_names_add_elim in H; destruct H;
    destruct H1; destruct H2; destruct H3; destruct H7;
    destruct H8; fold bindsC in H6.
    rewrite <- lem_commute_psubFTV; try rewrite IHth;
    try rewrite <- lem_commute_psubFTV_general;
    try (apply empty_no_elem; apply H7);
    pose proof fv_subFTV_elim as [_ [Hfv _]];
    pose proof ftv_subFTV_elim as [_ [Hftv _]];
    assert (Subset (free (tsubFTV a' t_a' t_a)) (vbindsC th))
      by (apply subset_trans with (union (free t_a) (free t_a'));
          try apply Hfv; try rewrite H1; try apply subset_union_intro_l;
          try apply subset_empty_l; auto);
    assert (Subset (freeTV (tsubFTV a' t_a' t_a)) (tvbindsC th))
      by (apply subset_trans with (union (diff (freeTV t_a) (singleton a')) (freeTV t_a'));
          try apply Hftv; try rewrite H7; try apply subset_union_intro_l;
          try apply subset_empty_l; try apply subset_add_to_diff; auto);
    pose proof (lem_ctsubst_no_more_fv th (tsubFTV a' t_a' t_a));
    try apply lem_ctsubst_noExists;
    try apply lemma_tsubFTV_noExists;
    apply H14 in H11 as H14'; try destruct H14'; try rewrite H16; auto.
  Qed.


(*  --- Closing Substitutions and Technical Operations *)

Lemma lem_remove_not_incsubst : forall (th:csub) (x:var_name),
    ~ in_csubst x th -> remove_fromCS th x = th.
Proof. induction th; unfold in_csubst; simpl; intros; 
  try reflexivity; apply not_elem_names_add_elim in H;
  destruct H; apply Nat.eqb_neq in H; rewrite H;
  f_equal; apply IHth; trivial. Qed.

Lemma lem_remove_ctsubst : forall (th:csub) (x:var_name) (t:type),
    In x (bindsC th) -> ~ In x (free t) -> ~ In x (freeTV t)
        -> closed th -> uniqueC th -> substitutable th
        -> ctsubst th t = ctsubst (remove_fromCS th x) t.
Proof. induction th; intros; simpl.
  - (* CEmpty *) reflexivity.
  - (* CCons  *) destruct (x0 =? x) eqn:X.
    * apply Nat.eqb_eq in X; subst x0; 
      rewrite lem_tsubFV_notin; trivial.
    * simpl; apply IHth; simpl in H;
      apply set_add_elim in H; destruct H;
      try (apply Nat.eqb_neq in X; contradiction);
      simpl in *; destruct H2 as [H2 [H2' Hcl]];
      destruct H3; destruct H4;
      pose proof fv_subFV_elim as [_ [H' _]];
      pose proof ftv_subFV_elim as [_ [H'' _]]; 
      unfold not; intros;
      try apply H' in H7; try apply H'' in H7;
      try rewrite H2 in H7; try rewrite H2' in H7;
      try revert H7;
      try apply not_elem_union_intro; unfold not; intros;
      try apply (set_diff_elim1 Nat.eq_dec) in H7; 
      try contradiction; auto.
  - (* CConsT *) destruct (x =? a) eqn:X.
    * apply Nat.eqb_eq in X; subst a; 
      rewrite lem_tsubFTV_notin; trivial.
    * simpl; apply IHth; simpl in H;
      apply set_add_elim in H; destruct H;
      try (apply Nat.eqb_neq in X; contradiction);
      simpl in *; destruct H2 as [H2 [H2' Hcl]];
      destruct H3; destruct H4; destruct H6;
      pose proof fv_subFTV_elim as [_ [H' _]];
      pose proof ftv_subFTV_elim as [_ [H'' _]]; 
      unfold not; intros;
      try apply H' in H8; try apply H'' in H8;
      try rewrite H2 in H8; try rewrite H2' in H8;
      try revert H8;
      try apply not_elem_union_intro; unfold not; intros;
      try apply (set_diff_elim1 Nat.eq_dec) in H8; 
      try contradiction; auto.
  Qed.  

Lemma lem_remove_cpsubst : forall (th:csub) (x:var_name) (ps:preds),
    In x (bindsC th) -> ~ In x (fvP ps) -> ~ In x (ftvP ps)
        -> closed th -> uniqueC th -> substitutable th
        -> cpsubst th ps = cpsubst (remove_fromCS th x) ps.
Proof. induction th; intros; simpl.
  - (* CEmpty *) reflexivity.
  - (* CCons  *) destruct (x0 =? x) eqn:X.
    * apply Nat.eqb_eq in X; subst x0; 
      rewrite lem_psubFV_notin; trivial.
    * simpl; apply IHth; simpl in H;
      apply set_add_elim in H; destruct H;
      try (apply Nat.eqb_neq in X; contradiction);
      simpl in *; destruct H2 as [H2 [H2' Hcl]];
      destruct H3; destruct H4;
      pose proof fv_subFV_elim as [_ [_ H' ]];
      pose proof ftv_subFV_elim as [_ [_ H'']]; 
      unfold not; intros;
      try apply H' in H7; try apply H'' in H7;
      try rewrite H2 in H7; try rewrite H2' in H7;
      try revert H7;
      try apply not_elem_union_intro; unfold not; intros;
      try apply (set_diff_elim1 Nat.eq_dec) in H7; 
      try contradiction; auto.
  - (* CConsT *) destruct (x =? a) eqn:X.
    * apply Nat.eqb_eq in X; subst a; 
      rewrite lem_psubFTV_notin; trivial.
    * simpl; apply IHth; simpl in H;
      apply set_add_elim in H; destruct H;
      try (apply Nat.eqb_neq in X; contradiction);
      simpl in *; destruct H2 as [H2 [H2' Hcl]];
      destruct H3; destruct H4; destruct H6;
      pose proof fv_subFTV_elim as [_ [_ H']];
      pose proof ftv_subFTV_elim as [_ [_ H'']]; 
      unfold not; intros;
      try apply H' in H8; try apply H'' in H8;
      try rewrite H2 in H8; try rewrite H2' in H8;
      try revert H8;
      try apply not_elem_union_intro; unfold not; intros;
      try apply (set_diff_elim1 Nat.eq_dec) in H8; 
      try contradiction; auto.
  Qed.
    