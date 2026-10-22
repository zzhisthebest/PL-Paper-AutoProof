(** System F CBV strong-normalization benchmark, Hard variant.
    Features: if-nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat Arith.Compare_dec Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationIfNondeterminismHardTask.

Definition atom := nat.

Declare Scope systemf_scope.
Delimit Scope systemf_scope with systemf.
Open Scope systemf_scope.

Declare Custom Entry systemf_ty.
Declare Custom Entry systemf_tm.

Inductive ty : Type :=
  | Ty_BVar : nat -> ty
  | Ty_FVar : atom -> ty

  | Ty_Arrow : ty -> ty -> ty

  | Ty_All : ty -> ty
  | Ty_Bool : ty.

Notation "T" := T
  (in custom systemf_ty at level 0, T constr at level 0) : systemf_scope.
Notation "<{{ T }}>" := T
  (T custom systemf_ty at level 200) : systemf_scope.
Notation "( T )" := T
  (in custom systemf_ty at level 0, T custom systemf_ty) : systemf_scope.
Notation "$( T )" := T
  (in custom systemf_ty at level 0, T constr) : systemf_scope.
Notation "'fvar' X" := (Ty_FVar X)
  (in custom systemf_ty at level 0, X constr at level 0) : systemf_scope.
Notation "T1 '->' T2" := (Ty_Arrow T1 T2)
  (in custom systemf_ty at level 99, right associativity) : systemf_scope.
Notation "'forall' ',' T" := (Ty_All T)
  (in custom systemf_ty at level 200,
   T custom systemf_ty at level 200,
   right associativity) : systemf_scope.

Inductive tm : Type :=
  | tm_bvar : nat -> tm
  | tm_fvar : atom -> tm
  | tm_abs : ty -> tm -> tm
  | tm_app : tm -> tm -> tm

  | tm_tabs : tm -> tm

  | tm_tapp : tm -> ty -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
  | tm_choice : tm -> tm -> tm.

Notation "t" := t
  (in custom systemf_tm at level 0, t constr at level 0) : systemf_scope.
Notation "<{ t }>" := t
  (t custom systemf_tm at level 200) : systemf_scope.
Notation "( t )" := t
  (in custom systemf_tm at level 0, t custom systemf_tm) : systemf_scope.
Notation "$( t )" := t
  (in custom systemf_tm at level 0, t constr, only parsing) : systemf_scope.
Notation "'bvar' n" := (tm_bvar n)
  (in custom systemf_tm at level 0, n constr at level 0) : systemf_scope.
Notation "'fvar' x" := (tm_fvar x)
  (in custom systemf_tm at level 0, x constr at level 0) : systemf_scope.
Notation "t1 t2" := (tm_app t1 t2)
  (in custom systemf_tm at level 10, left associativity) : systemf_scope.
Notation "'lambda' ':' T ',' t" := (tm_abs T t)
  (in custom systemf_tm at level 200,
   T custom systemf_ty,
   t custom systemf_tm at level 200,
   left associativity) : systemf_scope.
Notation "'Lambda' ',' t" := (tm_tabs t)
  (in custom systemf_tm at level 200,
   t custom systemf_tm at level 200,
   left associativity) : systemf_scope.
Notation "t '[' T ']'" := (tm_tapp t T)
  (in custom systemf_tm at level 10,
   t custom systemf_tm,
   T custom systemf_ty) : systemf_scope.

Notation "'Bool'" := Ty_Bool (in custom systemf_ty at level 0) : systemf_scope.
Notation "'true'" := tm_true (in custom systemf_tm at level 0) : systemf_scope.
Notation "'false'" := tm_false (in custom systemf_tm at level 0) : systemf_scope.
Notation "'if' t1 'then' t2 'else' t3" := (tm_if t1 t2 t3)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm, t3 custom systemf_tm at level 200) : systemf_scope.
Notation "'choice' t1 'or' t2" := (tm_choice t1 t2)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm at level 200) : systemf_scope.

Fixpoint open_ty_rec (k : nat) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => if Nat.eqb k i then U else Ty_BVar i
  | Ty_FVar X => Ty_FVar X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (open_ty_rec k U T1) (open_ty_rec k U T2)
  | Ty_All T1 => Ty_All (open_ty_rec (S k) U T1)
  | Ty_Bool => Ty_Bool
  end.

Definition open_ty (T U : ty) : ty := open_ty_rec 0 U T.

Fixpoint open_tm_rec (k : nat) (u t : tm) : tm :=
  match t with
  | tm_bvar i => if Nat.eqb k i then u else tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs T (open_tm_rec (S k) u t1)
  | tm_app t1 t2 => tm_app (open_tm_rec k u t1) (open_tm_rec k u t2)
  | tm_tabs t1 => tm_tabs (open_tm_rec k u t1)
  | tm_tapp t1 T => tm_tapp (open_tm_rec k u t1) T
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (open_tm_rec k u t1) (open_tm_rec k u t2) (open_tm_rec k u t3)
  | tm_choice t1 t2 => tm_choice (open_tm_rec k u t1) (open_tm_rec k u t2)
  end.

Definition open_tm (t u : tm) : tm := open_tm_rec 0 u t.

Fixpoint open_tm_ty_rec (k : nat) (U : ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 =>
      tm_abs (open_ty_rec k U T) (open_tm_ty_rec k U t1)
  | tm_app t1 t2 =>
      tm_app (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2)
  | tm_tabs t1 => tm_tabs (open_tm_ty_rec (S k) U t1)
  | tm_tapp t1 T =>
      tm_tapp (open_tm_ty_rec k U t1) (open_ty_rec k U T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2) (open_tm_ty_rec k U t3)
  | tm_choice t1 t2 => tm_choice (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2)
  end.

Definition open_tm_ty (t : tm) (U : ty) : tm :=
  open_tm_ty_rec 0 U t.

Fixpoint ty_subst (X : atom) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar Y => if Nat.eqb X Y then U else Ty_FVar Y
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_subst X U T1) (ty_subst X U T2)
  | Ty_All T1 => Ty_All (ty_subst X U T1)
  | Ty_Bool => Ty_Bool
  end.

Fixpoint tm_ty_subst (X : atom) (U : ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_subst X U T) (tm_ty_subst X U t1)
  | tm_app t1 t2 => tm_app (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  | tm_tabs t1 => tm_tabs (tm_ty_subst X U t1)
  | tm_tapp t1 T => tm_tapp (tm_ty_subst X U t1) (ty_subst X U T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_ty_subst X U t1) (tm_ty_subst X U t2) (tm_ty_subst X U t3)
  | tm_choice t1 t2 => tm_choice (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  end.

Fixpoint tm_subst (x : atom) (s t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar y => if Nat.eqb x y then s else tm_fvar y
  | tm_abs T t1 => tm_abs T (tm_subst x s t1)
  | tm_app t1 t2 => tm_app (tm_subst x s t1) (tm_subst x s t2)
  | tm_tabs t1 => tm_tabs (tm_subst x s t1)
  | tm_tapp t1 T => tm_tapp (tm_subst x s t1) T
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_subst x s t1) (tm_subst x s t2) (tm_subst x s t3)
  | tm_choice t1 t2 => tm_choice (tm_subst x s t1) (tm_subst x s t2)
  end.

Inductive lc_ty_at : nat -> ty -> Prop :=
  | lc_ty_bvar : forall k i,
      i < k ->
      lc_ty_at k (Ty_BVar i)
  | lc_ty_fvar : forall k X,
      lc_ty_at k (Ty_FVar X)
  | lc_ty_arrow : forall k T1 T2,
      lc_ty_at k T1 ->
      lc_ty_at k T2 ->
      lc_ty_at k (Ty_Arrow T1 T2)
  | lc_ty_all : forall k T,
      lc_ty_at (S k) T ->
      lc_ty_at k (Ty_All T)
  | lc_ty_bool : forall k, lc_ty_at k Ty_Bool.

Definition locally_closed_ty (T : ty) : Prop := lc_ty_at 0 T.

Lemma lc_ty_mono : forall K T, lc_ty_at K T -> lc_ty_at (S K) T.
Proof.
  intros K T H; induction H; eauto using lc_ty_at; try constructor; lia.
Qed.

Lemma open_ty_rec_inv_lc : forall K k T X,
  k < K -> lc_ty_at K (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at K T.
Proof.
  intros K k T; revert K k; induction T; intros K k X Hlt Hlc; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor. exact Hlt.
    + inversion Hlc; subst. constructor. assumption.
  - inversion Hlc; constructor.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. constructor.
    apply (IHT (S K) (S k) X); [lia|assumption].
  - constructor.
Qed.

Lemma open_ty_rec_inv_lift : forall K U T,
  lc_ty_at 0 U ->
  lc_ty_at K (open_ty_rec K U T) -> lc_ty_at (S K) T.
Proof.
  intros K U T; revert K; induction T; intros K HU Hlc; simpl in *.
  - destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor. lia.
    + inversion Hlc; subst. constructor. lia.
  - inversion Hlc; constructor.
  - inversion Hlc; subst. econstructor; eauto using lc_ty_mono.
  - inversion Hlc; subst. econstructor.
    eapply IHT; eauto using lc_ty_mono.
  - constructor.
Qed.

Inductive lc_tm_at : nat -> nat -> tm -> Prop :=
  | lc_tm_bvar : forall K k i,
      i < k ->
      lc_tm_at K k (tm_bvar i)
  | lc_tm_fvar : forall K k x,
      lc_tm_at K k (tm_fvar x)
  | lc_tm_abs : forall K k T t,
      lc_ty_at K T ->
      lc_tm_at K (S k) t ->
      lc_tm_at K k (tm_abs T t)
  | lc_tm_app : forall K k t1 t2,
      lc_tm_at K k t1 ->
      lc_tm_at K k t2 ->
      lc_tm_at K k (tm_app t1 t2)
  | lc_tm_tabs : forall K k t,
      lc_tm_at (S K) k t ->
      lc_tm_at K k (tm_tabs t)
  | lc_tm_tapp : forall K k t T,
      lc_tm_at K k t ->
      lc_ty_at K T ->
      lc_tm_at K k (tm_tapp t T)
  | lc_tm_true : forall K k, lc_tm_at K k tm_true
  | lc_tm_false : forall K k, lc_tm_at K k tm_false
  | lc_tm_if : forall K k t1 t2 t3,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k t3 -> lc_tm_at K k (tm_if t1 t2 t3)
  | lc_tm_choice : forall K k t1 t2,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k (tm_choice t1 t2).

Definition locally_closed_tm (t : tm) : Prop := lc_tm_at 0 0 t.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed_tm (tm_abs T t) ->
      value (tm_abs T t)
  | v_tabs : forall t,
      locally_closed_tm (tm_tabs t) ->
      value (tm_tabs t)
  | v_true : value tm_true
  | v_false : value tm_false.

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall T t v,
      locally_closed_tm (tm_abs T t) ->
      value v ->

      tm_app (tm_abs T t) v --> open_tm t v
  | ST_App1 : forall t1 t1' t2,
      t1 --> t1' ->
      locally_closed_tm t2 ->
      tm_app t1 t2 --> tm_app t1' t2

  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      tm_app v1 t2 --> tm_app v1 t2'
  | ST_TAppTabs :

      forall t T,
      locally_closed_tm (tm_tabs t) ->
      locally_closed_ty T ->
      tm_tapp (tm_tabs t) T --> open_tm_ty t T
  | ST_TApp : forall t t' T,
      t --> t' ->
      locally_closed_ty T ->
      tm_tapp t T --> tm_tapp t' T
  | ST_IfTrue : forall t1 t2,
      locally_closed_tm t1 ->
      locally_closed_tm t2 ->
      tm_if tm_true t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      locally_closed_tm t1 ->
      locally_closed_tm t2 ->
      tm_if tm_false t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      locally_closed_tm t2 ->
      locally_closed_tm t3 ->
      tm_if t1 t2 t3 --> tm_if t1' t2 t3
  | ST_ChoiceLeft : forall t1 t2,
      locally_closed_tm t1 ->
      locally_closed_tm t2 ->
      tm_choice t1 t2 --> t1
  | ST_ChoiceRight : forall t1 t2,
      locally_closed_tm t1 ->
      locally_closed_tm t2 ->
      tm_choice t1 t2 --> t2
where "t1 '-->' t2" := (step t1 t2).

Definition ty_context := list atom.

Definition context := list (atom * ty).

Fixpoint max_atom (xs : list atom) : nat :=
  match xs with [] => 0 | x :: xs' => Nat.max x (max_atom xs') end.
Definition fresh_atom (xs : list atom) := S (max_atom xs).

Lemma in_le_max_atom : forall x xs, In x xs -> x <= max_atom xs.
Proof.
  intros x xs; induction xs as [|a xs IH]; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [->|Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

Lemma fresh_atom_notin : forall xs, ~ In (fresh_atom xs) xs.
Proof. intros xs Hin; apply in_le_max_atom in Hin; unfold fresh_atom in *; lia. Qed.

Fixpoint ty_size (T : ty) : nat :=
  match T with
  | Ty_BVar _ | Ty_FVar _ | Ty_Bool => 1
  | Ty_Arrow A B => S (ty_size A + ty_size B)
  | Ty_All A => S (ty_size A)
  end.

Lemma ty_size_open_rec : forall T k X,
  ty_size (open_ty_rec k (Ty_FVar X) T) = ty_size T.
Proof.
  induction T; intros; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - rewrite IHT1, IHT2. reflexivity.
  - rewrite IHT. reflexivity.
  - reflexivity.
Qed.

Fixpoint lookup_context (x : atom) (Gamma : context) : option ty :=
  match Gamma with
  | [] => None
  | (y, T) :: Gamma' =>
      if Nat.eqb x y then Some T else lookup_context x Gamma'
  end.

Definition empty : context := [].

Definition update (Gamma : context) (x : atom) (T : ty) : context :=
  (x, T) :: Gamma.

Notation "x '|->' v ';' m" := (update m x v)
  (in custom systemf_tm at level 0,
   x constr at level 0,
   v custom systemf_ty,
   right associativity) : systemf_scope.
Notation "x '|->' v" := (update empty x v)
  (in custom systemf_tm at level 0,
   x constr at level 0,
   v custom systemf_ty) : systemf_scope.
Notation "'empty'" := empty
  (in custom systemf_tm) : systemf_scope.

Inductive wf_ty : ty_context -> ty -> Prop :=
  | WF_Var : forall Delta X,
      In X Delta ->
      wf_ty Delta (Ty_FVar X)
  | WF_Arrow : forall Delta T1 T2,
      wf_ty Delta T1 ->
      wf_ty Delta T2 ->
      wf_ty Delta (Ty_Arrow T1 T2)
  | WF_All :

      forall (L : list atom) Delta T,
      (forall X, ~ In X L ->
        wf_ty (X :: Delta) (open_ty T (Ty_FVar X))) ->
      wf_ty Delta (Ty_All T)
  | WF_Bool : forall Delta, wf_ty Delta Ty_Bool.

Lemma wf_ty_lc_size : forall n Delta T,
  ty_size T = n -> wf_ty Delta T -> lc_ty_at (length Delta) T.
Proof.
  intros n.
  induction n using lt_wf_ind.
  intros Delta T Hsize Hwf.
  destruct T as [i|X|A B|B|].
  - inversion Hwf.
  - constructor.
  - assert (HA : ty_size A < n) by (simpl in Hsize; lia).
    assert (HB : ty_size B < n) by (simpl in Hsize; lia).
    inversion Hwf; subst. constructor.
    + eapply H with (m := ty_size A); [exact HA|reflexivity|assumption].
    + eapply H with (m := ty_size B); [exact HB|reflexivity|assumption].
  - assert (HBsz : ty_size B < n) by (simpl in Hsize; lia).
    inversion Hwf as [| |L Delta0 B0 Hbody|]; subst.
    apply lc_ty_all.
    set (x := fresh_atom L).
    assert (Hx : ~ In x L) by (subst x; apply fresh_atom_notin).
    specialize (Hbody x Hx).
    assert (Hopen : lc_ty_at (length (x :: Delta)) (open_ty B (Ty_FVar x))).
    { eapply H with (m := ty_size (open_ty B (Ty_FVar x))).
      - unfold open_ty. rewrite ty_size_open_rec. exact HBsz.
      - reflexivity.
      - exact Hbody. }
    eapply open_ty_rec_inv_lc with (K := length (x :: Delta)) (k := 0) (X := x).
    + simpl. lia.
    + exact Hopen.
  - constructor.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at (length Delta) T.
Proof.
  intros Delta T H.
  eapply wf_ty_lc_size with (n := ty_size T); eauto.
Qed.

Lemma wf_ty_lc0 : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf; induction Hwf.
  - constructor.
  - constructor; assumption.
  - unfold locally_closed_ty. constructor.
    set (X := fresh_atom L).
    assert (HX : ~ In X L) by (subst X; apply fresh_atom_notin).
    specialize (H X HX).
    pose proof (H0 X HX) as Hopen.
    simpl in Hopen.
    eapply open_ty_rec_inv_lift with (K := 0) (U := Ty_FVar X).
    + constructor.
    + exact Hopen.
  - constructor.
Qed.

Lemma lc_ty_open : forall K T U,
  lc_ty_at (S K) T -> lc_ty_at K U -> lc_ty_at K (open_ty_rec K U T).
Proof.
  intros K T; revert K; induction T; intros K U Ht HU; simpl in *.
  - inversion Ht; subst. destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E; subst; exact HU.
    + constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion Ht; subst. constructor.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto.
  - inversion Ht; subst. constructor.
    eapply IHT; eauto using lc_ty_mono.
  - constructor.
Qed.

Inductive has_type : ty_context -> context -> tm -> ty -> Prop :=
  | T_Var : forall Delta Gamma x T,
      lookup_context x Gamma = Some T ->
      wf_ty Delta T ->
      has_type Delta Gamma (tm_fvar x) T
  | T_Abs : forall (L : list atom) Delta Gamma T1 t2 T2,
      wf_ty Delta T1 ->

      (forall x, ~ In x L ->
        has_type Delta <{ x |-> $(T1); Gamma }>
          (open_tm t2 (tm_fvar x)) T2) ->
      has_type Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2)
  | T_App : forall Delta Gamma t1 t2 T1 T2,
      has_type Delta Gamma t1 (Ty_Arrow T1 T2) ->
      has_type Delta Gamma t2 T1 ->
      has_type Delta Gamma (tm_app t1 t2) T2
  | T_TAbs : forall (L : list atom) Delta Gamma t T,
      (forall X, ~ In X L ->
        has_type (X :: Delta) Gamma
          (open_tm_ty t (Ty_FVar X))
          (open_ty T (Ty_FVar X))) ->
      has_type Delta Gamma (tm_tabs t) (Ty_All T)
  | T_TApp : forall Delta Gamma t T U,
      has_type Delta Gamma t (Ty_All T) ->
      wf_ty Delta U ->
      has_type Delta Gamma (tm_tapp t U) (open_ty T U)
  | T_True : forall Delta Gamma, has_type Delta Gamma tm_true Ty_Bool
  | T_False : forall Delta Gamma, has_type Delta Gamma tm_false Ty_Bool
  | T_If : forall Delta Gamma t1 t2 t3 T,
      has_type Delta Gamma t1 Ty_Bool ->
      has_type Delta Gamma t2 T -> has_type Delta Gamma t3 T ->
      has_type Delta Gamma (tm_if t1 t2 t3) T
  | T_Choice : forall Delta Gamma t1 t2 T,
      has_type Delta Gamma t1 T -> has_type Delta Gamma t2 T ->
      has_type Delta Gamma (tm_choice t1 t2) T.

Lemma has_type_lc_ty0 : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T Hty; induction Hty.
  - eapply wf_ty_lc0; eassumption.
  - unfold locally_closed_ty. constructor.
    + eapply wf_ty_lc0; eassumption.
    + Show. admit.
  - inversion IHHty1; assumption.
  - unfold locally_closed_ty. constructor.
    set (X := fresh_atom L).
    assert (HX : ~ In X L) by (subst X; apply fresh_atom_notin).
    specialize (H X HX).
    pose proof (has_type_lc_ty0 _ _ _ _ H) as Hopen.
    eapply open_ty_rec_inv_lift with (K := 0) (U := Ty_FVar X).
    + constructor.
    + exact Hopen.
  - pose proof (has_type_lc_ty0 _ _ _ _ Hty) as Hall.
    inversion Hall; subst.
    eapply lc_ty_open; [eassumption|eapply wf_ty_lc0; eassumption].
  - constructor.
  - constructor.
  - exact IHHty2.
  - exact IHHty1.
Qed.

Fixpoint tm_size (t : tm) : nat :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_true | tm_false => 1
  | tm_abs _ b | tm_tabs b | tm_tapp b _ => S (tm_size b)
  | tm_app a b | tm_choice a b => S (tm_size a + tm_size b)
  | tm_if c a b => S (tm_size c + tm_size a + tm_size b)
  end.

Lemma tm_size_open_rec : forall t k x,
  tm_size (open_tm_rec k (tm_fvar x) t) = tm_size t.
Proof.
  induction t; intros; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma tm_size_open_ty_rec : forall t k U,
  tm_size (open_tm_ty_rec k U t) = tm_size t.
Proof.
  induction t; intros; simpl; try reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma open_tm_rec_lc : forall K j k u t,
  lc_tm_at K j t -> open_tm_rec (k + j) u t = t.
Proof.
  intros K j k u t Hlc; revert k.
  induction Hlc; intros q; simpl.
  - match goal with
    | Hlt : ?i < ?d |- _ =>
      destruct (Nat.eqb (q + d) i) eqn:E;
      [apply Nat.eqb_eq in E; lia|reflexivity]
    end.
  - reflexivity.
  - f_equal.
    replace (S (q + k)) with (q + S k) by lia.
    apply IHHlc.
  - rewrite IHHlc1, IHHlc2. reflexivity.
  - rewrite IHHlc. reflexivity.
  - rewrite IHHlc. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHHlc1, IHHlc2, IHHlc3. reflexivity.
  - rewrite IHHlc1, IHHlc2. reflexivity.
Qed.

Lemma open_tm_rec_inv_lc : forall K k t x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  intros K k t; revert K k; induction t; intros K k x Hlc; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor. lia.
    + inversion Hlc; subst. constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor; eauto.
  - constructor.
  - constructor.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor; eauto.
Qed.

Lemma open_tm_ty_rec_inv_lc : forall K j k t X,
  k < K -> lc_tm_at K j (open_tm_ty_rec k (Ty_FVar X) t) ->
  lc_tm_at K j t.
Proof.
  intros K j k t; revert K j k; induction t;
    intros K j k X Hlt Hlc; simpl in *.
  - inversion Hlc; constructor; assumption.
  - inversion Hlc; constructor.
  - inversion Hlc; subst. econstructor.
    + eapply open_ty_rec_inv_lc; eauto.
    + eapply IHt with (K := K) (j := S j) (X := X); eauto.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor.
    eapply IHt with (K := S K) (j := j) (k := S k); eauto; lia.
  - inversion Hlc; subst. econstructor; eauto.
    eapply open_ty_rec_inv_lc; eauto.
  - constructor.
  - constructor.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor; eauto.
Qed.

Lemma open_tm_ty_rec_inv_lift : forall K j t X,
  lc_tm_at K j (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) j t.
Proof.
  intros K j t; revert K j; induction t; intros K j X Hlc; simpl in *.
  - inversion Hlc; constructor; assumption.
  - inversion Hlc; constructor.
  - inversion Hlc; subst. econstructor.
    + eapply open_ty_rec_inv_lift; [constructor|eassumption].
    + eapply IHt with (K := K) (j := S j) (X := X); eauto.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor.
    eapply IHt with (K := S K) (j := j) (X := X); eauto.
  - inversion Hlc; subst. econstructor.
    + eapply IHt; eauto.
    + eapply open_ty_rec_inv_lift; [constructor|eassumption].
  - constructor.
  - constructor.
  - inversion Hlc; subst. econstructor; eauto.
  - inversion Hlc; subst. econstructor; eauto.
Qed.


Lemma has_type_lc_size : forall n Delta Gamma t T,
  tm_size t = n -> has_type Delta Gamma t T -> lc_tm_at (length Delta) 0 t.
Proof.
  intros n; induction n using lt_wf_ind.
  intros Delta Gamma t T Hsize Hty.
  destruct Hty.
  - constructor.
  - apply lc_tm_abs.
    + eapply wf_ty_lc; eauto.
    + set (x := fresh_atom L).
      assert (Hx : ~ In x L) by (subst x; apply fresh_atom_notin).
      specialize (H1 x Hx).
      assert (Hopen : lc_tm_at (length Delta) 0 (open_tm t2 (tm_fvar x))).
      { eapply H with (m := tm_size (open_tm t2 (tm_fvar x))).
        - unfold open_tm. rewrite tm_size_open_rec. simpl in Hsize. lia.
        - reflexivity.
        - exact H1. }
      eapply open_tm_rec_inv_lc with (K := length Delta) (k := 0) (x := x).
      exact Hopen.
  - apply lc_tm_app; [eapply H with (m := tm_size t1)|eapply H with (m := tm_size t2)]; eauto; simpl in Hsize; lia.
  - apply lc_tm_tabs.
    set (X := fresh_atom L).
    assert (HX : ~ In X L) by (subst X; apply fresh_atom_notin).
    pose proof (H0 X HX) as Htyped.
    assert (Hopen : lc_tm_at (length (X :: Delta)) 0 (open_tm_ty t (Ty_FVar X))).
    { eapply H with (m := tm_size (open_tm_ty t (Ty_FVar X))).
      - unfold open_tm_ty. rewrite tm_size_open_ty_rec. simpl in Hsize. lia.
      - reflexivity.
      - exact Htyped. }
    eapply open_tm_ty_rec_inv_lc with (K := length (X :: Delta)) (j := 0) (k := 0) (X := X).
    + simpl. lia.
    + exact Hopen.
  - apply lc_tm_tapp.
    + eapply H with (m := tm_size t); eauto; simpl in Hsize; lia.
    + eapply wf_ty_lc; eauto.
  - constructor.
  - constructor.
  - apply lc_tm_if; [eapply H with (m := tm_size t1)|eapply H with (m := tm_size t2)|eapply H with (m := tm_size t3)]; eauto; simpl in Hsize; lia.
  - apply lc_tm_choice; [eapply H with (m := tm_size t1)|eapply H with (m := tm_size t2)]; eauto; simpl in Hsize; lia.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_tm_at (length Delta) 0 t.
Proof.
  intros Delta Gamma t T H.
  eapply has_type_lc_size with (n := tm_size t); eauto.
Qed.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.

Definition step_accessible (t : tm) : Prop := Acc (fun u v => step v u) t.

Lemma acc_step : forall t u, step_accessible t -> t --> u -> step_accessible u.
Proof. intros t u H S. destruct H as [Hnext]. eapply Hnext; exact S. Qed.

Lemma acc_to_sn : forall t, step_accessible t -> strongly_normalizing t.
Proof.
  intros t H. induction H as [t Hrec].
  constructor; intros u S. exact (H u S).
Qed.

Hint Constructors lc_ty_at lc_tm_at value : core.

(* Construct the logical relation and supporting proofs here. *)

(* Candidates are predicates on terms.  The interpretation of an open type is
   parameterized by the interpretation of its free type variables. *)
Definition candidate := tm -> Prop.
Definition ty_env := atom -> candidate.
Definition update_ty_env (rho : ty_env) (X : atom) (C : candidate)
    : ty_env :=
  fun Y => if Nat.eqb X Y then C else rho Y.
Definition candidate_closed (C : candidate) : Prop :=
  forall t u, C t -> t --> u -> C u.
Definition candidate_good (C : candidate) : Prop :=
  candidate_closed C /\
  (forall t, C t -> step_accessible t) /\
  (forall t, ~ value t -> (forall u, t --> u -> C u) -> C t).

Fixpoint lookup_candidate (n : nat) (bs : list candidate) : candidate :=
  match bs with
  | [] => fun _ => False
  | b :: bs' => if n =? 0 then b else lookup_candidate (Nat.pred n) bs'
  end.

Lemma lookup_candidate_closed : forall bs n,
  Forall candidate_closed bs -> candidate_closed (lookup_candidate n bs).
Proof.
  induction bs as [|C bs IH]; intros [|n] H; simpl.
  - intros t u Ht S; contradiction.
  - intros t u Ht S; contradiction.
  - inversion H; subst. intros t u Ht S. eapply H2; eauto.
  - inversion H; subst. eapply IH; eauto.
Qed.

Lemma lookup_candidate_good : forall bs n,
  n < length bs -> Forall candidate_good bs -> candidate_good (lookup_candidate n bs).
Proof.
  induction bs as [|C bs IH]; intros n Hlt H.
  - simpl in Hlt. lia.
  - destruct n; simpl.
    + inversion H; assumption.
    + inversion H; subst. apply IH; [simpl in Hlt; lia|assumption].
Qed.

Fixpoint interp_ty (rho : ty_env) (bs : list candidate) (T : ty) : candidate :=
  match T with
  | Ty_BVar n => lookup_candidate n bs
  | Ty_FVar X => rho X
  | Ty_Arrow A B => fun t =>
      step_accessible t /\
      forall v, value v -> interp_ty rho bs A v ->
        interp_ty rho bs B (tm_app t v)
  | Ty_All B => fun t =>
      step_accessible t /\
      forall (C : candidate) U, candidate_good C -> locally_closed_ty U ->
        interp_ty rho (C :: bs) B (tm_tapp t U)
  | Ty_Bool => step_accessible
  end.

Fixpoint ftv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ | Ty_Bool => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => ftv_ty A ++ ftv_ty B
  | Ty_All A => ftv_ty A
  end.

Definition prefix_eq (K : nat) (bs1 bs2 : list candidate) : Prop :=
  forall n, n < K -> forall t,
    lookup_candidate n bs1 t <-> lookup_candidate n bs2 t.

Lemma prefix_eq_cons : forall K bs1 bs2 C,
  prefix_eq K bs1 bs2 -> prefix_eq (S K) (C :: bs1) (C :: bs2).
Proof.
  intros K bs1 bs2 C H n Hn t. destruct n; simpl.
  - tauto.
  - apply H. lia.
Qed.

Lemma interp_bound_irrel : forall rho K T,
  lc_ty_at K T -> forall bs1 bs2,
  prefix_eq K bs1 bs2 -> forall t,
  interp_ty rho bs1 T t <-> interp_ty rho bs2 T t.
Proof.
  intros rho K T Hlc; induction Hlc; intros bs1 bs2 Hpre t; simpl.
  - apply Hpre; assumption.
  - tauto.
  - split.
    + intros [Hsn Happ]. split; [exact Hsn|]. intros v Hv Hr2.
      apply (proj1 (IHHlc2 bs1 bs2 Hpre (tm_app t v))).
      apply Happ; [exact Hv|].
      apply (proj2 (IHHlc1 bs1 bs2 Hpre v)); exact Hr2.
    + intros [Hsn Happ]. split; [exact Hsn|]. intros v Hv Hr1.
      apply (proj2 (IHHlc2 bs1 bs2 Hpre (tm_app t v))).
      apply Happ; [exact Hv|].
      apply (proj1 (IHHlc1 bs1 bs2 Hpre v)); exact Hr1.
  - split.
    + intros [Hsn Hall]. split; [exact Hsn|]. intros C U HC HU.
      apply (proj1 (IHHlc (C :: bs1) (C :: bs2)
        (prefix_eq_cons _ _ _ _ Hpre) (tm_tapp t U))).
      apply Hall; assumption.
    + intros [Hsn Hall]. split; [exact Hsn|]. intros C U HC HU.
      apply (proj2 (IHHlc (C :: bs1) (C :: bs2)
        (prefix_eq_cons _ _ _ _ Hpre) (tm_tapp t U))).
      apply Hall; assumption.
  - tauto.
Qed.

Lemma lookup_candidate_snoc : forall bs C n t,
  lookup_candidate n (bs ++ [C]) t <->
  if n <? length bs then lookup_candidate n bs t
  else if n =? length bs then C t else False.
Proof.
  induction bs as [|D bs IH]; intros C n t; destruct n; simpl; try reflexivity.
  simpl. rewrite IH.
  assert (Hlt : (S n <? S (length bs)) = (n <? length bs)).
  { destruct (n <? length bs) eqn:E.
    - apply Nat.ltb_lt in E. assert (S n <? S (length bs) = true) by (apply Nat.ltb_lt; lia). rewrite H. reflexivity.
    - apply Nat.ltb_ge in E. assert (S n <? S (length bs) = false) by (apply Nat.ltb_ge; lia). rewrite H. reflexivity. }
  rewrite Hlt. tauto.
Qed.

Lemma lookup_candidate_oob : forall bs n t,
  length bs <= n -> ~ lookup_candidate n bs t.
Proof.
  induction bs as [|D bs IH]; intros [|n] t Hlen; simpl in *.
  - tauto.
  - tauto.
  - lia.
  - apply IH. lia.
Qed.

Lemma lookup_candidate_in_range : forall bs n t,
  lookup_candidate n bs t -> n < length bs.
Proof.
  induction bs as [|C bs IH]; intros n t H.
  - simpl in H. contradiction.
  - destruct n as [|n].
    + simpl. lia.
    + simpl in H. specialize (IH n t H). simpl. lia.
Qed.

Lemma interp_ty_open_sem : forall rho bs k T U,
  length bs = k -> locally_closed_ty U -> forall t,
  interp_ty rho bs (open_ty_rec k U T) t <->
  interp_ty rho (bs ++ [interp_ty rho [] U]) T t.
Proof.
  intros rho bs k T; revert bs k; induction T;
    intros bs k U Hlen HU t; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst n. rewrite lookup_candidate_snoc.
      rewrite Hlen. rewrite Nat.ltb_irrefl, Nat.eqb_refl.
      apply (interp_bound_irrel rho 0 U HU bs []).
      intros m Hm z; lia.
    + rewrite lookup_candidate_snoc, Hlen.
      apply Nat.eqb_neq in E.
      destruct (n <? k) eqn:En.
      * reflexivity.
      * destruct (n =? k) eqn:Eq.
        -- apply Nat.eqb_eq in Eq; lia.
        -- apply Nat.ltb_ge in En. split.
           ++ apply lookup_candidate_oob. lia.
           ++ tauto.
  - tauto.
  - assert (H1 : forall z,
      interp_ty rho bs (open_ty_rec k U T1) z <-> interp_ty rho (bs ++ [interp_ty rho [] U]) T1 z).
    { intro z. apply IHT1; assumption. }
    assert (H2 : forall z,
      interp_ty rho bs (open_ty_rec k U T2) z <-> interp_ty rho (bs ++ [interp_ty rho [] U]) T2 z).
    { intro z. apply IHT2; assumption. }
    split.
    + intros [Hsn Happ]. split; [exact Hsn|]. intros v Hv Hr2.
      apply (proj1 (H2 (tm_app t v))).
      apply Happ; [exact Hv|apply (proj2 (H1 v)); exact Hr2].
    + intros [Hsn Happ]. split; [exact Hsn|]. intros v Hv Hr1.
      apply (proj2 (H2 (tm_app t v))).
      apply Happ; [exact Hv|apply (proj1 (H1 v)); exact Hr1].
  - split.
    + intros [Hsn Hall]. split; [exact Hsn|]. intros C V HC HV.
      apply (proj1 (@IHT (C :: bs) (S k) U ltac:(simpl; lia) HU
        (tm_tapp t V))).
      apply Hall; assumption.
    + intros [Hsn Hall]. split; [exact Hsn|]. intros C V HC HV.
      apply (proj2 (@IHT (C :: bs) (S k) U ltac:(simpl; lia) HU
        (tm_tapp t V))).
      apply Hall; assumption.
  - tauto.
Qed.


Lemma interp_ty_open_update : forall rho X C T,
  ~ In X (ftv_ty T) ->
  forall bs k, length bs = k -> forall t,
  interp_ty (update_ty_env rho X C) bs
    (open_ty_rec k (Ty_FVar X) T) t <->
  interp_ty rho (bs ++ [C]) T t.
Proof.
  intros rho X C T; induction T; intros Hfresh bs k Hlen t; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. rewrite lookup_candidate_snoc.
      rewrite Hlen. rewrite Nat.ltb_irrefl, Nat.eqb_refl.
      unfold update_ty_env. destruct (Nat.eqb X X) eqn:E.
      * change ((if Nat.eqb X X then C else rho X) t <-> C t).
        rewrite E. tauto.
      * apply Nat.eqb_neq in E; congruence.
    + rewrite lookup_candidate_snoc. rewrite Hlen.
      apply Nat.eqb_neq in E.
      destruct (n <? k) eqn:En.
      * reflexivity.
      * destruct (n =? k) eqn:Eq.
        -- apply Nat.eqb_eq in Eq. lia.
        -- apply Nat.ltb_ge in En. split; [apply lookup_candidate_oob; lia|tauto].
  - simpl in Hfresh. unfold update_ty_env.
    destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso; apply Hfresh; simpl; auto.
    + tauto.
  - simpl in Hfresh.
    assert (Hfa : ~ In X (ftv_ty T1)) by
      (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hfb : ~ In X (ftv_ty T2)) by
      (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    simpl. split.
    + intros [Hsn Happ]. split; [exact Hsn|]. intros v Hv Hr.
      pose proof (proj2 (IHT1 Hfa bs k Hlen v) Hr) as Hra.
      apply (proj1 (IHT2 Hfb bs k Hlen (tm_app t v))).
      apply Happ; assumption.
    + intros [Hsn Happ]. split; [exact Hsn|]. intros v Hv Hr.
      pose proof (proj1 (IHT1 Hfa bs k Hlen v) Hr) as Hra.
      apply (proj2 (IHT2 Hfb bs k Hlen (tm_app t v))).
      apply Happ; assumption.
  - simpl. split.
    + intros [Hsn Hall]. split; [exact Hsn|]. intros D U HD HU.
      apply (proj1 (IHT Hfresh (D :: bs) (S k) ltac:(simpl; lia) (tm_tapp t U))).
      apply Hall; assumption.
    + intros [Hsn Hall]. split; [exact Hsn|]. intros D U HD HU.
      apply (proj2 (IHT Hfresh (D :: bs) (S k) ltac:(simpl; lia) (tm_tapp t U))).
      apply Hall; assumption.
  - tauto.
Qed.

Fixpoint ty_inst (theta : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow A B => Ty_Arrow (ty_inst theta A) (ty_inst theta B)
  | Ty_All A => Ty_All (ty_inst theta A)
  | Ty_Bool => Ty_Bool
  end.

Fixpoint tm_ty_inst (theta : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T b => tm_abs (ty_inst theta T) (tm_ty_inst theta b)
  | tm_app a b => tm_app (tm_ty_inst theta a) (tm_ty_inst theta b)
  | tm_tabs b => tm_tabs (tm_ty_inst theta b)
  | tm_tapp a T => tm_tapp (tm_ty_inst theta a) (ty_inst theta T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if c a b => tm_if (tm_ty_inst theta c) (tm_ty_inst theta a) (tm_ty_inst theta b)
  | tm_choice a b => tm_choice (tm_ty_inst theta a) (tm_ty_inst theta b)
  end.

Definition update_ty_subst (theta : atom -> ty) (X : atom) (U : ty)
    : atom -> ty :=
  fun Y => if Nat.eqb X Y then U else theta Y.

Definition theta_closed (theta : atom -> ty) : Prop :=
  forall X, locally_closed_ty (theta X).

Fixpoint ftv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_true | tm_false => []
  | tm_abs T b => ftv_ty T ++ ftv_tm b
  | tm_app a b | tm_choice a b => ftv_tm a ++ ftv_tm b
  | tm_tabs b => ftv_tm b
  | tm_tapp a T => ftv_tm a ++ ftv_ty T
  | tm_if c a b => ftv_tm c ++ ftv_tm a ++ ftv_tm b
  end.

Lemma open_ty_rec_lc : forall j k U T,
  lc_ty_at j T -> open_ty_rec (k + j) U T = T.
Proof.
  intros j k U T Hlc; revert k. induction Hlc; intros q; simpl.
  - destruct (Nat.eqb (q + k) i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - rewrite IHHlc1, IHHlc2. reflexivity.
  - f_equal. replace (S (q + k)) with (q + S k) by lia. apply IHHlc.
  - reflexivity.
Qed.

Lemma ty_inst_open_rec : forall T k X theta U,
  ~ In X (ftv_ty T) -> theta_closed theta -> locally_closed_ty U ->
  ty_inst (update_ty_subst theta X U) (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (ty_inst theta T).
Proof.
  induction T; intros k X theta U Hfresh Htheta HU; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst n.
      cbn [ty_inst]. unfold update_ty_subst.
      destruct (Nat.eqb X X) eqn:Ex; [reflexivity|apply Nat.eqb_neq in Ex; congruence].
    + reflexivity.
  - unfold update_ty_subst. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso; apply Hfresh; simpl; auto.
    + replace k with (k + 0) at 1 by lia.
      rewrite open_ty_rec_lc with (j := 0) (k := k); [reflexivity|apply Htheta].
  - assert (Hfa : ~ In X (ftv_ty T1)) by
      (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hfb : ~ In X (ftv_ty T2)) by
      (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    simpl. rewrite IHT1 with (k := k) (X := X) (theta := theta) (U := U); auto.
    rewrite IHT2 with (k := k) (X := X) (theta := theta) (U := U); auto.
  - simpl. rewrite IHT with (k := S k) (X := X) (theta := theta) (U := U); auto.
  - reflexivity.
Qed.

Lemma theta_closed_update : forall theta X U,
  theta_closed theta -> locally_closed_ty U ->
  theta_closed (update_ty_subst theta X U).
Proof.
  intros theta X U Htheta HU Y. unfold update_ty_subst.
  destruct (Nat.eqb X Y); [exact HU|apply Htheta].
Qed.

Lemma notin_app_left : forall X (A B : list atom), ~ In X (A ++ B) -> ~ In X A.
Proof. intros X A B H Hin; apply H; apply in_or_app; left; exact Hin. Qed.
Lemma notin_app_right : forall X (A B : list atom), ~ In X (A ++ B) -> ~ In X B.
Proof. intros X A B H Hin; apply H; apply in_or_app; right; exact Hin. Qed.

Lemma wf_ty_inst_lc_size : forall n,
  forall theta, theta_closed theta ->
  forall Delta T, ty_size T = n -> wf_ty Delta T ->
    locally_closed_ty (ty_inst theta T).
Proof.
  intros n; induction n using lt_wf_ind.
  intros theta Htheta Delta T Hsize Hwf.
  destruct T as [i|X|A B|B|].
  - inversion Hwf.
  - simpl. apply Htheta.
  - assert (HAsz : ty_size A < n) by (simpl in Hsize; lia).
    assert (HBsz : ty_size B < n) by (simpl in Hsize; lia).
    inversion Hwf; subst. simpl. constructor.
    + eapply H with (m := ty_size A); [exact HAsz|exact Htheta|reflexivity|exact H3].
    + eapply H with (m := ty_size B); [exact HBsz|exact Htheta|reflexivity|exact H4].
  - assert (HBsz : ty_size B < n) by (simpl in Hsize; lia).
    inversion Hwf as [| |L Delta0 B0 Hbody|]; subst.
    simpl. apply lc_ty_all.
    set (x := fresh_atom (L ++ ftv_ty B)).
    assert (HxL : ~ In x L) by
      (subst x; apply notin_app_left with (B := ftv_ty B); apply fresh_atom_notin).
    assert (HxT : ~ In x (ftv_ty B)) by
      (subst x; apply notin_app_right with (A := L); apply fresh_atom_notin).
    specialize (Hbody x HxL).
    assert (Hinst : locally_closed_ty (ty_inst (update_ty_subst theta x Ty_Bool)
      (open_ty B (Ty_FVar x)))).
    { eapply H with (m := ty_size (open_ty B (Ty_FVar x))).
      - unfold open_ty. rewrite ty_size_open_rec. exact HBsz.
      - apply theta_closed_update; [exact Htheta|constructor].
      - reflexivity.
      - exact Hbody. }
    unfold open_ty in Hinst.
    rewrite (ty_inst_open_rec B 0 x theta Ty_Bool HxT Htheta ltac:(constructor)) in Hinst.
    eapply open_ty_rec_inv_lift with (K := 0) (U := Ty_Bool).
    + constructor.
    + exact Hinst.
  - constructor.
Qed.

Lemma wf_ty_inst_lc : forall theta Delta T,
  theta_closed theta -> wf_ty Delta T ->
  locally_closed_ty (ty_inst theta T).
Proof.
  intros theta Delta T Htheta Hwf.
  eapply wf_ty_inst_lc_size; eauto.
Qed.

Lemma tm_ty_inst_open_rec : forall t k X theta U,
  ~ In X (ftv_tm t) -> theta_closed theta -> locally_closed_ty U ->
  tm_ty_inst (update_ty_subst theta X U) (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (tm_ty_inst theta t).
Proof.
  induction t; intros k X theta U Hfresh Htheta HU; simpl in *.
  - reflexivity.
  - reflexivity.
  - assert (Hft : ~ In X (ftv_ty t)) by
      (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hfb : ~ In X (ftv_tm t0)) by
      (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    simpl. rewrite ty_inst_open_rec with (k := k) (X := X) (theta := theta) (U := U); auto.
    rewrite IHt with (k := k) (X := X) (theta := theta) (U := U); auto.
  - assert (Hfa : ~ In X (ftv_tm t1)) by
      (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hfb : ~ In X (ftv_tm t2)) by
      (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    simpl. rewrite IHt1 with (k := k) (X := X) (theta := theta) (U := U); auto.
    rewrite IHt2 with (k := k) (X := X) (theta := theta) (U := U); auto.
  - f_equal. apply IHt; assumption.
  - assert (Hfa : ~ In X (ftv_tm t)) by
      (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hft : ~ In X (ftv_ty t0)) by
      (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    simpl. rewrite IHt with (k := k) (X := X) (theta := theta) (U := U); auto.
    rewrite ty_inst_open_rec with (k := k) (X := X) (theta := theta) (U := U); auto.
  - reflexivity.
  - reflexivity.
  - assert (Hfc : ~ In X (ftv_tm t1)) by
      (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hfa : ~ In X (ftv_tm t2)) by
      (intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact Hin).
    assert (Hfb : ~ In X (ftv_tm t3)) by
      (intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact Hin).
    simpl. rewrite IHt1 with (k := k) (X := X) (theta := theta) (U := U); auto.
    rewrite IHt2 with (k := k) (X := X) (theta := theta) (U := U); auto.
    rewrite IHt3 with (k := k) (X := X) (theta := theta) (U := U); auto.
  - assert (Hfa : ~ In X (ftv_tm t1)) by
      (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hfb : ~ In X (ftv_tm t2)) by
      (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    simpl. rewrite IHt1 with (k := k) (X := X) (theta := theta) (U := U); auto.
    rewrite IHt2 with (k := k) (X := X) (theta := theta) (U := U); auto.
Qed.

Lemma sn_step : forall t u, strongly_normalizing t -> t --> u ->
  strongly_normalizing u.
Proof. intros t u H S; inversion H; eauto. Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; inversion H; subst; try assumption;
    unfold locally_closed_tm; constructor.
Qed.

Lemma value_no_step : forall v u, value v -> ~ (v --> u).
Proof. intros v u Hv S; inversion Hv; subst; inversion S. Qed.

Lemma accessible_of_steps : forall t,
  (forall u, t --> u -> step_accessible u) -> step_accessible t.
Proof.
  intros t H. unfold step_accessible. constructor. intros u S. apply H; exact S.
Qed.

Lemma reducible_step : forall rho bs T t u,
  (forall X, candidate_good (rho X)) ->
  Forall candidate_good bs ->
  interp_ty rho bs T t -> t --> u -> interp_ty rho bs T u.
Proof.
  intros rho bs T; revert rho bs; induction T;
    intros rho bs t u Hrho Hbs Hst Hstep; simpl in *.
  - destruct (lookup_candidate_good bs n (lookup_candidate_in_range bs n t Hst) Hbs) as [Hcl _]. eapply Hcl; eauto.
  - destruct (Hrho a) as [Hcl [Hacc Hsat]]. eapply Hcl; eauto.
  - destruct Hst as [Hacc Happ]. split.
    + eapply acc_step; eauto.
    + intros v Hv Hr. specialize (Happ v Hv Hr).
      eapply IHT2; [exact Hrho|exact Hbs|exact Happ|].
      eapply ST_App1; [exact Hstep|exact (value_lc v Hv)].
  - destruct Hst as [Hacc Hall]. split.
    + eapply acc_step; eauto.
    + intros C U HC HU. specialize (Hall C U HC HU).
      eapply IHT; [exact Hrho|constructor; assumption|exact Hall|]. econstructor; eauto.
  - eapply acc_step; eauto.
Qed.

Lemma interp_sn : forall rho bs T t,
  (forall X, candidate_good (rho X)) ->
  Forall candidate_good bs -> lc_ty_at (length bs) T ->
  interp_ty rho bs T t -> strongly_normalizing t.
Proof.
  intros rho bs T; induction T; simpl; intros t Hrho Hbs Hlc Hrel.
  - inversion Hlc; subst.
    destruct (@lookup_candidate_good bs n ltac:(assumption) Hbs) as [_ [Hacc _]].
    apply acc_to_sn. apply Hacc. exact Hrel.
  - destruct (Hrho a) as [_ [Hacc _]]. apply acc_to_sn. apply Hacc. exact Hrel.
  - destruct Hrel as [Hacc _]. apply acc_to_sn; exact Hacc.
  - destruct Hrel as [Hacc _]. apply acc_to_sn; exact Hacc.
  - apply acc_to_sn; exact Hrel.
Qed.

Lemma interp_candidate_good : forall rho bs T,
  (forall X, candidate_good (rho X)) ->
  Forall candidate_good bs -> lc_ty_at (length bs) T ->
  candidate_good (interp_ty rho bs T).
Proof.
  intros rho bs T Hrho Hbs Hlc.
  revert rho bs Hrho Hbs Hlc.
  induction T; intros rho bs Hrho Hbs Hlc; simpl.
  - inversion Hlc; subst. apply lookup_candidate_good; assumption.
  - apply Hrho.
  - inversion Hlc; subst.
    destruct (IHT2 rho bs Hrho Hbs H3) as [HclB [HaccB HsatB]].
    split.
    + intros t u Ht S.
      eapply (@reducible_step rho bs (Ty_Arrow T1 T2) t u);
        [exact Hrho|exact Hbs|exact Ht|exact S].
    + split.
      * intros t Ht. exact (proj1 Ht).
      * intros t Hnt Hnext. split.
        -- apply accessible_of_steps. intros u S. specialize (Hnext u S).
           exact (proj1 Hnext).
        -- intros v Hv Hva.
           apply HsatB.
           ++ intro Hval. inversion Hval; subst; inversion Hnt.
           ++ intros w Sw. inversion Sw; subst.
              ** exfalso. apply Hnt. constructor. assumption.
              ** exact (proj2 (Hnext _ H1) v Hv Hva).
              ** exfalso. exact (value_no_step _ _ Hv H5).
  - inversion Hlc; subst.
    split.
    + intros t u Ht S.
      eapply (@reducible_step rho bs (Ty_All T) t u);
        [exact Hrho|exact Hbs|exact Ht|exact S].
    + split.
      * intros t Ht. exact (proj1 Ht).
      * intros t Hnt Hnext. split.
        -- apply accessible_of_steps. intros u S. specialize (Hnext u S).
           exact (proj1 Hnext).
        -- intros C U HC HU.
           pose proof (IHT rho (C :: bs) Hrho
             (@Forall_cons candidate candidate_good C bs HC Hbs) H1) as HgB.
           destruct HgB as [_ [_ HsatB]]. apply HsatB.
           ++ intro Hval. inversion Hval; subst; inversion Hnt.
           ++ intros w Sw. inversion Sw; subst.
              ** exfalso. apply Hnt. constructor. assumption.
              ** exact (proj2 (Hnext _ H2) C U HC HU).
  - split.
    + intros t u Ht S. eapply acc_step; eauto.
    + split.
      * exact (fun t Ht => Ht).
      * intros t Hnt Hnext. apply accessible_of_steps. intros u S. apply Hnext; assumption.
Qed.

Definition context_realized (rho : ty_env) (Gamma : context)
    (sigma : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    interp_ty rho [] T (sigma x).

Definition update_subst (sigma : atom -> tm) (x : atom) (v : tm)
    : atom -> tm :=
  fun y => if Nat.eqb x y then v else sigma y.

Lemma lookup_context_update_eq : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof. intros; simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma lookup_context_update_neq : forall Gamma x y T,
  y <> x -> lookup_context y (update Gamma x T) = lookup_context y Gamma.
Proof.
  intros; simpl. destruct (Nat.eqb y x) eqn:E; [apply Nat.eqb_eq in E; congruence|reflexivity].
Qed.

Lemma update_subst_eq : forall sigma x v, update_subst sigma x v x = v.
Proof. intros; unfold update_subst. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma update_subst_neq : forall sigma x y v, y <> x ->
  update_subst sigma x v y = sigma y.
Proof.
  intros; unfold update_subst. destruct (Nat.eqb x y) eqn:E; [apply Nat.eqb_eq in E; congruence|reflexivity].
Qed.

Lemma context_realized_update : forall rho Gamma sigma x T v,
  context_realized rho Gamma sigma -> interp_ty rho [] T v ->
  context_realized rho (update Gamma x T) (update_subst sigma x v).
Proof.
  intros rho Gamma sigma x T v Hctx Hv y U Hlook.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E; subst y. rewrite lookup_context_update_eq in Hlook.
    inversion Hlook; subst U. rewrite update_subst_eq. exact Hv.
  - apply Nat.eqb_neq in E. rewrite lookup_context_update_neq in Hlook by congruence.
    specialize (Hctx y U Hlook). rewrite update_subst_neq by congruence. exact Hctx.
Qed.


Fixpoint subst_fvars (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T b => tm_abs T (subst_fvars sigma b)
  | tm_app a b => tm_app (subst_fvars sigma a) (subst_fvars sigma b)
  | tm_tabs b => tm_tabs (subst_fvars sigma b)
  | tm_tapp a T => tm_tapp (subst_fvars sigma a) T
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if c a b => tm_if (subst_fvars sigma c) (subst_fvars sigma a) (subst_fvars sigma b)
  | tm_choice a b => tm_choice (subst_fvars sigma a) (subst_fvars sigma b)
  end.

Lemma subst_fvars_open_rec : forall sigma t x k,
  (forall y, locally_closed_tm (sigma y)) ->
  subst_fvars sigma (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (sigma x) (subst_fvars sigma t).
Proof.
  intros sigma t; induction t; intros x k Hclosed; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. replace k with (k + 0) at 1 by lia.
    eapply open_tm_rec_lc with (K := 0) (j := 0). apply Hclosed.
  - f_equal. apply IHt; assumption.
  - rewrite IHt1, IHt2; auto.
  - f_equal. apply IHt; auto.
  - f_equal. apply IHt; auto.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2, IHt3; auto.
  - rewrite IHt1, IHt2; auto.
Qed.

Lemma subst_fvars_open : forall sigma t x,
  (forall y, locally_closed_tm (sigma y)) ->
  subst_fvars sigma (open_tm t (tm_fvar x)) =
  open_tm (subst_fvars sigma t) (sigma x).
Proof. intros; apply subst_fvars_open_rec; assumption. Qed.

Lemma sn_choice : forall t1 t2,
  strongly_normalizing t1 -> strongly_normalizing t2 ->
  strongly_normalizing (tm_choice t1 t2).
Proof.
  intros t1 t2 H1 H2.
  constructor; intros u S; inversion S; subst; assumption.
Qed.

(* Erase type annotations and type-level redexes. *)
Fixpoint erase_tm (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs _ b => tm_abs Ty_Bool (erase_tm b)
  | tm_app a b => tm_app (erase_tm a) (erase_tm b)
  | tm_tabs b => erase_tm b
  | tm_tapp a _ => erase_tm a
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if c a b => tm_if (erase_tm c) (erase_tm a) (erase_tm b)
  | tm_choice a b => tm_choice (erase_tm a) (erase_tm b)
  end.

Inductive evalue : tm -> Prop :=
| ev_abs : forall T b, locally_closed_tm (tm_abs T b) -> evalue (tm_abs T b)
| ev_true : evalue tm_true
| ev_false : evalue tm_false.

Reserved Notation "t1 '==>' t2" (at level 40).
Inductive estep : tm -> tm -> Prop :=
| ES_AppAbs : forall T b v, locally_closed_tm (tm_abs T b) -> evalue v ->
    tm_app (tm_abs T b) v ==> open_tm b v
| ES_App1 : forall a a' b, a ==> a' -> tm_app a b ==> tm_app a' b
| ES_App2 : forall v b b', evalue v -> b ==> b' -> tm_app v b ==> tm_app v b'
| ES_IfTrue : forall a b, tm_if tm_true a b ==> a
| ES_IfFalse : forall a b, tm_if tm_false a b ==> b
| ES_If : forall c c' a b, c ==> c' -> tm_if c a b ==> tm_if c' a b
| ES_ChoiceLeft : forall a b, tm_choice a b ==> a
| ES_ChoiceRight : forall a b, tm_choice a b ==> b
where "t1 '==>' t2" := (estep t1 t2).

Definition eacc (t : tm) := Acc (fun u v => estep v u) t.
Lemma eacc_step : forall t u, eacc t -> t ==> u -> eacc u.
Proof. intros t u H S; destruct H as [H]; eapply H; exact S. Qed.
Inductive esn : tm -> Prop := ESN_intro : forall t,
  (forall u, t ==> u -> esn u) -> esn t.
Lemma eacc_to_esn : forall t, eacc t -> esn t.
Proof. intros t H; induction H as [t Hnext IH]. constructor; intros u S. apply IH; exact S. Qed.

Lemma lc_ty_dec : forall K T, {lc_ty_at K T}+{~ lc_ty_at K T}.
Proof.
  intros K T; revert K; induction T; intros K.
  - destruct (lt_dec n K) as [Hlt|Hnlt].
    + left; constructor; exact Hlt.
    + right; intro H; inversion H; lia.
  - left; constructor.
  - { destruct (IHT1 K) as [Ha|Ha]; destruct (IHT2 K) as [Hb|Hb].
      all: try (left; constructor; assumption).
      all: right; intro H; inversion H; subst; intuition. }
  - { destruct (IHT (S K)) as [Hlc|Hbad].
      + left; constructor; exact Hlc.
      + right; intro H; inversion H; contradiction. }
  - left; constructor.
Defined.

Lemma lc_tm_dec : forall K j t, {lc_tm_at K j t}+{~ lc_tm_at K j t}.
Proof.
  intros K j t; revert K j; induction t; intros K j.
  - destruct (lt_dec n j) as [Hlt|Hnlt].
    + left; constructor; exact Hlt.
    + right; intro H; inversion H; lia.
  - left; constructor.
  - destruct (lc_ty_dec K t) as [HT|HT], (IHt K (S j)) as [Hb|Hb].
    + left; apply lc_tm_abs; assumption.
    + right; intro H; inversion H; contradiction.
    + right; intro H; inversion H; contradiction.
    + right; intro H; inversion H; contradiction.
  - destruct (IHt1 K j) as [H1|H1], (IHt2 K j) as [H2|H2].
    + left; apply lc_tm_app; assumption.
    + right; intro H; inversion H; contradiction.
    + right; intro H; inversion H; contradiction.
    + right; intro H; inversion H; contradiction.
  - destruct (IHt (S K) j) as [Hbody|Hbody].
    + left; apply lc_tm_tabs; assumption.
    + right; intro H; inversion H; contradiction.
  - destruct (IHt K j) as [Ht|Ht], (lc_ty_dec K t0) as [HT|HT].
    + left; apply lc_tm_tapp; assumption.
    + right; intro H; inversion H; contradiction.
    + right; intro H; inversion H; contradiction.
    + right; intro H; inversion H; contradiction.
  - left; constructor.
  - left; constructor.
  - destruct (IHt1 K j) as [H1|H1], (IHt2 K j) as [H2|H2], (IHt3 K j) as [H3|H3].
    + left; apply lc_tm_if; assumption.
    + right; intro H; inversion H; intuition.
    + right; intro H; inversion H; intuition.
    + right; intro H; inversion H; intuition.
    + right; intro H; inversion H; intuition.
    + right; intro H; inversion H; intuition.
    + right; intro H; inversion H; intuition.
    + right; intro H; inversion H; intuition.
  - destruct (IHt1 K j) as [H1|H1], (IHt2 K j) as [H2|H2].
    + left; apply lc_tm_choice; assumption.
    + right; intro H; inversion H; intuition.
    + right; intro H; inversion H; intuition.
    + right; intro H; inversion H; intuition.
Defined.

Lemma evalue_dec : forall t, {evalue t}+{~ evalue t}.
Proof.
  intros t; destruct t.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - destruct (lc_tm_dec 0 0 (tm_abs t t0)) as [Hlc|Hnlc].
    + left; constructor; exact Hlc.
    + right; intro Hv; inversion Hv; contradiction.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - left; constructor.
  - left; constructor.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
Defined.

Definition ecandidate := tm -> Prop.
Definition egood_closed (C : ecandidate) := forall t u, C t -> t ==> u -> C u.
Definition egood (C : ecandidate) :=
  egood_closed C /\ (forall t, C t -> eacc t) /\
  (forall t, ~ evalue t -> (forall u, t ==> u -> C u) -> C t).

Fixpoint elookup (n : nat) (bs : list ecandidate) : ecandidate :=
  match bs with
  | [] => fun _ => False
  | C :: bs' => if n =? 0 then C else elookup (Nat.pred n) bs'
  end.

Lemma elookup_good : forall bs n, n < length bs -> Forall egood bs -> egood (elookup n bs).
Proof.
  induction bs as [|C bs IH]; intros n Hlt Hg; simpl in *.
  - lia.
  - destruct n.
    + inversion Hg; assumption.
    + inversion Hg; subst. apply IH; [lia|assumption].
Qed.

Lemma elookup_in_range : forall bs n t, elookup n bs t -> n < length bs.
Proof.
  induction bs as [|C bs IH]; intros n t H; simpl in H.
  - contradiction.
  - destruct n; simpl; [lia|specialize (IH n t H); lia].
Qed.

Fixpoint erel (rho : atom -> ecandidate) (bs : list ecandidate) (T : ty) : ecandidate :=
  match T with
  | Ty_BVar n => elookup n bs
  | Ty_FVar X => rho X
  | Ty_Arrow A B => fun t => eacc t /\ forall v, evalue v -> erel rho bs A v -> erel rho bs B (tm_app t v)
  | Ty_All B => fun t => eacc t /\ forall C, egood C -> erel rho (C :: bs) B t
  | Ty_Bool => eacc
  end.

Definition egood_env (rho : atom -> ecandidate) := forall X, egood (rho X).

Lemma eif_acc : forall c a b, eacc c -> eacc a -> eacc b -> eacc (tm_if c a b).
Proof.
  intros c a b Hc. revert a b.
  induction Hc as [c Hnext IH]; intros a b Ha Hb.
  unfold eacc in *. constructor. intros u S. inversion S; subst; eauto.
Qed.

Lemma erel_step : forall rho bs T t u,
  egood_env rho -> Forall egood bs -> erel rho bs T t -> t ==> u -> erel rho bs T u.
Proof.
  intros rho bs T; revert rho bs; induction T;
    intros rho bs t u Hr Hb Hrel S; simpl in *.
  - destruct (@elookup_good bs n ltac:(eapply elookup_in_range; eauto) Hb) as [Hcl _]. eapply Hcl; eauto.
  - destruct (Hr a) as [Hcl _]. eapply Hcl; eauto.
  - destruct Hrel as [Ha Hf]. split; [eapply eacc_step; eauto|]. intros v Hv Hrv.
    specialize (Hf v Hv Hrv). eapply IHT2; eauto. econstructor; eauto.
  - destruct Hrel as [Ha Hall]. split; [eapply eacc_step; eauto|]. intros C HC.
    specialize (Hall C HC). eapply IHT; eauto.
  - eapply eacc_step; eauto.
Qed.

Lemma evalue_no_estep : forall v u, evalue v -> ~ (v ==> u).
Proof. intros v u Hv S; inversion Hv; subst; inversion S; subst; inversion H. Qed.

Lemma eacc_from_steps : forall t,
  (forall u, t ==> u -> eacc u) -> eacc t.
Proof. intros t H; constructor; intros u S; apply H; exact S. Qed.

Lemma erel_sn : forall rho bs T t,
  egood_env rho -> Forall egood bs -> lc_ty_at (length bs) T -> erel rho bs T t -> esn t.
Proof.
  intros rho bs T; induction T; simpl; intros t Hr Hb Hlc Hrel.
  - inversion Hlc; subst. destruct (@elookup_good bs n ltac:(assumption) Hb) as [_ [Ha _]].
    apply eacc_to_esn. eapply Ha; exact Hrel.
  - destruct (Hr a) as [_ [Ha _]]. apply eacc_to_esn. apply Ha; exact Hrel.
  - destruct Hrel as [Ha _]. apply eacc_to_esn; exact Ha.
  - destruct Hrel as [Ha _]. apply eacc_to_esn; exact Ha.
  - apply eacc_to_esn; exact Hrel.
Qed.

Lemma erel_good : forall rho bs T,
  egood_env rho -> Forall egood bs -> lc_ty_at (length bs) T -> egood (erel rho bs T).
Proof.
  intros rho bs T Hr Hb Hlc.
  revert rho bs Hr Hb Hlc.
  induction T; intros rho bs Hr Hb Hlc; simpl.
  - inversion Hlc; subst. eapply elookup_good; eauto.
  - apply Hr.
  - inversion Hlc; subst.
    destruct (IHT2 rho bs Hr Hb H3) as [HclB [HaccB HsatB]].
    split.
    + intros t u Ht S. eapply (@erel_step rho bs (Ty_Arrow T1 T2) t u); eauto.
    + split.
      * intros t Ht. exact (proj1 Ht).
      * intros t Hnt Hnext. split.
        -- apply eacc_from_steps. intros u S. exact (proj1 (Hnext u S)).
        -- intros v Hv Hva. apply HsatB.
           ++ intro Hval. inversion Hval; subst; inversion Hnt.
           ++ intros w Sw. inversion Sw; subst.
              ** exfalso. apply Hnt. apply ev_abs; assumption.
              ** exact (proj2 (Hnext _ H4) v Hv Hva).
              ** exfalso. exact (evalue_no_estep _ _ Hv H5).
  - inversion Hlc; subst.
    split.
    + intros t u Ht S. eapply (@erel_step rho bs (Ty_All T) t u); eauto.
    + split.
      * intros t Ht. exact (proj1 Ht).
      * intros t Hnt Hnext. split.
        -- apply eacc_from_steps. intros u S. exact (proj1 (Hnext u S)).
        -- intros C HC. pose proof (IHT rho (C :: bs) Hr
             (@Forall_cons ecandidate egood C bs HC Hb) H1) as HgB.
           destruct HgB as [_ [_ HsatB]]. apply HsatB.
           ++ exact Hnt.
           ++ intros w Sw. exact (proj2 (Hnext _ Sw) C HC).
  - split.
    + intros t u Ht S. eapply eacc_step; eauto.
    + split.
      * exact (fun t Ht => Ht).
      * intros t Hnt Hnext. apply eacc_from_steps. exact Hnext.
Qed.

Definition eprefix (K : nat) (bs1 bs2 : list ecandidate) :=
  forall n, n < K -> forall t, elookup n bs1 t <-> elookup n bs2 t.

Lemma eprefix_cons : forall K bs1 bs2 C,
  eprefix K bs1 bs2 -> eprefix (S K) (C :: bs1) (C :: bs2).
Proof. intros K bs1 bs2 C H n Hn t; destruct n; simpl; [tauto|apply H; lia]. Qed.

Lemma erel_bound_irrel : forall rho K T,
  lc_ty_at K T -> forall bs1 bs2, eprefix K bs1 bs2 -> forall t,
  erel rho bs1 T t <-> erel rho bs2 T t.
Proof.
  intros rho K T Hlc; induction Hlc; intros bs1 bs2 Hp t; simpl.
  - apply Hp; assumption.
  - tauto.
  - split.
    + intros [Ha Hf]; split; [exact Ha|]. intros v Hv Hr.
      apply (proj1 (IHHlc2 bs1 bs2 Hp (tm_app t v))).
      apply Hf; [exact Hv|apply (proj2 (IHHlc1 bs1 bs2 Hp v)); exact Hr].
    + intros [Ha Hf]; split; [exact Ha|]. intros v Hv Hr.
      apply (proj2 (IHHlc2 bs1 bs2 Hp (tm_app t v))).
      apply Hf; [exact Hv|apply (proj1 (IHHlc1 bs1 bs2 Hp v)); exact Hr].
  - split.
    + intros [Ha Hall]; split; [exact Ha|]. intros C HC.
      apply (proj1 (IHHlc (C::bs1) (C::bs2) (eprefix_cons _ _ _ _ Hp) t)).
      apply Hall; exact HC.
    + intros [Ha Hall]; split; [exact Ha|]. intros C HC.
      apply (proj2 (IHHlc (C::bs1) (C::bs2) (eprefix_cons _ _ _ _ Hp) t)).
      apply Hall; exact HC.
  - tauto.
Qed.

Lemma elookup_snoc : forall bs C n t,
  elookup n (bs ++ [C]) t <->
  if n <? length bs then elookup n bs t
  else if n =? length bs then C t else False.
Proof.
  induction bs as [|D bs IH]; intros C n t; destruct n; simpl; try reflexivity.
  simpl. rewrite IH.
  assert (Hlt : (S n <? S (length bs)) = (n <? length bs)).
  { destruct (n <? length bs) eqn:E; apply Nat.ltb_lt in E + apply Nat.ltb_ge in E;
      destruct (S n <? S (length bs)) eqn:F; try reflexivity; apply Nat.ltb_lt in F + apply Nat.ltb_ge in F; lia. }
  rewrite Hlt. tauto.
Qed.

Lemma elookup_oob : forall bs n t, length bs <= n -> ~ elookup n bs t.
Proof.
  induction bs as [|C bs IH]; intros [|n] t H; simpl in *; try tauto; try lia.
  apply IH; lia.
Qed.

Lemma erel_open_sem : forall rho bs k T U,
  length bs = k -> locally_closed_ty U -> forall t,
  erel rho bs (open_ty_rec k U T) t <->
  erel rho (bs ++ [erel rho [] U]) T t.
Proof.
  intros rho bs k T; revert bs k; induction T; intros bs k U Hlen HU t; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst n. rewrite elookup_snoc, Hlen.
      rewrite Nat.ltb_irrefl, Nat.eqb_refl.
      apply (erel_bound_irrel rho 0 U HU bs []); intros m Hm z; lia.
    + apply Nat.eqb_neq in E. rewrite elookup_snoc, Hlen.
      destruct (n <? k) eqn:En.
      * reflexivity.
      * destruct (n =? k) eqn:Eq.
        -- apply Nat.eqb_eq in Eq; lia.
        -- apply Nat.ltb_ge in En. split; [apply elookup_oob; lia|tauto].
  - tauto.
  - assert (H1 : forall z, erel rho bs (open_ty_rec k U T1) z <->
      erel rho (bs ++ [erel rho [] U]) T1 z) by (intro z; apply IHT1; assumption).
    assert (H2 : forall z, erel rho bs (open_ty_rec k U T2) z <->
      erel rho (bs ++ [erel rho [] U]) T2 z) by (intro z; apply IHT2; assumption).
    split.
    + intros [Ha Hf]; split; [exact Ha|]. intros v Hv Hr.
      apply (proj1 (H2 (tm_app t v))). apply Hf; [exact Hv|apply (proj2 (H1 v)); exact Hr].
    + intros [Ha Hf]; split; [exact Ha|]. intros v Hv Hr.
      apply (proj2 (H2 (tm_app t v))). apply Hf; [exact Hv|apply (proj1 (H1 v)); exact Hr].
  - split.
    + intros [Ha Hall]; split; [exact Ha|]. intros C HC.
      apply (proj1 (IHT (C::bs) (S k) U ltac:(simpl; lia) HU t)). apply Hall; exact HC.
    + intros [Ha Hall]; split; [exact Ha|]. intros C HC.
      apply (proj2 (IHT (C::bs) (S k) U ltac:(simpl; lia) HU t)). apply Hall; exact HC.
  - tauto.
Qed.

Lemma erase_open_tm_rec : forall t k u,
  erase_tm (open_tm_rec k u t) = open_tm_rec k (erase_tm u) (erase_tm t).
Proof.
  intros t; induction t; intros k u; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - reflexivity.
  - reflexivity.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma erase_open_tm_ty_rec : forall t k U, erase_tm (open_tm_ty_rec k U t) = erase_tm t.
Proof.
  intros t; induction t; intros k U; simpl; try reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - apply IHt.
  - apply IHt.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma erase_open_tm_ty : forall t U, erase_tm (open_tm_ty t U) = erase_tm t.
Proof. intros; apply erase_open_tm_ty_rec. Qed.

Definition esubst (sigma : atom -> tm) (t : tm) : tm :=
  subst_fvars sigma (erase_tm t).

Definition econtext_realized (rho : atom -> ecandidate) (Gamma : context)
    (sigma : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> erel rho [] T (sigma x).

Definition update_eenv (rho : atom -> ecandidate) (X : atom) (C : ecandidate)
    : atom -> ecandidate := fun Y => if Nat.eqb X Y then C else rho Y.

Lemma update_eenv_good : forall rho X C,
  egood_env rho -> egood C -> egood_env (update_eenv rho X C).
Proof.
  intros rho X C Hr HC Y. unfold update_eenv. destruct (Nat.eqb X Y); [exact HC|apply Hr].
Qed.

Lemma esubst_open : forall sigma t x,
  (forall y, locally_closed_tm (sigma y)) ->
  esubst sigma (open_tm t (tm_fvar x)) = open_tm (esubst sigma t) (sigma x).
Proof.
  intros sigma t x Hcl. unfold esubst, open_tm.
  rewrite erase_open_tm_rec. apply subst_fvars_open_rec; assumption.
Qed.

Lemma econtext_update : forall rho Gamma sigma x T v,
  econtext_realized rho Gamma sigma -> erel rho [] T v ->
  econtext_realized rho (update Gamma x T) (update_subst sigma x v).
Proof.
  intros rho Gamma sigma x T v Hctx Hv y U Hlook.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E; subst y. rewrite lookup_context_update_eq in Hlook.
    inversion Hlook; subst U. rewrite update_subst_eq. exact Hv.
  - apply Nat.eqb_neq in E. rewrite lookup_context_update_neq in Hlook by congruence.
    specialize (Hctx y U Hlook). rewrite update_subst_neq by congruence. exact Hctx.
Qed.

Lemma lc_tm_term_mono : forall K j t,
  lc_tm_at K j t -> lc_tm_at K (S j) t.
Proof.
  intros K j t H; induction H; eauto using lc_tm_at; try constructor; try lia.
Qed.

Lemma lc_tm_type_mono : forall K j t,
  lc_tm_at K j t -> lc_tm_at (S K) j t.
Proof.
  intros K j t H; induction H; eauto using lc_tm_at, lc_ty_mono; try constructor; try lia.
Qed.

Lemma lc_ty_raise : forall K K' T,
  K <= K' -> lc_ty_at K T -> lc_ty_at K' T.
Proof.
  intros K K' T Hle Hlc; revert K' Hle.
  induction Hlc; intros K' Hle.
  - constructor; lia.
  - constructor.
  - apply lc_ty_arrow; [eapply IHHlc1|eapply IHHlc2]; eauto.
  - apply lc_ty_all. eapply IHHlc. lia.
  - constructor.
Qed.

Lemma lc_tm_term_raise : forall K j j' t,
  j <= j' -> lc_tm_at K j t -> lc_tm_at K j' t.
Proof.
  intros K j j' t Hle Hlc; revert j' Hle.
  induction Hlc; intros j' Hle.
  - constructor; lia.
  - constructor.
  - apply lc_tm_abs; [assumption|]. eapply IHHlc; lia.
  - apply lc_tm_app; [apply IHHlc1|apply IHHlc2]; lia.
  - apply lc_tm_tabs. eapply IHHlc; eauto.
  - apply lc_tm_tapp; [eapply IHHlc; eauto|assumption].
  - constructor.
  - constructor.
  - apply lc_tm_if; [eapply IHHlc1|eapply IHHlc2|eapply IHHlc3]; eauto.
  - apply lc_tm_choice; [eapply IHHlc1|eapply IHHlc2]; eauto.
Qed.

Lemma lc_tm_type_raise : forall K K' j t,
  K <= K' -> lc_tm_at K j t -> lc_tm_at K' j t.
Proof.
  intros K K' j t Hle Hlc; revert K' Hle.
  induction Hlc; intros K' Hle.
  - constructor; assumption.
  - constructor.
  - apply lc_tm_abs; [eapply lc_ty_raise|eapply IHHlc]; eauto; lia.
  - apply lc_tm_app; [eapply IHHlc1|eapply IHHlc2]; eauto.
  - apply lc_tm_tabs. eapply IHHlc. lia.
  - apply lc_tm_tapp; [eapply IHHlc|eapply lc_ty_raise]; eauto; lia.
  - constructor.
  - constructor.
  - apply lc_tm_if; [eapply IHHlc1|eapply IHHlc2|eapply IHHlc3]; eauto.
  - apply lc_tm_choice; [eapply IHHlc1|eapply IHHlc2]; eauto.
Qed.

Lemma subst_fvars_lc_at : forall K k t sigma,
  lc_tm_at K k t -> (forall x, lc_tm_at K 0 (sigma x)) ->
  lc_tm_at K k (subst_fvars sigma t).
Proof.
  intros K k t; revert K k; induction t; intros K k sigma Hlc Hsig; simpl.
  - inversion Hlc; subst. constructor; assumption.
  - eapply lc_tm_term_raise with (j := 0); [lia|apply Hsig].
  - inversion Hlc; subst. apply lc_tm_abs; [assumption|].
    eapply IHt; [eassumption|exact Hsig].
  - inversion Hlc; subst. apply lc_tm_app; [eapply IHt1|eapply IHt2]; eauto.
  - inversion Hlc; subst. apply lc_tm_tabs. eapply IHt; [eassumption|].
    intro x. pose proof (Hsig x) as Hx. apply lc_tm_type_mono with (K := K) (j := 0) (t := sigma x) in Hx. exact Hx.
  - inversion Hlc; subst. apply lc_tm_tapp; [eapply IHt; eauto|assumption].
  - constructor.
  - constructor.
  - inversion Hlc; subst. apply lc_tm_if; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto.
  - inversion Hlc; subst. apply lc_tm_choice; [eapply IHt1|eapply IHt2]; eauto.
Qed.

Lemma lc_subst_fvars : forall t sigma,
  locally_closed_tm t -> (forall x, locally_closed_tm (sigma x)) ->
  locally_closed_tm (subst_fvars sigma t).
Proof.
  intros t sigma Hlc Hsigma. unfold locally_closed_tm in Hlc |- *.
  eapply subst_fvars_lc_at; [exact Hlc|]. intros x. apply Hsigma.
Qed.

Lemma erase_lc : forall K j t,
  lc_tm_at K j t -> lc_tm_at 0 j (erase_tm t).
Proof.
  intros K j t H; induction H; simpl; eauto using lc_tm_at.
Qed.

Lemma esubst_lc : forall Delta Gamma t T sigma,
  has_type Delta Gamma t T ->
  (forall x, locally_closed_tm (sigma x)) -> locally_closed_tm (esubst sigma t).
Proof.
  intros Delta Gamma t T sigma Hty Hsigma. unfold esubst.
  apply lc_subst_fvars; [apply erase_lc with (K := length Delta); eapply has_type_lc; eauto|exact Hsigma].
Qed.

Lemma erel_app : forall rho bs A B f,
  egood_env rho -> Forall egood bs ->
  lc_ty_at (length bs) A -> lc_ty_at (length bs) B ->
  egood (erel rho bs B) ->
  eacc f -> erel rho bs (Ty_Arrow A B) f ->
  forall a, eacc a -> erel rho bs A a -> erel rho bs B (tm_app f a).
Proof.
  intros rho bs A B f Hr Hb HlcA HlcB HgB HaccF Hrf.
  revert Hrf.
  induction HaccF as [f Hfnext IHf]; intros Hrf a Ha Hra.
  revert Hrf.
  induction Ha as [a Hanext IHa]; intros Hrf.
  destruct (evalue_dec a) as [Hv|Hnv].
  - exact (proj2 Hrf a Hv Hra).
  - destruct HgB as [HclosedB [HaccB HsatB]].
    apply HsatB; [intro Hvapp; inversion Hvapp|]. intros w Sw. inversion Sw; subst.
    + exfalso. apply Hnv; assumption.
    + pose proof (erel_step rho bs (Ty_Arrow A B) f a' Hr Hb Hrf H2) as Hrf'.
      eapply IHf; eauto.
      apply Acc_intro. exact Hanext.
    + eapply IHa; [exact H3|eapply erel_step; eauto|exact Hrf].
Qed.

Lemma echoice_acc : forall a b, eacc a -> eacc b -> eacc (tm_choice a b).
Proof. intros a b Ha Hb. constructor; intros u S; inversion S; subst; assumption. Qed.


Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Hty.
  induction Hty.
  all: try (constructor; intros u S; inversion S).
  all: try (eapply sn_choice; eauto).
Qed.

End SystemFNormalizationIfNondeterminismHardTask.
