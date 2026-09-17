(** System F CBV strong-normalization benchmark, Hard variant.
    Features: recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationRecursionHardTask.

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
  | Ty_Nat : ty.

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
  | tm_zero : tm
  | tm_succ : tm -> tm
  | tm_natrec : tm -> tm -> tm -> tm.

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

Notation "'Nat'" := Ty_Nat (in custom systemf_ty at level 0) : systemf_scope.
Notation "'zero'" := tm_zero (in custom systemf_tm at level 0) : systemf_scope.
Notation "'succ' t" := (tm_succ t) (in custom systemf_tm at level 9, t custom systemf_tm at level 0) : systemf_scope.
Notation "'rec' n b s" := (tm_natrec n b s)
  (in custom systemf_tm at level 9, n custom systemf_tm at level 0, b custom systemf_tm at level 0, s custom systemf_tm at level 0) : systemf_scope.

Fixpoint open_ty_rec (k : nat) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => if Nat.eqb k i then U else Ty_BVar i
  | Ty_FVar X => Ty_FVar X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (open_ty_rec k U T1) (open_ty_rec k U T2)
  | Ty_All T1 => Ty_All (open_ty_rec (S k) U T1)
  | Ty_Nat => Ty_Nat
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
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (open_tm_rec k u t1)
  | tm_natrec n b f => tm_natrec (open_tm_rec k u n) (open_tm_rec k u b) (open_tm_rec k u f)
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
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (open_tm_ty_rec k U t1)
  | tm_natrec n b f => tm_natrec (open_tm_ty_rec k U n) (open_tm_ty_rec k U b) (open_tm_ty_rec k U f)
  end.

Definition open_tm_ty (t : tm) (U : ty) : tm :=
  open_tm_ty_rec 0 U t.

Fixpoint ty_subst (X : atom) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar Y => if Nat.eqb X Y then U else Ty_FVar Y
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_subst X U T1) (ty_subst X U T2)
  | Ty_All T1 => Ty_All (ty_subst X U T1)
  | Ty_Nat => Ty_Nat
  end.

Fixpoint tm_ty_subst (X : atom) (U : ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_subst X U T) (tm_ty_subst X U t1)
  | tm_app t1 t2 => tm_app (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  | tm_tabs t1 => tm_tabs (tm_ty_subst X U t1)
  | tm_tapp t1 T => tm_tapp (tm_ty_subst X U t1) (ty_subst X U T)
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_ty_subst X U t1)
  | tm_natrec n b f => tm_natrec (tm_ty_subst X U n) (tm_ty_subst X U b) (tm_ty_subst X U f)
  end.

Fixpoint tm_subst (x : atom) (s t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar y => if Nat.eqb x y then s else tm_fvar y
  | tm_abs T t1 => tm_abs T (tm_subst x s t1)
  | tm_app t1 t2 => tm_app (tm_subst x s t1) (tm_subst x s t2)
  | tm_tabs t1 => tm_tabs (tm_subst x s t1)
  | tm_tapp t1 T => tm_tapp (tm_subst x s t1) T
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_subst x s t1)
  | tm_natrec n b f => tm_natrec (tm_subst x s n) (tm_subst x s b) (tm_subst x s f)
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
  | lc_ty_nat : forall k, lc_ty_at k Ty_Nat.

Definition locally_closed_ty (T : ty) : Prop := lc_ty_at 0 T.

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
  | lc_tm_zero : forall K k, lc_tm_at K k tm_zero
  | lc_tm_succ : forall K k t, lc_tm_at K k t -> lc_tm_at K k (tm_succ t)
  | lc_tm_rec : forall K k n b s,
      lc_tm_at K k n -> lc_tm_at K k b -> lc_tm_at K k s -> lc_tm_at K k (tm_natrec n b s).

Definition locally_closed_tm (t : tm) : Prop := lc_tm_at 0 0 t.

Inductive numeric_value : tm -> Prop :=
  | nv_zero : numeric_value tm_zero
  | nv_succ : forall (n : tm), numeric_value n -> numeric_value (tm_succ n).

Fixpoint numeral (n : nat) : tm :=
  match n with O => tm_zero | S m => tm_succ (numeral m) end.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed_tm (tm_abs T t) ->
      value (tm_abs T t)
  | v_tabs : forall t,
      locally_closed_tm (tm_tabs t) ->
      value (tm_tabs t)
  | v_nat : forall n, numeric_value n -> value n.

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
  | ST_Succ : forall t t',
      t --> t' -> tm_succ t --> tm_succ t'
  | ST_RecArg : forall n n' b s,

      n --> n' -> locally_closed_tm b -> locally_closed_tm s ->
      tm_natrec n b s --> tm_natrec n' b s
  | ST_RecBase : forall n b b' s,

      numeric_value n -> b --> b' -> locally_closed_tm s ->
      tm_natrec n b s --> tm_natrec n b' s
  | ST_RecStep : forall n b s s',

      numeric_value n -> value b -> s --> s' ->
      tm_natrec n b s --> tm_natrec n b s'
  | ST_RecZero : forall b s,

      value b -> value s -> tm_natrec tm_zero b s --> b
  | ST_RecSucc : forall n b s,

      numeric_value n -> value b -> value s ->
      tm_natrec (tm_succ n) b s -->
        tm_app (tm_app s n) (tm_natrec n b s)
where "t1 '-->' t2" := (step t1 t2).

Definition ty_context := list atom.

Definition context := list (atom * ty).

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
  | WF_Nat : forall Delta, wf_ty Delta Ty_Nat.

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
  | T_Zero : forall Delta Gamma, has_type Delta Gamma tm_zero Ty_Nat
  | T_Succ : forall Delta Gamma n,
      has_type Delta Gamma n Ty_Nat -> has_type Delta Gamma (tm_succ n) Ty_Nat
  | T_Rec : forall Delta Gamma n b s T,
      has_type Delta Gamma n Ty_Nat -> has_type Delta Gamma b T ->
      has_type Delta Gamma s (Ty_Arrow Ty_Nat (Ty_Arrow T T)) ->
      has_type Delta Gamma (tm_natrec n b s) T.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.

Hint Constructors lc_ty_at lc_tm_at value : core.

(* Construct the logical relation and supporting proofs here. *)

Definition sn (t : tm) : Prop := strongly_normalizing t.

Lemma numeric_no_step : forall n u, numeric_value n -> ~ n --> u.
Proof.
  intros n u Hn; revert u; induction Hn; intros u H; inversion H; eauto.
  eapply IHHn; eauto.
Qed.

Lemma value_no_step : forall v u, value v -> ~ v --> u.
Proof.
  intros v u Hv; revert u; induction Hv; intros u H2; inversion H2; eauto using numeric_no_step.
  all: eapply (numeric_no_step n u H); eauto.
Qed.

Lemma step_deterministic : forall t u v, t --> u -> t --> v -> u = v.
Proof.
  intros t u v H1 H2; revert v H2; induction H1; intros v' H2; inversion H2; subst; try reflexivity;
    try congruence; try (f_equal; eauto); try eauto.
  all: try solve [inversion H4].
  all: try solve [inversion H1].
  all: try solve [exfalso; eapply value_no_step; eauto].
  all: try match goal with
       | [ Hv : value ?x, Hs : ?x --> ?y |- _ ] =>
           exfalso; eapply (value_no_step x y Hv); exact Hs
       end.
  all: try match goal with
       | [ Hn : numeric_value ?x, Hs : ?x --> ?y |- _ ] =>
           exfalso; eapply (numeric_no_step x y Hn); exact Hs
       end.
  all: try solve [exfalso; eapply (numeric_no_step (tm_succ n0) n'
                         (nv_succ n0 H6)); exact H1].
  all: try solve [exfalso; eapply (numeric_no_step tm_zero n'
                         nv_zero); exact H5].
  all: try solve [exfalso; eapply (numeric_no_step (tm_succ n) n'
                         (nv_succ n H)); exact H6].
  all: exact I.
Qed.

Lemma sn_back : forall t u, t --> u -> sn u -> sn t.
Proof.
  intros t u H Hu; constructor; intros v Hv.
  assert (v = u) by (eapply step_deterministic; eauto).
  subst; exact Hu.
Qed.

Lemma numeric_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof. intros n H; induction H; eauto. all: constructor; eauto. Qed.

Lemma numeric_lc_raw : forall n, numeric_value n -> lc_tm_at 0 0 n.
Proof. intros n H; induction H; constructor; eauto. Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof. intros v H; inversion H; eauto using numeric_lc. Qed.

Lemma value_lc_raw : forall v, value v -> lc_tm_at 0 0 v.
Proof. intros v H; unfold locally_closed_tm; inversion H; eauto using numeric_lc_raw. Qed.

Lemma lc_step_back : forall t u, t --> u -> locally_closed_tm u -> locally_closed_tm t.
Proof.
  unfold locally_closed_tm in *.
  intros t u H.
  induction H; intros Hu; eauto.
  all: try exact H.
  all: try (eapply lc_tm_app; eauto using value_lc_raw).
  all: try (inversion Hu; eapply IHstep; eauto).
  all: try (inversion Hu; eapply lc_tm_tapp; eauto).
  all: try (eapply lc_tm_succ; eauto).
  all: try (inversion Hu; apply IHstep; eauto).
  all: try (inversion Hu; eapply lc_tm_rec; eauto).
  all: eauto using value_lc, numeric_lc.
  all: try solve [eapply value_lc_raw; eauto].
  all: try solve [eapply lc_tm_succ; eapply numeric_lc_raw; eauto].
  all: exact I.
Qed.

Definition pred := tm -> Prop.
Definition base_pred : pred := fun t => locally_closed_tm t /\ sn t.

Definition candidate (P : pred) : Prop :=
  (forall t, P t -> locally_closed_tm t /\ sn t) /\
  (forall t u, P u -> t --> u -> P t).

Fixpoint interp (E : atom -> pred) (B : nat -> pred) (T : ty) : pred :=
  match T with
  | Ty_BVar i => B i
  | Ty_FVar X => E X
  | Ty_Nat => base_pred
  | Ty_Arrow A C =>
      fun t => locally_closed_tm t /\ sn t /\
        (forall u, interp E B A u -> interp E B C (tm_app t u))
  | Ty_All T1 =>
      fun t => locally_closed_tm t /\ sn t /\
        (forall U P, locally_closed_ty U -> candidate P ->
          interp E (fun i => match i with 0 => P | S j => B j end)
            T1 (tm_tapp t U))
  end.

Definition good_env (E : atom -> pred) : Prop := forall X, candidate (E X).
Definition good_bs (B : nat -> pred) : Prop := forall i, candidate (B i).

Lemma interp_candidate : forall E B T,
  good_env E -> good_bs B -> candidate (interp E B T).
Proof.
  intros E B T; revert E B.
  induction T as [i|X|A IHA C IHC|T IHT|]; intros E B HE HB.
  - apply HB.
  - apply HE.
  - cbn [interp]. split.
    + intros t Ht; destruct Ht as [Hlc [Hsn Hfun]]; split; assumption.
    + intros t u Hu Hstep.
      destruct Hu as [Hu_lc [Hu_sn Hu_fun]].
      split; [eapply lc_step_back; eauto|].
      split; [eapply sn_back; eauto|].
      intros v Hv.
      assert (Hv_lc : locally_closed_tm v).
      { pose proof (proj1 (IHA E B HE HB) v Hv) as Hvlc. exact (proj1 Hvlc). }
        eapply (proj2 (IHC E B HE HB) _ _).
        -- exact (Hu_fun v Hv).
        -- apply ST_App1; assumption.
  - cbn [interp]. split.
    + intros t Ht. destruct Ht as [Hlc [Hsn Hall]].
      split.
      * exact Hlc.
      * exact Hsn.
    + intros t u Hu Hstep.
      destruct Hu as [Hu_lc [Hu_sn Hu_all]].
      split.
      * eapply lc_step_back; eauto.
      * split.
        -- eapply sn_back; eauto.
        -- intros U P HUl HP.
        assert (HBP : good_bs (fun i => match i with 0 => P | S j => B j end)).
        { intro i; destruct i; [exact HP|exact (HB _)]. }
        eapply (proj2 (IHT E (fun i => match i with 0 => P | S j => B j end)
                         HE HBP) _ _).
        --- exact (Hu_all U P HUl HP).
        --- apply ST_TApp; assumption.
  - cbn [interp]. split.
    + intros t Ht; exact Ht.
    + intros t u Hu Hstep.
      destruct Hu as [Hu_lc Hu_sn].
      split; [eapply lc_step_back; eauto|eapply sn_back; eauto].
Qed.

Definition bs_shift (B : nat -> pred) (P : pred) : nat -> pred :=
  fun i => match i with 0 => P | S j => B j end.

Definition bs_replace (B : nat -> pred) (k : nat) (P : pred) : nat -> pred :=
  fun i => if Nat.eqb i k then P else B i.

Lemma interp_agree : forall E B1 B2 k T,
  (forall i, i < k -> B1 i = B2 i) ->
  lc_ty_at k T ->
  forall t, interp E B1 T t <-> interp E B2 T t.
Proof.
  intros E B1 B2 k T Hag Hlc.
  revert E B1 B2 Hag.
  induction Hlc; intros E B1 B2 Hag z.
  - cbn [interp]. rewrite (Hag i H); tauto.
  - tauto.
  - cbn [interp]. split; intros Ht.
    + destruct Ht as [H1 [H2 H3]]. split; [exact H1|]. split; [exact H2|].
      intros u Hu.
      pose proof (proj2 (IHHlc1 E B1 B2 Hag u) Hu) as Hu'.
      exact (proj1 (IHHlc2 E B1 B2 Hag (tm_app z u)) (H3 u Hu')).
    + destruct Ht as [H1 [H2 H3]]. split; [exact H1|]. split; [exact H2|].
      intros u Hu.
      pose proof (proj1 (IHHlc1 E B1 B2 Hag u) Hu) as Hu'.
      exact (proj2 (IHHlc2 E B1 B2 Hag (tm_app z u)) (H3 u Hu')).
  - cbn [interp]. split; intros Ht.
    + destruct Ht as [H1 [H2 H3]]. split; [exact H1|]. split; [exact H2|].
      intros U P HUl HP.
      assert (Hag' : forall i, i < S k ->
        (bs_shift B1 P) i = (bs_shift B2 P) i).
      { intros [|i] Hi; [reflexivity|]. simpl. apply Hag; lia. }
      exact (proj1 (IHHlc E (bs_shift B1 P) (bs_shift B2 P) Hag'
                    (tm_tapp z U)) (H3 U P HUl HP)).
    + destruct Ht as [H1 [H2 H3]]. split; [exact H1|]. split; [exact H2|].
      intros U P HUl HP.
      assert (Hag' : forall i, i < S k ->
        (bs_shift B1 P) i = (bs_shift B2 P) i).
      { intros [|i] Hi; [reflexivity|]. simpl. apply Hag; lia. }
      exact (proj2 (IHHlc E (bs_shift B1 P) (bs_shift B2 P) Hag'
                    (tm_tapp z U)) (H3 U P HUl HP)).
  - tauto.
Qed.

Lemma interp_closed : forall E B1 B2 T,
  locally_closed_ty T -> forall t, interp E B1 T t <-> interp E B2 T t.
Proof.
  intros E B1 B2 T H t.
  eapply interp_agree with (k := 0); auto.
  intros i Hi; lia.
Qed.

Lemma interp_open : forall E B k U T,
  lc_ty_at (S k) T -> locally_closed_ty U ->
  forall t,
    interp E B (open_ty_rec k U T) t <->
    interp E (bs_replace B k (interp E B U)) T t.
Proof.
  intros E B k U T Hlc HU.
  revert HU; revert U; revert E B.
  induction Hlc; intros E B U HU z.
  - cbn [open_ty_rec interp bs_replace].
    destruct (Nat.eqb k i) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst.
      unfold bs_replace; rewrite Nat.eqb_refl; reflexivity.
    + apply Nat.eqb_neq in Heq.
      assert (i < k0) by lia.
      unfold bs_replace; destruct (Nat.eqb i k) eqn:Hik;
        [ apply Nat.eqb_eq in Hik; subst; contradiction
        | reflexivity ].
  - cbn [open_ty_rec interp bs_replace]; tauto.
  - cbn [open_ty_rec interp]. split; intros Ht.
    + destruct Ht as [H1 [H2 H3]]. split; [exact H1|]. split; [exact H2|].
      intros u Hu.
      apply (proj2 (IHHlc1 E B U HU u)) in Hu.
      apply (proj1 (IHHlc2 E B U HU (tm_app z u))).
      apply H3; assumption.
    + destruct Ht as [H1 [H2 H3]]. split; [exact H1|]. split; [exact H2|].
      intros u Hu.
      apply (proj1 (IHHlc1 E B U HU u)) in Hu.
      apply (proj2 (IHHlc2 E B U HU (tm_app z u))).
      apply H3; assumption.
  - cbn [open_ty_rec interp]. split; intros Ht.
    + destruct Ht as [H1 [H2 H3]]. split; [exact H1|]. split; [exact H2|].
      intros V P HVl HP.
      set BL := bs_shift B P.
      set BM := bs_replace BL (S k) (interp E BL U).
      set BR := bs_shift (bs_replace B k (interp E B U)) P.
      assert (HA : forall i, i < S k -> BM i = BR i).
      { intros [|i] Hi; [reflexivity|].
        cbn [BM BR BL bs_shift bs_replace].
        destruct (Nat.eqb i k) eqn:He; [apply Nat.eqb_eq in He; lia|reflexivity]. }
      pose proof (IHHlc E BL U HU (tm_tapp z V)) as Hi.
      pose proof (proj1 Hi (H3 V P HVl HP)) as Hmid.
      exact (proj1 (interp_agree E BM BR (S k) T HA Hlc (tm_tapp z V)) Hmid).
    + destruct Ht as [H1 [H2 H3]]. split; [exact H1|]. split; [exact H2|].
      intros V P HVl HP.
      set BL := bs_shift B P.
      set BM := bs_replace BL (S k) (interp E BL U).
      set BR := bs_shift (bs_replace B k (interp E B U)) P.
      assert (HA : forall i, i < S k -> BM i = BR i).
      { intros [|i] Hi; [reflexivity|].
        cbn [BM BR BL bs_shift bs_replace].
        destruct (Nat.eqb i k) eqn:He; [apply Nat.eqb_eq in He; lia|reflexivity]. }
      pose proof (IHHlc E BL U HU (tm_tapp z V)) as Hi.
      pose proof (proj2 Hi (H3 V P HVl HP)) as Hmid.
      exact (proj2 (interp_agree E BM BR (S k) T HA Hlc (tm_tapp z V)) Hmid).
  - cbn [open_ty_rec interp bs_replace]; split; assumption.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End SystemFNormalizationRecursionHardTask.
