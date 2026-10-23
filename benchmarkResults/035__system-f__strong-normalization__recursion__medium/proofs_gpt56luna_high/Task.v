(** System F CBV strong-normalization benchmark, Medium variant.
    Features: recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia Wellfounded.
Import ListNotations.

Module SystemFNormalizationRecursionMediumTask.

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

(* A few elementary facts about opening.  They are kept here, rather than
   hidden in the proof of normalization, since the same facts are useful for
   both the term and type abstraction cases. *)
Lemma lc_ty_open_inv : forall k U T,
  lc_ty_at k (open_ty_rec k U T) -> lc_ty_at (S k) T.
Proof.
  intros k U T. revert k U. induction T as [i|X|T1 IH1 T2 IH2|T IH|]; intros k U H;
    simpl in H.
  - destruct (Nat.eqb k i) eqn:E.
    + constructor. apply Nat.eqb_eq in E. lia.
    + constructor. apply Nat.eqb_neq in E. inversion H. lia.
  - constructor.
  - inversion H; constructor; eauto.
  - inversion H. constructor. eauto.
  - constructor.
Qed.

Lemma lc_tm_open_inv : forall K k u t,
  lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (S k) t.
Proof.
  intros K k u t. revert K k u. induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH T| |t IH|n IHn b IHb s IHs];
    intros K k u H; simpl in H.
  - destruct (Nat.eqb k i) eqn:E.
    + constructor. apply Nat.eqb_eq in E. lia.
    + constructor. apply Nat.eqb_neq in E. inversion H. lia.
  - constructor.
  - inversion H. constructor; eauto.
  - inversion H; constructor; eauto.
  - inversion H. constructor. eauto.
  - inversion H; constructor; eauto.
  - constructor.
  - inversion H. constructor. eauto.
  - inversion H; constructor; eauto.
Qed.

Lemma lc_ty_weaken_gen : forall k0 k T, k0 <= k -> lc_ty_at k0 T -> lc_ty_at k T.
Proof.
  intros k0 k T W H. revert k W.
  induction H as [k0 i Hi | k0 X | k0 T1 T2 H1 H2 IH1 IH2 |
                  k0 T HT IH | k0]; intros k' W.
  - constructor. lia.
  - constructor.
  - constructor; eauto.
  - constructor. apply IH. lia.
  - constructor.
Qed.

Lemma lc_ty_weaken : forall k T, lc_ty_at 0 T -> lc_ty_at k T.
Proof.
  intros k T H. apply lc_ty_weaken_gen with (k0 := 0); [lia | exact H].
Qed.

Lemma lc_tm_weaken_gen : forall K0 K k0 k t,
  K0 <= K -> k0 <= k -> lc_tm_at K0 k0 t -> lc_tm_at K k t.
Proof.
  intros K0 K k0 k t WK Wk H. revert K k WK Wk.
  induction H as [K0 k0 i Hi | K0 k0 x |
                  K0 k0 T t HT Ht IHt |
                  K0 k0 t1 t2 H1 IH1 H2 IH2 |
                  K0 k0 t Ht IHt |
                  K0 k0 t T Ht IHt HT |
                  K0 k0 | K0 k0 t Ht IHt |
                  K0 k0 n b s Hn IHn Hb IHb Hs IHs];
    intros K' k' WK Wk.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply lc_ty_weaken_gen with (k0 := K0); [exact WK | exact HT].
    + apply IHt; [exact WK | lia].
  - apply lc_tm_app.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - apply lc_tm_tabs. apply IHt; [lia | exact Wk].
  - apply lc_tm_tapp.
    + apply IHt; assumption.
    + apply lc_ty_weaken_gen with (k0 := K0); [exact WK | exact HT].
  - apply lc_tm_zero.
  - apply lc_tm_succ. apply IHt; assumption.
  - apply lc_tm_rec.
    + apply IHn; assumption.
    + apply IHb; assumption.
    + apply IHs; assumption.
Qed.

Lemma lc_tm_weaken : forall K k t, lc_tm_at 0 0 t -> lc_tm_at K k t.
Proof.
  intros K k t H.
  apply lc_tm_weaken_gen with (K0 := 0) (k0 := 0); [lia | lia | exact H].
Qed.

Lemma lc_ty_open_closed_gen : forall k0 k U T,
  lc_ty_at k0 T -> k0 <= k -> open_ty_rec k U T = T.
Proof.
  intros k0 k U T H W. revert k W.
  induction H as [k0 i Hi | k0 X | k0 T1 T2 H1 H2 IH1 IH2 |
                  k0 T HT IH | k0]; intros k' W; simpl.
  - destruct (Nat.eqb k' i) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. lia.
    + reflexivity.
  - reflexivity.
  - f_equal; eauto.
  - f_equal. apply IH. lia.
  - reflexivity.
Qed.

Lemma lc_ty_open_closed : forall k U T,
  lc_ty_at 0 T -> open_ty_rec k U T = T.
Proof.
  intros k U T H. eapply lc_ty_open_closed_gen; eauto; lia.
Qed.

Lemma lc_tm_open_closed_gen : forall K k0 k u t,
  lc_tm_at K k0 t -> k0 <= k -> open_tm_rec k u t = t.
Proof.
  intros K k0 k u t H W. revert k W.
  induction H as [K k0 i Hi | K k0 x | K k0 T t HT Ht IHt |
                  K k0 t1 t2 H1 H2 IH1 IH2 | K k0 t Ht IHt |
                  K k0 t T Ht HT IHt | K k0 | K k0 t Ht IHt |
                  K k0 n b s Hn Hb Hs IHn IHb IHs];
    intros k' W; simpl.
  - destruct (Nat.eqb k' i) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. lia.
    + reflexivity.
  - reflexivity.
  - f_equal. apply IHt. lia.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - reflexivity.
  - f_equal. apply IHt. exact W.
  - f_equal; eauto.
Qed.

Lemma lc_tm_open_closed : forall k u t,
  lc_tm_at 0 0 t -> open_tm_rec k u t = t.
Proof.
  intros k u t H. eapply lc_tm_open_closed_gen; eauto; lia.
Qed.

Fixpoint ty_size (T : ty) : nat :=
  match T with
  | Ty_BVar _ | Ty_FVar _ | Ty_Nat => 1
  | Ty_Arrow T1 T2 => S (ty_size T1 + ty_size T2)
  | Ty_All T1 => S (ty_size T1)
  end.

Fixpoint tm_size (t : tm) : nat :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_zero => 1
  | tm_abs _ t1 | tm_succ t1 | tm_tabs t1 => S (tm_size t1)
  | tm_app t1 t2 => S (tm_size t1 + tm_size t2)
  | tm_tapp t1 _ => S (tm_size t1)
  | tm_natrec n b s => S (tm_size n + tm_size b + tm_size s)
  end.

Lemma ty_size_open : forall k X T,
  ty_size (open_ty_rec k (Ty_FVar X) T) = ty_size T.
Proof.
  intros k U T. revert k U.
  induction T as [i|X|T1 IH1 T2 IH2|T IH|]; intros; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite (IH (S k) U). reflexivity.
  - reflexivity.
Qed.

Lemma tm_size_open : forall k x t,
  tm_size (open_tm_rec k (tm_fvar x) t) = tm_size t.
Proof.
  intros k x t. revert k x.
  induction t as [i|y|T t IH|t1 IH1 t2 IH2|t IH|t IH T| |t IH|n IHn b IHb s IHs];
    intros; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - reflexivity.
  - rewrite (IH (S k) x). reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IHn, IHb, IHs. reflexivity.
Qed.

Lemma tm_size_open_ty : forall k U t,
  tm_size (open_tm_ty_rec k U t) = tm_size t.
Proof.
  intros k U t. revert k U.
  induction t as [| |T t IH|t1 IH1 t2 IH2|t IH|t IH T| |t IH|n IHn b IHb s IHs];
    intros; simpl; f_equal; eauto.
Qed.

Lemma tm_size_ty_subst : forall X U t, tm_size (tm_ty_subst X U t) = tm_size t.
Proof.
  intros X U t. revert X U.
  induction t as [| |T t IH|t1 IH1 t2 IH2|t IH|t IH T| |t IH|n IHn b IHb s IHs];
    intros; simpl; f_equal; eauto.
Qed.

Definition ctx_incl (D D' : ty_context) : Prop :=
  forall X, In X D -> In X D'.

Fixpoint max_list (l : list nat) : nat :=
  match l with [] => 0 | x :: l => max x (max_list l) end.

Lemma max_list_bound : forall l x, In x l -> x <= max_list l.
Proof.
  induction l as [|y l IH].
  - intros x H. inversion H.
  - intros x H. simpl in H. destruct H as [<-|H].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact H | apply Nat.le_max_r].
Qed.

Lemma fresh_not_in : forall l, ~ In (S (max_list l)) l.
Proof.
  intros l H. pose proof (max_list_bound l _ H). lia.
Qed.

Lemma wf_ty_lc : forall n T, ty_size T < n ->
  forall D, wf_ty D T -> lc_ty_at 0 T.
Proof.
  refine (fun n => well_founded_ind Nat.lt_wf_0
    (fun n => forall T, ty_size T < n -> forall D, wf_ty D T -> lc_ty_at 0 T)
    _ n).
  intros n0 IH T Hn D H.
  inversion H as [D0 X0 HX0 | D0 T1 T2 H1 H2 |
                  L0 D0 T0 HAll | D0].
  all: try (rewrite <- H3 in *).
  all: try (rewrite <- H0 in *).
  simpl in Hn.
  - constructor.
  - constructor.
    + apply IH with (y := S (ty_size T1 + ty_size T2)) (D := D0).
      * exact Hn.
      * lia.
      * exact H1.
    + apply IH with (y := S (ty_size T1 + ty_size T2)) (D := D0).
      * exact Hn.
      * lia.
      * exact H2.
  - pose (Y := S (max_list L0)).
    rewrite <- H1 in Hn.
    simpl in Hn.
    constructor.
    apply lc_ty_open_inv with (k := 0) (U := Ty_FVar Y).
    apply IH with (y := S (ty_size (open_ty T0 (Ty_FVar Y)))) (D := Y :: D0).
    + unfold open_ty. rewrite ty_size_open. exact Hn.
    + unfold open_ty. rewrite ty_size_open. lia.
    + apply HAll. apply fresh_not_in.
  - constructor.
Qed.

Lemma wf_ty_weaken : forall n T, ty_size T < n ->
  forall D D', ctx_incl D D' -> wf_ty D T -> wf_ty D' T.
Proof.
  refine (fun n => well_founded_ind Nat.lt_wf_0
    (fun n => forall T, ty_size T < n -> forall D D', ctx_incl D D' ->
       wf_ty D T -> wf_ty D' T) _ n).
  intros n0 IH T Hn D D' HD H.
  inversion H as [D0 X0 HX0 | D0 T1 T2 H1 H2 |
                  L0 D0 T0 HAll | D0].
  all: try (rewrite <- H3 in Hn).
  subst T. simpl in Hn.
  - apply WF_Var. apply HD. exact HX0.
  - constructor.
    + apply IH with (y := S (ty_size T1 + ty_size T2)) (D := D) (D' := D').
      * exact Hn.
      * lia.
      * exact HD.
      * exact H1.
    + apply IH with (y := S (ty_size T1 + ty_size T2)) (D := D) (D' := D').
      * exact Hn.
      * lia.
      * exact HD.
      * exact H2.
  - apply WF_All with (L := L0).
    rewrite <- H1 in Hn.
    intros Y HY. apply IH with
      (y := S (ty_size (open_ty T0 (Ty_FVar Y))))
      (D := Y :: D) (D' := Y :: D').
    + unfold open_ty. rewrite ty_size_open. exact Hn.
    + unfold open_ty. rewrite ty_size_open. lia.
    + intros Z HZ. destruct HZ as [<-|HZ].
      * apply in_eq.
      * apply in_cons. apply HD. exact HZ.
    + apply HAll. exact HY.
  - constructor.
Qed.

Lemma ty_subst_open_ty_rec : forall X U Y k T,
  locally_closed_ty U -> X <> Y ->
  ty_subst X U (open_ty_rec k (Ty_FVar Y) T) =
  open_ty_rec k (Ty_FVar Y) (ty_subst X U T).
Proof.
  intros X U Y k T HU HXY. revert U Y k HXY HU.
  induction T as [i|Z|T1 IH1 T2 IH2|T IH|];
    intros U Y k HXY HU; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + destruct (Nat.eqb X Y) eqn:E2; simpl.
      * apply Nat.eqb_eq in E2. contradiction.
      * rewrite E2. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb X Z) eqn:E; simpl.
    + symmetry. apply lc_ty_open_closed_gen with (k0 := 0); [exact HU | lia].
    + reflexivity.
  - rewrite IH1, IH2; auto.
  - rewrite IH; auto.
  - reflexivity.
Qed.

Lemma ty_subst_open_ty : forall X U Y T,
  locally_closed_ty U -> X <> Y ->
  ty_subst X U (open_ty T (Ty_FVar Y)) =
  open_ty (ty_subst X U T) (Ty_FVar Y).
Proof.
  intros. unfold open_ty. apply ty_subst_open_ty_rec; assumption.
Qed.

Lemma wf_ty_subst : forall n T, ty_size T < n ->
  forall D X U, ~ In X D -> wf_ty (X :: D) T -> wf_ty D U ->
    wf_ty D (ty_subst X U T).
Proof.
  refine (fun n => well_founded_ind Nat.lt_wf_0
    (fun n => forall T, ty_size T < n -> forall D X U, ~ In X D ->
       wf_ty (X :: D) T -> wf_ty D U -> wf_ty D (ty_subst X U T)) _ n).
  intros n0 IH T Hn D X U HX H Uwf.
  inversion H as [D0 X0 HX0 | D0 T1 T2 H1 H2 |
                  L0 D0 T0 HAll | D0].
  all: try (rewrite <- H3 in Hn).
  subst T. simpl in Hn.
  - destruct (Nat.eqb X X0) eqn:E.
    + apply Nat.eqb_eq in E. subst X0. cbn [ty_subst].
      destruct (Nat.eqb X X) eqn:E2; simpl.
      * exact Uwf.
      * apply Nat.eqb_neq in E2. contradiction.
    + cbn [ty_subst]. rewrite E. apply WF_Var. simpl in HX0. destruct HX0 as [<-|HX0].
      * apply Nat.eqb_neq in E. contradiction.
      * exact HX0.
  - constructor.
    + apply IH with (y := S (ty_size T1 + ty_size T2)) (D := D) (X := X) (U := U).
      * exact Hn.
      * lia.
      * exact HX.
      * exact H1.
      * exact Uwf.
    + apply IH with (y := S (ty_size T1 + ty_size T2)) (D := D) (X := X) (U := U).
      * exact Hn.
      * lia.
      * exact HX.
      * exact H2.
      * exact Uwf.
  - apply WF_All with (L := X :: L0).
    intros Y HY.
    assert (Y <> X) as HYX.
    { intro E. subst. apply HY. left; reflexivity. }
    rewrite <- H1 in Hn.
    simpl in Hn.
    rewrite <- ty_subst_open_ty; auto.
    apply IH with (y := S (ty_size (open_ty T0 (Ty_FVar Y))))
      (D := Y :: D) (X := X) (U := U).
    + unfold open_ty. rewrite ty_size_open. exact Hn.
    + unfold open_ty. rewrite ty_size_open. lia.
    + unfold not. intro HZ. simpl in HZ. destruct HZ as [E|HZ].
      * apply HYX. exact E.
      * apply HX. exact HZ.
    + eapply (wf_ty_weaken
        (S (ty_size (open_ty T0 (Ty_FVar Y))))
        (open_ty T0 (Ty_FVar Y))
        (Nat.lt_succ_diag_r _) (Y :: X :: D) (X :: Y :: D)).
      * unfold ctx_incl. intro Z. intro HZ. cbn in HZ. cbn.
        destruct HZ as [E|HZ].
        -- right. left. exact E.
        -- simpl in HZ. destruct HZ as [E|HZ].
           ++ left. exact E.
           ++ right. right. exact HZ.
      * apply HAll. intro HZ. apply HY. right. exact HZ.
    + eapply (wf_ty_weaken (S (ty_size U)) U (Nat.lt_succ_diag_r _) D (Y :: D)).
      * unfold ctx_incl. intro Z. intro HZ. simpl. right. exact HZ.
      * exact Uwf.
    + apply wf_ty_lc with (n := S (ty_size U)) (D := D);
      [ apply Nat.lt_succ_diag_r | exact Uwf ].
  - constructor.
Qed.

Lemma lc_ty_subst_at : forall K X U T,
  lc_ty_at K T -> locally_closed_ty U -> lc_ty_at K (ty_subst X U T).
Proof.
  intros K X U T H HU.
  induction H as [K0 i Hi | K0 X0 | K0 T1 T2 H1 H2 IH1 IH2 |
                  K0 T HT IH | K0]; simpl.
  - constructor.
  - destruct (Nat.eqb X X0) eqn:E; simpl.
    + apply lc_ty_weaken with (k := K). exact HU.
    + constructor.
  - constructor; eauto.
  - constructor; eauto.
  - constructor. eauto.
Qed.

Lemma lc_tm_ty_subst_at : forall K k X U t,
  lc_tm_at K k t -> locally_closed_ty U ->
  lc_tm_at K k (tm_ty_subst X U t).
Proof.
  intros K k X U t H HU. induction H; simpl.
  - constructor.
  - constructor.
  - constructor; eauto using lc_ty_subst_at.
  - constructor; eauto.
  - constructor. eauto.
  - constructor; eauto using lc_ty_subst_at.
  - constructor.
  - constructor. eauto.
  - constructor; eauto.
Qed.

Definition type_substitution := atom -> ty.

Definition term_substitution := atom -> tm.

Fixpoint instantiate_ty (theta : type_substitution) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (instantiate_ty theta T1) (instantiate_ty theta T2)
  | Ty_All T1 => Ty_All (instantiate_ty theta T1)
  | Ty_Nat => Ty_Nat
  end.

Fixpoint instantiate
    (theta : type_substitution) (gamma : term_substitution) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => gamma x
  | tm_abs T t1 => tm_abs (instantiate_ty theta T) (instantiate theta gamma t1)
  | tm_app t1 t2 => tm_app (instantiate theta gamma t1) (instantiate theta gamma t2)
  | tm_tabs t1 => tm_tabs (instantiate theta gamma t1)
  | tm_tapp t1 T => tm_tapp (instantiate theta gamma t1) (instantiate_ty theta T)
  | tm_zero => tm_zero
  | tm_succ t => tm_succ (instantiate theta gamma t)
  | tm_natrec n b s => tm_natrec (instantiate theta gamma n) (instantiate theta gamma b) (instantiate theta gamma s)
  end.

Definition type_substitution_closed (theta : type_substitution) : Prop :=
  forall X : atom, locally_closed_ty (theta X).

Definition term_substitution_closed (gamma : term_substitution) : Prop :=
  forall x : atom, locally_closed_tm (gamma x).

Definition relation := tm -> Prop.
Record value_candidate := {
  candidate_relation : relation;
  candidate_values : forall v, candidate_relation v -> value v
}.
Definition relation_env := atom -> option value_candidate.
Definition relation_update (rho : relation_env) (X : atom) (a : value_candidate) :=
  fun Y => if Nat.eqb X Y then Some a else rho Y.

Definition expression_lifting (R : relation) (t : tm) : Prop :=
  locally_closed_tm t /\ strongly_normalizing t /\
  forall v, t -->* v -> value v -> R v.

Fixpoint value_relation (eta : list value_candidate) (rho : relation_env)
    (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_BVar i =>
      match nth_error eta i with Some a => a.(candidate_relation) v | None => False end
  | Ty_FVar X =>
      match rho X with Some a => a.(candidate_relation) v | None => False end
  | Ty_Arrow T1 T2 =>
      value v /\ exists U body, v = tm_abs U body /\
      forall arg, value_relation eta rho T1 arg ->
        expression_lifting (value_relation eta rho T2) (open_tm body arg)
  | Ty_All T =>
      value v /\ exists body, v = tm_tabs body /\
      forall (U : ty) (a : value_candidate), locally_closed_ty U ->
        expression_lifting (value_relation (a :: eta) rho T) (open_tm_ty body U)
  | Ty_Nat => value v /\ numeric_value v
  end.

Definition expression_relation eta rho T t :=
  expression_lifting (value_relation eta rho T) t.

Definition related_substitution (rho : relation_env) (Gamma : context)
    (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> value_relation [] rho T (gamma x).

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End SystemFNormalizationRecursionMediumTask.
