(** System F CBV strong-normalization benchmark, Hard variant.
    Features: nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationNondeterminismRecursionHardTask.

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
  | tm_natrec : tm -> tm -> tm -> tm
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

Notation "'Nat'" := Ty_Nat (in custom systemf_ty at level 0) : systemf_scope.
Notation "'zero'" := tm_zero (in custom systemf_tm at level 0) : systemf_scope.
Notation "'succ' t" := (tm_succ t) (in custom systemf_tm at level 9, t custom systemf_tm at level 0) : systemf_scope.
Notation "'rec' n b s" := (tm_natrec n b s)
  (in custom systemf_tm at level 9, n custom systemf_tm at level 0, b custom systemf_tm at level 0, s custom systemf_tm at level 0) : systemf_scope.
Notation "'choice' t1 'or' t2" := (tm_choice t1 t2)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm at level 200) : systemf_scope.

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
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (open_tm_ty_rec k U t1)
  | tm_natrec n b f => tm_natrec (open_tm_ty_rec k U n) (open_tm_ty_rec k U b) (open_tm_ty_rec k U f)
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
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_subst x s t1)
  | tm_natrec n b f => tm_natrec (tm_subst x s n) (tm_subst x s b) (tm_subst x s f)
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
      lc_tm_at K k n -> lc_tm_at K k b -> lc_tm_at K k s -> lc_tm_at K k (tm_natrec n b s)
  | lc_tm_choice : forall K k t1 t2,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k (tm_choice t1 t2).

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
      has_type Delta Gamma (tm_natrec n b s) T
  | T_Choice : forall Delta Gamma t1 t2 T,
      has_type Delta Gamma t1 T -> has_type Delta Gamma t2 T ->
      has_type Delta Gamma (tm_choice t1 t2) T.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.

Hint Constructors lc_ty_at lc_tm_at value : core.

(* Construct the logical relation and supporting proofs here. *)

Lemma lc_ty_weaken : forall k T, lc_ty_at k T -> lc_ty_at (S k) T.
Proof.
  intros k T H; induction H; eauto; lia.
Qed.

Fixpoint inst (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_abs T t1 => tm_abs T (inst rho t1)
  | tm_app t1 t2 => tm_app (inst rho t1) (inst rho t2)
  | tm_tabs t1 => tm_tabs (inst rho t1)
  | tm_tapp t1 T => tm_tapp (inst rho t1) T
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (inst rho t1)
  | tm_natrec n b s => tm_natrec (inst rho n) (inst rho b) (inst rho s)
  | tm_choice t1 t2 => tm_choice (inst rho t1) (inst rho t2)
  end.

Definition rho_upd (rho : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else rho y.

Lemma sn_step : forall t u, strongly_normalizing t -> t --> u -> strongly_normalizing u.
Proof. intros t u H Hs; inversion H; eauto. Qed.

Lemma sn_abs : forall T t, strongly_normalizing (tm_abs T t).
Proof. intros; constructor; intros u H; inversion H. Qed.
Lemma sn_tabs : forall t, strongly_normalizing (tm_tabs t).
Proof. intros; constructor; intros u H; inversion H. Qed.
Lemma sn_succ : forall n, strongly_normalizing n -> strongly_normalizing (tm_succ n).
Proof.
  intros n H; induction H as [n Hred IH].
  constructor; intros u Hu; inversion Hu; subst; apply IH; assumption.
Qed.
Lemma sn_num : forall n, numeric_value n -> strongly_normalizing n.
Proof.
  intros n H; induction H.
  - constructor; intros u Hu; inversion Hu.
  - apply sn_succ; assumption.
Qed.

Lemma sn_value : forall v, value v -> strongly_normalizing v.
Proof.
  intros v H; destruct H; eauto using sn_abs, sn_tabs, sn_num.
Qed.

Definition pred := tm -> Prop.
Definition cand (P : pred) : Prop := forall t u, P t -> t --> u -> P u.
Fixpoint list_cand (B : list pred) : Prop :=
  match B with [] => True | P :: B => cand P /\ list_cand B end.

Lemma nth_list_cand : forall B i P, list_cand B -> nth_error B i = Some P -> cand P.
Proof.
  intros B; induction B as [|Q B IH]; intros i P HC E.
  - destruct i; simpl in E; inversion E.
  - destruct i; simpl in E.
    + inversion E; subst; exact (proj1 HC).
    + apply IH with (i := i) (P := P); [exact (proj2 HC)|exact E].
Qed.

Fixpoint sem (E : atom -> pred) (B : list pred) (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_BVar i => match nth_error B i with Some P => P t | None => False end
  | Ty_FVar X => E X t
  | Ty_Nat => strongly_normalizing t
  | Ty_Arrow A C => strongly_normalizing t /\
      forall u, locally_closed_tm u -> sem E B A u -> sem E B C (tm_app t u)
  | Ty_All A => strongly_normalizing t /\
      forall U, locally_closed_ty U -> forall P, cand P ->
        sem E (P :: B) A (tm_tapp t U)
  end.

Lemma sem_step : forall E B T t u,
    (forall X, cand (E X)) -> list_cand B ->
    sem E B T t -> t --> u -> sem E B T u.
Proof.
  intros E B T; revert E B; induction T as [i|X|A IHA C IHC|A IHA|];
    intros E B t u HE HB H Hs; simpl in *.
  - destruct (nth_error B i) as [p|] eqn:EQ.
    + eapply (nth_list_cand B i p HB); eauto.
    + exact (False_rect _ H).
  - eapply (HE X); eauto.
  - destruct H as [Hsnt Hfun]; split; [eapply sn_step; eauto|].
    intros v Hvl Hv; eapply IHC; [exact HE|exact HB|apply Hfun; [exact Hvl|exact Hv]|].
    apply ST_App1; assumption.
  - destruct H as [Hsnt Hfun]; split; [eapply sn_step; eauto|].
    intros U HUl P HP; eapply IHA with (t := tm_tapp t U) (u := tm_tapp u U).
    + exact HE.
    + split; assumption.
    + apply Hfun; [exact HUl|exact HP].
    + apply ST_TApp; assumption.
  - apply sn_step with t; assumption.
Qed.

Lemma lc_ty_closed : forall k T, lc_ty_at 0 T -> lc_ty_at k T.
Proof.
  intros k T H; induction k; simpl; auto.
  apply lc_ty_weaken; assumption.
Qed.

Lemma lc_tm_weaken : forall K k t, lc_tm_at K k t -> lc_tm_at K (S k) t.
Proof.
  intros K k t H; induction H; eauto; lia.
Qed.

Lemma lc_tm_closed : forall K k t, lc_tm_at K 0 t -> lc_tm_at K k t.
Proof.
  intros K k t H; induction k; simpl; auto.
  apply lc_tm_weaken; assumption.
Qed.

Lemma lc_tm_type_weaken : forall K k t, lc_tm_at K k t -> lc_tm_at (S K) k t.
Proof.
  intros K k t H; induction H; eauto.
  all: try (constructor; eauto using lc_ty_weaken).
Qed.

Lemma lc_ty_open_closed : forall k T U,
    lc_ty_at (S k) T -> lc_ty_at 0 U ->
    lc_ty_at k (open_ty_rec k U T).
Proof.
  intros k T U; revert k U; induction T; intros k U H HU; simpl in *.
  - inversion H; subst; destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; apply lc_ty_closed; assumption.
    + constructor; apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion H; subst; constructor; eauto using lc_tm_type_weaken.
  - inversion H; subst; constructor; eauto.
  - constructor.
Qed.

Lemma lc_tm_open_closed : forall K k t u,
    lc_tm_at K (S k) t -> lc_tm_at K 0 u ->
    lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k t u; revert K k u; induction t; intros K k u H HU; simpl in *.
  - inversion H; subst; destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; apply lc_tm_closed; exact HU.
    + constructor; apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion H; subst; constructor; eauto using lc_ty_weaken.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto using lc_tm_type_weaken.
  - inversion H; subst; constructor; eauto using lc_ty_weaken.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma lc_tm_ty_open_closed : forall K k t U,
    lc_tm_at (S K) k t -> lc_ty_at 0 U ->
    lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros K k t U; revert K k U; induction t;
    intros K k U H HU; simpl in *.
  - inversion H; subst; constructor; assumption.
  - constructor.
  - inversion H; subst; constructor; eauto using lc_ty_open_closed.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto using lc_tm_type_weaken.
  - inversion H; subst; constructor; eauto using lc_ty_open_closed.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma lc_tm_subst_closed : forall K k t x s,
    lc_tm_at K k t -> lc_tm_at K 0 s ->
    lc_tm_at K k (tm_subst x s t).
Proof.
  intros K k t x s; revert K k x s; induction t;
    intros K k x s H HS; simpl in *.
  - inversion H; subst; constructor; assumption.
  - inversion H; subst; destruct (Nat.eqb x a) eqn:E.
    + apply lc_tm_closed; exact HS.
    + constructor.
  - inversion H; subst; constructor; eauto using lc_ty_weaken.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto using lc_tm_type_weaken.
  - inversion H; subst; constructor; eauto using lc_ty_weaken.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma numeric_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof.
  intros n H; induction H; unfold locally_closed_tm in *; eauto.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; destruct H as [T t Hlc | t Hlc | n Hn].
  - exact Hlc.
  - exact Hlc.
  - apply numeric_lc; exact Hn.
Qed.

Lemma lc_step : forall t u, locally_closed_tm t -> t --> u -> locally_closed_tm u.
Proof.
  intros t u Hlc Hs; unfold locally_closed_tm in *.
  induction Hs; inversion Hlc; subst; eauto using lc_tm_open_closed,
    lc_tm_ty_open_closed, numeric_lc, value_lc.
  - apply lc_tm_open_closed.
    + inversion H; assumption.
    + apply value_lc; exact H0.
  - apply lc_tm_ty_open_closed.
    + inversion H; assumption.
    + exact H0.
  - constructor.
    + constructor.
      * exact H9.
      * apply numeric_lc; exact H.
    + constructor.
      * apply numeric_lc; exact H.
      * exact H8.
      * exact H9.
Qed.

Lemma open_tm_closed : forall K k t u,
    lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  intros K k t u H; induction H; simpl; try rewrite IHlc_tm_at;
    try rewrite IHlc_tm_at0; try rewrite IHlc_tm_at1; try rewrite IHlc_tm_at2;
    try rewrite IHlc_tm_at3; try reflexivity.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + reflexivity.
Qed.

Lemma ty_open_closed : forall K T U,
    lc_ty_at K T -> open_ty_rec K U T = T.
Proof.
  intros K T U H; induction H; simpl; try rewrite IHlc_ty_at;
    try rewrite IHlc_ty_at0; try rewrite IHlc_ty_at1; try rewrite IHlc_ty_at2; try reflexivity.
  destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
Qed.

Lemma open_ty_closed : forall K k t U,
    lc_tm_at K k t -> open_tm_ty_rec K U t = t.
Proof.
  intros K k t U H; induction H; simpl; try rewrite IHlc_tm_at;
    try rewrite IHlc_tm_at0; try rewrite IHlc_tm_at1; try rewrite IHlc_tm_at2;
    try rewrite IHlc_tm_at3; try rewrite (ty_open_closed K _ U); try reflexivity.
  all: assumption.
Qed.

Lemma lc_tm_type_closed : forall K k t,
    lc_tm_at 0 k t -> lc_tm_at K k t.
Proof.
  intros K k t H; induction K; auto.
  apply lc_tm_type_weaken; assumption.
Qed.

Lemma lc_tm_closed_all : forall K k t,
    locally_closed_tm t -> lc_tm_at K k t.
Proof.
  intros K k t H; unfold locally_closed_tm in H.
  apply lc_tm_closed; apply lc_tm_type_closed; exact H.
Qed.

Lemma inst_lc : forall rho K k t,
    (forall x, locally_closed_tm (rho x)) ->
    lc_tm_at K k t -> lc_tm_at K k (inst rho t).
Proof.
  intros rho K k t Hr; revert K k; induction t; intros K k H; simpl in *.
  - inversion H; constructor; assumption.
  - apply lc_tm_closed_all; apply Hr.
  - inversion H; subst; constructor; eauto using lc_ty_weaken.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto using lc_tm_type_weaken.
  - inversion H; subst; constructor; eauto using lc_ty_weaken.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma inst_open : forall rho k u t,
    (forall x, locally_closed_tm (rho x)) -> locally_closed_tm u ->
    inst rho (open_tm_rec k u t) = open_tm_rec k (inst rho u) (inst rho t).
Proof.
  intros rho k u t Hr; revert k u; induction t; intros k u Hu; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite (open_tm_closed 0 k (rho a) (inst rho u)).
    + reflexivity.
    + apply lc_tm_closed_all; apply Hr.
  - f_equal; apply IHt; exact Hu.
  - f_equal; [apply IHt1; exact Hu|apply IHt2; exact Hu].
  - f_equal; apply IHt; exact Hu.
  - f_equal; apply IHt; exact Hu.
  - reflexivity.
  - f_equal; apply IHt; exact Hu.
  - f_equal; [apply IHt1; exact Hu|apply IHt2; exact Hu|apply IHt3; exact Hu].
  - f_equal; [apply IHt1; exact Hu|apply IHt2; exact Hu].
Qed.

Lemma inst_ty_open : forall rho K U t,
    (forall x, locally_closed_tm (rho x)) ->
    inst rho (open_tm_ty_rec K U t) = open_tm_ty_rec K U (inst rho t).
Proof.
  intros rho K U t Hr; revert K U; induction t; intros K U; simpl.
  - reflexivity.
  - assert (Hra : lc_tm_at K 0 (rho a)).
    { apply lc_tm_closed_all; apply Hr. }
    rewrite (open_ty_closed K 0 (rho a) U Hra); reflexivity.
  - f_equal; apply IHt.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal; apply IHt.
  - f_equal; apply IHt.
  - reflexivity.
  - f_equal; apply IHt.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3].
  - f_equal; [apply IHt1|apply IHt2].
Qed.

Fixpoint tm_fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => tm_fvars t1
  | tm_app t1 t2 => tm_fvars t1 ++ tm_fvars t2
  | tm_tabs t1 => tm_fvars t1
  | tm_tapp t1 _ => tm_fvars t1
  | tm_zero => []
  | tm_succ t1 => tm_fvars t1
  | tm_natrec n b s => tm_fvars n ++ tm_fvars b ++ tm_fvars s
  | tm_choice t1 t2 => tm_fvars t1 ++ tm_fvars t2
  end.

Fixpoint ty_fvars (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => ty_fvars T1 ++ ty_fvars T2
  | Ty_All T1 => ty_fvars T1
  | Ty_Nat => []
  end.

Fixpoint tm_tyfvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_zero => []
  | tm_abs T t1 => ty_fvars T ++ tm_tyfvars t1
  | tm_app t1 t2 => tm_tyfvars t1 ++ tm_tyfvars t2
  | tm_tabs t1 => tm_tyfvars t1
  | tm_tapp t1 T => tm_tyfvars t1 ++ ty_fvars T
  | tm_succ t1 => tm_tyfvars t1
  | tm_natrec n b s => tm_tyfvars n ++ tm_tyfvars b ++ tm_tyfvars s
  | tm_choice t1 t2 => tm_tyfvars t1 ++ tm_tyfvars t2
  end.

Definition fresh (xs : list atom) : atom :=
  S (fold_right Nat.max 0 xs).

Lemma inst_no_fvar : forall rho x v t,
    ~ In x (tm_fvars t) -> inst (rho_upd rho x v) t = inst rho t.
Proof.
  intros rho x v t; induction t; simpl; intros H; try reflexivity.
  - destruct (Nat.eqb x a) eqn:E; [exfalso|reflexivity].
    apply Nat.eqb_eq in E; subst; apply H; simpl; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma fresh_not_in : forall xs, ~ In (fresh xs) xs.
Proof.
  assert (Hmax : forall a xs, In a xs -> a <= fold_right Nat.max 0 xs).
  { intros a xs; induction xs as [|b xs IH].
    - simpl; contradiction.
    - simpl; intros H; destruct H as [E|E].
      + subst; lia.
      + specialize (IH E); lia. }
  intros xs H; specialize (Hmax (fresh xs) xs H).
  unfold fresh in Hmax.
  lia.
Qed.

Lemma not_in_app_l : forall (x : atom) (xs ys : list atom), ~ In x (xs ++ ys) -> ~ In x xs.
Proof. intros x xs ys Hnot H; apply Hnot; apply in_or_app; auto. Qed.
Lemma not_in_app_r : forall (x : atom) (xs ys : list atom), ~ In x (xs ++ ys) -> ~ In x ys.
Proof. intros x xs ys Hnot H; apply Hnot; apply in_or_app; auto. Qed.

Lemma tm_fvars_abs : forall T t x, In x (tm_fvars t) -> In x (tm_fvars (tm_abs T t)).
Proof. simpl; auto. Qed.

Lemma ty_fvars_all : forall T x, In x (ty_fvars T) -> In x (ty_fvars (Ty_All T)).
Proof. simpl; auto. Qed.

Lemma ty_open_inv : forall K X T,
    ~ In X (ty_fvars T) ->
    lc_ty_at K (open_ty_rec K (Ty_FVar X) T) ->
    lc_ty_at (S K) T.
Proof.
  intros K X T; revert K X; induction T; intros K X Hfv Hlc; simpl in *.
  - destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + apply Nat.eqb_neq in E; inversion Hlc; constructor; lia.
  - constructor.
  - inversion Hlc; subst; constructor.
    + eapply IHT1 with (K := K) (X := X).
      * exact (not_in_app_l X _ _ Hfv).
      * assumption.
    + eapply IHT2 with (K := K) (X := X).
      * exact (not_in_app_r X _ _ Hfv).
      * assumption.
  - inversion Hlc; subst; constructor.
    apply IHT with (K := S K) (X := X).
    + exact Hfv.
    + assumption.
  - constructor.
Qed.

Lemma tm_open_inv : forall K k X t,
    ~ In X (tm_fvars t) ->
    lc_tm_at K k (open_tm_rec k (tm_fvar X) t) ->
    lc_tm_at K (S k) t.
Proof.
  intros K k X t; revert K k X; induction t;
    intros K k X Hfv Hlc; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + apply Nat.eqb_neq in E; inversion Hlc; constructor; lia.
  - constructor.
  - inversion Hlc; subst; constructor; eauto using lc_ty_weaken.
  - inversion Hlc; subst; constructor.
    + eapply IHt1 with (K := K) (k := k) (X := X).
      * exact (not_in_app_l X _ _ Hfv).
      * assumption.
    + eapply IHt2 with (K := K) (k := k) (X := X).
      * exact (not_in_app_r X _ _ Hfv).
      * assumption.
  - inversion Hlc; subst; constructor.
    apply IHt with (K := S K) (k := k) (X := X); auto.
  - inversion Hlc; subst; constructor.
    + eapply IHt with (K := K) (k := k) (X := X); eauto.
    + assumption.
  - constructor.
  - inversion Hlc; subst; constructor; eauto using not_in_app_l, not_in_app_r.
  - inversion Hlc; subst; constructor.
    + eapply IHt1 with (K := K) (k := k) (X := X).
      * exact (not_in_app_l X _ _ Hfv).
      * assumption.
    + eapply IHt2 with (K := K) (k := k) (X := X).
      * exact (not_in_app_l X (tm_fvars t2) (tm_fvars t3)
          (not_in_app_r X (tm_fvars t1) (tm_fvars t2 ++ tm_fvars t3) Hfv)).
      * assumption.
    + eapply IHt3 with (K := K) (k := k) (X := X).
      * exact (not_in_app_r X (tm_fvars t2) (tm_fvars t3)
          (not_in_app_r X (tm_fvars t1) (tm_fvars t2 ++ tm_fvars t3) Hfv)).
      * assumption.
  - inversion Hlc; subst; constructor.
    + eapply IHt1 with (K := K) (k := k) (X := X).
      * exact (not_in_app_l X _ _ Hfv).
      * assumption.
    + eapply IHt2 with (K := K) (k := k) (X := X).
      * exact (not_in_app_r X _ _ Hfv).
      * assumption.
Qed.

Lemma tm_ty_open_inv : forall K k X t,
    ~ In X (tm_tyfvars t) ->
    lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
    lc_tm_at (S K) k t.
Proof.
  intros K k X t; revert K k X; induction t;
    intros K k X Hfv Hlc; simpl in *.
  - inversion Hlc; constructor; assumption.
  - constructor.
  - inversion Hlc; subst; constructor.
    + eapply ty_open_inv.
      * exact (not_in_app_l X _ _ Hfv).
      * assumption.
    + eapply IHt with (K := K) (k := S k) (X := X).
      * exact (not_in_app_r X _ _ Hfv).
      * assumption.
  - inversion Hlc; subst; constructor.
    + eapply IHt1 with (K := K) (k := k) (X := X).
      * exact (not_in_app_l X _ _ Hfv).
      * assumption.
    + eapply IHt2 with (K := K) (k := k) (X := X).
      * exact (not_in_app_r X _ _ Hfv).
      * assumption.
  - inversion Hlc; subst; constructor.
    apply IHt with (K := S K) (k := k) (X := X); auto.
  - inversion Hlc; subst; constructor.
    + eapply IHt with (K := K) (k := k) (X := X).
      * exact (not_in_app_l X _ _ Hfv).
      * assumption.
    + eapply ty_open_inv.
      * exact (not_in_app_r X _ _ Hfv).
      * assumption.
  - constructor.
  - inversion Hlc; subst; constructor.
    apply IHt with (K := K) (k := k) (X := X); eauto.
  - inversion Hlc; subst; constructor.
    + eapply IHt1 with (K := K) (k := k) (X := X).
      * exact (not_in_app_l X _ _ Hfv).
      * assumption.
    + eapply IHt2 with (K := K) (k := k) (X := X).
      * exact (not_in_app_l X _ _
          (not_in_app_r X _ _ Hfv)).
      * assumption.
    + eapply IHt3 with (K := K) (k := k) (X := X).
      * exact (not_in_app_r X _ _
          (not_in_app_r X _ _ Hfv)).
      * assumption.
  - inversion Hlc; subst; constructor.
    + eapply IHt1 with (K := K) (k := k) (X := X).
      * exact (not_in_app_l X _ _ Hfv).
      * assumption.
    + eapply IHt2 with (K := K) (k := k) (X := X).
      * exact (not_in_app_r X _ _ Hfv).
      * assumption.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H.
  refine (wf_ty_ind (fun _ T => locally_closed_ty T) _ _ _ _ Delta T H).
  - intros; constructor.
  - intros D T1 T2 H1 IH1 H2 IH2; constructor.
    + exact IH1.
    + exact IH2.
  - intros L D U Hforall IHforall.
    unfold locally_closed_ty; constructor.
    set (X := fresh (L ++ ty_fvars U)).
    assert (HX : ~ In X L).
    { unfold X; exact (not_in_app_l _ _ _ (fresh_not_in _)). }
    apply ty_open_inv with (X := X).
    + exact (not_in_app_r X L (ty_fvars U) (fresh_not_in _)).
    + exact (IHforall X HX).
  - constructor.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
    has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H.
  - constructor.
  - unfold locally_closed_tm.
    constructor.
    + exact (wf_ty_lc Delta T1 H).
    + set (x := fresh (L ++ tm_fvars t2)).
    assert (Hx : ~ In x L).
    { unfold x; exact (not_in_app_l _ _ _ (fresh_not_in _)). }
    specialize (H1 x Hx).
    apply tm_open_inv with (X := x).
    * exact (not_in_app_r x L (tm_fvars t2) (fresh_not_in _)).
    * exact H1.
  - constructor; assumption.
  - unfold locally_closed_tm; constructor.
    set (X := fresh (L ++ tm_tyfvars t)).
    assert (HX : ~ In X L).
    { unfold X; exact (not_in_app_l _ _ _ (fresh_not_in _)). }
    specialize (H0 X HX).
    apply tm_ty_open_inv with (X := X).
    + exact (not_in_app_r X L (tm_tyfvars t) (fresh_not_in _)).
    + exact H0.
  - unfold locally_closed_tm; constructor.
    + exact IHhas_type.
    + exact (wf_ty_lc Delta U H0).
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End SystemFNormalizationNondeterminismRecursionHardTask.
