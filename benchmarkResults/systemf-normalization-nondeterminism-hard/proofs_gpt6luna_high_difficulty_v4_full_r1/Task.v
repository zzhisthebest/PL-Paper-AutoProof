(** System F CBV strong-normalization benchmark, Hard variant.
    Features: nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Arith.Compare_dec Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationNondeterminismHardTask.

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

  | Ty_All : ty -> ty.

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

Notation "'choice' t1 'or' t2" := (tm_choice t1 t2)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm at level 200) : systemf_scope.

Fixpoint open_ty_rec (k : nat) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => if Nat.eqb k i then U else Ty_BVar i
  | Ty_FVar X => Ty_FVar X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (open_ty_rec k U T1) (open_ty_rec k U T2)
  | Ty_All T1 => Ty_All (open_ty_rec (S k) U T1)
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
  end.

Fixpoint tm_ty_subst (X : atom) (U : ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_subst X U T) (tm_ty_subst X U t1)
  | tm_app t1 t2 => tm_app (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  | tm_tabs t1 => tm_tabs (tm_ty_subst X U t1)
  | tm_tapp t1 T => tm_tapp (tm_ty_subst X U t1) (ty_subst X U T)
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
      lc_ty_at k (Ty_All T).

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
  | lc_tm_choice : forall K k t1 t2,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k (tm_choice t1 t2).

Definition locally_closed_tm (t : tm) : Prop := lc_tm_at 0 0 t.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed_tm (tm_abs T t) ->
      value (tm_abs T t)
  | v_tabs : forall t,
      locally_closed_tm (tm_tabs t) ->
      value (tm_tabs t).

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
      wf_ty Delta (Ty_All T).

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

Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => fv_ty A ++ fv_ty B
  | Ty_All A => fv_ty A
  end.

Definition candidate := tm -> Prop.
Definition tysem := (ty * candidate)%type.
Definition type_env := atom -> tysem.
Definition bound_env := nat -> tysem.

Definition admissible (P : candidate) : Prop :=
  (forall t, P t -> locally_closed_tm t /\ strongly_normalizing t) /\
  (forall t u, P t -> t --> u -> P u) /\
  (forall t, locally_closed_tm t -> ~ value t ->
     (forall u, t --> u -> P u) -> P t).

Definition sem_valid (rho : type_env) (bs : bound_env) : Prop :=
  (forall X, locally_closed_ty (fst (rho X)) /\ admissible (snd (rho X))) /\
  (forall i, locally_closed_ty (fst (bs i)) /\ admissible (snd (bs i))).

Definition extend_bound_at (bs : bound_env) (k : nat)
  (U : ty) (P : candidate) : bound_env :=
  fun i => if i <? k then bs i else if i =? k then (U, P) else bs (Nat.pred i).

Definition extend_bound (bs : bound_env) (U : ty) (P : candidate) : bound_env :=
  extend_bound_at bs 0 U P.

Lemma extend_bound_at_commute : forall bs K U P V Q i,
  extend_bound_at (extend_bound bs V Q) (S K) U P i =
  extend_bound (extend_bound_at bs K U P) V Q i.
Proof.
  intros bs K U P V Q i. unfold extend_bound, extend_bound_at.
  destruct i as [|i]; simpl.
  - reflexivity.
  - destruct (Nat.lt_trichotomy i K) as [Hlt|[Heq|Hgt]].
    + assert (E1 : (i <? K) = true) by (apply Nat.ltb_lt; lia).
      assert (E3 : (S i <? S K) = true) by (apply Nat.ltb_lt; lia).
      rewrite E3. simpl. rewrite E1. reflexivity.
    + subst.
      assert (E1 : (K <? K) = false) by (apply Nat.ltb_ge; lia).
      assert (E2 : (K =? K) = true) by (apply Nat.eqb_eq; reflexivity).
      assert (E3 : (S K <? S K) = false) by (apply Nat.ltb_ge; lia).
      rewrite E1, E2, E3. reflexivity.
    + assert (E1 : (i <? K) = false) by (apply Nat.ltb_ge; lia).
      assert (E2 : (i =? K) = false) by (apply Nat.eqb_neq; lia).
      assert (E3 : (S i <? S K) = false) by (apply Nat.ltb_ge; lia).
      assert (E4 : (i =? 0) = false) by (apply Nat.eqb_neq; lia).
      rewrite E3, E2. simpl. rewrite E1, E4. reflexivity.
Qed.

Definition sn_candidate : candidate := fun t =>
  locally_closed_tm t /\ strongly_normalizing t.
Definition default_tysem : tysem := (Ty_FVar 0, sn_candidate).

Fixpoint denote (rho : type_env) (bs : bound_env) (T : ty) : candidate :=
  match T with
  | Ty_BVar i => snd (bs i)
  | Ty_FVar X => snd (rho X)
  | Ty_Arrow A B => fun t =>
      locally_closed_tm t /\ strongly_normalizing t /\
      (forall u, denote rho bs A u -> denote rho bs B (tm_app t u))
  | Ty_All A => fun t =>
      locally_closed_tm t /\ strongly_normalizing t /\
      (forall U P, locally_closed_ty U -> admissible P ->
         forall w, tm_tapp t U --> w ->
           denote rho (extend_bound bs U P) A w)
  end.

Lemma denote_sn : forall rho bs T t,
  sem_valid rho bs -> denote rho bs T t -> strongly_normalizing t.
Proof.
  intros rho bs T t [Hr Hb] H. destruct T as [i|X|A B|A]; simpl in H.
  - destruct (Hb i) as [_ Hadm]. destruct Hadm as [HSN _].
    exact (proj2 (HSN t H)).
  - destruct (Hr X) as [_ Hadm]. destruct Hadm as [HSN _].
    exact (proj2 (HSN t H)).
  - tauto.
  - tauto.
Qed.

Definition default_type_env : type_env := fun _ => default_tysem.
Definition default_bound_env : bound_env := fun _ => default_tysem.

Definition extend_type_env (rho : type_env) (X : atom)
  (U : ty) (P : candidate) : type_env :=
  fun Y => if Nat.eqb X Y then (U, P) else rho Y.

Fixpoint subst_ty_env (rho : type_env) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => fst (rho X)
  | Ty_Arrow A B => Ty_Arrow (subst_ty_env rho A) (subst_ty_env rho B)
  | Ty_All A => Ty_All (subst_ty_env rho A)
  end.

Lemma sem_valid_extend_type : forall rho bs X U P,
  sem_valid rho bs -> locally_closed_ty U -> admissible P ->
  sem_valid (extend_type_env rho X U P) bs.
Proof.
  intros rho bs X U P [Hr Hb] HU HP. split.
  - intros Y. unfold extend_type_env. destruct (Nat.eqb X Y); auto.
  - exact Hb.
Qed.

Lemma denote_bound_congr : forall rho bs bs' T,
  (forall i, bs i = bs' i) -> forall t,
  denote rho bs T t <-> denote rho bs' T t.
Proof.
  intros rho bs bs' T. revert bs bs'.
  induction T; intros bs bs' Hbs t; simpl.
  - rewrite (Hbs n). tauto.
  - tauto.
  - split.
    + intros [Hlc [Hsn Happ]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros u Hru. apply (proj1 (IHT2 bs bs' Hbs (tm_app t u))).
      apply Happ. apply (proj2 (IHT1 bs bs' Hbs u)). exact Hru.
    + intros [Hlc [Hsn Happ]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros u Hru. apply (proj2 (IHT2 bs bs' Hbs (tm_app t u))).
      apply Happ. apply (proj1 (IHT1 bs bs' Hbs u)). exact Hru.
  - split.
    + intros [Hlc [Hsn Hall]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros U P HU HP w Hstep.
      assert (Hext : forall i, extend_bound bs U P i = extend_bound bs' U P i).
      { intros [|i]; unfold extend_bound, extend_bound_at; simpl; auto. }
      apply (proj1 (IHT (extend_bound bs U P) (extend_bound bs' U P) Hext w)).
      apply Hall with (U := U) (P := P); assumption.
    + intros [Hlc [Hsn Hall]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros U P HU HP w Hstep.
      assert (Hext : forall i, extend_bound bs U P i = extend_bound bs' U P i).
      { intros [|i]; unfold extend_bound, extend_bound_at; simpl; auto. }
      apply (proj2 (IHT (extend_bound bs U P) (extend_bound bs' U P) Hext w)).
      apply Hall with (U := U) (P := P); assumption.
Qed.

Lemma denote_bound_congr_lc : forall rho bs bs' K T,
  lc_ty_at K T -> (forall i, i < K -> bs i = bs' i) -> forall t,
  denote rho bs T t <-> denote rho bs' T t.
Proof.
  intros rho bs bs' K T Hlc. revert rho bs bs' K Hlc.
  induction T; intros rho bs bs' K Hlc Hbs t; simpl.
  - inversion Hlc as [k' i Hbound | | |]; subst.
    rewrite (Hbs n Hbound). tauto.
  - tauto.
  - inversion Hlc as [| |k' A B Hleft Hright|]; subst. split.
    + intros [Hlc' [Hsn Happ]]. split; [exact Hlc'|]. split; [exact Hsn|].
      intros u Hru. apply (proj1 (IHT2 rho bs bs' K Hright Hbs (tm_app t u))).
      apply Happ. apply (proj2 (IHT1 rho bs bs' K Hleft Hbs u)). exact Hru.
    + intros [Hlc' [Hsn Happ]]. split; [exact Hlc'|]. split; [exact Hsn|].
      intros u Hru. apply (proj2 (IHT2 rho bs bs' K Hright Hbs (tm_app t u))).
      apply Happ. apply (proj1 (IHT1 rho bs bs' K Hleft Hbs u)). exact Hru.
  - inversion Hlc as [| | |k' A HA]; subst. split.
    + intros [Hlc' [Hsn Hall]]. split; [exact Hlc'|]. split; [exact Hsn|].
      intros U P HU HP w Hstep.
      assert (Hext : forall i, i < S K ->
        extend_bound bs U P i = extend_bound bs' U P i).
      { intros [|i] Hi; unfold extend_bound, extend_bound_at; simpl; auto.
        rewrite (Hbs i); auto; lia. }
      apply (proj1 (IHT rho (extend_bound bs U P) (extend_bound bs' U P)
        (S K) HA Hext w)).
      apply Hall with (U := U) (P := P); assumption.
    + intros [Hlc' [Hsn Hall]]. split; [exact Hlc'|]. split; [exact Hsn|].
      intros U P HU HP w Hstep.
      assert (Hext : forall i, i < S K ->
        extend_bound bs U P i = extend_bound bs' U P i).
      { intros [|i] Hi; unfold extend_bound, extend_bound_at; simpl; auto.
        rewrite (Hbs i); auto; lia. }
      apply (proj2 (IHT rho (extend_bound bs U P) (extend_bound bs' U P)
        (S K) HA Hext w)).
      apply Hall with (U := U) (P := P); assumption.
Qed.

Definition bound_equiv (bs bs' : bound_env) : Prop :=
  forall i t, snd (bs i) t <-> snd (bs' i) t.

Lemma denote_bound_equiv : forall rho bs bs' T,
  bound_equiv bs bs' -> forall t,
  denote rho bs T t <-> denote rho bs' T t.
Proof.
  intros rho bs bs' T. revert bs bs'. induction T; intros bs bs' Hbs t; simpl.
  - apply Hbs.
  - tauto.
  - split.
    + intros [Hl [Hs Ha]]. split; [exact Hl|]. split; [exact Hs|].
      intros u Hu. apply (proj1 (IHT2 bs bs' Hbs (tm_app t u))).
      apply Ha. apply (proj2 (IHT1 bs bs' Hbs u)); exact Hu.
    + intros [Hl [Hs Ha]]. split; [exact Hl|]. split; [exact Hs|].
      intros u Hu. apply (proj2 (IHT2 bs bs' Hbs (tm_app t u))).
      apply Ha. apply (proj1 (IHT1 bs bs' Hbs u)); exact Hu.
  - split.
    + intros [Hl [Hs Ha]]. split; [exact Hl|]. split; [exact Hs|].
      intros U P HU HP w Hstep.
      assert (Hext : bound_equiv (extend_bound bs U P) (extend_bound bs' U P)).
      { intros [|i] z; unfold extend_bound, extend_bound_at; simpl.
        - tauto.
        - apply Hbs. }
      apply (proj1 (IHT (extend_bound bs U P) (extend_bound bs' U P) Hext w)).
      apply Ha with (U := U) (P := P); assumption.
    + intros [Hl [Hs Ha]]. split; [exact Hl|]. split; [exact Hs|].
      intros U P HU HP w Hstep.
      assert (Hext : bound_equiv (extend_bound bs U P) (extend_bound bs' U P)).
      { intros [|i] z; unfold extend_bound, extend_bound_at; simpl.
        - tauto.
        - apply Hbs. }
      apply (proj2 (IHT (extend_bound bs U P) (extend_bound bs' U P) Hext w)).
      apply Ha with (U := U) (P := P); assumption.
Qed.

Lemma extend_bound_at_equiv : forall bs bs' K U P Q,
  bound_equiv bs bs' -> (forall t, P t <-> Q t) ->
  bound_equiv (extend_bound_at bs K U P) (extend_bound_at bs' K U Q).
Proof.
  intros bs bs' K U P Q Hbs HP i t. unfold extend_bound_at.
  destruct (lt_dec i K) as [Hlt|Hge].
  - assert (E : (i <? K) = true) by (apply Nat.ltb_lt; lia).
    rewrite E. apply Hbs.
  - assert (E : (i <? K) = false) by (apply Nat.ltb_ge; lia).
    rewrite E. destruct (Nat.eq_dec i K) as [->|Hneq].
    + repeat rewrite Nat.eqb_refl. simpl. apply HP.
    + assert (E' : (i =? K) = false) by (apply Nat.eqb_neq; exact Hneq).
      rewrite E'. apply Hbs.
Qed.

Lemma extend_bound_equiv : forall bs bs' U P Q,
  bound_equiv bs bs' -> (forall t, P t <-> Q t) ->
  bound_equiv (extend_bound bs U P) (extend_bound bs' U Q).
Proof. intros; apply extend_bound_at_equiv; assumption. Qed.

Lemma lc_ty_at_mono : forall n m T,
  n <= m -> lc_ty_at n T -> lc_ty_at m T.
Proof.
  intros n m T Hle H. revert m Hle.
  induction H; intros m Hle.
  - constructor; lia.
  - constructor.
  - constructor; eauto.
  - constructor. apply IHlc_ty_at. lia.
Qed.

Lemma denote_type_env_fresh : forall rho rho' bs X T,
  (forall Y, Y <> X -> rho Y = rho' Y) ->
  ~ In X (fv_ty T) -> forall t,
  denote rho bs T t <-> denote rho' bs T t.
Proof.
  intros rho rho' bs X T. revert rho rho' bs X.
  induction T; intros rho rho' bs X Heq Hfresh t; simpl in *.
  - tauto.
  - destruct (Nat.eq_dec a X) as [E|E].
    + subst. exfalso. apply Hfresh. simpl; auto.
    + rewrite (Heq a E). tauto.
  - assert (Hf1 : ~ In X (fv_ty T1)).
    { intro H. apply Hfresh. apply in_or_app; left; exact H. }
    assert (Hf2 : ~ In X (fv_ty T2)).
    { intro H. apply Hfresh. apply in_or_app; right; exact H. }
    split.
    + intros [Hlc [Hsn Happ]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros u Hu. apply (proj1 (IHT2 rho rho' bs X Heq Hf2 (tm_app t u))).
      apply Happ. apply (proj2 (IHT1 rho rho' bs X Heq Hf1 u)); exact Hu.
    + intros [Hlc [Hsn Happ]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros u Hu. apply (proj2 (IHT2 rho rho' bs X Heq Hf2 (tm_app t u))).
      apply Happ. apply (proj1 (IHT1 rho rho' bs X Heq Hf1 u)); exact Hu.
  - split.
    + intros [Hlc [Hsn Hall]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros U P HU HP w Hstep.
      apply (proj1 (IHT rho rho' (extend_bound bs U P) X Heq Hfresh w)).
      apply Hall with (U := U) (P := P); assumption.
    + intros [Hlc [Hsn Hall]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros U P HU HP w Hstep.
      apply (proj2 (IHT rho rho' (extend_bound bs U P) X Heq Hfresh w)).
      apply Hall with (U := U) (P := P); assumption.
Qed.

Lemma denote_open_ty : forall rho bs X U P K T,
  sem_valid rho bs -> locally_closed_ty U -> admissible P ->
  lc_ty_at (S K) T -> ~ In X (fv_ty T) -> forall t,
  denote (extend_type_env rho X U P) bs
    (open_ty_rec K (Ty_FVar X) T) t <->
  denote rho (extend_bound_at bs K U P) T t.
Proof.
  intros rho bs X U P K T Hvalid HU HP. revert rho bs X U P K Hvalid HU HP.
  induction T; intros rho bs X U P K Hvalid HU HP Hlc Hfresh t; simpl in *.
  - inversion Hlc as [k' i Hbound | | |]; subst.
    destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E. subst.
      unfold extend_bound_at, extend_type_env. simpl.
      rewrite Nat.ltb_irrefl. repeat rewrite Nat.eqb_refl. simpl. tauto.
    + apply Nat.eqb_neq in E.
      unfold extend_bound_at.
      assert (Hlt : (n <? K) = true) by (apply Nat.ltb_lt; lia).
      rewrite Hlt. simpl. tauto.
  - simpl in Hfresh. assert (Hneq : a <> X) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold extend_type_env.
    assert (E : (X =? a) = false) by (apply Nat.eqb_neq; congruence).
    rewrite E. tauto.
  - inversion Hlc as [| |k' A B Hleft Hright|]; subst.
    assert (Hf1 : ~ In X (fv_ty T1)).
    { intro H. apply Hfresh. apply in_or_app; left; exact H. }
    assert (Hf2 : ~ In X (fv_ty T2)).
    { intro H. apply Hfresh. apply in_or_app; right; exact H. }
    split.
    + intros [Hlc' [Hsn Happ]]. split; [exact Hlc'|]. split; [exact Hsn|].
      intros u Hu. apply (proj1 (IHT2 rho bs X U P K Hvalid HU HP Hright Hf2 (tm_app t u))).
      apply Happ. apply (proj2 (IHT1 rho bs X U P K Hvalid HU HP Hleft Hf1 u)); exact Hu.
    + intros [Hlc' [Hsn Happ]]. split; [exact Hlc'|]. split; [exact Hsn|].
      intros u Hu. apply (proj2 (IHT2 rho bs X U P K Hvalid HU HP Hright Hf2 (tm_app t u))).
      apply Happ. apply (proj1 (IHT1 rho bs X U P K Hvalid HU HP Hleft Hf1 u)); exact Hu.
  - inversion Hlc as [| | |k' A HA]; subst.
    split.
    + intros [Hlc' [Hsn Hall]]. split; [exact Hlc'|]. split; [exact Hsn|].
      intros V Q HV HQ w Hstep.
      assert (Hcomm : forall i,
        extend_bound_at (extend_bound bs V Q) (S K) U P i =
        extend_bound (extend_bound_at bs K U P) V Q i).
      { apply extend_bound_at_commute. }
      assert (HvalidV : sem_valid rho (extend_bound bs V Q)).
      { destruct Hvalid as [Hr Hb]. split; [exact Hr|]. intros [|i].
        - unfold extend_bound, extend_bound_at. simpl. split; assumption.
        - unfold extend_bound, extend_bound_at. simpl. apply Hb. }
      apply (proj1 (denote_bound_congr rho
        (extend_bound_at (extend_bound bs V Q) (S K) U P)
        (extend_bound (extend_bound_at bs K U P) V Q) T Hcomm w)).
      apply (proj1 (IHT rho (extend_bound bs V Q) X U P (S K)
        HvalidV HU HP HA Hfresh w)).
      apply Hall with (U := V) (P := Q); assumption.
    + intros [Hlc' [Hsn Hall]]. split; [exact Hlc'|]. split; [exact Hsn|].
      intros V Q HV HQ w Hstep.
      assert (Hcomm : forall i,
        extend_bound_at (extend_bound bs V Q) (S K) U P i =
        extend_bound (extend_bound_at bs K U P) V Q i).
      { apply extend_bound_at_commute. }
      assert (HvalidV : sem_valid rho (extend_bound bs V Q)).
      { destruct Hvalid as [Hr Hb]. split; [exact Hr|]. intros [|i].
        - unfold extend_bound, extend_bound_at. simpl. split; assumption.
        - unfold extend_bound, extend_bound_at. simpl. apply Hb. }
      apply (proj2 (IHT rho (extend_bound bs V Q) X U P (S K)
        HvalidV HU HP HA Hfresh w)).
      apply (proj2 (denote_bound_congr rho
        (extend_bound_at (extend_bound bs V Q) (S K) U P)
        (extend_bound (extend_bound_at bs K U P) V Q) T Hcomm w)).
      apply Hall with (U := V) (P := Q); assumption.
Qed.

Lemma denote_open_sem : forall rho bs K U T,
  sem_valid rho bs -> lc_ty_at K U -> lc_ty_at 0 U ->
  lc_ty_at (S K) T -> forall t,
  denote rho bs (open_ty_rec K U T) t <->
  denote rho (extend_bound_at bs K (subst_ty_env rho U)
    (denote rho bs U)) T t.
Proof.
  intros rho bs K U T Hvalid HU Hclosed. revert rho bs K U HU Hclosed Hvalid.
  induction T; intros rho bs K U HU Hclosed Hvalid Hlc t; simpl in *.
  - inversion Hlc as [k' i Hbound | | |]; subst.
    destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E. subst. unfold extend_bound_at.
      rewrite Nat.ltb_irrefl. repeat rewrite Nat.eqb_refl. simpl. tauto.
    + apply Nat.eqb_neq in E. assert (Hlt : (n <? K) = true) by (apply Nat.ltb_lt; lia).
      unfold extend_bound_at. rewrite Hlt. simpl. tauto.
  - tauto.
  - inversion Hlc as [| |k' A B Hleft Hright|]; subst.
    split.
    + intros [Hlc' [Hsn Happ]]. split; [exact Hlc'|]. split; [exact Hsn|].
      intros u Hu. apply (proj1 (IHT2 rho bs K U HU Hclosed Hvalid Hright (tm_app t u))).
      apply Happ. apply (proj2 (IHT1 rho bs K U HU Hclosed Hvalid Hleft u)); exact Hu.
    + intros [Hlc' [Hsn Happ]]. split; [exact Hlc'|]. split; [exact Hsn|].
      intros u Hu. apply (proj2 (IHT2 rho bs K U HU Hclosed Hvalid Hright (tm_app t u))).
      apply Happ. apply (proj1 (IHT1 rho bs K U HU Hclosed Hvalid Hleft u)); exact Hu.
  - inversion Hlc as [| | |k' A HA]; subst. split.
    + intros [Hlc' [Hsn Hall]]. split; [exact Hlc'|]. split; [exact Hsn|].
      intros V Q HV HQ w Hstep.
      assert (HvalidV : sem_valid rho (extend_bound bs V Q)).
      { destruct Hvalid as [Hr Hb]. split; [exact Hr|]. intros [|i].
        - unfold extend_bound, extend_bound_at. simpl. split; assumption.
        - unfold extend_bound, extend_bound_at. simpl. apply Hb. }
      assert (HPeq : forall z, denote rho (extend_bound bs V Q) U z <-> denote rho bs U z).
      { eapply denote_bound_congr_lc.
        - exact Hclosed.
        - intros i Hi. lia. }
      assert (Hcomm : bound_equiv
        (extend_bound_at (extend_bound bs V Q) (S K)
          (subst_ty_env rho U) (denote rho (extend_bound bs V Q) U))
        (extend_bound (extend_bound_at bs K (subst_ty_env rho U)
          (denote rho bs U)) V Q)).
      { assert (Hin : bound_equiv
          (extend_bound_at bs K (subst_ty_env rho U) (denote rho (extend_bound bs V Q) U))
          (extend_bound_at bs K (subst_ty_env rho U) (denote rho bs U))).
        { apply extend_bound_at_equiv; [intros i z; tauto|exact HPeq]. }
        assert (Hout : bound_equiv
          (extend_bound (extend_bound_at bs K (subst_ty_env rho U) (denote rho (extend_bound bs V Q) U)) V Q)
          (extend_bound (extend_bound_at bs K (subst_ty_env rho U) (denote rho bs U)) V Q)).
        { apply extend_bound_equiv; [exact Hin|intros z; tauto]. }
        intros i z. rewrite extend_bound_at_commute. apply Hout. }
      apply (proj1 (denote_bound_equiv rho
        (extend_bound_at (extend_bound bs V Q) (S K)
          (subst_ty_env rho U) (denote rho (extend_bound bs V Q) U))
        (extend_bound (extend_bound_at bs K (subst_ty_env rho U)
          (denote rho bs U)) V Q) T Hcomm w)).
      apply (proj1 (IHT rho (extend_bound bs V Q) (S K) U
        (lc_ty_at_mono K (S K) U (Nat.le_succ_diag_r K) HU) Hclosed
        HvalidV HA w)).
      apply Hall with (U := V) (P := Q); assumption.
    + intros [Hlc' [Hsn Hall]]. split; [exact Hlc'|]. split; [exact Hsn|].
      intros V Q HV HQ w Hstep.
      assert (HvalidV : sem_valid rho (extend_bound bs V Q)).
      { destruct Hvalid as [Hr Hb]. split; [exact Hr|]. intros [|i].
        - unfold extend_bound, extend_bound_at. simpl. split; assumption.
        - unfold extend_bound, extend_bound_at. simpl. apply Hb. }
      assert (HPeq : forall z, denote rho (extend_bound bs V Q) U z <-> denote rho bs U z).
      { eapply denote_bound_congr_lc.
        - exact Hclosed.
        - intros i Hi. lia. }
      assert (Hcomm : bound_equiv
        (extend_bound_at (extend_bound bs V Q) (S K)
          (subst_ty_env rho U) (denote rho (extend_bound bs V Q) U))
        (extend_bound (extend_bound_at bs K (subst_ty_env rho U)
          (denote rho bs U)) V Q)).
      { assert (Hin : bound_equiv
          (extend_bound_at bs K (subst_ty_env rho U) (denote rho (extend_bound bs V Q) U))
          (extend_bound_at bs K (subst_ty_env rho U) (denote rho bs U))).
        { apply extend_bound_at_equiv; [intros i z; tauto|exact HPeq]. }
        assert (Hout : bound_equiv
          (extend_bound (extend_bound_at bs K (subst_ty_env rho U) (denote rho (extend_bound bs V Q) U)) V Q)
          (extend_bound (extend_bound_at bs K (subst_ty_env rho U) (denote rho bs U)) V Q)).
        { apply extend_bound_equiv; [exact Hin|intros z; tauto]. }
        intros i z. rewrite extend_bound_at_commute. apply Hout. }
      apply (proj2 (IHT rho (extend_bound bs V Q) (S K) U
        (lc_ty_at_mono K (S K) U (Nat.le_succ_diag_r K) HU) Hclosed
        HvalidV HA w)).
      apply (proj2 (denote_bound_equiv rho
        (extend_bound_at (extend_bound bs V Q) (S K)
          (subst_ty_env rho U) (denote rho (extend_bound bs V Q) U))
        (extend_bound (extend_bound_at bs K (subst_ty_env rho U)
          (denote rho bs U)) V Q) T Hcomm w)).
      apply Hall with (U := V) (P := Q); assumption.
Qed.

Fixpoint subst_tm_ty_env (rho : type_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T b => tm_abs (subst_ty_env rho T) (subst_tm_ty_env rho b)
  | tm_app a b => tm_app (subst_tm_ty_env rho a) (subst_tm_ty_env rho b)
  | tm_tabs b => tm_tabs (subst_tm_ty_env rho b)
  | tm_tapp a T => tm_tapp (subst_tm_ty_env rho a) (subst_ty_env rho T)
  | tm_choice a b => tm_choice (subst_tm_ty_env rho a) (subst_tm_ty_env rho b)
  end.

Definition term_env := atom -> tm.
Definition extend_term_env (sigma : term_env) (x : atom) (u : tm) : term_env :=
  fun y => if Nat.eqb x y then u else sigma y.

Fixpoint subst_tm_env (sigma : term_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T b => tm_abs T (subst_tm_env sigma b)
  | tm_app a b => tm_app (subst_tm_env sigma a) (subst_tm_env sigma b)
  | tm_tabs b => tm_tabs (subst_tm_env sigma b)
  | tm_tapp a T => tm_tapp (subst_tm_env sigma a) T
  | tm_choice a b => tm_choice (subst_tm_env sigma a) (subst_tm_env sigma b)
  end.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ b => fv_tm b
  | tm_app a b | tm_choice a b => fv_tm a ++ fv_tm b
  | tm_tabs b => fv_tm b
  | tm_tapp a _ => fv_tm a
  end.

Fixpoint fv_tm_types (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs T b => fv_ty T ++ fv_tm_types b
  | tm_app a b | tm_choice a b => fv_tm_types a ++ fv_tm_types b
  | tm_tabs b => fv_tm_types b
  | tm_tapp a T => fv_tm_types a ++ fv_ty T
  end.

Fixpoint fv_context_types (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => fv_ty T ++ fv_context_types Gamma'
  end.

Lemma fv_tm_ty_env : forall rho t,
  fv_tm (subst_tm_ty_env rho t) = fv_tm t.
Proof.
  intros rho t. induction t; simpl; try reflexivity;
    try rewrite IHt; try rewrite IHt1; try rewrite IHt2; try reflexivity.
Qed.


Lemma lc_tm_open_id : forall K k j t u,
  k <= j -> lc_tm_at K k t -> open_tm_rec j u t = t.
Proof.
  intros K k j t u Hle Hlc. revert K k j u Hle Hlc.
  induction t; intros K k j u Hle Hlc; simpl.
  - inversion Hlc; subst.
    assert (E : (j =? n) = false) by (apply Nat.eqb_neq; lia).
    now rewrite E.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    eapply IHt with (K := K) (k := S k) (j := S j); eauto; lia.
  - inversion Hlc; subst. f_equal.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  - inversion Hlc; subst. f_equal.
    eapply IHt with (K := S K) (k := k) (j := j); eauto; lia.
  - inversion Hlc; subst. f_equal. eapply IHt; eauto.
  - inversion Hlc; subst. f_equal.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
Qed.

Lemma subst_tm_ty_open_tm_rec : forall rho t k u,
  subst_tm_ty_env rho (open_tm_rec k u t) =
  open_tm_rec k (subst_tm_ty_env rho u) (subst_tm_ty_env rho t).
Proof.
  induction t; intros k u; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - f_equal. apply IHt.
  - rewrite IHt1, IHt2. reflexivity.
  - f_equal. apply IHt.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma subst_tm_env_open : forall sigma x u t k,
  ~ In x (fv_tm t) ->
  (forall y, locally_closed_tm (sigma y)) -> locally_closed_tm u ->
  subst_tm_env (extend_term_env sigma x u)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k u (subst_tm_env sigma t).
Proof.
  intros sigma x u t k Hfresh Hsigma Hu.
  revert sigma x u k Hfresh Hsigma Hu.
  induction t; intros sigma x u k Hfresh Hsigma Hu; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold extend_term_env. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - simpl in Hfresh. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso. apply Hfresh. simpl; auto.
    + unfold extend_term_env. rewrite E. symmetry.
      apply lc_tm_open_id with (K := 0) (k := 0).
      * lia.
      * apply Hsigma.
  - rewrite IHt with (x := x) (u := u) (k := S k); auto.
  - assert (Hf1 : ~ In x (fv_tm t1)).
    { intro Hin. apply Hfresh. apply in_or_app. left; exact Hin. }
    assert (Hf2 : ~ In x (fv_tm t2)).
    { intro Hin. apply Hfresh. apply in_or_app. right; exact Hin. }
    rewrite (IHt1 sigma x u k Hf1 Hsigma Hu),
      (IHt2 sigma x u k Hf2 Hsigma Hu). reflexivity.
  - rewrite IHt with (x := x) (u := u) (k := k); auto.
  - rewrite IHt with (x := x) (u := u) (k := k); auto.
  - assert (Hf1 : ~ In x (fv_tm t1)).
    { intro Hin. apply Hfresh. apply in_or_app. left; exact Hin. }
    assert (Hf2 : ~ In x (fv_tm t2)).
    { intro Hin. apply Hfresh. apply in_or_app. right; exact Hin. }
    rewrite (IHt1 sigma x u k Hf1 Hsigma Hu),
      (IHt2 sigma x u k Hf2 Hsigma Hu). reflexivity.
Qed.

Definition eval_tm (rho : type_env) (sigma : term_env) (t : tm) : tm :=
  subst_tm_env sigma (subst_tm_ty_env rho t).

Definition term_env_rel (rho : type_env) (Gamma : context)
  (sigma : term_env) : Prop :=
  (forall x, locally_closed_tm (sigma x)) /\
  (forall x T, lookup_context x Gamma = Some T ->
     denote rho default_bound_env T (sigma x)).

Lemma lookup_update_same : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof. intros; simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma lookup_update_other : forall Gamma x y T,
  x <> y -> lookup_context y (update Gamma x T) = lookup_context y Gamma.
Proof.
  intros Gamma x y T Hxy. simpl.
  assert (E : (y =? x) = false) by (apply Nat.eqb_neq; congruence).
  now rewrite E.
Qed.

Lemma term_env_rel_extend : forall rho Gamma sigma x T u,
  term_env_rel rho Gamma sigma ->
  denote rho default_bound_env T u -> locally_closed_tm u ->
  term_env_rel rho (update Gamma x T) (extend_term_env sigma x u).
Proof.
  intros rho Gamma sigma x T u [Hlc Hrel] Hu Hlu. split.
  - intros y. unfold extend_term_env. destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact Hlu.
    + apply Hlc.
  - intros y V Hlookup. unfold extend_term_env.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst. rewrite lookup_update_same in Hlookup.
      inversion Hlookup; subst. exact Hu.
    + apply Nat.eqb_neq in E. rewrite lookup_update_other in Hlookup by congruence.
      eapply Hrel; eauto.
Qed.
Lemma SN_step : forall t u, strongly_normalizing t -> t --> u ->
  strongly_normalizing u.
Proof. intros t u H; inversion H; subst; eauto. Qed.

Lemma lc_tm_at_mono : forall K1 K2 k1 k2 t,
  K1 <= K2 -> k1 <= k2 -> lc_tm_at K1 k1 t -> lc_tm_at K2 k2 t.
Proof.
  intros K1 K2 k1 k2 t HK Hk H. revert K2 k2 HK Hk.
  induction H; intros K2 k2 HK Hk.
  - constructor; lia.
  - constructor.
  - constructor.
    + eapply lc_ty_at_mono; eauto.
    + eapply IHlc_tm_at; eauto; lia.
  - constructor; [eapply IHlc_tm_at1|eapply IHlc_tm_at2]; eauto.
  - constructor. eapply IHlc_tm_at; eauto; lia.
  - constructor.
    + eapply IHlc_tm_at; eauto.
    + eapply lc_ty_at_mono; eauto.
  - constructor; [eapply IHlc_tm_at1|eapply IHlc_tm_at2]; eauto.
Qed.

Lemma lc_tm_open_rec : forall K k t u,
  lc_tm_at K (S k) t -> lc_tm_at K k u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k t u Ht Hu. revert K k u Ht Hu.
  induction t; intros K k u Ht Hu; simpl.
  - inversion Ht; subst. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. exact Hu.
    + constructor. apply Nat.eqb_neq in E. lia.
  - inversion Ht; subst. constructor.
  - inversion Ht; subst. constructor.
    + assumption.
    + eapply IHt with (K := K) (k := S k); [exact H4|].
      apply (lc_tm_at_mono K K k (S k) u); [lia|lia|exact Hu].
  - inversion Ht; subst. constructor.
    + eapply IHt1; eassumption.
    + eapply IHt2; eassumption.
  - inversion Ht; subst. constructor.
    eapply IHt with (K := S K) (k := k); [eassumption|].
    apply (lc_tm_at_mono K (S K) k k u); [lia|lia|exact Hu].
  - inversion Ht; subst. constructor.
    + eapply IHt; eassumption.
    + assumption.
  - inversion Ht; subst. constructor.
    + eapply IHt1; eassumption.
    + eapply IHt2; eassumption.
Qed.

Lemma lc_tm_open_inv : forall K k t u,
  lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (S k) t.
Proof.
  intros K k t u Hlc. revert K k u Hlc.
  induction t; intros K k u Hlc; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + inversion Hlc; subst. constructor.
      apply Nat.eqb_neq in E. lia.
  - inversion Hlc; subst. constructor.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion Hlc; subst. constructor. eapply IHt; eassumption.
  - inversion Hlc; subst. constructor.
    + eapply IHt; eassumption.
    + assumption.
  - inversion Hlc; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
Qed.

Lemma lc_ty_open_inv : forall K T U,
  lc_ty_at K (open_ty_rec K U T) -> lc_ty_at (S K) T.
Proof.
  intros K T U Hlc. revert K U Hlc.
  induction T; intros K U Hlc; simpl in *.
  - destruct (Nat.eqb K n) eqn:E.
    + constructor. apply Nat.eqb_eq in E. lia.
    + inversion Hlc; subst. constructor.
      apply Nat.eqb_neq in E. lia.
  - inversion Hlc; subst. constructor.
  - inversion Hlc; subst. constructor; [eapply IHT1|eapply IHT2]; eassumption.
  - inversion Hlc; subst. constructor.
    eapply IHT with (K := S K) (U := U). exact H1.
Qed.

Fixpoint max_atom_list (xs : list atom) : atom :=
  match xs with [] => 0 | x :: xs' => Nat.max x (max_atom_list xs') end.

Lemma in_max_atom_list : forall x xs, In x xs -> x <= max_atom_list xs.
Proof.
  intros x xs H. induction xs as [|y ys IH]; simpl in *.
  - contradiction.
  - destruct H as [->|H].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall xs : list atom, exists x, ~ In x xs.
Proof.
  intros xs. exists (S (max_atom_list xs)).
  intro H. pose proof (in_max_atom_list _ _ H). lia.
Qed.

Lemma lc_tm_type_open_inv : forall K k t U,
  lc_tm_at K k (open_tm_ty_rec K U t) -> lc_tm_at (S K) k t.
Proof.
  intros K k t U Hlc. revert K k U Hlc.
  induction t; intros K k U Hlc; simpl in *.
  - inversion Hlc; subst. constructor; assumption.
  - inversion Hlc; subst. constructor.
  - inversion Hlc; subst. constructor.
    + eapply lc_ty_open_inv. exact H3.
    + eapply IHt. exact H4.
  - inversion Hlc; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion Hlc; subst. constructor.
    eapply IHt with (K := S K) (k := k) (U := U). exact H2.
  - inversion Hlc; subst. constructor.
    + eapply IHt; eassumption.
    + eapply lc_ty_open_inv; eassumption.
  - inversion Hlc; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H. induction H as
    [Delta X Hin|Delta A B HA IHA HB IHB|L Delta T Hbody IHbody].
  - constructor.
  - constructor; assumption.
  - unfold locally_closed_ty. destruct (fresh_atom L) as [X HX].
    constructor. specialize (IHbody X HX). eapply lc_ty_open_inv; eauto.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H. induction H as
    [Delta Gamma x T Hlookup Hwf
    |L Delta Gamma T1 b T2 Hwf Hbody IHbody
    |Delta Gamma t1 t2 A B IH1 IH2
    |L Delta Gamma b T Hbody IHbody
    |Delta Gamma t U V IH Hwf
    |Delta Gamma t1 t2 T IH1 IH2].
  - constructor.
  - unfold locally_closed_tm. constructor.
    + eapply wf_ty_lc; eassumption.
    + destruct (fresh_atom L) as [x Hx].
      eapply lc_tm_open_inv. apply (IHbody x Hx).
  - unfold locally_closed_tm. constructor; assumption.
  - unfold locally_closed_tm. constructor.
    destruct (fresh_atom L) as [X HX].
    eapply lc_tm_type_open_inv. apply (IHbody X HX).
  - unfold locally_closed_tm. constructor; [assumption|eapply wf_ty_lc; eassumption].
  - unfold locally_closed_tm. constructor; assumption.
Qed.


Lemma lc_ty_open_rec : forall K j T U,
  lc_ty_at K T -> lc_ty_at K U -> lc_ty_at K (open_ty_rec j U T).
Proof.
  intros K j T U H. revert j U.
  induction H; intros j U HU; simpl.
  - destruct (Nat.eqb j i) eqn:E.
    + exact HU.
    + constructor. assumption.
  - constructor.
  - constructor; [eapply IHlc_ty_at1|eapply IHlc_ty_at2]; eassumption.
  - constructor. eapply IHlc_ty_at.
    + eapply lc_ty_at_mono with (n := k); eauto; lia.
Qed.

Lemma lc_ty_open_top : forall K T U,
  lc_ty_at (S K) T -> lc_ty_at K U -> lc_ty_at K (open_ty_rec K U T).
Proof.
  intros K T U Hlc HU. revert K U HU Hlc.
  induction T; intros K U HU Hlc; simpl; inversion Hlc; subst.
  - destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact HU.
    + constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - constructor; [eapply IHT1|eapply IHT2]; eassumption.
  - constructor. eapply IHT.
    + eapply lc_ty_at_mono with (n := K); eauto; lia.
    + assumption.
Qed.

Lemma lc_tm_type_open_rec : forall K k j t U,
  lc_tm_at K k t -> lc_ty_at K U ->
  lc_tm_at K k (open_tm_ty_rec j U t).
Proof.
  intros K k j t U Hlc HU. revert K k j U Hlc HU.
  induction t; intros K k j U Hlc HU; simpl.
  - inversion Hlc; subst. constructor; assumption.
  - inversion Hlc; subst. constructor.
  - inversion Hlc; subst. constructor.
    + eapply lc_ty_open_rec; eassumption.
    + eapply IHt; eassumption.
  - inversion Hlc; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion Hlc; subst. constructor. eapply IHt; [eassumption|].
    eapply lc_ty_at_mono with (n := K); eauto; lia.
  - inversion Hlc; subst. constructor; [eapply IHt|eapply lc_ty_open_rec]; eassumption.
  - inversion Hlc; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
Qed.

Lemma lc_tm_type_open_top : forall K k t U,
  lc_tm_at (S K) k t -> lc_ty_at K U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros K k t U Hlc HU. revert K k U Hlc HU.
  induction t; intros K k U Hlc HU; simpl.
  - inversion Hlc; subst. constructor; assumption.
  - inversion Hlc; subst. constructor.
  - inversion Hlc; subst. constructor.
    + eapply lc_ty_open_top; eassumption.
    + eapply IHt; eassumption.
  - inversion Hlc; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion Hlc; subst. constructor.
    eapply IHt with (K := S K) (k := k); [eassumption|].
    eapply lc_ty_at_mono with (n := K); eauto; lia.
  - inversion Hlc; subst. constructor.
    + eapply IHt; eassumption.
    + eapply lc_ty_open_top; eassumption.
  - inversion Hlc; subst. constructor; [eapply IHt1|eapply IHt2]; eassumption.
Qed.

Lemma lc_tm_step : forall t u,
  locally_closed_tm t -> t --> u -> locally_closed_tm u.
Proof.
  intros t u Hlc Hstep. unfold locally_closed_tm in Hlc |-.
  induction Hstep; inversion Hlc; subst.
  - inversion H5; subst. eapply lc_tm_open_rec; eassumption.
  - inversion Hlc; subst. constructor; [eapply IHHstep; eassumption|assumption].
  - inversion Hlc; subst. constructor; [assumption|eapply IHHstep; eassumption].
  - inversion H5; subst.
    eapply lc_tm_type_open_top; eassumption.
  - inversion Hlc; subst. constructor; [eapply IHHstep; eassumption|assumption].
  - inversion Hlc; subst. assumption.
  - inversion Hlc; subst. assumption.
Qed.

Lemma sn_candidate_admissible : admissible sn_candidate.
Proof.
  unfold admissible, sn_candidate. split.
  - intros t [Hlc Hsn]. auto.
  - split.
    + intros t u [Hlc Hsn] Hstep. split.
      * eapply lc_tm_step; eauto.
      * eapply SN_step; eauto.
    + intros t Hlc Hneutral Hred. split; [exact Hlc|].
      constructor. intros u Hstep.
      destruct (Hred u Hstep) as [_ Hsn]. exact Hsn.
Qed.

Lemma default_sem_valid : sem_valid default_type_env default_bound_env.
Proof.
  split.
  - intros X. split; [constructor|apply sn_candidate_admissible].
  - intros i. split; [constructor|apply sn_candidate_admissible].
Qed.

Lemma lc_ty_open_id : forall K j T U,
  K <= j -> lc_ty_at K T -> open_ty_rec j U T = T.
Proof.
  intros K j T U Hle H. revert j Hle.
  induction H; intros j Hle; simpl.
  - assert (E : (j =? i) = false) by (apply Nat.eqb_neq; lia).
    now rewrite E.
  - reflexivity.
  - now rewrite IHlc_ty_at1, IHlc_ty_at2.
  - rewrite IHlc_ty_at; [reflexivity|lia].
Qed.

Lemma subst_ty_env_open_rec : forall rho X U P K T bs,
  sem_valid rho bs -> ~ In X (fv_ty T) ->
  subst_ty_env (extend_type_env rho X U P) (open_ty_rec K (Ty_FVar X) T) =
  open_ty_rec K U (subst_ty_env rho T).
Proof.
  intros rho X U P K T. revert rho X U P K.
  induction T; intros rho X U P K bs Hvalid Hfresh; simpl in *.
  - destruct (Nat.eqb K n) eqn:E.
    + unfold extend_type_env. simpl. destruct (Nat.eqb X X) eqn:E2.
      * reflexivity.
      * apply Nat.eqb_neq in E2. contradiction.
    + reflexivity.
  - destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso. apply Hfresh. simpl; auto.
    + unfold extend_type_env. rewrite E.
      assert (Hlc : locally_closed_ty (fst (rho a))).
      { destruct Hvalid as [Hr _]. exact (proj1 (Hr a)). }
      rewrite (lc_ty_open_id 0 K (fst (rho a)) U); [reflexivity|lia|exact Hlc].
  - assert (Hfa : ~ In X (fv_ty T1)).
    { intro Hin. apply Hfresh. apply in_or_app. left; exact Hin. }
    assert (Hfb : ~ In X (fv_ty T2)).
    { intro Hin. apply Hfresh. apply in_or_app. right; exact Hin. }
    rewrite (IHT1 rho X U P K bs Hvalid Hfa),
      (IHT2 rho X U P K bs Hvalid Hfb). reflexivity.
  - rewrite (IHT rho X U P (S K) bs Hvalid Hfresh). reflexivity.
Qed.

Lemma lc_tm_type_open_id : forall K k j t U,
  K <= j -> lc_tm_at K k t -> open_tm_ty_rec j U t = t.
Proof.
  intros K k j t U Hle Hlc. revert K k j U Hle Hlc.
  induction t; intros K k j U Hle Hlc; simpl.
  - reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    + eapply lc_ty_open_id; eauto.
    + eapply IHt; eauto.
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2]; eauto.
  - inversion Hlc; subst. f_equal.
    eapply IHt with (K := S K) (k := k) (j := S j); eauto; lia.
  - inversion Hlc; subst. f_equal.
    + eapply IHt; eauto.
    + eapply lc_ty_open_id; eauto.
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2]; eauto.
Qed.

Lemma open_tm_ty_open_tm_rec : forall t i j U v,
  locally_closed_tm v ->
  open_tm_ty_rec j U (open_tm_rec i v t) =
  open_tm_rec i v (open_tm_ty_rec j U t).
Proof.
  induction t; intros i j U v Hlc; simpl.
  - destruct (Nat.eqb i n); [|reflexivity].
    f_equal. apply (lc_tm_type_open_id 0 0 j v U); [lia|exact Hlc].
  - reflexivity.
  - f_equal. apply IHt; exact Hlc.
  - rewrite IHt1, IHt2; auto.
  - rewrite (IHt i (S j) U v Hlc).
    reflexivity.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof. intros v H; inversion H; assumption. Qed.

Lemma value_no_step : forall t u, value t -> ~ (t --> u).
Proof. intros t u Hv Hs. inversion Hv; subst; inversion Hs. Qed.

Lemma sem_valid_extend : forall rho bs U P,
  sem_valid rho bs -> locally_closed_ty U -> admissible P ->
  sem_valid rho (extend_bound bs U P).
Proof.
  intros rho bs U P [Hr Hb] HU HP. split; [exact Hr|].
  intros i. destruct i as [|i].
  - unfold extend_bound, extend_bound_at. simpl. split; assumption.
  - unfold extend_bound, extend_bound_at. simpl. apply Hb.
Qed.

Lemma denote_admissible : forall rho bs T,
  sem_valid rho bs -> admissible (denote rho bs T).
Proof.
  intros rho bs T. revert rho bs.
  induction T as [i|X|A IHA B IHB|A IHA]; intros rho bs Hvalid;
    unfold admissible; simpl.
  - destruct Hvalid as [_ Hb]. exact (proj2 (Hb i)).
  - destruct Hvalid as [Hr _]. exact (proj2 (Hr X)).
  - pose proof (IHB rho bs Hvalid) as IH_B.
    unfold admissible in IH_B. simpl in IH_B.
    destruct IH_B as [_ [IHredB IHneutralB]].
    pose proof (IHA rho bs Hvalid) as IH_A.
    unfold admissible in IH_A. simpl in IH_A.
    destruct IH_A as [IHpropsA _].
    split.
    + intros t [Hlc [Hsn _]]. split; assumption.
    + split.
      * intros t t' [Hlc [Hsn Happ]] Htu.
        split; [eapply lc_tm_step; eauto|].
        split; [eapply SN_step; eauto|].
        intros u Hru.
        pose proof (Happ u Hru) as Hout.
        destruct (IHpropsA u Hru) as [Hlcu _].
        eapply IHredB; [exact Hout|].
        eapply ST_App1; eauto.
      * intros t Hlc Hneutral Hred.
        split; [exact Hlc|]. split.
        -- constructor. intros u Htu.
           destruct (Hred u Htu) as [_ [Hsu _]]. exact Hsu.
        -- intros u Hru.
           destruct (IHpropsA u Hru) as [Hlcu _].
           eapply IHneutralB.
           ++ constructor; assumption.
           ++ intro Hvalapp. inversion Hvalapp.
           ++ intros w Hwv. inversion Hwv; subst.
              ** exfalso. apply Hneutral. econstructor; eauto.
              ** destruct (Hred t1' H1) as [_ [_ Hfun]].
                 exact (Hfun u Hru).
              ** exfalso. apply Hneutral. exact H1.
  -
    split.
    + intros t [Hlc [Hsn _]]. split; assumption.
    + split.
      * intros t t' [Hlc [Hsn Hall]] Htu.
        split; [eapply lc_tm_step; eauto|].
        split; [eapply SN_step; eauto|].
        intros U P HU HP w Hstep.
        assert (Hmid : denote rho (extend_bound bs U P) A (tm_tapp t' U)).
        { apply (Hall U P HU HP (tm_tapp t' U)).
          apply ST_TApp; assumption. }
        pose proof (IHA rho (extend_bound bs U P)
          (sem_valid_extend rho bs U P Hvalid HU HP)) as IH_A.
        unfold admissible in IH_A. simpl in IH_A.
        destruct IH_A as [_ [IHredA _]].
        eapply IHredA; [exact Hmid|exact Hstep].
      * intros t Hlc Hneutral Hred.
        split.
        -- exact Hlc.
        -- split.
           ++ constructor. intros u Htu.
              destruct (Hred u Htu) as [_ [Hsu _]]. exact Hsu.
           ++ intros U P HU HP w Hstep. inversion Hstep; subst.
              ** exfalso. apply Hneutral. constructor; assumption.
              ** destruct (Hred t' H1) as [Hlc' [_ Hall']].
              pose proof (IHA rho (extend_bound bs U P)
                (sem_valid_extend rho bs U P Hvalid HU HP)) as IH_A.
              unfold admissible in IH_A. simpl in IH_A.
              destruct IH_A as [_ [_ IHsatA]].
              eapply IHsatA.
              --- constructor; assumption.
              --- intro Hv. inversion Hv.
              --- exact (Hall' U P HU HP).
Qed.


Lemma SN_from_steps : forall t,
  (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.
Proof. intros; constructor; assumption. Qed.

Lemma SN_choice : forall t1 t2,
  locally_closed_tm t1 -> locally_closed_tm t2 ->
  strongly_normalizing t1 -> strongly_normalizing t2 ->
  strongly_normalizing (tm_choice t1 t2).
Proof.
  intros t1 t2 Hlc1 Hlc2 Hsn1 Hsn2. constructor.
  intros u Hstep. inversion Hstep; subst; assumption.
Qed.

Lemma lc_ty_subst_env : forall rho K T,
  (forall X, lc_ty_at K (fst (rho X))) ->
  lc_ty_at K T -> lc_ty_at K (subst_ty_env rho T).
Proof.
  intros rho K T Henv Hlc. revert rho K Henv Hlc.
  induction T; intros rho K Henv Hlc; simpl in *.
  - inversion Hlc; subst. constructor; assumption.
  - apply Henv.
  - inversion Hlc; subst. constructor; [eapply IHT1|eapply IHT2]; eauto.
  - inversion Hlc as [| | |k' A HA]; subst. constructor.
    eapply IHT with (K := S K).
    + intros X. apply lc_ty_at_mono with (n := K); [lia|apply Henv].
    + exact HA.
Qed.

Lemma lc_tm_ty_subst_env : forall rho K k t,
  (forall X, lc_ty_at K (fst (rho X))) ->
  lc_tm_at K k t -> lc_tm_at K k (subst_tm_ty_env rho t).
Proof.
  intros rho K k t Henv Hlc. revert rho K k Henv Hlc.
  induction t; intros rho K k Henv Hlc; simpl in *.
  - inversion Hlc; subst. constructor; assumption.
  - constructor.
  - inversion Hlc as [| |k' j T b HT Hb | | | |]; subst. constructor.
    + eapply lc_ty_subst_env; eauto.
    + eapply IHt; eauto.
  - inversion Hlc as [| | |k' j u v H1 H2 | | |]; subst. constructor.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  - inversion Hlc as [| | | |k' j b Hb | |]; subst. constructor.
    eapply IHt with (K := S K) (k := k).
    + intros X. apply lc_ty_at_mono with (n := K); [lia|apply Henv].
    + exact Hb.
  - inversion Hlc as [| | | | |k' j a T Ha HT |]; subst. constructor.
    + eapply IHt; eauto.
    + eapply lc_ty_subst_env; eauto.
  - inversion Hlc as [| | | | | |k' j u v H1 H2]; subst. constructor;
      [eapply IHt1|eapply IHt2]; eauto.
Qed.

Lemma lc_tm_subst_env : forall sigma K k t,
  (forall x, lc_tm_at K 0 (sigma x)) ->
  lc_tm_at K k t -> lc_tm_at K k (subst_tm_env sigma t).
Proof.
  intros sigma K k t Henv Hlc. revert sigma K k Henv Hlc.
  induction t; intros sigma K k Henv Hlc; simpl in *.
  - inversion Hlc; subst. constructor; assumption.
  - apply (lc_tm_at_mono K K 0 k); [lia|lia|apply Henv].
  - inversion Hlc as [| |k' j T b HT Hb | | | |]; subst. constructor.
    + exact HT.
    + eapply IHt; eauto.
  - inversion Hlc as [| | |k' j u v H1 H2 | | |]; subst. constructor;
      [eapply IHt1|eapply IHt2]; eauto.
  - inversion Hlc as [| | | |k' j b Hb | |]; subst. constructor.
    eapply IHt with (K := S K) (k := k).
    + intros x. apply lc_tm_at_mono with (K1 := K) (k1 := 0); [lia|lia|apply Henv].
    + exact Hb.
  - inversion Hlc as [| | | | |k' j a T Ha HT |]; subst. constructor;
      [eapply IHt|exact HT]; eauto.
  - inversion Hlc as [| | | | | |k' j u v H1 H2]; subst. constructor;
      [eapply IHt1|eapply IHt2]; eauto.
Qed.

Lemma eval_tm_lc : forall rho sigma t,
  sem_valid rho default_bound_env ->
  (forall x, locally_closed_tm (sigma x)) -> locally_closed_tm t ->
  locally_closed_tm (eval_tm rho sigma t).
Proof.
  intros rho sigma t [Hr Hb] Hsigma Ht. unfold eval_tm.
  apply lc_tm_subst_env; [exact Hsigma|].
  eapply lc_tm_ty_subst_env; [|exact Ht].
  intros X. exact (proj1 (Hr X)).
Qed.

Lemma subst_tm_ty_env_open_ty : forall rho X U P K t,
  sem_valid rho default_bound_env ->
  ~ In X (fv_tm_types t) ->
  subst_tm_ty_env (extend_type_env rho X U P)
    (open_tm_ty_rec K (Ty_FVar X) t) =
  open_tm_ty_rec K U (subst_tm_ty_env rho t).
Proof.
  intros rho X U P K t Hvalid. revert rho X U P K Hvalid.
  induction t; intros rho X U P K Hvalid Hfresh; simpl in *.
  - reflexivity.
  - reflexivity.
  - assert (HfT : ~ In X (fv_ty t)).
    { intro H. apply Hfresh. apply in_or_app; left; exact H. }
    assert (Hft : ~ In X (fv_tm_types t0)).
    { intro H. apply Hfresh. apply in_or_app; right; exact H. }
    rewrite (subst_ty_env_open_rec rho X U P K t default_bound_env Hvalid HfT).
    rewrite (IHt rho X U P K Hvalid Hft). reflexivity.
  - assert (Hf1 : ~ In X (fv_tm_types t1)).
    { intro H. apply Hfresh. apply in_or_app; left; exact H. }
    assert (Hf2 : ~ In X (fv_tm_types t2)).
    { intro H. apply Hfresh. apply in_or_app; right; exact H. }
    rewrite (IHt1 rho X U P K Hvalid Hf1), (IHt2 rho X U P K Hvalid Hf2). reflexivity.
  - rewrite (IHt rho X U P (S K) Hvalid Hfresh). reflexivity.
  - assert (Hf1 : ~ In X (fv_tm_types t)).
    { intro H. apply Hfresh. apply in_or_app; left; exact H. }
    assert (HfT : ~ In X (fv_ty t0)).
    { intro H. apply Hfresh. apply in_or_app; right; exact H. }
    rewrite (IHt rho X U P K Hvalid Hf1).
    rewrite (subst_ty_env_open_rec rho X U P K t0 default_bound_env Hvalid HfT).
    reflexivity.
  - assert (Hf1 : ~ In X (fv_tm_types t1)).
    { intro H. apply Hfresh. apply in_or_app; left; exact H. }
    assert (Hf2 : ~ In X (fv_tm_types t2)).
    { intro H. apply Hfresh. apply in_or_app; right; exact H. }
    rewrite (IHt1 rho X U P K Hvalid Hf1), (IHt2 rho X U P K Hvalid Hf2). reflexivity.
Qed.

Lemma subst_tm_env_open_ty : forall sigma K U t,
  (forall x, locally_closed_tm (sigma x)) ->
  subst_tm_env sigma (open_tm_ty_rec K U t) =
  open_tm_ty_rec K U (subst_tm_env sigma t).
Proof.
  intros sigma K U t Hsigma. revert K.
  induction t; intros K; simpl.
  - reflexivity.
  - rewrite (lc_tm_type_open_id 0 0 K (sigma a) U); [reflexivity|lia|apply Hsigma].
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma lookup_context_fv : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (fv_ty T) ->
  In X (fv_context_types Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T X Hlook Hfv; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlook; subst. apply in_or_app; left; exact Hfv.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma term_env_rel_type_fresh : forall rho rho' Gamma sigma X,
  (forall Y, Y <> X -> rho Y = rho' Y) ->
  (forall y T, lookup_context y Gamma = Some T -> ~ In X (fv_ty T)) ->
  term_env_rel rho Gamma sigma -> term_env_rel rho' Gamma sigma.
Proof.
  intros rho rho' Gamma sigma X Heq Hfresh [Hlc Hrel]. split; [exact Hlc|].
  intros y T Hlook. apply (proj1 (denote_type_env_fresh rho rho' default_bound_env X T Heq
    (Hfresh y T Hlook) (sigma y))). eapply Hrel; eauto.
Qed.

Lemma has_type_result_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T Hty. induction Hty as
    [Delta Gamma x T Hlookup Hwf
    |L Delta Gamma T1 b T2 Hwf Hbody IHbody
    |Delta Gamma t1 t2 T1 T2 Hty1 IH1 Hty2 IH2
    |L Delta Gamma b T Hbody IHbody
    |Delta Gamma t A U Hfun IH Hwf
    |Delta Gamma t1 t2 T Hchoice1 IH1 Hchoice2 IH2].
  - eapply wf_ty_lc; eassumption.
  - destruct (fresh_atom L) as [x Hx].
    pose proof (IHbody x Hx) as Hlc2. unfold locally_closed_ty in *.
    apply lc_ty_arrow; [eapply wf_ty_lc; eassumption|exact Hlc2].
  - inversion IH1 as [| |k A B HA HB|]; subst. exact HB.
  - destruct (fresh_atom L) as [X HX].
    pose proof (IHbody X HX) as Hopen.
    unfold locally_closed_ty in Hopen |- *.
    apply lc_ty_open_inv in Hopen. apply lc_ty_all. exact Hopen.
  - inversion IH as [| | |k B0 HB0]; subst.
    eapply lc_ty_open_top; [exact HB0|eapply wf_ty_lc; eassumption].
  - assumption.
Qed.

Lemma denote_app_abs : forall rho bs A B U body u,
  sem_valid rho bs -> denote rho bs A u ->
  locally_closed_tm (tm_abs U body) ->
  (forall v, denote rho bs A v -> denote rho bs B (open_tm body v)) ->
  denote rho bs B (tm_app (tm_abs U body) u).
Proof.
  intros rho bs A B U body u Hvalid Hu Hlab Hbody.
  destruct (denote_admissible rho bs A Hvalid) as [HA _].
  destruct (HA u Hu) as [Hulc Husn].
  destruct (denote_admissible rho bs B Hvalid) as [_ [_ Hsat]].
  destruct (denote_admissible rho bs A Hvalid) as [_ [Hred _]].
  assert (Happ : forall v, strongly_normalizing v -> denote rho bs A v ->
      denote rho bs B (tm_app (tm_abs U body) v)).
  { intros v Hsn. induction Hsn as [v Hsteps IH]. intros Hv.
    apply Hsat.
    - destruct (HA v Hv) as [Hvlc _].
      unfold locally_closed_tm in *. apply lc_tm_app; assumption.
    - intro Hval. inversion Hval.
    - intros w Hstep. inversion Hstep; subst.
      + apply Hbody. exact Hv.
      + exfalso. eapply value_no_step; [apply v_abs; exact Hlab|eassumption].
      + apply IH.
        * exact H3.
        * eapply Hred; eauto. }
  apply Happ; assumption.
Qed.

Lemma eval_tm_open_term : forall rho sigma x u b,
  ~ In x (fv_tm b) ->
  (forall y, locally_closed_tm (sigma y)) -> locally_closed_tm u ->
  eval_tm rho (extend_term_env sigma x u) (open_tm b (tm_fvar x)) =
  open_tm (eval_tm rho sigma b) u.
Proof.
  intros rho sigma x u b Hfresh Hsigma Hu. unfold eval_tm, open_tm.
  rewrite subst_tm_ty_open_tm_rec.
  rewrite subst_tm_env_open.
  - reflexivity.
  - rewrite fv_tm_ty_env. exact Hfresh.
  - exact Hsigma.
  - exact Hu.
Qed.

Lemma eval_tm_open_type : forall rho sigma X V P b,
  sem_valid rho default_bound_env ->
  ~ In X (fv_tm_types b) ->
  (forall y, locally_closed_tm (sigma y)) ->
  eval_tm (extend_type_env rho X V P) sigma
    (open_tm_ty b (Ty_FVar X)) =
  open_tm_ty (eval_tm rho sigma b) V.
Proof.
  intros rho sigma X V P b Hvalid Hfresh Hsigma.
  unfold eval_tm, open_tm_ty.
  rewrite (subst_tm_ty_env_open_ty rho X V P 0 b Hvalid Hfresh).
  apply subst_tm_env_open_ty. exact Hsigma.
Qed.

Lemma fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T -> forall rho sigma,
  sem_valid rho default_bound_env -> term_env_rel rho Gamma sigma ->
  denote rho default_bound_env T (eval_tm rho sigma t).
Proof.
  intros Delta Gamma t T Hty. induction Hty as
    [Delta Gamma x T Hlookup Hwf
    |L Delta Gamma T1 b T2 Hwf Hbody IHbody
    |Delta Gamma t1 t2 T1 T2 Hty1 IH1 Hty2 IH2
    |L Delta Gamma b T Hbody IHbody
    |Delta Gamma t A U Hfun IH Hwf
    |Delta Gamma t1 t2 T Hchoice1 IH1 Hchoice2 IH2];
    intros rho sigma Hvalid Hrel; simpl [eval_tm].
  - exact (proj2 Hrel x T Hlookup).
  - pose proof (has_type_lc Delta Gamma (tm_abs T1 b) (Ty_Arrow T1 T2)
      (T_Abs L Delta Gamma T1 b T2 Hwf Hbody)) as Hlcsrc.
    assert (Hlev : locally_closed_tm (eval_tm rho sigma (tm_abs T1 b))).
    { eapply eval_tm_lc; [exact Hvalid|apply (proj1 Hrel)|exact Hlcsrc]. }
    split.
    + change (locally_closed_tm (eval_tm rho sigma (tm_abs T1 b))).
      exact Hlev.
    + split.
      * constructor. intros w Hstep.
        exfalso. eapply value_no_step; [apply v_abs; exact Hlev|exact Hstep].
      * intros u Hu.
        assert (Hbodyrel : forall v, denote rho default_bound_env T1 v ->
          denote rho default_bound_env T2 (open_tm (eval_tm rho sigma b) v)).
        { intros v Hv.
          destruct (fresh_atom (L ++ fv_tm b)) as [x Hx].
          assert (HxL : ~ In x L).
          { intro Hin. apply Hx. apply in_or_app; left; exact Hin. }
          assert (Hxb : ~ In x (fv_tm b)).
          { intro Hin. apply Hx. apply in_or_app; right; exact Hin. }
          assert (Hvlc : locally_closed_tm v).
          { exact (proj1 ((proj1 (denote_admissible rho default_bound_env T1 Hvalid)) v Hv)). }
          pose proof (IHbody x HxL rho (extend_term_env sigma x v) Hvalid
            (term_env_rel_extend rho Gamma sigma x T1 v Hrel Hv Hvlc)) as Hsem.
          rewrite (eval_tm_open_term rho sigma x v b Hxb (proj1 Hrel) Hvlc) in Hsem.
          exact Hsem. }
        eapply denote_app_abs; [exact Hvalid|exact Hu| |exact Hbodyrel].
        change (locally_closed_tm (eval_tm rho sigma (tm_abs T1 b))).
        exact Hlev.
  - specialize (IH1 rho sigma Hvalid Hrel).
    specialize (IH2 rho sigma Hvalid Hrel).
    exact (proj2 (proj2 IH1) (eval_tm rho sigma t2) IH2).
  - pose proof (has_type_lc Delta Gamma (tm_tabs b) (Ty_All T)
      (T_TAbs L Delta Gamma b T Hbody)) as Hlcsrc.
    assert (Hlev : locally_closed_tm (eval_tm rho sigma (tm_tabs b))).
    { eapply eval_tm_lc; [exact Hvalid|apply (proj1 Hrel)|exact Hlcsrc]. }
    pose proof (has_type_result_lc Delta Gamma (tm_tabs b) (Ty_All T)
      (T_TAbs L Delta Gamma b T Hbody)) as HtypeLC.
    unfold locally_closed_ty in HtypeLC. inversion HtypeLC as [| | |k Tbody HTbody]; subst.
    split.
    + change (locally_closed_tm (eval_tm rho sigma (tm_tabs b))).
      exact Hlev.
    + split.
      * constructor. intros w Hstep.
        exfalso. eapply value_no_step; [apply v_tabs; exact Hlev|exact Hstep].
      * intros V P HV HP w Hstep.
        inversion Hstep; subst; try (exfalso; eapply value_no_step;
          [apply v_tabs; exact Hlev|eassumption]).
        destruct (fresh_atom (L ++ fv_tm_types b ++ fv_ty T ++ fv_context_types Gamma)) as [X HX].
        assert (HXL : ~ In X L).
        { intro Hin. apply HX. repeat (apply in_or_app; left); exact Hin. }
        assert (HXb : ~ In X (fv_tm_types b)).
        { intro Hin. apply HX. apply in_or_app; right. apply in_or_app; left.
          exact Hin. }
        assert (HXT : ~ In X (fv_ty T)).
        { intro Hin. apply HX. apply in_or_app; right. apply in_or_app; right.
          apply in_or_app; left. exact Hin. }
        assert (HXG : ~ In X (fv_context_types Gamma)).
        { intro Hin. apply HX. repeat (apply in_or_app; right); exact Hin. }
        assert (HfreshG : forall y A0, lookup_context y Gamma = Some A0 -> ~ In X (fv_ty A0)).
        { intros y A0 Hlook Hin. apply HXG. eapply lookup_context_fv; eauto. }
        assert (HrelX : term_env_rel (extend_type_env rho X V P) Gamma sigma).
        { eapply term_env_rel_type_fresh; [|exact HfreshG|exact Hrel].
          intros Y HY. unfold extend_type_env. assert ((X =? Y) = false) by
            (apply Nat.eqb_neq; congruence). now rewrite H. }
        assert (HvalidX : sem_valid (extend_type_env rho X V P) default_bound_env).
        { eapply sem_valid_extend_type; eauto. }
        pose proof (IHbody X HXL (extend_type_env rho X V P) sigma HvalidX HrelX) as Hsem.
        assert (Heval : eval_tm (extend_type_env rho X V P) sigma (open_tm_ty b (Ty_FVar X)) =
          open_tm_ty (eval_tm rho sigma b) V).
        { exact (eval_tm_open_type rho sigma X V P b Hvalid HXb (proj1 Hrel)). }
        rewrite Heval in Hsem.
        apply (proj1 (denote_open_ty rho default_bound_env X V P 0 T Hvalid
          HV HP HTbody HXT
          (open_tm_ty (eval_tm rho sigma b) V))).
        exact Hsem.
  - pose proof (IH rho sigma Hvalid Hrel) as Hsem.
    pose proof (wf_ty_lc _ _ Hwf) as HUl.
    assert (HV : locally_closed_ty (subst_ty_env rho U)).
    { unfold locally_closed_ty. eapply lc_ty_subst_env; [|exact HUl].
      intros X. exact (proj1 (proj1 Hvalid X)). }
    assert (HP : admissible (denote rho default_bound_env U)).
    { apply denote_admissible. exact Hvalid. }
    assert (HvalidU : sem_valid rho
      (extend_bound default_bound_env (subst_ty_env rho U) (denote rho default_bound_env U))).
    { eapply sem_valid_extend; eauto. }
    destruct (denote_admissible rho
      (extend_bound default_bound_env (subst_ty_env rho U) (denote rho default_bound_env U))
      A HvalidU) as [_ [_ Hsat]].
    assert (Htapplc : locally_closed_tm (tm_tapp (eval_tm rho sigma t) (subst_ty_env rho U))).
    { apply lc_tm_tapp; [|exact HV].
      destruct Hsem as [Hlc _]. exact Hlc. }
    assert (Htapnval : ~ value (tm_tapp (eval_tm rho sigma t) (subst_ty_env rho U))).
    { intro Hval. inversion Hval. }
    assert (Hbody : denote rho
      (extend_bound default_bound_env (subst_ty_env rho U) (denote rho default_bound_env U))
      A (tm_tapp (eval_tm rho sigma t) (subst_ty_env rho U))).
    { apply Hsat; [exact Htapplc|exact Htapnval|].
      intros w Hstep.
      destruct Hsem as [_ [_ Hall]].
      eapply Hall with (U := subst_ty_env rho U)
        (P := denote rho default_bound_env U); eauto. }
    pose proof (has_type_result_lc Delta Gamma t (Ty_All A) Hfun) as HallLC.
    unfold locally_closed_ty in HallLC.
    inversion HallLC as [| | |k A0 HA0]; subst.
    apply (proj2 (denote_open_sem rho default_bound_env 0 U A Hvalid HUl HUl
      HA0
      (tm_tapp (eval_tm rho sigma t) (subst_ty_env rho U)))).
    exact Hbody.
  - destruct (denote_admissible rho default_bound_env T Hvalid) as [_ [_ Hsat]].
    apply Hsat.
    + eapply lc_tm_choice.
      * eapply eval_tm_lc; [exact Hvalid|apply (proj1 Hrel)|eapply has_type_lc; eauto].
      * eapply eval_tm_lc; [exact Hvalid|apply (proj1 Hrel)|eapply has_type_lc; eauto].
    + intro Hval. inversion Hval.
    + intros w Hstep. inversion Hstep; subst;
        [exact (IH1 rho sigma Hvalid Hrel)|exact (IH2 rho sigma Hvalid Hrel)].
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Hty.
  set (rho := fun X : atom => (Ty_FVar X, sn_candidate)).
  set (sigma := fun x : atom => tm_fvar x).
  assert (Hvalid : sem_valid rho default_bound_env).
  { split.
    - intros X. split; [constructor|apply sn_candidate_admissible].
    - intros i. split; [constructor|apply sn_candidate_admissible]. }
  assert (Hrel : term_env_rel rho empty sigma).
  { split.
    - intro x. constructor.
    - intros x U Hlook. discriminate. }
  assert (Htyid : forall A, subst_ty_env rho A = A).
  { induction A; simpl; try rewrite IHA1; try rewrite IHA2; try rewrite IHA;
      reflexivity. }
  assert (Htmtyid : forall a, subst_tm_ty_env rho a = a).
  { induction a; simpl; try rewrite Htyid; try rewrite IHa; try rewrite IHa1;
      try rewrite IHa2; reflexivity. }
  assert (Htmid : forall a, subst_tm_env sigma a = a).
  { induction a; simpl; try rewrite IHa; try rewrite IHa1; try rewrite IHa2;
      reflexivity. }
  pose proof (fundamental [] empty t T Hty rho sigma Hvalid Hrel) as Hsem.
  change (denote rho default_bound_env T
    (subst_tm_env sigma (subst_tm_ty_env rho t))) in Hsem.
  rewrite (Htmtyid t), (Htmid t) in Hsem.
  eapply denote_sn; [exact Hvalid|exact Hsem].
Qed.

End SystemFNormalizationNondeterminismHardTask.
