(** System F CBV strong-normalization benchmark, Hard variant.
    Features: if-nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
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

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.

Hint Constructors lc_ty_at lc_tm_at value : core.

(* Construct the logical relation and supporting proofs here. *)

Definition neutral (t : tm) : Prop :=
  match t with
  | tm_abs _ _ | tm_tabs _ | tm_true | tm_false => False
  | _ => True
  end.

Lemma sn_step : forall t u,
  strongly_normalizing t -> t --> u -> strongly_normalizing u.
Proof.
  intros t u H Hstep. destruct H as [t H]. now apply H.
Qed.

Lemma value_no_step : forall v u, value v -> v --> u -> False.
Proof.
  intros v u Hv Hs. inversion Hv; subst; inversion Hs.
Qed.

Lemma multi_value : forall v u,
  value v -> v -->* u -> u = v.
Proof.
  intros v u Hv Hm. inversion Hm; subst; auto.
  exfalso. eapply value_no_step; eauto.
Qed.

Record candidate : Type := {
  cand : tm -> Prop;
  cand_sn : forall t, cand t -> strongly_normalizing t;
  cand_step : forall t u, cand t -> t --> u -> cand u;
  cand_back : forall t, neutral t ->
    (forall u, t --> u -> cand u) -> cand t
}.

Definition ty_env := nat -> candidate.
Definition free_ty_env := atom -> candidate.

Definition extend_ty_env (C : candidate) (eta : ty_env) : ty_env :=
  fun i => match i with 0 => C | S j => eta j end.

Fixpoint interp (T : ty) (eta : ty_env) (rho : free_ty_env)
    (t : tm) : Prop :=
  match T with
  | Ty_BVar i => cand (eta i) t
  | Ty_FVar X => cand (rho X) t
  | Ty_Bool => strongly_normalizing t
  | Ty_Arrow A B =>
      strongly_normalizing t /\
      (forall U body, t -->* tm_abs U body ->
        forall v, value v -> interp A eta rho v ->
          interp B eta rho (open_tm body v))
  | Ty_All A =>
      strongly_normalizing t /\
      (forall body, t -->* tm_tabs body ->
        forall U (C : candidate), locally_closed_ty U ->
          interp A (extend_ty_env C eta) rho (open_tm_ty body U))
  end.

Lemma interp_sn : forall T eta rho t,
  interp T eta rho t -> strongly_normalizing t.
Proof.
  destruct T; simpl; intros eta rho t H.
  - exact (cand_sn (eta n) t H).
  - exact (cand_sn (rho a) t H).
  - exact (proj1 H).
  - exact (proj1 H).
  - exact H.
Qed.

Lemma interp_step : forall T eta rho t u,
  interp T eta rho t -> t --> u -> interp T eta rho u.
Proof.
  induction T; simpl; intros eta rho t u H Hs.
  - eapply cand_step; eauto.
  - eapply cand_step; eauto.
  - destruct H as [Hsn Hfun]. split.
    + eapply sn_step; eauto.
    + intros U body Hm v Hv Harg. eapply Hfun; eauto.
      eapply multi_step; eauto.
  - destruct H as [Hsn Hfun]. split.
    + eapply sn_step; eauto.
    + intros body Hm U C Hlc. eapply Hfun; eauto.
      eapply multi_step; eauto.
  - exact (sn_step t u H Hs).
Qed.

Lemma interp_back : forall T eta rho t,
  neutral t ->
  (forall u, t --> u -> interp T eta rho u) ->
  interp T eta rho t.
Proof.
  induction T; simpl; intros eta rho t Hneu Hred.
  - eapply cand_back; eauto.
  - eapply cand_back; eauto.
  - split.
    + constructor. intros u Hs. exact (proj1 (Hred u Hs)).
    + intros U body Hm v Hv Harg.
      inversion Hm; subst.
      * simpl in Hneu. contradiction.
      * destruct (Hred _ H) as [_ Hfun]. eapply Hfun; eauto.
  - split.
    + constructor. intros u Hs. exact (proj1 (Hred u Hs)).
    + intros body Hm U C Hlc.
      inversion Hm; subst.
      * simpl in Hneu. contradiction.
      * destruct (Hred _ H) as [_ Hfun]. eapply Hfun; eauto.
  - constructor. intros u Hs. exact (Hred u Hs).
Qed.

Definition interp_candidate (T : ty) (eta : ty_env)
    (rho : free_ty_env) : candidate.
Proof.
  refine {| cand := interp T eta rho |}.
  - exact (interp_sn T eta rho).
  - exact (interp_step T eta rho).
  - exact (interp_back T eta rho).
Defined.

Lemma interp_app : forall A B eta rho t1 t2,
  interp (Ty_Arrow A B) eta rho t1 ->
  interp A eta rho t2 ->
  interp B eta rho (tm_app t1 t2).
Proof.
  intros A B eta rho t1 t2 H1 H2.
  pose proof (interp_sn _ _ _ _ H1) as Hsn1.
  revert t2 H1 H2.
  induction Hsn1 as [t1 Hred1 IH1]; intros t2 H1 H2.
  pose proof (interp_sn _ _ _ _ H2) as Hsn2.
  revert H2.
  induction Hsn2 as [t2 Hred2 IH2]; intros H2.
  apply interp_back; [exact I|].
  intros u Hs. inversion Hs; subst.
  - destruct H1 as [_ Hfun]. eapply Hfun.
    + constructor.
    + eassumption.
    + exact H2.
  - eapply IH1; eauto using interp_step.
  - eapply IH2; eauto using interp_step.
Qed.

Lemma interp_tapp : forall A eta rho t U,
  interp (Ty_All A) eta rho t ->
  locally_closed_ty U ->
  interp A (extend_ty_env (interp_candidate U eta rho) eta) rho
    (tm_tapp t U).
Proof.
  intros A eta rho t U Ht HU.
  pose proof (interp_sn _ _ _ _ Ht) as Hsn.
  induction Hsn as [t Hred IH].
  apply interp_back; [exact I|].
  intros u Hs. inversion Hs; subst.
  - destruct Ht as [_ Hfun]. eapply Hfun; eauto.
    constructor.
  - eapply IH; [eassumption|]. eapply interp_step; eassumption.
Qed.

Lemma interp_tapp_any : forall A eta rho t U C,
  interp (Ty_All A) eta rho t -> locally_closed_ty U ->
  interp A (extend_ty_env C eta) rho (tm_tapp t U).
Proof.
  intros A eta rho t U C Ht HU.
  pose proof (interp_sn _ _ _ _ Ht) as Hsn.
  induction Hsn as [t Hred IH].
  apply interp_back; [exact I|].
  intros u Hs. inversion Hs; subst.
  - destruct Ht as [_ Hfun]. eapply Hfun; eauto. constructor.
  - eapply IH; [eassumption|]. eapply interp_step; eassumption.
Qed.

Lemma interp_if : forall T eta rho b t1 t2,
  interp Ty_Bool eta rho b ->
  interp T eta rho t1 -> interp T eta rho t2 ->
  interp T eta rho (tm_if b t1 t2).
Proof.
  intros T eta rho b t1 t2 Hb H1 H2.
  simpl in Hb. induction Hb as [b Hred IH].
  apply interp_back; [exact I|].
  intros u Hs. inversion Hs; subst; auto.
Qed.

Lemma interp_choice : forall T eta rho t1 t2,
  interp T eta rho t1 -> interp T eta rho t2 ->
  interp T eta rho (tm_choice t1 t2).
Proof.
  intros T eta rho t1 t2 H1 H2.
  apply interp_back; [exact I|].
  intros u Hs. inversion Hs; subst; assumption.
Qed.

Fixpoint ty_inst (theta : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow A B => Ty_Arrow (ty_inst theta A) (ty_inst theta B)
  | Ty_All A => Ty_All (ty_inst theta A)
  | Ty_Bool => Ty_Bool
  end.

Fixpoint tm_inst (theta : atom -> ty) (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs A b => tm_abs (ty_inst theta A) (tm_inst theta sigma b)
  | tm_app a b => tm_app (tm_inst theta sigma a) (tm_inst theta sigma b)
  | tm_tabs b => tm_tabs (tm_inst theta sigma b)
  | tm_tapp a A => tm_tapp (tm_inst theta sigma a) (ty_inst theta A)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if a b c => tm_if (tm_inst theta sigma a) (tm_inst theta sigma b) (tm_inst theta sigma c)
  | tm_choice a b => tm_choice (tm_inst theta sigma a) (tm_inst theta sigma b)
  end.

Definition ty_override (theta : atom -> ty) (X : atom) (U : ty) : atom -> ty :=
  fun Y => if Nat.eqb X Y then U else theta Y.
Definition tm_override (sigma : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else sigma y.

Lemma lc_ty_weaken : forall k j T,
  k <= j -> lc_ty_at k T -> lc_ty_at j T.
Proof.
  intros k j T Hle Hlc. revert j Hle.
  induction Hlc; intros j Hle.
  - constructor. lia.
  - constructor.
  - constructor; [eapply IHHlc1|eapply IHHlc2]; eauto.
  - constructor. eapply IHHlc. lia.
  - constructor.
Qed.

Lemma lc_ty_open_inverse : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  induction T; intros k X H; simpl in H.
  - destruct (Nat.eqb k n) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst. constructor. lia.
    + inversion H; subst. constructor. lia.
  - constructor.
  - inversion H; subst. constructor; [eapply IHT1|eapply IHT2]; eauto.
  - inversion H; subst. constructor. eapply IHT; eauto.
  - constructor.
Qed.

Lemma fresh_list : forall L : list atom, exists X, ~ In X L.
Proof.
  intro L. exists (S (fold_right Nat.max 0 L)).
  assert (Hbound : forall x, In x L -> x <= fold_right Nat.max 0 L).
  { induction L as [|a L IH]; simpl; intros x Hin.
    - contradiction.
    - destruct Hin as [<- | Hin]; [lia|].
      specialize (IH x Hin). lia. }
  intro Hin. specialize (Hbound _ Hin). lia.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf.
  induction Hwf as [Delta X Hin | Delta A B HA IHA HB IHB |
    L Delta T Hbody IH | Delta].
  - constructor.
  - constructor; assumption.
  - destruct (fresh_list L) as [X HX].
    specialize (IH X HX). unfold locally_closed_ty in IH.
    apply lc_ty_open_inverse in IH. now constructor.
  - constructor.
Qed.

Lemma ty_inst_lc : forall k T theta,
  lc_ty_at k T ->
  (forall X, locally_closed_ty (theta X)) ->
  lc_ty_at k (ty_inst theta T).
Proof.
  intros k T theta Hlc. induction Hlc; intros Htheta; simpl.
  - constructor; assumption.
  - apply lc_ty_weaken with (k := 0); [lia|apply Htheta].
  - constructor; auto.
  - constructor; auto.
  - constructor.
Qed.

Lemma ty_inst_wf_lc : forall Delta T theta,
  wf_ty Delta T ->
  (forall X, locally_closed_ty (theta X)) ->
  locally_closed_ty (ty_inst theta T).
Proof.
  intros Delta T theta Hwf Htheta.
  exact (ty_inst_lc 0 T theta (wf_ty_lc Delta T Hwf) Htheta).
Qed.

Fixpoint ty_bound (T : ty) : nat :=
  match T with
  | Ty_BVar _ | Ty_Bool => 0
  | Ty_FVar X => X
  | Ty_Arrow A B => Nat.max (ty_bound A) (ty_bound B)
  | Ty_All A => ty_bound A
  end.

Fixpoint tm_term_bound (t : tm) : nat :=
  match t with
  | tm_bvar _ | tm_true | tm_false => 0
  | tm_fvar x => x
  | tm_abs _ b | tm_tabs b | tm_tapp b _ => tm_term_bound b
  | tm_app a b | tm_choice a b => Nat.max (tm_term_bound a) (tm_term_bound b)
  | tm_if a b c => Nat.max (tm_term_bound a)
      (Nat.max (tm_term_bound b) (tm_term_bound c))
  end.

Fixpoint tm_type_bound (t : tm) : nat :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_true | tm_false => 0
  | tm_abs A b => Nat.max (ty_bound A) (tm_type_bound b)
  | tm_tabs b => tm_type_bound b
  | tm_tapp b A => Nat.max (tm_type_bound b) (ty_bound A)
  | tm_app a b | tm_choice a b => Nat.max (tm_type_bound a) (tm_type_bound b)
  | tm_if a b c => Nat.max (tm_type_bound a)
      (Nat.max (tm_type_bound b) (tm_type_bound c))
  end.

Fixpoint context_type_bound (Gamma : context) : nat :=
  match Gamma with
  | [] => 0
  | (_, A) :: G => Nat.max (ty_bound A) (context_type_bound G)
  end.

Lemma ty_inst_override_fresh : forall T theta X U,
  ty_bound T < X ->
  ty_inst (ty_override theta X U) T = ty_inst theta T.
Proof.
  induction T; intros theta X U Hfresh; simpl in *; try reflexivity.
  - unfold ty_override. destruct (Nat.eqb X a) eqn:E;
      [apply Nat.eqb_eq in E; lia|reflexivity].
  - f_equal; [apply IHT1|apply IHT2]; lia.
  - f_equal. apply IHT. lia.
Qed.

Lemma tm_inst_override_term_fresh : forall t theta sigma x v,
  tm_term_bound t < x ->
  tm_inst theta (tm_override sigma x v) t = tm_inst theta sigma t.
Proof.
  induction t; intros theta sigma x v Hfresh; simpl in *; try reflexivity;
    try (f_equal; eauto; lia).
  - unfold tm_override. destruct (Nat.eqb x a) eqn:E;
      [apply Nat.eqb_eq in E; lia|reflexivity].
  - f_equal; [apply IHt1|apply IHt2]; lia.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; lia.
  - f_equal; [apply IHt1|apply IHt2]; lia.
Qed.

Lemma tm_inst_override_type_fresh : forall t theta sigma X U,
  tm_type_bound t < X ->
  tm_inst (ty_override theta X U) sigma t = tm_inst theta sigma t.
Proof.
  induction t; intros theta sigma X U Hfresh; simpl in *; try reflexivity.
  - f_equal.
    + apply ty_inst_override_fresh. lia.
    + apply IHt. lia.
  - f_equal; [apply IHt1|apply IHt2]; lia.
  - f_equal. apply IHt. lia.
  - f_equal.
    + apply IHt. lia.
    + apply ty_inst_override_fresh. lia.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; lia.
  - f_equal; [apply IHt1|apply IHt2]; lia.
Qed.

Lemma lc_ty_open_rec_id : forall K T,
  lc_ty_at K T -> forall k U, K <= k -> open_ty_rec k U T = T.
Proof.
  intros K T Hlc. induction Hlc; intros k' U Hle; simpl.
  - destruct (Nat.eqb k' i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - f_equal; auto.
  - f_equal. apply IHHlc. lia.
  - reflexivity.
Qed.

Lemma lc_tm_open_rec_id : forall K n t,
  lc_tm_at K n t -> forall k u, n <= k -> open_tm_rec k u t = t.
Proof.
  intros K n t Hlc. induction Hlc; intros k' u Hle; simpl;
    try reflexivity; try (f_equal; eauto; lia).
  - destruct (Nat.eqb k' i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - f_equal. apply IHHlc. lia.
Qed.

Lemma lc_tm_open_ty_rec_id : forall K n t,
  lc_tm_at K n t -> forall k U, K <= k -> open_tm_ty_rec k U t = t.
Proof.
  intros K n t Hlc. induction Hlc; intros k' U Hle; simpl;
    try reflexivity; try (f_equal; eauto; lia).
  - f_equal.
    + apply lc_ty_open_rec_id with (K := K); assumption.
    + apply IHHlc. assumption.
  - f_equal. apply IHHlc. lia.
  - f_equal.
    + apply IHHlc. assumption.
    + apply lc_ty_open_rec_id with (K := K); assumption.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; inversion H; subst; unfold locally_closed_tm in *; eauto.
Qed.

Lemma ty_inst_open_rec : forall T k U theta,
  (forall X, locally_closed_ty (theta X)) ->
  ty_inst theta (open_ty_rec k U T) =
  open_ty_rec k (ty_inst theta U) (ty_inst theta T).
Proof.
  induction T; intros k U theta Htheta; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply lc_ty_open_rec_id with (K := 0); [apply Htheta|lia].
  - f_equal; auto.
  - f_equal. apply IHT. assumption.
  - reflexivity.
Qed.

Lemma tm_inst_open_rec : forall t k u theta sigma,
  (forall x, locally_closed_tm (sigma x)) ->
  tm_inst theta sigma (open_tm_rec k u t) =
  open_tm_rec k (tm_inst theta sigma u) (tm_inst theta sigma t).
Proof.
  induction t; intros k u theta sigma Hsigma; simpl;
    try reflexivity; try (f_equal; eauto).
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply lc_tm_open_rec_id with (K := 0) (n := 0);
      [apply Hsigma|lia].
Qed.

Lemma tm_inst_open_ty_rec : forall t k U theta sigma,
  (forall X, locally_closed_ty (theta X)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  tm_inst theta sigma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (ty_inst theta U) (tm_inst theta sigma t).
Proof.
  induction t; intros k U theta sigma Htheta Hsigma; simpl;
    try reflexivity; try (f_equal; eauto using ty_inst_open_rec).
  - symmetry. apply lc_tm_open_ty_rec_id with (K := 0) (n := 0);
      [apply Hsigma|lia].
Qed.

Lemma tm_override_lc : forall sigma x v,
  (forall y, locally_closed_tm (sigma y)) -> locally_closed_tm v ->
  forall y, locally_closed_tm (tm_override sigma x v y).
Proof.
  intros sigma x v Hsigma Hv y. unfold tm_override.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma ty_override_lc : forall theta X U,
  (forall Y, locally_closed_ty (theta Y)) -> locally_closed_ty U ->
  forall Y, locally_closed_ty (ty_override theta X U Y).
Proof.
  intros theta X U Htheta HU Y. unfold ty_override.
  destruct (Nat.eqb X Y); auto.
Qed.

Lemma tm_inst_open_term_fresh : forall t theta sigma x v,
  tm_term_bound t < x ->
  (forall y, locally_closed_tm (sigma y)) -> locally_closed_tm v ->
  tm_inst theta (tm_override sigma x v) (open_tm t (tm_fvar x)) =
  open_tm (tm_inst theta sigma t) v.
Proof.
  intros t theta sigma x v Hfresh Hsigma Hv.
  unfold open_tm.
  rewrite tm_inst_open_rec by (apply tm_override_lc; assumption).
  change (tm_inst theta (tm_override sigma x v) (tm_fvar x)) with
    (tm_override sigma x v x).
  unfold tm_override at 1. rewrite Nat.eqb_refl.
  rewrite tm_inst_override_term_fresh by assumption. reflexivity.
Qed.

Lemma tm_inst_open_type_fresh : forall t theta sigma X U,
  tm_type_bound t < X ->
  (forall Y, locally_closed_ty (theta Y)) -> locally_closed_ty U ->
  (forall y, locally_closed_tm (sigma y)) ->
  tm_inst (ty_override theta X U) sigma
    (open_tm_ty t (Ty_FVar X)) =
  open_tm_ty (tm_inst theta sigma t) U.
Proof.
  intros t theta sigma X U Hfresh Htheta HU Hsigma.
  unfold open_tm_ty.
  rewrite tm_inst_open_ty_rec by
    (try apply ty_override_lc; assumption).
  change (ty_inst (ty_override theta X U) (Ty_FVar X)) with
    (ty_override theta X U X).
  unfold ty_override at 1. rewrite Nat.eqb_refl.
  rewrite tm_inst_override_type_fresh by assumption. reflexivity.
Qed.

Lemma interp_lc_env : forall T K,
  lc_ty_at K T -> forall eta1 eta2 rho t,
  (forall i s, i < K -> cand (eta1 i) s <-> cand (eta2 i) s) ->
  interp T eta1 rho t <-> interp T eta2 rho t.
Proof.
  intros T K Hlc. induction Hlc; intros eta1 eta2 rho t Henv; simpl.
  - apply Henv. assumption.
  - tauto.
  - split; intros [Hsn Hfun]; split; [assumption| |assumption|];
      intros U body Hm v Hv Harg.
    + apply (proj1 (IHHlc2 _ _ _ _ Henv)).
      apply Hfun with (U := U); auto.
      apply (proj2 (IHHlc1 _ _ _ _ Henv)). exact Harg.
    + apply (proj2 (IHHlc2 _ _ _ _ Henv)).
      apply Hfun with (U := U); auto.
      apply (proj1 (IHHlc1 _ _ _ _ Henv)). exact Harg.
  - split; intros [Hsn Hfun]; split; [assumption| |assumption|];
      intros body Hm U C HU.
    + assert (Heq : interp T (extend_ty_env C eta1) rho
          (open_tm_ty body U) <->
          interp T (extend_ty_env C eta2) rho (open_tm_ty body U)).
      { apply IHHlc. intros [|i] s Hi; simpl.
        - tauto.
        - apply Henv. lia. }
      apply Heq. apply Hfun; assumption.
    + assert (Heq : interp T (extend_ty_env C eta1) rho
          (open_tm_ty body U) <->
          interp T (extend_ty_env C eta2) rho (open_tm_ty body U)).
      { apply IHHlc. intros [|i] s Hi; simpl.
        - tauto.
        - apply Henv. lia. }
      apply Heq. apply Hfun; assumption.
  - tauto.
Qed.

Definition replace_ty_env (k : nat) (C : candidate) (eta : ty_env) : ty_env :=
  fun i => if Nat.eqb k i then C else eta i.

Lemma interp_eta_pointwise : forall T eta1 eta2 rho t,
  (forall i, eta1 i = eta2 i) ->
  interp T eta1 rho t <-> interp T eta2 rho t.
Proof.
  induction T; intros eta1 eta2 rho t Heta; simpl.
  - rewrite Heta. tauto.
  - tauto.
  - split; intros [Hsn Hfun]; split; [assumption| |assumption|];
      intros U body Hm v Hv Harg.
    + apply (proj1 (IHT2 _ _ _ _ Heta)).
      apply Hfun with (U := U); auto.
      apply (proj2 (IHT1 _ _ _ _ Heta)). exact Harg.
    + apply (proj2 (IHT2 _ _ _ _ Heta)).
      apply Hfun with (U := U); auto.
      apply (proj1 (IHT1 _ _ _ _ Heta)). exact Harg.
  - split; intros [Hsn Hfun]; split; [assumption| |assumption|];
      intros body Hm U C HU.
    + assert (Heq : interp T (extend_ty_env C eta1) rho
          (open_tm_ty body U) <->
          interp T (extend_ty_env C eta2) rho (open_tm_ty body U)).
      { apply IHT. intros [|i]; simpl; [reflexivity|apply Heta]. }
      apply Heq. apply Hfun; assumption.
    + assert (Heq : interp T (extend_ty_env C eta1) rho
          (open_tm_ty body U) <->
          interp T (extend_ty_env C eta2) rho (open_tm_ty body U)).
      { apply IHT. intros [|i]; simpl; [reflexivity|apply Heta]. }
      apply Heq. apply Hfun; assumption.
  - tauto.
Qed.

Lemma replace_extend_interp : forall T k C D eta rho t,
  interp T (replace_ty_env (S k) C (extend_ty_env D eta)) rho t <->
  interp T (extend_ty_env D (replace_ty_env k C eta)) rho t.
Proof.
  intros T k C D eta rho t. apply interp_eta_pointwise.
  intros [|i]; reflexivity.
Qed.

Lemma interp_open_rec : forall T k U eta rho C t,
  locally_closed_ty U ->
  (forall s, cand C s <-> interp U eta rho s) ->
  interp (open_ty_rec k U T) eta rho t <->
  interp T (replace_ty_env k C eta) rho t.
Proof.
  induction T; intros k U eta rho C t HU HC; simpl.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold replace_ty_env. rewrite E. symmetry. apply HC.
    + unfold replace_ty_env. rewrite E. tauto.
  - tauto.
  - split; intros [Hsn Hfun]; split; [assumption| |assumption|];
      intros V body Hm v Hv Harg.
    + apply (proj1 (IHT2 k U eta rho C _ HU HC)).
      apply Hfun with (U := V); auto.
      apply (proj2 (IHT1 k U eta rho C _ HU HC)). exact Harg.
    + apply (proj2 (IHT2 k U eta rho C _ HU HC)).
      apply Hfun with (U := V); auto.
      apply (proj1 (IHT1 k U eta rho C _ HU HC)). exact Harg.
  - split; intros [Hsn Hfun]; split; [assumption| |assumption|];
      intros body Hm V D HV.
    + assert (HC' : forall s, cand C s <->
        interp U (extend_ty_env D eta) rho s).
      { intro s. transitivity (interp U eta rho s).
        - apply HC.
        - apply (interp_lc_env U 0 HU eta (extend_ty_env D eta) rho s).
          intros i q Hi. lia. }
      apply (proj1 (replace_extend_interp T k C D eta rho
        (open_tm_ty body V))).
      apply (proj1 (IHT (S k) U (extend_ty_env D eta) rho C
        (open_tm_ty body V) HU HC')).
      apply Hfun; assumption.
    + pose proof (Hfun body Hm V D HV) as Hbody.
      assert (HC' : forall s, cand C s <->
        interp U (extend_ty_env D eta) rho s).
      { intro s. transitivity (interp U eta rho s).
        - apply HC.
        - apply (interp_lc_env U 0 HU eta (extend_ty_env D eta) rho s).
          intros i q Hi. lia. }
      apply (proj2 (IHT (S k) U (extend_ty_env D eta) rho C
        (open_tm_ty body V) HU HC')).
      apply (proj2 (replace_extend_interp T k C D eta rho
        (open_tm_ty body V))). exact Hbody.
  - tauto.
Qed.

Lemma interp_open : forall T U eta rho C t,
  lc_ty_at 1 T -> locally_closed_ty U ->
  (forall s, cand C s <-> interp U eta rho s) ->
  interp (open_ty T U) eta rho t <->
  interp T (extend_ty_env C eta) rho t.
Proof.
  intros T U eta rho C t HT HU HC.
  unfold open_ty.
  transitivity (interp T (replace_ty_env 0 C eta) rho t).
  - apply interp_open_rec; assumption.
  - apply interp_lc_env with (K := 1); try assumption.
    intros [|i] s Hi; simpl in *; [tauto|lia].
Qed.

Lemma lc_ty_open_rec : forall k T U,
  lc_ty_at (S k) T -> locally_closed_ty U ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  intros k T U Hlc. remember (S k) as n eqn:Heq.
  revert k Heq.
  induction Hlc; intros k' Heq HU; subst; simpl.
  - destruct (Nat.eqb k' i) eqn:E.
    + apply lc_ty_weaken with (k := 0); [lia|assumption].
    + apply Nat.eqb_neq in E. constructor. lia.
  - constructor.
  - constructor; [eapply IHHlc1|eapply IHHlc2]; eauto.
  - constructor. eapply IHHlc; eauto.
  - constructor.
Qed.

Lemma typing_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T Hty.
  induction Hty as
    [Delta Gamma x T Hlookup Hwf
    |L Delta Gamma A b B Hwf Hbody IH
    |Delta Gamma a b A B Ha IHa Hb IHb
    |L Delta Gamma b T Hbody IH
    |Delta Gamma a T U Ha IHa Hwf
    |Delta Gamma |Delta Gamma
    |Delta Gamma a b c T Ha IHa Hb IHb Hc IHc
    |Delta Gamma a b T Ha IHa Hb IHb].
  - apply wf_ty_lc with (Delta := Delta). assumption.
  - constructor.
    + apply wf_ty_lc with (Delta := Delta). assumption.
    + destruct (fresh_list L) as [x Hx]. exact (IH x Hx).
  - inversion IHa; subst; assumption.
  - destruct (fresh_list L) as [X HX].
    specialize (IH X HX). unfold locally_closed_ty in IH.
    constructor. eapply lc_ty_open_inverse; eauto.
  - unfold locally_closed_ty in IHa. inversion IHa; subst.
    unfold open_ty. eapply lc_ty_open_rec; eauto using wf_ty_lc.
  - constructor.
  - constructor.
  - exact IHb.
  - exact IHa.
Qed.

Definition rho_override (rho : free_ty_env) (X : atom)
    (C : candidate) : free_ty_env :=
  fun Y => if Nat.eqb X Y then C else rho Y.

Lemma interp_rho_fresh : forall T eta rho X C t,
  ty_bound T < X ->
  interp T eta (rho_override rho X C) t <-> interp T eta rho t.
Proof.
  induction T; intros eta rho X C t Hfresh; simpl in *; try tauto.
  - unfold rho_override. destruct (Nat.eqb X a) eqn:E;
      [apply Nat.eqb_eq in E; lia|tauto].
  - split; intros [Hsn Hfun]; split; [assumption| |assumption|];
      intros U body Hm v Hv Harg.
    + apply (proj1 (IHT2 eta rho X C _ ltac:(lia))).
      apply Hfun with (U := U); auto.
      apply (proj2 (IHT1 eta rho X C _ ltac:(lia))). exact Harg.
    + apply (proj2 (IHT2 eta rho X C _ ltac:(lia))).
      apply Hfun with (U := U); auto.
      apply (proj1 (IHT1 eta rho X C _ ltac:(lia))). exact Harg.
  - split; intros [Hsn Hfun]; split; [assumption| |assumption|];
      intros body Hm U D HU.
    + apply (proj1 (IHT (extend_ty_env D eta) rho X C _ Hfresh)).
      apply Hfun; assumption.
    + apply (proj2 (IHT (extend_ty_env D eta) rho X C _ Hfresh)).
      apply Hfun; assumption.
Qed.

Lemma context_lookup_bound : forall Gamma x T,
  lookup_context x Gamma = Some T -> ty_bound T <= context_type_bound Gamma.
Proof.
  induction Gamma as [|[y A] Gamma IH]; intros x T H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion H; subst. lia.
    + specialize (IH _ _ H). lia.
Qed.

Lemma fresh_above : forall (L : list atom) n,
  exists X, n < X /\ ~ In X L.
Proof.
  intros L n. exists (S (Nat.max n (fold_right Nat.max 0 L))).
  split; [lia|].
  assert (Hbound : forall x, In x L -> x <= fold_right Nat.max 0 L).
  { induction L as [|a L IH]; simpl; intros x Hin.
    - contradiction.
    - destruct Hin as [<-|Hin]; [lia|specialize (IH x Hin); lia]. }
  intro Hin. specialize (Hbound _ Hin). lia.
Qed.

Lemma abs_multi_inv : forall A b U body,
  tm_abs A b -->* tm_abs U body -> A = U /\ b = body.
Proof.
  intros A b U body Hm. inversion Hm; subst.
  - auto.
  - inversion H.
Qed.

Lemma tabs_multi_inv : forall b body,
  tm_tabs b -->* tm_tabs body -> b = body.
Proof.
  intros b body Hm. inversion Hm; subst; auto. inversion H.
Qed.

Lemma fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall (eta : ty_env) (rho : free_ty_env)
    (theta : atom -> ty) (sigma : atom -> tm),
    (forall X, locally_closed_ty (theta X)) ->
    (forall x, locally_closed_tm (sigma x)) ->
    (forall x A, lookup_context x Gamma = Some A ->
       interp A eta rho (sigma x)) ->
    interp T eta rho (tm_inst theta sigma t).
Proof.
  intros Delta Gamma t T Hty.
  induction Hty as
    [Delta Gamma x T Hlookup Hwf
    |L Delta Gamma A b B Hwf Hbody IH
    |Delta Gamma a b A B Ha IHa Hb IHb
    |L Delta Gamma b T Hbody IH
    |Delta Gamma a T U Ha IHa Hwf
    |Delta Gamma |Delta Gamma
    |Delta Gamma a b c T Ha IHa Hb IHb Hc IHc
    |Delta Gamma a b T Ha IHa Hb IHb];
    intros eta rho theta sigma Htheta Hsigma Hgamma; simpl.
  - apply Hgamma with (x := x). exact Hlookup.
  - split.
    + constructor. intros u Hs. inversion Hs.
    + intros U body Hm v Hv Harg.
      apply abs_multi_inv in Hm. destruct Hm as [<- <-].
      destruct (fresh_above L (tm_term_bound b)) as [x [Hfresh Hnot]].
      specialize (IH x Hnot eta rho theta (tm_override sigma x v)
        Htheta (tm_override_lc sigma x v Hsigma (value_lc v Hv))).
      assert (Henv : forall y R,
        lookup_context y ((x, A) :: Gamma) = Some R ->
        interp R eta rho (tm_override sigma x v y)).
      { intros y R Hlookup'. simpl in Hlookup'.
        unfold tm_override. destruct (Nat.eqb y x) eqn:E.
        - inversion Hlookup'; subst. rewrite Nat.eqb_sym, E. exact Harg.
        - rewrite Nat.eqb_sym, E. eapply Hgamma. exact Hlookup'. }
      specialize (IH Henv).
      rewrite (tm_inst_open_term_fresh b theta sigma x v Hfresh Hsigma
        (value_lc v Hv)) in IH.
      exact IH.
  - eapply interp_app; [eapply IHa|eapply IHb]; eauto.
  - split.
    + constructor. intros u Hs. inversion Hs.
    + intros body Hm U C HU.
      apply tabs_multi_inv in Hm. subst body.
      destruct (fresh_above L
        (Nat.max (tm_type_bound b)
          (Nat.max (ty_bound T) (context_type_bound Gamma))))
        as [X [Hfresh Hnot]].
      set (rho' := rho_override rho X C).
      set (theta' := ty_override theta X U).
      assert (Henv : forall y A,
        lookup_context y Gamma = Some A -> interp A eta rho' (sigma y)).
      { intros y A Hlookup.
        unfold rho'.
        assert (Hbound : ty_bound A < X).
        { eapply Nat.le_lt_trans; [eapply context_lookup_bound; eauto|lia]. }
        apply (proj2 (interp_rho_fresh A eta rho X C (sigma y) Hbound)).
        eapply Hgamma; eauto. }
      assert (Htheta' : forall Y, locally_closed_ty (theta' Y)).
      { unfold theta'. eapply ty_override_lc; eauto. }
      pose proof (IH X Hnot eta rho' theta' sigma Htheta' Hsigma Henv)
        as Hopened.
      unfold theta' in Hopened.
      rewrite (tm_inst_open_type_fresh b theta sigma X U
        ltac:(lia) Htheta HU Hsigma) in Hopened.
      assert (HT : lc_ty_at 1 T).
      { pose proof (typing_type_lc _ _ _ _ (Hbody X Hnot)) as Hlc.
        unfold locally_closed_ty in Hlc.
        eapply lc_ty_open_inverse; eauto. }
      assert (HC : forall s, cand C s <-> interp (Ty_FVar X) eta rho' s).
      { intro s. unfold rho'. simpl. unfold rho_override.
        rewrite Nat.eqb_refl. tauto. }
      assert (HboundT : ty_bound T < X) by lia.
      apply (proj1 (interp_rho_fresh T (extend_ty_env C eta)
        rho X C (open_tm_ty (tm_inst theta sigma b) U) HboundT)).
      apply (proj1 (interp_open T (Ty_FVar X) eta rho' C
          (open_tm_ty (tm_inst theta sigma b) U) HT
          (lc_ty_fvar 0 X) HC)). exact Hopened.
  - pose proof (IHa eta rho theta sigma Htheta Hsigma Hgamma) as Hall.
    assert (HT : lc_ty_at 1 T).
    { pose proof (typing_type_lc _ _ _ _ Ha) as Hlc.
      unfold locally_closed_ty in Hlc. inversion Hlc; subst; assumption. }
    pose proof (wf_ty_lc _ _ Hwf) as HU.
    pose proof (ty_inst_wf_lc _ _ _ Hwf Htheta) as HUi.
    set (C := interp_candidate U eta rho).
    assert (HC : forall s, cand C s <-> interp U eta rho s).
    { intro s. unfold C. simpl. tauto. }
    apply (proj2 (interp_open T U eta rho C
      (tm_tapp (tm_inst theta sigma a) (ty_inst theta U))
      HT HU HC)).
    eapply interp_tapp_any; eauto.
  - constructor. intros u Hs. inversion Hs.
  - constructor. intros u Hs. inversion Hs.
  - eapply interp_if; eauto.
  - eapply interp_choice; eauto.
Qed.

Definition sn_candidate : candidate.
Proof.
  refine {| cand := strongly_normalizing |}.
  - intros t H. exact H.
  - intros t u H Hs. eapply sn_step; eauto.
  - intros t Hneutral Hred. constructor. exact Hred.
Defined.

Lemma ty_inst_id : forall T,
  ty_inst Ty_FVar T = T.
Proof.
  induction T; simpl; f_equal; auto.
Qed.

Lemma tm_inst_id : forall t,
  tm_inst Ty_FVar tm_fvar t = t.
Proof.
  induction t; simpl; try rewrite ty_inst_id; f_equal; auto.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Hty.
  pose (eta := fun _ : nat => sn_candidate).
  pose (rho := fun _ : atom => sn_candidate).
  pose proof (fundamental [] empty t T Hty eta rho Ty_FVar tm_fvar)
    as Hfund.
  assert (Htheta : forall X, locally_closed_ty (Ty_FVar X)).
  { intro X. constructor. }
  assert (Hsigma : forall x, locally_closed_tm (tm_fvar x)).
  { intro x. constructor. }
  specialize (Hfund Htheta Hsigma).
  assert (Henv : forall x A, lookup_context x empty = Some A ->
    interp A eta rho (tm_fvar x)).
  { intros x A Hlookup. discriminate. }
  specialize (Hfund Henv).
  rewrite tm_inst_id in Hfund.
  eapply interp_sn; eauto.
Qed.

End SystemFNormalizationIfNondeterminismHardTask.
