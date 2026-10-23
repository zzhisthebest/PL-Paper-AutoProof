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

(* Erasure removes type annotations from terms.  The logical relation is
   interpreted on erased terms, so substituting a type cannot change a
   candidate's term argument. *)
Fixpoint erase_tm (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs _ b => tm_abs Ty_Nat (erase_tm b)
  | tm_app t1 t2 => tm_app (erase_tm t1) (erase_tm t2)
  | tm_tabs b => tm_tabs (erase_tm b)
  | tm_tapp t1 _ => tm_tapp (erase_tm t1) Ty_Nat
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (erase_tm t1)
  | tm_natrec n b s => tm_natrec (erase_tm n) (erase_tm b) (erase_tm s)
  | tm_choice t1 t2 => tm_choice (erase_tm t1) (erase_tm t2)
  end.

Lemma erase_open_tm_rec : forall k u t,
  erase_tm (open_tm_rec k u t) = open_tm_rec k (erase_tm u) (erase_tm t).
Proof.
  intros k u t. revert k. induction t; intros k; simpl; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3].
  - f_equal; [apply IHt1|apply IHt2].
Qed.

Lemma erase_open_tm_ty_rec : forall k t U,
  erase_tm (open_tm_ty_rec k U t) = erase_tm t.
Proof.
  intros k t. revert k. induction t; intros k U; simpl; try reflexivity.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3].
  - f_equal; [apply IHt1|apply IHt2].
Qed.

Lemma erase_open_tm_ty : forall t U, erase_tm (open_tm_ty t U) = erase_tm t.
Proof. intros; apply erase_open_tm_ty_rec. Qed.

Lemma erase_tm_ty_subst : forall X U t, erase_tm (tm_ty_subst X U t) = erase_tm t.
Proof.
  intros X U t. induction t; simpl; try reflexivity.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3].
  - f_equal; [apply IHt1|apply IHt2].
Qed.

Lemma erase_idempotent : forall t, erase_tm (erase_tm t) = erase_tm t.
Proof. intros t. induction t; simpl; f_equal; auto. Qed.

Lemma erase_idempotent3 : forall t,
  erase_tm (erase_tm (erase_tm t)) = erase_tm t.
Proof.
  intros. transitivity (erase_tm (erase_tm t)); apply erase_idempotent.
Qed.

Fixpoint tm_fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ b => tm_fvars b
  | tm_app t1 t2 => tm_fvars t1 ++ tm_fvars t2
  | tm_tabs b => tm_fvars b
  | tm_tapp t1 _ => tm_fvars t1
  | tm_zero => []
  | tm_succ t1 => tm_fvars t1
  | tm_natrec n b s => tm_fvars n ++ tm_fvars b ++ tm_fvars s
  | tm_choice t1 t2 => tm_fvars t1 ++ tm_fvars t2
  end.

Fixpoint ty_fvars (T : ty) : list atom :=
  match T with
  | Ty_BVar _ | Ty_Nat => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => ty_fvars A ++ ty_fvars B
  | Ty_All A => ty_fvars A
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

Lemma erase_lc_tm_at : forall K k t,
  lc_tm_at K k t -> lc_tm_at K k (erase_tm t).
Proof.
  intros K k t H. induction H; simpl.
  - constructor. assumption.
  - constructor.
  - econstructor; [constructor|assumption].
  - econstructor; eauto.
  - constructor. assumption.
  - econstructor; [assumption|constructor].
  - constructor.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma lc_ty_at_context_mono : forall K T,
  lc_ty_at K T -> forall K', K <= K' -> lc_ty_at K' T.
Proof.
  intros K T H. revert K H. induction T; intros K H K' HK.
  - inversion H; subst. constructor. lia.
  - inversion H; subst. constructor.
  - inversion H; subst. constructor; [eapply IHT1|eapply IHT2]; eauto.
  - inversion H; subst. constructor. eapply IHT; eauto; lia.
  - inversion H; subst. constructor.
Qed.

Lemma lc_tm_at_depth_mono : forall K k t,
  lc_tm_at K k t -> forall j, k <= j -> lc_tm_at K j t.
Proof.
  intros K k t H. revert K k H. induction t; intros K k H j Hj.
  - inversion H; subst. constructor. lia.
  - inversion H; subst. constructor.
  - inversion H; subst. econstructor; [assumption|].
    eapply IHt with (K := K) (k := S k); [eassumption|lia].
  - inversion H; subst. econstructor; eauto.
  - inversion H; subst. constructor. eapply IHt with (K := S K) (k := k); eauto; lia.
  - inversion H; subst. econstructor; eauto.
  - inversion H; subst. constructor.
  - inversion H; subst. econstructor; eauto.
  - inversion H; subst. econstructor; eauto.
  - inversion H; subst. econstructor; eauto.
Qed.

Lemma lc_tm_at_context_mono : forall K k t,
  lc_tm_at K k t -> forall K', K <= K' -> lc_tm_at K' k t.
Proof.
  intros K k t H. revert K k H. induction t; intros K k H K' HK.
  - inversion H; subst. constructor. lia.
  - inversion H; subst. constructor.
  - inversion H; subst. econstructor.
    + eapply lc_ty_at_context_mono; eauto; lia.
    + eapply IHt with (K := K) (k := S k); [eassumption|lia].
  - inversion H; subst. econstructor; eauto.
  - inversion H; subst. constructor. eapply IHt with (K := S K) (k := k); eauto; lia.
  - inversion H; subst. econstructor; eauto using lc_ty_at_context_mono.
  - inversion H; subst. constructor.
  - inversion H; subst. econstructor; eauto.
  - inversion H; subst. econstructor; eauto.
  - inversion H; subst. econstructor; eauto.
Qed.

Lemma lc_ty_at_open_rec : forall k T U,
  lc_ty_at (S k) T -> lc_ty_at k U ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  intros k T. revert k. induction T; intros k U HT HU; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact HU.
    + apply Nat.eqb_neq in E. inversion HT; subst. constructor. lia.
  - inversion HT; subst. constructor.
  - inversion HT; subst. constructor; [eapply IHT1|eapply IHT2]; eauto.
  - inversion HT; subst. constructor. eapply IHT with (k := S k); eauto.
    eapply lc_ty_at_context_mono; eauto; lia.
  - constructor.
Qed.

Lemma lc_tm_at_open_rec : forall K k t u,
  lc_tm_at K (S k) t -> lc_tm_at K k u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k t. revert K k. induction t; intros K k u Ht Hu; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact Hu.
    + apply Nat.eqb_neq in E. inversion Ht; subst. constructor. lia.
  - inversion Ht; subst. constructor.
  - inversion Ht; subst. econstructor.
    + assumption.
    + eapply IHt with (K := K) (k := S k).
      * eassumption.
      * eapply lc_tm_at_depth_mono; [exact Hu|lia].
  - inversion Ht; subst. econstructor; eauto.
  - inversion Ht; subst. constructor.
    eapply IHt with (K := S K) (k := k).
    + eassumption.
    + eapply lc_tm_at_context_mono; [exact Hu|lia].
  - inversion Ht; subst. econstructor; eauto.
  - constructor.
  - inversion Ht; subst. econstructor. eauto.
  - inversion Ht; subst. econstructor; eauto.
  - inversion Ht; subst. econstructor; eauto.
Qed.

Lemma lc_tm_at_open_ty_rec : forall K k t U,
  lc_tm_at (S K) k t -> lc_ty_at K U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros K k t. revert K k. induction t; intros K k U Ht HU; simpl in *.
  - inversion Ht; subst. constructor; assumption.
  - inversion Ht; subst. constructor.
  - inversion Ht; subst. econstructor.
    + eapply lc_ty_at_open_rec; [eassumption|exact HU].
    + eapply IHt; eauto.
  - inversion Ht; subst. econstructor; eauto.
  - inversion Ht; subst. constructor.
    eapply IHt with (K := S K) (k := k); [eassumption|].
    eapply lc_ty_at_context_mono; [exact HU|lia].
  - inversion Ht; subst. econstructor.
    + eapply IHt; eauto.
    + eapply lc_ty_at_open_rec; [eassumption|exact HU].
  - constructor.
  - inversion Ht; subst. econstructor. eauto.
  - inversion Ht; subst. econstructor; eauto.
  - inversion Ht; subst. econstructor; eauto.
Qed.

Definition term_env := list (atom * tm).

Fixpoint term_env_lookup (x : atom) (Sigma : term_env) : option tm :=
  match Sigma with
  | [] => None
  | (y, u) :: Sigma' =>
      if Nat.eqb x y then Some u else term_env_lookup x Sigma'
  end.

Fixpoint apply_term_env (Sigma : term_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => match term_env_lookup x Sigma with
                 | Some u => u | None => tm_fvar x end
  | tm_abs T b => tm_abs T (apply_term_env Sigma b)
  | tm_app t1 t2 => tm_app (apply_term_env Sigma t1) (apply_term_env Sigma t2)
  | tm_tabs b => tm_tabs (apply_term_env Sigma b)
  | tm_tapp t1 T => tm_tapp (apply_term_env Sigma t1) T
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (apply_term_env Sigma t1)
  | tm_natrec n b s => tm_natrec (apply_term_env Sigma n)
                         (apply_term_env Sigma b) (apply_term_env Sigma s)
  | tm_choice t1 t2 => tm_choice (apply_term_env Sigma t1) (apply_term_env Sigma t2)
  end.

Definition erase_term_env (Sigma : term_env) : term_env :=
  map (fun p => (fst p, erase_tm (snd p))) Sigma.

Lemma term_env_lookup_erase : forall x Sigma u,
  term_env_lookup x Sigma = Some u ->
  term_env_lookup x (erase_term_env Sigma) = Some (erase_tm u).
Proof.
  intros x Sigma. induction Sigma as [|[y v] Sigma IH]; intros u H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion H; subst. reflexivity.
    + eapply IH. exact H.
Qed.

Lemma term_env_lookup_none_erase : forall x Sigma,
  term_env_lookup x Sigma = None ->
  term_env_lookup x (erase_term_env Sigma) = None.
Proof.
  intros x Sigma. induction Sigma as [|[y v] Sigma IH]; intros H; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb x y) eqn:E; try discriminate.
    eapply IH. exact H.
Qed.

Lemma erase_apply_term_env : forall Sigma t,
  erase_tm (apply_term_env Sigma t) =
  apply_term_env (erase_term_env Sigma) (erase_tm t).
Proof.
  intros Sigma t. induction t; simpl; try reflexivity.
  - destruct (term_env_lookup a Sigma) as [u|] eqn:E.
    + rewrite (term_env_lookup_erase _ _ _ E). reflexivity.
    + rewrite (term_env_lookup_none_erase _ _ E). reflexivity.
  - f_equal. exact IHt.
  - f_equal; assumption.
  - f_equal. exact IHt.
  - f_equal. exact IHt.
  - f_equal. exact IHt.
  - f_equal; assumption.
  - f_equal; assumption.
Qed.

Lemma erase_open_tm : forall t u,
  erase_tm (open_tm t u) = open_tm (erase_tm t) (erase_tm u).
Proof. intros; unfold open_tm; apply erase_open_tm_rec. Qed.

Lemma erase_app_erased : forall t u,
  erase_tm (tm_app (erase_tm t) (erase_tm u)) =
  tm_app (erase_tm t) (erase_tm u).
Proof. intros; simpl; repeat rewrite erase_idempotent; reflexivity. Qed.

Lemma erase_tapp_erased : forall t,
  erase_tm (tm_tapp (erase_tm t) Ty_Nat) = tm_tapp (erase_tm t) Ty_Nat.
Proof. intros; simpl; rewrite erase_idempotent; reflexivity. Qed.

Definition term_env_domain (Sigma : term_env) : list atom := map fst Sigma.

Definition term_env_lc_at (K : nat) (Sigma : term_env) : Prop :=
  forall x u, term_env_lookup x Sigma = Some u -> lc_tm_at K 0 u.

Definition term_env_avoids (x : atom) (Sigma : term_env) : Prop :=
  forall y v, term_env_lookup y Sigma = Some v -> ~ In x (tm_fvars v).

Lemma term_env_lc_at_mono : forall Sigma K K',
  term_env_lc_at K Sigma -> K <= K' -> term_env_lc_at K' Sigma.
Proof.
  intros Sigma K K' Hlc HK x u Hlookup.
  eapply lc_tm_at_context_mono; eauto.
Qed.

Lemma tm_subst_avoids : forall x u t,
  ~ In x (tm_fvars t) -> tm_subst x u t = t.
Proof.
  intros x u t. induction t; simpl; intros Hfresh.
  - reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl; auto.
    + reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. apply in_or_app. right. exact Hin.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. left. exact Hin.
    + apply IHt3. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. right. exact Hin.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. apply in_or_app. right. exact Hin.
Qed.

Lemma tm_subst_open_tm_rec : forall x u k t,
  ~ In x (tm_fvars t) ->
  tm_subst x u (open_tm_rec k (tm_fvar x) t) = open_tm_rec k u t.
Proof.
  intros x u k t. revert k. induction t; intros k Hfresh; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + simpl. rewrite Nat.eqb_refl. reflexivity.
    + simpl. reflexivity.
  - simpl in Hfresh. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl; auto.
    + reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. apply in_or_app. auto.
    + apply IHt2. intro Hin. apply Hfresh. apply in_or_app. auto.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. apply in_or_app. left. exact Hin.
    + apply IHt2. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. left. exact Hin.
    + apply IHt3. intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. right. exact Hin.
  - f_equal.
    + apply IHt1. intro Hin. apply Hfresh. apply in_or_app. auto.
    + apply IHt2. intro Hin. apply Hfresh. apply in_or_app. auto.
Qed.

Lemma lc_open_tm_rec_identity : forall K k t u,
  lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  intros K k t. revert K k. induction t; intros K k u Hlc; simpl.
  - inversion Hlc; subst. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal. eapply IHt. eassumption.
  - inversion Hlc; subst. f_equal; eauto.
  - inversion Hlc; subst. f_equal. eapply IHt. eassumption.
  - inversion Hlc; subst. f_equal. eapply IHt. eassumption.
  - reflexivity.
  - inversion Hlc; subst. f_equal. eapply IHt. eassumption.
  - inversion Hlc; subst. f_equal; eauto.
  - inversion Hlc; subst. f_equal; eauto.
Qed.

Lemma term_env_lookup_head_same : forall x u Sigma,
  term_env_lookup x ((x,u)::Sigma) = Some u.
Proof. intros; simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma term_env_lookup_head_other : forall x y u Sigma,
  x <> y -> term_env_lookup y ((x,u)::Sigma) = term_env_lookup y Sigma.
Proof.
  intros x y u Sigma Hxy. simpl. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. congruence.
  - reflexivity.
Qed.

Lemma term_env_lookup_none_domain : forall x Sigma,
  ~ In x (term_env_domain Sigma) -> term_env_lookup x Sigma = None.
Proof.
  intros x Sigma. induction Sigma as [|[y v] Sigma IH]; simpl; intros Hfresh.
  - reflexivity.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl; auto.
    + apply IH. intro Hin. apply Hfresh. simpl. right. exact Hin.
Qed.

Lemma apply_term_env_open_rec : forall Sigma x u k t,
  ~ In x (term_env_domain Sigma) -> term_env_avoids x Sigma ->
  term_env_lc_at 0 Sigma ->
  apply_term_env ((x,u)::Sigma) (open_tm_rec k (tm_fvar x) t) =
  tm_subst x u (open_tm_rec k (tm_fvar x) (apply_term_env Sigma t)).
Proof.
  intros Sigma x u k t. revert k. induction t; intros k Hfresh Havoid Hlc; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + unfold apply_term_env at 1. rewrite term_env_lookup_head_same. simpl.
      rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst a.
      rewrite (term_env_lookup_none_domain x Sigma Hfresh). simpl.
      rewrite Nat.eqb_refl. reflexivity.
    + apply Nat.eqb_neq in E.
      assert (E' : Nat.eqb a x = false) by (apply Nat.eqb_neq; congruence).
      rewrite E'.
      destruct (term_env_lookup a Sigma) as [v|] eqn:Ev; simpl.
      * rewrite (lc_open_tm_rec_identity 0 k v (tm_fvar x)).
        -- rewrite (tm_subst_avoids x u v).
           ++ reflexivity.
           ++ eapply Havoid. exact Ev.
        -- eapply lc_tm_at_depth_mono.
           ++ eapply Hlc. exact Ev.
           ++ lia.
      * simpl. assert (E'' : Nat.eqb x a = false) by (apply Nat.eqb_neq; exact E).
        rewrite E''. reflexivity.
  - f_equal. eapply IHt; eauto.
  - f_equal; [eapply IHt1|eapply IHt2]; eauto.
  - f_equal. eapply IHt; eauto.
  - f_equal. eapply IHt; eauto.
  - reflexivity.
  - f_equal. eapply IHt; eauto.
  - f_equal; [eapply IHt1|eapply IHt2|eapply IHt3]; eauto.
  - f_equal; [eapply IHt1|eapply IHt2]; eauto.
Qed.

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

(* Strong normalization is closed under taking a reduct. *)
Lemma SN_step : forall t u, strongly_normalizing t -> t --> u -> strongly_normalizing u.
Proof.
  intros t u H. inversion H; subst. auto.
Qed.

(* A useful view of the coinductive-looking definition above: all immediate
   reducts of an SN term are SN. *)
Lemma SN_children : forall t, strongly_normalizing t ->
  forall u, t --> u -> strongly_normalizing u.
Proof. intros; eapply SN_step; eauto. Qed.

Lemma numeric_value_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof.
  intros n Hn. induction Hn; simpl; constructor; assumption.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v Hv. inversion Hv; subst; auto using numeric_value_lc.
Qed.

Lemma numeric_value_erase : forall n, numeric_value n -> numeric_value (erase_tm n).
Proof. intros n Hn. induction Hn; simpl; constructor; assumption. Qed.

Lemma value_erase : forall v, value v -> value (erase_tm v).
Proof.
  intros v Hv. inversion Hv; subst.
  - apply v_abs. change (locally_closed_tm (erase_tm (tm_abs T t))).
    apply erase_lc_tm_at. assumption.
  - apply v_tabs. change (locally_closed_tm (erase_tm (tm_tabs t))).
    apply erase_lc_tm_at. assumption.
  - simpl. apply v_nat. eapply numeric_value_erase; eauto.
Qed.

Lemma open_tm_ty_rec_erase_identity : forall k t,
  open_tm_ty_rec k Ty_Nat (erase_tm t) = erase_tm t.
Proof.
  intros k t. revert k. induction t; intros k; simpl; try reflexivity;
    f_equal; eauto.
Qed.

Lemma open_tm_ty_erase_identity : forall t,
  open_tm_ty (erase_tm t) Ty_Nat = erase_tm t.
Proof. intros; apply open_tm_ty_rec_erase_identity. Qed.

Lemma erase_step : forall t u, t --> u -> erase_tm t --> erase_tm u.
Proof.
  intros t u Hstep. induction Hstep; cbn [erase_tm].
  - unfold open_tm. rewrite erase_open_tm_rec. apply ST_AppAbs.
    + change (locally_closed_tm (erase_tm (tm_abs T t))).
      apply erase_lc_tm_at. assumption.
    + apply value_erase. assumption.
  - eapply ST_App1.
    + exact IHHstep.
    + change (locally_closed_tm (erase_tm t2)). apply erase_lc_tm_at. assumption.
  - apply ST_App2; eauto using value_erase.
  - rewrite erase_open_tm_ty.
    replace (erase_tm t) with (open_tm_ty (erase_tm t) Ty_Nat) at 2
      by apply open_tm_ty_erase_identity.
    apply ST_TAppTabs.
    + change (locally_closed_tm (erase_tm (tm_tabs t))).
      apply erase_lc_tm_at. assumption.
    + constructor.
  - apply ST_TApp; [assumption|constructor].
  - apply ST_Succ. assumption.
  - eapply ST_RecArg.
    + exact IHHstep.
    + change (locally_closed_tm (erase_tm b)); apply erase_lc_tm_at; assumption.
    + change (locally_closed_tm (erase_tm s)); apply erase_lc_tm_at; assumption.
  - eapply ST_RecBase.
    + apply numeric_value_erase. assumption.
    + exact IHHstep.
    + change (locally_closed_tm (erase_tm s)); apply erase_lc_tm_at; assumption.
  - eapply ST_RecStep.
    + apply numeric_value_erase. assumption.
    + apply value_erase. assumption.
    + exact IHHstep.
  - apply ST_RecZero; apply value_erase; assumption.
  - apply ST_RecSucc.
    + apply numeric_value_erase. assumption.
    + apply value_erase. assumption.
    + apply value_erase. assumption.
  - apply ST_ChoiceLeft.
    + change (locally_closed_tm (erase_tm t1)); apply erase_lc_tm_at; assumption.
    + change (locally_closed_tm (erase_tm t2)); apply erase_lc_tm_at; assumption.
  - apply ST_ChoiceRight.
    + change (locally_closed_tm (erase_tm t1)); apply erase_lc_tm_at; assumption.
    + change (locally_closed_tm (erase_tm t2)); apply erase_lc_tm_at; assumption.
Qed.

Lemma SN_erase_to_SN : forall t,
  strongly_normalizing (erase_tm t) -> strongly_normalizing t.
Proof.
  assert (Hgen : forall e, strongly_normalizing e ->
      forall t, erase_tm t = e -> strongly_normalizing t).
  { intros e Hsn. induction Hsn as [e Hnext IH]. intros t He.
    apply SN_intro. intros u Hu. eapply IH.
    - rewrite <- He. apply erase_step. exact Hu.
    - reflexivity.
  }
  intros t Hsn. eapply Hgen; eauto.
Qed.

Lemma step_lc : forall t u, locally_closed_tm t -> t --> u -> locally_closed_tm u.
Proof.
  intros t u Hlc Hstep. induction Hstep; inversion Hlc; subst.
  - match goal with
    | Hab : locally_closed_tm (tm_abs ?A ?body), Hv : value ?v |- _ =>
        unfold locally_closed_tm, open_tm; inversion Hab; subst;
        eapply lc_tm_at_open_rec; [eassumption|apply value_lc; exact Hv]
    end.
  - econstructor; [apply IHHstep; assumption|assumption].
  - econstructor; [apply value_lc; assumption|apply IHHstep; assumption].
  - match goal with
    | Hab : locally_closed_tm (tm_tabs ?body), HT : locally_closed_ty ?T |- _ =>
        unfold locally_closed_tm, locally_closed_ty, open_tm_ty;
        inversion Hab; subst; eapply lc_tm_at_open_ty_rec; [eassumption|exact HT]
    end.
  - econstructor; [apply IHHstep; assumption|assumption].
  - econstructor; [apply IHHstep; assumption].
  - econstructor; [apply IHHstep; assumption|assumption|assumption].
  - econstructor; [apply numeric_value_lc; assumption|apply IHHstep; assumption|assumption].
  - econstructor; [apply numeric_value_lc; assumption|apply value_lc; assumption|apply IHHstep; assumption].
  - apply value_lc. assumption.
  - unfold locally_closed_tm. eapply lc_tm_app.
    + eapply lc_tm_app.
      * apply value_lc. assumption.
      * apply numeric_value_lc. assumption.
    + econstructor.
      * apply numeric_value_lc. assumption.
      * apply value_lc. assumption.
      * apply value_lc. assumption.
  - assumption.
  - assumption.
Qed.

Definition neutral (t : tm) : Prop := locally_closed_tm t /\ ~ value t.

Lemma neutral_lc : forall t, neutral t -> locally_closed_tm t.
Proof. intros t [Hlc _]. exact Hlc. Qed.

Lemma neutral_not_value : forall t, neutral t -> ~ value t.
Proof. intros t [_ Hnv]. exact Hnv. Qed.

Lemma neutral_app : forall t u,
  ~ value t -> locally_closed_tm t -> locally_closed_tm u ->
  neutral (tm_app t u).
Proof.
  intros t u Hnv Ht Hu. split.
  - unfold locally_closed_tm. econstructor; eauto.
  - intro Hv. inversion Hv; subst; try discriminate.
    match goal with Hnum : numeric_value (tm_app _ _) |- _ => inversion Hnum end.
Qed.

Lemma neutral_tapp : forall t T,
  (forall body, t <> tm_tabs body) ->
  locally_closed_tm t -> locally_closed_ty T -> neutral (tm_tapp t T).
Proof.
  intros t T Hneq Ht HT. split.
  - unfold locally_closed_tm. econstructor; eauto.
  - intro Hv. inversion Hv; subst; try discriminate.
    match goal with Hnum : numeric_value (tm_tapp _ _) |- _ => inversion Hnum end.
Qed.

Lemma value_no_step : forall v, value v -> forall u, ~ (v --> u).
Proof.
  intros v Hv u Hu. inversion Hv; subst.
  - inversion Hu.
  - inversion Hu.
  - clear Hv. revert u Hu. induction H; intros u Hu.
    + inversion Hu.
    + inversion Hu; subst. eapply IHnumeric_value. eassumption.
Qed.

(* Reducibility candidates are predicates on terms.  The three clauses below
   are the closure facts used by the type-indexed interpretation. *)
Definition candidate (P : tm -> Prop) : Prop :=
  (forall t, P t -> strongly_normalizing (erase_tm t)) /\
  (forall t, P t -> locally_closed_tm (erase_tm t)) /\
  (forall t u, P t -> t --> u -> P u) /\
  (forall t, neutral (erase_tm t) ->
     (forall u, erase_tm t --> u -> P (erase_tm u)) -> P (erase_tm t)).

Definition sn_lc (t : tm) : Prop :=
  strongly_normalizing (erase_tm t) /\ locally_closed_tm (erase_tm t).

Lemma SN_candidate : candidate sn_lc.
Proof.
  unfold candidate. split.
  - intros t [HS _]. exact HS.
  - split.
    + intros t [_ Hlc]. exact Hlc.
    + split.
      * intros t u [HS Hlc] Hu. split.
        -- eapply SN_step; [exact HS|apply erase_step; exact Hu].
        -- eapply step_lc; [exact Hlc|apply erase_step; exact Hu].
      * intros t Hn Hred. split.
        -- apply SN_intro. intros u Hu. rewrite erase_idempotent in Hu.
           pose proof (proj1 (Hred u Hu)) as HS.
           rewrite erase_idempotent in HS. eapply SN_erase_to_SN. exact HS.
        -- rewrite erase_idempotent. apply neutral_lc. exact Hn.
Qed.

Lemma candidate_erase : forall P, candidate P -> candidate (fun t => P (erase_tm t)).
Proof.
  intros P [Hsn [Hlc [Hstep Hneutral]]]. unfold candidate. split.
  - intros t HP. pose proof (Hsn (erase_tm t) HP) as HS.
    rewrite erase_idempotent in HS. exact HS.
  - split.
    + intros t HP. pose proof (Hlc (erase_tm t) HP) as HL.
      rewrite erase_idempotent in HL. exact HL.
    + split.
      * intros t u HP Htu. apply Hstep with (t := erase_tm t).
        -- exact HP.
        -- apply erase_step. exact Htu.
      * intros t Hn Hred.
        rewrite erase_idempotent.
        apply Hneutral.
        -- exact Hn.
        -- intros u Hu. specialize (Hred u Hu).
           rewrite erase_idempotent in Hred. exact Hred.
Qed.

(* The Nat interpretation will be the least candidate containing numerals;
   this helper records that numeric values themselves are SN. *)
Lemma numeric_value_no_step : forall n, numeric_value n ->
  forall u, ~ (n --> u).
Proof.
  intros n Hn. induction Hn; intros u Hu.
  - inversion Hu.
  - inversion Hu; subst. eapply IHHn. eassumption.
Qed.

Lemma numeric_value_SN : forall n, numeric_value n -> strongly_normalizing n.
Proof.
  intros n Hn. apply SN_intro. intros u Hu.
  exfalso. eapply numeric_value_no_step; eauto.
Qed.

Lemma SN_succ : forall t, strongly_normalizing t -> strongly_normalizing (tm_succ t).
Proof.
  intros t Hsn. induction Hsn as [t Hnext IH]. apply SN_intro. intros u Hu.
  inversion Hu; subst. eapply IH; eassumption.
Qed.

Lemma SN_choice : forall t1 t2,
  strongly_normalizing t1 -> strongly_normalizing t2 ->
  strongly_normalizing (tm_choice t1 t2).
Proof.
  intros t1 t2 H1 H2. apply SN_intro. intros u Hu. inversion Hu; subst; assumption.
Qed.

Lemma SN_abs : forall T t, strongly_normalizing (tm_abs T t).
Proof. intros. apply SN_intro. intros u Hu. inversion Hu. Qed.

Lemma SN_tabs : forall t, strongly_normalizing (tm_tabs t).
Proof. intros. apply SN_intro. intros u Hu. inversion Hu. Qed.

Definition ty_candidate_env := list (atom * (tm -> Prop)).

Fixpoint candidate_lookup (X : atom) (Xi : ty_candidate_env) : option (tm -> Prop) :=
  match Xi with
  | [] => None
  | (Y, P) :: Xi' => if Nat.eqb X Y then Some P else candidate_lookup X Xi'
  end.

(* Interpretation of types relative to candidates for free and bound type
   variables.  Universal types are interpreted through type application, so
   the All clause follows the supplied type-beta rule. *)
Fixpoint ty_interp (Xi : ty_candidate_env) (Rho : list (tm -> Prop))
    (T : ty) : tm -> Prop :=
  match T with
  | Ty_BVar i => match nth_error Rho i with Some P => fun t => P (erase_tm t) | None => sn_lc end
  | Ty_FVar X => match candidate_lookup X Xi with Some P => fun t => P (erase_tm t) | None => sn_lc end
  | Ty_Arrow A B => fun t =>
      sn_lc t /\
      (forall u, ty_interp Xi Rho A u ->
         ty_interp Xi Rho B (tm_app (erase_tm t) (erase_tm u)))
  | Ty_All A => fun t =>
      sn_lc t /\
      (forall X P, ~ In X (map fst Xi) -> ~ In X (ty_fvars A) -> candidate P ->
         ty_interp ((X, P) :: Xi) (P :: Rho) A
           (tm_tapp (erase_tm t) Ty_Nat))
  | Ty_Nat => sn_lc
  end.

(* At the term level the interpretation is pointwise in a substitution
   environment; this is the statement used in the fundamental lemma. *)
Definition candidate_env_ok (Xi : ty_candidate_env) (Rho : list (tm -> Prop)) : Prop :=
  (forall X P, candidate_lookup X Xi = Some P -> candidate P) /\
  (forall P, In P Rho -> candidate P).

Lemma candidate_env_ok_extend_bound : forall Xi Rho P,
  candidate_env_ok Xi Rho -> candidate P -> candidate_env_ok Xi (P :: Rho).
Proof.
  intros Xi Rho P [HXi HRho] HP. split; [exact HXi|].
  intros Q HQ. simpl in HQ. destruct HQ as [Heq|HQ].
  - subst Q. exact HP.
  - apply HRho. exact HQ.
Qed.

Lemma candidate_env_ok_extend_free : forall Xi Rho X P,
  candidate_env_ok Xi Rho -> candidate P ->
  candidate_env_ok ((X, P) :: Xi) Rho.
Proof.
  intros Xi Rho X P [HXi HRho] HP. split.
  - intros Y Q HY. simpl in HY.
    destruct (Nat.eqb Y X) eqn:E.
    + inversion HY; subst. exact HP.
    + eapply HXi. exact HY.
  - exact HRho.
Qed.

Lemma ty_interp_lc : forall T Xi Rho,
  candidate_env_ok Xi Rho -> forall t,
  ty_interp Xi Rho T t -> locally_closed_tm (erase_tm t).
Proof.
  induction T; intros Xi Rho Hok t Hrel; simpl in Hrel.
  - destruct (nth_error Rho n) as [P|] eqn:E.
    + destruct Hok as [_ HRho].
      pose proof (candidate_erase P (HRho P (nth_error_In _ _ E))) as HP.
      destruct HP as [_ [Hlc _]]. apply Hlc. exact Hrel.
    + exact (proj2 Hrel).
  - destruct (candidate_lookup a Xi) as [P|] eqn:E.
    + destruct Hok as [HXi _].
      pose proof (candidate_erase P (HXi a P E)) as HP.
      destruct HP as [_ [Hlc _]]. apply Hlc. exact Hrel.
    + exact (proj2 Hrel).
  - destruct Hrel as [[_ Hlc] _]. exact Hlc.
  - destruct Hrel as [[_ Hlc] _]. exact Hlc.
  - destruct Hrel as [_ Hlc]. exact Hlc.
Qed.

Lemma neutral_not_tabs : forall t, neutral t ->
  forall body, t <> tm_tabs body.
Proof.
  intros t [Hlc Hnv] body E. subst. apply Hnv. constructor. exact Hlc.
Qed.

Lemma ty_interp_candidate : forall T Xi Rho,
  candidate_env_ok Xi Rho -> candidate (ty_interp Xi Rho T).
Proof.
  induction T; intros Xi Rho Hok; simpl.
  - destruct (nth_error Rho n) as [P|] eqn:E.
    + destruct Hok as [_ HRho]. specialize (HRho P (nth_error_In _ _ E)).
      apply candidate_erase. exact HRho.
    + exact SN_candidate.
  - destruct (candidate_lookup a Xi) as [P|] eqn:E.
    + destruct Hok as [HXi _]. apply candidate_erase. exact (HXi a P E).
    + exact SN_candidate.
  - pose proof (IHT2 Xi Rho Hok) as CB. unfold candidate in CB.
    destruct CB as [CBsn [CBlc [CBstep CBneutral]]].
    unfold candidate. split.
    + intros t [[HS _] _]. exact HS.
    + split.
      * intros t [[_ Hlc] _]. exact Hlc.
      * split.
        -- intros t t' [[HS Hlc] HF] Hstep.
           split.
           ++ unfold sn_lc. split.
              ** eapply SN_step; [exact HS|apply erase_step; exact Hstep].
              ** eapply step_lc; [exact Hlc|apply erase_step; exact Hstep].
           ++ intros u Hu.
              apply CBstep with (t := tm_app (erase_tm t) (erase_tm u))
                (u := tm_app (erase_tm t') (erase_tm u)).
              ** apply HF. exact Hu.
              ** apply ST_App1; [apply erase_step; exact Hstep|].
                 eapply ty_interp_lc; eauto.
        -- intros t Hneutral Hred.
           split.
           ++ unfold sn_lc. split.
              ** apply SN_intro. intros t' Hstep.
                 rewrite erase_idempotent in Hstep.
                 pose proof (Hred t' Hstep) as Hchild.
                 destruct Hchild as [[HS _] _].
                 rewrite erase_idempotent in HS. eapply SN_erase_to_SN. exact HS.
              ** rewrite erase_idempotent. apply neutral_lc. exact Hneutral.
           ++ intros u Hu.
              rewrite <- erase_app_erased.
              apply CBneutral.
              ** repeat rewrite erase_idempotent. apply neutral_app.
                 --- apply neutral_not_value. rewrite erase_idempotent. exact Hneutral.
                 --- apply neutral_lc. rewrite erase_idempotent. exact Hneutral.
                 --- rewrite erase_idempotent. eapply ty_interp_lc; eauto.
              ** intros r Hr. inversion Hr; subst.
                 --- repeat rewrite erase_idempotent in H.
                     exfalso. apply (neutral_not_value (erase_tm t) Hneutral).
                     rewrite <- H. constructor. exact H1.
                 --- assert (Hstep' : erase_tm t --> t1') by
                       (rewrite <- (erase_idempotent3 t); exact H1).
                     destruct (Hred t1' Hstep') as [_ HF'].
                     pose proof (HF' u Hu) as Hres.
                     replace (erase_tm (erase_tm t1')) with (erase_tm t1') in Hres
                       by (symmetry; apply erase_idempotent).
                     simpl. repeat rewrite erase_idempotent. exact Hres.
                 --- assert (Hv : value (erase_tm t)) by
                       (rewrite <- erase_idempotent3; exact H1).
                     exfalso. exact (neutral_not_value (erase_tm t) Hneutral Hv).
  - pose proof (IHT Xi Rho Hok) as CA. unfold candidate in CA.
    destruct CA as [CAsn [CAlc [CAstep CAneutral]]].
    unfold candidate. split.
    + intros t [[HS _] _]. exact HS.
    + split.
      * intros t [[_ Hlc] _]. exact Hlc.
      * split.
        -- intros t t' [[HS Hlc] Hall] Hstep.
           split.
           ++ unfold sn_lc. split.
              ** eapply SN_step; [exact HS|apply erase_step; exact Hstep].
              ** eapply step_lc; [exact Hlc|apply erase_step; exact Hstep].
           ++ intros X P HfreshXi HfreshT HP.
              pose proof (candidate_env_ok_extend_free Xi Rho X P Hok HP) as Hok'.
              pose proof (candidate_env_ok_extend_bound ((X,P)::Xi) Rho P Hok' HP) as Hok''.
              pose proof (IHT ((X,P)::Xi) (P::Rho) Hok'') as CB.
              unfold candidate in CB. destruct CB as [_ [_ [CBstep _]]].
              apply CBstep with (t := tm_tapp (erase_tm t) Ty_Nat)
                (u := tm_tapp (erase_tm t') Ty_Nat).
              ** apply Hall; assumption.
              ** apply ST_TApp; [apply erase_step; exact Hstep|constructor].
        -- intros t Hneutral Hred.
           split.
           ++ unfold sn_lc. split.
              ** apply SN_intro. intros t' Hstep.
                 replace (erase_tm (erase_tm t)) with (erase_tm t) in Hstep
                   by (symmetry; apply erase_idempotent).
                 destruct (Hred t' Hstep) as [[HS _] _].
                 rewrite erase_idempotent in HS. eapply SN_erase_to_SN. exact HS.
              ** rewrite erase_idempotent. apply neutral_lc. exact Hneutral.
           ++ intros X P HfreshXi HfreshT HP.
              pose proof (candidate_env_ok_extend_free Xi Rho X P Hok HP) as Hok'.
              pose proof (candidate_env_ok_extend_bound ((X,P)::Xi) Rho P Hok' HP) as Hok''.
              pose proof (IHT ((X,P)::Xi) (P::Rho) Hok'') as CB.
              unfold candidate in CB. destruct CB as [_ [_ [_ CBneutral]]].
              rewrite <- erase_tapp_erased.
              apply CBneutral.
              ** repeat rewrite erase_idempotent. apply neutral_tapp.
                 --- apply neutral_not_tabs. rewrite erase_idempotent. exact Hneutral.
                 --- rewrite erase_idempotent. apply neutral_lc. exact Hneutral.
                 --- constructor.
              ** intros r Hr. inversion Hr; subst.
                 --- repeat rewrite erase_idempotent in H.
                     exfalso. apply (neutral_not_value (erase_tm t) Hneutral).
                     rewrite <- H. constructor. exact H1.
                 --- assert (Hs' : erase_tm t --> t') by
                       (rewrite <- (erase_idempotent3 t); exact H1).
                     destruct (Hred t' Hs') as [_ Hall'].
                     specialize (Hall' X P HfreshXi HfreshT HP).
                     simpl.
                     replace (erase_tm (erase_tm t')) with (erase_tm t') in Hall'
                       by (symmetry; apply erase_idempotent).
                     exact Hall'.
  - exact SN_candidate.
Qed.

Definition term_interp_env_ok (Gamma : context) (Xi : ty_candidate_env)
    (Rho : list (tm -> Prop)) (Sigma : term_env) : Prop :=
  term_env_lc_at 0 Sigma /\
  (forall x T, lookup_context x Gamma = Some T ->
     ty_interp Xi Rho T (erase_tm (apply_term_env Sigma (tm_fvar x)))).

Lemma lookup_context_head_same : forall x T Gamma,
  lookup_context x (update Gamma x T) = Some T.
Proof. intros; simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma lookup_context_head_other : forall x y T Gamma,
  x <> y -> lookup_context y (update Gamma x T) = lookup_context y Gamma.
Proof.
  intros x y T Gamma Hxy. simpl. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. congruence.
  - reflexivity.
Qed.

Lemma term_interp_env_extend : forall Gamma Xi Rho Sigma x T u,
  candidate_env_ok Xi Rho ->
  term_interp_env_ok Gamma Xi Rho Sigma ->
  ty_interp Xi Rho T u ->
  erase_tm u = u ->
  ~ In x (term_env_domain Sigma) ->
  term_interp_env_ok (update Gamma x T) Xi Rho ((x,u)::Sigma).
Proof.
  intros Gamma Xi Rho Sigma x T u Hok [Hlc Htyped] Hu Hcanon Hfresh. split.
  - intros y v Hlookup.
    destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. subst y. rewrite term_env_lookup_head_same in Hlookup.
      inversion Hlookup; subst.
      pose proof (ty_interp_lc T Xi Rho Hok v Hu) as Hlu.
      rewrite Hcanon in Hlu. exact Hlu.
    + apply Nat.eqb_neq in E. rewrite term_env_lookup_head_other in Hlookup by congruence.
      eapply Hlc. exact Hlookup.
  - intros y U Hlookup. destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. subst y. rewrite lookup_context_head_same in Hlookup.
      inversion Hlookup; subst U. simpl. rewrite Nat.eqb_refl. rewrite Hcanon. exact Hu.
    + assert (Hneq : y <> x) by (apply Nat.eqb_neq; exact E).
      rewrite lookup_context_head_other in Hlookup by congruence.
      simpl. rewrite E. eapply Htyped; eauto.
Qed.

Lemma ty_interp_sound : forall T Xi Rho,
  candidate_env_ok Xi Rho -> forall t,
  ty_interp Xi Rho T t -> strongly_normalizing t.
Proof.
  induction T; intros Xi Rho Hok t Hrel; simpl in Hrel.
  - destruct (nth_error Rho n) as [P|] eqn:E.
    + destruct Hok as [HXi HRho].
      pose proof (candidate_erase P (HRho P (nth_error_In _ _ E))) as HP.
      destruct HP as [Hsn _].
      eapply SN_erase_to_SN. apply Hsn. exact Hrel.
    + eapply SN_erase_to_SN. exact (proj1 Hrel).
  - destruct (candidate_lookup a Xi) as [P|] eqn:E.
    + destruct Hok as [HXi HRho].
      pose proof (candidate_erase P (HXi a P E)) as HP. destruct HP as [Hsn _].
      eapply SN_erase_to_SN. apply Hsn. exact Hrel.
    + eapply SN_erase_to_SN. exact (proj1 Hrel).
  - destruct Hrel as [[HS _] _]. eapply SN_erase_to_SN. exact HS.
  - destruct Hrel as [[HS _] _]. eapply SN_erase_to_SN. exact HS.
  - destruct Hrel as [HS _]. eapply SN_erase_to_SN. exact HS.
Qed.


Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End SystemFNormalizationNondeterminismRecursionHardTask.
