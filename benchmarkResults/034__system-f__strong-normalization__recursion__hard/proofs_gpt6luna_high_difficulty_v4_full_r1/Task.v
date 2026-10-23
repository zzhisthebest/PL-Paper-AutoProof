(** System F CBV strong-normalization benchmark, Hard variant.
    Features: recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia FunctionalExtensionality PropExtensionality.
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

Definition candidate := tm -> Prop.

Definition nat_candidate (t : tm) : Prop :=
  strongly_normalizing t /\
  forall v, t -->* v -> value v -> numeric_value v.

Definition cand_closed (P : candidate) : Prop :=
  (forall t, P t -> strongly_normalizing t) /\
  (forall t u, P t -> t --> u -> P u) /\
  (forall t, ~ value t -> strongly_normalizing t ->
    (forall u, t --> u -> P u) -> P t).

Definition sem_ty_env := list candidate.
Definition sem_free_ty_env := atom -> candidate.
Definition xi_update (xi : sem_free_ty_env) (X : atom) (P : candidate) : sem_free_ty_env :=
  fun Y => if Nat.eqb Y X then P else xi Y.

Fixpoint ty_fv (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => ty_fv A ++ ty_fv B
  | Ty_All A => ty_fv A
  | Ty_Nat => []
  end.

Fixpoint insert_candidate (k : nat) (P : candidate) (rho : sem_ty_env) : sem_ty_env :=
  match k, rho with
  | 0, _ => P :: rho
  | S k', Q :: rho' => Q :: insert_candidate k' P rho'
  | S _, [] => []
  end.

Fixpoint interp (rho : sem_ty_env) (xi : sem_free_ty_env) (T : ty) : candidate :=
  match T with
  | Ty_BVar i => nth i rho strongly_normalizing
  | Ty_FVar X => xi X
  | Ty_Arrow A B => fun t =>
      strongly_normalizing t /\
      forall v, t -->* v -> value v -> forall T b,
        v = tm_abs T b -> forall u, locally_closed_tm u ->
        interp rho xi A u -> interp rho xi B (open_tm b u)
  | Ty_All A => fun t =>
      strongly_normalizing t /\
      forall v, t -->* v -> value v -> forall b,
        v = tm_tabs b -> forall U, locally_closed_ty U -> forall P, cand_closed P ->
        interp (P :: rho) xi A (open_tm_ty b U)
  | Ty_Nat => nat_candidate
  end.

Lemma nth_app_prefix : forall (pre r : sem_ty_env) n d,
  n < length pre -> nth n (pre ++ r) d = nth n pre d.
Proof.
  induction pre as [|P pre IH]; intros r n d H.
  - simpl in H. lia.
  - destruct n; simpl; [reflexivity|]. apply IH. simpl in H. lia.
Qed.

Lemma interp_env_irrel_at : forall k T,
  lc_ty_at k T -> forall pre rho1 rho2 xi t,
    length pre = k ->
    (interp (pre ++ rho1) xi T t <-> interp (pre ++ rho2) xi T t).
Proof.
  intros k T. revert k. induction T; intros k Hlc pre rho1 rho2 xi t Hlen; simpl in *.
  - inversion Hlc as [K i Hi| | | |]; subst.
    rewrite (nth_app_prefix pre rho1 n strongly_normalizing ltac:(lia)),
      (nth_app_prefix pre rho2 n strongly_normalizing ltac:(lia)).
    reflexivity.
  - tauto.
  - inversion Hlc as [| |K A B HA HB| |].
    split.
    + intros [Hs Hrel]. split; [exact Hs|].
      intros v Hpath Hv U b Heq u HuL Hu.
      apply (proj1 (IHT2 k HB pre rho1 rho2 xi (open_tm b u) Hlen)).
      eapply Hrel; [exact Hpath|exact Hv|exact Heq|exact HuL|].
      apply (proj2 (IHT1 k HA pre rho1 rho2 xi u Hlen)). exact Hu.
    + intros [Hs Hrel]. split; [exact Hs|].
      intros v Hpath Hv U b Heq u HuL Hu.
      apply (proj2 (IHT2 k HB pre rho1 rho2 xi (open_tm b u) Hlen)).
      eapply Hrel; [exact Hpath|exact Hv|exact Heq|exact HuL|].
      apply (proj1 (IHT1 k HA pre rho1 rho2 xi u Hlen)). exact Hu.
  - inversion Hlc as [| | |K A HA|].
    split.
    + intros [Hs Hrel]. split; [exact Hs|].
      intros v Hpath Hv b Heq U HU P HP.
      change (interp (P :: pre ++ rho2) xi T (open_tm_ty b U)).
      apply (proj1 (IHT (S k) HA (P :: pre) rho1 rho2 xi
        (open_tm_ty b U) ltac:(simpl; lia))).
      eapply Hrel; eauto.
    + intros [Hs Hrel]. split; [exact Hs|].
      intros v Hpath Hv b Heq U HU P HP.
      change (interp (P :: pre ++ rho1) xi T (open_tm_ty b U)).
      apply (proj2 (IHT (S k) HA (P :: pre) rho1 rho2 xi
        (open_tm_ty b U) ltac:(simpl; lia))).
      eapply Hrel; eauto.
  - tauto.
Qed.

Lemma interp_env_irrel : forall T,
  locally_closed_ty T -> forall rho1 rho2 xi t,
    interp rho1 xi T t <-> interp rho2 xi T t.
Proof.
  intros T Hlc rho1 rho2 xi t.
  unfold locally_closed_ty in Hlc.
  replace rho1 with ([] ++ rho1) by reflexivity.
  replace rho2 with ([] ++ rho2) by reflexivity.
  eapply interp_env_irrel_at; eauto.
Qed.

Lemma interp_ty_subst_sem : forall T rho xi X U P t,
  locally_closed_ty U -> P = interp rho xi U ->
  (interp rho (xi_update xi X P) T t <->
   interp rho xi (ty_subst X U T) t).
Proof.
  induction T; intros rho xi X U P t HU HPeq; simpl.
  - tauto.
  - unfold xi_update, ty_subst.
    destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst a. simpl. rewrite Nat.eqb_refl.
      rewrite HPeq. reflexivity.
    + assert (E' : Nat.eqb a X = false).
      { apply Nat.eqb_neq. apply Nat.eqb_neq in E. congruence. }
      simpl. rewrite E'. reflexivity.
  - split.
    + intros [Hs Hrel]. split; [exact Hs|].
      intros v Hpath Hv A b Heq u HuL Hu.
      apply (proj1 (IHT2 rho xi X U P (open_tm b u) HU HPeq)).
      eapply Hrel; [exact Hpath|exact Hv|exact Heq|exact HuL|].
      apply (proj2 (IHT1 rho xi X U P u HU HPeq)). exact Hu.
    + intros [Hs Hrel]. split; [exact Hs|].
      intros v Hpath Hv A b Heq u HuL Hu.
      apply (proj2 (IHT2 rho xi X U P (open_tm b u) HU HPeq)).
      eapply Hrel; [exact Hpath|exact Hv|exact Heq|exact HuL|].
      apply (proj1 (IHT1 rho xi X U P u HU HPeq)). exact Hu.
  - split.
    + intros [Hs Hrel]. split; [exact Hs|].
      intros v Hpath Hv b Heq V HV Q HQ.
      assert (HPeq' : P = interp (Q :: rho) xi U).
      { rewrite HPeq. apply functional_extensionality. intro z.
        apply propositional_extensionality.
        apply interp_env_irrel; exact HU. }
      apply (proj1 (IHT (Q :: rho) xi X U P (open_tm_ty b V) HU HPeq')).
      eapply Hrel; eauto.
    + intros [Hs Hrel]. split; [exact Hs|].
      intros v Hpath Hv b Heq V HV Q HQ.
      assert (HPeq' : P = interp (Q :: rho) xi U).
      { rewrite HPeq. apply functional_extensionality. intro z.
        apply propositional_extensionality.
        apply interp_env_irrel; exact HU. }
      apply (proj2 (IHT (Q :: rho) xi X U P (open_tm_ty b V) HU HPeq')).
      eapply Hrel; eauto.
  - tauto.
Qed.

Lemma nth_insert_candidate_lt : forall k P rho i,
  i < k -> k <= length rho ->
  nth i (insert_candidate k P rho) strongly_normalizing = nth i rho strongly_normalizing.
Proof.
  induction k as [|k IH]; intros P rho i Hi Hlen; [lia|].
  destruct rho as [|Q rho']; [simpl in Hlen; lia|].
  destruct i as [|i]; simpl.
  - reflexivity.
  - apply IH; simpl in *; lia.
Qed.

Lemma nth_insert_candidate_eq : forall k P rho,
  k <= length rho ->
  nth k (insert_candidate k P rho) strongly_normalizing = P.
Proof.
  induction k as [|k IH]; intros P rho Hlen; simpl.
  - reflexivity.
  - destruct rho as [|Q rho']; [simpl in Hlen; lia|].
    simpl. f_equal. apply IH. simpl in Hlen. lia.
Qed.

Lemma insert_candidate_succ : forall k P rho Q,
  insert_candidate (S k) P (Q :: rho) = Q :: insert_candidate k P rho.
Proof. reflexivity. Qed.

Lemma interp_open_ty_sem_rec : forall T k rho xi U P t,
  lc_ty_at (S k) T -> k <= length rho ->
  P = interp rho xi U -> locally_closed_ty U ->
  (interp (insert_candidate k P rho) xi T t <->
   interp rho xi (open_ty_rec k U T) t).
Proof.
  intros T. induction T; intros k rho xi U P t Hlc Hlen HPeq HU; simpl in *.
  - inversion Hlc as [K i Hi| | | |].
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst k. rewrite nth_insert_candidate_eq by lia.
      simpl. rewrite HPeq. reflexivity.
    + apply Nat.eqb_neq in E. assert (Hnk : n < k) by lia.
      rewrite nth_insert_candidate_lt by lia. simpl. reflexivity.
  - tauto.
  - inversion Hlc as [| |K A B HA HB| |].
    split.
    + intros [Hs Hrel]. split; [exact Hs|].
      intros v Hpath Hv A0 b Heq u HuL Hu.
      apply (proj1 (IHT2 k rho xi U P (open_tm b u) HB Hlen HPeq HU)).
      eapply Hrel; [exact Hpath|exact Hv|exact Heq|exact HuL|].
      apply (proj2 (IHT1 k rho xi U P u HA Hlen HPeq HU)). exact Hu.
    + intros [Hs Hrel]. split; [exact Hs|].
      intros v Hpath Hv A0 b Heq u HuL Hu.
      apply (proj2 (IHT2 k rho xi U P (open_tm b u) HB Hlen HPeq HU)).
      eapply Hrel; [exact Hpath|exact Hv|exact Heq|exact HuL|].
      apply (proj1 (IHT1 k rho xi U P u HA Hlen HPeq HU)). exact Hu.
  - inversion Hlc as [| | |K A HA|].
    split.
    + intros [Hs Hrel]. split; [exact Hs|].
      intros v Hpath Hv b Heq V HV Q HQ.
      assert (HPeq' : P = interp (Q :: rho) xi U).
      { rewrite HPeq. apply functional_extensionality. intro z.
        apply propositional_extensionality. apply interp_env_irrel; exact HU. }
      apply (proj1 (IHT (S k) (Q :: rho) xi U P (open_tm_ty b V)
        HA ltac:(simpl; lia) HPeq' HU)).
      rewrite insert_candidate_succ. eapply Hrel; eauto.
    + intros [Hs Hrel]. split; [exact Hs|].
      intros v Hpath Hv b Heq V HV Q HQ.
      assert (HPeq' : P = interp (Q :: rho) xi U).
      { rewrite HPeq. apply functional_extensionality. intro z.
        apply propositional_extensionality. apply interp_env_irrel; exact HU. }
      apply (proj2 (IHT (S k) (Q :: rho) xi U P (open_tm_ty b V)
        HA ltac:(simpl; lia) HPeq' HU)).
      eapply Hrel; eauto.
  - tauto.
Qed.

Lemma interp_open_ty_rec : forall T k rho xi X P,
  lc_ty_at (S k) T -> ~ In X (ty_fv T) ->
  nth k rho strongly_normalizing = P ->
  forall t,
    interp rho (xi_update xi X P) (open_ty_rec k (Ty_FVar X) T) t <->
    interp rho xi T t.
Proof.
  induction T; intros k rho xi X P Hlc Hfresh Hnth t; simpl in *.
  - inversion Hlc as [K i Hi| | | |].
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. rewrite <- E.
      unfold interp, xi_update. simpl. rewrite Nat.eqb_refl.
      rewrite <- Hnth. reflexivity.
    + apply Nat.eqb_neq in E. assert (Hnk : n < k) by lia.
      reflexivity.
  - assert (X <> a).
    { intro Heq. subst a. apply Hfresh. simpl; auto. }
    unfold interp, xi_update. simpl.
    destruct (Nat.eqb a X) eqn:E; [apply Nat.eqb_eq in E; congruence|reflexivity].
  - inversion Hlc as [| |K A B HA HB| |].
    assert (Hfresh1 : ~ In X (ty_fv T1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hfresh2 : ~ In X (ty_fv T2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    simpl. split.
    + intros [Hs Hact]. split; [exact Hs|].
      intros v Hpath Hv T0 b Heq u HuL Hu.
      apply (proj1 (IHT2 k rho xi X P HB Hfresh2 Hnth
        (open_tm b u))).
      eapply Hact; [exact Hpath|exact Hv|exact Heq|exact HuL|].
      apply (proj2 (IHT1 k rho xi X P HA Hfresh1 Hnth u)). exact Hu.
    + intros [Hs Hact]. split; [exact Hs|].
      intros v Hpath Hv T0 b Heq u HuL Hu.
      apply (proj2 (IHT2 k rho xi X P HB Hfresh2 Hnth
        (open_tm b u))).
      eapply Hact; [exact Hpath|exact Hv|exact Heq|exact HuL|].
      apply (proj1 (IHT1 k rho xi X P HA Hfresh1 Hnth u)). exact Hu.
  - inversion Hlc as [| | |K A HA|].
    simpl. split.
    + intros [Hs Hall]. split; [exact Hs|].
      intros v Hpath Hv b Heq U HU Q HQ.
      (* The body relation is transported at one greater type depth. *)
      change (interp (Q :: rho) xi T (open_tm_ty b U)).
      pose proof (IHT (S k) (Q :: rho) xi X P HA Hfresh) as IHopen.
      assert (Hnth' : nth (S k) (Q :: rho) strongly_normalizing = P) by (simpl; exact Hnth).
      specialize (IHopen Hnth' (open_tm_ty b U)).
      apply (proj1 IHopen). eapply Hall; eauto.
    + intros [Hs Hall]. split; [exact Hs|].
      intros v Hpath Hv b Heq U HU Q HQ.
      change (interp (Q :: rho) (xi_update xi X P)
        (open_ty_rec (S k) (Ty_FVar X) T) (open_tm_ty b U)).
      pose proof (IHT (S k) (Q :: rho) xi X P HA Hfresh) as IHopen.
      assert (Hnth' : nth (S k) (Q :: rho) strongly_normalizing = P) by (simpl; exact Hnth).
      specialize (IHopen Hnth' (open_tm_ty b U)).
      apply (proj2 IHopen). eapply Hall; eauto.
  - split; intros [Hs Hcan]; split; try assumption;
      intros v Hv Hval; apply Hcan with (v := v); assumption.
Qed.

Lemma interp_xi_update_irrel : forall T rho xi X P,
  ~ In X (ty_fv T) -> forall t,
    interp rho (xi_update xi X P) T t <-> interp rho xi T t.
Proof.
  induction T; intros rho xi X P Hfresh t; simpl in *.
  - tauto.
  - assert (X <> a).
    { intro Heq. subst a. apply Hfresh. simpl; auto. }
    unfold xi_update. simpl.
    destruct (Nat.eqb a X) eqn:E; [apply Nat.eqb_eq in E; congruence|reflexivity].
  - assert (Hf1 : ~ In X (ty_fv T1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hf2 : ~ In X (ty_fv T2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    split.
    + intros [Hs Hact]. split; [exact Hs|].
      intros v Hpath Hv A b Heq u HuL Hu.
      apply (proj1 (IHT2 rho xi X P Hf2 (open_tm b u))).
      eapply Hact; [exact Hpath|exact Hv|exact Heq|exact HuL|].
      apply (proj2 (IHT1 rho xi X P Hf1 u)). exact Hu.
    + intros [Hs Hact]. split; [exact Hs|].
      intros v Hpath Hv A b Heq u HuL Hu.
      apply (proj2 (IHT2 rho xi X P Hf2 (open_tm b u))).
      eapply Hact; [exact Hpath|exact Hv|exact Heq|exact HuL|].
      apply (proj1 (IHT1 rho xi X P Hf1 u)). exact Hu.
  - split.
    + intros [Hs Hact]. split; [exact Hs|].
      intros v Hpath Hv b Heq U HU Q HQ.
      apply (proj1 (IHT (Q :: rho) xi X P Hfresh (open_tm_ty b U))).
      eapply Hact; eauto.
    + intros [Hs Hact]. split; [exact Hs|].
      intros v Hpath Hv b Heq U HU Q HQ.
      apply (proj2 (IHT (Q :: rho) xi X P Hfresh (open_tm_ty b U))).
      eapply Hact; eauto.
  - tauto.
Qed.

(* A first-order view of the interpretation for later substitution lemmas. *)
Definition sem_context (Gamma : context) (rho : sem_ty_env) (xi : sem_free_ty_env)
    (sigma : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> locally_closed_ty T ->
    interp rho xi T (sigma x) /\ locally_closed_tm (sigma x).

Fixpoint tm_subst_env (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T b => tm_abs T (tm_subst_env sigma b)
  | tm_app f a => tm_app (tm_subst_env sigma f) (tm_subst_env sigma a)
  | tm_tabs b => tm_tabs (tm_subst_env sigma b)
  | tm_tapp b T => tm_tapp (tm_subst_env sigma b) T
  | tm_zero => tm_zero
  | tm_succ a => tm_succ (tm_subst_env sigma a)
  | tm_natrec n b s => tm_natrec (tm_subst_env sigma n)
      (tm_subst_env sigma b) (tm_subst_env sigma s)
  end.

Fixpoint tm_fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ b => tm_fv b
  | tm_app f a => tm_fv f ++ tm_fv a
  | tm_tabs b => tm_fv b
  | tm_tapp b _ => tm_fv b
  | tm_zero => []
  | tm_succ a => tm_fv a
  | tm_natrec n b s => tm_fv n ++ tm_fv b ++ tm_fv s
  end.

Definition sigma_update (sigma : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb y x then u else sigma y.

Fixpoint ty_subst_env (theta : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow A B => Ty_Arrow (ty_subst_env theta A) (ty_subst_env theta B)
  | Ty_All A => Ty_All (ty_subst_env theta A)
  | Ty_Nat => Ty_Nat
  end.

Fixpoint tm_ty_subst_env (theta : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T b => tm_abs (ty_subst_env theta T) (tm_ty_subst_env theta b)
  | tm_app f a => tm_app (tm_ty_subst_env theta f) (tm_ty_subst_env theta a)
  | tm_tabs b => tm_tabs (tm_ty_subst_env theta b)
  | tm_tapp b T => tm_tapp (tm_ty_subst_env theta b) (ty_subst_env theta T)
  | tm_zero => tm_zero
  | tm_succ a => tm_succ (tm_ty_subst_env theta a)
  | tm_natrec n b s => tm_natrec (tm_ty_subst_env theta n)
      (tm_ty_subst_env theta b) (tm_ty_subst_env theta s)
  end.

Definition sem_context_subst (Gamma : context) (rho : sem_ty_env)
    (xi : sem_free_ty_env) (theta : atom -> ty) (sigma : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> locally_closed_ty T ->
    interp rho xi (ty_subst_env theta T) (sigma x) /\
    locally_closed_tm (sigma x).

Definition type_env_rel (Delta : ty_context) (rho : sem_ty_env)
    (xi : sem_free_ty_env) (theta : atom -> ty) : Prop :=
  forall X, In X Delta -> xi X = interp rho xi (theta X).

Definition ty_env_support (Delta : ty_context) (theta : atom -> ty) : list atom :=
  concat (map (fun X => ty_fv (theta X)) Delta).

Definition ctx_ty_support (Gamma : context) : list atom :=
  concat (map (fun p => ty_fv (snd p)) Gamma).

Definition ctx_ty_subst_support (Gamma : context) (theta : atom -> ty) : list atom :=
  concat (map (fun p => ty_fv (ty_subst_env theta (snd p))) Gamma).

Lemma in_ty_env_support : forall Delta theta X,
  In X (ty_env_support Delta theta) ->
  exists Z, In Z Delta /\ In X (ty_fv (theta Z)).
Proof.
  intros Delta theta X H. unfold ty_env_support in H.
  apply in_concat in H as [ys [Hys HX]].
  apply in_map_iff in Hys as [Z [E HZ]]. subst ys. eauto.
Qed.

Lemma in_ctx_ty_support : forall Gamma X,
  In X (ctx_ty_support Gamma) ->
  exists x T, In (x,T) Gamma /\ In X (ty_fv T).
Proof.
  intros Gamma X H. unfold ctx_ty_support in H.
  apply in_concat in H as [ys [Hys HX]].
  apply in_map_iff in Hys as [[x T] [E Hin]]. simpl in E. subst ys. eauto.
Qed.

Lemma in_ctx_ty_subst_support : forall Gamma theta X,
  In X (ctx_ty_subst_support Gamma theta) ->
  exists x T, In (x,T) Gamma /\ In X (ty_fv (ty_subst_env theta T)).
Proof.
  intros Gamma theta X H. unfold ctx_ty_subst_support in H.
  apply in_concat in H as [ys [Hys HX]].
  apply in_map_iff in Hys as [[x T] [E Hin]]. simpl in E. subst ys. eauto.
Qed.

Lemma lc_ty_weaken : forall j k T,
  j <= k -> lc_ty_at j T -> lc_ty_at k T.
Proof.
  intros j k T Hle Hlc. revert k Hle.
  induction Hlc; intros K Hle.
  - constructor. lia.
  - constructor.
  - constructor; [eapply IHHlc1|eapply IHHlc2]; eauto.
  - constructor. eapply IHHlc. lia.
  - constructor.
Qed.

Lemma ty_subst_env_lc_at : forall k T theta,
  lc_ty_at k T -> (forall X, locally_closed_ty (theta X)) ->
  lc_ty_at k (ty_subst_env theta T).
Proof.
  intros k T theta Hlc. revert theta.
  induction Hlc; intros theta Htheta; simpl.
  - constructor; assumption.
  - unfold locally_closed_ty in Htheta. eapply lc_ty_weaken with (j := 0); [lia|apply Htheta].
  - constructor; [apply IHHlc1|apply IHHlc2]; assumption.
  - constructor. apply IHHlc. assumption.
  - constructor.
Qed.

Lemma sem_context_subst_update : forall Gamma rho xi theta sigma x T u,
  ~ In x (map fst Gamma) ->
  sem_context_subst Gamma rho xi theta sigma ->
  locally_closed_ty T -> interp rho xi (ty_subst_env theta T) u ->
  locally_closed_tm u ->
  sem_context_subst (update Gamma x T) rho xi theta (sigma_update sigma x u).
Proof.
  intros Gamma rho xi theta sigma x T u Hfresh Hctx HT Hu Hul.
  intros y S Hlookup HlcS. destruct (Nat.eq_dec y x) as [->|Hneq].
  - simpl in Hlookup. rewrite Nat.eqb_refl in Hlookup. inversion Hlookup; subst S.
    unfold sigma_update. rewrite Nat.eqb_refl. auto.
  - simpl in Hlookup. destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. contradiction.
    +
    specialize (Hctx y S Hlookup HlcS). unfold sigma_update.
    rewrite E. exact Hctx.
Qed.

Definition theta_update (theta : atom -> ty) (X : atom) (U : ty) : atom -> ty :=
  fun Y => if Nat.eqb Y X then U else theta Y.

Lemma type_env_rel_extend : forall Delta rho xi theta X U P,
  type_env_rel Delta rho xi theta ->
  ~ In X Delta ->
  (forall Y, In Y Delta -> ~ In X (ty_fv (theta Y))) ->
  ~ In X (ty_fv U) -> P = interp rho xi U ->
  type_env_rel (X :: Delta) rho (xi_update xi X P) (theta_update theta X U).
Proof.
  intros Delta rho xi theta X U P Hrel HX Htheta HU HPeq Y HY.
  simpl in HY. destruct HY as [Heq|HY].
  - subst Y.
    unfold xi_update, theta_update. rewrite Nat.eqb_refl.
    rewrite HPeq. apply functional_extensionality. intro t.
    apply propositional_extensionality. symmetry.
    apply interp_xi_update_irrel; exact HU.
  - assert (Y <> X) by (intro E; subst; contradiction).
    unfold xi_update, theta_update.
    assert (Hneqb : Nat.eqb Y X = false) by (apply Nat.eqb_neq; congruence).
    rewrite Hneqb. rewrite Hrel; [|exact HY].
    apply functional_extensionality. intro t.
    apply propositional_extensionality. symmetry.
    apply interp_xi_update_irrel. apply Htheta. exact HY.
Qed.

Fixpoint tm_ty_fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_zero => []
  | tm_abs T b => ty_fv T ++ tm_ty_fv b
  | tm_app f a => tm_ty_fv f ++ tm_ty_fv a
  | tm_tabs b => tm_ty_fv b
  | tm_tapp b T => tm_ty_fv b ++ ty_fv T
  | tm_succ a => tm_ty_fv a
  | tm_natrec n b s => tm_ty_fv n ++ tm_ty_fv b ++ tm_ty_fv s
  end.

Lemma tm_subst_env_update_agree : forall t sigma x u,
  ~ In x (tm_fv t) ->
  tm_subst_env (sigma_update sigma x u) t = tm_subst_env sigma t.
Proof.
  induction t; intros sigma x u Hfresh; simpl in *.
  - reflexivity.
  - unfold sigma_update. destruct (Nat.eqb a x) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso. apply Hfresh. simpl. auto.
    + reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - rewrite IHt1, IHt2; [reflexivity|intro Hin; apply Hfresh; apply in_or_app; auto|intro Hin; apply Hfresh; apply in_or_app; auto].
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - assert (H1 : ~ In x (tm_fv t1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (H2 : ~ In x (tm_fv t2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. left. exact Hin. }
    assert (H3 : ~ In x (tm_fv t3)).
    { intro Hin. apply Hfresh. apply in_or_app. right. apply in_or_app. right. exact Hin. }
    rewrite (IHt1 sigma x u H1), (IHt2 sigma x u H2), (IHt3 sigma x u H3).
    reflexivity.
Qed.

Fixpoint max_atom (xs : list atom) : atom :=
  match xs with [] => 0 | x :: xs' => Nat.max x (max_atom xs') end.

Lemma in_le_max_atom : forall xs x, In x xs -> x <= max_atom xs.
Proof.
  induction xs as [|a xs IH]; intros x Hin; simpl in *; [contradiction|].
  destruct Hin as [->|Hin].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

Lemma exists_fresh_atoms : forall xs : list atom, exists x, ~ In x xs.
Proof.
  intros xs. exists (S (max_atom xs)). intro Hin.
  pose proof (in_le_max_atom xs _ Hin). lia.
Qed.

Lemma lc_ty_open_inv : forall K k X T,
  k = K -> ~ In X (ty_fv T) ->
  lc_ty_at K (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S K) T.
Proof.
  intros K0 k0 X0 T. revert K0 k0 X0. induction T; intros K0 k0 X0 Heq Hfresh Hlc; simpl in *.
  - destruct (Nat.eqb k0 n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. constructor. lia.
    + apply Nat.eqb_neq in E. inversion Hlc; subst. constructor. lia.
  - constructor.
  - inversion Hlc as [| |K' A B HA HB| |].
    apply lc_ty_arrow.
    + eapply IHT1; [exact Heq|intro Hin; apply Hfresh; apply in_or_app; left; exact Hin|exact HA].
    + eapply IHT2; [exact Heq|intro Hin; apply Hfresh; apply in_or_app; right; exact Hin|exact HB].
  - inversion Hlc as [| | |K' A HA|]; subst.
    apply lc_ty_all.
    eapply (IHT (S K0) (S K0) X0); [reflexivity|exact Hfresh|exact HA].
  - constructor.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf. induction Hwf.
  - unfold locally_closed_ty. constructor.
  - unfold locally_closed_ty in *. constructor; assumption.
  - unfold locally_closed_ty. apply lc_ty_all.
    destruct (exists_fresh_atoms (L ++ ty_fv T)) as [X HX].
    assert (HXL : ~ In X L).
    { intro Hin. apply HX. apply in_or_app. left. exact Hin. }
    assert (HXT : ~ In X (ty_fv T)).
    { intro Hin. apply HX. apply in_or_app. right. exact Hin. }
    pose proof (H0 X HXL) as Hlco.
    eapply lc_ty_open_inv; [reflexivity|exact HXT|exact Hlco].
  - unfold locally_closed_ty. constructor.
Qed.

Lemma lookup_update_eq : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof. intros. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma lookup_update_neq : forall Gamma x y T,
  x <> y -> lookup_context y (update Gamma x T) = lookup_context y Gamma.
Proof.
  intros Gamma x y T Hxy. simpl. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. congruence.
  - reflexivity.
Qed.

Lemma sem_context_update : forall Gamma rho xi sigma x T u,
  ~ In x (map fst Gamma) ->
  sem_context Gamma rho xi sigma ->
  locally_closed_ty T -> interp rho xi T u -> locally_closed_tm u ->
  sem_context (update Gamma x T) rho xi (sigma_update sigma x u).
Proof.
  intros Gamma rho xi sigma x T u Hfresh Hctx HT Hu Hul.
  intros y S Hlookup HS.
  destruct (Nat.eq_dec y x) as [->|Hneq].
  - rewrite lookup_update_eq in Hlookup. inversion Hlookup; subst S.
    unfold sigma_update. rewrite Nat.eqb_refl. auto.
  - rewrite lookup_update_neq in Hlookup by congruence.
    specialize (Hctx y S Hlookup HS). unfold sigma_update.
    destruct (Nat.eqb y x) eqn:E; [apply Nat.eqb_eq in E; contradiction|exact Hctx].
Qed.

Lemma ty_subst_env_update_agree : forall T theta X U,
  ~ In X (ty_fv T) ->
  ty_subst_env (theta_update theta X U) T = ty_subst_env theta T.
Proof.
  induction T; intros theta X U Hfresh; simpl in *.
  - reflexivity.
  - unfold theta_update. destruct (Nat.eqb a X) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso. apply Hfresh. simpl; auto.
    + reflexivity.
  - assert (H1 : ~ In X (ty_fv T1)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (H2 : ~ In X (ty_fv T2)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite (IHT1 theta X U H1), (IHT2 theta X U H2). reflexivity.
  - f_equal. apply IHT. exact Hfresh.
  - reflexivity.
Qed.

Lemma sem_context_subst_type_update : forall Gamma rho xi theta sigma X U P,
  sem_context_subst Gamma rho xi theta sigma ->
  (forall x T, lookup_context x Gamma = Some T -> locally_closed_ty T ->
    ~ In X (ty_fv T) /\ ~ In X (ty_fv (ty_subst_env theta T))) ->
  sem_context_subst Gamma rho (xi_update xi X P) (theta_update theta X U) sigma.
Proof.
  intros Gamma rho xi theta sigma X U P Hctx Hfresh x T Hlookup HT.
  destruct (Hfresh x T Hlookup HT) as [Hraw Hsub].
  specialize (Hctx x T Hlookup HT) as [Hrel Hul].
  rewrite (ty_subst_env_update_agree T theta X U Hraw).
  split; [|exact Hul].
  apply (proj2 (interp_xi_update_irrel (ty_subst_env theta T) rho xi X P Hsub (sigma x))).
  exact Hrel.
Qed.

Lemma tm_ty_subst_env_update_agree : forall t theta X U,
  ~ In X (tm_ty_fv t) ->
  tm_ty_subst_env (theta_update theta X U) t = tm_ty_subst_env theta t.
Proof.
  induction t as [n|x|A b IHb|f IHf a IHa|b IHb|b IHb A| |a IHa|n IHn b IHb s IHs];
    intros theta X U Hfresh; simpl in *.
  - reflexivity.
  - reflexivity.
  - assert (HA : ~ In X (ty_fv A)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hb : ~ In X (tm_ty_fv b)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite (ty_subst_env_update_agree A theta X U HA), (IHb theta X U Hb). reflexivity.
  - assert (Hf : ~ In X (tm_ty_fv f)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Ha : ~ In X (tm_ty_fv a)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite (IHf theta X U Hf), (IHa theta X U Ha). reflexivity.
  - f_equal. apply IHb. exact Hfresh.
  - assert (Hb : ~ In X (tm_ty_fv b)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (HA : ~ In X (ty_fv A)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    rewrite (IHb theta X U Hb), (ty_subst_env_update_agree A theta X U HA). reflexivity.
  - reflexivity.
  - f_equal. apply IHa. exact Hfresh.
  - assert (Hn : ~ In X (tm_ty_fv n)).
    { intro Hin. apply Hfresh. apply in_or_app. left. exact Hin. }
    assert (Hbs : ~ In X (tm_ty_fv b ++ tm_ty_fv s)).
    { intro Hin. apply Hfresh. apply in_or_app. right. exact Hin. }
    assert (Hb : ~ In X (tm_ty_fv b)).
    { intro Hin. apply Hbs. apply in_or_app. left. exact Hin. }
    assert (Hs : ~ In X (tm_ty_fv s)).
    { intro Hin. apply Hbs. apply in_or_app. right. exact Hin. }
    rewrite (IHn theta X U Hn), (IHb theta X U Hb), (IHs theta X U Hs). reflexivity.
Qed.

Lemma open_tm_rec_inert : forall K d k u t,
  lc_tm_at K d t -> d <= k -> open_tm_rec k u t = t.
Proof.
  intros K d k0 u t Hlc. revert k0. induction Hlc; intros q Hle; simpl.
  - destruct (Nat.eqb q i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - f_equal. eapply IHHlc. lia.
  - f_equal; [apply IHHlc1|apply IHHlc2]; exact Hle.
  - f_equal. apply IHHlc. exact Hle.
  - f_equal. apply IHHlc. exact Hle.
  - reflexivity.
  - f_equal. apply IHHlc. exact Hle.
  - f_equal; [apply IHHlc1|apply IHHlc2|apply IHHlc3]; exact Hle.
Qed.

Lemma tm_subst_env_open_rec : forall sigma k u t,
  (forall x, locally_closed_tm (sigma x)) ->
  tm_subst_env sigma (open_tm_rec k u t) =
  open_tm_rec k (tm_subst_env sigma u) (tm_subst_env sigma t).
Proof.
  intros sigma k u t Hsigma. revert k. induction t; intros k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - unfold locally_closed_tm in Hsigma.
    rewrite (open_tm_rec_inert 0 0 k (tm_subst_env sigma u) (sigma a)).
    + reflexivity.
    + apply Hsigma.
    + lia.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma tm_subst_env_open : forall sigma t u,
  (forall x, locally_closed_tm (sigma x)) ->
  tm_subst_env sigma (open_tm t u) =
  open_tm (tm_subst_env sigma t) (tm_subst_env sigma u).
Proof. intros. apply tm_subst_env_open_rec; assumption. Qed.

Lemma open_ty_rec_inert : forall K k U T,
  lc_ty_at K T -> K <= k -> open_ty_rec k U T = T.
Proof.
  intros K k U T Hlc. revert k. induction Hlc; intros q Hle; simpl.
  - destruct (Nat.eqb q i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - rewrite (IHHlc1 q Hle), (IHHlc2 q Hle). reflexivity.
  - f_equal. apply IHHlc. lia.
  - reflexivity.
Qed.

Lemma open_tm_ty_rec_inert : forall K d k U t,
  lc_tm_at K d t -> K <= k -> open_tm_ty_rec k U t = t.
Proof.
  intros K d k U t Hlc. revert k. induction Hlc; intros q Hle; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (open_ty_rec_inert K q U T H Hle). f_equal.
    exact (IHHlc q Hle).
  - rewrite (IHHlc1 q Hle), (IHHlc2 q Hle). reflexivity.
  - f_equal. apply IHHlc. lia.
  - rewrite (IHHlc q Hle).
    match goal with Hty : lc_ty_at K T |- _ =>
      rewrite (open_ty_rec_inert K q U T Hty Hle)
    end. reflexivity.
  - reflexivity.
  - f_equal. apply IHHlc. exact Hle.
  - rewrite (IHHlc1 q Hle), (IHHlc2 q Hle), (IHHlc3 q Hle). reflexivity.
Qed.

Lemma tm_subst_env_open_ty_rec : forall sigma k U t,
  (forall x, locally_closed_tm (sigma x)) ->
  tm_subst_env sigma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k U (tm_subst_env sigma t).
Proof.
  intros sigma k U t Hsigma. revert k. induction t; intros k; simpl.
  - reflexivity.
  - unfold locally_closed_tm in Hsigma.
    change (sigma a = open_tm_ty_rec k U (sigma a)).
    symmetry. apply open_tm_ty_rec_inert with (K := 0) (d := 0).
    + apply Hsigma.
    + lia.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma tm_subst_env_open_ty : forall sigma t U,
  (forall x, locally_closed_tm (sigma x)) ->
  tm_subst_env sigma (open_tm_ty t U) =
  open_tm_ty (tm_subst_env sigma t) U.
Proof. intros. unfold open_tm_ty. apply tm_subst_env_open_ty_rec; assumption. Qed.

Lemma ty_subst_env_open_rec : forall theta k U T,
  (forall X, locally_closed_ty (theta X)) ->
  ty_subst_env theta (open_ty_rec k U T) =
  open_ty_rec k (ty_subst_env theta U) (ty_subst_env theta T).
Proof.
  intros theta k U T Htheta. revert k. induction T; intros k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - unfold locally_closed_ty in Htheta. symmetry.
    apply open_ty_rec_inert with (K := 0); [apply Htheta|lia].
  - rewrite IHT1, IHT2; auto.
  - rewrite IHT. reflexivity.
  - reflexivity.
Qed.

Lemma tm_ty_subst_env_open_tm : forall theta k u t,
  tm_ty_subst_env theta (open_tm_rec k u t) =
  open_tm_rec k (tm_ty_subst_env theta u) (tm_ty_subst_env theta t).
Proof.
  intros theta k u t. revert k. induction t; intros k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma tm_ty_subst_env_open_ty_rec : forall theta k U t,
  (forall X, locally_closed_ty (theta X)) ->
  tm_ty_subst_env theta (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (ty_subst_env theta U) (tm_ty_subst_env theta t).
Proof.
  intros theta k U t Htheta. revert k.
  induction t as [n|x|A b IHb|f IHf a IHa|b IHb|b IHb A| |a IHa|n IHn b IHb s IHs]; intros k; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (ty_subst_env_open_rec theta k U A Htheta), IHb. reflexivity.
  - rewrite IHf, IHa. reflexivity.
  - rewrite IHb. reflexivity.
  - rewrite IHb, (ty_subst_env_open_rec theta k U A Htheta). reflexivity.
  - reflexivity.
  - rewrite IHa. reflexivity.
  - rewrite IHn, IHb, IHs. reflexivity.
Qed.

Lemma sn_succ : forall t, strongly_normalizing t ->
  strongly_normalizing (tm_succ t).
Proof.
  intros t H. induction H as [t Hred IH].
  apply SN_intro. intros u Hu. inversion Hu; subst.
  eapply IH. eassumption.
Qed.

Lemma sn_value_closed : forall v,
  value v -> strongly_normalizing v.
Proof.
  intros v Hv. induction Hv.
  - apply SN_intro. intros u Hs. inversion Hs.
  - apply SN_intro. intros u Hs. inversion Hs.
  - induction H as [|n Hn IH].
    + apply SN_intro. intros u Hs. inversion Hs.
    + apply sn_succ. exact IH.
Qed.

Lemma sn_abs : forall T t,
  strongly_normalizing (tm_abs T t).
Proof.
  intros. apply SN_intro. intros u Hstep. inversion Hstep.
Qed.

Lemma sn_tabs : forall t,
  strongly_normalizing (tm_tabs t).
Proof.
  intros. apply SN_intro. intros u Hstep. inversion Hstep.
Qed.

Lemma sn_step_inv : forall t, strongly_normalizing t ->
  forall u, t --> u -> strongly_normalizing u.
Proof. intros t H; inversion H; eauto. Qed.

Lemma sn_candidate_closed : cand_closed strongly_normalizing.
Proof.
  unfold cand_closed. split.
  - intros t Ht. exact Ht.
  - split.
    + intros t u Ht Hstep. eapply sn_step_inv; eauto.
    + intros t Hnv Hst Hred. exact Hst.
Qed.

Lemma numeric_value_value : forall n, numeric_value n -> value n.
Proof. intros n H; induction H; apply v_nat; constructor; assumption. Qed.

Lemma multi_succ_inv : forall t v,
  tm_succ t -->* v -> exists u, t -->* u /\ v = tm_succ u.
Proof.
  intros t v H. remember (tm_succ t) as w eqn:Hw in H.
  revert t Hw. induction H as [x|x y z Hxy Hyz IH]; intros t Hw.
  - inversion Hw; subst. exists t. split; [constructor|reflexivity].
  - inversion Hw; subst x. inversion Hxy; subst y.
    destruct (IH t' eq_refl) as [u [Hu Heq]]. subst z.
    exists u. split; [eapply multi_step; eauto|reflexivity].
Qed.

Lemma nat_candidate_step : forall t u,
  nat_candidate t -> t --> u -> nat_candidate u.
Proof.
  intros t u [Hs Hcan] Hstep. split.
  - eapply sn_step_inv; eauto.
  - intros v Hv Hval. apply Hcan with (v := v); [|exact Hval].
    econstructor; eauto.
Qed.

Lemma nat_candidate_succ : forall t,
  nat_candidate t -> nat_candidate (tm_succ t).
Proof.
  intros t [Hs Hcan]. split.
  - apply sn_succ. exact Hs.
  - intros v Hv Hval.
    destruct (multi_succ_inv _ _ Hv) as [u [Hu Heq]]. subst v.
    inversion Hval; subst.
    match goal with Hnv : numeric_value (tm_succ _) |- _ => inversion Hnv; subst end.
    apply nv_succ. eapply Hcan; [exact Hu|].
    apply numeric_value_value. assumption.
Qed.

Lemma nth_candidate_closed : forall rho n,
  (forall P, In P rho -> cand_closed P) ->
  cand_closed (nth n rho strongly_normalizing).
Proof.
  induction rho as [|P rho IH]; intros [|n] H; simpl.
  - apply sn_candidate_closed.
  - apply sn_candidate_closed.
  - apply H. simpl. auto.
  - apply IH. intros Q HQ. apply H. simpl. auto.
Qed.

Lemma interp_closed : forall T rho xi,
  (forall P, In P rho -> cand_closed P) ->
  (forall X, cand_closed (xi X)) ->
  cand_closed (interp rho xi T).
Proof.
  induction T; intros rho xi Hrho Hxi; simpl.
  - apply nth_candidate_closed. exact Hrho.
  - apply Hxi.
  - split.
    + intros t [Hs _]. exact Hs.
    + split.
      * intros t u [Hs Hrel] Hstep. split.
        -- eapply sn_step_inv; [exact Hs|exact Hstep].
        -- intros v Huv Hv T b Heq u0 HuL Hu.
           eapply Hrel; [eapply multi_step; eauto|exact Hv|exact Heq|exact HuL|exact Hu].
      * intros t Hnv Hst Hred. split; [exact Hst|].
        intros v Hpath Hv T b Heq u HuL Hu. inversion Hpath; subst.
        -- contradiction.
        -- eapply (proj2 (Hred y H) (tm_abs T b) H0 Hv T b eq_refl u HuL Hu).
  - split.
    + intros t [Hs _]. exact Hs.
    + split.
      * intros t u [Hs Hall] Hstep. split.
        -- eapply sn_step_inv; [exact Hs|exact Hstep].
        -- intros v Huv Hv b Heq U HU P HP.
           eapply Hall; [eapply multi_step; eauto|exact Hv|exact Heq|exact HU|exact HP].
      * intros t Hnv Hst Hred. split; [exact Hst|].
        intros v Hpath Hv b Heq U HU P HP. inversion Hpath; subst.
        -- contradiction.
        -- eapply (proj2 (Hred y H) (tm_tabs b) H0 Hv b eq_refl U HU P HP).
  - split.
    + intros t Ht. exact (proj1 Ht).
    + split.
      * intros t u Ht Hstep. eapply nat_candidate_step; eauto.
      * intros t Hnv Hst Hred. split; [exact Hst|].
        intros v Hpath Hv. inversion Hpath; subst.
        -- contradiction.
        -- destruct (Hred y H) as [_ Hcan]. eapply Hcan; eauto.
Qed.

Lemma interp_from_steps : forall T rho xi t,
  (forall P, In P rho -> cand_closed P) ->
  (forall X, cand_closed (xi X)) ->
  ~ value t ->
  (forall u, t --> u -> interp rho xi T u) ->
  interp rho xi T t.
Proof.
  induction T; intros rho xi t Hrho Hxi Hnv Hred; simpl.
  - assert (Hst : strongly_normalizing t).
    { apply SN_intro. intros u Hu.
      exact (proj1 (nth_candidate_closed rho n Hrho) u (Hred u Hu)). }
    eapply (proj2 (proj2 (nth_candidate_closed rho n Hrho)) t Hnv Hst).
    exact Hred.
  - assert (Hst : strongly_normalizing t).
    { apply SN_intro. intros u Hu. exact (proj1 (Hxi a) u (Hred u Hu)). }
    eapply (proj2 (proj2 (Hxi a)) t Hnv Hst). exact Hred.
  - assert (Hst : strongly_normalizing t).
    { apply SN_intro. intros u Hu. exact (proj1 (Hred u Hu)). }
    split; [exact Hst|]. intros v Hpath Hv T0 b Heq u HuL Hu.
    inversion Hpath as [|x y z Hxy Hyz]; subst; [contradiction|].
    eapply (proj2 (Hred y Hxy)); eauto.
  - assert (Hst : strongly_normalizing t).
    { apply SN_intro. intros u Hu. exact (proj1 (Hred u Hu)). }
    split; [exact Hst|]. intros v Hpath Hv b Heq U HU P HP.
    inversion Hpath as [|x y z Hxy Hyz]; subst; [contradiction|].
    eapply (proj2 (Hred y Hxy)); eauto.
  - assert (Hst : strongly_normalizing t).
    { apply SN_intro. intros u Hu. exact (proj1 (Hred u Hu)). }
    split; [exact Hst|]. intros v Hpath Hv.
    inversion Hpath as [|x y z Hxy Hyz]; subst; [contradiction|].
    destruct (Hred y Hxy) as [_ Hcan]. eapply Hcan; eauto.
Qed.

Lemma multi_abs_inv : forall A b v,
  tm_abs A b -->* v -> v = tm_abs A b.
Proof.
  intros A b v H. remember (tm_abs A b) as q eqn:E in H.
  induction H.
  - inversion E; reflexivity.
  - inversion E; subst. inversion H.
Qed.

Lemma multi_tabs_inv : forall b v,
  tm_tabs b -->* v -> v = tm_tabs b.
Proof.
  intros b v H. remember (tm_tabs b) as q eqn:E in H.
  induction H.
  - inversion E; reflexivity.
  - inversion E; subst. inversion H.
Qed.

Lemma numeric_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof. intros n H; induction H; simpl; constructor; assumption. Qed.

Lemma value_locally_closed : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H. inversion H; subst; eauto using numeric_lc.
Qed.

Lemma app_related : forall rho xi A B f a,
  (forall P, In P rho -> cand_closed P) ->
  (forall X, cand_closed (xi X)) ->
  interp rho xi (Ty_Arrow A B) f -> interp rho xi A a ->
  interp rho xi B (tm_app f a).
Proof.
  intros rho xi A B f a Hrho Hxi Hf Ha.
  destruct Hf as [Hsf Hfrel].
  revert a Hfrel Ha.
  induction Hsf as [f Hfstep IHf].
  intros a Hfrel Ha.
  assert (Hsa : strongly_normalizing a).
  { pose proof (interp_closed A rho xi Hrho Hxi) as Hcc.
    unfold cand_closed in Hcc. destruct Hcc as [Hsn _]. exact (Hsn a Ha). }
  pose proof Hfrel as Hbehavior. revert Hbehavior Ha.
  induction Hsa as [a Hastep IHa].
  intros Hbehavior Ha.
  apply interp_from_steps with (rho := rho) (xi := xi).
  - exact Hrho.
  - exact Hxi.
  - intro Hv. inversion Hv; subst; try congruence.
    match goal with Hn : numeric_value (tm_app _ _) |- _ => inversion Hn end.
  - intros r Hr.
    inversion Hr as [T0 b0 v0 Hlc Hv | f0 f1 a0 Hfs Hlc |
      v0 a0 a1 Hv Has | tb U Hlc HU | t0 t1 U Hts HU |
      t0 t1 Hts | n0 n1 b0 s0 Hns Hlb Hls |
      n0 b0 b1 s0 Hnv Hbs Hls | n0 b0 s0 s1 Hnv Hvb Hss |
      b0 s0 Hvb Hvs | n0 b0 s0 Hnv Hvb Hvs]; subst.
    + exact (@Hbehavior (tm_abs T0 b0) (multi_refl _) (v_abs T0 b0 Hlc)
        T0 b0 eq_refl a (value_locally_closed a Hv) Ha).
    + match goal with
      | |- interp rho xi B (tm_app ?g a) =>
        (assert (Hg : interp rho xi (Ty_Arrow A B) g) by
          (pose proof (interp_closed (Ty_Arrow A B) rho xi Hrho Hxi) as Hcc;
           unfold cand_closed in Hcc; destruct Hcc as [_ [Hstep _]];
           assert (Hsrc : interp rho xi (Ty_Arrow A B) f)
             by (split; [constructor; exact Hfstep|exact Hbehavior]);
           exact (@Hstep f g Hsrc Hfs));
         destruct Hg as [_ Hbehavior']; exact (IHf g Hfs a Hbehavior' Ha))
      end.
    + match goal with
      | |- interp rho xi B (tm_app f ?arg) =>
        (assert (Ha' : interp rho xi A arg) by
          (pose proof (interp_closed A rho xi Hrho Hxi) as Hcc;
           unfold cand_closed in Hcc; destruct Hcc as [_ [Hstep _]];
           exact (@Hstep a arg Ha Has));
         exact (IHa arg Has Hbehavior Ha'))
      end.
Qed.

Lemma numeric_no_step : forall n, numeric_value n -> forall u, ~ n --> u.
Proof.
  intros n H. induction H as [|n Hn IH]; intros u Hu.
  - inversion Hu.
  - inversion Hu; subst. eapply IH. eassumption.
Qed.

Lemma numeric_nat_related : forall n,
  numeric_value n -> nat_candidate n.
Proof.
  intros n Hn. split.
  - apply sn_value_closed. apply numeric_value_value. exact Hn.
  - intros v Hpath Hv. remember n as q eqn:Eq in Hpath.
    induction Hpath; subst; [exact Hn|]. exfalso. eapply numeric_no_step; eauto.
Qed.

Lemma natrec_numeric_related : forall rho xi T b s n,
  (forall P, In P rho -> cand_closed P) ->
  (forall X, cand_closed (xi X)) ->
  interp rho xi T b ->
  interp rho xi (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  numeric_value n -> interp rho xi T (tm_natrec n b s).
Proof.
  intros rho xi T b s n Hrho Hxi Hb Hs Hn.
  pose proof (interp_closed T rho xi Hrho Hxi) as Hcb.
  unfold cand_closed in Hcb. destruct Hcb as [Hbsn _].
  pose proof (Hbsn b Hb) as Hbs.
  pose proof (interp_closed (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho xi Hrho Hxi) as Hcs.
  unfold cand_closed in Hcs. destruct Hcs as [Hssn _].
  pose proof (Hssn s Hs) as Hsn_s.
  revert s Hs Hsn_s n Hn.
  induction Hbs as [b Hbred IHb].
  intros s Hs Hsn_s n Hn. revert n Hn.
  induction Hsn_s as [s Hsred IHs]. intros n Hn.
  induction Hn as [|n Hn IHn].
  -
    apply interp_from_steps with (rho := rho) (xi := xi).
    + exact Hrho.
    + exact Hxi.
    + intro Hv. inversion Hv; subst. match goal with Hnv : numeric_value (tm_natrec _ _ _) |- _ => inversion Hnv end.
    + intros r Hr. inversion Hr as [T0 b0 v0 Hlc Hv | f0 f1 a0 Hfs Hlc |
        v0 a0 a1 Hv Has | tb U Hlc HU | t0 t1 U Hts HU |
        t0 t1 Hts | n0 n1 b0 s0 Hns Hlb Hls |
        n0 b0 b1 s0 Hnv Hbs Hls | n0 b0 s0 s1 Hnv Hvb Hss |
        b0 s0 Hvb Hvs | n0 b0 s0 Hnv Hvb Hvs]; subst.
      * inversion Hns.
      * assert (Hb' : interp rho xi T b1).
        { pose proof (interp_closed T rho xi Hrho Hxi) as Hcc.
          unfold cand_closed in Hcc. destruct Hcc as [_ [Hstep _]].
          exact (@Hstep b b1 Hb Hbs). }
        eapply IHb; eauto.
      * assert (Hs' : interp rho xi (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s1).
        { pose proof (interp_closed (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho xi Hrho Hxi) as Hcc.
          unfold cand_closed in Hcc. destruct Hcc as [_ [Hstep _]].
          exact (@Hstep s s1 Hs Hss). }
        eapply IHs; eauto.
      * exact Hb.
  -
    apply interp_from_steps with (rho := rho) (xi := xi).
    + exact Hrho.
    + exact Hxi.
    + intro Hv. inversion Hv; subst. match goal with Hnv : numeric_value (tm_natrec _ _ _) |- _ => inversion Hnv end.
    + intros r Hr. inversion Hr as [T0 b0 v0 Hlc Hv | f0 f1 a0 Hfs Hlc |
        v0 a0 a1 Hv Has | tb U Hlc HU | t0 t1 U Hts HU |
        t0 t1 Hts | n0 n1 b0 s0 Hns Hlb Hls |
        n0 b0 b1 s0 Hnv Hbs Hls | n0 b0 s0 s1 Hnv Hvb Hss |
        b0 s0 Hvb Hvs | n0 b0 s0 Hnv Hvb Hvs]; subst.
      * exfalso. eapply numeric_no_step; [apply nv_succ; exact Hn|exact Hns].
      * assert (Hb' : interp rho xi T b1).
        { pose proof (interp_closed T rho xi Hrho Hxi) as Hcc.
          unfold cand_closed in Hcc. destruct Hcc as [_ [Hstep _]].
          exact (@Hstep b b1 Hb Hbs). }
        eapply IHb; eauto.
      * assert (Hs' : interp rho xi (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s1).
        { pose proof (interp_closed (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho xi Hrho Hxi) as Hcc.
          unfold cand_closed in Hcc. destruct Hcc as [_ [Hstep _]].
          exact (@Hstep s s1 Hs Hss). }
        eapply IHs; eauto.
      * assert (Hnrel : interp rho xi Ty_Nat n) by (apply numeric_nat_related; exact Hn).
        assert (Hrec : interp rho xi T (tm_natrec n b s)) by (apply IHn; assumption).
        eapply app_related.
        -- exact Hrho.
        -- exact Hxi.
        -- eapply app_related; [exact Hrho|exact Hxi|exact Hs|exact Hnrel].
        -- exact Hrec.
Qed.

Lemma natrec_related : forall rho xi T n b s,
  (forall P, In P rho -> cand_closed P) ->
  (forall X, cand_closed (xi X)) ->
  interp rho xi Ty_Nat n -> interp rho xi T b ->
  interp rho xi (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  interp rho xi T (tm_natrec n b s).
Proof.
  intros rho xi T n b s Hrho Hxi Hn Hb Hs.
  destruct Hn as [Hsn Hcan]. revert Hb Hs Hcan.
  induction Hsn as [n Hred IH]. intros Hb Hs Hcan.
  apply interp_from_steps with (rho := rho) (xi := xi).
  - exact Hrho.
  - exact Hxi.
  - intro Hv. inversion Hv; subst. match goal with Hnv : numeric_value (tm_natrec _ _ _) |- _ => inversion Hnv end.
  - intros r Hr. inversion Hr as [T0 b0 v0 Hlc Hv | f0 f1 a0 Hfs Hlc |
      v0 a0 a1 Hv Has | tb U Hlc HU | t0 t1 U Hts HU |
      t0 t1 Hts | n0 n1 b0 s0 Hns Hlb Hls |
      n0 b0 b1 s0 Hnv Hbs Hls | n0 b0 s0 s1 Hnv Hvb Hss |
      b0 s0 Hvb Hvs | n0 b0 s0 Hnv Hvb Hvs]; subst.
    + eapply IH.
      * exact Hns.
      * apply nat_candidate_step with (t := n) (u := n'); [split; assumption|exact Hns].
      * exact Hb.
      * exact Hs.
      * exact Hcan.
    + pose proof (interp_closed T rho xi Hrho Hxi) as Hcc.
      unfold cand_closed in Hcc. destruct Hcc as [_ [Hstep _]].
      exact (@Hstep b b1 Hb Hbs).
    + pose proof (interp_closed (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho xi Hrho Hxi) as Hcc.
      unfold cand_closed in Hcc. destruct Hcc as [_ [Hstep _]].
      exact (@Hstep s s1 Hs Hss).
    + exact Hb.
    + assert (Hrec : interp rho xi T (tm_natrec n0 b s)).
      { eapply natrec_numeric_related; eauto. }
      assert (Hnr : interp rho xi Ty_Nat n0) by (apply numeric_nat_related; exact Hnv).
      eapply app_related.
      * exact Hrho.
      * exact Hxi.
      * eapply app_related; [exact Hrho|exact Hxi|exact Hs|exact Hnr].
      * exact Hrec.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End SystemFNormalizationRecursionHardTask.
