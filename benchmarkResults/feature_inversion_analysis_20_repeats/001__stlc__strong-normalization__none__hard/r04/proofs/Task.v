(** STLC call-by-value strong-normalization benchmark.
    No if-then-else, non-determinism, or recursion is included. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Relations.Relation_Definitions.
From Stdlib Require Import Lia.

Module STLCNormalizationNoneHardTask.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
      R x y ->
      multi R y z ->
      multi R x z.

(** Language syntax, using locally nameless binders. *)

Definition atom := nat.

Inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tm_bvar : nat -> tm
  | tm_fvar : atom -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm.

Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.

Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.

Notation "<{{ x }}>" := x (x custom stlc_ty).
Notation "x" := x
  (in custom stlc_ty at level 0, x constr at level 0) : stlc_scope.
Notation "'Bool'" := Ty_Bool
  (in custom stlc_ty at level 0) : stlc_scope.
Notation "S -> T" := (Ty_Arrow S T)
  (in custom stlc_ty at level 99, right associativity) : stlc_scope.
Notation "$( t )" := t
  (in custom stlc_ty at level 0, t constr) : stlc_scope.
Notation "( T )" := T
  (in custom stlc_ty at level 0, T custom stlc_ty) : stlc_scope.

Notation "<{ e }>" := e
  (e custom stlc_tm at level 200) : stlc_scope.
Notation "$( x )" := x
  (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
Notation "x" := x
  (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "'bvar' n" := (tm_bvar n)
  (in custom stlc_tm at level 0, n constr at level 0) : stlc_scope.
Notation "'fvar' x" := (tm_fvar x)
  (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "'true'" := tm_true
  (in custom stlc_tm at level 0) : stlc_scope.
Notation "'false'" := tm_false
  (in custom stlc_tm at level 0) : stlc_scope.
Notation "( x )" := x
  (in custom stlc_tm at level 0, x custom stlc_tm) : stlc_scope.
Notation "x y" := (tm_app x y)
  (in custom stlc_tm at level 10, left associativity) : stlc_scope.
Notation "'lambda' ':' T ',' t" := (tm_abs T t)
  (in custom stlc_tm at level 200,
   T custom stlc_ty,
   t custom stlc_tm at level 200,
   left associativity) : stlc_scope.

(** Opening and local closure. *)

Fixpoint open_rec (k : nat) (u : tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => if Nat.eqb k i then u else tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_app t1 t2 => tm_app (open_rec k u t1) (open_rec k u t2)
  | tm_abs T t1 => tm_abs T (open_rec (S k) u t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Definition open (t u : tm) : tm := open_rec 0 u t.

Inductive lc_at : nat -> tm -> Prop :=
  | lc_bvar : forall k i,
      i < k ->
      lc_at k (tm_bvar i)
  | lc_fvar : forall k x,
      lc_at k (tm_fvar x)
  | lc_app : forall k t1 t2,
      lc_at k t1 ->
      lc_at k t2 ->
      lc_at k (tm_app t1 t2)
  | lc_abs : forall k T t1,
      lc_at (S k) t1 ->
      lc_at k (tm_abs T t1)
  | lc_true : forall k,
      lc_at k tm_true
  | lc_false : forall k,
      lc_at k tm_false.

Definition locally_closed (t : tm) : Prop := lc_at 0 t.

(** Call-by-value operational semantics. *)

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed (tm_abs T t) ->
      value (tm_abs T t)
  | v_true :
      value tm_true
  | v_false :
      value tm_false.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall T t v,
      locally_closed (tm_abs T t) ->
      value v ->
      tm_app (tm_abs T t) v --> open t v
  | ST_App1 : forall t1 t1' t2,
      t1 --> t1' ->
      locally_closed t2 ->
      tm_app t1 t2 --> tm_app t1' t2
  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      tm_app v1 t2 --> tm_app v1 t2'
where "t '-->' t'" := (step t t').

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

(** Typing rules. *)

Definition context := atom -> option ty.

Definition empty : context := fun _ => None.

Definition update (Gamma : context) (x : atom) (T : ty) : context :=
  fun y => if Nat.eqb x y then Some T else Gamma y.

Notation "x '|->' v ';' m" := (update m x v)
  (in custom stlc_tm at level 0,
   x constr at level 0,
   v custom stlc_ty,
   right associativity) : stlc_scope.
Notation "x '|->' v" := (update empty x v)
  (in custom stlc_tm at level 0,
   x constr at level 0,
   v custom stlc_ty) : stlc_scope.
Notation "'empty'" := empty
  (in custom stlc_tm) : stlc_scope.

Reserved Notation "<{ Gamma '|--' t '\in' T }>"
  (at level 0,
   Gamma custom stlc_tm at level 200,
   t custom stlc_tm,
   T custom stlc_ty).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      <{ Gamma |-- fvar x \in T }>
  | T_Abs : forall (L : list atom) Gamma T1 T2 t1,
      (forall x, ~ In x L ->
        <{ x |-> T1 ; Gamma |-- $(open t1 (tm_fvar x)) \in T2 }>) ->
      <{ Gamma |-- lambda : T1, $(t1) \in T1 -> T2 }>
  | T_App : forall Gamma t1 t2 T1 T2,
      <{ Gamma |-- $(t1) \in T1 -> T2 }> ->
      <{ Gamma |-- $(t2) \in T1 }> ->
      <{ Gamma |-- $(tm_app t1 t2) \in T2 }>
  | T_True : forall Gamma,
      <{ Gamma |-- true \in Bool }>
  | T_False : forall Gamma,
      <{ Gamma |-- false \in Bool }>
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

(** Target theorem: strong normalization for the supplied CBV relation. *)

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

(* ================================================================== *)
(* Strong normalization proof via a unary, type-indexed logical        *)
(* relation (reducibility candidates) adapted to call-by-value.        *)
(* ================================================================== *)

(** ** Substitution on free variables *)

Fixpoint subst (sigma : atom -> tm) (t : tm) {struct t} : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_app t1 t2 => tm_app (subst sigma t1) (subst sigma t2)
  | tm_abs T t1 => tm_abs T (subst sigma t1)
  | tm_true => tm_true
  | tm_false => tm_false
  end.

Fixpoint fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => cons x nil
  | tm_app t1 t2 => app (fvars t1) (fvars t2)
  | tm_abs _ t1 => fvars t1
  | tm_true => nil
  | tm_false => nil
  end.

Lemma subst_id : forall t, subst (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; try reflexivity; f_equal; assumption.
Qed.

(** ** Fresh atoms *)

Fixpoint max_list (l : list nat) : nat :=
  match l with
  | nil => 0
  | cons a l' => Nat.max a (max_list l')
  end.

Lemma in_max_list : forall l x, In x l -> x <= max_list l.
Proof.
  induction l as [| a l IH]; simpl; intros x H.
  - destruct H.
  - destruct H as [-> | H].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (max_list l);
        [apply IH; exact H | apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall (l : list nat), exists x : nat, ~ In x l.
Proof.
  intros l. exists (S (max_list l)). intros H.
  apply in_max_list in H.
  assert (S (max_list l) < S (max_list l)) by lia.
  exact (Nat.lt_irrefl _ H0).
Qed.

(** ** Opening of locally closed terms *)

Lemma lc_at_open_rec : forall t k,
  lc_at k t -> forall j u, k <= j -> open_rec j u t = t.
Proof.
  intros t. induction t as [n | a | t1 IH1 t2 IH2 | T1 t1 IH1 | | ];
    intros k Hlc j u Hkj; simpl.
  - inversion Hlc as [k' i Hi | | | | |]; subst.
    destruct (Nat.eqb j n) eqn:E; [| reflexivity].
    apply Nat.eqb_eq in E. lia.
  - reflexivity.
  - inversion Hlc as [| | k' a' b' H1 H2 | | |]; subst.
    rewrite (IH1 k H1 j u Hkj).
    rewrite (IH2 k H2 j u Hkj).
    reflexivity.
  - inversion Hlc as [| | | k' T' t' H1 | |]; subst.
    f_equal.
    rewrite (IH1 (S k) H1 (S j) u); [reflexivity | lia].
  - reflexivity.
  - reflexivity.
Qed.

Lemma lc_open_rec : forall t,
  locally_closed t -> forall j u, open_rec j u t = t.
Proof.
  intros t Hlc j u.
  apply (lc_at_open_rec t 0 Hlc j u). lia.
Qed.

(** ** The substitution/opening commutation lemma *)

Lemma subst_open_rec :
  forall (sigma : atom -> tm) (t : tm) (x : atom) (w : tm) (k : nat),
    ~ In x (fvars t) ->
    (forall y, locally_closed (sigma y)) ->
    subst (fun y => if Nat.eqb x y then w else sigma y)
          (open_rec k (tm_fvar x) t)
    = open_rec k w (subst sigma t).
Proof.
  intros sigma t. induction t as [n | a | t1 IH1 t2 IH2 | T1 t1 IH1 | | ];
    intros x w k Hfresh Hlc; simpl.
  - (* tm_bvar *) destruct (Nat.eqb k n) eqn:E; simpl.
    + rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - (* tm_fvar *)
    assert (Ha : x <> a) by (intro Heq; apply Hfresh; subst; simpl; auto).
    simpl.
    destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. exact (Ha E).
    + rewrite (lc_open_rec (sigma a) (Hlc a) k w). reflexivity.
  - (* tm_app *)
    simpl in Hfresh.
    assert (H1 : ~ In x (fvars t1))
      by (intro H; apply Hfresh; apply in_app_iff; left; exact H).
    assert (H2 : ~ In x (fvars t2))
      by (intro H; apply Hfresh; apply in_app_iff; right; exact H).
    rewrite (IH1 x w k H1 Hlc).
    rewrite (IH2 x w k H2 Hlc).
    reflexivity.
  - (* tm_abs *)
    f_equal.
    apply (IH1 x w (S k) Hfresh Hlc).
  - (* tm_true *) reflexivity.
  - (* tm_false *) reflexivity.
Qed.

(** ** The logical relation *)

Fixpoint lrel (T : ty) (t : tm) : Prop :=
  match T with
  | Ty_Bool => strongly_normalizing t
  | Ty_Arrow T1 T2 =>
      strongly_normalizing t /\
      (forall v, value v -> lrel T1 v -> lrel T2 (tm_app t v))
  end.

Lemma lrel_sn : forall T t, lrel T t -> strongly_normalizing t.
Proof.
  intros T; induction T; simpl; intros t H.
  - exact H.
  - exact (proj1 H).
Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v Hv. destruct Hv as [T t Hlc | | ].
  - exact Hlc.
  - apply lc_true.
  - apply lc_false.
Qed.

Lemma app_not_value : forall t1 t2, ~ value (tm_app t1 t2).
Proof. intros t1 t2 H; inversion H. Qed.

(** Inversion principle for steps out of an application. *)
Lemma step_app_inv : forall (t u r : tm),
  step (tm_app t u) r ->
  (exists T b, t = tm_abs T b /\ locally_closed (tm_abs T b) /\
               value u /\ r = open b u) \/
  (exists t', step t t' /\ r = tm_app t' u) \/
  (exists u', value t /\ step u u' /\ r = tm_app t u').
Proof.
  intros t u r H.
  inversion H as
    [ T b w Hlc Hval | t1 t1' t2 Hst Hlc | v1 t2 t2' Hval Hst ]; subst.
  - left. exists T, b. repeat split; auto.
  - right; left. exists t1'. auto.
  - right; right. exists t2'. auto.
Qed.

Lemma sn_step : forall t t',
  strongly_normalizing t -> step t t' -> strongly_normalizing t'.
Proof.
  intros t t' Hsn Hst.
  destruct Hsn as [x Hred].
  exact (Hred t' Hst).
Qed.

(** Reducibility is closed under forward reduction. *)
Lemma lrel_step : forall T t t',
  lrel T t -> step t t' -> lrel T t'.
Proof.
  intros T; induction T; intros t t' HR Hst; simpl in *.
  - apply sn_step with t; assumption.
  - destruct HR as [Hsn Harr]. split.
    + apply sn_step with t; assumption.
    + intros v Hval HRv.
      apply IHT2 with (t := tm_app t v).
      * apply Harr; assumption.
      * apply ST_App1; [assumption | apply value_lc; assumption].
Qed.

(** Non-values are reducible as soon as all their reducts are. *)
Lemma lrel_intro_nonvalue : forall T t,
  ~ value t ->
  (forall t', step t t' -> lrel T t') ->
  lrel T t.
Proof.
  intros T; induction T as [| T1 IH1 T2 IH2]; intros t Hnv Hred; simpl.
  - apply SN_intro. intros t' Hst.
    apply Hred in Hst. simpl in Hst. exact Hst.
  - split.
    + apply SN_intro. intros t' Hst.
      apply Hred in Hst. simpl in Hst. exact (proj1 Hst).
    + intros v Hval HRv.
      apply IH2.
      * apply app_not_value.
      * intros r Hstep.
        apply step_app_inv in Hstep.
        destruct Hstep as
          [ [T' [b [Heq [Hlc [Hval' Hr]]]]]
          | [ [t' [Hst1 Hr]] | [u' [Hval' [Hst2 Hr]]] ] ].
        -- (* ST_AppAbs *) exfalso. apply Hnv. rewrite Heq. apply v_abs. exact Hlc.
        -- (* ST_App1 *)
           rewrite Hr.
           pose proof (Hred t' Hst1) as Ht'.
           simpl in Ht'. apply (proj2 Ht'); assumption.
        -- (* ST_App2 *) exfalso. apply Hnv. exact Hval'.
Qed.

(** Application of a reducible function to a reducible argument. *)
Lemma lrel_app : forall T1 T2 (t u : tm),
  lrel (Ty_Arrow T1 T2) t -> lrel T1 u -> lrel T2 (tm_app t u).
Proof.
  intros T1 T2 t u Ht Hu.
  assert (Hsn : strongly_normalizing t)
    by (apply (lrel_sn (Ty_Arrow T1 T2)); exact Ht).
  revert Ht.
  revert Hu.
  revert u.
  induction Hsn as [t Hred IHout].
  intros u Hu Ht.
  assert (Hsnu : strongly_normalizing u)
    by (apply (lrel_sn T1); exact Hu).
  revert Ht.
  revert Hu.
  induction Hsnu as [u Hred_u IHin].
  intros Hu Ht.
  apply lrel_intro_nonvalue.
  - apply app_not_value.
  - intros r Hstep.
    apply step_app_inv in Hstep.
    destruct Hstep as
      [ [T' [b [Heq [Hlc [Hval Hr]]]]]
      | [ [t' [Hst1 Hr]] | [u' [Hval [Hst2 Hr]]] ] ].
    + (* ST_AppAbs *)
      rewrite Hr. subst t.
      pose proof Ht as Ht'. simpl in Ht'. destruct Ht' as [Hsn' Harr].
      apply lrel_step with (t := tm_app (tm_abs T' b) u).
      * apply Harr; assumption.
      * apply ST_AppAbs; assumption.
    + (* ST_App1 *)
      rewrite Hr.
      apply (IHout t' Hst1 u Hu).
      apply lrel_step with t; assumption.
    + (* ST_App2 *)
      rewrite Hr.
      apply (IHin u' Hst2).
      * apply lrel_step with u; assumption.
      * exact Ht.
Qed.

(** Application of an abstraction to a reducible argument. *)
Lemma lrel_app_abs : forall T1 T2 b v,
  (forall w, value w -> lrel T1 w -> lrel T2 (open b w)) ->
  lrel T1 v -> lrel T2 (tm_app (tm_abs T1 b) v).
Proof.
  intros T1 T2 b v Hb Hv.
  assert (Hsn : strongly_normalizing v)
    by (apply (lrel_sn T1); exact Hv).
  revert Hv.
  induction Hsn as [v Hred IH].
  intros Hv.
  apply lrel_intro_nonvalue.
  - apply app_not_value.
  - intros r Hstep.
    apply step_app_inv in Hstep.
    destruct Hstep as
      [ [T' [b' [Heq [Hlc [Hval Hr]]]]]
      | [ [t' [Hst1 Hr]] | [u' [Hval [Hst2 Hr]]] ] ].
    + (* ST_AppAbs *)
      rewrite Hr. injection Heq as HT Hbeq. subst T' b'.
      apply Hb; assumption.
    + (* ST_App1 *) rewrite Hr. inversion Hst1.
    + (* ST_App2 *)
      rewrite Hr.
      apply IH; [exact Hst2 | apply lrel_step with v; assumption].
Qed.

(** ** Interpretation of typing contexts *)

Definition env_rel (sigma : atom -> tm) (Gamma : context) : Prop :=
  (forall y, locally_closed (sigma y)) /\
  (forall x T, Gamma x = Some T -> lrel T (sigma x)).

Lemma env_rel_update : forall (sigma : atom -> tm) Gamma x T w,
  env_rel sigma Gamma ->
  value w ->
  lrel T w ->
  env_rel (fun y => if Nat.eqb x y then w else sigma y) (update Gamma x T).
Proof.
  intros sigma Gamma x T w [Hlc Hty] Hval Hw. split.
  - intros y. simpl. destruct (Nat.eqb x y) eqn:E.
    + apply value_lc; exact Hval.
    + apply Hlc.
  - intros y T' Hy. unfold update in Hy. simpl.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y.
      injection Hy as Heq. subst T'.
      exact Hw.
    + apply Hty. exact Hy.
Qed.

(** ** Fundamental theorem of logical relations *)

Theorem fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall sigma, env_rel sigma Gamma -> lrel T (subst sigma t).
Proof.
  intros Gamma t T Hty.
  induction Hty as
    [ Gamma0 x0 T0 Heq
    | L Gamma0 T1 T2 t1 Hprem IHAbs
    | Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2
    | Gamma0
    | Gamma0 ];
    intros sigma Henv; simpl.
  - (* T_Var *) apply (proj2 Henv). exact Heq.
  - (* T_Abs *)
    split.
    + (* strong normalization of the abstraction *)
      apply SN_intro. intros t' Hst. inversion Hst.
    + (* the arrow component *)
      intros w Hval Hw.
      apply (lrel_app_abs T1 T2 (subst sigma t1) w).
      * intros w' Hval' Hw'.
        destruct (fresh_atom (app L (fvars t1))) as [x Hx].
        assert (HxL : ~ In x L)
          by (intro Hin; apply Hx; apply in_app_iff; left; exact Hin).
        assert (Hxt : ~ In x (fvars t1))
          by (intro Hin; apply Hx; apply in_app_iff; right; exact Hin).
        pose proof (IHAbs x HxL) as IHx.
        pose proof (IHx (fun y => if Nat.eqb x y then w' else sigma y)) as Hres.
        specialize (Hres (env_rel_update sigma Gamma0 x T1 w' Henv Hval' Hw')).
        assert (Hrw :
          subst (fun y => if Nat.eqb x y then w' else sigma y)
                (open t1 (tm_fvar x))
          = open (subst sigma t1) w').
        { apply (subst_open_rec sigma t1 x w' 0 Hxt (proj1 Henv)). }
        rewrite Hrw in Hres.
        exact Hres.
      * exact Hw.
  - (* T_App *)
    apply (lrel_app T1 T2).
    + apply IH1. exact Henv.
    + apply IH2. exact Henv.
  - (* T_True *)
    apply SN_intro. intros t' Hst. inversion Hst.
  - (* T_False *)
    apply SN_intro. intros t' Hst. inversion Hst.
Qed.

(** ** The target theorem *)

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Hty.
  assert (H : lrel T (subst (fun x => tm_fvar x) t)).
  { apply (fundamental empty t T Hty (fun x => tm_fvar x)). split.
    - intros y. apply lc_fvar.
    - intros x T' Hcontra. unfold empty in Hcontra. discriminate. }
  rewrite subst_id in H.
  apply (lrel_sn T). exact H.
Qed.

End STLCNormalizationNoneHardTask.
