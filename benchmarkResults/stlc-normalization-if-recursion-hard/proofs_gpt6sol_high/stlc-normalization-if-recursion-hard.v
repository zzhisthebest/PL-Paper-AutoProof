(** STLC CBV strong-normalization benchmark, Hard variant.
    Features: if-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Relations.Relation_Definitions Lia.
Import ListNotations.

Module STLCNormalizationIfRecursionHardTask.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
      R x y ->
      multi R y z ->
      multi R x z.

Definition atom := nat.

Inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Nat : ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tm_bvar : nat -> tm
  | tm_fvar : atom -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_zero : tm
  | tm_succ : tm -> tm

  | tm_natrec : tm -> tm -> tm -> tm
  | tm_if : tm -> tm -> tm -> tm.

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
Notation "'zero'" := tm_zero
  (in custom stlc_tm at level 0) : stlc_scope.
Notation "'succ' t" := (tm_succ t)
  (in custom stlc_tm at level 9, t custom stlc_tm at level 0) : stlc_scope.
Notation "'rec' n b s" := (tm_natrec n b s)
  (in custom stlc_tm at level 9,
   n custom stlc_tm at level 0, b custom stlc_tm at level 0,
   s custom stlc_tm at level 0) : stlc_scope.
Notation "'Nat'" := Ty_Nat
  (in custom stlc_ty at level 0) : stlc_scope.

Notation "'if' t1 'then' t2 'else' t3" := (tm_if t1 t2 t3)
  (in custom stlc_tm at level 200,
   t1 custom stlc_tm, t2 custom stlc_tm, t3 custom stlc_tm at level 200) : stlc_scope.

Fixpoint open_rec (k : nat) (u : tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => if Nat.eqb k i then u else tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_app t1 t2 => tm_app (open_rec k u t1) (open_rec k u t2)
  | tm_abs T t1 => tm_abs T (open_rec (S k) u t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (open_rec k u t1)
  | tm_natrec n b s =>
      tm_natrec (open_rec k u n) (open_rec k u b) (open_rec k u s)
  | tm_if t1 t2 t3 => tm_if (open_rec k u t1) (open_rec k u t2) (open_rec k u t3)
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
      lc_at k tm_false
  | lc_zero : forall k, lc_at k tm_zero
  | lc_succ : forall k t, lc_at k t -> lc_at k (tm_succ t)
  | lc_rec : forall k n b s,
      lc_at k n -> lc_at k b -> lc_at k s ->
      lc_at k (tm_natrec n b s)
  | lc_if : forall k t1 t2 t3,
      lc_at k t1 -> lc_at k t2 -> lc_at k t3 -> lc_at k (tm_if t1 t2 t3)
  .

Definition locally_closed (t : tm) : Prop := lc_at 0 t.

Hint Constructors lc_at : core.

Inductive numeric_value : tm -> Prop :=
  | nv_zero : numeric_value tm_zero
  | nv_succ : forall (t : tm), numeric_value t -> numeric_value (tm_succ t).

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed (tm_abs T t) ->
      value (tm_abs T t)
  | v_true :
      value tm_true
  | v_false :
      value tm_false
  | v_nat : forall n, numeric_value n -> value n.

Hint Constructors value : core.

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
  | ST_Succ : forall t t',
      t --> t' -> tm_succ t --> tm_succ t'
  | ST_RecArg : forall n n' b s,

      n --> n' -> locally_closed b -> locally_closed s ->
      tm_natrec n b s --> tm_natrec n' b s
  | ST_RecBase : forall n b b' s,

      numeric_value n -> b --> b' -> locally_closed s ->
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
  | ST_IfTrue : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_if tm_true t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      locally_closed t1 ->
      locally_closed t2 ->
      tm_if tm_false t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      locally_closed t2 ->
      locally_closed t3 ->
      tm_if t1 t2 t3 --> tm_if t1' t2 t3
where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

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
  | T_Zero : forall Gamma,
      <{ Gamma |-- zero \in Nat }>
  | T_Succ : forall Gamma n,
      <{ Gamma |-- $(n) \in Nat }> ->
      <{ Gamma |-- succ $(n) \in Nat }>
  | T_Rec : forall Gamma n b s T,
      <{ Gamma |-- $(n) \in Nat }> ->
      <{ Gamma |-- $(b) \in T }> ->
      <{ Gamma |-- $(s) \in Nat -> T -> T }> ->
      <{ Gamma |-- rec $(n) $(b) $(s) \in T }>
  | T_If : forall Gamma t1 t2 t3 T,
      <{ Gamma |-- $(t1) \in Bool }> ->
      <{ Gamma |-- $(t2) \in T }> ->
      <{ Gamma |-- $(t3) \in T }> ->
      <{ Gamma |-- $(tm_if t1 t2 t3) \in T }>
where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T)
  : stlc_scope.

Hint Constructors has_type : core.

Inductive strongly_normalizing : tm -> Prop :=

  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

Lemma numeric_no_step : forall n t, numeric_value n -> n --> t -> False.
Proof.
  intros n result Hn. revert result. induction Hn; intros result H;
    inversion H; subst; eauto.
Qed.

Lemma value_no_step : forall v t, value v -> v --> t -> False.
Proof.
  intros v t Hv H. inversion Hv; subst; inversion H; subst;
    eauto using numeric_no_step.
Qed.

Fixpoint value_relation (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_Bool => v = tm_true \/ v = tm_false
  | Ty_Nat => numeric_value v
  | Ty_Arrow A B =>
      value v /\ forall a, value_relation A a ->
        forall r, tm_app v a --> r ->
          strongly_normalizing r /\
          (forall w, r -->* w -> value w -> value_relation B w)
  end.

Definition reducible (T : ty) (t : tm) : Prop :=
  strongly_normalizing t /\
  forall v, t -->* v -> value v -> value_relation T v.

Lemma relation_value : forall T v, value_relation T v -> value v.
Proof.
  intros T v H. destruct T; simpl in H.
  - destruct H as [H|H]; subst; constructor.
  - constructor; exact H.
  - exact (proj1 H).
Qed.

Lemma reducible_value : forall T v, value v ->
  (reducible T v <-> value_relation T v).
Proof.
  intros T v Hv; split.
  - intros H. apply (proj2 H v); auto. constructor.
  - intros H. split.
    + constructor. intros t Hstep. exfalso; eauto using value_no_step.
    + intros w Hmulti Hw. inversion Hmulti; subst; auto.
      exfalso; eauto using value_no_step.
Qed.

Lemma reducible_neutral : forall T t,
  ~ value t ->
  (forall t', t --> t' -> reducible T t') -> reducible T t.
Proof.
  intros T t Hnv Hstep. split.
  - constructor. intros t' H. exact (proj1 (Hstep t' H)).
  - intros v Hmulti Hv. inversion Hmulti; subst.
    + exfalso; eauto.
    + exact (proj2 (Hstep _ H) _ H0 Hv).
Qed.

Lemma app_not_value : forall t u, ~ value (tm_app t u).
Proof. intros t u H; inversion H; inversion H0. Qed.
Lemma rec_not_value : forall n b s, ~ value (tm_natrec n b s).
Proof. intros n b s H; inversion H; inversion H0. Qed.
Lemma if_not_value : forall t u v, ~ value (tm_if t u v).
Proof. intros t u v H; inversion H; inversion H0. Qed.

Lemma reducible_app : forall A B t u,
  reducible (Ty_Arrow A B) t -> reducible A u ->
  reducible B (tm_app t u).
Proof.
  intros A B t u Ht Hu.
  destruct Ht as [Hsn_t Hval_t]. destruct Hu as [Hsn_u Hval_u].
  revert u Hsn_u Hval_u.
  induction Hsn_t as [t Hnext_t IHt]; intros u Hsn_u Hval_u.
  induction Hsn_u as [u Hnext_u IHu].
  apply reducible_neutral; [apply app_not_value|].
  intros r Hstep; inversion Hstep; subst.
  - assert (Hfun : value_relation (Ty_Arrow A B) (tm_abs T t0)).
    { apply Hval_t; auto. constructor. }
    assert (Harg : value_relation A u).
    { apply Hval_u; auto. constructor. }
    exact (proj2 Hfun _ Harg _ Hstep).
  - apply (IHt _ H1).
    + intros v Hmulti Hv. apply Hval_t with (v := v); auto.
      econstructor; eauto.
    + exact (SN_intro _ Hnext_u).
    + exact Hval_u.
  - eapply IHu; [eassumption|].
    intros v Hmulti Hv. apply Hval_u with (v := v); auto.
    econstructor; eauto.
Qed.

Lemma numeric_reducible : forall n, numeric_value n -> reducible Ty_Nat n.
Proof.
  intros n H. apply reducible_value.
  - constructor; exact H.
  - exact H.
Qed.

Lemma reducible_if : forall T c t e,
  reducible Ty_Bool c -> reducible T t -> reducible T e ->
  locally_closed t -> locally_closed e ->
  reducible T (tm_if c t e).
Proof.
  intros T c t e Hc Ht He Hlc_t Hlc_e.
  destruct Hc as [Hsn Hval]. induction Hsn as [c Hnext IH].
  apply reducible_neutral; [apply if_not_value|].
  intros r Hstep; inversion Hstep; subst; auto.
  apply IH; auto. intros v Hmulti Hv. apply Hval with (v := v); auto.
  econstructor; eauto.
Qed.

Lemma reducible_succ : forall n,
  reducible Ty_Nat n -> reducible Ty_Nat (tm_succ n).
Proof.
  intros n [Hsn Hval]. induction Hsn as [n Hnext IH]. split.
  - constructor. intros r Hstep. inversion Hstep; subst.
    exact (proj1 (IH _ H0 (fun v Hmulti Hv =>
      Hval v (multi_step _ _ _ _ H0 Hmulti) Hv))).
  - intros v Hmulti Hv. inversion Hmulti; subst.
    + inversion Hv; subst; assumption.
    + inversion H; subst.
      exact (proj2 (IH _ H2 (fun w Hpath Hw =>
        Hval w (multi_step _ _ _ _ H2 Hpath) Hw)) _ H0 Hv).
Qed.

Fixpoint numeric_dec (n : tm) : {numeric_value n} + {~ numeric_value n}.
Proof.
  destruct n; try solve [right; intro H; inversion H].
  - left; constructor.
  - destruct (numeric_dec n) as [H|H].
    + left; constructor; exact H.
    + right; intro Hnv; inversion Hnv; subst; contradiction.
Defined.

Lemma reducible_rec_numeric : forall n, numeric_value n ->
  forall T b s, reducible T b -> reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros n Hnv. induction Hnv as [|n Hnv IH]; intros T b s Hb Hs.
  all: destruct Hb as [Hsn_b Hval_b]; destruct Hs as [Hsn_s Hval_s].
  all: revert s Hsn_s Hval_s; induction Hsn_b as [b Hnext_b IHb];
    intros s Hsn_s Hval_s; induction Hsn_s as [s Hnext_s IHs].
  all: apply reducible_neutral; [apply rec_not_value|];
    intros r Hstep; inversion Hstep; subst;
    try solve [exfalso; eapply numeric_no_step;
      [constructor; eauto | eassumption]].
  all: try (eapply IHb;
    [eassumption
    |intros v Hpath Hv; eapply Hval_b; [econstructor; eauto|exact Hv]
    |exact (SN_intro _ Hnext_s)
    |exact Hval_s]).
  all: try (eapply IHs; [eassumption|];
    intros v Hpath Hv; eapply Hval_s; [econstructor; eauto|exact Hv]).
  all: try (apply reducible_value; [assumption|];
    apply Hval_b; [constructor|assumption]).
  eapply reducible_app with (A := T).
  - eapply reducible_app with (A := Ty_Nat).
    + split; [constructor; exact Hnext_s|exact Hval_s].
    + apply numeric_reducible; exact Hnv.
  - apply IH.
    + split; [constructor; exact Hnext_b|exact Hval_b].
    + split; [constructor; exact Hnext_s|exact Hval_s].
Qed.

Lemma reducible_rec : forall T n b s,
  reducible Ty_Nat n -> reducible T b ->
  reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  reducible T (tm_natrec n b s).
Proof.
  intros T n b s [Hsn Hval]. induction Hsn as [n Hnext IH]; intros Hb Hs.
  destruct (numeric_dec n) as [Hnumeric|Hnon].
  - eapply reducible_rec_numeric; eauto.
  - apply reducible_neutral; [apply rec_not_value|].
    intros r Hstep; inversion Hstep; subst;
      try solve [exfalso; apply Hnon; assumption |
                 exfalso; apply Hnon; constructor; eauto].
    apply IH; auto. intros v Hpath Hv.
    eapply Hval; [econstructor; eauto|exact Hv].
Qed.

Fixpoint free_vars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_app t u => free_vars t ++ free_vars u
  | tm_abs _ t => free_vars t
  | tm_true | tm_false | tm_zero => []
  | tm_succ t => free_vars t
  | tm_natrec n b s => free_vars n ++ free_vars b ++ free_vars s
  | tm_if c t e => free_vars c ++ free_vars t ++ free_vars e
  end.

Fixpoint substitute (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_app t u => tm_app (substitute rho t) (substitute rho u)
  | tm_abs T t => tm_abs T (substitute rho t)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_zero => tm_zero
  | tm_succ t => tm_succ (substitute rho t)
  | tm_natrec n b s => tm_natrec (substitute rho n) (substitute rho b) (substitute rho s)
  | tm_if c t e => tm_if (substitute rho c) (substitute rho t) (substitute rho e)
  end.

Lemma fresh_bound : forall xs x, In x xs -> x <= fold_right Nat.max 0 xs.
Proof.
  induction xs as [|a xs IH]; intros x H; simpl in *.
  - contradiction.
  - destruct H as [H|H]; subst; [lia|]. specialize (IH _ H); lia.
Qed.

Lemma fresh_not_in : forall xs,
  ~ In (S (fold_right Nat.max 0 xs)) xs.
Proof.
  intros xs H. pose proof (fresh_bound xs _ H). lia.
Qed.

Lemma lc_open_inverse : forall t k u,
  lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  induction t; intros k u H; simpl in H;
    try solve [inversion H; subst; constructor; eauto].
  destruct (Nat.eqb k n) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst; constructor; lia.
    + inversion H; subst; constructor; lia.
Qed.

Lemma lc_weaken : forall k t, lc_at k t -> forall j, k <= j -> lc_at j t.
Proof.
  intros k t H. induction H; intros j Hj;
    try solve [econstructor; eauto].
  - apply lc_bvar; lia.
  - apply lc_abs. apply IHlc_at; lia.
Qed.

Lemma numeric_lc : forall n, numeric_value n -> locally_closed n.
Proof. intros n H; induction H; constructor; auto. Qed.

Lemma value_lc : forall v, value v -> locally_closed v.
Proof.
  intros v H; induction H; eauto using numeric_lc; constructor.
Qed.

Lemma substitute_lc : forall k t rho,
  lc_at k t -> (forall x, locally_closed (rho x)) ->
  lc_at k (substitute rho t).
Proof.
  intros k t rho H. induction H; intros Hrho; simpl;
    try solve [constructor; eauto].
  apply (lc_weaken 0); [apply Hrho|lia].
Qed.

Lemma open_closed : forall k t, lc_at k t -> forall j u,
  k <= j -> open_rec j u t = t.
Proof.
  intros k t H. induction H; intros j u Hj; simpl;
    try solve [f_equal; eauto].
  - destruct (Nat.eqb j i) eqn:Heq; [apply Nat.eqb_eq in Heq; lia|reflexivity].
  - f_equal. apply IHlc_at; lia.
Qed.

Lemma not_in_append : forall x (left right : list atom),
  ~ In x (left ++ right) -> ~ In x left /\ ~ In x right.
Proof.
  intros x left right H; split; intro Hin; apply H; apply in_or_app; auto.
Qed.

Lemma substitute_open : forall t k rho x v,
  (forall y, locally_closed (rho y)) -> ~ In x (free_vars t) ->
  substitute (fun y => if Nat.eqb x y then v else rho y)
    (open_rec k (tm_fvar x) t) = open_rec k v (substitute rho t).
Proof.
  induction t; intros k rho x v Hrho Hfresh; simpl in *.
  - destruct (Nat.eqb k n); simpl; [rewrite Nat.eqb_refl|]; reflexivity.
  - assert (x <> a) by (intro Heq; apply Hfresh; simpl; left; symmetry; exact Heq).
    apply Nat.eqb_neq in H. rewrite H.
    symmetry. apply (open_closed 0 (rho a) (Hrho a)); lia.
  - apply not_in_append in Hfresh as [H1 H2].
    simpl. f_equal; [apply IHt1|apply IHt2]; auto.
  - simpl. f_equal. apply IHt; auto.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. f_equal. apply IHt; auto.
  - apply not_in_append in Hfresh as [H1 Hrest].
    apply not_in_append in Hrest as [H2 H3].
    simpl. f_equal; [apply IHt1|apply IHt2|apply IHt3]; auto.
  - apply not_in_append in Hfresh as [H1 Hrest].
    apply not_in_append in Hrest as [H2 H3].
    simpl. f_equal; [apply IHt1|apply IHt2|apply IHt3]; auto.
Qed.

Lemma typing_lc : forall Gamma t T, has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Htype. induction Htype as
    [Gamma x T Hlookup
    |L Gamma A B body Hbody IHbody
    |Gamma t u A B Ht IHt Hu IHu
    |Gamma |Gamma |Gamma
    |Gamma n Hn IHn
    |Gamma n b s T Hn IHn Hb IHb Hs IHs
    |Gamma c t e T Hc IHc Ht IHt He IHe];
    try solve [constructor; eauto].
  set (x := S (fold_right Nat.max 0 L)).
  assert (Hfresh : ~ In x L) by (unfold x; apply fresh_not_in).
  apply lc_abs. apply (lc_open_inverse body 0 (tm_fvar x)).
  exact (IHbody x Hfresh).
Qed.

Definition environment (Gamma : context) (rho : atom -> tm) : Prop :=
  (forall x, locally_closed (rho x)) /\
  (forall x T, Gamma x = Some T -> value_relation T (rho x)).

Lemma environment_extend : forall Gamma rho x A v,
  environment Gamma rho -> value_relation A v ->
  environment (update Gamma x A)
    (fun y => if Nat.eqb x y then v else rho y).
Proof.
  intros Gamma rho x A v [Hlc Hrel] Hv. split.
  - intros y. destruct (Nat.eqb x y); auto.
    apply value_lc. eapply relation_value; eauto.
  - intros y T Hlookup. unfold update in Hlookup.
    destruct (Nat.eqb x y) eqn:Heq.
    + inversion Hlookup; subst; exact Hv.
    + apply Hrel; exact Hlookup.
Qed.

Lemma fundamental : forall Gamma t T,
  has_type Gamma t T ->
  forall rho, environment Gamma rho -> reducible T (substitute rho t).
Proof.
  intros Gamma t T Htype. induction Htype as
    [Gamma x T Hlookup
    |L Gamma A B body Hbody IHbody
    |Gamma t u A B Ht IHt Hu IHu
    |Gamma |Gamma |Gamma
    |Gamma n Hn IHn
    |Gamma n b s T Hn IHn Hb IHb Hs IHs
    |Gamma c t e T Hc IHc Ht IHt He IHe];
    intros rho Henv; simpl.
  - apply reducible_value.
    + apply relation_value with T. apply (proj2 Henv x T); exact Hlookup.
    + apply (proj2 Henv x T); exact Hlookup.
  - assert (Hlc_body : lc_at 1 body).
    { pose proof (typing_lc _ _ _ (T_Abs L Gamma A B body Hbody)) as Hlc.
      inversion Hlc; assumption. }
    assert (Hlc_abs : locally_closed (tm_abs A (substitute rho body))).
    { constructor. apply substitute_lc; [exact Hlc_body|exact (proj1 Henv)]. }
    apply reducible_value.
    + constructor; exact Hlc_abs.
    + simpl. split.
      * constructor; exact Hlc_abs.
      * intros arg Harg result Hstep.
        set (x := S (fold_right Nat.max 0 (L ++ free_vars body))).
        assert (Hfresh : ~ In x (L ++ free_vars body))
          by (unfold x; apply fresh_not_in).
        apply not_in_append in Hfresh as [Hfresh_L Hfresh_body].
        specialize (IHbody x Hfresh_L
          (fun y => if Nat.eqb x y then arg else rho y)
          (environment_extend Gamma rho x A arg Henv Harg)).
        unfold open in IHbody.
        rewrite (substitute_open body 0 rho x arg (proj1 Henv) Hfresh_body)
          in IHbody.
        inversion Hstep; subst.
        -- exact IHbody.
        -- exfalso. eapply value_no_step; [constructor; exact Hlc_abs|eassumption].
        -- exfalso. eapply value_no_step; [eapply relation_value; eauto|eassumption].
  - apply reducible_app with (A := A); auto.
  - apply reducible_value; [constructor|simpl; auto].
  - apply reducible_value; [constructor|simpl; auto].
  - apply numeric_reducible; constructor.
  - apply reducible_succ; auto.
  - apply reducible_rec with (T := T); auto.
  - eapply reducible_if; eauto.
    + apply substitute_lc; [eapply typing_lc; exact Ht|exact (proj1 Henv)].
    + apply substitute_lc; [eapply typing_lc; exact He|exact (proj1 Henv)].
Qed.

Lemma free_vars_open : forall t k u x,
  In x (free_vars t) -> In x (free_vars (open_rec k u t)).
Proof.
  induction t; intros k u x Hin; simpl in *; try contradiction;
    try solve [exact Hin | eauto].
  - apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff;
      [left; apply IHt1|right; apply IHt2]; exact Hin.
  - repeat rewrite in_app_iff in *.
    destruct Hin as [Hin|[Hin|Hin]];
      [left; apply IHt1|right; left; apply IHt2|right; right; apply IHt3]; exact Hin.
  - repeat rewrite in_app_iff in *.
    destruct Hin as [Hin|[Hin|Hin]];
      [left; apply IHt1|right; left; apply IHt2|right; right; apply IHt3]; exact Hin.
Qed.

Lemma typing_free : forall Gamma t T,
  has_type Gamma t T ->
  forall x, In x (free_vars t) -> exists U, Gamma x = Some U.
Proof.
  intros Gamma t T Htype. induction Htype as
    [Gamma y T Hlookup
    |L Gamma A B body Hbody IHbody
    |Gamma t u A B Ht IHt Hu IHu
    |Gamma |Gamma |Gamma
    |Gamma n Hn IHn
    |Gamma n b s T Hn IHn Hb IHb Hs IHs
    |Gamma c t e T Hc IHc Ht IHt He IHe];
    intros x Hin; simpl in Hin; try contradiction.
  - destruct Hin as [Heq|[]]; subst; eauto.
  - set (y := S (fold_right Nat.max 0 (L ++ [x]))).
    assert (Hfresh : ~ In y (L ++ [x])) by (unfold y; apply fresh_not_in).
    apply not_in_append in Hfresh as [HnotL HnotX].
    destruct (IHbody y HnotL x
      (free_vars_open body 0 (tm_fvar y) x Hin)) as [U HU].
    exists U. unfold update in HU.
    assert (y <> x) by (intro Heq; apply HnotX; simpl; auto).
    apply Nat.eqb_neq in H. rewrite H in HU. exact HU.
  - apply in_app_iff in Hin as [Hin|Hin]; [apply IHt|apply IHu]; exact Hin.
  - apply IHn; exact Hin.
  - repeat rewrite in_app_iff in Hin.
    destruct Hin as [Hin|[Hin|Hin]];
      [apply IHn|apply IHb|apply IHs]; exact Hin.
  - repeat rewrite in_app_iff in Hin.
    destruct Hin as [Hin|[Hin|Hin]];
      [apply IHc|apply IHt|apply IHe]; exact Hin.
Qed.

Lemma substitute_closed : forall t rho,
  (forall x, ~ In x (free_vars t)) -> substitute rho t = t.
Proof.
  induction t; intros rho Hfresh; simpl in *; try reflexivity.
  - exfalso. apply (Hfresh a). simpl; auto.
  - f_equal; [apply IHt1|apply IHt2];
      intros x Hin; apply (Hfresh x); apply in_or_app; auto.
  - f_equal. apply IHt; exact Hfresh.
  - f_equal. apply IHt; exact Hfresh.
  - f_equal.
    + apply IHt1. intros x Hin. apply (Hfresh x).
      repeat rewrite in_app_iff; auto.
    + apply IHt2. intros x Hin. apply (Hfresh x).
      repeat rewrite in_app_iff; auto.
    + apply IHt3. intros x Hin. apply (Hfresh x).
      repeat rewrite in_app_iff; auto.
  - f_equal.
    + apply IHt1. intros x Hin. apply (Hfresh x).
      repeat rewrite in_app_iff; auto.
    + apply IHt2. intros x Hin. apply (Hfresh x).
      repeat rewrite in_app_iff; auto.
    + apply IHt3. intros x Hin. apply (Hfresh x).
      repeat rewrite in_app_iff; auto.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> ->
  strongly_normalizing t.
Proof.
  intros t T Htype.
  pose (rho := fun _ : atom => tm_true).
  assert (Henv : environment empty rho).
  { split.
    - intros x; constructor.
    - intros x U Hlookup. discriminate Hlookup. }
  assert (Hclosed : substitute rho t = t).
  { apply substitute_closed. intros x Hin.
    destruct (typing_free _ _ _ Htype x Hin) as [U HU].
    discriminate HU. }
  rewrite <- Hclosed. exact (proj1 (fundamental _ _ _ Htype rho Henv)).
Qed.

End STLCNormalizationIfRecursionHardTask.
