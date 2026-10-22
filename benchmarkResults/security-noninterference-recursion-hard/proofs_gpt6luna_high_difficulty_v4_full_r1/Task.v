From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From Stdlib Require Import Program.Equality.
Import ListNotations.
Reserved Notation "t '-->' t'" (at level 40).

Inductive label : Type := Low | High.

Definition flows_to (l1 l2 : label) : Prop :=
  match l1, l2 with
  | High, Low => False
  | _, _ => True
  end.

Definition join (l1 l2 : label) : label :=
  match l1, l2 with
  | Low, Low => Low
  | _, _ => High
  end.

Record security : Type := {
  reader : label;
  indirect_reader : label
}.

Definition wf_security (kappa : security) : Prop :=
  flows_to kappa.(indirect_reader) kappa.(reader).

Definition security_le (kappa1 kappa2 : security) : Prop :=
  flows_to kappa1.(reader) kappa2.(reader) /\
  flows_to kappa1.(indirect_reader) kappa2.(indirect_reader).

Definition public : security :=
  {| reader := Low; indirect_reader := Low |}.

Definition secret : security :=
  {| reader := High; indirect_reader := High |}.

Definition protect_security (kappa : security) (l : label) : security :=
  {| reader := join kappa.(reader) l;
     indirect_reader := join kappa.(indirect_reader) l |}.

Lemma security_le_protect : forall k1 k2 l,
  security_le k1 k2 -> security_le (protect_security k1 l) (protect_security k2 l).
Proof.
  intros [r1 i1] [r2 i2] l H. destruct l, r1, r2, i1, i2;
    unfold security_le, protect_security, flows_to, join in *; simpl in *; intuition.
Qed.

Inductive ty : Type :=
  | Ty_Unit : security -> ty
  | Ty_Sum : ty -> ty -> security -> ty
  | Ty_Prod : ty -> ty -> security -> ty
  | Ty_Arrow : ty -> ty -> security -> ty
  | Ty_Nat : security -> ty.

Definition security_of (T : ty) : security :=
  match T with
  | Ty_Unit kappa | Ty_Nat kappa => kappa
  | Ty_Sum _ _ kappa | Ty_Prod _ _ kappa | Ty_Arrow _ _ kappa => kappa
  end.

Definition ty_protect (l : label) (T : ty) : ty :=
  match T with
  | Ty_Unit kappa => Ty_Unit (protect_security kappa l)
  | Ty_Nat kappa => Ty_Nat (protect_security kappa l)
  | Ty_Sum T1 T2 kappa => Ty_Sum T1 T2 (protect_security kappa l)
  | Ty_Prod T1 T2 kappa => Ty_Prod T1 T2 (protect_security kappa l)
  | Ty_Arrow T1 T2 kappa => Ty_Arrow T1 T2 (protect_security kappa l)
  end.

Lemma ty_protect_low : forall T, ty_protect Low T = T.
Proof. destruct T; simpl; try reflexivity; destruct s as [r i]; destruct r, i; reflexivity. Qed.

Fixpoint wf_ty (T : ty) : Prop :=
  match T with
  | Ty_Unit kappa | Ty_Nat kappa => wf_security kappa
  | Ty_Sum T1 T2 kappa | Ty_Prod T1 T2 kappa | Ty_Arrow T1 T2 kappa =>
      wf_ty T1 /\ wf_ty T2 /\ wf_security kappa
  end.

Definition atom := nat.

Inductive tm : Type :=
  | tm_bvar : nat -> tm
  | tm_fvar : atom -> tm
  | tm_unit : security -> tm
  | tm_abs : ty -> tm -> security -> tm
  | tm_app : tm -> tm -> label -> tm
  | tm_pair : tm -> tm -> security -> tm
  | tm_fst : tm -> label -> tm
  | tm_snd : tm -> label -> tm
  | tm_inl : tm -> security -> tm
  | tm_inr : tm -> security -> tm
  | tm_case : tm -> tm -> tm -> label -> tm
  | tm_protect : label -> tm -> tm
  | tm_nat : nat -> security -> tm
  | tm_succ : tm -> label -> tm
  | tm_natrec : tm -> tm -> tm -> label -> tm.

Fixpoint open_rec (k : nat) (u t : tm) : tm :=
  match t with
  | tm_bvar i => if Nat.eqb k i then u else tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_unit kappa => tm_unit kappa
  | tm_abs T body kappa => tm_abs T (open_rec (S k) u body) kappa
  | tm_app t1 t2 r => tm_app (open_rec k u t1) (open_rec k u t2) r
  | tm_pair t1 t2 kappa => tm_pair (open_rec k u t1) (open_rec k u t2) kappa
  | tm_fst t1 r => tm_fst (open_rec k u t1) r
  | tm_snd t1 r => tm_snd (open_rec k u t1) r
  | tm_inl t1 kappa => tm_inl (open_rec k u t1) kappa
  | tm_inr t1 kappa => tm_inr (open_rec k u t1) kappa
  | tm_case t0 body1 body2 r =>
      tm_case (open_rec k u t0)
        (open_rec (S k) u body1) (open_rec (S k) u body2) r
  | tm_protect l t1 => tm_protect l (open_rec k u t1)
  | tm_nat n s => tm_nat n s
  | tm_succ t r => tm_succ (open_rec k u t) r
  | tm_natrec n b s r => tm_natrec (open_rec k u n) (open_rec k u b) (open_rec k u s) r
  end.

Definition open (body u : tm) : tm := open_rec 0 u body.

Fixpoint subst (x : atom) (u t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar y => if Nat.eqb x y then u else tm_fvar y
  | tm_unit kappa => tm_unit kappa
  | tm_abs T body kappa => tm_abs T (subst x u body) kappa
  | tm_app t1 t2 r => tm_app (subst x u t1) (subst x u t2) r
  | tm_pair t1 t2 kappa => tm_pair (subst x u t1) (subst x u t2) kappa
  | tm_fst t1 r => tm_fst (subst x u t1) r
  | tm_snd t1 r => tm_snd (subst x u t1) r
  | tm_inl t1 kappa => tm_inl (subst x u t1) kappa
  | tm_inr t1 kappa => tm_inr (subst x u t1) kappa
  | tm_case t0 body1 body2 r =>
      tm_case (subst x u t0) (subst x u body1) (subst x u body2) r
  | tm_protect l t1 => tm_protect l (subst x u t1)
  | tm_nat n s => tm_nat n s
  | tm_succ t r => tm_succ (subst x u t) r
  | tm_natrec n b s r => tm_natrec (subst x u n) (subst x u b) (subst x u s) r
  end.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_unit _ | tm_nat _ _ => []
  | tm_fvar x => [x]
  | tm_abs _ body _ => fv body
  | tm_app t1 t2 _ | tm_pair t1 t2 _ => fv t1 ++ fv t2
  | tm_fst t1 _ | tm_snd t1 _ | tm_inl t1 _ | tm_inr t1 _
  | tm_protect _ t1 | tm_succ t1 _ => fv t1
  | tm_natrec n b s _ => fv n ++ fv b ++ fv s
  | tm_case t0 body1 body2 _ => fv t0 ++ fv body1 ++ fv body2
  end.

Fixpoint lc_at (k : nat) (t : tm) : Prop :=
  match t with
  | tm_bvar i => i < k
  | tm_fvar _ | tm_unit _ | tm_nat _ _ => True
  | tm_abs _ body _ => lc_at (S k) body
  | tm_app t1 t2 _ | tm_pair t1 t2 _ => lc_at k t1 /\ lc_at k t2
  | tm_fst t1 _ | tm_snd t1 _ | tm_inl t1 _ | tm_inr t1 _
  | tm_protect _ t1 | tm_succ t1 _ => lc_at k t1
  | tm_natrec n b s _ => lc_at k n /\ lc_at k b /\ lc_at k s
  | tm_case t0 body1 body2 _ =>
      lc_at k t0 /\ lc_at (S k) body1 /\ lc_at (S k) body2
  end.

Definition locally_closed (t : tm) : Prop := lc_at 0 t.

Definition closed (t : tm) : Prop := locally_closed t /\ fv t = [].

Inductive value : tm -> Prop :=
  | v_unit : forall kappa, value (tm_unit kappa)
  | v_abs : forall T body kappa,
      locally_closed (tm_abs T body kappa) -> value (tm_abs T body kappa)
  | v_pair : forall v1 v2 kappa,
      value v1 -> value v2 -> value (tm_pair v1 v2 kappa)
  | v_inl : forall v kappa, value v -> value (tm_inl v kappa)
  | v_inr : forall v kappa, value v -> value (tm_inr v kappa)
  | v_nat : forall n kappa, value (tm_nat n kappa).

Definition protect_value (v : tm) (l : label) : tm :=
  match v with
  | tm_unit kappa => tm_unit (protect_security kappa l)
  | tm_abs T body kappa => tm_abs T body (protect_security kappa l)
  | tm_pair v1 v2 kappa => tm_pair v1 v2 (protect_security kappa l)
  | tm_inl v1 kappa => tm_inl v1 (protect_security kappa l)
  | tm_inr v1 kappa => tm_inr v1 (protect_security kappa l)
  | tm_nat n kappa => tm_nat n (protect_security kappa l)
  | _ => v
  end.

Definition context := list (atom * ty).

Definition empty : context := [].

Fixpoint lookup_context (x : atom) (Gamma : context) : option ty :=
  match Gamma with
  | [] => None
  | (y, T) :: Gamma' =>
      if Nat.eqb x y then Some T else lookup_context x Gamma'
  end.

Definition update (Gamma : context) (x : atom) (T : ty) : context :=
  (x, T) :: Gamma.

Definition context_wf (Gamma : context) : Prop :=
  forall (x : atom) (T : ty), lookup_context x Gamma = Some T -> wf_ty T.

Fixpoint erase_type (T : ty) : ty :=
  match T with
  | Ty_Unit _ => Ty_Unit public
  | Ty_Nat _ => Ty_Nat public
  | Ty_Sum T1 T2 _ => Ty_Sum (erase_type T1) (erase_type T2) public
  | Ty_Prod T1 T2 _ => Ty_Prod (erase_type T1) (erase_type T2) public
  | Ty_Arrow T1 T2 _ => Ty_Arrow (erase_type T1) (erase_type T2) public
  end.

Fixpoint erase_security (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_unit _ => tm_unit public
  | tm_abs T body _ => tm_abs (erase_type T) (erase_security body) public
  | tm_app t1 t2 _ => tm_app (erase_security t1) (erase_security t2) Low
  | tm_pair t1 t2 _ => tm_pair (erase_security t1) (erase_security t2) public
  | tm_fst t1 _ => tm_fst (erase_security t1) Low
  | tm_snd t1 _ => tm_snd (erase_security t1) Low
  | tm_inl t1 _ => tm_inl (erase_security t1) public
  | tm_inr t1 _ => tm_inr (erase_security t1) public
  | tm_case t0 body1 body2 _ =>
      tm_case (erase_security t0) (erase_security body1) (erase_security body2) Low
  | tm_protect _ t1 => erase_security t1
  | tm_nat n _ => tm_nat n public
  | tm_succ t _ => tm_succ (erase_security t) Low
  | tm_natrec n b s _ => tm_natrec (erase_security n) (erase_security b) (erase_security s) Low
  end.

Lemma erase_protect_value : forall v l,
  erase_security (protect_value v l) = erase_security v.
Proof. destruct v; reflexivity. Qed.

Lemma protect_value_low : forall v, protect_value v Low = v.
Proof. destruct v; simpl; try reflexivity; destruct s as [r i]; destruct r, i; reflexivity. Qed.

Lemma value_protect_value : forall v l,
  value v -> value (protect_value v l).
Proof.
  intros v l Hv. inversion Hv; subst; simpl; try constructor; assumption.
Qed.

Lemma value_locally_closed : forall v, value v -> locally_closed v.
Proof. intros v H; induction H; unfold locally_closed in *; simpl in *; auto. Qed.

Fixpoint natrec_unroll (n : nat) (base step_function : tm) (r : label) : tm :=
  match n with
  | O => base
  | S k => tm_app (tm_app step_function (tm_nat k public) r)
                  (natrec_unroll k base step_function r) r
  end.

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall T body kappa v r,
      value (tm_abs T body kappa) -> value v ->
      flows_to kappa.(reader) r ->
      tm_app (tm_abs T body kappa) v r -->
        tm_protect kappa.(indirect_reader) (open body v)
  | ST_App1 : forall t1 t1' t2 r,
      t1 --> t1' -> tm_app t1 t2 r --> tm_app t1' t2 r
  | ST_App2 : forall v1 t2 t2' r,
      value v1 -> t2 --> t2' -> tm_app v1 t2 r --> tm_app v1 t2' r
  | ST_Pair1 : forall t1 t1' t2 kappa,
      t1 --> t1' -> tm_pair t1 t2 kappa --> tm_pair t1' t2 kappa
  | ST_Pair2 : forall v1 t2 t2' kappa,
      value v1 -> t2 --> t2' -> tm_pair v1 t2 kappa --> tm_pair v1 t2' kappa
  | ST_FstPair : forall v1 v2 kappa r,
      value v1 -> value v2 -> flows_to kappa.(reader) r ->
      tm_fst (tm_pair v1 v2 kappa) r --> tm_protect kappa.(indirect_reader) v1
  | ST_Fst : forall t t' r,
      t --> t' -> tm_fst t r --> tm_fst t' r
  | ST_SndPair : forall v1 v2 kappa r,
      value v1 -> value v2 -> flows_to kappa.(reader) r ->
      tm_snd (tm_pair v1 v2 kappa) r --> tm_protect kappa.(indirect_reader) v2
  | ST_Snd : forall t t' r,
      t --> t' -> tm_snd t r --> tm_snd t' r
  | ST_Inl : forall t t' kappa,
      t --> t' -> tm_inl t kappa --> tm_inl t' kappa
  | ST_Inr : forall t t' kappa,
      t --> t' -> tm_inr t kappa --> tm_inr t' kappa
  | ST_CaseLeft : forall v kappa body1 body2 r,
      value v -> flows_to kappa.(reader) r ->
      tm_case (tm_inl v kappa) body1 body2 r -->
        tm_protect kappa.(indirect_reader) (open body1 v)
  | ST_CaseRight : forall v kappa body1 body2 r,
      value v -> flows_to kappa.(reader) r ->
      tm_case (tm_inr v kappa) body1 body2 r -->
        tm_protect kappa.(indirect_reader) (open body2 v)
  | ST_Case : forall t t' body1 body2 r,
      t --> t' -> tm_case t body1 body2 r --> tm_case t' body1 body2 r
  | ST_ProtectValue : forall l v,
      value v -> tm_protect l v --> protect_value v l
  | ST_Protect : forall l t t',
      t --> t' -> tm_protect l t --> tm_protect l t'
  | ST_Succ : forall t t' r,
      t --> t' -> tm_succ t r --> tm_succ t' r
  | ST_SuccNat : forall n k r,
      flows_to k.(reader) r ->
      tm_succ (tm_nat n k) r --> tm_protect k.(indirect_reader) (tm_nat (S n) public)
  | ST_RecArg : forall n n' b s r,
      n --> n' -> tm_natrec n b s r --> tm_natrec n' b s r
  | ST_RecBase : forall n k b b' s r,
      b --> b' -> tm_natrec (tm_nat n k) b s r --> tm_natrec (tm_nat n k) b' s r
  | ST_RecStep : forall n k b s s' r,
      value b -> s --> s' -> tm_natrec (tm_nat n k) b s r --> tm_natrec (tm_nat n k) b s' r
  | ST_RecUnroll : forall n k b s r,
      value b -> value s -> flows_to k.(reader) r ->
      tm_natrec (tm_nat n k) b s r --> tm_protect k.(indirect_reader) (natrec_unroll n b s r)
where "t '-->' t'" := (step t t').

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall t, multi t t
  | multi_step : forall t1 t2 t3,
      step t1 t2 -> multi t2 t3 -> multi t1 t3.

Notation "t '-->*' t'" := (multi t t') (at level 40).

Lemma value_no_step : forall v t, value v -> ~ step v t.
Proof. intros v t Hv; revert t; induction Hv; intros t Hs; inversion Hs; subst; eauto.
  all: match goal with
       | IH : forall x, ~ step ?v x, Hstep : step ?v ?w |- False =>
           exact (IH w Hstep)
       end.
Qed.

Lemma multi_from_value : forall v w, value v -> multi v w -> v = w.
Proof.
  intros v w Hv Hm; induction Hm; auto.
  exfalso. eapply value_no_step; eauto.
Qed.

Definition evaluates (t v : tm) : Prop := t -->* v /\ value v.

Lemma evaluates_prepend : forall t t' v, step t t' -> evaluates t' v -> evaluates t v.
Proof.
  intros t t' v Hstep [Hm Hv]. split; [eapply multi_step; eauto | exact Hv].
Qed.

Lemma evaluates_pair_inv : forall t1 t2 k v,
  evaluates (tm_pair t1 t2 k) v ->
  exists v1 v2, evaluates t1 v1 /\ evaluates t2 v2 /\
    value v1 /\ value v2 /\ v = tm_pair v1 v2 k.
Proof.
  intros t1 t2 k v [Hm Hv].
  remember (tm_pair t1 t2 k) as p eqn:Hp in Hm.
  revert t1 t2 Hp. induction Hm; intros u1 u2 Hp.
  - inversion Hp; subst. inversion Hv; subst. exists u1, u2.
    split; [split; [constructor | assumption] |].
    split; [split; [constructor | assumption] |].
    repeat split; assumption.
  - inversion Hp; subst. inversion H; subst.
    + specialize (IHHm Hv t1' u2 eq_refl) as [v1 [v2 [E1 [E2 [V1 [V2 E]]]]]].
      exists v1, v2. split.
      * eapply evaluates_prepend; eauto.
      * split; [exact E2 | split; [exact V1 | split; [exact V2 | exact E]]].
    + specialize (IHHm Hv u1 t2' eq_refl) as [a [b [E1 [E2 [V1 [V2 E]]]]]].
      exists a, b. split; [exact E1 |].
      split.
      * eapply evaluates_prepend; eauto.
      * split; [exact V1 | split; [exact V2 | exact E]].
Qed.

Lemma evaluates_app_inv : forall f a r v,
  evaluates (tm_app f a r) v ->
  exists vf va, evaluates f vf /\ evaluates a va /\ value vf /\ value va /\
    evaluates (tm_app vf va r) v.
Proof.
  intros f a r v [Hm Hv]. remember (tm_app f a r) as p eqn:Hp in Hm.
  revert f a Hp. induction Hm; intros f a Hp.
  - inversion Hp; subst. inversion Hv.
  - inversion Hp; subst. inversion H; subst.
    + exists (tm_abs T body kappa), a. split.
      * split; [constructor | exact H4].
      * split.
        -- split; [constructor | exact H6].
        -- split; [exact H4 | split; [exact H6 | split; [eapply multi_step; eauto | exact Hv]]].
    + specialize (IHHm Hv t1' a eq_refl)
        as [vf [va [Ef [Ea [Vf [Va Eapp]]]]]].
      exists vf, va. split; [eapply evaluates_prepend; eauto |].
      split; [exact Ea | split; [exact Vf | split; [exact Va | exact Eapp]]].
    + specialize (IHHm Hv f t2' eq_refl)
        as [vf [va [Ef [Ea [Vf [Va Eapp]]]]]].
      exists vf, va. split; [exact Ef |].
      split; [eapply evaluates_prepend; eauto |].
      split; [exact Vf | split; [exact Va | exact Eapp]].
Qed.

Lemma evaluates_inl_inv : forall t k v,
  evaluates (tm_inl t k) v ->
  exists w, evaluates t w /\ value w /\ v = tm_inl w k.
Proof.
  intros orig k v [Hm Hv]. remember (tm_inl orig k) as p eqn:Hp in Hm.
  revert orig Hp. induction Hm; intros orig Hp.
  - inversion Hp; subst. inversion Hv; subst. exists orig. repeat split; auto; constructor.
  - inversion Hp; subst. inversion H; subst.
    specialize (IHHm Hv t' eq_refl) as [w [E [V Ew]]].
    exists w. split; [eapply evaluates_prepend; eauto |]. split; assumption.
Qed.

Lemma evaluates_inr_inv : forall t k v,
  evaluates (tm_inr t k) v ->
  exists w, evaluates t w /\ value w /\ v = tm_inr w k.
Proof.
  intros orig k v [Hm Hv]. remember (tm_inr orig k) as p eqn:Hp in Hm.
  revert orig Hp. induction Hm; intros orig Hp.
  - inversion Hp; subst. inversion Hv; subst. exists orig. repeat split; auto; constructor.
  - inversion Hp; subst. inversion H; subst.
    specialize (IHHm Hv t' eq_refl) as [w [E [V Ew]]].
    exists w. split; [eapply evaluates_prepend; eauto |]. split; assumption.
Qed.

Lemma evaluates_protect_inv : forall l t v,
  evaluates (tm_protect l t) v ->
  exists w, evaluates t w /\ value w /\ v = protect_value w l.
Proof.
  intros l orig v [Hm Hv]. remember (tm_protect l orig) as p eqn:Hp in Hm.
  revert orig Hp. induction Hm; intros orig Hp.
  - inversion Hp; subst. inversion Hv.
  - inversion Hp; subst. inversion H; subst.
    + assert (Htail : protect_value orig l = t3).
      { eapply multi_from_value; [eapply value_protect_value; eassumption | eassumption]. }
      exists orig. split; [split; [constructor | exact H4] |]. split; [exact H4 | symmetry; exact Htail].
    + specialize (IHHm Hv t' eq_refl) as [w [Ew [Vw Eout]]].
      exists w. split; [eapply evaluates_prepend; eauto |]. split; assumption.
Qed.

Lemma evaluates_abs_app_inv : forall T body k a r v,
  value (tm_abs T body k) -> value a ->
  evaluates (tm_app (tm_abs T body k) a r) v ->
  exists w, evaluates (open body a) w /\ value w /\
    v = protect_value w k.(indirect_reader).
Proof.
  intros T body k a r v Vabs Va [Hm Hv].
  remember (tm_app (tm_abs T body k) a r) as p eqn:Hp in Hm.
  revert Hp. induction Hm; intros Hp.
  - inversion Hp; subst. inversion Hv.
  - inversion Hp; subst. inversion H; subst.
    all: try (destruct (evaluates_protect_inv _ _ _ (conj Hm Hv)) as [w [Ew [Vw ->]]]; exists w; auto).
    all: try solve [exfalso; match goal with
      | Hs : step ?src ?dst |- _ => first
          [exact (value_no_step src dst Vabs Hs) | exact (value_no_step src dst Va Hs)]
      end].
Qed.

Lemma evaluates_fst_inv : forall t r v,
  evaluates (tm_fst t r) v ->
  exists p v1 v2 k, evaluates t p /\ value v1 /\ value v2 /\
    p = tm_pair v1 v2 k /\ evaluates (tm_protect k.(indirect_reader) v1) v.
Proof.
  intros orig r v [Hm Hv]. remember (tm_fst orig r) as p eqn:Hp in Hm.
  revert orig Hp. induction Hm; intros orig Hp.
  - inversion Hp; subst. inversion Hv.
  - inversion Hp; subst. inversion H; subst.
    + exists (tm_pair v1 v2 kappa), v1, v2, kappa.
      split; [split; [constructor | exact (v_pair _ _ _ H3 H4)] |].
      split; [exact H3 |]. split; [exact H4 |]. split; [reflexivity |].
      split; [exact Hm | exact Hv].
    + specialize (IHHm Hv t' eq_refl) as [p [a [b [k [Ep [Va [Vb [Epair Eout]]]]]]]].
      exists p, a, b, k. split.
      * eapply evaluates_prepend; eauto.
      * split; [exact Va |]. split; [exact Vb |]. split; assumption.
Qed.

Lemma evaluates_snd_inv : forall t r v,
  evaluates (tm_snd t r) v ->
  exists p v1 v2 k, evaluates t p /\ value v1 /\ value v2 /\
    p = tm_pair v1 v2 k /\ evaluates (tm_protect k.(indirect_reader) v2) v.
Proof.
  intros orig r v [Hm Hv]. remember (tm_snd orig r) as p eqn:Hp in Hm.
  revert orig Hp. induction Hm; intros orig Hp.
  - inversion Hp; subst. inversion Hv.
  - inversion Hp; subst. inversion H; subst.
    + exists (tm_pair v1 v2 kappa), v1, v2, kappa.
      split; [split; [constructor | exact (v_pair _ _ _ H3 H4)] |].
      split; [exact H3 |]. split; [exact H4 |]. split; [reflexivity |].
      split; [exact Hm | exact Hv].
    + specialize (IHHm Hv t' eq_refl) as [p [a [b [k [Ep [Va [Vb [Epair Eout]]]]]]]].
      exists p, a, b, k. split.
      * eapply evaluates_prepend; eauto.
      * split; [exact Va |]. split; [exact Vb |]. split; assumption.
Qed.

Lemma evaluates_succ_inv : forall t r v,
  evaluates (tm_succ t r) v ->
  exists n k, evaluates t (tm_nat n k) /\ flows_to k.(reader) r /\
    evaluates (tm_protect k.(indirect_reader) (tm_nat (S n) public)) v.
Proof.
  intros orig r v [Hm Hv]. remember (tm_succ orig r) as p eqn:Hp in Hm.
  revert orig Hp. induction Hm; intros orig Hp.
  - inversion Hp; subst. inversion Hv.
  - inversion Hp; subst. inversion H; subst.
    + specialize (IHHm Hv t' eq_refl) as [n [k [En [Hflow Eout]]]].
      exists n, k. split; [eapply evaluates_prepend; eauto |]. split; assumption.
    + exists n, k. split.
      * unfold evaluates. split; [apply multi_refl | apply v_nat].
      * split; [assumption |]. unfold evaluates. split; assumption.
Qed.

Lemma evaluates_case_inv : forall t b1 b2 r v,
  evaluates (tm_case t b1 b2 r) v ->
  exists s, evaluates t s /\
    ((exists a k, value a /\ s = tm_inl a k /\
       evaluates (tm_protect k.(indirect_reader) (open b1 a)) v) \/
     (exists a k, value a /\ s = tm_inr a k /\
       evaluates (tm_protect k.(indirect_reader) (open b2 a)) v)).
Proof.
  intros orig b1 b2 r v [Hm Hv]. remember (tm_case orig b1 b2 r) as p eqn:Hp in Hm.
  revert orig Hp. induction Hm; intros orig Hp.
  - inversion Hp; subst. inversion Hv.
  - inversion Hp; subst. inversion H; subst.
    + exists (tm_inl v kappa). split.
      * unfold evaluates; split; [apply multi_refl | apply v_inl; assumption].
      * left. exists v, kappa. split; [assumption |]. split; [reflexivity |].
        split; [exact Hm | exact Hv].
    + exists (tm_inr v kappa). split.
      * unfold evaluates; split; [apply multi_refl | apply v_inr; assumption].
      * right. exists v, kappa. split; [assumption |]. split; [reflexivity |].
        split; [exact Hm | exact Hv].
    + specialize (IHHm Hv t' eq_refl) as [s [Es [HL | HR]]].
      * exists s. split; [eapply evaluates_prepend; eauto | left; exact HL].
      * exists s. split; [eapply evaluates_prepend; eauto | right; exact HR].
Qed.

Lemma evaluates_natrec_inv : forall n b s r v,
  evaluates (tm_natrec n b s r) v ->
  exists n0 k vb vs,
    evaluates n (tm_nat n0 k) /\ evaluates b vb /\ evaluates s vs /\
    value vb /\ value vs /\
    evaluates (tm_protect k.(indirect_reader)
      (natrec_unroll n0 vb vs r)) v.
Proof.
  intros n b s r v [Hm Hv].
  remember (tm_natrec n b s r) as src eqn:Hsrc in Hm.
  revert n b s Hsrc.
  induction Hm; intros n b s Hsrc.
  - inversion Hsrc; subst; inversion Hv.
  - inversion Hsrc; subst.
    inversion H; subst.
    + match goal with
      | Hn : step n n', IH : forall n b s, tm_natrec n b s r = tm_natrec n' b s r -> _ |- _ =>
          destruct (IH n' b s eq_refl) as [m [k [vb [vs [En [Eb [Es [Vb [Vs Eout]]]]]]]]];
          exists m, k, vb, vs; repeat split; try assumption;
          eapply evaluates_prepend; eassumption
      end.
    + match goal with
      | Hb : step b b', IH : forall n b s, tm_natrec n b s r = tm_natrec n b' s r -> _ |- _ =>
          destruct (IH n b' s eq_refl) as [m [k [vb [vs [En [Eb [Es [Vb [Vs Eout]]]]]]]]];
          exists m, k, vb, vs; repeat split; try assumption;
          eapply evaluates_prepend; eassumption
      end.
    + match goal with
      | Hs : step s s', IH : forall n b s, tm_natrec n b s r = tm_natrec n b s' r -> _ |- _ =>
          destruct (IH n b s' eq_refl) as [m [k [vb [vs [En [Eb [Es [Vb [Vs Eout]]]]]]]]];
          exists m, k, vb, vs; repeat split; try assumption;
          eapply evaluates_prepend; eassumption
      end.
    + match goal with
      | E : evaluates (tm_protect _ (natrec_unroll _ _ _ _)) _ |- _ =>
          destruct (multi_from_value _ _ (v_nat _ _) (multi_refl _))
      end.
Qed.

Inductive subtype : ty -> ty -> Prop :=
  | S_Unit : forall kappa1 kappa2,
      wf_security kappa1 -> wf_security kappa2 -> security_le kappa1 kappa2 ->
      subtype (Ty_Unit kappa1) (Ty_Unit kappa2)
  | S_Sum : forall T1 T2 U1 U2 kappa1 kappa2,
      subtype T1 U1 -> subtype T2 U2 ->
      wf_security kappa1 -> wf_security kappa2 -> security_le kappa1 kappa2 ->
      subtype (Ty_Sum T1 T2 kappa1) (Ty_Sum U1 U2 kappa2)
  | S_Prod : forall T1 T2 U1 U2 kappa1 kappa2,
      subtype T1 U1 -> subtype T2 U2 ->
      wf_security kappa1 -> wf_security kappa2 -> security_le kappa1 kappa2 ->
      subtype (Ty_Prod T1 T2 kappa1) (Ty_Prod U1 U2 kappa2)
  | S_Arrow : forall T1 T2 U1 U2 kappa1 kappa2,
      subtype U1 T1 -> subtype T2 U2 ->
      wf_security kappa1 -> wf_security kappa2 -> security_le kappa1 kappa2 ->
      subtype (Ty_Arrow T1 T2 kappa1) (Ty_Arrow U1 U2 kappa2)
  | S_Trans : forall T U V, subtype T U -> subtype U V -> subtype T V
  | S_Nat : forall k1 k2, wf_security k1 -> wf_security k2 -> security_le k1 k2 ->
      subtype (Ty_Nat k1) (Ty_Nat k2).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      lookup_context x Gamma = Some T -> wf_ty T ->
      has_type Gamma (tm_fvar x) T
  | T_Unit : forall Gamma kappa,
      wf_security kappa -> has_type Gamma (tm_unit kappa) (Ty_Unit kappa)
  | T_Abs : forall (L : list atom) Gamma T1 body T2 kappa,
      wf_ty T1 -> wf_security kappa ->
      (forall x : atom, ~ In x L ->
        has_type (update Gamma x T1) (open body (tm_fvar x)) T2) ->
      has_type Gamma (tm_abs T1 body kappa) (Ty_Arrow T1 T2 kappa)
  | T_App : forall Gamma t1 t2 T1 T2 kappa r,
      has_type Gamma t1 (Ty_Arrow T1 T2 kappa) ->
      has_type Gamma t2 T1 -> flows_to kappa.(reader) r ->
      has_type Gamma (tm_app t1 t2 r) (ty_protect kappa.(indirect_reader) T2)
  | T_Pair : forall Gamma t1 t2 T1 T2 kappa,
      has_type Gamma t1 T1 -> has_type Gamma t2 T2 -> wf_security kappa ->
      has_type Gamma (tm_pair t1 t2 kappa) (Ty_Prod T1 T2 kappa)
  | T_Fst : forall Gamma t T1 T2 kappa r,
      has_type Gamma t (Ty_Prod T1 T2 kappa) -> flows_to kappa.(reader) r ->
      has_type Gamma (tm_fst t r) (ty_protect kappa.(indirect_reader) T1)
  | T_Snd : forall Gamma t T1 T2 kappa r,
      has_type Gamma t (Ty_Prod T1 T2 kappa) -> flows_to kappa.(reader) r ->
      has_type Gamma (tm_snd t r) (ty_protect kappa.(indirect_reader) T2)
  | T_Inl : forall Gamma t T1 T2 kappa,
      has_type Gamma t T1 -> wf_ty T2 -> wf_security kappa ->
      has_type Gamma (tm_inl t kappa) (Ty_Sum T1 T2 kappa)
  | T_Inr : forall Gamma t T1 T2 kappa,
      wf_ty T1 -> has_type Gamma t T2 -> wf_security kappa ->
      has_type Gamma (tm_inr t kappa) (Ty_Sum T1 T2 kappa)
  | T_Case : forall (L : list atom) Gamma t body1 body2 T1 T2 T kappa r,
      has_type Gamma t (Ty_Sum T1 T2 kappa) -> flows_to kappa.(reader) r ->
      (forall x : atom, ~ In x L ->
        has_type (update Gamma x T1) (open body1 (tm_fvar x)) T) ->
      (forall x : atom, ~ In x L ->
        has_type (update Gamma x T2) (open body2 (tm_fvar x)) T) ->
      has_type Gamma (tm_case t body1 body2 r)
        (ty_protect kappa.(indirect_reader) T)
  | T_Protect : forall Gamma t T l,
      has_type Gamma t T -> has_type Gamma (tm_protect l t) (ty_protect l T)
  | T_Sub : forall Gamma t T U,
      has_type Gamma t T -> subtype T U -> has_type Gamma t U
  | T_Nat : forall Gamma n k, wf_security k -> has_type Gamma (tm_nat n k) (Ty_Nat k)
  | T_Succ : forall Gamma t k r,
      has_type Gamma t (Ty_Nat k) -> flows_to k.(reader) r ->
      has_type Gamma (tm_succ t r) (ty_protect k.(indirect_reader) (Ty_Nat public))
  | T_NatRec : forall Gamma n b s k T r,
      has_type Gamma n (Ty_Nat k) -> has_type Gamma b T ->
      has_type Gamma s (Ty_Arrow (Ty_Nat public) (Ty_Arrow T T public) public) ->
      flows_to k.(reader) r ->
      has_type Gamma (tm_natrec n b s r) (ty_protect k.(indirect_reader) T).

Inductive program_context : Type :=
  | C_Hole : program_context
  | C_Abs : ty -> program_context -> security -> program_context
  | C_AppLeft : program_context -> tm -> label -> program_context
  | C_AppRight : tm -> program_context -> label -> program_context
  | C_PairLeft : program_context -> tm -> security -> program_context
  | C_PairRight : tm -> program_context -> security -> program_context
  | C_Fst : program_context -> label -> program_context
  | C_Snd : program_context -> label -> program_context
  | C_Inl : program_context -> security -> program_context
  | C_Inr : program_context -> security -> program_context
  | C_CaseScrutinee : program_context -> tm -> tm -> label -> program_context
  | C_CaseLeft : tm -> program_context -> tm -> label -> program_context
  | C_CaseRight : tm -> tm -> program_context -> label -> program_context
  | C_Protect : label -> program_context -> program_context
  | C_Succ : program_context -> label -> program_context
  | C_RecArg : program_context -> tm -> tm -> label -> program_context
  | C_RecBase : tm -> program_context -> tm -> label -> program_context
  | C_RecStep : tm -> tm -> program_context -> label -> program_context.

Fixpoint plug (C : program_context) (t : tm) : tm :=
  match C with
  | C_Hole => t
  | C_Abs T C' kappa => tm_abs T (plug C' t) kappa
  | C_AppLeft C' t2 r => tm_app (plug C' t) t2 r
  | C_AppRight t1 C' r => tm_app t1 (plug C' t) r
  | C_PairLeft C' t2 kappa => tm_pair (plug C' t) t2 kappa
  | C_PairRight t1 C' kappa => tm_pair t1 (plug C' t) kappa
  | C_Fst C' r => tm_fst (plug C' t) r
  | C_Snd C' r => tm_snd (plug C' t) r
  | C_Inl C' kappa => tm_inl (plug C' t) kappa
  | C_Inr C' kappa => tm_inr (plug C' t) kappa
  | C_CaseScrutinee C' body1 body2 r => tm_case (plug C' t) body1 body2 r
  | C_CaseLeft t0 C' body2 r => tm_case t0 (plug C' t) body2 r
  | C_CaseRight t0 body1 C' r => tm_case t0 body1 (plug C' t) r
  | C_Protect l C' => tm_protect l (plug C' t)
  | C_Succ C' r => tm_succ (plug C' t) r
  | C_RecArg C' b s r => tm_natrec (plug C' t) b s r
  | C_RecBase n C' s r => tm_natrec n (plug C' t) s r
  | C_RecStep n b C' r => tm_natrec n b (plug C' t) r
  end.

Definition context_has_type (C : program_context) (T_hole T_result : ty) : Prop :=
  exists L : list atom, forall x : atom, ~ In x L ->
    has_type (update empty x T_hole) (plug C (tm_fvar x)) T_result.

Fixpoint ground (T : ty) : Prop :=
  match T with
  | Ty_Unit _ | Ty_Nat _ => True
  | Ty_Sum T1 T2 _ | Ty_Prod T1 T2 _ => ground T1 /\ ground T2
  | Ty_Arrow _ _ _ => False
  end.

Fixpoint transparent_at (kappa : security) (T : ty) : Prop :=
  security_le (security_of T) kappa /\
  match T with
  | Ty_Unit _ | Ty_Nat _ => True
  | Ty_Sum T1 T2 _ | Ty_Prod T1 T2 _ | Ty_Arrow T1 T2 _ =>
      transparent_at kappa T1 /\ transparent_at kappa T2
  end.

Definition transparent (T : ty) : Prop := transparent_at (security_of T) T.

Definition same_result (t1 t2 : tm) : Prop :=
  forall v1 v2 : tm,
    evaluates t1 v1 -> evaluates t2 v2 ->
    erase_security v1 = erase_security v2.

(* The value relation is indexed by the type.  At an unreadable outer
   constructor it deliberately forgets the payload; at readable constructors
   it compares the observable shape recursively.  Functions are related by
   their behavior on related arguments. *)
Fixpoint value_rel (T : ty) (v1 v2 : tm) : Prop :=
  match T with
  | Ty_Unit k =>
      match k.(reader), k.(indirect_reader) with
      | High, High => True
      | _, _ => (exists k1, v1 = tm_unit k1) /\ (exists k2, v2 = tm_unit k2)
      end
  | Ty_Nat k =>
      match k.(reader), k.(indirect_reader) with
      | High, High => True
      | _, _ => exists n k1 k2, v1 = tm_nat n k1 /\ v2 = tm_nat n k2 /\
          security_le k1 k /\ security_le k2 k
      end
  | Ty_Sum A B k =>
      match k.(reader), k.(indirect_reader) with
      | High, High => True
      | _, _ =>
          (exists a1 a2 k1 k2, v1 = tm_inl a1 k1 /\ v2 = tm_inl a2 k2 /\
            security_le k1 k /\ security_le k2 k /\ value_rel A a1 a2) \/
          (exists b1 b2 k1 k2, v1 = tm_inr b1 k1 /\ v2 = tm_inr b2 k2 /\
            security_le k1 k /\ security_le k2 k /\ value_rel B b1 b2)
      end
  | Ty_Prod A B k =>
      match k.(reader), k.(indirect_reader) with
      | High, High => True
      | _, _ => exists a1 a2 b1 b2 k1 k2,
          v1 = tm_pair a1 b1 k1 /\ v2 = tm_pair a2 b2 k2 /\
          security_le k1 k /\ security_le k2 k /\
          value_rel A a1 a2 /\ value_rel B b1 b2
      end
  | Ty_Arrow A B k =>
      match k.(reader), k.(indirect_reader) with
      | High, High => True
      | _, _ => forall r, forall a1 a2, value a1 -> value a2 ->
          value_rel A a1 a2 ->
          forall w1 w2,
            evaluates (tm_app v1 a1 r) w1 ->
            evaluates (tm_app v2 a2 r) w2 ->
            match k.(indirect_reader) with
            | High => True
            | Low => value_rel B w1 w2
            end
      end
  end.

Definition term_rel (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2, evaluates t1 v1 -> evaluates t2 v2 -> value_rel T v1 v2.

Definition environment_rel (Gamma : context) (rho1 rho2 : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> term_rel T (rho1 x) (rho2 x).

Fixpoint instantiate (rho : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_unit k => tm_unit k
  | tm_abs T b k => tm_abs T (instantiate rho b) k
  | tm_app f a r => tm_app (instantiate rho f) (instantiate rho a) r
  | tm_pair a b k => tm_pair (instantiate rho a) (instantiate rho b) k
  | tm_fst a r => tm_fst (instantiate rho a) r
  | tm_snd a r => tm_snd (instantiate rho a) r
  | tm_inl a k => tm_inl (instantiate rho a) k
  | tm_inr a k => tm_inr (instantiate rho a) k
  | tm_case a b c r => tm_case (instantiate rho a) (instantiate rho b) (instantiate rho c) r
  | tm_protect l a => tm_protect l (instantiate rho a)
  | tm_nat n k => tm_nat n k
  | tm_succ a r => tm_succ (instantiate rho a) r
  | tm_natrec n b s r => tm_natrec (instantiate rho n) (instantiate rho b) (instantiate rho s) r
  end.

Definition extend_env (rho : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else rho y.

Lemma lc_at_mono : forall t k, lc_at k t -> forall k', k <= k' -> lc_at k' t.
Proof.
  induction t; simpl; intros k Hlc k' Hkk'; try exact I.
  - lia.
  - eapply IHt; [exact Hlc | lia].
  - destruct Hlc as [H1 H2]. split; [eapply IHt1 | eapply IHt2]; eauto.
  - destruct Hlc as [H1 H2]. split; [eapply IHt1 | eapply IHt2]; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - destruct Hlc as [H0 [H1 H2]]. repeat split; [eapply IHt1 | eapply IHt2 | eapply IHt3]; eauto; lia.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - destruct Hlc as [H1 [H2 H3]]. repeat split; [eapply IHt1 | eapply IHt2 | eapply IHt3]; eauto.
Qed.

Lemma instantiate_lc : forall t k, lc_at k t -> forall rho,
  (forall x, locally_closed (rho x)) -> lc_at k (instantiate rho t).
Proof.
  induction t; simpl; intros k Hlc rho Hrho; try exact I.
  - exact Hlc.
  - eapply lc_at_mono; [apply Hrho | lia].
  - eapply IHt; eauto.
  - destruct Hlc; split; [eapply IHt1 | eapply IHt2]; eauto.
  - destruct Hlc; split; [eapply IHt1 | eapply IHt2]; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - destruct Hlc as [H0 [H1 H2]]. repeat split; [eapply IHt1 | eapply IHt2 | eapply IHt3]; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - destruct Hlc as [H1 [H2 H3]]. repeat split; [eapply IHt1 | eapply IHt2 | eapply IHt3]; eauto.
Qed.

Lemma instantiate_extend_here : forall rho x v,
  instantiate (extend_env rho x v) (tm_fvar x) = v.
Proof. intros; simpl; unfold extend_env; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma instantiate_extend_other : forall rho x y v,
  x <> y -> instantiate (extend_env rho x v) (tm_fvar y) = rho y.
Proof.
  intros; simpl; unfold extend_env. destruct (Nat.eqb x y) eqn:E; auto.
  apply Nat.eqb_eq in E; contradiction.
Qed.

Lemma instantiate_extend_away : forall t rho x v,
  ~ In x (fv t) -> instantiate (extend_env rho x v) t = instantiate rho t.
Proof.
  induction t; simpl; intros rho x v Hnot; try reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso. apply Hnot. simpl; auto.
    + apply instantiate_extend_other. apply Nat.eqb_neq; exact E.
  - rewrite IHt; auto.
  - assert (N1 : ~ In x (fv t1)) by (intro Q; apply Hnot; apply in_app_iff; auto).
    assert (N2 : ~ In x (fv t2)) by (intro Q; apply Hnot; apply in_app_iff; auto).
    rewrite IHt1 by exact N1. rewrite IHt2 by exact N2. reflexivity.
  - assert (N1 : ~ In x (fv t1)) by (intro Q; apply Hnot; apply in_app_iff; auto).
    assert (N2 : ~ In x (fv t2)) by (intro Q; apply Hnot; apply in_app_iff; auto).
    rewrite IHt1 by exact N1. rewrite IHt2 by exact N2. reflexivity.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - assert (N1 : ~ In x (fv t1)) by (intro Q; apply Hnot; repeat rewrite in_app_iff; auto).
    assert (N2 : ~ In x (fv t2)) by (intro Q; apply Hnot; repeat rewrite in_app_iff; auto).
    assert (N3 : ~ In x (fv t3)) by (intro Q; apply Hnot; repeat rewrite in_app_iff; auto).
    rewrite IHt1 by exact N1. rewrite IHt2 by exact N2. rewrite IHt3 by exact N3. reflexivity.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - assert (N1 : ~ In x (fv t1)) by (intro Q; apply Hnot; repeat rewrite in_app_iff; auto).
    assert (N2 : ~ In x (fv t2)) by (intro Q; apply Hnot; repeat rewrite in_app_iff; auto).
    assert (N3 : ~ In x (fv t3)) by (intro Q; apply Hnot; repeat rewrite in_app_iff; auto).
    rewrite IHt1 by exact N1. rewrite IHt2 by exact N2. rewrite IHt3 by exact N3. reflexivity.
Qed.

Lemma open_rec_lc : forall t d, lc_at d t -> forall k u,
  d <= k -> open_rec k u t = t.
Proof.
  induction t; simpl; intros d Hlc k u Hdk; try reflexivity.
  - destruct (Nat.eqb k n) eqn:E; [apply Nat.eqb_eq in E; lia | reflexivity].
  - f_equal. eapply IHt; [exact Hlc | lia].
  - destruct Hlc as [H1 H2]. f_equal; [eapply IHt1 | eapply IHt2]; eauto.
  - destruct Hlc as [H1 H2]. f_equal; [eapply IHt1 | eapply IHt2]; eauto.
  - f_equal. eapply IHt; eauto.
  - f_equal. eapply IHt; eauto.
  - f_equal. eapply IHt; eauto.
  - f_equal. eapply IHt; eauto.
  - destruct Hlc as [H0 [H1 H2]]. f_equal.
    + eapply IHt1; [exact H0 | lia].
    + eapply IHt2; [exact H1 | lia].
    + eapply IHt3; [exact H2 | lia].
  - f_equal. eapply IHt; eauto.
  - f_equal. eapply IHt; eauto.
  - destruct Hlc as [H1 [H2 H3]]. f_equal.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
    + eapply IHt3; eauto.
Qed.

Lemma lc_open_rec_inv : forall t k u,
  lc_at k u -> lc_at k (open_rec k u t) -> lc_at (S k) t.
Proof.
  induction t; simpl; intros k u Hu Hopen; try exact I.
  - destruct (Nat.eqb k n) eqn:E; simpl in Hopen.
    + apply Nat.eqb_eq in E; subst; lia.
    + lia.
  - eapply IHt with (k := S k) (u := u); [|exact Hopen].
    eapply lc_at_mono; [exact Hu | lia].
  - destruct Hopen as [H1 H2]. split; [exact (IHt1 k u Hu H1) | exact (IHt2 k u Hu H2)].
  - destruct Hopen as [H1 H2]. split; [exact (IHt1 k u Hu H1) | exact (IHt2 k u Hu H2)].
  - exact (IHt k u Hu Hopen).
  - exact (IHt k u Hu Hopen).
  - exact (IHt k u Hu Hopen).
  - exact (IHt k u Hu Hopen).
  - destruct Hopen as [H0 [H1 H2]]. split.
    + exact (IHt1 k u Hu H0).
    + split.
      * eapply IHt2 with (k := S k); [|exact H1].
        eapply lc_at_mono; [exact Hu | lia].
      * eapply IHt3 with (k := S k); [|exact H2].
        eapply lc_at_mono; [exact Hu | lia].
  - exact (IHt k u Hu Hopen).
  - exact (IHt k u Hu Hopen).
  - destruct Hopen as [H1 [H2 H3]]. repeat split.
    + exact (IHt1 k u Hu H1).
    + exact (IHt2 k u Hu H2).
    + exact (IHt3 k u Hu H3).
Qed.

Lemma instantiate_open_rec : forall rho t, (forall x, locally_closed (rho x)) ->
  forall k u, locally_closed (instantiate rho u) ->
  instantiate rho (open_rec k u t) = open_rec k (instantiate rho u) (instantiate rho t).
Proof.
  intros rho t; induction t; intros Hrho k u Hu; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. eapply open_rec_lc; [apply Hrho | lia].
  - reflexivity.
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
  - f_equal. apply IHt; assumption.
  - reflexivity.
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
Qed.

Lemma instantiate_open_extend : forall rho t x v,
  (forall y, locally_closed (rho y)) -> ~ In x (fv t) -> locally_closed v ->
  instantiate (extend_env rho x v) (open t (tm_fvar x)) =
    open (instantiate rho t) v.
Proof.
  intros rho t x v Hrho Hfresh Hlc. unfold open.
  rewrite instantiate_open_rec.
  - rewrite instantiate_extend_here.
    rewrite instantiate_extend_away; auto.
  - intro y. unfold extend_env. destruct (Nat.eqb x y); [exact Hlc | apply Hrho].
  - simpl. unfold extend_env. rewrite Nat.eqb_refl. exact Hlc.
Qed.

Lemma environment_rel_extend : forall Gamma rho1 rho2 x T a1 a2,
  environment_rel Gamma rho1 rho2 -> term_rel T a1 a2 ->
  environment_rel (update Gamma x T)
    (extend_env rho1 x a1) (extend_env rho2 x a2).
Proof.
  intros Gamma rho1 rho2 x T a1 a2 Henv Harg y U Hlookup.
  unfold update in Hlookup. simpl in Hlookup.
  unfold extend_env. rewrite Nat.eqb_sym.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E; subst. simpl in Hlookup. rewrite Nat.eqb_refl in Hlookup.
    inversion Hlookup; subst. rewrite Nat.eqb_refl. exact Harg.
  - assert (E' : Nat.eqb y x = false).
    { rewrite Nat.eqb_sym. exact E. }
    rewrite E' in Hlookup. rewrite E'. eapply Henv; eauto.
Qed.

Fixpoint atom_bound (L : list atom) : nat :=
  match L with [] => 0 | x :: L' => Nat.max x (atom_bound L') end.

Lemma atom_le_bound : forall x L, In x L -> x <= atom_bound L.
Proof.
  intros x L; induction L as [|a L IH]; simpl; intros Hin; [contradiction|].
  destruct Hin as [-> | Hin].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [eapply IH; exact Hin | apply Nat.le_max_r].
Qed.

Lemma exists_fresh_atom : forall L, exists x : atom, ~ In x L.
Proof.
  intros L. exists (S (atom_bound L)). intro Hin.
  pose proof (atom_le_bound _ _ Hin). lia.
Qed.

Lemma has_type_locally_closed : forall Gamma t T,
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Hty; induction Hty; simpl; try exact I.
  - destruct (exists_fresh_atom L) as [x Hx].
    specialize (H2 x Hx). unfold locally_closed in H2.
    unfold open in H2. eapply lc_open_rec_inv with (k := 0) (u := tm_fvar x); simpl; eauto.
  - split; assumption.
  - split; assumption.
  - exact IHHty.
  - exact IHHty.
  - exact IHHty.
  - exact IHHty.
  - destruct (exists_fresh_atom L) as [x Hx].
    specialize (H1 x Hx). specialize (H3 x Hx).
    unfold locally_closed in H1, H3. unfold open in H1, H3.
    split; [exact IHHty |].
    split.
    + eapply lc_open_rec_inv with (k := 0) (u := tm_fvar x); simpl; eauto.
    + eapply lc_open_rec_inv with (k := 0) (u := tm_fvar x); simpl; eauto.
  - exact IHHty.
  - exact IHHty.
  - exact IHHty.
  - repeat split; assumption.
Qed.

Lemma instantiate_value : forall v, value v -> forall rho,
  (forall x, locally_closed (rho x)) -> value (instantiate rho v).
Proof.
  intros v Hv; induction Hv; intros rho Hrho; simpl.
  - constructor.
  - constructor. eapply instantiate_lc; [exact H | exact Hrho].
  - constructor; [eapply IHHv1 | eapply IHHv2]; eauto.
  - constructor. eapply IHHv; eauto.
  - constructor. eapply IHHv; eauto.
  - constructor.
Qed.

Lemma term_rel_value : forall T v1 v2,
  value v1 -> value v2 -> value_rel T v1 v2 -> term_rel T v1 v2.
Proof.
  intros T v1 v2 Hv1 Hv2 Hrel w1 w2 [Hsteps1 Hvalue1] [Hsteps2 Hvalue2].
  assert (w1 = v1) by (symmetry; eapply multi_from_value; eauto).
  assert (w2 = v2) by (symmetry; eapply multi_from_value; eauto).
  subst. exact Hrel.
Qed.

Lemma flows_to_low_inv : forall l, flows_to l Low -> l = Low.
Proof. destruct l; simpl; auto; contradiction. Qed.

Lemma not_flows_two_levels : forall l1 l2,
  ~ flows_to l1 l2 -> l1 = High /\ l2 = Low.
Proof. destruct l1, l2; simpl; intuition discriminate. Qed.

Lemma flows_trans : forall a b c, flows_to a b -> flows_to b c -> flows_to a c.
Proof. destruct a, b, c; simpl; intuition. Qed.

Lemma security_le_trans : forall a b c, security_le a b -> security_le b c -> security_le a c.
Proof. intros [a1 a2] [b1 b2] [c1 c2] [H1 H2] [H3 H4]; split; eapply flows_trans; eauto. Qed.

Lemma security_le_observable : forall k1 k2,
  security_le k1 k2 ->
  (k2.(reader) = Low \/ k2.(indirect_reader) = Low) ->
  (k1.(reader) = Low \/ k1.(indirect_reader) = Low).
Proof.
  intros k1 k2 [Hr Hi] [Hlow | Hlow].
  - left. rewrite Hlow in Hr. apply flows_to_low_inv in Hr. exact Hr.
  - right. rewrite Hlow in Hi. apply flows_to_low_inv in Hi. exact Hi.
Qed.

Lemma transparent_at_security_le : forall k T,
  transparent_at k T -> security_le (security_of T) k.
Proof. intros k T H; destruct T; simpl in H; tauto. Qed.

Lemma value_rel_ground_erases : forall T v1 v2 kappa,
  ground T -> transparent_at kappa T ->
  kappa.(reader) = Low -> kappa.(indirect_reader) = Low ->
  value_rel T v1 v2 -> erase_security v1 = erase_security v2.
Proof.
  induction T; simpl; intros v1 v2 kappa Hground Htrans Hlow Hindlow Hrel.
  - destruct Htrans as [Hsec _]. destruct Hsec as [Hread Hind].
    assert (Hsread : reader s = Low) by (rewrite Hlow in Hread; apply flows_to_low_inv in Hread; exact Hread).
    assert (Hsind : indirect_reader s = Low) by (rewrite Hindlow in Hind; apply flows_to_low_inv in Hind; exact Hind).
    rewrite Hsread in Hrel. simpl in Hrel.
    destruct Hrel as [[k1 ->] [k2 ->]]. reflexivity.
  - destruct Hground as [Hg1 Hg2]. destruct Htrans as [Hsec [Ht1 Ht2]].
    destruct Hsec as [Hread Hind].
    assert (Hsread : reader s = Low) by (rewrite Hlow in Hread; apply flows_to_low_inv in Hread; exact Hread).
    assert (Hsind : indirect_reader s = Low) by (rewrite Hindlow in Hind; apply flows_to_low_inv in Hind; exact Hind).
    rewrite Hsread in Hrel. simpl in Hrel.
    destruct Hrel as [HL | HR].
    + destruct HL as (a1 & a2 & k1 & k2 & E1 & E2 & S1 & S2 & Ha). subst.
      simpl. f_equal. eapply IHT1; eauto.
    + destruct HR as (b1 & b2 & k1 & k2 & E1 & E2 & S1 & S2 & Hb). subst.
      simpl. f_equal. eapply IHT2; eauto.
  - destruct Hground as [Hg1 Hg2]. destruct Htrans as [Hsec [Ht1 Ht2]].
    destruct Hsec as [Hread Hind].
    assert (Hsread : reader s = Low) by (rewrite Hlow in Hread; apply flows_to_low_inv in Hread; exact Hread).
    assert (Hsind : indirect_reader s = Low) by (rewrite Hindlow in Hind; apply flows_to_low_inv in Hind; exact Hind).
    rewrite Hsread in Hrel. simpl in Hrel.
    destruct Hrel as (a1 & a2 & b1 & b2 & k1 & k2 & E1 & E2 & Sk1 & Sk2 & Ha & Hb).
    subst.
    simpl. f_equal.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto.
  - contradiction.
  - destruct Htrans as [Hsec _]. destruct Hsec as [Hread Hind].
    assert (Hsread : reader s = Low) by (rewrite Hlow in Hread; apply flows_to_low_inv in Hread; exact Hread).
    assert (Hsind : indirect_reader s = Low) by (rewrite Hindlow in Hind; apply flows_to_low_inv in Hind; exact Hind).
    rewrite Hsread in Hrel. simpl in Hrel.
    destruct Hrel as (n & k1 & k2 & E1 & E2 & S1 & S2). rewrite E1, E2. reflexivity.
Qed.

Lemma value_rel_protect : forall T l v1 v2,
  value_rel T v1 v2 ->
  value_rel (ty_protect l T) (protect_value v1 l) (protect_value v2 l).
Proof.
  destruct T as [k|A B k|A B k|A B k|k]; intros l v1 v2 Hrel.
  all: destruct k as [r i]; destruct l.
  all: try (rewrite protect_value_low, protect_value_low; destruct r, i; simpl in *; exact Hrel).
  all: destruct r, i; simpl; exact I.
Qed.

Lemma value_rel_protect_high : forall T v1 v2,
  value_rel (ty_protect High T) v1 v2.
Proof.
  destruct T; simpl; try exact I; destruct s as [r i]; destruct r, i; simpl; repeat intro; exact I.
Qed.

Lemma term_rel_protect : forall T l t1 t2,
  term_rel T t1 t2 ->
  term_rel (ty_protect l T) (tm_protect l t1) (tm_protect l t2).
Proof.
  intros T l t1 t2 Hrel v1 v2 Ev1 Ev2.
  destruct (evaluates_protect_inv _ _ _ Ev1) as [w1 [Ew1 [Vw1 ->]]].
  destruct (evaluates_protect_inv _ _ _ Ev2) as [w2 [Ew2 [Vw2 ->]]].
  apply value_rel_protect. eapply Hrel; eassumption.
Qed.

Lemma value_rel_subtype : forall T U, subtype T U -> forall v1 v2,
  value_rel T v1 v2 -> value_rel U v1 v2.
Proof.
  intros T U Hsub; induction Hsub; intros v1 v2 Hrel; simpl in *.
  - destruct kappa2.(reader) eqn:Hr2, kappa2.(indirect_reader) eqn:Hi2; simpl; try exact I.
    all: assert (Hobs : kappa1.(reader) = Low \/ kappa1.(indirect_reader) = Low)
      by (eapply security_le_observable; [exact H1 | rewrite Hr2, Hi2; simpl; auto]).
    all: destruct kappa1.(reader), kappa1.(indirect_reader); simpl in Hobs, Hrel; try (destruct Hobs; discriminate); exact Hrel.
  - destruct kappa2.(reader) eqn:Hr2, kappa2.(indirect_reader) eqn:Hi2; simpl; try exact I.
    all: assert (Hobs : kappa1.(reader) = Low \/ kappa1.(indirect_reader) = Low)
      by (eapply security_le_observable; [exact H1 | rewrite Hr2, Hi2; simpl; auto]).
    all: destruct kappa1.(reader) eqn:Hr1, kappa1.(indirect_reader) eqn:Hi1;
      simpl in Hobs, Hrel; try (destruct Hobs; discriminate).
    all: destruct Hrel as [HL | HR].
    all: try (left; destruct HL as (a1 & a2 & x & y & E1 & E2 & Sx & Sy & HA);
      exists a1, a2, x, y; split; [exact E1 |]; split; [exact E2 |];
      split; [eapply security_le_trans; [exact Sx | exact H1] |];
      split; [eapply security_le_trans; [exact Sy | exact H1] |]; eapply IHHsub1; exact HA).
    all: right; destruct HR as (b1 & b2 & x & y & E1 & E2 & Sx & Sy & HB);
      exists b1, b2, x, y; split; [exact E1 |]; split; [exact E2 |];
      split; [eapply security_le_trans; [exact Sx | exact H1] |];
      split; [eapply security_le_trans; [exact Sy | exact H1] |]; eapply IHHsub2; exact HB.
  - destruct kappa2.(reader) eqn:Hr2, kappa2.(indirect_reader) eqn:Hi2; simpl; try exact I.
    all: assert (Hobs : kappa1.(reader) = Low \/ kappa1.(indirect_reader) = Low)
      by (eapply security_le_observable; [exact H1 | rewrite Hr2, Hi2; simpl; auto]).
    all: destruct kappa1.(reader) eqn:Hr1, kappa1.(indirect_reader) eqn:Hi1;
      simpl in Hobs, Hrel; try (destruct Hobs; discriminate).
    all: destruct Hrel as (a1 & a2 & b1 & b2 & x & y & E1 & E2 & Sx & Sy & HA & HB).
    all: exists a1, a2, b1, b2, x, y; repeat split; try assumption.
    all: try (eapply security_le_trans; [exact Sx | exact H1]).
    all: try (eapply security_le_trans; [exact Sy | exact H1]).
    all: try (eapply IHHsub1; exact HA).
    all: try (eapply IHHsub2; exact HB).
  - destruct kappa2.(reader) eqn:Hr2, kappa2.(indirect_reader) eqn:Hi2; simpl; try exact I.
    all: assert (Hobs : kappa1.(reader) = Low \/ kappa1.(indirect_reader) = Low)
      by (eapply security_le_observable; [exact H1 | rewrite Hr2, Hi2; simpl; auto]).
    all: destruct kappa1.(reader) eqn:Hr1, kappa1.(indirect_reader) eqn:Hi1;
      simpl in Hobs, Hrel; try (destruct Hobs; discriminate).
    all: intros r a1 a2 Va1 Va2 Ha w1 w2 Ew1 Ew2.
    all: specialize (Hrel r a1 a2 Va1 Va2 (IHHsub1 a1 a2 Ha) w1 w2 Ew1 Ew2).
    all: simpl.
    all: try exact I.
    all: assert (HiS : kappa1.(indirect_reader) = Low)
      by (pose proof (proj2 H1) as HH; rewrite Hi2 in HH; apply flows_to_low_inv in HH; exact HH);
      rewrite Hi1 in HiS; try discriminate; simpl in Hrel; eapply IHHsub2; exact Hrel.
  - eapply IHHsub2. eapply IHHsub1. exact Hrel.
  - destruct k2.(reader) eqn:Hr2, k2.(indirect_reader) eqn:Hi2; simpl; try exact I.
    all: assert (Hobs : k1.(reader) = Low \/ k1.(indirect_reader) = Low)
      by (eapply security_le_observable; [exact H1 | rewrite Hr2, Hi2; simpl; auto]).
    all: destruct k1.(reader), k1.(indirect_reader); simpl in Hobs, Hrel; try (destruct Hobs; discriminate).
    all: destruct Hrel as (n & x & y & E1 & E2 & Sx & Sy).
    all: exists n, x, y; split; [exact E1 |]; split; [exact E2 |];
      split; [eapply security_le_trans; [exact Sx | exact H1] |];
      eapply security_le_trans; [exact Sy | exact H1].
Qed.

Lemma term_rel_pair : forall A B k a1 a2 b1 b2,
  term_rel A a1 a2 -> term_rel B b1 b2 ->
  term_rel (Ty_Prod A B k) (tm_pair a1 b1 k) (tm_pair a2 b2 k).
Proof.
  intros A B [r i] a1 a2 b1 b2 Ha Hb v1 v2 Ev1 Ev2.
  destruct (evaluates_pair_inv _ _ _ _ Ev1) as [x1 [y1 [Ex1 [Ey1 [Vx1 [Vy1 ->]]]]]].
  destruct (evaluates_pair_inv _ _ _ _ Ev2) as [x2 [y2 [Ex2 [Ey2 [Vx2 [Vy2 ->]]]]]].
  simpl. destruct r, i; simpl; try exact I.
  all: eexists x1, x2, y1, y2; eexists; eexists; repeat split; try reflexivity.
  all: try (eapply Ha; eassumption).
  all: try (eapply Hb; eassumption).
Qed.

Lemma term_rel_inl : forall A B k a1 a2,
  term_rel A a1 a2 ->
  term_rel (Ty_Sum A B k) (tm_inl a1 k) (tm_inl a2 k).
Proof.
  intros A B [r i] a1 a2 Ha v1 v2 Ev1 Ev2.
  destruct (evaluates_inl_inv _ _ _ Ev1) as [x1 [Ex1 [Vx1 ->]]].
  destruct (evaluates_inl_inv _ _ _ Ev2) as [x2 [Ex2 [Vx2 ->]]].
  simpl. destruct r, i; simpl; try exact I.
  all: left; eexists x1, x2; eexists; eexists; repeat split; try reflexivity; eapply Ha; eassumption.
Qed.

Lemma term_rel_inr : forall A B k a1 a2,
  term_rel B a1 a2 ->
  term_rel (Ty_Sum A B k) (tm_inr a1 k) (tm_inr a2 k).
Proof.
  intros A B [r i] a1 a2 Hb v1 v2 Ev1 Ev2.
  destruct (evaluates_inr_inv _ _ _ Ev1) as [x1 [Ex1 [Vx1 ->]]].
  destruct (evaluates_inr_inv _ _ _ Ev2) as [x2 [Ex2 [Vx2 ->]]].
  simpl. destruct r, i; simpl; try exact I.
  all: right; eexists x1, x2; eexists; eexists; repeat split; try reflexivity; eapply Hb; eassumption.
Qed.

Lemma term_rel_abs : forall A B k b1 b2,
  locally_closed (tm_abs A b1 k) -> locally_closed (tm_abs A b2 k) ->
  (forall a1 a2, value a1 -> value a2 -> value_rel A a1 a2 ->
    term_rel B (open b1 a1) (open b2 a2)) ->
  term_rel (Ty_Arrow A B k) (tm_abs A b1 k) (tm_abs A b2 k).
Proof.
  intros A B [r i] b1 b2 L1 L2 Hbody v1 v2 Ev1 Ev2.
  assert (E1 : v1 = tm_abs A b1 {| reader := r; indirect_reader := i |}).
  { symmetry. eapply multi_from_value; [apply v_abs; exact L1 | exact (proj1 Ev1)]. }
  assert (E2 : v2 = tm_abs A b2 {| reader := r; indirect_reader := i |}).
  { symmetry. eapply multi_from_value; [apply v_abs; exact L2 | exact (proj1 Ev2)]. }
  subst v1 v2. destruct r, i; simpl; try exact I.
  all: intros q a1 a2 Va1 Va2 Ha w1 w2 Ew1 Ew2.
  all: try exact I.
  all: destruct (evaluates_abs_app_inv _ _ _ _ _ _ (v_abs _ _ _ L1) Va1 Ew1)
    as [bval1 [Ebval1 [Bval1 ->]]].
  all: destruct (evaluates_abs_app_inv _ _ _ _ _ _ (v_abs _ _ _ L2) Va2 Ew2)
    as [bval2 [Ebval2 [Bval2 ->]]].
  all: simpl.
  all: pose proof (Hbody a1 a2 Va1 Va2 Ha) as Hbodyrel.
  all: rewrite (protect_value_low bval1), (protect_value_low bval2).
  all: exact (Hbodyrel bval1 bval2 Ebval1 Ebval2).
Qed.

Lemma term_rel_app : forall A B k r f1 f2 a1 a2,
  term_rel (Ty_Arrow A B k) f1 f2 -> term_rel A a1 a2 ->
  term_rel (ty_protect k.(indirect_reader) B)
    (tm_app f1 a1 r) (tm_app f2 a2 r).
Proof.
  intros A B [kr ki] r f1 f2 a1 a2 Hf Ha w1 w2 Ew1 Ew2.
  destruct (evaluates_app_inv _ _ _ _ Ew1)
    as [vf1 [va1 [Evf1 [Eva1 [Vf1 [Va1 Eapp1]]]]]].
  destruct (evaluates_app_inv _ _ _ _ Ew2)
    as [vf2 [va2 [Evf2 [Eva2 [Vf2 [Va2 Eapp2]]]]]].
  pose proof (Hf vf1 vf2 Evf1 Evf2) as Hfr.
  pose proof (Ha va1 va2 Eva1 Eva2) as Har.
  destruct ki.
  - rewrite ty_protect_low. destruct kr; simpl in Hfr.
    all: exact (Hfr r va1 va2 Va1 Va2 Har w1 w2 Eapp1 Eapp2).
  - destruct B; simpl; try exact I; destruct s as [br bi]; destruct br, bi; simpl; exact I.
Qed.

Lemma term_rel_succ : forall k r t1 t2,
  term_rel (Ty_Nat k) t1 t2 ->
  term_rel (ty_protect k.(indirect_reader) (Ty_Nat public))
    (tm_succ t1 r) (tm_succ t2 r).
Proof.
  intros [rr ii] r t1 t2 Hnat w1 w2 Ew1 Ew2.
  destruct (evaluates_succ_inv _ _ _ Ew1) as [n1 [k1 [En1 [F1 O1]]]].
  destruct (evaluates_succ_inv _ _ _ Ew2) as [n2 [k2 [En2 [F2 O2]]]].
  destruct (evaluates_protect_inv _ _ _ O1) as [u1 [Eu1 [Vu1 Q1]]].
  destruct (evaluates_protect_inv _ _ _ O2) as [u2 [Eu2 [Vu2 Q2]]].
  assert (U1 : u1 = tm_nat (S n1) public).
  { symmetry. eapply multi_from_value; [constructor | exact (proj1 Eu1)]. }
  assert (U2 : u2 = tm_nat (S n2) public).
  { symmetry. eapply multi_from_value; [constructor | exact (proj1 Eu2)]. }
  rewrite Q1, Q2, U1, U2. simpl.
  pose proof (Hnat (tm_nat n1 k1) (tm_nat n2 k2) En1 En2) as Hcounts.
  destruct rr, ii; simpl in *; try exact I.
  all: destruct Hcounts as (n & ka & kb & E1 & E2 & S1 & S2).
  all: inversion E1; inversion E2; subst.
  all: pose proof (proj2 S1) as G1; pose proof (proj2 S2) as G2.
  all: apply flows_to_low_inv in G1; apply flows_to_low_inv in G2.
  all: rewrite G1, G2.
  all: unfold public, protect_security, join; simpl.
  all: exists (S n), {| reader := Low; indirect_reader := Low |},
    {| reader := Low; indirect_reader := Low |}; repeat split; try reflexivity; unfold security_le, flows_to; simpl; auto.
Qed.

Lemma term_rel_fst : forall A B k r t1 t2,
  term_rel (Ty_Prod A B k) t1 t2 ->
  term_rel (ty_protect k.(indirect_reader) A) (tm_fst t1 r) (tm_fst t2 r).
Proof.
  intros A B [rr ii] r t1 t2 Hprod w1 w2 Ew1 Ew2.
  destruct (evaluates_fst_inv _ _ _ Ew1) as [p1 [a1 [b1 [s1 [Ep1 [Va1 [Vb1 [P1 O1]]]]]]]].
  destruct (evaluates_fst_inv _ _ _ Ew2) as [p2 [a2 [b2 [s2 [Ep2 [Va2 [Vb2 [P2 O2]]]]]]]].
  destruct (evaluates_protect_inv _ _ _ O1) as [x1 [Ex1 [Vx1 Q1]]].
  destruct (evaluates_protect_inv _ _ _ O2) as [x2 [Ex2 [Vx2 Q2]]].
  assert (X1 : x1 = a1) by (symmetry; eapply multi_from_value; [exact Va1 | exact (proj1 Ex1)]).
  assert (X2 : x2 = a2) by (symmetry; eapply multi_from_value; [exact Va2 | exact (proj1 Ex2)]).
  subst x1 x2. destruct ii.
  - rewrite ty_protect_low. destruct rr; simpl in *.
    all: destruct (Hprod p1 p2 Ep1 Ep2)
      as (c1 & c2 & d1 & d2 & q1 & q2 & E1 & E2 & S1 & S2 & Ha & Hb).
    all: rewrite P1 in E1; inversion E1; subst c1.
    all: rewrite P2 in E2; inversion E2; subst c2.
    all: pose proof (proj2 S1) as F1; pose proof (proj2 S2) as F2.
    all: apply flows_to_low_inv in F1; apply flows_to_low_inv in F2.
    all: rewrite <- H2 in F1; rewrite <- H4 in F2.
    all: rewrite Q1, Q2, F1, F2; rewrite protect_value_low, protect_value_low; exact Ha.
  - apply value_rel_protect_high.
Qed.

Lemma term_rel_snd : forall A B k r t1 t2,
  term_rel (Ty_Prod A B k) t1 t2 ->
  term_rel (ty_protect k.(indirect_reader) B) (tm_snd t1 r) (tm_snd t2 r).
Proof.
  intros A B [rr ii] r t1 t2 Hprod w1 w2 Ew1 Ew2.
  destruct (evaluates_snd_inv _ _ _ Ew1) as [p1 [a1 [b1 [s1 [Ep1 [Va1 [Vb1 [P1 O1]]]]]]]].
  destruct (evaluates_snd_inv _ _ _ Ew2) as [p2 [a2 [b2 [s2 [Ep2 [Va2 [Vb2 [P2 O2]]]]]]]].
  destruct (evaluates_protect_inv _ _ _ O1) as [x1 [Ex1 [Vx1 Q1]]].
  destruct (evaluates_protect_inv _ _ _ O2) as [x2 [Ex2 [Vx2 Q2]]].
  assert (X1 : x1 = b1) by (symmetry; eapply multi_from_value; [exact Vb1 | exact (proj1 Ex1)]).
  assert (X2 : x2 = b2) by (symmetry; eapply multi_from_value; [exact Vb2 | exact (proj1 Ex2)]).
  subst x1 x2. destruct ii.
  - rewrite ty_protect_low. destruct rr; simpl in *.
    all: destruct (Hprod p1 p2 Ep1 Ep2)
      as (c1 & c2 & d1 & d2 & q1 & q2 & E1 & E2 & S1 & S2 & Ha & Hb).
    all: rewrite P1 in E1; inversion E1; subst d1.
    all: rewrite P2 in E2; inversion E2; subst d2.
    all: pose proof (proj2 S1) as F1; pose proof (proj2 S2) as F2.
    all: apply flows_to_low_inv in F1; apply flows_to_low_inv in F2.
    all: rewrite <- H2 in F1; rewrite <- H4 in F2.
    all: rewrite Q1, Q2, F1, F2; rewrite protect_value_low, protect_value_low; exact Hb.
  - apply value_rel_protect_high.
Qed.

Lemma term_rel_case : forall A B T k r s1 s2 l1 l2 r1 r2,
  term_rel (Ty_Sum A B k) s1 s2 ->
  (forall a1 a2, value a1 -> value a2 -> value_rel A a1 a2 ->
     term_rel T (open l1 a1) (open l2 a2)) ->
  (forall b1 b2, value b1 -> value b2 -> value_rel B b1 b2 ->
     term_rel T (open r1 b1) (open r2 b2)) ->
  term_rel (ty_protect k.(indirect_reader) T)
    (tm_case s1 l1 r1 r) (tm_case s2 l2 r2 r).
Proof.
  intros A B T [rr ii] r s1 s2 l1 l2 r1 r2 Hsum Hleft Hright w1 w2 E1 E2.
  all: destruct (evaluates_case_inv _ _ _ _ _ E1)
    as [q1 [Eq1 [[a1 [ka1 [Va1 [C1 O1]]]] | [b1 [kb1 [Vb1 [D1 O1]]]]]]].
  all: destruct (evaluates_case_inv _ _ _ _ _ E2)
    as [q2 [Eq2 [[a2 [ka2 [Va2 [C2 O2]]]] | [b2 [kb2 [Vb2 [D2 O2]]]]]]].
  all: destruct ii.
  all: try solve [apply value_rel_protect_high].
  all: rewrite ty_protect_low.
  all: pose proof (Hsum q1 q2 Eq1 Eq2) as Htmp.
  all: assert (Hshape :
      (exists x1 x2 u1 u2, q1 = tm_inl x1 u1 /\ q2 = tm_inl x2 u2 /\
        security_le u1 {| reader := rr; indirect_reader := Low |} /\
        security_le u2 {| reader := rr; indirect_reader := Low |} /\ value_rel A x1 x2) \/
      (exists x1 x2 u1 u2, q1 = tm_inr x1 u1 /\ q2 = tm_inr x2 u2 /\
        security_le u1 {| reader := rr; indirect_reader := Low |} /\
        security_le u2 {| reader := rr; indirect_reader := Low |} /\ value_rel B x1 x2))
    by (destruct rr; simpl in Htmp; exact Htmp).
  all: destruct Hshape as [HL | HR].
  all: try destruct HL as (x1 & x2 & u1 & u2 & EHL1 & EHL2 & SL1 & SL2 & Hpayload).
  all: try destruct HR as (x1 & x2 & u1 & u2 & EHR1 & EHR2 & SR1 & SR2 & Hpayload).
  all: try congruence.
  all: try (rewrite C1 in EHL1; injection EHL1 as Ex1 Hk1; subst x1 u1).
  all: try (rewrite C2 in EHL2; injection EHL2 as Ex2 Hk2; subst x2 u2).
  all: try (rewrite D1 in EHL1; discriminate).
  all: try (rewrite D2 in EHL2; discriminate).
  all: try (rewrite D1 in EHR1; injection EHR1 as Ex1 Hk1; subst x1 u1).
  all: try (rewrite D2 in EHR2; injection EHR2 as Ex2 Hk2; subst x2 u2).
  all: try (rewrite C1 in EHR1; discriminate).
  all: try (rewrite C2 in EHR2; discriminate).
  all: destruct (evaluates_protect_inv _ _ _ O1) as [z1 [Ez1 [Vz1 Qz1]]].
  all: destruct (evaluates_protect_inv _ _ _ O2) as [z2 [Ez2 [Vz2 Qz2]]].
  all: try (pose proof (proj2 SL1) as G1; pose proof (proj2 SL2) as G2).
  all: try (pose proof (proj2 SR1) as G1; pose proof (proj2 SR2) as G2).
  all: apply flows_to_low_inv in G1; apply flows_to_low_inv in G2.
  all: rewrite Qz1, Qz2, G1, G2, protect_value_low, protect_value_low.
  all: try exact ((Hleft a1 a2 Va1 Va2 Hpayload) z1 z2 Ez1 Ez2).
  all: exact ((Hright b1 b2 Vb1 Vb2 Hpayload) z1 z2 Ez1 Ez2).
Qed.

Theorem fundamental : forall Gamma t T, has_type Gamma t T ->
  forall rho1 rho2,
    environment_rel Gamma rho1 rho2 ->
    (forall x, locally_closed (rho1 x)) ->
    (forall x, locally_closed (rho2 x)) ->
    term_rel T (instantiate rho1 t) (instantiate rho2 t).
Proof.
  intros Gamma t T Htyping. induction Htyping;
    intros rho1 rho2 Henv Hlc1 Hlc2; simpl.
  - eapply Henv; eauto.
  - destruct kappa as [rr ii]. simpl.
    eapply term_rel_value; [constructor | constructor |].
    destruct rr, ii; simpl; try exact I.
    all: split; [eexists; reflexivity | eexists; reflexivity].
  - assert (LC1 : locally_closed (instantiate rho1 (tm_abs T1 body kappa))).
    { assert (Habs : has_type Gamma (tm_abs T1 body kappa) (Ty_Arrow T1 T2 kappa)) by (econstructor; eauto).
      eapply instantiate_lc; [eapply has_type_locally_closed; exact Habs | exact Hlc1]. }
    assert (LC2 : locally_closed (instantiate rho2 (tm_abs T1 body kappa))).
    { assert (Habs : has_type Gamma (tm_abs T1 body kappa) (Ty_Arrow T1 T2 kappa)) by (econstructor; eauto).
      eapply instantiate_lc; [eapply has_type_locally_closed; exact Habs | exact Hlc2]. }
    apply term_rel_abs; [exact LC1 | exact LC2 |].
    intros a1 a2 Va1 Va2 Harg.
    destruct (exists_fresh_atom (L ++ fv body)) as [x Hx].
    assert (HxL : ~ In x L) by (intro Q; apply Hx; apply in_or_app; left; exact Q).
    assert (HxF : ~ In x (fv body)) by (intro Q; apply Hx; apply in_or_app; right; exact Q).
    specialize (H2 x HxL
      (extend_env rho1 x a1) (extend_env rho2 x a2)
      (environment_rel_extend _ _ _ _ _ _ _ Henv
        (term_rel_value _ _ _ Va1 Va2 Harg))).
    assert (Hext1 : forall y, locally_closed (extend_env rho1 x a1 y)).
    { intro y. unfold extend_env. destruct (Nat.eqb x y); [exact (value_locally_closed _ Va1) | apply Hlc1]. }
    assert (Hext2 : forall y, locally_closed (extend_env rho2 x a2 y)).
    { intro y. unfold extend_env. destruct (Nat.eqb x y); [exact (value_locally_closed _ Va2) | apply Hlc2]. }
    specialize (H2 Hext1 Hext2).
    rewrite (instantiate_open_extend rho1 body x a1 Hlc1 HxF (value_locally_closed _ Va1)) in H2.
    rewrite (instantiate_open_extend rho2 body x a2 Hlc2 HxF (value_locally_closed _ Va2)) in H2.
    exact H2.
  - eapply term_rel_app; [eapply IHHtyping1; eauto | eapply IHHtyping2; eauto].
  - eapply term_rel_pair; [eapply IHHtyping1; eauto | eapply IHHtyping2; eauto].
  - eapply term_rel_fst. eapply IHHtyping; eauto.
  - eapply term_rel_snd. eapply IHHtyping; eauto.
  - eapply term_rel_inl. eapply IHHtyping; eauto.
  - eapply term_rel_inr. eapply IHHtyping; eauto.
  - eapply term_rel_case.
    + eapply IHHtyping; eauto.
    + intros a1 a2 Va1 Va2 Hrel.
      destruct (exists_fresh_atom (L ++ fv body1)) as [x0 Hx].
      assert (HxL : ~ In x0 L) by (intro Q; apply Hx; apply in_or_app; left; exact Q).
      assert (HxF : ~ In x0 (fv body1)) by (intro Q; apply Hx; apply in_or_app; right; exact Q).
      assert (Hext1 : forall y, locally_closed (extend_env rho1 x0 a1 y)).
      { intro y. unfold extend_env. destruct (Nat.eqb x0 y); [exact (value_locally_closed _ Va1) | apply Hlc1]. }
      assert (Hext2 : forall y, locally_closed (extend_env rho2 x0 a2 y)).
      { intro y. unfold extend_env. destruct (Nat.eqb x0 y); [exact (value_locally_closed _ Va2) | apply Hlc2]. }
      match goal with
      | IH : forall x1 : atom, ~ In x1 L -> forall q1 q2,
          environment_rel (update Gamma x1 T1) q1 q2 ->
          (forall y, locally_closed (q1 y)) -> (forall y, locally_closed (q2 y)) ->
          term_rel T (instantiate q1 (open body1 (tm_fvar x1)))
                    (instantiate q2 (open body1 (tm_fvar x1))) |- _ =>
          pose proof (IH x0 HxL (extend_env rho1 x0 a1) (extend_env rho2 x0 a2)
            (environment_rel_extend _ _ _ _ _ _ _ Henv
              (term_rel_value _ _ _ Va1 Va2 Hrel)) Hext1 Hext2) as Hopened
      end.
      rewrite (instantiate_open_extend rho1 body1 x0 a1 Hlc1 HxF (value_locally_closed _ Va1)) in Hopened.
      rewrite (instantiate_open_extend rho2 body1 x0 a2 Hlc2 HxF (value_locally_closed _ Va2)) in Hopened.
      exact Hopened.
    + intros b1 b2 Vb1 Vb2 Hrel.
      destruct (exists_fresh_atom (L ++ fv body2)) as [x0 Hx].
      assert (HxL : ~ In x0 L) by (intro Q; apply Hx; apply in_or_app; left; exact Q).
      assert (HxF : ~ In x0 (fv body2)) by (intro Q; apply Hx; apply in_or_app; right; exact Q).
      assert (Hext1 : forall y, locally_closed (extend_env rho1 x0 b1 y)).
      { intro y. unfold extend_env. destruct (Nat.eqb x0 y); [exact (value_locally_closed _ Vb1) | apply Hlc1]. }
      assert (Hext2 : forall y, locally_closed (extend_env rho2 x0 b2 y)).
      { intro y. unfold extend_env. destruct (Nat.eqb x0 y); [exact (value_locally_closed _ Vb2) | apply Hlc2]. }
      match goal with
      | IH : forall x1 : atom, ~ In x1 L -> forall q1 q2,
          environment_rel (update Gamma x1 T2) q1 q2 ->
          (forall y, locally_closed (q1 y)) -> (forall y, locally_closed (q2 y)) ->
          term_rel T (instantiate q1 (open body2 (tm_fvar x1)))
                    (instantiate q2 (open body2 (tm_fvar x1))) |- _ =>
          pose proof (IH x0 HxL (extend_env rho1 x0 b1) (extend_env rho2 x0 b2)
            (environment_rel_extend _ _ _ _ _ _ _ Henv
              (term_rel_value _ _ _ Vb1 Vb2 Hrel)) Hext1 Hext2) as Hopened
      end.
      rewrite (instantiate_open_extend rho1 body2 x0 b1 Hlc1 HxF (value_locally_closed _ Vb1)) in Hopened.
      rewrite (instantiate_open_extend rho2 body2 x0 b2 Hlc2 HxF (value_locally_closed _ Vb2)) in Hopened.
      exact Hopened.
  - eapply term_rel_protect. eapply IHHtyping; eauto.
  - intros v1 v2 Ev1 Ev2. eapply value_rel_subtype.
    + match goal with Hsub : subtype _ _ |- _ => exact Hsub end.
    + eapply IHHtyping; eauto.
  - destruct k as [rr ii]. simpl.
    pose (kk := {| reader := rr; indirect_reader := ii |}).
    eapply term_rel_value; [constructor | constructor |].
    destruct rr, ii; simpl; try exact I.
    all: exists n, kk, kk.
    all: repeat split; try reflexivity; unfold security_le, flows_to; simpl; auto.
  - eapply term_rel_succ. eapply IHHtyping; eauto.
  -
Admitted.

Theorem noninterference : forall (C : program_context) (t1 t2 : tm)
    (T_secret T_result : ty),
  has_type empty t1 T_secret ->
  has_type empty t2 T_secret ->
  context_has_type C T_secret T_result ->
  ground T_result ->
  transparent T_result ->
  ~ flows_to (security_of T_secret).(indirect_reader)
      (security_of T_result).(indirect_reader) ->
  same_result (plug C t1) (plug C t2).
Proof.
Admitted.
