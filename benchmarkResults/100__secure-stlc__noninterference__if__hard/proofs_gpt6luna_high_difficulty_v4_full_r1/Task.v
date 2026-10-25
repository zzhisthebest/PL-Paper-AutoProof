From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
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

Inductive ty : Type :=
  | Ty_Unit : security -> ty
  | Ty_Sum : ty -> ty -> security -> ty
  | Ty_Prod : ty -> ty -> security -> ty
  | Ty_Arrow : ty -> ty -> security -> ty.

Definition security_of (T : ty) : security :=
  match T with
  | Ty_Unit kappa => kappa
  | Ty_Sum _ _ kappa | Ty_Prod _ _ kappa | Ty_Arrow _ _ kappa => kappa
  end.

Definition ty_protect (l : label) (T : ty) : ty :=
  match T with
  | Ty_Unit kappa => Ty_Unit (protect_security kappa l)
  | Ty_Sum T1 T2 kappa => Ty_Sum T1 T2 (protect_security kappa l)
  | Ty_Prod T1 T2 kappa => Ty_Prod T1 T2 (protect_security kappa l)
  | Ty_Arrow T1 T2 kappa => Ty_Arrow T1 T2 (protect_security kappa l)
  end.

Fixpoint wf_ty (T : ty) : Prop :=
  match T with
  | Ty_Unit kappa => wf_security kappa
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
  | tm_if : tm -> tm -> tm -> label -> tm.

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
  | tm_if c yes no r => tm_if (open_rec k u c) (open_rec k u yes) (open_rec k u no) r
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
  | tm_if c yes no r => tm_if (subst x u c) (subst x u yes) (subst x u no) r
  end.

Fixpoint fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_unit _ => []
  | tm_fvar x => [x]
  | tm_abs _ body _ => fv body
  | tm_app t1 t2 _ | tm_pair t1 t2 _ => fv t1 ++ fv t2
  | tm_fst t1 _ | tm_snd t1 _ | tm_inl t1 _ | tm_inr t1 _
  | tm_protect _ t1 => fv t1
  | tm_case t0 body1 body2 _ | tm_if t0 body1 body2 _ => fv t0 ++ fv body1 ++ fv body2
  end.

Fixpoint lc_at (k : nat) (t : tm) : Prop :=
  match t with
  | tm_bvar i => i < k
  | tm_fvar _ | tm_unit _ => True
  | tm_abs _ body _ => lc_at (S k) body
  | tm_app t1 t2 _ | tm_pair t1 t2 _ => lc_at k t1 /\ lc_at k t2
  | tm_fst t1 _ | tm_snd t1 _ | tm_inl t1 _ | tm_inr t1 _
  | tm_protect _ t1 => lc_at k t1
  | tm_case t0 body1 body2 _ =>
      lc_at k t0 /\ lc_at (S k) body1 /\ lc_at (S k) body2
  | tm_if c yes no _ => lc_at k c /\ lc_at k yes /\ lc_at k no
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
  | v_inr : forall v kappa, value v -> value (tm_inr v kappa).

Lemma value_locally_closed : forall v, value v -> locally_closed v.
Proof. intros v Hv. induction Hv; unfold locally_closed in *; simpl; auto. Qed.

Definition protect_value (v : tm) (l : label) : tm :=
  match v with
  | tm_unit kappa => tm_unit (protect_security kappa l)
  | tm_abs T body kappa => tm_abs T body (protect_security kappa l)
  | tm_pair v1 v2 kappa => tm_pair v1 v2 (protect_security kappa l)
  | tm_inl v1 kappa => tm_inl v1 (protect_security kappa l)
  | tm_inr v1 kappa => tm_inr v1 (protect_security kappa l)
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
  | tm_if c yes no _ => tm_if (erase_security c) (erase_security yes) (erase_security no) Low
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
  | ST_If : forall c c' yes no r,
      c --> c' -> tm_if c yes no r --> tm_if c' yes no r
  | ST_IfTrue : forall v k yes no r,
      value v -> flows_to k.(reader) r ->
      tm_if (tm_inl v k) yes no r --> tm_protect k.(indirect_reader) yes
  | ST_IfFalse : forall v k yes no r,
      value v -> flows_to k.(reader) r ->
      tm_if (tm_inr v k) yes no r --> tm_protect k.(indirect_reader) no
where "t '-->' t'" := (step t t').

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall t, multi t t
  | multi_step : forall t1 t2 t3,
      step t1 t2 -> multi t2 t3 -> multi t1 t3.

Notation "t '-->*' t'" := (multi t t') (at level 40).

Definition evaluates (t v : tm) : Prop := t -->* v /\ value v.

Lemma value_no_step : forall v v', value v -> ~ step v v'.
Proof.
  intros v v' Hv. revert v'. induction Hv; intros v' Hs; inversion Hs; subst;
    try contradiction; try (exfalso; eapply IHHv1; eassumption);
    try (exfalso; eapply IHHv2; eassumption); eauto;
    try match goal with
    | IH : forall z, ~ step ?u z, H : step ?u ?w |- False => exact (IH _ H)
    end.
Qed.

Lemma step_deterministic : forall t t1 t2,
  step t t1 -> step t t2 -> t1 = t2.
Proof.
  intros t t1 t2 H1. generalize dependent t2.
  induction H1; intros z H2; inversion H2; subst; try reflexivity;
    try solve [match goal with
      | Hv : value ?u, Hs : step ?u ?w |- _ =>
          exfalso; exact (value_no_step u w Hv Hs)
      end];
    try solve [match goal with
      | Hs : step (tm_pair ?a ?b ?k) ?w, Ha : value ?a, Hb : value ?b |- _ =>
          let Hp := fresh "Hp" in
          assert (Hp : value (tm_pair a b k)) by (eapply v_pair; eassumption);
          exfalso; exact (value_no_step _ _ Hp Hs)
      | Hs : step (tm_inl ?a ?k) ?w, Ha : value ?a |- _ =>
          let Hp := fresh "Hp" in
          assert (Hp : value (tm_inl a k)) by (eapply v_inl; eassumption);
          exfalso; exact (value_no_step _ _ Hp Hs)
      | Hs : step (tm_inr ?a ?k) ?w, Ha : value ?a |- _ =>
          let Hp := fresh "Hp" in
          assert (Hp : value (tm_inr a k)) by (eapply v_inr; eassumption);
          exfalso; exact (value_no_step _ _ Hp Hs)
      end];
    try solve [f_equal; eauto].
Qed.

Lemma multi_from_value : forall v v',
  value v -> multi v v' -> v = v'.
Proof.
  intros v v' Hv Hm. induction Hm.
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
Qed.

Lemma multi_value_deterministic : forall t v1 v2,
  multi t v1 -> value v1 -> multi t v2 -> value v2 -> v1 = v2.
Proof.
  intros t v1 v2 H1. generalize dependent v2.
  induction H1; intros v2 Hv1 H2 Hv2.
  - eapply multi_from_value; eauto.
  - inversion H2; subst.
    + exfalso. eapply value_no_step; eauto.
    + assert (t2 = t4) by (eapply step_deterministic; eauto). subst.
      eapply IHmulti; eauto.
Qed.

Lemma evaluates_pair_inv : forall t1 t2 k w,
  evaluates (tm_pair t1 t2 k) w ->
  exists v1 v2, evaluates t1 v1 /\ evaluates t2 v2 /\
    w = tm_pair v1 v2 k.
Proof.
  intros t1 t2 k w [Hm Hv].
  remember (tm_pair t1 t2 k) as start eqn:E.
  revert t1 t2 k E.
  induction Hm; intros a b q E.
  - inversion E; subst. inversion Hv; subst.
    exists a, b. repeat split; try constructor; assumption.
  - inversion E; subst. inversion H; subst.
    + destruct (IHHm Hv t1' b q eq_refl) as [v1 [v2 [Ev1 [Ev2 Eout]]]].
      exists v1, v2. split.
      * destruct Ev1 as [M V]. split; [econstructor; eassumption|exact V].
      * split; assumption.
    + destruct (IHHm Hv a t2' q eq_refl) as [u1 [u2 [Eu1 [Eu2 Eout]]]].
      assert (a = u1) by (eapply multi_from_value; [exact H5|exact (proj1 Eu1)]).
      subst u1. exists a, u2. split.
      * split; [constructor|exact H5].
      * split.
        -- destruct Eu2 as [M V]. split; [econstructor; eassumption|exact V].
        -- exact Eout.
Qed.

Lemma evaluates_inl_inv : forall t k w,
  evaluates (tm_inl t k) w ->
  exists v, evaluates t v /\ w = tm_inl v k.
Proof.
  intros t k w [Hm Hv]. remember (tm_inl t k) as start eqn:E.
  revert t k E. induction Hm; intros a q E.
  - inversion E; subst. inversion Hv; subst.
    exists a. split; [split; [constructor|assumption]|reflexivity].
  - inversion E; subst. inversion H; subst.
    destruct (IHHm Hv t' q eq_refl) as [v [Ev Eout]].
    exists v. split; [|exact Eout].
    destruct Ev as [M V]. split; [econstructor; eassumption|exact V].
Qed.

Lemma evaluates_inr_inv : forall t k w,
  evaluates (tm_inr t k) w ->
  exists v, evaluates t v /\ w = tm_inr v k.
Proof.
  intros t k w [Hm Hv]. remember (tm_inr t k) as start eqn:E.
  revert t k E. induction Hm; intros a q E.
  - inversion E; subst. inversion Hv; subst.
    exists a. split; [split; [constructor|assumption]|reflexivity].
  - inversion E; subst. inversion H; subst.
    destruct (IHHm Hv t' q eq_refl) as [v [Ev Eout]].
    exists v. split; [|exact Eout].
    destruct Ev as [M V]. split; [econstructor; eassumption|exact V].
Qed.

Lemma evaluates_app_inv : forall t1 t2 r w,
  evaluates (tm_app t1 t2 r) w ->
  exists T b k va,
    evaluates t1 (tm_abs T b k) /\ evaluates t2 va /\ value va /\
    flows_to k.(reader) r /\
    evaluates (tm_protect k.(indirect_reader) (open b va)) w.
Proof.
  intros t1 t2 r w [Hm Hv].
  remember (tm_app t1 t2 r) as start eqn:E.
  revert t1 t2 r E.
  induction Hm; intros a b rr E.
  - inversion E; subst. inversion Hv.
  - inversion E; subst. inversion H; subst.
    + exists T, body, kappa, b. split.
      * split; [constructor|exact H4].
      * split.
        -- split; [constructor|exact H6].
        -- split; [exact H6|].
           split; [exact H7|].
           split; [exact Hm|exact Hv].
    + destruct (IHHm Hv t1' b rr eq_refl)
        as [T0 [body0 [k0 [va [Efun [Earg [Hva [Hflow Ebody]]]]]]]].
      exists T0, body0, k0, va. split.
      * destruct Efun as [M V]. split; [econstructor; eassumption|exact V].
      * split; [exact Earg|]. split; [exact Hva|].
        split; [exact Hflow|exact Ebody].
    + destruct (IHHm Hv a t2' rr eq_refl)
        as [T [body [k [va [Efun [Earg [Hva [Hflow Ebody]]]]]]]].
      assert (a = tm_abs T body k) as Eabs.
      { eapply multi_from_value; [exact H5|exact (proj1 Efun)]. }
      subst a. exists T, body, k, va. split.
      * split; [constructor|exact H5].
      * split.
        -- destruct Earg as [M V]. split; [econstructor; eassumption|exact V].
        -- split; [exact Hva|]. split; [exact Hflow|exact Ebody].
Qed.

Lemma evaluates_protect_inv : forall l t w,
  evaluates (tm_protect l t) w ->
  exists v, evaluates t v /\ evaluates (protect_value v l) w.
Proof.
  intros l t w [Hm Hv]. remember (tm_protect l t) as start eqn:E.
  revert t E. induction Hm; intros a E.
  - inversion E; subst. inversion Hv.
  - inversion E; subst. inversion H; subst.
    + exists a. split; [split; [constructor|exact H4]|]. exact (conj Hm Hv).
    + destruct (IHHm Hv t' eq_refl) as [v [Ev Eout]].
      exists v. split; [|exact Eout].
      destruct Ev as [M V]. split; [econstructor; eassumption|exact V].
Qed.

Lemma evaluates_fst_inv : forall t r w,
  evaluates (tm_fst t r) w ->
  exists v1 v2 k,
    evaluates t (tm_pair v1 v2 k) /\ value v1 /\ value v2 /\
    flows_to k.(reader) r /\ evaluates (tm_protect k.(indirect_reader) v1) w.
Proof.
  intros t r w [Hm Hv]. remember (tm_fst t r) as start eqn:E.
  revert t r E. induction Hm; intros a rr E.
  - inversion E; subst. inversion Hv.
  - inversion E; subst. inversion H; subst.
    +
      exists v1, v2, kappa. split.
      * split; [constructor|constructor; assumption].
      * split; [exact H3|]. split; [exact H4|]. split; [exact H6|].
        exact (conj Hm Hv).
    + destruct (IHHm Hv t' rr eq_refl) as [v1 [v2 [k [Et [Hv1 [Hv2 [Hflow Eout]]]]]]].
      exists v1, v2, k. split.
      * destruct Et as [M V]. split; [econstructor; eassumption|exact V].
      * exact (conj Hv1 (conj Hv2 (conj Hflow Eout))).
Qed.

Lemma evaluates_snd_inv : forall t r w,
  evaluates (tm_snd t r) w ->
  exists v1 v2 k,
    evaluates t (tm_pair v1 v2 k) /\ value v1 /\ value v2 /\
    flows_to k.(reader) r /\ evaluates (tm_protect k.(indirect_reader) v2) w.
Proof.
  intros t r w [Hm Hv]. remember (tm_snd t r) as start eqn:E.
  revert t r E. induction Hm; intros a rr E.
  - inversion E; subst. inversion Hv.
  - inversion E; subst. inversion H; subst.
    + exists v1, v2, kappa. split.
      * split; [constructor|constructor; assumption].
      * split; [exact H3|]. split; [exact H4|]. split; [exact H6|].
        exact (conj Hm Hv).
    + destruct (IHHm Hv t' rr eq_refl)
        as [v1 [v2 [k [Et [Hv1 [Hv2 [Hflow Eout]]]]]]].
      exists v1, v2, k. split.
      * destruct Et as [M V]. split; [econstructor; eassumption|exact V].
      * exact (conj Hv1 (conj Hv2 (conj Hflow Eout))).
Qed.

Lemma evaluates_case_inv : forall t b1 b2 r w,
  evaluates (tm_case t b1 b2 r) w ->
  (exists v k, evaluates t (tm_inl v k) /\ value v /\
     flows_to k.(reader) r /\
     evaluates (tm_protect k.(indirect_reader) (open b1 v)) w) \/
  (exists v k, evaluates t (tm_inr v k) /\ value v /\
     flows_to k.(reader) r /\
     evaluates (tm_protect k.(indirect_reader) (open b2 v)) w).
Proof.
  intros t b1 b2 r w [Hm Hv]. remember (tm_case t b1 b2 r) as start eqn:E.
  revert t b1 b2 r E. induction Hm; intros a b c rr E.
  - inversion E; subst. inversion Hv.
  - inversion E; subst. inversion H; subst.
    + left. exists v, kappa. split.
      * split; [exact (multi_refl _)|constructor; exact H6].
      * split; [exact H6|]. split; [exact H7|exact (conj Hm Hv)].
    + right. exists v, kappa. split.
      * split; [exact (multi_refl _)|constructor; exact H6].
      * split; [exact H6|]. split; [exact H7|exact (conj Hm Hv)].
    + destruct (IHHm Hv t' b c rr eq_refl) as [Hleft|Hright].
      * left. destruct Hleft as [v0 [k [Et [V [F Eout]]]]].
        exists v0, k. split.
        -- destruct Et as [M Vt]. split; [econstructor; eassumption|exact Vt].
        -- exact (conj V (conj F Eout)).
      * right. destruct Hright as [v0 [k [Et [V [F Eout]]]]].
        exists v0, k. split.
        -- destruct Et as [M Vt]. split; [econstructor; eassumption|exact Vt].
        -- exact (conj V (conj F Eout)).
Qed.

Lemma evaluates_if_inv : forall c yes no r w,
  evaluates (tm_if c yes no r) w ->
  (exists v k, evaluates c (tm_inl v k) /\ value v /\
      flows_to k.(reader) r /\
      evaluates (tm_protect k.(indirect_reader) yes) w) \/
  (exists v k, evaluates c (tm_inr v k) /\ value v /\
      flows_to k.(reader) r /\
      evaluates (tm_protect k.(indirect_reader) no) w).
Proof.
  intros c yes no r w [Hm Hv]. remember (tm_if c yes no r) as start eqn:E.
  revert c yes no r E. induction Hm; intros a y n rr E.
  - inversion E; subst. inversion Hv.
  - inversion E; subst. inversion H; subst.
    + destruct (IHHm Hv c' y n rr eq_refl) as [Hleft|Hright].
      * left. destruct Hleft as [v0 [k [Ec [V [F Eout]]]]].
        exists v0, k. split.
        -- destruct Ec as [M Vc]. split; [econstructor; eassumption|exact Vc].
        -- exact (conj V (conj F Eout)).
      * right. destruct Hright as [v0 [k [Ec [V [F Eout]]]]].
        exists v0, k. split.
        -- destruct Ec as [M Vc]. split; [econstructor; eassumption|exact Vc].
        -- exact (conj V (conj F Eout)).
    + left. exists v, k. split.
      * split; [exact (multi_refl _)|apply v_inl; exact H6].
      * split; [exact H6|]. split; [exact H7|exact (conj Hm Hv)].
    + right. exists v, k. split.
      * split; [exact (multi_refl _)|apply v_inr; exact H6].
      * split; [exact H6|]. split; [exact H7|exact (conj Hm Hv)].
Qed.

Lemma flows_to_transitive : forall a b c,
  flows_to a b -> flows_to b c -> flows_to a c.
Proof. destruct a, b, c; simpl; intuition. Qed.

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
  | S_Trans : forall T U V, subtype T U -> subtype U V -> subtype T V.

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
  | T_If : forall Gamma c yes no k T r,
      has_type Gamma c (Ty_Sum (Ty_Unit public) (Ty_Unit public) k) ->
      has_type Gamma yes T -> has_type Gamma no T -> flows_to k.(reader) r ->
      has_type Gamma (tm_if c yes no r) (ty_protect k.(indirect_reader) T).

Lemma subtype_indirect_flow : forall T U,
  subtype T U -> flows_to (security_of T).(indirect_reader)
                         (security_of U).(indirect_reader).
Proof.
  intros T U H. induction H.
  - exact (proj2 H1).
  - exact (proj2 H3).
  - exact (proj2 H3).
  - exact (proj2 H3).
  - eapply flows_to_transitive; eauto.
Qed.

Fixpoint max_atom (L : list atom) : atom :=
  match L with [] => 0 | x :: L' => Nat.max x (max_atom L') end.

Lemma in_le_max_atom : forall x L, In x L -> x <= max_atom L.
Proof.
  intros x L. induction L as [|a L IH]; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [->|Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

Lemma fresh_not_in : forall L, ~ In (S (max_atom L)) L.
Proof.
  intros L Hin. pose proof (in_le_max_atom _ _ Hin). lia.
Qed.

Lemma typed_hole_implies_indirect_flow : forall x T U,
  has_type (update empty x T) (tm_fvar x) U ->
  flows_to (security_of T).(indirect_reader)
           (security_of U).(indirect_reader).
Proof.
  intros x T U Hty. remember (update empty x T) as Gamma eqn:EG.
  remember (tm_fvar x) as term eqn:E.
  induction Hty; inversion E; subst.
  - simpl in H. rewrite Nat.eqb_refl in H. inversion H; subst.
    destruct (security_of T0).(indirect_reader); exact I.
  - eapply flows_to_transitive; eauto using subtype_indirect_flow.
Qed.

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
  | C_IfCondition : program_context -> tm -> tm -> label -> program_context
  | C_IfThen : tm -> program_context -> tm -> label -> program_context
  | C_IfElse : tm -> tm -> program_context -> label -> program_context.

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
  | C_IfCondition C' y n r => tm_if (plug C' t) y n r
  | C_IfThen c C' n r => tm_if c (plug C' t) n r
  | C_IfElse c y C' r => tm_if c y (plug C' t) r
  end.

Definition context_has_type (C : program_context) (T_hole T_result : ty) : Prop :=
  exists L : list atom, forall x : atom, ~ In x L ->
    has_type (update empty x T_hole) (plug C (tm_fvar x)) T_result.

Lemma hole_context_forces_flow : forall T U,
  context_has_type C_Hole T U ->
  flows_to (security_of T).(indirect_reader)
           (security_of U).(indirect_reader).
Proof.
  intros T U [L Hctx].
  pose (x := S (max_atom L)).
  specialize (Hctx x (fresh_not_in L)). simpl in Hctx.
  eapply typed_hole_implies_indirect_flow. exact Hctx.
Qed.

Fixpoint ground (T : ty) : Prop :=
  match T with
  | Ty_Unit _ => True
  | Ty_Sum T1 T2 _ | Ty_Prod T1 T2 _ => ground T1 /\ ground T2
  | Ty_Arrow _ _ _ => False
  end.

Fixpoint transparent_at (kappa : security) (T : ty) : Prop :=
  security_le (security_of T) kappa /\
  match T with
  | Ty_Unit _ => True
  | Ty_Sum T1 T2 _ | Ty_Prod T1 T2 _ | Ty_Arrow T1 T2 _ =>
      transparent_at kappa T1 /\ transparent_at kappa T2
  end.

Definition transparent (T : ty) : Prop := transparent_at (security_of T) T.

Definition same_result (t1 t2 : tm) : Prop :=
  forall v1 v2 : tm,
    evaluates t1 v1 -> evaluates t2 v2 ->
    erase_security v1 = erase_security v2.

Lemma hole_noninterference : forall t1 t2 T U,
  has_type empty t1 T -> has_type empty t2 T ->
  context_has_type C_Hole T U ->
  ~ flows_to (security_of T).(indirect_reader)
      (security_of U).(indirect_reader) ->
  same_result t1 t2.
Proof.
  intros t1 t2 T U _ _ HC Hnf. exfalso. apply Hnf.
  eapply hole_context_forces_flow; eauto.
Qed.

(* The observer-indexed value relation used by the noninterference proof.
   At a type whose indirect-reader is hidden from the observer, all values
   are related.  Visible sums and products are compared componentwise;
   visible functions are compared by their behavior on related arguments. *)
Definition visible_to (k : security) (l : label) : bool :=
  match k.(indirect_reader), l with
  | High, Low => false
  | _, _ => true
  end.

Fixpoint value_rel_with (l extra : label) (T : ty) (v1 v2 : tm) {struct T} : Prop :=
  if visible_to (protect_security (security_of T) extra) l then
    match T with
    | Ty_Unit _ => exists k1 k2, v1 = tm_unit k1 /\ v2 = tm_unit k2
    | Ty_Sum T1 T2 _ =>
        (exists a1 a2 k1 k2, v1 = tm_inl a1 k1 /\ v2 = tm_inl a2 k2 /\
          value_rel_with l Low T1 a1 a2) \/
        (exists a1 a2 k1 k2, v1 = tm_inr a1 k1 /\ v2 = tm_inr a2 k2 /\
          value_rel_with l Low T2 a1 a2)
    | Ty_Prod T1 T2 _ =>
        exists a1 a2 b1 b2 k1 k2,
          v1 = tm_pair a1 a2 k1 /\ v2 = tm_pair b1 b2 k2 /\
          value_rel_with l Low T1 a1 b1 /\ value_rel_with l Low T2 a2 b2
    | Ty_Arrow T1 T2 k =>
        let kp := protect_security k extra in
        exists b1 b2, v1 = tm_abs T1 b1 kp /\ v2 = tm_abs T1 b2 kp /\
        value v1 /\ value v2 /\ forall a1 a2 w1 w2,
          value_rel_with l Low T1 a1 a2 ->
          value a1 -> value a2 ->
          evaluates (open b1 a1) w1 ->
          evaluates (open b2 a2) w2 ->
          value_rel_with l Low T2 w1 w2
    end
  else value v1 /\ value v2.

Definition value_rel (l : label) (T : ty) (v1 v2 : tm) : Prop :=
  value_rel_with l Low T v1 v2.

Lemma value_rel_with_values : forall l extra T v1 v2,
  value_rel_with l extra T v1 v2 -> value v1 /\ value v2.
Proof.
  intros l extra T. revert extra. induction T; intros extra v1 v2 Hrel;
    unfold value_rel_with in Hrel; simpl in Hrel.
  - destruct (visible_to (protect_security s extra) l) eqn:E.
    + destruct Hrel as [k1 [k2 [-> ->]]]. split; constructor.
    + exact Hrel.
  - destruct (visible_to (protect_security s extra) l) eqn:E.
    + destruct Hrel as [[a1 [a2 [k1 [k2 [-> [-> Hr]]]]]]|
                        [a1 [a2 [k1 [k2 [-> [-> Hr]]]]]]].
      * destruct (IHT1 Low a1 a2 Hr) as [V1 V2]. split; constructor; assumption.
      * destruct (IHT2 Low a1 a2 Hr) as [V1 V2]. split; constructor; assumption.
    + exact Hrel.
  - destruct (visible_to (protect_security s extra) l) eqn:E.
    + destruct Hrel as [a1 [a2 [b1 [b2 [k1 [k2 [-> [-> [H1 H2]]]]]]]]].
      destruct (IHT1 Low a1 b1 H1) as [Va1 Vb1].
      destruct (IHT2 Low a2 b2 H2) as [Va2 Vb2].
      split; constructor; assumption.
    + exact Hrel.
  - destruct (visible_to (protect_security s extra) l) eqn:E.
    + destruct Hrel as [b1 [b2 [-> [-> [V1 [V2 Hfn]]]]]].
      exact (conj V1 V2).
    + exact Hrel.
Qed.

Lemma value_rel_protect : forall l q T v1 v2,
  value_rel l (ty_protect q T) v1 v2 <->
  value_rel_with l q T v1 v2.
Proof.
  intros l q T v1 v2. destruct T as [k|T1 T2 k|T1 T2 k|T1 T2 k];
    destruct k as [[|] [|]]; destruct q; unfold value_rel;
    cbn [value_rel_with ty_protect protect_security join]; reflexivity.
Qed.

Lemma protect_security_indirect_join : forall k l,
  (protect_security k l).(indirect_reader) = join k.(indirect_reader) l.
Proof. reflexivity. Qed.

Lemma join_low_flows_left : forall l1 l2 l,
  flows_to (join l1 l2) l -> flows_to l1 l.
Proof. destruct l1, l2, l; simpl; intuition. Qed.

Lemma join_low_flows_right : forall l1 l2 l,
  flows_to (join l1 l2) l -> flows_to l2 l.
Proof. destruct l1, l2, l; simpl; intuition. Qed.

Lemma visible_to_iff : forall k l,
  visible_to k l = true <-> flows_to k.(indirect_reader) l.
Proof. destruct k as [r [|]], l; simpl; intuition. Qed.

Lemma subtype_visible : forall T U l,
  subtype T U -> visible_to (security_of U) l = true ->
  visible_to (security_of T) l = true.
Proof.
  intros T U l Hsub Hv. apply visible_to_iff.
  eapply flows_to_transitive.
  - exact (subtype_indirect_flow _ _ Hsub).
  - apply visible_to_iff. exact Hv.
Qed.

Lemma visible_to_protect_low : forall k l,
  visible_to (protect_security k Low) l = visible_to k l.
Proof. destruct k as [r [|]], l; reflexivity. Qed.

Lemma protect_visibility : forall k l o,
  visible_to (protect_security k l) o = true ->
  visible_to k o = true.
Proof.
  intros [r [|]] [|] [|]; simpl; auto.
Qed.

Lemma protect_security_low_identity : forall k, protect_security k Low = k.
Proof. destruct k as [[|] [|]]; reflexivity. Qed.

Lemma protect_value_is_value : forall v q,
  value v -> value (protect_value v q).
Proof. intros v q Hv. inversion Hv; subst; destruct q; simpl; constructor; assumption. Qed.

Lemma abs_value_security : forall T b k1 k2,
  value (tm_abs T b k1) -> value (tm_abs T b k2).
Proof. intros. inversion H; subst. constructor; assumption. Qed.

Lemma value_rel_with_protect : forall l q T v1 v2,
  value_rel l T v1 v2 ->
  value_rel l (ty_protect q T) (protect_value v1 q) (protect_value v2 q).
Proof.
  intros l q T. induction T; intros v1 v2 Hrel.
  - apply (proj2 (value_rel_protect l q (Ty_Unit s) _ _)).
    unfold value_rel in Hrel. simpl in Hrel. rewrite visible_to_protect_low in Hrel.
    destruct (visible_to (protect_security s q) l) eqn:Ht.
    + assert (Hb : visible_to s l = true) by (eapply protect_visibility; exact Ht).
      simpl. rewrite Ht. rewrite Hb in Hrel. destruct Hrel as [k1 [k2 [-> ->]]]. simpl. eauto.
    + simpl. rewrite Ht. rewrite <- visible_to_protect_low in Hrel. destruct (value_rel_with_values l Low (Ty_Unit s) v1 v2 Hrel) as [V1 V2].
      split; eauto using protect_value_is_value.
  - apply (proj2 (value_rel_protect l q (Ty_Sum T1 T2 s) _ _)).
    unfold value_rel in Hrel. simpl in Hrel. rewrite visible_to_protect_low in Hrel.
    destruct (visible_to (protect_security s q) l) eqn:Ht.
    + assert (Hb : visible_to s l = true) by (eapply protect_visibility; exact Ht).
      simpl. rewrite Ht. rewrite Hb in Hrel.
      destruct Hrel as [[a1 [a2 [k1 [k2 [-> [-> Hr]]]]]]|
                        [a1 [a2 [k1 [k2 [-> [-> Hr]]]]]]]; simpl.
      * left. exists a1, a2, (protect_security k1 q), (protect_security k2 q). repeat split; try reflexivity; exact Hr.
      * right. exists a1, a2, (protect_security k1 q), (protect_security k2 q). repeat split; try reflexivity; exact Hr.
    + simpl. rewrite Ht. rewrite <- visible_to_protect_low in Hrel. destruct (value_rel_with_values l Low (Ty_Sum T1 T2 s) v1 v2 Hrel) as [V1 V2].
      split; eauto using protect_value_is_value.
  - apply (proj2 (value_rel_protect l q (Ty_Prod T1 T2 s) _ _)).
    unfold value_rel in Hrel. simpl in Hrel. rewrite visible_to_protect_low in Hrel.
    destruct (visible_to (protect_security s q) l) eqn:Ht.
    + assert (Hb : visible_to s l = true) by (eapply protect_visibility; exact Ht).
      simpl. rewrite Ht. rewrite Hb in Hrel.
      destruct Hrel as [a1 [a2 [b1 [b2 [k1 [k2 [-> [-> [H1 H2]]]]]]]]].
      exists a1, a2, b1, b2, (protect_security k1 q), (protect_security k2 q). repeat split; try reflexivity; assumption.
    + simpl. rewrite Ht. rewrite <- visible_to_protect_low in Hrel. destruct (value_rel_with_values l Low (Ty_Prod T1 T2 s) v1 v2 Hrel) as [V1 V2].
      split; eauto using protect_value_is_value.
  - apply (proj2 (value_rel_protect l q (Ty_Arrow T1 T2 s) _ _)).
    unfold value_rel in Hrel. simpl in Hrel. rewrite visible_to_protect_low in Hrel.
    destruct (visible_to (protect_security s q) l) eqn:Ht.
    + assert (Hb : visible_to s l = true) by (eapply protect_visibility; exact Ht).
      simpl. rewrite Ht. rewrite Hb in Hrel.
      destruct Hrel as [b1 [b2 [-> [-> [V1 [V2 Hfn]]]]]].
      rewrite protect_security_low_identity in V1, V2.
      simpl. rewrite protect_security_low_identity.
      exists b1, b2. split; [reflexivity|]. split; [reflexivity|].
      split; [eapply abs_value_security; exact V1|].
      split; [eapply abs_value_security; exact V2|exact Hfn].
    + simpl. rewrite Ht. rewrite <- visible_to_protect_low in Hrel. destruct (value_rel_with_values l Low (Ty_Arrow T1 T2 s) v1 v2 Hrel) as [V1 V2].
      split; eauto using protect_value_is_value.
Qed.

Lemma value_rel_hidden : forall l T v1 v2,
  ~ flows_to (security_of T).(indirect_reader) l ->
  value v1 -> value v2 -> value_rel l T v1 v2.
Proof.
  intros l T v1 v2 Hhide Hv1 Hv2. destruct T as
    [k|T1 T2 k|T1 T2 k|T1 T2 k];
    simpl in *; unfold value_rel; simpl;
    rewrite visible_to_protect_low;
    match goal with
    | |- context [visible_to ?q l] =>
        destruct (visible_to q l) eqn:Hvis;
        [exfalso; apply Hhide; apply visible_to_iff; exact Hvis|auto]
    end.
Qed.

Lemma value_rel_unit : forall l k k1 k2,
  value_rel l (Ty_Unit k) (tm_unit k1) (tm_unit k2).
Proof.
  intros. unfold value_rel. simpl. rewrite visible_to_protect_low.
  destruct (visible_to k l); simpl.
  - exists k1, k2. auto.
  - split; constructor.
Qed.

Lemma value_rel_inl : forall l T1 T2 k v1 v2,
  value v1 -> value v2 -> value_rel l T1 v1 v2 ->
  value_rel l (Ty_Sum T1 T2 k) (tm_inl v1 k) (tm_inl v2 k).
Proof.
  intros. unfold value_rel. simpl. rewrite visible_to_protect_low.
  destruct (visible_to k l); simpl.
  - left. exists v1, v2, k, k. auto.
  - split; constructor; assumption.
Qed.

Lemma value_rel_inr : forall l T1 T2 k v1 v2,
  value v1 -> value v2 -> value_rel l T2 v1 v2 ->
  value_rel l (Ty_Sum T1 T2 k) (tm_inr v1 k) (tm_inr v2 k).
Proof.
  intros. unfold value_rel. simpl. rewrite visible_to_protect_low.
  destruct (visible_to k l); simpl.
  - right. exists v1, v2, k, k. auto.
  - split; constructor; assumption.
Qed.

Lemma value_rel_pair : forall l T1 T2 k a1 a2 b1 b2,
  value a1 -> value a2 -> value b1 -> value b2 ->
  value_rel l T1 a1 b1 -> value_rel l T2 a2 b2 ->
  value_rel l (Ty_Prod T1 T2 k)
    (tm_pair a1 a2 k) (tm_pair b1 b2 k).
Proof.
  intros. unfold value_rel. simpl. rewrite visible_to_protect_low.
  destruct (visible_to k l); simpl.
  - exists a1, a2, b1, b2, k, k. auto.
  - split; constructor; assumption.
Qed.

Lemma not_flows_is_high_low : forall a b,
  ~ flows_to a b -> a = High /\ b = Low.
Proof. destruct a, b; simpl; intuition congruence. Qed.

Lemma nonflow_levels : forall S R,
  ~ flows_to (security_of S).(indirect_reader)
      (security_of R).(indirect_reader) ->
  (security_of S).(indirect_reader) = High /\
  (security_of R).(indirect_reader) = Low.
Proof.
  intros S R H. apply not_flows_is_high_low. exact H.
Qed.

Lemma secret_values_related : forall T l v1 v2,
  ~ flows_to (security_of T).(indirect_reader) l ->
  value v1 -> value v2 -> value_rel l T v1 v2.
Proof. intros T l v1 v2 H V1 V2. exact (value_rel_hidden l T v1 v2 H V1 V2). Qed.

Lemma value_rel_to_hidden_subtype : forall l T U v1 v2,
  subtype T U ->
  ~ flows_to (security_of U).(indirect_reader) l ->
  value_rel l T v1 v2 -> value_rel l U v1 v2.
Proof.
  intros l T U v1 v2 Hsub Hhide Hrel.
  destruct (value_rel_with_values l Low T v1 v2 Hrel) as [V1 V2].
  eapply value_rel_hidden; eauto.
Qed.

Lemma transparent_security_le : forall k T,
  transparent_at k T -> security_le (security_of T) k.
Proof. intros k [| | |]; simpl; tauto. Qed.

Lemma value_rel_erases_ground : forall l k T v1 v2,
  ground T -> transparent_at k T ->
  flows_to k.(indirect_reader) l -> value_rel l T v1 v2 ->
  erase_security v1 = erase_security v2.
Proof.
  intros l k T. induction T; intros v1 v2 Hg Htr Hkl Hrel.
  - simpl in Hg. unfold value_rel in Hrel. simpl in Hrel.
    rewrite visible_to_protect_low in Hrel.
    destruct (visible_to s l) eqn:Hvis.
    + destruct Hrel as [k1 [k2 [E1 E2]]]. subst. reflexivity.
    + exfalso. destruct Htr as [Hsec _].
      assert (Hflow : flows_to (indirect_reader s) l).
      { eapply flows_to_transitive; [exact (proj2 Hsec)|exact Hkl]. }
      pose proof (proj2 (visible_to_iff s l) Hflow). congruence.
  - simpl in Hg, Htr. destruct Hg as [Hg1 Hg2].
    destruct Htr as [Hsec [Htr1 Htr2]].
    unfold transparent_at in Htr1, Htr2.
    assert (Hvis : visible_to s l = true).
    { apply visible_to_iff. eapply flows_to_transitive;
        [exact (proj2 Hsec)|exact Hkl]. }
    unfold value_rel in Hrel. simpl in Hrel.
    rewrite visible_to_protect_low in Hrel. rewrite Hvis in Hrel.
    destruct Hrel as [[a1 [a2 [q1 [q2 [E1 [E2 Hr]]]]]]|
                      [a1 [a2 [q1 [q2 [E1 [E2 Hr]]]]]]]; subst.
    + simpl. f_equal. eapply IHT1.
      * exact Hg1.
      * exact Htr1.
      * exact Hkl.
      * exact Hr.
    + simpl. f_equal. eapply IHT2.
      * exact Hg2.
      * exact Htr2.
      * exact Hkl.
      * exact Hr.
  - simpl in Hg, Htr. destruct Hg as [Hg1 Hg2].
    destruct Htr as [Hsec [Htr1 Htr2]].
    unfold transparent_at in Htr1, Htr2.
    assert (Hvis : visible_to s l = true).
    { apply visible_to_iff. eapply flows_to_transitive;
        [exact (proj2 Hsec)|exact Hkl]. }
    unfold value_rel in Hrel. simpl in Hrel.
    rewrite visible_to_protect_low in Hrel. rewrite Hvis in Hrel.
    destruct Hrel as [a1 [a2 [b1 [b2 [q1 [q2 [E1 [E2 [Hr1 Hr2]]]]]]]]].
    subst. simpl. f_equal.
    + eapply IHT1.
      * exact Hg1.
      * exact Htr1.
      * exact Hkl.
      * exact Hr1.
    + eapply IHT2.
      * exact Hg2.
      * exact Htr2.
      * exact Hkl.
      * exact Hr2.
  - simpl in Hg. contradiction.
Qed.

Definition eval_rel (l : label) (T : ty) (t1 t2 : tm) : Prop :=
  forall v1 v2, evaluates t1 v1 -> evaluates t2 v2 ->
    value_rel l T v1 v2.

Lemma evaluates_protect_value : forall q v,
  value v -> evaluates (tm_protect q v) (protect_value v q).
Proof.
  intros q v Hv. split; [|apply protect_value_is_value; exact Hv].
  eapply multi_step. - apply ST_ProtectValue; exact Hv. - constructor.
Qed.

Lemma evaluates_protect_output : forall q v w,
  value v -> evaluates (tm_protect q v) w -> w = protect_value v q.
Proof.
  intros q v w Hv E. symmetry. eapply multi_value_deterministic.
  - exact (proj1 (evaluates_protect_value q v Hv)).
  - exact (proj2 (evaluates_protect_value q v Hv)).
  - exact (proj1 E).
  - exact (proj2 E).
Qed.

Lemma eval_rel_protect : forall l q T t1 t2,
  eval_rel l T t1 t2 -> eval_rel l (ty_protect q T) (tm_protect q t1) (tm_protect q t2).
Proof.
  intros l q T t1 t2 Hrel w1 w2 E1 E2.
  apply evaluates_protect_inv in E1 as [v1 [Ev1 Ep1]].
  apply evaluates_protect_inv in E2 as [v2 [Ev2 Ep2]].
  assert (V1 : value v1) by exact (proj2 Ev1).
  assert (V2 : value v2) by exact (proj2 Ev2).
  pose proof (Hrel v1 v2 Ev1 Ev2) as R.
  assert (O1 : w1 = protect_value v1 q).
  { symmetry. eapply multi_from_value; [eapply protect_value_is_value; exact V1|exact (proj1 Ep1)]. }
  assert (O2 : w2 = protect_value v2 q).
  { symmetry. eapply multi_from_value; [eapply protect_value_is_value; exact V2|exact (proj1 Ep2)]. }
  subst. eapply value_rel_with_protect. exact R.
Qed.

Lemma eval_rel_inl : forall l T1 T2 k t1 t2,
  eval_rel l T1 t1 t2 ->
  eval_rel l (Ty_Sum T1 T2 k) (tm_inl t1 k) (tm_inl t2 k).
Proof.
  intros l T1 T2 k t1 t2 Hrel w1 w2 E1 E2.
  apply evaluates_inl_inv in E1 as [v1 [Ev1 ->]].
  apply evaluates_inl_inv in E2 as [v2 [Ev2 ->]].
  eapply value_rel_inl; try exact (proj2 Ev1); try exact (proj2 Ev2).
  eapply Hrel; eauto.
Qed.

Lemma eval_rel_inr : forall l T1 T2 k t1 t2,
  eval_rel l T2 t1 t2 ->
  eval_rel l (Ty_Sum T1 T2 k) (tm_inr t1 k) (tm_inr t2 k).
Proof.
  intros l T1 T2 k t1 t2 Hrel w1 w2 E1 E2.
  apply evaluates_inr_inv in E1 as [v1 [Ev1 ->]].
  apply evaluates_inr_inv in E2 as [v2 [Ev2 ->]].
  eapply value_rel_inr; try exact (proj2 Ev1); try exact (proj2 Ev2).
  eapply Hrel; eauto.
Qed.

Lemma eval_rel_values : forall l T v1 v2,
  value v1 -> value v2 -> value_rel l T v1 v2 -> eval_rel l T v1 v2.
Proof.
  intros l T v1 v2 Hv1 Hv2 Hrel w1 w2 [M1 V1] [M2 V2].
  assert (v1 = w1) by (eapply multi_from_value; eauto).
  assert (v2 = w2) by (eapply multi_from_value; eauto).
  subst. exact Hrel.
Qed.

Lemma eval_rel_erases : forall l T t1 t2,
  ground T -> transparent_at (security_of T) T ->
  l = (security_of T).(indirect_reader) ->
  eval_rel l T t1 t2 -> same_result t1 t2.
Proof.
  intros l T t1 t2 Hg Htr -> Hrel v1 v2 E1 E2.
  eapply value_rel_erases_ground.
  - exact Hg.
  - exact Htr.
  - exact (proj2 (transparent_security_le (security_of T) T Htr)).
  - eapply Hrel; eauto.
Qed.

Lemma erase_protect_value : forall v l,
  erase_security (protect_value v l) = erase_security v.
Proof. destruct v; reflexivity. Qed.

Lemma erase_protect : forall l t,
  erase_security (tm_protect l t) = erase_security t.
Proof. reflexivity. Qed.

Definition tm_env := atom -> tm.

Definition env_update (rho : tm_env) (x : atom) (v : tm) : tm_env :=
  fun y => if Nat.eqb x y then v else rho y.

Fixpoint instantiate (rho : tm_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => rho x
  | tm_unit k => tm_unit k
  | tm_abs T b k => tm_abs T (instantiate rho b) k
  | tm_app t1 t2 r => tm_app (instantiate rho t1) (instantiate rho t2) r
  | tm_pair t1 t2 k => tm_pair (instantiate rho t1) (instantiate rho t2) k
  | tm_fst t r => tm_fst (instantiate rho t) r
  | tm_snd t r => tm_snd (instantiate rho t) r
  | tm_inl t k => tm_inl (instantiate rho t) k
  | tm_inr t k => tm_inr (instantiate rho t) k
  | tm_case t b1 b2 r =>
      tm_case (instantiate rho t) (instantiate rho b1) (instantiate rho b2) r
  | tm_protect l t => tm_protect l (instantiate rho t)
  | tm_if c y n r => tm_if (instantiate rho c) (instantiate rho y) (instantiate rho n) r
  end.

Definition environment_well_typed (Gamma : context) (rho : tm_env) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    has_type empty (rho x) T /\ closed (rho x).

Lemma environment_well_typed_lookup : forall Gamma rho x T,
  environment_well_typed Gamma rho -> lookup_context x Gamma = Some T ->
  has_type empty (rho x) T /\ closed (rho x).
Proof. intros. eapply H; eassumption. Qed.

Definition environments_related (l : label) (Gamma : context)
    (rho1 rho2 : tm_env) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    eval_rel l T (rho1 x) (rho2 x).


Lemma instantiate_update_same : forall rho x v y,
  x <> y -> env_update rho x v y = rho y.
Proof.
  intros. unfold env_update. destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

Lemma instantiate_update_eq : forall rho x v,
  env_update rho x v x = v.
Proof. intros. unfold env_update. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma not_in_app_inv : forall (x : atom) (A B : list atom),
  ~ In x (A ++ B) -> ~ In x A /\ ~ In x B.
Proof.
  intros x A B H. split; intro Hin; apply H; apply in_or_app; auto.
Qed.

Lemma instantiate_env_ext : forall rho x v t,
  ~ In x (fv t) -> instantiate (env_update rho x v) t = instantiate rho t.
Proof.
  intros rho x v t. induction t; simpl; intros Hnot; try reflexivity.
  - unfold env_update. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hnot. simpl. auto.
    + reflexivity.
  - f_equal. apply IHt. exact Hnot.
  - apply not_in_app_inv in Hnot as [H1 H2]. f_equal; auto.
  - apply not_in_app_inv in Hnot as [H1 H2]. f_equal; auto.
  - f_equal. apply IHt. exact Hnot.
  - f_equal. apply IHt. exact Hnot.
  - f_equal. apply IHt. exact Hnot.
  - f_equal. apply IHt. exact Hnot.
  - apply not_in_app_inv in Hnot as [H0 Hrest].
    apply not_in_app_inv in Hrest as [H1 H2]. f_equal; auto.
  - f_equal. apply IHt. exact Hnot.
  - apply not_in_app_inv in Hnot as [H0 Hrest].
    apply not_in_app_inv in Hrest as [H1 H2]. f_equal; auto.
Qed.

Lemma lookup_update_eq : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof. intros. unfold update. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma lookup_update_neq : forall Gamma x y T,
  x <> y -> lookup_context x (update Gamma y T) = lookup_context x Gamma.
Proof.
  intros. unfold update. simpl. destruct (Nat.eqb x y) eqn:E; auto.
  apply Nat.eqb_eq in E. contradiction.
Qed.

Lemma environment_well_typed_update : forall Gamma rho x T v,
  environment_well_typed Gamma rho ->
  has_type empty v T -> closed v ->
  environment_well_typed (update Gamma x T) (env_update rho x v).
Proof.
  intros Gamma rho x T v Henv Hty Hclosed y U Hlookup.
  destruct (Nat.eq_dec y x) as [->|Hneq].
  - rewrite lookup_update_eq in Hlookup. inversion Hlookup; subst U.
    rewrite instantiate_update_eq. auto.
  - rewrite lookup_update_neq in Hlookup by exact Hneq.
    specialize (Henv y U Hlookup). rewrite instantiate_update_same by congruence.
    exact Henv.
Qed.

Lemma environments_related_update : forall l Gamma rho1 rho2 x T v1 v2,
  environments_related l Gamma rho1 rho2 -> eval_rel l T v1 v2 ->
  environments_related l (update Gamma x T)
    (env_update rho1 x v1) (env_update rho2 x v2).
Proof.
  intros l Gamma rho1 rho2 x T v1 v2 Henv Hrel y U Hlookup.
  destruct (Nat.eq_dec y x) as [->|Hneq].
  - rewrite lookup_update_eq in Hlookup. inversion Hlookup; subst U.
    rewrite !instantiate_update_eq. exact Hrel.
  - rewrite lookup_update_neq in Hlookup by exact Hneq.
    specialize (Henv y U Hlookup).
    rewrite !instantiate_update_same by congruence. exact Henv.
Qed.

Lemma lc_at_open_rec_identity : forall t n,
  lc_at n t -> forall k u, open_rec (k + n) u t = t.
Proof.
  induction t; intros depth Hlc k u; simpl in *.
  - destruct (Nat.eqb (k + depth) n) eqn:E; auto.
    apply Nat.eqb_eq in E. lia.
  - reflexivity.
  - reflexivity.
  - f_equal. replace (S (k + depth)) with (k + S depth) by lia.
    exact (IHt (S depth) Hlc k u).
  - destruct Hlc as [H1 H2]. f_equal; [eapply IHt1|eapply IHt2]; eauto.
  - destruct Hlc as [H1 H2]. f_equal; [eapply IHt1|eapply IHt2]; eauto.
  - f_equal. eapply IHt. exact Hlc.
  - f_equal. eapply IHt. exact Hlc.
  - f_equal. eapply IHt. exact Hlc.
  - f_equal. eapply IHt. exact Hlc.
  - destruct Hlc as [H0 [H1 H2]]. f_equal.
    + eapply IHt1; eauto.
    + replace (S (k + depth)) with (k + S depth) by lia.
      exact (IHt2 (S depth) H1 k u).
    + replace (S (k + depth)) with (k + S depth) by lia.
      exact (IHt3 (S depth) H2 k u).
  - f_equal. eapply IHt. exact Hlc.
  - destruct Hlc as [H1 [H2 H3]]. f_equal;
      [eapply IHt1|eapply IHt2|eapply IHt3]; eauto.
Qed.

Lemma lc_open_rec_fvar : forall t k d x,
  k <= d -> lc_at d (open_rec k (tm_fvar x) t) -> lc_at (S d) t.
Proof.
  induction t; intros k d x Hkn Hlc; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. lia.
    + simpl in Hlc. lia.
  - exact I.
  - exact I.
  - apply IHt with (k := S k) (d := S d) (x := x); try lia; exact Hlc.
  - destruct Hlc as [H1 H2]. split;
      [eapply IHt1|eapply IHt2]; eauto; lia.
  - destruct Hlc as [H1 H2]. split;
      [eapply IHt1|eapply IHt2]; eauto; lia.
  - eapply IHt; eauto; lia.
  - eapply IHt; eauto; lia.
  - eapply IHt; eauto; lia.
  - eapply IHt; eauto; lia.
  - destruct Hlc as [H0 [H1 H2]]. repeat split.
    + eapply IHt1; eauto; lia.
    + eapply IHt2 with (k := S k) (d := S d) (x := x); eauto; lia.
    + eapply IHt3 with (k := S k) (d := S d) (x := x); eauto; lia.
  - eapply IHt; eauto; lia.
  - destruct Hlc as [H1 [H2 H3]]. repeat split;
      [eapply IHt1|eapply IHt2|eapply IHt3]; eauto; lia.
Qed.

Lemma lc_body_cofinite : forall L b,
  (forall x : atom, ~ In x L -> locally_closed (open b (tm_fvar x))) ->
  lc_at 1 b.
Proof.
  intros L b Hcof. eapply lc_open_rec_fvar with (k := 0)
    (x := S (max_atom L)); [lia|].
  apply Hcof. apply fresh_not_in.
Qed.

Lemma has_type_locally_closed : forall Gamma t T,
  has_type Gamma t T -> locally_closed t.
Proof.
  intros Gamma t T Hty. induction Hty; unfold locally_closed in *; simpl in *; auto; try tauto;
    try solve [repeat split; eauto using lc_body_cofinite].
Qed.

Lemma lc_at_weaken : forall t d,
  lc_at d t -> forall m, d <= m -> lc_at m t.
Proof.
  induction t; intros d Hlc m Hdm; simpl in *; try exact I.
  - lia.
  - f_equal. eapply IHt; [exact Hlc|lia].
  - destruct Hlc as [H1 H2]. split; [eapply IHt1|eapply IHt2]; eauto; lia.
  - destruct Hlc as [H1 H2]. split; [eapply IHt1|eapply IHt2]; eauto; lia.
  - eapply IHt; eauto; lia.
  - eapply IHt; eauto; lia.
  - eapply IHt; eauto; lia.
  - eapply IHt; eauto; lia.
  - destruct Hlc as [H0 [H1 H2]]. repeat split.
    + eapply IHt1; eauto; lia.
    + eapply IHt2; eauto; lia.
    + eapply IHt3; eauto; lia.
  - eapply IHt; eauto; lia.
  - destruct Hlc as [H1 [H2 H3]]. repeat split;
      [eapply IHt1|eapply IHt2|eapply IHt3]; eauto; lia.
Qed.

Lemma instantiate_lc_at : forall rho t d,
  (forall x, locally_closed (rho x)) ->
  lc_at d t -> lc_at d (instantiate rho t).
Proof.
  intros rho t. induction t; intros d Hr Hlc; simpl in *; try exact Hlc.
  - apply lc_at_weaken with (d := 0); [apply Hr|lia].
  - eapply IHt; eauto.
  - destruct Hlc as [H1 H2]. split; [eapply IHt1|eapply IHt2]; eauto.
  - destruct Hlc as [H1 H2]. split; [eapply IHt1|eapply IHt2]; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - destruct Hlc as [H0 [H1 H2]]. repeat split.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
    + eapply IHt3; eauto.
  - eapply IHt; eauto.
  - destruct Hlc as [H1 [H2 H3]]. repeat split;
      [eapply IHt1|eapply IHt2|eapply IHt3]; eauto.
Qed.

Lemma instantiate_open_rec : forall rho t k u,
  (forall x, locally_closed (rho x)) ->
  instantiate rho (open_rec k u t) =
  open_rec k (instantiate rho u) (instantiate rho t).
Proof.
  intros rho t. induction t; intros k u Hlc; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - replace k with (k + 0) at 1 by lia.
    rewrite (lc_at_open_rec_identity (rho a) 0 (Hlc a) k (instantiate rho u)).
    reflexivity.
  - reflexivity.
  - rewrite IHt with (k := S k) (u := u); auto.
  - rewrite IHt1 with (k := k) (u := u); auto.
    rewrite IHt2 with (k := k) (u := u); auto.
  - rewrite IHt1 with (k := k) (u := u); auto.
    rewrite IHt2 with (k := k) (u := u); auto.
  - rewrite IHt with (k := k) (u := u); auto.
  - rewrite IHt with (k := k) (u := u); auto.
  - rewrite IHt with (k := k) (u := u); auto.
  - rewrite IHt with (k := k) (u := u); auto.
  - rewrite IHt1 with (k := k) (u := u); auto.
    rewrite IHt2 with (k := S k) (u := u); auto.
    rewrite IHt3 with (k := S k) (u := u); auto.
  - rewrite IHt with (k := k) (u := u); auto.
  - rewrite IHt1 with (k := k) (u := u); auto.
    rewrite IHt2 with (k := k) (u := u); auto.
    rewrite IHt3 with (k := k) (u := u); auto.
Qed.

Lemma instantiate_open : forall rho body x,
  (forall y, locally_closed (rho y)) ->
  instantiate rho (open body (tm_fvar x)) =
  open (instantiate rho body) (rho x).
Proof.
  intros. unfold open. rewrite instantiate_open_rec; auto.
Qed.

Lemma eval_rel_pair : forall l T1 T2 k t1 t2 u1 u2,
  eval_rel l T1 t1 u1 -> eval_rel l T2 t2 u2 ->
  eval_rel l (Ty_Prod T1 T2 k) (tm_pair t1 t2 k) (tm_pair u1 u2 k).
Proof.
  intros l T1 T2 k t1 t2 u1 u2 H1 H2 w1 w2 E1 E2.
  apply evaluates_pair_inv in E1 as [a1 [a2 [Ea1 [Ea2 ->]]]].
  apply evaluates_pair_inv in E2 as [b1 [b2 [Eb1 [Eb2 ->]]]].
  eapply value_rel_pair; try exact (proj2 Ea1); try exact (proj2 Ea2);
    try exact (proj2 Eb1); try exact (proj2 Eb2).
  - eapply H1; eauto.
  - eapply H2; eauto.
Qed.

Lemma security_of_protect : forall q T,
  security_of (ty_protect q T) = protect_security (security_of T) q.
Proof. intros q [k|T1 T2 k|T1 T2 k|T1 T2 k]; reflexivity. Qed.

Lemma protected_hidden_results : forall l k T t1 t2 w1 w2,
  ~ flows_to (indirect_reader k) l ->
  evaluates (tm_protect (indirect_reader k) t1) w1 ->
  evaluates (tm_protect (indirect_reader k) t2) w2 ->
  value_rel l (ty_protect (indirect_reader k) T) w1 w2.
Proof.
  intros l k T t1 t2 w1 w2 Hhide E1 E2.
  apply value_rel_hidden.
  - intro Hf. rewrite security_of_protect in Hf. simpl in Hf.
    apply join_low_flows_right in Hf. contradiction.
  - exact (proj2 E1).
  - exact (proj2 E2).
Qed.

Lemma step_abs_none : forall T b k t, ~ step (tm_abs T b k) t.
Proof. intros T b k t H. inversion H. Qed.

Lemma multi_abs_same : forall T b k w,
  multi (tm_abs T b k) w -> w = tm_abs T b k.
Proof.
  intros T b k w Hm. remember (tm_abs T b k) as start eqn:E.
  revert T b k E. induction Hm; intros T b k E.
  - inversion E; reflexivity.
  - inversion E; subst. inversion H; subst; congruence.
Qed.

Lemma evaluates_abs_inv : forall T b k w,
  evaluates (tm_abs T b k) w -> w = tm_abs T b k /\ value w.
Proof.
  intros T b k w [Hm Hv]. pose proof (multi_abs_same _ _ _ _ Hm) as E.
  subst. split; auto.
Qed.

Lemma env_update_locally_closed : forall rho x v,
  (forall y, locally_closed (rho y)) -> locally_closed v ->
  forall y, locally_closed (env_update rho x v y).
Proof.
  intros rho x v Hrho Hv y. unfold env_update. destruct (Nat.eqb x y); auto.
Qed.

Lemma protect_security_low_reader : forall k,
  reader (protect_security k Low) = reader k.
Proof. destruct k as [[|] [|]]; reflexivity. Qed.

Lemma protect_security_low_indirect : forall k,
  indirect_reader (protect_security k Low) = indirect_reader k.
Proof. destruct k as [[|] [|]]; reflexivity. Qed.

Lemma eval_rel_app : forall l T1 T2 k r f1 f2 a1 a2,
  flows_to k.(reader) r ->
  eval_rel l (Ty_Arrow T1 T2 k) f1 f2 -> eval_rel l T1 a1 a2 ->
  eval_rel l (ty_protect k.(indirect_reader) T2)
    (tm_app f1 a1 r) (tm_app f2 a2 r).
Proof.
  intros l T1 T2 k r f1 f2 a1 a2 Hflow Hfun Harg w1 w2 E1 E2.
  apply evaluates_app_inv in E1 as [Ta [b1 [ka [va1 [Ef1 [Ea1 [V1 [F1 Eb1]]]]]]]].
  apply evaluates_app_inv in E2 as [Tb [b2 [kb [va2 [Ef2 [Ea2 [V2 [F2 Eb2]]]]]]]].
  pose proof (Hfun (tm_abs Ta b1 ka) (tm_abs Tb b2 kb) Ef1 Ef2) as Rfun.
  unfold value_rel in Rfun. simpl in Rfun.
  pose proof (Harg va1 va2 Ea1 Ea2) as Rarg.
  assert (Hres : value_rel l (ty_protect (indirect_reader k) T2) w1 w2).
  { destruct (visible_to (protect_security k Low) l) eqn:Hv.
      destruct Rfun as [bf1 [bf2 [Ebf1 [Ebf2 [VB1 [VB2 Hbody]]]]]].
      inversion Ebf1; inversion Ebf2; subst.
      apply evaluates_protect_inv in Eb1 as [raw1 [Er1 Ep1]].
      apply evaluates_protect_inv in Eb2 as [raw2 [Er2 Ep2]].
      rewrite protect_security_low_indirect in Ep1, Ep2.
      assert (Rraw : value_rel_with l Low T2 raw1 raw2).
      { eapply Hbody; eauto. }
      assert (O1 : w1 = protect_value raw1 (indirect_reader k)).
      { symmetry. eapply multi_from_value; [eapply protect_value_is_value; exact (proj2 Er1)|exact (proj1 Ep1)]. }
      assert (O2 : w2 = protect_value raw2 (indirect_reader k)).
      { symmetry. eapply multi_from_value; [eapply protect_value_is_value; exact (proj2 Er2)|exact (proj1 Ep2)]. }
      subst. eapply value_rel_with_protect. exact Rraw.
    - assert (Hhide : ~ flows_to (indirect_reader (security_of (ty_protect (indirect_reader k) T2))) l).
      { intro Hf. rewrite security_of_protect in Hf. simpl in Hf.
        apply join_low_flows_right in Hf.
        assert (Hvis : visible_to (protect_security k Low) l = true).
        { apply visible_to_iff. rewrite protect_security_low_indirect. exact Hf. }
        rewrite Hvis in Hv. discriminate. }
      eapply value_rel_hidden; [exact Hhide|exact (proj2 Eb1)|exact (proj2 Eb2)].
  }
  exact Hres.
Qed.

Lemma eval_rel_if_tagged : forall l T k r c1 c2 y1 y2 n1 n2,
  (forall v1 v2, evaluates c1 v1 -> evaluates c2 v2 ->
    (exists a1 a2, v1 = tm_inl a1 k /\ v2 = tm_inl a2 k) \/
    (exists a1 a2, v1 = tm_inr a1 k /\ v2 = tm_inr a2 k)) ->
  eval_rel l T y1 y2 -> eval_rel l T n1 n2 ->
  eval_rel l (ty_protect (indirect_reader k) T)
    (tm_if c1 y1 n1 r) (tm_if c2 y2 n2 r).
Proof.
  intros l T k r c1 c2 y1 y2 n1 n2 Htag Hy Hn w1 w2 E1 E2.
  apply evaluates_if_inv in E1 as [I1|I1];
    apply evaluates_if_inv in E2 as [I2|I2].
  all: destruct I1 as [v1 [q1 [Ec1 [V1 [F1 Eb1]]]]];
       destruct I2 as [v2 [q2 [Ec2 [V2 [F2 Eb2]]]]].
  all: specialize (Htag _ _ Ec1 Ec2) as Hsame.
  - destruct Hsame as [[a1 [a2 [Et1 Et2]]]|[a1 [a2 [Et1 Et2]]]].
    + inversion Et1; inversion Et2; subst.
      destruct (visible_to k l) eqn:Hv.
      * eapply (eval_rel_protect l (indirect_reader k) T y1 y2 Hy w1 w2); eauto.
      * apply value_rel_hidden.
        -- intro Hf. rewrite security_of_protect in Hf. simpl in Hf.
           apply join_low_flows_right in Hf.
           assert (Hvis : visible_to k l = true) by (apply visible_to_iff; exact Hf).
           rewrite Hv in Hvis. discriminate.
        -- exact (proj2 Eb1).
        -- exact (proj2 Eb2).
    + inversion Et1.
  - destruct Hsame as [[a1 [a2 [Et1 Et2]]]|[a1 [a2 [Et1 Et2]]]].
    + inversion Et2.
    + inversion Et1.
  - destruct Hsame as [[a1 [a2 [Et1 Et2]]]|[a1 [a2 [Et1 Et2]]]].
    + inversion Et1.
    + inversion Et2.
  - destruct Hsame as [[a1 [a2 [Et1 Et2]]]|[a1 [a2 [Et1 Et2]]]].
    + inversion Et1.
    + inversion Et1; inversion Et2; subst.
      destruct (visible_to k l) eqn:Hv.
      * eapply (eval_rel_protect l (indirect_reader k) T n1 n2 Hn w1 w2); eauto.
      * apply value_rel_hidden.
        -- intro Hf. rewrite security_of_protect in Hf. simpl in Hf.
           apply join_low_flows_right in Hf.
           assert (Hvis : visible_to k l = true) by (apply visible_to_iff; exact Hf).
           rewrite Hv in Hvis. discriminate.
        -- exact (proj2 Eb1).
        -- exact (proj2 Eb2).
Qed.

Lemma eval_rel_fst_tagged : forall l T1 T2 k r t1 t2,
  eval_rel l (Ty_Prod T1 T2 k) t1 t2 ->
  (forall a1 a2 b1 b2 q1 q2,
    evaluates t1 (tm_pair a1 a2 q1) -> evaluates t2 (tm_pair b1 b2 q2) ->
    q1 = k /\ q2 = k) ->
  eval_rel l (ty_protect (indirect_reader k) T1)
    (tm_fst t1 r) (tm_fst t2 r).
Proof.
  intros l T1 T2 k r t1 t2 Hrel Htag w1 w2 E1 E2.
  destruct (evaluates_fst_inv _ _ _ E1)
    as [a1 [a2 [q1 [Et1 [Va1 [Va2 [F1 Ep1]]]]]]].
  destruct (evaluates_fst_inv _ _ _ E2)
    as [b1 [b2 [q2 [Et2 [Vb1 [Vb2 [F2 Ep2]]]]]]].
  destruct (Htag _ _ _ _ _ _ Et1 Et2) as [-> ->].
  pose proof (Hrel _ _ Et1 Et2) as Rp.
  unfold value_rel in Rp. simpl in Rp. rewrite visible_to_protect_low in Rp.
  destruct (visible_to k l) eqn:Hv.
  - destruct Rp as [a1' [a2' [b1' [b2' [q1' [q2' [Epa [Epb [Ra Rb]]]]]]]]].
    inversion Epa; inversion Epb; subst.
    assert (Hraw : eval_rel l T1 a1' b1').
    { eapply eval_rel_values; [exact Va1|exact Vb1|exact Ra]. }
    exact (eval_rel_protect l (indirect_reader q2') T1 a1' b1'
      Hraw w1 w2 Ep1 Ep2).
  - apply value_rel_hidden.
    + intro Hf. rewrite security_of_protect in Hf. simpl in Hf.
      apply join_low_flows_right in Hf.
      assert (Hvis : visible_to k l = true) by (apply visible_to_iff; exact Hf).
      rewrite Hv in Hvis. discriminate.
    + exact (proj2 Ep1).
    + exact (proj2 Ep2).
Qed.

Lemma eval_rel_snd_tagged : forall l T1 T2 k r t1 t2,
  eval_rel l (Ty_Prod T1 T2 k) t1 t2 ->
  (forall a1 a2 b1 b2 q1 q2,
    evaluates t1 (tm_pair a1 a2 q1) -> evaluates t2 (tm_pair b1 b2 q2) ->
    q1 = k /\ q2 = k) ->
  eval_rel l (ty_protect (indirect_reader k) T2)
    (tm_snd t1 r) (tm_snd t2 r).
Proof.
  intros l T1 T2 k r t1 t2 Hrel Htag w1 w2 E1 E2.
  destruct (evaluates_snd_inv _ _ _ E1)
    as [a1 [a2 [q1 [Et1 [Va1 [Va2 [F1 Ep1]]]]]]].
  destruct (evaluates_snd_inv _ _ _ E2)
    as [b1 [b2 [q2 [Et2 [Vb1 [Vb2 [F2 Ep2]]]]]]].
  destruct (Htag _ _ _ _ _ _ Et1 Et2) as [-> ->].
  pose proof (Hrel _ _ Et1 Et2) as Rp.
  unfold value_rel in Rp. simpl in Rp. rewrite visible_to_protect_low in Rp.
  destruct (visible_to k l) eqn:Hv.
  - destruct Rp as [a1' [a2' [b1' [b2' [q1' [q2' [Epa [Epb [Ra Rb]]]]]]]]].
    inversion Epa; inversion Epb; subst.
    assert (Hraw : eval_rel l T2 a2' b2').
    { eapply eval_rel_values; [exact Va2|exact Vb2|exact Rb]. }
    exact (eval_rel_protect l (indirect_reader q2') T2 a2' b2'
      Hraw w1 w2 Ep1 Ep2).
  - apply value_rel_hidden.
    + intro Hf. rewrite security_of_protect in Hf. simpl in Hf.
      apply join_low_flows_right in Hf.
      assert (Hvis : visible_to k l = true) by (apply visible_to_iff; exact Hf).
      rewrite Hv in Hvis. discriminate.
    + exact (proj2 Ep1).
    + exact (proj2 Ep2).
Qed.

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
