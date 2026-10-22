(** System F parametricity benchmark, Hard variant.
    Features: if-nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityIfNondeterminismHardTask.

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


Hint Constructors lc_ty_at lc_tm_at value : core.

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof. intros t u v H; induction H; eauto using multi. Qed.

Lemma multi_one : forall t u, t --> u -> t -->* u.
Proof. intros; eauto using multi. Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof. intros v H; destruct H; try assumption; constructor. Qed.

Lemma multi_app_left : forall t t' v,
  t -->* t' -> locally_closed_tm v -> tm_app t v -->* tm_app t' v.
Proof.
  intros t t' v H; induction H as [x|x y z Hxy Hyz IH]; intro Hlc.
  - constructor.
  - eapply multi_step; [eapply ST_App1; eauto|].
    apply IH; assumption.
Qed.

Lemma multi_app_right : forall v t t',
  value v -> t -->* t' -> tm_app v t -->* tm_app v t'.
Proof.
  intros v t t' Hv H; induction H as [x|x y z Hxy Hyz IH].
  - constructor.
  - eapply multi_step; [eapply ST_App2; eauto|].
    apply IH.
Qed.

Lemma multi_tapp : forall t t' T,
  t -->* t' -> locally_closed_ty T -> tm_tapp t T -->* tm_tapp t' T.
Proof.
  intros t t' T H; induction H as [x|x y z Hxy Hyz IH]; intro Hlc.
  - constructor.
  - eapply multi_step; [eapply ST_TApp; eauto|].
    apply IH; assumption.
Qed.

Lemma multi_beta : forall T body v,
  locally_closed_tm (tm_abs T body) -> value v ->
  tm_app (tm_abs T body) v -->* open_tm body v.
Proof. intros; eapply multi_step; [apply ST_AppAbs; eauto|constructor]. Qed.

Lemma multi_type_beta : forall body T,
  locally_closed_tm (tm_tabs body) -> locally_closed_ty T ->
  tm_tapp (tm_tabs body) T -->* open_tm_ty body T.
Proof. intros; eapply multi_step; [apply ST_TAppTabs; eauto|constructor]. Qed.

Definition may_rel (R : tm -> Prop) (t : tm) : Prop :=
  exists v, t -->* v /\ value v /\ R v.

Lemma may_rel_step : forall R t t',
  t --> t' -> may_rel R t' -> may_rel R t.
Proof.
  intros R t t' H [v [Hm [Hv HR]]].
  exists v; repeat split; auto.
  eapply multi_step; eauto.
Qed.

Lemma may_rel_choice_left : forall R t1 t2,
  locally_closed_tm t1 -> locally_closed_tm t2 -> may_rel R t1 ->
  may_rel R (tm_choice t1 t2).
Proof.
  intros R t1 t2 H1 H2 Hm.
  eapply may_rel_step; [apply ST_ChoiceLeft; assumption|exact Hm].
Qed.

Lemma may_rel_choice_right : forall R t1 t2,
  locally_closed_tm t1 -> locally_closed_tm t2 -> may_rel R t2 ->
  may_rel R (tm_choice t1 t2).
Proof.
  intros R t1 t2 H1 H2 Hm.
  eapply may_rel_step; [apply ST_ChoiceRight; assumption|exact Hm].
Qed.

Definition may_rel2 (R : tm -> tm -> Prop) (t u : tm) : Prop :=
  exists v w, t -->* v /\ u -->* w /\ value v /\ value w /\ R v w.

Definition candidate_rel (R : tm -> tm -> Prop) : Prop :=
  forall v w, R v w -> value v /\ value w.

Fixpoint value_rel2 (rho : atom -> tm -> tm -> Prop)
    (bound : list (tm -> tm -> Prop)) (T : ty) : tm -> tm -> Prop :=
  match T with
  | Ty_BVar i => nth i bound (fun _ _ => False)
  | Ty_FVar X => rho X
  | Ty_Arrow A B => fun f g =>
      exists T1 b1 T2 b2, f = tm_abs T1 b1 /\ g = tm_abs T2 b2 /\
      value f /\ value g /\
      forall a b, value_rel2 rho bound A a b ->
        may_rel2 (value_rel2 rho bound B) (tm_app f a) (tm_app g b)
  | Ty_All B => fun f g =>
      value f /\ value g /\ exists tf tg, f = tm_tabs tf /\ g = tm_tabs tg /\
      forall U V R, locally_closed_ty U -> locally_closed_ty V -> candidate_rel R ->
        may_rel2 (value_rel2 rho (R :: bound) B)
          (open_tm_ty tf U) (open_tm_ty tg V)
  | Ty_Bool => fun b c =>
      (b = tm_true /\ c = tm_true) \/ (b = tm_false /\ c = tm_false)
  end.

Fixpoint ty_fv (T : ty) : list atom :=
  match T with
  | Ty_BVar _ | Ty_Bool => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => ty_fv A ++ ty_fv B
  | Ty_All A => ty_fv A
  end.

Lemma nth_insert_relation : forall (pre suf : list (tm -> tm -> Prop)) k
    (A B d : tm -> tm -> Prop) i,
  length pre = k ->
  (i = k -> nth i (pre ++ B :: suf) d = B) /\
  (i <> k -> nth i (pre ++ A :: suf) d = nth i (pre ++ B :: suf) d).
Proof.
  induction pre as [|p pre IH]; intros suf k A B d i Hlen; destruct k; simpl in *.
  - split; intros Hi; [subst i; reflexivity|].
    destruct i; [exfalso; apply Hi; reflexivity|reflexivity].
  - discriminate.
  - discriminate.
  - inversion Hlen; subst k.
    destruct i as [|i].
    + split; intros Hi; [lia|reflexivity].
    + specialize (IH suf (length pre) A B d i eq_refl) as [Hsame Hdiff].
      split.
      * intros Hi; simpl; apply Hsame; now inversion Hi.
      * intros Hi; simpl; apply Hdiff; intro E; apply Hi; now inversion E.
Qed.

Lemma may_rel2_iff : forall R S,
  (forall v w, R v w <-> S v w) ->
  forall t u, may_rel2 R t u <-> may_rel2 S t u.
Proof.
  intros R S H t u; split;
    intros [v [w [Ht [Hu [Hv [Hw HR]]]]]];
    exists v, w; repeat split; auto; apply H; assumption.
Qed.

Definition atom_update {A : Type} (e : atom -> A) (x : atom) (a : A) : atom -> A :=
  fun y => if Nat.eqb x y then a else e y.

Lemma value_rel2_open_ty : forall rho X R pre suf k T,
  length pre = k ->
  ~ In X (ty_fv T) ->
  forall v w,
  value_rel2 (atom_update rho X R) (pre ++ (fun _ _ => False) :: suf)
    (open_ty_rec k (Ty_FVar X) T) v w <->
  value_rel2 rho (pre ++ R :: suf) T v w.
Proof.
  intros rho X R pre suf k T; revert rho X R pre suf k.
  induction T as [i|Y|A IHA B IHB|B IHB|]; intros rho X R pre suf k Hlen Hfresh v w.
  - simpl; destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; subst i.
      simpl; split; intro H.
      * unfold atom_update in H; rewrite Nat.eqb_refl in H.
        rewrite (proj1 (nth_insert_relation pre suf k (fun _ _ => False) R (fun _ _ => False) k Hlen) eq_refl); exact H.
      * unfold atom_update; rewrite Nat.eqb_refl.
        rewrite <- (proj1 (nth_insert_relation pre suf k (fun _ _ => False) R (fun _ _ => False) k Hlen) eq_refl); exact H.
    + simpl; split; intro H.
      * assert (Hneq : i <> k).
        { intro Heq; subst i; rewrite Nat.eqb_refl in E; discriminate. }
        pose proof (proj2 (nth_insert_relation pre suf k (fun _ _ => False) R (fun _ _ => False) i Hlen) Hneq) as Hnth.
        rewrite Hnth in H; exact H.
      * assert (Hneq : i <> k).
        { intro Heq; subst i; rewrite Nat.eqb_refl in E; discriminate. }
        pose proof (proj2 (nth_insert_relation pre suf k (fun _ _ => False) R (fun _ _ => False) i Hlen) Hneq) as Hnth.
        rewrite <- Hnth in H; exact H.
  - simpl; destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E; subst Y; exfalso; apply Hfresh; simpl; auto.
    + unfold atom_update; rewrite E; tauto.
  - simpl; split.
    + intros [T1 [b1 [T2 [b2 [Hshape1 [Hshape2 [Hf [Hg Happ]]]]]]]].
      exists T1, b1, T2, b2; split; [exact Hshape1|]. split; [exact Hshape2|].
      split; [exact Hf|]. split; [exact Hg|].
      intros a b Ha.
      apply (proj1 (may_rel2_iff
        (value_rel2 (atom_update rho X R) (pre ++ (fun _ _ => False) :: suf)
          (open_ty_rec k (Ty_FVar X) B))
        (value_rel2 rho (pre ++ R :: suf) B)
        (fun z q => IHB rho X R pre suf k Hlen
          (fun Hin => Hfresh (in_or_app _ _ _ (or_intror Hin))) z q)
        (tm_app v a) (tm_app w b))).
      apply Happ; apply (proj2 (IHA rho X R pre suf k Hlen
        (fun Hin => Hfresh (in_or_app _ _ _ (or_introl Hin))) a b)); exact Ha.
    + intros [T1 [b1 [T2 [b2 [Hshape1 [Hshape2 [Hf [Hg Happ]]]]]]]].
      exists T1, b1, T2, b2; split; [exact Hshape1|]. split; [exact Hshape2|].
      split; [exact Hf|]. split; [exact Hg|].
      intros a b Ha.
      apply (proj2 (may_rel2_iff
        (value_rel2 (atom_update rho X R) (pre ++ (fun _ _ => False) :: suf)
          (open_ty_rec k (Ty_FVar X) B))
        (value_rel2 rho (pre ++ R :: suf) B)
        (fun z q => IHB rho X R pre suf k Hlen
          (fun Hin => Hfresh (in_or_app _ _ _ (or_intror Hin))) z q)
        (tm_app v a) (tm_app w b))).
      apply Happ; apply (proj1 (IHA rho X R pre suf k Hlen
        (fun Hin => Hfresh (in_or_app _ _ _ (or_introl Hin))) a b)); exact Ha.
  - simpl; split.
    + intros [Hvf [Hvg [tf [tg [Hf [Hg Hall]]]]]].
      split; [exact Hvf|]. split; [exact Hvg|]. exists tf, tg; split; [exact Hf|]. split; [exact Hg|].
      intros U V Q HU HV HQ.
      apply (proj1 (may_rel2_iff
        (value_rel2 (atom_update rho X R) ((Q :: pre) ++ (fun _ _ => False) :: suf)
          (open_ty_rec (Nat.succ k) (Ty_FVar X) B))
        (value_rel2 rho ((Q :: pre) ++ R :: suf) B)
        (fun z q => IHB rho X R (Q :: pre) suf (Nat.succ k) ltac:(simpl; now rewrite Hlen)
          (fun Hin => Hfresh Hin) z q)
        (open_tm_ty tf U) (open_tm_ty tg V))).
      apply Hall; assumption.
    + intros [Hvf [Hvg [tf [tg [Hf [Hg Hall]]]]]].
      split; [exact Hvf|]. split; [exact Hvg|]. exists tf, tg; split; [exact Hf|]. split; [exact Hg|].
      intros U V Q HU HV HQ.
      apply (proj2 (may_rel2_iff
        (value_rel2 (atom_update rho X R) ((Q :: pre) ++ (fun _ _ => False) :: suf)
          (open_ty_rec (Nat.succ k) (Ty_FVar X) B))
        (value_rel2 rho ((Q :: pre) ++ R :: suf) B)
        (fun z q => IHB rho X R (Q :: pre) suf (Nat.succ k) ltac:(simpl; now rewrite Hlen)
          (fun Hin => Hfresh Hin) z q)
        (open_tm_ty tf U) (open_tm_ty tg V))).
      apply Hall; assumption.
  - simpl; tauto.
Qed.

Lemma candidate_nth : forall bound i,
  Forall candidate_rel bound -> candidate_rel (nth i bound (fun _ _ => False)).
Proof.
  intros bound i Hall; revert i.
  induction Hall as [|R bound HR Hbound IH]; intros i; destruct i; simpl.
  - unfold candidate_rel; intros v w H; contradiction.
  - unfold candidate_rel; intros v w H; contradiction.
  - exact HR.
  - apply IH.
Qed.

Lemma value_rel2_values : forall rho bound T v w,
  (forall X, candidate_rel (rho X)) ->
  Forall candidate_rel bound ->
  value_rel2 rho bound T v w -> value v /\ value w.
Proof.
  intros rho bound T; induction T; intros v w Hrho Hbound Hrel; simpl in Hrel.
  - eapply (candidate_nth bound n Hbound); exact Hrel.
  - apply (Hrho a); exact Hrel.
  - destruct Hrel as [TT1 [bb1 [TT2 [bb2 [H1 [H2 [Hv [Hw _]]]]]]]]; auto.
  - destruct Hrel as [Hv [Hw _]]; auto.
  - destruct Hrel as [[H1 H2]|[H1 H2]].
    + subst; split; apply v_true.
    + subst; split; apply v_false.
Qed.

Lemma nth_prefix : forall (pre : list (tm -> tm -> Prop)) k R d i,
  length pre = k -> i < k ->
  nth i (pre ++ R :: []) d = nth i pre d.
Proof.
  induction pre as [|P pre IH].
  - intros k R d i Hlen Hi; simpl in Hlen; lia.
  - intros k R d i Hlen Hi; destruct k; [simpl in Hlen; discriminate|].
    simpl in Hlen; injection Hlen as Hlen0.
    destruct i; [reflexivity|].
    simpl; apply IH with (k := k); [exact Hlen0|lia].
Qed.

Lemma nth_default_ge : forall (A : Type) (l : list A) i (d : A),
  length l <= i -> nth i l d = d.
Proof.
  intros A l; induction l as [|a l IH].
  - intros i d H; destruct i; simpl; reflexivity.
  - intros i d H; destruct i; simpl in *.
    + lia.
    + apply IH; lia.
Qed.

Lemma nth_insert_drop : forall (pre : list (tm -> tm -> Prop)) k R d i,
  length pre = k -> i <> k ->
  nth i (pre ++ R :: []) d = nth i pre d.
Proof.
  intros pre k R d i Hlen Hneq.
  destruct (Nat.lt_ge_cases i k) as [Hlt|Hge].
  - apply nth_prefix with (k := k) (R := R); assumption.
  - assert (Hlong : k < i) by lia.
    assert (H1 : length (pre ++ R :: []) <= i).
    { rewrite length_app; simpl; rewrite Hlen; lia. }
    assert (H2 : length pre <= i) by (rewrite Hlen; lia).
    rewrite (nth_default_ge _ _ _ _ H1).
    rewrite (nth_default_ge _ _ _ _ H2); reflexivity.
Qed.

Lemma nth_cons_agree : forall K (R : tm -> tm -> Prop)
    (bound1 bound2 : list (tm -> tm -> Prop)),
  (forall i, i < K -> nth i bound1 (fun _ _ => False) = nth i bound2 (fun _ _ => False)) ->
  forall i, i < S K ->
    nth i (R :: bound1) (fun _ _ => False) = nth i (R :: bound2) (fun _ _ => False).
Proof.
  intros K R bound1 bound2 H i Hi; destruct i; simpl; auto.
  apply H; lia.
Qed.

Lemma value_rel2_bound_irrel : forall K T,
  lc_ty_at K T ->
  forall rho bound1 bound2,
    (forall i, i < K ->
       nth i bound1 (fun _ _ => False) = nth i bound2 (fun _ _ => False)) ->
    forall v w, value_rel2 rho bound1 T v w <-> value_rel2 rho bound2 T v w.
Proof.
  intros K T Hlc; induction Hlc as
    [K i Hlt|K X|K A B HA IHA HB IHB|K A HA IHA|K];
    intros rho bound1 bound2 Hagree v w.
  - simpl; rewrite (Hagree i Hlt); tauto.
  - simpl; tauto.
  - simpl; split.
    + intros [T1 [b1 [T2 [b2 [Hs1 [Hs2 [Hv [Hw Happ]]]]]]]].
      exists T1, b1, T2, b2; split; [exact Hs1|]. split; [exact Hs2|].
      split; [exact Hv|]. split; [exact Hw|].
      intros a b Ha.
      apply (proj1 (may_rel2_iff (value_rel2 rho bound1 B) (value_rel2 rho bound2 B)
        (fun z q => IHB rho bound1 bound2 Hagree z q) (tm_app v a) (tm_app w b))).
      apply Happ; apply (proj2 (IHA rho bound1 bound2 Hagree a b)); exact Ha.
    + intros [T1 [b1 [T2 [b2 [Hs1 [Hs2 [Hv [Hw Happ]]]]]]]].
      exists T1, b1, T2, b2; split; [exact Hs1|]. split; [exact Hs2|].
      split; [exact Hv|]. split; [exact Hw|].
      intros a b Ha.
      apply (proj2 (may_rel2_iff (value_rel2 rho bound1 B) (value_rel2 rho bound2 B)
        (fun z q => IHB rho bound1 bound2 Hagree z q) (tm_app v a) (tm_app w b))).
      apply Happ; apply (proj1 (IHA rho bound1 bound2 Hagree a b)); exact Ha.
  - simpl; split.
    + intros [Hv [Hw [tf [tg [Hs1 [Hs2 Hall]]]]]].
      split; [exact Hv|]. split; [exact Hw|]. exists tf, tg; split; [exact Hs1|]. split; [exact Hs2|].
      intros U V R HU HV HR.
      apply (proj1 (may_rel2_iff (value_rel2 rho (R :: bound1) A) (value_rel2 rho (R :: bound2) A)
        (fun z q => IHA rho (R :: bound1) (R :: bound2)
          (nth_cons_agree K R bound1 bound2 Hagree) z q)
        (open_tm_ty tf U) (open_tm_ty tg V))).
      apply Hall; assumption.
    + intros [Hv [Hw [tf [tg [Hs1 [Hs2 Hall]]]]]].
      split; [exact Hv|]. split; [exact Hw|]. exists tf, tg; split; [exact Hs1|]. split; [exact Hs2|].
      intros U V R HU HV HR.
      apply (proj2 (may_rel2_iff (value_rel2 rho (R :: bound1) A) (value_rel2 rho (R :: bound2) A)
        (fun z q => IHA rho (R :: bound1) (R :: bound2)
          (nth_cons_agree K R bound1 bound2 Hagree) z q)
        (open_tm_ty tf U) (open_tm_ty tg V))).
      apply Hall; assumption.
  - simpl; tauto.
Qed.

Lemma value_rel2_subst_open : forall k T,
  forall rho pre U R,
    length pre = k ->
    locally_closed_ty U ->
    (forall v w, R v w <-> value_rel2 rho [] U v w) ->
    forall v w,
      value_rel2 rho (pre ++ R :: []) T v w <->
      value_rel2 rho pre (open_ty_rec k U T) v w.
Proof.
  intros k T; revert k; induction T as [i|X|A IHA B IHB|B IHB|];
    intros k rho pre U R Hlen HU HR v w.
  - simpl; destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; subst i; simpl.
      pose proof (proj1 (nth_insert_relation pre [] k (fun _ _ => False) R
        (fun _ _ => False) k Hlen) eq_refl) as Hnth.
      split; intro H.
      * rewrite Hnth in H.
        apply (proj2 (value_rel2_bound_irrel 0 U HU rho pre [] (fun j Hj => ltac:(lia)) v w)).
        apply (proj1 (HR v w)); exact H.
      * rewrite Hnth; apply (proj2 (HR v w)).
        apply (proj1 (value_rel2_bound_irrel 0 U HU rho pre [] (fun j Hj => ltac:(lia)) v w)).
        exact H.
    + assert (Hneq : i <> k) by (apply Nat.eqb_neq in E; congruence).
      rewrite (nth_insert_drop pre k R (fun _ _ => False) i Hlen Hneq); tauto.
  - simpl; tauto.
  - simpl; split.
    + intros [T1 [b1 [T2 [b2 [Hs1 [Hs2 [Hv [Hw Happ]]]]]]]].
      exists T1, b1, T2, b2; split; [exact Hs1|]. split; [exact Hs2|].
      split; [exact Hv|]. split; [exact Hw|].
      intros a b Ha.
      apply (proj1 (may_rel2_iff (value_rel2 rho (pre ++ R :: []) B)
        (value_rel2 rho pre (open_ty_rec k U B))
        (fun z q => IHB k rho pre U R Hlen HU HR z q) (tm_app v a) (tm_app w b))).
      apply Happ; apply (proj2 (IHA k rho pre U R Hlen HU HR a b)); exact Ha.
    + intros [T1 [b1 [T2 [b2 [Hs1 [Hs2 [Hv [Hw Happ]]]]]]]].
      exists T1, b1, T2, b2; split; [exact Hs1|]. split; [exact Hs2|].
      split; [exact Hv|]. split; [exact Hw|].
      intros a b Ha.
      apply (proj2 (may_rel2_iff (value_rel2 rho (pre ++ R :: []) B)
        (value_rel2 rho pre (open_ty_rec k U B))
        (fun z q => IHB k rho pre U R Hlen HU HR z q) (tm_app v a) (tm_app w b))).
      apply Happ; apply (proj1 (IHA k rho pre U R Hlen HU HR a b)); exact Ha.
  - simpl; split.
    + intros [Hv [Hw [tf [tg [Hs1 [Hs2 Hall]]]]]].
      split; [exact Hv|]. split; [exact Hw|]. exists tf, tg; split; [exact Hs1|]. split; [exact Hs2|].
      intros U' V' Q HU' HV' HQ.
      apply (proj1 (may_rel2_iff
        (value_rel2 rho ((Q :: pre) ++ R :: []) B)
        (value_rel2 rho (Q :: pre) (open_ty_rec (S k) U B))
        (fun z q => IHB (S k) rho (Q :: pre) U R ltac:(simpl; lia) HU HR z q)
        (open_tm_ty tf U') (open_tm_ty tg V'))).
      apply Hall; assumption.
    + intros [Hv [Hw [tf [tg [Hs1 [Hs2 Hall]]]]]].
      split; [exact Hv|]. split; [exact Hw|]. exists tf, tg; split; [exact Hs1|]. split; [exact Hs2|].
      intros U' V' Q HU' HV' HQ.
      apply (proj2 (may_rel2_iff
        (value_rel2 rho ((Q :: pre) ++ R :: []) B)
        (value_rel2 rho (Q :: pre) (open_ty_rec (S k) U B))
        (fun z q => IHB (S k) rho (Q :: pre) U R ltac:(simpl; lia) HU HR z q)
        (open_tm_ty tf U') (open_tm_ty tg V'))).
      apply Hall; assumption.
  - simpl; tauto.
Qed.

Lemma value_rel2_open_ty_empty : forall rho X R pre k T,
  length pre = k ->
  ~ In X (ty_fv T) ->
  forall v w,
    value_rel2 (atom_update rho X R) pre
      (open_ty_rec k (Ty_FVar X) T) v w <->
    value_rel2 rho (pre ++ R :: []) T v w.
Proof.
  intros rho X R pre k T; revert rho X R pre k.
  induction T as [i|Y|A IHA B IHB|B IHB|]; intros rho X R pre k Hlen Hfresh v w.
  - simpl; destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; subst i; simpl; split; intro H.
      * unfold atom_update in H; rewrite Nat.eqb_refl in H.
        rewrite (proj1 (nth_insert_relation pre [] k (fun _ _ => False) R
          (fun _ _ => False) k Hlen) eq_refl); exact H.
      * unfold atom_update; rewrite Nat.eqb_refl.
        rewrite <- (proj1 (nth_insert_relation pre [] k (fun _ _ => False) R
          (fun _ _ => False) k Hlen) eq_refl); exact H.
    + assert (Hneq : i <> k) by (apply Nat.eqb_neq in E; congruence).
      pose proof (nth_insert_drop pre k R (fun _ _ => False) i Hlen Hneq) as Hnth.
      simpl; split; intro H.
      * unfold atom_update in H; rewrite Hnth; exact H.
      * unfold atom_update; rewrite Hnth in H; exact H.
  - simpl; destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E; subst Y; exfalso; apply Hfresh; simpl; auto.
    + unfold atom_update; rewrite E; tauto.
  - simpl; split.
    + intros [T1 [b1 [T2 [b2 [Hs1 [Hs2 [Hv [Hw Happ]]]]]]]].
      exists T1, b1, T2, b2; split; [exact Hs1|]. split; [exact Hs2|].
      split; [exact Hv|]. split; [exact Hw|].
      intros a b Ha.
      apply (proj1 (may_rel2_iff
        (value_rel2 (atom_update rho X R) pre (open_ty_rec k (Ty_FVar X) B))
        (value_rel2 rho (pre ++ R :: []) B)
        (fun z q => IHB rho X R pre k Hlen
          (fun Hin => Hfresh (in_or_app _ _ _ (or_intror Hin))) z q)
        (tm_app v a) (tm_app w b))).
      apply Happ; apply (proj2 (IHA rho X R pre k Hlen
        (fun Hin => Hfresh (in_or_app _ _ _ (or_introl Hin))) a b)); exact Ha.
    + intros [T1 [b1 [T2 [b2 [Hs1 [Hs2 [Hv [Hw Happ]]]]]]]].
      exists T1, b1, T2, b2; split; [exact Hs1|]. split; [exact Hs2|].
      split; [exact Hv|]. split; [exact Hw|].
      intros a b Ha.
      apply (proj2 (may_rel2_iff
        (value_rel2 (atom_update rho X R) pre (open_ty_rec k (Ty_FVar X) B))
        (value_rel2 rho (pre ++ R :: []) B)
        (fun z q => IHB rho X R pre k Hlen
          (fun Hin => Hfresh (in_or_app _ _ _ (or_intror Hin))) z q)
        (tm_app v a) (tm_app w b))).
      apply Happ; apply (proj1 (IHA rho X R pre k Hlen
        (fun Hin => Hfresh (in_or_app _ _ _ (or_introl Hin))) a b)); exact Ha.
  - simpl; split.
    + intros [Hv [Hw [tf [tg [Hs1 [Hs2 Hall]]]]]].
      split; [exact Hv|]. split; [exact Hw|]. exists tf, tg; split; [exact Hs1|]. split; [exact Hs2|].
      intros U V Q HU HV HQ.
      apply (proj1 (may_rel2_iff
        (value_rel2 (atom_update rho X R) (Q :: pre)
          (open_ty_rec (S k) (Ty_FVar X) B))
        (value_rel2 rho ((Q :: pre) ++ R :: []) B)
        (fun z q => IHB rho X R (Q :: pre) (S k) ltac:(simpl; lia)
          (fun Hin => Hfresh Hin) z q)
        (open_tm_ty tf U) (open_tm_ty tg V))).
      apply Hall; assumption.
    + intros [Hv [Hw [tf [tg [Hs1 [Hs2 Hall]]]]]].
      split; [exact Hv|]. split; [exact Hw|]. exists tf, tg; split; [exact Hs1|]. split; [exact Hs2|].
      intros U V Q HU HV HQ.
      apply (proj2 (may_rel2_iff
        (value_rel2 (atom_update rho X R) (Q :: pre)
          (open_ty_rec (S k) (Ty_FVar X) B))
        (value_rel2 rho ((Q :: pre) ++ R :: []) B)
        (fun z q => IHB rho X R (Q :: pre) (S k) ltac:(simpl; lia)
          (fun Hin => Hfresh Hin) z q)
        (open_tm_ty tf U) (open_tm_ty tg V))).
      apply Hall; assumption.
  - simpl; tauto.
Qed.

Lemma value_rel2_rho_update_fresh : forall rho X R bound T,
  ~ In X (ty_fv T) ->
  forall v w,
    value_rel2 (atom_update rho X R) bound T v w <->
    value_rel2 rho bound T v w.
Proof.
  intros rho X R bound T; revert bound; induction T as [i|Y|A IHA B IHB|B IHB|]; intros bound Hfresh v w.
  - simpl; tauto.
  - simpl; destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E; subst Y; exfalso; apply Hfresh; simpl; auto.
    + unfold atom_update; rewrite E; tauto.
  - simpl; split.
    + intros [T1 [b1 [T2 [b2 [Hs1 [Hs2 [Hv [Hw Happ]]]]]]]].
      exists T1, b1, T2, b2; split; [exact Hs1|]. split; [exact Hs2|].
      split; [exact Hv|]. split; [exact Hw|].
      intros a b Ha.
      apply (proj1 (may_rel2_iff (value_rel2 (atom_update rho X R) bound B)
        (value_rel2 rho bound B)
        (fun z q => IHB bound (fun Hin => Hfresh (in_or_app _ _ _ (or_intror Hin))) z q)
        (tm_app v a) (tm_app w b))).
      apply Happ; apply (proj2 (IHA bound (fun Hin => Hfresh (in_or_app _ _ _ (or_introl Hin))) a b)); exact Ha.
    + intros [T1 [b1 [T2 [b2 [Hs1 [Hs2 [Hv [Hw Happ]]]]]]]].
      exists T1, b1, T2, b2; split; [exact Hs1|]. split; [exact Hs2|].
      split; [exact Hv|]. split; [exact Hw|].
      intros a b Ha.
      apply (proj2 (may_rel2_iff (value_rel2 (atom_update rho X R) bound B)
        (value_rel2 rho bound B)
        (fun z q => IHB bound (fun Hin => Hfresh (in_or_app _ _ _ (or_intror Hin))) z q)
        (tm_app v a) (tm_app w b))).
      apply Happ; apply (proj1 (IHA bound (fun Hin => Hfresh (in_or_app _ _ _ (or_introl Hin))) a b)); exact Ha.
  - simpl; split.
    + intros [Hv [Hw [tf [tg [Hs1 [Hs2 Hall]]]]]].
      split; [exact Hv|]. split; [exact Hw|]. exists tf, tg; split; [exact Hs1|]. split; [exact Hs2|].
      intros U V Q HU HV HQ.
      apply (proj1 (may_rel2_iff (value_rel2 (atom_update rho X R) (Q :: bound) B)
        (value_rel2 rho (Q :: bound) B)
        (fun z q => IHB (Q :: bound) Hfresh z q) (open_tm_ty tf U) (open_tm_ty tg V))).
      apply Hall; assumption.
    + intros [Hv [Hw [tf [tg [Hs1 [Hs2 Hall]]]]]].
      split; [exact Hv|]. split; [exact Hw|]. exists tf, tg; split; [exact Hs1|]. split; [exact Hs2|].
      intros U V Q HU HV HQ.
      apply (proj2 (may_rel2_iff (value_rel2 (atom_update rho X R) (Q :: bound) B)
        (value_rel2 rho (Q :: bound) B)
        (fun z q => IHB (Q :: bound) Hfresh z q) (open_tm_ty tf U) (open_tm_ty tg V))).
      apply Hall; assumption.
  - simpl; tauto.
Qed.

Fixpoint context_ty_fv (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => ty_fv T ++ context_ty_fv Gamma'
  end.

Lemma lookup_context_ty_fv : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (ty_fv T) -> In X (context_ty_fv Gamma).
Proof.
  intros Gamma; induction Gamma as [|[y A] Gamma IH]; intros x T X Hlook HX; simpl in Hlook; try discriminate.
  simpl; destruct (Nat.eqb x y) eqn:E.
  - inversion Hlook; subst T; apply in_or_app; left; exact HX.
  - apply in_or_app; right; eapply IH; eauto.
Qed.

Lemma may_rel2_choice_left : forall R t1 t2 u1 u2,
  locally_closed_tm t1 -> locally_closed_tm t2 ->
  locally_closed_tm u1 -> locally_closed_tm u2 ->
  may_rel2 R t1 u1 -> may_rel2 R (tm_choice t1 t2) (tm_choice u1 u2).
Proof.
  intros R t1 t2 u1 u2 Ht1 Ht2 Hu1 Hu2 [v [w [Ht [Hu [Hv [Hw HR]]]]]].
  exists v, w; repeat split; auto.
  - eapply multi_step; [apply ST_ChoiceLeft; assumption|exact Ht].
  - eapply multi_step; [apply ST_ChoiceLeft; assumption|exact Hu].
Qed.

Lemma may_rel2_choice_right : forall R t1 t2 u1 u2,
  locally_closed_tm t1 -> locally_closed_tm t2 ->
  locally_closed_tm u1 -> locally_closed_tm u2 ->
  may_rel2 R t2 u2 -> may_rel2 R (tm_choice t1 t2) (tm_choice u1 u2).
Proof.
  intros R t1 t2 u1 u2 Ht1 Ht2 Hu1 Hu2 [v [w [Ht [Hu [Hv [Hw HR]]]]]].
  exists v, w; repeat split; auto.
  - eapply multi_step; [apply ST_ChoiceRight; assumption|exact Ht].
  - eapply multi_step; [apply ST_ChoiceRight; assumption|exact Hu].
Qed.

Lemma multi_if_left : forall t t' a b,
  t -->* t' -> locally_closed_tm a -> locally_closed_tm b ->
  tm_if t a b -->* tm_if t' a b.
Proof.
  intros t t' a b H; induction H as [x|x y z Hxy Hyz IH]; intros Ha Hb.
  - constructor.
  - eapply multi_step; [eapply ST_If; eauto|].
    apply IH; assumption.
Qed.

Lemma may_rel2_refl : forall R t u,
  value t -> value u -> R t u -> may_rel2 R t u.
Proof.
  intros R t u Ht Hu HR; exists t, u; repeat split; try assumption; constructor.
Qed.

Lemma may_rel2_step : forall R t t' u u',
  t --> t' -> u --> u' -> may_rel2 R t' u' -> may_rel2 R t u.
Proof.
  intros R t t' u u' Ht Hu [v [w [Hv [Hw [Hvv [Hww HR]]]]]].
  exists v, w; repeat split; auto;
    eapply multi_step; eauto.
Qed.

Definition type_env_ok (theta1 theta2 : atom -> ty)
    (rho : atom -> tm -> tm -> Prop) : Prop :=
  forall X, locally_closed_ty (theta1 X) /\
            locally_closed_ty (theta2 X) /\
            candidate_rel (rho X).

Definition term_env_ok (rho : atom -> tm -> tm -> Prop) (Gamma : context)
    (sigma1 sigma2 : atom -> tm) : Prop :=
  (forall x, value (sigma1 x) /\ value (sigma2 x)) /\
  (forall x T, lookup_context x Gamma = Some T ->
     value_rel2 rho [] T (sigma1 x) (sigma2 x)).

Lemma type_env_ok_update : forall theta1 theta2 rho X U V R,
  type_env_ok theta1 theta2 rho ->
  locally_closed_ty U -> locally_closed_ty V -> candidate_rel R ->
  type_env_ok (atom_update theta1 X U) (atom_update theta2 X V) (atom_update rho X R).
Proof.
  intros theta1 theta2 rho X U V R Hok HU HV HR Y.
  unfold type_env_ok in Hok; destruct (Nat.eqb X Y) eqn:E.
  - apply Nat.eqb_eq in E; subst Y; unfold atom_update; rewrite Nat.eqb_refl; auto.
  - specialize (Hok Y); unfold atom_update; rewrite E; auto.
Qed.

Lemma lookup_update : forall Gamma x T y,
  lookup_context y (update Gamma x T) =
  if Nat.eqb y x then Some T else lookup_context y Gamma.
Proof. reflexivity. Qed.

Lemma term_env_ok_update : forall rho Gamma sigma1 sigma2 x T a b,
  term_env_ok rho Gamma sigma1 sigma2 ->
  value a -> value b -> value_rel2 rho [] T a b ->
  term_env_ok rho (update Gamma x T)
    (atom_update sigma1 x a) (atom_update sigma2 x b).
Proof.
  intros rho Gamma sigma1 sigma2 x T a b [Hvals Hrel] Ha Hb Hab.
  split.
  - intros y; unfold atom_update; destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E; subst y; auto.
    + apply Hvals.
  - intros y S Hlookup.
    rewrite lookup_update in Hlookup; destruct (Nat.eqb y x) eqn:E.
    + inversion Hlookup; subst S; unfold atom_update; rewrite Nat.eqb_sym, E; exact Hab.
    + unfold atom_update; rewrite Nat.eqb_sym, E.
      apply Hrel with (T := S); exact Hlookup.
Qed.

Fixpoint close_ty (theta : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow A B => Ty_Arrow (close_ty theta A) (close_ty theta B)
  | Ty_All A => Ty_All (close_ty theta A)
  | Ty_Bool => Ty_Bool
  end.

Fixpoint close_term (theta : atom -> ty) (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T b => tm_abs (close_ty theta T) (close_term theta sigma b)
  | tm_app a b => tm_app (close_term theta sigma a) (close_term theta sigma b)
  | tm_tabs b => tm_tabs (close_term theta sigma b)
  | tm_tapp a T => tm_tapp (close_term theta sigma a) (close_ty theta T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if a b c => tm_if (close_term theta sigma a) (close_term theta sigma b) (close_term theta sigma c)
  | tm_choice a b => tm_choice (close_term theta sigma a) (close_term theta sigma b)
  end.

Fixpoint tm_fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_true | tm_false => []
  | tm_fvar x => [x]
  | tm_abs _ b | tm_tabs b => tm_fv b
  | tm_app a b | tm_choice a b => tm_fv a ++ tm_fv b
  | tm_tapp a _ => tm_fv a
  | tm_if a b c => tm_fv a ++ tm_fv b ++ tm_fv c
  end.

Fixpoint tm_ty_fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_true | tm_false => []
  | tm_abs T b => ty_fv T ++ tm_ty_fv b
  | tm_app a b | tm_choice a b => tm_ty_fv a ++ tm_ty_fv b
  | tm_tabs b => tm_ty_fv b
  | tm_tapp a T => tm_ty_fv a ++ ty_fv T
  | tm_if a b c => tm_ty_fv a ++ tm_ty_fv b ++ tm_ty_fv c
  end.

Lemma not_in_app : forall (x : atom) l m,
  ~ In x (l ++ m) -> ~ In x l /\ ~ In x m.
Proof.
  intros x l m H; split; intros Hin; apply H; apply in_or_app; auto.
Qed.

Lemma close_ty_update_fresh : forall theta X U T,
  ~ In X (ty_fv T) -> close_ty (atom_update theta X U) T = close_ty theta T.
Proof.
  intros theta X U T; induction T; simpl; intros Hfresh; try reflexivity.
  - destruct (Nat.eqb X a) eqn:E; [apply Nat.eqb_eq in E; subst; exfalso; apply Hfresh; simpl; auto|unfold atom_update; rewrite E; reflexivity].
  - apply not_in_app in Hfresh as [HA HB]. rewrite IHT1 by exact HA; rewrite IHT2 by exact HB; reflexivity.
  - rewrite IHT by assumption; reflexivity.
Qed.

Lemma close_term_update_fresh : forall theta sigma x v t,
  ~ In x (tm_fv t) -> close_term theta (atom_update sigma x v) t = close_term theta sigma t.
Proof.
  intros theta sigma x v t; induction t; simpl; intros Hfresh; try reflexivity.
  - destruct (Nat.eqb x a) eqn:E; [apply Nat.eqb_eq in E; subst; exfalso; apply Hfresh; simpl; auto|unfold atom_update; rewrite E; reflexivity].
  - f_equal; rewrite IHt by assumption; reflexivity.
  - apply not_in_app in Hfresh as [Ha Hb]; rewrite IHt1 by exact Ha; rewrite IHt2 by exact Hb; reflexivity.
  - f_equal; apply IHt; assumption.
  - f_equal; apply IHt; assumption.
  - apply not_in_app in Hfresh as [Ha Hrest].
    apply not_in_app in Hrest as [Hb Hc].
    rewrite IHt1 by exact Ha; rewrite IHt2 by exact Hb; rewrite IHt3 by exact Hc; reflexivity.
  - apply not_in_app in Hfresh as [Ha Hb]; rewrite IHt1 by exact Ha; rewrite IHt2 by exact Hb; reflexivity.
Qed.

Lemma close_term_ty_update_fresh : forall theta sigma X U t,
  ~ In X (tm_ty_fv t) ->
  close_term (atom_update theta X U) sigma t = close_term theta sigma t.
Proof.
  intros theta sigma X U t; induction t; simpl; intros Hfresh; try reflexivity.
  - apply not_in_app in Hfresh as [HT Hb].
    rewrite close_ty_update_fresh by exact HT; rewrite IHt by exact Hb; reflexivity.
  - apply not_in_app in Hfresh as [Ha Hb]; rewrite IHt1 by exact Ha; rewrite IHt2 by exact Hb; reflexivity.
  - f_equal; apply IHt; assumption.
  - apply not_in_app in Hfresh as [Ha HT].
    rewrite IHt by exact Ha; rewrite close_ty_update_fresh by exact HT; reflexivity.
  - apply not_in_app in Hfresh as [Ha Hrest].
    apply not_in_app in Hrest as [Hb Hc].
    rewrite IHt1 by exact Ha; rewrite IHt2 by exact Hb; rewrite IHt3 by exact Hc; reflexivity.
  - apply not_in_app in Hfresh as [Ha Hb]; rewrite IHt1 by exact Ha; rewrite IHt2 by exact Hb; reflexivity.
Qed.

Lemma open_ty_rec_lc_offset : forall d T,
  lc_ty_at d T -> forall k U, open_ty_rec (k + d) U T = T.
Proof.
  intros d T H; induction H as
    [k i Hlt | k X | k A B HA IHA HB IHB | k A HA IHA | k];
    intros ext U; simpl; try reflexivity.
  - destruct (Nat.eqb (ext + k) i) eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + reflexivity.
  - f_equal; [apply IHA|apply IHB].
  - f_equal; replace (S (ext + k)) with (ext + S k) by lia; apply IHA.
Qed.

Lemma close_ty_open_rec : forall theta X U,
  locally_closed_ty U ->
  (forall Y, locally_closed_ty (theta Y)) ->
  forall k T,
  close_ty (atom_update theta X U) (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (close_ty (atom_update theta X U) T).
Proof.
  intros theta X U HU Htheta k T; revert k.
  induction T; intros k; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + unfold close_ty, atom_update; simpl; rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; subst a; unfold atom_update; rewrite Nat.eqb_refl.
      replace k with (k + 0) by lia; symmetry; exact (open_ty_rec_lc_offset 0 U HU k U).
    + unfold atom_update; rewrite E.
      replace k with (k + 0) by lia; symmetry; exact (open_ty_rec_lc_offset 0 (theta a) (Htheta a) k U).
  - rewrite IHT1, IHT2; reflexivity.
  - simpl; rewrite IHT; reflexivity.
  - reflexivity.
Qed.

Lemma open_tm_ty_rec_lc_offset : forall K d t,
  lc_tm_at K d t -> forall ext U, open_tm_ty_rec (ext + K) U t = t.
Proof.
  intros K d t H.
  induction H as
    [K d i Hlt | K d x | K d T b HT Hb IHb
    | K d a b Ha IHa Hb IHb | K d b Hb IHb
    | K d a T Ha IHa HT | K d | K d
    | K d a b c Ha IHa Hb IHb Hc IHc
    | K d a b Ha IHa Hb IHb]; intros ext U; simpl; try reflexivity.
  - f_equal.
    + exact (open_ty_rec_lc_offset K T HT ext U).
    + apply IHb.
  - f_equal; [apply IHa|apply IHb].
  - f_equal; replace (S (ext + K)) with (ext + S K) by lia; apply IHb.
  - f_equal.
    + apply IHa.
    + exact (open_ty_rec_lc_offset K T HT ext U).
  - f_equal; [apply IHa|apply IHb|apply IHc].
  - f_equal; [apply IHa|apply IHb].
Qed.

Lemma lc_ty_weaken : forall K T, lc_ty_at K T -> lc_ty_at (S K) T.
Proof.
  intros K T H; induction H; eauto using lc_ty_at; try constructor; lia.
Qed.

Lemma lc_tm_weaken_ty : forall K k t,
  lc_tm_at K k t -> lc_tm_at (S K) k t.
Proof.
  intros K k t H; induction H; eauto using lc_tm_at, lc_ty_weaken.
Qed.

Lemma lc_ty_open_rec_inv : forall K X T,
  lc_ty_at K (open_ty_rec K (Ty_FVar X) T) -> lc_ty_at (S K) T.
Proof.
  intros K X T H; revert K X H; induction T; intros K X H; simpl in H.
  - destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E; subst n; constructor; lia.
    + inversion H; subst; constructor; lia.
  - inversion H; subst; constructor.
  - inversion H; subst; constructor; [apply IHT1 with (X := X)|apply IHT2 with (X := X)]; assumption.
  - inversion H; subst; constructor; apply IHT with (X := X); assumption.
  - constructor.
Qed.

Lemma lc_tm_ty_open_rec_inv : forall K k X t,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  intros K k X t H; revert K k X H; induction t; intros K k X H; simpl in H.
  - inversion H; subst; constructor; assumption.
  - inversion H; subst; constructor.
  - inversion H; subst; constructor.
    + apply lc_ty_open_rec_inv with (X := X); assumption.
    + apply IHt with (X := X); assumption.
  - inversion H; subst; constructor.
    + apply IHt1 with (X := X); assumption.
    + apply IHt2 with (X := X); assumption.
  - inversion H; subst; constructor; apply IHt with (K := S K) (X := X); assumption.
  - inversion H; subst; constructor.
    + apply IHt with (X := X); assumption.
    + apply lc_ty_open_rec_inv with (X := X); assumption.
  - inversion H; constructor.
  - inversion H; constructor.
  - inversion H; subst; constructor.
    + apply IHt1 with (X := X); assumption.
    + apply IHt2 with (X := X); assumption.
    + apply IHt3 with (X := X); assumption.
  - inversion H; subst; constructor.
    + apply IHt1 with (X := X); assumption.
    + apply IHt2 with (X := X); assumption.
Qed.

Lemma lc_tm_open_rec_inv : forall K k x t,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  intros K k x t H; revert K k x H; induction t; intros K k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst n; constructor; lia.
    + inversion H; subst; constructor; lia.
  - inversion H; subst; constructor.
  - inversion H; subst; constructor.
    + assumption.
    + apply IHt with (k := S k) (x := x); assumption.
  - inversion H; subst; constructor.
    + apply IHt1 with (k := k) (x := x); assumption.
    + apply IHt2 with (k := k) (x := x); assumption.
  - inversion H; subst; constructor; apply IHt with (K := S K) (k := k) (x := x); assumption.
  - inversion H; subst; constructor.
    + apply IHt with (k := k) (x := x); assumption.
    + assumption.
  - inversion H; constructor.
  - inversion H; constructor.
  - inversion H; subst; constructor.
    + apply IHt1 with (k := k) (x := x); assumption.
    + apply IHt2 with (k := k) (x := x); assumption.
    + apply IHt3 with (k := k) (x := x); assumption.
  - inversion H; subst; constructor.
    + apply IHt1 with (k := k) (x := x); assumption.
    + apply IHt2 with (k := k) (x := x); assumption.
Qed.

Fixpoint max_atom (L : list atom) : atom :=
  match L with
  | [] => 0
  | x :: L' => Nat.max x (max_atom L')
  end.

Lemma in_le_max_atom : forall x L, In x L -> x <= max_atom L.
Proof.
  intros x L; induction L as [|a L IH]; simpl; intros Hin; [contradiction|].
  destruct Hin as [Heq|Hin].
  - subst x; apply Nat.le_max_l.
  - apply Nat.le_trans with (m := max_atom L); [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

Definition fresh_atom (L : list atom) : atom := S (max_atom L).

Lemma fresh_atom_notin : forall L, ~ In (fresh_atom L) L.
Proof.
  intros L Hin; unfold fresh_atom in Hin.
  pose proof (in_le_max_atom _ _ Hin); lia.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H as
    [Delta X Hin | Delta A B HA IHA HB IHB
    | L Delta T Hbody IH | Delta].
  - constructor.
  - constructor; assumption.
  - unfold locally_closed_ty; constructor.
    specialize (IH (fresh_atom L) (fresh_atom_notin L)).
    unfold locally_closed_ty in IH.
    exact (lc_ty_open_rec_inv 0 (fresh_atom L) T IH).
  - constructor.
Qed.

Lemma has_type_lc : forall Delta Gamma t T, has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H as
    [Delta Gamma x T Hlookup0 Hwf
    |L Delta Gamma T1 body T2 Hwf Hbody IHbody
    |Delta Gamma f a A B Hf IHf Ha IHa
    |L Delta Gamma body T Hbody IHbody
    |Delta Gamma f T U Hf IHf Hwf
    |Delta Gamma |Delta Gamma
    |Delta Gamma c a b T Hc IHc Ha IHa Hb IHb
    |Delta Gamma a b T Ha IHa Hb IHb].
  - constructor.
  - unfold locally_closed_tm; constructor.
    + exact (wf_ty_lc _ _ Hwf).
    + specialize (IHbody (fresh_atom L) (fresh_atom_notin L)).
      exact (lc_tm_open_rec_inv 0 0 (fresh_atom L) body IHbody).
  - constructor; assumption.
  - unfold locally_closed_tm; constructor.
    specialize (IHbody (fresh_atom L) (fresh_atom_notin L)).
    exact (lc_tm_ty_open_rec_inv 0 0 (fresh_atom L) body IHbody).
  - constructor; [assumption|exact (wf_ty_lc _ _ Hwf)].
  - constructor.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma lc_ty_weaken_any : forall K K' T,
  K <= K' -> lc_ty_at K T -> lc_ty_at K' T.
Proof.
  intros K K' T Hle H; revert K' Hle.
  induction H as [K i Hlt|K X|K A B HA IHA HB IHB|K A HA IHA|K]; intros K' Hle.
  - constructor; lia.
  - constructor.
  - constructor; [apply IHA|apply IHB]; lia.
  - constructor; apply IHA; lia.
  - constructor.
Qed.

Lemma lc_tm_weaken_any : forall K k t K' k',
  K <= K' -> k <= k' -> lc_tm_at K k t -> lc_tm_at K' k' t.
Proof.
  intros K k t K' k' HK Hk H; revert K' k' HK Hk.
  induction H as
    [K k i Hlt | K k x | K k T b HT Hb IHb
    | K k a b Ha IHa Hb IHb | K k b Hb IHb
    | K k a T Ha IHa HT | K k | K k
    | K k a b c Ha IHa Hb IHb Hc IHc
    | K k a b Ha IHa Hb IHb]; intros K' k' HK Hk.
  - constructor; lia.
  - constructor.
  - constructor.
    + eapply lc_ty_weaken_any; eauto.
    + apply IHb; lia.
  - constructor; [apply IHa|apply IHb]; lia.
  - constructor; apply IHb; lia.
  - constructor.
    + apply IHa; lia.
    + eapply lc_ty_weaken_any; eauto.
  - constructor.
  - constructor.
  - constructor; [apply IHa|apply IHb|apply IHc]; lia.
  - constructor; [apply IHa|apply IHb]; lia.
Qed.

Lemma close_ty_lc : forall K T,
  lc_ty_at K T -> forall theta, (forall X, locally_closed_ty (theta X)) ->
  lc_ty_at K (close_ty theta T).
Proof.
  intros K T H; induction H as [K i Hlt|K X|K A B HA IHA HB IHB|K A HA IHA|K]; intros theta Htheta; simpl.
  - constructor; assumption.
  - exact (lc_ty_weaken_any 0 K (theta X) (Nat.le_0_l K) (Htheta X)).
  - constructor; [apply IHA|apply IHB]; assumption.
  - constructor; apply IHA; assumption.
  - constructor.
Qed.

Lemma close_term_lc : forall K k t,
  lc_tm_at K k t ->
  forall theta sigma,
    (forall X, locally_closed_ty (theta X)) ->
    (forall x, locally_closed_tm (sigma x)) ->
    lc_tm_at K k (close_term theta sigma t).
Proof.
  intros K k t H.
  induction H as
    [K k i Hlt | K k x | K k T b HT Hb IHb
    | K k a b Ha IHa Hb IHb | K k b Hb IHb
    | K k a T Ha IHa HT | K k | K k
    | K k a b c Ha IHa Hb IHb Hc IHc
    | K k a b Ha IHa Hb IHb];
    intros theta sigma Htheta Hsigma; simpl.
  - constructor; assumption.
  - exact (lc_tm_weaken_any 0 0 (sigma x) K k (Nat.le_0_l K) (Nat.le_0_l k) (Hsigma x)).
  - constructor.
    + eapply close_ty_lc; eauto.
    + apply IHb; assumption.
  - constructor; [apply IHa|apply IHb]; assumption.
  - constructor; apply IHb; assumption.
  - constructor.
    + apply IHa; assumption.
    + eapply close_ty_lc; eauto.
  - constructor.
  - constructor.
  - constructor; [apply IHa|apply IHb|apply IHc]; assumption.
  - constructor; [apply IHa|apply IHb]; assumption.
Qed.

Lemma close_term_ty_open_rec : forall theta sigma X U,
  locally_closed_ty U ->
  (forall Y, locally_closed_ty (theta Y)) ->
  (forall y, locally_closed_tm (sigma y)) ->
  forall k t,
  close_term (atom_update theta X U) sigma
    (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (close_term (atom_update theta X U) sigma t).
Proof.
  intros theta sigma X U HU Htheta Hsigma k t; revert k.
  induction t; intros k; simpl; try reflexivity.
  all: try (unfold close_term; simpl; reflexivity).
  - unfold close_term; simpl; replace k with (k + 0) by lia.
    symmetry; exact (open_tm_ty_rec_lc_offset 0 0 (sigma a) (Hsigma a) k U).
  - f_equal.
    + apply close_ty_open_rec; assumption.
    + apply IHt.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal; apply IHt.
  - f_equal; [apply IHt|apply close_ty_open_rec; assumption].
  - f_equal; [apply IHt1|apply IHt2|apply IHt3].
  - f_equal; [apply IHt1|apply IHt2].
Qed.

Lemma open_tm_rec_lc_offset : forall K d t,
  lc_tm_at K d t -> forall k u, open_tm_rec (k + d) u t = t.
Proof.
  intros K d t H.
  induction H as
    [K k i Hlt | K k x | K k T b HT Hb IHb
    | K k a b Ha IHa Hb IHb | K k b Hb IHb
    | K k a T Ha IHa HT | K k | K k
    | K k a b c Ha IHa Hb IHb Hc IHc
    | K k a b Ha IHa Hb IHb]; intros ext u; simpl; try reflexivity.
  - destruct (Nat.eqb (ext + k) i) eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + reflexivity.
  - f_equal; replace (S (ext + k)) with (ext + S k) by lia; apply IHb.
  - f_equal; [apply IHa|apply IHb].
  - f_equal; apply IHb.
  - f_equal; apply IHa.
  - f_equal; [apply IHa|apply IHb|apply IHc].
  - f_equal; [apply IHa|apply IHb].
Qed.

Lemma close_term_open_rec : forall theta sigma x v,
  locally_closed_tm v ->
  (forall y, locally_closed_tm (sigma y)) ->
  forall k t,
  close_term theta (atom_update sigma x v) (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (close_term theta (atom_update sigma x v) t).
Proof.
  intros theta sigma x v Hvl Hsigma.
  intros k t; revert k; induction t; intros k; simpl; try rewrite IHt; try rewrite IHt1; try rewrite IHt2; try rewrite IHt3; try reflexivity.
  - destruct (Nat.eqb k n) eqn:E.
    + unfold close_term, atom_update; simpl; rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E; subst a; unfold atom_update; rewrite Nat.eqb_refl.
      unfold open_tm; simpl; replace k with (k + 0) by lia; symmetry.
      exact (open_tm_rec_lc_offset 0 0 v Hvl k v).
    + unfold atom_update; rewrite E.
      replace k with (k + 0) by lia; symmetry.
      exact (open_tm_rec_lc_offset 0 0 (sigma a) (Hsigma a) k v).
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta1 theta2 rho sigma1 sigma2,
    type_env_ok theta1 theta2 rho ->
    term_env_ok rho Gamma sigma1 sigma2 ->
    may_rel2 (value_rel2 rho [] T)
      (close_term theta1 sigma1 t) (close_term theta2 sigma2 t).
Proof.
  intros Delta Gamma t T Hty.
  induction Hty as
    [Delta Gamma x T Hlookup Hwf
    |L Delta Gamma T1 body T2 Hwf Hbody IHbody
    |Delta Gamma t1 t2 T1 T2 Ht1 IHt1 Ht2 IHt2
    |L Delta Gamma body T Hbody IHbody
    |Delta Gamma t T U Ht IHt HwfU
    |Delta Gamma |Delta Gamma
    |Delta Gamma c t1 t2 T Hc IHc H1 IH1 H2 IH2
    |Delta Gamma t1 t2 T H1 IH1 H2 IH2];
    intros theta1 theta2 rho sigma1 sigma2 Htyenv Htermenv.
  - destruct Htermenv as [Hvals Hctxrel].
    simpl; eapply may_rel2_refl; [apply Hvals|apply Hvals|].
    apply Hctxrel with (T := T); assumption.
  - destruct Htermenv as [Hvals Hlookup].
    assert (Hx : ~ In (fresh_atom (L ++ tm_fv body)) L).
    { intro Hin; apply (fresh_atom_notin (L ++ tm_fv body)); apply in_or_app; left; exact Hin. }
    assert (Hxfv : ~ In (fresh_atom (L ++ tm_fv body)) (tm_fv body)).
    { intro Hin; apply (fresh_atom_notin (L ++ tm_fv body)); apply in_or_app; right; exact Hin. }
    set (x := fresh_atom (L ++ tm_fv body)).
    assert (Hlcabs : locally_closed_tm (tm_abs T1 body)).
    { unfold locally_closed_tm; constructor.
      - exact (wf_ty_lc _ _ Hwf).
      - specialize (Hbody x Hx).
        pose proof (has_type_lc _ _ _ _ Hbody) as Hopened.
        exact (lc_tm_open_rec_inv 0 0 x body Hopened). }
    assert (Hsig1 : forall y, locally_closed_tm (sigma1 y)).
    { intros y; apply value_lc; apply (proj1 (Hvals y)). }
    assert (Hsig2 : forall y, locally_closed_tm (sigma2 y)).
    { intros y; apply value_lc; apply (proj2 (Hvals y)). }
    pose proof (close_term_lc 0 0 (tm_abs T1 body) Hlcabs theta1 sigma1) as Hlc1.
    assert (Hlc1env : (forall X, locally_closed_ty (theta1 X)) /\
      (forall x, locally_closed_tm (sigma1 x))) by (split; [intros; destruct (Htyenv X); assumption|exact Hsig1]).
    specialize (Hlc1 (proj1 Hlc1env) Hsig1).
    pose proof (close_term_lc 0 0 (tm_abs T1 body) Hlcabs theta2 sigma2) as Hlc2.
    assert (Hlc2env : (forall X, locally_closed_ty (theta2 X)) /\
      (forall x, locally_closed_tm (sigma2 x))) by (split; [intros; destruct (Htyenv X); tauto|exact Hsig2]).
    specialize (Hlc2 (proj1 Hlc2env) Hsig2).
    simpl; apply may_rel2_refl.
    + apply v_abs; exact Hlc1.
    + apply v_abs; exact Hlc2.
    + simpl.
      exists (close_ty theta1 T1), (close_term theta1 sigma1 body),
        (close_ty theta2 T1), (close_term theta2 sigma2 body).
      split; [reflexivity|]. split; [reflexivity|].
      split; [apply v_abs; exact Hlc1|]. split; [apply v_abs; exact Hlc2|].
      intros a b Hab.
      assert (Hargvals : value a /\ value b).
      { eapply value_rel2_values.
        - intros Y; exact (proj2 (proj2 (Htyenv Y))).
        - constructor.
        - exact Hab. }
      destruct Hargvals as [Hva Hvb].
      pose proof (term_env_ok_update rho Gamma sigma1 sigma2 x T1 a b
        (conj Hvals Hlookup) Hva Hvb Hab) as Htermenv'.
      specialize (IHbody x Hx theta1 theta2 rho
        (atom_update sigma1 x a) (atom_update sigma2 x b) Htyenv Htermenv')
        as HbodyMay.
      assert (Hcomm1 :
        close_term theta1 (atom_update sigma1 x a) (open_tm body (tm_fvar x)) =
        open_tm (close_term theta1 sigma1 body) a).
      { unfold open_tm.
        rewrite (close_term_open_rec theta1 sigma1 x a
          (value_lc _ Hva) Hsig1 0 body).
        rewrite close_term_update_fresh by exact Hxfv; reflexivity. }
      assert (Hcomm2 :
        close_term theta2 (atom_update sigma2 x b) (open_tm body (tm_fvar x)) =
        open_tm (close_term theta2 sigma2 body) b).
      { unfold open_tm.
        rewrite (close_term_open_rec theta2 sigma2 x b
          (value_lc _ Hvb) Hsig2 0 body).
        rewrite close_term_update_fresh by exact Hxfv; reflexivity. }
      rewrite Hcomm1, Hcomm2 in HbodyMay.
      eapply may_rel2_step.
      * apply ST_AppAbs; assumption.
      * apply ST_AppAbs; assumption.
      * exact HbodyMay.
  - pose proof (IHt1 theta1 theta2 rho sigma1 sigma2 Htyenv Htermenv) as Hfunexp.
    pose proof (IHt2 theta1 theta2 rho sigma1 sigma2 Htyenv Htermenv) as Hargexp.
    destruct Hfunexp as [vf [vg [Hmf [Hmg [Hvf [Hvg Hfun]]]]]].
    destruct Hargexp as [va [vb [Hma [Hmb [Hva [Hvb Harg]]]]]].
    destruct Hfun as [FT [bf [GT [bg [Hfshape [Hgshape [Hfv [Hgv Happly]]]]]]]].
    assert (Hargvals : value va /\ value vb).
    { eapply value_rel2_values; [|constructor|exact Harg]. intros X; exact (proj2 (proj2 (Htyenv X))). }
    destruct Hargvals as [Hva' Hvb'].
    assert (Hsig1 : forall x, locally_closed_tm (sigma1 x)).
    { intros x; apply value_lc; exact (proj1 ((proj1 Htermenv) x)). }
    assert (Hsig2 : forall x, locally_closed_tm (sigma2 x)).
    { intros x; apply value_lc; exact (proj2 ((proj1 Htermenv) x)). }
    assert (Htheta1 : forall X, locally_closed_ty (theta1 X)).
    { intros X; exact (proj1 (Htyenv X)). }
    assert (Htheta2 : forall X, locally_closed_ty (theta2 X)).
    { intros X; exact (proj1 (proj2 (Htyenv X))). }
    pose proof (close_term_lc 0 0 t2 (has_type_lc _ _ _ _ Ht2) theta1 sigma1 Htheta1 Hsig1) as Hlcarg1.
    pose proof (close_term_lc 0 0 t2 (has_type_lc _ _ _ _ Ht2) theta2 sigma2 Htheta2 Hsig2) as Hlcarg2.
    assert (Hpath1 :
      tm_app (close_term theta1 sigma1 t1) (close_term theta1 sigma1 t2) -->* tm_app vf va).
    { simpl; eapply multi_trans.
      - apply multi_app_left; eauto.
      - apply multi_app_right; eauto. }
    assert (Hpath2 :
      tm_app (close_term theta2 sigma2 t1) (close_term theta2 sigma2 t2) -->* tm_app vg vb).
    { simpl; eapply multi_trans.
      - apply multi_app_left; eauto.
      - apply multi_app_right; eauto. }
    specialize (Happly va vb Harg) as Happ.
    destruct Happ as [r1 [r2 [Hout1 [Hout2 [Hr1 [Hr2 Hrel]]]]]].
    simpl; exists r1, r2; repeat split; try assumption.
    + eapply multi_trans; [exact Hpath1|exact Hout1].
    + eapply multi_trans; [exact Hpath2|exact Hout2].
  - destruct Htermenv as [Hvals Hlookup].
    set (X := fresh_atom (((L ++ ty_fv T) ++ tm_ty_fv body) ++ context_ty_fv Gamma)).
    assert (HXL : ~ In X L).
    { intro Hin; apply (fresh_atom_notin (((L ++ ty_fv T) ++ tm_ty_fv body) ++ context_ty_fv Gamma)).
      unfold X; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin. }
    assert (HXT : ~ In X (ty_fv T)).
    { intro Hin; apply (fresh_atom_notin (((L ++ ty_fv T) ++ tm_ty_fv body) ++ context_ty_fv Gamma)).
      unfold X; apply in_or_app; left; apply in_or_app; left; apply in_or_app; right; exact Hin. }
    assert (HXbody : ~ In X (tm_ty_fv body)).
    { intro Hin; apply (fresh_atom_notin (((L ++ ty_fv T) ++ tm_ty_fv body) ++ context_ty_fv Gamma)).
      unfold X; apply in_or_app; left; apply in_or_app; right; exact Hin. }
    assert (HXGamma : ~ In X (context_ty_fv Gamma)).
    { intro Hin; apply (fresh_atom_notin (((L ++ ty_fv T) ++ tm_ty_fv body) ++ context_ty_fv Gamma)).
      unfold X; apply in_or_app; right; exact Hin. }
    assert (Hraw : lc_tm_at 1 0 body).
    { specialize (Hbody X HXL).
      pose proof (has_type_lc _ _ _ _ Hbody) as Hopen.
      exact (lc_tm_ty_open_rec_inv 0 0 X body Hopen). }
    assert (Hlcabs : locally_closed_tm (tm_tabs body)).
    { unfold locally_closed_tm; constructor; exact Hraw. }
    assert (Hsig1 : forall y, locally_closed_tm (sigma1 y)).
    { intros y; apply value_lc; exact (proj1 (Hvals y)). }
    assert (Hsig2 : forall y, locally_closed_tm (sigma2 y)).
    { intros y; apply value_lc; exact (proj2 (Hvals y)). }
    assert (Htheta1 : forall Y, locally_closed_ty (theta1 Y)).
    { intros Y; exact (proj1 (Htyenv Y)). }
    assert (Htheta2 : forall Y, locally_closed_ty (theta2 Y)).
    { intros Y; exact (proj1 (proj2 (Htyenv Y))). }
    pose proof (close_term_lc 0 0 (tm_tabs body) Hlcabs theta1 sigma1 Htheta1 Hsig1) as Hlc1.
    pose proof (close_term_lc 0 0 (tm_tabs body) Hlcabs theta2 sigma2 Htheta2 Hsig2) as Hlc2.
    simpl; apply may_rel2_refl.
    + apply v_tabs; exact Hlc1.
    + apply v_tabs; exact Hlc2.
    + simpl; split; [apply v_tabs; exact Hlc1|].
      split; [apply v_tabs; exact Hlc2|].
      exists (close_term theta1 sigma1 body), (close_term theta2 sigma2 body).
      split; [reflexivity|]. split; [reflexivity|].
      intros U V R HU HV HR.
      pose proof (type_env_ok_update theta1 theta2 rho X U V R Htyenv HU HV HR) as Htyenv'.
      specialize (Hbody X HXL) as HbodyX.
      assert (Htermenv' : term_env_ok (atom_update rho X R) Gamma sigma1 sigma2).
      { split; [exact Hvals|]. intros y S Hlook.
        pose proof (Hlookup y S Hlook) as HrelYS.
        apply (proj2 (value_rel2_rho_update_fresh rho X R [] S
          (fun Hin => HXGamma (lookup_context_ty_fv Gamma y S X Hlook Hin))
          (sigma1 y) (sigma2 y))).
        exact HrelYS. }
      specialize (IHbody X HXL
        (atom_update theta1 X U) (atom_update theta2 X V) (atom_update rho X R)
        sigma1 sigma2 Htyenv' Htermenv') as Hopened.
      assert (Hcomm1 :
        close_term (atom_update theta1 X U) sigma1 (open_tm_ty body (Ty_FVar X)) =
        open_tm_ty (close_term theta1 sigma1 body) U).
      { pose proof (close_term_ty_open_rec theta1 sigma1 X U HU Htheta1 Hsig1 0 body) as Hc.
        rewrite (close_term_ty_update_fresh theta1 sigma1 X U body HXbody) in Hc.
        exact Hc. }
      assert (Hcomm2 :
        close_term (atom_update theta2 X V) sigma2 (open_tm_ty body (Ty_FVar X)) =
        open_tm_ty (close_term theta2 sigma2 body) V).
      { pose proof (close_term_ty_open_rec theta2 sigma2 X V HV Htheta2 Hsig2 0 body) as Hc.
        rewrite (close_term_ty_update_fresh theta2 sigma2 X V body HXbody) in Hc.
        exact Hc. }
      rewrite Hcomm1, Hcomm2 in Hopened.
      pose proof (value_rel2_open_ty_empty rho X R [] 0 T eq_refl HXT) as Hrel.
      apply (proj1 (may_rel2_iff
        (value_rel2 (atom_update rho X R) [] (open_ty T (Ty_FVar X)))
        (value_rel2 rho (R :: []) T)
        (fun z q => Hrel z q)
        (open_tm_ty (close_term theta1 sigma1 body) U)
        (open_tm_ty (close_term theta2 sigma2 body) V))).
      exact Hopened.
  - pose proof (IHt theta1 theta2 rho sigma1 sigma2 Htyenv Htermenv) as Hfun.
    destruct Hfun as [vf [vg [Hf [Hg [Hvf [Hvg Hrel]]]]]].
    simpl in Hrel.
    destruct Hrel as [Hvf' [Hvg' [bf [bg [Hshape1 [Hshape2 Hall]]]]]].
    assert (HU1 : locally_closed_ty (close_ty theta1 U)).
    { eapply close_ty_lc; [apply wf_ty_lc with (Delta := Delta); exact HwfU|].
      exact (fun X => proj1 (Htyenv X)). }
    assert (HU2 : locally_closed_ty (close_ty theta2 U)).
    { eapply close_ty_lc; [apply wf_ty_lc with (Delta := Delta); exact HwfU|].
      intros X; exact (proj1 (proj2 (Htyenv X))). }
    assert (HR : candidate_rel (value_rel2 rho [] U)).
    { unfold candidate_rel; intros a b Hab.
      eapply value_rel2_values.
      - intros X; exact (proj2 (proj2 (Htyenv X))).
      - constructor.
      - exact Hab. }
    pose proof (Hall (close_ty theta1 U) (close_ty theta2 U)
      (value_rel2 rho [] U) HU1 HU2 HR) as Hbody.
    pose proof (value_rel2_subst_open 0 T rho [] U
      (value_rel2 rho [] U) eq_refl (wf_ty_lc _ _ HwfU)
      (fun a b => conj (fun H => H) (fun H => H))) as Hsubst.
    apply (proj1 (may_rel2_iff
      (value_rel2 rho ((value_rel2 rho [] U) :: []) T)
      (value_rel2 rho [] (open_ty T U))
      (fun a b => Hsubst a b)
      (open_tm_ty bf (close_ty theta1 U))
      (open_tm_ty bg (close_ty theta2 U)))) in Hbody.
    destruct Hbody as [r1 [r2 [Hb1 [Hb2 [Hr1 [Hr2 Hrelout]]]]]].
    assert (Hpath1 :
      tm_tapp (close_term theta1 sigma1 t) (close_ty theta1 U) -->*
      open_tm_ty bf (close_ty theta1 U)).
    { inversion Hshape1; subst vf.
      eapply multi_trans.
      - apply multi_tapp; [exact Hf|exact HU1].
      - apply multi_type_beta; [apply value_lc; exact Hvf|exact HU1]. }
    assert (Hpath2 :
      tm_tapp (close_term theta2 sigma2 t) (close_ty theta2 U) -->*
      open_tm_ty bg (close_ty theta2 U)).
    { inversion Hshape2; subst vg.
      eapply multi_trans.
      - apply multi_tapp; [exact Hg|exact HU2].
      - apply multi_type_beta; [apply value_lc; exact Hvg|exact HU2]. }
    simpl; exists r1, r2; repeat split; try assumption.
    + eapply multi_trans; [exact Hpath1|exact Hb1].
    + eapply multi_trans; [exact Hpath2|exact Hb2].
  - simpl; apply may_rel2_refl; [apply v_true|apply v_true|left; auto].
  - simpl; apply may_rel2_refl; [apply v_false|apply v_false|right; auto].
  - pose proof (IHc theta1 theta2 rho sigma1 sigma2 Htyenv Htermenv) as Hguard.
    pose proof (IH1 theta1 theta2 rho sigma1 sigma2 Htyenv Htermenv) as Hthen.
    pose proof (IH2 theta1 theta2 rho sigma1 sigma2 Htyenv Htermenv) as Helse.
    destruct Hguard as [vc [vd [Hcpath [Hdpath [Hvc [Hvd Hbool]]]]]].
    simpl in Hbool; destruct Hbool as [[Hvc' Hvd']|[Hvc' Hvd']].
    + subst vc; subst vd.
      destruct Hthen as [va [vb [Hapath [Hbpath [Hva [Hvb Hrelab]]]]]].
      assert (Hlc11 : locally_closed_tm (close_term theta1 sigma1 t1)).
      { apply (close_term_lc 0 0 t1 (has_type_lc _ _ _ _ H1) theta1 sigma1).
        - intros X; exact (proj1 (Htyenv X)).
        - intros x; apply value_lc; exact (proj1 ((proj1 Htermenv) x)). }
      assert (Hlc12 : locally_closed_tm (close_term theta1 sigma1 t2)).
      { apply (close_term_lc 0 0 t2 (has_type_lc _ _ _ _ H2) theta1 sigma1).
        - intros X; exact (proj1 (Htyenv X)).
        - intros x; apply value_lc; exact (proj1 ((proj1 Htermenv) x)). }
      assert (Hlc21 : locally_closed_tm (close_term theta2 sigma2 t1)).
      { apply (close_term_lc 0 0 t1 (has_type_lc _ _ _ _ H1) theta2 sigma2).
        - intros X; exact (proj1 (proj2 (Htyenv X))).
        - intros x; apply value_lc; exact (proj2 ((proj1 Htermenv) x)). }
      assert (Hlc22 : locally_closed_tm (close_term theta2 sigma2 t2)).
      { apply (close_term_lc 0 0 t2 (has_type_lc _ _ _ _ H2) theta2 sigma2).
        - intros X; exact (proj1 (proj2 (Htyenv X))).
        - intros x; apply value_lc; exact (proj2 ((proj1 Htermenv) x)). }
      assert (Hpath1 : close_term theta1 sigma1 (tm_if c t1 t2) -->* va).
      { simpl; eapply multi_trans.
        - apply multi_if_left; [exact Hcpath|exact Hlc11|exact Hlc12].
        - eapply multi_step; [apply ST_IfTrue; assumption|exact Hapath]. }
      assert (Hpath2 : close_term theta2 sigma2 (tm_if c t1 t2) -->* vb).
      { simpl; eapply multi_trans.
        - apply multi_if_left; [exact Hdpath|exact Hlc21|exact Hlc22].
        - eapply multi_step; [apply ST_IfTrue; assumption|exact Hbpath]. }
      simpl; exists va, vb; repeat split; try assumption.
    + subst vc; subst vd.
      destruct Helse as [va [vb [Hapath [Hbpath [Hva [Hvb Hrelab]]]]]].
      assert (Hlc11 : locally_closed_tm (close_term theta1 sigma1 t1)).
      { apply (close_term_lc 0 0 t1 (has_type_lc _ _ _ _ H1) theta1 sigma1).
        - intros X; exact (proj1 (Htyenv X)).
        - intros x; apply value_lc; exact (proj1 ((proj1 Htermenv) x)). }
      assert (Hlc12 : locally_closed_tm (close_term theta1 sigma1 t2)).
      { apply (close_term_lc 0 0 t2 (has_type_lc _ _ _ _ H2) theta1 sigma1).
        - intros X; exact (proj1 (Htyenv X)).
        - intros x; apply value_lc; exact (proj1 ((proj1 Htermenv) x)). }
      assert (Hlc21 : locally_closed_tm (close_term theta2 sigma2 t1)).
      { apply (close_term_lc 0 0 t1 (has_type_lc _ _ _ _ H1) theta2 sigma2).
        - intros X; exact (proj1 (proj2 (Htyenv X))).
        - intros x; apply value_lc; exact (proj2 ((proj1 Htermenv) x)). }
      assert (Hlc22 : locally_closed_tm (close_term theta2 sigma2 t2)).
      { apply (close_term_lc 0 0 t2 (has_type_lc _ _ _ _ H2) theta2 sigma2).
        - intros X; exact (proj1 (proj2 (Htyenv X))).
        - intros x; apply value_lc; exact (proj2 ((proj1 Htermenv) x)). }
      assert (Hpath1 : close_term theta1 sigma1 (tm_if c t1 t2) -->* va).
      { simpl; eapply multi_trans.
        - apply multi_if_left; [exact Hcpath|exact Hlc11|exact Hlc12].
        - eapply multi_step; [apply ST_IfFalse; assumption|exact Hapath]. }
      assert (Hpath2 : close_term theta2 sigma2 (tm_if c t1 t2) -->* vb).
      { simpl; eapply multi_trans.
        - apply multi_if_left; [exact Hdpath|exact Hlc21|exact Hlc22].
        - eapply multi_step; [apply ST_IfFalse; assumption|exact Hbpath]. }
      simpl; exists va, vb; repeat split; try assumption.
  - pose proof (IH1 theta1 theta2 rho sigma1 sigma2 Htyenv Htermenv) as Hleft.
    pose proof (IH2 theta1 theta2 rho sigma1 sigma2 Htyenv Htermenv) as Hright.
    assert (Hlc1 : locally_closed_tm (close_term theta1 sigma1 t1)).
    { apply (close_term_lc 0 0 t1 (has_type_lc _ _ _ _ H1) theta1 sigma1).
      - intros X; exact (proj1 (Htyenv X)).
      - intros x; apply value_lc; exact (proj1 ((proj1 Htermenv) x)). }
    assert (Hlc2 : locally_closed_tm (close_term theta1 sigma1 t2)).
    { apply (close_term_lc 0 0 t2 (has_type_lc _ _ _ _ H2) theta1 sigma1).
      - intros X; exact (proj1 (Htyenv X)).
      - intros x; apply value_lc; exact (proj1 ((proj1 Htermenv) x)). }
    assert (Hlc3 : locally_closed_tm (close_term theta2 sigma2 t1)).
    { apply (close_term_lc 0 0 t1 (has_type_lc _ _ _ _ H1) theta2 sigma2).
      - intros X; exact (proj1 (proj2 (Htyenv X))).
      - intros x; apply value_lc; exact (proj2 ((proj1 Htermenv) x)). }
    assert (Hlc4 : locally_closed_tm (close_term theta2 sigma2 t2)).
    { apply (close_term_lc 0 0 t2 (has_type_lc _ _ _ _ H2) theta2 sigma2).
      - intros X; exact (proj1 (proj2 (Htyenv X))).
      - intros x; apply value_lc; exact (proj2 ((proj1 Htermenv) x)). }
    eapply may_rel2_choice_left; eauto.
Qed.


Lemma ty_fv_open_rec_in : forall k U T X,
  In X (ty_fv T) -> In X (ty_fv (open_ty_rec k U T)).
Proof.
  intros k U T; revert k; induction T; intros k X Hin; simpl in *; try contradiction.
  - simpl; auto.
  - apply in_app_or in Hin as [Hin|Hin]; apply in_or_app;
      [left; eapply IHT1|right; eapply IHT2]; eauto.
  - eapply IHT; eauto.
Qed.

Lemma tm_fv_open_rec_in : forall k u t x,
  In x (tm_fv t) -> In x (tm_fv (open_tm_rec k u t)).
Proof.
  intros k u t; revert k; induction t as [i|y|A b IHb|a IHa b IHb|b IHb|a IHa A| | |c IHc a IHa b IHb|a IHa b IHb]; intros k x Hin; simpl in *; try contradiction.
  - destruct Hin as [->|[]]; simpl; auto.
  - apply IHb; exact Hin.
  - apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left; eapply IHa|right; eapply IHb]; eauto.
  - apply IHb; exact Hin.
  - apply IHa; exact Hin.
  - apply in_app_or in Hin as [Hin|Hin].
    + apply in_or_app; left; eapply IHc; exact Hin.
    + apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; right; apply in_or_app;
        [left; eapply IHa|right; eapply IHb]; eauto.
  - apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left; eapply IHa|right; eapply IHb]; eauto.
Qed.

Lemma tm_ty_fv_open_tm_ty_rec_in : forall k U t X,
  In X (tm_ty_fv t) -> In X (tm_ty_fv (open_tm_ty_rec k U t)).
Proof.
  intros k U t; revert k; induction t as [i|y|A b IHb|a IHa b IHb|b IHb|a IHa A| | |c IHc a IHa b IHb|a IHa b IHb]; intros k X Hin; simpl in *; try contradiction.
  - apply in_app_or in Hin as [Ha|Hb]; apply in_or_app; [left; eapply ty_fv_open_rec_in|right; eapply IHb]; eauto.
  - apply in_app_or in Hin as [Ha|Hb]; apply in_or_app; [left; eapply IHa|right; eapply IHb]; eauto.
  - eapply IHb; eauto.
  - apply in_app_or in Hin as [Ha|Hb]; apply in_or_app; [left; eapply IHa|right; eapply ty_fv_open_rec_in]; eauto.
  - apply in_app_or in Hin as [Ha|Hrest].
    + apply in_or_app; left; eapply IHc; exact Ha.
    + apply in_app_or in Hrest as [Hb|Hc]; apply in_or_app; right; apply in_or_app;
        [left; eapply IHa|right; eapply IHb]; eauto.
  - apply in_app_or in Hin as [Ha|Hb]; apply in_or_app; [left; eapply IHa|right; eapply IHb]; eauto.
Qed.

Lemma tm_ty_fv_open_tm_rec_in : forall k u t X,
  In X (tm_ty_fv t) -> In X (tm_ty_fv (open_tm_rec k u t)).
Proof.
  intros k u t; revert k; induction t as [i|y|A b IHb|a IHa b IHb|b IHb|a IHa A| | |c IHc a IHa b IHb|a IHa b IHb];
    intros k X HX; simpl in *; try contradiction.
  - apply in_app_or in HX as [HA|Hb]; apply in_or_app; [left; exact HA|right; eapply IHb; exact Hb].
  - apply in_app_or in HX as [Ha|Hb]; apply in_or_app; [left; eapply IHa|right; eapply IHb]; eauto.
  - eapply IHb; eauto.
  - apply in_app_or in HX as [Ha|Hb]; apply in_or_app; [left; eapply IHa|right; exact Hb]; eauto.
  - apply in_app_or in HX as [Ha|Hrest].
    + apply in_or_app; left; eapply IHc; exact Ha.
    + apply in_app_or in Hrest as [Hb|Hc]; apply in_or_app; right; apply in_or_app;
        [left; eapply IHa|right; eapply IHb]; eauto.
  - apply in_app_or in HX as [Ha|Hb]; apply in_or_app; [left; eapply IHa|right; eapply IHb]; eauto.
Qed.

Lemma tm_fv_open_tm_ty_rec_in : forall k U t x,
  In x (tm_fv t) -> In x (tm_fv (open_tm_ty_rec k U t)).
Proof.
  intros k U t; revert k; induction t as [i|y|A b IHb|a IHa b IHb|b IHb|a IHa A| | |c IHc a IHa b IHb|a IHa b IHb];
    intros k x Hx; simpl in *; try contradiction.
  - destruct Hx as [->|[]]; simpl; auto.
  - eapply IHb; eauto.
  - apply in_app_or in Hx as [Ha|Hb]; apply in_or_app; [left; eapply IHa|right; eapply IHb]; eauto.
  - eapply IHb; eauto.
  - eapply IHa; eauto.
  - apply in_app_or in Hx as [Ha|Hrest].
    + apply in_or_app; left; eapply IHc; exact Ha.
    + apply in_app_or in Hrest as [Hb|Hc]; apply in_or_app; right; apply in_or_app;
        [left; eapply IHa|right; eapply IHb]; eauto.
  - apply in_app_or in Hx as [Ha|Hb]; apply in_or_app; [left; eapply IHa|right; eapply IHb]; eauto.
Qed.

Lemma wf_ty_fv : forall Delta T, wf_ty Delta T -> forall X,
  In X (ty_fv T) -> In X Delta.
Proof.
  intros Delta T H; induction H as
    [Delta X HX|Delta A B HA IHA HB IHB|L Delta T Hbody IH|Delta]; intros Y HY.
  - simpl in HY; destruct HY as [->|[]]; exact HX.
  - simpl in HY; apply in_app_or in HY as [HY|HY]; [eapply IHA|eapply IHB]; eauto.
  - set (Z := fresh_atom (L ++ ty_fv T)).
    assert (HZL : ~ In Z L).
    { intro Hin; apply (fresh_atom_notin (L ++ ty_fv T)); unfold Z; apply in_or_app; left; exact Hin. }
    assert (HZT : ~ In Z (ty_fv T)).
    { intro Hin; apply (fresh_atom_notin (L ++ ty_fv T)); unfold Z; apply in_or_app; right; exact Hin. }
    specialize (IH Z HZL Y (ty_fv_open_rec_in 0 (Ty_FVar Z) T Y HY)).
    simpl in IH; destruct IH as [<-|IH]; [contradiction|exact IH].
  - contradiction.
Qed.

Lemma has_type_support : forall Delta Gamma t T, has_type Delta Gamma t T ->
  (forall x, In x (tm_fv t) -> exists A, lookup_context x Gamma = Some A) /\
  (forall X, In X (tm_ty_fv t) -> In X Delta).
Proof.
  intros Delta Gamma t T Hty; induction Hty as
    [Delta Gamma x T Hlook Hwf
    |L Delta Gamma A body B Hwf Hbody IHbody
    |Delta Gamma t1 t2 A B H1 IH1 H2 IH2
    |L Delta Gamma body T Hbody IHbody
    |Delta Gamma t T U Ht IHt HwfU
    |Delta Gamma|Delta Gamma
    |Delta Gamma c a b T Hc IHc Ha IHa Hb IHb
    |Delta Gamma a b T Ha IHa Hb IHb].
  - split.
    + intros y Hy; simpl in Hy; destruct Hy as [->|[]]; eauto.
    + intros X HX; contradiction.
  - split.
    + intros y Hy.
      set (x := fresh_atom (((L ++ tm_fv body) ++ tm_ty_fv body))).
      assert (HxL : ~ In x L).
      { intro Hin; apply (fresh_atom_notin ((L ++ tm_fv body) ++ tm_ty_fv body)); unfold x;
        apply in_or_app; left; apply in_or_app; left; exact Hin. }
      assert (Hxfv : ~ In x (tm_fv body)).
      { intro Hin; apply (fresh_atom_notin ((L ++ tm_fv body) ++ tm_ty_fv body)); unfold x;
        apply in_or_app; left; apply in_or_app; right; exact Hin. }
      specialize (Hbody x HxL).
      destruct (proj1 (IHbody x HxL) y (tm_fv_open_rec_in 0 (tm_fvar x) body y Hy)) as [S HS].
      exists S; rewrite lookup_update in HS.
      destruct (Nat.eqb y x) eqn:E; [apply Nat.eqb_eq in E; subst; exfalso; apply Hxfv; exact Hy|exact HS].
    + intros X HX; simpl in HX; apply in_app_or in HX as [HX|HX].
      * eapply wf_ty_fv; [exact Hwf|exact HX].
      * set (x := fresh_atom (((L ++ tm_fv body) ++ tm_ty_fv body))).
        assert (HxL : ~ In x L).
        { intro Hin; apply (fresh_atom_notin ((L ++ tm_fv body) ++ tm_ty_fv body)); unfold x;
          apply in_or_app; left; apply in_or_app; left; exact Hin. }
        eapply (proj2 (IHbody x HxL)); eapply tm_ty_fv_open_tm_rec_in; exact HX.
  - split.
    + intros x Hx; simpl in Hx; apply in_app_or in Hx as [Hx|Hx].
      * destruct (proj1 IH1 x Hx) as [S HS]; exists S; exact HS.
      * destruct (proj1 IH2 x Hx) as [S HS]; exists S; exact HS.
    + intros X HX; simpl in HX; apply in_app_or in HX as [HX|HX].
      * eapply (proj2 IH1); exact HX.
      * eapply (proj2 IH2); exact HX.
  - split.
    + intros x Hx.
      set (Z := fresh_atom (L ++ tm_ty_fv body)).
      assert (HZL : ~ In Z L).
      { intro Hin; apply (fresh_atom_notin (L ++ tm_ty_fv body)); unfold Z; apply in_or_app; left; exact Hin. }
      destruct (proj1 (IHbody Z HZL) x (tm_fv_open_tm_ty_rec_in 0 (Ty_FVar Z) body x Hx)) as [A HA].
      exists A; exact HA.
    + intros X HX.
      set (Z := fresh_atom (L ++ tm_ty_fv body)).
      assert (HZL : ~ In Z L).
      { intro Hin; apply (fresh_atom_notin (L ++ tm_ty_fv body)); unfold Z; apply in_or_app; left; exact Hin. }
      assert (HZbody : ~ In Z (tm_ty_fv body)).
      { intro Hin; apply (fresh_atom_notin (L ++ tm_ty_fv body)); unfold Z; apply in_or_app; right; exact Hin. }
      pose proof (proj2 (IHbody Z HZL) X (tm_ty_fv_open_tm_ty_rec_in 0 (Ty_FVar Z) body X HX)) as HinDelta.
      simpl in HinDelta; destruct HinDelta as [<-|HinDelta]; [contradiction|exact HinDelta].
  - split.
    + intros x Hx; eapply (proj1 IHt); exact Hx.
    + intros X HX; simpl in HX; apply in_app_or in HX as [HX|HX].
      * eapply (proj2 IHt); exact HX.
      * eapply wf_ty_fv; [exact HwfU|exact HX].
  - split; [intros x Hx; contradiction|intros X HX; contradiction].
  - split; [intros x Hx; contradiction|intros X HX; contradiction].
  - split.
    + intros x Hx; simpl in Hx; apply in_app_or in Hx as [Hx|Hrest].
      * destruct (proj1 IHc x Hx) as [S HS]; exists S; exact HS.
      * apply in_app_or in Hrest as [Hx|Hx].
        -- destruct (proj1 IHa x Hx) as [S HS]; exists S; exact HS.
        -- destruct (proj1 IHb x Hx) as [S HS]; exists S; exact HS.
    + intros X HX; simpl in HX; apply in_app_or in HX as [HX|Hrest].
      * eapply (proj2 IHc); exact HX.
      * apply in_app_or in Hrest as [HX|HX].
        -- eapply (proj2 IHa); exact HX.
        -- eapply (proj2 IHb); exact HX.
  - split.
    + intros x Hx; simpl in Hx; apply in_app_or in Hx as [Hx|Hx].
      * destruct (proj1 IHa x Hx) as [S HS]; exists S; exact HS.
      * destruct (proj1 IHb x Hx) as [S HS]; exists S; exact HS.
    + intros X HX; simpl in HX; apply in_app_or in HX as [HX|HX].
      * eapply (proj2 IHa); exact HX.
      * eapply (proj2 IHb); exact HX.
Qed.

Lemma close_ty_no_fv : forall theta T,
  (forall X, ~ In X (ty_fv T)) -> close_ty theta T = T.
Proof.
  intros theta T; induction T; intros H; simpl; try reflexivity.
  - exfalso; apply (H a); simpl; auto.
  - assert (HA : forall X, ~ In X (ty_fv T1)).
    { intros X HX; apply (H X); apply in_or_app; left; exact HX. }
    assert (HB : forall X, ~ In X (ty_fv T2)).
    { intros X HX; apply (H X); apply in_or_app; right; exact HX. }
    rewrite IHT1 by exact HA; rewrite IHT2 by exact HB; reflexivity.
  - rewrite IHT by exact H; reflexivity.
Qed.

Lemma not_in_app_all : forall (l m : list atom),
  (forall X, ~ In X (l ++ m)) ->
  (forall X, ~ In X l) /\ (forall X, ~ In X m).
Proof.
  intros l m H; split; intros X HX; apply (H X); apply in_or_app; auto.
Qed.

Lemma close_term_no_fv : forall theta sigma t,
  (forall x, ~ In x (tm_fv t)) ->
  (forall X, ~ In X (tm_ty_fv t)) -> close_term theta sigma t = t.
Proof.
  intros theta sigma t; induction t; intros Hx HX; simpl; try reflexivity.
  - exfalso; apply (Hx a); simpl; auto.
  - apply not_in_app_all in HX as [HT Hb].
    rewrite close_ty_no_fv by exact HT; rewrite IHt by assumption; reflexivity.
  - apply not_in_app_all in Hx as [Ha Hb].
    apply not_in_app_all in HX as [Hta Htb].
    rewrite IHt1 by assumption; rewrite IHt2 by assumption; reflexivity.
  - rewrite IHt by assumption; reflexivity.
  - apply not_in_app_all in HX as [Ha HT].
    rewrite IHt by assumption; rewrite close_ty_no_fv by exact HT; reflexivity.
  - apply not_in_app_all in Hx as [Ha Hbc]; apply not_in_app_all in Hbc as [Hb Hc].
    apply not_in_app_all in HX as [Hta Hrest]; apply not_in_app_all in Hrest as [Htb Htc].
    rewrite IHt1 by assumption.
    rewrite IHt2 by assumption.
    rewrite IHt3 by assumption; reflexivity.
  - apply not_in_app_all in Hx as [Ha Hb].
    apply not_in_app_all in HX as [Hta Htb].
    rewrite IHt1 by assumption; rewrite IHt2 by assumption; reflexivity.
Qed.

Theorem polymorphic_identity_theorem_for_free : forall t,
  has_type [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) ->
  forall U v,
    wf_ty [] U ->
    value v ->
    has_type [] empty v U ->
    tm_app (tm_tapp t U) v -->* v.
Proof.
  intros t Ht U v HwfU Hv Htv.
  set (theta := fun _ : atom => Ty_Bool).
  set (sigma := fun _ : atom => tm_true).
  set (rho := fun _ : atom => fun _ _ : tm => False).
  assert (Htypes : type_env_ok theta theta rho).
  { intros X; split; [constructor|]. split; [constructor|].
    unfold candidate_rel; intros a b H; contradiction. }
  assert (Hterms : term_env_ok rho empty sigma sigma).
  { split.
    - intros x; unfold sigma; split; apply v_true.
    - intros x T Hlookup; discriminate. }
  pose proof (fundamental [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Ht
    theta theta rho sigma sigma Htypes Hterms) as Hfund.
  assert (HsupportT := has_type_support [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Ht).
  assert (Htfv : forall x, ~ In x (tm_fv t)).
  { intros x Hx; destruct (proj1 HsupportT x Hx) as [A HA]; discriminate. }
  assert (Httyfv : forall X, ~ In X (tm_ty_fv t)).
  { intros X HX; exact (proj2 HsupportT X HX). }
  assert (Hcloset : close_term theta sigma t = t).
  { apply close_term_no_fv; assumption. }
  assert (HwfUfv : forall X, ~ In X (ty_fv U)).
  { intros X HX; exact (wf_ty_fv [] U HwfU X HX). }
  assert (HcloseU : close_ty theta U = U).
  { apply close_ty_no_fv; exact HwfUfv. }
  rewrite Hcloset in Hfund.
  simpl in Hfund.
  destruct Hfund as [f [g [Hft [Hgt [Hfv [Hgv Hfr]]]]]].
  simpl in Hfr.
  destruct Hfr as [Hfv' [Hgv' [bf [bg [Hfshape [Hgshape Hall]]]]]].
  set (Rv := fun a b => a = v /\ b = v).
  assert (HRv : candidate_rel Rv).
  { unfold candidate_rel, Rv; intros a b [-> ->]; auto. }
  pose proof (Hall U U Rv (wf_ty_lc [] U HwfU) (wf_ty_lc [] U HwfU) HRv) as Hbody.
  simpl in Hbody.
  destruct Hbody as [q1 [q2 [Hq1 [Hq2 [Hvq1 [Hvq2 Hqrel]]]]]].
  simpl in Hqrel.
  destruct Hqrel as [F1 [B1 [F2 [B2 [Hqshape1 [Hqshape2 [Hqv1 [Hqv2 Happly]]]]]]]].
  assert (Hrelv : value_rel2 rho [Rv] (Ty_BVar 0) v v).
  { simpl; unfold Rv; auto. }
  pose proof (Happly v v Hrelv) as Happ.
  destruct Happ as [r1 [r2 [Happ1 [Happ2 [Hvr1 [Hvr2 Hrrel]]]]]].
  simpl in Hrrel.
  destruct Hrrel as [Hr1 Hr2].
  assert (Htypepath : tm_tapp t U -->* open_tm_ty bf U).
  { inversion Hfshape; subst f.
    eapply multi_trans.
    - apply multi_tapp; [exact Hft|exact (wf_ty_lc [] U HwfU)].
    - apply multi_type_beta; [apply value_lc; exact Hfv|exact (wf_ty_lc [] U HwfU)]. }
  assert (Hbodypath : open_tm_ty bf U -->* q1).
  { exact Hq1. }
  assert (HappPath : tm_app (tm_tapp t U) v -->* r1).
  { eapply multi_trans.
    - apply multi_app_left; [exact Htypepath|apply value_lc; exact Hv].
    - eapply multi_trans.
      + apply multi_app_left; [exact Hbodypath|apply value_lc; exact Hv].
      + exact Happ1. }
  rewrite Hr1 in HappPath; exact HappPath.
Qed.

End SystemFParametricityIfNondeterminismHardTask.
