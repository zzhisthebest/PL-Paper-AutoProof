Require Import syntax_ott.

Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Export LibTactics.

Require Import Lia.

Require Export equiRec.

Local Set Implicit Arguments.

(* Opening and substitution for the three kinds of binders. *)

Local Lemma typ_degree_open_inv : forall a k d x,
  k <= d ->
  degree_typ_wrt_typ d (open_typ_wrt_typ_rec k (t_var_f x) a) ->
  degree_typ_wrt_typ (S d) a.
Proof.
  induction a; intros k d x Hkd H; simpl in H;
    try match goal with
    | |- _ _ (t_var_b ?i) =>
        destruct (lt_eq_lt_dec i k) as [[Hlt | Heq] | Hgt]
    end;
    inversion H; subst; constructor; try lia;
    first [eapply IHa; [| eassumption]; lia | eauto].
Qed.

Local Lemma typ_lc_degree : forall a, lc_typ a -> degree_typ_wrt_typ 0 a.
Proof.
  intros a H; induction H; try solve [constructor; assumption | constructor].
  constructor.
  pick fresh x.
  eapply typ_degree_open_inv with (k := 0) (x := x); eauto.
Qed.

Local Lemma typ_open_vacuous : forall d a,
  degree_typ_wrt_typ d a ->
  forall k u, d <= k -> open_typ_wrt_typ_rec k u a = a.
Proof.
  intros d a H; induction H; intros k u Hk; simpl;
    try solve [reflexivity | f_equal; eauto with arith].
  destruct (lt_eq_lt_dec n2 k) as [[Hlt | Heq] | Hgt]; try reflexivity; lia.
Qed.

Local Lemma typ_subst_open_rec : forall a x u k v,
  lc_typ u ->
  typsubst_typ u x (open_typ_wrt_typ_rec k v a) =
  open_typ_wrt_typ_rec k (typsubst_typ u x v) (typsubst_typ u x a).
Proof.
  induction a; intros x u k v Hu; simpl; try (f_equal; auto).
  - destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt]; reflexivity.
  - destruct (eq_var _ _); simpl; auto.
    symmetry. eapply typ_open_vacuous; [eapply typ_lc_degree; exact Hu | lia].
Qed.

Local Lemma typ_subst_open_var : forall a x y u,
  x <> y -> lc_typ u ->
  typsubst_typ u x (open_typ_wrt_typ a (t_var_f y)) =
  open_typ_wrt_typ (typsubst_typ u x a) (t_var_f y).
Proof.
  intros a x y u Hxy Hu. unfold open_typ_wrt_typ.
  rewrite typ_subst_open_rec by assumption.
  simpl. destruct (eq_var y x); congruence.
Qed.

Local Lemma typ_open_intro_rec : forall a k x u,
  x \notin typefv_typ a ->
  typsubst_typ u x (open_typ_wrt_typ_rec k (t_var_f x) a) =
  open_typ_wrt_typ_rec k u a.
Proof.
  induction a; intros k x u Hfresh; simpl in *; try (f_equal; auto 7 using notin_union).
  - destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt]; simpl; auto.
    lazymatch goal with |- context [if ?d then _ else _] => destruct d end; congruence.
  - destruct (eq_var _ _) as [Heq | Hneq]; [subst; exfalso; fsetdec | reflexivity].
Qed.

Local Lemma castop_degree_open_inv : forall a k d x,
  k <= d ->
  degree_castop_wrt_castop d (open_castop_wrt_castop_rec k (c_var_f x) a) ->
  degree_castop_wrt_castop (S d) a.
Proof.
  induction a; intros k d x Hkd H; simpl in H;
    try match goal with
    | |- _ _ (c_var_b ?i) =>
        destruct (lt_eq_lt_dec i k) as [[Hlt | Heq] | Hgt]
    end;
    inversion H; subst; constructor; try lia;
    first [eapply IHa; [| eassumption]; lia | eauto].
Qed.

Local Lemma castop_lc_degree : forall a, lc_castop a -> degree_castop_wrt_castop 0 a.
Proof.
  intros a H; induction H; try solve [constructor; assumption | constructor].
  constructor.
  pick fresh x.
  eapply castop_degree_open_inv with (k := 0) (x := x); eauto.
Qed.

Local Lemma castop_open_vacuous : forall d a,
  degree_castop_wrt_castop d a ->
  forall k u, d <= k -> open_castop_wrt_castop_rec k u a = a.
Proof.
  intros d a H; induction H; intros k u Hk; simpl;
    try solve [reflexivity | f_equal; eauto with arith].
  destruct (lt_eq_lt_dec n2 k) as [[Hlt | Heq] | Hgt]; try reflexivity; lia.
Qed.

Local Lemma castop_subst_open_rec : forall a x u k v,
  lc_castop u ->
  castsubst_castop u x (open_castop_wrt_castop_rec k v a) =
  open_castop_wrt_castop_rec k (castsubst_castop u x v) (castsubst_castop u x a).
Proof.
  induction a; intros x u k v Hu; simpl; try (f_equal; auto).
  - destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt]; reflexivity.
  - destruct (eq_var _ _); simpl; auto.
    symmetry. eapply castop_open_vacuous; [eapply castop_lc_degree; exact Hu | lia].
Qed.

Local Lemma castop_subst_open_var : forall a x y u,
  x <> y -> lc_castop u ->
  castsubst_castop u x (open_castop_wrt_castop a (c_var_f y)) =
  open_castop_wrt_castop (castsubst_castop u x a) (c_var_f y).
Proof.
  intros a x y u Hxy Hu. unfold open_castop_wrt_castop.
  rewrite castop_subst_open_rec by assumption.
  simpl. destruct (eq_var y x); congruence.
Qed.

Local Lemma castop_open_intro_rec : forall a k x u,
  x \notin castfv_castop a ->
  castsubst_castop u x (open_castop_wrt_castop_rec k (c_var_f x) a) =
  open_castop_wrt_castop_rec k u a.
Proof.
  induction a; intros k x u Hfresh; simpl in *; try (f_equal; auto 7 using notin_union).
  - destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt]; simpl; auto.
    lazymatch goal with |- context [if ?d then _ else _] => destruct d end; congruence.
  - destruct (eq_var _ _) as [Heq | Hneq]; [subst; exfalso; fsetdec | reflexivity].
Qed.

Local Lemma exp_degree_open_inv : forall a k d x,
  k <= d ->
  degree_exp_wrt_exp d (open_exp_wrt_exp_rec k (e_var_f x) a) ->
  degree_exp_wrt_exp (S d) a.
Proof.
  induction a; intros k d x Hkd H; simpl in H;
    try match goal with
    | |- _ _ (e_var_b ?i) =>
        destruct (lt_eq_lt_dec i k) as [[Hlt | Heq] | Hgt]
    end;
    inversion H; subst; constructor; try lia;
    first [eapply IHa; [| eassumption]; lia | eauto].
Qed.

Local Lemma exp_lc_degree : forall a, lc_exp a -> degree_exp_wrt_exp 0 a.
Proof.
  intros a H; induction H; try solve [constructor; assumption | constructor].
  constructor.
  pick fresh x.
  eapply exp_degree_open_inv with (k := 0) (x := x); eauto.
Qed.

Local Lemma exp_open_vacuous : forall d a,
  degree_exp_wrt_exp d a ->
  forall k u, d <= k -> open_exp_wrt_exp_rec k u a = a.
Proof.
  intros d a H; induction H; intros k u Hk; simpl;
    try solve [reflexivity | f_equal; eauto with arith].
  destruct (lt_eq_lt_dec n2 k) as [[Hlt | Heq] | Hgt]; try reflexivity; lia.
Qed.

Local Lemma exp_subst_open_rec : forall a x u k v,
  lc_exp u ->
  subst_exp u x (open_exp_wrt_exp_rec k v a) =
  open_exp_wrt_exp_rec k (subst_exp u x v) (subst_exp u x a).
Proof.
  induction a; intros x u k v Hu; simpl; try (f_equal; auto).
  - destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt]; reflexivity.
  - destruct (eq_var _ _); simpl; auto.
    symmetry. eapply exp_open_vacuous; [eapply exp_lc_degree; exact Hu | lia].
Qed.

Local Lemma exp_subst_open_var : forall a x y u,
  x <> y -> lc_exp u ->
  subst_exp u x (open_exp_wrt_exp a (e_var_f y)) =
  open_exp_wrt_exp (subst_exp u x a) (e_var_f y).
Proof.
  intros a x y u Hxy Hu. unfold open_exp_wrt_exp.
  rewrite exp_subst_open_rec by assumption.
  simpl. destruct (eq_var y x); congruence.
Qed.

Local Lemma exp_open_intro_rec : forall a k x u,
  x \notin termfv_exp a ->
  subst_exp u x (open_exp_wrt_exp_rec k (e_var_f x) a) =
  open_exp_wrt_exp_rec k u a.
Proof.
  induction a; intros k x u Hfresh; simpl in *; try (f_equal; auto 7 using notin_union).
  - destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt]; simpl; auto.
    lazymatch goal with |- context [if ?d then _ else _] => destruct d end; congruence.
  - destruct (eq_var _ _) as [Heq | Hneq]; [subst; exfalso; fsetdec | reflexivity].
Qed.

(* A single fresh opening checks the bound indices of a binder.
   Annotation closure is checked separately for casts and expressions. *)
Local Fixpoint cast_annotations c : Prop :=
  match c with
  | c_unfold A | c_fold A => lc_typ A
  | c_arrow c1 c2 | c_seq c1 c2 => cast_annotations c1 /\ cast_annotations c2
  | c_fixc c => cast_annotations c
  | _ => True
  end.

Local Fixpoint exp_annotations e : Prop :=
  match e with
  | e_abs A body => lc_typ A /\ exp_annotations body
  | e_app e1 e2 => exp_annotations e1 /\ exp_annotations e2
  | e_cast c e => lc_castop c /\ exp_annotations e
  | _ => True
  end.

Local Lemma typ_degree_open : forall a k d x,
  k <= d ->
  degree_typ_wrt_typ (S d) a ->
  degree_typ_wrt_typ d (open_typ_wrt_typ_rec k (t_var_f x) a).
Proof.
  induction a; intros k d x Hkd H; simpl; inversion H; subst.
    all: try match goal with
    | |- context [lt_eq_lt_dec ?i ?j] =>
        destruct (lt_eq_lt_dec i j) as [[Hlt | Heq] | Hgt]
    end;
    constructor; try lia; eauto with arith.
Qed.

Local Lemma typ_size_open_var : forall a k x,
  size_typ (open_typ_wrt_typ_rec k (t_var_f x) a) = size_typ a.
Proof.
  induction a; intros k x; simpl;
    try match goal with
    | |- context [lt_eq_lt_dec ?i ?j] => destruct (lt_eq_lt_dec i j) as [[? | ?] | ?]
    end;
    simpl; f_equal; auto.
Qed.

Local Lemma typ_degree_lc : forall a, degree_typ_wrt_typ 0 a -> lc_typ a.
Proof.
  enough (forall n a, size_typ a < n -> degree_typ_wrt_typ 0 a -> lc_typ a)
    by (intros; eapply (H (S (size_typ a))); eauto).
  induction n as [|n IH]; intros a Hsize Hdegree; [lia |].
  destruct a; simpl in *; inversion Hdegree; subst; try lia;
    try solve [constructor; intuition (try (eapply IH; [lia | eassumption]))].
  apply lc_t_mu; try tauto.
  intro x. unfold open_typ_wrt_typ.
  eapply IH.
  - rewrite typ_size_open_var. lia.
  - eapply typ_degree_open with (d := 0); eauto.
Qed.

Local Lemma castop_degree_open : forall a k d x,
  k <= d ->
  degree_castop_wrt_castop (S d) a ->
  degree_castop_wrt_castop d (open_castop_wrt_castop_rec k (c_var_f x) a).
Proof.
  induction a; intros k d x Hkd H; simpl; inversion H; subst.
    all: try match goal with
    | |- context [lt_eq_lt_dec ?i ?j] =>
        destruct (lt_eq_lt_dec i j) as [[Hlt | Heq] | Hgt]
    end;
    constructor; try lia; eauto with arith.
Qed.

Local Lemma castop_size_open_var : forall a k x,
  size_castop (open_castop_wrt_castop_rec k (c_var_f x) a) = size_castop a.
Proof.
  induction a; intros k x; simpl;
    try match goal with
    | |- context [lt_eq_lt_dec ?i ?j] => destruct (lt_eq_lt_dec i j) as [[? | ?] | ?]
    end;
    simpl; f_equal; auto.
Qed.

Local Lemma castop_annotations_open_var : forall a k x,
  cast_annotations (open_castop_wrt_castop_rec k (c_var_f x) a) = cast_annotations a.
Proof.
  induction a; intros k x; simpl;
    try match goal with
    | |- context [lt_eq_lt_dec ?i ?j] => destruct (lt_eq_lt_dec i j) as [[? | ?] | ?]
    end;
    simpl; try rewrite IHa; try rewrite IHa1, IHa2; reflexivity.
Qed.

Local Lemma castop_degree_lc : forall a, degree_castop_wrt_castop 0 a -> cast_annotations a -> lc_castop a.
Proof.
  enough (forall n a, size_castop a < n -> degree_castop_wrt_castop 0 a -> cast_annotations a -> lc_castop a)
    by (intros; eapply (H (S (size_castop a))); eauto).
  induction n as [|n IH]; intros a Hsize Hdegree Hann; [lia |].
  destruct a; simpl in *; inversion Hdegree; subst; try lia;
    try solve [constructor; intuition (try (eapply IH; [lia | eassumption | assumption]))].
  apply lc_c_fixc; try tauto.
  intro x. unfold open_castop_wrt_castop.
  eapply IH.
  - rewrite castop_size_open_var. lia.
  - eapply castop_degree_open with (d := 0); eauto.
  - rewrite castop_annotations_open_var. tauto.
Qed.

Local Lemma exp_degree_open : forall a k d x,
  k <= d ->
  degree_exp_wrt_exp (S d) a ->
  degree_exp_wrt_exp d (open_exp_wrt_exp_rec k (e_var_f x) a).
Proof.
  induction a; intros k d x Hkd H; simpl; inversion H; subst.
    all: try match goal with
    | |- context [lt_eq_lt_dec ?i ?j] =>
        destruct (lt_eq_lt_dec i j) as [[Hlt | Heq] | Hgt]
    end;
    constructor; try lia; eauto with arith.
Qed.

Local Lemma exp_size_open_var : forall a k x,
  size_exp (open_exp_wrt_exp_rec k (e_var_f x) a) = size_exp a.
Proof.
  induction a; intros k x; simpl;
    try match goal with
    | |- context [lt_eq_lt_dec ?i ?j] => destruct (lt_eq_lt_dec i j) as [[? | ?] | ?]
    end;
    simpl; f_equal; auto.
Qed.

Local Lemma exp_annotations_open_var : forall a k x,
  exp_annotations (open_exp_wrt_exp_rec k (e_var_f x) a) = exp_annotations a.
Proof.
  induction a; intros k x; simpl;
    try match goal with
    | |- context [lt_eq_lt_dec ?i ?j] => destruct (lt_eq_lt_dec i j) as [[? | ?] | ?]
    end;
    simpl; try rewrite IHa; try rewrite IHa1, IHa2; reflexivity.
Qed.

Local Lemma exp_degree_lc : forall a, degree_exp_wrt_exp 0 a -> exp_annotations a -> lc_exp a.
Proof.
  enough (forall n a, size_exp a < n -> degree_exp_wrt_exp 0 a -> exp_annotations a -> lc_exp a)
    by (intros; eapply (H (S (size_exp a))); eauto).
  induction n as [|n IH]; intros a Hsize Hdegree Hann; [lia |].
  destruct a; simpl in *; inversion Hdegree; subst; try lia;
    try solve [constructor; intuition (try (eapply IH; [lia | eassumption | assumption]))].
  apply lc_e_abs; try tauto.
  intro x. unfold open_exp_wrt_exp.
  eapply IH.
  - rewrite exp_size_open_var. lia.
  - eapply exp_degree_open with (d := 0); eauto.
  - rewrite exp_annotations_open_var. tauto.
Qed.

Local Lemma wft_lc : forall D A, WFT D A -> lc_typ A.
Proof.
  intros D A H. apply typ_degree_lc.
  induction H; try solve [constructor; auto].
  constructor. pick fresh X.
  eapply typ_degree_open_inv with (k := 0) (x := X); eauto.
Qed.

Local Lemma cast_uniq : forall D E A B c, TypCast D E A B c -> uniq E.
Proof.
  intros D E A B c H; induction H; auto.
  pick fresh x.
  specialize (H0 x ltac:(fsetdec)).
  inversion H0; assumption.
Qed.

Local Lemma cast_lc : forall D E A B c, TypCast D E A B c -> lc_castop c.
Proof.
  intros D E A B c H.
  apply castop_degree_lc.
  - induction H; try solve [constructor; auto].
    constructor. pick fresh x.
    eapply castop_degree_open_inv with (k := 0) (x := x); [lia |].
    simpl. constructor; [apply H0 | apply H2]; fsetdec.
  - induction H; simpl; eauto using wft_lc.
    pick fresh x.
    specialize (H0 x ltac:(fsetdec)). specialize (H2 x ltac:(fsetdec)).
    unfold open_castop_wrt_castop in *.
    rewrite castop_annotations_open_var in H0, H2. auto.
Qed.

Local Lemma typing_env : forall G e A, Typing G e A -> WFTmE G.
Proof.
  intros G e A H; induction H; auto.
  pick fresh x.
  specialize (H0 x ltac:(fsetdec)).
  inversion H0; assumption.
Qed.

Local Lemma typing_lc : forall G e A, Typing G e A -> lc_exp e.
Proof.
  intros G e A H. apply exp_degree_lc.
  - induction H; try solve [constructor; auto | assumption].
    constructor. pick fresh x.
    eapply exp_degree_open_inv with (k := 0) (x := x); eauto.
  - induction H; simpl; eauto using cast_lc.
    pick fresh x.
    assert (Hfresh : x \notin L) by fsetdec.
    pose proof (typing_env (H x Hfresh)) as Henv. inversion Henv; subst.
    specialize (H0 x Hfresh). unfold open_exp_wrt_exp in H0.
    rewrite exp_annotations_open_var in H0. eauto using wft_lc.
Qed.

(* Environment transport for term substitution and cast unrolling. *)
Local Lemma typing_weaken : forall G e A, Typing G e A ->
  forall F, WFTmE F -> (forall x T, binds x T G -> binds x T F) ->
  Typing F e A.
Proof.
  intros G e A H; induction H; intros F HF Hinc;
    eauto using Typing_int, Typing_var, Typing_app, Typing_cast, Typing_sub.
  eapply Typing_abs with (L := L \u dom F).
  intros x Hx. assert (HxL : x \notin L) by fsetdec.
  pose proof (typing_env (H x HxL)) as Henv.
  inversion Henv; subst.
  apply H0; auto.
  - apply WFTmE_cons; auto; fsetdec.
  - intros y T Hy. apply binds_cons_1 in Hy. destruct Hy as [[-> ->] | Hy].
    + apply binds_cons_2; reflexivity.
    + apply binds_cons. auto.
Qed.

Local Lemma typing_subst : forall G e A, Typing G e A ->
  forall x v F, lc_exp v -> WFTmE F ->
  (forall y T, binds y T G -> Typing F (subst_exp v x (e_var_f y)) T) ->
  Typing F (subst_exp v x e) A.
Proof.
  intros G e A H; induction H; intros z v F Hv HF Hmap;
    simpl; eauto using Typing_int, Typing_app, Typing_cast, Typing_sub.
  eapply Typing_abs with (L := L \u dom F \u {{z}}).
  intros x Hx. assert (HxL : x \notin L) by fsetdec.
  pose proof (typing_env (H x HxL)) as Henv. inversion Henv; subst.
  assert (Hext : WFTmE ((x,A1)::F)) by (apply WFTmE_cons; auto; fsetdec).
  rewrite <- exp_subst_open_var by (assumption || fsetdec).
  apply H0; auto.
  intros y T Hy. apply binds_cons_1 in Hy. destruct Hy as [[-> ->] | Hy].
  - simpl. destruct (@eq_dec termvar _ x z); [fsetdec |].
    apply Typing_var; [exact Hext | apply binds_cons_2; reflexivity].
  - eapply typing_weaken; [eapply Hmap; exact Hy | exact Hext |].
    intros. now apply binds_cons.
Qed.

Local Lemma typing_beta : forall L A B body v,
  (forall x, x \notin L -> Typing ((x,A)::nil) (open_exp_wrt_exp body (e_var_f x)) B) ->
  Typing nil v A -> Typing nil (open_exp_wrt_exp body v) B.
Proof.
  intros L A B body v Hbody Hv.
  pick fresh x for (L \u termfv_exp body).
  specialize (Hbody x ltac:(fsetdec)).
  unfold open_exp_wrt_exp in *.
  rewrite <- exp_open_intro_rec with (x := x) by fsetdec.
  eapply typing_subst; eauto using typing_lc, WFTmE_empty.
  intros y T [[= -> ->] | []].
  simpl. lazymatch goal with |- context [if ?d then _ else _] => destruct d end;
    congruence.
Qed.

Local Lemma cast_weaken : forall D E A B c, TypCast D E A B c ->
  forall F, uniq F -> (forall p, In p E -> In p F) ->
  TypCast D F A B c.
Proof.
  intros D E A B c H; induction H; intros F HF Hinc;
    eauto using TCast_id, TCast_arrow, TCast_unfold, TCast_fold, TCast_seq, TCast_var.
  eapply TCast_fix with (L := L \u dom F); intros x Hx;
    [eapply H0 | eapply H2]; try fsetdec;
    [apply uniq_cons; [assumption | fsetdec] | intros p Hp; simpl in *; intuition
    |apply uniq_cons; [assumption | fsetdec] | intros p Hp; simpl in *; intuition].
Qed.

Local Lemma cast_subst : forall D E A B c, TypCast D E A B c ->
  forall x r F, lc_castop r -> uniq F ->
  (forall y S T, In (y,(S,T)) E -> WFT D S -> WFT D T ->
     TypCast D F S T (castsubst_castop r x (c_var_f y))) ->
  TypCast D F A B (castsubst_castop r x c).
Proof.
  intros D E A B c H; induction H; intros z r F Hr HF Hmap;
    simpl; eauto using TCast_id, TCast_arrow, TCast_unfold, TCast_fold, TCast_seq.
  eapply TCast_fix with (L := L \u dom F \u {{z}}); intros x Hx;
    assert (Hext : uniq ((x,(t_arrow A1 B1,t_arrow A2 B2))::F))
      by (apply uniq_cons; auto; fsetdec);
    rewrite <- castop_subst_open_var by (assumption || fsetdec);
    [eapply H0 | eapply H2]; try fsetdec; auto.
  all: intros y S T Hin HS HT; destruct Hin as [Heq | Hin].
  all: try solve
    [inversion Heq; subst y S T; simpl; destruct (@eq_dec castvar _ x z);
     [fsetdec | apply TCast_var; [exact HS | exact HT | exact Hext | left; reflexivity]]].
  all: eapply cast_weaken; [exact (Hmap _ _ _ Hin HS HT) | exact Hext |].
  all: intros p Hp; right; assumption.
Qed.

Local Lemma rev_cast_open : forall c k r,
  rev_cast (open_castop_wrt_castop_rec k r c) =
  open_castop_wrt_castop_rec k (rev_cast r) (rev_cast c).
Proof.
  induction c; intros k r; simpl; try (f_equal; auto).
  destruct (lt_eq_lt_dec n k) as [[? | ?] | ?]; reflexivity.
Qed.

Local Lemma cast_reverse : forall D E A B c, TypCast D E A B c ->
  forall F, uniq F ->
  (forall x S T, In (x,(S,T)) E -> In (x,(T,S)) F) ->
  TypCast D F B A (rev_cast c).
Proof.
  intros D E A B c H; induction H; intros F HF Hrev; simpl;
    eauto using TCast_id, TCast_arrow, TCast_unfold, TCast_fold, TCast_seq, TCast_var.
  eapply TCast_fix with (L := L \u dom F); intros x Hx;
    unfold open_castop_wrt_castop in *;
    change (c_var_f x) with (rev_cast (c_var_f x));
    rewrite <- rev_cast_open;
    [eapply H0 | eapply H2]; try fsetdec.
  all: try solve [apply uniq_cons; auto; fsetdec].
  all: intros y S T Hin; destruct Hin as [Heq | Hin];
    [inversion Heq; subst; left; reflexivity | right; auto].
Qed.

(* Amber subtyping under a fresh extension and simultaneous instantiation. *)
Local Lemma amber_dom_pair : forall E x y,
  In (x, y) E -> x `in` domA E /\ y `in` domA E.
Proof.
  induction E as [|[a b] E IH]; intros x y H; simpl in *; [contradiction |].
  destruct H as [Heq | Hin].
  - inversion Heq; subst. fsetdec.
  - specialize (IH _ _ Hin). fsetdec.
Qed.

Local Lemma amber_dom_incl : forall E F,
  (forall p, In p E -> In p F) -> domA E [<=] domA F.
Proof.
  induction E as [|[a b] E IH]; intros F H; simpl.
  - fsetdec.
  - pose proof (@amber_dom_pair F a b (H (a,b) (or_introl eq_refl))) as Hab.
    assert (domA E [<=] domA F) by (apply IH; auto with datatypes).
    fsetdec.
Qed.

Local Lemma amber_wft_var : forall E x,
  AmberWF E -> x `in` domA E -> AmberWFT E (t_var_f x).
Proof.
  assert (Hex : forall E z, z `in` domA E ->
             exists a b, In (a,b) E /\ (z = a \/ z = b)).
  { induction E as [|[a b] E IH]; intros z Hz; simpl in Hz.
    - fsetdec.
    - destruct (z == a) as [-> | Hza].
      + exists a, b. simpl; auto.
      + destruct (z == b) as [-> | Hzb].
        * exists a, b. simpl; auto.
        * destruct (IH z ltac:(fsetdec)) as (p & q & Hin & Heq).
          exists p, q. simpl; auto. }
  intros E x Hwf Hdom.
  destruct (Hex E x Hdom) as (a & b & Hin & [-> | ->]).
  - eapply AWFT_varl; eauto.
  - eapply AWFT_varr; eauto.
Qed.

Local Lemma amber_wft_rec : forall L E A,
  (forall x, x \notin L -> forall y, y \notin L \u {{x}} ->
     AmberWFT ((x,y)::E) (open_typ_wrt_typ A (t_var_f x))) ->
  AmberWFT E (t_mu A).
Proof.
  intros L E A H. pick fresh z for L.
  exact (@AWFT_rec L E A z H).
Qed.

Local Lemma amber_wft_weaken : forall E A, AmberWFT E A ->
  forall F, AmberWF F -> domA E [<=] domA F -> AmberWFT F A.
Proof.
  intros E A H; induction H; intros F HF Hdom;
    try solve [constructor; auto].
  - eapply amber_wft_var; [exact HF |].
    apply Hdom. edestruct amber_dom_pair; eauto.
  - eapply amber_wft_var; [exact HF |].
    apply Hdom. edestruct amber_dom_pair; eauto.
  - eapply amber_wft_rec with (L := L \u domA F).
    intros x Hx y Hy.
    apply (H0 x ltac:(fsetdec) y ltac:(fsetdec)).
    + apply AWF_cons; auto; fsetdec.
    + simpl. fsetdec.
Qed.

Local Lemma amber_sub_weaken : forall E A B, AmberSubtyping E A B ->
  forall F, AmberWF F -> (forall p, In p E -> In p F) ->
  AmberSubtyping F A B.
Proof.
  intros E A B H; induction H; intros F HF Hin;
    try solve [eauto using ASub_nat, ASub_top, ASub_arrow, ASub_var, ASub_self,
                         amber_wft_weaken, amber_dom_incl].
  eapply ASub_rec with (L := L \u domA F).
  intros y Hy x Hx.
  apply (H0 y ltac:(fsetdec) x ltac:(fsetdec)).
  - apply AWF_cons; auto; fsetdec.
  - intros p Hp. simpl in *. intuition.
Qed.

Local Lemma amber_sub_env : forall E A B, AmberSubtyping E A B -> AmberWF E.
Proof.
  intros E A B H; induction H; auto.
  pick fresh y for L. pick fresh x for (L \u {{y}}).
  pose proof (H0 y ltac:(fsetdec) x ltac:(fsetdec)) as Hwf.
  inversion Hwf; assumption.
Qed.

Local Lemma amber_sub_wft : forall E A B, AmberSubtyping E A B ->
  AmberWFT E A /\ AmberWFT E B.
Proof.
  intros E A B H; induction H.
  - split; constructor; assumption.
  - split; auto. constructor; assumption.
  - intuition.
    all: apply AWFT_arrow; assumption.
  - split; [eapply AWFT_varl | eapply AWFT_varr]; eauto.
  - split; eapply amber_wft_rec with (L := L); intros x Hx y Hy.
    + destruct (H0 y ltac:(fsetdec) x ltac:(fsetdec)); assumption.
    + assert (Hxy : y \notin L \u {{x}}) by fsetdec.
      assert (Hyx : x \notin L \u {{y}}) by fsetdec.
      destruct (H0 x Hx y Hxy) as [_ HB].
      pose proof (amber_sub_env (H x Hx y Hxy)) as Hwf.
      inversion Hwf; subst.
      eapply amber_wft_weaken; [exact HB | apply AWF_cons; auto; fsetdec |].
      simpl. fsetdec.
  - auto.
Qed.

Local Lemma amber_wft_lc : forall E A, AmberWFT E A -> lc_typ A.
Proof.
  intros E A H. apply typ_degree_lc.
  induction H; try solve [constructor; auto].
  constructor. pick fresh x for L. pick fresh y for (L \u {{x}}).
  eapply typ_degree_open_inv with (k := 0) (x := x); [lia |].
  apply (H0 x ltac:(fsetdec) y ltac:(fsetdec)).
Qed.

Local Lemma typ_subst_fresh : forall A x U,
  x \notin typefv_typ A -> typsubst_typ U x A = A.
Proof.
  induction A; intros x U H; simpl in *; try reflexivity.
  - destruct (eq_var _ _); subst; [exfalso; fsetdec | reflexivity].
  - rewrite IHA1, IHA2 by fsetdec. reflexivity.
  - rewrite IHA by fsetdec. reflexivity.
Qed.

Local Definition amber_instance x y S T A :=
  typsubst_typ T y (typsubst_typ S x A).

Section AmberInstantiation.
  Variables (x y : typevar) (S T : typ).
  Hypotheses (HS : lc_typ S) (HT : lc_typ T).
  Local Notation inst := (amber_instance x y S T).

  Local Lemma amber_instance_var : forall z,
    z <> x -> z <> y -> inst (t_var_f z) = t_var_f z.
  Proof.
    intros z Hx Hy. unfold amber_instance; simpl.
    destruct (eq_var z x); [congruence |].
    simpl. destruct (eq_var z y); congruence.
  Qed.

  Local Lemma amber_instance_open : forall A z,
    z <> x -> z <> y ->
    inst (open_typ_wrt_typ A (t_var_f z)) =
    open_typ_wrt_typ (inst A) (t_var_f z).
  Proof.
    intros A z Hx Hy. unfold amber_instance.
    rewrite !typ_subst_open_var by congruence. reflexivity.
  Qed.

  Local Definition amber_wft_instance E F :=
    forall z, z `in` domA E -> AmberWFT F (inst (t_var_f z)).

  Local Lemma amber_wft_instance_extend : forall E F a b,
    a <> x -> a <> y -> b <> x -> b <> y ->
    AmberWF ((a,b)::F) -> amber_wft_instance E F ->
    amber_wft_instance ((a,b)::E) ((a,b)::F).
  Proof.
    unfold amber_wft_instance.
    intros E F a b Hax Hay Hbx Hby HF Hmap z Hz. simpl in Hz.
    destruct (z == a) as [-> | Hza].
    - rewrite amber_instance_var by assumption.
      eapply AWFT_varl; [exact HF | left; reflexivity].
    - destruct (z == b) as [-> | Hzb].
      + rewrite amber_instance_var by assumption.
        eapply AWFT_varr; [exact HF | left; reflexivity].
      + eapply amber_wft_weaken; [apply Hmap | exact HF |]; simpl; fsetdec.
  Qed.

  Local Lemma amber_wft_instantiate : forall E A, AmberWFT E A ->
    forall F, AmberWF F -> amber_wft_instance E F -> AmberWFT F (inst A).
  Proof.
    intros E A H; induction H; intros F HF Hmap;
      cbn [amber_instance typsubst_typ] in *;
      try solve [constructor; auto].
    - apply Hmap. edestruct amber_dom_pair; eauto.
    - apply Hmap. edestruct amber_dom_pair; eauto.
    - eapply amber_wft_rec with (L := L \u domA F \u {{x}} \u {{y}}).
      intros a Ha b Hb. fold (inst A).
      rewrite <- amber_instance_open by fsetdec.
      assert (Hext : AmberWF ((a,b)::F)) by (apply AWF_cons; auto; fsetdec).
      apply (H0 a ltac:(fsetdec) b ltac:(fsetdec)); [exact Hext |].
      eapply amber_wft_instance_extend; eauto; fsetdec.
  Qed.

  Local Lemma amber_sub_instantiate : forall E A B, AmberSubtyping E A B ->
    forall F, AmberWF F -> amber_wft_instance E F ->
    (forall a b, In (a,b) E -> AmberSubtyping F (inst (t_var_f a)) (inst (t_var_f b))) ->
    AmberSubtyping F (inst A) (inst B).
  Proof.
    intros E A B H; induction H; intros F HF Hmap Hsub.
    - constructor; assumption.
    - apply ASub_top; eauto using amber_wft_instantiate.
    - apply ASub_arrow; auto.
    - auto.
    - eapply ASub_rec with (L := L \u domA F \u {{x}} \u {{y}}).
      intros b Hb a Ha. change (AmberSubtyping ((a,b)::F)
          (open_typ_wrt_typ (inst A) (t_var_f a))
          (open_typ_wrt_typ (inst B) (t_var_f b))).
      rewrite <- !amber_instance_open by fsetdec.
      assert (Hext : AmberWF ((a,b)::F)) by (apply AWF_cons; auto; fsetdec).
      apply (H0 b ltac:(fsetdec) a ltac:(fsetdec)); [exact Hext | |].
      + eapply amber_wft_instance_extend; eauto; fsetdec.
      + intros p q Hin. destruct Hin as [Heq | Hin].
        * inversion Heq; subst. rewrite !amber_instance_var by fsetdec.
          apply ASub_var; auto. left; reflexivity.
        * eapply amber_sub_weaken; eauto.
          intros r Hr. right; assumption.
    - apply ASub_self; [exact HF |].
      change (AmberWFT F (inst (t_mu A))).
      eapply amber_wft_instantiate; eassumption.
  Qed.
End AmberInstantiation.

(* Instantiate the fresh pair with the two recursive types. The original
   recursive subtyping derivation discharges the instantiated variable rule. *)
Local Lemma amber_unfold_rec : forall L A B,
  (forall y, y \notin L -> forall x, x \notin L \u {{y}} ->
     AmberSubtyping ((x,y)::nil) (open_typ_wrt_typ A (t_var_f x))
                                (open_typ_wrt_typ B (t_var_f y))) ->
  AmberSubtyping nil (unfold_mu A) (unfold_mu B).
Proof.
  intros L A B Hbody.
  assert (Hsub : AmberSubtyping nil (t_mu A) (t_mu B))
    by (eapply ASub_rec; exact Hbody).
  destruct (amber_sub_wft Hsub) as [HA HB].
  pose proof (amber_wft_lc HA) as HAlc.
  pose proof (amber_wft_lc HB) as HBlc.
  pick fresh y for (L \u typefv_typ A \u typefv_typ B).
  pick fresh x for (L \u typefv_typ A \u typefv_typ B \u {{y}}).
  pose proof (Hbody y ltac:(fsetdec) x ltac:(fsetdec)) as Hbody'.
  assert (Hxy : x <> y) by fsetdec.
  assert (Hleft : amber_instance x y (t_mu A) (t_mu B)
                   (open_typ_wrt_typ A (t_var_f x)) = unfold_mu A).
  { unfold amber_instance, open_typ_wrt_typ.
    rewrite typ_open_intro_rec by fsetdec.
    rewrite typ_subst_open_rec by assumption.
    rewrite !typ_subst_fresh by (simpl; fsetdec). reflexivity. }
  assert (Hright : amber_instance x y (t_mu A) (t_mu B)
                    (open_typ_wrt_typ B (t_var_f y)) = unfold_mu B).
  { unfold amber_instance. rewrite (@typ_subst_open_var B x y (t_mu A) Hxy HAlc).
    assert (Hfresh : typsubst_typ (t_mu A) x B = B) by (apply typ_subst_fresh; fsetdec).
    rewrite Hfresh.
    unfold open_typ_wrt_typ. apply typ_open_intro_rec. fsetdec. }
  assert (Hvarx : amber_instance x y (t_mu A) (t_mu B) (t_var_f x) = t_mu A).
  { unfold amber_instance; simpl. destruct (@eq_dec typevar _ x x); [|congruence].
    apply typ_subst_fresh. simpl; fsetdec. }
  assert (Hvary : amber_instance x y (t_mu A) (t_mu B) (t_var_f y) = t_mu B).
  { unfold amber_instance; simpl. destruct (@eq_dec typevar _ y x); [congruence |].
    simpl. destruct (@eq_dec typevar _ y y); congruence. }
  rewrite <- Hleft, <- Hright.
  eapply amber_sub_instantiate; eauto using AWF_nil.
  - unfold amber_wft_instance. intros z Hz. simpl in Hz.
    assert (z = x \/ z = y) by fsetdec.
    destruct H as [-> | ->]; rewrite ?Hvarx, ?Hvary; assumption.
  - intros p q Hin. destruct Hin as [Heq | []].
    inversion Heq; subst. now rewrite Hvarx, Hvary.
Qed.

(* Consecutive subsumption rules contribute a chain of Amber derivations. *)
Inductive SubChain : typ -> typ -> Prop :=
| sub_chain_refl : forall A, SubChain A A
| sub_chain_step : forall A B C,
    SubChain A B -> AmberSubtyping nil B C -> SubChain A C.

Local Lemma sub_chain_trans : forall A B C,
  SubChain A B -> SubChain B C -> SubChain A C.
Proof.
  intros A B C HAB HBC. induction HBC; eauto using sub_chain_step.
Qed.

Local Lemma typing_sub_chain : forall G e A B,
  Typing G e A -> SubChain A B -> Typing G e B.
Proof.
  intros G e A B HT HS. induction HS; eauto using Typing_sub.
Qed.

Local Lemma sub_chain_arrow : forall S T, SubChain S T ->
  forall A B, T = t_arrow A B ->
    exists C D, S = t_arrow C D /\ SubChain A C /\ SubChain D B.
Proof.
  intros S T H; induction H as [S | S U T HSU IH HUT]; intros A B Heq; subst.
  - exists A, B. repeat split; constructor.
  - inversion HUT as [| | E UDom UCod TDom TCod Hdom Hcod | | |]; subst.
    destruct (IH UDom UCod eq_refl) as (C & D & -> & HDom & HCod).
    exists C, D. split; [reflexivity | split].
    + eapply sub_chain_trans; [| exact HDom].
      eapply sub_chain_step; [apply sub_chain_refl | exact Hdom].
    + eapply sub_chain_step; [exact HCod | exact Hcod].
Qed.

Local Lemma sub_chain_mu : forall S T, SubChain S T ->
  forall B, T = t_mu B ->
    exists A, S = t_mu A /\ SubChain (unfold_mu A) (unfold_mu B).
Proof.
  intros S T H; induction H as [S | S U T HSU IH HUT]; intros B Heq; subst.
  - exists B. split; constructor.
  - inversion HUT as [| | | | L E UBody TBody Hbody | E Body Hwf Hwell]; subst.
    + destruct (IH UBody eq_refl) as (SourceBody & -> & Hunfold).
      exists SourceBody. split; [reflexivity |].
      eapply sub_chain_step; [exact Hunfold |].
      eapply amber_unfold_rec; exact Hbody.
    + apply IH. reflexivity.
Qed.

(* Recover the typing premises underneath outer uses of subsumption. *)
Local Lemma typing_app_inv : forall G e1 e2 T,
  Typing G (e_app e1 e2) T ->
  exists A B, Typing G e1 (t_arrow A B) /\ Typing G e2 A /\ SubChain B T.
Proof.
  intros G e1 e2 T HT. remember (e_app e1 e2) as e eqn:He.
  induction HT; inversion He; subst.
  - eauto using sub_chain_refl.
  - destruct (IHHT eq_refl) as (S & T & H1 & H2 & Hsub).
    exists S, T. repeat split; eauto using sub_chain_step.
Qed.

Local Lemma typing_abs_inv : forall G A body T, Typing G (e_abs A body) T ->
  exists L B, (forall x, x \notin L -> Typing ((x,A)::G)
                                  (open_exp_wrt_exp body (e_var_f x)) B) /\
              SubChain (t_arrow A B) T.
Proof.
  intros G A body T HT. remember (e_abs A body) as e eqn:He.
  induction HT; inversion He; subst.
  - eauto using sub_chain_refl.
  - destruct (IHHT eq_refl) as (L & T & Hbody & Hsub).
    exists L, T. eauto using sub_chain_step.
Qed.

Local Lemma typing_cast_inv : forall G c e T, Typing G (e_cast c e) T ->
  exists A B, Typing G e A /\ TypCast nil nil A B c /\ SubChain B T.
Proof.
  intros G c e T HT. remember (e_cast c e) as term eqn:He.
  induction HT; inversion He; subst.
  - eauto using sub_chain_refl.
  - destruct (IHHT eq_refl) as (S & T & Hty & Hc & Hsub).
    exists S, T. repeat split; eauto using sub_chain_step.
Qed.

Local Lemma typing_lit_inv : forall G i T, Typing G (e_lit i) T -> SubChain t_int T.
Proof.
  intros G i T HT. remember (e_lit i) as e eqn:He.
  induction HT; inversion He; subst; eauto using sub_chain_refl, sub_chain_step.
Qed.

(* Open a fixcast component with the original, well-typed fixcast. *)
Local Lemma cast_open_body : forall D E A B L S T body r,
  TypCast D E S T r ->
  (forall x, x \notin L -> TypCast D ((x,(S,T))::E) A B
                                (open_castop_wrt_castop body (c_var_f x))) ->
  TypCast D E A B (open_castop_wrt_castop body r).
Proof.
  intros D E A B L S T body r Hr Hbody.
  pick fresh x for (L \u castfv_castop body).
  specialize (Hbody x ltac:(fsetdec)).
  unfold open_castop_wrt_castop in *.
  rewrite <- castop_open_intro_rec with (x := x) by fsetdec.
  eapply cast_subst; eauto using cast_lc, cast_uniq.
  intros y U V [Heq | Hin] HU HV.
  - inversion Heq; subst. simpl.
    lazymatch goal with |- context [if ?d then _ else _] => destruct d end; congruence.
  - simpl. destruct (@eq_dec castvar _ y x) as [-> | Hneq].
    + exfalso. pose proof (cast_uniq Hbody) as Huniq. inversion Huniq; subst.
      match goal with
      | Hfresh : x \notin dom E |- _ => apply Hfresh; eapply binds_In; exact Hin
      end.
    + eauto using TCast_var, cast_uniq.
Qed.

Local Lemma cast_unroll : forall D E A B c,
  TypCast D E A B (c_fixc c) ->
  TypCast D E A B (open_castop_wrt_castop c (c_fixc c)).
Proof.
  intros D E A B c H. inversion H; subst.
  unfold open_castop_wrt_castop at 1. simpl.
  apply TCast_arrow; eapply cast_open_body; eassumption.
Qed.

Local Unset Implicit Arguments.

Theorem preservation: forall e T,
  Typing nil e T -> forall e',
  Reduction e e' -> Typing nil e' T.
Proof.
  intros e T Hty e' Hstep. revert T Hty.
  induction Hstep; intros T Hty.
  - destruct (typing_app_inv Hty) as (D & R & Hfun & Harg & Hout).
    destruct (typing_abs_inv Hfun) as (L & B & Hbody & Hsub).
    destruct (sub_chain_arrow Hsub eq_refl) as (A' & B' & [= <- <-] & HD & HB).
    apply (typing_sub_chain (B := T) (A := R)); [| exact Hout].
    eapply typing_sub_chain; [| exact HB].
    eapply typing_beta; [exact Hbody | eauto using typing_sub_chain].
  - destruct (typing_app_inv Hty) as (D & R & Hfun & Harg & Hout).
    eapply typing_sub_chain; [eapply Typing_app; eauto | exact Hout].
  - destruct (typing_app_inv Hty) as (D & R & Hfun & Harg & Hout).
    eapply typing_sub_chain; [eapply Typing_app; eauto | exact Hout].
  - destruct (typing_app_inv Hty) as (D & R & Hfun & Harg & Hout).
    destruct (typing_cast_inv Hfun) as (S & U & Hinner & Hcast & Hsub).
    inversion Hcast; subst.
    destruct (sub_chain_arrow Hsub eq_refl) as (D' & R' & [= <- <-] & HD & HR).
    eapply typing_sub_chain; [|exact Hout].
    eapply typing_sub_chain; [|exact HR].
    eapply Typing_cast; [|eassumption].
    eapply Typing_app; [exact Hinner |].
    eapply Typing_cast.
    + eapply typing_sub_chain; eassumption.
    + eapply cast_reverse; [eassumption | constructor | contradiction].
  - destruct (typing_cast_inv Hty) as (S & U & Hinner & Hcast & Hout).
    inversion Hcast; subst.
    eapply typing_sub_chain; [|exact Hout].
    eapply Typing_cast; [eapply Typing_cast |]; eassumption.
  - destruct (typing_cast_inv Hty) as (S & U & Hinner & Hcast & Hout).
    eapply typing_sub_chain; [eapply Typing_cast; eauto | exact Hout].
  - destruct (typing_cast_inv Hty) as (S & U & Hfold & Hunfold & Hout).
    inversion Hunfold; subst.
    destruct (typing_cast_inv Hfold) as (S & U & Hinner & Hcast & Hsub).
    inversion Hcast; subst.
    destruct (sub_chain_mu Hsub eq_refl) as (C & [= <-] & Hinside).
    eapply typing_sub_chain; [|exact Hout].
    eapply typing_sub_chain; eassumption.
  - destruct (typing_cast_inv Hty) as (S & U & Hinner & Hcast & Hout).
    inversion Hcast; subst. eauto using typing_sub_chain.
  - destruct (typing_cast_inv Hty) as (S & U & Hinner & Hcast & Hout).
    eapply typing_sub_chain; [eapply Typing_cast; eauto using cast_unroll | exact Hout].
Qed.

Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Export LibTactics.

Require Export subtyping.

Local Lemma value_app_steps : forall v w A B,
  value v -> value w -> Typing nil v (t_arrow A B) ->
  exists e', Reduction (e_app v w) e'.
Proof.
  intros v w A B Hv Hw HT. destruct Hv.
  - destruct (sub_chain_arrow (typing_lit_inv HT) eq_refl) as (? & ? & Heq & _).
    discriminate.
  - eexists. apply Red_beta; eassumption.
  - destruct (typing_cast_inv HT) as (S & U & Hinner & HC & HS).
    inversion HC; subst.
    destruct (sub_chain_arrow HS eq_refl) as (? & ? & Heq & _). discriminate.
  - eexists. apply Red_cast_arr; eassumption.
Qed.

Local Lemma value_unfold_steps : forall v A,
  value v -> lc_typ (t_mu A) -> Typing nil v (t_mu A) ->
  exists e', Reduction (e_cast (c_unfold (t_mu A)) v) e'.
Proof.
  intros v A Hv HA HT. destruct Hv.
  - destruct (sub_chain_mu (typing_lit_inv HT) eq_refl) as (? & Heq & _).
    discriminate.
  - destruct (typing_abs_inv HT) as (L & B & Hbody & HS).
    destruct (sub_chain_mu HS eq_refl) as (? & Heq & _). discriminate.
  - eexists. apply Red_castelim; eassumption.
  - destruct (typing_cast_inv HT) as (S & U & Hinner & HC & HS).
    inversion HC; subst.
    destruct (sub_chain_mu HS eq_refl) as (? & Heq & _). discriminate.
Qed.

Local Lemma cast_value_progress : forall A B c v,
  TypCast nil nil A B c -> Typing nil v A -> value v ->
  value (e_cast c v) \/ exists e', Reduction (e_cast c v) e'.
Proof.
  intros A B c v HC HT Hv. pose proof (cast_lc HC) as Hlc.
  inversion HC; subst.
  - right. eexists. apply Red_castid; assumption.
  - left. inversion Hlc; subst. apply V_arrow; assumption.
  - right. eapply value_unfold_steps; eauto using wft_lc.
  - left. apply V_fold; eauto using wft_lc.
  - right. inversion Hlc; subst. eexists. apply Red_cast_seq; assumption.
  - contradiction.
  - right. eexists. apply Red_castfix; assumption.
Qed.

Theorem progress: forall e t, Typing nil e t -> (value e) \/ exists e', Reduction e e'.
Proof.
  intros e t Hty. remember nil as G eqn:HG.
  induction Hty; subst.
  - left. apply V_lit.
  - inversion H.
    unfold binds in *. contradiction.
  - left. assert (Habs : lc_exp (e_abs A1 e)).
    { eapply typing_lc. eapply Typing_abs; eassumption. }
    inversion Habs; subst. apply V_abs; assumption.
  - specialize (IHHty1 eq_refl). specialize (IHHty2 eq_refl).
    right. destruct IHHty1 as [Hv1 | [e1' Hstep1]].
    + destruct IHHty2 as [Hv2 | [e2' Hstep2]].
      * eapply value_app_steps; eassumption.
      * eexists. eapply Red_appr; eassumption.
    + eexists. eapply Red_appl; eauto using typing_lc.
  - destruct (IHHty eq_refl) as [Hv | [e' Hstep]].
    + eapply cast_value_progress; eassumption.
    + right. eexists. eapply Red_cast; eauto using cast_lc.
  - auto.
Qed.
