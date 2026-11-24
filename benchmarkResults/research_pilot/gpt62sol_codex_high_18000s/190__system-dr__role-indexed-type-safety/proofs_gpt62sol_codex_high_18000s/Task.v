Require Import Language.

Fixpoint ctx_nom (G : context) := match G with
  | nil => nil
  | (x, Tm _) :: G' => (x, Nom) :: ctx_nom G'
  | (x, Co _) :: G' => ctx_nom G'
  end.

Definition Good (G : context) (D : available_props):=
  forall c1 A B1 T1 R,
    binds c1 (Co (Eq A B1 T1 R)) G
    -> c1 `in` D
    -> exists C, Par (ctx_nom G) A C R /\ Par (ctx_nom G) B1 C R.

Definition irrelevant G D (a : tm) :=
  (forall x A, binds x (Tm A) G -> x `notin` fv_tm_tm_tm a) /\ Good G D.

(* The singleton signature and the unfolding rule for Fix. *)

Local Hint Constructors SubRole : core.

Lemma dr_sig : forall F s, binds F s toplevel ->
  F = Fix /\ s = Ax FixPat FixDef FixTy Nom [Nom].
Proof.
  intros F s H. unfold toplevel in H.
  simpl in H. destruct H as [H | H]; [inversion H; auto | contradiction].
Qed.

Ltac dr_signature :=
  repeat match goal with
  | H : binds _ _ toplevel |- _ =>
      apply dr_sig in H; destruct H as [? H]; subst; inversion H; clear H; subst
  end.

Lemma dr_no_apps_path : forall R a F aps, ~ AppsPath R a F aps.
Proof.
  intros R a F aps H; induction H; dr_signature; auto.
Qed.

Lemma dr_no_sat : forall F aps, ~ SatApp F aps.
Proof. intros F aps H; inversion H; dr_signature; auto. Qed.

Definition dr_prefix := a_App (a_Fam Fix) (Rho Irrel) a_Bullet.
Definition dr_unfold f := a_App f (Rho Rel) (a_App dr_prefix (Rho Rel) f).

Lemma dr_subst_fixdef : forall f,
  tm_subst_tm_tm f FixVar2 FixDef = dr_unfold f.
Proof.
  intros f. unfold FixDef, dr_unfold, dr_prefix.
  change (a_App (if eq_var FixVar2 FixVar2 then f else a_Var_f FixVar2) (Rho Rel)
    (a_App (a_App (a_Fam Fix) (Rho Irrel) a_Bullet) (Rho Rel)
      (if eq_var FixVar2 FixVar2 then f else a_Var_f FixVar2)) = a_App f (Rho Rel) (a_App (a_App (a_Fam Fix) (Rho Irrel) a_Bullet) (Rho Rel) f)).
  destruct (eq_var FixVar2 FixVar2); [reflexivity | contradiction].
Qed.

Lemma dr_subst_unfold_var : forall f y,
  tm_subst_tm_tm f y (dr_unfold (a_Var_f y)) = dr_unfold f.
Proof.
  intros f y. unfold dr_unfold, dr_prefix. simpl.
  destruct (eq_var y y); [reflexivity | contradiction].
Qed.

Lemma dr_match_rename : forall D p b D', Rename FixPat FixDef p b D D' ->
  forall a z, MatchSubst a p b z ->
  exists i f, a = a_App (a_App (a_Fam Fix) (Rho Irrel) i) (Role Nom) f /\
              z = dr_unfold f /\ lc_tm i /\ lc_tm f.
Proof.
  intros D p b D' H a z M.
  unfold FixPat in H.
  inversion H; subst; clear H.
  match goal with H : Rename _ _ _ _ _ _ |- _ => inversion H; subst; clear H end.
  match goal with H : Rename _ _ _ _ _ _ |- _ => inversion H; subst; clear H end.
  inversion M; subst; clear M.
  match goal with H : MatchSubst _ _ _ _ |- _ => inversion H; subst; clear H end.
  match goal with H : MatchSubst _ _ _ _ |- _ => inversion H; subst; clear H end.
  do 2 eexists. repeat split; eauto.
  now rewrite dr_subst_fixdef, dr_subst_unfold_var.
Qed.

Lemma dr_rename_match : forall D i f,
  lc_tm i -> lc_tm f ->
  exists p b D', Rename FixPat FixDef p b D D' /\
    MatchSubst (a_App (a_App (a_Fam Fix) (Rho Irrel) i) (Role Nom) f) p b (dr_unfold f).
Proof.
  intros D i f Hi Hf. pick fresh y for (D \u {{FixVar2}}).
  exists (a_App dr_prefix (Role Nom) (a_Var_f y)),
    (tm_subst_tm_tm (a_Var_f y) FixVar2 FixDef), ({{y}} \u AtomSetImpl.empty).
  split.
  - unfold FixPat, dr_prefix. constructor.
    + constructor. constructor. unfold FixDef; repeat constructor.
    + fsetdec.
  - assert (M : MatchSubst
      (a_App (a_App (a_Fam Fix) (Rho Irrel) i) (Role Nom) f)
      (a_App dr_prefix (Role Nom) (a_Var_f y))
      (tm_subst_tm_tm (a_Var_f y) FixVar2 FixDef)
      (tm_subst_tm_tm f y (tm_subst_tm_tm (a_Var_f y) FixVar2 FixDef))).
    { unfold dr_prefix. apply MatchSubst_AppRelR; auto.
      apply MatchSubst_AppIrrel; auto. constructor.
      rewrite dr_subst_fixdef. unfold dr_unfold, dr_prefix; repeat constructor. }
    rewrite dr_subst_fixdef, dr_subst_unfold_var in M. now rewrite dr_subst_fixdef.
Qed.

Lemma dr_beta_fix : forall i f R,
  lc_tm i -> lc_tm f ->
  Beta (a_App (a_App (a_Fam Fix) (Rho Irrel) i) (Role Nom) f) (dr_unfold f) R.
Proof.
  intros i f R Hi Hf.
  destruct (dr_rename_match
    (fv_tm_tm_tm (a_App (a_App (a_Fam Fix) (Rho Irrel) i) (Role Nom) f) `union`
     fv_tm_tm_tm FixPat) i f Hi Hf) as (p & b & D & Hr & Hm).
  eapply Beta_Axiom with (F := Fix) (A := FixTy) (R1 := Nom) (Rs := [Nom]); eauto.
  unfold toplevel; simpl; auto.
Qed.

Lemma dr_beta_inv : forall a b R, Beta a b R ->
  (exists rho v arg, a = a_App (a_UAbs rho v) (Rho rho) arg /\
                     b = open_tm_wrt_tm v arg) \/
  (exists v, a = a_CApp (a_UCAbs v) g_Triv /\ b = open_tm_wrt_co v g_Triv) \/
  (exists i f, a = a_App (a_App (a_Fam Fix) (Rho Irrel) i) (Role Nom) f /\
               b = dr_unfold f) \/
  (exists a0 F aps b1 b2, a = a_Pattern Nom a0 F aps b1 b2 /\ b = b2).
Proof.
  intros a b R H; inversion H; subst; dr_signature; eauto 8.
  - right; right; left.
    match goal with H : Rename _ _ _ _ _ _, M : MatchSubst _ _ _ _ |- _ =>
      destruct (dr_match_rename _ _ _ _ H _ _ M) as (i & f & -> & -> & _); eauto
    end.
  - exfalso; eapply dr_no_sat; eauto.
  - do 3 right. do 5 eexists. auto.
Qed.

(* Opening, substitution, and local closure for erased terms. *)

Scheme dr_tm_ind := Induction for tm Sort Prop
with dr_constraint_ind := Induction for constraint Sort Prop
with dr_brs_ind := Induction for brs Sort Prop
with dr_co_ind := Induction for co Sort Prop.
Combined Scheme dr_syntax_ind from dr_tm_ind, dr_constraint_ind, dr_brs_ind, dr_co_ind.

Lemma dr_open_fresh_all :
  (forall a k u x, x `notin` fv_tm_tm_tm a ->
    tm_subst_tm_tm u x (open_tm_wrt_tm_rec k (a_Var_f x) a) =
    open_tm_wrt_tm_rec k u a) /\
  (forall a k u x, x `notin` fv_tm_tm_constraint a ->
    tm_subst_tm_constraint u x (open_constraint_wrt_tm_rec k (a_Var_f x) a) =
    open_constraint_wrt_tm_rec k u a) /\
  (forall a k u x, x `notin` fv_tm_tm_brs a ->
    tm_subst_tm_brs u x (open_brs_wrt_tm_rec k (a_Var_f x) a) =
    open_brs_wrt_tm_rec k u a) /\
  (forall a k u x, x `notin` fv_tm_tm_co a ->
    tm_subst_tm_co u x (open_co_wrt_tm_rec k (a_Var_f x) a) =
    open_co_wrt_tm_rec k u a).
Proof.
  apply dr_syntax_ind; intros; simpl in *; try reflexivity;
    try solve [f_equal; eauto using AtomSetImpl.union_2, AtomSetImpl.union_3 with sets].
  - destruct (lt_eq_lt_dec n k) as [[|]|]; simpl; auto.
    match goal with |- context [if ?d then _ else _] => destruct d; congruence end.
  - match goal with |- context [if ?d then _ else _] => destruct d; [subst; fsetdec | reflexivity] end.
  all: f_equal; try solve [match goal with
      | H : forall (_ : nat) (_ : tm) (_ : atom), _ |- _ => apply H; fsetdec
      end].
Qed.

From Stdlib Require Import Lia.

Definition dr_open_fresh := proj1 dr_open_fresh_all.

Fixpoint dr_scoped (n : nat) (a : tm) : Prop :=
  match a with
  | a_Star | a_Var_f _ | a_Bullet | a_Fam _ => True
  | a_Var_b k => k < n
  | a_UAbs _ b => dr_scoped (S n) b
  | a_App a _ b => dr_scoped n a /\ dr_scoped n b
  | a_Pi _ a b => dr_scoped n a /\ dr_scoped (S n) b
  | a_UCAbs a => dr_scoped n a
  | a_CApp a g => dr_scoped n a /\ g = g_Triv
  | a_CPi (Eq a b A _) B => dr_scoped n a /\ dr_scoped n b /\ dr_scoped n A /\ dr_scoped n B
  | a_Pattern Nom a _ _ b1 b2 => dr_scoped n a /\ dr_scoped n b1 /\ dr_scoped n b2
  | _ => False
  end.

Lemma dr_scoped_mono : forall a n m, dr_scoped n a -> n <= m -> dr_scoped m a.
Proof.
  fix IH 1; intros a; destruct a; intros; simpl in *; try tauto; try lia;
    try destruct phi; try destruct R; simpl in *; intuition eauto with arith.
Qed.

Lemma dr_scoped_open : forall a k x,
    dr_scoped k (open_tm_wrt_tm_rec k (a_Var_f x) a) <-> dr_scoped (S k) a.
Proof.
  fix IH 1; intros a; destruct a; intros; simpl in *; try tauto;
    try destruct phi; try destruct R; try destruct g; simpl;
    try rewrite !IH; try tauto; try (split; intuition discriminate).
  destruct (lt_eq_lt_dec n k) as [[|]|]; simpl; lia.
Qed.

Lemma dr_scoped_co_open : forall a n k c,
    dr_scoped n (open_tm_wrt_co_rec k (g_Var_f c) a) <-> dr_scoped n a.
Proof.
  fix IH 1; intros a; destruct a; intros; simpl in *; try tauto;
    try destruct phi; try destruct R; try destruct g; simpl;
    try rewrite !IH; try tauto; try (split; intuition discriminate).
  destruct (lt_eq_lt_dec n0 k) as [[|]|]; simpl; split; intuition discriminate.
Qed.

Lemma dr_scoped_open_id : forall a n u,
  dr_scoped n a -> open_tm_wrt_tm_rec n u a = a.
Proof.
  fix IH 1; intros a; destruct a; intros; simpl in *; try tauto;
    try destruct phi; try destruct R; try destruct g; simpl in *; try tauto;
    try (repeat f_equal; intuition eauto; fail); try (exfalso; intuition discriminate).
  destruct (lt_eq_lt_dec n n0) as [[|]|]; try reflexivity; lia.
Qed.

Lemma dr_scoped_co_id : forall a n k g,
  dr_scoped n a -> open_tm_wrt_co_rec k g a = a.
Proof.
  fix IH 1; intros a; destruct a; intros; simpl in *; try tauto;
    try destruct phi; try destruct R; try destruct g; simpl in *; try tauto;
    try solve [intuition discriminate]; repeat f_equal; intuition eauto.
Qed.

Lemma dr_role_scoped : forall W a R, roleing W a R -> dr_scoped 0 a.
Proof.
  intros W a R H; induction H; simpl; auto 8.
  - pick fresh x for L.
    apply (proj1 (dr_scoped_open a 0 x)); unfold open_tm_wrt_tm, open_tm_wrt_co in *; eauto.
  - pick fresh x for L.
    split; auto. apply (proj1 (dr_scoped_open B 0 x)); unfold open_tm_wrt_tm, open_tm_wrt_co in *; eauto.
  - pick fresh c for L.
    repeat split; auto. apply (proj1 (dr_scoped_co_open B 0 0 c)); unfold open_tm_wrt_tm, open_tm_wrt_co in *; eauto.
  - pick fresh c for L.
    apply (proj1 (dr_scoped_co_open b 0 0 c)); unfold open_tm_wrt_tm, open_tm_wrt_co in *; eauto.
Qed.

Fixpoint dr_size (a : tm) : nat :=
  match a with
  | a_UAbs _ a | a_UCAbs a | a_CApp a _ => S (dr_size a)
  | a_App a _ b | a_Pi _ a b => S (dr_size a + dr_size b)
  | a_CPi (Eq a b A _) B => S (dr_size a + dr_size b + dr_size A + dr_size B)
  | a_Pattern _ a _ _ b1 b2 => S (dr_size a + dr_size b1 + dr_size b2)
  | _ => 1
  end.

Lemma dr_size_open : forall a k x,
  dr_size (open_tm_wrt_tm_rec k (a_Var_f x) a) = dr_size a.
Proof.
  fix IH 1; intros a k x; destruct a; simpl; try reflexivity;
    try destruct phi; simpl; try now rewrite !IH.
  destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
Qed.

Lemma dr_scoped_lc : forall a, dr_scoped 0 a -> lc_tm a.
Proof.
  assert (H : forall n a, dr_size a < n -> dr_scoped 0 a -> lc_tm a).
  { induction n; intros a Hs Ha; [lia |].
    destruct a; simpl in *; try contradiction; try lia;
      try destruct phi; try destruct R; simpl in *; try contradiction;
      try solve [constructor; intuition (eapply IHn; [lia | assumption])].
    - constructor. intros x. unfold open_tm_wrt_tm.
      eapply IHn; [rewrite dr_size_open; lia|now apply dr_scoped_open].
    - destruct Ha as [H1 H2]. constructor.
      + eapply IHn; [lia|exact H1].
      + intros x. unfold open_tm_wrt_tm.
        eapply IHn; [rewrite dr_size_open; lia|now apply dr_scoped_open].
    - constructor. intros c. unfold open_tm_wrt_co.
      rewrite (dr_scoped_co_id _ _ _ _ Ha).
      eapply IHn; [lia|exact Ha].
    - destruct Ha as [Ha ->]. constructor; [eapply IHn; [lia|exact Ha] | constructor].
    - destruct Ha as (H1 & H2 & H3 & H4).
      constructor; [constructor; eapply IHn; [lia|exact H1 |lia|exact H2|lia|exact H3]|].
      intros c. unfold open_tm_wrt_co.
      rewrite (dr_scoped_co_id _ _ _ _ H4).
      eapply IHn; [lia|exact H4].
    - destruct Ha as (H1 & H2 & H3 & H4).
      constructor; [constructor; eapply IHn; [lia|exact H1 |lia|exact H2|lia|exact H3]|].
      intros c. unfold open_tm_wrt_co.
      rewrite (dr_scoped_co_id _ _ _ _ H4).
      eapply IHn; [lia|exact H4]. }
  intros; eapply H; eauto.
Qed.

Lemma dr_par_fam : forall W F a R, Par W (a_Fam F) a R -> a = a_Fam F.
Proof. intros; inversion H; subst; dr_signature; reflexivity. Qed.

Lemma dr_par_fix_prefix : forall W i a R,
  Par W (a_App (a_Fam Fix) (Rho Irrel) i) a R ->
  exists j, a = a_App (a_Fam Fix) (Rho Irrel) j /\ Par W i j Nom.
Proof.
  intros W i a R H. inversion H; subst; dr_signature.
  - exists i; split; [reflexivity|]. inversion H0; subst; now constructor.
  - match goal with P : Par _ (a_Fam _) _ _ |- _ =>
      apply dr_par_fam in P; discriminate
    end.
  - match goal with P : Par _ (a_Fam _) _ _ |- _ =>
      apply dr_par_fam in P; subst; eauto
    end.
  - match goal with Hr : Rename _ _ _ _ _ _, M : MatchSubst _ _ _ _ |- _ =>
      destruct (dr_match_rename _ _ _ _ Hr _ _ M) as (j & f & E & _); discriminate
    end.
Qed.

Lemma dr_subrole_cases : forall R S, SubRole R S -> R = Nom \/ S = Rep.
Proof. intros R S H; induction H; destruct_all role; intuition congruence. Qed.

Lemma dr_role_uniq : forall W a R, roleing W a R -> uniq W.
Proof.
  intros W a R H; induction H; eauto.
  all: pick fresh x for L; specialize (H0 x Fr); try assumption; inversion H0; auto.
Qed.

Definition dr_extends (W V : role_context) :=
  uniq V /\ forall x R, binds x R W -> binds x R V.

Lemma dr_extends_cons : forall W V x,
  dr_extends W V -> x `notin` dom V -> dr_extends (x ~ Nom ++ W) (x ~ Nom ++ V).
Proof.
Local Hint Unfold dr_extends : core.
  intros W V x [Hu Hb] Hx. split; [now apply uniq_cons |].
  intros y R H. simpl in *. destruct H as [H|H]; [now left | right; now apply Hb].
Qed.

Lemma dr_role_weak : forall W a R, roleing W a R ->
  forall V, dr_extends W V -> roleing V a R.
Proof.
  intros W a R H; induction H; intros V He; destruct He as [Hu Hb] eqn:E; eauto using roleing.
  - eapply role_a_Abs with (L := L \u dom V).
    intros x Hx. apply H0; [fsetdec|]. apply dr_extends_cons; [split; auto|fsetdec].
  - eapply role_a_Pi with (L := L \u dom V); eauto.
    intros x Hx. apply H1; [fsetdec|]. apply dr_extends_cons; [split; auto|fsetdec].
  - eapply role_a_CPi with (L := L); eauto.
Qed.

Lemma dr_role_promote : forall W a, roleing W a Nom -> roleing W a Rep.
Proof.
  intros W a H.
  remember Nom as R eqn:E in H. induction H; subst; eauto using roleing.
  destruct R1; simpl in *; eauto using roleing.
Qed.

Lemma dr_role_fix : forall W R, uniq W -> roleing W (a_Fam Fix) R.
Proof.
  intros. eapply role_a_Fam with (R := Nom); eauto.
  unfold toplevel; left; reflexivity.
Qed.

Lemma dr_role_prefix : forall W R, uniq W -> roleing W dr_prefix R.
Proof. intros; apply role_a_App; auto using dr_role_fix, role_a_Bullet. Qed.

Lemma dr_role_unfold : forall W f R, roleing W f Nom -> roleing W (dr_unfold f) R.
Proof.
  intros. unfold dr_unfold. apply role_a_App.
  - destruct R; auto using dr_role_promote.
  - apply role_a_App; eauto using dr_role_prefix, dr_role_uniq.
Qed.

Lemma dr_scoped_subst : forall a n u x,
  dr_scoped n a -> dr_scoped 0 u -> dr_scoped n (tm_subst_tm_tm u x a).
Proof.
  fix IH 1; intros a n u x Ha Hu; destruct a; simpl in *; try tauto;
    try destruct phi; try destruct R; simpl in *; try tauto.
  all: try solve [match goal with |- context [if ?d then _ else _] => destruct d end; simpl; auto; eapply dr_scoped_mono; [exact Hu|lia]].
  all: try destruct Ha as [? ->]; simpl in *; intuition eauto.
Qed.

Lemma dr_subst_open_comm : forall a n u x v k,
  dr_scoped n a -> dr_scoped 0 u ->
  tm_subst_tm_tm u x (open_tm_wrt_tm_rec k v a) =
    open_tm_wrt_tm_rec k (tm_subst_tm_tm u x v) (tm_subst_tm_tm u x a).
Proof.
  fix IH 1; intros a n u x v k Ha Hu; destruct a; simpl in *; try contradiction;
    try destruct phi; try destruct R; simpl in *; try contradiction; try reflexivity.
  all: try solve [destruct (lt_eq_lt_dec n0 k) as [[|]|]; reflexivity].
  all: try solve [match goal with |- context [if ?d then _ else _] => destruct d end; try reflexivity;
    symmetry; apply dr_scoped_open_id; eapply dr_scoped_mono; [exact Hu|lia]].
  all: try destruct Ha as [? ->]; simpl in *; repeat f_equal; intuition eauto.
Qed.

Lemma dr_subst_variable : forall u x, tm_subst_tm_tm u x (a_Var_f x) = u.
Proof.
  intros. simpl. match goal with |- context [if ?d then _ else _] => destruct d; congruence end.
Qed.

Lemma dr_subst_other_variable : forall u x y,
  x <> y -> tm_subst_tm_tm u x (a_Var_f y) = a_Var_f y.
Proof.
  intros. simpl. match goal with |- context [if ?d then _ else _] => destruct d; congruence end.
Qed.

(* Parallel reduction of Fix and the role judgments. *)

Lemma dr_par_axiom_shape : forall W a nu a' f' z R p b D,
  tm_subpattern_agree a FixPat -> ~ tm_pattern_agree a FixPat ->
  Par W a a' R ->
  Rename FixPat FixDef p b (dom W `union` fv_tm_tm_tm FixPat) D ->
  MatchSubst (a_App a' nu f') p b z ->
  (exists i, a = a_App (a_Fam Fix) (Rho Irrel) i) /\ nu = Role Nom /\ z = dr_unfold f'.
Proof.
  intros W a nu a' f' z R p b D Hs Hn Hp Hr Hm.
  destruct (dr_match_rename _ _ _ _ Hr _ _ Hm) as (j & g & He & Hz & _).
  injection He as -> -> ->.
  repeat split; auto.
  unfold FixPat in Hs, Hn. inversion Hs; subst.
  - contradiction.
  - match goal with H : tm_subpattern_agree _ _ |- _ =>
      inversion H; subst; clear H
    end.
    + match goal with H : tm_pattern_agree _ _ |- _ =>
        inversion H; subst; clear H
      end.
      match goal with H : tm_pattern_agree _ _ |- _ => inversion H; subst; eauto end.
    + match goal with H : tm_subpattern_agree _ _ |- _ =>
        inversion H; subst; clear H
      end.
      match goal with H : tm_pattern_agree _ _ |- _ =>
        inversion H; subst
      end.
      apply dr_par_fam in Hp; discriminate.
Qed.

Lemma dr_par_axiom : forall W R i j f f',
  Par W (a_App (a_Fam Fix) (Rho Irrel) i) (a_App (a_Fam Fix) (Rho Irrel) j) R ->
  Par W f f' Nom ->
  lc_tm i -> lc_tm j -> lc_tm f' ->
  Par W (a_App (a_App (a_Fam Fix) (Rho Irrel) i) (Role Nom) f) (dr_unfold f') R.
Proof.
  intros W R i j f f' Hi Hf Hli Hj Hf'.
  destruct (dr_rename_match (dom W `union` fv_tm_tm_tm FixPat) j f' Hj Hf')
    as (p & b & D & Hr & Hm).
  eapply Par_AxiomApp with (F := Fix) (R1 := Nom) (A := FixTy) (Rs := [Nom])
    (p := FixPat) (b := FixDef); eauto.
  - unfold toplevel; left; reflexivity.
  - unfold FixPat. split.
    + apply tm_subpattern_agree_AppRelR, tm_subpattern_agree_Base.
      now apply tm_pattern_agree_AppIrrel, tm_pattern_agree_Const.
    + intro H; inversion H.
Qed.

Ltac dr_axiom_cases :=
  dr_signature;
  repeat match goal with
  | Hr : Rename FixPat FixDef _ _ _ _, Hm : MatchSubst (a_CApp _ _) _ _ _ |- _ =>
      destruct (dr_match_rename _ _ _ _ Hr _ _ Hm) as (? & ? & E & _); discriminate
  | Hr : Rename FixPat FixDef _ _ _ _, Hm : MatchSubst (a_App ?a' ?nu ?f') _ _ _,
    Hs : tm_subpattern_agree ?a FixPat /\ ~ tm_pattern_agree ?a FixPat,
    Hp : Par _ ?a ?a' _ |- _ =>
      let S := fresh "Hsub" in let N := fresh "Hnot" in
      destruct Hs as [S N];
      let K := fresh in
      pose proof (dr_par_axiom_shape _ _ _ _ _ _ _ _ _ _ S N Hp Hr Hm) as K;
      destruct K as ((? & E) & ? & ?); subst; clear Hr Hm S N
  | H : SatApp _ _ |- _ => exfalso; exact (dr_no_sat _ _ H)
  end.

Lemma dr_par_role_l : forall W a b R, Par W a b R -> roleing W a R.
Proof.
  intros W a b R H; induction H; try solve [eauto using roleing].
  - destruct nu; simpl in *; eauto using roleing.
  - destruct H0 as [Hs Hn].
    destruct (dr_sig _ _ H) as [-> E]; inversion E; subst; clear H E.
    destruct (dr_par_axiom_shape _ _ _ _ _ _ _ _ _ _ Hs Hn H1 H3 H4)
      as ((i & ->) & -> & ->).
    apply role_a_TApp; assumption.
Qed.

Lemma dr_par_scoped_l : forall W a b R, Par W a b R -> dr_scoped 0 a.
Proof. eauto using dr_role_scoped, dr_par_role_l. Qed.

Lemma dr_par_lc_l : forall W a b R, Par W a b R -> lc_tm a.
Proof. eauto using dr_scoped_lc, dr_par_scoped_l. Qed.

Lemma dr_par_uniq : forall W a b R, Par W a b R -> uniq W.
Proof. eauto using dr_role_uniq, dr_par_role_l. Qed.

Lemma dr_role_subst : forall V a R, roleing V a R ->
  forall W x u, roleing W u Nom -> dr_extends V (x ~ Nom ++ W) ->
    roleing W (tm_subst_tm_tm u x a) R.
Proof.
  intros V a R H; induction H; intros V x0 u Hu He; simpl;
    try solve [eauto using roleing, dr_role_uniq].
  - rename x into y.
    destruct He as [Huniq Hb].
    specialize (Hb _ _ H0). change ((x0, Nom) = (y,R) \/ binds y R V) in Hb.
    destruct (y == x0) as [->|Hne].
    + destruct R1; auto using dr_role_promote.
    + try rewrite dr_subst_other_variable by congruence.
      destruct Hb as [E|Hb]; [congruence|eauto using roleing, dr_role_uniq].
  - eapply role_a_Abs with (L := L \u dom V \u {{x0}}).
    intros y Hy. unfold open_tm_wrt_tm in *.
    assert (Ha : dr_scoped 1 a).
    { apply (proj1 (dr_scoped_open a 0 y)); eauto 6 using dr_role_scoped. }
    rewrite <- dr_subst_other_variable with (x := x0) (u := u) (y := y) at 1 by fsetdec.
    rewrite <- (dr_subst_open_comm a 1 u x0 (a_Var_f y) 0 Ha) by eauto using dr_role_scoped.
    eapply H0; [fsetdec| |].
    + eapply dr_role_weak; [exact Hu|]. split.
      * apply uniq_cons; [eauto using dr_role_uniq|fsetdec].
      * intros. simpl. now right.
    + destruct He as [Huniq Hb]. split.
      * apply uniq_cons.
        -- apply uniq_cons; [eauto using dr_role_uniq|fsetdec].
        -- inversion Huniq; auto.
      * intros z r Hz. simpl in * |- *. destruct Hz as [E|Hz]; [right; now left|].
        destruct (Hb _ _ Hz) as [E|E]; [now left|right; now right].
  - eapply role_a_Pi with (L := L \u dom V \u {{x0}}); eauto.
    intros y Hy. unfold open_tm_wrt_tm in *.
    assert (Ha : dr_scoped 1 B).
    { apply (proj1 (dr_scoped_open B 0 y)); eauto 6 using dr_role_scoped. }
    rewrite <- dr_subst_other_variable with (x := x0) (u := u) (y := y) at 1 by fsetdec.
    rewrite <- (dr_subst_open_comm B 1 u x0 (a_Var_f y) 0 Ha) by eauto using dr_role_scoped.
    eapply H1; [fsetdec| |].
    + eapply dr_role_weak; [exact Hu|]. split.
      * apply uniq_cons; [eauto using dr_role_uniq|fsetdec].
      * intros. simpl. now right.
    + destruct He as [Huniq Hb]. split.
      * apply uniq_cons.
        -- apply uniq_cons; [eauto using dr_role_uniq|fsetdec].
        -- inversion Huniq; auto.
      * intros z r Hz. simpl in * |- *. destruct Hz as [E|Hz]; [right; now left|].
        destruct (Hb _ _ Hz) as [E|E]; [now left|right; now right].
  - pick fresh c for L.
    assert (HB : dr_scoped 0 B).
    { apply (proj1 (dr_scoped_co_open B 0 0 c)).
      unfold open_tm_wrt_co in *. eauto using dr_role_scoped. }
    eapply role_a_CPi with (L := empty); eauto.
    intros. unfold open_tm_wrt_co in *.
    rewrite (dr_scoped_co_id _ _ _ _ (dr_scoped_subst _ _ _ _ HB (dr_role_scoped _ _ _ Hu))).
    specialize (H3 c Fr _ _ _ Hu He).
    rewrite (dr_scoped_co_id _ _ _ _ HB) in H3. exact H3.
  - pick fresh c for L.
    assert (Hb : dr_scoped 0 b).
    { apply (proj1 (dr_scoped_co_open b 0 0 c)).
      unfold open_tm_wrt_co in *. eauto using dr_role_scoped. }
    eapply role_a_CAbs with (L := empty).
    intros. unfold open_tm_wrt_co in *.
    rewrite (dr_scoped_co_id _ _ _ _ (dr_scoped_subst _ _ _ _ Hb (dr_role_scoped _ _ _ Hu))).
    specialize (H0 c Fr _ _ _ Hu He).
    rewrite (dr_scoped_co_id _ _ _ _ Hb) in H0. exact H0.
Qed.

Lemma dr_role_open : forall W rho a R u,
  roleing W (a_UAbs rho a) R -> roleing W u Nom ->
  roleing W (open_tm_wrt_tm a u) R.
Proof.
  intros W rho a R u Ha Hu. inversion Ha; subst.
  pick fresh x for (L \u dom W \u fv_tm_tm_tm a).
  unfold open_tm_wrt_tm in *.
  rewrite <- (dr_open_fresh a 0 u x) by fsetdec.
  eapply dr_role_subst; [apply H3; fsetdec | exact Hu |].
  split; [apply uniq_cons; eauto using dr_role_uniq; fsetdec|auto].
Qed.

Lemma dr_role_co_open : forall W a R,
  roleing W (a_UCAbs a) R -> roleing W (open_tm_wrt_co a g_Triv) R.
Proof.
  intros W a R H. inversion H; subst. pick fresh c for L.
  specialize (H2 c Fr). unfold open_tm_wrt_co in *.
  pose proof (dr_role_scoped _ _ _ H2) as Hs.
  apply dr_scoped_co_open in Hs.
  rewrite (dr_scoped_co_id _ _ _ _ Hs) in H2. rewrite (dr_scoped_co_id _ _ _ _ Hs). exact H2.
Qed.

Lemma dr_par_role_r : forall W a b R, Par W a b R -> roleing W b R.
Proof.
  intros W a b R H; induction H; try solve [eauto using roleing, dr_role_open, dr_role_co_open].
  all: try solve [destruct nu; simpl in *; eauto using roleing].
  all: dr_axiom_cases; eauto using dr_role_unfold, roleing.
Qed.

Lemma dr_par_scoped_r : forall W a b R, Par W a b R -> dr_scoped 0 b.
Proof. eauto using dr_role_scoped, dr_par_role_r. Qed.

Lemma dr_par_lc_r : forall W a b R, Par W a b R -> lc_tm b.
Proof. eauto using dr_scoped_lc, dr_par_scoped_r. Qed.


Lemma dr_par_refl_r : forall W a b R, Par W a b R -> Par W b b R.
Proof. eauto using Par_Refl, dr_par_role_r. Qed.

Lemma dr_par_weak : forall W a b R, Par W a b R ->
  forall V, dr_extends W V -> Par V a b R.
Proof.
  intros W a b R H; induction H; intros V HV;
    try solve [eauto using Par, dr_role_weak].
  - eapply Par_Abs with (L := L \u dom V).
    intros x Hx. eapply H0; [fsetdec|apply dr_extends_cons; auto; fsetdec].
  - eapply Par_Pi with (L := L \u dom V); eauto.
    intros x Hx. eapply H1; [fsetdec|apply dr_extends_cons; auto; fsetdec].
  - eapply Par_CPi with (L := L); eauto.
  - dr_axiom_cases.
  - dr_signature. destruct H0 as [Hs Hn].
    destruct (dr_par_axiom_shape _ _ _ _ _ _ _ _ _ _ Hs Hn H1 H3 H4)
      as ((i & ->) & -> & ->).
    destruct (dr_par_fix_prefix _ _ _ _ H1) as (j & -> & Hj).
    eapply dr_par_axiom; [apply IHPar1; auto | destruct R; auto | eauto using dr_par_lc_l | eauto using dr_par_lc_r | destruct R; eauto using dr_par_lc_r].
  - dr_axiom_cases.
Qed.

Lemma dr_par_promote : forall W a b, Par W a b Nom -> Par W a b Rep.
Proof.
  intros W a b H. remember Nom as r eqn:E in H. induction H; subst;
    try solve [eauto using Par, dr_role_promote].
  - destruct nu as [[]|[]]; simpl in *; eauto using Par.
  - dr_axiom_cases.
    destruct (dr_par_fix_prefix _ _ _ _ H1) as (j & -> & Hj).
    eapply dr_par_axiom; [apply IHPar1; auto | exact H2 | eauto using dr_par_lc_l | eauto using dr_par_lc_r | eauto using dr_par_lc_r].
Qed.

Lemma dr_casepath_inv : forall R a F, CasePath R a F ->
  F = Fix /\ ValuePath a Fix /\ ~ subtm_pattern_agree a FixPat.
Proof. intros R a F H; inversion H; subst; dr_signature; auto. Qed.

Lemma dr_pattern_agree_shape : forall a, tm_pattern_agree a FixPat <->
  exists i f, a = a_App (a_App (a_Fam Fix) (Rho Irrel) i) (Role Nom) f /\ lc_tm i /\ lc_tm f.
Proof.
  intros a; split.
  - intros H. unfold FixPat in H. inversion H; subst; clear H.
    match goal with H : tm_pattern_agree _ _ |- _ => inversion H; subst; clear H end.
    match goal with H : tm_pattern_agree _ _ |- _ => inversion H; subst; clear H end.
    do 2 eexists; eauto.
  - intros (i & f & -> & Hi & Hf). unfold FixPat.
    constructor; auto. constructor; auto. constructor.
Qed.

Fixpoint dr_spine (a : tm) : option (const * list App) :=
  match a with
  | a_Fam F => Some (F, nil)
  | a_App a nu _ =>
    option_map (fun '(F, s) => (F, A_Tm nu :: s)) (dr_spine a)
  | a_CApp a g_Triv =>
    option_map (fun '(F, s) => (F, A_Co :: s)) (dr_spine a)
  | _ => None
  end.

Definition dr_fixed_spine := A_Tm (Role Nom) :: A_Tm (Rho Irrel) :: nil.

Lemma dr_valuepath_spine : forall a F, ValuePath a F ->
  exists s, dr_spine a = Some (F, s).
Proof.
  intros a F H; induction H; simpl; eauto;
    destruct IHValuePath as [s ->]; eexists; reflexivity.
Qed.

Lemma dr_spine_valuepath : forall a s, dr_scoped 0 a ->
  dr_spine a = Some (Fix,s) -> ValuePath a Fix.
Proof.
  induction a; intros s Hs H; simpl in *; try discriminate.
  - destruct (dr_spine a1) as [[G t]|] eqn:E; simpl in H; try discriminate.
    inversion H; subst. destruct Hs. constructor; eauto using dr_scoped_lc.
  - destruct Hs as [Hs ->]. simpl in H.
    destruct (dr_spine a) as [[G t]|] eqn:E; simpl in H; try discriminate.
    inversion H; subst. constructor; eauto.
  - inversion H; subst. apply ValuePath_Const with (p := FixPat) (a := FixDef)
      (A := FixTy) (R1 := Nom) (Rs := [Nom]).
    unfold toplevel; now left.
Qed.

Lemma dr_subpat_spine : forall a,
  subtm_pattern_agree a FixPat ->
  exists s, dr_spine a = Some (Fix, s ++ dr_fixed_spine).
Proof.
  intros a H; remember FixPat as p eqn:E in H. induction H; subst; simpl.
  - apply dr_pattern_agree_shape in H. destruct H as (i & f & -> & _).
    exists nil; reflexivity.
  - destruct IHsubtm_pattern_agree as [s ->]; auto.
    exists (A_Tm nu :: s); reflexivity.
  - destruct IHsubtm_pattern_agree as [s ->]; auto.
    exists (A_Co :: s); reflexivity.
Qed.

Lemma dr_spine_subpat : forall a s, dr_scoped 0 a ->
  dr_spine a = Some (Fix,s ++ dr_fixed_spine) -> subtm_pattern_agree a FixPat.
Proof.
  induction a; intros s Hs H; simpl in *; try discriminate.
  - destruct Hs as [H1 H2].
    destruct (dr_spine a1) as [[F t]|] eqn:E; simpl in H; try discriminate.
    destruct s as [|head s].
    + inversion H; subst. clear H.
      destruct a1; simpl in E; try discriminate.
      * destruct (dr_spine a1_1) as [[F t]|] eqn:E1; simpl in E; try discriminate.
        inversion E; subst. clear E.
        destruct a1_1; simpl in E1; try discriminate.
        -- destruct (dr_spine a1_1_1) as [[F t]|]; discriminate.
        -- destruct g; try discriminate. destruct (dr_spine a1_1) as [[F t]|]; discriminate.
        -- inversion E1; subst. destruct H1 as [_ H1].
           apply subtm_pattern_agree_Base, dr_pattern_agree_shape.
           do 2 eexists; repeat split; eauto using dr_scoped_lc.
      * destruct g; try discriminate. destruct (dr_spine a1) as [[F t]|]; discriminate.
    + inversion H; subst. apply subtm_pattern_agree_App; eauto using dr_scoped_lc.
  - destruct Hs as [Hs ->]. simpl in H.
    destruct (dr_spine a) as [[F t]|] eqn:E; simpl in H; try discriminate.
    destruct s as [|head s]; [discriminate|].
    inversion H; subst. apply subtm_pattern_agree_CAppp; eauto.
  - destruct s; discriminate.
Qed.

Lemma dr_spine_subst : forall a F s u x,
  dr_spine a = Some (F,s) ->
  dr_spine (tm_subst_tm_tm u x a) = Some (F,s).
Proof.
  induction a; intros F0 s u z H; simpl in *; try discriminate; auto.
  - destruct (dr_spine a1) as [[G t]|]; simpl in H; try discriminate.
    inversion H; subst. rewrite (IHa1 _ _ u z eq_refl). reflexivity.
  - destruct g; simpl in H; try discriminate.
    destruct (dr_spine a) as [[G t]|]; simpl in H; try discriminate.
    inversion H; subst. simpl. rewrite (IHa _ _ u z eq_refl). reflexivity.
Qed.

Lemma dr_casepath_spine : forall a s R,
  dr_scoped 0 a -> dr_spine a = Some (Fix,s) ->
  (forall t, s <> t ++ dr_fixed_spine) -> CasePath R a Fix.
Proof.
  intros a s R Hs H Hn.
  eapply CasePath_UnMatch with (p := FixPat) (R1 := Nom) (Rs := [Nom]) (b := FixDef) (A := FixTy).
  - eapply dr_spine_valuepath; eauto.
  - unfold toplevel; now left.
  - intros M. destruct (dr_subpat_spine _ M) as [t E]. rewrite H in E. inversion E; now apply (Hn t).
Qed.

Lemma dr_casepath_subst : forall R a F u x,
  CasePath R a F -> dr_scoped 0 a -> dr_scoped 0 u ->
  CasePath R (tm_subst_tm_tm u x a) F.
Proof.
  intros R a F u x H Ha Hu.
  destruct (dr_casepath_inv _ _ _ H) as (-> & V & N).
  destruct (dr_valuepath_spine _ _ V) as [s E].
  eapply dr_casepath_spine; eauto using dr_scoped_subst, dr_spine_subst.
  intros t ->. eapply N, dr_spine_subpat; eauto.
Qed.

Lemma dr_value_subst : forall R a u x,
  Value R a -> dr_scoped 0 a -> dr_scoped 0 u ->
  Value R (tm_subst_tm_tm u x a).
Proof.
  intros R a u x H. induction H; intros Ha Hu;
    try solve [constructor; [apply dr_scoped_lc; eapply dr_scoped_subst; eauto|..];
               apply dr_scoped_lc; eapply dr_scoped_subst; eauto].
  - constructor.
  - apply Value_Pi.
    + eapply dr_scoped_lc, dr_scoped_subst; [exact (proj1 Ha)|exact Hu].
    + apply dr_scoped_lc. exact (dr_scoped_subst _ _ u x Ha Hu).
  - change (Value R (tm_subst_tm_tm u x (a_CPi phi B))).
    destruct phi as [a b A R0]. apply Value_CPi.
    + simpl in Ha |- *. destruct Ha as (H1 & H2 & H3 & H4).
      constructor; eauto using dr_scoped_subst, dr_scoped_lc.
    + apply dr_scoped_lc. exact (dr_scoped_subst _ _ u x Ha Hu).
  - contradiction.
  - simpl in *. eapply Value_UAbsIrrel with (L := L \u {{x}}).
    intros y Hy. unfold open_tm_wrt_tm in *.
    rewrite <- (dr_subst_other_variable u x y) at 1 by fsetdec.
    rewrite <- (dr_subst_open_comm a 1 u x (a_Var_f y) 0 Ha Hu).
    eapply H0; [fsetdec | now apply dr_scoped_open | exact Hu].
  - contradiction.
  - eapply Value_Path; eauto using dr_casepath_subst.
Qed.

Lemma dr_par_extends_cons_swap : forall V W x y,
  dr_extends V (x ~ Nom ++ W) -> y `notin` dom W -> y <> x ->
  dr_extends (y ~ Nom ++ V) (x ~ Nom ++ y ~ Nom ++ W).
Proof.
  intros V W x y [Hu Hb] Hy Hxy. split.
  - apply uniq_cons.
    + apply uniq_cons; [inversion Hu; auto|exact Hy].
    + inversion Hu; subst. simpl. fsetdec.
  - intros z r H. simpl in H |- *. destruct H as [H|H].
    + right; now left.
    + destruct (Hb _ _ H); [now left|right; now right].
Qed.

Lemma dr_par_extends_push : forall W x,
  uniq W -> x `notin` dom W -> dr_extends W (x ~ Nom ++ W).
Proof. intros; split; [now apply uniq_cons|intros; simpl; now right]. Qed.

Lemma dr_par_co_body : forall W a b R c,
  Par W (open_tm_wrt_co a (g_Var_f c)) (open_tm_wrt_co b (g_Var_f c)) R ->
  Par W a b R.
Proof.
  intros W a b R c H. unfold open_tm_wrt_co in H.
  pose proof (dr_par_scoped_l _ _ _ _ H) as Ha.
  pose proof (dr_par_scoped_r _ _ _ _ H) as Hb.
  apply dr_scoped_co_open in Ha, Hb.
  rewrite (dr_scoped_co_id _ _ _ _ Ha), (dr_scoped_co_id _ _ _ _ Hb) in H. exact H.
Qed.

Lemma dr_par_cabs : forall W a b R, Par W a b R ->
  Par W (a_UCAbs a) (a_UCAbs b) R.
Proof.
  intros W a b R H. eapply Par_CAbs with (L := empty). intros.
  unfold open_tm_wrt_co. rewrite (dr_scoped_co_id _ _ _ _ (dr_par_scoped_l _ _ _ _ H)).
  now rewrite (dr_scoped_co_id _ _ _ _ (dr_par_scoped_r _ _ _ _ H)).
Qed.

Lemma dr_par_cpi : forall W a b A R1 B a' b' A' B' R,
  Par W A A' Rep -> Par W a a' R1 -> Par W b b' R1 -> Par W B B' R ->
  Par W (a_CPi (Eq a b A R1) B) (a_CPi (Eq a' b' A' R1) B') R.
Proof.
  intros. eapply Par_CPi with (L := empty); eauto. intros.
  unfold open_tm_wrt_co.
  rewrite (dr_scoped_co_id _ _ _ _ (dr_par_scoped_l _ _ _ _ H2)).
  now rewrite (dr_scoped_co_id _ _ _ _ (dr_par_scoped_r _ _ _ _ H2)).
Qed.

Ltac dr_bind_subst L P IH a b W x u v Hu HV :=
    first [eapply Par_Abs with (L := L \u dom W \u {{x}})
          |eapply Par_Pi with (L := L \u dom W \u {{x}}); [eauto|]];
    let y := fresh "y" in let Hy := fresh "Hy" in intros y Hy;
    unfold open_tm_wrt_tm in *;
    let Hs := fresh "Hs" in assert (Hs : y `notin` L) by fsetdec;
    let Ha := fresh "Ha" in let Hb := fresh "Hb" in
    assert (Ha : dr_scoped 0 (open_tm_wrt_tm_rec 0 (a_Var_f y) a))
      by (first [exact (dr_par_scoped_l _ _ _ _ (P y Hs)) | exact (dr_role_scoped _ _ _ (P y Hs))]);
    assert (Hb : dr_scoped 0 (open_tm_wrt_tm_rec 0 (a_Var_f y) b))
      by (first [exact (dr_par_scoped_r _ _ _ _ (P y Hs)) | exact (dr_role_scoped _ _ _ (P y Hs))]);
    apply dr_scoped_open in Ha, Hb;
    rewrite <- (dr_subst_other_variable u x y) at 1 by fsetdec;
    rewrite <- (dr_subst_open_comm a 1 u x (a_Var_f y) 0 Ha) by eauto using dr_par_scoped_l;
    rewrite <- (dr_subst_other_variable v x y) at 2 by fsetdec;
    rewrite <- (dr_subst_open_comm b 1 v x (a_Var_f y) 0 Hb) by eauto using dr_par_scoped_r;
    eapply IH; [exact Hs | eapply dr_par_weak; [exact Hu|apply dr_par_extends_push; [eauto using dr_par_uniq|fsetdec]]
               | eapply dr_par_extends_cons_swap; [exact HV|fsetdec|fsetdec]]
  .

Lemma dr_par_subst : forall V a b R, Par V a b R ->
  forall W x u v, Par W u v Nom -> dr_extends V (x ~ Nom ++ W) ->
  Par W (tm_subst_tm_tm u x a) (tm_subst_tm_tm v x b) R.
Proof.
  intros V a b R H; induction H; intros V x u v Huv HV.
  - revert V x u v Huv HV. induction H; intros V x0 u v Huv HV; simpl;
      try solve [eauto using Par, dr_role_subst, dr_par_role_l].
    + constructor. constructor. eauto using dr_par_uniq.
    + constructor. constructor. eauto using dr_par_uniq.
    + destruct (x == x0) as [->|Hne].
      * destruct R1; eauto using dr_par_promote.
      * apply Par_Refl. apply role_a_Var with (R := R); eauto using dr_par_uniq.
        destruct HV as [_ Hb]. specialize (Hb _ _ H0). simpl in Hb.
        destruct Hb; [congruence|assumption].
    + dr_bind_subst L H H0 a a V x0 u v Huv HV.
    + dr_bind_subst L H0 H1 B B V x0 u v Huv HV.
    + pick fresh c for L.
      pose proof (dr_role_scoped _ _ _ (H2 c Fr)) as Hs.
      unfold open_tm_wrt_co in Hs. apply dr_scoped_co_open in Hs.
      apply dr_par_cpi; eauto. specialize (H3 c Fr _ _ _ _ Huv HV).
      unfold open_tm_wrt_co in H3. now rewrite (dr_scoped_co_id _ _ _ _ Hs) in H3.
    + pick fresh c for L.
      pose proof (dr_role_scoped _ _ _ (H c Fr)) as Hs.
      unfold open_tm_wrt_co in Hs. apply dr_scoped_co_open in Hs.
      apply dr_par_cabs. specialize (H0 c Fr _ _ _ _ Huv HV).
      unfold open_tm_wrt_co in H0. now rewrite (dr_scoped_co_id _ _ _ _ Hs) in H0.
    + apply Par_Refl. econstructor; eauto using dr_par_uniq.
    + apply Par_Refl. eapply role_a_Fam; eauto using dr_par_uniq.
  - unfold open_tm_wrt_tm.
    pose proof (dr_par_scoped_r _ _ _ _ H) as Ha. simpl in Ha.
    rewrite (dr_subst_open_comm a' 1 v x b' 0 Ha) by eauto using dr_par_scoped_r.
    simpl. apply Par_Beta; eauto.
  - simpl. apply Par_App; eauto.
  - pose proof (dr_par_scoped_r _ _ _ _ H) as Ha. simpl in Ha.
    unfold open_tm_wrt_co. rewrite (dr_scoped_co_id _ _ _ _ Ha).
    rewrite <- (dr_scoped_co_id _ 0 0 g_Triv (dr_scoped_subst _ _ v x Ha (dr_par_scoped_r _ _ _ _ Huv))).
    simpl. apply Par_CBeta. apply IHPar; auto.
  - simpl. apply Par_CApp; auto.
  - simpl. dr_bind_subst L H H0 a a' V x u v Huv HV.
  - simpl. dr_bind_subst L H0 H1 B B' V x u v Huv HV.
  - simpl. pick fresh c for L.
    apply dr_par_cabs.
    pose proof (dr_par_co_body _ _ _ _ _ (H c Fr)) as P.
    pose proof (dr_par_scoped_l _ _ _ _ P) as Ha.
    pose proof (dr_par_scoped_r _ _ _ _ P) as Hb.
    specialize (H0 c Fr _ _ _ _ Huv HV).
    unfold open_tm_wrt_co in H0.
    rewrite (dr_scoped_co_id _ _ _ _ Ha), (dr_scoped_co_id _ _ _ _ Hb) in H0.
    exact H0.
  - simpl. pick fresh c for L.
    apply dr_par_cpi; eauto.
    pose proof (dr_par_co_body _ _ _ _ _ (H2 c Fr)) as P.
    pose proof (dr_par_scoped_l _ _ _ _ P) as Ha.
    pose proof (dr_par_scoped_r _ _ _ _ P) as Hb.
    specialize (H3 c Fr _ _ _ _ Huv HV).
    unfold open_tm_wrt_co in H3.
    rewrite (dr_scoped_co_id _ _ _ _ Ha), (dr_scoped_co_id _ _ _ _ Hb) in H3.
    exact H3.
  - dr_axiom_cases.
  - dr_axiom_cases.
    destruct (dr_par_fix_prefix _ _ _ _ H1) as (j & -> & Hj).
    specialize (IHPar1 _ _ _ _ Huv HV).
    specialize (IHPar2 _ _ _ _ Huv HV).
    change (Par V (a_App (a_Fam Fix) (Rho Irrel) (tm_subst_tm_tm u x x0))
        (a_App (a_Fam Fix) (Rho Irrel) (tm_subst_tm_tm v x j)) R) in IHPar1.
    change (Par V (a_App (a_App (a_Fam Fix) (Rho Irrel) (tm_subst_tm_tm u x x0))
        (Role Nom) (tm_subst_tm_tm u x a1)) (dr_unfold (tm_subst_tm_tm v x a1')) R).
    eapply dr_par_axiom; [exact IHPar1|destruct R; exact IHPar2|..].
    all: try solve [eapply dr_scoped_lc; eapply dr_scoped_subst; eauto using dr_par_scoped_l, dr_par_scoped_r].
  - dr_axiom_cases.
  - simpl. apply Par_Pattern; eauto.
  - dr_axiom_cases.
  - simpl. eapply Par_PatternFalse; eauto using dr_value_subst, dr_par_scoped_r, dr_no_apps_path.
Qed.

(* The diamond property for parallel reduction. *)

Lemma dr_par_open : forall W a b R L,
  (forall x, x `notin` L ->
    Par (x ~ Nom ++ W) (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm b (a_Var_f x)) R) ->
  forall u v, Par W u v Nom ->
  Par W (open_tm_wrt_tm a u) (open_tm_wrt_tm b v) R.
Proof.
  intros W a b R L H u v P.
  pick fresh x for (L \u dom W \u fv_tm_tm_tm a \u fv_tm_tm_tm b).
  unfold open_tm_wrt_tm in *.
  rewrite <- (dr_open_fresh a 0 u x), <- (dr_open_fresh b 0 v x) by fsetdec.
  eapply dr_par_subst; [apply H; fsetdec|exact P|].
  split; [apply uniq_cons; [eauto using dr_par_uniq|fsetdec]|auto].
Qed.

Lemma dr_par_abs_inv : forall W rho a b R,
  Par W (a_UAbs rho a) b R ->
  exists B L, b = a_UAbs rho B /\
    forall x, x `notin` L -> Par (x ~ Nom ++ W)
      (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x)) R.
Proof.
  intros W rho a b R H; inversion H; subst; eauto.
  inversion H0; subst. exists a, L; split; [reflexivity|].
  intros; apply Par_Refl; eauto.
Qed.

Lemma dr_par_cabs_inv : forall W a b R,
  Par W (a_UCAbs a) b R -> exists B, b = a_UCAbs B /\ Par W a B R.
Proof.
  intros W a b R H; inversion H; subst.
  - inversion H0; subst. pick fresh c for L.
    exists a; split; [reflexivity|].
    eapply dr_par_co_body; apply Par_Refl; eauto.
  - pick fresh c for L. eauto using dr_par_co_body.
Qed.

Lemma dr_par_spine_stable : forall W a b R, Par W a b R ->
  forall s, dr_spine a = Some (Fix,s) ->
  (forall t, s <> t ++ dr_fixed_spine) ->
  dr_spine b = Some (Fix,s).
Proof.
  intros W a b R H; induction H; intros s Hs Hn; simpl in *;
    try discriminate; try assumption.
  - destruct (dr_spine a) as [[F t]|] eqn:E; simpl in Hs; try discriminate.
    inversion Hs; subst. assert (N : forall u, t <> u ++ dr_fixed_spine).
    { intros u ->. apply (Hn (A_Tm (Rho rho) :: u)). reflexivity. }
    specialize (IHPar1 t eq_refl N). discriminate.
  - destruct (dr_spine a) as [[F t]|] eqn:E; simpl in Hs; try discriminate.
    inversion Hs; subst. assert (N : forall u, t <> u ++ dr_fixed_spine).
    { intros u ->. apply (Hn (A_Tm nu :: u)). reflexivity. }
    now rewrite (IHPar1 t eq_refl N).
  - destruct (dr_spine a) as [[F t]|] eqn:E; simpl in Hs; try discriminate.
    inversion Hs; subst. assert (N : forall u, t <> u ++ dr_fixed_spine).
    { intros u ->. apply (Hn (A_Co :: u)). reflexivity. }
    specialize (IHPar t eq_refl N). discriminate.
  - destruct (dr_spine a) as [[F t]|] eqn:E; simpl in Hs; try discriminate.
    inversion Hs; subst. assert (N : forall u, t <> u ++ dr_fixed_spine).
    { intros u ->. apply (Hn (A_Co :: u)). reflexivity. }
    now rewrite (IHPar t eq_refl N).
  - dr_axiom_cases.
  - dr_axiom_cases. simpl in Hs. inversion Hs; subst. exfalso. exact (Hn nil eq_refl).
  - dr_axiom_cases.
Qed.

Lemma dr_value_par : forall R a, Value R a ->
  forall W b, Par W a b R -> Value R b.
Proof.
  intros R a H; induction H; intros W z K.
  - inversion K; subst; constructor.
  - inversion K; subst; [now constructor|].
    apply Value_Pi; eauto using dr_par_lc_r.
  - inversion K; subst; [now constructor|].
    apply Value_CPi; [constructor; eauto using dr_par_lc_r|eauto using dr_par_lc_r].
  - inversion K; subst; constructor; eauto using dr_par_lc_r.
  - destruct (dr_par_abs_inv _ _ _ _ _ K) as (B & L' & -> & P).
    apply Value_UAbsRel; eauto using dr_par_lc_r.
  - destruct (dr_par_abs_inv _ _ _ _ _ K) as (B & L' & -> & P).
    eapply Value_UAbsIrrel with (L := L \u L'). intros x Hx.
    eapply (H0 x); [fsetdec|apply P; fsetdec].
  - inversion K; subst; constructor; eauto using dr_par_lc_r.
  - destruct (dr_par_cabs_inv _ _ _ _ K) as (? & -> & P).
    apply Value_UCAbs; eauto using dr_par_lc_r.
  - destruct (dr_casepath_inv _ _ _ H) as (-> & V & N).
    destruct (dr_valuepath_spine _ _ V) as [s E].
    assert (N' : forall t, s <> t ++ dr_fixed_spine).
    { intros t ->; eapply N, dr_spine_subpat; eauto using dr_par_scoped_l. }
    eapply Value_Path, dr_casepath_spine; eauto using dr_par_scoped_r, dr_par_spine_stable.
Qed.

Fixpoint dr_close (k : nat) (x : atom) (a : tm) : tm :=
  match a with
  | a_Var_b n => if lt_dec n k then a_Var_b n else a_Var_b (S n)
  | a_Var_f y => if y == x then a_Var_b k else a_Var_f y
  | a_UAbs rho b => a_UAbs rho (dr_close (S k) x b)
  | a_App a nu b => a_App (dr_close k x a) nu (dr_close k x b)
  | a_Pi rho a b => a_Pi rho (dr_close k x a) (dr_close (S k) x b)
  | a_UCAbs a => a_UCAbs (dr_close k x a)
  | a_CApp a g => a_CApp (dr_close k x a) g
  | a_CPi (Eq a b A R) B =>
      a_CPi (Eq (dr_close k x a) (dr_close k x b) (dr_close k x A) R) (dr_close k x B)
  | a_Pattern R a F aps b c => a_Pattern R (dr_close k x a) F aps (dr_close k x b) (dr_close k x c)
  | _ => a
  end.

Lemma dr_close_open : forall a n k x u,
  dr_scoped n a ->
  open_tm_wrt_tm_rec k u (dr_close k x a) = tm_subst_tm_tm u x a.
Proof.
  fix IH 1; intros a n k x u H; destruct a; simpl in *; try contradiction;
    try destruct phi; try destruct R; simpl in *; try contradiction; try reflexivity.
  all: try solve [try match type of H with _ /\ _ = g_Triv => destruct H as [? ->] end; simpl; repeat f_equal; intuition eauto].
  - destruct (lt_dec n0 k); cbn -[lt_eq_lt_dec].
    + destruct (lt_eq_lt_dec n0 k) as [[|]|]; try reflexivity; lia.
    + destruct (lt_eq_lt_dec (S n0) k) as [[|]|]; try lia.
      f_equal; lia.
  - match goal with |- context [if ?d then _ else _] => destruct d as [->|] end; cbn -[lt_eq_lt_dec].
    + destruct (lt_eq_lt_dec k k) as [[|]|]; try reflexivity; lia.
    + reflexivity.
Qed.

Lemma dr_join_bodies : forall L W a b R,
  (forall x, x `notin` L -> exists c,
      Par (x ~ Nom ++ W) (open_tm_wrt_tm a (a_Var_f x)) c R /\
      Par (x ~ Nom ++ W) (open_tm_wrt_tm b (a_Var_f x)) c R) ->
  exists c L', forall y, y `notin` L' ->
      Par (y ~ Nom ++ W) (open_tm_wrt_tm a (a_Var_f y)) (open_tm_wrt_tm c (a_Var_f y)) R /\
      Par (y ~ Nom ++ W) (open_tm_wrt_tm b (a_Var_f y)) (open_tm_wrt_tm c (a_Var_f y)) R.
Proof.
  intros L W a b R H. pick fresh x for (L \u dom W \u fv_tm_tm_tm a \u fv_tm_tm_tm b).
  assert (Hx : x `notin` L) by fsetdec.
  destruct (H x Hx) as (c & P & Q).
  exists (dr_close 0 x c), (dom W \u {{x}}). intros y Hy.
  assert (Hu : uniq W) by (pose proof (dr_par_uniq _ _ _ _ P); inversion H0; auto).
  assert (Y : Par (y ~ Nom ++ W) (a_Var_f y) (a_Var_f y) Nom).
  { apply Par_Refl. eapply role_a_Var with (R := Nom); auto. }
  assert (E : dr_extends (x ~ Nom ++ W) (x ~ Nom ++ y ~ Nom ++ W)).
  { apply dr_extends_cons; [apply dr_par_extends_push; auto; fsetdec|simpl; fsetdec]. }
  unfold open_tm_wrt_tm in *.
  rewrite (dr_close_open c 0) by eauto using dr_par_scoped_r.
  rewrite <- (dr_open_fresh a 0 (a_Var_f y) x), <- (dr_open_fresh b 0 (a_Var_f y) x) by fsetdec.
  split; eapply dr_par_subst; eauto.
Qed.

Definition dr_diamond W a R :=
  forall b, Par W a b R -> forall c, Par W a c R ->
    exists d, Par W b d R /\ Par W c d R.

Inductive dr_app_result : tm -> appflag -> tm -> tm -> tm -> Prop :=
| dr_ar_app : forall src nu a b, dr_app_result src nu a b (a_App a nu b)
| dr_ar_beta : forall src rho a b, dr_app_result src (Rho rho) (a_UAbs rho a) b (open_tm_wrt_tm a b)
| dr_ar_fix : forall i j b, dr_app_result
    (a_App (a_Fam Fix) (Rho Irrel) i) (Role Nom) (a_App (a_Fam Fix) (Rho Irrel) j) b (dr_unfold b).

Lemma dr_app_view : forall W a nu b c R, Par W (a_App a nu b) c R ->
  exists a' b', Par W a a' R /\ Par W b b' (app_role nu R) /\ dr_app_result a nu a' b' c.
Proof.
  intros W a nu b c R H. inversion H; subst.
  - inversion H0; subst; do 2 eexists; repeat split; eauto using Par_Refl, dr_ar_app.
  - do 2 eexists; repeat split; eauto using dr_ar_beta.
  - do 2 eexists; repeat split; eauto using dr_ar_app.
  - dr_axiom_cases.
    destruct (dr_par_fix_prefix _ _ _ _ H5) as (j & -> & Hj).
    do 2 eexists; repeat split; eauto using dr_ar_fix.
Qed.

Lemma dr_par_unfold : forall W a b R, Par W a b Nom -> Par W (dr_unfold a) (dr_unfold b) R.
Proof.
  intros W a b R H. unfold dr_unfold. eapply Par_App.
  - destruct R; eauto using dr_par_promote.
  - apply Par_App; [apply Par_Refl; eauto using dr_role_prefix, dr_par_uniq|exact H].
Qed.

Lemma dr_app_result_join : forall W src nu a1 a2 ac b1 b2 bc u v R,
  dr_app_result src nu a1 b1 u -> dr_app_result src nu a2 b2 v ->
  Par W src a1 R -> Par W src a2 R ->
  Par W a1 ac R -> Par W a2 ac R ->
  Par W b1 bc (app_role nu R) -> Par W b2 bc (app_role nu R) ->
  exists d, Par W u d R /\ Par W v d R.
Proof.
  intros W src nu a1 a2 ac b1 b2 bc u v R Hu Hv P Q Pa Qa Pb Qb.
  inversion Hu; inversion Hv; subst; try discriminate.
  - exists (a_App ac nu bc); eauto using Par_App.
  - destruct (dr_par_abs_inv _ _ _ _ _ Qa) as (C & L & -> & Qc).
    exists (open_tm_wrt_tm C bc); eauto using Par_Beta, dr_par_open.
  - destruct (dr_par_fix_prefix _ _ _ _ P) as (i' & -> & _).
    destruct (dr_par_fix_prefix _ _ _ _ Pa) as (j' & -> & Pj).
    destruct R; exists (dr_unfold bc); split;
      [eapply dr_par_axiom; [exact Pa|exact Pb|..] | now apply dr_par_unfold
      |eapply dr_par_axiom; [exact Pa|exact Pb|..] | now apply dr_par_unfold];
      eauto using dr_par_lc_l, dr_par_lc_r.
  - destruct (dr_par_abs_inv _ _ _ _ _ Pa) as (C & L & -> & Pc).
    exists (open_tm_wrt_tm C bc); eauto using Par_Beta, dr_par_open.
  - destruct (dr_par_abs_inv _ _ _ _ _ Pa) as (C & L & -> & Pc).
    destruct (dr_par_abs_inv _ _ _ _ _ Qa) as (D & M & E & Qc).
    inversion E; subst. exists (open_tm_wrt_tm D bc); eauto using dr_par_open.
  - destruct (dr_par_fix_prefix _ _ _ _ Q) as (i' & -> & _).
    destruct (dr_par_fix_prefix _ _ _ _ Qa) as (j' & -> & Qj).
    destruct R; exists (dr_unfold bc); split;
      [now apply dr_par_unfold | eapply dr_par_axiom; [exact Qa|exact Qb|..]
      |now apply dr_par_unfold | eapply dr_par_axiom; [exact Qa|exact Qb|..]];
      eauto using dr_par_lc_l, dr_par_lc_r.
  - destruct R; exists (dr_unfold bc); split; eauto using dr_par_unfold.
Qed.


Inductive dr_capp_result : tm -> tm -> Prop :=
| dr_cr_app : forall a, dr_capp_result a (a_CApp a g_Triv)
| dr_cr_beta : forall a, dr_capp_result (a_UCAbs a) (open_tm_wrt_co a g_Triv).

Lemma dr_capp_view : forall W a c R, Par W (a_CApp a g_Triv) c R ->
  exists a', Par W a a' R /\ dr_capp_result a' c.
Proof.
  intros W a c R H. inversion H; subst; dr_axiom_cases;
    eauto using dr_cr_beta, dr_cr_app.
  inversion H0; subst. eauto using Par_Refl, dr_cr_app.
Qed.

Lemma dr_capp_result_join : forall W a b c u v R,
  dr_capp_result a u -> dr_capp_result b v -> Par W a c R -> Par W b c R ->
  exists d, Par W u d R /\ Par W v d R.
Proof.
  intros W a b c u v R Hu Hv P Q. inversion Hu; inversion Hv; subst.
  - exists (a_CApp c g_Triv); auto using Par_CApp.
  - destruct (dr_par_cabs_inv _ _ _ _ Q) as (z & -> & Qz).
    exists (open_tm_wrt_co z g_Triv). split; [eauto using Par_CBeta|].
    unfold open_tm_wrt_co. rewrite (dr_scoped_co_id _ _ _ _ (dr_par_scoped_l _ _ _ _ Qz)).
    now rewrite (dr_scoped_co_id _ _ _ _ (dr_par_scoped_r _ _ _ _ Qz)).
  - destruct (dr_par_cabs_inv _ _ _ _ P) as (z & -> & Pz).
    exists (open_tm_wrt_co z g_Triv). split; [|eauto using Par_CBeta].
    unfold open_tm_wrt_co. rewrite (dr_scoped_co_id _ _ _ _ (dr_par_scoped_l _ _ _ _ Pz)).
    now rewrite (dr_scoped_co_id _ _ _ _ (dr_par_scoped_r _ _ _ _ Pz)).
  - destruct (dr_par_cabs_inv _ _ _ _ P) as (z & -> & Pz).
    destruct (dr_par_cabs_inv _ _ _ _ Q) as (zz & E & Qz). inversion E; subst.
    exists zz. unfold open_tm_wrt_co.
    rewrite (dr_scoped_co_id _ _ _ _ (dr_par_scoped_l _ _ _ _ Pz)).
    now rewrite (dr_scoped_co_id _ _ _ _ (dr_par_scoped_l _ _ _ _ Qz)).
Qed.

Inductive dr_pat_result (F : const) (aps : Apps) : tm -> tm -> tm -> tm -> Prop :=
| dr_pr_cong : forall a b1 b2, dr_pat_result F aps a b1 b2 (a_Pattern Nom a F aps b1 b2)
| dr_pr_false : forall a b1 b2, Value Nom a -> dr_pat_result F aps a b1 b2 b2.

Lemma dr_pat_view : forall W a F aps b1 b2 c R,
  Par W (a_Pattern Nom a F aps b1 b2) c R ->
  exists a' b1' b2', Par W a a' Nom /\ Par W b1 b1' R /\ Par W b2 b2' R /\
    dr_pat_result F aps a' b1' b2' c.
Proof.
  intros W a F aps b1 b2 c R H. inversion H; subst; dr_axiom_cases.
  - inversion H0; subst. do 3 eexists; repeat split; eauto using Par_Refl, dr_pr_cong.
  - do 3 eexists; repeat split; eauto using dr_pr_cong.
  - do 3 eexists; repeat split; eauto using dr_pr_false.
Qed.

Lemma dr_pat_result_join : forall W F aps a b c a1 b1 c1 a2 b2 c2 u v R,
  dr_pat_result F aps a a1 a2 u -> dr_pat_result F aps b b1 b2 v ->
  Par W a c Nom -> Par W b c Nom ->
  Par W a1 c1 R -> Par W b1 c1 R ->
  Par W a2 c2 R -> Par W b2 c2 R ->
  exists d, Par W u d R /\ Par W v d R.
Proof.
  intros W F aps a b c a1 b1 c1 a2 b2 c2 u v R P Q H1 H2 H3 H4 H5 H6.
  inversion P; inversion Q; subst.
  - exists (a_Pattern Nom c F aps c1 c2); auto using Par_Pattern.
  - exists c2; split; auto. eapply Par_PatternFalse; eauto using dr_value_par, dr_no_apps_path.
  - exists c2; split; auto. eapply Par_PatternFalse; eauto using dr_value_par, dr_no_apps_path.
  - exists c2; auto.
Qed.

Ltac dr_join_nested :=
  repeat match goal with
  | IH : forall y, Par ?W ?a y ?R -> exists d, Par ?W ?b d ?R /\ Par ?W y d ?R,
    K : Par ?W ?a ?c ?R |- _ =>
      let J := fresh "J" in pose proof (IH _ K) as J;
      clear IH;
      destruct J as (? & ? & ?)
  end.

Theorem confluence : forall W a a1 R,
  Par W a a1 R ->
  forall a2, Par W a a2 R -> exists b, Par W a1 b R /\ Par W a2 b R.
Proof.
  intros W a a1 R H. induction H; intros t K.
  - exists t; eauto using dr_par_refl_r.
  - destruct (dr_app_view _ _ _ _ _ _ K) as (u & v & Pa & Pb & S).
    destruct (IHPar1 _ Pa) as (c & P1 & Q1).
    destruct (IHPar2 _ Pb) as (d & P2 & Q2).
    eapply dr_app_result_join; eauto using dr_ar_beta.
  - destruct (dr_app_view _ _ _ _ _ _ K) as (u & v & Pa & Pb & S).
    destruct (IHPar1 _ Pa) as (c & P1 & Q1).
    destruct (IHPar2 _ Pb) as (d & P2 & Q2).
    eapply dr_app_result_join; eauto using dr_ar_app.
  - destruct (dr_capp_view _ _ _ _ K) as (u & P & S).
    destruct (IHPar _ P) as (c & P1 & Q1).
    eapply dr_capp_result_join; eauto using dr_cr_beta.
  - destruct (dr_capp_view _ _ _ _ K) as (u & P & S).
    destruct (IHPar _ P) as (c & P1 & Q1).
    eapply dr_capp_result_join; eauto using dr_cr_app.
  - destruct (dr_par_abs_inv _ _ _ _ _ K) as (u & M & -> & P).
    assert (J : forall x, x `notin` (L \u M) -> exists c,
        Par (x ~ Nom ++ W) (open_tm_wrt_tm a' (a_Var_f x)) c R /\
        Par (x ~ Nom ++ W) (open_tm_wrt_tm u (a_Var_f x)) c R).
    { intros x Hx. apply H0; [fsetdec|apply P; fsetdec]. }
    destruct (dr_join_bodies _ _ _ _ _ J) as (c & N & D).
    exists (a_UAbs rho c); split; eapply Par_Abs with (L := N); intros;
      specialize (D x H1); tauto.
  - inversion K; subst.
    + exists (a_Pi rho A' B'); split; eauto using dr_par_refl_r, Par_Pi.
    + destruct (IHPar _ H8) as (C & P & Q).
      assert (J : forall x, x `notin` (L \u L0) -> exists c,
          Par (x ~ Nom ++ W) (open_tm_wrt_tm B' (a_Var_f x)) c R /\
          Par (x ~ Nom ++ W) (open_tm_wrt_tm B'0 (a_Var_f x)) c R).
      { intros x Hx. apply H1; [fsetdec|apply H9; fsetdec]. }
      destruct (dr_join_bodies _ _ _ _ _ J) as (c & N & D).
      exists (a_Pi rho C c); split; eapply Par_Pi with (L := N); eauto;
        intros; specialize (D x ltac:(assumption)); tauto.
  - destruct (dr_par_cabs_inv _ _ _ _ K) as (u & -> & P).
    pick fresh c for L. specialize (H0 c Fr).
    pose proof (dr_par_co_body _ _ _ _ _ (H c Fr)) as Q.
    unfold open_tm_wrt_co in H0.
    rewrite (dr_scoped_co_id _ _ _ _ (dr_par_scoped_l _ _ _ _ Q)),
      (dr_scoped_co_id _ _ _ _ (dr_par_scoped_r _ _ _ _ Q)) in H0.
    destruct (H0 _ P) as (z & P1 & P2).
    exists (a_UCAbs z). auto using dr_par_cabs.
  - inversion K; subst.
    + exists (a_CPi (Eq a' b' A' R1) B'); split; eauto using dr_par_refl_r, Par_CPi.
    + pick fresh c for (L \u L0).
      assert (F1 : c `notin` L) by fsetdec.
      assert (F2 : c `notin` L0) by fsetdec.
      match goal with K : forall c, c `notin` L0 -> Par _ _ _ _ |- _ =>
        specialize (K c F2)
      end.
      specialize (H3 c F1).
      dr_join_nested.
      exists (a_CPi (Eq x1 x0 x2 R1) x); split;
        apply dr_par_cpi; try assumption; unfold open_tm_wrt_co in H3, H4.
      * pose proof (dr_par_scoped_l _ _ _ _ H3) as Hb; apply dr_scoped_co_open in Hb.
        now rewrite (dr_scoped_co_id _ _ _ _ Hb) in H3.
      * pose proof (dr_par_scoped_l _ _ _ _ H4) as Hb; apply dr_scoped_co_open in Hb.
        now rewrite (dr_scoped_co_id _ _ _ _ Hb) in H4.
  - dr_axiom_cases.
  - dr_axiom_cases.
    destruct (dr_app_view _ _ _ _ _ _ K) as (u & v & Pa & Pb & S).
    destruct (IHPar1 _ Pa) as (c & P1 & Q1).
    destruct (IHPar2 _ Pb) as (d & P2 & Q2).
    destruct (dr_par_fix_prefix _ _ _ _ H1) as (j & -> & Hj).
    eapply dr_app_result_join; eauto using dr_ar_fix.
  - dr_axiom_cases.
  - destruct (dr_pat_view _ _ _ _ _ _ _ _ K) as (u & v & w & Pa & Pb & Pc & S).
    destruct (IHPar1 _ Pa) as (c & P1 & Q1).
    destruct (IHPar2 _ Pb) as (d & P2 & Q2).
    destruct (IHPar3 _ Pc) as (e & P3 & Q3).
    eapply dr_pat_result_join; eauto using dr_pr_cong.
  - dr_axiom_cases.
  - destruct (dr_pat_view _ _ _ _ _ _ _ _ K) as (u & v & w & Pa & Pb & Pc & S).
    destruct (IHPar1 _ Pa) as (c & P1 & Q1).
    destruct (IHPar2 _ Pb) as (d & P2 & Q2).
    destruct (IHPar3 _ Pc) as (e & P3 & Q3).
    eapply dr_pat_result_join with (a := a') (b := u) (c := c) (a1 := b1') (b1 := v)
      (c1 := d) (a2 := b2') (b2 := w) (c2 := e); eauto using dr_pr_false.
Qed.

Lemma dr_scoped_instantiate : forall a u k, dr_scoped (S k) a -> dr_scoped 0 u ->
  dr_scoped k (open_tm_wrt_tm_rec k u a).
Proof.
  intros a u k Ha Hu. pick fresh x for (fv_tm_tm_tm a).
  rewrite <- (dr_open_fresh a k u x) by fsetdec.
  apply dr_scoped_subst; auto. now apply dr_scoped_open.
Qed.

(* Structural properties of the typing and equality judgments. *)

Scheme dr_wff_ind := Induction for PropWff Sort Prop
with dr_typ_ind := Induction for Typing Sort Prop
with dr_iso_ind := Induction for Iso Sort Prop
with dr_eq_ind := Induction for DefEq Sort Prop
with dr_ctx_ind := Induction for Ctx Sort Prop.
Combined Scheme dr_judgments_ind from dr_wff_ind, dr_typ_ind, dr_iso_ind, dr_eq_ind, dr_ctx_ind.

Definition dr_phi_scoped (phi : constraint) :=
  match phi with Eq a b A _ => dr_scoped 0 a /\ dr_scoped 0 b /\ dr_scoped 0 A end.

Definition dr_sort_scoped (s : sort) :=
  match s with Tm A => dr_scoped 0 A | Co phi => dr_phi_scoped phi end.

Local Hint Resolve dr_scoped_instantiate : core.

Ltac dr_scoped_binder :=
  match goal with
  | H : forall x : atom, x `notin` ?L -> _ |- dr_scoped 1 ?a =>
      let z := fresh "z" in let Hz := fresh "Hz" in destruct (atom_fresh L) as [z Hz];
      specialize (H z Hz);
      apply (proj1 (dr_scoped_open a 0 z)); tauto
  | H : forall x : atom, x `notin` ?L -> _ |- dr_scoped 0 ?a =>
      let z := fresh "z" in let Hz := fresh "Hz" in destruct (atom_fresh L) as [z Hz];
      specialize (H z Hz);
      apply (proj1 (dr_scoped_co_open a 0 0 z)); tauto
  end.

Lemma dr_judgments_scoped :
  (forall G phi, PropWff G phi -> dr_phi_scoped phi) /\
  (forall G a A, Typing G a A -> dr_scoped 0 a /\ dr_scoped 0 A) /\
  (forall G D phi psi, Iso G D phi psi -> dr_phi_scoped phi /\ dr_phi_scoped psi) /\
  (forall G D a b A R, DefEq G D a b A R -> dr_scoped 0 a /\ dr_scoped 0 b /\ dr_scoped 0 A) /\
  (forall G, Ctx G -> forall x s, binds x s G -> dr_sort_scoped s).
Proof.
  apply dr_judgments_ind; intros; simpl in *; unfold open_tm_wrt_tm, open_tm_wrt_co in *;
    try solve [intuition eauto 4].
  all: try solve [exfalso; eapply dr_no_sat; eauto].
  all: try solve [match goal with H : binds _ _ nil |- _ => contradiction end].
  all: try solve [match goal with H : _ = _ \/ binds _ _ _ |- _ =>
      destruct H as [H|H]; [inversion H; subst; simpl; tauto|eauto]
    end].
  all: try solve [repeat split; try tauto;
                  try (eapply dr_scoped_instantiate; tauto);
                  try dr_scoped_binder].
  all: try solve [repeat split; try tauto;
    match goal with H : forall x s, binds x s _ -> dr_sort_scoped s,
      K : binds _ _ _ |- _ => exact (H _ _ K) end].
  all: try solve [destruct phi || destruct phi1; simpl in *; repeat split; try tauto; dr_scoped_binder].
  all: try solve [repeat split; try tauto;
      match goal with |- dr_scoped 0 (open_tm_wrt_co_rec _ _ ?a) =>
        rewrite (dr_scoped_co_id a 0) by tauto; tauto end].
  all: try exact (H _ _ b0).
  all: match goal with K : binds _ _ (_ :: _) |- _ =>
    destruct K as [E|K]; [inversion E; subst; simpl; tauto|eauto]
  end.
Qed.

Definition dr_typ_scoped := proj1 (proj2 dr_judgments_scoped).
Definition dr_wff_scoped := proj1 dr_judgments_scoped.
Definition dr_eq_scoped := proj1 (proj2 (proj2 (proj2 dr_judgments_scoped))).

Lemma dr_judgments_ctx :
  (forall G phi, PropWff G phi -> Ctx G) /\
  (forall G a A, Typing G a A -> Ctx G) /\
  (forall G D phi psi, Iso G D phi psi -> Ctx G) /\
  (forall G D a b A R, DefEq G D a b A R -> Ctx G) /\
  (forall G, Ctx G -> uniq G).
Proof. apply dr_judgments_ind; intros; eauto using uniq_cons, uniq_nil. Qed.

Definition dr_typ_ctx := proj1 (proj2 dr_judgments_ctx).
Definition dr_wff_ctx := proj1 dr_judgments_ctx.
Definition dr_ctx_uniq := proj2 (proj2 (proj2 (proj2 dr_judgments_ctx))).

Lemma dr_ctx_nom_bind : forall G x A, binds x (Tm A) G -> binds x Nom (ctx_nom G).
Proof.
  induction G as [|[y [B|phi]] G IH]; intros x A H; simpl in *; try contradiction;
    destruct H as [H|H]; try discriminate; try (inversion H; subst; left; reflexivity);
    eauto.
Qed.

Lemma dr_ctx_nom_dom : forall G x, x `in` dom (ctx_nom G) -> x `in` dom G.
Proof.
  induction G as [|[y [A|phi]] G IH]; simpl; intros x H; auto.
  - destruct (x == y); [subst; fsetdec|]. apply AtomSetImpl.add_3 in H; auto.
Qed.

Lemma dr_ctx_nom_uniq : forall G, uniq G -> uniq (ctx_nom G).
Proof.
  intros G H; induction H; simpl; auto.
  destruct a; auto. apply uniq_cons; auto. intro K; eauto using dr_ctx_nom_dom.
Qed.

Lemma dr_judgments_role :
  (forall G phi, PropWff G phi -> match phi with Eq a b A R =>
    roleing (ctx_nom G) a R /\ roleing (ctx_nom G) b R /\ roleing (ctx_nom G) A Rep end) /\
  (forall G a A, Typing G a A -> forall R, roleing (ctx_nom G) a R) /\
  (forall G D phi psi, Iso G D phi psi -> True) /\
  (forall G D a b A R, DefEq G D a b A R -> True) /\
  (forall G, Ctx G -> uniq G).
Proof.
  apply dr_judgments_ind; intros; simpl in *;
    try solve [eauto using roleing, dr_ctx_nom_uniq, dr_ctx_uniq, dr_typ_ctx, uniq_cons, uniq_nil].
  all: try solve [eapply role_a_Var with (R := Nom); eauto using dr_ctx_nom_uniq, dr_ctx_uniq, dr_ctx_nom_bind].
  all: try solve [eapply role_a_Pi with (L := L); [apply H0 | intros x Hx; exact (H x Hx R)]].
  all: try solve [eapply role_a_Abs with (L := L); intros x Hx; exact (H x Hx R)].
  all: try solve [eapply role_a_CAbs with (L := L); intros x Hx; exact (H x Hx R)].
  all: try solve [destruct phi; simpl in *; eapply role_a_CPi with (L := L); intuition eauto].
  all: try solve [eapply role_a_TApp; eauto].
  all: try solve [apply role_a_App; [apply H | apply role_a_Bullet; eauto using dr_typ_ctx, dr_ctx_uniq, dr_ctx_nom_uniq]].
  all: exfalso; eauto using dr_no_sat.
Qed.

Definition dr_typ_role := proj1 (proj2 dr_judgments_role).

Definition dr_includes (G H : context) :=
  forall x s, binds x s G -> binds x s H.
Definition dr_set_includes (D E : available_props) := forall x, x `in` D -> x `in` E.

Lemma dr_includes_dom : forall G H, dr_includes G H -> dr_set_includes (dom G) (dom H).
Proof.
  intros G H K x Hx.
  assert (exists s, binds x s G) as [s B].
  { clear K. induction G as [|[y s] G IH]; simpl in Hx; [fsetdec|].
    destruct (x == y) as [->|N]; [exists s; now left|].
    apply AtomSetImpl.add_3 in Hx; auto.
    destruct (IH Hx) as [r Hr]. exists r; now right. }
  eauto using binds_In.
Qed.

Lemma dr_includes_cons : forall G H x s, dr_includes G H -> dr_includes (x ~ s ++ G) (x ~ s ++ H).
Proof.
  intros G H x s K y r [E|B]; [now left|right; now apply K].
Qed.

Local Hint Resolve dr_includes_cons dr_includes_dom : core.
Local Hint Constructors Typing DefEq Iso PropWff : dr_typ.

Lemma dr_bind_weaken : forall G H x s, dr_includes G H -> binds x s G -> binds x s H.
Proof. firstorder. Qed.
Lemma dr_mem_weaken : forall D E x, dr_set_includes D E -> x `in` D -> x `in` E.
Proof. firstorder. Qed.
Local Hint Resolve dr_bind_weaken dr_mem_weaken : core.

Ltac dr_weak_binder rule L :=
  match goal with C : Ctx ?G |- _ =>
    eapply rule with (L := L \u dom G); eauto 3 with dr_typ;
    let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
    match goal with IH : forall y, y `notin` L -> _ |- _ =>
      specialize (IH x ltac:(fsetdec));
      eapply IH; eauto 4 using E_ConsTm, E_ConsCo with dr_typ;
      eapply E_ConsTm || eapply E_ConsCo; eauto 3 with dr_typ; fsetdec
    end
  end.

Lemma dr_judgments_weak :
  (forall G phi, PropWff G phi -> forall H, Ctx H -> dr_includes G H -> PropWff H phi) /\
  (forall G a A, Typing G a A -> forall H, Ctx H -> dr_includes G H -> Typing H a A) /\
  (forall G D phi psi, Iso G D phi psi -> forall H E, Ctx H ->
    dr_includes G H -> dr_set_includes D E -> Iso H E phi psi) /\
  (forall G D a b A R, DefEq G D a b A R -> forall H E, Ctx H ->
    dr_includes G H -> dr_set_includes D E -> DefEq H E a b A R) /\
  (forall G, Ctx G -> True).
Proof.
  apply dr_judgments_ind; intros;
    try solve [eauto 3 with dr_typ];
    try solve [exfalso; eauto using dr_no_sat].
  all: try solve [dr_weak_binder E_Pi L].
  all: try solve [dr_weak_binder E_Abs L].
  all: try solve [dr_weak_binder E_CPi L].
  all: try solve [dr_weak_binder E_CAbs L].
  all: try solve [dr_weak_binder E_PiCong L].
  all: try solve [dr_weak_binder E_AbsCong L].
  all: try solve [dr_weak_binder E_CPiCong L].
  all: try solve [dr_weak_binder E_CAbsCong L].
  all: try solve [match goal with S : SatApp _ _ |- _ => exact (False_rect _ (dr_no_sat _ _ S)) end].
  all: first [
    solve [eapply E_Wff; eauto 5]
    | solve [eapply E_App; eauto 5]
    | solve [eapply E_TApp; eauto 5]
    | solve [eapply E_IApp; eauto 5]
    | solve [eapply E_Conv; eauto 5]
    | solve [eapply E_CApp; eauto 5]
    | solve [eapply E_PropCong; eauto 5]
    | solve [eapply E_IsoConv; eauto 5]
    | solve [eapply E_CPiFst; eauto 5]
    | solve [eapply E_Assn; eauto 5]
    | solve [eapply E_Beta; eauto 5]
    | solve [eapply E_Trans; eauto 5]
    | solve [eapply E_AppCong; eauto 5]
    | solve [eapply E_TAppCong; eauto 5]
    | solve [eapply E_IAppCong; eauto 5]
    | solve [eapply E_PiSnd; eauto 5]
    | solve [eapply E_CAppCong; eauto 5]
    | solve [eapply E_CPiSnd; eauto 5]
    | solve [eapply E_Cast; eauto 5]
    | solve [eapply E_EqConv; eauto 5]
    | solve [eapply E_LeftRel; eauto 5]
    | solve [eapply E_LeftIrrel; eauto 5]
    | solve [eapply E_Right; eauto 5]
    | solve [eapply E_CLeft; eauto 5]
    | idtac ].
  eapply E_LeftIrrel with (b := b) (b' := b') (F := F); eauto.
Qed.

Definition dr_wff_weak := proj1 dr_judgments_weak.
Definition dr_typ_weak := proj1 (proj2 dr_judgments_weak).
Definition dr_eq_weak := proj1 (proj2 (proj2 (proj2 dr_judgments_weak))).

Lemma dr_includes_push : forall (G : context) x s, dr_includes G (x ~ s ++ G).
Proof. intros G x s y r H. now right. Qed.
Lemma dr_subset_refl : forall D, dr_set_includes D D.
Proof. firstorder. Qed.
Local Hint Resolve dr_includes_push dr_subset_refl : core.

Lemma dr_subst_fv : forall a n u x y, dr_scoped n a ->
  y `in` fv_tm_tm_tm (tm_subst_tm_tm u x a) ->
  y `in` fv_tm_tm_tm a \/ y `in` fv_tm_tm_tm u.
Proof.
  fix IH 1; intros a n u x y Hs H;
    destruct a; simpl in *; try contradiction; try fsetdec;
    try destruct phi; try destruct R; simpl in *; try contradiction; try fsetdec.
  all: try match type of Hs with _ /\ _ = g_Triv => destruct Hs as [? ->]; simpl in H |- * end.
  all: try solve [match goal with H : context [if ?d then _ else _] |- _ =>
      destruct d; simpl in H; auto end].
  all: repeat match goal with H : _ `in` union _ _ |- _ =>
      apply AtomSetImpl.union_1 in H; destruct H
    end;
    first [solve [fsetdec] |
      match goal with H : ?y `in` fv_tm_tm_tm (tm_subst_tm_tm ?u ?x ?b) |- _ =>
        let J := fresh in
        assert (J : y `in` fv_tm_tm_tm b \/ y `in` fv_tm_tm_tm u)
          by (eapply IH; [first [eassumption|intuition eauto]|exact H]); fsetdec
      end].
Qed.

Lemma dr_fv_subst_fresh : forall a n u x, dr_scoped n a ->
  x `notin` fv_tm_tm_tm a -> tm_subst_tm_tm u x a = a.
Proof.
  fix IH 1; intros a n u x Hs H;
    destruct a; simpl in *; try contradiction; try reflexivity;
    try destruct phi; try destruct R; simpl in *; try contradiction; try reflexivity.
  all: try match type of Hs with _ /\ _ = g_Triv => destruct Hs as [? ->]; simpl in H |- * end.
  all: try solve [match goal with |- context [if ?d then _ else _] =>
      destruct d; [subst; fsetdec | reflexivity] end].
  all: repeat f_equal; (eapply IH; [first [eassumption|intuition eauto]|fsetdec]).
Qed.

Lemma dr_rolepath_subst : forall a Rs, RolePath a Rs ->
  forall u x, dr_scoped 0 a -> dr_scoped 0 u ->
  RolePath (tm_subst_tm_tm u x a) Rs.
Proof.
  intros a Rs H; induction H; intros u x Ha Hu; simpl in *;
    try solve [eauto using RolePath];
    constructor; intuition eauto using dr_scoped_subst, dr_scoped_lc.
Qed.

Lemma dr_beta_subst : forall a b R, Beta a b R ->
  forall u x, dr_scoped 0 a -> dr_scoped 0 u ->
  Beta (tm_subst_tm_tm u x a) (tm_subst_tm_tm u x b) R.
Proof.
  intros a b R H; inversion H; subst; intros u x Ha Hu.
  - simpl in Ha. destruct Ha as [Ha Hb].
    unfold open_tm_wrt_tm. rewrite (dr_subst_open_comm v 1 u x b0 0 Ha Hu).
    simpl. apply Beta_AppAbs.
    + eauto using dr_scoped_subst, dr_scoped_lc.
    + exact (dr_value_subst _ _ u x H1 Ha Hu).
  - simpl in Ha. destruct Ha as [Ha _].
    unfold open_tm_wrt_co. rewrite (dr_scoped_co_id _ _ _ _ Ha).
    rewrite <- (dr_scoped_co_id _ 0 0 g_Triv (dr_scoped_subst _ _ u x Ha Hu)).
    simpl. apply Beta_CAppCAbs.
    apply dr_scoped_lc. exact (dr_scoped_subst (a_UCAbs a') 0 u x Ha Hu).
  - dr_signature.
    match goal with Hr : Rename _ _ _ _ _ _, M : MatchSubst _ _ _ _ |- _ =>
      destruct (dr_match_rename _ _ _ _ Hr _ _ M) as (i & f & -> & -> & _)
    end.
    change (Beta (a_App (a_App (a_Fam Fix) (Rho Irrel) (tm_subst_tm_tm u x i))
      (Role Nom) (tm_subst_tm_tm u x f)) (dr_unfold (tm_subst_tm_tm u x f)) R).
    simpl in Ha. apply dr_beta_fix; intuition eauto using dr_scoped_subst, dr_scoped_lc.
  - match goal with S : SatApp _ _ |- _ => exact (False_rect _ (dr_no_sat _ _ S)) end.
  - simpl in *. destruct Ha as (Ha & H1s & H2s). apply Beta_PatternFalse;
      eauto using dr_value_subst, dr_scoped_subst, dr_scoped_lc, dr_no_apps_path.
Qed.

(* Transport of judgments across substitutions and contexts. *)

Definition dr_substitution := option (atom * tm).

Definition dr_tm (s : dr_substitution) (a : tm) :=
  match s with Some (x,u) => tm_subst_tm_tm u x a | None => a end.

Definition dr_phi (s : dr_substitution) (phi : constraint) :=
  match phi with Eq a b A R => Eq (dr_tm s a) (dr_tm s b) (dr_tm s A) R end.

Definition dr_support (s : dr_substitution) :=
  match s with Some (x,u) => {{x}} \u fv_tm_tm_tm u | None => empty end.

Definition dr_subst_ok (s : dr_substitution) :=
  match s with Some (_,u) => dr_scoped 0 u | None => True end.

Lemma dr_tm_scope : forall s a n, dr_subst_ok s -> dr_scoped n a -> dr_scoped n (dr_tm s a).
Proof. intros [[x u]|]; simpl; eauto using dr_scoped_subst. Qed.

Lemma dr_tm_var : forall s x, x `notin` dr_support s -> dr_tm s (a_Var_f x) = a_Var_f x.
Proof.
  intros [[y u]|] x H; [apply dr_subst_other_variable; simpl in H; fsetdec|reflexivity].
Qed.

Lemma dr_tm_open : forall s a u, dr_subst_ok s -> dr_scoped 1 a ->
  dr_tm s (open_tm_wrt_tm a u) = open_tm_wrt_tm (dr_tm s a) (dr_tm s u).
Proof.
  intros [[x v]|] a u Hs Ha; [exact (dr_subst_open_comm a 1 v x u 0 Ha Hs)|reflexivity].
Qed.

Lemma dr_tm_co_open : forall s a g, dr_subst_ok s -> dr_scoped 0 a ->
  dr_tm s (open_tm_wrt_co a g) = open_tm_wrt_co (dr_tm s a) g.
Proof.
  intros s a g Hs Ha. unfold open_tm_wrt_co.
  rewrite (dr_scoped_co_id a 0) by assumption.
  symmetry. apply dr_scoped_co_id with (n := 0). auto using dr_tm_scope.
Qed.

Lemma dr_tm_rho : forall s rho x a, x `notin` dr_support s -> dr_scoped 0 a ->
  RhoCheck rho x a -> RhoCheck rho x (dr_tm s a).
Proof.
  intros [[y u]|] rho x a Hx Ha H; inversion H; subst; try assumption; constructor; auto.
  intro N. simpl in Hx. pose proof (dr_subst_fv a 0 u y x Ha N); fsetdec.
Qed.

Lemma dr_tm_path : forall s a Rs, dr_subst_ok s -> dr_scoped 0 a ->
  RolePath a Rs -> RolePath (dr_tm s a) Rs.
Proof. intros [[x u]|]; simpl; eauto using dr_rolepath_subst. Qed.

Lemma dr_tm_casepath : forall s R a F, dr_subst_ok s -> dr_scoped 0 a ->
  CasePath R a F -> CasePath R (dr_tm s a) F.
Proof. intros [[x u]|]; simpl; eauto using dr_casepath_subst. Qed.

Lemma dr_tm_beta : forall s a b R, dr_subst_ok s -> dr_scoped 0 a ->
  Beta a b R -> Beta (dr_tm s a) (dr_tm s b) R.
Proof. intros [[x u]|]; simpl; eauto using dr_beta_subst. Qed.

Lemma dr_tm_heads : forall s,
  dr_tm s a_Star = a_Star /\ dr_tm s a_Bullet = a_Bullet /\
  (forall F, dr_tm s (a_Fam F) = a_Fam F) /\
  (forall a nu b, dr_tm s (a_App a nu b) = a_App (dr_tm s a) nu (dr_tm s b)) /\
  (forall rho a b, dr_tm s (a_Pi rho a b) = a_Pi rho (dr_tm s a) (dr_tm s b)) /\
  (forall rho a, dr_tm s (a_UAbs rho a) = a_UAbs rho (dr_tm s a)) /\
  (forall a, dr_tm s (a_UCAbs a) = a_UCAbs (dr_tm s a)) /\
  (forall a, dr_tm s (a_CApp a g_Triv) = a_CApp (dr_tm s a) g_Triv) /\
  (forall phi a, dr_tm s (a_CPi phi a) = a_CPi (dr_phi s phi) (dr_tm s a)).
Proof. intros [[]|]; repeat split; intros; try destruct phi; reflexivity. Qed.


Definition dr_formula (G : context) (D : available_props) (phi : constraint) :=
  match phi with Eq a b A R => DefEq G D a b A R end.

Definition dr_mapping (s : dr_substitution) (G H : context) :=
  Ctx H /\
  (forall x A, binds x (Tm A) G -> Typing H (dr_tm s (a_Var_f x)) (dr_tm s A)) /\
  (forall x phi, binds x (Co phi) G -> dr_formula H (dom H) (dr_phi s phi)).

Definition dr_available (s : dr_substitution) (G : context) (D : available_props)
                        (H : context) (E : available_props) :=
  forall x phi, binds x (Co phi) G -> x `in` D -> dr_formula H E (dr_phi s phi).

Lemma dr_map_ctx : forall s G H, dr_mapping s G H -> Ctx H.
Proof. firstorder. Qed.
Lemma dr_map_var : forall s G H x A, dr_mapping s G H ->
  binds x (Tm A) G -> Typing H (dr_tm s (a_Var_f x)) (dr_tm s A).
Proof. firstorder. Qed.
Lemma dr_map_assn : forall s G H D E x a b A R, dr_available s G D H E ->
  binds x (Co (Eq a b A R)) G -> x `in` D ->
  DefEq H E (dr_tm s a) (dr_tm s b) (dr_tm s A) R.
Proof. intros; exact (H0 _ _ H1 H2). Qed.

Lemma dr_dom_push : forall (G : context) x s, dr_set_includes (dom G) (dom (x ~ s ++ G)).
Proof. intros G x s y Hy. simpl; fsetdec. Qed.
Local Hint Resolve dr_dom_push dr_map_ctx : core.

Lemma dr_formula_weak : forall G D phi, dr_formula G D phi ->
  forall H E, Ctx H -> dr_includes G H -> dr_set_includes D E -> dr_formula H E phi.
Proof. intros G D [] H0; simpl in *; eauto using dr_eq_weak. Qed.

Lemma dr_map_tm_lift : forall s G H x A,
  dr_mapping s G H -> x `notin` (dr_support s \u dom H) ->
  Typing H (dr_tm s A) a_Star ->
  dr_mapping s (x ~ Tm A ++ G) (x ~ Tm (dr_tm s A) ++ H).
Proof.
  intros s G H x A [HC [HT HE]] Hx HA.
  assert (C : Ctx (x ~ Tm (dr_tm s A) ++ H)) by (apply E_ConsTm; auto; fsetdec).
  split; [exact C|]. split.
  - intros y B [K|K].
    + inversion K; subst. rewrite dr_tm_var by fsetdec.
      apply E_Var; auto.
    + eapply dr_typ_weak; eauto.
  - intros y phi [K|K]; [discriminate|].
    eapply dr_formula_weak; eauto.
Qed.

Lemma dr_map_co_lift : forall s G H x phi,
  dr_mapping s G H -> x `notin` dom H ->
  PropWff H (dr_phi s phi) ->
  dr_mapping s (x ~ Co phi ++ G) (x ~ Co (dr_phi s phi) ++ H).
Proof.
  intros s G H x phi [HC [HT HE]] Hx HA.
  assert (C : Ctx (x ~ Co (dr_phi s phi) ++ H)) by (apply E_ConsCo; auto).
  split; [exact C|]. split.
  - intros y B [K|K]; [discriminate|]. eapply dr_typ_weak; eauto.
  - intros y psi [K|K].
    + inversion K; subst. destruct psi. simpl. eapply E_Assn; [exact C|now left|simpl; fsetdec].
    + eapply dr_formula_weak; eauto.
Qed.

Lemma dr_avail_lift : forall s G H D E x S T,
  dr_available s G D H E -> Ctx (x ~ T ++ H) -> x `notin` D ->
  dr_available s (x ~ S ++ G) D (x ~ T ++ H) E.
Proof.
  intros s G H D E x S T K HC Hx y phi [B|B] Hy.
  - inversion B; subst; contradiction.
  - eapply dr_formula_weak; eauto.
Qed.

Lemma dr_avail_dom : forall s G H, dr_mapping s G H -> dr_available s G (dom G) H (dom H).
Proof. intros s G H [_ [_ K]] x phi B _; eauto. Qed.

Local Hint Resolve dr_map_tm_lift dr_map_co_lift dr_avail_lift dr_avail_dom : core.

Ltac dr_get_scopes :=
  repeat match goal with
  | T : Typing _ _ _ |- _ =>
      let S := fresh "scope" in
      pose proof (dr_typ_scoped _ _ _ T) as S;
      revert T
  | T : DefEq _ _ _ _ _ _ |- _ =>
      let S := fresh "scope" in
      pose proof (dr_eq_scoped _ _ _ _ _ _ T) as S;
      revert T
  | T : PropWff _ _ |- _ =>
      let S := fresh "scope" in
      pose proof (dr_wff_scoped _ _ T) as S;
      revert T
  end; intros; cbn [dr_scoped dr_phi_scoped] in *.

Lemma dr_tm_open_var : forall s a x, dr_subst_ok s -> dr_scoped 1 a ->
  x `notin` dr_support s ->
  dr_tm s (open_tm_wrt_tm a (a_Var_f x)) = open_tm_wrt_tm (dr_tm s a) (a_Var_f x).
Proof. intros; rewrite dr_tm_open, dr_tm_var by assumption; reflexivity. Qed.

Lemma dr_tm_fixty : forall s, dr_tm s FixTy = FixTy.
Proof.
  intros [[x u]|]; [apply dr_fv_subst_fresh with (n := 0)|reflexivity];
    unfold FixTy; simpl; try lia; fsetdec.
Qed.

Ltac dr_map_simpl s :=
  let K := fresh "heads" in pose proof (dr_tm_heads s) as K;
  let A := fresh "SStar" in let B := fresh "SBullet" in let C := fresh "SFam" in
  let D := fresh "SApp" in let E := fresh "SPi" in let F := fresh "SAbs" in
  let G := fresh "SCAbs" in let H := fresh "SCApp" in let I := fresh "SCPi" in
  destruct K as (A & B & C & D & E & F & G & H & I);
  rewrite ?D, ?E, ?F, ?G, ?H, ?I, ?A, ?B, ?C in *;
  cbn [dr_phi] in *.

Ltac dr_map_body_scoped :=
  first [solve [tauto] |
  match goal with
  | P : forall x : atom, x `notin` ?L -> _ |- _ =>
    let x := fresh "local" in let Hx := fresh "Hlocal" in
    destruct (atom_fresh L) as [x Hx]; specialize (P x Hx);
    dr_get_scopes; unfold open_tm_wrt_tm, open_tm_wrt_co in *;
    first [match goal with |- dr_scoped 1 ?a => apply (proj1 (dr_scoped_open a 0 x)); tauto end |
           match goal with |- dr_scoped 0 ?a => apply (proj1 (dr_scoped_co_open a 0 0 x)); tauto end]
  end].

Ltac dr_map_open :=
  repeat first [
    progress (rewrite ?dr_tm_open in * by (try assumption; tauto)) |
    progress (rewrite ?dr_tm_co_open in * by (try assumption; tauto)) ].

Ltac dr_map_binder rule s L target D :=
  let M := constr:(L \u dom target \u dr_support s \u D) in
  eapply rule with (L := M);
  try solve [eauto 5];
  let y := fresh "binder" in let Hy := fresh "Hbinder" in intros y Hy;
  repeat rewrite <- dr_tm_open_var by
    (first [assumption | solve [fsetdec] | dr_map_body_scoped]);
  repeat rewrite <- dr_tm_co_open by
    (first [assumption | dr_map_body_scoped]);
  first [
    match goal with
    | IH : forall x : atom, _ -> forall s : dr_substitution, _ |- _ =>
      let K := fresh "IHbinder" in
      pose proof (IH y ltac:(fsetdec) s) as K;
      dr_map_simpl s;
      eapply K; try solve [eauto 4];
      first [eapply dr_map_tm_lift | eapply dr_map_co_lift | eapply dr_avail_lift];
        try solve [eauto 4 | fsetdec |
          first [eapply E_ConsTm | eapply E_ConsCo]; try solve [eauto 4 | fsetdec]]
    end
  | eapply dr_tm_rho; [fsetdec | unfold open_tm_wrt_tm; eapply dr_scoped_instantiate;
                                [dr_map_body_scoped | exact I] | eauto] ].

Ltac dr_map_paths s :=
  match goal with OK : dr_subst_ok s |- _ =>
    repeat match goal with
    | P : CasePath ?r ?a ?F |- _ =>
      let K := fresh "mapped_path" in
      pose proof (dr_tm_casepath s r a F OK ltac:(cbn [dr_scoped]; tauto) P) as K;
      clear P; revert K
    | P : RolePath ?a ?Rs |- _ =>
      let K := fresh "mapped_path" in
      pose proof (dr_tm_path s a Rs OK ltac:(tauto) P) as K;
      clear P; revert K
    end; intros; dr_map_simpl s
  end.


Lemma dr_judgments_transport :
  (forall G phi, PropWff G phi -> forall s, dr_subst_ok s -> forall H,
    dr_mapping s G H -> PropWff H (dr_phi s phi)) /\
  (forall G a A, Typing G a A -> forall s, dr_subst_ok s -> forall H,
    dr_mapping s G H -> Typing H (dr_tm s a) (dr_tm s A)) /\
  (forall G D phi psi, Iso G D phi psi -> forall s, dr_subst_ok s -> forall H E,
    dr_mapping s G H -> dr_available s G D H E -> Iso H E (dr_phi s phi) (dr_phi s psi)) /\
  (forall G D a b A R, DefEq G D a b A R -> forall s, dr_subst_ok s -> forall H E,
    dr_mapping s G H -> dr_available s G D H E -> DefEq H E (dr_tm s a) (dr_tm s b) (dr_tm s A) R) /\
  (forall G, Ctx G -> True).
Proof.
  apply dr_judgments_ind; intros;
    try solve [exact I | match goal with K : SatApp _ _ |- _ => exact (False_rect _ (dr_no_sat _ _ K)) end].
  all: match goal with OK : dr_subst_ok ?s |- _ =>
    repeat match goal with IH : forall s : dr_substitution, dr_subst_ok s -> _ |- _ =>
      specialize (IH s OK)
    end;
    dr_get_scopes; dr_map_simpl s; dr_map_open
  end.
  all: try solve [eauto 4 using E_Star, dr_map_var, dr_map_assn].
  all: try solve [match goal with K : binds _ _ toplevel |- _ =>
    let K' := fresh in pose proof K as K'; apply dr_sig in K;
    destruct K as [? P]; subst; inversion P; subst; try discriminate;
    rewrite ?dr_tm_fixty in *; eapply E_Fam; eauto
  end].
  all: try solve [eapply E_Wff; eauto].
  all: try solve [eapply E_App; eauto].
  all: try solve [eapply E_TApp; eauto; eapply dr_tm_path; [eassumption|tauto|eassumption]].
  all: try solve [eapply E_IApp; eauto].
  all: try solve [eapply E_Conv; eauto].
  all: try solve [eapply E_CApp; eauto].
  all: try solve [eapply E_PropCong; eauto].
  all: try solve [eapply E_IsoConv; eauto].
  all: try solve [eapply E_CPiFst; eauto].
  all: try solve [eapply E_Refl; eauto].
  all: try solve [eapply E_Sym; eauto].
  all: try solve [eapply E_Trans; eauto].
  all: try solve [eapply E_Sub; eauto].
  all: try solve [eapply E_Beta; eauto; eapply dr_tm_beta; [eassumption|tauto|eassumption]].
  all: try solve [eapply E_AppCong; eauto].
  all: try solve [eapply E_TAppCong; eauto; eapply dr_tm_path; [eassumption|tauto|eassumption]].
  all: try solve [eapply E_IAppCong; eauto].
  all: try solve [eapply E_PiFst; eauto].
  all: try solve [eapply E_PiSnd; eauto].
  all: try solve [eapply E_CAppCong; eauto].
  all: try solve [eapply E_CPiSnd; eauto].
  all: try solve [eapply E_Cast; eauto].
  all: try solve [eapply E_EqConv; eauto].
  all: try solve [eapply E_IsoSnd; eauto].
  all: try solve [match goal with |- Typing ?V (a_Pi _ _ _) _ =>
    dr_map_binder E_Pi s L V empty
  end].
  all: try solve [match goal with |- Typing ?V (a_CPi _ _) _ =>
    destruct phi; cbn [dr_phi] in *; dr_map_binder E_CPi s L V empty
  end].
  all: try solve [match goal with |- Typing ?V (a_UCAbs _) _ =>
    dr_map_binder E_CAbs s L V empty
  end].
  all: try solve [match goal with |- DefEq ?V ?E (a_Pi _ _ _) _ _ _ =>
    dr_map_binder E_PiCong s L V D
  end].
  all: try solve [match goal with |- DefEq ?V ?E (a_CPi _ _) _ _ _ =>
    dr_map_binder E_CPiCong s L V D
  end].
  all: try solve [match goal with |- DefEq ?V ?E (a_UCAbs _) _ _ _ =>
    dr_map_binder E_CAbsCong s L V D
  end].
  all: try solve [match goal with |- Typing ?V (a_UAbs _ _) _ =>
    dr_map_binder E_Abs s L V empty
  end].
  all: try solve [match goal with |- DefEq ?V ?E (a_UAbs _ _) _ _ _ =>
    dr_map_binder E_AbsCong s L V D
  end].
  all: try (dr_map_paths s).
  all: try solve [eapply E_TAppCong with (Rs := Rs); eauto].
  all: try solve [eapply E_LeftRel with (F := F); eauto].
  all: try solve [eapply E_LeftIrrel with (F := F) (b := dr_tm s b) (b' := dr_tm s b'); eauto].
  all: try solve [eapply E_Right with (F := F); eauto].
  all: try solve [eapply E_CLeft with (F := F); eauto].
Qed.

Definition dr_typ_transport := proj1 (proj2 dr_judgments_transport).

Lemma dr_fv_open_contains : forall a n u k x,
  dr_scoped n a -> x `in` fv_tm_tm_tm a ->
  x `in` fv_tm_tm_tm (open_tm_wrt_tm_rec k u a).
Proof.
  fix IH 1; intros a n u k x Hs H;
    destruct a; simpl in *; try contradiction; try fsetdec;
    try destruct phi; try destruct R; simpl in *; try contradiction; try fsetdec.
  all: try match type of Hs with _ /\ _ = g_Triv => destruct Hs as [? ->]; simpl in H |- * end.
  all: repeat match goal with H : _ `in` union _ _ |- _ =>
      apply AtomSetImpl.union_1 in H; destruct H
    end;
    first [solve [fsetdec] |
      match goal with H : ?x `in` fv_tm_tm_tm ?b |- context [open_tm_wrt_tm_rec ?k ?u ?b] =>
        let J := fresh in
        assert (J : x `in` fv_tm_tm_tm (open_tm_wrt_tm_rec k u b))
          by (eapply IH; [first [eassumption|intuition eauto]|exact H]); fsetdec
      end].
Qed.

Lemma dr_fv_open_bound : forall a n u k x,
  dr_scoped n a -> x `in` fv_tm_tm_tm (open_tm_wrt_tm_rec k u a) ->
  x `in` fv_tm_tm_tm a \/ x `in` fv_tm_tm_tm u.
Proof.
  fix IH 1; intros a n u k x Hs H;
    destruct a; simpl in *; try contradiction; try fsetdec;
    try destruct phi; try destruct R; simpl in *; try contradiction; try fsetdec.
  all: try match type of Hs with _ /\ _ = g_Triv => destruct Hs as [? ->]; simpl in H |- * end.
  all: try solve [destruct (lt_eq_lt_dec n0 k) as [[|]|] in H; simpl in H; fsetdec].
  all: repeat match goal with H : _ `in` union _ _ |- _ =>
      apply AtomSetImpl.union_1 in H; destruct H
    end;
    first [solve [fsetdec] |
      match goal with H : ?x `in` fv_tm_tm_tm (open_tm_wrt_tm_rec ?k ?u ?b) |- _ =>
        let J := fresh in
        assert (J : x `in` fv_tm_tm_tm b \/ x `in` fv_tm_tm_tm u)
          by (eapply IH; [first [eassumption|intuition eauto]|exact H]); fsetdec
      end].
Qed.

Lemma dr_role_fv : forall W a R, roleing W a R ->
  forall x, x `in` fv_tm_tm_tm a -> x `in` dom W.
Proof.
  intros W a R H; induction H; intros y Hy; simpl in *; try fsetdec.
  - assert (y = x) by fsetdec. subst. eauto using binds_In.
  - pick fresh x for (L \u {{y}}).
    assert (K : x `notin` L) by fsetdec.
    pose proof (dr_role_scoped _ _ _ (H x K)) as Ha.
    unfold open_tm_wrt_tm in *. apply dr_scoped_open in Ha.
    specialize (H0 x K y (dr_fv_open_contains _ _ _ _ _ Ha Hy)); simpl in H0; fsetdec.
  - destruct (AtomSetImpl.union_1 Hy); eauto.
  - destruct (AtomSetImpl.union_1 Hy); eauto.
  - destruct (AtomSetImpl.union_1 Hy) as [P|Q]; eauto.
    pick fresh x for (L \u {{y}}).
    assert (K : x `notin` L) by fsetdec.
    pose proof (dr_role_scoped _ _ _ (H0 x K)) as Ha.
    unfold open_tm_wrt_tm in *. apply dr_scoped_open in Ha.
    specialize (H1 x K y (dr_fv_open_contains _ _ _ _ _ Ha Q)); simpl in H1; fsetdec.
  - pick fresh c for L.
    specialize (H2 c Fr). specialize (H3 c Fr y). unfold open_tm_wrt_co in *.
    pose proof (dr_role_scoped _ _ _ H2) as Ha. apply dr_scoped_co_open in Ha.
    rewrite (dr_scoped_co_id _ _ _ _ Ha) in H3.
    repeat (apply AtomSetImpl.union_1 in Hy; destruct Hy as [Hy|Hy]); eauto.
  - pick fresh c for L. specialize (H c Fr). specialize (H0 c Fr y).
    unfold open_tm_wrt_co in *.
    pose proof (dr_role_scoped _ _ _ H) as Ha. apply dr_scoped_co_open in Ha.
    rewrite (dr_scoped_co_id _ _ _ _ Ha) in H0. auto.
  - apply IHroleing; fsetdec.
  - repeat (apply AtomSetImpl.union_1 in Hy; destruct Hy as [Hy|Hy]); eauto.
Qed.

Lemma dr_typ_fv : forall G a A, Typing G a A ->
  forall x, x `in` fv_tm_tm_tm a -> x `in` dom G.
Proof. intros; eapply dr_ctx_nom_dom, dr_role_fv; [eapply (dr_typ_role _ _ _ H Nom)|eauto]. Qed.

Lemma dr_typ_subst_fresh : forall G a A, Typing G a A ->
  forall x u, x `notin` dom G -> tm_subst_tm_tm u x a = a.
Proof.
  intros. eapply dr_fv_subst_fresh with (n := 0).
  - exact (proj1 (dr_typ_scoped _ _ _ H)).
  - intro K; eauto using dr_typ_fv.
Qed.

Lemma dr_ctx_fresh_map : forall G, Ctx G ->
  forall x u z k, x `notin` dom G -> binds z k G ->
    match k with Tm A => tm_subst_tm_tm u x A = A
               | Co phi => dr_phi (Some (x,u)) phi = phi end.
Proof.
  intros G C; induction C; intros y u z k Hy B; [contradiction|..].
  - destruct B as [E|B].
    + inversion E; subst. eapply dr_typ_subst_fresh; eauto; simpl in Hy; fsetdec.
    + eapply IHC; eauto; simpl in Hy; fsetdec.
  - destruct B as [E|B].
    + inversion E; subst. inversion H; subst. simpl.
      repeat f_equal; eapply dr_typ_subst_fresh; eauto; simpl in Hy; fsetdec.
    + eapply IHC; eauto; simpl in Hy; fsetdec.
Qed.

Lemma dr_typ_insert : forall G x A a B u,
  Typing (x ~ Tm A ++ G) a B -> Typing G u A ->
  Typing G (tm_subst_tm_tm u x a) (tm_subst_tm_tm u x B).
Proof.
  intros G x A a B u T U.
  pose proof (dr_typ_ctx _ _ _ T) as C.
  assert (Props : Ctx G /\ Typing G A a_Star /\ x `notin` dom G) by (inversion C; subst; auto).
  destruct Props as (CG & AT & Fresh).
  assert (Map : dr_mapping (Some (x,u)) (x ~ Tm A ++ G) G).
  { split; [assumption|]. split.
    - intros y C0 [E|K].
      + inversion E; subst y C0. change (Typing G (tm_subst_tm_tm u x (a_Var_f x)) (tm_subst_tm_tm u x A)).
        rewrite dr_subst_variable, (dr_typ_subst_fresh G A a_Star) by assumption; exact U.
      + assert (x <> y) by (intro E; subst; apply Fresh; eauto using binds_In).
        change (Typing G (tm_subst_tm_tm u x (a_Var_f y)) (tm_subst_tm_tm u x C0)).
        rewrite dr_subst_other_variable by assumption.
        rewrite (dr_ctx_fresh_map G CG x u y (Tm C0)) by assumption.
        now apply E_Var.
    - intros y phi [E|K]; [discriminate|].
      rewrite (dr_ctx_fresh_map G CG x u y (Co phi)) by assumption.
      destruct phi. simpl. eapply E_Assn; eauto using binds_In. }
  exact (dr_typ_transport _ _ _ T (Some (x,u)) (proj1 (dr_typ_scoped _ _ _ U)) _ Map).
Qed.

Lemma dr_typ_drop_co : forall G c a b A R t T,
  Typing (c ~ Co (Eq a b A R) ++ G) t T -> DefEq G (dom G) a b A R ->
  Typing G t T.
Proof.
  intros G c a b A R t T H E.
  pose proof (dr_typ_ctx _ _ _ H) as C. inversion C; subst.
  assert (Map : dr_mapping None (c ~ Co (Eq a b A R) ++ G) G).
  { split; [assumption|]. split.
    - intros y B [Q|Q]; [discriminate|]. simpl. now apply E_Var.
    - intros y phi [Q|Q].
      + inversion Q; subst; exact E.
      + destruct phi; simpl. eapply E_Assn; eauto using binds_In. }
  exact (dr_typ_transport _ _ _ H None I _ Map).
Qed.

Lemma dr_typ_open : forall G a B A L u,
  (forall x, x `notin` L ->
    Typing (x ~ Tm A ++ G) (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x))) ->
  Typing G u A -> Typing G (open_tm_wrt_tm a u) (open_tm_wrt_tm B u).
Proof.
  intros G a B A L u H U.
  pick fresh x for (L \u fv_tm_tm_tm a \u fv_tm_tm_tm B).
  assert (Hx : x `notin` L) by fsetdec.
  pose proof (dr_typ_insert _ _ _ _ _ _ (H x Hx) U) as P.
  unfold open_tm_wrt_tm in *. rewrite !dr_open_fresh in P by fsetdec. exact P.
Qed.

Lemma dr_typ_co_open : forall G a B p q A R L,
  (forall c, c `notin` L ->
    Typing (c ~ Co (Eq p q A R) ++ G) (open_tm_wrt_co a (g_Var_f c)) (open_tm_wrt_co B (g_Var_f c))) ->
  DefEq G (dom G) p q A R -> Typing G (open_tm_wrt_co a g_Triv) (open_tm_wrt_co B g_Triv).
Proof.
  intros G a B p q A R L H E. pick fresh c for L.
  pose proof (dr_typ_drop_co _ _ _ _ _ _ _ _ (H c Fr) E) as T.
  destruct (dr_typ_scoped _ _ _ T) as [Ha Hb]. unfold open_tm_wrt_co in *.
  apply dr_scoped_co_open in Ha, Hb.
  rewrite (dr_scoped_co_id a 0), (dr_scoped_co_id B 0) in T by assumption.
  rewrite (dr_scoped_co_id a 0), (dr_scoped_co_id B 0) by assumption. exact T.
Qed.

(* Preservation under one-step reduction. *)

Lemma dr_fv_inclusion : forall a b R, reduction_in_one a b R -> dr_scoped 0 a ->
  dr_scoped 0 b /\ forall x, x `in` fv_tm_tm_tm b -> x `in` fv_tm_tm_tm a.
Proof.
  intros a b R H; induction H; intros Ha.
  - simpl in Ha |- *. split.
    + pick fresh x for L. apply (proj1 (dr_scoped_open a' 0 x)).
      apply (proj1 (H0 x Fr (proj2 (dr_scoped_open a 0 x) Ha))).
    + intros y Hy. pick fresh x for (L \u {{y}}).
      assert (F : x `notin` L) by fsetdec.
      destruct (H0 x F (proj2 (dr_scoped_open a 0 x) Ha)) as [Hs Hfv].
      unfold open_tm_wrt_tm in Hs, Hfv. apply dr_scoped_open in Hs.
      pose proof (Hfv y (dr_fv_open_contains _ _ _ _ _ Hs Hy)) as K.
      apply dr_fv_open_bound with (n := 1) in K; [simpl in K; fsetdec|exact Ha].
  - simpl in *. destruct Ha as [Ha Hb]. destruct (IHreduction_in_one Ha) as [Hs Hfv].
    repeat split; auto. intros y Hy.
    apply AtomSetImpl.union_1 in Hy. destruct Hy as [Hy|Hy]; [specialize (Hfv y Hy)|]; fsetdec.
  - simpl in *. destruct Ha as [Ha Hb]. destruct (IHreduction_in_one Ha) as [Hs Hfv].
    repeat split; auto. intros y Hy.
    apply AtomSetImpl.union_1 in Hy. destruct Hy as [Hy|Hy]; [specialize (Hfv y Hy)|]; fsetdec.
  - simpl in *. destruct Ha as (Ha & Hb & Hc). destruct (IHreduction_in_one Ha) as [Hs Hfv].
    repeat split; auto. intros y Hy.
    apply AtomSetImpl.union_1 in Hy. destruct Hy as [Hy|Hy]; [specialize (Hfv y Hy)|]; fsetdec.
  - destruct (dr_beta_inv _ _ _ H) as
      [(rho & v & arg & -> & ->)|[(v & -> & ->)|[(i & f & -> & ->)|(z & F & aps & c & d & -> & ->)]]].
    + simpl in Ha |- *. destruct Ha as [Ha Harg]. unfold open_tm_wrt_tm.
      split; [eauto using dr_scoped_instantiate|].
      intros x Hx. pose proof (dr_fv_open_bound _ 1 _ _ _ Ha Hx); fsetdec.
    + simpl in Ha |- *. destruct Ha as [Ha _]. unfold open_tm_wrt_co.
      rewrite (dr_scoped_co_id _ _ _ _ Ha). split; auto.
    + unfold dr_unfold, dr_prefix. simpl in *. intuition fsetdec.
    + simpl in *. intuition fsetdec.
Qed.

Lemma dr_unused_open : forall a u v x,
  dr_scoped 1 a -> x `notin` fv_tm_tm_tm a ->
  x `notin` fv_tm_tm_tm (open_tm_wrt_tm a (a_Var_f x)) ->
  open_tm_wrt_tm a u = open_tm_wrt_tm a v.
Proof.
  intros a u v x Ha Hx Hxo; unfold open_tm_wrt_tm in *.
  rewrite <- (dr_open_fresh a 0 u x), <- (dr_open_fresh a 0 v x) by assumption.
  pose proof (proj2 (dr_scoped_open a 0 x) Ha) as Ho.
  now rewrite (dr_fv_subst_fresh _ 0 u x Ho Hxo), (dr_fv_subst_fresh _ 0 v x Ho Hxo).
Qed.

Lemma dr_rolepath_nonempty : forall a Rs, RolePath a Rs -> Rs <> nil ->
  (forall b R, ~ reduction_in_one a b R) /\
  (forall rho body, a <> a_UAbs rho body) /\ (forall body, a <> a_UCAbs body).
Proof.
  intros a Rs H; induction H; intro Hr.
  all: try solve [dr_signature].
  all: try solve [exfalso; apply Hr; reflexivity].
  all: try solve [
    match goal with H : RolePath _ (_ :: _) |- _ =>
      let K := fresh in
      assert (K : forall a Rs, RolePath a Rs -> length Rs <= 1)
        by (intros a0 Rs0 P; induction P; dr_signature; simpl in *; lia);
      specialize (K _ _ H); simpl in K; exfalso; apply Hr; destruct Rs; [reflexivity|simpl in K; lia]
    end].
  all: repeat split; try discriminate.
  - intros z R S. inversion S; subst.
    match goal with H : Beta _ _ _ |- _ => destruct (dr_beta_inv _ _ _ H) as [(? & ? & ? & E & _)|[(? & E & _)|[(? & ? & E & _)|(? & ? & ? & ? & ? & E & _)]]]; discriminate end.
  - destruct (IHRolePath Hr) as (No & N1 & N2).
    intros z R S. inversion S; subst; try solve [match goal with K : reduction_in_one _ _ _ |- _ => exact (No _ _ K) end].
    match goal with H : Beta _ _ _ |- _ =>
      destruct (dr_beta_inv _ _ _ H) as
      [(rho & v & arg & E & _)|[(v & E & _)|[(i & f & E & _)|(t & F & Aps & p & q & E & _)]]];
      try discriminate; injection E; intros; subst; first [eapply N1; reflexivity|eapply N2; reflexivity]
    end.
  - destruct (IHRolePath Hr) as (No & N1 & N2).
    intros z R S. inversion S; subst; try solve [match goal with K : reduction_in_one _ _ _ |- _ => exact (No _ _ K) end].
    match goal with H : Beta _ _ _ |- _ =>
      destruct (dr_beta_inv _ _ _ H) as
      [(rho & v & arg & E & _)|[(v & E & _)|[(i & f & E & _)|(t & F & Aps & p & q & E & _)]]];
      try discriminate; injection E; intros; subst; first [eapply N1; reflexivity|eapply N2; reflexivity]
    end.
Qed.

Lemma dr_ctx_type : forall G, Ctx G -> forall x A, binds x (Tm A) G -> Typing G A a_Star.
Proof.
  intros G C; induction C; intros y B K; try contradiction.
  - destruct K as [E|K].
    + inversion E; subst. eapply dr_typ_weak; eauto using E_ConsTm.
    + eapply dr_typ_weak; eauto using E_ConsTm.
  - destruct K as [E|K]; [discriminate|]. eapply dr_typ_weak; eauto using E_ConsCo.
Qed.

Lemma dr_pi_type : forall G rho A B T, Typing G (a_Pi rho A B) T ->
  Typing G A a_Star /\ exists L, forall x, x `notin` L ->
    Typing (x ~ Tm A ++ G) (open_tm_wrt_tm B (a_Var_f x)) a_Star.
Proof.
  intros G rho A B T H. remember (a_Pi rho A B) as p eqn:E.
  induction H; inversion E; subst; eauto.
Qed.

Lemma dr_cpi_type : forall G phi B T, Typing G (a_CPi phi B) T ->
  PropWff G phi /\ exists L, forall c, c `notin` L ->
    Typing (c ~ Co phi ++ G) (open_tm_wrt_co B (g_Var_f c)) a_Star.
Proof.
  intros G phi B T H. remember (a_CPi phi B) as p eqn:E.
  induction H; inversion E; subst; eauto.
Qed.

Lemma dr_typ_regular : forall G t T, Typing G t T -> Typing G T a_Star.
Proof.
  intros G t T H; induction H; try solve [eauto using E_Star, dr_ctx_type].
  - eapply E_Pi with (L := L); eauto.
  - destruct (dr_pi_type _ _ _ _ _ IHTyping1) as [_ [L K]].
    eapply (dr_typ_open G B a_Star A L a); assumption.
  - destruct (dr_pi_type _ _ _ _ _ IHTyping1) as [_ [L K]].
    eapply (dr_typ_open G B a_Star A L a); assumption.
  - destruct (dr_pi_type _ _ _ _ _ IHTyping1) as [_ [L K]].
    eapply (dr_typ_open G B a_Star A L a); assumption.
  - apply E_Star; eauto using dr_typ_ctx, dr_wff_ctx.
  - eapply E_CPi with (L := L); eauto.
  - destruct (dr_cpi_type _ _ _ _ IHTyping) as [_ [L K]].
    eapply (dr_typ_co_open G B1 a_Star a b A R L); assumption.
  - eapply dr_typ_weak; eauto. intros x s K; contradiction.
  - eapply dr_typ_weak; eauto. intros x s K; contradiction.
Qed.

Lemma dr_abs_type : forall G rho a T, Typing G (a_UAbs rho a) T ->
  exists L A B, Typing G A a_Star /\
    (forall x, x `notin` L ->
      Typing (x ~ Tm A ++ G) (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x))) /\
    (forall x, x `notin` L -> RhoCheck rho x (open_tm_wrt_tm a (a_Var_f x))) /\
    DefEq G (dom G) (a_Pi rho A B) T a_Star Rep.
Proof.
  intros G rho a T H. remember (a_UAbs rho a) as p eqn:E.
  induction H; inversion E; subst.
  - exists L, A, B. repeat split; auto. apply E_Refl.
    eapply dr_typ_regular, E_Abs with (L := L); auto.
  - destruct (IHTyping1 eq_refl) as (L & U & V & P & Q & S & K).
    exists L, U, V; repeat split; eauto using E_Trans.
Qed.

Lemma dr_cabs_type : forall G a T, Typing G (a_UCAbs a) T ->
  exists L phi B, PropWff G phi /\
    (forall c, c `notin` L ->
      Typing (c ~ Co phi ++ G) (open_tm_wrt_co a (g_Var_f c)) (open_tm_wrt_co B (g_Var_f c))) /\
    DefEq G (dom G) (a_CPi phi B) T a_Star Rep.
Proof.
  intros G a T H. remember (a_UCAbs a) as p eqn:E.
  induction H; inversion E; subst.
  - destruct (IHTyping1 eq_refl) as (L & U & V & P & Q & K).
    exists L, U, V; repeat split; eauto using E_Trans.
  - exists L, phi, B. repeat split; auto. apply E_Refl.
    eapply dr_typ_regular, E_CAbs with (L := L); auto.
Qed.

Lemma dr_fix_type : forall G T, Typing G (a_Fam Fix) T ->
  DefEq G (dom G) FixTy T a_Star Rep.
Proof.
  intros G T H. remember (a_Fam Fix) as p eqn:E.
  induction H; inversion E; subst; try solve [dr_signature];
    try solve [eauto using E_Trans].
  assert (A = FixTy) by (pose proof (dr_sig _ _ H0) as [_ K]; inversion K; auto).
  subst. apply E_Refl. eapply dr_typ_regular; eauto using E_Fam.
Qed.

Lemma dr_prefix_type : forall G T, Typing G dr_prefix T ->
  exists a, Typing G a a_Star /\
    DefEq G (dom G) (a_Pi Rel (a_Pi Rel a a) a) T a_Star Rep.
Proof.
  intros G T H. remember dr_prefix as p eqn:E. unfold dr_prefix in E.
  induction H; inversion E; subst.
  - pose proof (dr_fix_type _ _ H) as K.
    assert (Tstar : Typing G a_Star a_Star) by (eauto using E_Star, dr_typ_ctx).
    assert (Ta : Typing G a a_Star).
    { eapply E_Conv; [exact H0| eapply E_PiFst; apply E_Sym; exact K |exact Tstar]. }
    exists a; split; [exact Ta|].
    change (DefEq G (dom G)
      (open_tm_wrt_tm (a_Pi Rel (a_Pi Rel (a_Var_b 0) (a_Var_b 1)) (a_Var_b 1)) a)
      (open_tm_wrt_tm B a) a_Star Rep).
    eapply E_PiSnd; [exact K|eauto using E_Refl].
  - destruct (IHTyping1 eq_refl) as [a [Ta K]].
    eauto using E_Trans.
Qed.

Lemma dr_term_beta_typed : forall G rho v u A B,
  Typing G (a_UAbs rho v) (a_Pi rho A B) -> Typing G u A ->
  Typing G (open_tm_wrt_tm v u) (open_tm_wrt_tm B u).
Proof.
  intros G rho v u A B T U.
  destruct (dr_abs_type _ _ _ _ T) as (L & A0 & B0 & TA & Body & Check & Eq).
  assert (U0 : Typing G u A0).
  { eapply E_Conv; [exact U|eapply E_PiFst; apply E_Sym; exact Eq|exact TA]. }
  eapply E_Conv with (A := open_tm_wrt_tm B0 u).
  - eapply dr_typ_open; eauto.
  - eapply E_PiSnd; [exact Eq|apply E_Refl; exact U0].
  - destruct (dr_pi_type _ _ _ _ _ (dr_typ_regular _ _ _ T)) as [_ [M HB]].
    exact (dr_typ_open G B a_Star A M u HB U).
Qed.

Lemma dr_irrel_erased : forall G v T, Typing G (a_UAbs Irrel v) T ->
  forall u w, open_tm_wrt_tm v u = open_tm_wrt_tm v w.
Proof.
  intros G v T H u w.
  destruct (dr_abs_type _ _ _ _ H) as (L & A & B & TA & Body & Check & Eq).
  pick fresh x for (L \u fv_tm_tm_tm v).
  assert (F : x `notin` L) by fsetdec.
  specialize (Check x F). inversion Check; subst.
  eapply dr_unused_open with (x := x); [exact (proj1 (dr_typ_scoped _ _ _ H))|fsetdec|eassumption].
Qed.

Lemma dr_co_beta_typed : forall G v a b A R B,
  Typing G (a_UCAbs v) (a_CPi (Eq a b A R) B) -> DefEq G (dom G) a b A R ->
  Typing G (open_tm_wrt_co v g_Triv) (open_tm_wrt_co B g_Triv).
Proof.
  intros G v a b A R B T E.
  destruct (dr_cabs_type _ _ _ T) as (L & [p q A0 R0] & B0 & W & Body & Eq).
  assert (E0 : DefEq G (dom G) p q A0 R0).
  { eapply E_Cast; [exact E|eapply E_CPiFst; apply E_Sym; exact Eq]. }
  eapply E_Conv with (A := open_tm_wrt_co B0 g_Triv).
  - eapply dr_typ_co_open; eauto.
  - eapply E_CPiSnd; eauto.
  - destruct (dr_cpi_type _ _ _ _ (dr_typ_regular _ _ _ T)) as [_ [M HB]].
    exact (dr_typ_co_open G B a_Star a b A R M HB E).
Qed.

Lemma dr_fix_typed : forall G f A B,
  Typing G dr_prefix (a_Pi Rel A B) -> Typing G f A ->
  Typing G (dr_unfold f) (open_tm_wrt_tm B f).
Proof.
  intros G f A B T F. destruct (dr_prefix_type _ _ T) as (a & Ta & E).
  assert (P : Typing G (a_Pi Rel a a) a_Star).
  { eapply E_Pi with (L := dom G); [|exact Ta].
    intros y Hy. unfold open_tm_wrt_tm.
    pose proof (proj1 (dr_typ_scoped _ _ _ Ta)) as Ha.
    rewrite (dr_scoped_open_id a 0) by exact Ha.
    eapply dr_typ_weak; eauto.
    apply E_ConsTm; eauto using dr_typ_ctx. }
  assert (F0 : Typing G f (a_Pi Rel a a)).
  { eapply E_Conv; [exact F|apply E_PiFst with (B1 := B) (B2 := a) (rho := Rel); now apply E_Sym|exact P]. }
  assert (Eo : DefEq G (dom G) a (open_tm_wrt_tm B f) a_Star Rep).
  { pose proof (E_PiSnd _ _ _ _ _ _ _ _ _ _ E (E_Refl _ _ _ _ _ F0)) as Q.
    unfold open_tm_wrt_tm in Q.
    now rewrite (dr_scoped_open_id a 0) in Q by exact (proj1 (dr_typ_scoped _ _ _ Ta)). }
  assert (Call : Typing G (a_App dr_prefix (Rho Rel) f) a).
  { eapply E_Conv; [eapply E_App; [exact T|exact F]|now apply E_Sym|exact Ta]. }
  unfold dr_unfold.
  assert (H : Typing G (a_App f (Rho Rel) (a_App dr_prefix (Rho Rel) f))
                    (open_tm_wrt_tm a (a_App dr_prefix (Rho Rel) f))).
  { eapply E_App; [exact F0|exact Call]. }
  unfold open_tm_wrt_tm in H. rewrite (dr_scoped_open_id a 0) in H by exact (proj1 (dr_typ_scoped _ _ _ Ta)).
  eapply E_Conv; [exact H|exact Eo|].
  exact (dr_typ_regular _ _ _ (E_App G dr_prefix f B A T F)).
Qed.

Lemma dr_irrel_arg : forall G a i T, Typing G (a_App a (Rho Irrel) i) T -> i = a_Bullet.
Proof.
  intros G a i T H. remember (a_App a (Rho Irrel) i) as p eqn:E.
  induction H; inversion E; subst; auto.
Qed.

Lemma dr_no_pattern_typing : forall G r a F aps b1 b2 T,
  ~ Typing G (a_Pattern r a F aps b1 b2) T.
Proof.
  intros G r a F aps b1 b2 T H.
  remember (a_Pattern r a F aps b1 b2) as p eqn:E.
  induction H; inversion E; subst; eauto using dr_no_sat.
  all: match goal with S : SatApp _ _ |- _ => exact (dr_no_sat _ _ S) end.
Qed.

Lemma dr_typ_beta : forall a b R, Beta a b R -> forall G T,
  Typing G a T -> Typing G b T.
Proof.
  intros a b R H G T Ty.
  destruct (dr_beta_inv _ _ _ H) as
    [(rho & v & u & -> & ->)|[(v & -> & ->)|[(i & f & -> & ->)|(z & F & aps & c & d & -> & ->)]]].
  - remember (a_App (a_UAbs rho v) (Rho rho) u) as p eqn:E.
    induction Ty; inversion E; subst;
      try solve [eauto using dr_term_beta_typed, E_Conv].
    rewrite (dr_irrel_erased _ _ _ Ty1 _ a). eauto using dr_term_beta_typed.
  - remember (a_CApp (a_UCAbs v) g_Triv) as p eqn:E.
    induction Ty; inversion E; subst; eauto using dr_co_beta_typed, E_Conv.
  - remember (a_App (a_App (a_Fam Fix) (Rho Irrel) i) (Role Nom) f) as p eqn:E.
    induction Ty; inversion E; subst; try solve [eauto using E_Conv].
    assert (i = a_Bullet) by (eapply dr_irrel_arg; eauto). subst.
    eauto using dr_fix_typed.
  - exfalso. eapply dr_no_pattern_typing; eauto.
Qed.

Lemma dr_preservation_conv : forall G D a b A B R,
  (Typing G b A /\ DefEq G D a b A R) ->
  DefEq G (dom G) A B a_Star Rep -> Typing G B a_Star ->
  Typing G b B /\ DefEq G D a b B R.
Proof. intros until R; intros [T E] E' T'; split; eauto using E_Conv, E_EqConv. Qed.

Theorem reduction_preservation : forall a a' R, reduction_in_one a a' R -> forall G A D,
      Typing G a A -> Typing G a' A /\ DefEq G D a a' A R.
Proof.
  intros a a' R H. induction H; intros G T D Ty.
  - destruct (dr_abs_type _ _ _ _ Ty) as (M & A & B & TA & Body & Check & Eq).
    eapply dr_preservation_conv; [|exact Eq|eauto using dr_typ_regular].
    assert (P : forall x, x `notin` (L \u M) ->
      Typing (x ~ Tm A ++ G) (open_tm_wrt_tm a' (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x)) /\
      DefEq (x ~ Tm A ++ G) D (open_tm_wrt_tm a (a_Var_f x))
           (open_tm_wrt_tm a' (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x)) R).
    { intros x Hx. eapply H0; [fsetdec|apply Body; fsetdec]. }
    assert (Check' : forall x, x `notin` (L \u M) -> RhoCheck Irrel x (open_tm_wrt_tm a' (a_Var_f x))).
    { intros x Hx.
      assert (FL : x `notin` L) by fsetdec. assert (FM : x `notin` M) by fsetdec.
      specialize (Check x FM). inversion Check; subst. apply Rho_IrrRel.
      pose proof (proj1 (dr_typ_scoped _ _ _ (Body x FM))) as Scope.
      destruct (dr_fv_inclusion _ _ _ (H x FL) Scope) as [_ K].
      intro Fv. eauto. }
    split.
    + eapply E_Abs with (L := L \u M); [intros x Hx; exact (proj1 (P x Hx))|exact TA|exact Check'].
    + eapply E_AbsCong with (L := L \u M); eauto.
      intros x Hx; exact (proj2 (P x Hx)).
  - remember (a_App a nu b) as p eqn:E.
    induction Ty; inversion E; subst; try solve [eauto using dr_preservation_conv].
    + destruct (IHreduction_in_one _ _ D Ty1) as [T Q].
      split; eauto using E_App, E_AppCong, E_Refl.
    + exfalso. eapply (proj1 (dr_rolepath_nonempty _ _ H1 ltac:(discriminate))); eauto.
    + destruct (IHreduction_in_one _ _ D Ty1) as [T Q].
      split; eauto using E_IApp, E_IAppCong.
  - remember (a_CApp a g_Triv) as p eqn:E.
    induction Ty; inversion E; subst; try solve [eauto using dr_preservation_conv].
    destruct (IHreduction_in_one _ _ D Ty) as [T Q].
    split; eauto using E_CApp, E_CAppCong.
  - exfalso. eapply dr_no_pattern_typing; eauto.
  - split; eauto using dr_typ_beta, E_Beta.
Qed.

(* Regularity of definitional equality. *)

Lemma dr_eq_at_dom : forall G D a b A R, DefEq G D a b A R -> DefEq G (dom G) a b A R.
Proof.
  intros G D a b A R H.
  pose proof (proj1 (proj2 (proj2 (proj2 dr_judgments_ctx))) _ _ _ _ _ _ H) as C.
  assert (M : dr_mapping None G G).
  { split; [exact C|]. split.
    - intros; simpl. eauto using E_Var.
    - intros y [] K; simpl. eauto using E_Assn, binds_In. }
  apply (proj1 (proj2 (proj2 (proj2 dr_judgments_transport))) _ _ _ _ _ _ H None I G (dom G) M).
  intros y [] K _; simpl. eauto using E_Assn, binds_In.
Qed.

Lemma dr_ctx_prop : forall G, Ctx G -> forall c phi, binds c (Co phi) G -> PropWff G phi.
Proof.
  intros G K; induction K; intros y p B; try contradiction.
  - destruct B as [B|B]; [discriminate|].
    eapply dr_wff_weak; eauto using E_ConsTm, dr_includes_push.
  - destruct B as [B|B].
    + inversion B; subst. eapply dr_wff_weak; eauto using E_ConsCo, dr_includes_push.
    + eapply dr_wff_weak; eauto using E_ConsCo, dr_includes_push.
Qed.

Lemma dr_judgments_regular :
  (forall G phi, PropWff G phi -> True) /\
  (forall G a A, Typing G a A -> True) /\
  (forall G D phi psi, Iso G D phi psi -> PropWff G phi /\ PropWff G psi) /\
  (forall G D a b A R, DefEq G D a b A R -> Typing G a A /\ Typing G b A) /\
  (forall G, Ctx G -> True).
Proof.
  apply dr_judgments_ind; intros; try exact I;
    try solve [intuition eauto 3 using E_Wff, dr_typ_regular, E_Var, E_Conv, E_Refl, E_CApp, E_IApp];
    try solve [exfalso; match goal with S : SatApp _ _ |- _ => exact (dr_no_sat _ _ S) end].
  all: try solve [split; eapply dr_cpi_type; tauto].
  all: try solve [
    match goal with K : PropWff _ (Eq _ _ _ _) |- _ => inversion K; subst; auto end].
  all: try solve [
    match goal with K : PropWff _ (Eq _ _ _ _) /\ PropWff _ (Eq _ _ _ _) |- _ =>
      destruct K as [K1 K2]; inversion K2; subst; auto
    end].
  all: try solve [split; eapply dr_pi_type; tauto].
  all: try solve [
    match goal with K : PropWff _ (Eq _ _ _ _) /\ PropWff _ (Eq _ _ _ _) |- _ =>
      destruct K as [K1 K2]; inversion K1; inversion K2; subst; auto
    end].
  all: try solve [
    match goal with K : Ctx ?G, B : binds ?c (Co ?p) ?G |- _ =>
      let W := fresh in assert (W : PropWff G p)
        by (revert c p B; induction K; intros z p B; try contradiction;
          destruct B as [B|B];
          [try discriminate; inversion B; subst; eapply dr_wff_weak; eauto using E_ConsCo
          |eapply dr_wff_weak; eauto using E_ConsTm, E_ConsCo]);
      inversion W; subst; auto
    end].
  all: try solve [split; eapply E_Abs with (L := L); eauto; intros; firstorder].
  all: try solve [split; eapply E_CAbs with (L := L); eauto; intros; firstorder].
  all: try solve [
    match goal with |- Typing _ (a_App _ (Role _) _) _ /\ _ =>
      split; [eapply E_TApp with (Rs := Rs); intuition eauto|assumption]
    end].
  all: try solve [
    match goal with |- Typing ?G (a_App ?a1 (Rho Rel) ?a2) _ /\ Typing ?G (a_App ?b1 (Rho Rel) ?b2) _ =>
      destruct H as [T1 T2]; destruct H0 as [U1 U2];
      split; [eapply E_App; eauto|];
      let Te := fresh in
      pose proof (E_App G b1 b2 B A T2 U2) as Te;
      eapply E_Conv; [exact Te| |eauto using dr_typ_regular, E_App];
      eapply E_PiSnd; [apply E_Refl; eauto using dr_typ_regular|apply E_Sym, dr_eq_at_dom; eauto]
    end].
  all: try solve [
    match goal with |- Typing ?G (open_tm_wrt_co ?B1 g_Triv) _ /\ Typing ?G (open_tm_wrt_co ?B2 g_Triv) _ =>
      destruct H as [T1 T2];
      destruct (dr_cpi_type _ _ _ _ T1) as [_ [L1 K1]];
      destruct (dr_cpi_type _ _ _ _ T2) as [_ [L2 K2]];
      split; eapply dr_typ_co_open; eauto
    end].
  all: try solve [
    match goal with |- Typing ?G (open_tm_wrt_tm ?B1 ?a1) _ /\ Typing ?G (open_tm_wrt_tm ?B2 ?a2) _ =>
      destruct H as [T1 T2]; destruct H0 as [U1 U2];
      destruct (dr_pi_type _ _ _ _ _ T1) as [TA1 [L1 K1]];
      destruct (dr_pi_type _ _ _ _ _ T2) as [TA2 [L2 K2]];
      split; [eapply dr_typ_open; eauto |];
      eapply dr_typ_open; [exact K2|];
      eapply E_Conv; [exact U2| |exact TA2];
      eapply E_Sub; [eapply E_PiFst; eauto using dr_eq_at_dom|auto]
    end].
  - destruct H as [P Q].
    split; [exact (proj1 (dr_cpi_type _ _ _ _ P)) | exact (proj1 (dr_cpi_type _ _ _ _ Q))].
  - assert (W : PropWff G (Eq a b A R)) by (eapply dr_ctx_prop; eassumption).
    inversion W; subst; auto.
  - destruct H as [T1 T2]. destruct H0 as [U1 U2].
    pose proof (E_App G a1 a2 B A T1 U1) as P.
    pose proof (E_App G b1 b2 B A T2 U2) as Q.
    split; [exact P|].
    eapply E_Conv; [exact Q| |exact (dr_typ_regular _ _ _ P)].
    eapply E_PiSnd with (B1 := B) (B2 := B) (A1 := A) (A2 := A) (rho := Rel).
    + apply E_Refl. exact (dr_typ_regular _ _ _ T1).
    + apply E_Sym, dr_eq_at_dom with (D := D). assumption.
  - destruct H as [P Q].
    split; [exact (proj1 (dr_pi_type _ _ _ _ _ P)) | exact (proj1 (dr_pi_type _ _ _ _ _ Q))].
  - destruct H as [T1 T2]; destruct H0 as [U1 U2].
    destruct (dr_pi_type _ _ _ _ _ T1) as [TA1 [L1 K1]].
    destruct (dr_pi_type _ _ _ _ _ T2) as [TA2 [L2 K2]].
    split.
    + exact (dr_typ_open G B1 a_Star A1 L1 a1 K1 U1).
    + apply (dr_typ_open G B2 a_Star A2 L2 a2 K2).
      eapply E_Conv; [exact U2| |exact TA2].
      eapply E_Sub with (R1 := R); [eapply E_PiFst; apply dr_eq_at_dom with (D := D); eassumption|auto].
  - destruct H as [T1 T2].
    destruct (dr_cpi_type _ _ _ _ T1) as [_ [L1 K1]].
    destruct (dr_cpi_type _ _ _ _ T2) as [_ [L2 K2]].
    split.
    + eapply (dr_typ_co_open G B1 a_Star _ _ _ _ L1); eassumption.
    + eapply (dr_typ_co_open G B2 a_Star _ _ _ _ L2); eassumption.
Qed.

Definition dr_eq_regular := proj1 (proj2 (proj2 (proj2 dr_judgments_regular))).

(* Joinability and soundness of definitional equality. *)

Inductive dr_steps (W : role_context) (R : role) : tm -> tm -> Prop :=
| dr_steps_refl : forall a, roleing W a R -> dr_steps W R a a
| dr_steps_step : forall a b c, Par W a b R -> dr_steps W R b c -> dr_steps W R a c.

Local Hint Constructors dr_steps : core.

Definition dr_join W R a b := exists c, dr_steps W R a c /\ dr_steps W R b c.

Lemma dr_steps_l : forall W R a b, dr_steps W R a b -> roleing W a R.
Proof. intros W R a b H; inversion H; eauto using dr_par_role_l. Qed.

Lemma dr_steps_r : forall W R a b, dr_steps W R a b -> roleing W b R.
Proof. intros W R a b H; induction H; auto. Qed.

Lemma dr_steps_cat : forall W R a b c, dr_steps W R a b -> dr_steps W R b c -> dr_steps W R a c.
Proof. intros W R a b c H; induction H; eauto. Qed.

Lemma dr_steps_map : forall W R V S (f : tm -> tm),
  (forall a b, Par W a b R -> Par V (f a) (f b) S) ->
  forall a b, dr_steps W R a b -> dr_steps V S (f a) (f b).
Proof.
  intros W R V S f H a b K. induction K.
  - apply dr_steps_refl. eapply dr_par_role_l, H, Par_Refl; exact H0.
  - eauto.
Qed.

Lemma dr_steps_single : forall W R a b, Par W a b R -> dr_steps W R a b.
Proof. eauto using dr_par_role_r. Qed.

Lemma dr_steps_strip : forall W R a b c, dr_steps W R a b -> Par W a c R ->
  exists d : tm, Par W b d R /\ dr_steps W R c d.
Proof.
  intros W R a b c H; revert c; induction H; intros z Q.
  - eauto using dr_par_role_r.
  - destruct (confluence _ _ _ _ H _ Q) as (d & P & S).
    destruct (IHdr_steps _ P) as (e & K & L).
    exists e; split; eauto.
Qed.

Lemma dr_steps_diamond : forall W R a b c, dr_steps W R a b -> dr_steps W R a c ->
  dr_join W R b c.
Proof.
  intros W R a b c H K. revert b H; induction K; intros d P.
  - unfold dr_join; eauto using dr_steps_r.
  - destruct (dr_steps_strip _ _ _ _ _ P H) as (e & H1 & H2).
    destruct (IHK _ H2) as (f & H3 & H4).
    exists f; eauto.
Qed.

Lemma dr_join_refl : forall W R a, roleing W a R -> dr_join W R a a.
Proof. unfold dr_join; eauto. Qed.

Lemma dr_join_sym : forall W R a b, dr_join W R a b -> dr_join W R b a.
Proof. unfold dr_join; firstorder. Qed.

Lemma dr_join_trans : forall W R a b c, dr_join W R a b -> dr_join W R b c -> dr_join W R a c.
Proof.
  intros W R a b c (d & P & Q) (e & H & K).
  destruct (dr_steps_diamond _ _ _ _ _ Q H) as (f & F & F').
  exists f; eauto using dr_steps_cat.
Qed.

Lemma dr_join_map : forall W R V S (f : tm -> tm),
  (forall a b, Par W a b R -> Par V (f a) (f b) S) ->
  forall a b, dr_join W R a b -> dr_join V S (f a) (f b).
Proof. intros W R V S f H a b (c & P & Q); exists (f c); eauto using dr_steps_map. Qed.

Lemma dr_join_promote : forall W a b, dr_join W Nom a b -> dr_join W Rep a b.
Proof. intros. apply (dr_join_map W Nom W Rep (fun z => z)); auto using dr_par_promote. Qed.

Lemma dr_join_role_l : forall W R a b, dr_join W R a b -> roleing W a R.
Proof. intros W R a b (c & H & _); eauto using dr_steps_l. Qed.

Lemma dr_join_role_r : forall W R a b, dr_join W R a b -> roleing W b R.
Proof. intros W R a b (c & _ & H); eauto using dr_steps_l. Qed.

Lemma dr_join_app : forall W R nu a b c d,
  dr_join W R a b -> dr_join W (app_role nu R) c d ->
  dr_join W R (a_App a nu c) (a_App b nu d).
Proof.
  intros W R nu a b c d H K.
  eapply dr_join_trans with (b := a_App b nu c).
  - eapply (dr_join_map W R W R (fun x => a_App x nu c)); [|exact H].
    intros; apply Par_App; eauto using Par_Refl, dr_join_role_l.
  - eapply (dr_join_map W (app_role nu R) W R (fun x => a_App b nu x)); [|exact K].
    intros; apply Par_App; eauto using Par_Refl, dr_join_role_r.
Qed.

Lemma dr_join_capp : forall W R a b, dr_join W R a b ->
  dr_join W R (a_CApp a g_Triv) (a_CApp b g_Triv).
Proof. intros; eapply (dr_join_map W R W R (fun x => a_CApp x g_Triv)); eauto using Par_CApp. Qed.

Lemma dr_join_cabs : forall W R a b, dr_join W R a b ->
  dr_join W R (a_UCAbs a) (a_UCAbs b).
Proof. intros; eapply (dr_join_map W R W R a_UCAbs); eauto using dr_par_cabs. Qed.

Lemma dr_join_cpi : forall W R S a b A B p q P Q,
  dr_join W S a p -> dr_join W S b q -> dr_join W Rep A P -> dr_join W R B Q ->
  dr_join W R (a_CPi (Eq a b A S) B) (a_CPi (Eq p q P S) Q).
Proof.
  intros W R S a b A B p q P Q (a' & Ha & Hp) (b' & Hb & Hq) (A' & HA & HP) (B' & HB & HQ).
  exists (a_CPi (Eq a' b' A' S) B'); split.
  - eapply dr_steps_cat.
    + eapply (dr_steps_map W S W R (fun x => a_CPi (Eq x b A S) B)); [|exact Ha].
      intros; apply dr_par_cpi; eauto using Par_Refl, dr_steps_l.
    + eapply dr_steps_cat.
      * eapply (dr_steps_map W S W R (fun x => a_CPi (Eq a' x A S) B)); [|exact Hb].
        intros; apply dr_par_cpi; eauto using Par_Refl, dr_steps_l, dr_steps_r.
      * eapply dr_steps_cat.
        -- eapply (dr_steps_map W Rep W R (fun x => a_CPi (Eq a' b' x S) B)); [|exact HA].
           intros; apply dr_par_cpi; eauto using Par_Refl, dr_steps_l, dr_steps_r.
        -- eapply (dr_steps_map W R W R (fun x => a_CPi (Eq a' b' A' S) x)); [|exact HB].
           intros; apply dr_par_cpi; eauto using Par_Refl, dr_steps_r.
  - eapply dr_steps_cat.
    + eapply (dr_steps_map W S W R (fun x => a_CPi (Eq x q P S) Q)); [|exact Hp].
      intros; apply dr_par_cpi; eauto using Par_Refl, dr_steps_l.
    + eapply dr_steps_cat.
      * eapply (dr_steps_map W S W R (fun x => a_CPi (Eq a' x P S) Q)); [|exact Hq].
        intros; apply dr_par_cpi; eauto using Par_Refl, dr_steps_l, dr_steps_r.
      * eapply dr_steps_cat.
        -- eapply (dr_steps_map W Rep W R (fun x => a_CPi (Eq a' b' x S) Q)); [|exact HP].
           intros; apply dr_par_cpi; eauto using Par_Refl, dr_steps_l, dr_steps_r.
        -- eapply (dr_steps_map W R W R (fun x => a_CPi (Eq a' b' A' S) x)); [|exact HQ].
           intros; apply dr_par_cpi; eauto using Par_Refl, dr_steps_r.
Qed.

Lemma dr_close_left : forall a n k x,
  dr_scoped n a -> x `notin` fv_tm_tm_tm a ->
  dr_close k x (open_tm_wrt_tm_rec k (a_Var_f x) a) = a.
Proof.
  fix IH 1; intros a n k x Ha Hx; destruct a; simpl in *; try contradiction;
    try destruct phi; try destruct R; simpl in *; try contradiction; try reflexivity.
  all: try solve [try match type of Ha with _ /\ _ = g_Triv => destruct Ha as [? ->] end; simpl; repeat f_equal;
    (eapply IH; [first [eassumption|intuition eauto]|fsetdec])].
  - destruct (lt_eq_lt_dec n0 k) as [[H|H]|H]; cbn -[lt_dec].
    + destruct (lt_dec n0 k); [reflexivity|lia].
    + match goal with |- context [if ?d then _ else _] => destruct d; [subst; reflexivity|congruence] end.
    + destruct (lt_dec (n0 - 1) k); [lia|]. f_equal; lia.
  - match goal with |- context [if ?d then _ else _] => destruct d; [subst; fsetdec|reflexivity] end.
Qed.

Lemma dr_par_rename : forall W x y a b R,
  x `notin` dom W -> y `notin` dom W -> x <> y ->
  Par (x ~ Nom ++ W) a b R ->
  Par (y ~ Nom ++ W) (tm_subst_tm_tm (a_Var_f y) x a) (tm_subst_tm_tm (a_Var_f y) x b) R.
Proof.
  intros W x y a b R Hx Hy N P.
  assert (U : uniq W) by (pose proof (dr_par_uniq _ _ _ _ P); inversion H; auto).
  eapply dr_par_subst; [exact P| |].
  - apply Par_Refl; eapply role_a_Var with (R := Nom); auto using uniq_cons.
  - apply dr_extends_cons; [apply dr_par_extends_push; auto|simpl; fsetdec].
Qed.

Lemma dr_par_close_body : forall W R x a b, x `notin` dom W ->
  Par (x ~ Nom ++ W) a b R ->
  forall y, y `notin` (dom W \u {{x}}) ->
  Par (y ~ Nom ++ W) (open_tm_wrt_tm (dr_close 0 x a) (a_Var_f y))
                    (open_tm_wrt_tm (dr_close 0 x b) (a_Var_f y)) R.
Proof.
  intros W R x a b Hx P y Hy. unfold open_tm_wrt_tm.
  rewrite (dr_close_open a 0), (dr_close_open b 0) by eauto using dr_par_scoped_l, dr_par_scoped_r.
  eapply dr_par_rename; [exact Hx|fsetdec|fsetdec|exact P].
Qed.

Lemma dr_join_abs : forall W x rho a b R,
  x `notin` dom W -> x `notin` (fv_tm_tm_tm a \u fv_tm_tm_tm b) ->
  dr_join (x ~ Nom ++ W) R (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm b (a_Var_f x)) ->
  dr_join W R (a_UAbs rho a) (a_UAbs rho b).
Proof.
  intros W x rho a b R Hx HF P.
  assert (R1 : dr_scoped 1 a).
  { unfold open_tm_wrt_tm in P. eapply (proj1 (dr_scoped_open a 0 x)); eauto using dr_role_scoped, dr_join_role_l. }
  assert (R2 : dr_scoped 1 b).
  { unfold open_tm_wrt_tm in P. eapply (proj1 (dr_scoped_open b 0 x)); eauto using dr_role_scoped, dr_join_role_r. }
  pose proof (dr_join_map _ _ _ R (fun z => a_UAbs rho (dr_close 0 x z))
    ltac:(intros; eapply Par_Abs with (L := dom W \u {{x}}); eauto using dr_par_close_body) _ _ P) as K.
  simpl in K. unfold open_tm_wrt_tm in K.
  rewrite (dr_close_left a 1), (dr_close_left b 1) in K by (auto; fsetdec). exact K.
Qed.

Lemma dr_join_pi : forall W x rho A B A' B' R,
  x `notin` dom W -> x `notin` (fv_tm_tm_tm B \u fv_tm_tm_tm B') ->
  dr_join W R A A' ->
  dr_join (x ~ Nom ++ W) R (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x)) ->
  dr_join W R (a_Pi rho A B) (a_Pi rho A' B').
Proof.
  intros W x rho A B A' B' R Hx HF P Q.
  assert (R1 : dr_scoped 1 B).
  { unfold open_tm_wrt_tm in Q. eapply (proj1 (dr_scoped_open B 0 x)); eauto using dr_role_scoped, dr_join_role_l. }
  assert (R2 : dr_scoped 1 B').
  { unfold open_tm_wrt_tm in Q. eapply (proj1 (dr_scoped_open B' 0 x)); eauto using dr_role_scoped, dr_join_role_r. }
  eapply dr_join_trans.
  - pose proof (dr_join_map _ _ _ R (fun z => a_Pi rho A (dr_close 0 x z))
      ltac:(intros; eapply Par_Pi with (L := dom W \u {{x}});
        eauto using dr_par_close_body, Par_Refl, dr_join_role_l) _ _ Q) as K.
    simpl in K. unfold open_tm_wrt_tm in K.
    rewrite (dr_close_left B 1), (dr_close_left B' 1) in K by (auto; fsetdec). exact K.
  - eapply (dr_join_map W R W R (fun z => a_Pi rho z B')); [|exact P].
    intros a b H. eapply Par_Pi with (L := dom W \u {{x}}); [exact H|].
    intros y Hy.
    pose proof (dr_join_role_r _ _ _ _ Q) as T.
    pose proof (dr_par_rename _ _ y _ _ _ Hx ltac:(fsetdec) ltac:(fsetdec) (Par_Refl _ _ _ T)) as K.
    unfold open_tm_wrt_tm in *.
    rewrite !dr_open_fresh in K by fsetdec. exact K.
Qed.

Lemma dr_par_body_fresh : forall W R a b L x,
  x `notin` dom W ->
  (forall y, y `notin` L -> Par (y ~ Nom ++ W)
    (open_tm_wrt_tm a (a_Var_f y)) (open_tm_wrt_tm b (a_Var_f y)) R) ->
  Par (x ~ Nom ++ W) (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm b (a_Var_f x)) R.
Proof.
  intros W R a b L x Hx P.
  pick fresh y for (L \u dom W \u fv_tm_tm_tm a \u fv_tm_tm_tm b \u {{x}}).
  assert (F : y `notin` L) by fsetdec.
  pose proof (dr_par_rename W y x _ _ _ ltac:(fsetdec) Hx ltac:(fsetdec) (P y F)) as K.
  unfold open_tm_wrt_tm in *. rewrite !dr_open_fresh in K by fsetdec. exact K.
Qed.

Lemma dr_par_pi_view : forall W rho A B t R,
  Par W (a_Pi rho A B) t R ->
  exists A' B' L, t = a_Pi rho A' B' /\ Par W A A' R /\
    forall x, x `notin` L -> Par (x ~ Nom ++ W)
      (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x)) R.
Proof.
  intros W rho A B t R H; inversion H; subst.
  - inversion H0; subst. exists A, B, L; repeat split; eauto using Par_Refl.
  - exists A', B', L; auto.
Qed.

Lemma dr_steps_pi_view : forall W R t u, dr_steps W R t u ->
  forall rho A B x, t = a_Pi rho A B -> x `notin` dom W ->
  exists A' B', u = a_Pi rho A' B' /\ dr_steps W R A A' /\
    dr_steps (x ~ Nom ++ W) R (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x)).
Proof.
  intros W R t u H; induction H; intros rho A B x E Hx; subst.
  - destruct (dr_par_pi_view _ _ _ _ _ _ (Par_Refl _ _ _ H)) as (P & Q & L & E & Ha & Hb).
    inversion E; subst. do 2 eexists; repeat split; eauto using dr_steps_single, dr_par_body_fresh.
  - destruct (dr_par_pi_view _ _ _ _ _ _ H) as (P & Q & L & -> & Ha & Hb).
    destruct (IHdr_steps _ _ _ x eq_refl Hx) as (P' & Q' & -> & HP & HQ).
    exists P', Q'; repeat split; eauto using dr_par_body_fresh.
Qed.

Lemma dr_join_pi_view : forall W R rho A B rho' A' B' x,
  x `notin` dom W -> dr_join W R (a_Pi rho A B) (a_Pi rho' A' B') ->
  rho = rho' /\ dr_join W R A A' /\
    dr_join (x ~ Nom ++ W) R (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x)).
Proof.
  intros W R rho A B rho' A' B' x Hx (t & P & Q).
  destruct (dr_steps_pi_view _ _ _ _ P _ _ _ x eq_refl Hx) as (C & D & -> & P1 & P2).
  destruct (dr_steps_pi_view _ _ _ _ Q _ _ _ x eq_refl Hx) as (C' & D' & E & Q1 & Q2).
  inversion E; subst. repeat split; unfold dr_join; eauto.
Qed.

Lemma dr_join_open : forall W R x B B' a a',
  x `notin` dom W -> x `notin` (fv_tm_tm_tm B \u fv_tm_tm_tm B') ->
  dr_join (x ~ Nom ++ W) R (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x)) ->
  dr_join W Nom a a' ->
  dr_join W R (open_tm_wrt_tm B a) (open_tm_wrt_tm B' a').
Proof.
  intros W R x B B' a a' Hx HF P Q.
  assert (U : uniq (x ~ Nom ++ W)) by
    (eapply dr_role_uniq, dr_join_role_l; exact P).
  assert (Ext : dr_extends (x ~ Nom ++ W) (x ~ Nom ++ W)) by (split; auto).
  eapply dr_join_trans with (b := open_tm_wrt_tm B' a).
  - pose proof (dr_join_role_l _ _ _ _ Q) as T.
    pose proof (dr_join_map _ _ _ R (tm_subst_tm_tm a x)
      ltac:(intros; eapply dr_par_subst; [eassumption|exact (Par_Refl _ _ _ T)|exact Ext]) _ _ P) as K.
    unfold open_tm_wrt_tm in K. rewrite !dr_open_fresh in K by fsetdec. exact K.
  - pose proof (dr_join_role_r _ _ _ _ P) as T.
    pose proof (dr_join_map _ _ _ R (fun z => tm_subst_tm_tm z x (open_tm_wrt_tm B' (a_Var_f x)))
      ltac:(intros; eapply dr_par_subst; [exact (Par_Refl _ _ _ T)|eassumption|exact Ext]) _ _ Q) as K.
    unfold open_tm_wrt_tm in K. rewrite !dr_open_fresh in K by fsetdec. exact K.
Qed.

Lemma dr_par_cpi_view : forall W a b A B S t R,
  Par W (a_CPi (Eq a b A S) B) t R ->
  exists p q P Q, t = a_CPi (Eq p q P S) Q /\
    Par W a p S /\ Par W b q S /\ Par W A P Rep /\ Par W B Q R.
Proof.
  intros W a b A B S t R H; inversion H; subst.
  - inversion H0; subst. pick fresh c for L.
    exists a,b,A,B; repeat split; eauto using Par_Refl, dr_par_co_body.
  - pick fresh c for L.
    do 4 eexists; repeat split; eauto using dr_par_co_body.
Qed.

Lemma dr_steps_cpi_view : forall W R t u, dr_steps W R t u ->
  forall a b A B S, t = a_CPi (Eq a b A S) B ->
  exists p q P Q, u = a_CPi (Eq p q P S) Q /\
    dr_steps W S a p /\ dr_steps W S b q /\ dr_steps W Rep A P /\ dr_steps W R B Q.
Proof.
  intros W R t u H; induction H; intros p q P Q S E; subst.
  - destruct (dr_par_cpi_view _ _ _ _ _ _ _ _ (Par_Refl _ _ _ H))
      as (a & b & A & B & E & Pa & Pb & PA & PB).
    inversion E; subst. do 4 eexists; repeat split; eauto using dr_steps_single.
  - destruct (dr_par_cpi_view _ _ _ _ _ _ _ _ H) as (a & b0 & A & B & -> & Pa & Pb & PA & PB).
    destruct (IHdr_steps _ _ _ _ _ eq_refl) as (a' & b' & A' & B' & -> & Qa & Qb & QA & QB).
    do 4 eexists; repeat split; eauto.
Qed.

Lemma dr_join_cpi_view : forall W R a b A B S p q P Q T,
  dr_join W R (a_CPi (Eq a b A S) B) (a_CPi (Eq p q P T) Q) ->
  S = T /\ dr_join W S a p /\ dr_join W S b q /\ dr_join W Rep A P /\ dr_join W R B Q.
Proof.
  intros W R a b A B S p q P Q T (t & H & K).
  destruct (dr_steps_cpi_view _ _ _ _ H _ _ _ _ _ eq_refl) as (a' & b' & A' & B' & -> & H1 & H2 & H3 & H4).
  destruct (dr_steps_cpi_view _ _ _ _ K _ _ _ _ _ eq_refl) as (a'' & b'' & A'' & B'' & E & K1 & K2 & K3 & K4).
  inversion E; subst. repeat split; unfold dr_join; eauto.
Qed.

Lemma dr_casepath_par : forall W R a b F, CasePath R a F -> Par W a b R -> CasePath R b F.
Proof.
  intros W R a b F C P.
  destruct (dr_casepath_inv _ _ _ C) as (-> & V & N).
  destruct (dr_valuepath_spine _ _ V) as [s S].
  assert (Cond : forall t, s <> t ++ dr_fixed_spine).
  { intros t ->. apply N. eapply dr_spine_subpat; eauto using dr_par_scoped_l. }
  eapply dr_casepath_spine; eauto using dr_par_scoped_r, dr_par_spine_stable.
Qed.

Lemma dr_par_neutral_app : forall W R a nu b c F,
  CasePath R (a_App a nu b) F -> Par W (a_App a nu b) c R ->
  exists a' b', c = a_App a' nu b' /\ Par W a a' R /\ Par W b b' (app_role nu R).
Proof.
  intros W R a nu b c F C H.
  destruct (dr_casepath_inv _ _ _ C) as (-> & V & N).
  destruct (dr_app_view _ _ _ _ _ _ H) as (p & q & P & Q & K).
  inversion K; subst; eauto.
  - exfalso. assert (V' : ValuePath a Fix) by (inversion V; subst; assumption).
    destruct (dr_valuepath_spine _ _ V') as [s S].
    assert (Cond : forall t, s <> t ++ dr_fixed_spine).
    { intros t E. eapply N, subtm_pattern_agree_App; eauto using dr_par_lc_l.
      apply (dr_spine_subpat a t (dr_par_scoped_l _ _ _ _ P)). now rewrite <- E. }
    pose proof (dr_par_spine_stable _ _ _ _ P _ S Cond). discriminate.
  - exfalso. eapply N, subtm_pattern_agree_Base, dr_pattern_agree_shape.
    exists i,b. repeat split; eauto using dr_par_lc_l.
    destruct (dr_par_fix_prefix _ _ _ _ P) as (? & _ & ?); eauto using dr_par_lc_l.
Qed.

Lemma dr_par_neutral_capp : forall W R a c F,
  CasePath R (a_CApp a g_Triv) F -> Par W (a_CApp a g_Triv) c R ->
  exists a', c = a_CApp a' g_Triv /\ Par W a a' R.
Proof.
  intros W R a c F C H.
  destruct (dr_casepath_inv _ _ _ C) as (-> & V & N).
  destruct (dr_capp_view _ _ _ _ H) as (p & P & K). inversion K; subst; eauto.
  exfalso. assert (V' : ValuePath a Fix) by (inversion V; subst; assumption).
  destruct (dr_valuepath_spine _ _ V') as [s S].
  assert (Cond : forall t, s <> t ++ dr_fixed_spine).
  { intros t E. eapply N, subtm_pattern_agree_CAppp.
    apply (dr_spine_subpat a t (dr_par_scoped_l _ _ _ _ P)). now rewrite <- E. }
  pose proof (dr_par_spine_stable _ _ _ _ P _ S Cond). discriminate.
Qed.

Lemma dr_steps_neutral_app : forall W R t u, dr_steps W R t u ->
  forall a nu b F, t = a_App a nu b -> CasePath R t F ->
  exists a' b', u = a_App a' nu b' /\ dr_steps W R a a' /\ dr_steps W (app_role nu R) b b'.
Proof.
  intros W R t u H; induction H; intros p nu q F E C; subst.
  - destruct (dr_par_neutral_app _ _ _ _ _ _ _ C (Par_Refl _ _ _ H)) as (p' & q' & E & P & Q).
    inversion E; subst; do 2 eexists; repeat split; eauto using dr_steps_single.
  - destruct (dr_par_neutral_app _ _ _ _ _ _ _ C H) as (p' & q' & -> & P & Q).
    destruct (IHdr_steps _ _ _ F eq_refl (dr_casepath_par _ _ _ _ _ C H))
      as (a' & b' & -> & P' & Q').
    do 2 eexists; repeat split; eauto.
Qed.

Lemma dr_join_neutral_app : forall W R a nu b a' b' F,
  CasePath R (a_App a nu b) F -> CasePath R (a_App a' nu b') F ->
  dr_join W R (a_App a nu b) (a_App a' nu b') ->
  dr_join W R a a' /\ dr_join W (app_role nu R) b b'.
Proof.
  intros W R a nu b a' b' F C C' (u & P & Q).
  destruct (dr_steps_neutral_app _ _ _ _ P _ _ _ _ eq_refl C) as (p & r & -> & P1 & P2).
  destruct (dr_steps_neutral_app _ _ _ _ Q _ _ _ _ eq_refl C') as (q & s & E & Q1 & Q2).
  inversion E; subst; split; unfold dr_join; eauto.
Qed.

Lemma dr_steps_neutral_capp : forall W R t u, dr_steps W R t u ->
  forall a F, t = a_CApp a g_Triv -> CasePath R t F ->
  exists a', u = a_CApp a' g_Triv /\ dr_steps W R a a'.
Proof.
  intros W R t u H; induction H; intros p F E C; subst.
  - destruct (dr_par_neutral_capp _ _ _ _ _ C (Par_Refl _ _ _ H)) as (p' & E & P).
    inversion E; subst; eauto using dr_steps_single.
  - destruct (dr_par_neutral_capp _ _ _ _ _ C H) as (p' & -> & P).
    destruct (IHdr_steps _ F eq_refl (dr_casepath_par _ _ _ _ _ C H)) as (a' & -> & P').
    eauto.
Qed.

Lemma dr_join_neutral_capp : forall W R a a' F,
  CasePath R (a_CApp a g_Triv) F -> CasePath R (a_CApp a' g_Triv) F ->
  dr_join W R (a_CApp a g_Triv) (a_CApp a' g_Triv) -> dr_join W R a a'.
Proof.
  intros W R a a' F C C' (u & P & Q).
  destruct (dr_steps_neutral_capp _ _ _ _ P _ _ eq_refl C) as (p & -> & P1).
  destruct (dr_steps_neutral_capp _ _ _ _ Q _ _ eq_refl C') as (q & E & Q1).
  inversion E; subst. unfold dr_join; eauto.
Qed.

Lemma dr_beta_par : forall a b R, Beta a b R -> forall W, roleing W a R -> Par W a b R.
Proof.
  intros a b R H W T. inversion H; subst; dr_signature.
  - inversion T; subst; eauto using Par_Beta, Par_Refl.
  - inversion T; subst; eauto using Par_CBeta, Par_Refl.
  - match goal with Hr : Rename _ _ _ _ _ _, M : MatchSubst _ _ _ _ |- _ =>
      destruct (dr_match_rename _ _ _ _ Hr _ _ M) as (i & f & -> & -> & Hi & Hf)
    end.
    inversion T; subst. destruct R; eapply dr_par_axiom; eauto using Par_Refl.
  - exfalso; match goal with S : SatApp _ _ |- _ => exact (dr_no_sat _ _ S) end.
  - inversion T; subst. eapply Par_PatternFalse; eauto using Par_Refl.
Qed.

Lemma dr_good_tm : forall G D x A, Good G D -> uniq G -> x `notin` dom G ->
  Good (x ~ Tm A ++ G) D.
Proof.
  intros G D x A H Hu Hx y p q T R [B|B] Hy; [discriminate|].
  destruct (H _ _ _ _ _ B Hy) as (z & P & Q). exists z. simpl.
  assert (K : dr_extends (ctx_nom G) (x ~ Nom ++ ctx_nom G)).
  { apply dr_par_extends_push; auto using dr_ctx_nom_uniq. intro E; eauto using dr_ctx_nom_dom. }
  split; eauto using dr_par_weak.
Qed.

Lemma dr_good_co : forall G D c phi, Good G D -> c `notin` D ->
  Good (c ~ Co phi ++ G) D.
Proof.
  intros G D c phi H Hc x a b A R [B|B] Hx; [inversion B; subst; contradiction|].
  simpl. eapply H; eauto.
Qed.

Lemma dr_good_dom_tm : forall G x A, Good G (dom G) -> uniq G -> x `notin` dom G ->
  Good (x ~ Tm A ++ G) (dom (x ~ Tm A ++ G)).
Proof.
  intros G x A H Hu Hx y p q T R B Hy.
  apply (dr_good_tm G (dom G) x A H Hu Hx y p q T R B).
  destruct B as [B|B]; [discriminate|eauto using binds_In].
Qed.

Definition dr_iso_join (W : role_context) (p q : constraint) :=
  match p,q with Eq a b A R, Eq a' b' A' R' =>
    R = R' /\ dr_join W R a a' /\ dr_join W R b b' /\ dr_join W Rep A A' end.

Lemma dr_join_co_body : forall W R B C c,
  dr_join W R (open_tm_wrt_co B (g_Var_f c)) (open_tm_wrt_co C (g_Var_f c)) ->
  dr_join W R B C.
Proof.
  intros W R B C c H.
  pose proof (dr_role_scoped _ _ _ (dr_join_role_l _ _ _ _ H)) as HB.
  pose proof (dr_role_scoped _ _ _ (dr_join_role_r _ _ _ _ H)) as HC.
  unfold open_tm_wrt_co in *. apply dr_scoped_co_open in HB, HC.
  now rewrite (dr_scoped_co_id B 0), (dr_scoped_co_id C 0) in H.
Qed.

Ltac dr_sound_good :=
  first [assumption |
    match goal with |- Good (_ :: ?G) _ =>
      first [eapply dr_good_tm; [assumption | eauto using dr_ctx_uniq, dr_typ_ctx | fsetdec] |
             apply dr_good_co; [assumption | fsetdec]]
    end].

Lemma dr_equality_sound :
  (forall G phi, PropWff G phi -> True) /\
  (forall G a A, Typing G a A -> True) /\
  (forall G D phi psi, Iso G D phi psi ->
    Good G D -> dr_iso_join (ctx_nom G) phi psi) /\
  (forall G D a b A R, DefEq G D a b A R ->
    Good G D -> dr_join (ctx_nom G) R a b) /\
  (forall G, Ctx G -> True).
Proof.
  apply dr_judgments_ind; intros; simpl in *; try exact I.
  all: try solve [eauto 3 using dr_join_refl, dr_typ_role, dr_join_sym, dr_join_trans, dr_join_promote].
  all: try solve [eauto 3 using dr_join_capp].
  all: try solve [match goal with S : SatApp _ _ |- _ => exact (False_rect _ (dr_no_sat _ _ S)) end].
  - split; [reflexivity|]. split; [auto|]. split; [auto|].
    apply dr_join_refl. eapply dr_typ_role, dr_typ_regular.
    exact (proj1 (dr_eq_regular _ _ _ _ _ _ d)).
  - repeat split; try reflexivity.
    + apply dr_join_refl. inversion p; subst; eauto using dr_typ_role.
    + apply dr_join_refl. inversion p; subst; eauto using dr_typ_role.
    + destruct R0; eauto using dr_join_promote.
  - destruct (dr_join_cpi_view _ _ _ _ _ _ _ _ _ _ _ _ (H H0)) as (E & P & Q & T & _).
    exact (conj E (conj P (conj Q T))).
  - match goal with Hd : Good ?G ?D, B : binds ?c (Co (Eq ?a ?b ?A ?R)) ?G,
                    Hin : ?c `in` ?D |- _ =>
      destruct (Hd c a b A R B Hin) as (z & P & Q); exists z; split; eauto using dr_steps_single
    end.
  - eapply dr_join_trans; [apply H; assumption|apply H0; assumption].
  - apply dr_subrole_cases in s. destruct s as [E | E]; subst; destruct_all role; eauto using dr_join_promote.
  - exists a2; split; eauto using dr_steps_single, dr_beta_par, dr_typ_role, dr_steps_refl.
  - pick fresh x for (L \u dom G \u fv_tm_tm_tm B1 \u fv_tm_tm_tm B2).
    eapply dr_join_pi with (x := x); try solve [intro K; apply dr_ctx_nom_dom in K; fsetdec|fsetdec|auto].
    apply H0; [fsetdec|dr_sound_good].
  - pick fresh x for (L \u dom G \u fv_tm_tm_tm b1 \u fv_tm_tm_tm b2).
    eapply dr_join_abs with (x := x); try solve [intro K; apply dr_ctx_nom_dom in K; fsetdec|fsetdec].
    apply H; [fsetdec|dr_sound_good].
  - eapply (dr_join_app (ctx_nom G) R' (Rho Rel)); eauto.
  - eapply (dr_join_app (ctx_nom G) R' (Role R)); eauto.
  - eapply (dr_join_app (ctx_nom G) R (Rho Irrel)); eauto.
    apply dr_join_refl, role_a_Bullet. eauto using dr_ctx_nom_uniq, dr_ctx_uniq, dr_typ_ctx.
  - pick fresh x for (dom G).
    assert (K : x `notin` dom (ctx_nom G)) by (intro E; apply dr_ctx_nom_dom in E; fsetdec).
    destruct (dr_join_pi_view _ _ _ _ _ _ _ _ _ K (H H0)) as (_ & P & _). exact P.
  - pick fresh x for (dom G \u fv_tm_tm_tm B1 \u fv_tm_tm_tm B2).
    assert (K : x `notin` dom (ctx_nom G)) by (intro E; apply dr_ctx_nom_dom in E; fsetdec).
    destruct (dr_join_pi_view _ _ _ _ _ _ _ _ _ K (H H1)) as (_ & _ & P).
    eapply dr_join_open with (x := x); eauto; fsetdec.
  - destruct (H H4) as (_ & P & Q & T).
    apply dr_join_cpi; auto.
    pick fresh c for (L \u D).
    eapply dr_join_co_body with (c := c).
    apply H0; [fsetdec|dr_sound_good].
  - pick fresh c for (L \u D). apply dr_join_cabs.
    eapply dr_join_co_body with (c := c). apply H; [fsetdec|dr_sound_good].
  - destruct (dr_join_cpi_view _ _ _ _ _ _ _ _ _ _ _ _ (H H2)) as (_ & _ & _ & _ & P).
    pose proof (dr_role_scoped _ _ _ (dr_join_role_l _ _ _ _ P)) as HB.
    pose proof (dr_role_scoped _ _ _ (dr_join_role_r _ _ _ _ P)) as HB'.
    unfold open_tm_wrt_co. now rewrite (dr_scoped_co_id B1 0), (dr_scoped_co_id B2 0).
  - destruct (H0 H1) as (E & P & Q & T). subst.
    eapply dr_join_trans; [apply dr_join_sym; exact P|]. eauto using dr_join_trans.
  - destruct (H H0) as (_ & _ & _ & P); exact P.
  - pose proof (dr_join_neutral_app (ctx_nom G) R' a (Role R1) b a' b' F c c0 (H3 H5)) as K; tauto.
  - pose proof (dr_join_neutral_app (ctx_nom G) R' a (Rho Irrel) a_Bullet a' a_Bullet F c c0 (H3 H5)) as K; tauto.
  - pose proof (dr_join_neutral_app (ctx_nom G) R2 a (Role R1) b a' b' F c c0 (H3 H5)) as K; tauto.
  - eapply dr_join_neutral_capp; eauto.
Qed.

Definition dr_defeq_sound := proj1 (proj2 (proj2 (proj2 dr_equality_sound))).

(* Canonical forms and progress. *)

Lemma dr_steps_star : forall W R a b, dr_steps W R a b -> a = a_Star -> b = a_Star.
Proof.
  intros W R a b H; induction H; intros ->; auto.
  inversion H; subst; auto.
Qed.

Lemma dr_join_star_pi : forall W R rho A B, ~ dr_join W R a_Star (a_Pi rho A B).
Proof.
  intros W R rho A B (t & P & Q).
  apply dr_steps_star in P; [subst t|reflexivity].
  pick fresh x for (dom W).
  destruct (dr_steps_pi_view _ _ _ _ Q _ _ _ x eq_refl Fr) as (C & D & E & _); discriminate.
Qed.

Lemma dr_join_star_cpi : forall W R p q A B S, ~ dr_join W R a_Star (a_CPi (Eq p q A S) B).
Proof.
  intros W R p q A B S (t & P & Q).
  apply dr_steps_star in P; [subst t|reflexivity].
  destruct (dr_steps_cpi_view _ _ _ _ Q _ _ _ _ _ eq_refl) as (? & ? & ? & ? & E & _); discriminate.
Qed.

Lemma dr_join_pi_cpi : forall W R rho A B p q C D S,
  ~ dr_join W R (a_Pi rho A B) (a_CPi (Eq p q C S) D).
Proof.
  intros W R rho A B p q C D S (t & P & Q). pick fresh x for (dom W).
  destruct (dr_steps_pi_view _ _ _ _ P _ _ _ x eq_refl Fr) as (A' & B' & -> & _).
  destruct (dr_steps_cpi_view _ _ _ _ Q _ _ _ _ _ eq_refl) as (? & ? & ? & ? & E & _); discriminate.
Qed.

Definition dr_type_form a := match a with a_Star | a_Pi _ _ _ | a_CPi _ _ => True | _ => False end.

Lemma dr_type_form_type : forall G a A, Typing G a A -> dr_type_form a ->
  DefEq G (dom G) a_Star A a_Star Rep.
Proof.
  intros G a A T; induction T; simpl; try contradiction; intros;
    eauto using E_Star, E_Refl, E_Trans, dr_typ_ctx, dr_wff_ctx.
Qed.

Lemma dr_value_pi : forall G a rho A B R, Good G (dom G) ->
  Typing G a (a_Pi rho A B) -> Value R a ->
  (exists v, a = a_UAbs rho v) \/ exists F, CasePath R a F.
Proof.
  intros G a rho A B R Good T V. inversion V; subst; eauto.
  all: try solve [exfalso; eapply dr_join_star_pi; eapply dr_defeq_sound; [eapply dr_type_form_type; [exact T|exact I]|exact Good]].
  all: try solve [inversion T; subst; eapply dr_no_pattern_typing; eauto].
  all: try solve [exfalso; clear V; remember (a_Abs Rel A0 a0) as t; induction T; inversion Heqt; subst; auto].
  all: try solve [exfalso; clear V; remember (a_CAbs phi a0) as t; induction T; inversion Heqt; subst; auto].
  all: try solve [
    destruct (dr_abs_type _ _ _ _ T) as (L0 & U & V' & _ & _ & _ & E);
    pose proof (dr_defeq_sound _ _ _ _ _ _ E Good) as J;
    pick fresh x for (dom (ctx_nom G));
    destruct (dr_join_pi_view _ _ _ _ _ _ _ _ _ Fr J) as [RelEq _]; subst rho; eauto].
  all: try solve [
    destruct (dr_cabs_type _ _ _ T) as (L & [p q U S] & V' & _ & _ & E);
    exfalso; eapply dr_join_pi_cpi, dr_join_sym, dr_defeq_sound; eauto].
Qed.

Lemma dr_value_cpi : forall G a p q A S B R, Good G (dom G) ->
  Typing G a (a_CPi (Eq p q A S) B) -> Value R a ->
  (exists v, a = a_UCAbs v) \/ exists F, CasePath R a F.
Proof.
  intros G a p q A S B R Good T V. inversion V; subst; eauto.
  all: try solve [exfalso; eapply dr_join_star_cpi; eapply dr_defeq_sound; [eapply dr_type_form_type; [exact T|exact I]|exact Good]].
  all: try solve [exfalso; clear V; remember (a_Abs Rel A0 a0) as t; induction T; inversion Heqt; subst; auto].
  all: try solve [exfalso; clear V; remember (a_CAbs phi a0) as t; induction T; inversion Heqt; subst; auto].
  all: try solve [
    destruct (dr_abs_type _ _ _ _ T) as (L0 & U & V' & _ & _ & _ & E);
    exfalso; eapply dr_join_pi_cpi, dr_defeq_sound; eauto].
Qed.

Lemma dr_match_shape_dec : forall a,
  {dr_spine a = Some (Fix, dr_fixed_spine)} + {dr_spine a <> Some (Fix, dr_fixed_spine)}.
Proof.
  intros. repeat (first [apply eq_dec | decide equality]).
Qed.

Lemma dr_casepath_app : forall R a nu b F,
  CasePath R a F -> dr_scoped 0 (a_App a nu b) ->
  Value R (a_App a nu b) \/ exists a', reduction_in_one (a_App a nu b) a' R.
Proof.
  intros R a nu b F C Hs.
  destruct (dr_casepath_inv _ _ _ C) as (-> & V & N).
  destruct (dr_match_shape_dec (a_App a nu b)) as [E|E].
  - right. assert (M : subtm_pattern_agree (a_App a nu b) FixPat).
    { eapply dr_spine_subpat with (s := nil); eauto. }
    inversion M; subst; try contradiction.
    apply dr_pattern_agree_shape in H. destruct H as (i & f & Eq & Hi & Hf).
    inversion Eq; subst. eauto using E_Prim, dr_beta_fix.
  - left. apply Value_Path with (F := Fix).
    eapply CasePath_UnMatch with (p := FixPat) (b := FixDef) (A := FixTy) (R1 := Nom) (Rs := [Nom]).
    + constructor; eauto using dr_scoped_lc; apply dr_scoped_lc; exact (proj2 Hs).
    + unfold toplevel; now left.
    + intro P; inversion P; subst; try contradiction.
      apply dr_pattern_agree_shape in H. destruct H as (i & f & Eq & _). apply E. rewrite Eq; reflexivity.
Qed.

Lemma dr_casepath_capp : forall R a F, CasePath R a F -> Value R (a_CApp a g_Triv).
Proof.
  intros R a F C.
  destruct (dr_casepath_inv _ _ _ C) as (-> & V & N).
  apply Value_Path with (F := Fix).
  eapply CasePath_UnMatch with (p := FixPat) (b := FixDef) (A := FixTy) (R1 := Nom) (Rs := [Nom]).
  - constructor; auto.
  - unfold toplevel; now left.
  - intro P; inversion P; subst; try contradiction.
    apply dr_pattern_agree_shape in H. destruct H as (? & ? & E & _); discriminate.
Qed.

Lemma dr_one_subst : forall a b R, reduction_in_one a b R -> dr_scoped 0 a ->
  forall u x, dr_scoped 0 u ->
  reduction_in_one (tm_subst_tm_tm u x a) (tm_subst_tm_tm u x b) R.
Proof.
  intros a b R H; induction H; intros Ha u z Hu; simpl in *.
  - assert (Hb : dr_scoped 1 a').
    { pick fresh x for L.
      apply (proj1 (dr_scoped_open a' 0 x)).
      apply (proj1 (dr_fv_inclusion _ _ _ (H x Fr) (proj2 (dr_scoped_open a 0 x) Ha))). }
    eapply E_AbsTerm with (L := L \u {{z}} \u fv_tm_tm_tm u); intros x Hx.
    change (reduction_in_one (open_tm_wrt_tm (dr_tm (Some (z,u)) a) (a_Var_f x))
      (open_tm_wrt_tm (dr_tm (Some (z,u)) a') (a_Var_f x)) R).
    rewrite <- (dr_tm_open_var (Some (z,u)) a x Hu Ha),
      <- (dr_tm_open_var (Some (z,u)) a' x Hu Hb) by (simpl; fsetdec).
    exact (H0 x ltac:(fsetdec) (proj2 (dr_scoped_open a 0 x) Ha) u z Hu).
  - apply E_AppLeft; intuition eauto using dr_scoped_subst, dr_scoped_lc.
  - apply E_CAppLeft; intuition eauto.
  - apply E_Pattern; intuition eauto using dr_scoped_subst, dr_scoped_lc.
  - apply E_Prim; eauto using dr_beta_subst.
Qed.

Lemma dr_abs_progress : forall a R x, dr_scoped 1 a ->
  x `notin` fv_tm_tm_tm a ->
  (Value R (open_tm_wrt_tm a (a_Var_f x)) \/
     exists b, reduction_in_one (open_tm_wrt_tm a (a_Var_f x)) b R) ->
  Value R (a_UAbs Irrel a) \/ exists b, reduction_in_one (a_UAbs Irrel a) b R.
Proof.
  intros a R x Ha Hx [V|[b K]].
  - left. eapply Value_UAbsIrrel with (L := empty); intros y Hy.
    unfold open_tm_wrt_tm in *. rewrite <- (dr_open_fresh a 0 (a_Var_f y) x) by assumption.
    eapply dr_value_subst; [exact V | exact (proj2 (dr_scoped_open a 0 x) Ha) | exact I].
  - right. exists (a_UAbs Irrel (dr_close 0 x b)).
    eapply E_AbsTerm with (L := empty); intros y Hy.
    pose proof (proj2 (dr_scoped_open a 0 x) Ha) as Hs.
    pose proof (proj1 (dr_fv_inclusion _ _ _ K Hs)) as Hb.
    unfold open_tm_wrt_tm in *.
    rewrite (dr_close_open b 0), <- (dr_open_fresh a 0 (a_Var_f y) x) by assumption.
    eapply dr_one_subst; [exact K | exact Hs | exact I].
Qed.

Lemma dr_irrelevant_sub : forall G D a b, irrelevant G D a ->
  (forall x, x `in` fv_tm_tm_tm b -> x `in` fv_tm_tm_tm a) -> irrelevant G D b.
Proof. intros G D a b [F K] M; split; auto. intros x A B N. eapply F; eauto. Qed.

Lemma dr_abs_irrelevant : forall G A a x,
  irrelevant G (dom G) (a_UAbs Irrel a) -> Ctx G -> dr_scoped 1 a ->
  x `notin` dom G -> RhoCheck Irrel x (open_tm_wrt_tm a (a_Var_f x)) ->
  irrelevant (x ~ Tm A ++ G) (dom (x ~ Tm A ++ G)) (open_tm_wrt_tm a (a_Var_f x)).
Proof.
  intros G A a x [H K] C Ha Hx Rho. split.
  - intros y T [B|B] Hy.
    + inversion B; subst. inversion Rho; contradiction.
    + pose proof (binds_In _ _ _ _ B) as N.
      unfold open_tm_wrt_tm in Hy. pose proof (dr_fv_open_bound _ _ _ _ _ Ha Hy) as M.
      simpl in M. destruct M as [M|M].
      * exact (H y T B M).
      * fsetdec.
  - eauto using dr_good_dom_tm, dr_ctx_uniq.
Qed.

Theorem progress : forall G a A R, Typing G a A ->
                          irrelevant G (dom G) a ->
                          Value R a \/ exists a', reduction_in_one a a' R.
Proof.
  intros G a A R H. induction H; intros Relv.
  - left; constructor.
  - destruct Relv as [B K]. exfalso. eapply B; [eassumption|simpl; fsetdec].
  - left; apply Value_Pi; eauto using dr_scoped_lc, dr_typ_scoped.
    + apply dr_scoped_lc. exact (proj1 (dr_typ_scoped _ _ _ H1)).
    + apply dr_scoped_lc. exact (proj1 (dr_typ_scoped _ _ _ (E_Pi L _ _ _ _ H H1))).
  - destruct rho.
    + left; apply Value_UAbsRel, dr_scoped_lc. exact (proj1 (dr_typ_scoped _ _ _ (E_Abs L _ _ _ _ _ H H1 H2))).
    + pick fresh x for (L \u dom G \u fv_tm_tm_tm a).
      assert (Hx : x `notin` L) by fsetdec.
      pose proof (proj1 (dr_typ_scoped _ _ _ (H x Hx))) as Ha.
      unfold open_tm_wrt_tm in Ha. apply dr_scoped_open in Ha.
      eapply dr_abs_progress with (x := x); [exact Ha|fsetdec|].
      apply H0; [exact Hx|].
      eapply dr_abs_irrelevant; [exact Relv|eauto using dr_typ_ctx|exact Ha|fsetdec|eauto].
  - assert (M : irrelevant G (dom G) b) by (eapply dr_irrelevant_sub; [exact Relv|simpl; intros; fsetdec]).
    destruct (IHTyping1 M) as [V|[b' K]].
    + destruct (dr_value_pi _ _ _ _ _ _ (proj2 M) H V) as [[v ->]|[F C]].
      * right. eexists. apply E_Prim, Beta_AppAbs; eauto using dr_scoped_lc.
        apply dr_scoped_lc. exact (proj1 (dr_typ_scoped _ _ _ H0)).
      * eapply dr_casepath_app; eauto.
        exact (proj1 (dr_typ_scoped _ _ _ (E_App _ _ _ _ _ H H0))).
    + right. eexists. eapply E_AppLeft; [apply dr_scoped_lc; exact (proj1 (dr_typ_scoped _ _ _ H0))|exact K].
  - assert (M : irrelevant G (dom G) b) by (eapply dr_irrelevant_sub; [exact Relv|simpl; intros; fsetdec]).
    destruct (IHTyping1 M) as [V|[b' K]].
    + destruct (dr_value_pi _ _ _ _ _ _ (proj2 M) H V) as [[v E]|[F C]].
      * exfalso. eapply (proj1 (proj2 (dr_rolepath_nonempty _ _ H1 ltac:(discriminate)))); exact E.
      * eapply dr_casepath_app; eauto.
        exact (proj1 (dr_typ_scoped _ _ _ (E_TApp _ _ _ _ _ _ _ H H0 H1))).
    + right. eexists. eapply E_AppLeft; [apply dr_scoped_lc; exact (proj1 (dr_typ_scoped _ _ _ H0))|exact K].
  - assert (M : irrelevant G (dom G) b) by (eapply dr_irrelevant_sub; [exact Relv|simpl; intros; fsetdec]).
    destruct (IHTyping1 M) as [V|[b' K]].
    + destruct (dr_value_pi _ _ _ _ _ _ (proj2 M) H V) as [[v ->]|[F C]].
      * right. eexists. apply E_Prim, Beta_AppAbs; auto using lc_a_Bullet.
      * eapply dr_casepath_app; eauto.
        exact (proj1 (dr_typ_scoped _ _ _ (E_IApp _ _ _ _ _ H H0))).
    + right. eexists. eapply E_AppLeft; eauto using lc_a_Bullet.
  - auto.
  - left. apply Value_CPi.
    + destruct phi; constructor; apply dr_scoped_lc; pose proof (dr_wff_scoped _ _ H1); simpl in *; tauto.
    + apply dr_scoped_lc. exact (proj1 (dr_typ_scoped _ _ _ (E_CPi L _ _ _ H H1))).
  - left. apply Value_UCAbs, dr_scoped_lc. exact (proj1 (dr_typ_scoped _ _ _ (E_CAbs L _ _ _ _ H H1))).
  - assert (M : irrelevant G (dom G) a1) by (eapply dr_irrelevant_sub; [exact Relv|simpl; intros; fsetdec]).
    destruct (IHTyping M) as [V|[b' K]].
    + destruct (dr_value_cpi _ _ _ _ _ _ _ _ (proj2 M) H V) as [[v ->]|[F C]].
      * right. eexists. apply E_Prim, Beta_CAppCAbs, dr_scoped_lc. exact (proj1 (dr_typ_scoped _ _ _ H)).
      * left; eauto using dr_casepath_capp.
    + right. eexists. eauto using E_CAppLeft.
  - dr_signature.
  - dr_signature. left. eapply Value_Path, dr_casepath_spine with (s := nil); try exact I; try reflexivity.
    intros [|h l]; discriminate.
  - exact (False_rect _ (dr_no_sat _ _ H4)).
Qed.
