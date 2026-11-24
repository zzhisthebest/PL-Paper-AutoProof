Require Import Coq.Program.Equality.

Require Import Program.Tactics.

Require Import Metalib.Metatheory.

Require Import List.

Require Import uni.notations.

Require Import uni.algo_worklist.def_extra.

Open Scope aworklist_scope.

Open Scope dworklist_scope.

From Stdlib Require Import Lia Sorting.Permutation.

Local Hint Constructors lc_typ s_in d_wf_typ d_mono_typ
  a_wf_typ a_mono_typ d_wf_exp a_wf_exp a_wf_conts a_wf_contd
  a_wf_work a_wf_wwl a_wf_twl a_wf_wl d_wf_tenv d_wf_env : core.

(* Interpret free type variables simultaneously. An assignment maps each
   solved existential to its declarative monotype. *)
Definition assignment := atom -> typ.

Fixpoint interp_typ (f : assignment) (A : typ) : typ :=
  match A with
  | typ_var_f X => f X
  | typ_arrow A B => typ_arrow (interp_typ f A) (interp_typ f B)
  | typ_all A => typ_all (interp_typ f A)
  | typ_union A B => typ_union (interp_typ f A) (interp_typ f B)
  | typ_intersection A B => typ_intersection (interp_typ f A) (interp_typ f B)
  | _ => A
  end.

Fixpoint interp_exp (f : assignment) (e : exp) : exp :=
  match e with
  | exp_abs e => exp_abs (interp_exp f e)
  | exp_app e1 e2 => exp_app (interp_exp f e1) (interp_exp f e2)
  | exp_tabs e => exp_tabs (interp_exp f e)
  | exp_tapp e A => exp_tapp (interp_exp f e) (interp_typ f A)
  | exp_anno e A => exp_anno (interp_exp f e) (interp_typ f A)
  | _ => e
  end.

Fixpoint interp_cs (f : assignment) (cs : conts) : conts :=
  match cs with
  | conts_infabs cd => conts_infabs (interp_cd f cd)
  | conts_inftapp A cs => conts_inftapp (interp_typ f A) (interp_cs f cs)
  | conts_inftappunion A B cs =>
      conts_inftappunion (interp_typ f A) (interp_typ f B) (interp_cs f cs)
  | conts_unioninftapp A cs => conts_unioninftapp (interp_typ f A) (interp_cs f cs)
  | conts_sub A => conts_sub (interp_typ f A)
  end
with interp_cd (f : assignment) (cd : contd) : contd :=
  match cd with
  | contd_infabsunion A cd => contd_infabsunion (interp_typ f A) (interp_cd f cd)
  | contd_infapp e cs => contd_infapp (interp_exp f e) (interp_cs f cs)
  | contd_unioninfabs A B cd =>
      contd_unioninfabs (interp_typ f A) (interp_typ f B) (interp_cd f cd)
  end.

Definition interp_work (f : assignment) (w : work) : work :=
  match w with
  | work_infer e cs => work_infer (interp_exp f e) (interp_cs f cs)
  | work_check e A => work_check (interp_exp f e) (interp_typ f A)
  | work_infabs A cd => work_infabs (interp_typ f A) (interp_cd f cd)
  | work_infabsunion A B C cd =>
      work_infabsunion (interp_typ f A) (interp_typ f B) (interp_typ f C) (interp_cd f cd)
  | work_infapp A B e cs =>
      work_infapp (interp_typ f A) (interp_typ f B) (interp_exp f e) (interp_cs f cs)
  | work_inftapp A B cs => work_inftapp (interp_typ f A) (interp_typ f B) (interp_cs f cs)
  | work_sub A B => work_sub (interp_typ f A) (interp_typ f B)
  | work_inftappunion A B C cs =>
      work_inftappunion (interp_typ f A) (interp_typ f B) (interp_typ f C) (interp_cs f cs)
  | work_unioninftapp A B cs => work_unioninftapp (interp_typ f A) (interp_typ f B) (interp_cs f cs)
  | work_unioninfabs A B C D cd =>
      work_unioninfabs (interp_typ f A) (interp_typ f B) (interp_typ f C)
                       (interp_typ f D) (interp_cd f cd)
  | work_applys cs A => work_applys (interp_cs f cs) (interp_typ f A)
  | work_applyd cd A B => work_applyd (interp_cd f cd) (interp_typ f A) (interp_typ f B)
  end.

Definition assign (f : assignment) (X : atom) (A : typ) : assignment :=
  fun Y => if eq_var Y X then A else f Y.

Definition agrees (L : atoms) (f g : assignment) :=
  forall X, X `in` L -> f X = g X.

Local Ltac restrict_agreement :=
  unfold agrees in *; intros;
  match goal with
  | H : forall x, x `in` _ -> ?f x = ?g x |- ?f ?x = ?g ?x =>
      apply H; fsetdec
  end.

Lemma interp_typ_ext : forall A f g,
  agrees (ftvar_in_typ A) f g -> interp_typ f A = interp_typ g A.
Proof.
  induction A; cbn; intros; try reflexivity; try solve [restrict_agreement];
    f_equal; first [apply IHA | apply IHA1 | apply IHA2]; restrict_agreement.
Qed.

Lemma interp_exp_ext : forall e f g,
  agrees (ftvar_in_exp e) f g -> interp_exp f e = interp_exp g e.
Proof.
  induction e; cbn; intros; try reflexivity;
    f_equal; first [apply IHe | apply IHe1 | apply IHe2 | apply interp_typ_ext]; restrict_agreement.
Qed.

Lemma interp_cont_ext :
  (forall d f g, agrees (ftvar_in_contd d) f g -> interp_cd f d = interp_cd g d) /\
  (forall s f g, agrees (ftvar_in_conts s) f g -> interp_cs f s = interp_cs g s).
Proof.
  apply contd_conts_mutind; cbn; intros;
    f_equal;
    first [apply interp_typ_ext | apply interp_exp_ext |
           match goal with IH : forall _ _, agrees _ _ _ -> _ = _ |- _ => apply IH end];
    restrict_agreement.
Qed.

Lemma interp_work_ext : forall w f g,
  agrees (ftvar_in_work w) f g -> interp_work f w = interp_work g w.
Proof.
  destruct interp_cont_ext.
  destruct w; cbn; intros;
    f_equal; first [apply interp_typ_ext | apply interp_exp_ext | apply H | apply H0]; restrict_agreement.
Qed.

Lemma interp_open_typ_rec : forall A k B f,
  (forall X n C, open_typ_wrt_typ_rec n C (f X) = f X) ->
  interp_typ f (open_typ_wrt_typ_rec k B A) =
  open_typ_wrt_typ_rec k (interp_typ f B) (interp_typ f A).
Proof.
  induction A; cbn; intros; try reflexivity; try solve [f_equal; eauto].
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
Qed.

Lemma interp_open_exp_typ_rec : forall e k B f,
  (forall X n C, open_typ_wrt_typ_rec n C (f X) = f X) ->
  interp_exp f (open_exp_wrt_typ_rec k B e) =
  open_exp_wrt_typ_rec k (interp_typ f B) (interp_exp f e).
Proof.
  induction e; cbn; intros; f_equal; eauto using interp_open_typ_rec.
Qed.

Lemma interp_open_exp_exp_rec : forall e k x f,
  interp_exp f (open_exp_wrt_exp_rec k (exp_var_f x) e) =
  open_exp_wrt_exp_rec k (exp_var_f x) (interp_exp f e).
Proof.
  induction e; cbn; intros; try reflexivity; try solve [f_equal; eauto].
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
Qed.

Lemma open_mono_rec : forall E T, d_mono_typ E T ->
  forall k B, open_typ_wrt_typ_rec k B T = T.
Proof. intros E T H; induction H; cbn; intros; f_equal; auto. Qed.

Definition closed_assignment (f : assignment) :=
  forall X k B, open_typ_wrt_typ_rec k B (f X) = f X.

Lemma interp_open_typ : forall A B f, closed_assignment f ->
  interp_typ f (open_typ_wrt_typ A B) =
  open_typ_wrt_typ (interp_typ f A) (interp_typ f B).
Proof. unfold open_typ_wrt_typ; eauto using interp_open_typ_rec. Qed.

Lemma interp_open_exp_typ : forall e B f, closed_assignment f ->
  interp_exp f (open_exp_wrt_typ e B) =
  open_exp_wrt_typ (interp_exp f e) (interp_typ f B).
Proof. unfold open_exp_wrt_typ; eauto using interp_open_exp_typ_rec. Qed.

Lemma interp_open_exp_exp : forall e x f,
  interp_exp f (open_exp_wrt_exp e (exp_var_f x)) =
  open_exp_wrt_exp (interp_exp f e) (exp_var_f x).
Proof. intros; apply interp_open_exp_exp_rec. Qed.

Lemma interp_assign_typ : forall A f X B g,
  interp_typ f B = g X -> (forall Y, Y <> X -> f Y = g Y) ->
  interp_typ f ({B ᵗ/ₜ X} A) = interp_typ g A.
Proof.
  induction A; cbn; intros; try reflexivity; try solve [f_equal; auto].
  destruct (eq_var X X0); subst; cbn; auto.
Qed.

Lemma interp_assign_exp : forall e f X B g,
  interp_typ f B = g X -> (forall Y, Y <> X -> f Y = g Y) ->
  interp_exp f ({B ᵉ/ₜ X} e) = interp_exp g e.
Proof. induction e; cbn; intros; f_equal; eauto using interp_assign_typ. Qed.

Lemma interp_assign_cont :
  (forall d f X B g, interp_typ f B = g X -> (forall Y, Y <> X -> f Y = g Y) ->
      interp_cd f ({B ᶜᵈ/ₜ X} d) = interp_cd g d) /\
  (forall s f X B g, interp_typ f B = g X -> (forall Y, Y <> X -> f Y = g Y) ->
      interp_cs f ({B ᶜˢ/ₜ X} s) = interp_cs g s).
Proof.
  apply contd_conts_mutind; cbn; intros; f_equal; eauto using interp_assign_typ, interp_assign_exp.
Qed.

Lemma interp_assign_work : forall w f X B g,
  interp_typ f B = g X -> (forall Y, Y <> X -> f Y = g Y) ->
  interp_work f ({B ʷ/ₜ X} w) = interp_work g w.
Proof.
  destruct interp_assign_cont.
  destruct w; cbn; intros; f_equal; eauto using interp_assign_typ, interp_assign_exp.
Qed.

Lemma interp_assign_self : forall f X A, assign f X A X = A.
Proof. intros; unfold assign; destruct (eq_var X X); congruence. Qed.

Lemma interp_assign_other : forall f X A Y, Y <> X -> assign f X A Y = f Y.
Proof. intros; unfold assign; destruct (eq_var Y X); congruence. Qed.

Lemma interp_assign_fresh_typ : forall A f X B,
  X `notin` ftvar_in_typ A -> interp_typ (assign f X B) A = interp_typ f A.
Proof.
  intros; apply interp_typ_ext; intros Y HY; apply interp_assign_other; intro; subst; contradiction.
Qed.

Definition finite_assignment (f : assignment) :=
  exists L : atoms, forall X, X `notin` L -> f X = typ_var_f X.

Local Hint Constructors degree_typ_wrt_typ : core.

Lemma degree_open_var : forall A k X,
  degree_typ_wrt_typ k (open_typ_wrt_typ_rec k (typ_var_f X) A) <->
  degree_typ_wrt_typ (S k) A.
Proof.
  induction A; cbn; intros; split; intros H; try solve [constructor];
    try solve [inversion H; subst; constructor;
      first [apply (IHA _ X) | apply (IHA1 _ X) | apply (IHA2 _ X)]; assumption].
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; inversion H; subst; constructor; lia.
  - inversion H; subst.
    destruct (lt_eq_lt_dec n k) as [[?|?]|?]; try constructor; lia.
Qed.

Lemma lc_to_degree : forall A, lc_typ A -> degree_typ_wrt_typ 0 A.
Proof.
  intros A H; induction H; eauto.
  constructor. apply (degree_open_var A 0 (fresh (nil : list atom))). apply H0.
Qed.

Lemma degree_to_lc : forall A, degree_typ_wrt_typ 0 A -> lc_typ A.
Proof.
  assert (Hs : forall A k X, size_typ (open_typ_wrt_typ_rec k (typ_var_f X) A) = size_typ A).
  { induction A; cbn; intros; try solve [rewrite ?IHA, ?IHA1, ?IHA2; reflexivity].
    destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity. }
  assert (H : forall n A, size_typ A < n -> degree_typ_wrt_typ 0 A -> lc_typ A).
  { induction n; intros A Hn Hd; [lia|].
    destruct A; inversion Hd; subst; cbn in Hn.
    all: try solve [apply lc_typ_unit | apply lc_typ_top | apply lc_typ_bot |
                    apply lc_typ_var_f | lia].
    all: constructor; intros; apply IHn.
    all: try solve [lia | assumption].
    - unfold open_typ_wrt_typ; rewrite Hs; lia.
    - apply (degree_open_var _ _ X); assumption. }
  intros A HA. apply (H (S (size_typ A))); [lia|exact HA].
Qed.

Lemma degree_weaken : forall n A, degree_typ_wrt_typ n A ->
  forall m, n <= m -> degree_typ_wrt_typ m A.
Proof.
  intros n A H; induction H; intros m Hm; eauto.
  - apply degree_wrt_typ_typ_var_b. lia.
  - apply degree_wrt_typ_typ_all. apply IHdegree_typ_wrt_typ. lia.
Qed.

Lemma interp_lc : forall A, lc_typ A -> forall f,
  (forall X, lc_typ (f X)) -> lc_typ (interp_typ f A).
Proof.
  intros A HA f Hf. apply degree_to_lc.
  assert (H : forall n A, degree_typ_wrt_typ n A ->
                 degree_typ_wrt_typ n (interp_typ f A)).
  { intros n B HB; induction HB; cbn; eauto.
    eapply degree_weaken; [apply lc_to_degree, Hf|lia]. }
  auto using lc_to_degree.
Qed.

Lemma interp_strong : forall X A, s_in X A -> forall f,
  closed_assignment f -> finite_assignment f ->
  (forall Y, lc_typ (f Y)) -> f X = typ_var_f X -> s_in X (interp_typ f A).
Proof.
  intros X A H; induction H; cbn; intros f Hc [F Hf] Hl HX;
    assert (Hfinite : finite_assignment f) by (exists F; assumption); eauto using interp_lc.
  - rewrite HX; constructor.
  - apply s_in__all with (L := L `union` F); intros Y HY.
    rewrite <- (Hf Y) by fsetdec.
    change (s_in X (open_typ_wrt_typ (interp_typ f A) (interp_typ f (typ_var_f Y)))).
    rewrite <- interp_open_typ by assumption.
    eauto 8.
Qed.


Definition a_typ_map (E : aenv) (f : assignment) (F : aenv) :=
  (forall X, binds X abind_tvar_empty E -> a_wf_typ F (f X)) /\
  (forall X, binds X abind_stvar_empty E -> a_wf_typ F (f X)) /\
  (forall X, binds X abind_etvar_empty E -> a_wf_typ F (f X)).

Definition a_exp_map (E : aenv) (F : aenv) :=
  forall x T, binds x (abind_var_typ T) E -> exists U, binds x (abind_var_typ U) F.

Definition d_typ_map (E : aenv) (f : assignment) (F : denv) :=
  (forall X, binds X abind_tvar_empty E -> d_wf_typ F (f X)) /\
  (forall X, binds X abind_stvar_empty E -> d_wf_typ F (f X)) /\
  (forall X, binds X abind_etvar_empty E -> d_wf_typ F (f X)).

Lemma binds_cons_cases : forall B x y (b c : B) E,
  binds x b ((y,c)::E) -> (x = y /\ b = c) \/ binds x b E.
Proof. unfold binds; simpl; intuition congruence. Qed.

Lemma binds_cons_weak : forall B x y (b c : B) E,
  binds x b E -> binds x b ((y,c)::E).
Proof. unfold binds; simpl; auto. Qed.

Lemma binds_cons_head : forall B x (b : B) E,
  binds x b ((x,b)::E).
Proof. unfold binds; simpl; auto. Qed.

Local Hint Resolve binds_cons_weak binds_cons_head : core.

Lemma a_wf_typ_weak_map : forall E A, a_wf_typ E A ->
  forall F, (forall X b, binds X b E -> binds X b F) -> a_wf_typ F A.
Proof.
  intros E A H; induction H; intros F HF; eauto.
  apply a_wf_typ__all with (L := L); eauto.
  intros X HX; apply H1; auto.
  intros Y b Hb; apply binds_cons_cases in Hb as [[-> ->]|Hb]; eauto.
Qed.

Lemma d_wf_typ_weak_map : forall E A, d_wf_typ E A ->
  forall F, (forall X b, binds X b E -> binds X b F) -> d_wf_typ F A.
Proof.
  intros E A H; induction H; intros F HF; eauto.
  apply d_wf_typ__all with (L := L); eauto.
  intros X HX; apply H1; auto.
  intros Y b Hb; apply binds_cons_cases in Hb as [[-> ->]|Hb]; eauto.
Qed.

Local Hint Resolve a_wf_typ_weak_map d_wf_typ_weak_map : scope_weak.

Local Ltac extend_type_map :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  repeat split; intros Y HY; apply binds_cons_cases in HY as [[-> HE]|HY];
  try discriminate; eauto 7 with scope_weak.

Lemma interp_a_wf_typ : forall E A, a_wf_typ E A -> forall f F,
  closed_assignment f -> finite_assignment f ->
  (forall X, lc_typ (f X)) -> a_typ_map E f F -> a_wf_typ F (interp_typ f A).
Proof.
  intros E A H; induction H; cbn; intros f F Hc [S Hf] Hl Hm;
    assert (Hfinite : finite_assignment f) by (exists S; assumption);
    try solve [pose proof Hm as [Hm1 [Hm2 Hm3]]; eauto 8].
  apply a_wf_typ__all with (L := L `union` S); intros X HX;
    assert (HH : f X = typ_var_f X) by (apply Hf; fsetdec);
    idtac.
  - rewrite <- HH at 1.
    change (s_in X (open_typ_wrt_typ (interp_typ f A) (interp_typ f (typ_var_f X)))).
    rewrite <- interp_open_typ by assumption.
    eapply interp_strong; eauto 8; fsetdec.
  - rewrite <- HH.
    change (a_wf_typ ((X,abind_tvar_empty)::F)
                     (open_typ_wrt_typ (interp_typ f A) (interp_typ f (typ_var_f X)))).
    rewrite <- interp_open_typ by assumption.
    apply H1; [fsetdec | assumption | exists S; assumption | assumption |].
    unfold a_typ_map in *; extend_type_map.
    now rewrite HH; auto.
Qed.

Lemma interp_d_wf_typ : forall E A, a_wf_typ E A -> forall f F,
  closed_assignment f -> finite_assignment f ->
  (forall X, lc_typ (f X)) -> d_typ_map E f F -> d_wf_typ F (interp_typ f A).
Proof.
  intros E A H; induction H; cbn; intros f F Hc [S Hf] Hl Hm;
    assert (Hfinite : finite_assignment f) by (exists S; assumption);
    try solve [pose proof Hm as [Hm1 [Hm2 Hm3]]; eauto 8].
  apply d_wf_typ__all with (L := L `union` S); intros X HX;
    assert (HH : f X = typ_var_f X) by (apply Hf; fsetdec).
  - rewrite <- HH at 1.
    change (s_in X (open_typ_wrt_typ (interp_typ f A) (interp_typ f (typ_var_f X)))).
    rewrite <- interp_open_typ by assumption.
    eapply interp_strong; eauto 8; fsetdec.
  - rewrite <- HH.
    change (d_wf_typ ((X,dbind_tvar_empty)::F)
                     (open_typ_wrt_typ (interp_typ f A) (interp_typ f (typ_var_f X)))).
    rewrite <- interp_open_typ by assumption.
    apply H1; [fsetdec | assumption | exists S; assumption | assumption |].
    unfold d_typ_map in *; extend_type_map.
    now rewrite HH; auto.
Qed.

Lemma a_mono_wf : forall E A, a_mono_typ E A -> a_wf_typ E A.
Proof. intros E A H; induction H; eauto. Qed.

Lemma d_mono_wf : forall E A, d_mono_typ E A -> d_wf_typ E A.
Proof. intros E A H; induction H; eauto. Qed.

Lemma d_mono_lc : forall E A, d_mono_typ E A -> lc_typ A.
Proof. intros E A H; induction H; eauto. Qed.

Lemma d_mono_weak_map : forall E A, d_mono_typ E A ->
  forall F, (forall X, binds X dbind_tvar_empty E -> binds X dbind_tvar_empty F) ->
  d_mono_typ F A.
Proof. intros E A H; induction H; eauto. Qed.

Lemma a_mono_weak_map : forall E A, a_mono_typ E A ->
  forall F, (forall X b, binds X b E -> binds X b F) ->
  a_mono_typ F A.
Proof. intros E A H; induction H; eauto. Qed.

Lemma d_mono_interp : forall E A, a_mono_typ E A ->
  forall f F, (forall X, binds X abind_tvar_empty E -> d_mono_typ F (f X)) ->
  (forall X, binds X abind_etvar_empty E -> d_mono_typ F (f X)) ->
  d_mono_typ F (interp_typ f A).
Proof. intros E A H; induction H; simpl; eauto. Qed.

Lemma a_wf_typ_lc : forall E A, a_wf_typ E A -> lc_typ A.
Proof.
  intros E A HA; induction HA; eauto.
  apply degree_to_lc. constructor.
  pick fresh X for L.
  apply (degree_open_var A 0 X). apply lc_to_degree. apply H1; assumption.
Qed.

Lemma arm_weak : forall E f F X b c,
  a_typ_map E f F ->
  (b = abind_tvar_empty -> a_wf_typ ((X,c)::F) (f X)) ->
  (b = abind_stvar_empty -> a_wf_typ ((X,c)::F) (f X)) ->
  (b = abind_etvar_empty -> a_wf_typ ((X,c)::F) (f X)) ->
  a_typ_map ((X,b)::E) f ((X,c)::F).
Proof. unfold a_typ_map; intros; extend_type_map. Qed.

Lemma arm_app : forall E f F X b,
  a_typ_map E f F -> a_typ_map E f ((X,b)::F).
Proof.
  unfold a_typ_map; intros E f F X b [H1 [H2 H3]]; repeat split; intros;
    eapply a_wf_typ_weak_map; eauto.
Qed.

Lemma are_weak : forall E F x b c,
  a_exp_map E F ->
  (forall T, b = abind_var_typ T -> exists U, c = abind_var_typ U) ->
  a_exp_map ((x,b)::E) ((x,c)::F).
Proof.
  unfold a_exp_map. intros E F x b c H Hc y T Hy.
  apply binds_cons_cases in Hy as [[-> <-]|Hy].
  - destruct (Hc T eq_refl) as [U ->]; eauto.
  - destruct (H _ _ Hy); eauto.
Qed.

Local Hint Resolve arm_weak arm_app are_weak : scope_weak.

Lemma interp_a_wf_exp : forall E e, a_wf_exp E e -> forall f F,
  closed_assignment f -> finite_assignment f ->
  (forall X, lc_typ (f X)) -> a_typ_map E f F -> a_exp_map E F ->
  a_wf_exp F (interp_exp f e).
Proof.
  intros E e He; induction He; cbn; intros f F Hc Hfinite Hl Hm Hme.
  - constructor.
  - destruct (Hme _ _ H); eauto.
  - apply a_wf_exp__abs with (L := L) (T := interp_typ f T).
    + eapply interp_a_wf_typ; eassumption.
    + intros x Hx. rewrite <- interp_open_exp_exp.
      apply H1; try assumption.
      * apply arm_weak; try assumption; discriminate.
      * apply are_weak; try assumption; intros; eexists; reflexivity.
  - constructor; eauto.
  - destruct Hfinite as [S Hf].
    apply a_wf_exp__tabs with (L := L `union` S); intros X HX;
      assert (HH : f X = typ_var_f X) by (apply Hf; fsetdec);
      rewrite <- HH;
      change (f X) with (interp_typ f (typ_var_f X));
      rewrite <- interp_open_typ by assumption.
    + eapply interp_strong; try eassumption.
      * apply H; fsetdec.
      * exists S; assumption.
    + rewrite <- interp_open_exp_typ by assumption.
      change (a_wf_exp ((X,abind_tvar_empty)::F)
        (interp_exp f (exp_anno (open_exp_wrt_typ e (typ_var_f X)) (A ᵗ^ₜ X)))).
      apply H1; try assumption.
      * fsetdec.
      * exists S; assumption.
      * apply arm_weak; try assumption; try discriminate. intros; rewrite HH; eauto.
      * apply are_weak; auto; discriminate.
  - constructor; eauto using interp_a_wf_typ.
  - constructor; eauto using interp_a_wf_typ.
Qed.

Lemma interp_a_wf_cont :
  (forall E s, a_wf_conts E s -> forall f F,
   closed_assignment f -> finite_assignment f ->
   (forall X, lc_typ (f X)) -> a_typ_map E f F -> a_exp_map E F ->
   a_wf_conts F (interp_cs f s)) /\
  (forall E d, a_wf_contd E d -> forall f F,
   closed_assignment f -> finite_assignment f ->
   (forall X, lc_typ (f X)) -> a_typ_map E f F -> a_exp_map E F ->
   a_wf_contd F (interp_cd f d)).
Proof.
  Scheme a_wf_conts_ind2 := Induction for a_wf_conts Sort Prop
  with a_wf_contd_ind2 := Induction for a_wf_contd Sort Prop.
  Combined Scheme a_wf_cont_ind from a_wf_conts_ind2, a_wf_contd_ind2.
  apply a_wf_cont_ind; cbn; intros; constructor;
    try solve [eauto 5 using interp_a_wf_typ, interp_a_wf_exp].
  match goal with
  | H : a_wf_typ _ (typ_arrow ?A ?B) |- a_wf_typ ?F (typ_arrow (interp_typ ?f ?A) (interp_typ ?f ?B)) =>
    change (a_wf_typ F (interp_typ f (typ_arrow A B)));
    eapply interp_a_wf_typ; eassumption
  end.
Qed.

Lemma interp_a_wf_work : forall E w, a_wf_work E w -> forall f F,
  closed_assignment f -> finite_assignment f ->
  (forall X, lc_typ (f X)) -> a_typ_map E f F -> a_exp_map E F ->
  a_wf_work F (interp_work f w).
Proof.
  destruct interp_a_wf_cont.
  intros E w Hw; destruct Hw; cbn; intros; constructor;
    try solve [eauto 5 using interp_a_wf_typ, interp_a_wf_exp].
  all: match goal with
  | H : a_wf_typ _ (typ_arrow ?A ?B) |- a_wf_typ ?F (typ_arrow (interp_typ ?f ?A) (interp_typ ?f ?B)) =>
    change (a_wf_typ F (interp_typ f (typ_arrow A B)));
    eapply interp_a_wf_typ; eassumption
  end.
Qed.

Lemma ftv_open_typ : forall A k B X,
  X `in` ftvar_in_typ A ->
  X `in` ftvar_in_typ (open_typ_wrt_typ_rec k B A).
Proof.
  induction A; cbn; intros; try solve [fsetdec | auto].
  all: fsetdec || (eauto using AtomSetImpl.union_2, AtomSetImpl.union_3) ||
    match goal with
    | H : ?x `in` union ?S ?T |- _ =>
      apply AtomSetImpl.union_1 in H as [H|H];
      [apply AtomSetImpl.union_2 | apply AtomSetImpl.union_3]; eauto
    end.
Qed.

Lemma ftv_open_exp_typ : forall e k B X,
  X `in` ftvar_in_exp e ->
  X `in` ftvar_in_exp (open_exp_wrt_typ_rec k B e).
Proof.
  induction e; cbn; intros; try solve [fsetdec | auto].
  all: apply AtomSetImpl.union_1 in H as [H|H];
    [apply AtomSetImpl.union_2 | apply AtomSetImpl.union_3]; eauto using ftv_open_typ.
Qed.

Lemma ftv_open_exp_exp : forall e k x X,
  X `in` ftvar_in_exp e ->
  X `in` ftvar_in_exp (open_exp_wrt_exp_rec k (exp_var_f x) e).
Proof.
  induction e; cbn; intros; try solve [fsetdec | auto].
  all: apply AtomSetImpl.union_1 in H as [H|H];
    [apply AtomSetImpl.union_2 | apply AtomSetImpl.union_3]; eauto.
Qed.

Lemma d_wf_typ_scope : forall E A, d_wf_typ E A ->
  forall X, X `in` ftvar_in_typ A -> X `in` dom E.
Proof.
  intros E A H; induction H; cbn; intros Y HY; try solve [fsetdec].
  - assert (Y = X) by fsetdec; subst; eauto using binds_In.
  - assert (Y = X) by fsetdec; subst; eauto using binds_In.
  - apply AtomSetImpl.union_1 in HY as [HY|HY]; auto.
  - pick fresh X for (L `union` singleton Y).
    assert (Hd : Y `in` dom ((X,dbind_tvar_empty)::Ψ)).
    { apply H1; try fsetdec. apply ftv_open_typ; assumption. }
    simpl in Hd; fsetdec.
  - apply AtomSetImpl.union_1 in HY as [HY|HY]; auto.
  - apply AtomSetImpl.union_1 in HY as [HY|HY]; auto.
Qed.

Lemma a_wf_typ_scope : forall E A, a_wf_typ E A ->
  forall X, X `in` ftvar_in_typ A -> X `in` dom E.
Proof.
  intros E A H; induction H; cbn; intros Y HY; try solve [fsetdec].
  - assert (Y = X) by fsetdec; subst; eauto using binds_In.
  - assert (Y = X) by fsetdec; subst; eauto using binds_In.
  - assert (Y = X) by fsetdec; subst; eauto using binds_In.
  - apply AtomSetImpl.union_1 in HY as [HY|HY]; auto.
  - pick fresh X for (L `union` singleton Y).
    assert (Hd : Y `in` dom ((X,abind_tvar_empty)::Σ)).
    { apply H1; try fsetdec. apply ftv_open_typ; assumption. }
    simpl in Hd; fsetdec.
  - apply AtomSetImpl.union_1 in HY as [HY|HY]; auto.
  - apply AtomSetImpl.union_1 in HY as [HY|HY]; auto.
Qed.

Lemma a_wf_exp_scope : forall E e, a_wf_exp E e ->
  forall X, X `in` ftvar_in_exp e -> X `in` dom E.
Proof.
  intros E e H; induction H; cbn; intros Y HY; try solve [fsetdec].
  - pick fresh x for (L `union` singleton Y).
    assert (Hd : Y `in` dom ((x,abind_var_typ T)::Σ)).
    { apply H1; try fsetdec. apply ftv_open_exp_exp; assumption. }
    simpl in Hd; fsetdec.
  - apply AtomSetImpl.union_1 in HY as [HY|HY]; auto.
  - pick fresh X for (L `union` singleton Y).
    assert (Hd : Y `in` dom ((X,abind_tvar_empty)::Σ)).
    { apply H1; try fsetdec. simpl.
      apply AtomSetImpl.union_1 in HY as [HY|HY];
        [apply AtomSetImpl.union_2 | apply AtomSetImpl.union_3];
        eauto using ftv_open_exp_typ, ftv_open_typ. }
    simpl in Hd; fsetdec.
  - apply AtomSetImpl.union_1 in HY as [HY|HY]; eauto using a_wf_typ_scope.
  - apply AtomSetImpl.union_1 in HY as [HY|HY]; eauto using a_wf_typ_scope.
Qed.

Local Ltac solve_scope :=
  repeat match goal with H : _ `in` union _ _ |- _ => apply AtomSetImpl.union_1 in H as [H|H] end;
  first [solve [auto] |
    match goal with
    | H : a_wf_typ _ ?A, Hx : _ `in` ftvar_in_typ ?A |- _ =>
        exact (a_wf_typ_scope _ _ H _ Hx)
    | H : a_wf_exp _ ?e, Hx : _ `in` ftvar_in_exp ?e |- _ =>
        exact (a_wf_exp_scope _ _ H _ Hx)
    end].

Lemma a_wf_cont_scope :
  (forall E s, a_wf_conts E s -> forall X, X `in` ftvar_in_conts s -> X `in` dom E) /\
  (forall E d, a_wf_contd E d -> forall X, X `in` ftvar_in_contd d -> X `in` dom E).
Proof.
  apply a_wf_cont_ind; cbn; intros;
    repeat match goal with H : a_wf_typ _ (typ_arrow _ _) |- _ => inversion H; subst; clear H end;
    solve_scope.
Qed.

Lemma a_wf_work_scope : forall E w, a_wf_work E w ->
  forall X, X `in` ftvar_in_work w -> X `in` dom E.
Proof.
  destruct a_wf_cont_scope as [Hs Hd].
  intros E w Hw; destruct Hw; cbn; intros;
    repeat match goal with H : a_wf_typ _ (typ_arrow _ _) |- _ => inversion H; subst; clear H end;
    repeat match goal with H : _ `in` union _ _ |- _ => apply AtomSetImpl.union_1 in H as [H|H] end;
    first [solve_scope | solve [eapply Hs; eassumption] | solve [eapply Hd; eassumption]].
Qed.

Lemma interp_typ_id : forall A f,
  (forall X, X `in` ftvar_in_typ A -> f X = typ_var_f X) ->
  interp_typ f A = A.
Proof.
  assert (I : forall A, interp_typ typ_var_f A = A) by (induction A; simpl; congruence).
  intros; rewrite <- (I A) at 2; apply interp_typ_ext; exact H.
Qed.

Lemma interp_exp_id : forall e f,
  (forall X, X `in` ftvar_in_exp e -> f X = typ_var_f X) ->
  interp_exp f e = e.
Proof.
  assert (I : forall e, interp_exp typ_var_f e = e).
  { induction e; simpl; try reflexivity; f_equal; auto using interp_typ_id. }
  intros; rewrite <- (I e) at 2; apply interp_exp_ext; exact H.
Qed.

Lemma a_typ_map_weak : forall E F,
  (forall X b, binds X b E -> binds X b F) -> a_typ_map E typ_var_f F.
Proof. unfold a_typ_map; intros; repeat split; eauto. Qed.

Lemma a_exp_map_weak : forall E F,
  (forall X b, binds X b E -> binds X b F) -> a_exp_map E F.
Proof. unfold a_exp_map; eauto. Qed.

Lemma id_assignment_closed : closed_assignment typ_var_f.
Proof. intros X k B; reflexivity. Qed.

Lemma id_assignment_finite : finite_assignment typ_var_f.
Proof. exists ({} : atoms); reflexivity. Qed.

Lemma id_assignment_lc : forall X, lc_typ (typ_var_f X).
Proof. constructor. Qed.

Local Hint Resolve id_assignment_closed id_assignment_finite id_assignment_lc : core.

Lemma a_wf_exp_weak_map : forall E e, a_wf_exp E e ->
  forall F, (forall X b, binds X b E -> binds X b F) -> a_wf_exp F e.
Proof.
  intros E e He F HF.
  rewrite <- (interp_exp_id e typ_var_f) by reflexivity.
  eapply interp_a_wf_exp; eauto using a_typ_map_weak, a_exp_map_weak.
Qed.

Lemma a_wf_exp_retype : forall E e, a_wf_exp E e ->
  forall F,
    (forall X b, binds X b E -> (forall T, b <> abind_var_typ T) -> binds X b F) ->
    a_exp_map E F -> a_wf_exp F e.
Proof.
  intros E e He F HF HM.
  rewrite <- (interp_exp_id e typ_var_f) by reflexivity.
  eapply interp_a_wf_exp; eauto.
  - unfold a_typ_map; repeat split; intros; cbn; constructor; apply HF; auto; discriminate.
Qed.

Lemma a_wf_abs_open : forall E e T,
  a_wf_exp E (exp_abs e) -> exists L,
  forall x, x `notin` L -> a_wf_exp ((x,abind_var_typ T)::E) (open_exp_wrt_exp e (exp_var_f x)).
Proof.
  intros E e T H; inversion H; subst; exists L; intros x Hx.
  eapply a_wf_exp_retype; [eauto| |].
  - intros Y b Hb Hnot; apply binds_cons_cases in Hb as [[-> ->]|Hb];
      [exfalso; eapply Hnot; reflexivity | eauto].
  - apply are_weak; unfold a_exp_map; eauto.
Qed.

Lemma interp_cs_id : forall cs, interp_cs typ_var_f cs = cs.
Proof.
  assert (H : (forall d, interp_cd typ_var_f d = d) /\ (forall s, interp_cs typ_var_f s = s)).
  { apply contd_conts_mutind; cbn; intros; f_equal; eauto using interp_exp_id, interp_typ_id. }
  tauto.
Qed.

Lemma interp_cd_id : forall cd, interp_cd typ_var_f cd = cd.
Proof.
  assert (H : forall d, conts_infabs (interp_cd typ_var_f d) = conts_infabs d).
  { intro; apply (interp_cs_id (conts_infabs d)). }
  intro; specialize (H cd); congruence.
Qed.

Lemma interp_work_id : forall w, interp_work typ_var_f w = w.
Proof. destruct w; cbn; f_equal; auto using interp_exp_id, interp_typ_id, interp_cs_id, interp_cd_id. Qed.

Lemma a_wf_work_weak_map : forall E w, a_wf_work E w ->
  forall F, (forall X b, binds X b E -> binds X b F) -> a_wf_work F w.
Proof.
  intros E w Hw F HF.
  rewrite <- (interp_work_id w).
  eapply interp_a_wf_work; eauto using a_typ_map_weak, a_exp_map_weak.
Qed.

Lemma val_lc_map : forall X A,
  lc_typ A -> forall Y, lc_typ (assign typ_var_f X A Y).
Proof. unfold assign; intros; destruct (eq_var Y X); eauto. Qed.

Lemma val_closed_map : forall X E A,
  a_mono_typ E A -> closed_assignment (assign typ_var_f X A).
Proof.
  intros X E A H; unfold closed_assignment, assign; intros Y k B.
  destruct (eq_var Y X); [|reflexivity].
  induction H; cbn; congruence.
Qed.

Lemma val_finite_map : forall X A, finite_assignment (assign typ_var_f X A).
Proof.
  intros; exists (singleton X); intros Y HY; apply interp_assign_other; fsetdec.
Qed.

Lemma awl_to_aenv_app : forall G H,
  awl_to_aenv (awl_app G H) = awl_to_aenv G ++ awl_to_aenv H.
Proof. induction G; intros; simpl; rewrite ?IHG; reflexivity. Qed.

Lemma awl_to_aenv_subst : forall G X B,
  awl_to_aenv (subst_typ_in_aworklist B X G) =
  List.map (fun p => (fst p, subst_typ_in_abind B X (snd p))) (awl_to_aenv G).
Proof. induction G; intros; simpl; rewrite ?IHG; reflexivity. Qed.

Definition worklist_dom (G : aworklist) := dom (awl_to_aenv G).

Lemma worklist_dom_app : forall G H,
  worklist_dom (awl_app G H) [=] worklist_dom G `union` worklist_dom H.
Proof. unfold worklist_dom; intros; rewrite awl_to_aenv_app, dom_app; fsetdec. Qed.

Lemma worklist_dom_subst : forall G X B,
  worklist_dom (subst_typ_in_aworklist B X G) [=] worklist_dom G.
Proof.
  unfold worklist_dom; induction G; intros; simpl; try rewrite IHG; fsetdec.
Qed.

Lemma awl_unique : forall G, a_wf_wwl G -> uniq (awl_to_aenv G).
Proof. intros G H; induction H; cbn; eauto using uniq_cons, uniq_nil. Qed.

Lemma awl_wf_prefix : forall S G, a_wf_wwl (awl_app S G) -> a_wf_wwl G.
Proof. induction S; simpl; intros; auto; inversion H; eauto. Qed.

Lemma awl_wf_insert_etvar : forall S G Y,
  a_wf_wwl (awl_app S G) ->
  Y `notin` worklist_dom (awl_app S G) ->
  a_wf_wwl (awl_app S (aworklist_cons_var G Y abind_etvar_empty)).
Proof.
  induction S; cbn; intros G Y HW HY.
  - apply a_wf_wwl__consetvar; auto.
  - inversion HW; subst; clear HW; constructor.
    all: try solve [apply IHS; [assumption|unfold worklist_dom in *; cbn in *; fsetdec]].
    all: try solve [
      unfold worklist_dom in *; rewrite !awl_to_aenv_app in *; cbn in *;
      rewrite !dom_app in *; cbn in *; fsetdec].
    eapply a_wf_typ_weak_map; [eassumption|].
    rewrite !awl_to_aenv_app. cbn. unfold binds. intros.
    apply in_app_or in H as [H|H]; apply in_or_app; simpl; auto.
  - inversion HW; subst; clear HW; apply a_wf_wwl__conswork.
    + eapply a_wf_work_weak_map; [eassumption|].
      rewrite !awl_to_aenv_app. cbn. unfold binds. intros.
      apply in_app_or in H as [H|H]; apply in_or_app; simpl; auto.
    + apply IHS; auto.
Qed.

Lemma a_subst_morphism : forall E F X B,
  a_mono_typ F B ->
  (forall Y b, binds Y b E -> Y <> X ->
     binds Y (subst_typ_in_abind B X b) F) ->
  (forall b, binds X b E -> b = abind_etvar_empty) ->
  a_typ_map E (assign typ_var_f X B) F.
Proof.
  unfold a_typ_map; intros E F X B HB HE HX.
  repeat split; intros Y HY; destruct (eq_var Y X) as [->|Hn].
  - specialize (HX _ HY); discriminate.
  - rewrite interp_assign_other by assumption. apply a_wf_typ__tvar.
    exact (HE _ _ HY Hn).
  - specialize (HX _ HY); discriminate.
  - rewrite interp_assign_other by assumption. apply a_wf_typ__stvar.
    exact (HE _ _ HY Hn).
  - rewrite interp_assign_self; eauto using a_mono_wf.
  - rewrite interp_assign_other by assumption. apply a_wf_typ__etvar.
    exact (HE _ _ HY Hn).
Qed.

Lemma a_subst_work_valid : forall E F X B w,
  a_mono_typ F B ->
  (forall Y b, binds Y b E -> Y <> X ->
     binds Y (subst_typ_in_abind B X b) F) ->
  (forall b, binds X b E -> b = abind_etvar_empty) ->
  a_wf_work E w -> a_wf_work F ({B ʷ/ₜ X} w).
Proof.
  intros E F X B w HB HE HX Hw.
  rewrite <- (interp_work_id ({B ʷ/ₜ X} w)).
  erewrite interp_assign_work with (g := assign typ_var_f X B).
  - eapply interp_a_wf_work; eauto using val_closed_map, val_finite_map, val_lc_map,
      a_mono_wf, a_wf_typ_lc.
    + eapply a_subst_morphism; eassumption.
    + intros y T Hy. exists ({B ᵗ/ₜ X}T).
      apply (HE y (abind_var_typ T)); auto.
      intros ->. specialize (HX _ Hy); discriminate.
  - rewrite interp_assign_self; apply interp_typ_id; reflexivity.
  - intros; rewrite interp_assign_other by assumption; reflexivity.
Qed.

Lemma a_subst_type_valid : forall E F X B A,
  a_mono_typ F B ->
  (forall Y b, binds Y b E -> Y <> X ->
     binds Y (subst_typ_in_abind B X b) F) ->
  (forall b, binds X b E -> b = abind_etvar_empty) ->
  a_wf_typ E A -> a_wf_typ F ({B ᵗ/ₜ X} A).
Proof.
  intros E F X B A HB HE HX HA.
  rewrite <- (interp_typ_id ({B ᵗ/ₜ X} A) typ_var_f) by reflexivity.
  erewrite interp_assign_typ with (g := assign typ_var_f X B).
  - eapply interp_a_wf_typ; eauto using val_closed_map, val_finite_map, val_lc_map,
      a_mono_wf, a_wf_typ_lc.
    eapply a_subst_morphism; eassumption.
  - rewrite interp_assign_self; apply interp_typ_id; reflexivity.
  - intros; rewrite interp_assign_other by assumption; reflexivity.
Qed.

(* A solution may mention only the ordinary type variables declared
   before its existential. The projection erases existential declarations. *)
Fixpoint regulars (G : aworklist) : denv :=
  match G with
  | aworklist_empty => nil
  | aworklist_cons_var G X abind_tvar_empty => (X,dbind_tvar_empty)::regulars G
  | aworklist_cons_var G _ _ | aworklist_cons_work G _ => regulars G
  end.

Fixpoint interp_env (f : assignment) (G : aworklist) : denv :=
  match G with
  | aworklist_empty => nil
  | aworklist_cons_var G X abind_tvar_empty => (X,dbind_tvar_empty)::interp_env f G
  | aworklist_cons_var G X abind_stvar_empty => (X,dbind_stvar_empty)::interp_env f G
  | aworklist_cons_var G _ abind_etvar_empty => interp_env f G
  | aworklist_cons_var G x (abind_var_typ A) => (x,dbind_typ (interp_typ f A))::interp_env f G
  | aworklist_cons_work G _ => interp_env f G
  end.

Fixpoint interp_wl (f : assignment) (G : aworklist) : dworklist :=
  match G with
  | aworklist_empty => dworklist_empty
  | aworklist_cons_var G X abind_tvar_empty => dworklist_cons_var (interp_wl f G) X dbind_tvar_empty
  | aworklist_cons_var G X abind_stvar_empty => dworklist_cons_var (interp_wl f G) X dbind_stvar_empty
  | aworklist_cons_var G _ abind_etvar_empty => interp_wl f G
  | aworklist_cons_var G x (abind_var_typ A) => dworklist_cons_var (interp_wl f G) x (dbind_typ (interp_typ f A))
  | aworklist_cons_work G w => dworklist_cons_work (interp_wl f G) (interp_work f w)
  end.

Fixpoint scoped_assignment (f : assignment) (G : aworklist) : Prop :=
  match G with
  | aworklist_empty => True
  | aworklist_cons_var G X abind_etvar_empty =>
     d_mono_typ (regulars G) (f X) /\ scoped_assignment f G
  | aworklist_cons_var G _ _ | aworklist_cons_work G _ => scoped_assignment f G
  end.

Definition valid_assignment (f : assignment) (G : aworklist) :=
  scoped_assignment f G /\
  forall X, ~ binds X abind_etvar_empty (awl_to_aenv G) -> f X = typ_var_f X.

Lemma interp_wl_env : forall G f, dwl_to_denv (interp_wl f G) = interp_env f G.
Proof. induction G; intros; cbn; try destruct ab; cbn; rewrite ?IHG; reflexivity. Qed.

Lemma regulars_app : forall S G,
  regulars (awl_app S G) = regulars S ++ regulars G.
Proof. induction S; intros; cbn; try destruct ab; cbn; rewrite ?IHS; reflexivity. Qed.

Lemma regulars_subst : forall G X B,
  regulars (subst_typ_in_aworklist B X G) = regulars G.
Proof. induction G; intros; cbn; try destruct ab; cbn; rewrite ?IHG; reflexivity. Qed.

Lemma regulars_binds : forall G X,
  binds X dbind_tvar_empty (regulars G) <-> binds X abind_tvar_empty (awl_to_aenv G).
Proof.
  induction G as [|G IH X b|G IH w]; intros Y.
  - unfold binds; cbn; tauto.
  - specialize (IH Y). destruct b; cbn; unfold binds in *; cbn in *.
    + split; intros [H|H]; [left|right|left|right].
      * injection H as EQ; subst; reflexivity.
      * apply IH; assumption.
      * injection H as EQ; subst; reflexivity.
      * apply IH; assumption.
    + intuition congruence.
    + intuition congruence.
    + intuition congruence.
  - apply IH.
Qed.

Lemma regulars_interp_binds : forall G f X,
  binds X dbind_tvar_empty (regulars G) -> binds X dbind_tvar_empty (interp_env f G).
Proof.
  induction G as [|G IH X b|G IH w]; intros f Y H.
  - exact H.
  - specialize (IH f Y). destruct b; cbn in *; unfold binds in *; cbn in *; tauto.
  - apply IH; exact H.
Qed.

Lemma interp_env_dom : forall G f X,
  X `in` dom (interp_env f G) -> X `in` worklist_dom G.
Proof.
  unfold worklist_dom. induction G as [|G IH Y b|G IH w]; intros f X H; cbn in *.
  - exact H.
  - specialize (IH f X). destruct b; simpl in *; fsetdec.
  - apply (IH f); exact H.
Qed.

Lemma scoped_assignment_binds : forall G f X,
  scoped_assignment f G ->
  binds X abind_etvar_empty (awl_to_aenv G) -> d_mono_typ (regulars G) (f X).
Proof.
  induction G; intros f Y Hv Hb; cbn in *; try solve [contradiction | eauto].
  apply binds_cons_cases in Hb as [[-> <-]|Hb].
  - cbn in *; tauto.
  - destruct ab; cbn in *; eauto using d_mono_weak_map.
    eapply IHG; tauto.
Qed.

Lemma etvar_binds_dec : forall G X,
  sumbool (binds X abind_etvar_empty (awl_to_aenv G))
    (~ binds X abind_etvar_empty (awl_to_aenv G)).
Proof.
  induction G as [|G IHG Y ab|G IHG w]; intros X; simpl.
  - right; unfold binds; auto.
  - destruct (IHG X) as [Hb|Hb]; [left; auto|].
    destruct (eq_var X Y) as [->|Hn]; destruct ab;
      try solve [right; intro H; apply binds_cons_cases in H as [[? ?]|?]; congruence].
    left; auto.
  - apply IHG.
Qed.

Lemma valid_assignment_facts : forall f G,
  valid_assignment f G ->
  closed_assignment f /\ finite_assignment f /\ (forall X, lc_typ (f X)).
Proof.
  intros f G [Hs Hi].
  assert (HM : forall X, (exists E, d_mono_typ E (f X)) \/ f X = typ_var_f X).
  { intro X; destruct (etvar_binds_dec G X) as [H|H].
    - left. exists (regulars G). eapply scoped_assignment_binds; eassumption.
    - right; auto. }
  repeat split.
  - intros X k B. destruct (HM X) as [[E H] | ->]; eauto using open_mono_rec.
  - exists (worklist_dom G). intros X HX; apply Hi; intro; apply HX.
    unfold worklist_dom; eauto using binds_In.
  - intros X. destruct (HM X) as [[E H] | ->]; eauto using d_mono_lc.
Qed.

(* Solving an existential moves only the existential declarations needed
   by its solution. These lemmas track the resulting scopes. *)
Lemma aws_permutation : forall G X B P S,
  aworklist_subst G X B P S ->
  Permutation (awl_to_aenv G)
              (awl_to_aenv S ++ (X,abind_etvar_empty)::awl_to_aenv P).
Proof.
  intros G X B P S H; induction H; simpl; try solve [constructor | now apply perm_skip | assumption].
  rewrite awl_to_aenv_app in *; simpl in *.
  eapply Permutation_trans; [|eassumption].
  eapply Permutation_trans; [apply Permutation_middle|].
  apply Permutation_app_head, perm_swap.
Qed.

Lemma aws_binds : forall G X B P S Y b,
  aworklist_subst G X B P S ->
  (binds Y b (awl_to_aenv G) <->
   binds Y b (awl_to_aenv S ++ (X,abind_etvar_empty)::awl_to_aenv P)).
Proof.
  intros; pose proof (aws_permutation _ _ _ _ _ H) as Hp.
  unfold binds; split; eauto using Permutation_in, Permutation_sym.
Qed.

Lemma binds_equiv_dom : forall E F : aenv,
  (forall X b, binds X b E <-> binds X b F) -> dom E [=] dom F.
Proof.
  intros E F H X; split; intro Hin;
    apply binds_In_inv in Hin as [b Hb]; eapply binds_In.
  - apply (proj1 (H X b)); exact Hb.
  - apply (proj2 (H X b)); exact Hb.
Qed.

Lemma aws_dom : forall G X B P S,
  aworklist_subst G X B P S ->
  worklist_dom G [=] worklist_dom S `union` singleton X `union` worklist_dom P.
Proof.
  intros G X B P S H.
  pose proof (binds_equiv_dom _ _ (fun Y b => aws_binds _ _ _ _ _ Y b H)) as Hd.
  unfold worklist_dom. rewrite Hd, dom_app. simpl. fsetdec.
Qed.

Lemma mono_env_transport : forall E B,
  a_mono_typ E B -> forall F,
  (forall Y, Y `in` ftvar_in_typ B ->
    (binds Y abind_tvar_empty E -> binds Y abind_tvar_empty F) /\
    (binds Y abind_etvar_empty E -> binds Y abind_etvar_empty F)) ->
  a_mono_typ F B.
Proof.
  intros E B H; induction H; simpl; intros F HF; eauto.
  - apply a_mono_typ__tvar. apply (HF X); [fsetdec|assumption].
  - apply a_mono_typ__etvar. apply (HF X); [fsetdec|assumption].
  - constructor; [apply IHa_mono_typ1|apply IHa_mono_typ2]; intros; apply HF; fsetdec.
Qed.

Lemma aws_mono : forall G X B P S,
  aworklist_subst G X B P S ->
  a_mono_typ (awl_to_aenv G) B ->
  X `notin` ftvar_in_typ B ->
  a_mono_typ (awl_to_aenv P) B.
Proof.
  intros G X B P S H; induction H; simpl; intros HM Hx.
  - eapply mono_env_transport; [eassumption|].
    intros Y HY; split; intros Hb; apply binds_cons_cases in Hb as [[? ?]|?]; try congruence; fsetdec.
  - apply IHaworklist_subst; auto.
    eapply mono_env_transport; [eassumption|].
    intros Y' HY'; split; intros Hb; apply binds_cons_cases in Hb as [[? ?]|?]; congruence.
  - apply IHaworklist_subst; auto.
    eapply mono_env_transport; [eassumption|].
    intros Y' HY'; split; intros Hb; apply binds_cons_cases in Hb as [[? ?]|?]; try congruence; fsetdec.
  - apply IHaworklist_subst; auto.
    eapply mono_env_transport; [eassumption|].
    intros Y' HY'; split; intros Hb; apply binds_cons_cases in Hb as [[? ?]|?]; congruence.
  - auto.
  - apply IHaworklist_subst; auto.
    eapply mono_env_transport; [eassumption|].
    intros Y' HY'; split; intros Hb; apply binds_cons_cases in Hb as [[? ?]|?]; try congruence; fsetdec.
  - apply IHaworklist_subst; auto.
    eapply a_mono_weak_map; [eassumption|].
    rewrite !awl_to_aenv_app. simpl. unfold binds. intros.
    destruct H2 as [H2|H2].
    + apply in_or_app; right; simpl; tauto.
    + apply in_app_or in H2 as [H2|H2]; apply in_or_app; [now left|right].
      simpl in *; tauto.
Qed.

Lemma awl_app_assoc : forall S T G,
  awl_app (awl_app S T) G = awl_app S (awl_app T G).
Proof. induction S; intros; simpl; rewrite ?IHS; reflexivity. Qed.

Lemma aws_source_reordered : forall G X B P S,
  aworklist_subst G X B P S ->
  a_wf_wwl G ->
  a_wf_wwl (awl_app S (aworklist_cons_var P X abind_etvar_empty)).
Proof.
  intros G X B P S H; induction H; intros HW; simpl.
  - assumption.
  - inversion HW; subst; clear HW. apply a_wf_wwl__consvar.
    + pose proof (aws_dom _ _ _ _ _ H) as Hd. unfold worklist_dom in Hd.
      rewrite awl_to_aenv_app, dom_app. simpl. fsetdec.
    + eapply a_wf_typ_weak_map; [eassumption|].
      rewrite awl_to_aenv_app. simpl. intros; apply (aws_binds _ _ _ _ _ _ _ H); assumption.
    + auto.
  - inversion HW; subst; clear HW. apply a_wf_wwl__constvar; auto.
    pose proof (aws_dom _ _ _ _ _ H) as Hd. unfold worklist_dom in Hd.
    rewrite awl_to_aenv_app, dom_app. simpl. fsetdec.
  - inversion HW; subst; clear HW. apply a_wf_wwl__consstvar; auto.
    pose proof (aws_dom _ _ _ _ _ H) as Hd. unfold worklist_dom in Hd.
    rewrite awl_to_aenv_app, dom_app. simpl. fsetdec.
  - inversion HW; subst; clear HW. apply a_wf_wwl__conswork; auto.
    eapply a_wf_work_weak_map; [eassumption|].
    rewrite awl_to_aenv_app. simpl. intros; apply (aws_binds _ _ _ _ _ _ _ H); assumption.
  - inversion HW; subst; clear HW. apply a_wf_wwl__consetvar; auto.
    pose proof (aws_dom _ _ _ _ _ H) as Hd. unfold worklist_dom in Hd.
    rewrite awl_to_aenv_app, dom_app. simpl. fsetdec.
  - inversion HW; subst; clear HW. apply IHaworklist_subst.
    change (a_wf_wwl (awl_app Γ2 (awl_app (aworklist_cons_var aworklist_empty X abind_etvar_empty)
                 (aworklist_cons_var Γ1 Y abind_etvar_empty)))).
    rewrite <- awl_app_assoc. apply awl_wf_insert_etvar.
    + rewrite awl_app_assoc. simpl. assumption.
    + unfold worklist_dom in *. rewrite !awl_to_aenv_app in *. simpl in *.
      rewrite !dom_app in *. simpl in *. fsetdec.
Qed.

Lemma awl_bind_type_wf : forall G,
  a_wf_wwl G -> forall z A, binds z (abind_var_typ A) (awl_to_aenv G) ->
  a_wf_typ (awl_to_aenv G) A.
Proof.
  intros G HW; induction HW; cbn; intros z U Hz.
  - exact (False_rect _ Hz).
  - apply binds_cons_cases in Hz as [[_ E]|Hz].
    + injection E as ->. eapply a_wf_typ_weak_map; [eassumption|eauto].
    + eapply a_wf_typ_weak_map; [eapply IHHW; eassumption|eauto].
  - apply binds_cons_cases in Hz as [[_ E]|Hz]; [discriminate|].
    eapply a_wf_typ_weak_map; [eapply IHHW; eassumption|eauto].
  - apply binds_cons_cases in Hz as [[_ E]|Hz]; [discriminate|].
    eapply a_wf_typ_weak_map; [eapply IHHW; eassumption|eauto].
  - apply binds_cons_cases in Hz as [[_ E]|Hz]; [discriminate|].
    eapply a_wf_typ_weak_map; [eapply IHHW; eassumption|eauto].
  - eauto.
Qed.

Lemma awl_subst_suffix_binds : forall S G X B Y b,
  a_wf_wwl G ->
  X `notin` worklist_dom G ->
  Y <> X ->
  binds Y b (awl_to_aenv (awl_app S (aworklist_cons_var G X abind_etvar_empty))) ->
  binds Y (subst_typ_in_abind B X b)
    (awl_to_aenv (awl_app (subst_typ_in_aworklist B X S) G)).
Proof.
  intros S G X B Y b HW Hx Hneq Hb.
  rewrite !awl_to_aenv_app, awl_to_aenv_subst in *; simpl in Hb.
  unfold binds in *. apply in_app_or in Hb as [Hb|Hb]; apply in_or_app.
  - left. change ((Y, subst_typ_in_abind B X b)) with
      ((fun p => (fst p, subst_typ_in_abind B X (snd p))) (Y,b)).
    apply in_map; auto.
  - right. simpl in Hb. destruct Hb as [Hb|Hb]; [congruence|].
    destruct b; simpl; auto.
    assert (Hr : X `notin` ftvar_in_typ A).
    { intro Hi. apply Hx. eapply a_wf_typ_scope; [eapply awl_bind_type_wf; eassumption|exact Hi]. }
    assert (Hid : subst_typ_in_typ B X A = A).
    { rewrite <- (interp_typ_id (subst_typ_in_typ B X A) typ_var_f) by reflexivity.
      rewrite (interp_assign_typ A typ_var_f X B (assign typ_var_f X B)).
      - rewrite interp_assign_fresh_typ by assumption; apply interp_typ_id; reflexivity.
      - rewrite interp_assign_self; apply interp_typ_id; reflexivity.
      - intros; symmetry; apply interp_assign_other; assumption. }
    now rewrite Hid.
Qed.

Lemma awl_subst_suffix_wf : forall S G X B,
  a_wf_wwl (awl_app S (aworklist_cons_var G X abind_etvar_empty)) ->
  a_mono_typ (awl_to_aenv G) B ->
  a_wf_wwl (awl_app (subst_typ_in_aworklist B X S) G).
Proof.
  induction S as [|S IH Y b|S IH w]; intros G X B HW HB; cbn in *.
  - inversion HW; assumption.
  - assert (Htail : a_wf_wwl (awl_app S (aworklist_cons_var G X abind_etvar_empty))) by (inversion HW; assumption).
    assert (HgX : a_wf_wwl (aworklist_cons_var G X abind_etvar_empty)) by (eapply awl_wf_prefix; eassumption).
    assert (Hg : a_wf_wwl G) by (inversion HgX; assumption).
    assert (Hx : X `notin` worklist_dom G) by (inversion HgX; assumption).
    assert (Hnew : a_wf_wwl (awl_app (subst_typ_in_aworklist B X S) G)) by eauto.
    assert (Hfresh : Y `notin` worklist_dom (awl_app (subst_typ_in_aworklist B X S) G)).
    { pose proof (worklist_dom_app S (aworklist_cons_var G X abind_etvar_empty)).
      pose proof (worklist_dom_app (subst_typ_in_aworklist B X S) G).
      pose proof (worklist_dom_subst S X B).
      inversion HW; subst; unfold worklist_dom in *; simpl in *; fsetdec. }
    destruct b; cbn; eauto.
    apply a_wf_wwl__consvar; try assumption.
    inversion HW; subst.
    eapply a_subst_type_valid.
    + eapply a_mono_weak_map; [eassumption|].
      rewrite awl_to_aenv_app. unfold binds; auto using in_or_app.
    + intros; eapply awl_subst_suffix_binds; eassumption.
    + intros b Hb. eapply binds_unique; [eassumption| |apply awl_unique; exact Htail].
      rewrite awl_to_aenv_app. unfold binds; apply in_or_app; right; left; reflexivity.
    + eassumption.
  - inversion HW; subst; clear HW. apply a_wf_wwl__conswork; eauto.
    assert (HgX : a_wf_wwl (aworklist_cons_var G X abind_etvar_empty)) by (eapply awl_wf_prefix; eassumption).
    assert (Hg : a_wf_wwl G) by (inversion HgX; assumption).
    assert (Hx : X `notin` worklist_dom G) by (inversion HgX; assumption).
    eapply a_subst_work_valid.
    + eapply a_mono_weak_map; [eassumption|].
      rewrite awl_to_aenv_app. unfold binds; auto using in_or_app.
    + intros; eapply awl_subst_suffix_binds; eassumption.
    + intros b Hb. eapply binds_unique; [eassumption| |apply awl_unique; eassumption].
      rewrite awl_to_aenv_app. unfold binds; apply in_or_app; right; left; reflexivity.
    + eassumption.
Qed.

Lemma aws_target_wf : forall G X B P S,
  aworklist_subst G X B P S ->
  a_wf_wwl G ->
  a_mono_typ (awl_to_aenv G) B ->
  X `notin` ftvar_in_typ B ->
  a_wf_wwl (awl_app (subst_typ_in_aworklist B X S) P).
Proof.
  intros. apply awl_subst_suffix_wf; eauto using aws_source_reordered, aws_mono.
Qed.

Lemma degree_open_same : forall n A, degree_typ_wrt_typ n A ->
  forall k B, n <= k -> open_typ_wrt_typ_rec k B A = A.
Proof.
  intros n A H; induction H; intros k B Hk; cbn; try reflexivity.
  - destruct (lt_eq_lt_dec n2 k) as [[?|?]|?]; auto; lia.
  - f_equal; eauto.
  - f_equal. apply IHdegree_typ_wrt_typ. lia.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma lc_open_same : forall A, lc_typ A -> forall k B,
  open_typ_wrt_typ_rec k B A = A.
Proof. intros; eapply degree_open_same; [eauto using lc_to_degree|lia]. Qed.

Lemma valid_update_lc : forall X B, lc_typ B ->
  closed_assignment (assign typ_var_f X B).
Proof.
  intros X B HB Y k C. unfold assign; destruct (eq_var Y X);
    eauto using lc_open_same.
Qed.

Lemma a_wf_open_all : forall E A B,
  a_wf_typ E (typ_all A) -> a_wf_typ E B ->
  a_wf_typ E (open_typ_wrt_typ A B).
Proof.
  intros E A B HA HB; inversion HA; subst.
  pick fresh X for (L `union` dom E `union` ftvar_in_typ A).
  assert (HF : finite_assignment (assign typ_var_f X B)) by apply val_finite_map.
  assert (HL : forall Y, lc_typ (assign typ_var_f X B Y)) by (apply val_lc_map; eauto using a_wf_typ_lc).
  assert (HC : closed_assignment (assign typ_var_f X B)) by (apply valid_update_lc; eauto using a_wf_typ_lc).
  match goal with Hbody : forall X, X `notin` L -> a_wf_typ _ _ |- _ =>
    pose proof (interp_a_wf_typ _ _ (Hbody X ltac:(fsetdec)) _ E HC HF HL) as HP
  end.
  rewrite interp_open_typ in HP by assumption.
  rewrite interp_assign_fresh_typ, interp_typ_id in HP by (reflexivity || fsetdec).
  change (interp_typ (assign typ_var_f X B) (typ_var_f X)) with (assign typ_var_f X B X) in HP.
  rewrite interp_assign_self in HP. apply HP.
  unfold a_typ_map; repeat split; intros Y HY;
    apply binds_cons_cases in HY as [[-> E0]|HY]; try discriminate.
  - rewrite interp_assign_self; assumption.
  - rewrite interp_assign_other; [eauto|].
    intro; subst; eapply binds_dom_contradiction; [eassumption|fsetdec].
  - rewrite interp_assign_other; [eauto|].
    intro; subst; eapply binds_dom_contradiction; [eassumption|fsetdec].
  - rewrite interp_assign_other; [eauto|].
    intro; subst; eapply binds_dom_contradiction; [eassumption|fsetdec].
Qed.

Lemma a_wf_open_all_extend : forall E A X b,
  a_wf_typ E (typ_all A) ->
  a_wf_typ ((X,b)::E) (typ_var_f X) ->
  a_wf_typ ((X,b)::E) (open_typ_wrt_typ A (typ_var_f X)).
Proof. intros; eapply a_wf_open_all; [eapply a_wf_typ_weak_map|]; eauto. Qed.

Lemma interp_env_tvar_binds : forall G f X,
  binds X abind_tvar_empty (awl_to_aenv G) ->
  binds X dbind_tvar_empty (interp_env f G).
Proof. intros; apply regulars_interp_binds, regulars_binds; assumption. Qed.

Lemma interp_env_stvar_binds : forall G f X,
  binds X abind_stvar_empty (awl_to_aenv G) ->
  binds X dbind_stvar_empty (interp_env f G).
Proof.
  induction G as [|G IH Y b|G IH w]; intros f X H; cbn in *.
  - exact (False_rect _ H).
  - apply binds_cons_cases in H as [[-> <-]|H]; simpl; auto.
    specialize (IH f X H); destruct b; simpl; auto.
  - exact (IH f X H).
Qed.

Lemma interp_env_var_binds : forall G f x A,
  binds x (abind_var_typ A) (awl_to_aenv G) ->
  binds x (dbind_typ (interp_typ f A)) (interp_env f G).
Proof.
  induction G as [|G IH Y b|G IH w]; intros f x A H; cbn in *.
  - exact (False_rect _ H).
  - apply binds_cons_cases in H as [[-> <-]|H]; simpl; auto.
    specialize (IH f x A H); destruct b; simpl; auto.
  - exact (IH f x A H).
Qed.

Lemma valid_tvar : forall G f X b,
  uniq (awl_to_aenv G) -> valid_assignment f G ->
  binds X b (awl_to_aenv G) -> b <> abind_etvar_empty ->
  f X = typ_var_f X.
Proof.
  intros G f X b HU [HS HI] Hb Hn; apply HI; intro HE.
  apply Hn. eapply binds_unique; eassumption.
Qed.

Lemma interp_env_type_map : forall G f,
  a_wf_wwl G -> valid_assignment f G ->
  d_typ_map (awl_to_aenv G) f (interp_env f G).
Proof.
  intros G f HW HV.
  assert (HU := awl_unique _ HW).
  unfold d_typ_map; repeat split; intros X HX.
  - rewrite (valid_tvar _ f _ _ HU HV HX) by discriminate.
    apply d_wf_typ__tvar; auto using interp_env_tvar_binds.
  - rewrite (valid_tvar _ f _ _ HU HV HX) by discriminate.
    apply d_wf_typ__stvar; auto using interp_env_stvar_binds.
  - apply d_mono_wf.
    eapply d_mono_weak_map; [|intros; eapply regulars_interp_binds; eassumption].
    apply scoped_assignment_binds; [apply HV|assumption].
Qed.

Lemma d_type_of_a_type : forall G f A,
  a_wf_wwl G -> valid_assignment f G -> a_wf_typ (awl_to_aenv G) A ->
  d_wf_typ (interp_env f G) (interp_typ f A).
Proof.
  intros G f A HW HV HA.
  destruct (valid_assignment_facts _ _ HV) as [Hc [Hf Hl]].
  eapply interp_d_wf_typ; eauto using interp_env_type_map.
Qed.

Lemma d_mono_of_a_mono : forall G f A,
  a_wf_wwl G -> valid_assignment f G -> a_mono_typ (awl_to_aenv G) A ->
  d_mono_typ (interp_env f G) (interp_typ f A).
Proof.
  intros G f A HW HV HA.
  eapply d_mono_interp; [eassumption| |].
  - intros X HX. rewrite (valid_tvar _ f _ _ (awl_unique _ HW) HV HX) by discriminate.
    constructor; eauto using interp_env_tvar_binds.
  - intros X HX. eapply d_mono_weak_map.
    + eapply scoped_assignment_binds; [apply HV|eassumption].
    + eauto using regulars_interp_binds.
Qed.

Lemma d_neq_of_a_neq : forall G f A,
  a_wf_wwl G -> valid_assignment f G -> a_wneq_all (awl_to_aenv G) A ->
  d_wneq_all (interp_env f G) (interp_typ f A).
Proof.
  intros G f A HW HV HA.
  remember (awl_to_aenv G) as E; induction HA; subst; cbn;
    try solve [eauto using d_wneq_all__unit, d_wneq_all__top].
  - rewrite (valid_tvar _ f _ _ (awl_unique _ HW) HV H) by discriminate.
    constructor; eauto using interp_env_tvar_binds.
  - assert (HM : d_mono_typ (interp_env f G) (f X)).
    { apply (d_mono_of_a_mono G f (typ_var_f X)); eauto. }
    induction HM; eauto using d_wneq_all__unit, d_wneq_all__tvar,
      d_wneq_all__arrow, d_mono_lc.
  - constructor; eapply interp_lc; eauto using valid_assignment_facts.
    all: apply (proj2 (proj2 (valid_assignment_facts _ _ HV))).
  - eapply d_wneq_all__union1; eauto.
    apply interp_lc; auto. apply (proj2 (proj2 (valid_assignment_facts _ _ HV))).
  - eapply d_wneq_all__union2; eauto.
    apply interp_lc; auto. apply (proj2 (proj2 (valid_assignment_facts _ _ HV))).
  - constructor; eauto.
Qed.

Lemma interp_wl_app : forall S G f,
  interp_wl f (awl_app S G) = dwl_app (interp_wl f S) (interp_wl f G).
Proof. induction S; intros; simpl; try destruct ab; simpl; rewrite ?IHS; reflexivity. Qed.

Lemma interp_wl_agree : forall G f g,
  a_wf_wwl G -> agrees (worklist_dom G) f g -> interp_wl f G = interp_wl g G.
Proof.
  intros G f g HW; induction HW; simpl; intros HM; try reflexivity;
    try solve [rewrite IHHW; [reflexivity|unfold worklist_dom in *; simpl in *; restrict_agreement]].
  - rewrite IHHW by (unfold worklist_dom in *; simpl in *; restrict_agreement).
    f_equal; f_equal. apply interp_typ_ext. intros X HX. apply HM.
    pose proof (a_wf_typ_scope _ _ H0 _ HX). unfold worklist_dom; simpl; fsetdec.
  - rewrite IHHW by exact HM.
    f_equal; apply interp_work_ext. intros X HX; apply HM.
    eapply a_wf_work_scope; eassumption.
Qed.

Lemma aws_interp_reorder : forall G X B P S,
  aworklist_subst G X B P S ->
  forall f, interp_wl f G = dwl_app (interp_wl f S) (interp_wl f P).
Proof.
  intros G X B P S HW; induction HW; intros f; simpl;
    try solve [rewrite IHHW; reflexivity].
  - reflexivity.
  - specialize (IHHW f); rewrite interp_wl_app in *; exact IHHW.
Qed.

Lemma interp_wl_subst : forall S X B f g,
  interp_typ f B = g X -> (forall Y, Y <> X -> f Y = g Y) ->
  interp_wl f (subst_typ_in_aworklist B X S) = interp_wl g S.
Proof.
  induction S as [|S IH Y b|S IH w]; intros X B f g HX HY; simpl.
  - reflexivity.
  - destruct b; cbn; rewrite (IH X B f g HX HY); try reflexivity.
    rewrite (interp_assign_typ _ _ _ _ _ HX HY); reflexivity.
  - rewrite (IH X B f g HX HY), (interp_assign_work _ _ _ _ _ HX HY); reflexivity.
Qed.

Lemma aws_interp_target : forall G X B P S f g,
  aworklist_subst G X B P S ->
  a_wf_wwl G ->
  interp_typ f B = g X -> (forall Y, Y <> X -> f Y = g Y) ->
  interp_wl f (awl_app (subst_typ_in_aworklist B X S) P) = interp_wl g G.
Proof.
  intros G X B P S f g HS HW Hx Hy.
  rewrite (aws_interp_reorder _ _ _ _ _ HS g), interp_wl_app, (interp_wl_subst S X B f g Hx Hy).
  assert (HW' : a_wf_wwl (aworklist_cons_var P X abind_etvar_empty)).
  { eapply awl_wf_prefix. eapply aws_source_reordered; eassumption. }
  f_equal. apply interp_wl_agree.
  - inversion HW'; assumption.
  - intros Y HY; apply Hy. inversion HW'; subst. unfold worklist_dom in *; intro; subst; contradiction.
Qed.

Lemma scoped_app : forall S P Q f g,
  regulars P = regulars Q ->
  (forall Y, binds Y abind_etvar_empty (awl_to_aenv S) -> f Y = g Y) ->
  (scoped_assignment f P <-> scoped_assignment g Q) ->
  (scoped_assignment f (awl_app S P) <-> scoped_assignment g (awl_app S Q)).
Proof.
  induction S as [|S IH y b|S IH w]; intros P Q f g HR HA HP; simpl.
  - exact HP.
  - assert (HT : forall Y, binds Y abind_etvar_empty (awl_to_aenv S) -> f Y = g Y) by (intros; apply HA; simpl; auto).
    specialize (IH P Q f g HR HT HP). destruct b; simpl; try exact IH.
    rewrite !regulars_app, HR, (HA y) by (simpl; apply binds_cons_head). tauto.
  - apply IH; try assumption; exact HA.
Qed.

Lemma scoped_subst : forall S P Q X B f g,
  regulars P = regulars Q ->
  (forall Y, binds Y abind_etvar_empty (awl_to_aenv S) -> f Y = g Y) ->
  (scoped_assignment f P <-> scoped_assignment g Q) ->
  (scoped_assignment f (awl_app (subst_typ_in_aworklist B X S) P) <->
   scoped_assignment g (awl_app S Q)).
Proof.
  induction S as [|S IH y b|S IH w]; intros P Q X B f g HR HA HP; simpl.
  - exact HP.
  - assert (HT : forall Y, binds Y abind_etvar_empty (awl_to_aenv S) -> f Y = g Y) by (intros; apply HA; simpl; auto).
    specialize (IH P Q X B f g HR HT HP). destruct b; simpl; try exact IH.
    rewrite !regulars_app, regulars_subst, HR, (HA y) by (simpl; apply binds_cons_head). tauto.
  - apply IH; try assumption; exact HA.
Qed.

Lemma scoped_prefix : forall S P f, scoped_assignment f (awl_app S P) -> scoped_assignment f P.
Proof.
  induction S; intros; cbn in *; try solve [auto].
  destruct ab; cbn in *; eauto. apply IHS; tauto.
Qed.

Lemma scoped_same : forall G f g,
  (forall X, binds X abind_etvar_empty (awl_to_aenv G) -> f X = g X) ->
  (scoped_assignment f G <-> scoped_assignment g G).
Proof.
  induction G as [|G IH y b|G IH w]; intros f g H; simpl in *.
  - tauto.
  - assert (HT : forall Y, binds Y abind_etvar_empty (awl_to_aenv G) -> f Y = g Y) by eauto.
    specialize (IH f g HT). destruct b; simpl; try exact IH.
    rewrite (H y) by auto. tauto.
  - exact (IH f g H).
Qed.

Lemma aws_regulars : forall G X B P S,
  aworklist_subst G X B P S -> regulars G = regulars S ++ regulars P.
Proof.
  intros G X B P S H; induction H; simpl;
    try solve [now rewrite ?IHaworklist_subst | assumption].
  rewrite regulars_app in *. exact IHaworklist_subst.
Qed.

Lemma aws_scoped_back : forall G X B P S,
  aworklist_subst G X B P S ->
  forall f, scoped_assignment f (awl_app S (aworklist_cons_var P X abind_etvar_empty)) ->
  scoped_assignment f G.
Proof.
  intros G X B P S H; induction H; intros f HS; cbn in *; try solve [auto].
  - destruct HS as [Hm HS]; split.
    + rewrite !regulars_app in *; cbn in *.
      now rewrite (aws_regulars _ _ _ _ _ H).
    + auto.
  - apply IHaworklist_subst in HS. split.
    + rewrite regulars_app; cbn.
      apply scoped_prefix with (S := Γ2) in HS. cbn in HS.
      eapply d_mono_weak_map; [exact (proj1 (proj2 HS))|].
      unfold binds; eauto using in_or_app.
    + assert (HQ : scoped_assignment f (aworklist_cons_var (aworklist_cons_var Γ1 Y abind_etvar_empty) X abind_etvar_empty))
        by (eapply scoped_prefix; eassumption).
      assert (HR : scoped_assignment f (aworklist_cons_var (aworklist_cons_var Γ1 Y abind_etvar_empty) X abind_etvar_empty) <->
                   scoped_assignment f (aworklist_cons_var Γ1 X abind_etvar_empty)).
      { cbn in *; tauto. }
      exact (proj1 (scoped_app Γ2 (aworklist_cons_var (aworklist_cons_var Γ1 Y abind_etvar_empty) X abind_etvar_empty) (aworklist_cons_var Γ1 X abind_etvar_empty) f f eq_refl (fun _ _ => eq_refl) HR) HS).
Qed.

Lemma etvar_subst_binds : forall S X B Y,
  binds Y abind_etvar_empty (awl_to_aenv (subst_typ_in_aworklist B X S)) <->
  binds Y abind_etvar_empty (awl_to_aenv S).
Proof.
  induction S as [|S IH z b|S IH w]; intros; cbn; try apply IH; try tauto.
  specialize (IH X B Y). destruct b; cbn; unfold binds in *; cbn in *; intuition congruence.
Qed.

Lemma etvar_app_binds : forall S G Y,
  binds Y abind_etvar_empty (awl_to_aenv (awl_app S G)) <->
  binds Y abind_etvar_empty (awl_to_aenv S) \/ binds Y abind_etvar_empty (awl_to_aenv G).
Proof.
  intros; rewrite awl_to_aenv_app; unfold binds; rewrite in_app_iff; tauto.
Qed.

Lemma aws_target_binds : forall G X B P S Y,
  aworklist_subst G X B P S -> Y <> X ->
  (binds Y abind_etvar_empty (awl_to_aenv (awl_app (subst_typ_in_aworklist B X S) P)) <->
   binds Y abind_etvar_empty (awl_to_aenv G)).
Proof.
  intros G X B P S Y H Hneq.
  rewrite etvar_app_binds, etvar_subst_binds, (aws_binds _ _ _ _ _ Y abind_etvar_empty H).
  unfold binds. rewrite in_app_iff. simpl. intuition congruence.
Qed.

Lemma awl_subst_suffix_fresh : forall S P X,
  a_wf_wwl (awl_app S (aworklist_cons_var P X abind_etvar_empty)) ->
  X `notin` worklist_dom S /\ X `notin` worklist_dom P.
Proof.
  intros S P X H. apply awl_unique in H.
  unfold worklist_dom. rewrite awl_to_aenv_app in H. simpl in H.
  split; [exact (fresh_mid_head abind X abind_etvar_empty _ _ H)|exact (fresh_mid_tail abind X abind_etvar_empty _ _ H)].
Qed.

Lemma aws_valid_back : forall G X B P S f,
  aworklist_subst G X B P S -> a_wf_wwl G ->
  a_mono_typ (awl_to_aenv G) B -> X `notin` ftvar_in_typ B ->
  valid_assignment f (awl_app (subst_typ_in_aworklist B X S) P) ->
  valid_assignment (assign f X (interp_typ f B)) G.
Proof.
  intros G X B P S f HS HW HM HX HF.
  rename HF into HV.
  pose proof (aws_source_reordered _ _ _ _ _ HS HW) as HR.
  pose proof (aws_target_wf _ _ _ _ _ HS HW HM HX) as HT.
  pose proof (aws_mono _ _ _ _ _ HS HM HX) as Hmono.
  destruct (awl_subst_suffix_fresh S P X HR) as [HXS HXP].
  assert (Hfx : forall Y, Y <> X -> f Y = assign f X (interp_typ f B) Y)
    by (intros; symmetry; apply interp_assign_other; assumption).
  assert (Hp : d_mono_typ (regulars P) (interp_typ f B)).
  { eapply d_mono_interp; [exact Hmono| |].
    - intros Y HY.
      assert (HY' : binds Y abind_tvar_empty (awl_to_aenv (awl_app (subst_typ_in_aworklist B X S) P))).
      { rewrite awl_to_aenv_app; unfold binds; auto using in_or_app. }
      rewrite (valid_tvar _ f _ _ (awl_unique _ HT) HV HY') by discriminate.
      constructor. now apply regulars_binds.
    - intros Y HY. eapply scoped_assignment_binds; [|exact HY].
      eapply scoped_prefix. apply HV. }
  split.
  - eapply aws_scoped_back; [exact HS|].
    assert (HH : scoped_assignment f P <->
      scoped_assignment (assign f X (interp_typ f B)) (aworklist_cons_var P X abind_etvar_empty)).
    { simpl. rewrite interp_assign_self, <- (scoped_same P f (assign f X (interp_typ f B))).
      - tauto.
      - intros Y HY; apply Hfx; intro; subst; eauto using binds_dom_contradiction. }
    assert (HA : forall Y, binds Y abind_etvar_empty (awl_to_aenv S) ->
        f Y = assign f X (interp_typ f B) Y).
    { intros Y HY; apply Hfx; intro; subst; eauto using binds_dom_contradiction. }
    apply (proj1 (scoped_subst S P (aworklist_cons_var P X abind_etvar_empty) X B
                  f (assign f X (interp_typ f B)) eq_refl HA HH)).
    apply HV.
  - intros Y HY.
    assert (Hneq : Y <> X).
    { intro; subst; apply HY. apply (aws_binds _ _ _ _ _ _ _ HS).
      unfold binds; apply in_or_app; right; left; reflexivity. }
    rewrite interp_assign_other by assumption.
    apply HV. rewrite (aws_target_binds _ _ _ _ _ Y HS Hneq); exact HY.
Qed.

Lemma valid_prefix_restrict : forall G G' f,
  a_wf_wwl (awl_app G' G) ->
  valid_assignment f (awl_app G' G) ->
  exists g, valid_assignment g G /\ agrees (worklist_dom G) f g.
Proof.
  intros G S f HW HV.
  exists (fun X => if etvar_binds_dec G X then f X else typ_var_f X).
  split.
  - split.
    + assert (HA : forall X, binds X abind_etvar_empty (awl_to_aenv G) ->
          f X = (if etvar_binds_dec G X then f X else typ_var_f X)).
      { intros X HX; destruct (etvar_binds_dec G X); congruence. }
      apply (proj1 (scoped_same G f _ HA)).
      eapply scoped_prefix; apply HV.
    + intros X HX; destruct (etvar_binds_dec G X); congruence.
  - intros X HX; destruct (etvar_binds_dec G X); auto.
    apply HV. rewrite etvar_app_binds. intros [HY|HY]; [|contradiction].
    apply awl_unique in HW. rewrite awl_to_aenv_app in HW.
    eapply fresh_app_r in HW; eauto.
Qed.

Fixpoint dl_no_rigid (D : dworklist) : Prop :=
  match D with
  | dworklist_empty => True
  | dworklist_cons_var _ _ dbind_stvar_empty => False
  | dworklist_cons_var D _ _ | dworklist_cons_work D _ => dl_no_rigid D
  end.

Fixpoint dl_phase (D : dworklist) : Prop :=
  match D with
  | dworklist_empty => True
  | dworklist_cons_var D _ dbind_stvar_empty | dworklist_cons_work D (work_sub _ _) =>
      dl_phase D
  | dworklist_cons_var D _ _ | dworklist_cons_work D _ =>
      dl_no_rigid D /\ dl_phase D
  end.

Definition awl_phase G := dl_phase (interp_wl typ_var_f G).
Definition awl_no_rigid G := dl_no_rigid (interp_wl typ_var_f G).

Lemma interp_tenv_valid : forall G f,
  a_wf_wwl G -> valid_assignment f G -> awl_no_rigid G ->
  d_wf_tenv (interp_env f G).
Proof.
  assert (H : forall G f, a_wf_wwl G ->
    (forall S, valid_assignment f (awl_app S G) ->
      a_wf_wwl (awl_app S G) -> awl_no_rigid G ->
      d_wf_tenv (interp_env f G))).
  { intros G f HW; induction HW; intros S HV HW' Hnr; unfold awl_no_rigid in *; cbn in *.
    - constructor.
    - apply d_wf_tenv__typ.
      + eapply (IHHW (awl_app S (aworklist_cons_var aworklist_empty x (abind_var_typ A))));
          try rewrite awl_app_assoc; try eassumption.
      + assert (Hweak : a_wf_typ (awl_to_aenv (awl_app S (aworklist_cons_var Γ x (abind_var_typ A)))) A).
        { eapply a_wf_typ_weak_map; [eassumption|]. rewrite awl_to_aenv_app. simpl.
          unfold binds; intros; apply in_or_app; right; simpl; auto. }
        (* Use only the original prefix's assignment when interpreting its binding. *)
        assert (HV0 : exists g, valid_assignment g Γ /\ agrees (worklist_dom Γ) f g).
        { eapply (valid_prefix_restrict Γ (awl_app S (aworklist_cons_var aworklist_empty x (abind_var_typ A))) f);
            rewrite awl_app_assoc; eassumption. }
        destruct HV0 as [g [Hg HF]].
        rewrite <- (interp_wl_env Γ f), (interp_wl_agree _ _ _ HW HF), interp_wl_env.
        rewrite (interp_typ_ext A f g) by (intros Y HY; apply HF; eapply a_wf_typ_scope; eassumption).
        eapply d_type_of_a_type; eassumption.
      + intro Hx. apply H. eapply interp_env_dom; exact Hx.
    - apply d_wf_tenv__tvar.
      + eapply (IHHW (awl_app S (aworklist_cons_var aworklist_empty X abind_tvar_empty)));
          try rewrite awl_app_assoc; try eassumption.
      + intro Hx. apply H. eapply interp_env_dom; exact Hx.
    - contradiction.
    - eapply (IHHW (awl_app S (aworklist_cons_var aworklist_empty X abind_etvar_empty)));
        try rewrite awl_app_assoc; try eassumption.
    - change (dl_no_rigid (interp_wl typ_var_f Γ)) in Hnr.
      eapply (IHHW (awl_app S (aworklist_cons_work aworklist_empty w)));
        try rewrite awl_app_assoc; try eassumption. }
  intros; exact (H G f H0 aworklist_empty H1 H0 H2).
Qed.

Lemma interp_denv_valid : forall G f,
  a_wf_wwl G -> valid_assignment f G -> awl_phase G ->
  d_wf_env (interp_env f G).
Proof.
  assert (H : forall G f, a_wf_wwl G ->
    (forall S, valid_assignment f (awl_app S G) ->
      a_wf_wwl (awl_app S G) -> awl_phase G ->
      d_wf_env (interp_env f G))).
  { intros G f HW; induction HW; intros S HV HW' HP.
    - constructor; constructor.
    - apply d_wf_env__empty.
      change (d_wf_tenv (interp_env f (aworklist_cons_var Γ x (abind_var_typ A)))).
      destruct (valid_prefix_restrict _ _ _ HW' HV) as [g [HV' HA]].
      assert (HW0 : a_wf_wwl (aworklist_cons_var Γ x (abind_var_typ A))) by eauto.
      rewrite <- (interp_wl_env _ f), (interp_wl_agree _ _ _ HW0 HA), interp_wl_env.
      apply interp_tenv_valid; auto. apply HP.
    - apply d_wf_env__empty.
      change (d_wf_tenv (interp_env f (aworklist_cons_var Γ X abind_tvar_empty))).
      destruct (valid_prefix_restrict _ _ _ HW' HV) as [g [HV' HA]].
      assert (HW0 : a_wf_wwl (aworklist_cons_var Γ X abind_tvar_empty)) by eauto.
      rewrite <- (interp_wl_env _ f), (interp_wl_agree _ _ _ HW0 HA), interp_wl_env.
      apply interp_tenv_valid; auto. apply HP.
    - simpl. apply d_wf_env__stvar.
      + eapply (IHHW (awl_app S (aworklist_cons_var aworklist_empty X abind_stvar_empty)));
          try rewrite awl_app_assoc; try eassumption.
      + intro Hx; apply H. eauto using interp_env_dom.
    - eapply (IHHW (awl_app S (aworklist_cons_var aworklist_empty X abind_etvar_empty)));
        try rewrite awl_app_assoc; try eassumption.
    - eapply (IHHW (awl_app S (aworklist_cons_work aworklist_empty w)));
        try rewrite awl_app_assoc; try eassumption.
      unfold awl_phase in *; destruct w; simpl in HP; tauto. }
  intros; exact (H G f H0 aworklist_empty H1 H0 H2).
Qed.

(* Swapping fresh atoms transports a single projected binder premise
   to all names outside the cofinite exclusion set. *)
Definition ren_typ (p : atom -> atom) := interp_typ (fun X => typ_var_f (p X)).

Fixpoint ren_exp (p : atom -> atom) (e : exp) : exp :=
  match e with
  | exp_var_f x => exp_var_f (p x)
  | exp_abs e => exp_abs (ren_exp p e)
  | exp_app e1 e2 => exp_app (ren_exp p e1) (ren_exp p e2)
  | exp_tabs e => exp_tabs (ren_exp p e)
  | exp_tapp e A => exp_tapp (ren_exp p e) (ren_typ p A)
  | exp_anno e A => exp_anno (ren_exp p e) (ren_typ p A)
  | _ => e
  end.

Fixpoint ren_cs (p : atom -> atom) (s : conts) : conts :=
  match s with
  | conts_infabs d => conts_infabs (ren_cd p d)
  | conts_inftapp A s => conts_inftapp (ren_typ p A) (ren_cs p s)
  | conts_inftappunion A B s => conts_inftappunion (ren_typ p A) (ren_typ p B) (ren_cs p s)
  | conts_unioninftapp A s => conts_unioninftapp (ren_typ p A) (ren_cs p s)
  | conts_sub A => conts_sub (ren_typ p A)
  end
with ren_cd (p : atom -> atom) (d : contd) : contd :=
  match d with
  | contd_infabsunion A d => contd_infabsunion (ren_typ p A) (ren_cd p d)
  | contd_infapp e s => contd_infapp (ren_exp p e) (ren_cs p s)
  | contd_unioninfabs A B d => contd_unioninfabs (ren_typ p A) (ren_typ p B) (ren_cd p d)
  end.

Definition ren_work (p : atom -> atom) (w : work) : work :=
  match w with
  | work_infer e s => work_infer (ren_exp p e) (ren_cs p s)
  | work_check e A => work_check (ren_exp p e) (ren_typ p A)
  | work_infabs A d => work_infabs (ren_typ p A) (ren_cd p d)
  | work_infabsunion A B C d =>
      work_infabsunion (ren_typ p A) (ren_typ p B) (ren_typ p C) (ren_cd p d)
  | work_infapp A B e s => work_infapp (ren_typ p A) (ren_typ p B) (ren_exp p e) (ren_cs p s)
  | work_inftapp A B s => work_inftapp (ren_typ p A) (ren_typ p B) (ren_cs p s)
  | work_sub A B => work_sub (ren_typ p A) (ren_typ p B)
  | work_inftappunion A B C s =>
      work_inftappunion (ren_typ p A) (ren_typ p B) (ren_typ p C) (ren_cs p s)
  | work_unioninftapp A B s => work_unioninftapp (ren_typ p A) (ren_typ p B) (ren_cs p s)
  | work_unioninfabs A B C D d =>
      work_unioninfabs (ren_typ p A) (ren_typ p B) (ren_typ p C) (ren_typ p D) (ren_cd p d)
  | work_applys s A => work_applys (ren_cs p s) (ren_typ p A)
  | work_applyd d A B => work_applyd (ren_cd p d) (ren_typ p A) (ren_typ p B)
  end.

Definition ren_dbind (p : atom -> atom) (b : dbind) : dbind :=
  match b with
  | dbind_typ A => dbind_typ (ren_typ p A)
  | _ => b
  end.

Fixpoint ren_wl (p : atom -> atom) (D : dworklist) : dworklist :=
  match D with
  | dworklist_empty => dworklist_empty
  | dworklist_cons_var D x b => dworklist_cons_var (ren_wl p D) (p x) (ren_dbind p b)
  | dworklist_cons_work D w => dworklist_cons_work (ren_wl p D) (ren_work p w)
  end.

Definition ren_env (p : atom -> atom) (D : denv) : denv :=
  List.map (fun binding => (p (fst binding), ren_dbind p (snd binding))) D.

Lemma ren_wl_env : forall D p, dwl_to_denv (ren_wl p D) = ren_env p (dwl_to_denv D).
Proof. induction D; intros; cbn; unfold ren_env in *; cbn; now rewrite ?IHD. Qed.

Lemma ren_env_binds : forall E p x b, binds x b E -> binds (p x) (ren_dbind p b) (ren_env p E).
Proof.
  intros. unfold binds, ren_env in *.
  change (p x, ren_dbind p b) with ((fun binding => (p (fst binding), ren_dbind p (snd binding))) (x,b)).
  auto using in_map.
Qed.

Lemma ren_open_typ : forall A B p,
  ren_typ p (open_typ_wrt_typ A B) =
  open_typ_wrt_typ (ren_typ p A) (ren_typ p B).
Proof. intros; apply interp_open_typ; unfold closed_assignment; intros; reflexivity. Qed.

Lemma ren_open_exp_typ : forall e B p,
  ren_exp p (open_exp_wrt_typ e B) =
  open_exp_wrt_typ (ren_exp p e) (ren_typ p B).
Proof.
  unfold open_exp_wrt_typ.
  assert (H : forall e k B p, ren_exp p (open_exp_wrt_typ_rec k B e) =
                  open_exp_wrt_typ_rec k (ren_typ p B) (ren_exp p e)).
  { induction e; intros; cbn; try reflexivity;
    try solve [f_equal; eauto | f_equal; auto; apply interp_open_typ_rec; intros; reflexivity]. }
  eauto.
Qed.

Lemma ren_open_exp_exp : forall e x p,
  ren_exp p (open_exp_wrt_exp e (exp_var_f x)) =
  open_exp_wrt_exp (ren_exp p e) (exp_var_f (p x)).
Proof.
  unfold open_exp_wrt_exp.
  assert (H : forall e k x p, ren_exp p (open_exp_wrt_exp_rec k (exp_var_f x) e) =
    open_exp_wrt_exp_rec k (exp_var_f (p x)) (ren_exp p e)).
  { induction e; intros; cbn; try reflexivity; try solve [f_equal; auto].
    destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity. }
  auto.
Qed.

Lemma ren_lc : forall A p, lc_typ A -> lc_typ (ren_typ p A).
Proof. intros; apply interp_lc; eauto. Qed.

Lemma ren_dmono : forall E A, d_mono_typ E A -> forall p,
  d_mono_typ (ren_env p E) (ren_typ p A).
Proof.
  intros E A H; induction H; intros; cbn; eauto.
  apply d_mono_typ__tvar. exact (ren_env_binds Ψ p X dbind_tvar_empty H).
Qed.

Lemma ren_dneq : forall E A, d_wneq_all E A -> forall p,
  d_wneq_all (ren_env p E) (ren_typ p A).
Proof.
  Local Hint Constructors d_wneq_all : core.
  intros E A H; induction H; intros; cbn; eauto using ren_lc.
  apply d_wneq_all__tvar. exact (ren_env_binds Ψ p X dbind_tvar_empty H).
Qed.

Definition ren_atoms (p : atom -> atom) (L : atoms) : atoms :=
  fold_right (fun X S => singleton (p X) `union` S) ({} : atoms) (AtomSetImpl.elements L).

Lemma ren_atoms_in : forall p L X, X `in` L -> p X `in` ren_atoms p L.
Proof.
  unfold ren_atoms; intros p L X H.
  apply AtomSetImpl.elements_1 in H.
  induction H; simpl.
  - subst; fsetdec.
  - apply AtomSetImpl.union_3; assumption.
Qed.

Local Hint Constructors apply_conts apply_contd : core.
Local Hint Constructors d_wl_red : decl_reduce.
Local Hint Resolve ren_dmono ren_dneq : decl_reduce.

Lemma ren_d_reduce : forall D, d_wl_red D -> forall p,
  (forall X, p (p X) = X) -> d_wl_red (ren_wl p D).
Proof.
  intros D H; induction H; intros p Hp; cbn.
  all: repeat match goal with
    | IH : forall q : atom -> atom, (forall X, q (q X) = X) -> d_wl_red _ |- _ =>
        specialize (IH p Hp); cbn in IH
    end.
  all: try solve [eauto 4 with decl_reduce].
  all: try solve [eapply d_wl_red__sub_alll;
    [rewrite ren_wl_env; eapply ren_dneq; eassumption
    |rewrite ren_wl_env; eapply ren_dmono; eassumption
    |rewrite <- ren_open_typ; eassumption]].
  all: try solve [eapply d_wl_red__infabs_all;
    [rewrite ren_wl_env; eapply ren_dmono; eassumption|rewrite <- ren_open_typ; assumption]].
  all: try solve [apply d_wl_red__inftapp_all; rewrite <- ren_open_typ; assumption].
  all: try solve [eapply d_wl_red__inf_var;
    [rewrite ren_wl_env; eapply ren_env_binds; eassumption | eassumption]].
  - apply d_wl_red__sub_all with (L := ren_atoms p L).
    intros y Hy. assert (Hx : p y `notin` L).
    { intro Hx. apply Hy. pose proof (ren_atoms_in p L (p y) Hx). rewrite Hp in H1. assumption. }
    specialize (H0 (p y) Hx p Hp); cbn in H0.
    rewrite !ren_open_typ in H0.
    change (ren_typ p (typ_var_f (p y))) with (typ_var_f (p (p y))) in H0.
    rewrite Hp in H0; exact H0.
  - apply d_wl_red__chk_absarrow with (L := ren_atoms p L).
    intros y Hy. assert (Hx : p y `notin` L) by
      (intro Hx; apply Hy; pose proof (ren_atoms_in p L (p y) Hx) as HA; now rewrite Hp in HA).
    specialize (H0 (p y) Hx p Hp); cbn in H0.
    rewrite ren_open_exp_exp, !Hp in H0; exact H0.
  - apply d_wl_red__chk_abstop with (L := ren_atoms p L).
    intros y Hy. assert (Hx : p y `notin` L) by
      (intro Hx; apply Hy; pose proof (ren_atoms_in p L (p y) Hx) as HA; now rewrite Hp in HA).
    specialize (H0 (p y) Hx p Hp); cbn in H0.
    rewrite ren_open_exp_exp, !Hp in H0; exact H0.
  - match goal with Hb : binds _ (dbind_typ ?T) _ |- _ =>
      eapply d_wl_red__inf_var with (A := ren_typ p T) end.
    + rewrite ren_wl_env. exact (ren_env_binds _ p _ _ H).
    + assumption.
  - apply d_wl_red__inf_tabs with (L := ren_atoms p L).
    intros y Hy. assert (Hx : p y `notin` L).
    { intro Hx. apply Hy. pose proof (ren_atoms_in p L (p y) Hx) as HA. now rewrite Hp in HA. }
    specialize (H0 (p y) Hx p Hp); cbn in H0.
    rewrite ren_open_typ, ren_open_exp_typ in H0.
    change (ren_typ p (typ_var_f (p y))) with (typ_var_f (p (p y))) in H0.
    rewrite Hp in H0; exact H0.
  - eapply d_wl_red__inf_abs_mono with (L := ren_atoms p L)
      (T1 := ren_typ p T1) (T2 := ren_typ p T2).
    + rewrite ren_wl_env. exact (ren_dmono _ _ H p).
    + intros y Hy. assert (Hx : p y `notin` L).
      { intro Hx. apply Hy. pose proof (ren_atoms_in p L (p y) Hx) as HA. now rewrite Hp in HA. }
      specialize (H1 (p y) Hx p Hp); cbn in H1.
      rewrite ren_open_exp_exp, !Hp in H1; exact H1.
  - match goal with K : apply_conts _ _ _ |- _ => destruct K end.
    all: cbn in *; eapply d_wl_red__applys; [|eassumption]; constructor.
  - match goal with K : apply_contd _ _ _ _ |- _ => destruct K end.
    all: cbn in *; eapply d_wl_red__applyd; [|eassumption]; constructor.
Qed.

Lemma awl_split_at : forall G X, binds X abind_etvar_empty (awl_to_aenv G) ->
  exists P S, G = awl_app S (aworklist_cons_var P X abind_etvar_empty).
Proof.
  induction G as [|G IH Y b|G IH w]; intros X H; simpl in H.
  - contradiction.
  - apply binds_cons_cases in H as [[-> <-]|H].
    + exists G, aworklist_empty; reflexivity.
    + destruct (IH X H) as [P [S ->]].
      exists P, (aworklist_cons_var S Y b); reflexivity.
  - destruct (IH X H) as [P [S ->]].
    exists P, (aworklist_cons_work S w); reflexivity.
Qed.

Definition avoids_regulars (S : aworklist) (B : typ) :=
  forall Y, (binds Y abind_tvar_empty (awl_to_aenv S) \/
             binds Y abind_stvar_empty (awl_to_aenv S)) ->
  Y `notin` ftvar_in_typ B.

Lemma aws_exists_suffix : forall S P X B,
  a_wf_wwl (awl_app S (aworklist_cons_var P X abind_etvar_empty)) ->
  avoids_regulars S B ->
  exists Q T, aworklist_subst (awl_app S (aworklist_cons_var P X abind_etvar_empty)) X B Q T.
Proof.
  induction S as [|S IH Y b|S IH w]; intros P X B HW HA; simpl in *.
  - exists P, aworklist_empty. constructor.
  - assert (Htail : a_wf_wwl (awl_app S (aworklist_cons_var P X abind_etvar_empty)))
      by (inversion HW; assumption).
    assert (HY : Y `notin` worklist_dom (awl_app S (aworklist_cons_var P X abind_etvar_empty)))
      by (inversion HW; assumption).
    assert (Hneq : Y <> X).
    { intro; subst. apply HY. unfold worklist_dom; rewrite awl_to_aenv_app, dom_app; cbn; fsetdec. }
    assert (HA' : avoids_regulars S B).
    { intros Z [HZ|HZ]; apply HA; simpl; auto. }
    destruct b.
    + destruct (IH P X B Htail HA') as [Q [T HT]].
      exists Q, (aworklist_cons_var T Y abind_tvar_empty). constructor; auto.
      apply HA; left; simpl; auto.
    + destruct (IH P X B Htail HA') as [Q [T HT]].
      exists Q, (aworklist_cons_var T Y abind_stvar_empty). constructor; auto.
      apply HA; right; simpl; auto.
    + destruct (AtomSetImpl.mem Y (ftvar_in_typ B)) eqn:HB.
      * assert (HW' : a_wf_wwl (awl_app S (aworklist_cons_var
                     (aworklist_cons_var P Y abind_etvar_empty) X abind_etvar_empty))).
        { change (a_wf_wwl (awl_app S
              (awl_app (aworklist_cons_var aworklist_empty X abind_etvar_empty)
                      (aworklist_cons_var P Y abind_etvar_empty)))).
          rewrite <- awl_app_assoc. apply awl_wf_insert_etvar;
            rewrite awl_app_assoc; assumption. }
        destruct (IH _ X B HW' HA') as [Q [T HT]].
        exists Q, T. apply a_ws__etvar_move; try assumption.
        apply AtomSetImpl.mem_2; exact HB.
      * destruct (IH P X B Htail HA') as [Q [T HT]].
        exists Q, (aworklist_cons_var T Y abind_etvar_empty).
        apply a_ws__etvar_stay; try assumption.
        intro HH; apply AtomSetImpl.mem_1 in HH; congruence.
    + destruct (IH P X B Htail HA') as [Q [T HT]].
      exists Q, (aworklist_cons_var T Y (abind_var_typ A)); constructor; assumption.
  - assert (Htail : a_wf_wwl (awl_app S (aworklist_cons_var P X abind_etvar_empty)))
      by (inversion HW; assumption).
    destruct (IH P X B Htail HA) as [Q [T HT]].
    exists Q, (aworklist_cons_work T w); constructor; assumption.
Qed.

Lemma aws_exists_etvars : forall G X B,
  binds X abind_etvar_empty (awl_to_aenv G) -> a_wf_wwl G ->
  (forall Y, Y `in` ftvar_in_typ B -> binds Y abind_etvar_empty (awl_to_aenv G)) ->
  exists P S, aworklist_subst G X B P S.
Proof.
  intros G X B HX HW HB.
  destruct (awl_split_at _ _ HX) as [P [S HE]].
  subst G. apply aws_exists_suffix; auto.
  intros Y [Hi|Hi] Hy; specialize (HB Y Hy); apply awl_unique in HW;
    rewrite awl_to_aenv_app in *; unfold binds in *;
    assert (Hlink : (In (Y,abind_tvar_empty) (awl_to_aenv S ++ (X,abind_etvar_empty)::awl_to_aenv P) \/
                     In (Y,abind_stvar_empty) (awl_to_aenv S ++ (X,abind_etvar_empty)::awl_to_aenv P)))
      by (unfold binds; eauto using in_or_app);
    destruct Hlink as [HL|HL];
    pose proof (binds_unique _ _ _ _ _ HB HL HW); discriminate.
Qed.

Definition fixes (p : atom -> atom) (L : atoms) :=
  forall X, X `in` L -> p X = X.

Definition fixes_images (p : atom -> atom) (f : assignment) (L : atoms) :=
  forall X, X `in` L -> ren_typ p (f X) = f X.

Local Ltac restrict_fixes :=
  unfold fixes, fixes_images in *; cbn in *; intros;
  match goal with
  | H : forall X, X `in` _ -> ?p X = X |- ?p ?x = ?x => apply H; fsetdec
  | H : forall X, X `in` _ -> ren_typ ?p (?f X) = ?f X |- ren_typ ?p (?f ?x) = ?f ?x => apply H; fsetdec
  end.

Lemma fix_interp_typ : forall A p f, fixes_images p f (ftvar_in_typ A) ->
  ren_typ p (interp_typ f A) = interp_typ f A.
Proof.
  induction A; intros; cbn; try reflexivity; try solve [restrict_fixes].
  all: f_equal; first [apply IHA |apply IHA1|apply IHA2]; restrict_fixes.
Qed.

Lemma fix_interp_exp : forall e p f, fixes p (fvar_in_exp e) -> fixes_images p f (ftvar_in_exp e) ->
  ren_exp p (interp_exp f e) = interp_exp f e.
Proof.
  induction e; intros; cbn; try reflexivity;
    f_equal; first [apply IHe|apply IHe1|apply IHe2|apply fix_interp_typ|idtac];
    restrict_fixes.
Qed.

Lemma fix_interp_cont :
  (forall d p f, fixes p (fvar_in_contd d) -> fixes_images p f (ftvar_in_contd d) ->
   ren_cd p (interp_cd f d) = interp_cd f d) /\
  (forall s p f, fixes p (fvar_in_conts s) -> fixes_images p f (ftvar_in_conts s) ->
   ren_cs p (interp_cs f s) = interp_cs f s).
Proof.
  apply contd_conts_mutind; intros; cbn; f_equal;
    first [apply fix_interp_typ|apply fix_interp_exp|
      match goal with IH : forall p f, fixes p _ -> fixes_images p f _ -> _ |- _ => apply IH end];
    restrict_fixes.
Qed.

Lemma fix_interp_work : forall w p f, fixes p (fvar_in_work w) -> fixes_images p f (ftvar_in_work w) ->
  ren_work p (interp_work f w) = interp_work f w.
Proof.
  destruct fix_interp_cont as [Hd Hs]. destruct w; intros; cbn; f_equal;
    first [apply fix_interp_typ|apply fix_interp_exp|apply Hd|apply Hs]; restrict_fixes.
Qed.

Lemma fix_mono : forall E A, d_mono_typ E A -> forall p,
  fixes p (dom E) -> ren_typ p A = A.
Proof.
  intros E A H; induction H; intros; cbn; auto.
  - f_equal; eauto using binds_In.
  - f_equal; auto.
Qed.

Lemma regulars_dom : forall G X,
  X `in` dom (regulars G) -> X `in` worklist_dom G.
Proof.
  intros G X HX; apply binds_In_inv in HX as [b Hb].
  assert (K : forall G X b, binds X b (regulars G) -> b = dbind_tvar_empty).
  { intros G0; induction G0 as [|G0 IH y bk|G0 IH w]; intros z c H; simpl in H.
    - contradiction.
    - destruct bk; cbn in H; try solve [apply (IH _ _ H)].
      apply binds_cons_cases in H as [[_ ->]|H]; eauto.
    - apply (IH _ _ H). }
  rewrite (K _ _ _ Hb) in Hb. apply regulars_binds in Hb.
  unfold worklist_dom; eauto using binds_In.
Qed.

Lemma fix_valid_assignment : forall G f p,
  valid_assignment f G -> fixes p (worklist_dom G) -> fixes_images p f (worklist_dom G).
Proof.
  intros G f p [HS HI] HP X HX.
  destruct (etvar_binds_dec G X) as [HB|HB].
  - eapply fix_mono; [eapply scoped_assignment_binds; eassumption|].
    intros Y HY; apply HP; eauto using regulars_dom.
  - rewrite HI by assumption. cbn. f_equal; eauto.
Qed.

Lemma fix_interp_wl : forall G p f,
  a_wf_wwl G ->
  fixes p (worklist_dom G) ->
  fixes p (fvar_in_aworklist' G) ->
  fixes_images p f (worklist_dom G) ->
  ren_wl p (interp_wl f G) = interp_wl f G.
Proof.
  intros G p f HW; induction HW; cbn; intros HP HT HI; try reflexivity;
    try solve [rewrite IHHW by (unfold worklist_dom in *; cbn in *; restrict_fixes); reflexivity].
  - rewrite IHHW by (unfold worklist_dom in *; cbn in *; restrict_fixes).
    f_equal.
    + apply HP; unfold worklist_dom; cbn; fsetdec.
    + f_equal. apply fix_interp_typ. intros Y HY. apply HI.
      pose proof (a_wf_typ_scope _ _ H0 Y HY).
      unfold worklist_dom; cbn; fsetdec.
  - rewrite IHHW by (unfold worklist_dom in *; cbn in *; restrict_fixes).
    f_equal. apply HP; unfold worklist_dom; cbn; fsetdec.
  - rewrite IHHW by (unfold worklist_dom in *; cbn in *; restrict_fixes).
    f_equal. apply HP; unfold worklist_dom; cbn; fsetdec.
  - rewrite IHHW by (unfold worklist_dom in *; cbn in *; restrict_fixes).
    f_equal. apply fix_interp_work; [restrict_fixes|].
    intros Y HY; apply HI. eapply a_wf_work_scope; eassumption.
Qed.

Definition swap_names (x y z : atom) : atom :=
  if eq_var z x then y else if eq_var z y then x else z.

Lemma swap_at : forall x y, swap_names x y x = y.
Proof. unfold swap_names; intros; destruct (eq_var x x); congruence. Qed.

Lemma swap_involution : forall x y z, swap_names x y (swap_names x y z) = z.
Proof.
  unfold swap_names; intros.
  destruct (eq_var z x) as [->|H1].
  - destruct (eq_var y x), (eq_var y y); congruence.
  - destruct (eq_var z y) as [->|H2].
    + destruct (eq_var x x); congruence.
    + destruct (eq_var z x), (eq_var z y); congruence.
Qed.

Lemma swap_fixes : forall L x y, x `notin` L -> y `notin` L -> fixes (swap_names x y) L.
Proof. unfold fixes, swap_names; intros; destruct (eq_var X x), (eq_var X y); subst; congruence. Qed.

Definition projected_reduction (G : aworklist) :=
  exists f, valid_assignment f G /\ d_wl_red (interp_wl f G).

Lemma valid_work : forall f G w,
  valid_assignment f (aworklist_cons_work G w) <-> valid_assignment f G.
Proof. reflexivity. Qed.

Lemma valid_nonetvar : forall f G X b,
  b <> abind_etvar_empty ->
  (valid_assignment f (aworklist_cons_var G X b) <-> valid_assignment f G).
Proof.
  intros f G X b Hb.
  assert (K : forall Y, binds Y abind_etvar_empty (awl_to_aenv (aworklist_cons_var G X b)) <->
                       binds Y abind_etvar_empty (awl_to_aenv G)).
  { simpl; intros; split; intros HY; eauto.
    apply binds_cons_cases in HY as [[_ E]|HY]; congruence. }
  unfold valid_assignment. setoid_rewrite K. destruct b; simpl; tauto.
Qed.

Lemma valid_etvar_image : forall G X f,
  valid_assignment f (aworklist_cons_var G X abind_etvar_empty) ->
  d_mono_typ (regulars G) (f X).
Proof. intros G X f [[H _] _]; exact H. Qed.

Lemma valid_fresh : forall G f X,
  valid_assignment f G -> X `notin` worklist_dom G -> f X = typ_var_f X.
Proof. intros G f X [_ H] HX; apply H; intro; eapply binds_dom_contradiction; eassumption. Qed.

Lemma awl_agree_typ : forall A G f g,
  agrees (worklist_dom G) f g -> a_wf_typ (awl_to_aenv G) A ->
  interp_typ f A = interp_typ g A.
Proof. intros; apply interp_typ_ext; intros X HX; apply H; eapply a_wf_typ_scope; eassumption. Qed.

Lemma awl_agree_exp : forall e G f g,
  agrees (worklist_dom G) f g -> a_wf_exp (awl_to_aenv G) e ->
  interp_exp f e = interp_exp g e.
Proof. intros; apply interp_exp_ext; intros X HX; apply H; eapply a_wf_exp_scope; eassumption. Qed.

Lemma awl_agree_cs : forall cs G f g,
  agrees (worklist_dom G) f g -> a_wf_conts (awl_to_aenv G) cs ->
  interp_cs f cs = interp_cs g cs.
Proof.
  destruct interp_cont_ext as [_ Hext]; destruct a_wf_cont_scope as [Hscope _].
  intros; apply Hext; intros X HX; apply H; eapply Hscope; eassumption.
Qed.

Lemma awl_agree_cd : forall cd G f g,
  agrees (worklist_dom G) f g -> a_wf_contd (awl_to_aenv G) cd ->
  interp_cd f cd = interp_cd g cd.
Proof.
  destruct interp_cont_ext as [Hext _]; destruct a_wf_cont_scope as [_ Hscope].
  intros; apply Hext; intros X HX; apply H; eapply Hscope; eassumption.
Qed.

Local Hint Resolve a_wf_open_all a_wf_open_all_extend a_mono_wf : awf.
Local Hint Resolve a_wf_typ_weak_map a_wf_exp_weak_map a_wf_work_weak_map : awf.

Lemma awf_cs_weak : forall E cs, a_wf_conts E cs ->
  forall F, (forall X b, binds X b E -> binds X b F) -> a_wf_conts F cs.
Proof.
  intros; rewrite <- (interp_cs_id cs).
  eapply (proj1 interp_a_wf_cont); eauto using a_typ_map_weak, a_exp_map_weak.
Qed.

Lemma awf_cd_weak : forall E cd, a_wf_contd E cd ->
  forall F, (forall X b, binds X b E -> binds X b F) -> a_wf_contd F cd.
Proof.
  intros; rewrite <- (interp_cd_id cd).
  eapply (proj2 interp_a_wf_cont); eauto using a_typ_map_weak, a_exp_map_weak.
Qed.

Local Hint Resolve awf_cs_weak awf_cd_weak : awf.

Local Ltac invert_work_wf :=
  repeat match goal with
  | H : a_wf_wwl (aworklist_cons_work _ _) |- _ => inversion H; subst; clear H
  | H : a_wf_work _ _ |- _ => inversion H; subst; clear H
  | H : a_wf_typ _ (typ_arrow _ _) |- _ => inversion H; subst; clear H
  | H : a_wf_typ _ (typ_union _ _) |- _ => inversion H; subst; clear H
  | H : a_wf_typ _ (typ_intersection _ _) |- _ => inversion H; subst; clear H
  | H : a_wf_exp _ (exp_app _ _) |- _ => inversion H; subst; clear H
  | H : a_wf_exp _ (exp_tapp _ _) |- _ => inversion H; subst; clear H
  | H : a_wf_exp _ (exp_anno _ _) |- _ => inversion H; subst; clear H
  end.

Local Ltac solve_plain_proj :=
  match goal with
  | IH : a_wf_wwl (aworklist_cons_work ?G ?w) -> projected_reduction _ |- _ =>
    let HW := fresh "HW" in let f := fresh "f" in let HV := fresh "HV" in let HR := fresh "HR" in
    assert (HW : a_wf_wwl (aworklist_cons_work G w)) by (eauto 7);
    destruct (IH HW) as [f [HV HR]];
    exists f; split; [exact HV|cbn in HR |- *; eauto 6 with decl_reduce]
  end.


Lemma dl_red_refl_mono : forall E A, d_mono_typ E A ->
  forall D, d_wl_red D -> d_wl_red (dworklist_cons_work D (work_sub A A)).
Proof.
  intros E A H; induction H; intros; eauto 6 with decl_reduce.
Qed.

Lemma interp_project_mono : forall G X B P S,
  aworklist_subst G X B P S -> a_wf_wwl G ->
  a_mono_typ (awl_to_aenv G) B -> X `notin` ftvar_in_typ B ->
  projected_reduction (awl_app (subst_typ_in_aworklist B X S) P) ->
  exists f, valid_assignment f G /\ d_wl_red (interp_wl f G) /\ f X = interp_typ f B.
Proof.
  intros G X B P S HS HW HM HX [g [HV HR]].
  exists (assign g X (interp_typ g B)); repeat split.
  - apply (aws_valid_back _ _ _ _ _ _ HS HW HM HX HV).
  - apply (aws_valid_back _ _ _ _ _ _ HS HW HM HX HV).
  - rewrite <- (aws_interp_target G X B P S g);
      try assumption; eauto using interp_assign_other.
    + symmetry; apply interp_assign_self.
    + intros; symmetry; apply interp_assign_other; assumption.
  - rewrite interp_assign_self, interp_assign_fresh_typ; auto.
Qed.

Lemma project_split_arrow : forall G S X X1 X2,
  let T := typ_arrow (typ_var_f X1) (typ_var_f X2) in
  let E := aworklist_cons_var (aworklist_cons_var G X1 abind_etvar_empty) X2 abind_etvar_empty in
  let D := awl_app S E in
  X <> X1 -> X <> X2 ->
  binds X abind_etvar_empty (awl_to_aenv G) ->
  a_wf_wwl D ->
  (forall P S, aworklist_subst D X T P S ->
    a_wf_wwl (awl_app (subst_typ_in_aworklist T X S) P) ->
    projected_reduction (awl_app (subst_typ_in_aworklist T X S) P)) ->
  exists f g, valid_assignment f G /\ agrees (worklist_dom G) g f /\    f X = typ_arrow (g X1) (g X2) /\ d_wl_red (interp_wl g D).
Proof.
  intros G S X X1 X2 T E D HX1 HX2 HX HW IH.
  assert (Hboth : forall Y, Y `in` ftvar_in_typ T ->
    binds Y abind_etvar_empty (awl_to_aenv D)).
  { intros Y HY. unfold T in HY; simpl in HY.
    assert (Hsplit : Y = X1 \/ Y = X2) by fsetdec.
    destruct Hsplit as [->| ->]; unfold D; rewrite awl_to_aenv_app;
    unfold binds; apply in_or_app; right; unfold E; simpl; auto. }
  assert (Hbind : binds X abind_etvar_empty (awl_to_aenv D)).
  { unfold D. rewrite awl_to_aenv_app. unfold binds in *. apply in_or_app. right.
    unfold E; simpl; auto. }
  assert (HM : a_mono_typ (awl_to_aenv D) T).
  { unfold T; constructor; apply a_mono_typ__etvar; apply Hboth; simpl; fsetdec. }
  assert (Hnot : X `notin` ftvar_in_typ T) by (unfold T; simpl; fsetdec).
  destruct (aws_exists_etvars _ _ _ Hbind HW Hboth) as [P [S' HS]].
  destruct (interp_project_mono _ _ _ _ _ HS HW HM Hnot
    (IH _ _ HS (aws_target_wf _ _ _ _ _ HS HW HM Hnot))) as [g [HV [HR HE]]].
  assert (HG : exists S', D = awl_app S' G).
  { exists (awl_app S (aworklist_cons_var
       (aworklist_cons_var aworklist_empty X1 abind_etvar_empty) X2 abind_etvar_empty)).
    rewrite awl_app_assoc; reflexivity. }
  destruct HG as [S'0 HS0].
  destruct (valid_prefix_restrict G S'0 g ltac:(rewrite <- HS0; exact HW)
     ltac:(rewrite <- HS0; exact HV)) as [f [Hf HA]].
  exists f, g; repeat split; try apply Hf; auto.
  rewrite <- HA by (unfold worklist_dom; eauto using binds_In). exact HE.
Qed.

Lemma awl_fixes_typ : forall A G f p,
  a_wf_typ (awl_to_aenv G) A -> fixes_images p f (worklist_dom G) ->
  ren_typ p (interp_typ f A) = interp_typ f A.
Proof.
  intros; apply fix_interp_typ. intros X HX; apply H0; eapply a_wf_typ_scope; eassumption.
Qed.

Definition binder_avoid (G : aworklist) (e : exp) :=
  worklist_dom G `union` fvar_in_aworklist' G `union` fvar_in_exp e.

Lemma rename_abs_body : forall G f e A B L x,
  a_wf_wwl G -> valid_assignment f G -> a_wf_exp (awl_to_aenv G) (exp_abs e) ->
  (forall p, fixes p (worklist_dom G) -> ren_typ p A = A /\ ren_typ p B = B) ->
  x `notin` (binder_avoid G e `union` L) ->
  d_wl_red (dworklist_cons_work (dworklist_cons_var (interp_wl f G) x (dbind_typ A))
            (work_check (open_exp_wrt_exp (interp_exp f e) (exp_var_f x)) B)) ->
  forall y, y `notin` (binder_avoid G e `union` L) ->
  d_wl_red (dworklist_cons_work (dworklist_cons_var (interp_wl f G) y (dbind_typ A))
            (work_check (open_exp_wrt_exp (interp_exp f e) (exp_var_f y)) B)).
Proof.
  intros G f e A B L x HG HV HE HT Hx HR y Hy.
  unfold binder_avoid in *.
  pose (p := swap_names x y).
  assert (HF : fixes p (worklist_dom G)) by (apply swap_fixes; fsetdec).
  assert (HI := fix_valid_assignment G f p HV HF).
  assert (HW : ren_wl p (interp_wl f G) = interp_wl f G).
  { apply fix_interp_wl; auto. apply swap_fixes; fsetdec. }
  assert (HX : ren_exp p (interp_exp f e) = interp_exp f e).
  { apply fix_interp_exp; [apply swap_fixes; fsetdec|].
    intros U HU; apply HI. eapply a_wf_exp_scope; [exact HE|exact HU]. }
  destruct (HT p HF) as [Ha Hb].
  pose proof (ren_d_reduce _ HR p (swap_involution x y)) as H; cbn in H.
  assert (Hs : p x = y) by apply swap_at.
  rewrite ren_open_exp_exp, HW, HX, Hs, Ha, Hb in H; exact H.
Qed.

Lemma project_check_abs : forall G e A B L,
  a_wf_wwl G -> a_wf_exp (awl_to_aenv G) (exp_abs e) ->
  a_wf_typ (awl_to_aenv G) A -> a_wf_typ (awl_to_aenv G) B ->
  (forall x, x `notin` L ->
     a_wf_wwl (aworklist_cons_work (aworklist_cons_var G x (abind_var_typ A))
         (work_check (open_exp_wrt_exp e (exp_var_f x)) B)) ->
     projected_reduction (aworklist_cons_work (aworklist_cons_var G x (abind_var_typ A))
         (work_check (open_exp_wrt_exp e (exp_var_f x)) B))) ->
  exists f, valid_assignment f G /\  forall y, y `notin` (binder_avoid G e `union` L) ->
    d_wl_red (dworklist_cons_work
        (dworklist_cons_var (interp_wl f G) y (dbind_typ (interp_typ f A)))
        (work_check (open_exp_wrt_exp (interp_exp f e) (exp_var_f y)) (interp_typ f B))).
Proof.
  intros G e A B L HG HE HA HB IH.
  destruct (a_wf_abs_open _ _ A HE) as [M HM].
  pick fresh x for (binder_avoid G e `union` L `union` M).
  assert (x `notin` worklist_dom G) by (unfold binder_avoid in *; fsetdec).
  specialize (IH x ltac:(fsetdec)).
  destruct (IH ltac:(apply a_wf_wwl__conswork;
      [constructor; [apply HM; fsetdec|eapply (a_wf_typ_weak_map _ _ HB); simpl; intros; auto]
      |constructor; assumption])) as [f [HV HR]].
  apply valid_work in HV. apply valid_nonetvar in HV; [|discriminate].
  exists f; split; auto.
  cbn in HR. rewrite interp_open_exp_exp in HR.
  eapply rename_abs_body with (x := x); try eassumption; try fsetdec.
  intros p HP. split; eapply awl_fixes_typ; eauto using fix_valid_assignment.
Qed.

Lemma project_drop_etvar : forall G X w g,
  a_wf_wwl (aworklist_cons_work (aworklist_cons_var G X abind_etvar_empty) w) ->
  valid_assignment g (aworklist_cons_work (aworklist_cons_var G X abind_etvar_empty) w) ->
  exists f, valid_assignment f G /\ agrees (worklist_dom G) g f /\    d_mono_typ (interp_env f G) (g X).
Proof.
  intros. change (a_wf_wwl (awl_app (aworklist_cons_work (aworklist_cons_var aworklist_empty X abind_etvar_empty) w) G)) in H.
  destruct (valid_prefix_restrict _ _ _ H H0) as [f [Hf HA]].
  exists f; split; [exact Hf|split; [exact HA|]].
  eapply d_mono_weak_map; [apply valid_etvar_image; apply H0|].
  apply regulars_interp_binds.
Qed.

Lemma worklist_bind_dom : forall G X b,
  binds X b (awl_to_aenv G) -> X `in` worklist_dom G.
Proof. unfold worklist_dom; eauto using binds_In. Qed.

Local Hint Resolve worklist_bind_dom : awf.

Lemma fresh_env_cons : forall (E : aenv) (x y : atom) b,
  x <> y -> x `notin` dom E -> x `notin` dom ((y,b)::E).
Proof.
  intros E x y b Hneq Hf Hin; apply Hf. simpl in Hin.
  apply (@AtomSetImpl.add_3 _ y x); [congruence|exact Hin].
Qed.

Lemma fresh_two_etvars : forall G x U V,
  x <> U -> x <> V -> x `notin` worklist_dom G ->
  x `notin` dom (awl_to_aenv (aworklist_cons_var
        (aworklist_cons_var G U abind_etvar_empty) V abind_etvar_empty)).
Proof.
  intros G x U V Hu Hv Hg.
  exact (fresh_env_cons ((U,abind_etvar_empty)::awl_to_aenv G) x V abind_etvar_empty Hv
    (fresh_env_cons (awl_to_aenv G) x U abind_etvar_empty Hu Hg)).
Qed.

Lemma two_etvars_wf : forall G U V,
  a_wf_wwl G -> U `notin` worklist_dom G -> V `notin` worklist_dom G ->
  V <> U ->
  a_wf_wwl (aworklist_cons_var (aworklist_cons_var G U abind_etvar_empty) V abind_etvar_empty).
Proof.
  intros G U V HG HU HV Hneq. apply a_wf_wwl__consetvar.
  - exact (fresh_env_cons (awl_to_aenv G) V U abind_etvar_empty Hneq HV).
  - constructor; assumption.
Qed.

(* A successful algorithmic reduction supplies an assignment and
   a successful reduction of the projected declarative worklist. *)
Lemma projected_from_algorithm : forall G, a_wl_red G ->
  a_wf_wwl G -> projected_reduction G.
Proof.
  intros G H; induction H; intros Hw.
  all: try solve [
    invert_work_wf; solve_plain_proj].
  all: try solve [
    match goal with
    | I : a_wf_wwl _ -> projected_reduction _,
      HS : aworklist_subst ?G ?X ?A ?P ?S |- projected_reduction (aworklist_cons_work ?G (work_sub _ _)) =>
      invert_work_wf;
      let HR := fresh "HR" in let f := fresh "f" in
      let HV := fresh "HV" in let HE := fresh "HE" in
      assert (HR : projected_reduction (awl_app (subst_typ_in_aworklist A X S) P))
        by (apply I; eapply aws_target_wf; eassumption);
      destruct (interp_project_mono _ _ _ _ _ HS ltac:(assumption) ltac:(assumption) ltac:(assumption) HR)
        as [f [HV [HR HE]]];
      exists f; split; [exact HV|cbn; rewrite <- HE;
        eapply dl_red_refl_mono; [eapply scoped_assignment_binds; [apply HV|eassumption]|exact HR]]
    end].
  all: try solve [
    match goal with
    | I : a_wf_wwl _ -> projected_reduction _,
      Hb : binds ?x (abind_var_typ ?A) (awl_to_aenv ?G) |- projected_reduction (aworklist_cons_work ?G (work_infer (exp_var_f ?x) ?cs)) =>
      invert_work_wf;
      let f := fresh "f" in let HV := fresh "HV" in let HR := fresh "HR" in
      destruct (I ltac:(apply a_wf_wwl__conswork; [constructor; [eapply awl_bind_type_wf; eassumption|assumption]|assumption]))
        as [f [HV HR]];
      exists f; split; [exact HV|cbn];
      eapply d_wl_red__inf_var with (A := interp_typ f A);
      [rewrite interp_wl_env; eapply interp_env_var_binds; eassumption|exact HR]
    end].
  all: try solve [
    match goal with
    | I : a_wf_wwl _ -> projected_reduction _
      |- projected_reduction (aworklist_cons_work ?G (work_inftapp (typ_all ?A) ?B ?cs)) =>
      invert_work_wf;
      let f := fresh "f" in let HV := fresh "HV" in let HR := fresh "HR" in let HC := fresh "HC" in
      destruct (I ltac:(apply a_wf_wwl__conswork; [constructor; [eapply a_wf_open_all; eassumption|assumption]|assumption]))
        as [f [HV HR]];
      exists f; split; [exact HV|cbn in HR |- *];
      pose proof (proj1 (valid_assignment_facts f G HV)) as HC;
      apply d_wl_red__inftapp_all; rewrite <- interp_open_typ by exact HC; exact HR
    end].
  all: try solve [
    match goal with H : apply_conts _ _ _ |- _ => destruct H end;
    invert_work_wf;
    repeat match goal with H : a_wf_conts _ ?C |- _ => tryif is_var C then fail else (inversion H; subst; clear H) end;
    solve_plain_proj].
  all: try solve [
    match goal with H : apply_contd _ _ _ _ |- _ => destruct H end;
    invert_work_wf;
    repeat match goal with H : a_wf_contd _ ?C |- _ => tryif is_var C then fail else (inversion H; subst; clear H) end;
    solve_plain_proj].
  - exists typ_var_f; split; [split; reflexivity || exact I|constructor].
  - assert (HW0 : a_wf_wwl Γ) by (inversion Hw; assumption).
    destruct (IHa_wl_red HW0) as [f [HV HR]].
    destruct b; try solve [
      exists f; split; [apply valid_nonetvar; discriminate || assumption|simpl; constructor; assumption]].
    inversion Hw; subst.
    exists (assign f X typ_unit); split.
    + split.
      * simpl. rewrite interp_assign_self. split; [constructor|].
        assert (HA : forall Y, binds Y abind_etvar_empty (awl_to_aenv Γ) ->
          f Y = assign f X typ_unit Y).
        { intros Y HY; symmetry; apply interp_assign_other; intro; subst;
            eauto using binds_dom_contradiction. }
        apply (proj1 (scoped_same Γ f _ HA)); apply HV.
      * intros Y HY. rewrite interp_assign_other.
        -- apply HV. intro HB; apply HY; simpl; auto.
        -- intro; subst. apply HY; simpl; auto.
    + simpl. erewrite <- interp_wl_agree; try eassumption.
      intros Y HY; symmetry; apply interp_assign_other; intro; subst; contradiction.
  - invert_work_wf. destruct (IHa_wl_red ltac:(assumption)) as [f [HV HR]].
    exists f; split; [exact HV|simpl; apply d_wl_red__sub_top; assumption].
  - invert_work_wf. destruct (IHa_wl_red ltac:(assumption)) as [f [HV HR]].
    exists f; split; [exact HV|simpl; apply d_wl_red__sub_bot; assumption].
  - invert_work_wf. destruct (IHa_wl_red ltac:(assumption)) as [f [HV HR]].
    exists f; split; [exact HV|simpl; apply d_wl_red__sub_unit; assumption].
  - invert_work_wf. destruct (IHa_wl_red ltac:(assumption)) as [f [HV HR]].
    exists f; split; [exact HV|simpl].
    destruct (etvar_binds_dec Γ X) as [HX|HX].
    + eapply dl_red_refl_mono; [eapply scoped_assignment_binds; [apply HV|exact HX]|assumption].
    + rewrite (proj2 HV X HX). apply d_wl_red__sub_tvar; assumption.
  - invert_work_wf.
    pick fresh X for (L `union` worklist_dom Γ).
    assert (HW : a_wf_wwl (aworklist_cons_work (aworklist_cons_var Γ X abind_etvar_empty)
        (work_sub (B1 ᵗ^ₜ X) A1))).
    { apply a_wf_wwl__conswork.
      - constructor; [apply a_wf_open_all_extend; eauto|eapply a_wf_typ_weak_map; [eassumption|simpl; intros; auto]].
      - constructor; try assumption. unfold worklist_dom in *; fsetdec. }
    destruct (H1 X ltac:(fsetdec) HW) as [g [Hg Hr]].
    destruct (project_drop_etvar _ _ _ _ HW Hg) as [f [Hf [Ha Hmono]]].
    exists f; split; [exact Hf|simpl].
    eapply d_wl_red__sub_alll with (T := g X).
    + rewrite interp_wl_env. eapply d_neq_of_a_neq; eassumption.
    + rewrite interp_wl_env; exact Hmono.
    + simpl in Hr. rewrite interp_open_typ in Hr by (eapply valid_assignment_facts; exact Hg).
      cbn in Hr. rewrite (interp_wl_agree Γ g f ltac:(assumption) Ha) in Hr.
      rewrite (awl_agree_typ A1 Γ g f Ha ltac:(assumption)) in Hr.
      assert (HB : interp_typ g (typ_all B1) = interp_typ f (typ_all B1)) by
        (apply (awl_agree_typ _ Γ); assumption).
      simpl in HB; injection HB as HB. now rewrite HB in Hr.
  - invert_work_wf.
    pose (K := L `union` worklist_dom Γ `union` fvar_in_aworklist' Γ).
    pick fresh X for K.
    assert (HW : a_wf_wwl (aworklist_cons_work (aworklist_cons_var Γ X abind_stvar_empty)
        (work_sub (B1 ᵗ^ₜ X) (A1 ᵗ^ₜ X)))).
    { constructor.
      - constructor; apply a_wf_open_all_extend; eauto.
      - constructor; try assumption. unfold K, worklist_dom in *; fsetdec. }
    destruct (H0 X ltac:(unfold K in *; fsetdec) HW) as [f [Hf Hr]].
    apply valid_work in Hf. apply valid_nonetvar in Hf; [|discriminate].
    assert (HX : f X = typ_var_f X) by
      (apply (valid_fresh Γ); auto; unfold K in *; fsetdec).
    exists f; split; [exact Hf|simpl].
    apply d_wl_red__sub_all with (L := K); intros Y HY.
    set (p := swap_names X Y).
    assert (HP : fixes p (worklist_dom Γ)) by (apply swap_fixes; unfold K in *; fsetdec).
    assert (HI := fix_valid_assignment Γ f p Hf HP).
    assert (Hfix : ren_wl p (interp_wl f Γ) = interp_wl f Γ).
    { apply fix_interp_wl; auto. apply swap_fixes; unfold K in *; fsetdec. }
    simpl in Hr. rewrite !interp_open_typ in Hr by (apply (proj1 (valid_assignment_facts _ _ Hf))).
    cbn in Hr; rewrite HX in Hr.
    pose proof (ren_d_reduce _ Hr p (swap_involution X Y)) as HH; cbn in HH.
    assert (Hp : p X = Y) by apply swap_at.
    assert (HB : ren_typ p (interp_typ f (typ_all B1)) = interp_typ f (typ_all B1))
      by (eapply awl_fixes_typ; eassumption).
    assert (HA : ren_typ p (interp_typ f (typ_all A1)) = interp_typ f (typ_all A1))
      by (eapply awl_fixes_typ; eassumption).
    simpl in HA, HB; injection HA as HA; injection HB as HB.
    change (ren_typ p (interp_typ f A1) = interp_typ f A1) in HA.
    change (ren_typ p (interp_typ f B1) = interp_typ f B1) in HB.
    rewrite !ren_open_typ, Hfix, HA, HB in HH.
    change (ren_typ p (typ_var_f X)) with (typ_var_f (p X)) in HH.
    now rewrite Hp in HH.
  - invert_work_wf.
    pose (K := L `union` worklist_dom Γ).
    pick fresh U for K.
    pick fresh V for (K `union` singleton U).
    assert (HX : X `in` worklist_dom Γ) by (eauto with awf).
    assert (HW : a_wf_wwl (awl_app (aworklist_cons_work aworklist_empty (work_sub (typ_var_f X) (typ_arrow A1 A2)))
       (aworklist_cons_var (aworklist_cons_var Γ U abind_etvar_empty) V abind_etvar_empty))).
    { cbn. apply a_wf_wwl__conswork.
      - apply a_wf_work__sub.
        all: try apply a_wf_typ__arrow.
        all: eapply a_wf_typ_weak_map; [eassumption|simpl; intros; auto].
      - apply two_etvars_wf; try assumption.
        + clear - Fr. unfold K in *; fsetdec.
        + clear - Fr0. unfold K in *; fsetdec.
        + clear - Fr0; fsetdec. }
    destruct (project_split_arrow _ _ X U V ltac:(unfold K in *; fsetdec)
      ltac:(unfold K in *; fsetdec) H HW) as [f [g [Hf [HA [HE HR]]]]].
    { intros P S HS HT. eapply H2; try eassumption; unfold K in *; fsetdec. }
    exists f; split; [exact Hf|simpl].
    cbn in HR. rewrite (interp_wl_agree Γ g f ltac:(assumption) HA) in HR.
    rewrite (awl_agree_typ A1 Γ g f HA ltac:(assumption)),
            (awl_agree_typ A2 Γ g f HA ltac:(assumption)), HA in HR by exact HX.
    exact HR.
  - invert_work_wf.
    pose (K := L `union` worklist_dom Γ).
    pick fresh U for K.
    pick fresh V for (K `union` singleton U).
    assert (HX : X `in` worklist_dom Γ) by (eauto with awf).
    assert (HW : a_wf_wwl (awl_app (aworklist_cons_work aworklist_empty (work_sub (typ_arrow A1 A2) (typ_var_f X)))
       (aworklist_cons_var (aworklist_cons_var Γ U abind_etvar_empty) V abind_etvar_empty))).
    { cbn. apply a_wf_wwl__conswork.
      - apply a_wf_work__sub.
        all: try apply a_wf_typ__arrow.
        all: eapply a_wf_typ_weak_map; [eassumption|simpl; intros; auto].
      - apply two_etvars_wf; try assumption.
        + clear - Fr. unfold K in *; fsetdec.
        + clear - Fr0. unfold K in *; fsetdec.
        + clear - Fr0; fsetdec. }
    destruct (project_split_arrow _ _ X U V ltac:(unfold K in *; fsetdec)
      ltac:(unfold K in *; fsetdec) H HW) as [f [g [Hf [HA [HE HR]]]]].
    { intros P S HS HT. eapply H2; try eassumption; unfold K in *; fsetdec. }
    exists f; split; [exact Hf|simpl].
    cbn in HR. rewrite (interp_wl_agree Γ g f ltac:(assumption) HA) in HR.
    rewrite (awl_agree_typ A1 Γ g f HA ltac:(assumption)),
            (awl_agree_typ A2 Γ g f HA ltac:(assumption)), HA in HR by exact HX.
    exact HR.
  - invert_work_wf.
    destruct (interp_project_mono _ _ _ _ _ H2 ltac:(assumption) H0 H1
      (IHa_wl_red (aws_target_wf _ _ _ _ _ H2 ltac:(assumption) H0 H1))) as [f [HV [HR HE]]].
    exists f; split; [exact HV|cbn; rewrite <- HE].
    eapply dl_red_refl_mono; [eapply scoped_assignment_binds; [apply HV|exact H]|exact HR].
  - invert_work_wf.
    destruct (interp_project_mono _ _ _ _ _ H2 ltac:(assumption) H0 H1
      (IHa_wl_red (aws_target_wf _ _ _ _ _ H2 ltac:(assumption) H0 H1))) as [f [HV [HR HE]]].
    exists f; split; [exact HV|cbn; rewrite <- HE].
    eapply dl_red_refl_mono; [eapply scoped_assignment_binds; [apply HV|exact H]|exact HR].
  - invert_work_wf.
    destruct (project_check_abs Γ e A1 A2 L ltac:(assumption) ltac:(assumption)
              ltac:(assumption) ltac:(assumption) H0) as [f [HV HR]].
    exists f; split; [exact HV|simpl].
    eapply d_wl_red__chk_absarrow; exact HR.
  - invert_work_wf.
    destruct (a_wf_abs_open _ _ typ_bot ltac:(eassumption)) as [M HM].
    pose (K := binder_avoid Γ e `union` L `union` M).
    pick fresh x for K.
    pick fresh U for (K `union` singleton x).
    pick fresh V for (K `union` singleton x `union` singleton U).
    assert (HX : X `in` worklist_dom Γ) by (eauto with awf).
    pose (S := aworklist_cons_work (aworklist_cons_var aworklist_empty x (abind_var_typ (typ_var_f U)))
        (work_check (open_exp_wrt_exp e (exp_var_f x)) (typ_var_f V))).
    assert (HW : a_wf_wwl (awl_app S (aworklist_cons_var
       (aworklist_cons_var Γ U abind_etvar_empty) V abind_etvar_empty))).
    { unfold S; cbn. constructor.
      - constructor.
        + eapply a_wf_exp_retype; [apply HM; unfold K in *; fsetdec| |].
          * simpl. intros Y b Hb Hneq. apply binds_cons_cases in Hb as [[-> ->]|Hb].
            -- exfalso; eapply Hneq; reflexivity.
            -- auto.
          * simpl. intros Y T Hb. apply binds_cons_cases in Hb as [[-> _]|Hb].
            -- exists (typ_var_f U); auto.
            -- exists T; auto.
        + apply a_wf_typ__etvar; simpl; eauto.
      - apply a_wf_wwl__consvar.
        + apply fresh_two_etvars; [clear - Fr0; fsetdec|clear - Fr1; fsetdec|].
          clear - Fr. unfold K, binder_avoid, worklist_dom in *; fsetdec.
        + apply a_wf_typ__etvar; simpl; eauto.
        + apply two_etvars_wf; try assumption.
          * clear - Fr0. unfold K, binder_avoid in *; fsetdec.
          * clear - Fr1. unfold K, binder_avoid in *; fsetdec.
          * clear - Fr1; fsetdec. }
    destruct (project_split_arrow Γ S X U V
      ltac:(unfold K, binder_avoid in *; fsetdec)
      ltac:(unfold K, binder_avoid in *; fsetdec) H HW) as [f [g [Hf [Ha [He Hr]]]]].
    { intros P S' HS HT.
      exact (H1 x ltac:(unfold K in *; fsetdec)
        U ltac:(unfold K in *; fsetdec)
        V ltac:(unfold K in *; fsetdec) P S' HS HT). }
    exists f; split; [exact Hf|simpl; rewrite He].
    apply d_wl_red__chk_absarrow with (L := binder_avoid Γ e `union` (L `union` M)).
    eapply (rename_abs_body Γ f e (g U) (g V) (L `union` M) x); try eassumption.
    + intros p Hp. pose proof (fix_valid_assignment Γ f p Hf Hp X HX) as HF.
      rewrite He in HF; simpl in HF. injection HF as HfixU HfixV; split; assumption.
    + unfold S in Hr; simpl in Hr. rewrite interp_open_exp_exp in Hr.
      rewrite (interp_wl_agree Γ g f ltac:(assumption) Ha) in Hr.
      assert (Hbody : interp_exp g (exp_abs e) = interp_exp f (exp_abs e))
        by (apply (awl_agree_exp _ Γ); assumption).
      simpl in Hbody; injection Hbody as Hbody; now rewrite Hbody in Hr.
  - invert_work_wf.
    destruct (project_check_abs Γ e typ_bot typ_top L ltac:(assumption) ltac:(assumption)
              ltac:(constructor) ltac:(constructor) H0) as [f [HV HR]].
    exists f; split; [exact HV|simpl].
    eapply d_wl_red__chk_abstop; exact HR.
  - invert_work_wf.
    match goal with HH : a_wf_exp _ (exp_tabs _) |- _ =>
      pose proof HH as Htabs; inversion HH; subst end.
    assert (HA : a_wf_typ (awl_to_aenv Γ) (typ_all A)).
    { apply a_wf_typ__all with (L := L0); auto.
      intros X HX. match goal with HB : forall X, X `notin` L0 -> a_wf_exp _ _ |- _ =>
        specialize (HB X HX); inversion HB; assumption end. }
    pose (P := aworklist_cons_work Γ (work_applys cs (typ_all A))).
    assert (HP : a_wf_wwl P) by (unfold P; eauto).
    pose (K := binder_avoid P e `union` L `union` L0).
    pick fresh X for K.
    assert (HW : a_wf_wwl (aworklist_cons_work (aworklist_cons_var P X abind_tvar_empty)
       (work_check (open_exp_wrt_typ e (typ_var_f X)) (A ᵗ^ₜ X)))).
    { constructor.
      - constructor; match goal with HB : forall X, X `notin` L0 -> a_wf_exp _ _ |- _ =>
          specialize (HB X ltac:(unfold K in *; fsetdec)); inversion HB; assumption end.
      - constructor; try assumption. unfold K, binder_avoid, P, worklist_dom in *; simpl in *; fsetdec. }
    destruct (H0 X ltac:(unfold K in *; fsetdec) HW) as [f [Hf Hr]].
    apply valid_work in Hf. apply valid_nonetvar in Hf; [|discriminate].
    assert (HX : f X = typ_var_f X) by
      (apply (valid_fresh P); auto; unfold K, binder_avoid in *; fsetdec).
    exists f; split; [exact Hf|simpl].
    apply d_wl_red__inf_tabs with (L := K); intros Y HY.
    set (p := swap_names X Y).
    assert (Hfix : fixes p (worklist_dom P)) by (apply swap_fixes; unfold K, binder_avoid in *; fsetdec).
    assert (Hfi := fix_valid_assignment P f p Hf Hfix).
    assert (Hwp : ren_wl p (interp_wl f P) = interp_wl f P).
    { apply fix_interp_wl; auto. apply swap_fixes; unfold K, binder_avoid in *; fsetdec. }
    change (d_wl_red (dworklist_cons_work (dworklist_cons_var (interp_wl f P) X dbind_tvar_empty)
       (work_check (interp_exp f (open_exp_wrt_typ e (typ_var_f X))) (interp_typ f (A ᵗ^ₜ X))))) in Hr.
    rewrite interp_open_exp_typ, interp_open_typ in Hr by (apply (proj1 (valid_assignment_facts _ _ Hf))).
    cbn in Hr; rewrite HX in Hr.
    pose proof (ren_d_reduce _ Hr p (swap_involution X Y)) as HH.
    change (d_wl_red (dworklist_cons_work (dworklist_cons_var (ren_wl p (interp_wl f P)) (p X) dbind_tvar_empty)
       (work_check (ren_exp p (open_exp_wrt_typ (interp_exp f e) (typ_var_f X)))
                   (ren_typ p (open_typ_wrt_typ (interp_typ f A) (typ_var_f X)))))) in HH.
    assert (Hp : p X = Y) by apply swap_at.
    assert (Hty : ren_typ p (interp_typ f (typ_all A)) = interp_typ f (typ_all A))
      by (eapply awl_fixes_typ; [exact HA|exact Hfi]).
    simpl in Hty; injection Hty as Hty.
    change (ren_typ p (interp_typ f A) = interp_typ f A) in Hty.
    assert (Hex : ren_exp p (interp_exp f e) = interp_exp f e).
    { apply fix_interp_exp; [apply swap_fixes; unfold K, binder_avoid in *; fsetdec|].
      intros Z HZ. apply Hfi. unfold P. eapply a_wf_exp_scope; [exact Htabs|simpl; fsetdec]. }
    rewrite ren_open_exp_typ, ren_open_typ, Hwp, Hty, Hex in HH.
    change (ren_typ p (typ_var_f X)) with (typ_var_f (p X)) in HH.
    now rewrite Hp in HH.
  - invert_work_wf.
    destruct (a_wf_abs_open _ _ typ_bot ltac:(eassumption)) as [M HM].
    pose (K := binder_avoid Γ e `union` fvar_in_conts cs `union` L `union` M).
    pick fresh x for K.
    pick fresh U for (K `union` singleton x).
    pick fresh V for (K `union` singleton x `union` singleton U).
    pose (E := aworklist_cons_var (aworklist_cons_var Γ U abind_etvar_empty) V abind_etvar_empty).
    pose (P := aworklist_cons_work E (work_applys cs (typ_arrow (typ_var_f U) (typ_var_f V)))).
    pose (T := aworklist_cons_work (aworklist_cons_var P x (abind_var_typ (typ_var_f U)))
          (work_check (open_exp_wrt_exp e (exp_var_f x)) (typ_var_f V))).
    assert (HE : a_wf_wwl E).
    { unfold E. apply two_etvars_wf; try assumption.
      - clear - Fr0. unfold K, binder_avoid in *; fsetdec.
      - clear - Fr1. unfold K, binder_avoid in *; fsetdec.
      - clear - Fr1; fsetdec. }
    assert (HP : a_wf_wwl P).
    { unfold P. constructor; [|exact HE].
      constructor; unfold E; simpl.
      - constructor; apply a_wf_typ__etvar; auto.
      - eapply awf_cs_weak; [eassumption|auto]. }
    assert (HT : a_wf_wwl T).
    { unfold T; constructor.
      - constructor.
        + eapply a_wf_exp_retype; [apply HM; unfold K in *; fsetdec| |].
          * unfold P, E; simpl. intros Y b Hb Hneq. apply binds_cons_cases in Hb as [[-> ->]|Hb].
            -- exfalso; eapply Hneq; reflexivity.
            -- auto.
          * unfold P, E; simpl. intros y B Hb. apply binds_cons_cases in Hb as [[-> _]|Hb].
            -- exists (typ_var_f U); auto.
            -- exists B; auto.
        + unfold P, E; apply a_wf_typ__etvar; simpl; auto.
      - apply a_wf_wwl__consvar; [|unfold P, E; apply a_wf_typ__etvar; simpl; auto|exact HP].
        unfold P, E. apply fresh_two_etvars; [clear - Fr0; fsetdec|clear - Fr1; fsetdec|].
        clear - Fr. unfold K, binder_avoid, worklist_dom in *; fsetdec. }
    assert (I : projected_reduction T).
    { unfold T, P, E in *; eapply H0; try exact HT; unfold K in *; fsetdec. }
    destruct I as [g [Hg Hr]].
    pose (S := aworklist_cons_work
          (aworklist_cons_var (aworklist_cons_work
          (aworklist_cons_var (aworklist_cons_var aworklist_empty U abind_etvar_empty) V abind_etvar_empty)
          (work_applys cs (typ_arrow (typ_var_f U) (typ_var_f V)))) x (abind_var_typ (typ_var_f U)))
          (work_check (open_exp_wrt_exp e (exp_var_f x)) (typ_var_f V))).
    change (a_wf_wwl (awl_app S Γ)) in HT.
    change (valid_assignment g (awl_app S Γ)) in Hg.
    destruct (valid_prefix_restrict Γ S g HT Hg) as [f [Hf Ha]].
    pose proof (proj1 Hg) as Hs. unfold S in Hs; simpl in Hs.
    destruct Hs as [HV [HU Hs]].
    exists f; split; [exact Hf|simpl].
    eapply d_wl_red__inf_abs_mono with (T1 := g U) (T2 := g V) (L := binder_avoid Γ e
       `union` (fvar_in_conts cs `union` (L `union` M))).
    + rewrite interp_wl_env. constructor; eapply d_mono_weak_map;
        [exact HU|apply regulars_interp_binds|exact HV|apply regulars_interp_binds].
    + intros y Hy.
      set (p := swap_names x y).
      assert (Hfix : fixes p (worklist_dom Γ)) by
        (apply swap_fixes; unfold K, binder_avoid in *; fsetdec).
      assert (Hfi := fix_valid_assignment Γ f p Hf Hfix).
      assert (Hwp : ren_wl p (interp_wl f Γ) = interp_wl f Γ).
      { apply fix_interp_wl; auto. apply swap_fixes; unfold K, binder_avoid in *; fsetdec. }
      assert (Hex : ren_exp p (interp_exp f e) = interp_exp f e).
      { apply fix_interp_exp; [apply swap_fixes; unfold K, binder_avoid in *; fsetdec|].
        intros Z HZ. apply Hfi. eapply a_wf_exp_scope; [eassumption|exact HZ]. }
      assert (Hcs : ren_cs p (interp_cs f cs) = interp_cs f cs).
      { apply (proj2 fix_interp_cont); [apply swap_fixes; unfold K, binder_avoid in *; fsetdec|].
        intros Z HZ. apply Hfi. eapply (proj1 a_wf_cont_scope); eassumption. }
      assert (HMono : forall A, d_mono_typ (regulars Γ) A -> ren_typ p A = A).
      { intros; eapply fix_mono; [eassumption|]. intros Z HZ. apply Hfix; auto using regulars_dom. }
      change (d_wl_red (dworklist_cons_work
        (dworklist_cons_var (dworklist_cons_work (interp_wl g Γ) (work_applys (interp_cs g cs) (typ_arrow (g U) (g V))))
          x (dbind_typ (g U)))
          (work_check (interp_exp g (open_exp_wrt_exp e (exp_var_f x))) (g V)))) in Hr.
      rewrite interp_open_exp_exp, (interp_wl_agree Γ g f ltac:(assumption) Ha),
         (awl_agree_cs cs Γ g f Ha ltac:(assumption)) in Hr.
      assert (Hbody : interp_exp g (exp_abs e) = interp_exp f (exp_abs e))
        by (apply (awl_agree_exp _ Γ); assumption).
      simpl in Hbody; injection Hbody as Hbody; rewrite Hbody in Hr.
      pose proof (ren_d_reduce _ Hr p (swap_involution x y)) as HH. cbn in HH.
      assert (HsW : p x = y) by apply swap_at.
      now rewrite ren_open_exp_exp, Hwp, Hex, Hcs, HsW, (HMono _ HU), (HMono _ HV) in HH.
  - invert_work_wf.
    destruct (IHa_wl_red ltac:(eauto)) as [f [HV HR]].
    exists f; split; [exact HV|simpl].
    simpl in HR; inversion HR; subst; apply d_wl_red__infabs_bot; assumption.
  - invert_work_wf.
    pick fresh X for (L `union` worklist_dom Γ).
    assert (HW : a_wf_wwl (aworklist_cons_work (aworklist_cons_var Γ X abind_etvar_empty)
       (work_infabs (A ᵗ^ₜ X) cd))).
    { constructor.
      - constructor; [apply a_wf_open_all_extend; eauto|eapply awf_cd_weak; [eassumption|simpl; intros; auto]].
      - constructor; try assumption. unfold worklist_dom in *; fsetdec. }
    destruct (H0 X ltac:(fsetdec) HW) as [g [Hg Hr]].
    destruct (project_drop_etvar _ _ _ _ HW Hg) as [f [Hf [Ha Hmono]]].
    exists f; split; [exact Hf|simpl].
    eapply d_wl_red__infabs_all with (T := g X).
    + rewrite interp_wl_env; exact Hmono.
    + simpl in Hr. rewrite interp_open_typ in Hr by (eapply valid_assignment_facts; exact Hg).
      cbn in Hr. rewrite (interp_wl_agree Γ g f ltac:(assumption) Ha),
        (awl_agree_cd cd Γ g f Ha ltac:(assumption)) in Hr.
      assert (HA : interp_typ g (typ_all A) = interp_typ f (typ_all A)) by (apply (awl_agree_typ _ Γ); assumption).
      simpl in HA; injection HA as HA. now rewrite HA in Hr.
  - invert_work_wf.
    pose (K := L `union` worklist_dom Γ).
    pick fresh U for K.
    pick fresh V for (K `union` singleton U).
    assert (HX : X `in` worklist_dom Γ) by (eauto with awf).
    assert (HW : a_wf_wwl (awl_app (aworklist_cons_work aworklist_empty
          (work_infabs (typ_arrow (typ_var_f U) (typ_var_f V)) cd))
       (aworklist_cons_var (aworklist_cons_var Γ U abind_etvar_empty) V abind_etvar_empty))).
    { cbn. constructor.
      - constructor.
        + apply a_wf_typ__arrow; apply a_wf_typ__etvar; simpl; auto.
        + eapply awf_cd_weak; [eassumption|simpl; intros; auto].
      - apply two_etvars_wf; try assumption.
        + clear - Fr. unfold K in *; fsetdec.
        + clear - Fr0. unfold K in *; fsetdec.
        + clear - Fr0; fsetdec. }
    destruct (project_split_arrow _ _ X U V ltac:(unfold K in *; fsetdec)
      ltac:(unfold K in *; fsetdec) H HW) as [f [g [Hf [HA [HE HR]]]]].
    { intros P S HS HT. eapply H1; try eassumption; unfold K in *; fsetdec. }
    exists f; split; [exact Hf|simpl; rewrite HE].
    cbn in HR. rewrite (interp_wl_agree Γ g f ltac:(assumption) HA),
            (awl_agree_cd cd Γ g f HA ltac:(assumption)) in HR. exact HR.
Qed.

Definition embed_binding (b : dbind) :=
  match b with
  | dbind_tvar_empty => abind_tvar_empty
  | dbind_stvar_empty => abind_stvar_empty
  | dbind_typ A => abind_var_typ A
  end.

Fixpoint embed_wl (D : dworklist) : aworklist :=
  match D with
  | dworklist_empty => aworklist_empty
  | dworklist_cons_var D X b => aworklist_cons_var (embed_wl D) X (embed_binding b)
  | dworklist_cons_work D w => aworklist_cons_work (embed_wl D) w
  end.

Lemma embed_projection : forall D, interp_wl typ_var_f (embed_wl D) = D.
Proof.
  induction D; cbn; try reflexivity.
  - destruct db; cbn; rewrite IHD; try reflexivity.
    rewrite interp_typ_id by reflexivity; reflexivity.
  - rewrite IHD, interp_work_id; reflexivity.
Qed.

Lemma embed_assignment : forall D, valid_assignment typ_var_f (embed_wl D).
Proof.
  intro D; split; [|reflexivity].
  induction D; cbn; auto; destruct db; cbn; auto.
Qed.

Lemma embed_env : forall D, interp_env typ_var_f (embed_wl D) = dwl_to_denv D.
Proof. intro; rewrite <- interp_wl_env, embed_projection; reflexivity. Qed.

Definition well_scoped_dl (D : dworklist) :=
  a_wf_wwl (embed_wl D) /\ dl_phase D.

Lemma dl_scoped_env : forall D, well_scoped_dl D -> d_wf_env (dwl_to_denv D).
Proof.
  intros D [HW HP]. rewrite <- embed_env. apply interp_denv_valid;
    auto using embed_assignment.
  unfold awl_phase; now rewrite embed_projection.
Qed.

Lemma dl_scoped_tenv : forall D, a_wf_wwl (embed_wl D) -> dl_no_rigid D ->
  d_wf_tenv (dwl_to_denv D).
Proof.
  intros D HW HP. rewrite <- embed_env. apply interp_tenv_valid;
    auto using embed_assignment.
  unfold awl_no_rigid; now rewrite embed_projection.
Qed.

Lemma dl_wf_typ : forall D A, a_wf_wwl (embed_wl D) ->
  a_wf_typ (awl_to_aenv (embed_wl D)) A -> d_wf_typ (dwl_to_denv D) A.
Proof.
  intros D A HW HA; rewrite <- embed_env, <- (interp_typ_id A typ_var_f) by reflexivity.
  apply d_type_of_a_type; eauto using embed_assignment.
Qed.

Lemma embed_binds : forall D X b, binds X b (dwl_to_denv D) ->
  binds X (embed_binding b) (awl_to_aenv (embed_wl D)).
Proof.
  induction D as [|D IH y c|D IH w]; intros X b H; cbn in *.
  - exact H.
  - apply binds_cons_cases in H as [[-> ->]|H].
    + apply binds_cons_head.
    + apply binds_cons_weak. exact (IH X b H).
  - exact (IH X b H).
Qed.

Lemma d_mono_embed : forall D A,
  d_mono_typ (dwl_to_denv D) A -> a_mono_typ (awl_to_aenv (embed_wl D)) A.
Proof.
  intros D A H; remember (dwl_to_denv D) as E; induction H; subst; eauto.
  apply a_mono_typ__tvar. exact (embed_binds _ _ dbind_tvar_empty H).
Qed.

(* Interpret continuations directly with the declarative judgments.
   Worklist evaluation requires every job to hold in its own prefix. *)
Fixpoint eval_cs (E : denv) (cs : conts) (A : typ) : Prop :=
  match cs with
  | conts_infabs cd => exists B C, d_infabs E A B C /\ eval_cd E cd B C
  | conts_inftapp B cs => exists C, d_inftapp E A B C /\ eval_cs E cs C
  | conts_inftappunion A2 B cs => exists C, d_inftapp E A2 B C /\ eval_cs E cs (typ_union A C)
  | conts_unioninftapp C cs => eval_cs E cs (typ_union C A)
  | conts_sub B => d_sub E A B
  end
with eval_cd (E : denv) (cd : contd) (A B : typ) : Prop :=
  match cd with
  | contd_infabsunion A2 cd =>
      exists C D, d_infabs E A2 C D /\ eval_cd E cd (typ_intersection A C) (typ_union B D)
  | contd_infapp e cs => d_chk_inf E e typingmode__chk A /\ eval_cs E cs B
  | contd_unioninfabs C D cd => eval_cd E cd (typ_intersection C A) (typ_union D B)
  end.

Definition eval_work (E : denv) (w : work) : Prop :=
  match w with
  | work_infer e cs => exists A, d_chk_inf E e typingmode__inf A /\ eval_cs E cs A
  | work_check e A => d_chk_inf E e typingmode__chk A
  | work_infabs A cd => exists B C, d_infabs E A B C /\ eval_cd E cd B C
  | work_infabsunion B C A cd => exists P Q, d_infabs E A P Q /\
      eval_cd E cd (typ_intersection B P) (typ_union C Q)
  | work_infapp A B e cs => d_chk_inf E e typingmode__chk A /\ eval_cs E cs B
  | work_inftapp A B cs => exists C, d_inftapp E A B C /\ eval_cs E cs C
  | work_inftappunion C A B cs => exists D, d_inftapp E A B D /\ eval_cs E cs (typ_union C D)
  | work_sub A B => d_sub E A B
  | work_unioninftapp A B cs => eval_cs E cs (typ_union A B)
  | work_unioninfabs A B C D cd => eval_cd E cd (typ_intersection A C) (typ_union B D)
  | work_applys cs A => eval_cs E cs A
  | work_applyd cd A B => eval_cd E cd A B
  end.

Fixpoint eval_wl (D : dworklist) : Prop :=
  match D with
  | dworklist_empty => True
  | dworklist_cons_var D _ _ => eval_wl D
  | dworklist_cons_work D w => eval_wl D /\ eval_work (dwl_to_denv D) w
  end.


Local Hint Constructors d_sub d_infabs d_inftapp d_chk_inf : eval_decl.
Local Hint Resolve dl_scoped_env dl_scoped_tenv dl_wf_typ : eval_decl.

Local Ltac simplify_dl_wf :=
  unfold well_scoped_dl in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  cbn [embed_wl embed_binding dl_phase dl_no_rigid] in *;
  invert_work_wf.

Local Ltac solve_dl_wf :=
  unfold well_scoped_dl;
  cbn [embed_wl embed_binding dl_phase dl_no_rigid]; split;
  [eauto 7 with awf|tauto].

Local Ltac prepare_dl_env D :=
  let HE := fresh "HE" in let HT := fresh "HT" in let HA := fresh "HEType" in
  assert (HE : d_wf_env (dwl_to_denv D)) by (apply dl_scoped_env; unfold well_scoped_dl; tauto);
  assert (HT : dl_no_rigid D -> d_wf_tenv (dwl_to_denv D))
    by (intro; apply dl_scoped_tenv; assumption);
  assert (HA : forall A, a_wf_typ (awl_to_aenv (embed_wl D)) A -> d_wf_typ (dwl_to_denv D) A)
    by (intros; apply dl_wf_typ; assumption).

Local Ltac destruct_eval :=
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : exists _, _ |- _ => destruct H
  end.

Local Ltac finish_eval := destruct_eval; split; [assumption|eauto 8 with eval_decl].

Lemma declarative_reduction_evaluates : forall D,
  d_wl_red D -> well_scoped_dl D -> eval_wl D.
Proof.
  intros D HR; induction HR; intro HW.
  all: try solve [exact I].
  all: try solve [simplify_dl_wf; cbn; eapply IHHR;
    unfold well_scoped_dl; split; [inversion H; assumption|assumption]].
  all: try solve [
    match goal with
    | IH : well_scoped_dl ?D -> eval_wl ?D |- eval_wl (dworklist_cons_work ?E _) =>
      simplify_dl_wf;
      prepare_dl_env E;
      specialize (IH ltac:(solve_dl_wf));
      cbn in IH |- *;
      finish_eval
    end].
  - simplify_dl_wf. inversion H; subst. apply IHHR.
    unfold well_scoped_dl; split; [assumption|tauto].
  - simplify_dl_wf. inversion H; subst. apply IHHR.
    unfold well_scoped_dl; split; [assumption|tauto].
  - simplify_dl_wf.
    match goal with H : a_wf_typ _ (typ_all A) |- _ => inversion H; subst end.
    match goal with H : a_wf_typ _ (typ_all B) |- _ => inversion H; subst end.
    pose (K := L `union` L0 `union` L1 `union` dom (awl_to_aenv (embed_wl Ω))).
    assert (HX : forall X, X `notin` K ->
      eval_wl Ω /\ d_sub ((X, dbind_stvar_empty)::dwl_to_denv Ω) (A ᵗ^ₜ X) (B ᵗ^ₜ X)).
    { intros X HX. apply (H0 X ltac:(unfold K in *; fsetdec)).
      unfold well_scoped_dl; simpl; split.
      - apply a_wf_wwl__conswork.
        + apply a_wf_work__sub; apply a_wf_open_all_extend; eauto.
        + apply a_wf_wwl__consstvar; [clear - HX; unfold K in *; fsetdec|assumption].
      - assumption. }
    cbn. split.
    + pick fresh X for K. exact (proj1 (HX X Fr)).
    + apply d_sub__all with (L := K); intros X HF; try solve [apply (HX X HF)].
      all: match goal with HH : forall X, X `notin` _ -> s_in X _ |- _ => apply HH; unfold K in *; fsetdec end.
  - simplify_dl_wf.
    assert (Hmono : a_mono_typ (awl_to_aenv (embed_wl Ω)) T) by (eapply d_mono_embed; eassumption).
    assert (Hb : a_wf_typ (awl_to_aenv (embed_wl Ω)) (open_typ_wrt_typ A T))
      by (eapply a_wf_open_all; eauto using a_mono_wf).
    specialize (IHHR ltac:(solve_dl_wf)). cbn in IHHR |- *.
    destruct IHHR as [IH1 IH2]; split; [exact IH1|].
    match goal with H : a_wf_typ _ (typ_all A) |- _ => inversion H; subst end.
    eapply d_sub__alll; eassumption.
  - simplify_dl_wf. prepare_dl_env Ω.
    destruct (a_wf_abs_open (awl_to_aenv (embed_wl Ω)) e A1 ltac:(assumption)) as [M HM].
    pose (K := L `union` M `union` dom (awl_to_aenv (embed_wl Ω))).
    assert (HX : forall x, x `notin` K ->
      eval_wl Ω /\ d_chk_inf ((x,dbind_typ A1)::dwl_to_denv Ω)
        (open_exp_wrt_exp e (exp_var_f x)) typingmode__chk A2).
    { intros x Hx. apply (H0 x ltac:(unfold K in *; fsetdec)).
      unfold well_scoped_dl; cbn; split.
      - apply a_wf_wwl__conswork.
        + apply a_wf_work__check; [apply HM; unfold K in *; fsetdec|].
          eapply a_wf_typ_weak_map; [eassumption|simpl; intros; auto].
        + apply a_wf_wwl__consvar; try assumption. unfold K in *; fsetdec.
      - tauto. }
    cbn. split.
    + pick fresh x for K. exact (proj1 (HX x Fr)).
    + apply d_chk_inf__chk_abs with (L := K); [auto|intros y Hy; apply (HX y Hy)].
  - simplify_dl_wf. prepare_dl_env Ω.
    destruct (a_wf_abs_open (awl_to_aenv (embed_wl Ω)) e typ_bot ltac:(assumption)) as [M HM].
    pose (K := L `union` M `union` dom (awl_to_aenv (embed_wl Ω))).
    assert (HX : forall x, x `notin` K ->
      eval_wl Ω /\ d_chk_inf ((x,dbind_typ typ_bot)::dwl_to_denv Ω)
        (open_exp_wrt_exp e (exp_var_f x)) typingmode__chk typ_top).
    { intros x Hx. apply (H0 x ltac:(unfold K in *; fsetdec)).
      unfold well_scoped_dl; cbn; split.
      - apply a_wf_wwl__conswork.
        + constructor; [apply HM; unfold K in *; fsetdec|constructor].
        + apply a_wf_wwl__consvar; try assumption; [unfold K in *; fsetdec|constructor].
      - tauto. }
    cbn. split.
    + pick fresh x for K. exact (proj1 (HX x Fr)).
    + apply d_chk_inf__chk_abstop with (L := K); intros y Hy; apply (HX y Hy).
  - simplify_dl_wf. prepare_dl_env Ω.
    assert (HA : a_wf_typ (awl_to_aenv (embed_wl Ω)) A).
    { eapply awl_bind_type_wf; [eassumption|]. exact (embed_binds _ _ (dbind_typ A) H). }
    specialize (IHHR ltac:(solve_dl_wf)). cbn in IHHR |- *. finish_eval.
  - simplify_dl_wf. prepare_dl_env Ω.
    match goal with H : a_wf_exp _ (exp_tabs _) |- _ => inversion H; subst end.
    assert (HA : a_wf_typ (awl_to_aenv (embed_wl Ω)) (typ_all A)).
    { apply a_wf_typ__all with (L := L0); auto.
      intros X HX; match goal with H : forall _, _ -> a_wf_exp _ _ |- _ =>
        specialize (H X HX); inversion H; assumption end. }
    pose (K := L `union` L0 `union` dom (awl_to_aenv (embed_wl Ω))).
    assert (HX : forall X, X `notin` K ->
        eval_wl Ω /\ eval_cs (dwl_to_denv Ω) cs (typ_all A) /\
        d_chk_inf ((X,dbind_tvar_empty)::dwl_to_denv Ω)
          (open_exp_wrt_typ e (typ_var_f X)) typingmode__chk (A ᵗ^ₜ X)).
    { intros X HX. assert (HH := H0 X ltac:(unfold K in *; fsetdec)).
      specialize (HH ltac:(unfold well_scoped_dl; cbn; split; [|tauto];
        apply a_wf_wwl__conswork; [
          constructor; match goal with H : forall _, _ -> a_wf_exp _ _ |- _ =>
            specialize (H X ltac:(unfold K in *; fsetdec)); inversion H; assumption end
          |apply a_wf_wwl__constvar; [unfold K in *; fsetdec|eauto]])).
      cbn in HH; tauto. }
    pick fresh X for K. destruct (HX X Fr) as [Hbase [Hcont Hchecked]].
    cbn; split; [exact Hbase|exists (typ_all A); split; [|exact Hcont]].
    apply d_chk_inf__inf_tabs with (L := K); intros;
      try solve [eapply HX; eassumption].
    match goal with HH : forall X, X `notin` _ -> s_in X _ |- _ => apply HH; unfold K in *; fsetdec end.
  - simplify_dl_wf. prepare_dl_env Ω.
    assert (HM : a_mono_typ (awl_to_aenv (embed_wl Ω)) (typ_arrow T1 T2))
      by (eapply d_mono_embed; eassumption).
    inversion HM; subst.
    destruct (a_wf_abs_open _ _ T1 ltac:(eassumption)) as [M Hbody].
    pose (K := L `union` M `union` dom (awl_to_aenv (embed_wl Ω))).
    assert (HX : forall x, x `notin` K ->
        eval_wl Ω /\ eval_cs (dwl_to_denv Ω) cs (typ_arrow T1 T2) /\
        d_chk_inf ((x,dbind_typ T1)::dwl_to_denv Ω)
          (open_exp_wrt_exp e (exp_var_f x)) typingmode__chk T2).
    { intros x Hx. assert (HH := H1 x ltac:(unfold K in *; fsetdec)).
      specialize (HH ltac:(unfold well_scoped_dl; cbn; split; [|tauto];
        apply a_wf_wwl__conswork; [
          apply a_wf_work__check; [apply Hbody; unfold K in *; fsetdec |
             eapply a_wf_typ_weak_map; [eapply a_mono_wf; eassumption|simpl; intros; auto]]
          |apply a_wf_wwl__consvar; [unfold K in *; fsetdec|eauto using a_mono_wf|
              eauto using a_mono_wf]])).
      cbn in HH; tauto. }
    pick fresh x for K. destruct (HX x Fr) as [Hbase [Hcont Hchecked]].
    cbn; split; [exact Hbase|exists (typ_arrow T1 T2); split; [|exact Hcont]].
    apply d_chk_inf__inf_abs_mono with (L := K); [assumption|intros y Hy; apply (HX y Hy)].
  - simplify_dl_wf. prepare_dl_env Ω.
    assert (Hmono : a_mono_typ (awl_to_aenv (embed_wl Ω)) T) by (eapply d_mono_embed; eassumption).
    assert (Hb : a_wf_typ (awl_to_aenv (embed_wl Ω)) (open_typ_wrt_typ A T))
      by (eapply a_wf_open_all; eauto using a_mono_wf).
    specialize (IHHR ltac:(solve_dl_wf)). cbn in IHHR |- *. finish_eval.
  - destruct H;
      simplify_dl_wf;
      repeat match goal with H : a_wf_conts _ ?c |- _ =>
        tryif is_var c then fail else (inversion H; subst; clear H) end;
      specialize (IHHR ltac:(solve_dl_wf));
      cbn in IHHR |- *; exact IHHR.
  - destruct H;
      simplify_dl_wf;
      repeat match goal with H : a_wf_contd _ ?c |- _ =>
        tryif is_var c then fail else (inversion H; subst; clear H) end;
      specialize (IHHR ltac:(solve_dl_wf));
      cbn in IHHR |- *; exact IHHR.
Qed.

Lemma closed_work_evaluates : forall w,
  a_wf_work nil w ->
  a_wl_red (aworklist_cons_work aworklist_empty w) ->
  eval_work nil w.
Proof.
  intros w HW HR.
  destruct (projected_from_algorithm _ HR (a_wf_wwl__conswork aworklist_empty w HW a_wf_wwl__empty))
    as [f [HF HD]].
  assert (HE : interp_work f w = w).
  { rewrite <- (interp_work_id w) at 2. apply interp_work_ext. intros X _.
    apply HF. simpl. unfold binds; auto. }
  simpl in HD. rewrite HE in HD.
  assert (WF : well_scoped_dl (dworklist_cons_work dworklist_empty w)).
  { unfold well_scoped_dl; simpl; split; [constructor; auto|destruct w; simpl; tauto]. }
  exact (proj2 (declarative_reduction_evaluates _ HD WF)).
Qed.

Theorem a_wl_red_chk_soundness: forall e A,
  nil ᵉ⊢ᵃ e ->
  nil ᵗ⊢ᵃ A ->
  (work_check e A ⫤ᵃ aworklist_empty) ⟶ᵃʷ⁎⋅ ->
  nil ⊢ e ⇐ A.
Proof.
  intros e A He HA HR.
  exact (closed_work_evaluates (work_check e A) (a_wf_work__check nil _ _ He HA) HR).
Qed.

Theorem a_wl_red_inf_soundness: forall e,
  nil ᵉ⊢ᵃ e ->
  (work_infer e (conts_sub typ_top) ⫤ᵃ aworklist_empty) ⟶ᵃʷ⁎⋅ ->
  exists A, nil ⊢ e ⇒ A.
Proof.
  intros e He HR.
  assert (HW : a_wf_work nil (work_infer e (conts_sub typ_top))) by eauto.
  destruct (closed_work_evaluates _ HW HR) as [A [HT HS]].
  exists A; exact HT.
Qed.

(* Read declarative derivations as successful declarative worklists. *)
Lemma decl_types_to_work : forall E A B,
  d_sub E A B -> forall D,
  dwl_to_denv D = E -> d_wl_red D ->
  d_wl_red (dworklist_cons_work D (work_sub A B)).
Proof.
  intros E A B H; induction H; intros D HD HR; eauto 5 with decl_reduce.
  - apply d_wl_red__sub_all with (L := L); intros.
    eapply H2; [eassumption|simpl; now rewrite HD|].
    apply d_wl_red__gc_stvar; assumption.
  - eapply d_wl_red__sub_alll with (T := T); [now rewrite HD|now rewrite HD|].
    eapply IHd_sub; eauto.
Qed.

Lemma decl_apply_typ_to_work : forall E A B C,
  d_inftapp E A B C -> forall D cs,
  d_wl_red (dworklist_cons_work D (work_applys cs C)) ->
  d_wl_red (dworklist_cons_work D (work_inftapp A B cs)).
Proof.
  intros E A B C H; induction H; intros D cs HR; eauto 4 with decl_reduce.
  apply d_wl_red__inftapp_union, IHd_inftapp1.
  apply d_wl_red__applys with (w := work_inftappunion C1 A2 B cs); [constructor|].
  apply d_wl_red__inftappunion, IHd_inftapp2.
  apply d_wl_red__applys with (w := work_unioninftapp C1 C2 cs); [constructor|].
  apply d_wl_red__unioninftapp; assumption.
Qed.

Lemma decl_apply_arrow_to_work : forall E A B C,
  d_infabs E A B C -> forall D cd,
  dwl_to_denv D = E -> d_wl_red (dworklist_cons_work D (work_applyd cd B C)) ->
  d_wl_red (dworklist_cons_work D (work_infabs A cd)).
Proof.
  intros E A B C H; induction H; intros D cd HD HR; eauto 4 with decl_reduce.
  - eapply d_wl_red__infabs_all with (T := T); [now rewrite HD|]. eauto.
  - apply d_wl_red__infabs_union, IHd_infabs1; [exact HD|].
    apply d_wl_red__applyd with (w := work_infabsunion B1 C1 A2 cd); [constructor|].
    apply d_wl_red__infabsunion, IHd_infabs2; [exact HD|].
    apply d_wl_red__applyd with (w := work_unioninfabs B1 C1 B2 C2 cd); [constructor|].
    apply d_wl_red__unioninfabs; assumption.
Qed.

Definition decl_task (D : dworklist) (e : exp) (m : typing_mode) (A : typ) :=
  match m with
  | typingmode__chk => d_wl_red D -> d_wl_red (dworklist_cons_work D (work_check e A))
  | typingmode__inf => forall cs,
    d_wl_red (dworklist_cons_work D (work_applys cs A)) ->
    d_wl_red (dworklist_cons_work D (work_infer e cs))
  end.

Lemma decl_typing_to_work : forall E e m A,
  d_chk_inf E e m A -> forall D, dwl_to_denv D = E -> decl_task D e m A.
Proof.
  intros E e m A H; induction H; intros D HE; cbn in *.
  - intros cs HR. eapply d_wl_red__inf_var with (A := A); [now rewrite HE|eassumption].
  - intros cs HR. apply d_wl_red__inf_anno, IHd_chk_inf; eauto.
  - auto with decl_reduce.
  - intros cs HR. apply d_wl_red__inf_app, IHd_chk_inf1; [exact HE|].
    apply d_wl_red__applys with (w := work_infabs A (contd_infapp e2 cs)); [constructor|].
    eapply decl_apply_arrow_to_work; [eassumption|exact HE|].
    apply d_wl_red__applyd with (w := work_infapp B C e2 cs); [constructor|].
    apply d_wl_red__infapp, IHd_chk_inf2; auto.
  - intros cs HR. eapply d_wl_red__inf_abs_mono with (T1 := A) (T2 := B) (L := L).
    + now rewrite HE.
    + intros; eapply H1; [eassumption|simpl; now rewrite HE|].
      apply d_wl_red__gc_var; assumption.
  - intros cs HR. apply d_wl_red__inf_tabs with (L := L); intros.
    eapply H1; [eassumption|simpl; now rewrite HE|].
    apply d_wl_red__gc_tvar; assumption.
  - intros cs HR. apply d_wl_red__inf_tapp, IHd_chk_inf; [exact HE|].
    apply d_wl_red__applys with (w := work_inftapp A B cs); [constructor|].
    eapply decl_apply_typ_to_work; eassumption.
  - intros HR. apply d_wl_red__chk_abstop with (L := L); intros.
    eapply H0; [eassumption|simpl; now rewrite HE|].
    apply d_wl_red__gc_var; assumption.
  - intros HR. apply d_wl_red__chk_absarrow with (L := L); intros.
    eapply H1; [eassumption|simpl; now rewrite HE|].
    apply d_wl_red__gc_var; assumption.
  - intros HR. apply d_wl_red__chk_sub, IHd_chk_inf; [exact HE|].
    apply d_wl_red__applys with (w := work_sub B A); [constructor|].
    eapply decl_types_to_work; eassumption.
  - intros HR. apply d_wl_red__chk_inter, IHd_chk_inf2; [exact HE|].
    apply IHd_chk_inf1; eauto.
  - intros HR. apply d_wl_red__chk_union1, IHd_chk_inf; eauto.
  - intros HR. apply d_wl_red__chk_union2, IHd_chk_inf; eauto.
Qed.

Definition lift_environment (E : denv) : aenv :=
  List.map (fun p => (fst p, embed_binding (snd p))) E.

Lemma lift_binds : forall E X b, binds X b E ->
  binds X (embed_binding b) (lift_environment E).
Proof.
  unfold binds, lift_environment; intros E X b H.
  change (X, embed_binding b) with ((fun p => (fst p, embed_binding (snd p))) (X,b)).
  auto using in_map.
Qed.

Lemma lift_wf_type : forall E A, d_wf_typ E A -> a_wf_typ (lift_environment E) A.
Proof.
  intros E A H; induction H; eauto using a_wf_typ__unit, a_wf_typ__bot,
    a_wf_typ__top, a_wf_typ__arrow, a_wf_typ__union, a_wf_typ__intersection.
  - apply a_wf_typ__tvar; exact (lift_binds _ _ dbind_tvar_empty H).
  - apply a_wf_typ__stvar; exact (lift_binds _ _ dbind_stvar_empty H).
Qed.

Lemma lift_wf_exp : forall E e, d_wf_exp E e -> a_wf_exp (lift_environment E) e.
Proof.
  intros E e H; induction H; eauto using a_wf_exp__unit, a_wf_exp__app,
    a_wf_exp__tapp, a_wf_exp__anno, lift_wf_type.
  - eapply a_wf_exp__var. exact (lift_binds _ _ (dbind_typ A) H).
Qed.

(* In the reverse direction the chosen declarative monotypes tell us
   which existential solutions can move to an earlier scope. *)
Fixpoint regulars_before (X : atom) (G : aworklist) : denv :=
  match G with
  | aworklist_empty => nil
  | aworklist_cons_var G Y abind_etvar_empty =>
      if eq_var X Y then regulars G else regulars_before X G
  | aworklist_cons_var G _ _ | aworklist_cons_work G _ => regulars_before X G
  end.

Lemma regulars_before_here : forall P X,
  regulars_before X (aworklist_cons_var P X abind_etvar_empty) = regulars P.
Proof. simpl; intros; destruct (eq_var X X); congruence. Qed.

Lemma regulars_before_skip : forall G X Y,
  Y <> X ->
  regulars_before X (aworklist_cons_var G Y abind_etvar_empty) = regulars_before X G.
Proof. simpl; intros; destruct (eq_var X Y); congruence. Qed.

Lemma regulars_before_app : forall S P X,
  X `notin` worklist_dom S ->
  regulars_before X (awl_app S P) = regulars_before X P.
Proof.
  unfold worklist_dom; induction S as [|S IH Y b|S IH w]; intros P X HX; simpl in *; auto.
  assert (Ht : X `notin` dom (awl_to_aenv S)) by fsetdec.
  destruct b; cbn; try solve [auto].
  destruct (eq_var X Y); subst; try fsetdec. apply IH; exact Ht.
Qed.

Lemma scoped_at : forall G f X,
  scoped_assignment f G -> binds X abind_etvar_empty (awl_to_aenv G) ->
  d_mono_typ (regulars_before X G) (f X).
Proof.
  induction G as [|G IH Y b|G IH w]; simpl; intros f X HS HB.
  - contradiction.
  - destruct b; simpl in *;
      try solve [apply binds_cons_cases in HB as [[_ E]|HB]; [discriminate|eauto]].
    destruct (eq_var X Y) as [->|Hn]; [tauto|].
    apply binds_cons_cases in HB as [[E _]|HB]; [congruence|].
    apply IH; tauto.
  - auto.
Qed.

Lemma interp_type_variable_image : forall A f X Y,
  X `in` ftvar_in_typ A -> Y `in` ftvar_in_typ (f X) ->
  Y `in` ftvar_in_typ (interp_typ f A).
Proof.
  induction A; intros f Z Y HF HY; cbn in *; try solve [fsetdec | auto].
  all: try solve [assert (Z = X) by fsetdec; subst; assumption | eapply IHA; eassumption].
  all: apply AtomSetImpl.union_1 in HF as [HF|HF];
    [apply AtomSetImpl.union_2|apply AtomSetImpl.union_3]; eauto.
Qed.

Lemma interp_type_mono_image : forall A E f X,
  X `in` ftvar_in_typ A -> d_mono_typ E (interp_typ f A) ->
  d_mono_typ E (f X).
Proof.
  induction A; intros E f Y HF HM; simpl in *;
    try solve [fsetdec | discriminate].
  - assert (Y = X) by fsetdec. subst; assumption.
  - inversion HM; subst. apply AtomSetImpl.union_1 in HF as [HF|HF]; eauto.
  - inversion HM.
  - inversion HM.
  - inversion HM.
Qed.

Lemma interp_occurs_size : forall A f X,
  X `in` ftvar_in_typ A -> size_typ (f X) <= size_typ (interp_typ f A).
Proof.
  induction A; intros f Y HF; cbn in *; try solve [fsetdec].
  all: try solve [assert (Y = X) by fsetdec; now subst].
  - apply AtomSetImpl.union_1 in HF as [HF|HF]; [apply (IHA1 f) in HF | apply (IHA2 f) in HF]; lia.
  - apply (IHA f) in HF; lia.
  - apply AtomSetImpl.union_1 in HF as [HF|HF]; [apply (IHA1 f) in HF | apply (IHA2 f) in HF]; lia.
  - apply AtomSetImpl.union_1 in HF as [HF|HF]; [apply (IHA1 f) in HF | apply (IHA2 f) in HF]; lia.
Qed.

Lemma interp_occurs_check : forall A f X,
  f X = interp_typ f A -> A <> typ_var_f X -> X `notin` ftvar_in_typ A.
Proof.
  destruct A; simpl; intros f Y HE Hneq HY; try solve [fsetdec].
  all: try solve [assert (Y = X) by fsetdec; now subst].
  - apply AtomSetImpl.union_1 in HY as [HY|HY];
      apply (interp_occurs_size _ f) in HY; rewrite HE in HY; simpl in HY; lia.
  - apply (interp_occurs_size _ f) in HY; rewrite HE in HY; simpl in HY; lia.
  - apply AtomSetImpl.union_1 in HY as [HY|HY];
      apply (interp_occurs_size _ f) in HY; rewrite HE in HY; simpl in HY; lia.
  - apply AtomSetImpl.union_1 in HY as [HY|HY];
      apply (interp_occurs_size _ f) in HY; rewrite HE in HY; simpl in HY; lia.
Qed.

Lemma aws_normalize_assignment : forall G X B P S,
  aworklist_subst G X B P S ->
  forall f, a_wf_wwl G -> scoped_assignment f G ->
  d_mono_typ (regulars_before X G) (interp_typ f B) ->
  scoped_assignment f (awl_app S (aworklist_cons_var P X abind_etvar_empty)).
Proof.
  intros G X B P S HS; induction HS; intros f HW HV HM; simpl.
  - exact HV.
  - apply IHHS; try assumption; inversion HW; assumption.
  - apply IHHS; try assumption; inversion HW; assumption.
  - apply IHHS; try assumption; inversion HW; assumption.
  - apply IHHS; try assumption; inversion HW; assumption.
  - destruct HV as [HV HM0]. rewrite regulars_before_skip in HM by assumption.
    split.
    + rewrite regulars_app. simpl. rewrite <- (aws_regulars _ _ _ _ _ HS). exact HV.
    + apply IHHS.
      * inversion HW; assumption.
      * exact HM0.
      * exact HM.
  - destruct HV as [_ HV]. rewrite regulars_before_skip in HM by assumption.
    inversion HW; subst.
    assert (Hmid : a_wf_wwl (awl_app Γ2 (aworklist_cons_var Γ1 X abind_etvar_empty))) by assumption.
    destruct (awl_subst_suffix_fresh _ _ _ Hmid) as [HXS HXP].
    rewrite regulars_before_app, regulars_before_here in HM by assumption.
    apply IHHS.
    + change (a_wf_wwl (awl_app Γ2 (awl_app (aworklist_cons_var aworklist_empty X abind_etvar_empty)
          (aworklist_cons_var Γ1 Y abind_etvar_empty)))).
      rewrite <- awl_app_assoc; apply awl_wf_insert_etvar; rewrite awl_app_assoc; assumption.
    + assert (HQ := scoped_prefix _ _ _ HV).
      assert (HF : d_mono_typ (regulars Γ1) (f Y)).
      { eapply interp_type_mono_image; eassumption. }
      assert (Hiff : scoped_assignment f (aworklist_cons_var Γ1 X abind_etvar_empty) <->
        scoped_assignment f (aworklist_cons_var (aworklist_cons_var Γ1 Y abind_etvar_empty) X abind_etvar_empty)).
      { simpl in *; tauto. }
      exact (proj1 (scoped_app Γ2 (aworklist_cons_var Γ1 X abind_etvar_empty)
        (aworklist_cons_var (aworklist_cons_var Γ1 Y abind_etvar_empty) X abind_etvar_empty)
        f f eq_refl (fun _ _ => eq_refl) Hiff) HV).
    + rewrite regulars_before_app, regulars_before_here by assumption. exact HM.
Qed.

Lemma valid_extend_etvar : forall G f X T,
  valid_assignment f G -> X `notin` worklist_dom G ->
  d_mono_typ (regulars G) T ->
  valid_assignment (assign f X T) (aworklist_cons_var G X abind_etvar_empty).
Proof.
  intros G f X T HV HX HT. split.
  - simpl. rewrite interp_assign_self. split; [assumption|].
    assert (HA : forall Y, binds Y abind_etvar_empty (awl_to_aenv G) -> f Y = assign f X T Y).
    { intros Y HY. symmetry; apply interp_assign_other.
      intro; subst; eapply binds_dom_contradiction; eassumption. }
    apply (proj1 (scoped_same _ _ _ HA)); apply HV.
  - intros Y HY. assert (Hneq : Y <> X).
    { intro; subst; apply HY; simpl; auto. }
    rewrite interp_assign_other by exact Hneq. apply HV.
    intro HF; apply HY; simpl; auto.
Qed.

Lemma valid_extend_agrees : forall G f X T,
  X `notin` worklist_dom G ->
  agrees (worklist_dom G) f (assign f X T).
Proof.
  intros G f X T HX Y HY. symmetry; apply interp_assign_other; intro; subst; contradiction.
Qed.

Lemma mono_regulars_denv : forall E A,
  d_mono_typ E A ->
  forall G f, interp_env f G = E ->
  d_mono_typ (regulars G) A.
Proof.
  intros E A H; induction H; intros G f HQ; subst; eauto.
  assert (HB : forall G f X, binds X dbind_tvar_empty (interp_env f G) ->
      binds X dbind_tvar_empty (regulars G)).
  { intros G0; induction G0 as [|G0 IH y b|G0 IH w]; intros g Y Hy; simpl in *.
    - exact Hy.
    - destruct b; simpl in *; try solve [apply (IH g); exact Hy].
      all: apply binds_cons_cases in Hy as [[-> HH]|Hy]; try discriminate.
      all: try solve [apply binds_cons_head | apply (IH g); exact Hy |
                       apply binds_cons_weak; apply (IH g); exact Hy].
    - apply (IH g); exact Hy. }
  apply d_mono_typ__tvar; exact (HB G f _ H).
Qed.

Lemma assignment_regulars_before : forall G f X,
  valid_assignment f G -> binds X abind_etvar_empty (awl_to_aenv G) ->
  d_mono_typ (regulars_before X G) (f X).
Proof. intros; apply scoped_at; [apply H|assumption]. Qed.

Lemma forward_aws_exists : forall G f X B,
  a_wf_wwl G -> valid_assignment f G ->
  binds X abind_etvar_empty (awl_to_aenv G) ->
  interp_typ f B = f X ->
  exists P S, aworklist_subst G X B P S.
Proof.
  intros G f X B HW HV HX HE.
  pose proof (assignment_regulars_before _ _ _ HV HX) as HM.
  destruct (awl_split_at _ _ HX) as [P [S Hs]]. subst G.
  destruct (awl_subst_suffix_fresh _ _ _ HW) as [Hsf Hpf].
  rewrite regulars_before_app, regulars_before_here in HM by assumption.
  apply aws_exists_suffix; [assumption|].
  unfold avoids_regulars; intros Y HY Hfv.
  assert (HS : forall b, binds Y b (awl_to_aenv S) ->
      binds Y b (awl_to_aenv (awl_app S (aworklist_cons_var P X abind_etvar_empty)))).
  { intros; rewrite awl_to_aenv_app; unfold binds; apply in_or_app; auto. }
  assert (Hint : f Y = typ_var_f Y).
  { destruct HY as [HY|HY]; apply HS in HY.
    all: eapply valid_tvar; [eapply awl_unique; eassumption|exact HV|eassumption|discriminate]. }
  assert (HY' : Y `in` ftvar_in_typ (interp_typ f B)).
  { apply (interp_type_variable_image B f Y); [exact Hfv|rewrite Hint; cbn; fsetdec]. }
  rewrite HE in HY'.
  pose proof (d_wf_typ_scope _ _ (d_mono_wf _ _ HM) _ HY') as Hscope.
  apply regulars_dom in Hscope.
  apply awl_unique in HW. rewrite awl_to_aenv_app in HW.
  destruct HY as [Hb|Hb];
    apply (fresh_app_r _ _ _ _ _ HW Hb); simpl;
    unfold worklist_dom in *; fsetdec.
Qed.

Lemma aws_assignment_after : forall G f X B P S,
  aworklist_subst G X B P S ->
  a_wf_wwl G -> valid_assignment f G ->
  a_mono_typ (awl_to_aenv G) B ->
  X `notin` ftvar_in_typ B ->
  interp_typ f B = f X ->
  let T := awl_app (subst_typ_in_aworklist B X S) P in
  let g := assign f X (typ_var_f X) in
  valid_assignment g T /\ interp_wl g T = interp_wl f G.
Proof.
  intros G f X B P S HS HW HV HB Hneg HE T g.
  pose proof (aws_source_reordered _ _ _ _ _ HS HW) as Hnormalized.
  destruct (awl_subst_suffix_fresh _ _ _ Hnormalized) as [HXS HXP].
  assert (HX : binds X abind_etvar_empty (awl_to_aenv G)).
  { apply (aws_binds _ _ _ _ _ _ _ HS). unfold binds; apply in_or_app; right; left; reflexivity. }
  assert (Hsc : scoped_assignment f (awl_app S (aworklist_cons_var P X abind_etvar_empty))).
  { eapply aws_normalize_assignment; [eassumption|eassumption|apply HV|].
    rewrite HE; eapply assignment_regulars_before; eassumption. }
  assert (Hagree : forall Y, Y <> X -> g Y = f Y) by (unfold g; auto using interp_assign_other).
  assert (Hstay : forall Y, binds Y abind_etvar_empty (awl_to_aenv S) -> g Y = f Y).
  { intros Y H; apply Hagree; intro; subst; eapply binds_dom_contradiction; eassumption. }
  assert (HP : scoped_assignment f P).
  { apply scoped_prefix in Hsc. simpl in Hsc; tauto. }
  assert (Hequiv : scoped_assignment g P <-> scoped_assignment f (aworklist_cons_var P X abind_etvar_empty)).
  { simpl.
    assert (HT : scoped_assignment g P <-> scoped_assignment f P).
    { apply scoped_same; intros Y H; apply Hagree; intro; subst; eapply binds_dom_contradiction; eassumption. }
    rewrite HT.
    assert (HM := scoped_prefix S _ f Hsc); simpl in HM; tauto. }
  split.
  - split.
    + unfold T.
      apply (proj2 (scoped_subst S P (aworklist_cons_var P X abind_etvar_empty) X B g f
          eq_refl Hstay Hequiv)). exact Hsc.
    + intros Y HY. destruct (eq_var Y X) as [->|Hne].
      * apply interp_assign_self.
      * rewrite Hagree by assumption. apply HV. rewrite <- (aws_target_binds _ _ _ _ _ Y HS Hne); exact HY.
  - unfold T. apply (aws_interp_target _ _ _ _ _ _ _ HS HW); auto.
    unfold g. rewrite interp_assign_fresh_typ by assumption. exact HE.
Qed.

(* Splitting an interpreted arrow into two existential components
   removes one type constructor from this sum. *)
Fixpoint assignment_weight (f : assignment) (G : aworklist) : nat :=
  match G with
  | aworklist_empty => 0
  | aworklist_cons_var G X abind_etvar_empty => size_typ (f X) + assignment_weight f G
  | aworklist_cons_var G _ _ | aworklist_cons_work G _ => assignment_weight f G
  end.

Lemma weight_app : forall S P f,
  assignment_weight f (awl_app S P) = assignment_weight f S + assignment_weight f P.
Proof.
  induction S as [|S IH x b|S IH w]; intros P f.
  - reflexivity.
  - destruct b; cbn; rewrite (IH P f); lia.
  - apply IH.
Qed.

Lemma weight_subst : forall S B X f,
  assignment_weight f (subst_typ_in_aworklist B X S) = assignment_weight f S.
Proof. induction S; intros; simpl; try destruct ab; simpl; rewrite ?IHS; reflexivity. Qed.

Lemma aws_weight : forall G X B P S,
  aworklist_subst G X B P S -> forall f,
  assignment_weight f G = size_typ (f X) + assignment_weight f (awl_app S P).
Proof.
  intros G X B P S H; induction H; intros f; simpl;
    try solve [reflexivity | rewrite IHaworklist_subst; lia | apply IHaworklist_subst].
  specialize (IHaworklist_subst f). rewrite weight_app in *. simpl in *. lia.
Qed.

Lemma weight_agrees : forall G f g,
  (forall X, binds X abind_etvar_empty (awl_to_aenv G) -> f X = g X) ->
  assignment_weight f G = assignment_weight g G.
Proof.
  induction G as [|G IH X b|G IH w]; intros f g H; simpl in *.
  - reflexivity.
  - assert (Ha : forall X, binds X abind_etvar_empty (awl_to_aenv G) -> f X = g X) by eauto.
    specialize (IH f g Ha). destruct b; simpl; try exact IH.
    rewrite (H X) by auto. rewrite IH; reflexivity.
  - now apply IH.
Qed.

Lemma aws_weight_after : forall G X B P S f,
  aworklist_subst G X B P S -> a_wf_wwl G ->
  assignment_weight f G =
  size_typ (f X) + assignment_weight (assign f X (typ_var_f X)) (awl_app (subst_typ_in_aworklist B X S) P).
Proof.
  intros G X B P S f H HW.
  rewrite (aws_weight _ _ _ _ _ H), !weight_app, weight_subst.
  f_equal. symmetry.
  pose proof (aws_source_reordered _ _ _ _ _ H HW) as HR.
  destruct (awl_subst_suffix_fresh _ _ _ HR) as [HX HY].
  f_equal; apply weight_agrees; intros Y Hb; apply interp_assign_other; intro; subst;
    eapply binds_dom_contradiction; eassumption.
Qed.

Lemma size_typ_pos : forall A, 0 < size_typ A.
Proof. destruct A; simpl; lia. Qed.

Lemma interp_env_tvar_inverse : forall G f X,
  binds X dbind_tvar_empty (interp_env f G) ->
  binds X abind_tvar_empty (awl_to_aenv G).
Proof.
  induction G as [|G IH y b|G IH w]; intros f X H; simpl in *.
  - exact H.
  - destruct b; simpl in *.
    + apply binds_cons_cases in H as [[-> _]|H]; [auto|apply binds_cons_weak, (IH f); assumption].
    + apply binds_cons_cases in H as [[? E]|H]; [discriminate|apply binds_cons_weak, (IH f); assumption].
    + apply binds_cons_weak, (IH f); assumption.
    + apply binds_cons_cases in H as [[? E]|H]; [discriminate|apply binds_cons_weak, (IH f); assumption].
  - apply (IH f); assumption.
Qed.

Lemma interp_env_var_inverse : forall G f x A,
  binds x (dbind_typ A) (interp_env f G) ->
  exists B, binds x (abind_var_typ B) (awl_to_aenv G) /\ interp_typ f B = A.
Proof.
  induction G as [|G IH y b|G IH w]; intros f x A H; simpl in *.
  - contradiction.
  - assert (HT : binds x (dbind_typ A) (interp_env f G) ->
       exists B, binds x (abind_var_typ B) ((y,b)::awl_to_aenv G) /\ interp_typ f B = A).
    { intros HH; destruct (IH _ _ _ HH) as [B [HB HE]]; eauto. }
    destruct b; simpl in *; try solve [apply HT; exact H].
    all: apply binds_cons_cases in H as [[-> E]|H]; try discriminate; auto.
    injection E as Eq. subst A. eauto.
  - apply IH; exact H.
Qed.

Lemma interp_mono_reflect : forall G f A,
  a_wf_wwl G -> valid_assignment f G -> a_wf_typ (awl_to_aenv G) A ->
  d_mono_typ (interp_env f G) (interp_typ f A) ->
  a_mono_typ (awl_to_aenv G) A.
Proof.
  intros G f A HG HF HA. remember (awl_to_aenv G) as E.
  induction HA; intros HM; subst; simpl in HM;
    try solve [eauto | inversion HM].
  - rewrite (valid_tvar _ f _ _ (awl_unique _ HG) HF H) in HM by discriminate.
    inversion HM; subst.
    assert (HS : binds X abind_tvar_empty (awl_to_aenv G)) by (eapply interp_env_tvar_inverse; eassumption).
    pose proof (binds_unique _ _ _ _ _ HS H (awl_unique _ HG)); discriminate.
  - inversion HM; subst. constructor; auto.
Qed.

Lemma interp_neq_reflect : forall G f A,
  a_wf_wwl G -> valid_assignment f G -> a_wf_typ (awl_to_aenv G) A ->
  d_wneq_all (interp_env f G) (interp_typ f A) ->
  a_wneq_all (awl_to_aenv G) A.
Proof.
  Local Hint Constructors a_wneq_all : core.
  intros G f A HG HF HA. remember (awl_to_aenv G) as E.
  induction HA; intros Hneq; subst; simpl in Hneq;
    try solve [eauto using a_wf_typ_lc | inversion Hneq].
  - rewrite (valid_tvar _ f _ _ (awl_unique _ HG) HF H) in Hneq by discriminate.
    inversion Hneq; subst.
    assert (HS : binds X abind_tvar_empty (awl_to_aenv G)) by (eapply interp_env_tvar_inverse; eassumption).
    pose proof (binds_unique _ _ _ _ _ HS H (awl_unique _ HG)); discriminate.
  - inversion Hneq; subst; eauto using a_wf_typ_lc.
  - inversion Hneq; subst; eauto.
Qed.

Lemma tvar_binds_dec : forall G X,
  sumbool (binds X abind_tvar_empty (awl_to_aenv G))
    (~ binds X abind_tvar_empty (awl_to_aenv G)).
Proof.
  induction G as [|G IHG Y ab|G IHG w]; intros X; simpl.
  - right; unfold binds; auto.
  - destruct (IHG X) as [Hb|Hb]; [left; auto|].
    destruct (eq_var X Y) as [->|Hn]; destruct ab;
      try solve [right; intro H; apply binds_cons_cases in H as [[? ?]|?]; congruence].
    left; auto.
  - apply IHG.
Qed.

Lemma a_mono_dec : forall G A,
  sumbool (a_mono_typ (awl_to_aenv G) A) (~ a_mono_typ (awl_to_aenv G) A).
Proof.
  intros G A; induction A.
  all: try solve [left; constructor | right; inversion 1].
  - destruct (tvar_binds_dec G X), (etvar_binds_dec G X);
      eauto using left, right.
    all: try solve [left; eauto | right; inversion 1; contradiction].
  - destruct IHA1, IHA2; try solve [left; eauto | right; inversion 1; contradiction].
Qed.

Lemma mono_unify_reduces : forall G f X A,
  a_wf_wwl G -> valid_assignment f G ->
  binds X abind_etvar_empty (awl_to_aenv G) ->
  a_mono_typ (awl_to_aenv G) A -> interp_typ f A = f X ->
  A <> typ_var_f X ->
  (forall G' g, a_wf_wwl G' -> valid_assignment g G' ->
     interp_wl g G' = interp_wl f G -> a_wl_red G') ->
  a_wl_red (aworklist_cons_work G (work_sub (typ_var_f X) A)) /\
  a_wl_red (aworklist_cons_work G (work_sub A (typ_var_f X))).
Proof.
  intros G f X A HW HV HB HM HE Hne IH.
  assert (Hnot : X `notin` ftvar_in_typ A) by (apply (interp_occurs_check A f); auto).
  destruct (forward_aws_exists _ _ _ _ HW HV HB HE) as [P [S HS]].
  pose (g := assign f X (typ_var_f X)).
  destruct (aws_assignment_after _ _ _ _ _ _ HS HW HV HM Hnot HE) as [Hv Hi].
  assert (HR : a_wl_red (awl_app (subst_typ_in_aworklist A X S) P)).
  { exact (IH _ g (aws_target_wf _ _ _ _ _ HS HW HM Hnot) Hv Hi). }
  split.
  - eapply a_wl_red__sub_etvarmono2; eassumption.
  - eapply a_wl_red__sub_etvarmono1; eassumption.
Qed.

Lemma extend_two_etvars : forall G f U V A B,
  a_wf_wwl G -> valid_assignment f G ->
  U `notin` worklist_dom G -> V `notin` worklist_dom G -> V <> U ->
  d_mono_typ (regulars G) A -> d_mono_typ (regulars G) B ->
  let E := aworklist_cons_var (aworklist_cons_var G U abind_etvar_empty) V abind_etvar_empty in
  let g := assign (assign f U A) V B in
  valid_assignment g E /\ agrees (worklist_dom G) f g /\
  g U = A /\ g V = B /\
  assignment_weight g E = size_typ A + size_typ B + assignment_weight f G.
Proof.
  intros G f U V A B Hwf HV HU HVi HVU HA HB E g.
  assert (HV' : V `notin` worklist_dom (aworklist_cons_var G U abind_etvar_empty)).
  { unfold worklist_dom. exact (fresh_env_cons _ _ _ _ HVU HVi). }
  assert (Fa : agrees (worklist_dom G) f g).
  { intros X HX. unfold g. rewrite !interp_assign_other;
      [reflexivity|intro; subst; contradiction|intro; subst; contradiction]. }
  assert (Eu : g U = A).
  { unfold g; rewrite interp_assign_other by congruence; apply interp_assign_self. }
  assert (Ev : g V = B) by (unfold g; apply interp_assign_self).
  split.
  - apply valid_extend_etvar; auto using valid_extend_etvar.
  - split; [exact Fa|]. split; [exact Eu|]. split; [exact Ev|].
    unfold E; simpl. rewrite Eu, Ev, <- (weight_agrees G f g).
    + lia.
    + intros; apply Fa; eauto using worklist_bind_dom.
Qed.

Definition double_extension (G : aworklist) (U V : atom) :=
  aworklist_cons_var (aworklist_cons_var G U abind_etvar_empty) V abind_etvar_empty.

Definition double_assignment f U V A B :=
  assign (assign f U A) V B.

Lemma forward_arrow_target : forall G f X U V A B S P R,
  a_wf_wwl G -> valid_assignment f G ->
  binds X abind_etvar_empty (awl_to_aenv G) ->
  f X = typ_arrow A B ->
  U `notin` worklist_dom G -> V `notin` worklist_dom G -> V <> U ->
  let g := double_assignment f U V A B in
  let E := double_extension G U V in
  let D := awl_app S E in
  let T := typ_arrow (typ_var_f U) (typ_var_f V) in
  a_wf_wwl D -> valid_assignment g D -> assignment_weight g S = 0 ->
  aworklist_subst D X T P R ->
  let D' := awl_app (subst_typ_in_aworklist T X R) P in
  exists h, a_wf_wwl D' /\ valid_assignment h D' /\
    interp_wl h D' = interp_wl g D /\ assignment_weight h D' < assignment_weight f G.
Proof.
  intros G f X U V A B S P R HG HF HX HE HU HV Hneq g E D T HD Hg Hzero Hsubst D'.
  assert (HM : d_mono_typ (regulars G) (f X)).
  { eapply scoped_assignment_binds; [apply HF|eassumption]. }
  rewrite HE in HM.
  assert (Hma : d_mono_typ (regulars G) A) by (inversion HM; assumption).
  assert (Hmb : d_mono_typ (regulars G) B) by (inversion HM; assumption).
  destruct (extend_two_etvars G f U V A B HG HF HU HV Hneq Hma Hmb)
    as [Hext [Hagree [Hu [Hv Hw]]]].
  change (g U = A) in Hu; change (g V = B) in Hv.
  change (agrees (worklist_dom G) f g) in Hagree.
  assert (Hdom : X `in` worklist_dom G) by (eauto using worklist_bind_dom).
  assert (Hbind : forall Y, Y `in` ftvar_in_typ T ->
      binds Y abind_etvar_empty (awl_to_aenv D)).
  { intros Y HY. unfold T in HY; simpl in HY.
    assert (HEq : Y = U \/ Y = V) by fsetdec. destruct HEq as [->| ->];
      unfold D, E, double_extension; apply etvar_app_binds; right; simpl; eauto. }
  assert (HT : a_mono_typ (awl_to_aenv D) T).
  { unfold T; constructor; apply a_mono_typ__etvar; apply Hbind; simpl; fsetdec. }
  assert (HN : X `notin` ftvar_in_typ T).
  { unfold T; simpl. clear - Hdom HU HV; fsetdec. }
  assert (Hit : interp_typ g T = g X).
  { unfold T; simpl; rewrite Hu, Hv, <- Hagree by exact Hdom. symmetry; exact HE. }
  destruct (aws_assignment_after _ _ _ _ _ _ Hsubst HD Hg HT HN Hit) as [Hi Hproj].
  exists (assign g X (typ_var_f X)); split; [eapply aws_target_wf; eassumption|].
  split; [exact Hi|split; [exact Hproj|]].
  pose proof (aws_weight_after _ _ _ _ _ g Hsubst HD) as Hk.
  change (assignment_weight g D = size_typ (g X) +
    assignment_weight (assign g X (typ_var_f X)) D') in Hk.
  unfold D in Hk. rewrite weight_app, Hzero in Hk.
  change (assignment_weight g E = size_typ A + size_typ B + assignment_weight f G) in Hw.
  rewrite Hw, <- (Hagree X Hdom), HE in Hk. simpl in Hk. lia.
Qed.

Inductive dl_prefix : dworklist -> dworklist -> Prop :=
  | dl_prefix_same : forall D, dl_prefix D D
  | dl_prefix_var : forall D E x b, dl_prefix D E -> dl_prefix D (dworklist_cons_var E x b)
  | dl_prefix_work : forall D E w, dl_prefix D E -> dl_prefix D (dworklist_cons_work E w).

Local Hint Constructors dl_prefix : decl_prefix.

Lemma decl_reduce_prefix : forall D,
  d_wl_red D -> forall P, dl_prefix P D -> d_wl_red P.
Proof.
  intros D H; induction H; intros P Hp; inversion Hp; subst; try solve [eauto 5 with decl_reduce decl_prefix].
  all: match goal with
  | IH : forall x, x `notin` ?L -> forall Q, dl_prefix Q _ -> d_wl_red Q |- _ =>
    let x := fresh "x" in pick fresh x for L; eapply (IH x); eauto 5 with decl_prefix
  end.
Qed.

Lemma dl_red_eq_mono : forall E D A B,
  d_mono_typ E A -> d_mono_typ E B ->
  d_wl_red (dworklist_cons_work D (work_sub A B)) -> A = B.
Proof.
  intros E D A B HA HB HR.
  assert (H : forall A B E D,
     size_typ A + size_typ B < size_typ A + size_typ B + 1 ->
     d_mono_typ E A -> d_mono_typ E B ->
     d_wl_red (dworklist_cons_work D (work_sub A B)) -> A = B).
  { clear E D A B HA HB HR.
    assert (H' : forall n A B E D, size_typ A + size_typ B < n ->
        d_mono_typ E A -> d_mono_typ E B ->
        d_wl_red (dworklist_cons_work D (work_sub A B)) -> A = B).
    { induction n; intros A B E D Hn HA HB HR; [lia|].
      inversion HR; subst; try reflexivity;
        try solve [inversion HA | inversion HB].
      inversion HA; inversion HB; subst. simpl in Hn. f_equal.
      - symmetry. eapply IHn; [simpl; lia|eassumption|eassumption|].
        eapply decl_reduce_prefix; [eassumption|eauto using dl_prefix_work, dl_prefix_same].
      - eapply IHn; [simpl; lia|eassumption|eassumption|eassumption]. }
    intros; eapply H'; eassumption. }
  eapply H; eauto; lia.
Qed.

Definition realizes (D : dworklist) : Prop :=
  forall G f, a_wf_wwl G -> valid_assignment f G -> interp_wl f G = D -> a_wl_red G.

Lemma strip_one_etvar : forall G f X,
  a_wf_wwl (aworklist_cons_var G X abind_etvar_empty) ->
  valid_assignment f (aworklist_cons_var G X abind_etvar_empty) ->
  exists g, valid_assignment g G /\ interp_wl g G = interp_wl f G /\    assignment_weight g G = assignment_weight f G.
Proof.
  intros G f X HW HV.
  change (a_wf_wwl (awl_app (aworklist_cons_var aworklist_empty X abind_etvar_empty) G)) in HW.
  destruct (valid_prefix_restrict G (aworklist_cons_var aworklist_empty X abind_etvar_empty) f HW HV)
    as [g [HG HA]].
  exists g; split; [exact HG|].
  split; symmetry.
  - apply interp_wl_agree; [inversion HW; assumption|exact HA].
  - apply weight_agrees. intros Y HB. apply HA. eauto using worklist_bind_dom.
Qed.

Local Hint Constructors a_wl_red : algo_reduce.

Local Ltac peel_projection D :=
  let n := fresh "n" in let G := fresh "G" in let f := fresh "f" in
  let Hwf := fresh "Hwf" in let Hval := fresh "Hval" in let Heq := fresh "Heq" in
  let Hn := fresh "Hn" in let IHn := fresh "IHn" in
  let w := fresh "raw_work" in let b := fresh "raw_bind" in let Z := fresh "Z" in
  unfold realizes;
  cut (forall n G f, assignment_weight f G = n ->
        a_wf_wwl G -> valid_assignment f G -> interp_wl f G = D -> a_wl_red G);
  [intros HA G f Hwf Hval Heq; exact (HA _ G f eq_refl Hwf Hval Heq)|];
  intro n; induction n as [n IHn] using lt_wf_ind;
  intros G f Hn Hwf Hval Heq; destruct G as [|G Z b|G w];
  [cbn in Heq; try discriminate; constructor |
   destruct b; cbn in Heq; try discriminate |
   cbn in Heq; try discriminate];
  try solve [
    let g := fresh "g" in let Hg := fresh "Hg" in let Hproj := fresh "Hproj" in
    let Hweight := fresh "Hweight" in
    destruct (strip_one_etvar G f Z Hwf Hval) as [g [Hg [Hproj Hweight]]];
    apply a_wl_red__gc_var; eapply (IHn (assignment_weight g G));
    [cbn in Hn; rewrite Hweight; pose proof (size_typ_pos (f Z)); lia
    |reflexivity | inversion Hwf; assumption |exact Hg|congruence]].

Lemma interp_var_mono_or_same : forall G f X,
  valid_assignment f G ->
  (binds X abind_etvar_empty (awl_to_aenv G) /\ d_mono_typ (regulars G) (f X)) \/
  f X = typ_var_f X.
Proof.
  intros G f X HV. destruct (etvar_binds_dec G X) as [H|H].
  - left; split; auto; eapply scoped_assignment_binds; [apply HV|eassumption].
  - right; apply HV; assumption.
Qed.

Local Ltac exclude_projected_var :=
  match goal with
  | H : ?f ?X = _, HV : valid_assignment ?f ?G |- _ =>
      destruct (interp_var_mono_or_same G f X HV) as [[? HM]|HM];
      [rewrite H in HM; inversion HM |congruence]
  end.

Local Ltac decompose_projected_work :=
  match goal with
  | H : dworklist_cons_work _ (interp_work ?f ?w) = dworklist_cons_work _ _ |- _ =>
    destruct w; cbn in H; try discriminate; inversion H; subst; clear H
  | H : dworklist_cons_work _ ?w = dworklist_cons_work _ _ |- _ =>
    inversion H; subst; clear H
  end.

Local Ltac decompose_projected_types :=
  repeat match goal with
  | H : interp_typ _ ?A = typ_unit |- _ => is_var A; destruct A; cbn in H; try discriminate
  | H : interp_typ _ ?A = typ_top |- _ => is_var A; destruct A; cbn in H; try discriminate
  | H : interp_typ _ ?A = typ_bot |- _ => is_var A; destruct A; cbn in H; try discriminate
  | H : interp_typ _ ?A = typ_arrow _ _ |- _ => is_var A; destruct A; cbn in H; try discriminate; try (injection H as ?; subst; clear H)
  | H : interp_typ _ ?A = typ_all _ |- _ => is_var A; destruct A; cbn in H; try discriminate; try (injection H as ?; subst; clear H)
  | H : interp_typ _ ?A = typ_union _ _ |- _ => is_var A; destruct A; cbn in H; try discriminate; try (injection H as ?; subst; clear H)
  | H : interp_typ _ ?A = typ_intersection _ _ |- _ => is_var A; destruct A; cbn in H; try discriminate; try (injection H as ?; subst; clear H)
  | H : interp_typ _ ?A = typ_var_f _ |- _ => is_var A; destruct A; cbn in H; try discriminate
  end.

Local Ltac decompose_projected_terms :=
  repeat match goal with
  | H : interp_exp _ ?e = exp_unit |- _ => is_var e; destruct e; cbn in H; try discriminate; clear H
  | H : interp_exp _ ?e = exp_var_f _ |- _ => is_var e; destruct e; cbn in H; try discriminate; inversion H; subst; clear H
  | H : interp_exp _ ?e = exp_abs _ |- _ => is_var e; destruct e; cbn in H; try discriminate; inversion H; subst; clear H
  | H : interp_exp _ ?e = exp_app _ _ |- _ => is_var e; destruct e; cbn in H; try discriminate; inversion H; subst; clear H
  | H : interp_exp _ ?e = exp_tabs _ |- _ => is_var e; destruct e; cbn in H; try discriminate; inversion H; subst; clear H
  | H : interp_exp _ ?e = exp_tapp _ _ |- _ => is_var e; destruct e; cbn in H; try discriminate; inversion H; subst; clear H
  | H : interp_exp _ ?e = exp_anno _ _ |- _ => is_var e; destruct e; cbn in H; try discriminate; inversion H; subst; clear H
  end.

Local Ltac apply_realization_prefix f :=
  match goal with
  | IH : forall P, dl_prefix P ?D -> realizes P |- a_wl_red ?G =>
    apply (IH (interp_wl f G) ltac:(eauto 6 with decl_prefix) G f);
    [eauto 6 with awf|cbn; assumption|reflexivity]
  end.

Local Ltac apply_realization_exact f :=
  match goal with
  | IH : forall P, dl_prefix P ?D -> realizes P |- a_wl_red ?G =>
    eapply (IH D (dl_prefix_same _) G f);
    [eauto 6 with awf|cbn; assumption|cbn; reflexivity]
  end.

Local Ltac simple_reverse f :=
  first [
    solve [apply a_wl_red__sub_top; apply_realization_prefix f]
  | solve [apply a_wl_red__sub_bot; apply_realization_prefix f]
  | solve [apply a_wl_red__sub_unit; apply_realization_prefix f]
  | solve [apply a_wl_red__sub_tvar; apply_realization_prefix f]
  | solve [apply a_wl_red__subarrow; apply_realization_exact f]
  | solve [apply a_wl_red__sub_intersection1; apply_realization_exact f]
  | solve [apply a_wl_red__sub_intersection2; apply_realization_exact f]
  | solve [apply a_wl_red__sub_intersection3; apply_realization_exact f]
  | solve [apply a_wl_red__sub_union1; apply_realization_exact f]
  | solve [apply a_wl_red__sub_union2; apply_realization_exact f]
  | solve [apply a_wl_red__sub_union3; apply_realization_exact f]
  | solve [apply a_wl_red__chk_sub; apply_realization_exact f]
  | solve [apply a_wl_red__chk_inter; apply_realization_exact f]
  | solve [apply a_wl_red__chk_union1; apply_realization_exact f]
  | solve [apply a_wl_red__chk_union2; apply_realization_exact f]
  | solve [apply a_wl_red__inf_anno; apply_realization_exact f]
  | solve [apply a_wl_red__inf_unit; apply_realization_exact f]
  | solve [apply a_wl_red__inf_app; apply_realization_exact f]
  | solve [apply a_wl_red__inf_tapp; apply_realization_exact f]
  | solve [apply a_wl_red__infapp; apply_realization_exact f]
  | solve [apply a_wl_red__infabs_arr; apply_realization_exact f]
  | solve [apply a_wl_red__infabs_bot, a_wl_red__infabs_arr; apply_realization_exact f]
  | solve [apply a_wl_red__infabs_inter1; apply_realization_exact f]
  | solve [apply a_wl_red__infabs_inter2; apply_realization_exact f]
  | solve [apply a_wl_red__infabs_union; apply_realization_exact f]
  | solve [apply a_wl_red__infabsunion; apply_realization_exact f]
  | solve [apply a_wl_red__unioninfabs; apply_realization_exact f]
  | solve [apply a_wl_red__inftapp_bot; apply_realization_exact f]
  | solve [apply a_wl_red__inftapp_inter1; apply_realization_exact f]
  | solve [apply a_wl_red__inftapp_inter2; apply_realization_exact f]
  | solve [apply a_wl_red__inftapp_union; apply_realization_exact f]
  | solve [apply a_wl_red__inftappunion; apply_realization_exact f]
  | solve [apply a_wl_red__unioninftapp; apply_realization_exact f]
  ].

Definition applied_cs (s : conts) (A : typ) : work :=
  match s with
  | conts_infabs d => work_infabs A d
  | conts_inftapp B s => work_inftapp A B s
  | conts_inftappunion B C s => work_inftappunion A B C s
  | conts_unioninftapp B s => work_unioninftapp B A s
  | conts_sub B => work_sub A B
  end.

Definition applied_cd (d : contd) (A B : typ) : work :=
  match d with
  | contd_infabsunion C d => work_infabsunion A B C d
  | contd_infapp e s => work_infapp A B e s
  | contd_unioninfabs C D d => work_unioninfabs C D A B d
  end.

Lemma applied_cs_correct : forall s A, apply_conts s A (applied_cs s A).
Proof. destruct s; constructor. Qed.

Lemma applied_cd_correct : forall d A B, apply_contd d A B (applied_cd d A B).
Proof. destruct d; constructor. Qed.

Lemma applied_cs_interp : forall f s A w,
  apply_conts (interp_cs f s) (interp_typ f A) w ->
  interp_work f (applied_cs s A) = w.
Proof. destruct s; simpl; intros; inversion H; reflexivity. Qed.

Lemma applied_cd_interp : forall f d A B w,
  apply_contd (interp_cd f d) (interp_typ f A) (interp_typ f B) w ->
  interp_work f (applied_cd d A B) = w.
Proof. destruct d; simpl; intros; inversion H; reflexivity. Qed.

Lemma applied_cs_scope : forall E s A,
  a_wf_typ E A -> a_wf_conts E s -> a_wf_work E (applied_cs s A).
Proof. intros E s A HA HS; destruct HS; simpl; eauto. Qed.

Lemma applied_cd_scope : forall E d A B,
  a_wf_typ E A -> a_wf_typ E B -> a_wf_contd E d -> a_wf_work E (applied_cd d A B).
Proof. intros E d A B HA HB HD; destruct HD; simpl; eauto. Qed.

Lemma var_type_eq_dec : forall A X,
  sumbool (A = typ_var_f X) (A <> typ_var_f X).
Proof.
  destruct A; intros Y; try solve [right; discriminate].
  destruct (eq_var X Y) as [->|H]; [left; reflexivity|right; congruence].
Qed.

Local Ltac equal_variable_left G f X A :=
  let HW := fresh "Hwf0" in let HV := fresh "HV" in
  let HE := fresh "HE" in let HB := fresh "HB" in let HM := fresh "HM" in
  let Hneq := fresh "Hneq" in
  assert (HW : a_wf_wwl G) by assumption;
  assert (HV : valid_assignment f G) by assumption;
  assert (HE : interp_typ f A = f X) by (cbn; congruence);
  destruct (var_type_eq_dec A X) as [->|Hneq];
  [apply a_wl_red__sub_tvar; apply_realization_prefix f|];
  destruct (interp_var_mono_or_same G f X HV) as [[HB HM]|HB];
  [let Hm := fresh "Hmono" in
   assert (Hm : a_mono_typ (awl_to_aenv G) A)
     by (apply (interp_mono_reflect G f); try assumption;
         rewrite HE; eapply d_mono_weak_map; [exact HM|apply regulars_interp_binds]);
   apply (proj1 (mono_unify_reduces G f X A HW HV HB Hm HE Hneq
                  ltac:(intros G0 g Hw0 Hv0 HE0;
                    match goal with IH : forall P, dl_prefix P _ -> realizes P |- _ =>
                      apply (IH (interp_wl f G) ltac:(eauto 6 with decl_prefix) G0 g); assumption
                    end)))
  |congruence].

Local Ltac equal_variable_right G f X A :=
  let HW := fresh "Hwf0" in let HV := fresh "HV" in
  let HE := fresh "HE" in let HB := fresh "HB" in let HM := fresh "HM" in
  let Hneq := fresh "Hneq" in
  assert (HW : a_wf_wwl G) by assumption;
  assert (HV : valid_assignment f G) by assumption;
  assert (HE : interp_typ f A = f X) by (cbn; congruence);
  destruct (var_type_eq_dec A X) as [->|Hneq];
  [apply a_wl_red__sub_tvar; apply_realization_prefix f|];
  destruct (interp_var_mono_or_same G f X HV) as [[HB HM]|HB];
  [let Hm := fresh "Hmono" in
   assert (Hm : a_mono_typ (awl_to_aenv G) A)
     by (apply (interp_mono_reflect G f); try assumption;
         rewrite HE; eapply d_mono_weak_map; [exact HM|apply regulars_interp_binds]);
   apply (proj2 (mono_unify_reduces G f X A HW HV HB Hm HE Hneq
                  ltac:(intros G0 g Hw0 Hv0 HE0;
                    match goal with IH : forall P, dl_prefix P _ -> realizes P |- _ =>
                      apply (IH (interp_wl f G) ltac:(eauto 6 with decl_prefix) G0 g); assumption
                    end)))
  |congruence].

Lemma equal_variable_sub : forall G f X Y,
  a_wf_wwl G -> valid_assignment f G ->
  a_wf_typ (awl_to_aenv G) (typ_var_f X) -> a_wf_typ (awl_to_aenv G) (typ_var_f Y) ->
  f X = f Y ->
  realizes (interp_wl f G) ->
  a_wl_red (aworklist_cons_work G (work_sub (typ_var_f X) (typ_var_f Y))).
Proof.
  intros G f X Y HG HV HX HY HF IH.
  destruct (eq_var X Y) as [->|Hneq].
  - apply a_wl_red__sub_tvar; exact (IH G f HG HV eq_refl).
  - destruct (etvar_binds_dec G X) as [Hbx|Hbx].
    + assert (HM : a_mono_typ (awl_to_aenv G) (typ_var_f Y)).
      { apply (interp_mono_reflect G f); try assumption.
        change (d_mono_typ (interp_env f G) (f Y)).
        rewrite <- HF. eapply d_mono_weak_map;
          [eapply scoped_assignment_binds; [apply HV|exact Hbx]|apply regulars_interp_binds]. }
      apply (proj1 (mono_unify_reduces G f X (typ_var_f Y) HG HV Hbx HM
                     ltac:(cbn; congruence) ltac:(congruence) IH)).
    + destruct (etvar_binds_dec G Y) as [Hby|Hby].
      * assert (HM : a_mono_typ (awl_to_aenv G) (typ_var_f X)).
        { apply (interp_mono_reflect G f); try assumption.
          change (d_mono_typ (interp_env f G) (f X)).
          rewrite HF. eapply d_mono_weak_map;
            [eapply scoped_assignment_binds; [apply HV|exact Hby]|apply regulars_interp_binds]. }
        apply (proj2 (mono_unify_reduces G f Y (typ_var_f X) HG HV Hby HM
                     ltac:(cbn; congruence) ltac:(congruence) IH)).
      * rewrite (proj2 HV X Hbx), (proj2 HV Y Hby) in HF. congruence.
Qed.

Lemma arrow_image_properties : forall G f X A B,
  valid_assignment f G -> f X = typ_arrow A B ->
  binds X abind_etvar_empty (awl_to_aenv G) /\
  d_mono_typ (regulars G) A /\ d_mono_typ (regulars G) B.
Proof.
  intros G f X A B HV HE.
  destruct (interp_var_mono_or_same G f X HV) as [[HB HM]|HB]; [|congruence].
  rewrite HE in HM; inversion HM; subst; auto.
Qed.

Lemma awl_agree_work : forall w G f g,
  agrees (worklist_dom G) f g -> a_wf_work (awl_to_aenv G) w ->
  interp_work f w = interp_work g w.
Proof.
  intros; apply interp_work_ext; intros X HX; apply H; eapply a_wf_work_scope; eassumption.
Qed.

Lemma reverse_mono_arrow_eq : forall G f A B,
  a_wf_wwl G -> valid_assignment f G ->
  a_mono_typ (awl_to_aenv G) A -> a_mono_typ (awl_to_aenv G) B ->
  d_wl_red (dworklist_cons_work (interp_wl f G) (work_sub (interp_typ f A) (interp_typ f B))) ->
  interp_typ f A = interp_typ f B.
Proof.
  intros. eapply dl_red_eq_mono with (E:=interp_env f G); eauto using d_mono_of_a_mono.
Qed.

Definition oriented_sub (left : bool) (A B : typ) :=
  if left then work_sub A B else work_sub B A.

Lemma realizes_sub_arrow_var : forall G f X A B U V left,
  a_wf_wwl G -> valid_assignment f G ->
  a_wf_typ (awl_to_aenv G) A -> a_wf_typ (awl_to_aenv G) B ->
  f X = typ_arrow U V ->
  let w := oriented_sub left (typ_var_f X) (typ_arrow A B) in
  let D := dworklist_cons_work (interp_wl f G) (interp_work f w) in
  d_wl_red D -> realizes (interp_wl f G) ->
  (forall G0 g, assignment_weight g G0 < assignment_weight f G ->
    a_wf_wwl G0 -> valid_assignment g G0 -> interp_wl g G0 = D -> a_wl_red G0) ->
  a_wl_red (aworklist_cons_work G w).
Proof.
  intros G f X A B U V left HW HV HA HB HE w D Hred Hprev IH.
  destruct (arrow_image_properties G f X U V HV HE) as [HX [HU HV']].
  destruct (a_mono_dec G (typ_arrow A B)) as [HMono|HNotMono].
  - assert (HmX : a_mono_typ (awl_to_aenv G) (typ_var_f X)) by eauto.
    assert (HEq : interp_typ f (typ_arrow A B) = f X).
    { unfold D, w in Hred. destruct left; cbn in Hred.
      - symmetry. eapply (reverse_mono_arrow_eq G f (typ_var_f X) (typ_arrow A B)); eassumption.
      - eapply (reverse_mono_arrow_eq G f (typ_arrow A B) (typ_var_f X)); eassumption. }
    destruct (mono_unify_reduces _ _ _ _ HW HV HX HMono HEq ltac:(discriminate) Hprev) as [HL HR].
    destruct left; assumption.
  - assert (HW0 : a_wf_work (awl_to_aenv G) w).
    { unfold w, oriented_sub; destruct left; eauto. }
    unfold w; destruct left; simpl;
      [apply a_wl_red__sub_arrow1 with (L := worklist_dom G)
      |apply a_wl_red__sub_arrow2 with (L := worklist_dom G)]; try assumption.
    all: intros Y HY Z HZ P R HS;
      assert (HZ' : Z `notin` worklist_dom G) by fsetdec;
      assert (HZY : Z <> Y) by fsetdec;
      destruct (extend_two_etvars G f Y Z U V HW HV HY HZ' HZY HU HV') as [Hval [Hagree [Hyu [Hzv Hweight]]]];
      pose (suffix := aworklist_cons_work aworklist_empty w);
      pose (extended := double_extension G Y Z);
      pose (g := double_assignment f Y Z U V).
    all: assert (HW1 : a_wf_wwl (awl_app suffix extended)) by
      (unfold suffix; cbn; apply a_wf_wwl__conswork;
       [eapply a_wf_work_weak_map; [exact HW0|unfold extended, double_extension; simpl; intros; auto]
       |unfold extended, double_extension; apply two_etvars_wf; assumption]).
    all: change (valid_assignment g (awl_app suffix extended)) in Hval.
    all: destruct (forward_arrow_target G f X Y Z U V suffix P R HW HV HX HE HY HZ' HZY
          HW1 Hval eq_refl HS) as [h [Hwf [Hvh [Hproj Hlt]]]].
    all: apply (IH _ h Hlt Hwf Hvh); rewrite Hproj;
      try reflexivity.
    all: change (agrees (worklist_dom G) f g) in Hagree.
    all: unfold D;
      change (dworklist_cons_work (interp_wl g G) (interp_work g w) =
              dworklist_cons_work (interp_wl f G) (interp_work f w));
      rewrite <- (interp_wl_agree G f g HW Hagree),
              <- (awl_agree_work w G f g Hagree HW0); reflexivity.
Qed.

Lemma agree_all_body : forall G f g A,
  agrees (worklist_dom G) f g -> a_wf_typ (awl_to_aenv G) (typ_all A) ->
  interp_typ f A = interp_typ g A.
Proof.
  intros. pose proof (awl_agree_typ (typ_all A) G f g H H0).
  simpl in H1; congruence.
Qed.

Lemma agree_abs_body : forall G f g e,
  agrees (worklist_dom G) f g -> a_wf_exp (awl_to_aenv G) (exp_abs e) ->
  interp_exp f e = interp_exp g e.
Proof.
  intros. pose proof (awl_agree_exp (exp_abs e) G f g H H0).
  simpl in H1; congruence.
Qed.

Lemma open_abs_in_double_env : forall G e x Y Z,
  a_wf_exp ((x,abind_var_typ typ_bot)::awl_to_aenv G) (open_exp_wrt_exp e (exp_var_f x)) ->
  a_wf_exp ((x,abind_var_typ (typ_var_f Y))::awl_to_aenv (double_extension G Y Z))
          (open_exp_wrt_exp e (exp_var_f x)).
Proof.
  intros G e x Y Z H; eapply a_wf_exp_retype; [exact H| |].
  - simpl. intros U b HB Hneq. apply binds_cons_cases in HB as [[-> ->]|HB].
    + exfalso; eapply Hneq; reflexivity.
    + auto.
  - intros U T HB; simpl in *. apply binds_cons_cases in HB as [[-> _]|HB].
    + exists (typ_var_f Y); auto.
    + exists T; auto.
Qed.

(* Induct on declarative reduction, keeping its prefixes available.
   When a split leaves the projected worklist unchanged, recur on
   the smaller sum of the existential solution sizes. *)
Lemma realize_from_raw : forall D, d_wl_red D ->
  forall P, dl_prefix P D -> realizes P.
Proof.
  intros D H; induction H; intros P HP; inversion HP; subst;
    try solve [
      match goal with
      | IH : forall P, dl_prefix P _ -> realizes P,
        H : dl_prefix ?P _ |- realizes ?P =>
          eapply IH; eauto 6 with decl_prefix
      end].
  all: try solve [
    match goal with
    | IH : forall x, x `notin` ?L -> forall P, dl_prefix P _ -> realizes P,
      H : dl_prefix ?P _ |- realizes ?P =>
        let x := fresh "x" in pick fresh x for L; eapply (IH x);
        eauto 6 with decl_prefix
    end].
  all: match goal with |- realizes ?D => peel_projection D end.
  all: try solve [
    match goal with
    | Heq : dworklist_cons_var _ _ _ = dworklist_cons_var _ _ _ |- _ =>
      inversion Heq; subst
    end;
    match goal with |- a_wl_red (aworklist_cons_var ?G ?Z ?b) =>
      apply (proj1 (valid_nonetvar f G Z b ltac:(discriminate))) in Hval;
      apply a_wl_red__gc_var;
      inversion Hwf; subst;
      apply_realization_prefix f
    end].
  all: try decompose_projected_work.
  all: repeat match goal with H : @eq typ _ _ |- _ => progress cbn in H end.
  all: decompose_projected_terms; decompose_projected_types.
  all: repeat match goal with H : @eq typ _ _ |- _ => progress cbn in H end.
  all: decompose_projected_types.
  all: repeat match goal with
       | H1 : ?f ?X = typ_var_f ?Y, H2 : interp_typ ?f _ = ?f ?X |- _ => rewrite H1 in H2
       end.
  all: decompose_projected_types.
  all: try solve [exclude_projected_var].
  all: invert_work_wf.
  all: try solve [simple_reverse f].
  all: try solve [
    match goal with
    | H : apply_conts (interp_cs ?f ?cs) (interp_typ ?f ?A) ?w,
      IH : forall P, dl_prefix P ?D -> realizes P |- a_wl_red (aworklist_cons_work ?G (work_applys _ _)) =>
      apply a_wl_red__applys with (w := applied_cs cs A); [apply applied_cs_correct|];
      apply (IH D (dl_prefix_same D) _ f);
      [apply a_wf_wwl__conswork; [apply applied_cs_scope; assumption|assumption]
      |exact Hval
      |cbn; rewrite (applied_cs_interp _ _ _ _ H); reflexivity]
    end].
  all: try solve [
    match goal with
    | H : apply_contd (interp_cd ?f ?cd) (interp_typ ?f ?A) (interp_typ ?f ?B) ?w,
      IH : forall P, dl_prefix P ?D -> realizes P |- a_wl_red (aworklist_cons_work ?G (work_applyd _ _ _)) =>
      apply a_wl_red__applyd with (w := applied_cd cd A B); [apply applied_cd_correct|];
      apply (IH D (dl_prefix_same D) _ f);
      [apply a_wf_wwl__conswork; [apply applied_cd_scope; assumption|assumption]
      |exact Hval
      |cbn; rewrite (applied_cd_interp _ _ _ _ _ H); reflexivity]
    end].
  all: try solve [
    match goal with
    | IH : forall P, dl_prefix P ?D -> realizes P
      |- a_wl_red (aworklist_cons_work ?G (work_sub (typ_var_f ?X) (typ_var_f ?Y))) =>
      apply (equal_variable_sub G f X Y); try assumption; [congruence|];
      apply IH; eauto 6 with decl_prefix
    end].
  all: try solve [
    match goal with |- a_wl_red (aworklist_cons_work ?G (work_sub ?A (typ_var_f ?X))) =>
      equal_variable_right G f X A end].
  all: try solve [
    match goal with |- a_wl_red (aworklist_cons_work ?G (work_sub (typ_var_f ?X) ?A)) =>
      equal_variable_left G f X A end].
  all: try solve [
    match goal with
    | Hb : binds ?x (dbind_typ ?A) (dwl_to_denv (interp_wl ?f ?G)),
      IH : forall P, dl_prefix P ?D -> realizes P
      |- a_wl_red (aworklist_cons_work ?G (work_infer (exp_var_f ?x) ?cs)) =>
      rewrite interp_wl_env in Hb;
      let B := fresh "B" in let HR := fresh "HR" in let HE := fresh "HE" in
      destruct (interp_env_var_inverse _ _ _ _ Hb) as [B [HR HE]];
      eapply a_wl_red__inf_var with (A := B); [exact HR|];
      apply (IH D (dl_prefix_same D) _ f);
      [apply a_wf_wwl__conswork; [constructor; [eapply awl_bind_type_wf; eassumption|assumption]|assumption]
      |exact Hval|cbn; now rewrite HE]
    end].
  all: try solve [
    match goal with
    | IH : forall P, dl_prefix P ?D -> realizes P
      |- a_wl_red (aworklist_cons_work ?G (work_inftapp (typ_all ?A) ?B ?cs)) =>
      apply a_wl_red__inftapp_all;
      apply (IH D (dl_prefix_same D) _ f);
      [apply a_wf_wwl__conswork; [constructor; [apply a_wf_open_all; assumption|assumption]|assumption]
      |exact Hval|cbn; rewrite interp_open_typ by (apply (proj1 (valid_assignment_facts f G Hval))); reflexivity]
    end].
  - assert (HE : f X0 = f X).
    { eapply dl_red_eq_mono with (E := regulars G) (D := interp_wl f G).
      - eapply scoped_assignment_binds; [apply Hval|].
        apply (arrow_image_properties G f X0 A1 A2 Hval H2).
      - eapply scoped_assignment_binds; [apply Hval|].
        apply (arrow_image_properties G f X B1 B2 Hval H3).
      - rewrite H2, H3. apply d_wl_red__sub_arrow; assumption. }
    apply (equal_variable_sub G f X0 X); try assumption. apply IHd_wl_red; eauto with decl_prefix.
  - eapply (realizes_sub_arrow_var G f X A0_1 A0_2 B1 B2 false); try assumption.
    + cbn; rewrite H3; apply d_wl_red__sub_arrow; assumption.
    + apply IHd_wl_red; eauto with decl_prefix.
    + intros G0 g Hlt HW HV HE. apply (IHn _ Hlt G0 g eq_refl); try assumption.
      cbn in HE; now rewrite H3 in HE.
  - eapply (realizes_sub_arrow_var G f X A3_1 A3_2 A1 A2 true); try assumption.
    + cbn; rewrite H2; apply d_wl_red__sub_arrow; assumption.
    + apply IHd_wl_red; eauto with decl_prefix.
    + intros G0 g Hlt HW HV HE. apply (IHn _ Hlt G0 g eq_refl); try assumption.
      cbn in HE; now rewrite H2 in HE.
  - apply a_wl_red__sub_all with (L := L `union` worklist_dom G).
    intros X HX.
    assert (Hfresh : X `notin` worklist_dom G) by fsetdec.
    assert (HXL : X `notin` L) by fsetdec.
    apply (H0 X HXL _ (dl_prefix_same _) _ f).
    + apply a_wf_wwl__conswork.
      * apply a_wf_work__sub; apply a_wf_open_all_extend; eauto.
      * apply a_wf_wwl__consstvar; assumption.
    + cbn [valid_assignment]. apply (proj2 (valid_nonetvar f G X abind_stvar_empty ltac:(discriminate))).
      exact Hval.
    + cbn. rewrite !interp_open_typ by (apply (proj1 (valid_assignment_facts f G Hval))).
      cbn. rewrite (valid_fresh G f X Hval Hfresh); reflexivity.
  - apply a_wl_red__sub_alll with (L := worklist_dom G).
    + apply (interp_neq_reflect G f); try assumption. now rewrite <- interp_wl_env.
    + intros X HX.
      assert (HM : d_mono_typ (regulars G) T).
      { eapply mono_regulars_denv; [exact H0|symmetry; apply interp_wl_env]. }
      pose (g := assign f X T).
      assert (HV : valid_assignment g (aworklist_cons_var G X abind_etvar_empty))
        by (apply valid_extend_etvar; assumption).
      assert (Hagree : agrees (worklist_dom G) f g) by (apply valid_extend_agrees; assumption).
      apply (IHd_wl_red _ (dl_prefix_same _) _ g).
      * apply a_wf_wwl__conswork.
        -- constructor; [apply a_wf_open_all_extend; eauto|].
           eapply a_wf_typ_weak_map; [eassumption|simpl; intros; auto].
        -- constructor; assumption.
      * exact HV.
      * cbn; rewrite interp_open_typ by (apply (proj1 (valid_assignment_facts _ _ HV))).
        cbn. rewrite <- (interp_wl_agree G f g H5 Hagree),
          <- (agree_all_body G f g A1 Hagree H7),
          <- (awl_agree_typ A2 G f g Hagree H8).
        unfold g; rewrite interp_assign_self; reflexivity.
  - destruct (arrow_image_properties G f X A1 A2 Hval H4) as [Hbx [HmA HmB]].
    destruct (a_wf_abs_open _ _ typ_bot H7) as [M Hbody].
    pose (K := worklist_dom G `union` L `union` M).
    apply a_wl_red__chk_absetvar with (L := K); [assumption|].
    intros x Hx Y HY Z HZ P R HS.
    assert (HYg : Y `notin` worklist_dom G) by (clear - HY; unfold K in *; fsetdec).
    assert (HZg : Z `notin` worklist_dom G) by (clear - HZ; unfold K in *; fsetdec).
    assert (Hzy : Z <> Y) by (clear - HZ; fsetdec).
    assert (HxL : x `notin` L) by (clear - Hx; unfold K in *; fsetdec).
    destruct (extend_two_etvars G f Y Z A1 A2 H5 Hval HYg HZg Hzy HmA HmB) as [Hv [Ha [HY' [HZ' Hm]]]].
    pose (g := double_assignment f Y Z A1 A2).
    pose (extended := double_extension G Y Z).
    pose (suffix := aworklist_cons_work
       (aworklist_cons_var aworklist_empty x (abind_var_typ (typ_var_f Y)))
       (work_check (open_exp_wrt_exp e0 (exp_var_f x)) (typ_var_f Z))).
    change (valid_assignment g extended) in Hv.
    change (agrees (worklist_dom G) f g) in Ha.
    change (g Y = A1) in HY'; change (g Z = A2) in HZ'.
    assert (HF : a_wf_wwl (awl_app suffix extended)).
    { unfold suffix; simpl. apply a_wf_wwl__conswork.
      - constructor.
        + unfold extended. eapply open_abs_in_double_env. apply Hbody; clear - Hx; unfold K in *; fsetdec.
        + unfold extended, double_extension; apply a_wf_typ__etvar; simpl; auto.
      - apply a_wf_wwl__consvar.
        + unfold extended, double_extension. apply fresh_two_etvars.
          * clear - HY; fsetdec.
          * clear - HZ; fsetdec.
          * clear - Hx; unfold K in *; fsetdec.
        + unfold extended, double_extension; apply a_wf_typ__etvar; simpl; auto.
        + unfold extended, double_extension; apply two_etvars_wf; assumption. }
    assert (HV : valid_assignment g (awl_app suffix extended)).
    { unfold suffix; cbn [awl_app]. apply valid_work.
      apply (proj2 (valid_nonetvar g extended x (abind_var_typ (typ_var_f Y)) ltac:(discriminate))); exact Hv. }
    destruct (forward_arrow_target G f X Y Z A1 A2 suffix P R H5 Hval Hbx H4 HYg HZg Hzy
          HF HV eq_refl HS) as [h [Hwf [Hvh [Hproj Hlt]]]].
    apply (H0 x HxL _ (dl_prefix_same _) _ h); try assumption.
    rewrite Hproj.
    change (dworklist_cons_work (dworklist_cons_var (interp_wl g G) x (dbind_typ (g Y)))
        (work_check (interp_exp g (open_exp_wrt_exp e0 (exp_var_f x))) (g Z)) =
      dworklist_cons_work (dworklist_cons_var (interp_wl f G) x (dbind_typ A1))
        (work_check (open_exp_wrt_exp (interp_exp f e0) (exp_var_f x)) A2)).
    rewrite interp_open_exp_exp, HY', HZ',
      <- (interp_wl_agree G f g H5 Ha),
      <- (agree_abs_body G f g e0 Ha H7); reflexivity.
  - destruct (a_wf_abs_open _ _ A3 ltac:(eassumption)) as [M HM].
    pose (K := L `union` M `union` worklist_dom G).
    apply a_wl_red__chk_absarrow with (L := K); intros x Hx.
    apply (H0 x ltac:(unfold K in *; fsetdec) _ (dl_prefix_same _) _ f).
    + apply a_wf_wwl__conswork.
      * constructor; [apply HM; unfold K in *; fsetdec|].
        eapply a_wf_typ_weak_map; [eassumption|simpl; intros; auto].
      * constructor; try assumption. clear - Hx; unfold K, worklist_dom in *; fsetdec.
    + apply valid_work.
      apply (proj2 (valid_nonetvar f G x (abind_var_typ A3) ltac:(discriminate))); exact Hval.
    + cbn. rewrite interp_open_exp_exp; reflexivity.
  - destruct (a_wf_abs_open _ _ typ_bot ltac:(eassumption)) as [M HM].
    pose (K := L `union` M `union` worklist_dom G).
    apply a_wl_red__chk_abstop with (L := K); intros x Hx.
    apply (H0 x ltac:(unfold K in *; fsetdec) _ (dl_prefix_same _) _ f).
    + apply a_wf_wwl__conswork.
      * constructor; [apply HM; unfold K in *; fsetdec|constructor].
      * constructor; try assumption; [clear - Hx; unfold K, worklist_dom in *; fsetdec|constructor].
    + apply valid_work.
      apply (proj2 (valid_nonetvar f G x (abind_var_typ typ_bot) ltac:(discriminate))); exact Hval.
    + cbn. rewrite interp_open_exp_exp; reflexivity.
  - inversion H6; subst.
    assert (HA : a_wf_typ (awl_to_aenv G) (typ_all A0)).
    { apply a_wf_typ__all with (L := L0); auto.
      intros X HX. match goal with HB : forall X, X `notin` L0 -> a_wf_exp _ _ |- _ =>
        specialize (HB X HX); inversion HB; assumption end. }
    pose (K := L `union` L0 `union` worklist_dom G).
    apply a_wl_red__inf_tabs with (L := K); intros X HX.
    assert (HXG : X `notin` worklist_dom G) by (clear - HX; unfold K in *; fsetdec).
    pose (base := aworklist_cons_work G (work_applys cs0 (typ_all A0))).
    apply (H0 X ltac:(unfold K in *; fsetdec) _ (dl_prefix_same _) _ f).
    + apply a_wf_wwl__conswork.
      * constructor; match goal with HB : forall X, X `notin` L0 -> a_wf_exp _ _ |- _ =>
          specialize (HB X ltac:(unfold K in *; fsetdec)); inversion HB; assumption end.
      * apply a_wf_wwl__constvar; [exact HXG|constructor; eauto].
    + apply valid_work. change (valid_assignment f (aworklist_cons_var base X abind_tvar_empty)).
      apply (proj2 (valid_nonetvar f base X abind_tvar_empty ltac:(discriminate))); exact Hval.
    + cbn. rewrite interp_open_exp_typ, interp_open_typ by (apply (proj1 (valid_assignment_facts _ _ Hval))).
      cbn; rewrite (valid_fresh G f X Hval HXG); reflexivity.
  - assert (HM : d_mono_typ (regulars G) (typ_arrow T1 T2)).
    { eapply mono_regulars_denv; [exact H|symmetry; apply interp_wl_env]. }
    assert (HmA : d_mono_typ (regulars G) T1) by (inversion HM; assumption).
    assert (HmB : d_mono_typ (regulars G) T2) by (inversion HM; assumption).
    destruct (a_wf_abs_open _ _ typ_bot H7) as [M Hbody].
    pose (K := worklist_dom G `union` L `union` M).
    apply a_wl_red__inf_abs_mono with (L := K).
    intros x Hx Y HY Z HZ.
    assert (HYg : Y `notin` worklist_dom G) by (clear - HY; unfold K in *; fsetdec).
    assert (HZg : Z `notin` worklist_dom G) by (clear - HZ; unfold K in *; fsetdec).
    assert (Hzy : Z <> Y) by (clear - HZ; fsetdec).
    assert (HxL : x `notin` L) by (clear - Hx; unfold K in *; fsetdec).
    destruct (extend_two_etvars G f Y Z T1 T2 H5 Hval HYg HZg Hzy HmA HmB) as [Hv [Ha [HY' [HZ' Hm]]]].
    pose (g := double_assignment f Y Z T1 T2).
    pose (extended := double_extension G Y Z).
    pose (base := aworklist_cons_work extended (work_applys cs0 (typ_arrow (typ_var_f Y) (typ_var_f Z)))).
    change (valid_assignment g extended) in Hv.
    change (agrees (worklist_dom G) f g) in Ha.
    change (g Y = T1) in HY'; change (g Z = T2) in HZ'.
    apply (H1 x HxL _ (dl_prefix_same _) _ g).
    + apply a_wf_wwl__conswork.
      * constructor.
        -- eapply open_abs_in_double_env. apply Hbody; clear - Hx; unfold K in *; fsetdec.
        -- apply a_wf_typ__etvar; simpl; auto.
      * apply a_wf_wwl__consvar.
        -- apply fresh_two_etvars.
           ++ clear - HY; fsetdec.
           ++ clear - HZ; fsetdec.
           ++ clear - Hx; unfold K in *; fsetdec.
        -- apply a_wf_typ__etvar; simpl; auto.
        -- apply a_wf_wwl__conswork.
           ++ constructor.
              ** constructor; apply a_wf_typ__etvar; simpl; auto.
              ** eapply awf_cs_weak; [eassumption|simpl; intros; auto].
           ++ apply two_etvars_wf; assumption.
    + apply valid_work. change (valid_assignment g (aworklist_cons_var base x (abind_var_typ (typ_var_f Y)))).
      apply (proj2 (valid_nonetvar g base x (abind_var_typ (typ_var_f Y)) ltac:(discriminate))); exact Hv.
    + change (dworklist_cons_work
        (dworklist_cons_var (dworklist_cons_work (interp_wl g G)
            (work_applys (interp_cs g cs0) (typ_arrow (g Y) (g Z)))) x (dbind_typ (g Y)))
        (work_check (interp_exp g (open_exp_wrt_exp e0 (exp_var_f x))) (g Z)) =
        dworklist_cons_work
        (dworklist_cons_var (dworklist_cons_work (interp_wl f G)
            (work_applys (interp_cs f cs0) (typ_arrow T1 T2))) x (dbind_typ T1))
        (work_check (open_exp_wrt_exp (interp_exp f e0) (exp_var_f x)) T2)).
      rewrite interp_open_exp_exp, HY', HZ',
        <- (interp_wl_agree G f g H5 Ha), <- (agree_abs_body G f g e0 Ha H7),
        <- (awl_agree_cs cs0 G f g Ha H8); reflexivity.
  - destruct (arrow_image_properties G f X A B Hval H2) as [Hbx [HmA HmB]].
    apply a_wl_red__infabs_etvar with (L := worklist_dom G); [assumption|].
    intros Y HY Z HZ P R HS.
    assert (HZg : Z `notin` worklist_dom G) by (clear - HZ; fsetdec).
    assert (Hzy : Z <> Y) by (clear - HZ; fsetdec).
    destruct (extend_two_etvars G f Y Z A B H4 Hval HY HZg Hzy HmA HmB) as [Hv [Ha [HY' [HZ' Hm]]]].
    pose (g := double_assignment f Y Z A B).
    pose (extended := double_extension G Y Z).
    pose (suffix := aworklist_cons_work aworklist_empty
          (work_infabs (typ_arrow (typ_var_f Y) (typ_var_f Z)) cd0)).
    change (valid_assignment g (awl_app suffix extended)) in Hv.
    change (agrees (worklist_dom G) f g) in Ha.
    change (g Y = A) in HY'; change (g Z = B) in HZ'.
    assert (HF : a_wf_wwl (awl_app suffix extended)).
    { unfold suffix; cbn. apply a_wf_wwl__conswork.
      - constructor.
        + constructor; apply a_wf_typ__etvar; unfold extended, double_extension; simpl; auto.
        + eapply awf_cd_weak; [exact H7|unfold extended, double_extension; simpl; intros; auto].
      - apply two_etvars_wf; assumption. }
    destruct (forward_arrow_target G f X Y Z A B suffix P R H4 Hval Hbx H2 HY HZg Hzy
          HF Hv eq_refl HS) as [h [Hwf [Hvh [Hproj Hlt]]]].
    apply (IHn _ Hlt _ h eq_refl); try assumption.
    rewrite Hproj.
    change (dworklist_cons_work (interp_wl g G) (work_infabs (typ_arrow (g Y) (g Z)) (interp_cd g cd0)) =
            dworklist_cons_work (interp_wl f G) (work_infabs (typ_arrow A B) (interp_cd f cd0))).
    rewrite HY', HZ', <- (interp_wl_agree G f g H4 Ha),
      <- (awl_agree_cd cd0 G f g Ha H7); reflexivity.
  - apply a_wl_red__infabs_all with (L := worklist_dom G).
    intros X HX.
    assert (HM : d_mono_typ (regulars G) T).
    { eapply mono_regulars_denv; [exact H|symmetry; apply interp_wl_env]. }
    pose (g := assign f X T).
    assert (HV : valid_assignment g (aworklist_cons_var G X abind_etvar_empty))
      by (apply valid_extend_etvar; assumption).
    assert (Hagree : agrees (worklist_dom G) f g) by (apply valid_extend_agrees; assumption).
    apply (IHd_wl_red _ (dl_prefix_same _) _ g).
    + apply a_wf_wwl__conswork.
      * constructor.
        -- apply a_wf_open_all_extend; eauto.
        -- eapply awf_cd_weak; [eassumption|simpl; intros; auto].
      * constructor; assumption.
    + exact HV.
    + cbn. rewrite interp_open_typ by (apply (proj1 (valid_assignment_facts _ _ HV))).
      cbn. rewrite <- (interp_wl_agree G f g H4 Hagree),
        <- (agree_all_body G f g A0 Hagree H6),
        <- (awl_agree_cd cd0 G f g Hagree H7).
      unfold g; rewrite interp_assign_self; reflexivity.
Qed.

Lemma closed_work_realizes : forall w,
  a_wf_work nil w ->
  d_wl_red (dworklist_cons_work dworklist_empty w) ->
  a_wl_red (aworklist_cons_work aworklist_empty w).
Proof.
  intros w HW HR.
  apply (realize_from_raw _ HR _ (dl_prefix_same _) _ typ_var_f).
  - constructor; [exact HW|constructor].
  - split; [exact I|reflexivity].
  - cbn. rewrite interp_work_id; reflexivity.
Qed.

Theorem a_wl_red_chk_completeness : forall e A,
  nil ᵉ⊢ᵈ e ->
  nil ᵗ⊢ᵈ A ->
  nil ⊢ e ⇐ A ->
  (work_check e A ⫤ᵃ aworklist_empty) ⟶ᵃʷ⁎⋅.
Proof.
  intros e A He HA HT.
  apply closed_work_realizes.
  - constructor; [exact (lift_wf_exp _ _ He)|exact (lift_wf_type _ _ HA)].
  - exact (decl_typing_to_work nil e typingmode__chk A HT dworklist_empty eq_refl d_wl_red__empty).
Qed.

Theorem a_wl_red_inf_completeness : forall e A,
  nil ᵉ⊢ᵈ e ->
  nil ⊢ e ⇒ A ->
  (work_infer e (conts_sub typ_top) ⫤ᵃ aworklist_empty) ⟶ᵃʷ⁎⋅.
Proof.
  intros e A He HT.
  apply closed_work_realizes.
  - constructor; [exact (lift_wf_exp _ _ He)|constructor; constructor].
  - apply (decl_typing_to_work nil e typingmode__inf A HT dworklist_empty eq_refl (conts_sub typ_top)).
    apply d_wl_red__applys with (w := work_sub A typ_top); [constructor|].
    apply d_wl_red__sub_top, d_wl_red__empty.
Qed.
