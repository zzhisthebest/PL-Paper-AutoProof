Require Export Qual.typing.

Set Implicit Arguments.

Open Scope grade_scope.

Fixpoint erasure (phi : grade) (a:tm)  : tm :=
  match a with
  | a_TyUnit => a_TyUnit
  | a_TmUnit => a_TmUnit
  | (a_Pi psi A B) => a_Pi psi (erasure phi A) (erasure phi B)
  | (a_Abs psi A a) =>
      if q_leb q_Top phi then
        a_Abs psi (erasure phi A) (erasure phi a)
      else
        a_Abs psi a_TmUnit (erasure phi a)
  | (a_App a psi b) =>
      if q_leb psi phi then
        a_App (erasure phi a) psi (erasure phi b)
      else
        a_App (erasure phi a) psi a_TmUnit
  | (a_Type s) => a_Type s
  | (a_Var_b nat) => a_Var_b nat
  | (a_Var_f x) => a_Var_f x
  | (a_Sum A1 A2) => a_Sum (erasure phi A1) (erasure phi A2)
  | (a_Inj1 a) => a_Inj1 (erasure phi a)
  | (a_Inj2 a) => a_Inj2 (erasure phi a)
  | (a_Case psi a b1 b2) => a_Case psi (erasure phi a) (erasure phi b1) (erasure phi b2)
  | (a_WSigma psi A B) => a_WSigma psi (erasure phi A) (erasure phi B)
  | (a_WPair a psi b) =>
      if q_leb psi phi then
        a_WPair (erasure phi a) psi (erasure phi b)
      else
        a_WPair a_TmUnit psi (erasure phi b)
  | (a_LetPair psi a b) => a_LetPair psi (erasure phi a) (erasure phi b)
  | (a_SSigma psi A B) => a_SSigma psi (erasure phi A) (erasure phi B)
  | (a_SPair a psi b) =>
      if q_leb psi phi then
        a_SPair (erasure phi a) psi (erasure phi b)
      else
        a_SPair a_TmUnit psi (erasure phi b)
  | (a_Proj1 psi a) => a_Proj1 psi (erasure phi a)
  | (a_Proj2 psi a) => a_Proj2 psi (erasure phi a)
end.

From Stdlib Require Import Lia.

Local Hint Constructors lc_tm Step CEq GEq : task.

Scheme task_ceq_ind := Induction for CEq Sort Prop
  with task_geq_ind := Induction for GEq Sort Prop.
Combined Scheme task_eq_ind from task_ceq_ind, task_geq_ind.

Scheme task_cgrade_ind := Induction for CGrade Sort Prop
  with task_grade_ind := Induction for Grade Sort Prop.
Combined Scheme task_grading_ind from task_cgrade_ind, task_grade_ind.

(* Track the number of enclosing binders for locally nameless terms. *)
Local Fixpoint task_scoped (k : nat) (a : tm) : Prop :=
  match a with
  | a_Var_b n => (n < k)%nat
  | a_Pi _ A B | a_Abs _ A B | a_WSigma _ A B | a_SSigma _ A B
  | a_LetPair _ A B => task_scoped k A /\ task_scoped (S k) B
  | a_App A _ B | a_WPair A _ B | a_SPair A _ B | a_Sum A B =>
      task_scoped k A /\ task_scoped k B
  | a_Case _ a b c => task_scoped k a /\ task_scoped k b /\ task_scoped k c
  | a_Inj1 a | a_Inj2 a | a_Proj1 _ a | a_Proj2 _ a => task_scoped k a
  | _ => True
  end.

Local Lemma task_scoped_mono : forall a k j,
  (k <= j)%nat -> task_scoped k a -> task_scoped j a.
Proof.
  induction a; simpl; intros k j Hle H;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; eauto with arith.
Qed.

Local Lemma task_scoped_open : forall a k u,
  task_scoped k u ->
  (task_scoped k (open_tm_wrt_tm_rec k u a) <-> task_scoped (S k) a).
Proof.
  induction a; simpl; intros k u Hu;
    assert (Hsu : task_scoped (S k) u) by
      (eapply task_scoped_mono; [| exact Hu]; lia);
    try solve [rewrite ?IHa, ?IHa1, ?IHa2, ?IHa3 by assumption; reflexivity].
  destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt]; simpl.
  - lia.
  - subst; intuition.
  - lia.
Qed.

Local Lemma task_scoped_lc : forall a, lc_tm a -> task_scoped 0 a.
Proof.
  destruct (atom_fresh {}) as [witness _].
  intros a H; induction H; simpl; repeat split; try assumption; try exact I.
  all: apply (proj1 (task_scoped_open _ 0 (a_Var_f witness) I)); eauto.
Qed.

Local Lemma task_lc_body : forall a,
  (forall x, lc_tm (open_tm_wrt_tm a (a_Var_f x))) -> task_scoped 1 a.
Proof.
  intros a Hbody.
  destruct (atom_fresh {}) as [x _].
  apply (proj1 (task_scoped_open a 0 (a_Var_f x) I)).
  apply task_scoped_lc, Hbody.
Qed.

Local Fixpoint task_size (a : tm) : nat :=
  S (match a with
     | a_Pi _ a b | a_Abs _ a b | a_WSigma _ a b | a_SSigma _ a b
     | a_LetPair _ a b | a_App a _ b | a_WPair a _ b | a_SPair a _ b
     | a_Sum a b => task_size a + task_size b
     | a_Case _ a b c => task_size a + task_size b + task_size c
     | a_Inj1 a | a_Inj2 a | a_Proj1 _ a | a_Proj2 _ a => task_size a
     | _ => 0
     end)%nat.

Local Lemma task_size_open_var : forall a k x,
  task_size (open_tm_wrt_tm_rec k (a_Var_f x) a) = task_size a.
Proof.
  induction a; simpl; intros; rewrite ?IHa, ?IHa1, ?IHa2, ?IHa3; try reflexivity.
  destruct (lt_eq_lt_dec n k) as [[] |]; reflexivity.
Qed.

Local Lemma task_lc_scoped : forall a, task_scoped 0 a -> lc_tm a.
Proof.
  assert (H : forall n a, task_size a = n -> task_scoped 0 a -> lc_tm a).
  { induction n using lt_wf_ind; intros a Hsize Hscope; destruct a;
      simpl in Hsize, Hscope; try lia; constructor;
      repeat match goal with H : _ /\ _ |- _ => destruct H end.
    all: try solve [eapply H; [| reflexivity | assumption]; lia].
    all: intros x; unfold open_tm_wrt_tm;
      eapply H; [| reflexivity |]; [rewrite task_size_open_var; lia |];
      apply (proj2 (task_scoped_open _ 0 (a_Var_f x) I)); assumption. }
  eauto.
Qed.

Local Lemma task_lc_open : forall a u,
  task_scoped 1 a -> lc_tm u -> lc_tm (open_tm_wrt_tm a u).
Proof.
  intros a u Ha Hu. apply task_lc_scoped.
  apply (proj2 (task_scoped_open a 0 u (task_scoped_lc Hu))); exact Ha.
Qed.

Local Lemma task_open_inert : forall a k j u,
  (k <= j)%nat -> task_scoped k a -> open_tm_wrt_tm_rec j u a = a.
Proof.
  induction a; simpl; intros k j u Hle Hscope;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try solve [f_equal; eauto with arith].
  destruct (lt_eq_lt_dec n j) as [[] |]; try reflexivity; lia.
Qed.

Local Lemma task_scoped_subst : forall a k u x,
  task_scoped k a -> task_scoped 0 u -> task_scoped k (subst_tm_tm u x a).
Proof.
  induction a; simpl; intros k u y Ha Hu;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; eauto.
  destruct (eq_var x y); simpl; eauto using task_scoped_mono with arith.
Qed.

Local Lemma task_lc_subst : forall a u x,
  lc_tm a -> lc_tm u -> lc_tm (subst_tm_tm u x a).
Proof.
  eauto using task_lc_scoped, task_scoped_subst, task_scoped_lc.
Qed.

Local Lemma task_subst_open : forall a k u v x,
  lc_tm v ->
  subst_tm_tm v x (open_tm_wrt_tm_rec k u a) =
    open_tm_wrt_tm_rec k (subst_tm_tm v x u) (subst_tm_tm v x a).
Proof.
  induction a; simpl; intros k u v y Hv;
    rewrite ?IHa, ?IHa1, ?IHa2, ?IHa3 by assumption; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[] |]; reflexivity.
  - destruct (eq_var x y); simpl; try reflexivity.
    symmetry; eapply task_open_inert with (k := 0); eauto using task_scoped_lc with arith.
Qed.

Local Lemma task_open_as_subst : forall a k u x,
  x \notin fv_tm_tm a ->
  subst_tm_tm u x (open_tm_wrt_tm_rec k (a_Var_f x) a) =
    open_tm_wrt_tm_rec k u a.
Proof.
  induction a; simpl; intros k u y Hfresh;
    try solve [f_equal; eauto; apply IHa || apply IHa1 || apply IHa2 || apply IHa3;
      fsetdec].
  - destruct (lt_eq_lt_dec n k) as [[] |]; simpl; try reflexivity.
    match goal with |- context [if ?d then _ else _] => destruct d end; congruence.
  - match goal with |- context [if ?d then _ else _] => destruct d end;
      subst; [exfalso; fsetdec | reflexivity].
Qed.

Local Lemma task_erasure_open : forall a phi k u,
  erasure phi (open_tm_wrt_tm_rec k u a) =
    open_tm_wrt_tm_rec k (erasure phi u) (erasure phi a).
Proof.
  induction a; simpl; intros phi k u;
    repeat match goal with
    | |- context [if ?test then _ else _] => destruct test; simpl
    end;
    rewrite ?IHa, ?IHa1, ?IHa2, ?IHa3; try reflexivity.
  destruct (lt_eq_lt_dec n k) as [[] |]; reflexivity.
Qed.

Local Lemma task_erasure_lc : forall a phi, lc_tm a -> lc_tm (erasure phi a).
Proof.
  intros a phi H; induction H; simpl;
    repeat match goal with
    | |- context [if ?test then _ else _] => destruct test
    end;
    constructor; auto with task.
  all: intros x; unfold open_tm_wrt_tm in *;
    rewrite <- (task_erasure_open _ phi 0 (a_Var_f x)); auto.
Qed.

Local Lemma task_eq_regular :
  (forall P phi g a b, CEq P phi g a b ->
    uniq P /\ task_scoped 0 a /\ task_scoped 0 b) /\
  (forall P phi a b, GEq P phi a b ->
    uniq P /\ task_scoped 0 a /\ task_scoped 0 b).
Proof.
  apply task_eq_ind; intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    simpl; repeat split; eauto using task_scoped_lc.
  all: match goal with
    | IH : forall x, x \notin ?L -> uniq _ /\ _ |- _ =>
        destruct (atom_fresh L) as [y Hy];
        destruct (IH y Hy) as [Hctx [Ha Hb]];
        inversion Hctx; subst;
        unfold open_tm_wrt_tm in Ha, Hb;
        apply (proj1 (task_scoped_open _ 0 (a_Var_f y) I));
        assumption
    end.
Qed.

Local Lemma task_ceq_closed : forall P phi g a b,
  CEq P phi g a b -> lc_tm a /\ lc_tm b.
Proof.
  intros P phi g a b H.
  destruct (proj1 task_eq_regular _ _ _ _ _ H) as [_ [Ha Hb]].
  split; now apply task_lc_scoped.
Qed.

Local Lemma task_geq_closed : forall P phi a b,
  GEq P phi a b -> lc_tm a /\ lc_tm b.
Proof.
  intros P phi a b H.
  destruct (proj2 task_eq_regular _ _ _ _ H) as [_ [Ha Hb]].
  split; now apply task_lc_scoped.
Qed.

Local Lemma task_ceq_visible : forall P phi g a b,
  CEq P phi g a b -> g <= phi -> GEq P phi a b.
Proof.
  intros P phi g a b Heq Hle. inversion Heq; intuition.
Qed.

Local Lemma task_bottom_le : forall phi, q_Bot <= phi.
Proof.
  intro phi. apply leq_meet. rewrite meet_comm. apply meet_Bot_r.
Qed.

Local Lemma task_step_closed : forall a b, Step a b -> lc_tm b.
Proof.
  intros a b H. induction H; eauto with task.
  - inversion H0; subst. eauto using task_lc_body, task_lc_open.
  - inversion H; subst. eauto with task.
  - inversion H; subst. eauto using task_lc_body, task_lc_open with task.
Qed.

Local Ltac task_eq_binder fresh_set :=
  first [eapply GEq_Pi with (L := fresh_set) | eapply GEq_Abs with (L := fresh_set)
        | eapply GEq_WSigma with (L := fresh_set) | eapply GEq_SSigma with (L := fresh_set)
        | eapply GEq_LetPair with (L := fresh_set)].

Local Lemma task_binds_extend : forall (P Q : econtext) x g,
  (forall y h, binds y h P -> binds y h Q) ->
  forall y h, binds y h (x ~ g ++ P) -> binds y h (x ~ g ++ Q).
Proof.
  intros P Q x g H y h Hb.
  apply binds_cons_iff in Hb. apply binds_cons_iff. intuition.
Qed.

Local Lemma task_eq_weaken :
  (forall P phi g a b, CEq P phi g a b -> forall Q,
    uniq Q -> (forall x h, binds x h P -> binds x h Q) -> CEq Q phi g a b) /\
  (forall P phi a b, GEq P phi a b -> forall Q,
    uniq Q -> (forall x h, binds x h P -> binds x h Q) -> GEq Q phi a b).
Proof.
  apply task_eq_ind; intros; try solve [eauto 5 with task].
  all: let fresh_set := constr:(L \u dom Q) in task_eq_binder fresh_set; try solve [eauto with task].
  all: intros y Hy;
    match goal with
    | IH : forall x, x \notin ?fresh -> forall Q, uniq Q -> _ |- _ =>
        apply IH; [fsetdec | apply uniq_cons; [assumption | fsetdec] |
          apply task_binds_extend; assumption]
    end.
Qed.

(* The prefix Q holds bindings introduced while descending under binders. *)
Local Lemma task_eq_subst :
  (forall P phi g a b, CEq P phi g a b -> forall Q R z h u v,
    P = Q ++ z ~ h ++ R -> uniq (Q ++ R) -> CEq R phi h u v ->
    CEq (Q ++ R) phi g (subst_tm_tm u z a) (subst_tm_tm v z b)) /\
  (forall P phi a b, GEq P phi a b -> forall Q R z h u v,
    P = Q ++ z ~ h ++ R -> uniq (Q ++ R) -> CEq R phi h u v ->
    GEq (Q ++ R) phi (subst_tm_tm u z a) (subst_tm_tm v z b)).
Proof.
  apply task_eq_ind; intros; subst P; simpl;
    try solve [eauto 5 with task].
  { match goal with Harg : CEq _ _ _ _ _ |- _ =>
      destruct (task_ceq_closed Harg)
    end.
    eauto using task_lc_subst with task. }
  { match goal with |- context [if ?d then _ else _] => destruct d as [Heq | Hneq] end.
    + subst x.
      assert (psi0 = h) as ->.
      { eapply binds_unique; try eassumption.
        apply binds_app_iff. right. apply binds_cons_2; reflexivity. }
      eapply (proj2 task_eq_weaken); [eapply task_ceq_visible; eassumption | assumption |].
      intros y j Hb. apply binds_app_iff. now right.
    + eapply GEq_Var; try eassumption.
      match goal with Hb : binds _ _ (Q ++ _ ~ _ ++ R) |- _ =>
        apply binds_app_iff in Hb; destruct Hb as [Hb | Hb];
        [apply binds_app_iff; now left | apply binds_cons_iff in Hb;
         destruct Hb as [[Heq _] | Hb]; [contradiction | apply binds_app_iff; now right]]
      end. }
  all: let fresh_set := constr:(L \u dom (Q ++ R) \u {{z}}) in
    task_eq_binder fresh_set;
    try solve [eauto with task].
  all: intros y Hy; unfold open_tm_wrt_tm in *.
  all: match goal with
    | Harg : CEq _ _ _ ?arg1 ?arg2 |- context[subst_tm_tm ?arg1 _ _] =>
        destruct (task_ceq_closed Harg) as [Hu Hv];
        match goal with
        | IH : forall x, x \notin ?fresh -> forall Q R _ _ _ _, _ |- _ =>
            specialize (IH y ltac:(fsetdec) (y ~ _ ++ Q) R z h u v Logic.eq_refl
              ltac:(apply uniq_cons; [assumption | fsetdec]) Harg);
            rewrite !task_subst_open in IH by assumption;
            cbn [subst_tm_tm] in IH;
            match type of IH with
            | context [if ?d then _ else _] => destruct d as [Heq | Hneq]
            end;
            [exfalso; subst; fsetdec | exact IH]
        end
    end.
Qed.

Local Lemma task_geq_open : forall L P phi g a b u v,
  (forall x, x \notin L ->
    GEq (x ~ g ++ P) phi (open_tm_wrt_tm a (a_Var_f x))
                         (open_tm_wrt_tm b (a_Var_f x))) ->
  CEq P phi g u v ->
  GEq P phi (open_tm_wrt_tm a u) (open_tm_wrt_tm b v).
Proof.
  intros L P phi g a b u v Hbody Harg.
  destruct (atom_fresh (L \u fv_tm_tm a \u fv_tm_tm b)) as [x Hfresh].
  pose proof (Hbody x ltac:(fsetdec)) as Hopened.
  destruct (proj1 task_eq_regular _ _ _ _ _ Harg) as [Huniq _].
  pose proof (proj2 task_eq_subst _ _ _ _ Hopened nil P x g u v
    Logic.eq_refl Huniq Harg) as Hresult.
  unfold open_tm_wrt_tm in *.
  now rewrite !task_open_as_subst in Hresult by fsetdec.
Qed.

Local Ltac task_right_closed :=
  match goal with
  | H : CEq _ _ _ _ ?b |- lc_tm ?b => exact (proj2 (task_ceq_closed H))
  | H : GEq _ _ _ ?b |- lc_tm ?b => exact (proj2 (task_geq_closed H))
  end.

Local Lemma task_geq_step : forall a b, Step a b -> forall P phi a',
  GEq P phi a a' -> exists b', Step a' b' /\ GEq P phi b b'.
Proof.
  intros a b Hstep; induction Hstep; intros P phi t Heq; inversion Heq; subst.
  - edestruct IHHstep as [r [Hred Hrel]]; [eassumption |].
    eexists; split.
    + apply S_AppCong; [task_right_closed | exact Hred].
    + now apply GEq_App.
  - match goal with Habs : GEq _ _ (a_Abs _ _ _) _ |- _ =>
      inversion Habs; subst
    end.
    eexists; split.
    + apply S_Beta; task_right_closed.
    + eapply task_geq_open; eassumption.
  - edestruct IHHstep as [r [Hred Hrel]]; [eassumption |].
    eexists; split.
    + apply S_CaseCong; [task_right_closed | task_right_closed | exact Hred].
    + now apply GEq_Case.
  - match goal with Hinj : GEq _ _ (a_Inj1 _) _ |- _ =>
      inversion Hinj; subst
    end.
    eexists; split.
    + apply S_Case1Beta; task_right_closed.
    + eauto with task.
  - match goal with Hinj : GEq _ _ (a_Inj2 _) _ |- _ =>
      inversion Hinj; subst
    end.
    eexists; split.
    + apply S_Case2Beta; task_right_closed.
    + eauto with task.
  - edestruct IHHstep as [r [Hred Hrel]]; [eassumption |].
    eexists; split.
    + apply S_Proj1Cong; exact Hred.
    + now apply GEq_Proj1.
  - edestruct IHHstep as [r [Hred Hrel]]; [eassumption |].
    eexists; split.
    + apply S_Proj2Cong; exact Hred.
    + now apply GEq_Proj2.
  - match goal with Hpair : GEq _ _ (a_SPair _ _ _) _ |- _ =>
      inversion Hpair; subst
    end.
    eexists; split.
    + apply S_Proj1Beta; task_right_closed.
    + eapply task_ceq_visible; eassumption.
  - match goal with Hpair : GEq _ _ (a_SPair _ _ _) _ |- _ =>
      inversion Hpair; subst
    end.
    eexists; split.
    + apply S_Proj2Beta; task_right_closed.
    + assumption.
  - edestruct IHHstep as [r [Hred Hrel]]; [eassumption |].
    eexists; split.
    + apply S_LetPairCong; [task_right_closed | exact Hred].
    + eapply GEq_LetPair; eassumption.
  - match goal with Hpair : GEq _ _ (a_WPair _ _ _) _ |- _ =>
      inversion Hpair; subst
    end.
    eexists; split.
    + apply S_LetPairBeta; task_right_closed.
    + apply GEq_App.
      * eapply task_geq_open; eassumption.
      * apply CEq_Leq; [apply task_bottom_le | assumption].
Qed.

Theorem CEq_GEq_respects_Step :
  (forall P phi phi0 b1 b1',
  CEq P phi phi0 b1 b1' ->  forall b2, Step b1 b2 ->
       exists b2', (phi0 <= phi -> Step b1' b2') /\ CEq P phi phi0 b2 b2') /\
  (forall P phi b1 b1',
  GEq P phi b1 b1' -> forall b2, Step b1 b2 ->
       exists b2', Step b1' b2' /\ GEq P phi b2 b2').

Proof.
  split.
  - intros P phi phi0 b1 b1' Heq b2 Hstep.
    destruct Heq as [P phi phi0 b1 b1' Hle Heq | P phi phi0 b1 b1' Hl Hr Hnle Hu].
    + destruct (task_geq_step Hstep Heq) as [b2' [Hred Hrel]].
      exists b2'; split; eauto with task.
    + exists b1'; split.
      * intro Hle. contradiction.
      * apply CEq_Nleq; eauto using task_step_closed.
  - intros P phi b1 b1' Heq b2 Hstep. exact (task_geq_step Hstep Heq).
Qed.

Local Lemma task_erasure_component : forall P phi g a,
  CEq P phi g a (erasure phi a) ->
  CEq P phi g a (if q_leb g phi then erasure phi a else a_TmUnit).
Proof.
  intros P phi g a Heq.
  destruct (q_leb g phi) eqn:Htest; [exact Heq |].
  destruct Heq as [P phi g a b Hle _ | P phi g a b Ha Hb Hnle Huniq].
  - apply leb_leq in Hle. congruence.
  - apply CEq_Nleq; eauto with task.
Qed.

Theorem Erasure_Indistinguishability :
  (forall P phi psi a, CGrade P phi psi a -> CEq P phi psi a (erasure phi a)) /\
  (forall P phi a, Grade P phi a -> GEq P phi a (erasure phi a)).
Proof.
  apply task_grading_ind; intros; simpl.
  all: try solve [eauto using task_erasure_lc with task].
  all: try match goal with
    | Hgrade : CGrade ?P ?phi ?g ?a |- context [?g <=? ?phi] =>
        let Harg := fresh "Harg" in
        assert (Harg : CEq P phi g a
          (if q_leb g phi then erasure phi a else a_TmUnit))
          by (apply task_erasure_component; assumption);
        destruct (q_leb g phi)
    end.
  all: try solve [eauto with task].
  all: let fresh_set := constr:(L) in task_eq_binder fresh_set; try assumption.
  all: intros x Hx; unfold open_tm_wrt_tm in *;
    rewrite <- (task_erasure_open _ psi 0 (a_Var_f x)); auto.
Qed.
