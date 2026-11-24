From Stdlib Require Import List Relation_Operators Wellfounded.Transitive_Closure.
From Stdlib Require Import Wellfounded.Lexicographic_Product
  Wellfounded.Inverse_Image Arith.Wf_nat Lia.
Import ListNotations.

Require Import Section3_Requirements.

Require Import Section4_Requirements.

Module Integrated (M_traditional : Traditional) (M_intersector : Intersector M_traditional).

Import M_traditional.

Import M_intersector.

Inductive IPremise {ll lr : Lit} (r : RRule ll lr) : T -> T -> Prop :=
    ipremise (tl tr : T) : RPremise r tl tr -> IPremise r (Integrate intersect tl) tr.

Definition isub' : T -> T -> Prop :=
    rsubf (@IPremise).

Definition isub (tl : T) : T -> Prop :=
    isub' (Integrate intersect tl).

Local Hint Resolve dsubda_refl dsubda_top dsubda_bot dsubda_int_r
  dsubda_int_ll dsubda_int_lr dsubda_uni_l dsubda_uni_rl dsubda_uni_rr
  : extended.

Lemma esub_intersect_app : forall xs ys,
  esub (TIsect (Intersect xs) (Intersect ys)) (Intersect (xs ++ ys)).
Proof.
  induction xs as [|x xs IH]; intros ys; cbn.
  - apply dsubda_int_lr.
  - apply dsubda_int_r.
    + eapply dsubda_trans; [apply dsubda_int_ll|apply dsubda_int_ll].
    + eapply dsubda_trans; [|apply IH].
      apply dsubda_int_r.
      * eapply dsubda_trans; [apply dsubda_int_ll|apply dsubda_int_lr].
      * apply dsubda_int_lr.
Qed.

(* Carry the context a while distributing intersections over unions. *)
Lemma integrate_sound_aux : forall t a f,
  (forall ls, esub (TIsect a (Intersect ls)) (f ls)) ->
  esub (TIsect a t) (Integrate f t).
Proof.
  induction t as [| |l IHl r IHr|l IHl r IHr|x]; intros a f H; cbn.
  - exact (H []).
  - eapply dsubda_trans; [apply dsubda_int_lr|apply dsubda_bot].
  - eapply dsubda_trans; [apply dsubda_dist|].
    apply dsubda_uni_l.
    + eapply dsubda_trans; [apply IHl, H|apply dsubda_uni_rl].
    + eapply dsubda_trans; [apply IHr, H|apply dsubda_uni_rr].
  - eapply dsubda_trans with (tm := TIsect (TIsect a r) l).
    + apply dsubda_int_r.
      * apply dsubda_int_r.
        -- apply dsubda_int_ll.
        -- eapply dsubda_trans; [apply dsubda_int_lr|apply dsubda_int_lr].
      * eapply dsubda_trans; [apply dsubda_int_lr|apply dsubda_int_ll].
    + apply IHl. intro xs.
      eapply dsubda_trans with (tm := TIsect (TIsect a (Intersect xs)) r).
      * apply dsubda_int_r.
        -- apply dsubda_int_r.
           ++ eapply dsubda_trans; [apply dsubda_int_ll|apply dsubda_int_ll].
           ++ apply dsubda_int_lr.
        -- eapply dsubda_trans; [apply dsubda_int_ll|apply dsubda_int_lr].
      * apply IHr. intro ys.
        eapply dsubda_trans; [|apply H].
        apply dsubda_int_r.
        -- eapply dsubda_trans; [apply dsubda_int_ll|apply dsubda_int_ll].
        -- eapply dsubda_trans; [|apply esub_intersect_app].
           apply dsubda_int_r.
           ++ eapply dsubda_trans; [apply dsubda_int_ll|apply dsubda_int_lr].
           ++ apply dsubda_int_lr.
  - eapply dsubda_trans; [|apply (H [x])].
    cbn. apply dsubda_int_r; eauto with extended.
Qed.

Lemma integrate_sound : forall t, esub t (Integrate intersect t).
Proof.
  intro t. eapply dsubda_trans with (tm := TIsect TTop t).
  - eauto with extended.
  - apply integrate_sound_aux. intro ls.
    eapply dsubda_trans; [apply dsubda_int_lr|apply IntersectorSoundness].
Qed.

Lemma dsuba_into_esub : forall (A : T -> T -> Prop) l r,
  (forall x y, A x y -> esub x y) ->
  dsuba (@DPremise) A l r -> esub l r.
Proof.
  intros A l r HA H. induction H;
    eauto using dsubda_trans, dsubda_lit with extended.
Qed.

Lemma rrule_into_esub : forall ll lr (r : RRule ll lr),
  (forall l t, RPremise r l t -> esub l t) -> esub (TLit ll) (TLit lr).
Proof.
  intros ll lr r H.
  eapply dsuba_into_esub; [exact H|apply RRuleToDProof].
Qed.

Local Ltac uisub_esub_step :=
  first [ apply dsubda_top
        | apply dsubda_bot
        | apply dsubda_int_r; assumption
        | apply dsubda_uni_l; assumption
        | eapply dsubda_trans; [apply dsubda_int_ll|assumption]
        | eapply dsubda_trans; [apply dsubda_int_lr|assumption]
        | eapply dsubda_trans; [|apply dsubda_uni_rl]; assumption
        | eapply dsubda_trans; [|apply dsubda_uni_rr]; assumption ].

Lemma rsub_into_esub : forall l r, rsub l r -> esub l r.
Proof.
  fix IH 3. intros l r D; destruct D as [l r H].
  induction H; try uisub_esub_step.
  destruct H as [rule H]. apply (rrule_into_esub _ _ rule).
  intros x y Hp. apply IH, H, Hp.
Qed.

Lemma isub'_into_esub : forall l r, isub' l r -> esub l r.
Proof.
  fix IH 3. intros l r D; destruct D as [l r H].
  induction H; try uisub_esub_step.
  destruct H as [rule H]. apply (rrule_into_esub _ _ rule).
  intros x y Hp. eapply dsubda_trans; [apply integrate_sound|].
  apply IH, H. now constructor.
Qed.

Theorem IntegratedSoundness : forall tl tr : T, isub tl tr -> esub tl tr.
Proof.
  intros tl tr H. eapply dsubda_trans.
  - apply integrate_sound.
  - exact (isub'_into_esub _ _ H).
Qed.

(* The measure decreases at literal premises. Size breaks ties at UI rules. *)
Fixpoint ui_size (t : T) : nat :=
  match t with
  | TUni l r | TIsect l r => S (ui_size l + ui_size r)
  | _ => 1
  end.

Definition measure_lt := clos_trans M mlt.

Lemma measure_lt_wf : well_founded measure_lt.
Proof. exact (wf_clos_trans M mlt mltwf). Qed.

Lemma measure_le_cases : forall x y,
  clos_refl_trans M mlt x y -> x = y \/ measure_lt x y.
Proof.
  intros x y H. induction H as [x y H|x|x y z Hxy IHxy Hyz IHyz].
  - right. now apply t_step.
  - now left.
  - destruct IHxy as [E1|H1], IHyz as [E2|H2]; subst; auto.
    right. eapply t_trans; eassumption.
Qed.

Definition pair_rank (p : T * T) : M * nat :=
  (m (fst p) (snd p), ui_size (fst p) + ui_size (snd p)).

Definition pair_lt (p q : T * T) : Prop :=
  slexprod M nat measure_lt lt (pair_rank p) (pair_rank q).

Lemma pair_lt_wf : well_founded pair_lt.
Proof.
  unfold pair_lt. apply wf_inverse_image, wf_slexprod.
  - exact measure_lt_wf.
  - exact lt_wf.
Qed.

Lemma pair_lt_left : forall l l' r, subui l l' -> pair_lt (l, r) (l', r).
Proof.
  intros l l' r H. destruct (measure_le_cases _ _ (m_ui_l l l' r H)) as [E|Hm].
  - unfold pair_lt, pair_rank; cbn. rewrite E.
    apply right_slex. destruct H; cbn; lia.
  - exact (left_slex _ _ _ _ _ _ _ _ Hm).
Qed.

Lemma pair_lt_right : forall l r r', subui r r' -> pair_lt (l, r) (l, r').
Proof.
  intros l r r' H. destruct (measure_le_cases _ _ (m_ui_r l r r' H)) as [E|Hm].
  - unfold pair_lt, pair_rank; cbn. rewrite E.
    apply right_slex. destruct H; cbn; lia.
  - exact (left_slex _ _ _ _ _ _ _ _ Hm).
Qed.

Lemma pair_lt_premise : forall ll lr (rule : RRule ll lr) x y,
  RPremise rule x y -> pair_lt (Integrate intersect x, y) (TLit ll, TLit lr).
Proof.
  intros ll lr rule x y H. apply left_slex.
  pose proof (t_step _ _ _ _ (m_lit rule x y H)) as Hstrict.
  destruct (measure_le_cases _ _ (MeasurePreservation x y)) as [E|Hm]; cbn.
  - now rewrite E.
  - eapply t_trans; eassumption.
Qed.

Lemma forall_in_dec {A : Type} (P : A -> Prop) : forall ls : list A,
  (forall x, In x ls -> {P x} + {~ P x}) -> {Forall P ls} + {~ Forall P ls}.
Proof.
  induction ls as [|x xs IH]; intro D.
  - left. constructor.
  - destruct (D x (or_introl eq_refl)) as [Hx|Hx].
    + destruct (IH (fun y Hy => D y (or_intror Hy))) as [Hs|Hs].
      * left. now constructor.
      * right. intro H. inversion H; contradiction.
    + right. intro H. inversion H; contradiction.
Defined.

Local Notation IL := (lsub (@IPremise) isub').

Lemma integrated_literal_dec : forall ll lr,
  (forall p, pair_lt p (TLit ll, TLit lr) ->
    {isub' (fst p) (snd p)} + {~ isub' (fst p) (snd p)}) ->
  {IL ll lr} + {~ IL ll lr}.
Proof.
  intros ll lr IH.
  destruct (SyntaxDirectedness_Rules ll lr) as [rules Hrules].
  assert (dec_rule : forall rule : RRule ll lr,
    {forall x y, IPremise rule x y -> isub' x y} +
    {~ (forall x y, IPremise rule x y -> isub' x y)}).
  { intro rule. destruct (SyntaxDirectedness_Premises rule) as [ps Hps].
    destruct (forall_in_dec (fun p => isub' (Integrate intersect (fst p)) (snd p))
      ps) as [Hyes|Hno].
    - intros [x y] Hin. apply (IH (Integrate intersect x, y)).
      eapply pair_lt_premise. now apply Hps.
    - left. intros x y Hp. destruct Hp as [a b Hp].
      apply (proj1 (Forall_forall _ _) Hyes (a, b)). now apply Hps.
    - right. intro H. apply Hno, Forall_forall. intros [x y] Hin.
      apply H, ipremise. now apply Hps. }
  destruct (@Exists_dec _ _ rules dec_rule) as [Hex|Hex].
  - left. apply Exists_exists in Hex. destruct Hex as [rule [_ Hr]].
    now apply (Lsub (@IPremise) isub' ll lr rule).
  - right. intros [rule Hr]. apply Hex, Exists_exists.
    exists rule. auto.
Defined.

Local Hint Resolve ui_lit ui_top ui_bot ui_int_ll ui_int_lr ui_int_r
  ui_uni_rl ui_uni_rr ui_uni_l : ui.

Lemma isub'_ui : forall l r, isub' l r -> uisub IL l r.
Proof. intros l r H. now destruct H. Qed.

Lemma integrated_dec : forall p : T * T,
  {isub' (fst p) (snd p)} + {~ isub' (fst p) (snd p)}.
Proof.
  apply (well_founded_induction_type pair_lt_wf).
  intros [l r] IH. cbn.
  assert (D : {uisub IL l r} + {~ uisub IL l r}).
  { destruct l as [| |a b|a b|x], r as [| |c d|c d|y];
      try solve [left; eauto with ui].
    all: try match goal with
    | |- {_ (TUni ?a ?b) ?r} + {_} =>
        destruct (IH (a, r) (pair_lt_left _ _ _ (sub_uni_l a b))) as [Ha|Ha];
        destruct (IH (b, r) (pair_lt_left _ _ _ (sub_uni_r b a))) as [Hb|Hb]
    | |- {_ (TIsect ?a ?b) ?r} + {_} =>
        destruct (IH (a, r) (pair_lt_left _ _ _ (sub_isect_l a b))) as [Ha|Ha];
        destruct (IH (b, r) (pair_lt_left _ _ _ (sub_isect_r b a))) as [Hb|Hb]
    end; cbn [fst snd] in *; try solve [left; eauto using isub'_ui with ui].
    all: try match goal with
    | |- {_ ?l (TUni ?c ?d)} + {_} =>
        destruct (IH (l, c) (pair_lt_right _ _ _ (sub_uni_l c d))) as [Hc|Hc];
        destruct (IH (l, d) (pair_lt_right _ _ _ (sub_uni_r d c))) as [Hd|Hd]
    | |- {_ ?l (TIsect ?c ?d)} + {_} =>
        destruct (IH (l, c) (pair_lt_right _ _ _ (sub_isect_l c d))) as [Hc|Hc];
        destruct (IH (l, d) (pair_lt_right _ _ _ (sub_isect_r d c))) as [Hd|Hd]
    end; cbn [fst snd] in *; try solve [left; eauto using isub'_ui with ui].
    all: try match goal with
    | |- {_ (TLit ?x) (TLit ?y)} + {_} =>
        destruct (integrated_literal_dec x y IH); [left; now apply ui_lit|]
    end.
    all: right; intro H; inversion H; subst;
      first [ contradiction
            | match goal with
              | Hno : ~ isub' ?a ?b, Hyes : uisub IL ?a ?b |- False =>
                  apply Hno; now constructor
              end ]. }
  destruct D as [H|H].
  - left. now constructor.
  - right. intro H'. exact (H (isub'_ui _ _ H')).
Defined.

Theorem IntegratedDecidability : forall tl tr : T, {isub tl tr} + {~ isub tl tr}.
Proof.
  intros tl tr. exact (integrated_dec (Integrate intersect tl, tr)).
Defined.

(* Interpret literals by rules whose premises hold in extended subtyping. *)
Local Notation EL := (lsub (@RPremise) esub).

Lemma rsubam_into_esub : forall (A : T -> T -> Prop) l r,
  (forall x y, A x y -> esub x y) ->
  rsubam (@RPremise) A l r -> esub l r.
Proof.
  intros A l r HA H. induction H; try uisub_esub_step.
  - now apply HA.
  - apply dsubda_trans with (tm := tl'); [now apply rsub_into_esub|].
    apply dsubda_trans with (tm := tr'); [assumption|now apply rsub_into_esub].
  - eapply rrule_into_esub. exact H0.
Qed.

Lemma extended_literal_refl : forall x, EL x x.
Proof.
  intro x. destruct (LiteralReflexivity x) as [rule Hr].
  apply (Lsub (@RPremise) esub x x rule).
  intros l r Hp. rewrite (Hr _ _ Hp). apply dsubda_refl.
Qed.

Lemma extended_literal_trans : forall x y z, EL x y -> EL y z -> EL x z.
Proof.
  intros x y z [left_rule Hl] [right_rule Hr].
  destruct (LiteralTransitivity left_rule right_rule) as [rule H].
  apply (Lsub (@RPremise) esub x z rule).
  intros l r Hp. destruct (H _ _ Hp) as [mid [[Ha Hb]|[Ha Hb]]].
  all: apply dsubda_trans with (tm := mid);
    (eapply rsubam_into_esub; [|eassumption]); eassumption.
Qed.

(* A valuation is generated by a list of literals in an integrated clause. *)
Fixpoint holds (env : list Lit) (t : T) : Prop :=
  match t with
  | TTop => True
  | TBot => False
  | TUni l r => holds env l \/ holds env r
  | TIsect l r => holds env l /\ holds env r
  | TLit y => exists x, In x env /\ EL x y
  end.

Definition entails (l r : T) : Prop :=
  forall env, intersected env -> holds env l -> holds env r.

Lemma extended_literal_entails : forall x y, EL x y -> entails (TLit x) (TLit y).
Proof.
  intros x y H env _ [a [Hin Ha]]. exists a.
  split; [exact Hin|eapply extended_literal_trans; eassumption].
Qed.

Lemma uisub_entails : forall (L : Lit -> Lit -> Prop) l r,
  (forall x y, L x y -> entails (TLit x) (TLit y)) ->
  uisub L l r -> entails l r.
Proof.
  intros L l r HL H. induction H; try now apply HL.
  all: unfold entails in *; intros env He; cbn; intuition eauto.
Qed.

Lemma rsub_entails : forall l r, rsub l r -> entails l r.
Proof.
  intros l r H. destruct H as [l r H].
  eapply uisub_entails; [|exact H].
  intros x y [rule Hr]. apply extended_literal_entails.
  apply (Lsub (@RPremise) esub x y rule).
  intros a b Hp. apply rsub_into_esub, Hr, Hp.
Qed.

Lemma rsubam_entails : forall (A : T -> T -> Prop) l r,
  (forall x y, A x y -> esub x y) ->
  (forall x y, A x y -> entails x y) ->
  rsubam (@RPremise) A l r -> entails l r.
Proof.
  intros A l r Hsound HA H. induction H;
    try solve [unfold entails in *; intros env He; cbn; intuition eauto 4].
  - intros env He Hval. apply (rsub_entails tr' tr); [assumption|exact He|].
    apply IHrsubam; [exact He|]. apply (rsub_entails tl tl'); assumption.
  - apply extended_literal_entails. apply (Lsub (@RPremise) esub ll lr r).
    intros x y Hp. eapply rsubam_into_esub; eauto.
Qed.

Lemma dsuba_entails : forall (A : T -> T -> Prop) l r,
  (forall x y, A x y -> esub x y) ->
  (forall x y, A x y -> entails x y) ->
  dsuba (@DPremise) A l r -> entails l r.
Proof.
  intros A l r Hsound HA H. induction H;
    try solve [unfold entails in *; intros env He; cbn; intuition eauto 4].
  eapply rsubam_entails; [| |exact (DRuleToRProof r)].
  - intros x y Hp. eapply dsuba_into_esub; eauto.
  - assumption.
Qed.

Lemma holds_app : forall env xs ys,
  holds env (Intersect (xs ++ ys)) <->
  holds env (Intersect xs) /\ holds env (Intersect ys).
Proof.
  intros env xs; induction xs as [|x xs IH]; intros ys; cbn.
  - tauto.
  - rewrite IH. tauto.
Qed.

(* A pure intersection projects each of its literals and has their valuation. *)
Definition clause_of (t : T) (xs : list Lit) : Prop :=
  (forall env, holds env t <-> holds env (Intersect xs)) /\
  (forall x y, In x xs -> EL x y -> uisub EL t (TLit y)).

Lemma integrated_int_clause : forall t (P : list Lit -> Prop),
  Integrated_int P t -> exists xs, P xs /\ clause_of t xs.
Proof.
  induction t as [| |l IHl r IHr|l IHl r IHr|x]; intros P H; cbn in H;
    try contradiction.
  - exists []. split; [exact H|]. split; [reflexivity|inversion 1].
  - destruct (IHl _ H) as [xs [Hxs [Hval_l Hproj_l]]].
    destruct (IHr _ Hxs) as [ys [Hys [Hval_r Hproj_r]]].
    exists (xs ++ ys). split; [exact Hys|]. split.
    + intro env. cbn. now rewrite Hval_l, Hval_r, holds_app.
    + intros a b Hin Hab. apply in_app_or in Hin. destruct Hin.
      * eapply ui_int_ll, Hproj_l; eassumption.
      * eapply ui_int_lr, Hproj_r; eassumption.
  - exists [x]. split; [exact H|]. split.
    + intro env. change (holds env (TLit x) <-> holds env (TLit x) /\ True). tauto.
    + intros a b [E|[]] Hab. subst. now constructor.
Qed.

Lemma exists_intersection_holds : forall env t (P : list Lit -> Prop),
  (forall xs, P xs -> holds env (Intersect xs)) ->
  Exists_Intersection P t -> holds env t.
Proof.
  intros env t. induction t as [| |l IHl r IHr|l IHl r IHr|x];
    intros P HP H; cbn in H |- *; try contradiction.
  - exact I.
  - destruct H as [Hl|Hr]; [left; eapply IHl|right; eapply IHr]; eassumption.
  - destruct (integrated_int_clause (TIsect l r) P H) as [xs [Hx [Hv _]]].
    exact (proj2 (Hv env) (HP xs Hx)).
  - exact (proj1 (HP [x] H)).
Qed.

Local Notation Rule := (sig2T RRule).
Definition rule_sound (rule : Rule) : Prop :=
  forall l r, RPremise (proj2V rule) l r -> esub l r.

Lemma collect_rules : forall env xs, holds env (Intersect xs) ->
  exists rs : list Rule,
    Forall (fun y => Exists (fun rule => proj2T2 rule = y) rs) xs /\
    incl (map proj2T1 rs) env /\ Forall rule_sound rs.
Proof.
  intros env xs. induction xs as [|x xs IH]; intro H.
  - exists []. split; [apply Forall_nil|].
    split; [apply incl_nil_l|apply Forall_nil].
  - change (holds env (TLit x) /\ holds env (Intersect xs)) in H.
    destruct H as [[a [Ha [rule Hr]]] Hxs].
    destruct (IH Hxs) as [rs [Hcover [Hin Hsound]]].
    exists (exist2T a x rule :: rs). split.
    + constructor.
      * now apply Exists_cons_hd.
      * eapply Forall_impl; [|exact Hcover]. intros y Hy.
        now apply Exists_cons_tl.
    + split.
      * apply incl_cons; assumption.
      * constructor; assumption.
Qed.

Lemma listed_premise_sound : forall rs l r,
  Forall rule_sound rs ->
  Exists (fun rule : Rule => RPremise (proj2V rule) l r) rs ->
  esub l r.
Proof.
  intros rs l r Hsound H. apply Exists_exists in H.
  destruct H as [rule [Hin Hp]].
  exact (proj1 (Forall_forall _ _) Hsound rule Hin l r Hp).
Qed.

Lemma rules_hold : forall env rs,
  incl (map proj2T1 rs) env -> Forall rule_sound rs ->
  holds env (Intersect (map proj2T2 rs)).
Proof.
  intros env rs H. induction rs as [|[x y rule] rs IH]; intro Hsound; cbn.
  - exact I.
  - inversion Hsound as [|? ? Hr Hrs]; subst.
    split.
    + exists x. split.
      * apply H. now left.
      * now apply (Lsub (@RPremise) esub x y rule).
    + apply IH; [|exact Hrs]. intros a Ha. apply H. now right.
Qed.

Lemma intersect_holds : forall env xs,
  intersected env ->
  (holds env (intersect xs) <-> holds env (Intersect xs)).
Proof.
  intros env xs He. split.
  - apply rsub_entails; [apply LiteralDereliction|exact He].
  - intro H. destruct (collect_rules env xs H) as [rs [Hcover [Hin Hsound]]].
    destruct (LiteralPromotion env xs rs Hcover Hin He) as [rs' Hprom].
    eapply exists_intersection_holds; [|exact Hprom].
    intros ys [-> [Hin' Hp]]. apply rules_hold; [exact Hin'|].
    eapply Forall_impl; [|exact Hp].
    intros rule Hr l r Hprem.
    eapply rsubam_into_esub; [|apply Hr, Hprem].
    intros a b Hab. eapply listed_premise_sound; eassumption.
Qed.

Lemma integrate_holds_aux : forall env t f (Q : Prop),
  (forall xs, holds env (f xs) <-> Q /\ holds env (Intersect xs)) ->
  (holds env (Integrate f t) <-> Q /\ holds env t).
Proof.
  intros env t.
  induction t as [| |l IHl r IHr|l IHl r IHr|x]; intros f Q H; cbn.
  - exact (H []).
  - tauto.
  - rewrite (IHl f Q H), (IHr f Q H). tauto.
  - rewrite (IHl _ (Q /\ holds env r)); [tauto|].
    intro xs. rewrite (IHr _ (Q /\ holds env (Intersect xs))); [tauto|].
    intro ys. rewrite H, holds_app. tauto.
  - specialize (H [x]). cbn in H. tauto.
Qed.

Lemma integrate_holds : forall env t, intersected env ->
  (holds env (Integrate intersect t) <-> holds env t).
Proof.
  intros env t He.
  rewrite (integrate_holds_aux env t intersect True); [tauto|].
  intro xs. rewrite (intersect_holds env xs He). tauto.
Qed.

Lemma esub_entails : forall l r, esub l r -> entails l r.
Proof.
  intros l r H. induction H;
    try solve [unfold entails in *; intros env He; cbn; intuition eauto 4].
  - intros env He Hv.
    apply (dsuba_entails (fun _ _ => False) (Integrate intersect tl) tr).
    + contradiction.
    + contradiction.
    + now apply IntersectorCompleteness.
    + exact He.
    + now apply (integrate_holds env tl He).
  - exact (rsubam_entails _ _ _ H H0 (DRuleToRProof r)).
Qed.

Lemma integrate_integrated : forall t f,
  (forall xs, Integrated intersected (f xs)) ->
  Integrated intersected (Integrate f t).
Proof.
  induction t as [| |l IHl r IHr|l IHl r IHr|x]; intros f H; cbn.
  - apply H.
  - exact I.
  - split; [now apply IHl|now apply IHr].
  - apply IHl. intro xs. now apply IHr.
  - apply H.
Qed.

Lemma holds_own_literals : forall env xs,
  incl xs env -> holds env (Intersect xs).
Proof.
  intros env xs. induction xs as [|x xs IH]; intro H; cbn.
  - exact I.
  - split.
    + exists x. split; [apply H; now left|apply extended_literal_refl].
    + apply IH. intros a Ha. apply H. now right.
Qed.

Lemma clause_holds_into_ui : forall l xs r,
  clause_of l xs -> holds xs r -> uisub EL l r.
Proof.
  intros l xs r [_ Hproj]. induction r; cbn;
    intuition eauto with ui.
  destruct H as [x [Hin Hr]]. eapply Hproj; eassumption.
Qed.

Lemma pure_entails_into_ui : forall l r,
  Integrated_int intersected l -> entails l r -> uisub EL l r.
Proof.
  intros l r H Hint.
  destruct (integrated_int_clause l intersected H) as [xs [Hxs Hclause]].
  apply (clause_holds_into_ui l xs r Hclause), Hint; [exact Hxs|].
  apply (proj2 (proj1 Hclause xs)), holds_own_literals, incl_refl.
Qed.

Lemma integrated_entails_into_ui : forall l r,
  Integrated intersected l -> entails l r -> uisub EL l r.
Proof.
  induction l; intros r H Hint;
    try solve [apply ui_bot | eapply pure_entails_into_ui; eassumption].
  destruct H as [Ha Hb]. apply ui_uni_l.
  - apply IHl1; [exact Ha|].
    intros env He Hv. apply Hint; [exact He|now left].
  - apply IHl2; [exact Hb|].
    intros env He Hv. apply Hint; [exact He|now right].
Qed.

Lemma esub_integrated_ui : forall l r, esub l r ->
  uisub EL (Integrate intersect l) r.
Proof.
  intros l r H. apply integrated_entails_into_ui.
  - apply integrate_integrated, IntersectorIntegrated.
  - intros env He Hv. apply (esub_entails _ _ H env He).
    now apply (integrate_holds env l He).
Qed.

Local Hint Resolve pair_lt_left pair_lt_right sub_uni_l sub_uni_r
  sub_isect_l sub_isect_r : ui_steps.

(* Each extended premise goes through its own integrated left-hand side. *)
Lemma extended_ui_into_isub' : forall p : T * T,
  uisub EL (fst p) (snd p) -> isub' (fst p) (snd p).
Proof.
  apply (well_founded_induction pair_lt_wf
    (fun p => uisub EL (fst p) (snd p) -> isub' (fst p) (snd p))).
  intros [l r] IH H. cbn in H. revert IH.
  destruct H; intro IH; cbn; apply Rsubf.
  - destruct H as [rule Hr]. apply ui_lit.
    apply (Lsub (@IPremise) isub' ll lr rule).
    intros l r Hp. destruct Hp as [a b Hp].
    apply (IH (Integrate intersect a, b)).
    + eapply pair_lt_premise; exact Hp.
    + apply esub_integrated_ui, Hr, Hp.
  - apply ui_top.
  - apply ui_int_ll, isub'_ui.
    apply (IH (il, tr)); [eauto with ui_steps|exact H].
  - apply ui_int_lr, isub'_ui.
    apply (IH (ir, tr)); [eauto with ui_steps|exact H].
  - apply ui_int_r; apply isub'_ui.
    + apply (IH (tl, il)); [eauto with ui_steps|exact H].
    + apply (IH (tl, ir)); [eauto with ui_steps|exact H0].
  - apply ui_bot.
  - apply ui_uni_rl, isub'_ui.
    apply (IH (tl, ul)); [eauto with ui_steps|exact H].
  - apply ui_uni_rr, isub'_ui.
    apply (IH (tl, ur)); [eauto with ui_steps|exact H].
  - apply ui_uni_l; apply isub'_ui.
    + apply (IH (ul, tr)); [eauto with ui_steps|exact H].
    + apply (IH (ur, tr)); [eauto with ui_steps|exact H0].
Qed.

Theorem IntegratedCompleteness : forall tl tr : T, esub tl tr -> isub tl tr.
Proof.
  intros tl tr H. apply (extended_ui_into_isub' (Integrate intersect tl, tr)).
  now apply esub_integrated_ui.
Qed.

Theorem DecidabilityOfExtendedSubtyping : forall tl tr : T, {esub tl tr} + {~ esub tl tr}.
Proof.
  intros tl tr. destruct (IntegratedDecidability tl tr) as [H|H].
  - left. now apply IntegratedSoundness.
  - right. intro He. apply H. now apply IntegratedCompleteness.
Defined.

End Integrated.
