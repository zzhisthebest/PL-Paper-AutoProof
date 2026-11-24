Require Import Syntax Sequences Reduction.

Definition process_exceptions :=
  (Lam (* x => *) (Lam (* y => *)
    (Match_ (Var 0 (* y *)) (* with *)
      (* | None => *)
        (Var 1 (* y *))
      (* | Some z => *)
        (Match_ (Var 2 (* x *)) (* with *)
          (* | None => *)
            (Var 1 (* y *))
          (* | Some w => *)
            (Conflict)
        )
      ))).


Fixpoint trans (t: term) : term :=
  match t with
  | Var x => Var x
  | App t1 t2 => App (trans t1) (trans t2)
  | Lam t => Lam (trans t)

  | Value v => Value (trans_value v)
  | Binop op t1 t2 => Binop op (trans t1) (trans t2)

  | Match_ u t1 t2 =>
    Match_ (trans u) (trans t1) (trans t2)
  | ENone => ENone
  | ESome t => ESome (trans t)

  | If t ta tb =>
    If (trans t) (trans ta) (trans tb)
  | Fold f ts acc =>
    Fold (trans f) (List.map trans ts) (trans acc)

  | ErrorOnEmpty t => Match_ (trans t) Conflict (Var 0)
  | DefaultPure t => ESome (trans t)
  | Default ts tj tc =>
    Match_
      (Fold
        process_exceptions
        (List.map trans ts) ENone)
      (If (trans tj) (trans tc) ENone)
      (ESome (Var 0))
  | Empty => ENone
  | Conflict => Conflict
  end

with trans_value v :=
  match v with
  | Bool b => Bool b
  | Int i => Int i
  | Closure t sigma => Closure (trans t) (List.map trans_value sigma)
  | VNone => VNone
  | VUnit => VUnit
  | VSome v => VSome (trans_value v)
  | VPure v => VSome (trans_value v)
  end
.

From Stdlib Require Import List.
Import ListNotations.

Local Lemma term_ind_lists (P : term -> Prop) :
  (forall x, P (Var x)) ->
  (forall t u, P t -> P u -> P (App t u)) ->
  (forall t, P t -> P (Lam t)) ->
  (forall t, P t -> P (ErrorOnEmpty t)) ->
  (forall t, P t -> P (DefaultPure t)) ->
  (forall ts j c, Forall P ts -> P j -> P c -> P (Default ts j c)) ->
  P Empty ->
  P Conflict ->
  (forall v, P (Value v)) ->
  (forall op t u, P t -> P u -> P (Binop op t u)) ->
  (forall t u v, P t -> P u -> P v -> P (Match_ t u v)) ->
  P ENone ->
  (forall t, P t -> P (ESome t)) ->
  (forall f ts a, P f -> Forall P ts -> P a -> P (Fold f ts a)) ->
  (forall t u v, P t -> P u -> P v -> P (If t u v)) ->
  forall t, P t.
Proof.
  intros Hvar Happ Hlam Herror Hpure Hdefault Hempty Hconflict Hvalue
    Hbinop Hmatch Hnone Hsome Hfold Hif.
  fix IH 1.
  destruct t;
    first [apply Hvar | apply Happ | apply Hlam | apply Herror | apply Hpure
          | apply Hdefault | apply Hempty | apply Hconflict | apply Hvalue
          | apply Hbinop | apply Hmatch | apply Hnone | apply Hsome
          | apply Hfold | apply Hif];
    try apply IH.
  -
    revert ts.
    fix IHlist 1.
    destruct ts; constructor; [apply IH | apply IHlist].
  -
    revert ts.
    fix IHlist 1.
    destruct ts; constructor; [apply IH | apply IHlist].
Qed.

Local Lemma mmap_term_map (f : term -> term) ts :
  mmap f ts = map f (ts : list term).
Proof.
  induction ts; reflexivity.
Qed.

Local Lemma trans_map_commute (f g : term -> term) ts :
  Forall (fun t => trans (f t) = g (trans t)) ts ->
  map trans (mmap f ts) = mmap g (map trans ts).
Proof.
  intro H.
  rewrite !mmap_term_map, !map_map.
  apply map_ext_in.
  intros t Hin.
  apply Forall_forall with (x := t) in H; assumption.
Qed.

Local Lemma trans_rename t xi :
  trans (rename xi t) = rename xi (trans t).
Proof.
  revert xi.
  induction t using term_ind_lists; intro xi; cbn [rename Rename_term trans];
    try solve [f_equal; auto].
  - f_equal.
    + f_equal.
      apply trans_map_commute.
      eapply Forall_impl; [| eassumption].
      auto.
    + f_equal; auto.
  - f_equal; auto.
    apply trans_map_commute.
    eapply Forall_impl; [| eassumption].
    auto.
Qed.

Local Lemma trans_up sigma tau :
  (forall x, trans (sigma x) = tau x) ->
  forall x, trans (up sigma x) = up tau x.
Proof.
  intros H [|x].
  - reflexivity.
  - change (trans (rename S (sigma x)) = rename S (tau x)).
    now rewrite trans_rename, H.
Qed.

Local Lemma trans_subst t sigma tau :
  (forall x, trans (sigma x) = tau x) ->
  trans t.[sigma] = (trans t).[tau].
Proof.
  revert sigma tau.
  induction t using term_ind_lists; intros sigma tau Hsub;
    cbn [subst Subst_term trans];
    try solve [auto using trans_up | f_equal; auto using trans_up].
  - f_equal.
    + f_equal.
      apply trans_map_commute.
      eapply Forall_impl; [| eassumption].
      auto.
    + f_equal; auto.
  - f_equal; auto.
    apply trans_map_commute.
    eapply Forall_impl; [| eassumption].
    auto.
Qed.

Local Lemma trans_subst_of_env t vs :
  trans t.[subst_of_env vs] =
  (trans t).[subst_of_env (map trans_value vs)].
Proof.
  apply trans_subst.
  intro x.
  unfold subst_of_env.
  rewrite nth_error_map, length_map.
  destruct (nth_error vs x); reflexivity.
Qed.

Local Lemma trans_subst_value t v :
  trans t.[Value v/] = (trans t).[Value (trans_value v)/].
Proof.
  apply trans_subst.
  intros [|x]; reflexivity.
Qed.

Local Lemma sred_star_trans t u v :
  star sred t u -> star sred u v -> star sred t v.
Proof.
  intros Htu Huv.
  induction Htu; eauto using star_step.
Qed.

Local Lemma sred_star_context (C : term -> term) :
  (forall t u, sred t u -> sred (C t) (C u)) ->
  forall t u, star sred t u -> star sred (C t) (C u).
Proof.
  intros Hcontext t u H.
  induction H; eauto using star_refl, star_step.
Qed.

Local Definition joins t u :=
  exists v, star sred t v /\ star sred u v.

Local Lemma joins_star t u : star sred t u -> joins t u.
Proof.
  intro H.
  exists u; split; auto using star_refl.
Qed.

Local Lemma joins_step t u : sred t u -> joins t u.
Proof.
  intro H.
  apply joins_star.
  eauto using star_step, star_refl.
Qed.

Local Lemma joins_prefix t t' u u' :
  star sred t t' -> star sred u u' -> joins t' u' -> joins t u.
Proof.
  intros Ht Hu (v & Htv & Huv).
  exists v; split; eauto using sred_star_trans.
Qed.

Local Lemma joins_context (C : term -> term) :
  (forall t u, sred t u -> sred (C t) (C u)) ->
  forall t u, joins t u -> joins (C t) (C u).
Proof.
  intros Hcontext t u (v & Htv & Huv).
  exists (C v); split; now apply sred_star_context.
Qed.

(* The fold evaluates each exception as the first argument of the same closure. *)
Local Definition exception_head ts acc h :=
  Fold process_exceptions ts
    (App (App (Value (Closure
      (Lam (Match_ (Var 0) (Var 1) (Match_ (Var 2) (Var 1) Conflict))) [])) h)
      (Value acc)).

Local Lemma exceptions_start ts acc h :
  star sred (Fold process_exceptions (h :: ts) (Value acc))
    (exception_head ts acc h).
Proof.
  eapply star_step; [apply sred_Fold_rec |].
  eapply star_step.
  - apply sred_Fold_step, sred_app_left, sred_app_left, sred_lam.
  - apply star_refl.
Qed.

Local Lemma exception_head_step ts acc t u :
  sred t u -> sred (exception_head ts acc t) (exception_head ts acc u).
Proof.
  intro H.
  apply sred_Fold_step, sred_app_left, sred_app_right, H.
Qed.

Local Lemma exceptions_match ts acc v :
  star sred (exception_head ts acc (Value v))
    (Fold process_exceptions ts
      (Match_ (Value acc) (Value v)
        (Match_ (Value v) (Value acc) Conflict))).
Proof.
  unfold exception_head.
  eapply star_step; [apply sred_Fold_step, sred_app_left, sred_beta |].
  eapply star_step; [apply sred_Fold_step, sred_app_left, sred_lam |].
  eapply star_step; [apply sred_Fold_step, sred_beta |].
  apply star_refl.
Qed.

Local Lemma exceptions_cons_none ts h v :
  star sred h (Value v) ->
  star sred (Fold process_exceptions (h :: ts) (Value VNone))
    (Fold process_exceptions ts (Value v)).
Proof.
  intro H.
  eapply sred_star_trans; [apply exceptions_start |].
  eapply sred_star_trans.
  - apply (sred_star_context (exception_head ts VNone)).
    + apply exception_head_step.
    + exact H.
  - eapply sred_star_trans; [apply exceptions_match |].
    eapply star_step; [apply sred_Fold_step, sred_match_None | apply star_refl].
Qed.

Local Lemma exceptions_cons_some_none ts v :
  star sred (Fold process_exceptions (ENone :: ts) (Value (VSome v)))
    (Fold process_exceptions ts (Value (VSome v))).
Proof.
  eapply sred_star_trans; [apply exceptions_start |].
  eapply star_step; [apply exception_head_step, sred_None |].
  eapply sred_star_trans; [apply exceptions_match |].
  eapply star_step; [apply sred_Fold_step, sred_match_Some |].
  eapply star_step; [apply sred_Fold_step, sred_match_None | apply star_refl].
Qed.

Local Lemma exceptions_cons_some_some ts v w :
  star sred
    (Fold process_exceptions (Value (VSome w) :: ts) (Value (VSome v)))
    Conflict.
Proof.
  eapply sred_star_trans; [apply exceptions_start |].
  eapply sred_star_trans; [apply exceptions_match |].
  eapply star_step; [apply sred_Fold_step, sred_match_Some |].
  eapply star_step; [apply sred_Fold_step, sred_match_Some |].
  eapply star_step; [apply sred_Fold_Conflict | apply star_refl].
Qed.

Local Lemma exceptions_cons_conflict ts acc :
  star sred (Fold process_exceptions (Conflict :: ts) (Value acc)) Conflict.
Proof.
  eapply sred_star_trans; [apply exceptions_start |].
  eapply star_step; [apply sred_Fold_step, sred_app_left, sred_app_left_conflict |].
  eapply star_step; [apply sred_Fold_step, sred_app_right_conflict |].
  eapply star_step; [apply sred_Fold_Conflict | apply star_refl].
Qed.

Local Lemma exceptions_init ts :
  star sred (Fold process_exceptions ts ENone)
    (Fold process_exceptions ts (Value VNone)).
Proof.
  eapply star_step; [apply sred_Fold_step, sred_None | apply star_refl].
Qed.

Local Lemma exceptions_first_some ts v :
  star sred (Fold process_exceptions (Value (VSome v) :: ts) ENone)
    (Fold process_exceptions ts (Value (VSome v))).
Proof.
  eapply sred_star_trans; [apply exceptions_init |].
  apply exceptions_cons_none, star_refl.
Qed.

Local Lemma match_star t u l r :
  star sred t u -> star sred (Match_ t l r) (Match_ u l r).
Proof.
  apply (sred_star_context (fun t => Match_ t l r)).
  intros; now apply sred_match_cond.
Qed.

Local Lemma match_joins t u l r :
  joins t u -> joins (Match_ t l r) (Match_ u l r).
Proof.
  apply (joins_context (fun t => Match_ t l r)).
  intros; now apply sred_match_cond.
Qed.

Local Lemma exceptions_cons_joins ts acc t u :
  joins t u ->
  joins (Fold process_exceptions (t :: ts) (Value acc))
    (Fold process_exceptions (u :: ts) (Value acc)).
Proof.
  intro H.
  eapply joins_prefix; [apply exceptions_start | apply exceptions_start |].
  apply (joins_context (exception_head ts acc)); auto using exception_head_step.
Qed.

Local Lemma default_conflict ts j c :
  star sred (Fold process_exceptions ts ENone) Conflict ->
  joins (Match_ (Fold process_exceptions ts ENone) (If j c ENone) (ESome (Var 0)))
    Conflict.
Proof.
  intro H.
  apply joins_star.
  eapply sred_star_trans; [apply match_star; exact H |].
  eapply star_step; [apply sred_match_conflict | apply star_refl].
Qed.

Local Lemma default_justification j c :
  star sred
    (Match_ (Fold process_exceptions [] ENone) (If j c ENone) (ESome (Var 0)))
    (If j c ENone).
Proof.
  eapply sred_star_trans; [apply match_star, exceptions_init |].
  eapply star_step; [apply sred_match_cond, sred_Fold_init |].
  eapply star_step; [apply sred_match_None | apply star_refl].
Qed.

Theorem correction_small_steps:
  forall s1 s2,
  sred s1 s2 ->
  exists target,
    star sred
      (trans s1) target /\
    star sred
      (trans s2) target.
Proof.
  intros s1 s2 H.
  change (joins (trans s1) (trans s2)).
  induction H; cbn [trans trans_value map] in *;
    try solve [apply joins_step; constructor; assumption].
  - rewrite trans_subst_of_env.
    apply joins_step, sred_beta.
  - apply (joins_context (fun u =>
      App (Value (Closure (trans t) (map trans_value sigma))) u));
      auto using sred_app_right.
  - apply (joins_context (fun t => App t (trans u))); auto using sred_app_left.
  - apply joins_step, sred_binop_finish.
    destruct op, v1, v2; cbn in H; inversion H; reflexivity.
  - apply (joins_context (fun u => Binop op (Value (trans_value v)) u));
      auto using sred_binop_right.
  - apply (joins_context (fun t => Binop op t (trans u)));
      auto using sred_binop_left.
  - apply joins_star.
    eapply sred_star_trans; [apply default_justification |].
    eapply star_step; [apply sred_if_true | apply star_refl].
  - apply joins_star.
    eapply sred_star_trans; [apply default_justification |].
    eapply star_step; [apply sred_if_false | apply star_refl].
  - apply joins_star.
    eapply sred_star_trans; [apply default_justification |].
    eapply star_step; [apply sred_if_cond_conflict | apply star_refl].
  - eapply joins_prefix; [apply default_justification | apply default_justification |].
    apply (joins_context (fun t => If t (trans tc) ENone)); auto using sred_if_cond.
  - apply default_conflict.
    eapply sred_star_trans; [apply exceptions_first_some |].
    apply exceptions_cons_some_some.
  - apply joins_star.
    eapply sred_star_trans; [apply match_star, exceptions_first_some |].
    eapply star_step; [apply sred_match_cond, sred_Fold_init |].
    eapply star_step; [apply sred_match_Some |].
    eapply star_step; [apply sred_Some | apply star_refl].
  - apply default_conflict.
    eapply sred_star_trans; [apply exceptions_init |].
    apply exceptions_cons_conflict.
  - apply default_conflict.
    eapply sred_star_trans; [apply exceptions_first_some |].
    apply exceptions_cons_conflict.
  - apply match_joins.
    eapply joins_prefix; [apply exceptions_first_some | apply exceptions_first_some |].
    apply joins_star, exceptions_cons_some_none.
  - apply match_joins.
    eapply joins_prefix; [apply exceptions_init | apply exceptions_init |].
    apply joins_star, exceptions_cons_none.
    eapply star_step; [apply sred_None | apply star_refl].
  - apply match_joins.
    eapply joins_prefix; [apply exceptions_first_some | apply exceptions_first_some |].
    now apply exceptions_cons_joins.
  - apply match_joins.
    eapply joins_prefix; [apply exceptions_init | apply exceptions_init |].
    now apply exceptions_cons_joins.
  - rewrite trans_subst_value.
    apply joins_step, sred_match_Some.
  - now apply match_joins.
  - apply (joins_context ESome); auto using sred_Some_context.
  - apply (joins_context (fun t => If t (trans ta) (trans tb)));
      auto using sred_if_cond.
  - now apply match_joins.
  - apply joins_star.
    eapply star_step; [apply sred_match_cond, sred_None |].
    eapply star_step; [apply sred_match_None | apply star_refl].
  - apply (joins_context ESome); auto using sred_Some_context.
  - apply (joins_context (fun t => Fold (trans f) (map trans ts) t));
      auto using sred_Fold_step.
Qed.
