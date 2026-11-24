Require Import SSTS CD Reduction.
From Stdlib Require Import List Arith Lia Relation_Operators Wf_nat.
Import ListNotations.
Import L (term, var, app, lam).

(* Renaming and simultaneous substitution on de Bruijn terms. *)
Definition up_ren (f : nat -> nat) (i : nat) :=
  match i with 0 => 0 | S j => S (f j) end.

Fixpoint rename (f : nat -> nat) (M : term) : term :=
  match M with
  | var i => var (f i)
  | app M N => app (rename f M) (rename f N)
  | lam M => lam (rename (up_ren f) M)
  end.

Definition cons_sub (N : term) (f : nat -> term) (i : nat) :=
  match i with 0 => N | S j => f j end.

Definition up_sub (f : nat -> term) :=
  cons_sub (var 0) (fun i => rename S (f i)).

Fixpoint subst (f : nat -> term) (M : term) : term :=
  match M with
  | var i => f i
  | app M N => app (subst f M) (subst f N)
  | lam M => lam (subst (up_sub f) M)
  end.

Definition subst0 N M := subst (cons_sub N var) M.

Lemma rename_ext M f g :
  (forall i, f i = g i) -> rename f M = rename g M.
Proof.
  revert f g. induction M; intros f g H; cbn; f_equal; auto.
  apply IHM. intros [|i]; cbn; auto.
Qed.

Lemma subst_ext M f g :
  (forall i, f i = g i) -> subst f M = subst g M.
Proof.
  revert f g. induction M; intros f g H; cbn; f_equal; auto.
  apply IHM. intros [|i]; cbn; now rewrite ?H.
Qed.

Lemma rename_comp M f g :
  rename f (rename g M) = rename (fun i => f (g i)) M.
Proof.
  revert f g. induction M; intros f g; cbn; f_equal; auto.
  rewrite IHM. apply rename_ext. now intros [|i].
Qed.

Lemma subst_rename M f g :
  subst f (rename g M) = subst (fun i => f (g i)) M.
Proof.
  revert f g. induction M; intros f g; cbn; f_equal; auto.
  rewrite IHM. apply subst_ext. now intros [|i].
Qed.

Lemma rename_subst M f g :
  rename f (subst g M) = subst (fun i => rename f (g i)) M.
Proof.
  revert f g. induction M; intros f g; cbn; f_equal; auto.
  rewrite IHM. apply subst_ext. intros [|i]; cbn; auto.
  now rewrite !rename_comp.
Qed.

Lemma subst_comp M f g :
  subst f (subst g M) = subst (fun i => subst f (g i)) M.
Proof.
  revert f g. induction M; intros f g; cbn; f_equal; auto.
  rewrite IHM. apply subst_ext. intros [|i]; cbn; auto.
  now rewrite subst_rename, rename_subst.
Qed.

Lemma subst_id M : subst var M = M.
Proof.
  induction M; cbn; f_equal; auto.
  rewrite <- IHM at 2. apply subst_ext. now intros [|i].
Qed.

Lemma subst0_up M N f :
  subst0 N (subst (up_sub f) M) = subst (cons_sub N f) M.
Proof.
  unfold subst0. rewrite subst_comp. apply subst_ext.
  intros [|i]; cbn; auto. now rewrite subst_rename, subst_id.
Qed.

Lemma subst_subst0 M N f :
  subst f (subst0 N M) = subst0 (subst f N) (subst (up_sub f) M).
Proof.
  rewrite subst0_up. unfold subst0. rewrite subst_comp.
  apply subst_ext. now intros [|i].
Qed.

Lemma rename_as_subst M f : rename f M = subst (fun i => var (f i)) M.
Proof.
  rewrite <- subst_rename, subst_id. reflexivity.
Qed.

Inductive beta : term -> term -> Prop :=
| beta_red M N : beta (app (lam M) N) (subst0 N M)
| beta_fun M M' N : beta M M' -> beta (app M N) (app M' N)
| beta_arg M N N' : beta N N' -> beta (app M N) (app M N')
| beta_lam M M' : beta M M' -> beta (lam M) (lam M').

Definition betas := clos_refl_trans term beta.

Lemma beta_subst M M' f : beta M M' -> beta (subst f M) (subst f M').
Proof.
  intros D. revert f. induction D; intros f; cbn.
  - rewrite subst_subst0. apply beta_red.
  - apply beta_fun, IHD.
  - apply beta_arg, IHD.
  - apply beta_lam, IHD.
Qed.

Lemma beta_rename M M' f : beta M M' -> beta (rename f M) (rename f M').
Proof.
  rewrite !rename_as_subst. apply beta_subst.
Qed.

Lemma betas_map (f : term -> term) :
  (forall M N, beta M N -> beta (f M) (f N)) ->
  forall M N, betas M N -> betas (f M) (f N).
Proof. intros H M N D. induction D; [apply rt_step; auto|apply rt_refl|eapply rt_trans; eauto]. Qed.

Lemma betas_subst_arguments M f g :
  (forall i, betas (f i) (g i)) -> betas (subst f M) (subst g M).
Proof.
  revert f g. induction M; intros f g H; cbn.
  - apply H.
  - eapply rt_trans.
    + apply (betas_map (fun U => app U (subst f M2))); [intros; now apply beta_fun|auto].
    + apply (betas_map (app (subst g M1))); [intros; now apply beta_arg|auto].
  - apply (betas_map lam); [intros; now apply beta_lam|].
    apply IHM. intros [|i]; cbn; [apply rt_refl|].
    apply (betas_map (rename S)); [intros; now apply beta_rename|auto].
Qed.

Definition SN M := Acc (fun N M => beta M N) M.

Lemma sn_subst_inv M f : SN (subst f M) -> SN M.
Proof.
  intros H. remember (subst f M) as U eqn:E in H.
  revert M E. induction H as [U _ IH]. intros M ->.
  constructor. intros N D. apply (IH (subst f N)); [now apply beta_subst|reflexivity].
Qed.

Lemma sn_fun M N : SN (app M N) -> SN M.
Proof.
  intros H. remember (app M N) as U eqn:E in H.
  revert M E. induction H as [U _ IH]. intros M ->.
  constructor. intros M' D. apply (IH (app M' N)); [now apply beta_fun|reflexivity].
Qed.


Lemma sty_ind_deep (P : sty -> Prop) :
  (forall a, P (atom a)) ->
  (forall s l t, P s -> Forall P l -> P t -> P (arr s l t)) ->
  forall t, P t.
Proof.
  intros A B. fix IH 1. intros [a|s l t].
  - apply A.
  - apply B; [apply IH| |apply IH].
    induction l as [|u l F]; constructor; auto.
Qed.

Fixpoint reducible (t : sty) (M : term) : Prop :=
  match t with
  | atom _ => SN M
  | arr s l t => forall N, reducible s N ->
      (fix all (l : list sty) : Prop :=
        match l with [] => True | u :: l => reducible u N /\ all l end) l ->
      reducible t (app M N)
  end.

Lemma reducible_arr s l t M :
  reducible (arr s l t) M <->
  forall N, reducible s N -> Forall (fun u => reducible u N) l -> reducible t (app M N).
Proof.
  cbn. assert (H : forall N, (fix all (l : list sty) : Prop :=
        match l with [] => True | u :: l => reducible u N /\ all l end) l <->
        Forall (fun u => reducible u N) l).
  { intros N. induction l; cbn.
    - split; constructor.
    - rewrite IHl, Forall_cons_iff. tauto. }
  setoid_rewrite H. reflexivity.
Qed.

Definition non_lam (M : term) :=
  match M with lam _ => False | _ => True end.

Lemma reducible_properties t :
  (forall M, reducible t M -> SN M) /\
  (forall M N, reducible t M -> beta M N -> reducible t N) /\
  (forall M, non_lam M -> (forall N, beta M N -> reducible t N) -> reducible t M).
Proof.
  induction t as [a|s l t [Ss [Rs Es]] Il [St [Rt Et]]] using sty_ind_deep.
  - cbn. split; [auto|]. split.
    + intros M N H D. exact (Acc_inv H D).
    + intros M _ H. now constructor.
  - assert (V : forall u, In u l -> reducible u (var 0)).
    { intros u Hu. specialize ((proj1 (Forall_forall _ _) Il) u Hu) as Iu.
      destruct Iu as [_ [_ E]]. apply E; [exact I|intros N D; inversion D]. }
    split.
    + intros M H. apply (sn_fun M (var 0)), St.
      apply (proj1 (reducible_arr s l t M) H).
      * apply Es; [exact I|intros N D; inversion D].
      * now apply Forall_forall.
    + split.
      * intros M M' H D. apply reducible_arr. intros N Hs Hl.
        eapply Rt; [exact (proj1 (reducible_arr s l t M) H N Hs Hl)|now apply beta_fun].
      * intros M E H. apply reducible_arr. intros N Hs Hl.
        pose proof (Ss _ Hs) as A. induction A as [N _ IH].
        apply Et; [exact I|]. intros U D. inversion D; subst.
        -- contradiction.
        -- apply (proj1 (reducible_arr s l t M') (H M' ltac:(eassumption)) N Hs Hl).
        -- apply IH; [eassumption|eapply Rs; eauto|].
           rewrite Forall_forall in Il, Hl |- *.
           intros u Hu. apply (proj1 (proj2 (Il u Hu)) N N'); auto.
Qed.

Lemma reducible_sn t M : reducible t M -> SN M.
Proof. apply (proj1 (reducible_properties t)). Qed.

Lemma reducible_beta t M N : reducible t M -> beta M N -> reducible t N.
Proof. apply (proj1 (proj2 (reducible_properties t))). Qed.

Lemma reducible_non_lam t M :
  non_lam M -> (forall N, beta M N -> reducible t N) -> reducible t M.
Proof. apply (proj2 (proj2 (reducible_properties t))). Qed.

Lemma reducible_var t x : reducible t (var x).
Proof. apply reducible_non_lam; [exact I|intros N D; inversion D]. Qed.

Lemma reducible_betas t M N : betas M N -> reducible t M -> reducible t N.
Proof. induction 1; eauto using reducible_beta. Qed.

Lemma reducible_redex t M N :
  SN N -> reducible t (subst0 N M) -> reducible t (app (lam M) N).
Proof.
  intros HN H. assert (HM : SN M).
  { apply (sn_subst_inv M (cons_sub N var)), (reducible_sn t), H. }
  revert N HN H. induction HM as [M _ IM]. intros N HN.
  induction HN as [N AN IN]. intros H.
  apply reducible_non_lam; [exact I|]. intros U D. inversion D; subst.
  - exact H.
  - match goal with K : beta (lam _) _ |- _ => inversion K; subst end.
    eapply IM.
    + eassumption.
    + now constructor.
    + eapply reducible_beta; [exact H|now apply beta_subst].
  - eapply IN; [eassumption|].
    eapply reducible_betas; [|exact H].
    apply betas_subst_arguments. intros [|i]; cbn; [apply rt_step; eassumption|apply rt_refl].
Qed.

Lemma typing_var_inv G x t :
  type_assignment G (var x) t <->
  exists s l, nth_error G x = Some (s,l) /\ In t (s::l).
Proof.
  split; [inversion 1; subst; eauto|intros (s & l & H & I); eapply type_assignment_var; eauto].
Qed.

Lemma typing_app_inv G M N t :
  type_assignment G (app M N) t <->
  exists s l, type_assignment G M (arr s l t) /\
              type_assignment G N s /\ Forall (type_assignment G N) l.
Proof.
  split; [inversion 1; subst; eauto 8|intros (s & l & H & A & B); eapply type_assignment_app; eauto].
Qed.

Lemma typing_lam_inv G M t :
  type_assignment G (lam M) t <->
  exists s l u, t = arr s l u /\ type_assignment ((s,l)::G) M u.
Proof.
  split; [inversion 1; subst; eauto 8|intros (s & l & u & -> & H); now constructor].
Qed.

Lemma typing_ind_deep (P : list ty -> term -> sty -> Prop) :
  (forall G x s l t, nth_error G x = Some (s,l) -> In t (s::l) -> P G (var x) t) ->
  (forall G M N s l t, type_assignment G M (arr s l t) -> P G M (arr s l t) ->
       type_assignment G N s -> P G N s ->
       Forall (type_assignment G N) l -> Forall (P G N) l -> P G (app M N) t) ->
  (forall G M s l t, type_assignment ((s,l)::G) M t -> P ((s,l)::G) M t ->
       P G (lam M) (arr s l t)) ->
  forall G M t, type_assignment G M t -> P G M t.
Proof.
  intros V A L. fix IH 4. intros G M t H. destruct H.
  - eapply V; eauto.
  - eapply A; try eassumption; try now apply IH.
    clear H H0. induction H1 as [|u l Hu Hl IHl].
    + constructor.
    + constructor; [now apply IH|exact IHl].
  - apply L; [assumption|now apply IH].
Qed.

Lemma typing_rename G M t :
  type_assignment G M t ->
  forall D f, (forall x p, nth_error G x = Some p -> nth_error D (f x) = Some p) ->
  type_assignment D (rename f M) t.
Proof.
  induction 1 using typing_ind_deep; intros D f E; cbn.
  - eapply type_assignment_var; eauto.
  - eapply type_assignment_app; [eauto|eauto|].
    eapply Forall_impl; [|eassumption]. auto.
  - constructor. apply IHtype_assignment. intros [|x] p Hp; cbn in *; auto.
Qed.

Lemma typing_subst G M t :
  type_assignment G M t ->
  forall D f, (forall x s l t, nth_error G x = Some (s,l) -> In t (s::l) ->
      type_assignment D (f x) t) ->
  type_assignment D (subst f M) t.
Proof.
  induction 1 using typing_ind_deep; intros D f E; cbn.
  - eauto.
  - eapply type_assignment_app; [eauto|eauto|].
    eapply Forall_impl; [|eassumption]. auto.
  - constructor. apply IHtype_assignment. intros [|x] u k v Hp Hu; cbn in *.
    + eapply type_assignment_var; [exact Hp|exact Hu].
    + eapply typing_rename; [eapply E; eassumption|]. now intros.
Qed.

Lemma beta_preserves M N :
  beta M N -> forall G t, type_assignment G M t -> type_assignment G N t.
Proof.
  intros D. induction D as [M N|M M' N D IHD|M N N' D IHD|M M' D IHD]; intros G u H.
  - apply typing_app_inv in H as (s & l & H & A & F).
    apply typing_lam_inv in H as (v & k & w & E & H). inversion E; subst.
    eapply typing_subst; [exact H|].
    intros [|x] p q r E' Hr; cbn in *.
    + inversion E'; subst. destruct Hr as [<-|Hr]; [exact A|].
      exact ((proj1 (Forall_forall _ _) F) r Hr).
    + eapply type_assignment_var; eauto.
  - apply typing_app_inv in H as (s & l & H & A & F).
    eapply type_assignment_app; eauto.
  - apply typing_app_inv in H as (s & l & H & A & F).
    eapply type_assignment_app; [exact H|eauto|].
    eapply Forall_impl; [|exact F]. auto.
  - apply typing_lam_inv in H as (s & l & t & -> & H).
    constructor. auto.
Qed.

Lemma betas_preserve M N G t :
  betas M N -> type_assignment G M t -> type_assignment G N t.
Proof. induction 1; eauto using beta_preserves. Qed.

Lemma typing_reducible G M t :
  type_assignment G M t ->
  forall f, (forall x s l t, nth_error G x = Some (s,l) -> In t (s::l) ->
       reducible t (f x)) -> reducible t (subst f M).
Proof.
  induction 1 using typing_ind_deep; intros f E; cbn [subst].
  - eauto.
  - apply (proj1 (reducible_arr s l t _) (IHtype_assignment1 f E)).
    + auto.
    + eapply Forall_impl; [|eassumption]. auto.
  - apply reducible_arr. intros N HN FN.
    apply reducible_redex; [eapply reducible_sn; exact HN|].
    rewrite subst0_up. apply IHtype_assignment.
    intros [|x] u k v Hp Hu; cbn in *.
    + inversion Hp; subst. destruct Hu as [<-|Hu]; [exact HN|].
      exact ((proj1 (Forall_forall _ _) FN) v Hu).
    + eauto.
Qed.

Definition normal M := forall N, ~ beta M N.

Lemma beta_dec M : normal M \/ exists N, beta M N.
Proof.
  induction M as [x|M I N J|M I].
  - left. intros U D. inversion D.
  - destruct M as [x|P Q|P].
    + destruct J as [J|[N' J]].
      * left. intros U D. inversion D; subst.
        -- match goal with H : beta (var _) _ |- _ => inversion H end.
        -- eapply J; eassumption.
      * right. eauto using beta_arg.
    + destruct I as [I|[M' I]], J as [J|[N' J]].
      * left. intros U D. inversion D; subst; first [eapply I; eassumption|eapply J; eassumption].
      * right. eauto using beta_arg.
      * right. eauto using beta_fun.
      * right. eauto using beta_fun.
    + right. eauto using beta_red.
  - destruct I as [I|[M' I]].
    + left. intros U D. inversion D; subst; eapply I; eassumption.
    + right. eauto using beta_lam.
Qed.

Lemma sn_normal M : SN M -> exists N, betas M N /\ normal N.
Proof.
  induction 1 as [M _ IH]. destruct (beta_dec M) as [H|[U D]].
  - exists M. split; [apply rt_refl|exact H].
  - destruct (IH U D) as (N & E & H). exists N. split; [|exact H].
    eapply rt_trans; [apply rt_step, D|exact E].
Qed.

Lemma typed_normal G M t :
  type_assignment G M t -> exists N, normal N /\ type_assignment G N t.
Proof.
  intros H. pose proof (typing_reducible G M t H var) as R.
  assert (SN M) as A.
  { apply (reducible_sn t). rewrite <- subst_id. apply R. intros. apply reducible_var. }
  destruct (sn_normal M A) as (N & D & F).
  exists N. split; [exact F|eauto using betas_preserve].
Qed.

(* A normal term is an abstraction or a variable applied to a list of arguments. *)
Definition apps M (args : list term) := fold_left app args M.

Lemma normal_fun M N : normal (app M N) -> normal M.
Proof. intros H U D. exact (H _ (beta_fun _ _ _ D)). Qed.

Lemma normal_arg M N : normal (app M N) -> normal N.
Proof. intros H U D. exact (H _ (beta_arg _ _ _ D)). Qed.

Lemma normal_body M : normal (lam M) -> normal M.
Proof. intros H U D. exact (H _ (beta_lam _ _ D)). Qed.

Lemma apps_snoc M args N : apps M (args ++ [N]) = app (apps M args) N.
Proof. apply fold_left_app. Qed.

Lemma normal_shape M :
  normal M -> (exists N, M = lam N) \/ (exists x args, M = apps (var x) args).
Proof.
  induction M as [x|M IH N _|M _]; intros H.
  - right. exists x, []. reflexivity.
  - destruct (IH (normal_fun _ _ H)) as [[U ->]|(x & args & ->)].
    + exfalso. eapply H, beta_red.
    + right. exists x, (args ++ [N]). now rewrite apps_snoc.
  - left. eauto.
Qed.

Fixpoint spine G t (args : list term) u {struct args} : Prop :=
  match args with
  | [] => t = u
  | N :: args => match t with
    | atom _ => False
    | arr s l t => type_assignment G N s /\ Forall (type_assignment G N) l /\ spine G t args u
    end
  end.

Lemma spine_snoc G t args s l u N :
  spine G t args (arr s l u) ->
  type_assignment G N s -> Forall (type_assignment G N) l ->
  spine G t (args ++ [N]) u.
Proof.
  revert t. induction args as [|P args IH]; intros t H A F; cbn in *.
  - subst t. auto.
  - destruct t; [contradiction|]. destruct H as (B & C & H). auto.
Qed.

Lemma typing_spine G x args u :
  type_assignment G (apps (var x) args) u ->
  exists t, type_assignment G (var x) t /\ spine G t args u.
Proof.
  revert u. induction args as [|args N IH] using rev_ind; intros u H.
  - exists u. split; [exact H|reflexivity].
  - rewrite apps_snoc in H. apply typing_app_inv in H as (s & l & H & A & F).
    destruct (IH _ H) as (t & V & S). exists t. eauto using spine_snoc.
Qed.

Fixpoint result t :=
  match t with atom k => k | arr _ _ t => result t end.

Lemma spine_result G t args u : spine G t args u -> result t = result u.
Proof.
  revert t. induction args; intros t H; cbn in H.
  - now subst.
  - destruct t as [k|s l t]; cbn in H; [contradiction|]. apply (IHargs t). tauto.
Qed.

(* The four control atoms and the three position markers are disjoint
   from the alphabet atoms. *)
Definition goal_ty := atom 0.
Definition active := atom 1.
Definition frozen := atom 2.
Definition reserve := atom 3.
Definition left_mark := atom 4.
Definition right_mark := atom 5.
Definition other_mark := atom 6.
Definition cell a := atom (7 + a).
Local Infix "~>" := (fun s t => arr s [] t) (at level 60, right associativity).

Definition start_ty := arr active [reserve] goal_ty.
Definition grow_active := (right_mark ~> frozen) ~> active.
Definition grow_frozen := (other_mark ~> frozen) ~> frozen.
Definition grow_reserve := arr (left_mark ~> active) [other_mark ~> reserve] reserve.
Definition stop_active := cell 1 ~> active.
Definition stop_frozen := cell 1 ~> frozen.
Definition stop_reserve := cell 0 ~> reserve.

Definition rule := ((nat * nat) * (nat * nat))%type.

Definition alphabet (R : Ssts) : list nat :=
  0 :: 1 :: flat_map (fun '((a,b),(c,d)) => [a;b;c;d]) R.

Inductive action R : rule -> sty -> nat -> nat -> Prop :=
| action_left a b c d : action R ((a,b),(c,d)) left_mark a c
| action_right a b c d : action R ((a,b),(c,d)) right_mark b d
| action_other r a : In a (alphabet R) -> action R r other_mark a a.

Definition rule_entry R (r : rule) : ty :=
  let '((a,b),(c,d)) := r in
  (left_mark ~> cell a ~> cell c,
   (right_mark ~> cell b ~> cell d) ::
   map (fun z => other_mark ~> cell z ~> cell z) (alphabet R)).

Definition entry_types (p : ty) := fst p :: snd p.

Lemma rule_entry_spec R r t :
  In t (entry_types (rule_entry R r)) <->
  exists k a b, action R r k a b /\ t = (k ~> cell a ~> cell b).
Proof.
  destruct r as [[a b] [c d]]. cbn [rule_entry entry_types fst snd In].
  split.
  - intros [<-|[<-|H]].
    + eauto using action_left.
    + eauto using action_right.
    + apply in_map_iff in H as (z & <- & I).
      exists other_mark, z, z. split; [now apply action_other|reflexivity].
  - intros (k & x & y & H & ->). inversion H; subst.
    + now left.
    + now right; left.
    + right; right. apply in_map_iff. exists y. auto.
Qed.

Definition marker i x :=
  atom (if i =? x then 4 else if i =? S x then 5 else 6).

Definition prefix n i : list ty :=
  map (fun x => (marker i x, [])) (seq 0 n).

Definition constants R : list ty :=
  (start_ty, []) ::
  (grow_active, [grow_frozen; grow_reserve]) ::
  (stop_active, [stop_frozen; stop_reserve]) ::
  (cell 0, []) :: map (rule_entry R) R.

Definition context R n i := prefix n i ++ constants R.

Lemma prefix_length n i : length (prefix n i) = n.
Proof. unfold prefix. now rewrite length_map, length_seq. Qed.

Lemma prefix_lookup n i x :
  x < n -> nth_error (prefix n i) x = Some (marker i x, []).
Proof.
  intros H. unfold prefix. rewrite nth_error_map.
  assert (nth_error (seq 0 n) x = Some x) as ->.
  { rewrite (nth_error_nth' (seq 0 n) 0) by now rewrite length_seq.
    f_equal. now rewrite seq_nth. }
  reflexivity.
Qed.

Lemma context_push R n i :
  context R (S n) (S i) = (marker (S i) 0, []) :: context R n i.
Proof.
  unfold context, prefix. cbn [seq map].
  rewrite <- (seq_shift n 0), map_map. reflexivity.
Qed.

Lemma marker_outside i x : i <> x -> i <> S x -> marker i x = other_mark.
Proof. intros A B. unfold marker. now rewrite (proj2 (Nat.eqb_neq _ _) A), (proj2 (Nat.eqb_neq _ _) B). Qed.

Lemma marker_here x : marker x x = left_mark.
Proof. unfold marker. now rewrite Nat.eqb_refl. Qed.

Lemma marker_next x : marker (S x) x = right_mark.
Proof.
  unfold marker. rewrite (proj2 (Nat.eqb_neq (S x) x) ltac:(lia)), Nat.eqb_refl. reflexivity.
Qed.

Lemma prefix_outside n i j : n < i -> n < j -> prefix n i = prefix n j.
Proof.
  intros A B. unfold prefix. apply map_ext_in. intros x H. apply in_seq in H.
  rewrite !marker_outside by lia. reflexivity.
Qed.

Lemma context_outside R n i j :
  n < i -> n < j -> context R n i = context R n j.
Proof. intros A B. unfold context. now rewrite (prefix_outside n i j). Qed.

Lemma context_new R n :
  context R (S n) 0 = (left_mark, []) :: context R n (S n).
Proof.
  unfold context, prefix. cbn [seq map].
  rewrite <- (seq_shift n 0), map_map, marker_here.
  cbn [List.app]. f_equal. f_equal. apply map_ext_in. intros x H. apply in_seq in H.
  change ((other_mark, @nil sty) = (marker (S n) x, [])).
  rewrite marker_outside by lia. reflexivity.
Qed.

Definition at_head R n i x t :=
  exists p, nth_error (context R n i) x = Some p /\ In t (entry_types p).

Lemma at_head_typed R n i x t :
  at_head R n i x t <-> type_assignment (context R n i) (var x) t.
Proof.
  unfold at_head. rewrite typing_var_inv. split.
  - intros ([s l] & H & I). exists s, l. exact (conj H I).
  - intros (s & l & H & I). exists (s,l). exact (conj H I).
Qed.

Inductive head R n i : nat -> sty -> Prop :=
| head_marker x : x < n -> head R n i x (marker i x)
| head_start : head R n i n start_ty
| head_grow_active : head R n i (n+1) grow_active
| head_grow_frozen : head R n i (n+1) grow_frozen
| head_grow_reserve : head R n i (n+1) grow_reserve
| head_stop_active : head R n i (n+2) stop_active
| head_stop_frozen : head R n i (n+2) stop_frozen
| head_stop_reserve : head R n i (n+2) stop_reserve
| head_zero : head R n i (n+3) (cell 0)
| head_rule j r k a b :
    nth_error R j = Some r -> action R r k a b ->
    head R n i (n+4+j) (k ~> cell a ~> cell b).

Lemma head_spec R n i x t : at_head R n i x t <-> head R n i x t.
Proof.
  split.
  - intros (p & E & H). unfold context in E.
    destruct (lt_dec x n) as [L|L].
    + rewrite nth_error_app1 in E by now rewrite prefix_length.
      rewrite prefix_lookup in E by exact L. inversion E; subst p.
      destruct H as [<-|[]]. now constructor.
    + rewrite nth_error_app2, prefix_length in E by (rewrite prefix_length; lia).
      remember (x-n) as j eqn:Ej. destruct j as [|[|[|[|j]]]].
      * replace x with n by lia. cbn in E. inversion E; subst p.
        destruct H as [<-|[]]. constructor.
      * replace x with (n+1) by lia. cbn in E. inversion E; subst p.
        destruct H as [<-|[<-|[<-|[]]]]; constructor.
      * replace x with (n+2) by lia. cbn in E. inversion E; subst p.
        destruct H as [<-|[<-|[<-|[]]]]; constructor.
      * replace x with (n+3) by lia. cbn in E. inversion E; subst p.
        destruct H as [<-|[]]. constructor.
      * replace x with (n+4+j) by lia. cbn in E. rewrite nth_error_map in E.
        destruct (@nth_error rule R j) as [r|] eqn:Er; cbn in E; [|discriminate E].
        inversion E; subst p. apply rule_entry_spec in H as (k & a & b & A & ->).
        eapply head_rule; eassumption.
  - intros H. destruct H.
    + exists (marker i x, []). split; [|now left].
      unfold context. rewrite nth_error_app1, prefix_lookup; auto.
      now rewrite prefix_length.
    + exists (start_ty, []). split; [|now left].
      unfold context. rewrite nth_error_app2, prefix_length, Nat.sub_diag; [reflexivity|now rewrite prefix_length].
    + exists (grow_active, [grow_frozen; grow_reserve]). split; [|now left].
      unfold context. rewrite nth_error_app2, prefix_length by (rewrite prefix_length; lia).
      replace (n+1-n) with 1 by lia. reflexivity.
    + exists (grow_active, [grow_frozen; grow_reserve]). split; [|now right; left].
      unfold context. rewrite nth_error_app2, prefix_length by (rewrite prefix_length; lia).
      replace (n+1-n) with 1 by lia. reflexivity.
    + exists (grow_active, [grow_frozen; grow_reserve]). split; [|now right; right; left].
      unfold context. rewrite nth_error_app2, prefix_length by (rewrite prefix_length; lia).
      replace (n+1-n) with 1 by lia. reflexivity.
    + exists (stop_active, [stop_frozen; stop_reserve]). split; [|now left].
      unfold context. rewrite nth_error_app2, prefix_length by (rewrite prefix_length; lia).
      replace (n+2-n) with 2 by lia. reflexivity.
    + exists (stop_active, [stop_frozen; stop_reserve]). split; [|now right; left].
      unfold context. rewrite nth_error_app2, prefix_length by (rewrite prefix_length; lia).
      replace (n+2-n) with 2 by lia. reflexivity.
    + exists (stop_active, [stop_frozen; stop_reserve]). split; [|now right; right; left].
      unfold context. rewrite nth_error_app2, prefix_length by (rewrite prefix_length; lia).
      replace (n+2-n) with 2 by lia. reflexivity.
    + exists (cell 0, []). split; [|now left].
      unfold context. rewrite nth_error_app2, prefix_length by (rewrite prefix_length; lia).
      replace (n+3-n) with 3 by lia. reflexivity.
    + exists (rule_entry R r). split.
      * unfold context. rewrite nth_error_app2, prefix_length by (rewrite prefix_length; lia).
        replace (n+4+j-n) with (4+j) by lia. cbn. rewrite nth_error_map.
        change (@nth_error rule R j = Some r) in H. now rewrite H.
      * apply rule_entry_spec. eauto.
Qed.

Lemma head_typed R n i x t :
  head R n i x t <-> type_assignment (context R n i) (var x) t.
Proof. now rewrite <- head_spec, at_head_typed. Qed.

Definition row R n i M t := type_assignment (context R n i) M t.

Lemma spine_nullary G args a b :
  spine G (atom a) args (atom b) -> args = [] /\ atom a = atom b.
Proof. now destruct args. Qed.

Lemma spine_unary G args s l a b :
  spine G (arr s l (atom a)) args (atom b) ->
  exists N, args = [N] /\ atom a = atom b /\
    type_assignment G N s /\ Forall (type_assignment G N) l.
Proof.
  destruct args as [|N args]; cbn; [discriminate|].
  intros (H & F & S). apply spine_nullary in S as [-> E]. eauto.
Qed.

Lemma spine_binary G args s t a b :
  spine G (s ~> t ~> atom a) args (atom b) ->
  exists X N, args = [X;N] /\ atom a = atom b /\
    type_assignment G X s /\ type_assignment G N t.
Proof.
  destruct args as [|X args]; cbn; [discriminate|].
  intros (H & _ & S). apply spine_unary in S as (N & -> & E & B & _). exists X, N. auto.
Qed.

Inductive atom_case R n i : nat -> list term -> sty -> Prop :=
| case_marker x : x < n -> atom_case R n i x [] (marker i x)
| case_start U :
    row R n i U active -> row R n i U reserve ->
    atom_case R n i n [U] goal_ty
| case_grow_active U :
    row R n i U (right_mark ~> frozen) ->
    atom_case R n i (n+1) [U] active
| case_grow_frozen U :
    row R n i U (other_mark ~> frozen) ->
    atom_case R n i (n+1) [U] frozen
| case_grow_reserve U :
    row R n i U (left_mark ~> active) -> row R n i U (other_mark ~> reserve) ->
    atom_case R n i (n+1) [U] reserve
| case_stop_active U :
    row R n i U (cell 1) -> atom_case R n i (n+2) [U] active
| case_stop_frozen U :
    row R n i U (cell 1) -> atom_case R n i (n+2) [U] frozen
| case_stop_reserve U :
    row R n i U (cell 0) -> atom_case R n i (n+2) [U] reserve
| case_zero : atom_case R n i (n+3) [] (cell 0)
| case_rule j r k a b X U :
    nth_error R j = Some r -> action R r k a b ->
    row R n i X k -> row R n i U (cell a) ->
    atom_case R n i (n+4+j) [X;U] (cell b).

Lemma atomic_spine R n i x args a :
  row R n i (apps (var x) args) (atom a) -> atom_case R n i x args (atom a).
Proof.
  intros H. apply typing_spine in H as (t & V & S).
  apply head_typed in V. destruct V.
  - apply spine_nullary in S as (-> & E). rewrite <- E. now constructor.
  - apply spine_unary in S as (U & -> & E & A & F).
    rewrite <- E. inversion F; subst. now constructor.
  - apply spine_unary in S as (U & -> & E & A & F). rewrite <- E. now constructor.
  - apply spine_unary in S as (U & -> & E & A & F). rewrite <- E. now constructor.
  - apply spine_unary in S as (U & -> & E & A & F).
    rewrite <- E. inversion F; subst. now constructor.
  - apply spine_unary in S as (U & -> & E & A & F). rewrite <- E. now constructor.
  - apply spine_unary in S as (U & -> & E & A & F). rewrite <- E. now constructor.
  - apply spine_unary in S as (U & -> & E & A & F). rewrite <- E. now constructor.
  - apply spine_nullary in S as (-> & E). rewrite <- E. constructor.
  - apply spine_binary in S as (X & U & -> & E & A & B).
    rewrite <- E. eapply case_rule; eassumption.
Qed.

Lemma normal_atom_spine R n i M a :
  normal M -> row R n i M (atom a) ->
  exists x args, M = apps (var x) args /\ atom_case R n i x args (atom a).
Proof.
  intros H T. destruct (normal_shape M H) as [(U & ->)|(x & args & ->)].
  - apply typing_lam_inv in T as (s & l & u & E & _). discriminate E.
  - exists x, args. auto using atomic_spine.
Qed.

Lemma marker_inv R n i M k :
  normal M -> row R n i M k ->
  (k = left_mark \/ k = right_mark \/ k = other_mark) ->
  exists x, x < n /\ M = var x /\ marker i x = k.
Proof.
  intros H T [-> | [-> | ->]].
  all: destruct (normal_atom_spine R n i M _ H T) as (x & args & -> & C).
  all: inversion C; subst; try discriminate; exists x;
    split; [assumption|split; [reflexivity|unfold marker, left_mark, right_mark, other_mark; congruence]].
Qed.

Lemma normal_reserve_arrow R n i M :
  normal M -> row R n i M (other_mark ~> reserve) -> exists U, M = lam U.
Proof.
  intros H T. destruct (normal_shape M H) as [(U & ->)|(x & args & ->)]; [eauto|].
  apply typing_spine in T as (t & V & Sp).
  pose proof (spine_result _ _ _ _ Sp) as E.
  apply head_typed in V. destruct V.
  - unfold marker in E. destruct (i =? x), (i =? S x); discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - destruct args as [|N args]; cbn in Sp; [discriminate|].
    destruct args; cbn in Sp; [destruct Sp as (_ & _ & F); discriminate|tauto].
  - discriminate.
  - discriminate.
  - destruct args as [|N args]; cbn in Sp; [discriminate|].
    destruct args; cbn in Sp; [destruct Sp as (_ & _ & F); discriminate|tauto].
  - discriminate.
  - discriminate.
Qed.

(* The rule term carries the index of one rule and the binder for one pair. *)
Definition rule_term n j x U := app (app (var (n+4+j)) (var x)) U.

Lemma cell_case R n i x args z :
  atom_case R n i x args (cell z) ->
  (x = n+3 /\ args = [] /\ z = 0) \/
  exists j r k a X U, x = n+4+j /\ args = [X;U] /\
    nth_error R j = Some r /\ action R r k a z /\ row R n i X k /\ row R n i U (cell a).
Proof.
  intros C. inversion C; subst; try discriminate.
  - match goal with E : (if _ then _ else _) = _ |- _ =>
      unfold cell in E; destruct (i =? x), (i =? S x); lia
    end.
  - left. auto.
  - right. exists j, r, k, a, X, U. repeat split; assumption.
Qed.

Lemma action_marker R r k a b :
  action R r k a b -> k = left_mark \/ k = right_mark \/ k = other_mark.
Proof. destruct 1; auto. Qed.

Lemma normal_cell R n i M b :
  normal M -> row R n i M (cell b) ->
  M = var (n+3) \/
  exists j r x U, nth_error R j = Some r /\ x < n /\ M = rule_term n j x U.
Proof.
  intros H T. destruct (normal_atom_spine R n i M _ H T) as (v & args & -> & C).
  apply cell_case in C as [(-> & -> & _) | (j & r & k & a & X & U & -> & -> & E & A & V & W)].
  - now left.
  - cbn [apps fold_left] in H.
    pose proof (normal_arg _ _ (normal_fun _ _ H)) as Hx.
    destruct (marker_inv R n i X k Hx V (action_marker _ _ _ _ _ A)) as (x & L & -> & _).
    right. exists j, r, x, U. auto.
Qed.

Lemma zero_at R n i b :
  row R n i (var (n+3)) (cell b) -> b = 0.
Proof.
  change (row R n i (apps (var (n+3)) []) (cell b) -> b = 0).
  intros H. apply atomic_spine, cell_case in H.
  destruct H as [(_ & _ & H)|(j & r & k & a & X & U & E & _)]; [exact H|lia].
Qed.

Lemma marker_var_at R n i x k :
  x < n -> row R n i (var x) k <-> marker i x = k.
Proof.
  intros L. unfold row. rewrite <- at_head_typed. unfold at_head.
  assert (E : nth_error (context R n i) x = Some (marker i x, [])).
  { unfold context. rewrite nth_error_app1 by (rewrite prefix_length; lia).
    now apply prefix_lookup. }
  rewrite E. split.
  - intros (p & H & I). inversion H; subst p. now destruct I as [I|[]].
  - intros <-. eexists. split; [reflexivity|now left].
Qed.

Lemma rule_at R n i j r x U b :
  nth_error R j = Some r -> x < n ->
  (row R n i (rule_term n j x U) (cell b) <->
   exists a, action R r (marker i x) a b /\ row R n i U (cell a)).
Proof.
  intros E L. split.
  - change (row R n i (apps (var (n+4+j)) [var x;U]) (cell b) ->
      exists a, action R r (marker i x) a b /\ row R n i U (cell a)).
    intros H. apply atomic_spine, cell_case in H.
    destruct H as [(_ & F & _) | (j' & r' & k & a & X & V & J & F & E' & A & T & W)].
    + discriminate F.
    + inversion F; subst X V.
      assert (j' = j) as -> by lia. rewrite E in E'. inversion E'; subst r'.
      apply marker_var_at in T; [|exact L]. subst k. eauto.
  - intros (a & A & T). unfold rule_term, row in *.
    eapply type_assignment_app with (s := cell a) (phi := []); [|exact T|constructor].
    eapply type_assignment_app with (s := marker i x) (phi := []); [|apply marker_var_at; auto|constructor].
    apply head_typed. eapply head_rule; eassumption.
Qed.

Definition cells R n M (w : list nat) :=
  length w = S n /\
  forall i a, nth_error w i = Some a -> row R n i M (cell a).

Lemma nth_cons_pair p q (a b : nat) :
  nth_error (p ++ a::b::q) (length p) = Some a /\
  nth_error (p ++ a::b::q) (S (length p)) = Some b.
Proof.
  rewrite !nth_error_app2 by lia.
  replace (S (length p) - length p) with 1 by lia.
  rewrite Nat.sub_diag. auto.
Qed.

Lemma nth_other_pair p q (a b c d : nat) i :
  i <> length p -> i <> S (length p) ->
  nth_error (p ++ a::b::q) i = nth_error (p ++ c::d::q) i.
Proof.
  intros A B. destruct (lt_dec i (length p)) as [H|H].
  - now rewrite !nth_error_app1.
  - rewrite !nth_error_app2 by lia.
    replace (i - length p) with (S (S (i - length p - 2))) by lia. reflexivity.
Qed.

Lemma split_pair (w : list nat) x :
  S x < length w ->
  exists p a b q, w = p ++ a::b::q /\ length p = x.
Proof.
  revert w. induction x as [|x IH]; intros w H.
  - destruct w as [|a [|b q]]; cbn in H; try lia.
    exists [], a, b, q. auto.
  - destruct w as [|y w]; cbn in H; [lia|].
    destruct (IH w ltac:(lia)) as (p & a & b & q & -> & E).
    exists (y::p), a, b, q. cbn. auto.
Qed.

Lemma zero_cells R n w :
  cells R n (var (n+3)) w -> w = repeat 0 (S n).
Proof.
  intros [L H]. apply nth_error_ext. intros i.
  destruct (lt_dec i (S n)) as [I|I].
  - rewrite nth_error_repeat by exact I.
    destruct (nth_error w i) as [a|] eqn:E.
    + f_equal. apply zero_at with R n i. now apply H.
    + apply nth_error_None in E. lia.
  - rewrite (proj2 (nth_error_None w i)) by lia.
    symmetry. apply nth_error_None. rewrite repeat_length. lia.
Qed.

Lemma recover_step R n j r x U w :
  nth_error R j = Some r -> x < n ->
  cells R n (rule_term n j x U) w ->
  exists v, cells R n U v /\ step R v w.
Proof.
  intros E Hx [L T]. destruct r as [[a b] [c d]].
  destruct (split_pair w x ltac:(lia)) as (p & e & f & q & -> & Lp).
  subst x.
  destruct (nth_cons_pair p q e f) as [Ee Ef].
  pose proof (proj1 (rule_at R n _ j _ _ U _ E Hx) (T _ _ Ee)) as (aa & Aa & Ta).
  pose proof (proj1 (rule_at R n _ j _ _ U _ E Hx) (T _ _ Ef)) as (bb & Ab & Tb).
  rewrite marker_here in Aa. rewrite marker_next in Ab.
  inversion Aa; subst aa e. inversion Ab; subst bb f.
  exists (p ++ a::b::q). split.
  - split.
    + rewrite length_app in *. cbn in *. lia.
    + intros i z Ez. destruct (Nat.eq_dec i (length p)) as [->|A].
      * rewrite (proj1 (nth_cons_pair p q a b)) in Ez. inversion Ez; subst. exact Ta.
      * destruct (Nat.eq_dec i (S (length p))) as [->|B].
        -- rewrite (proj2 (nth_cons_pair p q a b)) in Ez. inversion Ez; subst. exact Tb.
        -- rewrite (nth_other_pair p q a b c d i A B) in Ez.
           destruct (proj1 (rule_at R n i j _ _ U z E Hx) (T _ _ Ez)) as (y & Ay & Ty).
           rewrite marker_outside in Ay by assumption. inversion Ay; subst. exact Ty.
  - constructor. eapply nth_error_In. exact E.
Qed.

Lemma normal_cells_sound R n M w :
  normal M -> cells R n M w -> multi_step R (repeat 0 (S n)) w.
Proof.
  revert w. induction M as [v|P IH_P Q IH_Q|M IH]; intros w H [L T];
    assert (E : exists b, nth_error w 0 = Some b) by (destruct w; cbn in *; [lia|eauto]);
    destruct E as [b E]; destruct (normal_cell R n 0 _ b H (T _ _ E))
      as [F|(j & r & x & U & J & X & F)]; try discriminate F.
  - injection F as ->. replace w with (repeat 0 (S n)); [apply rt_refl|].
    symmetry. apply (zero_cells R n). exact (conj L T).
  - unfold rule_term in F. inversion F; subst P U.
    destruct (recover_step R n j r x Q w J X (conj L T)) as (v & V & D).
    eapply rt_trans; [apply IH_Q; [eapply normal_arg; exact H|exact V]|apply rt_step, D].
Qed.

Lemma nth_repeat_value (w : nat) m i a :
  nth_error (repeat w m) i = Some a -> a = w.
Proof.
  intros E. assert (H : i < m).
  { rewrite <- (repeat_length w m). apply nth_error_Some. congruence. }
  rewrite nth_error_repeat in E by exact H. congruence.
Qed.

Lemma rule_alphabet R a b c d :
  In ((a,b),(c,d)) R ->
  In a (alphabet R) /\ In b (alphabet R) /\
  In c (alphabet R) /\ In d (alphabet R).
Proof.
  intros H. unfold alphabet. cbn [In]. repeat split.
  all: right; right; apply in_flat_map; exists ((a,b),(c,d)); split; [exact H|cbn; auto].
Qed.

Definition word_witness R n w :=
  Forall (fun z => In z (alphabet R)) w /\
  exists U, cells R n U w /\ row R n (S n) U (cell 0).

Lemma witness_zero R n : word_witness R n (repeat 0 (S n)).
Proof.
  split.
  - apply Forall_forall. intros z H. apply repeat_spec in H as ->. now left.
  - exists (var (n+3)). split.
    + split; [apply repeat_length|].
      intros i a H. apply nth_repeat_value in H as ->.
      apply head_typed, head_zero.
    + apply head_typed, head_zero.
Qed.

Lemma realize_step R n u v :
  step R u v -> word_witness R n u -> word_witness R n v.
Proof.
  intros D. destruct D as [p q a b c d E].
  intros [A (U & [L T] & Z)].
  pose proof (rule_alphabet R a b c d E) as (_ & _ & Ac & Ad).
  apply In_nth_error in E as [j J]. set (x := length p).
  assert (H : x < n) by (unfold x; rewrite length_app in L; cbn in L; lia).
  assert (Len : length (p ++ c::d::q) = S n).
  { rewrite length_app in *. cbn in *. lia. }
  apply Forall_app in A as [Ap Aq]. inversion Aq as [|? ? _ Aq']; subst.
  inversion Aq' as [|? ? _ Aqt]; subst.
  split.
  - apply Forall_app. split; [exact Ap|]. now constructor; [|constructor].
  - exists (rule_term n j x U). split.
    + split; [exact Len|].
      intros i z Ei. apply rule_at with (r := ((a,b),(c,d))); [exact J|exact H|].
      destruct (nth_cons_pair p q c d) as [Ec Ed].
      destruct (nth_cons_pair p q a b) as [Ea Eb].
      destruct (Nat.eq_dec i x) as [->|Lx].
      * unfold x in Ei. rewrite Ec in Ei. inversion Ei; subst z.
        exists a. rewrite marker_here. split; [constructor|now apply T].
      * destruct (Nat.eq_dec i (S x)) as [->|Ly].
        -- unfold x in Ei. rewrite Ed in Ei. inversion Ei; subst z.
           exists b. rewrite marker_next. split; [constructor|now apply T].
        -- rewrite <- (nth_other_pair p q a b c d i Lx Ly) in Ei.
           exists z. rewrite marker_outside by assumption. split; [|now apply T].
           apply action_other. eapply (proj1 (Forall_forall _ _) (proj2 (Forall_app _ _ _) (conj Ap Aq))).
           eapply nth_error_In, Ei.
    + apply rule_at with (r := ((a,b),(c,d))); [exact J|exact H|].
      exists 0. rewrite marker_outside by lia. split; [apply action_other; now left|exact Z].
Qed.

Lemma realize_rewriting R n w :
  multi_step R (repeat 0 (S n)) w -> word_witness R n w.
Proof.
  intros D. assert (H : word_witness R n (repeat 0 (S n))) by apply witness_zero.
  revert H. induction D; eauto using realize_step.
Qed.

(* Row zero is the newest position. A growth step pushes an index on
   every old row and creates a new row zero from the auxiliary row. *)
Definition phase i := match i with 0 => active | S _ => frozen end.

Definition generating R n M :=
  (forall i, i <= n -> row R n i M (phase i)) /\ row R n (S n) M reserve.

Lemma typing_lam_exact G U s l t :
  type_assignment G (lam U) (arr s l t) <->
  type_assignment ((s,l)::G) U t.
Proof. split; [inversion 1; assumption|apply type_assignment_arr]. Qed.

Lemma stop_cells R n i U :
  row R n i (app (var (n+2)) U) (phase i) -> row R n i U (cell 1).
Proof.
  change (row R n i (apps (var (n+2)) [U]) (phase i) -> row R n i U (cell 1)).
  destruct i; intros H; apply atomic_spine in H; inversion H; subst;
    try discriminate; try lia; assumption.
Qed.

Lemma grow_old R n i U :
  row R n i (app (var (n+1)) (lam U)) (phase i) ->
  row R (S n) (S i) U frozen.
Proof.
  change (row R n i (apps (var (n+1)) [lam U]) (phase i) -> row R (S n) (S i) U frozen).
  destruct i; intros H; apply atomic_spine in H; inversion H; subst;
    try discriminate; try lia; unfold row in *; rewrite context_push; eapply typing_lam_exact; eassumption.
Qed.

Lemma stopped_word R n U :
  (forall i, i <= n -> row R n i (app (var (n+2)) U) (phase i)) ->
  cells R n U (repeat 1 (S n)).
Proof.
  intros H. split; [apply repeat_length|].
  intros i a E. pose proof (nth_repeat_value _ _ _ _ E) as ->.
  apply stop_cells, H.
  assert (I : nth_error (repeat 1 (S n)) i <> None) by congruence.
  apply nth_error_Some in I. rewrite repeat_length in I. lia.
Qed.

Lemma reserve_case R n x args :
  atom_case R n (S n) x args reserve ->
  (exists U, x = n+2 /\ args = [U]) \/
  (exists U, x = n+1 /\ args = [U] /\
    row R n (S n) U (left_mark ~> active) /\
    row R n (S n) U (other_mark ~> reserve)).
Proof.
  intros C. inversion C; subst; try discriminate.
  - change ((if S n =? x then 4 else if S n =? S x then 5 else 6) = 3) in H.
    destruct (S n =? x), (S n =? S x); discriminate H.
  - right. exists U. auto.
  - left. exists U. auto.
Qed.

Lemma generation_view R n M :
  normal M -> generating R n M ->
  (exists U, M = app (var (n+2)) U /\ cells R n U (repeat 1 (S n))) \/
  (exists U, M = app (var (n+1)) (lam U) /\ generating R (S n) U).
Proof.
  intros H [F V].
  destruct (normal_atom_spine R n (S n) M _ H V) as (x & args & -> & C).
  apply reserve_case in C as [(U & -> & ->) | (N & -> & -> & A & B)].
  - left. exists U. split; [reflexivity|now apply stopped_word].
  - cbn [apps fold_left] in H, F |- *.
    destruct (normal_reserve_arrow R n (S n) N (normal_arg _ _ H) B) as (U & ->).
    unfold row in A, B. apply typing_lam_exact in A, B.
    right. exists U. split; [reflexivity|].
    split.
    + intros [|i] I.
      * unfold row. rewrite context_new. exact A.
      * apply grow_old, F. lia.
    + unfold row. rewrite context_push. exact B.
Qed.

Fixpoint term_size M :=
  match M with
  | var _ => 1
  | app M N => 1 + term_size M + term_size N
  | lam M => 1 + term_size M
  end.

Lemma generation_sound R n M :
  normal M -> generating R n M -> SSTS01 R.
Proof.
  revert n. pattern M. apply (well_founded_induction (well_founded_ltof _ term_size)).
  intros V IH n H G.
  destruct (generation_view R n V H G) as [(U & -> & C) | (U & -> & G')].
  - exists n. apply (normal_cells_sound R n U); [eapply normal_arg; exact H|exact C].
  - eapply (IH U).
    + unfold ltof. cbn. lia.
    + apply normal_body. eapply normal_arg. exact H.
    + exact G'.
Qed.

Lemma stop_complete R n U :
  cells R n U (repeat 1 (S n)) -> row R n (S n) U (cell 0) ->
  generating R n (app (var (n+2)) U).
Proof.
  intros [_ T] Z. split.
  - intros i I. assert (V := T i 1 (@nth_error_repeat nat 1 (S n) i ltac:(lia))).
    unfold row in *. destruct i.
    + eapply type_assignment_app with (phi := []); [apply head_typed, head_stop_active|exact V|constructor].
    + eapply type_assignment_app with (phi := []); [apply head_typed, head_stop_frozen|exact V|constructor].
  - unfold row in *. eapply type_assignment_app with (phi := []).
    + apply head_typed, head_stop_reserve.
    + exact Z.
    + constructor.
Qed.

Lemma grow_complete R n U :
  generating R (S n) U -> generating R n (app (var (n+1)) (lam U)).
Proof.
  intros [F V]. unfold row in *. split.
  - intros [|i] I.
    + eapply type_assignment_app with (phi := []).
      * apply head_typed, head_grow_active.
      * apply typing_lam_exact. specialize (F 1 ltac:(lia)).
        rewrite context_push in F. exact F.
      * constructor.
    + eapply type_assignment_app with (phi := []).
      * apply head_typed, head_grow_frozen.
      * apply typing_lam_exact. specialize (F (S (S i)) ltac:(lia)).
        rewrite context_push in F. exact F.
      * constructor.
  - eapply type_assignment_app with (phi := [other_mark ~> reserve]).
    + apply head_typed, head_grow_reserve.
    + apply typing_lam_exact. specialize (F 0 ltac:(lia)).
      rewrite context_new in F. exact F.
    + constructor; [|constructor]. apply typing_lam_exact.
      rewrite context_push in V. exact V.
Qed.

Lemma generating_at_zero R n :
  (exists M, generating R n M) -> exists M, generating R 0 M.
Proof.
  induction n as [|n IH]; intros (M & H).
  - eauto.
  - apply IH. eauto using grow_complete.
Qed.

Theorem reduction : SSTS01 ⪯ CD_INH.
Proof.
  exists (fun R => (constants R, goal_ty)). intros R. split.
  - intros (n & H). apply realize_rewriting in H as (_ & U & C & Z).
    assert (G : exists V, generating R n V) by (eexists; eauto using stop_complete).
    apply generating_at_zero in G as (V & A & B).
    exists (app (var 0) V).
    eapply type_assignment_app with (s := active) (phi := [reserve]).
    + apply (head_typed R 0 0), head_start.
    + exact (A 0 (Nat.le_refl 0)).
    + constructor; [exact B|constructor].
  - intros (M & T). apply typed_normal in T as (V & H & T).
    destruct (normal_atom_spine R 0 0 V _ H T) as (x & args & -> & C).
    inversion C; subst; try discriminate; try lia.
    eapply (generation_sound R 0); [eapply normal_arg; exact H|].
    split; [intros i I; replace i with 0 by lia|]; assumption.
Qed.
