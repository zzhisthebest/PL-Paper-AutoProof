From Fsub Require Import Fm_Definitions.
From Stdlib Require Import Lists.List Sorting.SetoidList FSets.FMapFacts Lia.
Import ListNotations.

Local Hint Constructors sealcomp sealcomp_rec_comp expr record_comp value
  value_record_comp red red_record_comp redm : seal.

Scheme sealcomp_ind_mut := Induction for sealcomp Sort Prop
with sealcomp_rec_ind_mut := Induction for sealcomp_rec_comp Sort Prop.
Combined Scheme sealcomp_mutind from sealcomp_ind_mut, sealcomp_rec_ind_mut.

Lemma seal_open_ee_rec :
  (forall e f, sealcomp e f -> forall k v w, sealcomp v w ->
    sealcomp (open_ee_rec k v e) (open_ee_rec k w f)) /\
  (forall r q, sealcomp_rec_comp r q -> forall k v w, sealcomp v w ->
    sealcomp_rec_comp (open_ee_record_rec k v r) (open_ee_record_rec k w q)).
Proof.
  apply sealcomp_mutind; intros; simpl; eauto with seal.
  destruct (k == n); eauto with seal.
Qed.

Lemma seal_open_te_rec :
  (forall e f, sealcomp e f -> forall k U,
    sealcomp (open_te_rec k U e) (open_te_rec k U f)) /\
  (forall r q, sealcomp_rec_comp r q -> forall k U,
    sealcomp_rec_comp (open_te_record_rec k U r) (open_te_record_rec k U q)).
Proof. apply sealcomp_mutind; intros; simpl; eauto with seal. Qed.

Lemma seal_open_ee : forall e f v w, sealcomp e f -> sealcomp v w ->
  sealcomp (open_ee e v) (open_ee f w).
Proof. unfold open_ee; intros; eapply (proj1 seal_open_ee_rec); eauto. Qed.

Lemma seal_open_te : forall e f U, sealcomp e f ->
  sealcomp (open_te e U) (open_te f U).
Proof. unfold open_te; intros; eapply (proj1 seal_open_te_rec); eauto. Qed.

Scheme expr_ind_mut := Induction for expr Sort Prop
with record_comp_ind_mut := Induction for record_comp Sort Prop.
Combined Scheme expr_mutind from expr_ind_mut, record_comp_ind_mut.

Lemma seal_expr :
  (forall f, expr f -> forall e, sealcomp e f -> expr e) /\
  (forall q, record_comp q -> forall r, sealcomp_rec_comp r q -> record_comp r).
Proof.
  apply expr_mutind; intros;
    match goal with
    | H : sealcomp _ _ |- _ => inversion H; subst; clear H
    | H : sealcomp_rec_comp _ _ |- _ => inversion H; subst; clear H
    end; eauto 4 with seal.
  - eapply expr_abs; eauto using seal_open_ee, sealcomp_fvar.
  - eapply expr_tabs; eauto using seal_open_te.
  - eapply expr_let; eauto using seal_open_ee, sealcomp_fvar.
Qed.

Lemma seal_body : forall e f, sealcomp e f -> body_e f -> body_e e.
Proof.
  intros e f H [L HL]. exists L. intros.
  eapply (proj1 seal_expr); eauto using seal_open_ee, sealcomp_fvar.
Qed.

Lemma seal_rec_value : forall r q, sealcomp_rec_comp r q ->
  value_record_comp q -> r = q.
Proof.
  intros r q H; induction H; intros V; inversion V; subst; f_equal; auto.
Qed.

Lemma seal_value : forall e f, sealcomp e f -> value f -> value e.
Proof.
  intros e f H; induction H; intros V; inversion V; subst; eauto 4 with seal.
  all: try solve [constructor; eapply (proj1 seal_expr); eauto with seal].
  all: match goal with
  | H : sealcomp_rec_comp _ _ |- _ =>
      rewrite (seal_rec_value _ _ H) by assumption; eauto with seal
  | H : sealcomp _ (exp_ref _) |- _ => inversion H; subst; constructor
  | H : sealcomp _ (exp_record _) |- _ =>
      inversion H; subst;
      match goal with C : sealcomp_rec_comp _ _ |- _ =>
        rewrite (seal_rec_value _ _ C) by assumption; eauto with seal end
  end.
Qed.

Module SealMapFacts := WFacts_fun Label LabelMapImpl.

Lemma seal_key_membership : forall (s : store) l,
  In l (List.map fst (LabelMapImpl.elements s)) <->
  exists v, LabelMapImpl.MapsTo l v s.
Proof.
  intros s l; split.
  - rewrite List.in_map_iff. intros [[k v] [E H]]. simpl in E; subst k.
    exists v. apply LabelMapImpl.elements_2. apply In_InA; auto.
    split; [intros [x u]|intros [x u] [y w]|intros [x u] [y w] [z a]];
      unfold LabelMapImpl.eq_key_elt; simpl; intuition congruence.
  - intros [v H]. apply LabelMapImpl.elements_1 in H.
    apply InA_alt in H. destruct H as [[k w] [[E _] H]].
    apply List.in_map_iff. exists (k,w); simpl in *; auto.
Qed.

Lemma seal_fresh : forall s t, sealcomp_store s t ->
  fresh_label_for_store s = fresh_label_for_store t.
Proof.
  intros s t [H K]. apply Label.fresh_permute. intros l.
  rewrite !seal_key_membership. firstorder.
Qed.

Lemma seal_add : forall s t l v w, sealcomp_store s t -> sealcomp v w ->
  sealcomp_store (LabelMapImpl.add l v s) (LabelMapImpl.add l w t).
Proof.
  intros s t l v w [H K] C. split; intros k u M;
    destruct (Label.eq_dec l k) as [<-|NE].
  - assert (u = v) by (eapply SealMapFacts.MapsTo_fun; [exact M| apply LabelMapImpl.add_1; reflexivity]).
    subst. exists w. split; auto using LabelMapImpl.add_1.
  - apply LabelMapImpl.add_3 in M; auto.
    destruct (H _ _ M) as [z [Mz Cz]]. exists z.
    auto using LabelMapImpl.add_2.
  - assert (u = w) by (eapply SealMapFacts.MapsTo_fun; [exact M| apply LabelMapImpl.add_1; reflexivity]).
    subst. exists v. split; auto using LabelMapImpl.add_1.
  - apply LabelMapImpl.add_3 in M; auto.
    destruct (K _ _ M) as [z [Mz Cz]]. exists z.
    auto using LabelMapImpl.add_2.
Qed.

Lemma seal_wf_add : forall s l v, well_formed_store s -> value v ->
  well_formed_store (LabelMapImpl.add l v s).
Proof.
  intros s l v W V k w M. destruct (Label.eq_dec l k) as [<-|NE].
  - assert (w = v) by (eapply SealMapFacts.MapsTo_fun; [exact M| apply LabelMapImpl.add_1; reflexivity]).
    congruence.
  - eapply W. eapply LabelMapImpl.add_3; eauto.
Qed.

Scheme red_ind_mut := Induction for red Sort Prop
with red_record_ind_mut := Induction for red_record_comp Sort Prop.
Combined Scheme red_mutind from red_ind_mut, red_record_ind_mut.

Local Hint Resolve seal_body seal_value seal_open_ee seal_open_te seal_add
  seal_wf_add : seal.
Definition seal_expr_lower := proj1 seal_expr.
Definition seal_rec_expr_lower := proj2 seal_expr.
Local Hint Resolve seal_expr_lower seal_rec_expr_lower : seal.

Lemma seal_backward_step :
  (forall f t f' t', red f t f' t' -> forall e s,
    sealcomp e f -> sealcomp_store s t -> well_formed_store s ->
    exists e' s', (red e s e' s' \/ (e = e' /\ s = s' /\ seal_count f' < seal_count f)) /\
      sealcomp e' f' /\ sealcomp_store s' t' /\ well_formed_store s') /\
  (forall q t q' t', red_record_comp q t q' t' -> forall r s,
    sealcomp_rec_comp r q -> sealcomp_store s t -> well_formed_store s ->
    exists r' s', (red_record_comp r s r' s' \/ (r = r' /\ s = s' /\ seal_count_record q' < seal_count_record q)) /\
      sealcomp_rec_comp r' q' /\ sealcomp_store s' t' /\ well_formed_store s').
Proof.
  apply red_mutind; intros;
    match goal with
    | H : sealcomp _ _ |- _ => inversion H; subst; clear H
    | H : sealcomp_rec_comp _ _ |- _ => inversion H; subst; clear H
    end.
  all: try match goal with
  | IH : forall _ _, _ -> _ -> _ -> exists _ _, _ |- _ =>
      let E := fresh "E" in let S := fresh "S" in let D := fresh "D" in
      let C := fresh "C" in let M := fresh "M" in let W := fresh "W" in
      edestruct IH as (E & S & D & C & M & W); [eassumption|eassumption|eassumption|];
      destruct D as [D|[-> [-> Less]]]; clear IH;
      solve [do 2 eexists; split; [left; solve [eauto 5 with seal]|];
             split; [solve [eauto 5 with seal]|]; split; assumption |
             do 2 eexists; split; [right; split; [reflexivity|split; [reflexivity|simpl in *; lia]]|];
             split; [solve [eauto 5 with seal]|]; split; assumption]
  end.
  all: try match goal with
  | H : sealcomp_rec_comp _ _, V : value_record_comp _ |- _ =>
      let E := fresh in pose proof (seal_rec_value _ _ H V) as E; subst; clear H
  end.
  all: try match goal with
  | H : sealcomp _ (exp_abs _ _) |- _ => inversion H; subst; clear H
  | H : sealcomp _ (exp_tabs _ _) |- _ => inversion H; subst; clear H
  | H : sealcomp _ (exp_ref _) |- _ => inversion H; subst; clear H
  | H : sealcomp _ (exp_record _) |- _ => inversion H; subst; clear H
  end.
  all: try match goal with
  | H : sealcomp _ (exp_seal _) |- _ => inversion H; subst; clear H
  end.
  all: try match goal with
  | H : sealcomp _ (exp_ref _) |- _ => inversion H; subst; clear H
  | H : sealcomp _ (exp_record _) |- _ => inversion H; subst; clear H
  end.
  all: try match goal with
  | H : sealcomp_rec_comp _ _, V : value_record_comp _ |- _ =>
      let E := fresh in pose proof (seal_rec_value _ _ H V) as E; subst
  end.
  all: try match goal with
  | M : LabelMapImpl.MapsTo ?l ?w ?t, S : sealcomp_store ?s ?t |- _ =>
    let v := fresh "v" in let B := fresh "B" in let C := fresh "C" in
    destruct (proj2 S _ _ M) as [v [B C]];
    assert (value v) by (eapply (fun W : well_formed_store s => W _ _ B); eassumption)
  end.
  all: try match goal with
  | S : sealcomp_store ?s ?t |- _ =>
      assert (fresh_label_for_store s = fresh_label_for_store t) by (apply seal_fresh; exact S)
  end.
  all: try solve [
    do 2 eexists; split; [left; solve [eauto 5 with seal]|];
    split; [solve [eauto 5 with seal]|]; split; eauto 5 with seal |
    do 2 eexists; split; [right; split; [reflexivity|split; [reflexivity|simpl in *; lia]]|];
    split; [solve [eauto 5 with seal]|]; split; eauto 5 with seal].

  - exists (exp_ref (fresh_label_for_store s1)),
      (LabelMapImpl.add (fresh_label_for_store s1) e1 s).
    split; [left; apply red_box_ref; eauto with seal; congruence|].
    split; [eauto with seal|]. split; eauto with seal.
  - exists (rec_ref a (fresh_label_for_store s1) r2),
      (LabelMapImpl.add (fresh_label_for_store s1) e1 s).
    split; [left; apply red_record_exp_2; eauto with seal; congruence|].
    split; [eauto with seal|]. split; eauto with seal.
Qed.

(* A presentation of subtyping with explicit laws for readonly types.
   These laws apply before as well as after type substitution. *)
Inductive seal_sub : env -> typ -> typ -> Prop :=
| ss_refl : forall E A, seal_sub E A A
| ss_top : forall E A, seal_sub E A typ_top
| ss_bound : forall E X A, binds X (bind_sub A) E -> seal_sub E X A
| ss_trans : forall E A B C, seal_sub E A B -> seal_sub E B C -> seal_sub E A C
| ss_arrow : forall E A B C D, seal_sub E C A -> seal_sub E B D ->
    seal_sub E (typ_arrow A B) (typ_arrow C D)
| ss_all : forall L E A B C D, seal_sub E C A ->
    (forall X : atom, X `notin` L ->
      seal_sub (X ~ bind_sub C ++ E) (open_tt B X) (open_tt D X)) ->
    seal_sub E (typ_all A B) (typ_all C D)
| ss_box : forall E A B, seal_sub E A B -> seal_sub E B A ->
    seal_sub E (typ_box A) (typ_box B)
| ss_ro : forall E A B, seal_sub E A B ->
    seal_sub E (typ_mut mut_readonly A) (typ_mut mut_readonly B)
| ss_promote : forall E A, seal_sub E A (typ_mut mut_readonly A)
| ss_left : forall E A B, seal_sub E (typ_int A B) A
| ss_right : forall E A B, seal_sub E (typ_int A B) B
| ss_both : forall E A B C, seal_sub E A B -> seal_sub E A C ->
    seal_sub E A (typ_int B C)
| ss_field : forall E a A B, seal_sub E A B -> seal_sub E B A ->
    seal_sub E (typ_record a A) (typ_record a B)
| ss_readonly_field : forall E a A B, seal_sub E A B ->
    seal_sub E (typ_mut mut_readonly (typ_record a A)) (typ_mut mut_readonly (typ_record a B))
| ss_arrow_ro : forall E A B,
    seal_sub E (typ_mut mut_readonly (typ_arrow A B)) (typ_arrow A B)
| ss_all_ro : forall E A B,
    seal_sub E (typ_mut mut_readonly (typ_all A B)) (typ_all A B)
| ss_flatten : forall E A,
    seal_sub E (typ_mut mut_readonly (typ_mut mut_readonly A)) (typ_mut mut_readonly A)
| ss_distribute : forall E A B,
    seal_sub E (typ_int (typ_mut mut_readonly A) (typ_mut mut_readonly B))
      (typ_mut mut_readonly (typ_int A B)).

Local Hint Constructors seal_sub : sealsub.
Local Hint Resolve ss_refl ss_top : core.

Lemma seal_sub_mono : forall E A B, seal_sub E A B ->
  forall F, (forall X U, binds X (bind_sub U) E -> binds X (bind_sub U) F) ->
  seal_sub F A B.
Proof.
  intros E A B D; induction D; intros F HF; eauto 4 with sealsub.
  eapply ss_all with (L := L); eauto.
  intros X HX. apply H0; [assumption|].
  intros Y U Bnd. apply binds_cons_iff in Bnd.
  destruct Bnd as [[-> ->]|Bnd]; auto using binds_cons_2, binds_cons.
Qed.

Lemma seal_sub_push : forall E A B x b, seal_sub E A B ->
  seal_sub (x ~ b ++ E) A B.
Proof. intros; eapply seal_sub_mono; eauto using binds_cons. Qed.

Lemma seal_sub_env : forall E A B, seal_sub E A B ->
  forall F, (forall X U, binds X (bind_sub U) E -> seal_sub F X U) ->
  seal_sub F A B.
Proof.
  intros E A B D; induction D; intros F HF; eauto 4 with sealsub.
  eapply ss_all with (L := L); eauto.
  intros X HX. apply H0; [assumption|].
  intros Y U Bnd. apply binds_cons_iff in Bnd.
  destruct Bnd as [[-> Einj]|Bnd].
  - injection Einj as ->. apply ss_bound; auto using binds_cons_2.
  - apply seal_sub_push; auto.
Qed.

Lemma seal_sub_narrow : forall E X A B S T, seal_sub E A B ->
  seal_sub (X ~ bind_sub B ++ E) S T ->
  seal_sub (X ~ bind_sub A ++ E) S T.
Proof.
  intros E X A B S T D H. eapply seal_sub_env; [exact H|].
  intros Y U Bnd. apply binds_cons_iff in Bnd.
  destruct Bnd as [[-> Einj]|Bnd].
  - injection Einj as ->. eapply ss_trans; [apply ss_bound; apply binds_cons_2; reflexivity|].
    apply seal_sub_push; assumption.
  - apply ss_bound; auto using binds_cons.
Qed.

Definition seal_equiv E A B := seal_sub E A B /\ seal_sub E B A.

Lemma seal_merge_equiv : forall E A,
  seal_equiv E (typ_mut mut_readonly A) (merge_mutability A mut_readonly).
Proof.
  intros E A; induction A; simpl; unfold seal_equiv in *;
    try solve [split; auto with sealsub].
  destruct m; split; auto with sealsub.
  destruct IHA1, IHA2. split.

  - apply ss_both.
    + eapply ss_trans; [apply ss_ro, ss_left|eassumption].
    + eapply ss_trans; [apply ss_ro, ss_right|eassumption].
  - eapply ss_trans; [|apply ss_distribute].
    apply ss_both.
    + eapply ss_trans; [apply ss_left|eassumption].
    + eapply ss_trans; [apply ss_right|eassumption].
Qed.

Lemma seal_merge_open_var : forall A k (X : atom),
  open_tt_rec k X (merge_mutability A mut_readonly) =
  merge_mutability (open_tt_rec k X A) mut_readonly.
Proof.
  induction A; intros; simpl; try reflexivity.
  - destruct (k == n); reflexivity.
  - now rewrite IHA1, IHA2.
Qed.

Lemma seal_norm_open_var : forall A k (X : atom),
  open_tt_rec k X (normal_form_typing A) =
  normal_form_typing (open_tt_rec k X A).
Proof.
  induction A; intros; simpl;
    try now rewrite ?IHA, ?IHA1, ?IHA2.
  - destruct (k == n); reflexivity.
  - destruct m. simpl. now rewrite seal_merge_open_var, IHA.
Qed.

Lemma seal_norm_equiv : forall E A, wf_typ E A ->
  seal_equiv E A (normal_form_typing A).
Proof.
  intros E A W; induction W; simpl; unfold seal_equiv in *;
    try solve [split; auto with sealsub];
    try match goal with H : _ /\ _ |- _ => destruct H end;
    try match goal with H : _ /\ _ |- _ => destruct H end;
    try solve [split; auto with sealsub].
  - split.
    + eapply ss_all with (L := L); auto.
      intros X HX. unfold open_tt. rewrite seal_norm_open_var.
      eapply seal_sub_narrow; [exact H2|]. exact (proj1 (H0 X HX)).
    + eapply ss_all with (L := L); auto.
      intros X HX. unfold open_tt. rewrite seal_norm_open_var.
      exact (proj2 (H0 X HX)).
  - split.
    + eapply ss_trans; [apply ss_ro; eassumption|apply seal_merge_equiv].
    + eapply ss_trans; [apply seal_merge_equiv|apply ss_ro; eassumption].
  - split; apply ss_both; eauto 5 with sealsub.
Qed.

Lemma seal_sub_relax : forall E A B, sub E A B -> seal_sub E A B.
Proof.
  intros E A B D; induction D; eauto 5 with sealsub.
  - eapply ss_trans; [apply seal_norm_equiv; eassumption|].
    eapply ss_trans; [eassumption|apply seal_norm_equiv; eassumption].
Qed.

(* Opening and substitution for the locally nameless syntax. *)
Scheme seal_exp_ind := Induction for exp Sort Prop
with seal_rec_ind := Induction for rec_comp Sort Prop.
Combined Scheme seal_syntax_ind from seal_exp_ind, seal_rec_ind.

Fixpoint seal_tmap (g : atom -> typ) (A : typ) : typ :=
  match A with
  | typ_fvar x => g x
  | typ_arrow A B => typ_arrow (seal_tmap g A) (seal_tmap g B)
  | typ_all A B => typ_all (seal_tmap g A) (seal_tmap g B)
  | typ_int A B => typ_int (seal_tmap g A) (seal_tmap g B)
  | typ_box A => typ_box (seal_tmap g A)
  | typ_record a A => typ_record a (seal_tmap g A)
  | typ_mut m A => typ_mut m (seal_tmap g A)
  | _ => A
  end.

Fixpoint seal_emap (g : atom -> exp) (h : typ -> typ) (e : exp) : exp :=
  match e with
  | exp_fvar x => g x
  | exp_abs T e => exp_abs (h T) (seal_emap g h e)
  | exp_app e f => exp_app (seal_emap g h e) (seal_emap g h f)
  | exp_tabs T e => exp_tabs (h T) (seal_emap g h e)
  | exp_tapp e T => exp_tapp (seal_emap g h e) (h T)
  | exp_let e f => exp_let (seal_emap g h e) (seal_emap g h f)
  | exp_box e => exp_box (seal_emap g h e)
  | exp_unbox e => exp_unbox (seal_emap g h e)
  | exp_set_box e f => exp_set_box (seal_emap g h e) (seal_emap g h f)
  | exp_seal e => exp_seal (seal_emap g h e)
  | exp_record r => exp_record (seal_rmap g h r)
  | exp_record_read e a => exp_record_read (seal_emap g h e) a
  | exp_record_write e a f => exp_record_write (seal_emap g h e) a (seal_emap g h f)
  | _ => e
  end
with seal_rmap (g : atom -> exp) (h : typ -> typ) (r : rec_comp) : rec_comp :=
  match r with
  | rec_exp a e r => rec_exp a (seal_emap g h e) (seal_rmap g h r)
  | rec_ref a l r => rec_ref a l (seal_rmap g h r)
  | rec_empty => rec_empty
  end.

Definition seal_replace {A : Type} (base : atom -> A) x (u : A) y :=
  if y === x then u else base y.
Definition seal_tsubst x U := seal_tmap (seal_replace typ_fvar x U).
Definition seal_tesubst x U := seal_emap exp_fvar (seal_tsubst x U).
Definition seal_eesubst x u := seal_emap (seal_replace exp_fvar x u) (fun T => T).

Fixpoint seal_tdepth k (T : typ) : Prop :=
  match T with
  | typ_bvar i => i < k
  | typ_all A B => seal_tdepth k A /\ seal_tdepth (S k) B
  | typ_int A B | typ_arrow A B => seal_tdepth k A /\ seal_tdepth k B
  | typ_box A | typ_record _ A | typ_mut _ A => seal_tdepth k A
  | _ => True
  end.

Fixpoint seal_edepth k j (e : exp) : Prop :=
  match e with
  | exp_bvar i => i < k
  | exp_abs T e => seal_tdepth j T /\ seal_edepth (S k) j e
  | exp_tabs T e => seal_tdepth j T /\ seal_edepth k (S j) e
  | exp_tapp e T => seal_edepth k j e /\ seal_tdepth j T
  | exp_let e f => seal_edepth k j e /\ seal_edepth (S k) j f
  | exp_app e f | exp_set_box e f | exp_record_write e _ f =>
      seal_edepth k j e /\ seal_edepth k j f
  | exp_box e | exp_unbox e | exp_seal e | exp_record_read e _ => seal_edepth k j e
  | exp_record r => seal_rdepth k j r
  | _ => True
  end
with seal_rdepth k j (r : rec_comp) : Prop :=
  match r with
  | rec_empty => True
  | rec_exp _ e r => seal_edepth k j e /\ seal_rdepth k j r
  | rec_ref _ _ r => seal_rdepth k j r
  end.

Lemma seal_tdepth_open : forall T k (X : atom),
  seal_tdepth k (open_tt_rec k X T) -> seal_tdepth (S k) T.
Proof.
  induction T; intros; simpl in *; intuition eauto.
  destruct (k == n); simpl in *; lia.
Qed.

Lemma seal_tdepth_inert : forall T k U,
  seal_tdepth k T -> open_tt_rec k U T = T.
Proof.
  induction T; intros; simpl in *;
    try solve [intuition; f_equal; eauto].
  destruct (k == n); [lia|reflexivity].
Qed.

Lemma seal_type_depth : forall T, type T -> seal_tdepth 0 T.
Proof.
  intros T D; induction D; simpl; auto.
  split; auto. pick fresh X for L.
  eapply seal_tdepth_open. exact (H0 X ltac:(assumption)).
Qed.

Lemma seal_edepth_open :
  (forall e k j (x : atom),
    seal_edepth k j (open_ee_rec k x e) -> seal_edepth (S k) j e) /\
  (forall r k j (x : atom),
    seal_rdepth k j (open_ee_record_rec k x r) -> seal_rdepth (S k) j r).
Proof.
  apply seal_syntax_ind; intros; simpl in *; intuition eauto.
  destruct (k == n); simpl in *; lia.
Qed.

Lemma seal_etdepth_open :
  (forall e k j (X : atom),
    seal_edepth k j (open_te_rec j X e) -> seal_edepth k (S j) e) /\
  (forall r k j (X : atom),
    seal_rdepth k j (open_te_record_rec j X r) -> seal_rdepth k (S j) r).
Proof.
  apply seal_syntax_ind; intros; simpl in *; intuition eauto using seal_tdepth_open.
Qed.

Lemma seal_expr_depth :
  (forall e, expr e -> seal_edepth 0 0 e) /\
  (forall r, record_comp r -> seal_rdepth 0 0 r).
Proof.
  apply expr_mutind; intros; simpl; intuition eauto using seal_type_depth.
  - pick fresh x for L. eapply (proj1 seal_edepth_open); eauto.
  - pick fresh X for L. eapply (proj1 seal_etdepth_open); eauto.
  - pick fresh x for L. eapply (proj1 seal_edepth_open); eauto.
Qed.

Lemma seal_edepth_inert :
  (forall e k j u U, seal_edepth k j e ->
    open_ee_rec k u e = e /\ open_te_rec j U e = e) /\
  (forall r k j u U, seal_rdepth k j r ->
    open_ee_record_rec k u r = r /\ open_te_record_rec j U r = r).
Proof.
  apply seal_syntax_ind; intros; simpl in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: try solve [split; reflexivity].
  all: try solve [destruct (k == n); [lia|auto]].
  all: repeat match goal with
  | I : forall k j u U, seal_edepth k j ?e -> _, D : seal_edepth ?k ?j ?e |- _ =>
      destruct (I k j u U D); clear I
  | I : forall k j u U, seal_rdepth k j ?r -> _, D : seal_rdepth ?k ?j ?r |- _ =>
      destruct (I k j u U D); clear I
  end; split; f_equal; eauto using seal_tdepth_inert.
Qed.

Lemma seal_tdepth_mono : forall T i j, seal_tdepth i T -> i <= j -> seal_tdepth j T.
Proof.
  induction T; intros; simpl in *; intuition eauto with arith; lia.
Qed.

Lemma seal_edepth_mono :
  (forall e k j k' j', seal_edepth k j e -> k <= k' -> j <= j' -> seal_edepth k' j' e) /\
  (forall r k j k' j', seal_rdepth k j r -> k <= k' -> j <= j' -> seal_rdepth k' j' r).
Proof.
  apply seal_syntax_ind; intros; simpl in *;
    intuition eauto using seal_tdepth_mono with arith; lia.
Qed.

Definition seal_expr_open_id e (D : expr e) k j u U :=
  proj1 seal_edepth_inert e k j u U
    (proj1 seal_edepth_mono e 0 0 k j (proj1 seal_expr_depth e D)
      (Nat.le_0_l k) (Nat.le_0_l j)).

Lemma seal_type_open_id : forall T, type T -> forall k U, open_tt_rec k U T = T.
Proof.
  intros. apply seal_tdepth_inert.
  eapply seal_tdepth_mono; eauto using seal_type_depth, Nat.le_0_l.
Qed.

Lemma seal_tmap_open : forall g,
  (forall x k U, open_tt_rec k U (g x) = g x) ->
  forall T k U, seal_tmap g (open_tt_rec k U T) =
    open_tt_rec k (seal_tmap g U) (seal_tmap g T).
Proof.
  intros g G T. induction T; intros; simpl; try now rewrite ?IHT, ?IHT1, ?IHT2.
  - destruct (k == n); reflexivity.
Qed.

Lemma seal_emap_open_ee : forall g h,
  (forall x k u, open_ee_rec k u (g x) = g x) ->
  (forall e k u, seal_emap g h (open_ee_rec k u e) =
    open_ee_rec k (seal_emap g h u) (seal_emap g h e)) /\
  (forall r k u, seal_rmap g h (open_ee_record_rec k u r) =
    open_ee_record_rec k (seal_emap g h u) (seal_rmap g h r)).
Proof.
  intros g h G. apply seal_syntax_ind; intros; simpl;
    try now rewrite ?H, ?H0.
  - destruct (k == n); reflexivity.
  all: symmetry; apply G.
Qed.

Lemma seal_emap_open_te : forall g h,
  (forall x k U, open_te_rec k U (g x) = g x) ->
  (forall T k U, h (open_tt_rec k U T) = open_tt_rec k (h U) (h T)) ->
  (forall e k U, seal_emap g h (open_te_rec k U e) =
    open_te_rec k (h U) (seal_emap g h e)) /\
  (forall r k U, seal_rmap g h (open_te_record_rec k U r) =
    open_te_record_rec k (h U) (seal_rmap g h r)).
Proof.
  intros g h G F. apply seal_syntax_ind; intros; simpl;
    try now rewrite ?H, ?H0, ?F.
  all: symmetry; apply G.
Qed.

Local Ltac seal_var_replace :=
  unfold seal_replace; repeat match goal with
  | |- context [ ?x === ?y ] => destruct (x === y); try congruence
  end.

Lemma seal_ee_open_ee : forall x u, expr u -> forall k v e,
  seal_eesubst x u (open_ee_rec k v e) =
  open_ee_rec k (seal_eesubst x u v) (seal_eesubst x u e).
Proof.
  intros. refine (proj1 (seal_emap_open_ee _ _ _) e k v). intros.
  seal_var_replace; try reflexivity. apply (proj1 (seal_expr_open_id u H _ 0 _ typ_top)).
Qed.

Lemma seal_ee_open_te : forall x u, expr u -> forall k A e,
  seal_eesubst x u (open_te_rec k A e) = open_te_rec k A (seal_eesubst x u e).
Proof.
  intros. refine (proj1 (seal_emap_open_te _ _ _ _) e k A); intros; auto.
  seal_var_replace; try reflexivity. apply (proj2 (seal_expr_open_id u H 0 _ (exp_bvar 0) _)).
Qed.

Lemma seal_ts_open_tt : forall x U, type U -> forall k V T,
  seal_tsubst x U (open_tt_rec k V T) =
  open_tt_rec k (seal_tsubst x U V) (seal_tsubst x U T).
Proof.
  intros. apply seal_tmap_open. intros. seal_var_replace; try reflexivity.
  apply seal_type_open_id; assumption.
Qed.

Lemma seal_te_open_te : forall x U, type U -> forall k V e,
  seal_tesubst x U (open_te_rec k V e) =
  open_te_rec k (seal_tsubst x U V) (seal_tesubst x U e).
Proof.
  intros. refine (proj1 (seal_emap_open_te _ _ _ _) e k V); intros; auto using seal_ts_open_tt.
Qed.

Lemma seal_te_open_ee : forall x U k v e,
  seal_tesubst x U (open_ee_rec k v e) =
  open_ee_rec k (seal_tesubst x U v) (seal_tesubst x U e).
Proof. intros. refine (proj1 (seal_emap_open_ee _ _ _) e k v); reflexivity. Qed.

Fixpoint seal_ftv (T : typ) : atoms :=
  match T with
  | typ_fvar x => {{x}}
  | typ_all A B | typ_int A B | typ_arrow A B => seal_ftv A `union` seal_ftv B
  | typ_box A | typ_record _ A | typ_mut _ A => seal_ftv A
  | _ => {}
  end.

Fixpoint seal_fev (e : exp) : atoms :=
  match e with
  | exp_fvar x => {{x}}
  | exp_abs A e | exp_tabs A e | exp_tapp e A => seal_ftv A `union` seal_fev e
  | exp_app e f | exp_let e f | exp_set_box e f | exp_record_write e _ f =>
      seal_fev e `union` seal_fev f
  | exp_box e | exp_unbox e | exp_seal e | exp_record_read e _ => seal_fev e
  | exp_record r => seal_frv r
  | _ => {}
  end
with seal_frv (r : rec_comp) : atoms :=
  match r with
  | rec_exp _ e r => seal_fev e `union` seal_frv r
  | rec_ref _ _ r => seal_frv r
  | rec_empty => {}
  end.

Lemma seal_ts_fresh : forall T x U, x `notin` seal_ftv T -> seal_tsubst x U T = T.
Proof.
  unfold seal_tsubst. induction T; intros; simpl in *; f_equal;
    eauto using AtomSetImpl.union_2, AtomSetImpl.union_3.
  seal_var_replace. fsetdec.
Qed.

Lemma seal_es_fresh :
  (forall e x v, x `notin` seal_fev e -> seal_eesubst x v e = e) /\
  (forall r x v, x `notin` seal_frv r ->
    seal_rmap (seal_replace exp_fvar x v) (fun T => T) r = r).
Proof.
  unfold seal_eesubst. apply seal_syntax_ind; intros; simpl in *; f_equal;
    eauto using AtomSetImpl.union_2, AtomSetImpl.union_3.
  seal_var_replace. fsetdec.
Qed.

Lemma seal_te_fresh :
  (forall e x U, x `notin` seal_fev e -> seal_tesubst x U e = e) /\
  (forall r x U, x `notin` seal_frv r ->
    seal_rmap exp_fvar (seal_tsubst x U) r = r).
Proof.
  unfold seal_tesubst. apply seal_syntax_ind; intros; simpl in *; f_equal;
    eauto using seal_ts_fresh, AtomSetImpl.union_2, AtomSetImpl.union_3.
Qed.

Local Ltac seal_open_subst :=
  unfold open_tt, open_te, open_ee in *;
  try rewrite !seal_ts_open_tt in * by assumption;
  try rewrite !seal_te_open_te in * by assumption;
  try rewrite !seal_te_open_ee in *;
  try rewrite !seal_ee_open_te in * by assumption;
  try rewrite !seal_ee_open_ee in * by assumption.

Local Ltac seal_close_var :=
  repeat match goal with
  | H : context [seal_tsubst ?x ?U (typ_fvar ?y)] |- _ =>
      change (seal_tsubst x U (typ_fvar y)) with (seal_replace typ_fvar x U y) in H
  | H : context [seal_tesubst ?x ?U (exp_fvar ?y)] |- _ =>
      change (seal_tesubst x U (exp_fvar y)) with (exp_fvar y) in H
  | H : context [seal_eesubst ?x ?V (exp_fvar ?y)] |- _ =>
      change (seal_eesubst x V (exp_fvar y)) with (seal_replace exp_fvar x V y) in H
  end;
  unfold seal_replace in *; repeat match goal with
  | H : context [ ?y === ?x ] |- _ => destruct (y === x); try solve [fsetdec]
  end.

Local Ltac seal_specialize H :=
  lazymatch type of H with
  | ?P -> _ =>
      let K := fresh "Premise" in assert (K : P);
      [|specialize (H K); clear K]
  end.

Lemma seal_sub_tsubst : forall E A B, seal_sub E A B ->
  forall F x U, type U ->
  (forall Y T, binds Y (bind_sub T) E ->
    seal_sub F (seal_tsubst x U Y) (seal_tsubst x U T)) ->
  seal_sub F (seal_tsubst x U A) (seal_tsubst x U B).
Proof.
  intros E A B D; induction D; intros F x U HU HF;
    cbn [seal_tsubst seal_tmap]; fold (seal_tsubst x U); eauto 4 with sealsub.
  eapply ss_all with (L := L `union` {{x}}); eauto.
  intros Y HY.
  assert (Y `notin` L) as HY' by fsetdec.
  specialize (H0 Y HY' (Y ~ bind_sub (seal_tsubst x U C) ++ F) x U HU).
  seal_specialize H0.
  { intros Z T Bnd. apply binds_cons_iff in Bnd.
    destruct Bnd as [[-> EQ]|Bnd].
    - injection EQ as ->.
      change (seal_sub (Y ~ bind_sub (seal_tsubst x U C) ++ F)
        (seal_replace typ_fvar x U Y) (seal_tsubst x U C)).
      unfold seal_replace. destruct (Y === x); [fsetdec|].
      apply ss_bound. apply binds_cons_2; reflexivity.
    - apply seal_sub_push; auto. }
  seal_open_subst. seal_close_var. exact H0.
Qed.

Lemma seal_sub_instantiate_empty : forall L A B D U,
  type U -> seal_sub empty U A ->
  (forall X : atom, X `notin` L ->
    seal_sub (X ~ bind_sub A) (open_tt B X) (open_tt D X)) ->
  seal_sub empty (open_tt B U) (open_tt D U).
Proof.
  intros L A B D U HU SU H.
  pick fresh X for (L `union` seal_ftv A `union` seal_ftv B `union` seal_ftv D).
  assert (X `notin` L) as HX by fsetdec.
  specialize (H X HX).
  pose proof (seal_sub_tsubst _ _ _ H empty X U HU) as K.
  seal_specialize K.
  { intros Y T Bnd. apply binds_one_iff in Bnd. destruct Bnd as [-> E].
    injection E as ->. rewrite (seal_ts_fresh A X U) by fsetdec.
    change (seal_sub empty (seal_replace typ_fvar X U X) A).
    seal_var_replace. }
  seal_open_subst.
  rewrite (seal_ts_fresh B X U), (seal_ts_fresh D X U) in K by fsetdec.
  seal_close_var. exact K.
Qed.

(* Observable type components. The flag records whether a reference may be sealed. *)
Inductive seal_facet :=
| sf_arrow : typ -> typ -> seal_facet
| sf_all : typ -> typ -> seal_facet
| sf_box : bool -> typ -> seal_facet
| sf_field : bool -> atom -> typ -> seal_facet.

Definition seal_facet_ro c :=
  match c with
  | sf_box _ A => sf_box true A
  | sf_field _ a A => sf_field true a A
  | _ => c
  end.

Fixpoint seal_facets A : list seal_facet :=
  match A with
  | typ_arrow A B => [sf_arrow A B]
  | typ_all A B => [sf_all A B]
  | typ_box A => [sf_box false A]
  | typ_record a A => [sf_field false a A]
  | typ_int A B => seal_facets A ++ seal_facets B
  | typ_mut _ A => List.map seal_facet_ro (seal_facets A)
  | _ => []
  end.

Definition seal_flag_le b c := b = true -> c = true.

Definition seal_facet_sub c d :=
  match c, d with
  | sf_arrow A B, sf_arrow C D => seal_sub empty C A /\ seal_sub empty B D
  | sf_all A B, sf_all C D => seal_sub empty C A /\
      (forall U, type U -> seal_sub empty U C ->
        seal_sub empty (open_tt B U) (open_tt D U))
  | sf_box b A, sf_box c C => seal_flag_le b c /\ seal_sub empty A C /\ seal_sub empty C A
  | sf_field b a A, sf_field c a' C => a = a' /\ seal_flag_le b c /\
      seal_sub empty A C /\ (c = false -> seal_sub empty C A)
  | _, _ => False
  end.

Lemma seal_facet_refl : forall c, seal_facet_sub c c.
Proof. destruct c; simpl; unfold seal_flag_le; auto. Qed.

Lemma seal_facet_trans : forall a b c, seal_facet_sub a b ->
  seal_facet_sub b c -> seal_facet_sub a c.
Proof.
  intros x y z; destruct x, y, z; simpl; try tauto; unfold seal_flag_le.
  all: repeat match goal with z : bool |- _ => destruct z end.
  all: intuition (try congruence; eauto 6 using ss_trans).
Qed.

Lemma seal_facet_sub_ro : forall a b, seal_facet_sub a b ->
  seal_facet_sub (seal_facet_ro a) (seal_facet_ro b).
Proof.
  intros x y; destruct x, y; simpl; try tauto; unfold seal_flag_le;
    intuition discriminate.
Qed.

Lemma seal_facet_promote : forall c, seal_facet_sub c (seal_facet_ro c).
Proof.
  destruct c; simpl; unfold seal_flag_le; intuition (auto || discriminate).
Qed.

Lemma seal_facet_ro_idem : forall c, seal_facet_ro (seal_facet_ro c) = seal_facet_ro c.
Proof. destruct c; reflexivity. Qed.

Lemma seal_facets_sub : forall A B, seal_sub empty A B ->
  forall d, In d (seal_facets B) ->
    exists c, In c (seal_facets A) /\ seal_facet_sub c d.
Proof.
  intros A B H. remember (@nil (atom * binding)) as E.
  induction H; intros d IN; subst; simpl in *.
  - exists d; auto using seal_facet_refl.
  - contradiction.
  - apply binds_nil_iff in H; contradiction.
  - destruct (IHseal_sub2 eq_refl _ IN) as [b [IB BC]].
    destruct (IHseal_sub1 eq_refl _ IB) as [a [IA AB]].
    exists a; eauto using seal_facet_trans.
  - destruct IN as [<-|[]]. exists (sf_arrow A B). split; [left; reflexivity|simpl; auto].
  - destruct IN as [<-|[]]. exists (sf_all A B). split; [left; reflexivity|].
    simpl; split; auto. intros. eapply seal_sub_instantiate_empty; eauto.
  - destruct IN as [<-|[]]. exists (sf_box false A). split; [left; reflexivity|].
    simpl; unfold seal_flag_le; auto.
  - apply List.in_map_iff in IN. destruct IN as [c [<- IC]].
    destruct (IHseal_sub eq_refl _ IC) as [a [IA AB]].
    exists (seal_facet_ro a). split; auto using List.in_map, seal_facet_sub_ro.
  - apply List.in_map_iff in IN. destruct IN as [c [<- IC]].
    exists c. auto using seal_facet_promote.
  - exists d; auto using List.in_or_app, seal_facet_refl.
  - exists d; auto using List.in_or_app, seal_facet_refl.
  - apply List.in_app_or in IN; destruct IN; auto.
  - destruct IN as [<-|[]]. exists (sf_field false a A). split; [left; reflexivity|].
    simpl; unfold seal_flag_le; auto.
  - destruct IN as [<-|[]]. exists (sf_field true a A). split; [left; reflexivity|].
    simpl; unfold seal_flag_le; intuition discriminate.
  - exists d; auto using seal_facet_refl.
  - exists d; auto using seal_facet_refl.
  - exists d. split; [|apply seal_facet_refl].
    apply List.in_map_iff in IN. destruct IN as [c [<- IC]].
    rewrite <- seal_facet_ro_idem. auto using List.in_map.
  - rewrite List.map_app in IN. exists d; auto using seal_facet_refl.
Qed.

(* Typing with the explicit readonly laws. *)
Inductive seal_typing : env -> sig -> exp -> typ -> Prop :=
| st_var : forall E R x A, binds x (bind_typ A) E -> seal_typing E R x A
| st_abs : forall L E R A e B,
    (forall x : atom, x `notin` L ->
      seal_typing (x ~ bind_typ A ++ E) R (open_ee e x) B) ->
    seal_typing E R (exp_abs A e) (typ_arrow A B)
| st_app : forall E R e f A B,
    seal_typing E R e (typ_arrow A B) -> seal_typing E R f A ->
    seal_typing E R (exp_app e f) B
| st_tabs : forall L E R A e B,
    (forall X : atom, X `notin` L ->
      seal_typing (X ~ bind_sub A ++ E) R (open_te e X) (open_tt B X)) ->
    seal_typing E R (exp_tabs A e) (typ_all A B)
| st_tapp : forall E R e A B U,
    seal_typing E R e (typ_all A B) -> seal_sub E U A ->
    seal_typing E R (exp_tapp e U) (open_tt B U)
| st_sub : forall E R e A B, seal_typing E R e A -> seal_sub E A B -> seal_typing E R e B
| st_let : forall L E R e f A B,
    seal_typing E R e A ->
    (forall x : atom, x `notin` L ->
      seal_typing (x ~ bind_typ A ++ E) R (open_ee f x) B) ->
    seal_typing E R (exp_let e f) B
| st_box : forall E R e A, seal_typing E R e A -> seal_typing E R (exp_box e) (typ_box A)
| st_unbox : forall E R e A, seal_typing E R e (typ_box A) ->
    seal_typing E R (exp_unbox e) A
| st_set_box : forall E R e f A,
    seal_typing E R e (typ_box A) -> seal_typing E R f A ->
    seal_typing E R (exp_set_box e f) A
| st_ref : forall E R l A, Signatures.binds l (bind_sig A) R ->
    seal_typing E R (exp_ref l) (typ_box A)
| st_seal : forall E R e A, seal_typing E R e A ->
    seal_typing E R (exp_seal e) (typ_mut mut_readonly A)
| st_unbox_ro : forall E R e A,
    seal_typing E R e (typ_mut mut_readonly (typ_box A)) ->
    seal_typing E R (exp_unbox e) (typ_mut mut_readonly A)
| st_record : forall E R r A, seal_rtyping E R r A -> seal_typing E R (exp_record r) A
| st_read : forall E R e a A, seal_typing E R e (typ_record a A) ->
    seal_typing E R (exp_record_read e a) A
| st_read_ro : forall E R e a A,
    seal_typing E R e (typ_mut mut_readonly (typ_record a A)) ->
    seal_typing E R (exp_record_read e a) (typ_mut mut_readonly A)
| st_write : forall E R e a f A,
    seal_typing E R e (typ_record a A) -> seal_typing E R f A ->
    seal_typing E R (exp_record_write e a f) A
with seal_rtyping : env -> sig -> rec_comp -> typ -> Prop :=
| st_r_empty : forall E R, seal_rtyping E R rec_empty typ_top
| st_r_exp : forall E R a e r A B, a `notin` record_dom r ->
    seal_rtyping E R r B -> seal_typing E R e A ->
    seal_rtyping E R (rec_exp a e r) (typ_int (typ_record a A) B)
| st_r_ref : forall E R a l r A B, a `notin` record_dom r ->
    seal_rtyping E R r B -> Signatures.binds l (bind_sig A) R ->
    seal_rtyping E R (rec_ref a l r) (typ_int (typ_record a A) B).

Scheme seal_typing_ind_mut := Induction for seal_typing Sort Prop
with seal_rtyping_ind_mut := Induction for seal_rtyping Sort Prop.
Combined Scheme seal_typing_mutind from seal_typing_ind_mut, seal_rtyping_ind_mut.
Scheme typing_ind_mut := Induction for typing Sort Prop
with typing_record_ind_mut := Induction for typing_record_comp Sort Prop.
Combined Scheme typing_mutind from typing_ind_mut, typing_record_ind_mut.

Local Hint Constructors seal_typing seal_rtyping : sealtype.

Lemma seal_typing_relax :
  (forall E R e A, typing E R e A -> seal_typing E R e A) /\
  (forall E R r A, typing_record_comp E R r A -> seal_rtyping E R r A).
Proof.
  apply typing_mutind; intros; eauto 4 using seal_sub_relax with sealtype.
Qed.

Definition seal_sig_le (R Q : sig) :=
  forall l A, Signatures.binds l (bind_sig A) R -> Signatures.binds l (bind_sig A) Q.

Lemma seal_sig_le_refl : forall R, seal_sig_le R R.
Proof. firstorder. Qed.

Lemma seal_sig_le_push : forall R l A, seal_sig_le R (l ~ bind_sig A ++ R).
Proof. unfold seal_sig_le; auto using Signatures.binds_cons_3. Qed.

Definition seal_env_le (E F : env) := forall x b, binds x b E -> binds x b F.

Lemma seal_env_le_cons : forall E F x b, seal_env_le E F ->
  seal_env_le (x ~ b ++ E) (x ~ b ++ F).
Proof.
  unfold seal_env_le; intros E F x b INC y a B.
  apply binds_cons_iff in B. destruct B as [[-> ->]|B]; auto using binds_cons, binds_cons_2.
Qed.

Lemma seal_typing_mono :
  (forall E R e A, seal_typing E R e A -> forall F Q,
    seal_env_le E F -> seal_sig_le R Q -> seal_typing F Q e A) /\
  (forall E R r A, seal_rtyping E R r A -> forall F Q,
    seal_env_le E F -> seal_sig_le R Q -> seal_rtyping F Q r A).
Proof.
  apply seal_typing_mutind; intros; unfold seal_sig_le in *;
    eauto 5 using seal_sub_mono, seal_env_le_cons with sealtype.
Qed.

Lemma seal_typed_push : forall E R e A x b, seal_typing E R e A ->
  seal_typing (x ~ b ++ E) R e A.
Proof. intros; eapply (proj1 seal_typing_mono); [eassumption| |apply seal_sig_le_refl].
  unfold seal_env_le; auto using binds_cons. Qed.

Definition seal_typing_sig := fun E R e A (D : seal_typing E R e A) Q =>
  proj1 seal_typing_mono E R e A D E Q (fun _ _ B => B).
Definition seal_rtyping_sig := fun E R r A (D : seal_rtyping E R r A) Q =>
  proj2 seal_typing_mono E R r A D E Q (fun _ _ B => B).

Lemma seal_record_dom_map : forall r g h, record_dom (seal_rmap g h r) = record_dom r.
Proof. induction r; intros; simpl; congruence. Qed.

Lemma seal_typing_esubst :
  (forall E R e A, seal_typing E R e A -> forall F x v,
    expr v ->
    (forall Y B, binds Y (bind_sub B) E -> binds Y (bind_sub B) F) ->
    (forall y B, binds y (bind_typ B) E -> seal_typing F R (seal_eesubst x v y) B) ->
    seal_typing F R (seal_eesubst x v e) A) /\
  (forall E R r A, seal_rtyping E R r A -> forall F x v,
    expr v ->
    (forall Y B, binds Y (bind_sub B) E -> binds Y (bind_sub B) F) ->
    (forall y B, binds y (bind_typ B) E -> seal_typing F R (seal_eesubst x v y) B) ->
    seal_rtyping F R (seal_rmap (seal_replace exp_fvar x v) (fun T => T) r) A).
Proof.
  apply seal_typing_mutind; intros;
    try solve [eauto 6 using seal_sub_mono with sealtype].
  all: cbn [seal_eesubst seal_emap seal_rmap]; fold (seal_eesubst x v);
    try rewrite seal_record_dom_map.
  all: try solve [eauto 5 using seal_sub_mono with sealtype].
  all: try solve [eapply st_r_exp; [rewrite seal_record_dom_map|..]; eauto |
                  eapply st_r_ref; [rewrite seal_record_dom_map|..]; eauto].
  all: first [eapply st_abs with (L := L `union` {{x}}) |
              eapply st_tabs with (L := L `union` {{x}}) |
              eapply st_let with (L := L `union` {{x}}); [eauto|]].
  all: intros y HY; assert (y `notin` L) as Fresh by fsetdec.
  all:
    lazymatch goal with
    | IH : forall z : atom, z `notin` ?LS -> forall _ _ _, _ |- _ =>
        let D := fresh "D" in
        lazymatch goal with |- seal_typing ?FE _ _ _ =>
          assert (D := IH y Fresh FE x v ltac:(assumption))
        end;
        seal_specialize D;
        [ intros Z BoundTy Bnd; apply binds_cons_iff in Bnd;
          destruct Bnd as [[-> ->]|Bnd]; auto using binds_cons_2, binds_cons
        | seal_specialize D;
          [ intros qv BoundTy Bnd; apply binds_cons_iff in Bnd;
            destruct Bnd as [[-> EQ]|Bnd];
            [ first [solve [discriminate EQ] |
                injection EQ as ->; simpl; unfold seal_replace;
                destruct (y === x); [fsetdec|apply st_var; apply binds_cons_2; reflexivity]]
            | apply seal_typed_push; auto ]
          | seal_open_subst; seal_close_var; exact D ]]
    end.
Qed.

Lemma seal_typed_open_ee : forall L R A B e v,
  expr v -> seal_typing empty R v A ->
  (forall x : atom, x `notin` L ->
    seal_typing (x ~ bind_typ A) R (open_ee e x) B) ->
  seal_typing empty R (open_ee e v) B.
Proof.
  intros L R A B e v V T H. pick fresh x for (L `union` seal_fev e).
  assert (x `notin` L) as F by fsetdec.
  pose proof (proj1 seal_typing_esubst _ _ _ _ (H x F) empty x v V) as D.
  seal_specialize D.
  { intros Y U K. apply binds_one_2 in K. discriminate. }
  seal_specialize D.
  { intros y U K. apply binds_one_iff in K. destruct K as [-> EQ].
    injection EQ as ->. simpl. unfold seal_replace.
    destruct (x === x); congruence. }
  seal_open_subst. rewrite (proj1 seal_es_fresh e x v) in D by fsetdec.
  seal_close_var. exact D.
Qed.

Lemma seal_typing_tsubst :
  (forall E R e A, seal_typing E R e A -> forall F Q X U,
    type U ->
    (forall Y B, binds Y (bind_sub B) E ->
      seal_sub F (seal_tsubst X U Y) (seal_tsubst X U B)) ->
    (forall y B, binds y (bind_typ B) E -> binds y (bind_typ (seal_tsubst X U B)) F) ->
    (forall l B, Signatures.binds l (bind_sig B) R ->
      Signatures.binds l (bind_sig (seal_tsubst X U B)) Q) ->
    seal_typing F Q (seal_tesubst X U e) (seal_tsubst X U A)) /\
  (forall E R r A, seal_rtyping E R r A -> forall F Q X U,
    type U ->
    (forall Y B, binds Y (bind_sub B) E ->
      seal_sub F (seal_tsubst X U Y) (seal_tsubst X U B)) ->
    (forall y B, binds y (bind_typ B) E -> binds y (bind_typ (seal_tsubst X U B)) F) ->
    (forall l B, Signatures.binds l (bind_sig B) R ->
      Signatures.binds l (bind_sig (seal_tsubst X U B)) Q) ->
    seal_rtyping F Q (seal_rmap exp_fvar (seal_tsubst X U) r) (seal_tsubst X U A)).
Proof.
  apply seal_typing_mutind; intros;
    try solve [eauto 6 using seal_sub_tsubst with sealtype].
  all: cbn [seal_tesubst seal_emap seal_rmap]; fold (seal_tesubst X U);
    try rewrite seal_record_dom_map.
  all: cbn [seal_tsubst seal_tmap]; fold (seal_tsubst X U).
  all: try solve [eauto 5 using seal_sub_tsubst with sealtype].
  all: try solve [unfold open_tt at 1; rewrite seal_ts_open_tt by assumption;
      eapply st_tapp; eauto using seal_sub_tsubst].
  all: try solve [eapply st_r_exp; [rewrite seal_record_dom_map|..]; eauto |
                  eapply st_r_ref; [rewrite seal_record_dom_map|..]; eauto].
  all: first [eapply st_abs with (L := L `union` {{X}}) |
              eapply st_tabs with (L := L `union` {{X}}) |
              eapply st_let with (L := L `union` {{X}}); [eauto|]].
  all: intros y HY; assert (y `notin` L) as Fresh by fsetdec.
  all:
    lazymatch goal with
    | IH : forall z : atom, z `notin` ?LS -> forall _ _ _ _, _ |- _ =>
        let D := fresh "D" in
        lazymatch goal with |- seal_typing ?FE _ _ _ =>
          assert (D := IH y Fresh FE Q X U ltac:(assumption))
        end;
        seal_specialize D;
        [ intros Z BoundTy Bnd; apply binds_cons_iff in Bnd;
          destruct Bnd as [[-> EQ]|Bnd];
          [ first [solve [discriminate EQ] |
              injection EQ as ->;
              lazymatch goal with |- seal_sub ?FE _ ?BT =>
                change (seal_sub FE (seal_replace typ_fvar X U y) BT)
              end;
              unfold seal_replace; destruct (y === X);
              [fsetdec|apply ss_bound; apply binds_cons_2; reflexivity]]
          | apply seal_sub_push; auto ]
        | seal_specialize D;
          [ intros qv BoundTy Bnd; apply binds_cons_iff in Bnd;
            destruct Bnd as [[-> EQ]|Bnd];
            [try discriminate EQ; injection EQ as ->; apply binds_cons_2; reflexivity|apply binds_cons; auto]
          | specialize (D ltac:(assumption)); seal_open_subst; seal_close_var; exact D ]]
    end.
Qed.

Fixpoint seal_fsig (R : sig) : atoms :=
  match R with
  | nil => {}
  | (_, bind_sig B) :: Q => seal_ftv B `union` seal_fsig Q
  end.

Lemma seal_fsig_notin : forall R X l T, X `notin` seal_fsig R ->
  Signatures.binds l (bind_sig T) R -> X `notin` seal_ftv T.
Proof.
  induction R as [|[k [B]] R IH]; intros X l T F D; simpl in F.
  - apply Signatures.binds_nil_iff in D; contradiction.
  - apply Signatures.binds_cons_iff in D.
    destruct D as [[-> EQ]|D].
    + injection EQ as ->. fsetdec.
    + eapply IH; [|eassumption]. fsetdec.
Qed.

Lemma seal_typed_open_te : forall L R A B e U,
  type U -> seal_sub empty U A ->
  (forall X : atom, X `notin` L ->
    seal_typing (X ~ bind_sub A) R (open_te e X) (open_tt B X)) ->
  seal_typing empty R (open_te e U) (open_tt B U).
Proof.
  intros L R A B e U W S H.
  pick fresh X for (L `union` seal_fev e `union` seal_ftv A `union` seal_ftv B `union` seal_fsig R).
  assert (X `notin` L) as F by fsetdec.
  pose proof (proj1 seal_typing_tsubst _ _ _ _ (H X F) empty R X U W) as D.
  seal_specialize D.
  { intros Y T K. apply binds_one_iff in K. destruct K as [-> EQ].
    injection EQ as ->. rewrite (seal_ts_fresh A X U) by fsetdec.
    change (seal_sub empty (seal_replace typ_fvar X U X) A).
    seal_var_replace. }
  seal_specialize D.
  { intros y T K. apply binds_one_2 in K. discriminate. }
  seal_specialize D.
  { intros l T K. rewrite seal_ts_fresh; auto.
    eapply seal_fsig_notin; [|exact K]. fsetdec. }
  seal_open_subst.
  rewrite (proj1 seal_te_fresh e X U), (seal_ts_fresh B X U) in D by fsetdec.
  seal_close_var. exact D.
Qed.

Definition seal_usable R e c :=
  match c with
  | sf_arrow A B => exists T b, e = exp_abs T b /\
      (forall v, expr v -> seal_typing empty R v A -> seal_typing empty R (open_ee b v) B)
  | sf_all A B => exists T b, e = exp_tabs T b /\
      (forall U, type U -> seal_sub empty U A ->
        seal_typing empty R (open_te b U) (open_tt B U))
  | sf_box ro A => exists l T,
      (e = exp_ref l \/ ro = true /\ e = exp_seal (exp_ref l)) /\
      Signatures.binds l (bind_sig T) R /\ seal_sub empty T A /\ seal_sub empty A T
  | sf_field ro a A => exists r l T,
      (e = exp_record r \/ ro = true /\ e = exp_seal (exp_record r)) /\
      value_record_comp r /\ record_lookup_ref a r = Some l /\
      Signatures.binds l (bind_sig T) R /\
      seal_sub empty T A /\ (ro = false -> seal_sub empty A T)
  end.

Lemma seal_usable_sub : forall R e c d, seal_facet_sub c d ->
  seal_usable R e c -> seal_usable R e d.
Proof.
  intros R e c d SS V; destruct c, d; simpl in *; try contradiction.
  - destruct SS as [S1 S2], V as (T & b & -> & H). exists T, b.
    split; auto. intros. eapply st_sub; [apply H; eauto using st_sub|assumption].
  - destruct SS as [S1 S2], V as (T & b & -> & H). exists T, b.
    split; auto. intros. eapply st_sub; [apply H; eauto using ss_trans|auto].
  - destruct SS as (F & S1 & S2), V as (l & T & H & K & D & U).
    exists l, T; unfold seal_flag_le in F; intuition eauto using ss_trans.
  - destruct SS as (-> & F & S1 & S2), V as (r & l & T & H & Vr & K & D & S & U).
    exists r, l, T; unfold seal_flag_le in F; intuition eauto using ss_trans.
    eapply ss_trans; [exact H1|].
    apply U. destruct b; [specialize (F eq_refl); congruence|reflexivity].
Qed.

Lemma seal_usable_seal : forall R e c, value (exp_seal e) -> seal_usable R e c ->
  seal_usable R (exp_seal e) (seal_facet_ro c).
Proof.
  intros R e c V H. inversion V; subst; destruct c; simpl in *;
    try solve [destruct H as (? & ? & E & _); discriminate E].
  all: try solve [
    destruct H as (loc & T & [E|[_ E]] & K & S & D); inversion E; subst;
    exists loc, T; intuition discriminate].
  all: destruct H as (r0 & loc & T & [E|[_ E]] & V0 & K & M & S & D);
    try discriminate E.
  injection E as <-. exists r, loc, T; intuition discriminate.
Qed.

Lemma seal_lookup_in_dom : forall r a l,
  record_lookup_ref a r = Some l -> a `in` record_dom r.
Proof.
  induction r; intros; simpl in *; try discriminate.
  destruct (a0 === a); subst; [fsetdec|].
  apply AtomSetImpl.union_3; eauto.
Qed.

Lemma seal_rtyped_usable : forall R r A, seal_rtyping empty R r A ->
  value_record_comp r -> forall c, In c (seal_facets A) ->
  seal_usable R (exp_record r) c.
Proof.
  intros R r A D. remember (@nil (atom * binding)) as E.
  induction D; intros V c IN; subst; simpl in *; try contradiction.
  - inversion V.
  - inversion V; subst. destruct IN as [<-|IN].
    + simpl. exists (rec_ref a l r), l, A. repeat split; auto.
      simpl. destruct (a === a); congruence.
    + specialize (IHD eq_refl ltac:(eassumption) c IN).
      destruct c; simpl in *;
        try solve [destruct IHD as (? & ? & E & _); discriminate].
      * destruct IHD as (? & ? & [E|[_ E]] & _); discriminate.
      * destruct IHD as (r0 & k & T & [E|[_ E]] & Vr & K & Bnd & S & F);
          [injection E as <-|discriminate].
        exists (rec_ref a l r), k, T. repeat split; auto.
        simpl. destruct (a0 === a); subst; auto.
        exfalso. eapply H. eauto using seal_lookup_in_dom.
Qed.

Lemma seal_typed_usable : forall R e A, seal_typing empty R e A ->
  value e -> forall c, In c (seal_facets A) -> seal_usable R e c.
Proof.
  intros R e A D. remember (@nil (atom * binding)) as E.
  induction D; intros V c IN; subst.
  all: try solve [inversion V].
  - simpl in IN; destruct IN as [<-|[]].
    simpl. eexists; eexists. split; [reflexivity|].
    intros. eapply seal_typed_open_ee; eauto.
  - simpl in IN; destruct IN as [<-|[]].
    simpl. eexists; eexists. split; [reflexivity|].
    intros. eapply seal_typed_open_te; eauto.
  - destruct (seal_facets_sub _ _ H _ IN) as [d [ID SD]].
    eapply seal_usable_sub; eauto.
  - simpl in IN; destruct IN as [<-|[]].
    simpl. exists l, A. auto.
  - simpl in IN. apply List.in_map_iff in IN.
    destruct IN as [d [<- ID]]. apply seal_usable_seal; auto.
    eapply IHD; eauto; inversion V; subst; eauto with seal.
  - eapply seal_rtyped_usable; eauto. inversion V; assumption.
Qed.

Lemma seal_expr_raise :
  (forall e, expr e -> forall f, sealcomp e f -> expr f) /\
  (forall r, record_comp r -> forall q, sealcomp_rec_comp r q -> record_comp q).
Proof.
  apply expr_mutind; intros;
    match goal with
    | C : sealcomp ?e _ |- _ =>
        let EQ := fresh "EQ" in remember e as src eqn:EQ in C;
        induction C; inversion EQ; subst; eauto 4 with seal
    | C : sealcomp_rec_comp _ _ |- _ => inversion C; subst; eauto 4 with seal
    end.
  all: first [solve [eapply expr_abs with (L := L); eauto using seal_open_ee, sealcomp_fvar] |
              solve [eapply expr_tabs with (L := L); eauto using seal_open_te] |
              solve [eapply expr_let with (L := L); eauto using seal_open_ee, sealcomp_fvar]].
Qed.

Lemma seal_value_expr :
  (forall e, value e -> expr e) /\
  (forall r, value_record_comp r -> record_comp r).
Proof.
  assert (forall r, value_record_comp r -> record_comp r) as W
    by (intros r V; induction V; eauto with seal).
  split; auto. intros e V; destruct V; eauto with seal.
Qed.

Definition seal_expr_of_value := proj1 seal_value_expr.
Definition seal_expr_of_rec_value := proj2 seal_value_expr.
Local Hint Resolve seal_expr_of_value seal_expr_of_rec_value : seal.

Lemma seal_red_source :
  (forall e s e' s', red e s e' s' -> expr e) /\
  (forall r s r' s', red_record_comp r s r' s' -> record_comp r).
Proof.
  apply red_mutind; intros; eauto 4 with seal.
  all: try match goal with H : body_e _ |- _ => destruct H as [L B]; eapply expr_let; eauto with seal end.
  all: eauto 6 with seal.
Qed.

Lemma seal_typing_wf_sig :
  (forall E R e A, typing E R e A -> wf_sig E R) /\
  (forall E R r A, typing_record_comp E R r A -> wf_sig E R).
Proof. apply typing_mutind; auto. Qed.

Lemma seal_wf_sig_uniq : forall E R, wf_sig E R -> Signatures.uniq R.
Proof. intros E R W; induction W; constructor; auto. Qed.

Definition seal_runtime_store R s :=
  Signatures.uniq R /\ well_formed_store s /\
  (forall l T, Signatures.binds l (bind_sig T) R ->
    exists v, LabelMapImpl.MapsTo l v s /\ value v /\ seal_typing empty R v T).

Lemma seal_runtime_init : forall R s f A, typing_store empty R s ->
  typing empty R f A -> seal_runtime_store R s.
Proof.
  intros R s f A W D. split.
  - eapply seal_wf_sig_uniq. eapply (proj1 seal_typing_wf_sig); eauto.
  - split.
    + intros l v H. destruct (proj2 (W l) _ H) as [T [? _]]; assumption.
    + intros l T B. destruct (proj1 (W l) _ B) as [v [M [D' V]]].
      exists v. split; [exact M|]. split; [exact V|].
      exact (proj1 seal_typing_relax _ _ _ _ D').
Qed.

Lemma seal_runtime_fresh : forall R s, seal_runtime_store R s ->
  ~ LabelSetImpl.In (fresh_label_for_store s) (Signatures.dom R).
Proof.
  intros R s (_ & _ & H) B. apply Signatures.binds_In_inv in B.
  destruct B as [[T] B]. destruct (H _ _ B) as [v [M _]].
  apply (Label.fresh_not_in (List.map fst (LabelMapImpl.elements s))).
  apply seal_key_membership. eauto.
Qed.

Lemma seal_runtime_alloc : forall R s v A l, seal_runtime_store R s ->
  l = fresh_label_for_store s -> value v -> seal_typing empty R v A ->
  seal_runtime_store (l ~ bind_sig A ++ R) (LabelMapImpl.add l v s).
Proof.
  intros R s v A l W -> V D.
  pose proof (seal_runtime_fresh _ _ W) as F.
  destruct W as (Un & W & H). split; auto using Signatures.uniq_cons_3.
  split; eauto using seal_wf_add.
  intros k T B. apply Signatures.binds_cons_iff in B.
  destruct B as [[<- EQ]|B].
  - injection EQ as <-. exists v. repeat split; auto using LabelMapImpl.add_1.
    eapply seal_typing_sig; eauto using seal_sig_le_push.
  - destruct (H _ _ B) as (w & M & WV & WD). exists w.
    assert (fresh_label_for_store s <> k).
    { intros <-. eapply Signatures.binds_dom_contradiction; eauto. }
    repeat split; auto using LabelMapImpl.add_2.
    eapply seal_typing_sig; eauto using seal_sig_le_push.
Qed.

Lemma seal_runtime_update : forall R s v A l, seal_runtime_store R s ->
  Signatures.binds l (bind_sig A) R -> value v -> seal_typing empty R v A ->
  seal_runtime_store R (LabelMapImpl.add l v s).
Proof.
  intros R s v A l (Un & W & H) B V D.
  split; auto. split; eauto using seal_wf_add.
  intros k T K. destruct (Label.eq_dec l k) as [<-|NE].
  - assert (bind_sig A = bind_sig T) by (eapply Signatures.binds_unique; eauto).
    injection H0 as <-. exists v. auto using LabelMapImpl.add_1.
  - destruct (H _ _ K) as (w & M & WV & WD). exists w.
    auto using LabelMapImpl.add_2.
Qed.

Definition seal_advances R s e A :=
  value e \/ exists Q f t,
    red e s f t /\ seal_sig_le R Q /\ seal_runtime_store Q t /\ seal_typing empty Q f A.

Definition seal_radvances R s r A :=
  value_record_comp r \/ exists Q q t,
    red_record_comp r s q t /\ seal_sig_le R Q /\ seal_runtime_store Q t /\ seal_rtyping empty Q q A.

Local Hint Resolve seal_sig_le_refl seal_sig_le_push seal_runtime_alloc seal_runtime_update
  seal_typing_sig seal_rtyping_sig : sealtype.

Lemma seal_record_red_dom : forall r s q t, red_record_comp r s q t ->
  record_dom q = record_dom r.
Proof. intros r s q t H; induction H; simpl; congruence. Qed.

Local Ltac seal_progress_inv :=
  repeat match goal with
  | H : expr (exp_app _ _) |- _ => inversion H; clear H; subst
  | H : expr (exp_tapp _ _) |- _ => inversion H; clear H; subst
  | H : expr (exp_let _ _) |- _ => inversion H; clear H; subst
  | H : expr (exp_box _) |- _ => inversion H; clear H; subst
  | H : expr (exp_unbox _) |- _ => inversion H; clear H; subst
  | H : expr (exp_set_box _ _) |- _ => inversion H; clear H; subst
  | H : expr (exp_seal _) |- _ => inversion H; clear H; subst
  | H : expr (exp_record _) |- _ => inversion H; clear H; subst
  | H : expr (exp_record_read _ _) |- _ => inversion H; clear H; subst
  | H : expr (exp_record_write _ _ _) |- _ => inversion H; clear H; subst
  | H : record_comp (rec_exp _ _ _) |- _ => inversion H; clear H; subst
  | H : record_comp (rec_ref _ _ _) |- _ => inversion H; clear H; subst
  end.

Local Ltac seal_step_as Q f t :=
  right; exists Q, f, t;
  split; [|split; [|split]].

Local Ltac seal_step_same f :=
  match goal with
  | W : seal_runtime_store ?R ?s |- _ =>
      seal_step_as R f s; [|apply seal_sig_le_refl|exact W|]
  end.

Local Ltac seal_destruct_progress IH :=
  let V := fresh "V" in let Q := fresh "Q" in let f := fresh "f" in
  let t := fresh "t" in let H := fresh "Step" in let I := fresh "Inc" in
  let S := fresh "Store" in let T := fresh "Typed" in
  let P := fresh "P" in
  lazymatch goal with WS : seal_runtime_store _ ?s |- _ =>
    pose proof (IH eq_refl s WS ltac:(assumption)) as P
  end;
  destruct P as [V | (Q & f & t & H & I & S & T)].

Local Ltac seal_usable_get e c :=
  let P := fresh "Can" in
  let V := fresh "Val" in
  assert (V : value e) by assumption;
  match goal with
  | D : seal_typing empty ?R e ?T |- _ =>
    assert (P : seal_usable R e c) by
      (eapply seal_typed_usable; [exact D|exact V|simpl; auto])
  end;
  clear V; cbn [seal_usable] in P.

Local Ltac seal_runtime_wf :=
  match goal with H : seal_runtime_store _ _ |- well_formed_store _ => exact (proj1 (proj2 H)) end.

Local Ltac seal_lookup_payload :=
  match goal with
  | B : Signatures.binds ?l (bind_sig ?T) ?R, S : seal_runtime_store ?R ?s |- _ =>
    let v := fresh "v" in let M := fresh "Maps" in
    let V := fresh "Val" in let D := fresh "Typ" in
    destruct (proj2 (proj2 S) l T B) as (v & M & V & D)
  end.

Lemma seal_typed_advance :
  (forall E R e A, seal_typing E R e A -> E = empty -> forall s,
    seal_runtime_store R s -> expr e -> seal_advances R s e A) /\
  (forall E R r A, seal_rtyping E R r A -> E = empty -> forall s,
    seal_runtime_store R s -> record_comp r -> seal_radvances R s r A).
Proof.
  apply seal_typing_mutind; intros; subst; seal_progress_inv;
    match goal with W : seal_runtime_store _ ?s |- _ => rename s into heap end.
  - apply binds_nil_iff in b; contradiction.
  - left; auto with seal.
  - rename H into IH1, H0 into IH2.
    seal_destruct_progress IH1.
    + seal_destruct_progress IH2.
      * seal_usable_get e (sf_arrow A B).
        destruct Can as (L & b & -> & Body).
        seal_step_same (open_ee b f).
        -- apply red_abs; auto; seal_runtime_wf.
        -- apply Body; auto.
      * seal_step_as Q (exp_app e f0) t; eauto 5 with seal sealtype.
    + seal_step_as Q (exp_app f0 f) t; eauto 5 with seal sealtype.
  - left; auto with seal.
  - seal_destruct_progress H.
    + seal_usable_get e (sf_all A B).
      destruct Can as (L & b & -> & Body).
      seal_step_same (open_te b U).
      * apply red_tabs; auto; seal_runtime_wf.
      * auto.
    + seal_step_as Q (exp_tapp f U) t; eauto with seal sealtype.
  - seal_destruct_progress H.
    + left; auto.
    + seal_step_as Q f t; eauto with seal sealtype.
  - seal_destruct_progress H.
    + seal_step_same (open_ee f e).
      * apply red_let; auto; [seal_runtime_wf|].
        eexists; eassumption.
      * eapply seal_typed_open_ee; eauto.
    + seal_step_as Q (exp_let f0 f) t; eauto 6 with seal sealtype.
      * eapply red_let_1; eauto. eexists; eassumption.
  - seal_destruct_progress H.
    + set (l := fresh_label_for_store heap).
      seal_step_as (l ~ bind_sig A ++ R) (exp_ref l) (LabelMapImpl.add l e heap).
      * apply red_box_ref; auto; seal_runtime_wf.
      * apply seal_sig_le_push.
      * eapply seal_runtime_alloc; eauto.
      * apply st_ref. apply Signatures.binds_cons_2; reflexivity.
    + seal_step_as Q (exp_box f) t; eauto with seal sealtype.
  - seal_destruct_progress H.
    + seal_usable_get e (sf_box false A).
      destruct Can as (l & T & [->|[No ?]] & Bd & Lo & Hi); [|discriminate].
      seal_lookup_payload.
      seal_step_same v.
      * eapply red_unbox_ref; eauto; seal_runtime_wf.
      * eauto with sealtype.
    + seal_step_as Q (exp_unbox f) t; eauto with seal sealtype.
  - rename H into IH1, H0 into IH2.
    seal_destruct_progress IH1.
    + seal_destruct_progress IH2.
      * seal_usable_get e (sf_box false A).
        destruct Can as (l & T & [->|[No ?]] & Bd & Lo & Hi); [|discriminate].
        seal_lookup_payload.
        seal_step_as R v (LabelMapImpl.add l f heap).
        -- eapply red_set_box_ref; eauto; seal_runtime_wf.
        -- apply seal_sig_le_refl.
        -- eapply seal_runtime_update; eauto with sealtype.
        -- eauto with sealtype.
      * seal_step_as Q (exp_set_box e f0) t; eauto 5 with seal sealtype.
    + seal_step_as Q (exp_set_box f0 f) t; eauto 5 with seal sealtype.
  - left; auto with seal.
  - seal_destruct_progress H.
    + inversion V; subst.
      all: try solve [left; eauto with seal].
      all: assert (well_formed_store heap) by seal_runtime_wf;
        match goal with
        | |- seal_advances _ _ (exp_seal ?v) _ => seal_step_same v
        end;
        [eauto 4 with seal|eapply st_sub; [eassumption|apply ss_promote]].
    + seal_step_as Q (exp_seal f) t; eauto with seal sealtype.
  - seal_destruct_progress H.
    + seal_usable_get e (sf_box true A).
      destruct Can as (l & T & [->|[_ ->]] & Bd & Lo & Hi); seal_lookup_payload.
      * seal_step_same v.
        -- eapply red_unbox_ref; eauto; seal_runtime_wf.
        -- eapply st_sub; [eapply st_sub; eauto|apply ss_promote].
      * seal_step_same (exp_seal v).
        -- eapply red_unbox_sealed_ref; eauto; seal_runtime_wf.
        -- apply st_seal. eauto with sealtype.
    + seal_step_as Q (exp_unbox f) t; eauto with seal sealtype.
  - seal_destruct_progress H.
    + left; auto with seal.
    + seal_step_as Q (exp_record f) t; eauto with seal sealtype.
  - seal_destruct_progress H.
    + seal_usable_get e (sf_field false a A).
      destruct Can as (r & l & T & [->|[No ?]] & Vr & Key & Bd & Lo & Hi); [|discriminate].
      seal_lookup_payload.
      seal_step_same v.
      * eapply red_record_read_ref; eauto; seal_runtime_wf.
      * eauto with sealtype.
    + seal_step_as Q (exp_record_read f a) t; eauto with seal sealtype.
  - seal_destruct_progress H.
    + seal_usable_get e (sf_field true a A).
      destruct Can as (r & l & T & [->|[_ ->]] & Vr & Key & Bd & Lo & Hi); seal_lookup_payload.
      * seal_step_same v.
        -- eapply red_record_read_ref; eauto; seal_runtime_wf.
        -- eapply st_sub; [eapply st_sub; eauto|apply ss_promote].
      * seal_step_same (exp_seal v).
        -- eapply red_sealed_record_read_ref; eauto; seal_runtime_wf.
        -- apply st_seal. eauto with sealtype.
    + seal_step_as Q (exp_record_read f a) t; eauto with seal sealtype.
  - rename H into IH1, H0 into IH2.
    seal_destruct_progress IH1.
    + seal_destruct_progress IH2.
      * seal_usable_get e (sf_field false a A).
        destruct Can as (r & l & T & [->|[No ?]] & Vr & Key & Bd & Lo & Hi); [|discriminate].
        seal_lookup_payload.
        seal_step_as R v (LabelMapImpl.add l f heap).
        -- eapply red_record_write_ref; eauto; seal_runtime_wf.
        -- apply seal_sig_le_refl.
        -- eapply seal_runtime_update; eauto with sealtype.
        -- eauto with sealtype.
      * seal_step_as Q (exp_record_write e a f0) t; eauto 5 with seal sealtype.
    + seal_step_as Q (exp_record_write f0 a f) t; eauto 5 with seal sealtype.
  - left; auto with seal.
  - seal_destruct_progress H0.
    + set (l := fresh_label_for_store heap).
      seal_step_as (l ~ bind_sig A ++ R) (rec_ref a l r) (LabelMapImpl.add l e heap).
      * apply red_record_exp_2; auto; seal_runtime_wf.
      * apply seal_sig_le_push.
      * eapply seal_runtime_alloc; eauto.
      * apply st_r_ref.
        -- assumption.
        -- eauto with sealtype.
        -- apply Signatures.binds_cons_2; reflexivity.
    + seal_step_as Q (rec_exp a f r) t; eauto 5 with seal sealtype.
  - seal_destruct_progress H.
    + left; auto with seal.
    + seal_step_as Q (rec_ref a l f) t; eauto with seal sealtype.
      eapply st_r_ref; eauto.
      rewrite (seal_record_red_dom _ _ _ _ Step). assumption.
Qed.

Lemma seal_value_irreducible :
  (forall e s f t, red e s f t -> value e -> False) /\
  (forall r s q t, red_record_comp r s q t -> value_record_comp r -> False).
Proof.
  apply red_mutind; intros;
    match goal with V : _ |- False =>
      solve [inversion V; subst; eauto with seal]
    end.
Qed.

Definition seal_value_no_red := proj1 seal_value_irreducible.
Definition seal_rec_value_no_red := proj2 seal_value_irreducible.

Lemma seal_red_deterministic :
  (forall e s f t, red e s f t -> forall g u, red e s g u -> f = g /\ t = u) /\
  (forall r s q t, red_record_comp r s q t ->
    forall p u, red_record_comp r s p u -> q = p /\ t = u).
Proof.
  apply red_mutind; intros;
    match goal with
    | D : red _ _ ?g ?u |- _ = ?g /\ _ = ?u => inversion D; subst; clear D
    | D : red_record_comp _ _ ?g ?u |- _ = ?g /\ _ = ?u => inversion D; subst; clear D
    end.
  all: try solve [split; reflexivity].
  all: try match goal with
  | D : red ?e ?s ?f ?t |- _ =>
      solve [exfalso; apply (seal_value_no_red e s f t D); eauto 4 with seal]
  | D : red_record_comp ?r ?s ?q ?t |- _ =>
      solve [exfalso; apply (seal_rec_value_no_red r s q t D); eauto 4 with seal]
  end.
  all: try match goal with
  | IH : forall f t, red ?e ?s f t -> _, D : red ?e ?s ?f ?t |- _ =>
      destruct (IH f t D); subst; split; reflexivity
  | IH : forall f t, red_record_comp ?e ?s f t -> _,
    D : red_record_comp ?e ?s ?f ?t |- _ =>
      destruct (IH f t D); subst; split; reflexivity
  end.
  all: repeat match goal with
  | M : LabelMapImpl.MapsTo ?l ?v ?s, N : LabelMapImpl.MapsTo ?l ?w ?s |- _ =>
      tryif constr_eq v w then fail else assert (v = w) by (eapply SealMapFacts.MapsTo_fun; eassumption); subst
  | M : record_lookup_ref ?a ?r = Some ?l, N : record_lookup_ref ?a ?r = Some ?k |- _ =>
      tryif constr_eq l k then fail else assert (l = k) by congruence; subst k
  end; split; reflexivity.
Qed.

Lemma seal_wf_store_lower : forall s t, sealcomp_store s t -> well_formed_store t ->
  well_formed_store s.
Proof.
  intros s t [H _] W l v M.
  destruct (H l v M) as [w [B C]].
  eapply seal_value; [exact C|exact (W l w B)].
Qed.

(* A replay step either follows the given trace or decreases the right-hand seal count. *)
Lemma seal_forward_replay : forall e s e' s',
  redm e s e' s' -> value e' -> forall f t R A,
  sealcomp e f -> sealcomp_store s t -> seal_runtime_store R t ->
  seal_typing empty R f A ->
  exists f' t', sealcomp e' f' /\ sealcomp_store s' t' /\ value f' /\ redm f t f' t'.
Proof.
  intros e s e' s' D.
  induction D as [e s e' s' Ee Es| e s u v e' s' Step D IH]; subst; intros V.
  all: assert (expr e') by eauto with seal.
  all: intros f t R A C M W T.
  all: remember (seal_count f) as n eqn:Count; revert f t R A C M W T Count;
    induction n as [n Fuel] using lt_wf_ind;
    intros f t R A C M W T Count.
  all: assert (expr f) as E by
    (eapply (proj1 seal_expr_raise); [|exact C]; first [eassumption|eapply (proj1 seal_red_source); eassumption]).
  all: destruct (proj1 seal_typed_advance _ _ _ _ T eq_refl _ W E)
    as [FV | (Q & f1 & t1 & FStep & Inc & W1 & T1)].
  - exists f,t. repeat (split; [assumption|]). constructor; reflexivity.
  - pose proof (seal_wf_store_lower _ _ M (proj1 (proj2 W))) as WS.
    destruct (proj1 seal_backward_step _ _ _ _ FStep _ _ C M WS)
      as (g & x & S & C1 & M1 & WS1).
    destruct S as [S|[<- [<- Less]]].
    + exfalso. eapply seal_value_no_red; eassumption.
    + destruct (Fuel (seal_count f1) ltac:(lia) f1 t1 Q A C1 M1 W1 T1 eq_refl)
        as (g & x & C2 & M2 & V2 & D2).
      exists g,x. repeat (split; [assumption|]). eapply redm_step; eassumption.
  - exfalso. eapply seal_value_no_red; [exact Step|eauto with seal].
  - pose proof (seal_wf_store_lower _ _ M (proj1 (proj2 W))) as WS.
    destruct (proj1 seal_backward_step _ _ _ _ FStep _ _ C M WS)
      as (g & x & S & C1 & M1 & WS1).
    destruct S as [S|[<- [<- Less]]].
    + destruct (proj1 seal_red_deterministic _ _ _ _ Step _ _ S) as [<- <-].
      destruct (IH V f1 t1 Q A C1 M1 W1 T1) as (g & x & C2 & M2 & V2 & D2).
      exists g,x. repeat (split; [assumption|]). eapply redm_step; eassumption.
    + destruct (Fuel (seal_count f1) ltac:(lia) f1 t1 Q A C1 M1 W1 T1 eq_refl)
        as (g & x & C2 & M2 & V2 & D2).
      exists g,x. repeat (split; [assumption|]). eapply redm_step; eassumption.
Qed.

Theorem safety_value_multistep : forall e s e' s' f ns R T,
  sealcomp_store s ns ->
  sealcomp e f ->
  redm e s e' s' ->
  value e' ->
  typing_store empty R ns ->
  typing empty R f T ->
  exists f' ns', sealcomp e' f' /\ sealcomp_store s' ns' /\ value f' /\ redm f ns f' ns'.
Proof.
  intros e s e' s' f ns R T M C D V W DT.
  exact (seal_forward_replay _ _ _ _ D V _ _ R T C M
    (seal_runtime_init R ns f T W DT) (proj1 seal_typing_relax _ _ _ _ DT)).
Qed.

Theorem safety_value_multistep' : forall e s f ns f' ns',
  expr f ->
  expr e ->
  well_formed_store s ->
  sealcomp_store s ns ->
  sealcomp e f ->
  redm f ns f' ns' ->
  value f' ->
  (exists e' s', redm e s e' s' /\ sealcomp_store s' ns' /\ sealcomp e' f' /\ value e').
Proof.
  intros e s f ns f' ns' _ _ W M C D V. revert e s W M C.
  induction D; intros u t W M C; subst.
  - exists u, t. split; [constructor; reflexivity|].
    split; [exact M|]. split; eauto with seal.
  - destruct (proj1 seal_backward_step _ _ _ _ H _ _ C M W)
      as (u1 & t1 & S & C1 & M1 & W1).
    destruct (IHD V u1 t1 W1 M1 C1) as (u2 & t2 & D2 & M2 & C2 & V2).
    exists u2, t2. split; [|auto].
    destruct S as [S|[-> [-> _]]]; eauto with seal.
Qed.
