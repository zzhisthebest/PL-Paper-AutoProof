Set Implicit Arguments.

Require Import LibExtra.

Require Import AbstractSyntax PreTyping Typing GeneralTyping RecordTypes InertTypes DefRecordInertTyping OperationalSemantics Effects Initialization InitTyping ConfigTyping.

From Stdlib Require Import List Lia.
Require Import StackTyping HeapUpdate HeapCorrespondence InitLookup InertInitContexts
  EffectCorrespondence HeapEffects HeapDefsPointsTo WellPointed FreeItems
  CommittedSubHeap FreeSubHeapSingle FreeSubHeapStack.
Existing Instance ty_heap_def.

(* Canonical forms in an inert type context. *)
Local Lemma inert_binding : forall G x T,
  inert G -> binds x T G -> inert_typ T.
Proof.
  intros G x T H. induction H; intro Hb.
  - false (binds_empty_inv Hb).
  - apply binds_concat_inv in Hb. destruct Hb as [Hb | [_ Hb]].
    + apply binds_single_inv in Hb. destruct Hb as [? ->]. assumption.
    + auto.
Qed.

Local Lemma open_record : forall R ls,
  record_typ R ls -> forall n x, record_typ (open_rec n x R) ls.
Proof.
  intros R ls H. induction H; intros n x; subst l.
  - destruct H; apply rt_one; first [apply rd_typ | apply rd_trm | reflexivity].
  - destruct H0; eapply rt_cons; try solve [eassumption | eauto | apply rd_typ | apply rd_trm | reflexivity].
Qed.

Local Lemma record_leaf : forall R ls D,
  record_typ R ls -> record_has R D -> record_dec D /\ label_of D \in ls.
Proof.
  intros R ls D Hr. induction Hr; intros HH; inversion HH; subst.
  - split; auto. apply in_singleton_self.
  - match goal with Hleaf : record_has T _ |- _ => destruct (IHHr Hleaf) end;
    split; auto. rewrite in_union; auto.
  - match goal with Hleaf : record_has (typ_rcd _) _ |- _ => inversion Hleaf; subst end.
    split; auto. rewrite in_union; right; apply in_singleton_self.
Qed.

Local Lemma record_unique : forall R ls D E,
  record_typ R ls -> record_has R D -> record_has R E ->
  label_of D = label_of E -> D = E.
Proof.
  intros R ls D E Hr. induction Hr; intros HD HE Eq;
    inversion HD; inversion HE; subst.
  - reflexivity.
  - eauto.
  - match goal with
    | H : record_has (typ_rcd _) _ |- _ => inversion H; subst
    end.
    exfalso. match goal with Hn : _ \notin _ |- _ => apply Hn end.
    rewrite <- Eq. eapply (proj2 (record_leaf Hr ltac:(eassumption))).
  - match goal with
    | H : record_has (typ_rcd _) _ |- _ => inversion H; subst
    end.
    exfalso. match goal with Hn : _ \notin _ |- _ => apply Hn end.
    rewrite Eq. eapply (proj2 (record_leaf Hr ltac:(eassumption))).
  - repeat match goal with H : record_has (typ_rcd _) _ |- _ => inversion H; subst; clear H end.
    reflexivity.
Qed.

Local Definition exact_member (G : ctx) x A T :=
  exists R, binds x (typ_bnd R) G /\ record_has (open x R) (dec_typ A T T).

Local Lemma exact_member_unique : forall G x A S T,
  inert G -> exact_member G x A S -> exact_member G x A T -> S = T.
Proof.
  intros G x A S T Hi [R [Hb Hs]] [R' [Hb' Ht]].
  assert (typ_bnd R = typ_bnd R') by (eapply binds_functional; eauto).
  injection H as <-.
  pose proof (inert_binding Hi Hb) as H. inversion H as [| |? [ls Hr]]; subst.
  pose proof (record_unique (open_record Hr 0 x) Hs Ht eq_refl) as E.
  congruence.
Qed.

Local Lemma record_project : forall G R D,
  record_has R D -> G ⊢ R <: typ_rcd D.
Proof.
  intros G R D H. induction H; eauto using subtyp_refl, subtyp_trans,
    subtyp_and11, subtyp_and12.
Qed.

Local Lemma exact_member_typing : forall G x A T,
  exact_member G x A T -> G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_typ A T T).
Proof.
  intros G x A T [R [Hb Hr]].
  eapply ty_sub; [eapply ty_rec_elim, ty_var; exact Hb | apply record_project; exact Hr].
Qed.

(* Function subtyping is kept as a sequence of steps. Each step can be
   instantiated at the actual argument, including its dependent result. *)
Inductive function_flow (G : ctx) : typ -> typ -> typ -> typ -> Prop :=
| function_flow_refl : forall S T, function_flow G S T S T
| function_flow_step : forall L S T S' T',
    G ⊢ S' <: S ->
    (forall x, x \notin L -> G & x ~ S' ⊢ open x T <: open x T') ->
    function_flow G S T S' T'
| function_flow_trans : forall S T S' T' S'' T'',
    function_flow G S T S' T' -> function_flow G S' T' S'' T'' ->
    function_flow G S T S'' T''.

Inductive exact_sub (G : ctx) : typ -> typ -> Prop :=
| es_top : forall T, exact_sub G T typ_top
| es_bot : forall T, exact_sub G typ_bot T
| es_refl : forall T, exact_sub G T T
| es_trans : forall S T U, exact_sub G S T -> exact_sub G T U -> exact_sub G S U
| es_and1 : forall T U, exact_sub G (typ_and T U) T
| es_and2 : forall T U, exact_sub G (typ_and T U) U
| es_and : forall S T U, exact_sub G S T -> exact_sub G S U ->
    exact_sub G S (typ_and T U)
| es_fld : forall a S1 S2 T1 T2, exact_sub G S2 S1 -> exact_sub G T1 T2 ->
    exact_sub G (typ_rcd (dec_trm a S1 T1)) (typ_rcd (dec_trm a S2 T2))
| es_typ : forall A S1 S2 T1 T2, exact_sub G S2 S1 -> exact_sub G T1 T2 ->
    exact_sub G (typ_rcd (dec_typ A S1 T1)) (typ_rcd (dec_typ A S2 T2))
| es_sel1 : forall x A T, exact_member G x A T -> exact_sub G (typ_sel (avar_f x) A) T
| es_sel2 : forall x A T, exact_member G x A T -> exact_sub G T (typ_sel (avar_f x) A)
| es_all : forall L S T S' T',
    G ⊢ S' <: S ->
    (forall x, x \notin L -> G & x ~ S' ⊢ open x T <: open x T') ->
    exact_sub G (typ_all S T) (typ_all S' T').

Local Lemma exact_sub_general : forall G S T,
  exact_sub G S T -> G ⊢ S <: T.
Proof.
  intros G S T H. induction H; eauto using subtyp_top, subtyp_bot, subtyp_refl,
    subtyp_trans, subtyp_and11, subtyp_and12, subtyp_and2, subtyp_fld,
    subtyp_typ, subtyp_all, subtyp_sel1, subtyp_sel2, exact_member_typing.
Qed.

(* Head observations follow intersections and exact type aliases. The
   inductive definition also covers aliases that refer back to themselves. *)
Inductive head (G : ctx) : typ -> typ -> Prop :=
| head_bot : head G typ_bot typ_bot
| head_rcd : forall D, head G (typ_rcd D) (typ_rcd D)
| head_all : forall S T, head G (typ_all S T) (typ_all S T)
| head_con : forall Ts is' T, head G (typ_con Ts is' T) (typ_con Ts is' T)
| head_bnd : forall T, head G (typ_bnd T) (typ_bnd T)
| head_and1 : forall S T A, head G S A -> head G (typ_and S T) A
| head_and2 : forall S T A, head G T A -> head G (typ_and S T) A
| head_sel : forall x A T B, exact_member G x A T ->
    head G T B -> head G (typ_sel (avar_f x) A) B.

Local Definition head_flow G S T : Prop :=
  match S, T with
  | typ_bot, _ => True
  | typ_rcd (dec_trm a S1 T1), typ_rcd (dec_trm b S2 T2) =>
      a = b /\ exact_sub G S2 S1 /\ exact_sub G T1 T2
  | typ_rcd (dec_typ a S1 T1), typ_rcd (dec_typ b S2 T2) =>
      a = b /\ exact_sub G S2 S1 /\ exact_sub G T1 T2
  | typ_all S1 T1, typ_all S2 T2 => function_flow G S1 T1 S2 T2
  | _, _ => S = T
  end.

Local Lemma head_flow_refl : forall G S, head_flow G S S.
Proof. intros G []; simpl; try destruct d; eauto using es_refl, function_flow_refl. Qed.

Local Lemma head_flow_trans : forall G S T U,
  head_flow G S T -> head_flow G T U -> head_flow G S U.
Proof.
  intros G S T U. destruct S, T, U; simpl; try destruct d; try destruct d0;
    try destruct d1; simpl; intros; try congruence;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    eauto 8 using es_trans, function_flow_trans.
  all: repeat split; try congruence; eauto using es_trans.
Qed.

Local Lemma exact_sub_heads : forall G S T,
  inert G -> exact_sub G S T -> forall B, head G T B ->
  exists A, head G S A /\ head_flow G A B.
Proof.
  intros G S T Hi H. induction H; intros B Hb.
  - inversion Hb.
  - exists typ_bot. split; [constructor|exact I].
  - exists B. auto using head_flow_refl.
  - destruct (IHexact_sub2 _ Hb) as [A [Ha Hab]].
    destruct (IHexact_sub1 _ Ha) as [C [Hc Hca]].
    eauto using head_flow_trans.
  - exists B. auto using head_and1, head_flow_refl.
  - exists B. auto using head_and2, head_flow_refl.
  - inversion Hb; subst; auto.
  - inversion Hb; subst. eexists; split; [constructor|simpl; auto].
  - inversion Hb; subst. eexists; split; [constructor|simpl; auto].
  - exists B. eauto using head_sel, head_flow_refl.
  - inversion Hb; subst. match goal with
    | Hm : exact_member G x A ?U, Ha : head G ?U B |- _ =>
      assert (T = U) by (eapply exact_member_unique; eauto); subst U;
      exists B; auto using head_flow_refl
    end.
  - inversion Hb; subst. eexists; split; [constructor|simpl; eauto using function_flow_step].
Qed.

Inductive observable : typ -> Prop :=
| obs_bot : observable typ_bot
| obs_rcd : forall D, observable (typ_rcd D)
| obs_all : forall S T, observable (typ_all S T)
| obs_con : forall Ts is' T, observable (typ_con Ts is' T).

Inductive observe (G : ctx) (x : var) : typ -> typ -> Prop :=
| observe_atom : forall T A, head G T A -> observable A -> observe G x T A
| observe_open : forall T R A, head G T (typ_bnd R) ->
    observe G x (open x R) A -> observe G x T A.

Local Lemma exact_sub_observe : forall G x S T,
  inert G -> exact_sub G S T -> forall B, observe G x T B ->
  exists A, observe G x S A /\ head_flow G A B.
Proof.
  intros G x S T Hi H B Ho. destruct Ho.
  - destruct (exact_sub_heads Hi H H0) as [C [Hc Hcb]].
    exists C. split; auto. apply observe_atom; auto.
    destruct C; simpl in Hcb; try constructor; try destruct d; destruct A;
      simpl in Hcb; try destruct d; try discriminate; inversion Hcb; subst; auto.
  - destruct (exact_sub_heads Hi H H0) as [C [Hc Hcb]].
    destruct C; simpl in Hcb; try destruct d; try discriminate.
    + exists typ_bot. auto using observe_atom, obs_bot.
    + injection Hcb as ->. eauto using observe_open, head_flow_refl.
Qed.

Inductive binding_atom (x : var) : typ -> typ -> Prop :=
| ba_all : forall S T, binding_atom x (typ_all S T) (typ_all S T)
| ba_con : forall Ts is' T, binding_atom x (typ_con Ts is' T) (typ_con Ts is' T)
| ba_record : forall R D, record_has (open x R) D ->
    binding_atom x (typ_bnd R) (typ_rcd D).

Local Lemma record_heads : forall G R ls A,
  record_typ R ls -> head G R A ->
  exists D, A = typ_rcd D /\ record_has R D.
Proof.
  intros G R ls A Hr. revert A. induction Hr; intros B Hb; inversion Hb; subst.
  - eauto using rh_one.
  - destruct (IHHr _ H5) as [E [-> He]]. eauto using rh_andl.
  - match goal with H : head _ (typ_rcd _) _ |- _ => inversion H; subst end.
    eauto using rh_one, rh_andr.
Qed.

Local Lemma inert_observe : forall G x T A,
  inert_typ T -> observe G x T A -> binding_atom x T A.
Proof.
  intros G x T A Hi Ho. destruct Hi as [S T | Ts is' T Hr | R [ls Hr]];
    inversion Ho; subst;
    repeat match goal with H : head _ (typ_all _ _) _ |- _ => inversion H; subst; clear H
      | H : head _ (typ_con _ _ _) _ |- _ => inversion H; subst; clear H
      | H : head _ (typ_bnd _) _ |- _ => inversion H; subst; clear H
      | H : observable (typ_bnd _) |- _ => inversion H
    end; try constructor.
  match goal with H : observe _ _ (open _ _) _ |- _ => inversion H; subst; clear H end.
  - match goal with Hh : head _ (open _ _) _ |- _ =>
      destruct (record_heads (open_record Hr 0 x) Hh) as [D [-> Hd]]
    end. constructor. exact Hd.
  - match goal with Hh : head _ (open _ _) _ |- _ =>
      destruct (record_heads (open_record Hr 0 x) Hh) as [? [E _]]; discriminate E
    end.
Qed.

Local Definition variable_shape G x T :=
  exists B, binds x B G /\
  forall A, observe G x T A ->
  exists C, binding_atom x B C /\ head_flow G C A.

Local Lemma variable_shape_and : forall G x S T,
  variable_shape G x S -> variable_shape G x T -> variable_shape G x (typ_and S T).
Proof.
  intros G x S T [B [Hb Hs]] [B' [Hb' Ht]].
  assert (B = B') by (eapply binds_functional; eauto). subst B'.
  exists B. split; auto. intros A H. inversion H; subst;
    match goal with Hh : head _ (typ_and _ _) _ |- _ => inversion Hh; subst end;
    eauto using observe_atom, observe_open.
Qed.

Local Lemma variable_shape_member : forall G x A S T,
  inert G -> variable_shape G x (typ_rcd (dec_typ A S T)) ->
  exists V, exact_member G x A V /\ exact_sub G S V /\ exact_sub G V T.
Proof.
  intros G x A S T Hi [B [Hb H]].
  destruct (H _ (observe_atom x (head_rcd G _) (obs_rcd _))) as [C [Hc Hf]].
  inversion Hc; subst; simpl in Hf; try discriminate.
  destruct D; simpl in Hf; try discriminate.
  destruct Hf as [-> [Hs Ht]].
  pose proof (inert_binding Hi Hb) as Hit. inversion Hit as [| |? [ls Hr]]; subst.
  destruct (record_leaf (open_record Hr 0 x) H0) as [Hd _].
  inversion Hd; subst. eexists; repeat split; try eassumption.
  unfold exact_member. eauto.
Qed.

Local Lemma exact_typing :
  (forall G t T, G ⊢ t ∶ T -> inert G ->
      forall x, t = trm_var (avar_f x) -> variable_shape G x T) /\
  (forall G (l : lit) T, G ⊢ l ∶ T -> True) /\
  (forall G S T, G ⊢ S <: T -> inert G -> exact_sub G S T) /\
  (forall G vs Ts, G ⊢ vs :: Ts -> True).
Proof.
  apply rules_mutind; intros; try discriminate; try exact I.
  all: try match goal with H : trm_var (avar_f _) = trm_var (avar_f _) |- _ => injection H as -> end.
  - eexists; split; [eassumption|].
    intros. eauto using inert_observe, inert_binding, head_flow_refl.
  - subst. match goal with
    | IH : inert _ -> forall _, trm_var _ = _ -> variable_shape _ _ (open _ _) |- _ =>
      destruct (IH ltac:(assumption) _ eq_refl) as [B [Hb Hs]]
    end.
    exists B. split; auto. intros A Ho. inversion Ho; subst;
      match goal with H : head _ (typ_bnd _) _ |- _ => inversion H; subst end;
      auto. match goal with H : observable (typ_bnd _) |- _ => inversion H end.
  - subst. match goal with
    | IH : inert _ -> forall _, trm_var _ = _ -> variable_shape _ _ (typ_bnd _) |- _ =>
      destruct (IH ltac:(assumption) _ eq_refl) as [B [Hb Hs]]
    end.
    exists B. split; auto. eauto using observe_open, head_bnd.
  - subst. eapply variable_shape_and; eauto.
  - subst. match goal with
    | IH : inert _ -> forall _, trm_var _ = _ -> variable_shape _ _ _ |- _ =>
      destruct (IH ltac:(assumption) _ eq_refl) as [B [Hb Hs]]
    end.
    exists B. split; auto. intros A Ho.
    destruct (exact_sub_observe H1 (H0 H1) Ho) as [C [Hc Hca]].
    destruct (Hs _ Hc) as [D [Hd Hdc]]. eauto using head_flow_trans.
  - apply es_top.
  - apply es_bot.
  - apply es_refl.
  - eauto using es_trans.
  - apply es_and1.
  - apply es_and2.
  - auto using es_and.
  - auto using es_fld.
  - auto using es_typ.
  - match goal with IH : inert _ -> forall z : var, trm_var _ = trm_var (avar_f z) -> variable_shape _ z _ |- _ =>
      destruct (variable_shape_member H0 (IH H0 x eq_refl))
        as [V [Hv [Hs Ht]]]
    end.
    eauto using es_trans, es_sel2.
  - match goal with IH : inert _ -> forall z : var, trm_var _ = trm_var (avar_f z) -> variable_shape _ z _ |- _ =>
      destruct (variable_shape_member H0 (IH H0 x eq_refl))
        as [V [Hv [Hs Ht]]]
    end.
    eauto using es_trans, es_sel1.
  - eauto using es_all.
Qed.

Local Lemma typed_variable_shape : forall G x T,
  inert G -> G ⊢ trm_var (avar_f x) ∶ T -> variable_shape G x T.
Proof. intros; eapply (proj1 exact_typing); eauto. Qed.

Local Lemma heap_entry : forall G Sigma x B,
  heap_correspond G Sigma -> binds x B G ->
  (exists l, binds x (item_lit l) Sigma /\ G ⊢ l ∶ B) \/
  (exists R hds, B = typ_bnd R /\ binds x (item_obj R hds) Sigma /\
    G ⊢ hds ∶ open x R).
Proof.
  intros G Sigma x B [_ H] Hb.
  specialize (H x (get_some_inv Hb)). inversion H; subst;
    match goal with H' : binds x ?C G |- _ =>
      assert (B = C) by (eapply binds_functional; [exact Hb | exact H']); subst
    end; eauto 10.
Qed.

Local Lemma canonical_function : forall G Sigma x S T,
  inert G -> heap_correspond G Sigma ->
  G ⊢ trm_var (avar_f x) ∶ typ_all S T ->
  exists S0 T0 t, binds x (item_lit (lit_fun S0 t)) Sigma /\
    G ⊢ lit_fun S0 t ∶ typ_all S0 T0 /\ function_flow G S0 T0 S T.
Proof.
  intros G Sigma x S T Hi Hheap Hty.
  destruct (typed_variable_shape Hi Hty) as [B [Hb H]].
  destruct (H _ (observe_atom x (head_all G S T) (obs_all S T))) as [C [Hc Hf]].
  inversion Hc; subst; simpl in Hf; try (destruct D; discriminate); try discriminate.
  destruct (heap_entry Hheap Hb) as [[l [Hl Htyl]] | [? [? [E _]]]]; try discriminate.
  inversion Htyl; subst. eauto 10.
Qed.

Local Lemma canonical_constructor : forall G Sigma x Ts is' T,
  inert G -> heap_correspond G Sigma ->
  G ⊢ trm_var (avar_f x) ∶ typ_con Ts is' T ->
  exists ds t, binds x (item_lit (lit_con Ts is' T ds t)) Sigma /\
    G ⊢ lit_con Ts is' T ds t ∶ typ_con Ts is' T.
Proof.
  intros G Sigma x Ts is' T Hi Hheap Hty.
  destruct (typed_variable_shape Hi Hty) as [B [Hb H]].
  destruct (H _ (observe_atom x (head_con G Ts is' T) (obs_con Ts is' T)))
    as [C [Hc Hf]].
  inversion Hc; subst; simpl in Hf; try (destruct D; discriminate); try discriminate.
  inversion Hf; subst.
  destruct (heap_entry Hheap Hb) as [[l [Hl Htyl]] | [? [? [E _]]]]; try discriminate.
  inversion Htyl; subst. eauto 10.
Qed.

Local Lemma heap_defs_field : forall G (hds : heap_defs) R a V,
  G ⊢ hds ∶ R -> record_has R (dec_trm a V V) ->
  exists o, labels_has hds (heap_def_trm a o) /\
    G ⊢ heap_def_trm a o ∶d dec_trm a V V.
Proof.
  intros G hds R a V H. induction H; intro Hfield; inversion Hfield; subst.
  - match goal with H : _ ⊢ _ ∶d _ |- _ => inversion H; subst end;
      eexists; split; try solve [eassumption | unfold labels_has; simpl; case_if*].
  - destruct (IHty_defs ltac:(eassumption)) as [o [Hl Ht]].
    exists o. split; auto. unfold labels_has in *. simpl in *. case_if.
    all: try exact Hl.
  - match goal with H : record_has (typ_rcd _) _ |- _ => inversion H; subst end.
    match goal with H : _ ⊢ _ ∶d _ |- _ => inversion H; subst end;
      eexists; split; try solve [eassumption | unfold labels_has; simpl; case_if*].
Qed.

Local Lemma canonical_field : forall G Sigma x a S T,
  inert G -> heap_correspond G Sigma ->
  G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S T) ->
  exists R hds V o,
    binds x (item_obj R hds) Sigma /\ G ⊢ hds ∶ open x R /\
    record_has (open x R) (dec_trm a V V) /\
    labels_has hds (heap_def_trm a o) /\
    G ⊢ heap_def_trm a o ∶d dec_trm a V V /\
    G ⊢ S <: V /\ G ⊢ V <: T.
Proof.
  intros G Sigma x a S T Hi Hheap Hty.
  destruct (typed_variable_shape Hi Hty) as [B [Hb H]].
  destruct (H _ (observe_atom x (head_rcd G _) (obs_rcd _))) as [C [Hc Hf]].
  inversion Hc; subst; simpl in Hf; try discriminate.
  destruct D; simpl in Hf; try discriminate.
  destruct Hf as [-> [Hs Ht]].
  pose proof (inert_binding Hi Hb) as Hit. inversion Hit as [| |? [ls Hr]]; subst.
  destruct (record_leaf (open_record Hr 0 x) H0) as [Hd _].
  inversion Hd; subst.
  destruct (heap_entry Hheap Hb) as [[l [_ Htyl]] | [? [hds [E [Hbh Hh]]]]].
  - inversion Htyl.
  - injection E as <-. destruct (heap_defs_field Hh H0) as [o [Ho Htyo]].
    do 4 eexists; repeat split; eauto using exact_sub_general.
Qed.

Local Definition term_typing_head (G : ctx) (t : trm) (U : typ) : Prop :=
  match t with
  | trm_var (avar_f x) => G ⊢ trm_var (avar_f x) ∶ U
  | trm_sel (avar_f x) a => exists S T,
      G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S T) /\ G ⊢ T <: U
  | trm_asn (avar_f x) a (avar_f y) => exists S T,
      G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S T) /\
      G ⊢ trm_var (avar_f y) ∶ S /\ G ⊢ T <: U
  | trm_app (avar_f f) (avar_f a) => exists S T,
      G ⊢ trm_var (avar_f f) ∶ typ_all S T /\ G ⊢ trm_var (avar_f a) ∶ S /\
      G ⊢ open a T <: U
  | trm_new (avar_f c) avs => exists xs Ts is' T,
      G ⊢ trm_var (avar_f c) ∶ typ_con Ts is' T /\ G ⊢ avs :: Ts /\
      vars_of_avars xs avs /\ G ⊢ typ_bnd (open_rec_vars 1 xs T) <: U
  | trm_let V t u => exists L T,
      G ⊢ t ∶ V /\ (forall x, x \notin L -> G & x ~ V ⊢ open x u ∶ T) /\ G ⊢ T <: U
  | trm_lit V l u => exists L T,
      G ⊢ l ∶ V /\ (forall x, x \notin L -> G & x ~ V ⊢ open x u ∶ T) /\ G ⊢ T <: U
  | _ => False
  end.

Local Lemma invert_term_typing : forall G t U, G ⊢ t ∶ U -> term_typing_head G t U.
Proof.
  intros G t U H. induction H; simpl; try solve
    [eauto 8 using ty_var, ty_rec_intro, ty_rec_elim, ty_and_intro, subtyp_refl].
  destruct t; repeat match goal with a : avar |- _ => destruct a end;
    simpl in *; try contradiction; try solve [eauto using ty_sub];
    repeat match goal with H : exists _, _ |- _ => destruct H end;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    eauto 10 using subtyp_trans.
Qed.

Local Lemma committed_heap_of_stack : forall G D Sigma E,
  free_sub_heaps G D Sigma E -> well_committed_heap G D Sigma.
Proof. intros G D Sigma E H. induction H; auto. Qed.

Local Lemma var_initialization : forall G D vs x i,
  G ⸴ D ⸴ vs ⊢i trm_var (avar_f x) ∶ i -> init_var D vs x i.
Proof.
  intros G D vs x i H. inversion H; subst; auto.
  match goal with Hc : _ ⸴ _ ⊢c trm_var _ |- _ => inversion Hc; subst end.
  apply init_var_commit. assumption.
Qed.

Local Lemma init_var_status : forall D vs x i,
  inert_inits D -> init_var D vs x i ->
  binds x committed D \/ (x \in vs /\ binds x free D).
Proof.
  intros D vs x i Hi H. induction H; auto.
  destruct (Hi _ _ H0) as [E | E]; discriminate.
Qed.

Local Lemma select_committed : forall G D vs x a i,
  G ⸴ D ⸴ vs ⊢i trm_sel (avar_f x) a ∶ i -> i = committed /\ binds x committed D.
Proof.
  intros G D vs x a i H. inversion H; subst.
  match goal with Hc : _ ⸴ _ ⊢c trm_sel _ _ |- _ => inversion Hc; subst end.
  match goal with Hc : _ ⸴ _ ⊢c trm_var _ |- _ => inversion Hc; subst end.
  auto.
Qed.

Local Lemma committed_field_initialized : forall D hds a o,
  committed_heap_defs D hds -> labels_has hds (heap_def_trm a o) ->
  exists y, o = Some y /\ binds y committed D.
Proof.
  intros D hds a o H. induction H; unfold labels_has in *; simpl; intro Hget.
  - discriminate.
  - case_if in Hget.
    + injection Hget as ->. inversion H0; subst. eauto.
    + auto.
Qed.

Local Lemma field_can_update : forall hds a o y,
  labels_has hds (heap_def_trm a o) -> exists hds', defs_update hds a y hds'.
Proof.
  intros hds a o y H. induction hds as [|d hds IH]; unfold labels_has in *; simpl in H.
  - discriminate.
  - case_if in H.
    + injection H as ->. eauto using defs_update_var.
    + destruct (IH H). eauto using defs_update_push.
Qed.

Local Lemma binding_split : forall A (E : env A) x v,
  binds x v E -> exists E1 E2, E = E1 & x ~ v & E2 /\ x # E2.
Proof.
  intros A E x v. induction E as [|E z w IH] using env_ind; intros Hb.
  - false (binds_empty_inv Hb).
  - apply binds_push_inv in Hb. destruct Hb as [[-> ->] | [Hneq Hb]].
    + exists E, (@empty A). rewrite concat_empty_r. split; auto.
    + destruct (IH Hb) as [E1 [E2 [-> Hfresh]]].
      exists E1, (E2 & z ~ w). rewrite concat_assoc, dom_push.
      split; auto.
Qed.

Local Lemma heap_can_update : forall Sigma x T hds a o y,
  binds x (item_obj T hds) Sigma -> labels_has hds (heap_def_trm a o) ->
  exists Sigma', heap_update Sigma x a y Sigma'.
Proof.
  intros Sigma x T hds a o y Hb Hfield.
  destruct (field_can_update y Hfield) as [hds' Hup].
  apply binding_split in Hb. destruct Hb as [S1 [S2 [-> Hfresh]]].
  exists (S1 & x ~ item_obj T hds' & S2).
  unfold heap_update. eauto 10.
Qed.

Local Lemma typed_args_length : forall G avs Ts xs,
  G ⊢ avs :: Ts -> vars_of_avars xs avs -> length xs = length_s Ts.
Proof.
  intros G avs Ts xs H. revert xs. induction H; intros xs Hxs; inversion Hxs; subst;
    simpl; auto.
Qed.

(* Renaming free variables also handles substitution of already evaluated
   arguments. Bound indices stay in place, so renaming commutes with opening. *)
Local Definition rename_avar (r : var -> var) (a : avar) :=
  match a with avar_b i => avar_b i | avar_f x => avar_f (r x) end.

Fixpoint rename_typ (r : var -> var) (T : typ) : typ :=
  match T with
  | typ_top => typ_top
  | typ_bot => typ_bot
  | typ_rcd D => typ_rcd (rename_dec r D)
  | typ_and V T => typ_and (rename_typ r V) (rename_typ r T)
  | typ_sel a A => typ_sel (rename_avar r a) A
  | typ_bnd T => typ_bnd (rename_typ r T)
  | typ_all V T => typ_all (rename_typ r V) (rename_typ r T)
  | typ_con Ts is' T => typ_con (rename_typs r Ts) is' (rename_typ r T)
  end
with rename_typs (r : var -> var) (Ts : typs) : typs :=
  match Ts with
  | typs_nil => typs_nil
  | typs_cons T Ts => typs_cons (rename_typ r T) (rename_typs r Ts)
  end
with rename_dec (r : var -> var) (D : dec) : dec :=
  match D with
  | dec_typ A V T => dec_typ A (rename_typ r V) (rename_typ r T)
  | dec_trm a V T => dec_trm a (rename_typ r V) (rename_typ r T)
  end.

Local Definition rename_def r (d : def) :=
  match d with def_typ A T => def_typ A (rename_typ r T) | def_trm a => def_trm a end.

Fixpoint rename_trm (r : var -> var) (t : trm) : trm :=
  match t with
  | trm_var a => trm_var (rename_avar r a)
  | trm_sel a f => trm_sel (rename_avar r a) f
  | trm_app a b => trm_app (rename_avar r a) (rename_avar r b)
  | trm_let T t u => trm_let (rename_typ r T) (rename_trm r t) (rename_trm r u)
  | trm_lit T l t => trm_lit (rename_typ r T) (rename_lit r l) (rename_trm r t)
  | trm_asn a f b => trm_asn (rename_avar r a) f (rename_avar r b)
  | trm_new a avs => trm_new (rename_avar r a) (List.map (rename_avar r) avs)
  end
with rename_lit (r : var -> var) (l : lit) : lit :=
  match l with
  | lit_fun T t => lit_fun (rename_typ r T) (rename_trm r t)
  | lit_con Ts is' T ds t =>
      lit_con (rename_typs r Ts) is' (rename_typ r T)
        (List.map (rename_def r) ds) (rename_trm r t)
  end.

Local Lemma rename_typs_list : forall r Ts,
  to_list (rename_typs r Ts) = List.map (rename_typ r) (to_list Ts).
Proof. intros r Ts. change (typs_to_list (rename_typs r Ts) = List.map (rename_typ r) (typs_to_list Ts)); induction Ts; simpl; congruence. Qed.

Local Lemma rename_typs_length : forall r Ts,
  length_s (rename_typs r Ts) = length_s Ts.
Proof. intros r Ts. unfold length_s. rewrite rename_typs_list, List.length_map. reflexivity. Qed.

Local Lemma rename_avar_open : forall r a n x,
  rename_avar r (open_rec n x a) = open_rec n (r x) (rename_avar r a).
Proof. destruct a; intros; simpl; try case_if; reflexivity. Qed.

Local Ltac syntax_rewrites :=
  repeat match goal with
  | H : forall _ _ _, _ = _ |- _ => progress rewrite H
  | H : forall _ _, _ = _ |- _ => progress rewrite H
  | H : forall _, _ = _ |- _ => progress rewrite H
  end.

Local Lemma rename_types_open : forall r,
  (forall T n x, rename_typ r (open_rec n x T) = open_rec n (r x) (rename_typ r T)) /\
  (forall Ts n x, rename_typs r (open_rec n x Ts) = open_rec n (r x) (rename_typs r Ts)) /\
  (forall D n x, rename_dec r (open_rec n x D) = open_rec n (r x) (rename_dec r D)).
Proof.
  intros r. apply typ_mutind; intros; simpl;
    fold open_rec_typ open_rec_typs open_rec_dec;
    change (open_rec_typ) with (@open_rec typ TypOpenable) in *;
    change (open_rec_typs) with (@open_rec typs TypsOpenable) in *;
    change (open_rec_dec) with (@open_rec dec DecOpenable) in *;
    try rewrite rename_typs_length; try rewrite rename_avar_open;
    syntax_rewrites; reflexivity.
Qed.

Local Lemma rename_list_open : forall A (O : Openable A) (f : A -> A) r,
  (forall a n x, f (open_rec n x a) = open_rec n (r x) (f a)) ->
  forall (xs : list A) n x,
    List.map f (open_rec n x xs) = open_rec n (r x) (List.map f xs).
Proof.
  intros A O f r H xs n x. change (List.map f (List.map (open_rec n x) xs) = List.map (open_rec n (r x)) (List.map f xs)).
  induction xs; simpl; [reflexivity | rewrite H, IHxs; reflexivity].
Qed.

Local Lemma rename_def_open : forall r d n x,
  rename_def r (open_rec n x d) = open_rec n (r x) (rename_def r d).
Proof. destruct d; intros; simpl; [f_equal; apply (proj1 (rename_types_open r))|reflexivity]. Qed.

Local Lemma rename_terms_open : forall r,
  (forall t n x, rename_trm r (open_rec n x t) = open_rec n (r x) (rename_trm r t)) /\
  (forall l n x, rename_lit r (open_rec n x l) = open_rec n (r x) (rename_lit r l)).
Proof.
  intros r. destruct (rename_types_open r) as [HT [HTs HD]].
  apply trm_mutind; intros;
    cbn [open_rec TrmOpenable LitOpenable open_rec_trm open_rec_lit rename_trm rename_lit];
    fold open_rec_trm open_rec_lit;
    change open_rec_trm with (@open_rec trm TrmOpenable) in *;
    change open_rec_lit with (@open_rec lit LitOpenable) in *;
    try rewrite rename_typs_length;
    try rewrite !rename_avar_open;
    try rewrite (@rename_list_open avar AvarOpenable (rename_avar r) r (rename_avar_open r));
    try rewrite (@rename_list_open def DefOpenable (rename_def r) r (rename_def_open r));
    syntax_rewrites; reflexivity.
Qed.

Local Lemma rename_open_many : forall A (O : Openable A) (f : A -> A) r,
  (forall a n x, f (open_rec n x a) = open_rec n (r x) (f a)) ->
  forall ys n a, f (open_rec_vars n ys a) =
    open_rec_vars n (List.map r ys) (f a).
Proof.
  intros A O f r H ys. induction ys; intros; simpl; rewrite ?IHys, ?H; reflexivity.
Qed.

Local Definition fixes (r : var -> var) (X : vars) := forall x, x \in X -> r x = x.

Local Lemma fixes_union : forall r X Y, fixes r (X \u Y) -> fixes r X /\ fixes r Y.
Proof. unfold fixes. intros; split; intros; apply H; rewrite in_union; auto. Qed.

Local Lemma rename_avar_fixed : forall r a, fixes r (fv a) -> rename_avar r a = a.
Proof.
  intros r [i|x] H; simpl in *; auto. f_equal. apply H, in_singleton_self.
Qed.

Local Ltac split_fixes :=
  repeat match goal with
  | H : fixes _ (_ \u _) |- _ => apply fixes_union in H; destruct H
  end.

Local Ltac solve_fixed := split_fixes; f_equal; eauto using rename_avar_fixed.

Local Lemma rename_types_fixed : forall r,
  (forall T, fixes r (fv T) -> rename_typ r T = T) /\
  (forall Ts, fixes r (fv Ts) -> rename_typs r Ts = Ts) /\
  (forall D, fixes r (fv D) -> rename_dec r D = D).
Proof. intros. apply typ_mutind; intros; simpl in *; solve_fixed. Qed.

Local Lemma rename_list_fixed : forall A (F : FreeVar A) (f : A -> A) r,
  (forall a, fixes r (fv a) -> f a = a) ->
  forall (xs : list A), fixes r (fv xs) -> List.map f xs = xs.
Proof. intros A F f r H xs; induction xs; intros; simpl in *; solve_fixed. Qed.

Local Lemma rename_def_fixed : forall r d, fixes r (fv d) -> rename_def r d = d.
Proof. destruct d; simpl; intros; f_equal; apply (proj1 (rename_types_fixed r)); assumption. Qed.

Local Lemma rename_terms_fixed : forall r,
  (forall t, fixes r (fv t) -> rename_trm r t = t) /\
  (forall l, fixes r (fv l) -> rename_lit r l = l).
Proof.
  intros r. destruct (rename_types_fixed r) as [HT [HTs HD]].
  apply trm_mutind; intros; simpl in *; solve_fixed;
    eapply rename_list_fixed; eauto using rename_avar_fixed, rename_def_fixed.
Qed.

Local Definition isolated (r : var -> var) (L : vars) :=
  forall x, x \notin L -> r x = x /\ forall y, r y = x -> y = x.

Local Lemma identity_isolated : isolated id \{}.
Proof. unfold isolated, id. auto. Qed.

Local Definition typing_map r (G G' : ctx) :=
  forall x T, binds x T G -> G' ⊢ trm_var (avar_f (r x)) ∶ rename_typ r T.

Local Lemma rename_def_label : forall r d, label_of (rename_def r d) = label_of d.
Proof. intros r []; reflexivity. Qed.

Local Lemma map_get_label : forall A B (LA : LabelOf A) (LB : LabelOf B)
  (f : A -> B), (forall a, label_of (f a) = label_of a) ->
  forall l ds, get_labeld l (List.map f ds) = option_map f (get_labeld l ds).
Proof.
  intros A B LA LB f H l ds. induction ds; simpl; auto.
  rewrite H. case_if*.
Qed.

Local Lemma rename_defs_typed : forall G (ds : defs) T r G',
  G ⊢ ds ∶ T -> G' ⊢ List.map (rename_def r) ds ∶ rename_typ r T.
Proof.
  intros G ds T r G' H. induction H; simpl.
  - apply ty_defs_one. inversion H; subst; try apply ty_def_typ; try apply (@ty_def_trm _ _ (trm_var (avar_b 0)) _).
  - apply ty_defs_cons; auto.
    + inversion H0; subst; first [apply ty_def_typ | apply (@ty_def_trm _ _ (trm_var (avar_b 0)) _)].
    + unfold labels_hasnt in *. rewrite rename_def_label, (@map_get_label def def DefLabelOf DefLabelOf (rename_def r) (rename_def_label r)).
      rewrite H1. reflexivity.
Qed.

Local Lemma extends_suffix : forall A (E F Q : env A),
  extends E F -> extends (E & Q) (F & Q).
Proof.
  unfold extends. intros A E F Q H x v Hb. apply binds_concat_inv in Hb.
  destruct Hb as [Hb | [Hf Hb]]; eauto using binds_concat_right, binds_concat_left.
Qed.

Local Lemma defs_context : forall G (ds : defs) T,
  G ⊢ ds ∶ T -> forall G', G' ⊢ ds ∶ T.
Proof.
  intros G ds T H. induction H; intros.
  - apply ty_defs_one. inversion H; subst; first [apply ty_def_typ | eapply ty_def_trm; eassumption].
  - apply ty_defs_cons; auto.
    inversion H0; subst; first [apply ty_def_typ | eapply ty_def_trm; eassumption].
Qed.

Local Lemma weaken_typing :
  (forall G t T, G ⊢ t ∶ T -> forall G', extends G G' -> G' ⊢ t ∶ T) /\
  (forall G (l : lit) T, G ⊢ l ∶ T -> forall G', extends G G' -> G' ⊢ l ∶ T) /\
  (forall G S T, G ⊢ S <: T -> forall G', extends G G' -> G' ⊢ S <: T) /\
  (forall G vs Ts, G ⊢ vs :: Ts -> forall G', extends G G' -> G' ⊢ vs :: Ts).
Proof.
  apply rules_mutind; intros; try solve
    [eauto using ty_var, ty_all_elim, ty_new, ty_rcd_elim, ty_fld_asn,
       ty_rec_intro, ty_rec_elim, ty_and_intro, ty_sub, subtyp_top, subtyp_bot,
       subtyp_refl, subtyp_trans, subtyp_and11, subtyp_and12, subtyp_and2,
       subtyp_fld, subtyp_typ, subtyp_sel1, subtyp_sel2, typ_avars_nil, typ_avars_cons].
  - eapply ty_let with (L:=L); eauto using extends_suffix.
  - eapply ty_llit with (L:=L); eauto using extends_suffix.
  - eapply ty_all_intro with (L:=L); eauto using extends_suffix.
  - eapply ty_con_intro with (L:=L) (T':=T'); eauto using extends_suffix, defs_context.
  - eapply subtyp_all with (L:=L); eauto using extends_suffix.
  Unshelve. all: try assumption.
Qed.

Local Lemma weaken_term : forall G t T,
  G ⊢ t ∶ T -> forall G', extends G G' -> G' ⊢ t ∶ T.
Proof. exact (proj1 weaken_typing). Qed.

Local Lemma weaken_literal : forall G (l : lit) T,
  G ⊢ l ∶ T -> forall G', extends G G' -> G' ⊢ l ∶ T.
Proof. exact (proj1 (proj2 weaken_typing)). Qed.

Local Lemma typing_map_suffix : forall r G G' Q,
  typing_map r G G' ->
  (forall x, x \in dom Q -> r x = x /\ forall y, r y = x -> y = x) ->
  all_notin (dom Q) (dom G') ->
  typing_map r (G & Q) (G' & EnvOps.map (rename_typ r) Q).
Proof.
  unfold typing_map. intros r G G' Q H Hr Hf y V Hb.
  apply binds_concat_inv in Hb. destruct Hb as [Hb | [Hn Hb]].
  - rewrite (proj1 (Hr _ (get_some_inv Hb))). apply ty_var, binds_concat_right, binds_map.
    exact Hb.
  - eapply (proj1 weaken_typing); [eauto|].
    apply extends_concat_r, disjoint_comm. rewrite dom_map.
    unfold disjoint. apply fset_extens; intros x Hx; [rewrite in_inter in Hx | exfalso; exact (in_empty_inv Hx)].
    destruct Hx as [Ha Hb']. false (Hf _ Ha Hb').
Qed.

Local Lemma typing_map_push : forall r G G' z T,
  typing_map r G G' ->
  r z = z -> (forall y, r y = z -> y = z) -> z # G' ->
  typing_map r (G & z ~ T) (G' & z ~ rename_typ r T).
Proof.
  intros r G G' z T H Hr Hinv Hf.
  rewrite <- map_single. apply typing_map_suffix; auto;
    unfold all_notin; rewrite dom_single; intros x Hx; rewrite in_singleton in Hx;
    subst; auto.
Qed.

Local Lemma fresh_avoids : forall L n xs,
  fresh L n xs -> all_notin (from_list xs) L.
Proof.
  intros L n xs. revert L n. induction xs as [|x xs IH]; intros L [|n] H;
    unfold all_notin in *; simpl in H; try contradiction.
  - intros y Hy. rewrite from_list_nil in Hy. exfalso. exact (in_empty_inv Hy).
  - intros y Hy. rewrite from_list_cons, in_union, in_singleton in Hy.
    destruct H as [Hx Hrest]. destruct Hy as [-> | Hy]; auto.
    eapply notin_union_r1, IH; eauto.
Qed.
Arguments fresh_avoids {L n xs} _.

Local Lemma from_list_iff : forall A (xs : list A) x, x \in from_list xs <-> List.In x xs.
Proof.
  intros A xs x. induction xs; simpl.
  - rewrite from_list_nil. split; intro H; [exact (in_empty_inv H) | contradiction].
  - rewrite from_list_cons, in_union, in_singleton, IHxs. intuition congruence.
Qed.

Local Lemma from_list_reverse : forall A (xs : list A), from_list (List.rev xs) = from_list xs.
Proof.
  intros A xs. apply fset_extens; intros x Hx; rewrite from_list_iff in *.
  - apply (proj2 (List.in_rev xs x)); exact Hx.
  - apply (proj1 (List.in_rev xs x)); exact Hx.
Qed.

Local Lemma tlc_length : forall A (xs : list A), LibList.length xs = List.length xs.
Proof. intros A xs. induction xs; simpl; rewrite ?LibList.length_nil, ?LibList.length_cons, ?IHxs; reflexivity. Qed.

Local Lemma tlc_map : forall A B (f : A -> B) xs, LibList.map f xs = List.map f xs.
Proof. intros A B f xs. induction xs; simpl; rewrite ?LibList.map_nil, ?LibList.map_cons, ?IHxs; reflexivity. Qed.

Local Lemma dom_bindings : forall A (xs : list var) (vs : list A),
  length xs = length vs -> dom (xs ~** vs) = from_list xs.
Proof.
  intros A xs vs H. rewrite dom_singles; [apply from_list_reverse|].
  rewrite !tlc_length, !List.length_rev. exact H.
Qed.

Local Lemma map_bindings : forall A B (f : A -> B) xs vs,
  length xs = length vs ->
  EnvOps.map f (xs ~** vs) = xs ~** List.map f vs.
Proof.
  intros A B f xs vs H. rewrite map_singles, tlc_map, List.map_rev; auto.
  rewrite !tlc_length, !List.length_rev. exact H.
Qed.

Local Lemma fixes_list : forall r xs, fixes r (from_list xs) -> List.map r xs = xs.
Proof.
  intros r xs. induction xs; intros H; simpl; auto.
  rewrite from_list_cons in H. destruct (fixes_union H) as [Ha Hrest].
  rewrite (Ha _ (in_singleton_self a)), (IHxs Hrest). reflexivity.
Qed.

Local Lemma rename_vars_of_avars : forall r xs avs,
  vars_of_avars xs avs -> vars_of_avars (List.map r xs) (List.map (rename_avar r) avs).
Proof. intros r xs avs H. induction H; simpl; constructor; auto. Qed.

Local Ltac split_fresh :=
  repeat match goal with H : _ \notin (_ \u _) |- _ => apply notin_union in H; destruct H end.

Local Ltac rename_opening r :=
  let HT := fresh "rename_type_open" in
  let HTr := fresh "rename_trm_open" in
  pose proof (proj1 (rename_types_open r)) as HT;
  pose proof (proj1 (rename_terms_open r)) as HTr;
  rewrite ?HT, ?HTr;
  clear HT HTr.

Local Lemma rename_typing : forall r L, isolated r L ->
  (forall G t T, G ⊢ t ∶ T ->
      forall G', typing_map r G G' -> G' ⊢ rename_trm r t ∶ rename_typ r T) /\
  (forall G (l : lit) T, G ⊢ l ∶ T ->
      forall G', typing_map r G G' -> G' ⊢ rename_lit r l ∶ rename_typ r T) /\
  (forall G S T, G ⊢ S <: T ->
      forall G', typing_map r G G' -> G' ⊢ rename_typ r S <: rename_typ r T) /\
  (forall G avs Ts, G ⊢ avs :: Ts ->
      forall G', typing_map r G G' -> G' ⊢ List.map (rename_avar r) avs :: rename_typs r Ts).
Proof.
  intros r K Hr. apply rules_mutind; intros; simpl in *.
  - eauto.
  - rename_opening r. eauto using ty_all_elim.
  - rewrite (@rename_open_many typ TypOpenable (rename_typ r) r (proj1 (rename_types_open r))).
    eauto using ty_new, rename_vars_of_avars.
  - eauto using ty_rcd_elim.
  - eauto using ty_fld_asn.
  - eapply ty_let with (L:=L \u K \u dom G'); eauto.
    intros z Hz. split_fresh.
    destruct (Hr z ltac:(assumption)) as [Hrz Hrinv].
    pose proof (@typing_map_push r G G' z T ltac:(assumption) Hrz Hrinv ltac:(assumption)) as Hmap.
    specialize (H0 z ltac:(assumption) _ Hmap).
    rewrite (proj1 (rename_terms_open r)), ?(proj1 (rename_types_open r)), Hrz in H0.
    exact H0.
  - eapply ty_llit with (L:=L \u K \u dom G'); eauto.
    intros z Hz. split_fresh.
    destruct (Hr z ltac:(assumption)) as [Hrz Hrinv].
    pose proof (@typing_map_push r G G' z T ltac:(assumption) Hrz Hrinv ltac:(assumption)) as Hmap.
    specialize (H0 z ltac:(assumption) _ Hmap).
    rewrite (proj1 (rename_terms_open r)), ?(proj1 (rename_types_open r)), Hrz in H0.
    exact H0.
  - specialize (H G' H0). rewrite (proj1 (rename_types_open r)) in H.
    eapply ty_rec_intro; exact H.
  - rename_opening r. eauto using ty_rec_elim.
  - eauto using ty_and_intro.
  - eauto using ty_sub.
  - eapply ty_all_intro with (L:=L \u K \u dom G').
    intros z Hz. split_fresh.
    destruct (Hr z ltac:(assumption)) as [Hrz Hrinv].
    pose proof (@typing_map_push r G G' z T ltac:(assumption) Hrz Hrinv ltac:(assumption)) as Hmap.
    specialize (H z ltac:(assumption) _ Hmap).
    rewrite (proj1 (rename_terms_open r)), ?(proj1 (rename_types_open r)), Hrz in H.
    exact H.
  - eapply ty_con_intro with (L:=L \u K \u dom G') (T':=rename_typ r T');
      intros z zs Hlen Hz; rewrite rename_typs_length in Hlen;
      destruct (fresh_union_r Hz) as [HL Hlo];
      destruct (fresh_union_r Hlo) as [HK Hdom];
      pose proof (fresh_avoids HK) as Havoids;
      assert (Hfix : List.map r (z :: zs) = (z :: zs)%list)
        by (apply fixes_list; unfold fixes; intros y Hy; apply (proj1 (Hr _ (Havoids _ Hy)))).
    + pose proof (@rename_defs_typed _ _ _ r G' (t0 _ _ Hlen HL)) as Hnew.
      change (G' ⊢ List.map (rename_def r) (open_vars (z :: zs) ds)
        ∶ rename_typ r (open_vars (z :: zs) T)) in Hnew.
      rewrite (@rename_open_many typ TypOpenable (rename_typ r) r (proj1 (rename_types_open r))),
        (@rename_open_many defs _ (List.map (rename_def r)) r
          (@rename_list_open def DefOpenable (rename_def r) r (rename_def_open r))),
        Hfix in Hnew.
      eapply defs_context; exact Hnew.
    + assert (Hopen : rename_typ r (open_vars (z :: zs) T) =
          open_vars (z :: zs) (rename_typ r T)).
      { rewrite (@rename_open_many typ TypOpenable (rename_typ r) r (proj1 (rename_types_open r))), Hfix.
        reflexivity. }
      assert (Hmap : typing_map r
          (G & zs ~** to_list Ts & z ~ open_vars (z :: zs) T)
          (G' & zs ~** to_list (rename_typs r Ts) & z ~ open_vars (z :: zs) (rename_typ r T))).
      { rewrite <- concat_assoc, <- (concat_assoc G').
        replace (zs ~** to_list (rename_typs r Ts) & z ~ open_vars (z :: zs) (rename_typ r T))
          with (EnvOps.map (rename_typ r) (zs ~** to_list Ts & z ~ open_vars (z :: zs) T)).
        - apply typing_map_suffix; try assumption;
            rewrite dom_push, dom_bindings by exact Hlen;
            rewrite <- from_list_cons.
          + intros y Hy. apply Hr, Havoids, Hy.
          + exact (fresh_avoids Hdom).
        - rewrite map_concat, map_single, map_bindings by exact Hlen.
          rewrite rename_typs_list, Hopen. reflexivity. }
      pose proof (H _ _ Hlen HL _ Hmap) as Hnew.
      change (G' & zs ~** to_list (rename_typs r Ts) & z ~ open_vars (z :: zs) (rename_typ r T) ⊢ rename_trm r (open_vars (z :: zs) t)
        ∶ rename_typ r (open_vars (z :: zs) T')) in Hnew.
      rewrite (@rename_open_many typ TypOpenable (rename_typ r) r (proj1 (rename_types_open r))),
        (@rename_open_many trm TrmOpenable (rename_trm r) r (proj1 (rename_terms_open r))),
        Hfix in Hnew. exact Hnew.
  - apply subtyp_top.
  - apply subtyp_bot.
  - apply subtyp_refl.
  - eauto using subtyp_trans.
  - apply subtyp_and11.
  - apply subtyp_and12.
  - eauto using subtyp_and2.
  - eauto using subtyp_fld.
  - eauto using subtyp_typ.
  - eauto using subtyp_sel2.
  - eauto using subtyp_sel1.
  - eapply subtyp_all with (L:=L \u K \u dom G'); eauto.
    intros z Hz. split_fresh.
    destruct (Hr z ltac:(assumption)) as [Hrz Hrinv].
    pose proof (@typing_map_push r G G' z S2 H1 Hrz Hrinv ltac:(assumption)) as Hmap.
    specialize (H0 z ltac:(assumption) _ Hmap).
    rewrite !(proj1 (rename_types_open r)), Hrz in H0. exact H0.
  - apply typ_avars_nil.
  - eauto using typ_avars_cons.
Qed.

Local Definition rename_effect (r : var -> var) (p : effect) : effect := (r (fst p), snd p).
Local Definition rename_effects r := List.map (rename_effect r).

Local Lemma rename_effect_typing : forall r L, isolated r L ->
  forall t e, ⊢e t ∶ e -> ⊢e rename_trm r t ∶ rename_effects r e.
Proof.
  intros r K Hr t e H. induction H; simpl.
  - apply eff_ignore.
  - apply eff_fld_asn.
  - unfold rename_effects in *. rewrite List.map_app.
    eapply eff_let with (L:=L \u K); [exact IHeff_trm|].
    intros z Hz. split_fresh. specialize (H1 z ltac:(assumption)).
    rewrite (proj1 (rename_terms_open r)), (proj1 (Hr z ltac:(assumption))) in H1.
    exact H1.
  - eapply eff_llit with (L:=L \u K).
    intros z Hz. split_fresh. specialize (H0 z ltac:(assumption)).
    rewrite (proj1 (rename_terms_open r)), (proj1 (Hr z ltac:(assumption))) in H0.
    exact H0.
Qed.

Local Lemma map_from_list_eq : forall A B (f : A -> B) xs ys,
  from_list xs = from_list ys ->
  from_list (List.map f xs) = from_list (List.map f ys).
Proof.
  intros A B f xs ys H. apply fset_extens; intros x Hx;
    apply from_list_iff in Hx; apply List.in_map_iff in Hx; destruct Hx as [y [<- Hy]];
    apply from_list_iff, List.in_map; apply from_list_iff in Hy; apply from_list_iff;
    congruence.
Qed.

Local Lemma rename_has_effs : forall r L t e, isolated r L ->
  has_effs t e -> has_effs (rename_trm r t) (rename_effects r e).
Proof.
  intros r L t e Hr [es [H Hset]].
  exists (rename_effects r es). split; eauto using rename_effect_typing.
  apply map_from_list_eq. exact Hset.
Qed.

Local Lemma rename_def_effects : forall r x ds,
  rename_effects r (def_eff x ds) = def_eff (r x) (List.map (rename_def r) ds).
Proof. intros r x ds. unfold rename_effects. induction ds as [|[] ds IH]; cbn [List.map def_eff rename_def rename_effect fst snd]; rewrite ?IH; reflexivity. Qed.

Local Lemma init_var_committed_inv : forall D vs x,
  init_var D vs x committed -> binds x committed D.
Proof.
  intros D vs x H. remember committed as i eqn:E. induction H; subst; try discriminate; auto.
  inversion H0; subst; auto.
Qed.

Local Lemma init_var_from_binding : forall D vs x i,
  binds x i D -> (i = committed \/ x \in vs) -> init_var D vs x i.
Proof.
  intros D vs x [] Hb [H | H]; try discriminate;
    eauto using init_var_commit, init_var_free, init_var_unspec.
Qed.

Local Definition commit_map r (D D' : init_ctx) :=
  forall x, binds x committed D -> binds (r x) committed D'.

Local Definition init_map r (D : init_ctx) (vs : vars) (D' : init_ctx) (vs' : vars) :=
  forall x i, binds x i D -> (i = committed \/ x \in vs) -> init_var D' vs' (r x) i.

Local Lemma init_map_commit : forall r D vs D' vs', init_map r D vs D' vs' -> commit_map r D D'.
Proof.
  unfold init_map, commit_map. intros r D vs D' vs' H x Hb.
  eapply init_var_committed_inv. apply H; auto.
Qed.

Local Lemma init_map_var : forall r D vs D' vs' x i,
  init_map r D vs D' vs' -> init_var D vs x i -> init_var D' vs' (r x) i.
Proof.
  intros r D vs D' vs' x i H Hx. induction Hx; eauto using init_var_sub.
Qed.

Local Lemma init_var_extend : forall D vs x i D' vs',
  init_var D vs x i -> extends D D' -> vs \c vs' -> init_var D' vs' x i.
Proof.
  intros D vs x i D' vs' H Hext Hsub. induction H;
    eauto using init_var_commit, init_var_free, init_var_unspec, init_var_sub.
Qed.

Local Lemma init_var_push_other : forall D vs x i z j vs',
  init_var D vs x i -> x <> z -> vs \c vs' ->
  init_var (D & z ~ j) vs' x i.
Proof.
  intros D vs x i z j vs' H Hne Hsub. induction H;
    eauto using binds_push_neq, init_var_commit, init_var_free, init_var_unspec, init_var_sub.
Qed.

Local Lemma commit_map_suffix : forall r D D' Q,
  commit_map r D D' ->
  (forall z, z \in dom Q -> r z = z /\ forall y, r y = z -> y = z) ->
  commit_map r (D & Q) (D' & Q).
Proof.
  unfold commit_map. intros r D D' Q H Hr x Hb.
  apply binds_concat_inv in Hb. destruct Hb as [Hb | [Hfresh Hb]].
  - rewrite (proj1 (Hr _ (get_some_inv Hb))). apply binds_concat_right. exact Hb.
  - apply binds_concat_left; auto. intro Hx. apply Hfresh.
    rewrite (proj2 (Hr _ Hx) x eq_refl). exact Hx.
Qed.

Local Lemma commit_map_push : forall r D D' z i,
  commit_map r D D' -> r z = z -> (forall y, r y = z -> y = z) ->
  commit_map r (D & z ~ i) (D' & z ~ i).
Proof.
  intros. apply commit_map_suffix; auto. rewrite dom_single. intros y Hy.
  rewrite in_singleton in Hy. subst; auto.
Qed.

Local Lemma init_map_push : forall r D vs D' vs' z i,
  init_map r D vs D' vs' -> r z = z -> (forall y, r y = z -> y = z) ->
  init_map r (D & z ~ i) (vs \u \{z}) (D' & z ~ i) (vs' \u \{z}).
Proof.
  unfold init_map. intros r D vs D' vs' z i H Hr Hinv x j Hb Haccess.
  apply binds_push_inv in Hb. destruct Hb as [[-> ->] | [Hne Hb]].
  - rewrite Hr. apply init_var_from_binding; [apply binds_push_eq |].
    right. rewrite in_union; right; apply in_singleton_self.
  - apply init_var_push_other with (vs:=vs'); auto.
    + apply H; auto. destruct Haccess as [Hc | Hv]; auto.
      rewrite in_union, in_singleton in Hv. intuition congruence.
    + intros y Hy. rewrite in_union; auto.
Qed.

Local Lemma init_map_push_committed : forall r D vs D' vs' z,
  init_map r D vs D' vs' -> r z = z -> (forall y, r y = z -> y = z) ->
  init_map r (D & z ~ committed) vs (D' & z ~ committed) vs'.
Proof.
  unfold init_map. intros r D vs D' vs' z H Hr Hinv x j Hb Haccess.
  apply binds_push_inv in Hb. destruct Hb as [[-> ->] | [Hne Hb]].
  - rewrite Hr. apply init_var_commit, binds_push_eq.
  - apply init_var_push_other with (vs:=vs'); eauto using subset_refl.
Qed.

Local Lemma init_map_local : forall r D D' Q,
  commit_map r D D' ->
  (forall z, z \in dom Q -> r z = z /\ forall y, r y = z -> y = z) ->
  init_map r (D & Q) (dom Q) (D' & Q) (dom Q).
Proof.
  unfold init_map. intros r D D' Q H Hr x i Hb Ha.
  apply binds_concat_inv in Hb. destruct Hb as [Hb | [Hfresh Hb]].
  - rewrite (proj1 (Hr _ (get_some_inv Hb))). apply init_var_from_binding.
    + apply binds_concat_right. exact Hb.
    + right. exact (get_some_inv Hb).
  - destruct Ha as [-> | Ha]; [|contradiction].
    apply init_var_commit. apply (commit_map_suffix H Hr).
    apply binds_concat_left; auto.
Qed.

Local Lemma rename_initialization : forall r L, isolated r L ->
  (forall G D t, G ⸴ D ⊢c t -> forall G' D',
    typing_map r G G' -> commit_map r D D' -> G' ⸴ D' ⊢c rename_trm r t) /\
  (forall G D (avs : avars), G ⸴ D ⊢c avs -> forall G' D',
    typing_map r G G' -> commit_map r D D' -> G' ⸴ D' ⊢c List.map (rename_avar r) avs) /\
  (forall G D (l : lit), G ⸴ D ⊢c l -> forall G' D',
    typing_map r G G' -> commit_map r D D' -> G' ⸴ D' ⊢c rename_lit r l) /\
  (forall G D vs t i, G ⸴ D ⸴ vs ⊢i t ∶ i -> forall G' D' vs',
    typing_map r G G' -> init_map r D vs D' vs' -> G' ⸴ D' ⸴ vs' ⊢i rename_trm r t ∶ i) /\
  (forall G D vs (avs : avars) is', G ⸴ D ⸴ vs ⊢i avs :: is' -> forall G' D' vs',
    typing_map r G G' -> init_map r D vs D' vs' ->
    G' ⸴ D' ⸴ vs' ⊢i List.map (rename_avar r) avs :: is').
Proof.
  intros r K Hr.
  pose proof (proj1 (rename_typing Hr)) as Htypen.
  apply well_init_mut_ind; intros; simpl in *; try solve
    [eauto using commit_var, commit_all_elim, commit_rcd_elim, commit_fld_asn,
    committed_nil, committed_cons, init_var_binds, init_map_var, init_commit, init_map_commit,
    init_fld_asn_ac, init_fld_asn_ff, well_inits_nil, well_inits_cons].
  - eapply commit_new with (Ts:=rename_typs r Ts) (T:=rename_typ r T) (is':=is'); eauto.
    exact (Htypen _ _ _ t _ H1).
  - eapply commit_let with (L:=L \u K \u dom G'); eauto.
    intros z Hz. split_fresh. destruct (Hr z ltac:(assumption)) as [Hrz Hrinv].
    pose proof (@typing_map_push r Gamma G' z T ltac:(assumption) Hrz Hrinv ltac:(assumption)) as Hmap.
    pose proof (@commit_map_push r Delta D' z committed ltac:(assumption) Hrz Hrinv) as Hd.
    specialize (H0 z ltac:(assumption) _ _ Hmap Hd).
    rewrite (proj1 (rename_terms_open r)), Hrz in H0. exact H0.
  - eapply commit_llit with (L:=L \u K \u dom G'); eauto.
    intros z Hz. split_fresh. destruct (Hr z ltac:(assumption)) as [Hrz Hrinv].
    pose proof (@typing_map_push r Gamma G' z T ltac:(assumption) Hrz Hrinv ltac:(assumption)) as Hmap.
    pose proof (@commit_map_push r Delta D' z committed ltac:(assumption) Hrz Hrinv) as Hd.
    specialize (H0 z ltac:(assumption) _ _ Hmap Hd).
    rewrite (proj1 (rename_terms_open r)), Hrz in H0. exact H0.
  - eapply commit_all_intro with (L:=L \u K \u dom G').
    intros z Hz. split_fresh. destruct (Hr z ltac:(assumption)) as [Hrz Hrinv].
    pose proof (@typing_map_push r Gamma G' z T ltac:(assumption) Hrz Hrinv ltac:(assumption)) as Hmap.
    pose proof (@commit_map_push r Delta D' z committed ltac:(assumption) Hrz Hrinv) as Hd.
    specialize (H z ltac:(assumption) _ _ Hmap Hd).
    rewrite (proj1 (rename_terms_open r)), Hrz in H. exact H.
  - eapply commit_con_intro with (L:=L \u K \u dom G') (i:=i);
      rewrite ?rename_typs_length; auto.
    all: intros z zs Hlen Hz;
      destruct (fresh_union_r Hz) as [HL Hlo];
      destruct (fresh_union_r Hlo) as [HK Hdom];
      pose proof (fresh_avoids HK) as Havoids;
      assert (Hfix : List.map r (z :: zs) = (z :: zs)%list)
        by (apply fixes_list; unfold fixes; intros y Hy; apply (proj1 (Hr _ (Havoids _ Hy)))).
    + pose proof (rename_has_effs Hr (h _ _ Hlen HL)) as He.
      change (has_effs (rename_trm r (open_vars (z :: zs) t))
        (rename_effects r (def_eff z ds))) in He.
      rewrite (@rename_open_many trm TrmOpenable (rename_trm r) r (proj1 (rename_terms_open r))),
        Hfix, rename_def_effects in He.
      replace (r z) with z in He by (symmetry; apply (proj1 (Hr z (proj1 HK)))).
      exact He.
    + assert (Hopen : rename_typ r (open_vars (z :: zs) T) =
          open_vars (z :: zs) (rename_typ r T)).
      { rewrite (@rename_open_many typ TypOpenable (rename_typ r) r (proj1 (rename_types_open r))), Hfix.
        reflexivity. }
      assert (Hmap : typing_map r
          (Gamma & zs ~** to_list Ts & z ~ open_vars (z :: zs) T)
          (G' & zs ~** to_list (rename_typs r Ts) & z ~ open_vars (z :: zs) (rename_typ r T))).
      { rewrite <- concat_assoc, <- (concat_assoc G').
        replace (zs ~** to_list (rename_typs r Ts) & z ~ open_vars (z :: zs) (rename_typ r T))
          with (EnvOps.map (rename_typ r) (zs ~** to_list Ts & z ~ open_vars (z :: zs) T)).
        - apply typing_map_suffix; try assumption;
            rewrite dom_push, dom_bindings by exact Hlen;
            rewrite <- from_list_cons.
          + intros y Hy. apply Hr, Havoids, Hy.
          + exact (fresh_avoids Hdom).
        - rewrite map_concat, map_single, map_bindings by exact Hlen.
          rewrite rename_typs_list, Hopen. reflexivity. }
      assert (HmapD : init_map r (Delta & zs ~** is' & z ~ free) (from_list zs \u \{z})
          (D' & zs ~** is' & z ~ free) (from_list zs \u \{z})).
      { assert (Hlen' : length zs = length is') by congruence.
        rewrite <- concat_assoc, <- (concat_assoc D').
        assert (Hkeys : dom (zs ~** is' & z ~ free) = from_list zs \u \{z}).
        { rewrite dom_push, dom_bindings by exact Hlen'. apply union_comm. }
        rewrite <- Hkeys. apply init_map_local; auto. intros y Hy.
        apply Hr, Havoids. rewrite from_list_cons, <- dom_bindings with (vs:=is') by exact Hlen'.
        rewrite <- dom_push with (v:=free). exact Hy. }
      pose proof (H _ _ Hlen HL _ _ _ Hmap HmapD) as Hbody.
      change (G' & zs ~** to_list (rename_typs r Ts) & z ~ open_vars (z :: zs) (rename_typ r T)
        ⸴ D' & zs ~** is' & z ~ free ⸴ from_list zs \u \{z}
        ⊢i rename_trm r (open_vars (z :: zs) t) ∶ i) in Hbody.
      rewrite (@rename_open_many trm TrmOpenable (rename_trm r) r (proj1 (rename_terms_open r))),
        Hfix in Hbody. exact Hbody.
  - eapply init_new_free with (Ts:=rename_typs r Ts) (is':=is') (T:=rename_typ r T);
      eauto using init_map_commit.
    eapply Htypen in t; eauto.
  - eapply init_let with (L:=L \u K \u dom G'); eauto.
    intros z Hz. split_fresh. destruct (Hr z ltac:(assumption)) as [Hrz Hrinv].
    pose proof (@typing_map_push r Gamma G' z T ltac:(assumption) Hrz Hrinv ltac:(assumption)) as Hmap.
    pose proof (@init_map_push r Delta vs D' vs' z i ltac:(assumption) Hrz Hrinv) as Hd.
    specialize (H0 z ltac:(assumption) _ _ _ Hmap Hd).
    rewrite (proj1 (rename_terms_open r)), Hrz in H0. exact H0.
  - eapply init_llit with (L:=L \u K \u dom G'); eauto using init_map_commit.
    intros z Hz. split_fresh. destruct (Hr z ltac:(assumption)) as [Hrz Hrinv].
    pose proof (@typing_map_push r Gamma G' z T ltac:(assumption) Hrz Hrinv ltac:(assumption)) as Hmap.
    pose proof (@init_map_push_committed r Delta vs D' vs' z ltac:(assumption) Hrz Hrinv) as Hd.
    specialize (H0 z ltac:(assumption) _ _ _ Hmap Hd).
    rewrite (proj1 (rename_terms_open r)), Hrz in H0. exact H0.
  Unshelve. all: try assumption.
Qed.

Local Lemma rename_id_typ : forall T, rename_typ id T = T.
Proof. intros; apply (proj1 (rename_types_fixed id)); intros x _; reflexivity. Qed.

Local Lemma rename_id_trm : forall t, rename_trm id t = t.
Proof. intros; apply (proj1 (rename_terms_fixed id)); intros x _; reflexivity. Qed.

Local Lemma rename_id_lit : forall l, rename_lit id l = l.
Proof. intros; apply (proj2 (rename_terms_fixed id)); intros x _; reflexivity. Qed.

Local Lemma typing_map_identity : forall G G', extends G G' -> typing_map id G G'.
Proof.
  intros G G' H x T Hb. rewrite rename_id_typ. apply ty_var, H, Hb.
Qed.

Local Lemma init_identity : forall G D vs t i G' D' vs',
  G ⸴ D ⸴ vs ⊢i t ∶ i -> extends G G' -> init_map id D vs D' vs' ->
  G' ⸴ D' ⸴ vs' ⊢i t ∶ i.
Proof.
  intros. pose proof (proj1 (proj2 (proj2 (proj2 (rename_initialization identity_isolated))))
    _ _ _ _ _ H _ _ _ (typing_map_identity H0) H1) as Ht.
  rewrite rename_id_trm in Ht. exact Ht.
Qed.

Local Lemma commit_identity_lit : forall G D (l : lit) G' D',
  G ⸴ D ⊢c l -> extends G G' -> commit_map id D D' -> G' ⸴ D' ⊢c l.
Proof.
  intros. pose proof (proj1 (proj2 (proj2 (rename_initialization identity_isolated)))
    _ _ _ H _ _ (typing_map_identity H0) H1) as Hl.
  rewrite rename_id_lit in Hl. exact Hl.
Qed.

Local Lemma init_map_identity : forall D vs D' vs',
  commit_map id D D' ->
  (forall x i, x \in vs -> binds x i D -> binds x i D') ->
  vs \c vs' -> init_map id D vs D' vs'.
Proof.
  intros D vs D' vs' Hc Hf Hsub x i Hb [-> | Hv].
  - apply init_var_commit, Hc, Hb.
  - apply init_var_from_binding; auto.
Qed.

Local Lemma init_map_extends : forall D vs D' vs',
  extends D D' -> vs \c vs' -> init_map id D vs D' vs'.
Proof.
  intros D vs D' vs' Hext Hsub. apply init_map_identity; auto.
  intros x Hb. exact (Hext _ _ Hb).
Qed.

Local Lemma rename_one_same : forall z x, subst_fvar z x z = x.
Proof. intros. unfold subst_fvar. case_if*. Qed.

Local Lemma rename_one_other : forall z x y, y <> z -> subst_fvar z x y = y.
Proof. intros. unfold subst_fvar. case_if*. Qed.

Local Lemma rename_one_isolated : forall z x, isolated (subst_fvar z x) (\{z} \u \{x}).
Proof.
  unfold isolated. intros z x y H. split_fresh.
  assert (y <> z) by (intro E; subst; apply H, in_singleton_self).
  assert (y <> x) by (intro E; subst; apply H0, in_singleton_self).
  split.
  - apply rename_one_other; auto.
  - intros w E. destruct (classic (w = z)) as [-> | Hne].
    + rewrite rename_one_same in E. congruence.
    + rewrite rename_one_other in E by exact Hne. exact E.
Qed.

Local Lemma rename_one_fixed : forall z x X,
  z \notin X -> fixes (subst_fvar z x) X.
Proof. intros z x X H y Hy. apply rename_one_other. congruence. Qed.

Local Lemma typing_map_one : forall G z S G' a,
  extends G G' -> z \notin fv_env G -> z \notin fv S ->
  G' ⊢ trm_var (avar_f a) ∶ S ->
  typing_map (subst_fvar z a) (G & z ~ S) G'.
Proof.
  intros G z S G' a Hg Hfv Hs Ha x T Hb.
  apply binds_push_inv in Hb. destruct Hb as [[-> ->] | [Hne Hb]].
  - rewrite rename_one_same, (proj1 (rename_types_fixed _)); auto using rename_one_fixed.
  - rewrite rename_one_other by exact Hne.
    rewrite (proj1 (rename_types_fixed _)); eauto using ty_var, rename_one_fixed, fv_in_values_binds.
Qed.

Local Definition body_result (dep : bool) x (T : typ) := if dep then open x T else T.

Local Lemma open_at_typing : forall dep G G' L S a t T,
  (forall z, z \notin L -> G & z ~ S ⊢ open z t ∶ body_result dep z T) ->
  extends G G' -> G' ⊢ trm_var (avar_f a) ∶ S ->
  G' ⊢ open a t ∶ body_result dep a T.
Proof.
  intros dep G G' L S a t T H Hg Ha.
  destruct (var_fresh (L \u fv_env G \u fv S \u fv t \u fv T)) as [z Hz].
  split_fresh. pose proof (@typing_map_one G z S G' a Hg ltac:(assumption) ltac:(assumption) Ha) as Hm.
  pose proof (proj1 (rename_typing (@rename_one_isolated z a)) _ _ _
    (H z ltac:(assumption)) _ Hm) as Ht.
  rewrite (proj1 (rename_terms_open _)), rename_one_same,
    (proj1 (rename_terms_fixed _) t) in Ht by (apply rename_one_fixed; assumption).
  destruct dep; unfold body_result in *;
    rewrite ?(proj1 (rename_types_open _)), ?rename_one_same,
      (proj1 (rename_types_fixed _) T) in Ht by (apply rename_one_fixed; assumption);
    exact Ht.
Qed.

Local Lemma open_at_subtyping : forall G L S a T U,
  (forall z, z \notin L -> G & z ~ S ⊢ open z T <: open z U) ->
  G ⊢ trm_var (avar_f a) ∶ S -> G ⊢ open a T <: open a U.
Proof.
  intros G L S a T U H Ha.
  destruct (var_fresh (L \u fv_env G \u fv S \u fv T \u fv U)) as [z Hz].
  split_fresh.
  pose proof (@typing_map_one G z S G a ltac:(unfold extends; auto)
    ltac:(assumption) ltac:(assumption) Ha) as Hm.
  pose proof (proj1 (proj2 (proj2 (rename_typing (@rename_one_isolated z a)))) _ _ _
    (H z ltac:(assumption)) _ Hm) as Ht.
  rewrite !(proj1 (rename_types_open _)), !rename_one_same,
    (proj1 (rename_types_fixed _) T), (proj1 (rename_types_fixed _) U) in Ht
      by (apply rename_one_fixed; assumption).
  exact Ht.
Qed.

Local Lemma function_flow_at : forall G S T S' T' a,
  function_flow G S T S' T' -> G ⊢ trm_var (avar_f a) ∶ S' ->
  G ⊢ trm_var (avar_f a) ∶ S /\ G ⊢ open a T <: open a T'.
Proof.
  intros G S T S' T' a H. induction H; intros Ha.
  - split; auto using subtyp_refl.
  - split; eauto using ty_sub, open_at_subtyping.
  - destruct (IHfunction_flow2 Ha) as [Ha' Hsub'].
    destruct (IHfunction_flow1 Ha') as [Ha0 Hsub].
    eauto using subtyp_trans.
Qed.

Local Lemma init_map_one : forall D vs D' vs' z a i,
  init_map id D vs D' vs' ->
  init_var D' vs' a i ->
  init_map (subst_fvar z a) (D & z ~ i) (vs \u \{z}) D' vs'.
Proof.
  intros D vs D' vs' z a i Hm Ha x j Hb Haccess.
  apply binds_push_inv in Hb. destruct Hb as [[-> ->] | [Hne Hb]].
  - rewrite rename_one_same. exact Ha.
  - rewrite rename_one_other by exact Hne. apply Hm; auto.
    destruct Haccess as [Hc | Hv]; auto.
    rewrite in_union, in_singleton in Hv. intuition congruence.
Qed.

Local Lemma init_map_one_plain : forall D vs D' vs' z a i,
  init_map id D vs D' vs' ->
  init_var D' vs' a i ->
  init_map (subst_fvar z a) (D & z ~ i) vs D' vs'.
Proof.
  intros D vs D' vs' z a i H Ha.
  pose proof (@init_map_one D vs D' vs' z a i H Ha) as Hm.
  intros x j Hb Haccess. apply Hm; auto.
  destruct Haccess as [Hc | Hv]; auto. right. rewrite in_union; auto.
Qed.

Local Lemma open_at_init : forall (visible : bool) G G' D D' vs vs' L S a i t j,
  (forall z, z \notin L ->
    G & z ~ S ⸴ D & z ~ i ⸴ (if visible then vs \u \{z} else vs) ⊢i open z t ∶ j) ->
  extends G G' -> G' ⊢ trm_var (avar_f a) ∶ S ->
  init_map id D vs D' vs' -> init_var D' vs' a i ->
  G' ⸴ D' ⸴ vs' ⊢i open a t ∶ j.
Proof.
  intros b G G' D D' vs vs' L S a i t j H Hg Ha HmD Hai.
  destruct (var_fresh (L \u fv_env G \u fv S \u fv t)) as [z Hz].
  split_fresh. pose proof (@typing_map_one G z S G' a Hg ltac:(assumption) ltac:(assumption) Ha) as Hm.
  assert (Hd : init_map (subst_fvar z a) (D & z ~ i)
      (if b then vs \u \{z} else vs) D' vs').
  { destruct b; simpl; eauto using init_map_one, init_map_one_plain. }
  pose proof (proj1 (proj2 (proj2 (proj2 (rename_initialization (@rename_one_isolated z a)))))
    _ _ _ _ _ (H z ltac:(assumption)) _ _ _ Hm Hd) as Ht.
  rewrite (proj1 (rename_terms_open _)), rename_one_same,
    (proj1 (rename_terms_fixed _) t) in Ht by (apply rename_one_fixed; assumption).
  exact Ht.
Qed.

Local Lemma open_at_commit : forall G G' D D' L S a (t : trm),
  (forall z, z \notin L -> G & z ~ S ⸴ D & z ~ committed ⊢c open z t) ->
  extends G G' -> G' ⊢ trm_var (avar_f a) ∶ S ->
  commit_map id D D' -> binds a committed D' ->
  G' ⸴ D' ⊢c open a t.
Proof.
  intros G G' D D' L S a t H Hg Ha Hd Hac.
  destruct (var_fresh (L \u fv_env G \u fv S \u fv t)) as [z Hz].
  split_fresh. pose proof (@typing_map_one G z S G' a Hg ltac:(assumption) ltac:(assumption) Ha) as Hm.
  assert (Hmd : commit_map (subst_fvar z a) (D & z ~ committed) D').
  { intros x Hb. apply binds_push_inv in Hb. destruct Hb as [[-> _] | [Hne Hb]].
    - rewrite rename_one_same. exact Hac.
    - rewrite rename_one_other by exact Hne. apply Hd, Hb. }
  pose proof (proj1 (rename_initialization (@rename_one_isolated z a))
    _ _ _ (H z ltac:(assumption)) _ _ Hm Hmd) as Ht.
  rewrite (proj1 (rename_terms_open _)), rename_one_same,
    (proj1 (rename_terms_fixed _) t) in Ht by (apply rename_one_fixed; assumption).
  exact Ht.
Qed.

Local Definition effect_vars (e : effects) := from_list (List.map fst e).

Local Lemma rename_effects_fixed : forall r e,
  fixes r (effect_vars e) -> rename_effects r e = e.
Proof.
  intros r e. unfold effect_vars, rename_effects. induction e as [|[x a] e IH]; simpl; auto.
  rewrite from_list_cons. intro H. destruct (fixes_union H) as [Hx He].
  change ((r x, a) :: List.map (rename_effect r) e = (x,a) :: e)%list.
  rewrite (Hx _ (in_singleton_self x)), (IH He). reflexivity.
Qed.

Local Lemma open_at_effect : forall L t e a,
  (forall z, z \notin L -> ⊢e open z t ∶ e) -> ⊢e open a t ∶ e.
Proof.
  intros L t e a H.
  destruct (var_fresh (L \u fv t \u effect_vars e)) as [z Hz].
  split_fresh. pose proof (rename_effect_typing (@rename_one_isolated z a) (H z ltac:(assumption))) as He.
  rewrite (proj1 (rename_terms_open _)), rename_one_same, (proj1 (rename_terms_fixed _) t),
    rename_effects_fixed in He by (apply rename_one_fixed; assumption).
  exact He.
Qed.

Local Lemma stack_transport : forall G D E fs T i es U,
  ty_stack G D E fs T i es U ->
  forall G' D' E', extends G G' -> commit_map id D D' ->
  (forall x j, x \in list_dom_union E -> binds x j D -> binds x j D') ->
  List.Forall2 (fun a b : eff_ctx => dom a \c dom b) E E' ->
  ty_stack G' D' E' fs T i es U.
Proof.
  intros G D E fs T i es U H. induction H; intros G' D' E' Hg Hd Hb HE;
    inversion HE as [|EO EN EsO EsN Hsub Htail]; subst.
  - inversion Htail; subst. constructor. eapply (proj1 (proj2 (proj2 weaken_typing))); eauto.
  - eapply ty_stack_let with (L:=L); eauto.
    + intros. eapply (proj1 weaken_typing); eauto using extends_suffix.
    + intros z Hz. eapply init_identity; eauto using extends_suffix.
      apply init_map_push with (r:=id); try reflexivity; auto.
      eapply init_map_identity; eauto. intros x j Hx HxD. apply Hb; auto.
      simpl. rewrite in_union; auto.
  - eapply ty_stack_ret_free; eauto.
    + eapply (proj1 weaken_typing); eauto.
    + eapply init_identity; eauto. eapply init_map_identity; eauto.
      intros x' j Hx HxD. apply Hb; auto. simpl. rewrite in_union; auto.
  - eapply ty_stack_ret_committed.
    + eapply IHty_stack; eauto. intros x' j Hx HxD. apply Hb; auto.
      simpl. rewrite in_union; auto.
    + eapply (proj1 weaken_typing); eauto.
    + eapply init_identity; eauto. eapply init_map_identity; eauto.
      intros x' j Hx HxD. apply Hb; auto. simpl. rewrite in_union; auto.
Qed.

Local Lemma doms_refl : forall E : list eff_ctx,
  List.Forall2 (fun a b : eff_ctx => dom a \c dom b) E E.
Proof. induction E; constructor; auto using subset_refl. Qed.

Local Lemma committed_var_typing : forall G D vs x,
  binds x committed D -> G ⸴ D ⸴ vs ⊢i trm_var (avar_f x) ∶ committed.
Proof. eauto using init_var_binds, init_var_commit. Qed.

Local Lemma free_var_typing : forall G D vs x,
  binds x free D -> x \in vs -> G ⸴ D ⸴ vs ⊢i trm_var (avar_f x) ∶ free.
Proof. eauto using init_var_binds, init_var_free. Qed.

(* Heap updates preserve the bindings outside the updated object. *)
Local Lemma heap_update_bindings : forall A (E1 E2 : env A) x v w,
  x # E2 ->
  binds x v (E1 & x ~ v & E2) /\ binds x w (E1 & x ~ w & E2) /\
  (forall z u, z <> x -> binds z u (E1 & x ~ v & E2) <-> binds z u (E1 & x ~ w & E2)) /\
  dom (E1 & x ~ v & E2) = dom (E1 & x ~ w & E2).
Proof.
  intros A E1 E2 x v w Hn. repeat split; try solve [apply binds_middle_eq; exact Hn].
  - intro Hb. apply binds_middle_inv in Hb.
    destruct Hb as [Hb | [[_ [E _]] | [Hz [_ Hb]]]]; try contradiction.
    + apply binds_concat_right. exact Hb.
    + apply binds_concat_left; [apply binds_push_neq; assumption|assumption].
  - intro Hb. apply binds_middle_inv in Hb.
    destruct Hb as [Hb | [[_ [E _]] | [Hz [_ Hb]]]]; try contradiction.
    + apply binds_concat_right. exact Hb.
    + apply binds_concat_left; [apply binds_push_neq; assumption|assumption].
  - rewrite !dom_concat, !dom_single. reflexivity.
Qed.

Local Lemma defs_update_preserves_absence : forall hds a y hds',
  defs_update hds a y hds' -> forall l, labels_hasnt hds l -> labels_hasnt hds' l.
Proof.
  intros hds a y hds' H. induction H; intros l Hnone;
    unfold labels_hasnt in *; simpl in *; case_if in Hnone; try discriminate; try case_if; try congruence; auto.
  exact (IHdefs_update l Hnone).
Qed.

Local Lemma defs_update_label_present : forall hds a y hds',
  defs_update hds a y hds' -> ~ labels_hasnt hds (label_trm a).
Proof.
  intros hds a y hds' H. induction H; intro Hnone;
    unfold labels_hasnt in *; simpl in *; case_if in Hnone; try discriminate; try case_if; try congruence; auto.
Qed.

Local Lemma defs_update_typed : forall hds a y hds',
  defs_update hds a y hds' ->
  forall G R V, G ⊢ hds ∶ R ->
  record_has R (dec_trm a V V) ->
  G ⊢ trm_var (avar_f y) ∶ V -> G ⊢ hds' ∶ R.
Proof.
  intros hds a y hds' Hup. induction Hup; intros G R V Hty Hr Hy;
    inversion Hty; subst; inversion Hr; subst.
  - apply ty_defs_one, ty_heap_def_trm_some. exact Hy.
  - exfalso.
    match goal with Ht : _ ⊢ hds ∶ _, Hfield : record_has _ (dec_trm a V V) |- _ =>
      destruct (heap_defs_field Ht Hfield) as [w [Hw _]]
    end.
    unfold labels_has, labels_hasnt in *. simpl in *. congruence.
  - match goal with Hfield : record_has (typ_rcd _) _ |- _ => inversion Hfield; subst end.
    apply ty_defs_cons; auto using ty_heap_def_trm_some.
  - inversion Hup.
  - eapply ty_defs_cons; eauto using defs_update_preserves_absence.
  - match goal with Hfield : record_has (typ_rcd _) _ |- _ => inversion Hfield; subst end.
    match goal with H : _ ⊢ d ∶d _ |- _ => inversion H; subst end;
      exfalso; eapply defs_update_label_present; eassumption.
Qed.

Local Lemma defs_update_committed : forall hds a y hds',
  defs_update hds a y hds' ->
  forall D, committed_heap_defs D hds -> binds y committed D ->
  committed_heap_defs D hds'.
Proof.
  intros hds a y hds' H. induction H; intros D Hc Hy; inversion Hc; subst;
    eauto using committed_heap_defs_cons, committed_heap_def_trm.
Qed.

Local Lemma defs_update_points : forall hds a y hds',
  defs_update hds a y hds' ->
  heap_defs_points_to hds' \c \{y} \u heap_defs_points_to hds.
Proof.
  intros hds a y hds' H. induction H; simpl.
  - destruct o; simpl; intros z Hz; repeat rewrite in_union in *; intuition.
  - destruct d as [|b [w|]]; simpl; try exact IHdefs_update.
    intros z Hz. rewrite in_union in Hz |- *.
    destruct Hz as [Hz | Hz].
    + right. rewrite in_union; auto.
    + specialize (IHdefs_update _ Hz). rewrite in_union in IHdefs_update.
      destruct IHdefs_update; auto. right. rewrite in_union; auto.
Qed.

Local Lemma defs_update_effect_subset : forall hds a y hds',
  defs_update hds a y hds' ->
  forall x, from_list (heap_defs_effs x hds') \c from_list (heap_defs_effs x hds).
Proof.
  intros hds a y hds' H. induction H; intros z; simpl.
  - destruct o; simpl; try apply subset_refl. rewrite from_list_cons.
    intros p Hp; rewrite in_union; auto.
  - destruct d as [|b [w|]]; simpl; auto. rewrite !from_list_cons.
    intros p Hp. rewrite in_union in *. firstorder.
Qed.

Local Lemma no_label_no_effect : forall hds x a,
  labels_hasnt hds (label_trm a) -> (x,a) \notin from_list (heap_defs_effs x hds).
Proof.
  intros hds x a H. unfold labels_hasnt in H.
  induction hds as [|[A T|b [w|]] hds IH]; simpl in *;
    try solve [rewrite from_list_nil; apply notin_empty].
  all: case_if in H; try discriminate; auto.
  rewrite from_list_cons, notin_union. split; auto.
  intro Hx. rewrite in_singleton in Hx. inversion Hx; subst. auto.
Qed.

Local Lemma defs_update_removes_effect : forall hds a y hds',
  defs_update hds a y hds' ->
  forall G R, G ⊢ hds ∶ R -> forall x, (x,a) \notin from_list (heap_defs_effs x hds').
Proof.
  intros hds a y hds' H. induction H; intros G R Hty z; inversion Hty; subst.
  - simpl. rewrite from_list_nil. apply notin_empty.
  - simpl. eapply no_label_no_effect. eassumption.
  - inversion H.
  - destruct d as [|b [w|]]; simpl; eauto. rewrite from_list_cons, notin_union.
    split; eauto. intro Hp. rewrite in_singleton in Hp. inversion Hp; subst.
    eapply defs_update_label_present; eassumption.
Qed.

Local Lemma heap_correspond_update : forall G Sigma Sigma' x R ds ds',
  heap_correspond G Sigma -> binds x (item_obj R ds) Sigma ->
  binds x (item_obj R ds') Sigma' -> dom Sigma = dom Sigma' ->
  (forall z itm, z <> x -> binds z itm Sigma -> binds z itm Sigma') ->
  G ⊢ ds' ∶ open x R ->
  heap_correspond G Sigma'.
Proof.
  intros G Sigma Sigma' x R ds ds' [Hdom Hheap] Hx Hx' Hds Hother Hty.
  split; [congruence|]. intros z Hz. specialize (Hheap _ Hz).
  destruct (classic (z = x)) as [->|Hne].
  - inversion Hheap; subst.
    + pose proof (binds_functional Hx H0) as E; discriminate.
    + match goal with H : binds x (item_obj _ _) Sigma |- _ =>
        pose proof (binds_functional Hx H) as Eq
      end. inversion Eq; subst. eauto using ty_item_obj_s.
  - inversion Hheap; subst; eauto using ty_item_lit_s, ty_item_obj_s.
Qed.

Local Lemma free_item_extend : forall D E x itm D' E',
  free_heap_item D E x itm ->
  (forall z i, binds z i D -> binds z i D') ->
  (forall z es, binds z es E -> binds z es E') ->
  free_heap_item D' E' x itm.
Proof.
  intros D E x itm D' E' H Hd He. inversion H as [D0 E0 x0 T ds [Hb [Hes Hp]]]; subst.
  constructor. repeat split; auto. intros y Hy. specialize (Hp _ Hy).
  destruct Hp as [Hc|[Hin Hf]]; auto. right. split; auto.
  apply get_some in Hin. destruct Hin as [es Hb'].
  apply get_some_inv with (v:=es). apply He. exact Hb'.
Qed.

Local Lemma free_dom_not_committed : forall D E Sigma x,
  free_sub_heap E Sigma D -> x \in dom E -> binds x committed D -> False.
Proof.
  intros D E Sigma x H Hin Hb. apply get_some in Hin. destruct Hin as [e He].
  destruct (H _ _ He) as [_ [itm [_ Hf]]]. inversion Hf as [? ? ? ? ? [Hfree _]]; subst.
  pose proof (binds_functional Hb Hfree); discriminate.
Qed.

Local Lemma free_dom_in_heap : forall G D Sigma E,
  free_sub_heaps G D Sigma E -> list_dom_union E \c dom Sigma.
Proof.
  intros G D Sigma E H. induction H; simpl.
  - intros x Hx. exfalso. exact (in_empty_inv Hx).
  - intros x Hx. rewrite in_union in Hx. destruct Hx as [Hx | Hx]; auto.
    apply get_some in Hx. destruct Hx as [es He].
    destruct (H0 _ _ He) as [_ [itm [Hb _]]]. exact (get_some_inv Hb).
Qed.

Local Lemma free_stack_heap_update : forall G D Sigma Sigma' E x R ds ds' a y,
  free_sub_heaps G D Sigma E ->
  binds x (item_obj R ds) Sigma -> binds x (item_obj R ds') Sigma' ->
  dom Sigma = dom Sigma' ->
  (forall z itm, z <> x -> binds z itm Sigma -> binds z itm Sigma') ->
  defs_update ds a y ds' -> (binds x committed D -> binds y committed D) ->
  (forall e, List.In e E -> x \notin dom e) ->
  free_sub_heaps G D Sigma' E.
Proof.
  intros G D Sigma Sigma' E x R ds ds' a y Hfree Hx Hx' Hdom Hother Hup Hy Hskip.
  induction Hfree.
  - constructor. destruct H as [Hg [Hd Hitems]].
    split; [assumption|]. split; [congruence|].
    intros z itm Hc Hb. destruct (classic (z = x)) as [-> | Hne].
    + assert (E : itm = item_obj R ds') by (eapply binds_functional; eauto). subst itm.
      specialize (Hitems _ _ Hc Hx). inversion Hitems; subst.
      constructor. eauto using defs_update_committed.
    + apply Hitems with (x:=z); auto.
      (* The unchanged binding is recovered from the domain and functionality. *)
      assert (z \in dom Sigma) by (rewrite Hdom; exact (get_some_inv Hb)).
      apply get_some in H. destruct H as [itm0 Hb0].
      pose proof (Hother _ _ Hne Hb0) as Hb0'.
      assert (itm = itm0) by (eapply binds_functional; eauto). subst. exact Hb0.
  - constructor; auto.
    + intros z es He. destruct (H0 _ _ He) as [Hself [itm [Hb Hf]]].
      split; auto. exists itm. split; auto.
      apply Hother; auto. intro Eq. subst z. eapply Hskip; [left; reflexivity|exact (get_some_inv He)].
    + apply IHHfree; try assumption. intros e Hin. apply Hskip. right; assumption.
Qed.

Local Lemma free_stack_each : forall G D Sigma E e,
  free_sub_heaps G D Sigma E -> List.In e E -> free_sub_heap e Sigma D.
Proof.
  intros G D Sigma E e H. induction H; simpl; intros HIn.
  - contradiction.
  - destruct HIn as [-> | HIn]; auto.
Qed.

Local Lemma dom_stack_each : forall E (e : eff_ctx) x,
  List.In e E -> x \in dom e -> x \in list_dom_union E.
Proof.
  intros E e x H. induction E as [|e0 E IH]; intros; simpl in *; try contradiction.
  rewrite in_union. destruct H as [-> | H]; auto.
Qed.

Local Lemma init_var_free_inv : forall D vs x,
  init_var D vs x free -> x \in vs /\ binds x free D.
Proof.
  intros D vs x H. remember free as i eqn:E. induction H; subst; try discriminate; auto.
  inversion H0; subst; auto.
Qed.

Local Lemma assign_initialization : forall G D (E : eff_ctx) x a y i,
  inert_inits D ->
  G ⸴ D ⸴ dom E ⊢i trm_asn (avar_f x) a (avar_f y) ∶ i ->
  well_pointed D E x /\ well_pointed D E y /\
  (binds x committed D -> binds y committed D) /\
  G ⸴ D ⸴ dom E ⊢i trm_var (avar_f y) ∶ i.
Proof.
  intros G D E x a y i Hid H. inversion H; subst.
  - match goal with Hc : _ ⸴ _ ⊢c trm_asn _ _ _ |- _ => inversion Hc; subst end.
    repeat match goal with Hc : _ ⸴ _ ⊢c trm_var _ |- _ => inversion Hc; subst; clear Hc end.
    eauto 8 using committed_var_typing.
  - repeat match goal with
      Hvar : _ ⸴ _ ⸴ _ ⊢i trm_var _ ∶ _ |- _ => apply var_initialization in Hvar
    end.
    eauto 8 using init_var_status, init_var_committed_inv, init_var_binds.
  - assert (Hx : x \in dom E /\ binds x free D) by
      (apply init_var_free_inv, var_initialization with (G:=G); assumption).
    assert (Hy : y \in dom E /\ binds y free D) by
      (apply init_var_free_inv, var_initialization with (G:=G); assumption).
    repeat split; auto.
    intro Hc. pose proof (binds_functional Hc (proj2 Hx)). discriminate.
Qed.

Local Lemma assignment_effect_tail : forall (e e' : effects) x a p,
  (e' = nil \/ e' = ((x,a) :: nil)%list) ->
  p \in from_list (e' ++ e)%list -> p <> (x,a) -> p \in from_list e.
Proof.
  intros e e' x a p [-> | ->] Hin Hne; simpl in *; auto.
  rewrite from_list_cons, in_union, in_singleton in Hin. intuition congruence.
Qed.

Local Lemma assignment_head : forall G D E Et Sigma Sigma' x a y R ds ds' e' e,
  all_notin (dom E) (list_dom_union Et) ->
  free_sub_heap E Sigma D ->
  free_sub_heaps G D Sigma Et ->
  defs_update ds a y ds' -> G ⊢ ds ∶ open x R ->
  binds x (item_obj R ds) Sigma -> binds x (item_obj R ds') Sigma' ->
  dom Sigma = dom Sigma' ->
  (forall z itm, z <> x -> binds z itm Sigma -> binds z itm Sigma') ->
  well_pointed D E x -> well_pointed D E y ->
  (binds x committed D -> binds y committed D) ->
  eff_ctx_corr_one E (e' ++ e)%list ->
  (e' = nil \/ e' = ((x,a) :: nil)%list) ->
  exists Enew, dom Enew = dom E /\
    free_sub_heaps G D Sigma' (Enew :: Et) /\ eff_ctx_corr_one Enew e.
Proof.
  intros G D E Et Sigma Sigma' x a y R ds ds' e' e Hdis Hhead Htail Hup Hty
    Hx Hx' Hdom Hother Hpx Hpy Hy Hcorr He.
  assert (Hskip : forall Et0, List.In Et0 Et -> x # Et0).
  { intros E0 HIn Hin. destruct Hpx as [Hc | [Hfree _]].
    - eapply free_dom_not_committed; [eapply free_stack_each; eassumption | eassumption | eassumption].
    - apply (Hdis _ Hfree). eapply dom_stack_each; eassumption. }
  pose proof (free_stack_heap_update Htail Hx Hx' Hdom Hother Hup Hy Hskip) as Htail'.
  assert (Hrest : forall z es p, z <> x -> binds z es E ->
      p \in from_list es -> p \in from_list e).
  { intros z es [w b] Hz Hb Hp. eapply assignment_effect_tail; eauto.
    intro Eq. injection Eq as -> ->. apply Hz. symmetry.
    exact (proj1 (Hhead _ _ Hb) _ _ Hp). }
  destruct Hpx as [Hxc | [Hxin Hxf]].
  - assert (Hn : x # E) by (intro Hin; eapply free_dom_not_committed; eassumption).
    exists E. split; auto. split.
    + constructor; auto. intros z es Hb.
      assert (Hz : z <> x) by (intro Eq; subst z; apply Hn; exact (get_some_inv Hb)).
      destruct (Hhead _ _ Hb) as [Hself [itm [Hit Hf]]].
      split; auto. exists itm. split; auto.
    + intros z es Hb p Hp. eapply Hrest; eauto.
      intro Eq. subst z. exact (Hn (get_some_inv Hb)).
  - set (Enew := E & x ~ heap_defs_effs x ds').
    assert (HE : dom Enew = dom E).
    { unfold Enew. rewrite dom_push. apply fset_extens; intros z Hz.
      - rewrite in_union, in_singleton in Hz. destruct Hz as [-> | Hz]; assumption.
      - rewrite in_union; auto. }
    assert (Holds : binds x (heap_defs_effs x ds) E).
    { apply get_some in Hxin. destruct Hxin as [es Hes].
      destruct (Hhead _ _ Hes) as [_ [itm [Hit Hf]]].
      assert (itm = item_obj R ds) by (eapply binds_functional; eauto). subst.
      inversion Hf as [? ? ? ? ? [_ [Hes' _]]]; subst. exact Hes'. }
    assert (Hpoint : forall z, well_pointed D E z -> well_pointed D Enew z)
      by (intros z; rewrite <- HE; auto).
    exists Enew. split; auto. split.
    + constructor; [rewrite HE; exact Hdis| |exact Htail'].
      intros z es Hes. unfold Enew in Hes. apply binds_push_inv in Hes.
      destruct Hes as [[-> ->] | [Hne Hes]].
      * split.
        -- intros w b Hwb. apply (proj1 (Hhead _ _ Holds) w b).
           eapply defs_update_effect_subset; eassumption.
        -- exists (item_obj R ds'). split; auto. constructor.
           repeat split; auto. unfold Enew; apply binds_push_eq.
           intros w Hw. pose proof (defs_update_points Hup Hw) as Hor.
           rewrite in_union, in_singleton in Hor. destruct Hor as [-> | Hor]; auto.
           apply Hpoint. destruct (Hhead _ _ Holds) as [_ [itm [Hit Hf]]].
           assert (itm = item_obj R ds) by (eapply binds_functional; eauto). subst.
           inversion Hf as [? ? ? ? ? [_ [_ Hpts]]]; subst. auto.
      * destruct (Hhead _ _ Hes) as [Hself [itm [Hit Hf]]].
        split; auto. exists itm. split; auto.
        inversion Hf as [? ? ? ? ? [Hfree [Hes' Hpts]]]; subst.
        constructor. repeat split; auto.
        -- unfold Enew. apply binds_push_neq; assumption.
    + intros z es Hes p Hp. unfold Enew in Hes. apply binds_push_inv in Hes.
      destruct Hes as [[-> ->] | [Hne Hes]]; [|eauto].
      eapply assignment_effect_tail; [exact He| |].
      * eapply Hcorr; [exact Holds|]. eapply defs_update_effect_subset; eassumption.
      * intro Eq. subst p. eapply defs_update_removes_effect; eassumption.
Qed.

Local Lemma committed_defs_transport : forall D ds,
  committed_heap_defs D ds -> forall D', commit_map id D D' -> committed_heap_defs D' ds.
Proof.
  intros D ds H. induction H; intros D' Hmap; constructor; auto.
  inversion H0; subst; eauto using committed_heap_def_typ, committed_heap_def_trm.
Qed.

Local Lemma committed_item_transport : forall G D itm G' D',
  committed_heap_item G D itm ->
  extends G G' -> commit_map id D D' -> committed_heap_item G' D' itm.
Proof.
  intros G D itm G' D' H Hg Hd. inversion H; subst;
    eauto using committed_heap_lit, committed_heap_obj, commit_identity_lit, committed_defs_transport.
Qed.

Local Lemma heap_defs_weaken : forall G (hds : heap_defs) T G',
  G ⊢ hds ∶ T -> extends G G' -> G' ⊢ hds ∶ T.
Proof.
  intros G hds T G' H. induction H; intro Hg.
  - apply ty_defs_one. inversion H; subst; eauto using ty_heap_def_typ, ty_heap_def_trm_none,
      ty_heap_def_trm_some, weaken_term.
  - apply ty_defs_cons; auto.
    inversion H0; subst; eauto using ty_heap_def_typ, ty_heap_def_trm_none,
      ty_heap_def_trm_some, weaken_term.
Qed.

Local Lemma heap_correspond_push : forall G Sigma x B itm,
  heap_correspond G Sigma -> x # Sigma ->
  (match itm with
   | item_lit l => G & x ~ B ⊢ l ∶ B
   | item_obj R hds => B = typ_bnd R /\ G & x ~ B ⊢ hds ∶ open x R
   end) ->
  heap_correspond (G & x ~ B) (Sigma & x ~ itm).
Proof.
  intros G Sigma x B itm [Hdom Hheap] Hfresh Hnew.
  assert (Hg : extends G (G & x ~ B)) by (apply extends_push; congruence).
  split; [rewrite !dom_push, Hdom; reflexivity|].
  intros z Hz. rewrite dom_push, in_union, in_singleton in Hz.
  destruct (classic (z = x)) as [-> | Hne].
  - destruct itm as [R ds|l].
    + destruct Hnew as [-> Hty]. eapply ty_item_obj_s; eauto using binds_push_eq.
    + eapply ty_item_lit_s; eauto using binds_push_eq.
  - destruct Hz as [Hz | Hz]; try congruence.
    specialize (Hheap _ Hz). inversion Hheap; subst;
      eauto using ty_item_obj_s, ty_item_lit_s, binds_push_neq, heap_defs_weaken,
      weaken_literal.
Qed.

Local Lemma inert_inits_push : forall D x i,
  inert_inits D -> (i = free \/ i = committed) -> inert_inits (D & x ~ i).
Proof.
  intros D x i H Hold z j Hb. apply binds_push_inv in Hb.
  destruct Hb as [[-> ->] | [_ Hb]]; [exact Hold | exact (H _ _ Hb)].
Qed.

Local Lemma free_stack_push : forall G D Sigma E x B i itm,
  free_sub_heaps G D Sigma E -> x # Sigma ->
  (i = committed -> committed_heap_item (G & x ~ B) (D & x ~ i) itm) ->
  free_sub_heaps (G & x ~ B) (D & x ~ i) (Sigma & x ~ itm) E.
Proof.
  intros G D Sigma E x B i itm H Hfresh Hnew.
  destruct (committed_heap_of_stack H) as [Hgdom [Hdom _]].
  assert (Hg : extends G (G & x ~ B)) by (apply extends_push; congruence).
  assert (Hd : extends D (D & x ~ i)) by (apply extends_push; congruence).
  assert (Hs : extends Sigma (Sigma & x ~ itm)) by (apply extends_push; assumption).
  induction H.
  - constructor. destruct H as [HGD [HDS Hitems]].
    split; [rewrite !dom_push, HGD; reflexivity|].
    split; [rewrite !dom_push, HDS; reflexivity|].
    intros z w Hc Hb.
    apply binds_push_inv in Hb. destruct Hb as [[-> ->] | [Hne Hb]].
    + apply Hnew. symmetry. eauto using binds_push_eq_inv.
    + pose proof (binds_push_neq_inv Hc Hne) as Hc0.
      eapply committed_item_transport; [eapply Hitems; eassumption | exact Hg |].
      intros w0 Hw. apply Hd, Hw.
  - constructor; auto.
    intros z es Hb. destruct (H0 _ _ Hb) as [Hself [w [Hw Hf]]].
    split; auto. exists w. split; auto. eapply free_item_extend; eauto.
Qed.

(* A completed effect context can be promoted to committed bindings. *)
Local Definition promote (D : init_ctx) (E : eff_ctx) :=
  D & EnvOps.map (fun _ : effects => committed) E.

Local Lemma promote_in : forall D E x, x \in dom E -> binds x committed (promote D E).
Proof.
  intros D E x H. apply get_some in H. destruct H as [es Hb].
  unfold promote. apply binds_concat_right. exact (binds_map (fun _ : effects => committed) Hb).
Qed.

Local Lemma promote_out : forall D E x i, x # E ->
  binds x i (promote D E) <-> binds x i D.
Proof.
  intros D E x i H. unfold promote.
  assert (Hx : x # EnvOps.map (fun _ : effects => committed) E) by (rewrite dom_map; exact H).
  split; intro Hb.
  - exact (binds_concat_left_inv Hb Hx).
  - exact (binds_concat_left Hb Hx).
Qed.

Local Lemma promote_committed : forall D E, commit_map id D (promote D E).
Proof.
  intros D E x Hb. change (binds x committed (promote D E)).
  destruct (classic (x \in dom E)) as [Hin|Hout].
  - apply promote_in, Hin.
  - apply (proj2 (promote_out D committed Hout)), Hb.
Qed.

Local Lemma promote_inert : forall D E,
  inert_inits D -> inert_inits (promote D E).
Proof.
  intros D E Hi x i Hb. destruct (classic (x \in dom E)) as [Hin|Hout].
  - right. eapply binds_functional; [exact Hb | apply promote_in, Hin].
  - eapply Hi. exact (proj1 (promote_out D i Hout) Hb).
Qed.

Local Lemma initialized_defs : forall D x hds,
  heap_defs_effs x hds = nil ->
  (forall y, y \in heap_defs_points_to hds -> binds y committed D) ->
  committed_heap_defs D hds.
Proof.
  intros D x hds. induction hds as [|[A T|a [y|]] hds IH]; simpl; intros He Hp.
  - constructor.
  - constructor; auto. constructor.
  - constructor.
    + apply IH; auto. intros z Hz. apply Hp. rewrite in_union; auto.
    + constructor. apply Hp. rewrite in_union. left. apply in_singleton_self.
  - discriminate.
Qed.

Local Lemma promote_items : forall G D Sigma E,
  free_sub_heap E Sigma D -> eff_ctx_corr_one E nil ->
  forall x itm, x \in dom E -> binds x itm Sigma ->
  committed_heap_item G (promote D E) itm.
Proof.
  intros G D Sigma E Hfree Hcorr x itm Hin Hb.
  apply get_some in Hin. destruct Hin as [es Hes].
  destruct (Hfree _ _ Hes) as [_ [itm' [Hit Hf]]].
  assert (itm' = itm) by (eapply binds_functional; eauto). subst itm'.
  inversion Hf as [? ? ? ? ds [_ [Hes' Hpt]]]; subst.
  constructor. eapply initialized_defs with (x:=x).
  - destruct (heap_defs_effs x ds) as [|p ps] eqn:He; auto.
    exfalso. specialize (Hcorr _ _ Hes' p).
    rewrite from_list_cons, from_list_nil in Hcorr.
    apply (in_empty_inv (Hcorr ltac:(rewrite in_union; left; apply in_singleton_self))).
  - intros z Hz. destruct (Hpt _ Hz) as [Hc | [HzE _]].
    + exact (@promote_committed D E z Hc).
    + apply promote_in, HzE.
Qed.

Local Lemma promote_stack : forall G D Sigma E Et,
  free_sub_heap E Sigma D -> eff_ctx_corr_one E nil ->
  all_notin (dom E) (list_dom_union Et) ->
  free_sub_heaps G D Sigma Et ->
  free_sub_heaps G (promote D E) Sigma Et.
Proof.
  intros G D Sigma E Et Hhead Hcorr Hdis Htail. induction Htail.
  - constructor. destruct H as [HG [HD Hitems]].
    assert (Hd : dom (promote Delta E) = dom Delta).
    { unfold promote. rewrite dom_concat, dom_map. apply fset_extens; intros x Hx.
      - rewrite in_union in Hx. destruct Hx as [Hx | Hx]; auto.
        rewrite HD. apply get_some in Hx. destruct Hx as [es He].
        destruct (Hhead _ _ He) as [_ [itm [Hb _]]]. exact (get_some_inv Hb).
      - rewrite in_union; auto. }
    split; [congruence|]. split; [congruence|].
    intros x itm Hc Hit. destruct (classic (x \in dom E)) as [Hin | Hout].
    + eauto using promote_items.
    + apply (proj1 (promote_out Delta committed Hout)) in Hc.
      eapply committed_item_transport; eauto using promote_committed.
  - constructor; auto.
    + intros x es He. destruct (H0 _ _ He) as [Hself [itm [Hit Hf]]].
      split; auto. exists itm. split; auto.
      assert (Hout : forall y, y \in dom ℰ -> y # E).
      { intros y Hy Hbad. apply (Hdis y Hbad). simpl. rewrite in_union; auto. }
      inversion Hf as [? ? ? ? ? [Hf0 [He0 Hp]]]; subst.
      constructor. repeat split; auto.
      * apply (proj2 (promote_out Delta free (Hout _ (get_some_inv He)))), Hf0.
      * intros y Hy. destruct (Hp _ Hy) as [Hc | [Hin Hfy]].
        -- left. apply promote_committed, Hc.
        -- right. split; auto. apply (proj2 (promote_out Delta free (Hout _ Hin))), Hfy.
    + apply IHHtail; try assumption. intros x Hx Hin. apply (Hdis _ Hx). simpl. rewrite in_union; auto.
Qed.

Local Lemma from_list_append : forall A (xs ys : list A),
  from_list (xs ++ ys)%list = from_list xs \u from_list ys.
Proof.
  intros. apply fset_extens; intros p Hp;
    rewrite from_list_iff, ?List.in_app_iff in *; rewrite ?in_union, ?from_list_iff in *; auto.
Qed.

Local Lemma cofinite_let_initialization : forall G D vs S t body i,
  G ⸴ D ⸴ vs ⊢i trm_let S t body ∶ i ->
  exists L j, G ⸴ D ⸴ vs ⊢i t ∶ j /\
    forall x, x \notin L -> G & x ~ S ⸴ D & x ~ j ⸴ vs \u \{x} ⊢i open x body ∶ i.
Proof.
  intros G D vs S t body i H. inversion H; subst.
  - match goal with Hc : _ ⸴ _ ⊢c trm_let _ _ _ |- _ => inversion Hc; subst end.
    eexists _, committed. split; eauto using init_commit.
  - eauto.
Qed.

Local Lemma cofinite_lit_initialization : forall G D vs S l body i,
  G ⸴ D ⸴ vs ⊢i trm_lit S l body ∶ i ->
  exists L, G ⸴ D ⊢c l /\
    forall x, x \notin L -> G & x ~ S ⸴ D & x ~ committed ⸴ vs ⊢i open x body ∶ i.
Proof.
  intros G D vs S l body i H. inversion H; subst.
  - match goal with Hc : _ ⸴ _ ⊢c trm_lit _ _ _ |- _ => inversion Hc; subst end.
    eexists; split; eauto using init_commit.
  - eauto.
Qed.

Local Lemma cofinite_let_effect : forall S t body es,
  ⊢e trm_let S t body ∶ es ->
  exists L e e', es = (e ++ e')%list /\ ⊢e t ∶ e /\
    (forall x, x \notin L -> ⊢e open x body ∶ e').
Proof.
  intros S t body es H. inversion H; subst.
  - exists (\{} : vars), (nil : effects), (nil : effects). repeat split; auto using eff_ignore.
  - eauto 8.
Qed.

Local Lemma cofinite_lit_effect : forall S l body es,
  ⊢e trm_lit S l body ∶ es ->
  exists L, forall x, x \notin L -> ⊢e open x body ∶ es.
Proof.
  intros S l body es H; inversion H; subst.
  - exists (\{} : vars). intros; apply eff_ignore.
  - eauto.
Qed.

Local Lemma app_initialization : forall G D vs f a i,
  G ⸴ D ⸴ vs ⊢i trm_app (avar_f f) (avar_f a) ∶ i ->
  i = committed /\ binds f committed D /\ binds a committed D.
Proof.
  intros G D vs f a i H. inversion H; subst.
  match goal with Hc : _ ⸴ _ ⊢c trm_app _ _ |- _ => inversion Hc; subst end.
  repeat match goal with Hc : _ ⸴ _ ⊢c trm_var _ |- _ => inversion Hc; subst; clear Hc end.
  auto.
Qed.

Local Lemma committed_avars_init : forall G D avs,
  G ⸴ D ⊢c avs -> forall is' vs, all_comm_unspec is' ->
  length avs = length is' -> G ⸴ D ⸴ vs ⊢i avs :: is'.
Proof.
  intros G D avs H. induction H; intros is' vs Hi Hlen.
  - destruct is'; [constructor | discriminate].
  - inversion Hi; subst; [discriminate|].
    constructor; eauto. inversion H; subst.
    match goal with Hflag : _ = committed \/ _ = unspecified |- _ => destruct Hflag as [-> | ->] end.
    + eauto using committed_var_typing.
    + apply init_var_binds. eapply init_var_sub; eauto using init_sub_comm_unspec, init_var_commit.
Qed.

Local Lemma new_initialization : forall G D (E : eff_ctx) c avs Sigma Ts is' R ds body i,
  inert G -> heap_correspond G Sigma ->
  binds c (item_lit (lit_con Ts is' R ds body)) Sigma ->
  length avs = length is' ->
  G ⸴ D ⸴ dom E ⊢i trm_new (avar_f c) avs ∶ i ->
  binds c committed D /\
  ((i = free /\ G ⸴ D ⸴ dom E ⊢i avs :: is') \/
   (i = committed /\ G ⸴ D ⸴ \{} ⊢i avs :: is')).
Proof.
  intros G D E c avs Sigma Ts is' R ds body i Hi Hheap Hb Hlen Hinit.
  inversion Hinit; subst.
  - match goal with Hc : _ ⸴ _ ⊢c trm_new _ _ |- _ => inversion Hc; subst end.
    match goal with Hc : _ ⸴ _ ⊢c trm_var _ |- _ => inversion Hc; subst end.
    match goal with Ht : _ ⊢ trm_var _ ∶ typ_con _ _ _ |- _ =>
      destruct (canonical_constructor Hi Hheap Ht) as [ds' [body' [Hb' _]]]
    end.
    pose proof (binds_functional Hb Hb') as Eq. inversion Eq; subst.
    eauto using committed_avars_init.
  - match goal with Hc : _ ⸴ _ ⊢c trm_var _ |- _ => inversion Hc; subst end.
    match goal with Ht : _ ⊢ trm_var _ ∶ typ_con _ _ _ |- _ =>
      destruct (canonical_constructor Hi Hheap Ht) as [ds' [body' [Hb' _]]]
    end.
    pose proof (binds_functional Hb Hb') as Eq. inversion Eq; subst. eauto.
Qed.

Local Definition preserved (G : ctx) (c : config) (U : typ) :=
  exists G' D' E' es', ty_config (G & G') D' E' es' c U.

Local Ltac unpack_config Hc :=
  let G := fresh in let D := fresh in let Sh := fresh in let Fs := fresh in
  let t := fresh in let Out := fresh in
  inversion Hc as [G D Sh E Et Fs t T i Out e' e et
    Hi Hid Hheap Hfree Hstack Hty He Hinit Hcorr]; subst.

Local Lemma preserve_selection : forall G D E es Sigma fs x a R ds y U,
  ty_config G D E es (trm_sel (avar_f x) a ; fs ; Sigma) U ->
  binds x (item_obj R ds) Sigma -> labels_has ds (heap_def_trm a (Some y)) ->
  preserved G (trm_var (avar_f y) ; fs ; Sigma) U.
Proof.
  intros G D Eall es Sigma fs x a R ds y U Hc Hb Hsel. unpack_config Hc.
  destruct (invert_term_typing Hty) as [S [T0 [Hfield Hsub]]].
  destruct (canonical_field Hi Hheap Hfield)
    as [R0 [hds [V [o [Hb0 [Hds [Hrecord [Hhas [Hdec [_ HVT]]]]]]]]]].
  pose proof (binds_functional Hb Hb0) as Eq. inversion Eq; subst R0 hds.
  unfold labels_has in Hsel, Hhas. simpl in Hsel, Hhas.
  assert (o = Some y) by congruence. subst o.
  inversion Hdec; subst.
  destruct (select_committed Hinit) as [-> Hcomm].
  destruct (committed_heap_of_stack Hfree) as [_ [_ Hall]].
  specialize (Hall _ _ Hcomm Hb). inversion Hall; subst.
  destruct (committed_field_initialized ltac:(eassumption) Hsel) as [z [Ez Hz]].
  injection Ez as <-.
  assert (e' = nil) by (inversion He; reflexivity). subst e'.
  exists (empty : ctx), D, (E :: Et)%list, (e :: et)%list. rewrite concat_empty_r.
  change (ty_config G D (E :: Et) ((nil ++ e) :: et) (trm_var (avar_f y) ; fs ; Sigma) U).
  eapply ty_config_c; eauto using eff_ignore, committed_var_typing, ty_sub, subtyp_trans.
Qed.

Local Lemma preserve_application : forall G D E es Sigma fs f a S0 body U,
  ty_config G D E es (trm_app (avar_f f) (avar_f a) ; fs ; Sigma) U ->
  binds f (item_lit (lit_fun S0 body)) Sigma ->
  preserved G (open a body ; fs ; Sigma) U.
Proof.
  intros G D Eall es Sigma fs f a S0 body U Hc Hb. unpack_config Hc.
  destruct (invert_term_typing Hty) as [S [Tfun [Hf [Ha Hsub]]]].
  destruct (canonical_function Hi Hheap Hf) as [S1 [T1 [t1 [Hb0 [Hlit Hflow]]]]].
  pose proof (binds_functional Hb Hb0) as Eq. inversion Eq; subst S1 t1.
  destruct (function_flow_at Hflow Ha) as [Ha0 Hsub0].
  inversion Hlit; subst.
  assert (Ht : G ⊢ open a body ∶ open a T1).
  { eapply (@open_at_typing true); eauto. }
  destruct (app_initialization Hinit) as [-> [Hcf Hca]].
  destruct (committed_heap_of_stack Hfree) as [_ [_ Hall]].
  specialize (Hall _ _ Hcf Hb). inversion Hall; subst.
  match goal with H : _ ⸴ _ ⊢c lit_fun _ _ |- _ => inversion H; subst end.
  assert (Hbody : G ⸴ D ⊢c open a body).
  { eapply (@open_at_commit G G D D _ S0 a body); [eassumption | unfold extends; auto | exact Ha0 | intros z Hz; exact Hz | exact Hca]. }
  assert (e' = nil) by (inversion He; reflexivity). subst e'.
  exists (empty : ctx), D, (E :: Et)%list, (e :: et)%list. rewrite concat_empty_r.
  change (ty_config G D (E :: Et) ((nil ++ e) :: et) (open a body ; fs ; Sigma) U).
  eapply ty_config_c; eauto using eff_ignore, init_commit, ty_sub, subtyp_trans.
Qed.

Local Lemma preserve_assignment : forall G D E es Sigma Sigma' fs x a y U,
  ty_config G D E es (trm_asn (avar_f x) a (avar_f y) ; fs ; Sigma) U ->
  heap_update Sigma x a y Sigma' ->
  preserved G (trm_var (avar_f y) ; fs ; Sigma') U.
Proof.
  intros G D Eall es Sigma Sigma' fs x a y U Hc Hup. unpack_config Hc.
  destruct (invert_term_typing Hty) as [S [T0 [Hfield [Hy Hsub]]]].
  destruct (canonical_field Hi Hheap Hfield)
    as [R [ds [V [o [Hb [Hds [Hrecord [Hhas [Hdec [HSV HVT]]]]]]]]]].
  destruct Hup as [R0 [ds0 [ds' [S1 [S2 [-> [Hfresh [Hup ->]]]]]]]].
  destruct (@heap_update_bindings item S1 S2 x (item_obj R0 ds0) (item_obj R0 ds') Hfresh)
    as [Hb0 [Hb' [Hother Hdom]]].
  pose proof (binds_functional Hb Hb0) as Eq. inversion Eq; subst R0 ds0.
  assert (HyV : G ⊢ trm_var (avar_f y) ∶ V) by (eauto using ty_sub).
  assert (Hother' : forall z itm, z <> x ->
    binds z itm (S1 & x ~ item_obj R ds & S2) ->
    binds z itm (S1 & x ~ item_obj R ds' & S2)).
  { intros z itm Hne Hz. apply (proj1 (Hother z itm Hne)), Hz. }
  assert (Hh : heap_correspond G (S1 & x ~ item_obj R ds' & S2)).
  { eapply heap_correspond_update; try eassumption.
    eapply defs_update_typed; eassumption. }
  destruct (assign_initialization Hid Hinit) as [Hx [Hyp [Himp Hiy]]].
  inversion Hfree as [|? ? ? ? ? Hdis Hhead Htail]; subst.
  inversion Hcorr as [|? ? ? ? HcorrT HcorrH]; subst.
  assert (He' : e' = nil \/ e' = ((x,a) :: nil)%list) by (inversion He; auto).
  destruct (@assignment_head G D E Et _ _ x a y R ds ds' e' e Hdis Hhead Htail Hup Hds Hb Hb' Hdom Hother' Hx Hyp Himp HcorrH He')
    as [Enew [HE [Hfree' HcorrH']]].
  assert (Hstack' : ty_stack G D (Enew :: Et) fs T i (e :: et) U).
  { eapply stack_transport; [exact Hstack | unfold extends; auto | intros z Hb0'; exact Hb0' | intros; assumption |].
    constructor; [rewrite HE; apply subset_refl | apply doms_refl]. }
  exists (empty : ctx), D, (Enew :: Et)%list, (e :: et)%list. rewrite concat_empty_r.
  change (ty_config G D (Enew :: Et) ((nil ++ e) :: et)
    (trm_var (avar_f y) ; fs ; S1 & x ~ item_obj R ds' & S2) U).
  eapply ty_config_c; eauto using eff_ignore, ty_sub, subtyp_trans, eff_ctx_corr_cons.
  rewrite HE. exact Hiy.
Qed.

Local Lemma preserve_let_variable : forall G D E es Sigma fs x body U,
  ty_config G D E es (trm_var (avar_f x) ; (frame_let body :: fs)%list ; Sigma) U ->
  preserved G (open x body ; fs ; Sigma) U.
Proof.
  intros G D Eall es Sigma fs x body U Hc. unpack_config Hc.
  assert (e' = nil) by (inversion He; reflexivity). subst e'.
  inversion Hstack as [|L ? ? ? ? ? ? ? ? ? T0 e0 et0 eb ? Hs Htb Hib Heb| |]; subst.
  exists (empty : ctx), D, (E :: Et)%list, ((eb ++ e0) :: et)%list. rewrite concat_empty_r.
  eapply ty_config_c with (T:=T0); try eassumption.
  - eapply (@open_at_typing false); eauto.
  - eapply open_at_effect. eassumption.
  - eapply (@open_at_init true); try eassumption.
    + unfold extends. auto.
    + apply init_map_extends; [unfold extends; auto|apply subset_refl].
    + eapply var_initialization. eassumption.
Qed.

Local Lemma preserve_let_step : forall G D E es Sigma fs S t body U,
  ty_config G D E es (trm_let S t body ; fs ; Sigma) U ->
  preserved G (t ; (frame_let body :: fs)%list ; Sigma) U.
Proof.
  intros G D Eall es Sigma fs S t body U Hc. unpack_config Hc.
  destruct (invert_term_typing Hty) as [Lty [T0 [Ht [Hb Hsub]]]].
  destruct (cofinite_let_initialization Hinit) as [Li [j [Hti Hbi]]].
  destruct (cofinite_let_effect He) as [Le [e1 [e2 [-> [H1 H2]]]]].
  exists (empty : ctx), D, (E :: Et)%list, ((e1 ++ (e2 ++ e)) :: et)%list. rewrite concat_empty_r.
  eapply ty_config_c with (T:=S) (i:=j); try eassumption.
  - eapply ty_stack_let with (L:=Lty \u Li \u Le \u dom G); try eassumption.
    + intros z Hz. split_fresh. eapply ty_sub; eauto.
      apply (proj1 (proj2 (proj2 weaken_typing))) with (G:=G); auto.
    + intros z Hz. split_fresh. eauto.
    + intros z Hz. split_fresh. eauto.
  - rewrite List.app_assoc. exact Hcorr.
Qed.

Local Lemma preserve_return : forall G D E es Sigma fs x y U,
  ty_config G D E es (trm_var (avar_f y) ; (frame_ret x :: fs)%list ; Sigma) U ->
  preserved G (trm_var (avar_f x) ; fs ; Sigma) U.
Proof.
  intros G D Eall es Sigma fs x y U Hc. unpack_config Hc.
  assert (e' = nil) by (inversion He; reflexivity). subst e'.
  inversion Hstack as [| |? ? ? ? ? ? ? ? ? ? ? ? Hs Hx Hix |
      ? ? ? ? ? ? ? ? ? ? ? Hs Hx Hix]; subst.
  - exists (empty : ctx), D, (E :: Et)%list, (e :: et)%list. rewrite concat_empty_r.
    change (ty_config G D (E :: Et) ((nil ++ e) :: et) (trm_var (avar_f x) ; fs ; Sigma) U).
    eapply ty_config_c; eauto using eff_ignore.
  - inversion Hfree as [|? ? ? ? ? Hdis Hhead Htail]; subst.
    inversion Hcorr as [|? ? ? ? HcorrT HcorrH]; subst.
    pose proof (promote_stack Hhead HcorrH Hdis Htail) as Hfree'.
    destruct (init_var_free_inv (var_initialization Hix)) as [Hxin _].
    assert (Hs' : ty_stack G (promote D E) Et fs T0 committed et U).
    { eapply stack_transport; [exact Hs | intros ? ?; auto | apply promote_committed | |apply doms_refl].
      intros z j Hin Hb.
      assert (Hn : z # E) by (intro Hbad; exact (Hdis _ Hbad Hin)).
      exact (proj2 (promote_out D j Hn) Hb). }
    destruct Et as [|En Et]; [inversion Hs'|].
    destruct et as [|en et]; [inversion Hs'|].
    exists (empty : ctx), (promote D E), (En :: Et)%list, (en :: et)%list.
    rewrite concat_empty_r.
    change (ty_config G (promote D E) (En :: Et) ((nil ++ en) :: et)
      (trm_var (avar_f x) ; fs ; Sigma) U).
    eapply ty_config_c; eauto using eff_ignore, promote_inert, committed_var_typing, promote_in.
Qed.

Local Lemma preserve_literal :
  (forall G (l : lit) B, G ⊢ l ∶ B -> inert_typ B) ->
  forall G D E es Sigma fs x S l body U,
  ty_config G D E es (trm_lit S l body ; fs ; Sigma) U ->
  x # Sigma ->
  preserved G (open x body ; fs ; Sigma & x ~ item_lit l) U.
Proof.
  intros inert_lit G D Eall es Sigma fs x S l body U Hc Hfresh. unpack_config Hc.
  destruct (invert_term_typing Hty) as [Lty [T0 [Hl [Hbody Hsub]]]].
  destruct (cofinite_lit_initialization Hinit) as [Li [Hcl Hbi]].
  destruct (cofinite_lit_effect He) as [Le Heb].
  destruct Hheap as [HG Hheap]. destruct (committed_heap_of_stack Hfree) as [_ [HD _]].
  set (Gn := G & x ~ S).
  set (Dn := D & x ~ committed).
  assert (Hg : extends G Gn) by (unfold Gn; apply extends_push; congruence).
  assert (Hd : extends D Dn) by (unfold Dn; apply extends_push; congruence).
  assert (Hcd : commit_map id D Dn) by (intros z Hb; apply Hd, Hb).
  assert (Hcv : Gn ⊢ trm_var (avar_f x) ∶ S) by (apply ty_var, binds_push_eq).
  exists (x ~ S), Dn, (E :: Et)%list, ((e' ++ e) :: et)%list.
  change (ty_config Gn Dn (E :: Et) ((e' ++ e) :: et)
    (open x body ; fs ; Sigma & x ~ item_lit l) U).
  eapply ty_config_c with (T:=T) (i:=i); try eassumption.
  - apply inert_all; eauto. congruence.
  - apply inert_inits_push; auto.
  - apply heap_correspond_push; [exact (conj HG Hheap) | exact Hfresh |].
    simpl. eapply (proj1 (proj2 weaken_typing)); eassumption.
  - eapply free_stack_push; eauto. intros _. constructor.
    eapply commit_identity_lit; eauto.
  - eapply stack_transport; eauto using doms_refl.
  - eapply ty_sub with (T:=T0).
    + eapply (@open_at_typing false); eauto.
    + eapply (proj1 (proj2 (proj2 weaken_typing))); eauto.
  - eapply open_at_effect; eauto.
  - eapply (@open_at_init false); try eassumption.
    + eapply init_map_extends; eauto using subset_refl.
    + apply init_var_commit, binds_push_eq.
Qed.

(* Opening constructor parameters preserves the record shape. *)
Local Lemma open_typs_length : forall Ts n x,
  length_s (open_rec n x Ts) = length_s Ts.
Proof.
  induction Ts; intros n x; [reflexivity|].
  change (S (length_s (open_rec n x Ts)) = S (length_s Ts)).
  f_equal. apply IHTs.
Qed.

Local Lemma open_avar_commute : forall (a : avar) n m x y,
  n <> m -> open_rec n x (open_rec m y a) = open_rec m y (open_rec n x a).
Proof.
  intros [i|z] n m x y H; simpl; auto.
  repeat (progress (simpl; try case_if)); try reflexivity; try congruence.
Qed.

Local Lemma open_type_commute :
  (forall (T : typ) n m x y, n <> m ->
    open_rec n x (open_rec m y T) = open_rec m y (open_rec n x T)) /\
  (forall (Ts : typs) n m x y, n <> m ->
    open_rec n x (open_rec m y Ts) = open_rec m y (open_rec n x Ts)) /\
  (forall (D : dec) n m x y, n <> m ->
    open_rec n x (open_rec m y D) = open_rec m y (open_rec n x D)).
Proof.
  apply typ_mutind; intros; simpl;
    fold open_rec_typ open_rec_typs open_rec_dec;
    change open_rec_typ with (@open_rec typ TypOpenable) in *;
    change open_rec_typs with (@open_rec typs TypsOpenable) in *;
    change open_rec_dec with (@open_rec dec DecOpenable) in *;
    rewrite ?open_typs_length;
    f_equal; eauto using open_avar_commute;
    try solve [match goal with IH : forall _ _ _ _, _ -> _ |- _ => apply IH; lia end].
Qed.

Local Lemma open_self_after_args : forall ys n m x (T : typ),
  m < n -> open_rec m x (open_rec_vars n ys T) = open_rec_vars n ys (open_rec m x T).
Proof.
  induction ys as [|y ys IH]; intros n m x T H; simpl; auto.
  rewrite IH by lia. rewrite (proj1 open_type_commute T m n x y) by lia. reflexivity.
Qed.

Fixpoint close_type (n : nat) (x : var) (T : typ) : typ :=
  match T with
  | typ_top => typ_top
  | typ_bot => typ_bot
  | typ_rcd D => typ_rcd (close_decl n x D)
  | typ_and U V => typ_and (close_type n x U) (close_type n x V)
  | typ_sel a A => typ_sel (close_rec n x a) A
  | typ_bnd U => typ_bnd (close_type (S n) x U)
  | typ_all U V => typ_all (close_type n x U) (close_type (S n) x V)
  | typ_con Ts is' U =>
      typ_con (close_types n x Ts) is' (close_type (S (length_s Ts) + n) x U)
  end
with close_types (n : nat) (x : var) (Ts : typs) : typs :=
  match Ts with
  | typs_nil => typs_nil
  | typs_cons T Ts => typs_cons (close_type n x T) (close_types n x Ts)
  end
with close_decl (n : nat) (x : var) (D : dec) : dec :=
  match D with
  | dec_typ a U V => dec_typ a (close_type n x U) (close_type n x V)
  | dec_trm a U V => dec_trm a (close_type n x U) (close_type n x V)
  end.

Local Lemma close_open_avar_fresh : forall (a : avar) n x,
  x \notin fv a -> close_rec n x (open_rec n x a) = a.
Proof.
  intros [k|y] n x H; repeat (progress (simpl in *; try case_if)); try reflexivity; try congruence.
  exfalso. apply H. subst. apply in_singleton_self.
Qed.

Local Lemma close_open_type_fresh :
  (forall T n x, x \notin fv T -> close_type n x (open_rec n x T) = T) /\
  (forall Ts n x, x \notin fv Ts -> close_types n x (open_rec n x Ts) = Ts) /\
  (forall D n x, x \notin fv D -> close_decl n x (open_rec n x D) = D).
Proof.
  apply typ_mutind; intros; simpl in *;
    fold open_rec_typ open_rec_typs open_rec_dec;
    change open_rec_typ with (@open_rec typ TypOpenable) in *;
    change open_rec_typs with (@open_rec typs TypsOpenable) in *;
    change open_rec_dec with (@open_rec dec DecOpenable) in *;
    rewrite ?open_typs_length; split_fresh;
    f_equal; eauto using close_open_avar_fresh.
Qed.

Local Lemma close_preserves_record : forall R ls,
  record_typ R ls -> forall n x, record_typ (close_type n x R) ls.
Proof.
  intros R ls H. induction H; intros n x; subst l.
  - destruct H; apply rt_one; first [apply rd_typ | apply rd_trm | reflexivity].
  - destruct H0; apply rt_cons; solve [eassumption | eauto | apply rd_typ | apply rd_trm | reflexivity].
Qed.

Local Lemma fv_type_open_other :
  (forall (T : typ) n x y, y <> x -> y \in fv (open_rec n x T) -> y \in fv T) /\
  (forall (Ts : typs) n x y, y <> x -> y \in fv (open_rec n x Ts) -> y \in fv Ts) /\
  (forall (D : dec) n x y, y <> x -> y \in fv (open_rec n x D) -> y \in fv D).
Proof.
  apply typ_mutind; intros; simpl in *;
    fold open_rec_typ open_rec_typs open_rec_dec in *;
    change open_rec_typ with (@open_rec typ TypOpenable) in *;
    change open_rec_typs with (@open_rec typs TypsOpenable) in *;
    change open_rec_dec with (@open_rec dec DecOpenable) in *;
    repeat rewrite in_union in *; try solve [intuition eauto].
  destruct a; simpl in *; auto. case_if in H0.
  all: simpl in H0; first [exact H0 | rewrite in_singleton in H0; congruence].
Qed.

Local Lemma record_fresh_open_many : forall xs L R n ls,
  fresh L (length xs) xs -> fv R \c L ->
  record_typ (open_rec_vars n xs R) ls -> record_typ R ls.
Proof.
  induction xs as [|x xs IH]; intros L R n ls Hfresh HF H; simpl in *; auto.
  destruct Hfresh as [Hx Hxs].
  assert (HR : record_typ (open_rec n x R) ls).
  { eapply IH; [exact Hxs | | exact H].
    intros y Hy. rewrite in_union. destruct (classic (y=x)) as [->|Hne].
    - right. apply in_singleton_self.
    - left. apply HF. eapply (proj1 fv_type_open_other); eassumption. }
  pose proof (close_preserves_record HR n x) as HC.
  rewrite (proj1 close_open_type_fresh) in HC by (intro Hbad; apply Hx, HF, Hbad).
  exact HC.
Qed.

Local Lemma record_open_many : forall xs R n ls,
  record_typ R ls -> record_typ (open_rec_vars n xs R) ls.
Proof. induction xs; intros; simpl; auto using open_record. Qed.

Local Lemma typed_def_record_label : forall G (d : def) D,
  G ⊢ d ∶d D -> record_dec D /\ label_of D = label_of d.
Proof. intros G d D H. inversion H; subst; split; [constructor | reflexivity | constructor | reflexivity]. Qed.

Local Lemma type_defs_record_labels : forall G (ds : defs) R,
  G ⊢ ds ∶ R ->
  exists ls, record_typ R ls /\ (forall l, l \in ls -> ~ labels_hasnt ds l).
Proof.
  intros G ds R H. induction H.
  - destruct (typed_def_record_label H) as [Hr Hl].
    exists (\{label_of d}). split; [apply rt_one; [exact Hr|symmetry; exact Hl]|].
    intros l Hin Hnone. rewrite in_singleton in Hin. subst l.
    unfold labels_hasnt in Hnone. simpl in Hnone. case_if in Hnone; congruence.
  - destruct IHty_defs as [ls [Hr Hlabels]].
    destruct (typed_def_record_label H0) as [HD Hl].
    exists (ls \u \{label_of d}). split.
    + apply rt_cons; [exact Hr | exact HD | symmetry; exact Hl |].
      intros Hin. exact (Hlabels _ Hin H1).
    + intros l Hin Hnone. rewrite in_union, in_singleton in Hin.
      unfold labels_hasnt in Hnone. simpl in Hnone. case_if in Hnone; try discriminate.
      destruct Hin as [Hin | E]; try congruence.
      exact (Hlabels _ Hin Hnone).
Qed.

Local Lemma type_defs_record : forall G (ds : defs) R, G ⊢ ds ∶ R -> record_type R.
Proof.
  intros G ds R H. destruct (type_defs_record_labels H) as [ls [Hr _]].
  exists ls. exact Hr.
Qed.

Local Lemma lit_inert_type : forall G (l : lit) B, G ⊢ l ∶ B -> inert_typ B.
Proof.
  intros G l B H. inversion H; subst.
  - constructor.
  - apply inert_typ_con.
    destruct (var_freshes (L \u fv T) (S (length_s Ts))) as [zs Hz].
    destruct zs as [|z zs]; [contradiction|].
    pose proof (fresh_length Hz) as Hlen. rewrite tlc_length in Hlen. simpl in Hlen.
    assert (Hsz : length zs = length_s Ts) by lia.
    rewrite <- Hsz in Hz.
    destruct (fresh_union_r Hz) as [HL HF].
    match goal with Hd : forall _ _, _ -> _ -> _ ⊢ _ ∶ _ |- _ =>
      destruct (type_defs_record (Hd z zs Hsz HL)) as [ls Hr]
    end.
    exists ls. eapply record_fresh_open_many with (xs:=(z :: zs)%list) (n:=0) (L:=fv T);
      eauto using subset_refl.
Qed.

Local Lemma defs_to_heap_label : forall d, label_of (heap_def_of_def d) = label_of d.
Proof. intros []; reflexivity. Qed.

Local Lemma defs_to_heap_typed : forall G (ds : defs) R,
  G ⊢ ds ∶ R -> forall G', G' ⊢ heap_defs_of_defs ds ∶ R.
Proof.
  intros G ds R H. induction H; intros; unfold heap_defs_of_defs in *; simpl.
  - apply ty_defs_one. inversion H; subst;
      first [apply ty_heap_def_typ | apply ty_heap_def_trm_none].
  - apply ty_defs_cons; auto.
    + inversion H0; subst; first [apply ty_heap_def_typ | apply ty_heap_def_trm_none].
    + unfold labels_hasnt in *.
      rewrite defs_to_heap_label,
       (@map_get_label def heap_def DefLabelOf HeapDefLabelOf heap_def_of_def defs_to_heap_label),
       H1. reflexivity.
Qed.

Local Lemma defs_to_heap_open : forall zs n (ds : defs),
  heap_defs_of_defs (open_rec_vars n zs ds) =
  open_rec_vars n zs (heap_defs_of_defs ds).
Proof.
  induction zs as [|z zs IH]; intros n ds; simpl; auto.
  rewrite IH. f_equal. unfold heap_defs_of_defs.
  change (List.map heap_def_of_def (List.map (open_rec n z) ds) =
          List.map (open_rec n z) (List.map heap_def_of_def ds)).
  rewrite !List.map_map. apply List.map_ext. intros []; reflexivity.
Qed.

Local Lemma fresh_defs_points : forall zs n ds,
  heap_defs_points_to (open_rec_vars n zs (heap_defs_of_defs ds)) = \{}.
Proof.
  intros. rewrite <- defs_to_heap_open. generalize (open_rec_vars n zs ds) as ds'.
  intros ds'. induction ds' as [|[] ds' IH]; simpl; auto.
Qed.

Local Lemma open_def_eff : forall ds zs n x,
  def_eff x (open_rec_vars n zs ds) = def_eff x ds.
Proof.
  intros ds zs; revert ds. induction zs as [|a zs IH]; intros ds n x; simpl; auto.
  rewrite IH. change (def_eff x (List.map (open_rec n a) ds) = def_eff x ds).
  induction ds as [|[] ds IHds]; cbn [List.map def_eff open_rec DefOpenable open_rec_def]; rewrite ?IHds; reflexivity.
Qed.

Local Lemma fresh_defs_effects : forall zs n ds x,
  heap_defs_effs x (open_rec_vars n zs (heap_defs_of_defs ds)) = def_eff x ds.
Proof.
  intros. rewrite <- defs_to_heap_open, <- (open_def_eff ds zs n x).
  generalize (open_rec_vars n zs ds) as ds'. intros ds'.
  induction ds' as [|[] ds' IH]; try unfold heap_defs_of_defs in IH;
    cbn [heap_defs_of_defs List.map heap_def_of_def heap_defs_effs def_eff]; rewrite ?IH; reflexivity.
Qed.

Fixpoint actual_names (formals actuals : list var) (z : var) :=
  match formals, actuals with
  | (x :: xs)%list, (y :: ys)%list => If z = x then y else actual_names xs ys z
  | _, _ => z
  end.

Local Lemma actual_names_out : forall xs ys z,
  ~ List.In z xs -> actual_names xs ys z = z.
Proof.
  induction xs as [|x xs IH]; destruct ys as [|y ys]; simpl; intros; auto.
  case_if.
  - exfalso. apply H. left. congruence.
  - apply IH. intuition.
Qed.

Local Lemma actual_names_range : forall xs ys z,
  actual_names xs ys z = z \/ List.In (actual_names xs ys z) ys.
Proof.
  induction xs as [|x xs IH]; destruct ys as [|y ys]; simpl; intros; auto.
  case_if; auto. destruct (IH ys z); auto.
Qed.

Local Lemma actual_names_isolated : forall xs ys,
  isolated (actual_names xs ys) (from_list xs \u from_list ys).
Proof.
  unfold isolated. intros xs ys z Hz. split_fresh.
  assert (Hnx : ~ List.In z xs) by (intro Hin; apply H; apply from_list_iff; exact Hin).
  assert (Hny : ~ List.In z ys) by (intro Hin; apply H0; apply from_list_iff; exact Hin).
  split; auto using actual_names_out.
  intros w E. destruct (actual_names_range xs ys w); congruence.
Qed.

Local Lemma actual_names_map : forall xs ys,
  List.NoDup xs -> length xs = length ys -> List.map (actual_names xs ys) xs = ys.
Proof.
  induction xs as [|x xs IH]; destruct ys as [|y ys]; simpl; intros Hnd Hlen; try discriminate; auto.
  inversion Hnd as [|? ? Hnx Htail]; subst. case_if.
  f_equal. transitivity (List.map (actual_names xs ys) xs).
  - apply List.map_ext_in. intros z Hz. simpl. case_if; congruence.
  - apply IH; congruence.
Qed.

Local Lemma fresh_nodup : forall L xs,
  fresh L (length xs) xs -> List.NoDup xs.
Proof.
  intros L xs. revert L. induction xs as [|x xs IH]; simpl; intros; constructor.
  - destruct H as [_ H]. apply fresh_union_r2 in H. apply fresh_single_notin in H.
    intro Hin. apply H, from_list_iff, Hin.
  - apply IH with (L:=L \u \{x}). tauto.
Qed.

Local Lemma forall2_append : forall A B (P : A -> B -> Prop) xs ys xs' ys',
  List.Forall2 P xs ys -> List.Forall2 P xs' ys' ->
  List.Forall2 P (xs ++ xs')%list (ys ++ ys')%list.
Proof. intros A B P xs ys xs' ys' H. induction H; simpl; intros H'; [exact H' | constructor; auto]. Qed.

Local Lemma forall2_reverse : forall A B (P : A -> B -> Prop) xs ys,
  List.Forall2 P xs ys -> List.Forall2 P (List.rev xs) (List.rev ys).
Proof.
  intros A B P xs ys H. induction H; simpl; [constructor|].
  apply forall2_append; auto.
Qed.

Local Lemma forall2_map_left : forall A B C (f : A -> B) (P : B -> C -> Prop) xs ys,
  List.Forall2 P (List.map f xs) ys -> List.Forall2 (fun x y => P (f x) y) xs ys.
Proof.
  intros A B C f P xs. induction xs; intros ys H; inversion H; subst; constructor; auto.
Qed.

Local Lemma forall2_map_right : forall A B C (f : A -> B) (P : C -> B -> Prop) xs ys,
  List.Forall2 P xs (List.map f ys) -> List.Forall2 (fun x y => P x (f y)) xs ys.
Proof.
  intros A B C f P xs ys. revert xs. induction ys; intros xs H; inversion H; subst; constructor; auto.
Qed.

Local Lemma forall2_impl : forall A B (P Q : A -> B -> Prop) xs ys,
  List.Forall2 P xs ys -> (forall x y, P x y -> Q x y) -> List.Forall2 Q xs ys.
Proof. intros A B P Q xs ys H Himp. induction H; constructor; auto. Qed.

Local Lemma bind_singles_property : forall A (P : var -> A -> Prop) xs vs,
  List.Forall2 P xs vs -> forall x v, binds x v (xs ~* vs) -> P x v.
Proof.
  intros A P xs vs H. induction H as [|p u xs vs Hpu Htail IH]; intros x v Hb.
  - rewrite singles_nil in Hb. false (binds_empty_inv Hb).
  - rewrite singles_cons in Hb. apply binds_push_inv in Hb.
    destruct Hb as [[-> ->]|[_ Hb]]; auto.
Qed.

Local Lemma bind_mapped_property : forall A (P : var -> A -> Prop) r zs ys vs x v,
  List.map r zs = ys ->
  List.Forall2 P ys vs -> binds x v (zs ~** vs) ->
  P (r x) v.
Proof.
  intros A P r zs ys vs x v Hm H Hb.
  eapply (@bind_singles_property A (fun z w => P (r z) w) _ _); [|exact Hb].
  apply forall2_reverse, forall2_map_left. rewrite Hm. exact H.
Qed.

Local Lemma argument_types : forall G avs Ts ys,
  G ⊢ avs :: Ts -> vars_of_avars ys avs ->
  List.Forall2 (fun x T => G ⊢ trm_var (avar_f x) ∶ T) ys (to_list Ts).
Proof.
  intros G avs Ts ys H. revert ys. induction H; intros ys Hva; inversion Hva; subst;
    simpl; constructor; auto.
Qed.

Local Lemma argument_inits : forall G D vs avs is' ys,
  G ⸴ D ⸴ vs ⊢i avs :: is' -> vars_of_avars ys avs ->
  List.Forall2 (fun x i => init_var D vs x i) ys is'.
Proof.
  intros G D vs avs is' ys H. revert ys. induction H; intros ys Hva; inversion Hva; subst;
    constructor; eauto using var_initialization.
Qed.

Local Lemma vars_of_avars_length : forall xs avs, vars_of_avars xs avs -> length xs = length avs.
Proof. intros xs avs H. induction H; simpl; congruence. Qed.

(* Instantiate the constructor premises using the actual arguments and its allocated self variable. *)
Local Lemma constructor_body_at : forall G D vs vs' ts is' R ds body avs x ys,
  G ⊢ lit_con ts is' R ds body ∶ typ_con ts is' R ->
  G ⸴ D ⊢c lit_con ts is' R ds body ->
  G ⊢ avs :: ts -> G ⸴ D ⸴ vs ⊢i avs :: is' -> vars_of_avars ys avs ->
  x # G -> x # D -> vs \c vs' -> x \in vs' ->
  exists B i e,
    let G' := G & x ~ typ_bnd (open_rec_vars 1 ys R) in
    let D' := D & x ~ free in
    let hds := open_vars (x :: ys) (heap_defs_of_defs ds) in
    G' ⊢ hds ∶ open x (open_rec_vars 1 ys R) /\
    G' ⊢ open_vars (x :: ys) body ∶ B /\
    G' ⸴ D' ⸴ vs' ⊢i open_vars (x :: ys) body ∶ i /\
    ⊢e open_vars (x :: ys) body ∶ e /\
    from_list (def_eff x ds) = from_list e.
Proof.
  intros G D vs vs' ts is' R ds body avs x ys Hty Hcomm Hargs Hinits Hvars HxG HxD Hsub Hvisible.
  inversion Hty as [|Lt ? ? ? ? ? ? B Hdefs Hbody]; subst.
  inversion Hcomm as [|Li ? ? ? ? ? i ? ? Hli Heff Hinit]; subst.
  set (L := Lt \u Li \u dom G \u dom D \u fv_env G \u fv ts \u fv R \u fv ds \u fv body \u fv B).
  destruct (var_freshes L (S (length ys))) as [zs Hzs].
  destruct zs as [|z zs]; [contradiction|].
  pose proof (fresh_length Hzs) as Hlen. rewrite tlc_length in Hlen. simpl in Hlen.
  assert (Hlen' : length zs = length ys) by lia.
  assert (HlenTs : length zs = length_s ts) by (rewrite Hlen'; eauto using typed_args_length).
  rewrite <- Hlen' in Hzs.
  set (r := actual_names (z :: zs) (x :: ys)).
  assert (Hr : isolated r (from_list (z :: zs) \u from_list (x :: ys))) by apply actual_names_isolated.
  assert (Hactual : List.map r (z :: zs) = (x :: ys)%list).
  { apply actual_names_map; [apply fresh_nodup with (L:=L); exact Hzs | simpl; lia]. }
  inversion Hactual as [[Hrx Hrzs]].
  assert (Havoid : all_notin (from_list (z :: zs)) L) by (eapply fresh_avoids; exact Hzs).
  assert (Hfix : fixes r L).
  { intros v Hv. unfold r. apply actual_names_out. intro Hin.
    exact (Havoid _ (proj2 (from_list_iff _ _) Hin) Hv). }
  assert (HLt : fresh Lt (S (length zs)) (z :: zs)).
  { apply fresh_union_r1 in Hzs. exact Hzs. }
  assert (HLi : fresh Li (S (length zs)) (z :: zs)).
  { apply fresh_union_r2 in Hzs. apply fresh_union_r1 in Hzs. exact Hzs. }
  assert (HfixR : rename_typ r R = R).
  { apply (proj1 (rename_types_fixed _)). unfold L in Hfix. split_fixes; assumption. }
  assert (HfixB : rename_typ r B = B).
  { apply (proj1 (rename_types_fixed _)). unfold L in Hfix. split_fixes; assumption. }
  assert (HfixTs : rename_typs r ts = ts).
  { apply (proj1 (proj2 (rename_types_fixed _))). unfold L in Hfix. split_fixes; assumption. }
  assert (HfixDefs : List.map (rename_def r) ds = ds).
  { eapply (@rename_list_fixed def DefFreeVar); [apply rename_def_fixed|].
    unfold L in Hfix. split_fixes; assumption. }
  assert (HfixBody : rename_trm r body = body).
  { apply (proj1 (rename_terms_fixed _)). unfold L in Hfix. split_fixes; assumption. }
  assert (Hfo : fixes r (fv_env G)) by (unfold L in Hfix; split_fixes; assumption).
  assert (Hfg : fixes r (dom G)) by (unfold L in Hfix; split_fixes; assumption).
  assert (Hfd : fixes r (dom D)) by (unfold L in Hfix; split_fixes; assumption).
  set (Gn := G & x ~ typ_bnd (open_rec_vars 1 ys R)).
  set (Dn := D & x ~ free).
  assert (Hg : extends G Gn) by (apply extends_push; exact HxG).
  assert (Hd : extends D Dn) by (apply extends_push; exact HxD).
  assert (HRself : rename_typ r (open_vars (z :: zs) R) = open x (open_rec_vars 1 ys R)).
  { rewrite (@rename_open_many typ TypOpenable (rename_typ r) r (proj1 (rename_types_open r))),
      Hactual, HfixR. apply eq_sym, open_self_after_args. lia. }
  assert (Hm : typing_map r (G & zs ~** to_list ts & z ~ open_vars (z :: zs) R) Gn).
  { intros v V Hv. apply binds_push_inv in Hv. destruct Hv as [[-> ->]|[_ Hv]].
    - rewrite Hrx, HRself. apply ty_rec_elim, ty_var, binds_push_eq.
    - apply binds_concat_inv in Hv. destruct Hv as [Hv|[_ Hv]].
      + eapply (@bind_mapped_property typ (fun y V => Gn ⊢ trm_var (avar_f y) ∶ rename_typ r V)
          r zs ys (to_list ts) v V); [exact Hrzs | | exact Hv].
        apply (@forall2_map_right typ typ var (rename_typ r) (fun y V => Gn ⊢ trm_var (avar_f y) ∶ V)).
        rewrite <- rename_typs_list, HfixTs.
        eapply forall2_impl; [exact (argument_types Hargs Hvars)|].
        intros w A Hwa. exact (proj1 weaken_typing _ _ _ Hwa _ Hg).
      + rewrite (Hfg _ (get_some_inv Hv)), (proj1 (rename_types_fixed r) V).
        * apply ty_var, Hg, Hv.
        * intros w Hw. apply Hfo. destruct (classic (w \in fv_env G)) as [Hin|Hout]; auto.
          exfalso. exact (@fv_in_values_binds typ w fv v V G Hv Hout Hw). }
  assert (Hmd : init_map r (D & zs ~** is' & z ~ free) (from_list zs \u \{z}) Dn vs').
  { intros v j Hv Hacc. apply binds_push_inv in Hv. destruct Hv as [[-> ->]|[Hne Hv]].
    - rewrite Hrx. apply init_var_free; [exact Hvisible | unfold Dn; apply binds_push_eq].
    - apply binds_concat_inv in Hv. destruct Hv as [Hv|[Hzs0 Hv]].
      + apply init_var_extend with (D:=D) (vs:=vs); auto.
        exact (@bind_mapped_property init_typ (fun y i => init_var D vs y i)
          r zs ys is' v j Hrzs (argument_inits Hinits Hvars) Hv).
      + assert (Hj : j = committed).
        { destruct Hacc as [Hj|Hin]; auto. exfalso.
          rewrite in_union, in_singleton in Hin. destruct Hin as [Hin|Hin]; try contradiction.
          apply Hzs0. rewrite dom_bindings; [exact Hin|congruence]. }
        subst j. rewrite (Hfd _ (get_some_inv Hv)). apply init_var_commit, Hd, Hv. }
  pose proof (@rename_defs_typed _ _ _ r Gn (Hdefs z zs HlenTs HLt)) as Hds.
  rewrite (@rename_open_many defs _ (List.map (rename_def r)) r
    (@rename_list_open def DefOpenable (rename_def r) r (rename_def_open r))),
    Hactual, HfixDefs, HRself in Hds.
  pose proof (proj1 (rename_typing Hr) _ _ _ (Hbody z zs HlenTs HLt) _ Hm) as Hbt.
  rewrite (@rename_open_many trm TrmOpenable (rename_trm r) r (proj1 (rename_terms_open r))),
    (@rename_open_many typ TypOpenable (rename_typ r) r (proj1 (rename_types_open r))),
    Hactual, HfixBody, HfixB in Hbt.
  pose proof (proj1 (proj2 (proj2 (proj2 (rename_initialization Hr))))
    _ _ _ _ _ (Hinit z zs HlenTs HLi) _ _ _ Hm Hmd) as Hbi.
  rewrite (@rename_open_many trm TrmOpenable (rename_trm r) r (proj1 (rename_terms_open r))),
    Hactual, HfixBody in Hbi.
  pose proof (rename_has_effs Hr (Heff z zs HlenTs HLi)) as Hbe.
  rewrite (@rename_open_many trm TrmOpenable (rename_trm r) r (proj1 (rename_terms_open r))),
    Hactual, HfixBody, rename_def_effects, Hrx, HfixDefs in Hbe.
  destruct Hbe as [e [He Hset]].
  exists (open_vars (x :: ys) B), i, e. cbv zeta.
  repeat split; try assumption.
  pose proof (@defs_to_heap_typed Gn (open_vars (x :: ys) ds) _ Hds Gn) as Hheap.
  rewrite defs_to_heap_open in Hheap.
  rewrite ?Hrx, ?Hrzs. exact Hheap.
  all: rewrite ?Hrx, ?Hrzs; assumption.
Qed.

Local Lemma from_empty_heap : forall Sigma D, free_sub_heap (empty : eff_ctx) Sigma D.
Proof. intros Sigma D x es H; false (binds_empty_inv H). Qed.

Local Lemma def_effect_owner : forall ds x y a,
  (y,a) \in from_list (def_eff x ds) -> y = x.
Proof.
  induction ds as [|[] ds IH]; simpl; intros x y a H;
    try solve [rewrite from_list_nil in H; false (in_empty_inv H) | eauto].
  rewrite from_list_cons, in_union, in_singleton in H.
  destruct H as [H|H]; [congruence|eauto].
Qed.

Local Lemma allocated_head : forall G D E Et Sigma ds R x ys,
  free_sub_heap E Sigma D -> free_sub_heaps G D Sigma Et ->
  all_notin (dom E) (list_dom_union Et) ->
  x \notin list_dom_union Et -> x # E ->
  binds x free D ->
  binds x (item_obj R (open_vars (x :: ys) (heap_defs_of_defs ds))) Sigma ->
  free_sub_heaps G D Sigma ((E & x ~ def_eff x ds) :: Et).
Proof.
  intros G D E Et Sigma ds R x ys Hhead Htail Hdis HxEt HxE Hx Hit.
  constructor; auto.
  - intros z Hz. rewrite dom_push, in_union, in_singleton in Hz.
    destruct Hz as [->|Hz]; auto.
  - intros z es Hb. apply binds_push_inv in Hb. destruct Hb as [[-> ->]|[Hnz Hb]].
    + split; [eauto using def_effect_owner|].
      eexists; split; [exact Hit|]. constructor. repeat split; auto.
      * rewrite fresh_defs_effects. apply binds_push_eq.
      * intros w Hw. rewrite fresh_defs_points in Hw. false (in_empty_inv Hw).
    + destruct (Hhead _ _ Hb) as [Howner [itm [His Hf]]].
      split; auto. exists itm. split; auto.
      eapply free_item_extend; eauto. apply extends_push; exact HxE.
Qed.

Local Lemma allocated_corr : forall E ds x e old,
  eff_ctx_corr_one E old ->
  from_list (def_eff x ds) = from_list e ->
  eff_ctx_corr_one (E & x ~ def_eff x ds) (e ++ old)%list.
Proof.
  intros E ds x e old Hcorr Hset z es Hb p Hp.
  rewrite from_list_append, in_union.
  apply binds_push_inv in Hb. destruct Hb as [[-> ->]|[_ Hb]].
  - left. rewrite <- Hset. exact Hp.
  - right. eapply Hcorr; eassumption.
Qed.

Local Lemma preserve_new : forall G D E es Sigma fs x c avs ys ts is' R ds body U,
  ty_config G D E es (trm_new (avar_f c) avs ; fs ; Sigma) U ->
  x # Sigma -> binds c (item_lit (lit_con ts is' R ds body)) Sigma ->
  length ys = length_s ts -> vars_of_avars ys avs ->
  preserved G
    (open_vars (x :: ys) body ; (frame_ret x :: fs)%list ;
      Sigma & x ~ item_obj (open_rec_vars 1 ys R) (open_vars (x :: ys) (heap_defs_of_defs ds))) U.
Proof.
  intros G D Eall es Sigma fs x c avs ys ts is' R ds body U Hc Hfresh Hcbind Hlen Hvars.
  unpack_config Hc.
  destruct (invert_term_typing Hty) as [zs [ts' [is'' [R' [Hcon [Hargs [Hzs Hsub]]]]]]].
  destruct (canonical_constructor Hi Hheap Hcon) as [ds' [body' [Hcbind' Hlit]]].
  pose proof (binds_functional Hcbind Hcbind') as Eq. inversion Eq; subst ts' is'' R' ds' body'.
  assert (zs = ys).
  { clear -Hzs Hvars. revert ys Hvars. induction Hzs; intros ys Hys; inversion Hys; subst; auto.
    f_equal; eauto. }
  subst zs.
  assert (e' = nil) by (inversion He; reflexivity). subst e'.
  destruct Hheap as [HG HS].
  destruct (committed_heap_of_stack Hfree) as [_ [HD Hall]].
  assert (Hcl : G ⸴ D ⊢c lit_con ts is' R ds body).
  { specialize (Hall c _ (ltac:(inversion Hinit; subst;
        repeat match goal with H : _ ⸴ _ ⊢c trm_new _ _ |- _ => inversion H; subst; clear H end;
        match goal with H : _ ⸴ _ ⊢c trm_var _ |- _ => inversion H; subst; assumption end)) Hcbind).
    inversion Hall; subst; assumption. }
  assert (HlenI : length avs = length is').
  { inversion Hcl; subst. rewrite <- (vars_of_avars_length Hvars). congruence. }
  destruct (new_initialization Hi (conj HG HS) Hcbind HlenI Hinit) as [_ Hflags].
  set (Bself := typ_bnd (open_rec_vars 1 ys R)).
  set (hds := open_vars (x :: ys) (heap_defs_of_defs ds)).
  set (Gn := G & x ~ Bself).
  set (Dn := D & x ~ free).
  set (Sn := Sigma & x ~ item_obj (open_rec_vars 1 ys R) hds).
  assert (HxG : x # G) by congruence.
  assert (HxD : x # D) by congruence.
  assert (Hg : extends G Gn) by (apply extends_push; exact HxG).
  assert (Hd : extends D Dn) by (apply extends_push; exact HxD).
  assert (Hcd : commit_map id D Dn) by (intros z Hb; apply Hd; exact Hb).
  assert (Hn : x \notin list_dom_union (E :: Et)) by (intro Hbad; apply Hfresh, (free_dom_in_heap Hfree Hbad)).
  assert (HxE : x # E) by (intro Hbad; apply Hn; simpl; rewrite in_union; auto).
  assert (HxEt : x \notin list_dom_union Et) by (intro Hbad; apply Hn; simpl; rewrite in_union; auto).
  assert (HiGn : inert Gn).
  { apply inert_all; auto. unfold Bself.
    pose proof (lit_inert_type Hlit) as HlitInert.
    inversion HlitInert as [|? ? ? [ls Hrec]|]; subst.
    apply inert_typ_bnd. exists ls. apply record_open_many, Hrec. }
  assert (HiDn : inert_inits Dn) by (apply inert_inits_push; auto).
  assert (Hys : Gn ⊢ trm_var (avar_f x) ∶ T).
  { eapply ty_sub; [apply ty_var, binds_push_eq |].
    eapply (proj1 (proj2 (proj2 weaken_typing))); eassumption. }
  assert (Hfrees : free_sub_heaps Gn Dn Sn (E :: Et)).
  { eapply free_stack_push; eauto. discriminate. }
  assert (Hxs : binds x (item_obj (open_rec_vars 1 ys R) hds) Sn) by apply binds_push_eq.
  assert (Hxd : binds x free Dn) by apply binds_push_eq.
  inversion Hfrees as [|? ? ? ? ? Hdis Hhead Htail]; subst.
  inversion Hcorr as [|? ? ? ? HcorrT HcorrH]; subst.
  destruct Hflags as [[-> Hinitargs] | [-> Hinitargs]].
  - set (Enew := E & x ~ def_eff x ds).
    assert (Hdom : dom E \c dom Enew) by (unfold Enew; rewrite dom_push; intros z Hz; rewrite in_union; auto).
    assert (HxEn : x \in dom Enew) by (unfold Enew; rewrite dom_push, in_union; left; apply in_singleton_self).
    destruct (constructor_body_at Hlit Hcl Hargs Hinitargs Hvars HxG HxD Hdom HxEn)
      as [Bt [j [eb [Hds [Hbt [Hbi [Hbe Hset]]]]]]].
    assert (Hheap' : heap_correspond Gn Sn).
    { apply heap_correspond_push; [exact (conj HG HS) | exact Hfresh |].
      split; [reflexivity | exact Hds]. }
    assert (Hstack' : ty_stack Gn Dn (Enew :: Et) fs T free (e :: et) U).
    { eapply stack_transport; [exact Hstack | exact Hg | exact Hcd | |].
      - intros z k _ Hk. exact (Hd _ _ Hk).
      - constructor; [exact Hdom | apply doms_refl]. }
    exists (x ~ Bself), Dn, (Enew :: Et)%list, ((eb ++ e) :: et)%list.
    change (ty_config Gn Dn (Enew :: Et) ((eb ++ e) :: et)
      (open_vars (x :: ys) body ; (frame_ret x :: fs)%list ; Sn) U).
    eapply ty_config_c with (T:=Bt) (i:=j); try eassumption.
    + unfold Enew. eapply allocated_head; eassumption.
    + eapply ty_stack_ret_free; eauto using free_var_typing.
    + apply eff_ctx_corr_cons; auto. unfold Enew. eapply allocated_corr; eassumption.
  - set (Enew := (empty : eff_ctx) & x ~ def_eff x ds).
    assert (Hdom : \{} \c dom Enew) by (intros z Hz; exfalso; exact (in_empty_inv Hz)).
    assert (HxEn : x \in dom Enew) by (unfold Enew; rewrite dom_push, in_union; left; apply in_singleton_self).
    destruct (constructor_body_at Hlit Hcl Hargs Hinitargs Hvars HxG HxD Hdom HxEn)
      as [Bt [j [eb [Hds [Hbt [Hbi [Hbe Hset]]]]]]].
    assert (Hheap' : heap_correspond Gn Sn).
    { apply heap_correspond_push; [exact (conj HG HS) | exact Hfresh |].
      split; [reflexivity | exact Hds]. }
    assert (Hstack' : ty_stack Gn Dn (E :: Et) fs T committed (e :: et) U).
    { eapply stack_transport; eauto using doms_refl. }
    exists (x ~ Bself), Dn, (Enew :: E :: Et)%list, ((eb ++ nil) :: e :: et)%list.
    change (ty_config Gn Dn (Enew :: E :: Et) ((eb ++ nil) :: e :: et)
      (open_vars (x :: ys) body ; (frame_ret x :: fs)%list ; Sn) U).
    eapply ty_config_c with (T:=Bt) (i:=j); try eassumption.
    + unfold Enew. eapply allocated_head; eauto using from_empty_heap.
      intros z Hz. rewrite dom_empty in Hz. false (in_empty_inv Hz).
    + eapply ty_stack_ret_committed; eauto using free_var_typing.
    + apply eff_ctx_corr_cons; auto. unfold Enew. apply allocated_corr; auto.
      intros z es Hz. false (binds_empty_inv Hz).
Qed.

Theorem preservation : forall Gamma Delta ℰs effss c c' U,
    ty_config Gamma Delta ℰs effss c U ->
    c ↦ c' ->
    exists Gamma' Delta' ℰs' effss', ty_config (Gamma & Gamma') Delta' ℰs' effss' c' U.
Proof.
  intros G D E es c c' U Hc Hstep. change (preserved G c' U).
  destruct Hstep.
  - eapply preserve_selection; eassumption.
  - eapply preserve_assignment; eassumption.
  - eapply preserve_application; eassumption.
  - eapply preserve_literal; eauto using lit_inert_type.
  - eapply preserve_new; eassumption.
  - eapply preserve_return; eassumption.
  - eapply preserve_let_variable; eassumption.
  - eapply preserve_let_step; eassumption.
Qed.

Theorem progress: forall Gamma Delta ℰs Es t s Sigma T,
    ty_config Gamma Delta ℰs Es (t ; s; Sigma) T ->
    answer (t; s; Sigma) \/
    exists s' Sigma' t', (t; s; Sigma) ↦ (t'; s'; Sigma').
Proof.
  intros G D E Es t s Sigma T Hc.
  inversion Hc as [G0 D0 Sigma0 E0 Et Fs t0 T0 i U e' e et
    Hi Hid Hheap Hfree Hstack Hty He Hinit Hcorr]; subst.
  pose proof (invert_term_typing Hty) as Hhead.
  destruct t; repeat match goal with a : avar |- _ => destruct a end;
    simpl in Hhead; try contradiction.
  - destruct s as [|[] s].
    + left. constructor.
    + right. eauto using red_let_var.
    + right. eauto using red_return.
  - destruct Hhead as [S [V [Hfield _]]].
    destruct (canonical_field Hi Hheap Hfield) as [R [hds [W [o [Hb [_ [_ [Hhas _]]]]]]]].
    destruct (select_committed Hinit) as [_ Hcomm].
    destruct (committed_heap_of_stack Hfree) as [_ [_ Hall]].
    specialize (Hall _ _ Hcomm Hb). inversion Hall; subst.
    destruct (committed_field_initialized ltac:(eassumption) Hhas) as [y [-> _]].
    right. eauto using red_sel.
  - destruct Hhead as [S [V [Hfun _]]].
    destruct (canonical_function Hi Hheap Hfun) as [S0 [Tfun [body [Hb _]]]].
    right. eauto using red_app.
  - right. eauto using red_let_sta.
  - destruct (var_fresh (dom Sigma)) as [x Hx].
    right. eauto using red_let_lit.
  - destruct Hhead as [S [V [Hfield _]]].
    destruct (canonical_field Hi Hheap Hfield) as [R [hds [W [o [Hb [_ [_ [Hhas _]]]]]]]].
    destruct (heap_can_update v Hb Hhas) as [Sigma' Hup].
    right. exists s, Sigma', (trm_var (avar_f v)). apply red_asn. exact Hup.
  - destruct Hhead as [xs [Ts [is' [R [Hcon [Has [Hxs _]]]]]]].
    destruct (canonical_constructor Hi Hheap Hcon) as [ds [body [Hb _]]].
    destruct (var_fresh (dom Sigma \u fv (open_rec_vars 1 xs ds))) as [x Hx].
    apply notin_union in Hx. destruct Hx as [Hfresh Hfv].
    right. eauto 10 using red_new, typed_args_length.
Qed.
