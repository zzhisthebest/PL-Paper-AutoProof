Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Import Language Infra SubDis Determinism.

Definition i : Set := nat.

Definition sctx : Set := list ( i * typ ).

Inductive sexp :=
  | se_i : nat -> sexp
  | se_lit : nat -> sexp
  | se_unit : sexp
  | se_abs : nat -> sexp -> sexp
  | se_app : sexp -> sexp -> sexp
  | se_merge : sexp -> sexp -> sexp.

Inductive lityp : typ -> Prop :=
  | li_int : lityp int
  | li_top : lityp top
  | li_arr : forall (A B:typ),
      lityp A ->
      lityp B ->
      lityp (arr A B)
  | li_and : forall (A B:typ),
      lityp A ->
      lityp B ->
      lityp (and A B).

Definition sbinds (x : i) (A : typ) (E : list (i * typ)) : Prop := In (x, A) E.

Fixpoint sdom (E : list (i * typ)) {struct E} : list i :=
  match E with
    | nil => nil
    | (x, A) :: E' => cons x (sdom E')
  end.

Inductive suniq : list (i * typ) -> Prop :=
  | suniq_nil :
      suniq nil
  | suniq_push : forall x A E,
      suniq E ->
      ~ In x (sdom E) ->
      suniq (cons (x, A) E).

Fixpoint ctx_sw (E : list (i * typ)) {struct E} : typ :=
  match E with
    | nil => top
    | (x, A) :: E' => and (ctx_sw E') (rcd x A)
  end.

Inductive contains: nat -> typ -> Prop:=
  | ct_rcd : forall x A,
      contains x (rcd x A)
  | ct_andl : forall x A B,
      contains x A ->
      contains x (and A B)
  | ct_andr : forall x A B,
      contains x B ->
      contains x (and A B).

Definition fresh x A := ~ (contains x A).

Inductive styping : sctx -> sexp -> typ -> exp -> Prop :=
  | styping_lit : forall (G:sctx) (i5:i),
      suniq  G  ->
      styping G (se_lit i5) int (lit i5)
  | styping_top : forall (G:sctx),
      suniq  G  ->
      styping G se_unit top unit
  | styping_var : forall (G:sctx) (x:i) (A:typ),
      suniq G  ->
      sbinds  x A G  ->
      lityp A ->
      styping G (se_i x) A (proj  ( (ann ctx (rcd x A)) )  x)
  | styping_abs : forall (G:sctx) (x:i) (A:typ) (ee:sexp) (B:typ) (e:exp),
      styping  (cons ( x , A )  G )  ee B e ->
      lityp A ->
      lityp B ->
      styping G (se_abs x ee) (arr A B) (ann (lam wh e) (arr (rcd x A) B))
  | styping_app : forall (G:sctx) (ee1 ee2:sexp) (B:typ) (e1 e2:exp) (A:typ),
      styping G ee1 (arr A B) e1 ->
      styping G ee2 A e2 ->
      lityp A ->
      lityp B ->
      styping G (se_app ee1 ee2) B (app e1 e2)
  | styping_merge : forall (G:sctx) (ee1 ee2:sexp) (B:typ) (e1 e2:exp) (A:typ) (m:nat),
    styping G ee1 A e1 ->
    styping G ee2 B e2 ->
    lityp A ->
    lityp B ->
    disjoint A B ->
    fresh m A ->
    styping G (se_merge ee1 ee2) (and A B) (box (rec m ctx) (merge (box (proj ctx m) e1) (box (proj (ann ctx (rcd m (ctx_sw G))) m) e2)))
  | styping_sub : forall (G:sctx) (ee1 ee2:sexp) (B:typ) (e1 e2:exp) (A:typ) (m:nat),
    styping G ee1 A e1 ->
    lityp A ->
    lityp B ->
    sub A B ->
    styping G ee1 B (ann e1 B).

Section ListProperties.

Variables X : Set.

Variables x y : X.

Variables l l1 l2 l3 : list X.

End ListProperties.

(* ------------------------------------------------------------------ *)
(* Helper lemmas                                                        *)
(* ------------------------------------------------------------------ *)

Lemma sub_refl : forall A : typ, sub A A.
Proof.
  induction A.
  - apply sint.
  - apply stop.
  - apply sand.
    + apply sandl. assumption.
    + apply sandr. assumption.
  - apply srcd. assumption.
  - apply sarr; assumption.
Qed.

(* Every binding occurring in [G] is a supertype of the conjunction of [G]. *)
Lemma sub_ctx_sw_binds : forall (G : sctx) (x : i) (A : typ),
  sbinds x A G -> sub (ctx_sw G) (rcd x A).
Proof.
  intros G. induction G as [| [y B] G' IHG].
  - intros x A H. destruct H.
  - intros x A H. simpl in H. simpl.
    destruct H as [Heq | Hin].
    + inversion Heq; subst. apply sandr. apply sub_refl.
    + apply sandl. apply IHG. exact Hin.
Qed.

(* The label of a record is preserved by subtyping. *)
Lemma sub_rcd_label : forall (x y : nat) (A B : typ),
  sub (rcd x A) (rcd y B) -> y = x.
Proof.
  intros x y A B H. inversion H; subst. reflexivity.
Qed.

(* A subtype of a record either comes from the left or the right conjunct. *)
Lemma sub_and_rcd_inv : forall (A B : typ) (x : i) (D : typ),
  sub (and A B) (rcd x D) -> sub A (rcd x D) \/ sub B (rcd x D).
Proof.
  intros A B x D H. inversion H; subst; auto.
Qed.

(* If a context conjunction is a subtype of a record, the record's label
   occurs in the context. *)
Lemma sub_ctx_sw_rcd_inv : forall (G : sctx) (x : i) (D : typ),
  sub (ctx_sw G) (rcd x D) -> In x (sdom G).
Proof.
  intros G. induction G as [| [y B] G' IHG].
  - intros x D H. simpl in H. inversion H.
  - intros x D H. simpl in H.
    destruct (sub_and_rcd_inv (ctx_sw G') (rcd y B) x D H) as [H1 | H1].
    + simpl. right. apply (IHG x D). exact H1.
    + simpl. left. apply sub_rcd_label in H1. symmetry. exact H1.
Qed.

(* Well-ordered types are either [int], or a record/arrow whose codomain is
   well-ordered. *)
Lemma gord_rcd_inv : forall (m : nat) (X C : typ),
  gord C -> sub (rcd m X) C -> exists D, C = rcd m D.
Proof.
  intros m X C Hg. destruct Hg.
  - intros Hs. inversion Hs.
  - intros Hs. inversion Hs.
  - intros Hs. inversion Hs; subst. exists B. reflexivity.
Qed.

(* Literal/arrow/top types are never subtypes of a record. *)
Lemma lityp_not_sub_rcd : forall (A : typ),
  lityp A -> forall (m : nat) (B : typ), ~ sub A (rcd m B).
Proof.
  intros A HA. induction HA.
  - intros m C Hs. inversion Hs.
  - intros m C Hs. inversion Hs.
  - intros m C Hs. inversion Hs.
  - intros m C Hs. inversion Hs; subst.
    + exact (IHHA1 m C H2).
    + exact (IHHA2 m C H2).
Qed.

(* A syntactic [rcd] is disjoint from any literal type. *)
Lemma disjoint_rcd_lityp : forall (m : nat) (X A : typ),
  lityp A -> disjoint (rcd m X) A.
Proof.
  intros m X A HA Hcs.
  unfold cost_spec in Hcs. destruct Hcs as [C [Hg [H1 H2]]].
  destruct (gord_rcd_inv m X C Hg H1) as [D Heq]. subst C.
  exact (lityp_not_sub_rcd A HA m D H2).
Qed.

Lemma suniq_cons_inv : forall (G : sctx) (x : i) (A : typ),
  suniq (cons (x, A) G) -> suniq G /\ ~ In x (sdom G).
Proof.
  intros G x A H. inversion H; subst. split; assumption.
Qed.

(* A context conjunction is disjoint from a record at a label that does not
   occur in the context. *)
Lemma disjoint_abs : forall (G : sctx) (x : i) (A : typ),
  suniq (cons (x, A) G) -> disjoint (ctx_sw G) (rcd x A).
Proof.
  intros G x A Huniq Hcs.
  unfold cost_spec in Hcs. destruct Hcs as [C [Hg [H1 H2]]].
  destruct (gord_rcd_inv x A C Hg H2) as [D Heq]. subst C.
  assert (Hin : In x (sdom G)) by (apply (sub_ctx_sw_rcd_inv G x D); exact H1).
  destruct (suniq_cons_inv G x A Huniq) as [_ Hnotin].
  exact (Hnotin Hin).
Qed.

Lemma styping_suniq : forall (G : sctx) (ee : sexp) (A : typ) (e : exp),
  styping G ee A e -> suniq G.
Proof.
  intros G ee A e H.
  induction H as [ G0 i5 Hs
                 | G0 Hs
                 | G0 x A0 Hs Hbinds0 Hlt
                 | G0 x A0 ee0 B0 e0 Hprem IHprem HltA HltB
                 | G0 ee1 ee2 B0 e1 e2 A0 H1 IH1 H2 IH2 HltA HltB
                 | G0 ee1 ee2 B0 e1 e2 A0 m H1 IH1 H2 IH2 HltA HltB Hdisj Hfresh
                 | G0 ee1 ee2 B0 e1 e2 A0 m H1 IHprem HltA HltB Hsub ].
  - assumption.
  - assumption.
  - assumption.
  - destruct (suniq_cons_inv _ _ _ IHprem) as [HG _]. exact HG.
  - assumption.
  - assumption.
  - assumption.
Qed.

Theorem encoding_complete: forall sctx A ee e,
  styping sctx ee A e ->
  has_type (ctx_sw sctx) e inf A.
Proof.
  intros G A ee e Hst.
  induction Hst as [ G0 i5 Hs
                   | G0 Hs
                   | G0 x A0 Hs Hbinds0 Hlt
                   | G0 x A0 ee0 B0 e0 Hprem IHprem HltA HltB
                   | G0 ee1 ee2 B0 e1 e2 A0 H1 IH1 H2 IH2 HltA HltB
                   | G0 ee1 ee2 B0 e1 e2 A0 m H1 IH1 H2 IH2 HltA HltB Hdisj Hfresh
                   | G0 ee1 ee2 B0 e1 e2 A0 m H1 IHprem HltA HltB Hsub ].
  - (* lit *) apply tlit.
  - (* unit *) apply tunit.
  - (* var *) eapply tproj. eapply tann. eapply tsub.
    + apply tctx.
    + apply sub_ctx_sw_binds. exact Hbinds0.
  - (* abs *) simpl. eapply tlam.
    + apply disjoint_abs. apply styping_suniq in Hprem. exact Hprem.
    + apply ext_wh.
    + apply sub_refl.
    + eapply tsub.
      * simpl in IHprem. exact IHprem.
      * apply sub_refl.
  - (* app *) eapply tapp.
    + exact IH1.
    + eapply tsub. exact IH2. apply sub_refl.
  - (* merge *) eapply tbox.
    + eapply trec. apply tctx.
    + eapply tmrg.
      * eapply tbox with (B := ctx_sw G0) (A := A0).
        -- eapply tproj. apply tctx.
        -- exact IH1.
      * eapply tbox with (B := ctx_sw G0) (A := B0).
        -- eapply tproj. eapply tann. eapply tsub.
           ++ apply tctx.
           ++ apply sandl. apply sub_refl.
        -- exact IH2.
      * exact Hdisj.
      * apply disjoint_rcd_lityp. exact HltA.
  - (* sub *) eapply tann. eapply tsub.
    + exact IHprem.
    + exact Hsub.
Qed.
