Require Import Arith.

Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.

(* reminder: strengthen PEmpty       rs = rs
--           strengthen (PCons p ps) rs = PCons p (strengthen ps rs) *)

Lemma lem_strengthen_empty : forall (ps:preds), 
    strengthen ps PEmpty = ps.
Proof. induction ps. all : simpl.
  - (* PEmpty *) reflexivity.
  - (* PCons p ps *) rewrite -> IHps. reflexivity. Qed.

Lemma lem_strengthen_one : forall (p:expr) (ps:preds),
    strengthen (PCons p PEmpty) ps = PCons p ps.           (* may not be needed *)
Proof. intros p. induction ps. all : simpl.                (* cf. LemmasExactnessSubst.v *)
  - (* PEmpty *) reflexivity.
  - (* PCons p ps *) reflexivity. Qed.

Lemma lem_strengthen_assoc : forall (ps:preds) (qs:preds) (rs:preds),
    strengthen ps (strengthen qs rs) = strengthen (strengthen ps qs) rs.
Proof. induction ps. all : simpl.
  - (* PEmpty *) reflexivity.
  - (* PCons p ps *) intros. rewrite -> IHps. reflexivity. Qed.

Lemma lem_psubFV_strengthen : forall (x:var_name) (v:expr) (ps rs:preds),
    psubFV x v (strengthen ps rs) = strengthen (psubFV x v ps) (psubFV x v rs).
Proof. intros x v. induction ps. all : simpl.
  - (* PEmpty *) reflexivity.
  - (* PCons p ps *) intros rs. rewrite -> IHps. reflexivity. Qed.

Lemma lem_psubFTV_strengthen : forall (a:var_name) (t_a:type) (ps rs:preds),
    psubFTV a t_a (strengthen ps rs) = strengthen (psubFTV a t_a ps) (psubFTV a t_a rs).
Proof. intros a t_a. induction ps. all : simpl.
  - (* PEmpty *) reflexivity.
  - (* PCons p ps *) intros rs. rewrite -> IHps. reflexivity. Qed.

Lemma lem_openP_at_strengthen : forall (j:index) (y:var_name) (ps:preds) (rs:preds),
    openP_at j y (strengthen ps rs) = strengthen (openP_at j y ps) (openP_at j y rs).
Proof. intros j y. induction ps. all : simpl.
- (* PEmpty *) reflexivity.
- (* PCons p ps *) intros rs. rewrite -> IHps. reflexivity. Qed.

Lemma lem_unbindP_strengthen : forall (y:var_name) (ps rs:preds),
    unbindP y (strengthen ps rs) = strengthen (unbindP y ps) (unbindP y rs).
Proof. apply lem_openP_at_strengthen. Qed. 
 
Lemma lem_psubBV_at_strengthen : forall (j:index) (v:expr) (ps rs:preds),
    psubBV_at j v (strengthen ps rs) = strengthen (psubBV_at j v ps) (psubBV_at j v rs).
Proof. intros j v. induction ps. all : simpl.
  - (* PEmpty *) reflexivity.
  - (* PCons p ps *) intro rs. rewrite -> IHps. reflexivity. Qed.

Lemma lem_psubBV_strengthen : forall (v:expr) (ps rs:preds),
    psubBV v (strengthen ps rs) = strengthen (psubBV v ps) (psubBV v rs).
Proof. apply lem_psubBV_at_strengthen. Qed.

Lemma lem_open_tvP_at_strengthen : forall (j:index) (a':var_name) (ps rs:preds),
    open_tvP_at j a' (strengthen ps rs) = 
      strengthen (open_tvP_at j a' ps) (open_tvP_at j a' rs).
Proof. intros j a'. induction ps. all : simpl.
  - (* PEmpty *) reflexivity.
  - (* PCons p ps *) intro rs. rewrite -> IHps. reflexivity. Qed.

Lemma lem_psubBTV_at_strengthen : forall (j:index) (t_a:type) (ps rs:preds),
    psubBTV_at j t_a (strengthen ps rs) = 
      strengthen (psubBTV_at j t_a ps) (psubBTV_at j t_a rs).
Proof. intros j t_a. induction ps. all : simpl.
  - (* PEmpty *) reflexivity.
  - (* PCons p ps *) intro rs. rewrite -> IHps. reflexivity. Qed.

Lemma lem_psubBTV_strengthen : forall (t_a:type) (ps rs:preds),
    psubBTV t_a (strengthen ps rs) = strengthen (psubBTV t_a ps) (psubBTV t_a rs).
Proof. apply lem_psubBTV_at_strengthen. Qed.