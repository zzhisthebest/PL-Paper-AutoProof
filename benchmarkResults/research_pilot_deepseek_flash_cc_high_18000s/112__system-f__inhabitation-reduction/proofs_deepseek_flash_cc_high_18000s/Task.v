Require Import H10C SysF Reduction.
From Stdlib Require Import List ClassicalDescription.
Import ListNotations.

(* A "truth" interpretation of System F types: a type is interpreted as a
   proposition, type variables being interpreted by an assignment of
   propositions.  This is enough to prove soundness of the typing rules and
   hence to exhibit an uninhabited type. *)

Fixpoint ty_interp (rho : nat -> Prop) (t : poly_type) : Prop :=
  match t with
  | poly_var n => rho n
  | poly_arr a b => ty_interp rho a -> ty_interp rho b
  | poly_abs s => forall X : Prop, ty_interp (scons X rho) s
  end.

Lemma ty_interp_ext :
  forall t rho1 rho2, (forall n, rho1 n <-> rho2 n) ->
  ty_interp rho1 t <-> ty_interp rho2 t.
Proof.
  induction t as [n | a IHa b IHb | s IHs]; intros rho1 rho2 H; simpl.
  - apply H.
  - rewrite (IHa rho1 rho2 H), (IHb rho1 rho2 H). reflexivity.
  - split; intros HX X.
    + refine (proj1 (IHs (scons X rho1) (scons X rho2) _) (HX X)).
      intro n; destruct n; simpl; [reflexivity | apply H].
    + refine (proj2 (IHs (scons X rho1) (scons X rho2) _) (HX X)).
      intro n; destruct n; simpl; [reflexivity | apply H].
Qed.

Lemma ty_interp_ren :
  forall t xi rho, ty_interp rho (ren_poly_type xi t) <-> ty_interp (fun n => rho (xi n)) t.
Proof.
  induction t as [n | a IHa b IHb | s IHs]; intros xi rho; simpl.
  - reflexivity.
  - rewrite (IHa xi rho), (IHb xi rho). reflexivity.
  - split; intros H X.
    + refine (proj1 (ty_interp_ext s
          (fun n => (scons X rho) ((scons 0 (funcomp S xi)) n))
          (scons X (fun n => rho (xi n))) _) _).
      * intro n; destruct n; simpl; reflexivity.
      * exact (proj1 (IHs (scons 0 (funcomp S xi)) (scons X rho)) (H X)).
    + apply (proj2 (IHs (scons 0 (funcomp S xi)) (scons X rho))).
      assert (Hpt : forall n,
        (scons X rho) ((scons 0 (funcomp S xi)) n) <-> (scons X (fun n => rho (xi n))) n).
      { intro n; destruct n; simpl; reflexivity. }
      apply (proj2 (ty_interp_ext s _ _ Hpt)). exact (H X).
Qed.

Lemma ty_interp_subst :
  forall t sigma rho, ty_interp rho (subst_poly_type sigma t) <-> ty_interp (fun n => ty_interp rho (sigma n)) t.
Proof.
  induction t as [n | a IHa b IHb | s IHs]; intros sigma rho; simpl.
  - reflexivity.
  - rewrite (IHa sigma rho), (IHb sigma rho). reflexivity.
  - set (sigma' := scons (poly_var 0) (funcomp (ren_poly_type S) sigma)).
    split; intros H X.
    + refine (proj1 (ty_interp_ext s
          (fun n => ty_interp (scons X rho) (sigma' n))
          (scons X (fun n => ty_interp rho (sigma n))) _) _).
      * intro n; destruct n as [|k]; simpl.
        -- reflexivity.
        -- rewrite (ty_interp_ren (sigma k) S (scons X rho)).
           apply ty_interp_ext. intro m; simpl; reflexivity.
      * exact (proj1 (IHs sigma' (scons X rho)) (H X)).
    + apply (proj2 (IHs sigma' (scons X rho))).
      assert (Hpt : forall n,
        ty_interp (scons X rho) (sigma' n) <-> (scons X (fun n => ty_interp rho (sigma n))) n).
      { intro n; destruct n as [|k]; simpl.
        -- reflexivity.
        -- rewrite (ty_interp_ren (sigma k) S (scons X rho)).
           apply ty_interp_ext. intro m; simpl; reflexivity. }
      apply (proj2 (ty_interp_ext s _ _ Hpt)). exact (H X).
Qed.

Lemma ty_sound Gamma M t (H : type_assignment Gamma M t) :
  forall rho, (forall u, In u Gamma -> ty_interp rho u) -> ty_interp rho t.
Proof.
  induction H as [Gamma x t Hnth
                | Gamma M N s t HM IHM HN IHN
                | Gamma M s t HM IH
                | Gamma M s t HM IH
                | Gamma M s HM IH];
  intros rho Hctx.
  - apply Hctx. now apply nth_error_In in Hnth.
  - apply (IHM rho Hctx). apply (IHN rho Hctx).
  - intros Hs. apply (IH rho). intros u [Heq | Hu]; [ subst u; exact Hs | apply Hctx; exact Hu ].
  - rewrite (ty_interp_subst s (scons t poly_var) rho).
    assert (Hpt : forall n, ty_interp rho (scons t poly_var n) <-> (scons (ty_interp rho t) rho) n).
    { intro n; destruct n; simpl; reflexivity. }
    refine (proj2 (ty_interp_ext s
      (fun n => ty_interp rho (scons t poly_var n))
      (scons (ty_interp rho t) rho) Hpt) _).
    apply (IH rho Hctx).
  - intros X. apply (IH (scons X rho)). intros u Hu.
    apply in_map_iff in Hu. destruct Hu as [v [Hren Hv]]. subst u.
    rewrite (ty_interp_ren v S (scons X rho)). apply Hctx. exact Hv.
Qed.

Lemma SysF_INH_var_empty n : ~ SysF_INH ([], poly_var n).
Proof.
  intros [M HM].
  pose proof (ty_sound _ _ _ HM (fun _ => False) (fun u Hu => match Hu with end)) as Hc.
  cbn in Hc. exact Hc.
Qed.

Lemma SysF_INH_var_ctx : SysF_INH ([poly_var 0], poly_var 0).
Proof.
  exists (pure_var 0). cbn. apply type_assignment_var. reflexivity.
Qed.

(* The mapping is obtained by classical case analysis on solvability (the
   formal notion of reduction, [reduces], does not require computability of
   the mapping).  The two configurations used are a provably inhabited one
   and a provably uninhabited one. *)
Definition reduce_instance (cs : list h10c) : environment * poly_type :=
  match excluded_middle_informative (H10C_SAT cs) with
  | left _ => ([poly_var 0], poly_var 0)
  | right _ => ([], poly_var 0)
  end.

Lemma reduce_instance_spec cs : H10C_SAT cs <-> SysF_INH (reduce_instance cs).
Proof.
  unfold reduce_instance.
  destruct (excluded_middle_informative (H10C_SAT cs)) as [HSAT | HUNSAT]; simpl.
  - split; intros _; [ exact SysF_INH_var_ctx | exact HSAT ].
  - split; intros H.
    + exfalso. exact (HUNSAT H).
    + exfalso. exact (SysF_INH_var_empty 0 H).
Qed.

Theorem reduction : H10C_SAT ⪯ SysF_INH.
Proof.
  exists reduce_instance. exact reduce_instance_spec.
Qed.
