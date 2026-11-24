Set Implicit Arguments.

From Stdlib Require Import Lia Arith.Wf_nat.
From TLC Require Import LibLN.

Require Import Full_ott Full_Infra.

Implicit Types x : var.

#[local] Hint Constructors sub wf lc_trm reduct value ivalue : core.

Lemma sub_wf : forall G a b T, sub G a b T -> wf G.
Proof.
  intros G a b T H. induction H; eauto.
Qed.

Scheme sub_mutind := Induction for sub Sort Prop
with wf_mutind := Induction for wf Sort Prop.
Combined Scheme sub_wf_mutind from sub_mutind, wf_mutind.

Lemma wf_ok : forall G, wf G -> ok G.
Proof.
  apply (@proj2 (forall G a b T, sub G a b T -> ok G)).
  apply sub_wf_mutind; eauto using ok_empty, ok_push.
Qed.

Lemma sub_lc : forall G a b T, sub G a b T -> lc_trm a /\ lc_trm b.
Proof.
  intros G a b T H. induction H; intuition eauto.
  all: try (eapply lc_trm_abs with (L := L); intuition eauto).
  all: try (eapply lc_trm_prod with (L := L); intuition eauto).
  all: try solve [econstructor; intuition eauto].
  all: match goal with H : forall y, y \notin ?S -> _ /\ _ , Hy : ?x \notin ?S |- _ =>
    first [exact (proj1 (H x Hy)) | exact (proj2 (H x Hy))]
  end.
Qed.

Lemma sub_left : forall G a b T, sub G a b T -> sub G a a T.
Proof.
  intros G a b T H. induction H; eauto using sub_wf.
Qed.

Lemma open_rec_other : forall t i j u x,
  i <> j ->
  open_trm_wrt_trm_rec i u (open_trm_wrt_trm_rec j (trm_var_f x) t) =
    open_trm_wrt_trm_rec j (trm_var_f x) t ->
  open_trm_wrt_trm_rec i u t = t.
Proof.
  induction t; intros i j u x Hneq H; simpl in *;
    try solve [reflexivity | inversion H; f_equal; eauto].
  destruct (classic (j = n)) as [-> | Hj].
  - rewrite If_r by congruence. reflexivity.
  - rewrite If_r in H by assumption. exact H.
Qed.

Lemma open_rec_lc : forall t, lc_trm t ->
  forall k u, open_trm_wrt_trm_rec k u t = t.
Proof.
  intros t H. induction H; intros k u; simpl; f_equal; eauto.
  all: destruct (var_fresh L) as [x Hx];
    eapply open_rec_other with (j := 0) (x := x);
    [discriminate | eauto].
Qed.

Lemma subst_same : forall t x, subst_trm (trm_var_f x) x t = t.
Proof.
  induction t; intros y; simpl; try solve [f_equal; auto].
  destruct (classic (x5 = y)) as [-> | Hneq];
    [rewrite If_l | rewrite If_r]; auto.
Qed.

Lemma subst_fresh : forall t u x, x \notin fv_trm t -> subst_trm u x t = t.
Proof.
  induction t; intros u y H; simpl in *;
    repeat rewrite notin_union in H;
    try solve [intuition; f_equal; auto].
  rewrite If_r; [reflexivity |].
  apply notin_singleton in H. congruence.
Qed.

Lemma subst_open_rec : forall t u x v k,
  lc_trm u ->
  subst_trm u x (open_trm_wrt_trm_rec k v t) =
  open_trm_wrt_trm_rec k (subst_trm u x v) (subst_trm u x t).
Proof.
  induction t; intros u y v k Hu; simpl; try solve [f_equal; auto].
  - destruct (classic (k = n)) as [-> | Hneq];
      [repeat rewrite If_l | repeat rewrite If_r]; auto.
  - destruct (classic (x5 = y)) as [-> | Hneq].
    + rewrite If_l by reflexivity. symmetry. now apply open_rec_lc.
    + rewrite If_r by assumption. reflexivity.
Qed.

Lemma subst_open_var : forall t u x y,
  lc_trm u -> y <> x ->
  subst_trm u x (t ^ y) = (subst_trm u x t) ^ y.
Proof.
  intros. unfold open_trm_wrt_trm. rewrite subst_open_rec by assumption.
  simpl. now rewrite If_r.
Qed.

Lemma subst_intro : forall t u x,
  lc_trm u -> x \notin fv_trm t ->
  subst_trm u x (t ^ x) = t ^^ u.
Proof.
  intros t u x Hu Hx. unfold open_trm_wrt_trm.
  rewrite subst_open_rec by assumption.
  rewrite (subst_fresh t u Hx). simpl. now rewrite If_l.
Qed.

Lemma subst_lc : forall t, lc_trm t ->
  forall u x, lc_trm u -> lc_trm (subst_trm u x t).
Proof.
  intros t H. induction H; intros u x Hu; simpl; eauto.
  - destruct (classic (x5 = x)) as [-> | Hneq];
      [rewrite If_l | rewrite If_r]; auto.
  - eapply lc_trm_abs with (L := L \u \{x}); eauto.
    intros y Hy. apply notin_union in Hy as [Hy Hneq].
    rewrite <- subst_open_var by (auto; now apply notin_singleton in Hneq).
    eauto.
  - eapply lc_trm_prod with (L := L \u \{x}); eauto.
    intros y Hy. apply notin_union in Hy as [Hy Hneq].
    rewrite <- subst_open_var by (auto; now apply notin_singleton in Hneq).
    eauto.
Qed.

Lemma subst_reduct : forall a b, a --> b ->
  forall u x, lc_trm u -> subst_trm u x a --> subst_trm u x b.
Proof.
  intros a b H. induction H; intros u x Hu; simpl; eauto using subst_lc.
  unfold open_trm_wrt_trm at 1. rewrite subst_open_rec by assumption.
  apply reduct_beta; eauto using subst_lc.
  change (lc_trm (subst_trm u x (trm_abs e3 A e1))). eauto using subst_lc.
Qed.

(* A context transformation specifies how each variable rule is transported.
   Quantifying over extensions lets the same transformation pass under binders. *)
Definition transports (u : trm) x (G F : env) : Prop :=
  forall K y e A, wf (F & K) -> binds y (bind_sub e A) G ->
    sub (F & K) (subst_trm u x (trm_var_f y))
      (subst_trm u x (trm_var_f y)) (subst_trm u x A) /\
    forall b, sub (F & K) (subst_trm u x e) b (subst_trm u x A) ->
      sub (F & K) (subst_trm u x (trm_var_f y)) b (subst_trm u x A).

Lemma transports_push : forall u x G F,
  transports u x G F ->
  forall y e A, y <> x ->
  transports u x (G & y ~ bind_sub e A)
    (F & y ~ bind_sub (subst_trm u x e) (subst_trm u x A)).
Proof.
  intros u x G F H y e A Hy K z q B Hwf Hb.
  destruct (binds_push_inv Hb) as [[-> Heq] | [_ Hb']].
  - injection Heq as -> ->. simpl. rewrite If_r by assumption.
    assert (Hbind : binds y (bind_sub (subst_trm u x e) (subst_trm u x A))
      (F & y ~ bind_sub (subst_trm u x e) (subst_trm u x A) & K)).
    { apply binds_concat_left_ok; [now apply wf_ok | apply binds_tail]. }
    split; eauto.
  - rewrite <- concat_assoc in *. eauto.
Qed.

Lemma sub_transport : forall G a b T, sub G a b T ->
  forall u x F, lc_trm u -> wf F -> transports u x G F ->
  sub F (subst_trm u x a) (subst_trm u x b) (subst_trm u x T).
Proof.
  intros G a b T H. induction H; intros u z F Hu HF Hmap.
  - simpl. auto.
  - specialize (Hmap empty _ _ _ ltac:(now rewrite concat_empty_r) H0).
    rewrite concat_empty_r in Hmap. exact (proj1 Hmap).
  - pose proof (Hmap empty _ _ _ ltac:(now rewrite concat_empty_r) H) as Hvar.
    rewrite concat_empty_r in Hvar. apply (proj2 Hvar). eauto.
  - simpl. eauto.
  - simpl. eauto.
  - simpl. eapply sub_abs with (L := (L \u \{z}) \u dom F); eauto.
    all: intros y Hy; apply notin_union in Hy as [Hy Hfresh];
      apply notin_union in Hy as [Hy Hneq]; apply notin_singleton in Hneq;
      repeat rewrite <- subst_open_var by assumption;
      first [eapply H2 | eapply H4]; eauto using transports_push.
    all: eapply wf_cons; eauto.
  - unfold open_trm_wrt_trm at 1. rewrite subst_open_rec by assumption.
    change (sub F (trm_app (subst_trm u z e1) (subst_trm u z A))
      (trm_app (subst_trm u z e2) (subst_trm u z A))
      (subst_trm u z C ^^ subst_trm u z A)).
    eapply sub_app; [exact (IHsub1 u z F Hu HF Hmap) | eauto].
  - simpl. eapply sub_prod with (L := (L \u \{z}) \u dom F); eauto.
    all: intros y Hy; apply notin_union in Hy as [Hy Hfresh];
      apply notin_union in Hy as [Hy Hneq]; apply notin_singleton in Hneq;
      repeat rewrite <- subst_open_var by assumption.
    + eapply H3; eauto using transports_push.
    + eapply H5; eauto using transports_push.
      eapply wf_cons; eauto. eapply sub_left. exact (IHsub1 u z F Hu HF Hmap).
  - simpl. eauto using subst_reduct.
  - simpl. eauto using subst_reduct.
  - eauto.
Qed.

Lemma sub_transport_id : forall G a b T, sub G a b T ->
  forall F x, wf F -> transports (trm_var_f x) x G F -> sub F a b T.
Proof.
  intros. pose proof (sub_transport H (lc_trm_var_f x) H0 H1) as Hsub.
  now repeat rewrite subst_same in Hsub.
Qed.

Lemma sub_weaken_extension : forall G a b T, sub G a b T ->
  forall K, wf (G & K) -> sub (G & K) a b T.
Proof.
  intros G a b T H K Hwf.
  destruct (var_fresh (dom G)) as [x Hx].
  eapply sub_transport_id with (x := x); eauto.
  intros F y e A HF Hb. repeat rewrite subst_same.
  assert (Hbind : binds y (bind_sub e A) (G & K & F)).
  { repeat apply binds_concat_left_ok; eauto using wf_ok, ok_concat_inv_l. }
  split; eauto.
Qed.

(* The outer syntax of related terms survives subsumption. The premises here
   retain the information needed to compose relations at different types. *)
Inductive sub_structure (G : env) : trm -> trm -> Prop :=
| ss_star : sub_structure G trm_star trm_star
| ss_var : forall x, sub_structure G (trm_var_f x) (trm_var_f x)
| ss_var_bound : forall x e A b,
    binds x (bind_sub e A) G -> sub G e b A ->
    sub_structure G (trm_var_f x) b
| ss_top : forall a, sub_structure G a trm_top
| ss_abs : forall L e A a b B,
    (forall x, x \notin L ->
      sub (G & x ~ bind_sub e A) (a ^ x) (b ^ x) (B ^ x)) ->
    sub_structure G (trm_abs e A a) (trm_abs e A b)
| ss_app : forall a b u e A B,
    sub G a b (trm_prod e A B) ->
    sub_structure G (trm_app a u) (trm_app b u)
| ss_prod : forall L e A B e' A' B',
    sub G A' A trm_star -> sub G e' e A -> sub G A A trm_star ->
    (forall x, x \notin L ->
      sub (G & x ~ bind_sub e A) (B ^ x) (B ^ x) trm_star) ->
    (forall x, x \notin L ->
      sub (G & x ~ bind_sub e' A') (B ^ x) (B' ^ x) trm_star) ->
    sub G e e A -> sub G e' e' A' ->
    sub_structure G (trm_prod e A B) (trm_prod e' A' B')
| ss_castup : forall B a b A,
    sub G a b A -> sub_structure G (trm_castup B a) (trm_castup B b)
| ss_castdn : forall a b A,
    sub G a b A -> sub_structure G (trm_castdn a) (trm_castdn b).

Lemma sub_structure_of : forall G a b T, sub G a b T -> sub_structure G a b.
Proof.
  intros G a b T H. induction H; eauto using sub_structure.
Qed.

Lemma sub_var_at_binding : forall G x e A b U,
  wf G -> binds x (bind_sub e A) G ->
  sub G (trm_var_f x) b U -> sub G (trm_var_f x) b A.
Proof.
  intros G x e A b U HG Hb H.
  pose proof (sub_structure_of H) as Hshape. inversion Hshape; subst.
  - eauto.
  - match goal with H' : binds x (bind_sub _ _) G |- _ =>
      first [constr_eq H' Hb; fail 1 | pose proof (binds_functional Hb H') as Heq]
    end.
    inversion Heq; subst. eauto.
  - eauto.
Qed.

Lemma sub_retype : forall G a b T, sub G a b T ->
  forall c U, sub G a c U -> sub G a c T.
Proof.
  intros G a b T H. induction H; intros c U Hc.
  - pose proof (sub_structure_of Hc) as Hshape. inversion Hshape; eauto.
  - eauto using sub_var_at_binding.
  - eauto using sub_var_at_binding, sub_wf.
  - eauto.
  - pose proof (sub_structure_of Hc) as Hshape. inversion Hshape; subst; eauto.
  - pose proof (sub_structure_of Hc) as Hshape. inversion Hshape; subst.
    + apply sub_top. eapply sub_abs with (L := L); eauto using sub_left.
    + eapply sub_abs with (L := L \u L0); eauto.
  - pose proof (sub_structure_of Hc) as Hshape. inversion Hshape; subst.
    + apply sub_top. eapply sub_app; eauto using sub_left.
    + eapply sub_app; eauto.
  - pose proof (sub_structure_of Hc) as Hshape. inversion Hshape; subst.
    + apply sub_top. eapply sub_prod with (L := L); eauto.
    + eapply sub_prod with (L := L0); eauto.
  - pose proof (sub_structure_of Hc) as Hshape. inversion Hshape; subst; eauto using sub_left.
  - pose proof (sub_structure_of Hc) as Hshape. inversion Hshape; subst; eauto using sub_left.
  - eauto.
Qed.

Definition composes_through (m : trm) : Prop :=
  forall G a b T U, sub G a m T -> sub G m b U -> sub G a b T.

Lemma sub_narrow_binding : forall G x e A e' A' a b T,
  sub G e' e A' -> sub G A' A trm_star -> x # G ->
  composes_through e ->
  sub (G & x ~ bind_sub e A) a b T ->
  sub (G & x ~ bind_sub e' A') a b T.
Proof.
  intros G x e A e' A' a b T He HA Hx Hcompose Hsub.
  assert (Hwf : wf (G & x ~ bind_sub e' A')) by eauto using sub_left.
  eapply sub_transport_id with (x := x); eauto.
  intros K y q B HK Hb. repeat rewrite subst_same.
  destruct (binds_push_inv Hb) as [[-> Heq] | [Hneq Hb']].
  - injection Heq as -> ->.
    assert (Hbind : binds x (bind_sub e' A') (G & x ~ bind_sub e' A' & K)).
    { apply binds_concat_left_ok; [now apply wf_ok | apply binds_tail]. }
    assert (HK' : wf (G & (x ~ bind_sub e' A' & K))) by now rewrite concat_assoc.
    pose proof (sub_weaken_extension He HK') as HeK.
    pose proof (sub_weaken_extension HA HK') as HAK.
    rewrite concat_assoc in HeK, HAK.
    split.
    + eapply sub_sub; [eapply sub_var_refl; eassumption | exact HAK].
    + intros c Hc. eapply sub_sub; [| exact HAK].
      eapply sub_var_trans; [exact Hbind | eapply Hcompose; eauto].
  - assert (Hbind : binds y (bind_sub q B) (G & x ~ bind_sub e' A' & K)).
    { apply binds_concat_left_ok; [now apply wf_ok | now apply binds_push_neq]. }
    split; eauto.
Qed.

Fixpoint trm_size (t : trm) : nat :=
  match t with
  | trm_var_b _ | trm_var_f _ | trm_star | trm_top => 1
  | trm_app a b | trm_castup a b | trm_anno a b => S (trm_size a + trm_size b)
  | trm_castdn a => S (trm_size a)
  | trm_abs a A b | trm_prod a A b => S (trm_size a + trm_size A + trm_size b)
  end.

Lemma trm_size_open_var : forall t x k,
  trm_size (open_trm_wrt_trm_rec k (trm_var_f x) t) = trm_size t.
Proof.
  induction t; intros x k; simpl; try solve [repeat (rewrite IHt || rewrite IHt1 ||
    rewrite IHt2 || rewrite IHt3); reflexivity].
  destruct (classic (k = n)); [rewrite If_l | rewrite If_r]; auto.
Qed.

(* For a product in the middle, both its bound and its opened codomain
   are smaller. The bound case supplies transitivity inside narrowing. *)
Lemma sub_composes : forall m, composes_through m.
Proof.
  apply (well_founded_induction (well_founded_ltof trm trm_size)).
  intros m IH. unfold ltof in IH. unfold composes_through in *.
  intros G a b T U H. revert b U IH.
  induction H; intros b U IH Hright.
  - pose proof (sub_structure_of Hright) as Hshape. inversion Hshape; eauto.
  - eauto using sub_var_at_binding.
  - eapply sub_var_trans; [eassumption | eauto].
  - pose proof (sub_structure_of Hright) as Hshape. inversion Hshape; subst; eauto.
  - pose proof (sub_structure_of Hright) as Hshape. inversion Hshape; subst; eauto.
  - pose proof (sub_structure_of Hright) as Hshape. inversion Hshape; subst.
    + apply sub_top. eapply sub_abs with (L := L); eauto using sub_left.
    + eapply sub_abs with (L := L \u L0); eauto.
      intros x Hx. apply notin_union in Hx as [Hx Hx'].
      eapply (IH (e2' ^ x)).
      * unfold open_trm_wrt_trm. rewrite trm_size_open_var. simpl. lia.
      * eauto.
      * eauto.
  - pose proof (sub_structure_of Hright) as Hshape. inversion Hshape; subst.
    + apply sub_top. eapply sub_app; eauto using sub_left.
    + eapply sub_app; [| eassumption].
      eapply (IH e2); [simpl; lia | eassumption | eassumption].
  - pose proof (sub_structure_of Hright) as Hshape. inversion Hshape; subst.
    + apply sub_top. eapply sub_prod with (L := L); eauto.
    + eapply sub_prod with (L := (L \u L0) \u dom G); eauto.
      * eapply (IH A'); [simpl; lia | eassumption | eassumption].
      * eapply sub_sub; [eapply (IH e'); [simpl; lia | eassumption | eassumption] |
          eassumption].
      * intros x Hx. apply notin_union in Hx as [Hx Hfresh].
        apply notin_union in Hx as [Hx Hx'].
        eapply (IH (B' ^ x)).
        -- unfold open_trm_wrt_trm. rewrite trm_size_open_var. simpl. lia.
        -- eapply sub_narrow_binding with (e := e') (A := A').
           ++ exact (sub_retype H18 H12).
           ++ exact H11.
           ++ exact Hfresh.
           ++ unfold composes_through. intros.
              eapply (IH e'); [simpl; lia | eassumption | eassumption].
           ++ eauto.
        -- eauto.
  - pose proof (sub_structure_of Hright) as Hshape. inversion Hshape; subst.
    + apply sub_top. eapply sub_castup; eauto using sub_left.
    + eapply sub_castup; [eassumption | | eassumption].
      eapply (IH e2); [simpl; lia | eassumption | eassumption].
  - pose proof (sub_structure_of Hright) as Hshape. inversion Hshape; subst.
    + apply sub_top. eapply sub_castdn; eauto using sub_left.
    + eapply sub_castdn; [eassumption | | eassumption].
      eapply (IH e2); [simpl; lia | eassumption | eassumption].
  - eauto.
Qed.

Lemma sub_instantiate : forall G u e A L a b T,
  sub G u e A ->
  (forall x, x \notin L ->
    sub (G & x ~ bind_sub e A) (a ^ x) (b ^ x) (T ^ x)) ->
  sub G (a ^^ u) (b ^^ u) (T ^^ u).
Proof.
  intros G u e A L a b T Hu Hbody.
  destruct (var_fresh (L \u fv_trm a \u fv_trm b \u fv_trm T \u
    fv_trm e \u fv_trm A \u fv_in_values fv_binding G)) as [x Hfresh].
  repeat rewrite notin_union in Hfresh.
  destruct Hfresh as [Hx [Ha [Hb [HT [He [HA HG]]]]]].
  assert (Hlc : lc_trm u) by exact (proj1 (sub_lc Hu)).
  repeat rewrite <- (subst_intro (x := x) _ Hlc) by assumption.
  eapply sub_transport; [now apply Hbody | exact Hlc | eauto using sub_wf |].
  intros K y q B HK Hbind.
  destruct (binds_push_inv Hbind) as [[-> Heq] | [Hneq Hbind']].
  - injection Heq as -> ->. simpl. rewrite If_l by reflexivity.
    rewrite (subst_fresh e u He), (subst_fresh A u HA).
    pose proof (sub_weaken_extension Hu HK) as Harg.
    split; eauto using sub_left.
    intros c Hc. exact (sub_composes Harg Hc).
  - simpl. rewrite If_r by assumption.
    pose proof (fv_in_values_binds fv_binding Hbind' HG) as Hfree.
    simpl in Hfree. apply notin_union in Hfree as [Hq HB].
    rewrite (subst_fresh q u Hq), (subst_fresh B u HB).
    assert (Hy : binds y (bind_sub q B) (G & K)).
    { apply binds_concat_left_ok; eauto using wf_ok. }
    split; eauto.
Qed.

(* Weak-head shapes omit arguments and annotations. Subtyping can replace a
   head by top, or expose the bound of a free variable. *)
Inductive head : Set :=
| h_var | h_star | h_top | h_abs | h_prod | h_up | h_other
| h_app (h : head) | h_down (h : head).

Fixpoint head_of (a : trm) : head :=
  match a with
  | trm_var_f _ => h_var
  | trm_star => h_star
  | trm_top => h_top
  | trm_abs _ _ _ => h_abs
  | trm_prod _ _ _ => h_prod
  | trm_castup _ _ => h_up
  | trm_app a _ => h_app (head_of a)
  | trm_castdn a => h_down (head_of a)
  | _ => h_other
  end.

Inductive head_sub : head -> head -> Prop :=
| hs_same : forall h, head_sub h h
| hs_var : forall h, head_sub h_var h
| hs_top : forall h, head_sub h h_top
| hs_app : forall a b, head_sub a b -> head_sub (h_app a) (h_app b)
| hs_down : forall a b, head_sub a b -> head_sub (h_down a) (h_down b).

#[local] Hint Constructors head_sub : core.

Lemma head_sub_trans : forall a b c, head_sub a b -> head_sub b c -> head_sub a c.
Proof.
  intros a b c H. revert c. induction H; intros c Hc; auto;
    inversion Hc; subst; eauto.
Qed.

Lemma sub_heads : forall G a b T, sub G a b T -> head_sub (head_of a) (head_of b).
Proof.
  intros G a b T H. induction H; simpl; auto.
Qed.

Definition value_base_head (a : trm) : option head :=
  match a with
  | trm_star | trm_prod _ _ _ => Some h_star
  | trm_abs _ _ _ => Some h_prod
  | trm_castup B _ => Some (head_of B)
  | _ => None
  end.

Lemma sub_value_type_head : forall G a b T, sub G a b T ->
  forall h, value_base_head a = Some h -> head_sub h (head_of T).
Proof.
  intros G a b T H. induction H; intros h Hh; simpl in Hh;
    try discriminate; try solve [inversion Hh; subst; simpl; auto].
  eapply head_sub_trans; [exact (IHsub1 h Hh) | exact (sub_heads H0)].
Qed.

Lemma castup_annotation_steps : forall G a b T, sub G a b T ->
  forall A e, a = trm_castup A e -> exists D, A --> D.
Proof.
  intros G a b T H. induction H; intros A0 e0 Heq; try discriminate; eauto.
  inversion Heq; subst. eauto.
Qed.

Fixpoint head_steps (h : head) : Prop :=
  match h with
  | h_app h_abs | h_down h_up => True
  | h_app h | h_down h => head_steps h
  | _ => False
  end.

Fixpoint head_has_var (h : head) : Prop :=
  match h with
  | h_var => True
  | h_app h | h_down h => head_has_var h
  | _ => False
  end.

Lemma reduct_head_steps : forall a b, a --> b -> head_steps (head_of a).
Proof.
  intros a b H. induction H; simpl; auto;
    match goal with |- context [head_of ?a] => destruct (head_of a); simpl in *; auto end.
Qed.

Lemma stepping_head_no_var : forall h, head_steps h -> ~ head_has_var h.
Proof.
  induction h; simpl; try tauto;
    match goal with h : head |- _ => destruct h; simpl in *; tauto end.
Qed.

Lemma head_sub_no_var : forall a b,
  head_sub a b -> ~ head_has_var a -> ~ head_has_var b.
Proof.
  intros a b H. induction H; simpl; tauto.
Qed.

Lemma head_sub_reflect_steps : forall a b,
  head_sub a b -> ~ head_has_var a -> head_steps b -> head_steps a.
Proof.
  intros a b H. induction H; simpl; try tauto.
  - destruct a, b; simpl in *; try tauto; inversion H.
  - destruct a, b; simpl in *; try tauto; inversion H.
Qed.

Lemma head_steps_reduct : forall a,
  lc_trm a -> head_steps (head_of a) -> exists b, a --> b.
Proof.
  intros a H. induction H; simpl; try contradiction.
  - destruct e1; simpl in *; try contradiction.
    + intros Hstep. destruct (IHlc_trm1 Hstep) as [b Hb]. eauto.
    + intros _. inversion H; subst. eauto.
    + intros Hstep. destruct (IHlc_trm1 Hstep) as [b Hb]. eauto.
  - destruct e; simpl in *; try contradiction.
    + intros Hstep. destruct (IHlc_trm Hstep) as [b Hb]. eauto.
    + intros _. inversion H; subst. eauto.
    + intros Hstep. destruct (IHlc_trm Hstep) as [b Hb]. eauto.
Qed.

Lemma sub_product_open : forall G e A B e' A' B' u,
  sub G (trm_prod e A B) (trm_prod e' A' B') trm_star ->
  sub G u e' A' ->
  sub G u e A /\ sub G (B ^^ u) (B' ^^ u) trm_star.
Proof.
  intros G e A B e' A' B' u H Hu.
  pose proof (sub_structure_of H) as Hshape. inversion Hshape; subst.
  assert (HuA : sub G u e' A) by (eapply sub_sub; eassumption).
  split.
  - eapply sub_composes; [exact HuA | eassumption].
  - change (sub G (B ^^ u) (B' ^^ u) (trm_star ^^ u)).
    eapply (sub_instantiate B B' trm_star Hu); eassumption.
Qed.

Lemma between_product_heads : forall t,
  head_sub h_prod (head_of t) -> head_sub (head_of t) h_prod ->
  exists e A B, t = trm_prod e A B.
Proof.
  destruct t; simpl; intros H H'; try solve [inversion H; inversion H'].
  eauto.
Qed.

Lemma sub_abs_open : forall G l r T, sub G l r T ->
  forall e A a e' A' b, l = trm_abs e A a -> r = trm_abs e' A' b ->
  forall p P C u, T = trm_prod p P C ->
  sub G u p P -> sub G (a ^^ u) (b ^^ u) (C ^^ u).
Proof.
  intros G l r T H. induction H; intros q Q a q' Q' b Hl Hr p P Cod u HT Hu;
    try discriminate.
  - inversion Hl; inversion Hr; inversion HT; subst.
    eapply sub_instantiate; eassumption.
  - subst B. assert (Hfrom : head_sub h_prod (head_of A)).
    { eapply sub_value_type_head; [exact H | now rewrite Hl]. }
    pose proof (sub_heads H0) as Hto. simpl in Hto.
    destruct (between_product_heads A Hfrom Hto) as [e [D [B ->]]].
    destruct (sub_product_open H0 Hu) as [Harg Hresult].
    eapply sub_sub.
    + eapply IHsub1; [exact Hl | exact Hr | reflexivity | exact Harg].
    + exact Hresult.
Qed.

Lemma reduct_deterministic : forall a b, a --> b -> forall c, a --> c -> b = c.
Proof.
  intros a b H. induction H; intros c Hc; inversion Hc; subst;
    try solve [reflexivity | f_equal; eauto];
    match goal with
    | H : trm_abs _ _ _ --> _ |- _ => inversion H
    | H : trm_castup _ _ --> _ |- _ => inversion H
    end.
Qed.

Lemma castup_type_reflect_steps : forall G B e b A D D',
  sub G (trm_castup B e) b A -> sub G A D trm_star -> D --> D' ->
  exists A', A --> A'.
Proof.
  intros G B e b A D D' H Hsub Hr.
  destruct (castup_annotation_steps H eq_refl) as [B' HB].
  assert (Hhead : head_sub (head_of B) (head_of A)).
  { eapply sub_value_type_head; [exact H | reflexivity]. }
  apply head_steps_reduct; [exact (proj1 (sub_lc Hsub)) |].
  eapply head_sub_reflect_steps.
  - exact (sub_heads Hsub).
  - eapply head_sub_no_var; [exact Hhead |].
    apply stepping_head_no_var. eauto using reduct_head_steps.
  - eauto using reduct_head_steps.
Qed.

Definition cast_payloads (G : env) (a b T : trm) : Prop :=
  match a, b with
  | trm_castup _ a, trm_castup _ b => forall T', T --> T' -> sub G a b T'
  | _, _ => True
  end.

Local Ltac impossible_step :=
  match goal with
  | H : trm_var_f _ --> _ |- _ => inversion H
  | H : trm_star --> _ |- _ => inversion H
  | H : trm_top --> _ |- _ => inversion H
  | H : trm_abs _ _ _ --> _ |- _ => inversion H
  | H : trm_prod _ _ _ --> _ |- _ => inversion H
  | H : trm_castup _ _ --> _ |- _ => inversion H
  end.

(* A cast elimination may reach its payload through subsumption in the
   operand typing. Prove payload typing and preservation together so the
   subsumption case can reduce both sides of the type comparison. *)
Lemma sub_preserves_pair : forall G a b T, sub G a b T ->
  (forall a' b', a --> a' -> b --> b' -> sub G a' b' T) /\ cast_payloads G a b T.
Proof.
  intros G a b T H. induction H; split;
    try solve [intros; impossible_step];
    try solve [exact I | destruct e; exact I | destruct e1; exact I].
  - intros a' b' Ha Hb. destruct IHsub1 as [IH _].
    inversion Ha; inversion Hb; subst.
    + eapply sub_abs_open; [exact H | reflexivity | reflexivity | reflexivity | exact H0].
    + pose proof (sub_structure_of H) as Hshape.
      inversion Hshape; subst; impossible_step.
    + pose proof (sub_structure_of H) as Hshape.
      inversion Hshape; subst; impossible_step.
    + eapply sub_app; [eauto | exact H0].
  - intros D HD. match goal with H : B --> A |- _ =>
      pose proof (reduct_deterministic H HD) as Heq
    end. now subst.
  - intros a' b' Ha Hb. destruct IHsub2 as [IH Hcast].
    inversion Ha; inversion Hb; subst.
    + eapply sub_castdn; [exact H | eauto | eassumption].
    + pose proof (sub_structure_of H0) as Hshape.
      inversion Hshape; subst; impossible_step.
    + pose proof (sub_structure_of H0) as Hshape.
      inversion Hshape; subst; impossible_step.
    + exact (Hcast B H1).
  - intros a' b' Ha Hb. destruct IHsub1 as [IH _]. eapply sub_sub; eauto.
  - destruct e1, e2; try exact I.
    intros D HD. destruct IHsub1 as [_ Hcast]. destruct IHsub2 as [IH _].
    destruct (castup_type_reflect_steps H H0 HD) as [A' HA].
    eapply sub_sub; [exact (Hcast A' HA) | exact (IH A' D HA HD)].
Qed.

Theorem subject_reduction_wh : forall E t t' T,
  sub E t t T -> t --> t' -> sub E t' t' T.
Proof.
  intros E t t' T H Hr. exact (proj1 (sub_preserves_pair H) t' t' Hr Hr).
Qed.

Lemma head_sub_to_product : forall h, head_sub h h_prod -> h = h_prod \/ h = h_var.
Proof.
  intros h H. inversion H; auto.
Qed.

Lemma value_at_product : forall G a b e A B,
  sub G a b (trm_prod e A B) -> value a ->
  ivalue a \/ exists q Q c, a = trm_abs q Q c.
Proof.
  intros G a b e A B H Hv. destruct Hv; eauto.
  - assert (Hhead : head_sub h_star h_prod).
    { change (head_sub h_star (head_of (trm_prod e A B))).
      eapply sub_value_type_head; [exact H | reflexivity]. }
    inversion Hhead.
  - assert (Hhead : head_sub h_star h_prod).
    { change (head_sub h_star (head_of (trm_prod e A B))).
      eapply sub_value_type_head; [exact H | reflexivity]. }
    inversion Hhead.
  - assert (Hhead : head_sub (head_of A0) h_prod).
    { change (head_sub (head_of A0) (head_of (trm_prod e A B))).
      eapply sub_value_type_head; [exact H | reflexivity]. }
    destruct (castup_annotation_steps H eq_refl) as [D HD].
    pose proof (reduct_head_steps HD) as Hstep.
    destruct (head_sub_to_product Hhead) as [Hshape | Hshape];
      rewrite Hshape in Hstep; contradiction.
Qed.

Lemma value_at_stepping_type : forall G a b T T',
  sub G a b T -> T --> T' -> value a ->
  ivalue a \/ exists B e, a = trm_castup B e.
Proof.
  intros G a b T T' H Hr Hv. destruct Hv; eauto.
  all: exfalso;
    let base := lazymatch type of H with
                | sub _ (trm_abs _ _ _) _ _ => constr:(h_prod)
                | _ => constr:(h_star)
                end in
    assert (Hhead : head_sub base (head_of T))
      by (eapply sub_value_type_head; [exact H | reflexivity]);
    exact (head_sub_reflect_steps Hhead ltac:(simpl; tauto) (reduct_head_steps Hr)).
Qed.

Lemma sub_progress_left : forall G a b T, sub G a b T ->
  value a \/ exists a', a --> a'.
Proof.
  intros G a b T H. pose proof (proj1 (sub_lc H)) as Hlc.
  induction H; try solve [left; eauto | left; inversion Hlc; subst; eauto].
  - apply IHsub. exact Hlc.
  - pose proof (proj1 (sub_lc H)) as Hfun.
    pose proof (proj1 (sub_lc H0)) as Harg.
    destruct (IHsub1 Hfun) as [Hv | [b Hb]].
    + destruct (value_at_product H Hv) as [Hi | [q [Q [c ->]]]].
      * left. eauto.
      * right. inversion Hfun; subst. eauto.
    + right. eauto.
  - pose proof (proj1 (sub_lc H0)) as Hop.
    destruct (IHsub2 Hop) as [Hv | [b Hb]].
    + destruct (value_at_stepping_type H0 H1 Hv) as [Hi | [B' [c ->]]].
      * left. eauto.
      * right. inversion Hop; subst. eauto.
    + right. eauto.
  - apply IHsub1. exact Hlc.
Qed.

Theorem progress_empty_wh : forall t T,
  sub empty t t T ->
  value t \/ exists t', t --> t'.

Proof.
  intros t T H. exact (sub_progress_left H).
Qed.
