Require Import SysF SemiU Reduction.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

Local Definition up_ren (r : nat -> nat) := scons 0 (funcomp S r).
Local Definition up_sub (f : nat -> poly_type) :=
  scons (poly_var 0) (funcomp (ren_poly_type S) f).

Local Lemma ren_ext r q A :
  (forall x, r x = q x) -> ren_poly_type r A = ren_poly_type q A.
Proof.
  revert r q. induction A; intros r q H; cbn.
  - now rewrite H.
  - now rewrite (IHA1 r q H), (IHA2 r q H).
  - f_equal. apply IHA. intros x. change (up_ren r x = up_ren q x).
    destruct x; unfold up_ren, scons, funcomp; [reflexivity|now rewrite H].
Qed.

Local Lemma sub_ext f g A :
  (forall x, f x = g x) -> subst_poly_type f A = subst_poly_type g A.
Proof.
  revert f g. induction A; intros f g H; cbn.
  - apply H.
  - now rewrite (IHA1 f g H), (IHA2 f g H).
  - f_equal. apply IHA. intros x. change (up_sub f x = up_sub g x).
    destruct x; unfold up_sub, scons, funcomp; [reflexivity|now rewrite H].
Qed.

Local Lemma ren_ren r q A :
  ren_poly_type r (ren_poly_type q A) = ren_poly_type (funcomp r q) A.
Proof.
  revert r q. induction A; intros r q; cbn; try reflexivity.
  - now rewrite IHA1, IHA2.
  - f_equal. rewrite IHA. apply ren_ext. now intros [|x].
Qed.

Local Lemma sub_ren f r A :
  subst_poly_type f (ren_poly_type r A) = subst_poly_type (funcomp f r) A.
Proof.
  revert f r. induction A; intros f r; cbn; try reflexivity.
  - now rewrite IHA1, IHA2.
  - f_equal. rewrite IHA. apply sub_ext. now intros [|x].
Qed.

Local Lemma ren_sub r f A :
  ren_poly_type r (subst_poly_type f A) =
  subst_poly_type (funcomp (ren_poly_type r) f) A.
Proof.
  revert r f. induction A; intros r f; cbn; try reflexivity.
  - now rewrite IHA1, IHA2.
  - f_equal. rewrite IHA. apply sub_ext. intros [|x]; cbn [funcomp scons].
    + reflexivity.
    + change (ren_poly_type (up_ren r) (ren_poly_type S (f x)) =
              ren_poly_type S (ren_poly_type r (f x))).
      now rewrite !ren_ren.
Qed.

Local Lemma sub_sub f g A :
  subst_poly_type f (subst_poly_type g A) =
  subst_poly_type (funcomp (subst_poly_type f) g) A.
Proof.
  revert f g. induction A; intros f g; cbn; try reflexivity.
  - now rewrite IHA1, IHA2.
  - f_equal. rewrite IHA. apply sub_ext. intros [|x]; cbn [funcomp scons subst_poly_type].
    + reflexivity.
    + change (subst_poly_type (up_sub f) (ren_poly_type S (g x)) =
              ren_poly_type S (subst_poly_type f (g x))).
      now rewrite sub_ren, ren_sub.
Qed.

Local Lemma sub_vars A : subst_poly_type poly_var A = A.
Proof.
  induction A; cbn; try congruence.
  f_equal. rewrite <- IHA at 2. apply sub_ext. now intros [|x].
Qed.

Local Lemma sub_cancel f A :
  subst_poly_type (scons f poly_var) (ren_poly_type S A) = A.
Proof. rewrite sub_ren. apply sub_vars. Qed.

Local Lemma sub_inst f B A :
  subst_poly_type f (subst_poly_type (scons B poly_var) A) =
  subst_poly_type (scons (subst_poly_type f B) poly_var)
    (subst_poly_type (up_sub f) A).
Proof.
  rewrite !sub_sub. apply sub_ext. intros [|x].
  - reflexivity.
  - cbn [funcomp up_sub scons subst_poly_type]. symmetry. apply sub_cancel.
Qed.

Local Lemma typing_sub G M A :
  type_assignment G M A -> forall f,
  type_assignment (map (subst_poly_type f) G) M (subst_poly_type f A).
Proof.
  intros H. induction H; intros f; cbn.
  - constructor. rewrite nth_error_map, H. reflexivity.
  - econstructor; eauto.
  - constructor. apply IHtype_assignment.
  - rewrite sub_inst. econstructor. apply (IHtype_assignment f).
  - constructor. specialize (IHtype_assignment (up_sub f)).
    rewrite !map_map in *.
    replace (map (fun x => ren_poly_type S (subst_poly_type f x)) Gamma)
      with (map (fun x => subst_poly_type (up_sub f) (ren_poly_type S x)) Gamma).
    + exact IHtype_assignment.
    + apply map_ext. intros A. rewrite sub_ren, ren_sub. reflexivity.
Qed.

Local Fixpoint specialize_type (args : list poly_type) (A : poly_type) :
    option poly_type :=
  match args with
  | [] => Some A
  | B :: rest =>
      match A with
      | poly_abs C => specialize_type rest (subst_poly_type (scons B poly_var) C)
      | _ => None
      end
  end.

Local Lemma sub_open f B A :
  subst_poly_type (scons B poly_var) (subst_poly_type (up_sub f) A) =
  subst_poly_type (scons B f) A.
Proof.
  rewrite sub_sub. apply sub_ext. intros [|x].
  - reflexivity.
  - change (subst_poly_type (scons B poly_var) (ren_poly_type S (f x)) = f x).
    apply sub_cancel.
Qed.

Local Lemma map_sub_shift f B G :
  map (subst_poly_type (scons B f)) (map (ren_poly_type S) G) =
  map (subst_poly_type f) G.
Proof.
  rewrite map_map. apply map_ext. intros A. rewrite sub_ren. reflexivity.
Qed.

Local Lemma arrow_inv G M A :
  type_assignment G (pure_abs M) A ->
  forall f args B C, specialize_type args (subst_poly_type f A) =
    Some (poly_arr B C) ->
    type_assignment (B :: map (subst_poly_type f) G) M C.
Proof.
  intros H. remember (pure_abs M) as N eqn:HN.
  induction H; intros f args B C E; inversion HN; subst.
  - destruct args as [|D args]; cbn in E; try discriminate.
    inversion E; subst. exact (typing_sub _ _ _ H f).
  - apply (IHtype_assignment eq_refl f (subst_poly_type f t :: args) B C).
    cbn. now rewrite <- sub_inst.
  - destruct args as [|D args]; [discriminate|].
    change (specialize_type args
              (subst_poly_type (scons D poly_var) (subst_poly_type (up_sub f) s))
            = Some (poly_arr B C)) in E.
    rewrite sub_open in E.
    pose proof (IHtype_assignment eq_refl (scons D f) args B C E) as K.
    now rewrite map_sub_shift in K.
Qed.

Local Lemma abs_inv G M B C :
  type_assignment G (pure_abs M) (poly_arr B C) ->
  type_assignment (B :: G) M C.
Proof.
  intros H. pose proof (arrow_inv _ _ _ H poly_var [] B C) as K.
  rewrite sub_vars in K. rewrite (map_ext _ _ sub_vars), map_id in K. auto.
Qed.

Local Lemma app_inv G M N A :
  type_assignment G (pure_app M N) A ->
  exists B C, type_assignment G M (poly_arr B C) /\ type_assignment G N B.
Proof.
  intros H. remember (pure_app M N) as P eqn:HP.
  induction H; inversion HP; subst.
  - eauto.
  - auto.
  - destruct IHtype_assignment as (B & C & HB & HC); [reflexivity|].
    exists (subst_poly_type (scons (poly_var 0) poly_var) B),
           (subst_poly_type (scons (poly_var 0) poly_var) C).
    assert (E : map (subst_poly_type (scons (poly_var 0) poly_var))
                    (map (ren_poly_type S) Gamma) = Gamma).
    { rewrite map_sub_shift, (map_ext _ _ sub_vars), map_id. reflexivity. }
    rewrite <- E. split.
    + exact (typing_sub _ _ _ HB (scons (poly_var 0) poly_var)).
    + exact (typing_sub _ _ _ HC (scons (poly_var 0) poly_var)).
Qed.

Local Lemma var_specialization G x A :
  type_assignment G (pure_var x) A ->
  forall f args B, (forall C, B <> poly_abs C) ->
    specialize_type args (subst_poly_type f A) = Some B ->
    exists E actual_args, nth_error G x = Some E /\
      specialize_type actual_args (subst_poly_type f E) =
        Some B.
Proof.
  intros H. remember (pure_var x) as M eqn:HM.
  induction H; intros f args B HB E; inversion HM; subst.
  - eauto.
  - apply (IHtype_assignment eq_refl f (subst_poly_type f t :: args) B HB).
    cbn. now rewrite <- sub_inst.
  - destruct args as [|D args].
    { cbn [specialize_type subst_poly_type] in E. injection E as E.
      exact (False_rect _ (HB _ (eq_sym E))). }
    change (specialize_type args
              (subst_poly_type (scons D poly_var) (subst_poly_type (up_sub f) s))
            = Some B) in E.
    rewrite sub_open in E.
    destruct (IHtype_assignment eq_refl (scons D f) args B HB E)
      as (E' & actual_args & P & Q).
    rewrite nth_error_map in P.
    destruct (nth_error Gamma x) as [T|] eqn:HT; cbn in P; try discriminate.
    inversion P; subst E'. rewrite sub_ren in Q.
    exists T, actual_args. auto.
Qed.

Local Lemma var_arrow_specialization G x A :
  type_assignment G (pure_var x) A ->
  forall f args B C, specialize_type args (subst_poly_type f A) =
    Some (poly_arr B C) ->
    exists E actual_args, nth_error G x = Some E /\
      specialize_type actual_args (subst_poly_type f E) =
        Some (poly_arr B C).
Proof.
  intros H f args B C. eapply var_specialization; try exact H. intros T E. discriminate.
Qed.

(* Quantifier erasure reserves atom 0 for bound variables and preserves
   substitution on the remaining atoms. *)
Local Fixpoint project_type (v : valuation) (A : poly_type) : term :=
  match A with
  | poly_var n => v n
  | poly_arr B C => arr (project_type v B) (project_type v C)
  | poly_abs B => project_type (scons (atom 0) v) B
  end.

Local Lemma project_ext v w A :
  (forall n, v n = w n) -> project_type v A = project_type w A.
Proof.
  revert v w. induction A; intros v w E; cbn.
  - apply E.
  - now rewrite (IHA1 v w E), (IHA2 v w E).
  - apply IHA. intros [|n]; [reflexivity|apply E].
Qed.

Local Lemma project_ren v r A :
  project_type v (ren_poly_type r A) =
  project_type (funcomp v r) A.
Proof.
  revert v r. induction A; intros v r; cbn; try reflexivity.
  - now rewrite IHA1, IHA2.
  - rewrite IHA. apply project_ext. now intros [|n].
Qed.

Local Lemma project_sub v f A :
  project_type v (subst_poly_type f A) =
  project_type (funcomp (project_type v) f) A.
Proof.
  revert v f. induction A; intros v f; cbn; try reflexivity.
  - now rewrite IHA1, IHA2.
  - rewrite IHA. apply project_ext. intros [|n]; [reflexivity|].
    change (project_type (scons (atom 0) v) (ren_poly_type S (f n)) =
            project_type v (f n)).
    now rewrite project_ren.
Qed.

Local Lemma project_substitute v w (f : valuation) A :
  (f 0 = atom 0) ->
  (forall n, substitute f (v n) = w n) ->
  substitute f (project_type v A) = project_type w A.
Proof.
  intros H0. revert v w. induction A; intros v w H; cbn.
  - apply H.
  - now rewrite (IHA1 v w H), (IHA2 v w H).
  - apply IHA. intros [|n]; [exact H0|apply H].
Qed.

Local Definition erase_type := project_type (fun n => atom (S n)).

Local Lemma erase_sub f A :
  erase_type (subst_poly_type f A) =
  substitute (scons (atom 0) (funcomp erase_type f)) (erase_type A).
Proof.
  unfold erase_type. rewrite project_sub. symmetry.
  apply project_substitute; reflexivity.
Qed.

Local Fixpoint quantify (k : nat) (A : poly_type) :=
  match k with
  | 0 => A
  | S k => poly_abs (quantify k A)
  end.

Local Fixpoint lift_substitution (k : nat) (f : nat -> poly_type) :=
  match k with
  | 0 => f
  | S k => lift_substitution k (up_sub f)
  end.

Local Lemma sub_quantify f k A :
  subst_poly_type f (quantify k A) =
  quantify k (subst_poly_type (lift_substitution k f) A).
Proof.
  revert f. induction k; intros f; cbn; [reflexivity|].
  f_equal. apply IHk.
Qed.

Local Lemma specialize_quantify k args A B :
  length args = k ->
  specialize_type args (quantify k A) = Some B ->
  exists f, subst_poly_type f A = B.
Proof.
  revert k A B. induction args as [|D args IH]; intros [|k] A B Len E;
    cbn in Len; try discriminate.
  - cbn in E. inversion E; subst. exists poly_var. apply sub_vars.
  - change (specialize_type args
          (subst_poly_type (scons D poly_var) (quantify k A)) = Some B) in E.
    rewrite sub_quantify in E. injection Len as Len.
    destruct (IH k _ _ Len E) as [f H].
    rewrite sub_sub in H. eauto.
Qed.

Local Lemma ren_id A : ren_poly_type (fun x => x) A = A.
Proof.
  induction A; cbn; try congruence.
  f_equal. etransitivity; [|exact IHA].
  apply ren_ext. now intros [|n].
Qed.

Local Lemma lift_substitution_index k f j :
  lift_substitution k f j =
  if j <? k then poly_var j else ren_poly_type (Nat.add k) (f (j - k)).
Proof.
  revert f j. induction k; intros f j.
  - cbn. rewrite Nat.sub_0_r. symmetry. apply ren_id.
  - cbn [lift_substitution]. rewrite IHk.
    destruct (j <? S k) eqn:H; destruct (j <? k) eqn:E.
    + reflexivity.
    + apply Nat.ltb_lt in H. apply Nat.ltb_ge in E.
      assert (F : j = k) by lia. subst j.
      rewrite Nat.sub_diag. cbn [up_sub scons].
      change (poly_var (k + 0) = poly_var k). now rewrite Nat.add_0_r.
    + apply Nat.ltb_ge in H. apply Nat.ltb_lt in E. lia.
    + apply Nat.ltb_ge in H.
      assert (Hs : j - k = S (j - S k)) by lia.
      rewrite Hs.
      change (ren_poly_type (Nat.add k) (ren_poly_type S (f (j - S k))) =
        ren_poly_type (Nat.add (S k)) (f (j - S k))). rewrite ren_ren.
      apply ren_ext. intros n. unfold funcomp. lia.
Qed.

Local Definition prefix_substitution (k : nat) (f : nat -> poly_type) :=
  fun j => if j <? k then f j else poly_var (j - k).

Local Fixpoint opening_args (k : nat) (f : nat -> poly_type) :=
  match k with
  | 0 => []
  | S k => f k :: opening_args k f
  end.

Local Lemma specialize_prefix k f A :
  specialize_type (opening_args k f) (quantify k A) =
  Some (subst_poly_type (prefix_substitution k f) A).
Proof.
  revert A. induction k as [|k IH]; intros A.
  - cbn [opening_args quantify specialize_type]. f_equal.
    rewrite <- (sub_vars A) at 1. apply sub_ext. intros j.
    unfold prefix_substitution. destruct j; reflexivity.
  - change (specialize_type (opening_args k f)
      (subst_poly_type (scons (f k) poly_var)
         (quantify k A)) = Some (subst_poly_type (prefix_substitution (S k) f) A)).
    rewrite sub_quantify, IH, sub_sub. f_equal. apply sub_ext.
    intros j. unfold funcomp. rewrite lift_substitution_index.
    unfold prefix_substitution. destruct (j <? k) eqn:E.
    + assert (j <? S k = true) as H by (apply Nat.ltb_lt in E; apply Nat.ltb_lt; lia).
      rewrite H. change ((if j <? k then f j else poly_var (j - k)) = f j). now rewrite E.
    + apply Nat.ltb_ge in E.
      rewrite sub_ren. destruct (j <? S k) eqn:H.
      * apply Nat.ltb_lt in H. assert (F : j = k) by lia. subst j.
        rewrite Nat.sub_diag. cbn [scons].
        transitivity (subst_poly_type poly_var (f k)); [|apply sub_vars].
        apply sub_ext. intros n. unfold funcomp.
        replace (k + n <? k) with false by (symmetry; apply Nat.ltb_ge; lia).
        f_equal. lia.
      * apply Nat.ltb_ge in H.
        replace (j - k) with (S (j - S k)) by lia. cbn [scons subst_poly_type].
        unfold funcomp.
        replace (k + (j - S k) <? k) with false by (symmetry; apply Nat.ltb_ge; lia).
        change (poly_var (k + (j - S k) - k) = poly_var (j - S k)).
        f_equal. lia.
Qed.

Local Lemma specialize_arrow_length k args A B C D :
  specialize_type args (quantify k (poly_arr A B)) = Some (poly_arr C D) ->
  length args = k.
Proof.
  revert args A B C D. induction k as [|k IH]; intros [|X args] A B C D H;
    try discriminate; try reflexivity.
  change (specialize_type args
    (subst_poly_type (scons X poly_var) (quantify k (poly_arr A B))) =
      Some (poly_arr C D)) in H.
  rewrite sub_quantify in H. cbn [subst_poly_type] in H. cbn [length].
  f_equal. exact (IH _ _ _ _ _ H).
Qed.

Local Lemma typing_specialize G M A B args :
  type_assignment G M A ->
  specialize_type args A = Some B ->
  type_assignment G M B.
Proof.
  revert A. induction args as [|X args IH]; intros A H E.
  - cbn in E. injection E as E. subst B. exact H.
  - destruct A as [n|L R|A]; try discriminate.
    cbn in E. eapply IH; try exact E. now apply type_assignment_inst.
Qed.

Local Lemma typing_ren G M A :
  type_assignment G M A -> forall r,
  type_assignment (map (ren_poly_type r) G) M (ren_poly_type r A).
Proof.
  intros H r.
  assert (E : forall B, subst_poly_type (fun n => poly_var (r n)) B =
                       ren_poly_type r B).
  { intros B. rewrite <- (sub_vars (ren_poly_type r B)), sub_ren.
    reflexivity. }
  pose proof (typing_sub _ _ _ H (fun n => poly_var (r n))) as K.
  now rewrite E, (map_ext _ _ E) in K.
Qed.

Local Lemma typing_open G M A :
  type_assignment G M (poly_abs A) ->
  type_assignment (map (ren_poly_type S) G) M A.
Proof.
  intros H. pose proof (typing_ren _ _ _ H S) as K.
  change (type_assignment (map (ren_poly_type S) G) M (poly_abs (ren_poly_type (up_ren S) A))) in K.
  pose proof (@type_assignment_inst _ _ _ (poly_var 0) K) as L.
  rewrite sub_ren in L.
  replace (subst_poly_type (funcomp (scons (poly_var 0) poly_var) (up_ren S)) A)
    with A in L; [exact L|].
  symmetry. rewrite <- (sub_vars A) at 2. apply sub_ext. now intros [|n].
Qed.

Local Lemma typing_open_prefix G M k A :
  type_assignment G M (quantify k A) ->
  type_assignment (map (ren_poly_type (Nat.add k)) G) M A.
Proof.
  revert G. induction k as [|k IH]; intros G H.
  - cbn. rewrite (map_ext _ _ ren_id), map_id. exact H.
  - cbn [quantify] in H. apply typing_open in H. apply IH in H.
    rewrite map_map in H.
    replace (map (ren_poly_type (Nat.add (S k))) G) with
      (map (fun x => ren_poly_type (Nat.add k) (ren_poly_type S x)) G).
    + exact H.
    + apply map_ext. intros B. rewrite ren_ren. apply ren_ext.
      intro n. unfold funcomp. lia.
Qed.

Local Fixpoint head_quantifiers (A : poly_type) : nat :=
  match A with poly_abs B => S (head_quantifiers B) | _ => 0 end.

Local Fixpoint head_body (A : poly_type) : poly_type :=
  match A with poly_abs B => head_body B | _ => A end.

Local Lemma head_decompose A :
  A = quantify (head_quantifiers A) (head_body A).
Proof. induction A; cbn; congruence. Qed.

Local Lemma head_body_nonabs A B : head_body A <> poly_abs B.
Proof. induction A; cbn; congruence. Qed.

(* Self-application forces the leaf at the end of the left spine of
   the function domain to be free in that domain. *)
Local Fixpoint left_depth (A : poly_type) : nat :=
  match A with
  | poly_var _ => 0
  | poly_arr B _ => S (left_depth B)
  | poly_abs B => left_depth B
  end.

Local Fixpoint left_free (A : poly_type) : option nat :=
  match A with
  | poly_var n => Some n
  | poly_arr B _ => left_free B
  | poly_abs B =>
      match left_free B with Some (S n) => Some n | _ => None end
  end.

Local Lemma left_depth_quantify k A : left_depth (quantify k A) = left_depth A.
Proof. induction k; cbn; auto. Qed.

Local Lemma left_depth_ren r A :
  left_depth (ren_poly_type r A) = left_depth A.
Proof. revert r. induction A; intros r; cbn; congruence. Qed.

Local Lemma left_depth_sub f A :
  left_depth A <= left_depth (subst_poly_type f A).
Proof.
  revert f. induction A; intros f; cbn.
  - lia.
  - specialize (IHA1 f). lia.
  - apply IHA.
Qed.

Local Lemma left_depth_sub_free f A n :
  left_free A = Some n ->
  left_depth (subst_poly_type f A) = left_depth A + left_depth (f n).
Proof.
  revert f n. induction A; intros f m E; cbn in *.
  - now injection E as E; subst.
  - now rewrite (IHA1 f m E).
  - destruct (left_free A) as [[|n]|] eqn:H; try discriminate.
    injection E as E. subst m.
    change (left_depth (subst_poly_type (up_sub f) A) = left_depth A + left_depth (f n)).
    rewrite (IHA (up_sub f) (S n)) by reflexivity.
    change (left_depth A + left_depth (ren_poly_type S (f n)) = left_depth A + left_depth (f n)).
    now rewrite left_depth_ren.
Qed.

Local Lemma left_depth_sub_bound f A :
  left_free A = None ->
  left_depth (subst_poly_type f A) = left_depth A.
Proof.
  revert f. induction A; intros f E; cbn in *.
  - discriminate.
  - now rewrite IHA1.
  - destruct (left_free A) as [[|n]|] eqn:H; try discriminate.
    all: change (left_depth (subst_poly_type (up_sub f) A) = left_depth A).
    + rewrite (left_depth_sub_free (up_sub f) A 0 H). cbn.
      apply Nat.add_0_r.
    + apply IHA. reflexivity.
Qed.

Local Lemma specialize_left_depth args A B :
  specialize_type args A = Some B -> left_depth A <= left_depth B.
Proof.
  revert A. induction args as [|X args IH]; intros A E.
  - cbn in E. now injection E as E; subst.
  - destruct A as [n|L R|A]; try discriminate.
    cbn in E. specialize (IH _ E). cbn.
    pose proof (left_depth_sub (scons X poly_var) A). lia.
Qed.

Local Lemma self_application_left_free G k A B C :
  type_assignment
    (quantify k (poly_arr A B) :: G) (pure_app (pure_var 0) (pure_var 0)) C ->
  exists n, left_free A = Some n.
Proof.
  intros H.
  destruct (app_inv _ _ _ _ H) as (P & Q & HP & HQ).
  assert (E : forall T, specialize_type [] (subst_poly_type poly_var T) = Some T)
    by (intros T; now rewrite sub_vars).
  destruct (var_arrow_specialization _ _ _ HP poly_var [] P Q (E _))
    as (F & args & Look & S).
  cbn in Look. inversion Look; subst F. rewrite sub_vars in S.
  pose proof (specialize_arrow_length _ _ _ _ _ _ S) as L.
  destruct (specialize_quantify _ _ _ _ L S) as [f K].
  change (poly_arr (subst_poly_type f A) (subst_poly_type f B) = poly_arr P Q) in K.
  injection K as K _. subst P.
  set (T := subst_poly_type f A) in *.
  pose proof (head_decompose T) as D.
  rewrite D in HQ. apply typing_open_prefix in HQ.
  destruct (var_specialization _ _ _ HQ poly_var [] (head_body T)
    (head_body_nonabs T) (E _)) as (F & bs & Look2 & S').
  cbn in Look2. inversion Look2; subst F. rewrite sub_vars in S'.
  apply specialize_left_depth in S'. rewrite left_depth_ren, left_depth_quantify in S'.
  assert (DT : left_depth (head_body T) = left_depth T).
  { rewrite D at 2. symmetry. apply left_depth_quantify. }
  rewrite DT in S'. cbn in S'.
  destruct (left_free A) eqn:Free; eauto.
  unfold T in S'. rewrite left_depth_sub_bound in S' by exact Free. lia.
Qed.

(* Paths count arrow edges and pass through universal binders. *)
Local Fixpoint free_at (A : poly_type) (p : list bool) : option nat :=
  match A with
  | poly_var n => match p with [] => Some n | _ => None end
  | poly_arr L R =>
      match p with
      | false :: q => free_at L q
      | true :: q => free_at R q
      | [] => None
      end
  | poly_abs B =>
      match free_at B p with Some (S n) => Some n | _ => None end
  end.

Local Lemma free_at_ren A r p :
  free_at (ren_poly_type r A) p = option_map r (free_at A p).
Proof.
  revert r p. induction A; intros r p; cbn.
  - now destruct p.
  - destruct p as [|[] p]; cbn; auto.
  - rewrite IHA. destruct (free_at A p) as [[|n]|]; reflexivity.
Qed.

Local Lemma free_at_sub A f p z :
  free_at (subst_poly_type f A) p = Some z <->
  exists q r n, p = q ++ r /\ free_at A q = Some n /\ free_at (f n) r = Some z.
Proof.
  revert f p z. induction A; intros f p z; split.
  - cbn. intro E. exists [], p, n. auto.
  - intros (q & r & m & E & H & K). destruct q; cbn in H; try discriminate.
    injection H as H. subst m p. exact K.
  - destruct p as [|b p]; cbn; try discriminate.
    destruct b; [intro E; apply IHA2 in E|intro E; apply IHA1 in E];
      destruct E as (q & r & n & E & H & K); subst p;
      [exists (true :: q), r, n|exists (false :: q), r, n]; auto.
  - intros (q & r & n & E & H & K).
    destruct q as [|b q]; cbn in H; try discriminate.
    subst p. destruct b; cbn;
      [apply IHA2|apply IHA1]; exists q, r, n; auto.
  - cbn. intro E.
    destruct (free_at (subst_poly_type
      (scons (poly_var 0) (funcomp (ren_poly_type S) f)) A) p)
      as [[|m]|] eqn:H; try discriminate.
    injection E as E. subst m.
    apply IHA in H. destruct H as (q & r & n & E & H & K).
    destruct n as [|n].
    + change (free_at (poly_var 0) r = Some (S z)) in K.
      now destruct r.
    + change (free_at (ren_poly_type S (f n)) r = Some (S z)) in K.
      rewrite free_at_ren in K. destruct (free_at (f n) r) as [v|] eqn:F;
        try discriminate. injection K as K. subst v.
      exists q, r, n. split; [exact E|]. split; [cbn; now rewrite H|exact F].
  - intros (q & r & n & E & H & K).
    cbn in H. destruct (free_at A q) as [[|v]|] eqn:F; try discriminate.
    injection H as H. subst v.
    assert (J : free_at (subst_poly_type (up_sub f) A) p = Some (S z)).
    { apply IHA. exists q, r, (S n). repeat split; try assumption.
      change (free_at (ren_poly_type S (f n)) r = Some (S z)).
      now rewrite free_at_ren, K. }
    cbn. change ((match free_at (subst_poly_type (up_sub f) A) p with
                  | Some (S x) => Some x | _ => None end) = Some z).
    now rewrite J.
Qed.

Local Lemma small_free_lift k f A p i :
  i < k ->
  (free_at (subst_poly_type (lift_substitution k f) A) p = Some i <->
   free_at A p = Some i).
Proof.
  intros Hi. rewrite free_at_sub. split.
  - intros (q & r & n & E & H & K). rewrite lift_substitution_index in K.
    destruct (n <? k) eqn:F.
    + destruct r; cbn in K; try discriminate.
      injection K as K. subst n. now rewrite app_nil_r in E; subst p.
    + rewrite free_at_ren in K.
      destruct (free_at (f (n-k)) r); cbn in K; try discriminate.
      injection K as K. lia.
  - intros H. exists p, [], i. rewrite app_nil_r, lift_substitution_index.
    assert (E : (i <? k) = true) by now apply Nat.ltb_lt.
    rewrite E. auto.
Qed.

Local Lemma left_free_quantify k A n :
  left_free (quantify k A) = Some n <-> left_free A = Some (k + n).
Proof.
  revert n. induction k as [|k IH]; intro n; [reflexivity|].
  cbn. replace (S (k + n)) with (k + S n) by lia.
  rewrite <- (IH (S n)). destruct (left_free (quantify k A)) as [[|v]|];
    split; intro H; try discriminate; congruence.
Qed.

Local Lemma quantify_arrow_inj k l A B C D :
  quantify k (poly_arr A B) = quantify l (poly_arr C D) ->
  k = l /\ A = C /\ B = D.
Proof.
  revert l. induction k as [|k IH]; intros [|l] E; cbn in E; try discriminate.
  - now inversion E.
  - injection E as E. apply IH in E. destruct E as [-> [-> ->]]. auto.
Qed.

Local Lemma left_zero_free A p n :
  left_depth A = 0 ->
  free_at A p = Some n ->
  p = [] /\ left_free A = Some n.
Proof.
  revert p n. induction A; intros p m H E; cbn in *.
  - destruct p; try discriminate. auto.
  - discriminate.
  - destruct (free_at A p) as [[|n]|] eqn:F; try discriminate.
    injection E as E. subst n. destruct (IHA p (S m) H F) as [-> K].
    now rewrite K.
Qed.

Local Lemma no_captured_leaf_in_domain k L R f g i p :
  subst_poly_type f L = subst_poly_type g (quantify k (poly_arr L R)) ->
  (exists n, left_free (quantify k (poly_arr L R)) = Some n) ->
  i < k ->
  free_at L p <> Some i.
Proof.
  remember (left_depth L) as d eqn:D.
  revert k L R f g i p D.
  induction d as [d IH] using lt_wf_ind.
  intros k L R f g i p D E (n & H) Hi F.
  apply left_free_quantify in H. cbn in H.
  destruct d as [|d].
  - apply left_zero_free in F; [|now symmetry]. destruct F as [_ F].
    rewrite H in F. injection F as F. lia.
  - pose proof (head_decompose L) as Split.
    destruct (head_body L) as [j|L' R'|U] eqn:C.
    + rewrite Split, left_depth_quantify in D. discriminate.
    + assert (K : exists l,
          head_quantifiers L = l /\ L = quantify l (poly_arr L' R')).
      { exists (head_quantifiers L). auto. }
      destruct K as (l & El & Shape).
      rewrite Shape in E. rewrite !sub_quantify in E. cbn [subst_poly_type] in E.
      apply quantify_arrow_inj in E. destruct E as [Eq [E1 E2]]. subst l.
      rewrite Shape in D. rewrite left_depth_quantify in D. cbn [left_depth] in D.
      assert (V : free_at (poly_arr L R) (false :: p) = Some i) by exact F.
      apply (small_free_lift k g _ _ _ Hi) in V.
      assert (E3 : subst_poly_type (lift_substitution k f) (poly_arr L' R') =
                   subst_poly_type (lift_substitution k g) (poly_arr L R)).
      { cbn. rewrite E1, E2. now rewrite <- Shape. }
      rewrite <- E3 in V. apply (proj1 (small_free_lift k f (poly_arr L' R') (false :: p) i Hi)) in V.
      cbn in V.
      assert (Free : exists m, left_free (quantify k (poly_arr L' R')) = Some m).
      { exists (k + n). now rewrite <- Shape. }
      exact (IH (left_depth L') ltac:(lia) k L' R'
        (lift_substitution k f) (lift_substitution k g) i p eq_refl E1 Free Hi V).
    + exfalso. eapply head_body_nonabs. exact C.
Qed.

Local Lemma free_at_quantify k A p n :
  free_at (quantify k A) p = Some n <-> free_at A p = Some (k + n).
Proof.
  revert n. induction k as [|k IH]; intro n; [reflexivity|].
  cbn. replace (S (k + n)) with (k + S n) by lia.
  rewrite <- (IH (S n)). destruct (free_at (quantify k A) p) as [[|v]|];
    split; intro H; try discriminate; congruence.
Qed.

Local Lemma specialize_nonabs_length k args A B T :
  (forall C, T <> poly_abs C) ->
  specialize_type args (quantify k (poly_arr A B)) = Some T ->
  length args = k.
Proof.
  revert args A B. induction k as [|k IH]; intros [|X args] A B H E;
    try discriminate; try reflexivity.
  - cbn [specialize_type quantify] in E. injection E as E.
    exfalso. exact (H _ (eq_sym E)).
  - change (specialize_type args
      (subst_poly_type (scons X poly_var) (quantify k (poly_arr A B))) =
        Some T) in E.
    rewrite sub_quantify in E. cbn [subst_poly_type] in E.
    cbn. f_equal. exact (IH _ _ _ H E).
Qed.

Local Lemma opening_args_ext k f g :
  (forall n, n < k -> f n = g n) ->
  opening_args k f = opening_args k g.
Proof.
  induction k; intros E; cbn; [reflexivity|].
  f_equal; [apply E; lia|]. apply IHk. intros n H. apply E. lia.
Qed.

Local Lemma opening_args_rev args :
  opening_args (length args) (fun n => nth n (rev args) (poly_var 0)) = args.
Proof.
  induction args as [|A args IH]; cbn; [reflexivity|].
  rewrite app_nth2 by (rewrite length_rev; lia).
  rewrite length_rev, Nat.sub_diag. cbn. f_equal.
  rewrite <- IH at 2. apply opening_args_ext. intros n H.
  rewrite app_nth1 by (rewrite length_rev; lia). reflexivity.
Qed.

Local Lemma specialize_prefix_inv k args A B :
  length args = k ->
  specialize_type args (quantify k A) = Some B ->
  exists f, subst_poly_type (prefix_substitution k f) A = B.
Proof.
  intros <- E. rewrite <- (opening_args_rev args) in E at 1.
  rewrite specialize_prefix in E. injection E as E. eauto.
Qed.

Local Lemma ren_as_sub r A :
  ren_poly_type r A = subst_poly_type (fun n => poly_var (r n)) A.
Proof.
  rewrite <- (sub_vars (ren_poly_type r A)), sub_ren. reflexivity.
Qed.

Local Lemma var_instance G A T :
  type_assignment (A :: G) (pure_var 0) T ->
  (forall C, T <> poly_abs C) ->
  exists args, specialize_type args A = Some T.
Proof.
  intros H N.
  assert (E : specialize_type [] (subst_poly_type poly_var T) = Some T)
    by now rewrite sub_vars.
  destruct (var_specialization _ _ _ H _ _ _ N E) as (F & args & L & K).
  cbn in L. inversion L; subst F. rewrite sub_vars in K. eauto.
Qed.

(* For an identity-shaped scheme that admits self-application, the
   leading quantifiers of its domain are vacuous. Matching the domains
   rules out bound occurrences to the left. A bound occurrence to the
   right would require a strictly shorter such occurrence. *)
Local Lemma self_identity_vacuous G G0 k A B C :
  type_assignment (A :: G) (pure_var 0) B ->
  type_assignment (quantify k (poly_arr A B) :: G0)
    (pure_app (pure_var 0) (pure_var 0)) C ->
  forall p i, i < head_quantifiers A -> free_at (head_body A) p <> Some i.
Proof.
  intros HB HH.
  destruct (self_application_left_free _ _ _ _ _ HH) as [n Lf].
  pose proof (head_decompose A) as D.
  revert HB HH D Lf.
  generalize (head_quantifiers A) as l.
  destruct (head_body A) as [m|L R|T] eqn:Body.
  - intros l HB HH D Lf p i H E. rewrite D in Lf.
    apply left_free_quantify in Lf. cbn in Lf. destruct p; cbn in E; try discriminate.
    injection Lf as Lf. injection E as E. lia.
  - intros l HB HH D Lf.
    destruct (app_inv _ _ _ _ HH) as (P & Q & HP & HQ).
    destruct (var_instance _ _ _ HP ltac:(intros ? E; discriminate E))
      as (args & S).
    pose proof (specialize_arrow_length _ _ _ _ _ _ S) as Len.
    destruct (specialize_quantify _ _ _ _ Len S) as [f E].
    change (poly_arr (subst_poly_type f A) (subst_poly_type f B) =
      poly_arr P Q) in E. injection E as E _. subst P.
    rewrite D, sub_quantify in HQ. apply typing_open_prefix in HQ.
    cbn [subst_poly_type map] in HQ.
    destruct (var_instance _ _ _ HQ ltac:(intros ? E; discriminate E))
      as (args2 & S2).
    rewrite ren_as_sub, sub_quantify in S2. cbn [subst_poly_type] in S2.
    pose proof (specialize_arrow_length _ _ _ _ _ _ S2) as Len2.
    destruct (specialize_quantify _ _ _ _ Len2 S2) as [g E2].
    cbn [subst_poly_type] in E2. rewrite !sub_sub in E2.
    set (rho := funcomp (subst_poly_type g)
      (lift_substitution k (fun n => poly_var (l + n)))) in *.
    (* The renaming in the context and the subsequent specializations
       act on the same two components of the function type. *)
    rewrite <- D in E2.
    injection E2 as ED EC.
    assert (NoLeft : forall p i, i < l -> free_at L p <> Some i).
    { intros p i I. eapply no_captured_leaf_in_domain with (f := lift_substitution l f)
        (g := rho).
      - symmetry. now rewrite <- D.
      - exists n. now rewrite <- D.
      - exact I. }
    assert (NoSmall : forall p i, i < l -> free_at (subst_poly_type rho A) p <> Some i).
    { intros p i I U. rewrite ED in U.
      apply (proj1 (small_free_lift l f L p i I)) in U.
      exact (NoLeft p i I U). }
    assert (NoRight : forall m p i, length p = m -> i < l -> free_at R p <> Some i).
    { induction m as [m IH] using lt_wf_ind.
      intros p i Size I U.
      pose proof (proj2 (small_free_lift l f R p i I) U) as V. rewrite <- EC in V.
      set (T := subst_poly_type rho B) in *.
      set (h := head_quantifiers T) in *.
      pose proof (head_decompose T) as Shape. fold h in Shape.
      assert (W : free_at (head_body T) p = Some (h + i)).
      { apply free_at_quantify. now rewrite <- Shape. }
      pose proof (typing_sub _ _ _ HB rho) as H.
      change (type_assignment (subst_poly_type rho A :: map (subst_poly_type rho) G)
        (pure_var 0) T) in H.
      rewrite Shape in H. apply typing_open_prefix in H. cbn [map] in H.
      destruct (var_instance _ _ _ H (head_body_nonabs T)) as [a Use].
      rewrite ren_as_sub, sub_sub, D, sub_quantify in Use.
      cbn [subst_poly_type] in Use.
      pose proof (specialize_nonabs_length _ _ _ _ _ (head_body_nonabs T) Use) as Len3.
      destruct (specialize_prefix_inv _ _ _ _ Len3 Use) as [u UU].
      rewrite <- UU in W. apply (proj1 (free_at_sub _ _ _ _)) in W.
      destruct W as (q & r & j & Pth & Occ & Value).
      unfold prefix_substitution in Value. destruct (j <? l) eqn:J.
      - apply Nat.ltb_lt in J.
        apply (proj1 (small_free_lift l _ (poly_arr L R) q j J)) in Occ.
        destruct q as [|b q]; cbn in Occ; try discriminate.
        destruct b.
        + apply (IH (length q) ltac:(rewrite Pth, length_app in Size; cbn in Size; lia)
            q j eq_refl J Occ).
        + exact (NoLeft q j J Occ).
      - destruct r; cbn in Value; try discriminate.
        injection Value as Value.
        assert (Hbad : free_at (ren_poly_type (Nat.add h) (subst_poly_type rho A)) q =
          Some (h + i)).
        { rewrite ren_as_sub, sub_sub, D, sub_quantify.
          apply free_at_quantify. apply Nat.ltb_ge in J.
          replace (l + (h + i)) with j by lia. exact Occ. }
        rewrite free_at_ren in Hbad.
        destruct (free_at (subst_poly_type rho A) q) as [j'|] eqn:J';
          cbn in Hbad; try discriminate.
        injection Hbad as Hbad. assert (j' = i) by lia. subst j'.
        exact (NoSmall q i I J'). }
    intros [|b p] i Hi Bad; cbn in Bad; try discriminate.
    destruct b; [exact (NoRight _ _ _ eq_refl Hi Bad)|exact (NoLeft _ _ Hi Bad)].
  - intros. exfalso. eapply head_body_nonabs. exact Body.
Qed.

Local Definition bottom := poly_abs (poly_var 0).

Local Definition close_head A :=
  subst_poly_type (prefix_substitution (head_quantifiers A) (fun _ => bottom))
    (head_body A).

Local Lemma prefix_shift k f A :
  subst_poly_type (prefix_substitution k f) (ren_poly_type (Nat.add k) A) = A.
Proof.
  rewrite sub_ren. transitivity (subst_poly_type poly_var A); [|apply sub_vars].
  apply sub_ext. intros i. unfold funcomp, prefix_substitution.
  assert ((k + i <? k) = false) as E by (apply Nat.ltb_ge; lia).
  rewrite E. f_equal. lia.
Qed.

Local Lemma head_quantifiers_quantify k A :
  head_quantifiers (quantify k A) = k + head_quantifiers A.
Proof. induction k; cbn; congruence. Qed.

Local Lemma head_body_quantify k A : head_body (quantify k A) = head_body A.
Proof. induction k; cbn; auto. Qed.

Local Lemma typing_close_head G M A :
  type_assignment G M A -> type_assignment G M (close_head A).
Proof.
  intros H. pose proof (head_decompose A) as D.
  rewrite D in H. apply typing_open_prefix in H.
  unfold close_head.
  pose proof (typing_sub _ _ _ H
    (prefix_substitution (head_quantifiers A) (fun _ => bottom))) as K.
  rewrite map_map in K.
  assert (E : map (fun x => subst_poly_type
    (prefix_substitution (head_quantifiers A) (fun _ => bottom))
    (ren_poly_type (Nat.add (head_quantifiers A)) x)) G = G).
  { rewrite <- (map_id G) at 2. apply map_ext. apply prefix_shift. }
  now rewrite E in K.
Qed.

Local Lemma typing_close_abs G M A k B C :
  A = quantify k (poly_arr B C) ->
  type_assignment G (pure_abs M) A ->
  type_assignment
    (subst_poly_type (prefix_substitution k (fun _ => bottom)) B :: G) M
    (subst_poly_type (prefix_substitution k (fun _ => bottom)) C).
Proof.
  intros -> H. apply typing_close_head in H.
  unfold close_head in H. rewrite head_quantifiers_quantify, head_body_quantify in H.
  cbn [head_quantifiers head_body] in H. rewrite Nat.add_0_r in H.
  now apply abs_inv in H.
Qed.

Local Lemma subst_free_congr A f g :
  (forall p n, free_at A p = Some n -> f n = g n) ->
  subst_poly_type f A = subst_poly_type g A.
Proof.
  revert f g. induction A; intros f g H; cbn.
  - apply (H [] n). reflexivity.
  - f_equal.
    + apply IHA1. intros p n. apply (H (false :: p)).
    + apply IHA2. intros p n. apply (H (true :: p)).
  - f_equal. apply IHA. intros p [|n] E; [reflexivity|].
    change (ren_poly_type S (f n) = ren_poly_type S (g n)).
    f_equal. apply (H p n). cbn. now rewrite E.
Qed.

Local Lemma close_vacuous k A :
  (forall p n, n < k -> free_at A p <> Some n) ->
  A = ren_poly_type (Nat.add k)
    (subst_poly_type (prefix_substitution k (fun _ => bottom)) A).
Proof.
  intro E. rewrite ren_sub. rewrite <- (sub_vars A) at 1.
  apply subst_free_congr. intros p n Occ.
  unfold funcomp, prefix_substitution. destruct (n <? k) eqn:L.
  - apply Nat.ltb_lt in L. exfalso. exact (E p n L Occ).
  - apply Nat.ltb_ge in L. cbn. f_equal. lia.
Qed.

Local Definition rigid_type A :=
  exists k B C, A = quantify k (ren_poly_type (Nat.add k) (poly_arr B C)).

Local Lemma rigid_close k B C :
  close_head (quantify k (ren_poly_type (Nat.add k) (poly_arr B C))) =
    poly_arr B C.
Proof.
  unfold close_head. rewrite head_quantifiers_quantify, head_body_quantify.
  change (subst_poly_type (prefix_substitution (k + 0) (fun _ => bottom))
    (ren_poly_type (Nat.add k) (poly_arr B C)) = poly_arr B C).
  rewrite Nat.add_0_r. apply prefix_shift.
Qed.

Local Lemma rigid_sub A f : rigid_type A -> rigid_type (subst_poly_type f A).
Proof.
  intros (k & B & C & ->). exists k, (subst_poly_type f B), (subst_poly_type f C).
  rewrite sub_quantify. f_equal.
  change (subst_poly_type (lift_substitution k f)
    (ren_poly_type (Nat.add k) (poly_arr B C)) =
    ren_poly_type (Nat.add k) (subst_poly_type f (poly_arr B C))).
  rewrite sub_ren, ren_sub. apply sub_ext. intros n. unfold funcomp.
  rewrite lift_substitution_index.
  assert ((k + n <? k) = false) as E by (apply Nat.ltb_ge; lia).
  rewrite E. replace (k + n - k) with n by lia. reflexivity.
Qed.

Local Lemma instance_rigid_core G x A T k B C :
  nth_error G x = Some A ->
  A = quantify k (ren_poly_type (Nat.add k) (poly_arr B C)) ->
  type_assignment G (pure_var x) T ->
  (forall Y, T <> poly_abs Y) ->
  T = poly_arr B C.
Proof.
  intros E -> H No.
  assert (S : specialize_type [] (subst_poly_type poly_var T) = Some T)
    by now rewrite sub_vars.
  destruct (var_specialization _ _ _ H _ _ _ No S) as (X & a & L & Q).
  rewrite E in L. injection L as L. subst X. rewrite sub_vars in Q.
  change (specialize_type a
      (quantify k (poly_arr (ren_poly_type (Nat.add k) B)
                             (ren_poly_type (Nat.add k) C))) = Some T) in Q.
  pose proof (specialize_nonabs_length _ _ _ _ _ No Q) as Len.
  destruct (specialize_prefix_inv _ _ _ _ Len Q) as [f F].
  change (subst_poly_type (prefix_substitution k f)
    (ren_poly_type (Nat.add k) (poly_arr B C)) = T) in F.
  now rewrite prefix_shift in F.
Qed.

Local Lemma rigid_var_arrow G x A B C L R k :
  nth_error G x = Some A ->
  A = quantify k (ren_poly_type (Nat.add k) (poly_arr L R)) ->
  type_assignment G (pure_var x) (poly_arr B C) ->
  B = L /\ C = R.
Proof.
  intros E F H. pose proof
    (instance_rigid_core _ _ _ _ _ _ _ E F H ltac:(intros ? Eq; discriminate Eq)) as J.
  now inversion J.
Qed.

Local Lemma quantified_var_instance k n args T :
  specialize_type args (quantify k (poly_var (k + n))) = Some T ->
  (forall C, T <> poly_abs C) -> T = poly_var n.
Proof.
  revert args. induction k as [|k IH]; intros [|D args] E F; try discriminate.
  - now inversion E.
  - cbn [specialize_type quantify] in E. injection E as E.
    exfalso. exact (F _ (eq_sym E)).
  - change (specialize_type args
      (subst_poly_type (scons D poly_var) (quantify k (poly_var (S k + n)))) =
      Some T) in E.
    rewrite sub_quantify in E.
    change (specialize_type args
      (quantify k (lift_substitution k (scons D poly_var) (S k + n))) = Some T) in E.
    rewrite lift_substitution_index in E.
    assert ((S k + n <? k) = false) as J by (apply Nat.ltb_ge; lia).
    rewrite J in E. replace (S k + n - k) with (S n) in E by lia.
    change (specialize_type args (quantify k (poly_var (k + n))) = Some T) in E.
    now apply IH in E.
Qed.

Local Lemma self_identity_rigid G H k A B C :
  type_assignment (A :: G) (pure_var 0) B ->
  (exists N D E, type_assignment (A :: G) (pure_var 0) (poly_arr D E) /\
                 type_assignment (A :: G) N D) ->
  type_assignment (quantify k (poly_arr A B) :: H)
    (pure_app (pure_var 0) (pure_var 0)) C ->
  rigid_type A.
Proof.
  intros HB (N & D & E & HF & HN) HS.
  pose proof (self_identity_vacuous _ _ _ _ _ _ HB HS) as Vac.
  pose proof (head_decompose A) as Shape.
  remember (head_quantifiers A) as l eqn:Eq in *.
  destruct (head_body A) as [v|L R|T] eqn:Body.
  - assert (F : l <= v).
    { destruct (Nat.lt_ge_cases v l) as [K|K]; [|exact K].
      exfalso. exact (Vac [] v K eq_refl). }
    replace v with (l + (v-l)) in Shape by lia.
    destruct (var_instance _ _ _ HF ltac:(intros ? P; discriminate P)) as [args Inst].
    rewrite Shape in Inst.
    pose proof (quantified_var_instance _ _ _ _ Inst ltac:(intros ? P; discriminate P)).
    discriminate.
  - pose proof (close_vacuous l (poly_arr L R) Vac) as V.
    change (poly_arr L R =
      ren_poly_type (Nat.add l) (poly_arr
        (subst_poly_type (prefix_substitution l (fun _ => bottom)) L)
        (subst_poly_type (prefix_substitution l (fun _ => bottom)) R))) in V.
    eexists l, _, _. rewrite <- V. exact Shape.
  - exfalso. exact (head_body_nonabs _ _ Body).
Qed.

Local Fixpoint rename_term (r : nat -> nat) (M : pure_term) :=
  match M with
  | pure_var n => pure_var (r n)
  | pure_app M N => pure_app (rename_term r M) (rename_term r N)
  | pure_abs M => pure_abs (rename_term (up_ren r) M)
  end.

Local Definition lookup_r r (G D : environment) :=
  forall x A, nth_error G x = Some A <-> nth_error D (r x) = Some A.

Local Lemma lookup_r_cons r G D A :
  lookup_r r G D -> lookup_r (up_ren r) (A :: G) (A :: D).
Proof. intros H [|n] B; [reflexivity|apply H]. Qed.

Local Lemma lookup_r_map r G D f :
  lookup_r r G D -> lookup_r r (map f G) (map f D).
Proof.
  intros H x A. rewrite !nth_error_map.
  destruct (nth_error G x) as [B|] eqn:E.
  - apply (proj1 (H x B)) in E. now rewrite E.
  - destruct (nth_error D (r x)) as [B|] eqn:F; [|reflexivity].
    apply (proj2 (H x B)) in F. congruence.
Qed.

Local Lemma rename_term_typing G D M A r :
  lookup_r r G D -> type_assignment G M A ->
  type_assignment D (rename_term r M) A.
Proof.
  intros L H. revert r D L. induction H; intros r D L; cbn.
  - constructor. now apply L.
  - econstructor; eauto.
  - constructor. apply IHtype_assignment. now apply lookup_r_cons.
  - econstructor. eauto.
  - constructor. apply IHtype_assignment. now apply lookup_r_map.
Qed.

Local Lemma rename_term_typing_inv G D M A r :
  lookup_r r G D -> type_assignment D (rename_term r M) A ->
  type_assignment G M A.
Proof.
  intros E H. remember (rename_term r M) as N eqn:Eq.
  revert M r G E Eq.
  induction H; intros P r G E Eq.
  - destruct P; cbn in Eq; try discriminate. injection Eq as Eq. subst x.
    constructor. now apply E.
  - destruct P; cbn in Eq; try discriminate. injection Eq as Eq1 Eq2.
    econstructor; [eapply IHtype_assignment1|eapply IHtype_assignment2]; eauto.
  - destruct P; cbn in Eq; try discriminate. injection Eq as Eq.
    constructor. eapply IHtype_assignment; [now apply lookup_r_cons|exact Eq].
  - econstructor. eauto.
  - constructor. eapply IHtype_assignment; [now apply lookup_r_map|eassumption].
Qed.

Local Lemma typing_weaken G M T A :
  type_assignment G M T <-> type_assignment (A :: G) (rename_term S M) T.
Proof.
  split; intro H.
  - apply (rename_term_typing G); [intros x B; reflexivity|exact H].
  - eapply rename_term_typing_inv; [|exact H]. intros x B. reflexivity.
Qed.

Local Definition pkg_let (M N : pure_term) := pure_app (pure_abs N) M.
Local Definition pkg_seq (M N : pure_term) := pkg_let M (rename_term S N).
Local Definition typable_in G M := exists A, type_assignment G M A.

Local Lemma typing_seq_inv G M N T :
  type_assignment G (pkg_seq M N) T ->
  type_assignment G N T.
Proof.
  intros H. remember (pkg_seq M N) as P eqn:E.
  induction H.
  - discriminate.
  - unfold pkg_seq, pkg_let in E. inversion E; subst.
    apply abs_inv in H. now apply typing_weaken in H.
  - discriminate.
  - econstructor. now apply IHtype_assignment.
  - constructor. now apply IHtype_assignment.
Qed.

Local Lemma typable_seq G M N :
  typable_in G (pkg_seq M N) <-> typable_in G M /\ typable_in G N.
Proof.
  split.
  - intros [T H]. split.
    + destruct (app_inv _ _ _ _ H) as (A & B & K & L). now exists A.
    + exists T. now apply typing_seq_inv in H.
  - intros [[A H] [T K]]. exists T. unfold pkg_seq, pkg_let.
    eapply type_assignment_app; [apply type_assignment_abs|exact H].
    now apply typing_weaken.
Qed.

Local Lemma typing_seq G M N T :
  typable_in G M -> type_assignment G N T -> type_assignment G (pkg_seq M N) T.
Proof.
  intros [A H] K. unfold pkg_seq, pkg_let. eapply type_assignment_app;
    [apply type_assignment_abs; now apply typing_weaken|exact H].
Qed.

Local Lemma typable_let G M N :
  typable_in G (pkg_let M N) <->
  exists A, type_assignment G M A /\ typable_in (A :: G) N.
Proof.
  split.
  - intros [T H]. destruct (app_inv _ _ _ _ H) as (A & B & K & L).
    exists A. split; [exact L|]. exists B. now apply abs_inv.
  - intros (A & H & B & K). exists B. exact (type_assignment_app (type_assignment_abs K) H).
Qed.

Local Lemma lambda_not_var G M T :
  type_assignment G (pure_abs M) T ->
  forall f args n, specialize_type args (subst_poly_type f T) =
    Some (poly_var n) -> False.
Proof.
  intros H. remember (pure_abs M) as P eqn:E.
  induction H; intros f args n Eq; inversion E; subst.
  - destruct args; discriminate.
  - apply (IHtype_assignment eq_refl f (subst_poly_type f t :: args) n).
    cbn. now rewrite <- sub_inst.
  - destruct args as [|X args]; [discriminate|].
    change (specialize_type args
      (subst_poly_type (scons X poly_var) (subst_poly_type (up_sub f) s))
      = Some (poly_var n)) in Eq.
    rewrite sub_open in Eq.
    exact (IHtype_assignment eq_refl (scons X f) args n Eq).
Qed.

Local Lemma lambda_shape G M T :
  type_assignment G (pure_abs M) T ->
  exists k A B, T = quantify k (poly_arr A B).
Proof.
  intro H. pose proof (head_decompose T) as D.
  rewrite D in H. apply typing_open_prefix in H.
  destruct (head_body T) as [n|A B|A] eqn:E.
  - exfalso. exact (lambda_not_var _ _ _ H poly_var [] n eq_refl).
  - eauto.
  - exfalso. exact (head_body_nonabs _ _ E).
Qed.

Local Definition ref_term (arg : pure_term) :=
  pure_abs (pkg_seq (pure_app (pure_var 0) (rename_term S arg)) (pure_var 0)).

Local Definition reference_type F :=
  exists k A B, F = quantify k (poly_arr A B) /\ rigid_type A.

Local Lemma ref_term_type G D arg F :
  type_assignment G (ref_term arg) F ->
  typable_in (F :: D) (pure_app (pure_var 0) (pure_var 0)) ->
  reference_type F.
Proof.
  intros H [T K].
  destruct (lambda_shape _ _ _ H) as (k & A & B & ->).
  apply typing_open_prefix in H. apply abs_inv in H.
  exists k, A, B. split; [reflexivity|].
  eapply self_identity_rigid; [| |exact K].
  - exact (typing_seq_inv _ _ _ _ H).
  - assert (C : typable_in (A :: map (ren_poly_type (Nat.add k)) G)
    (pkg_seq (pure_app (pure_var 0) (rename_term S arg)) (pure_var 0))) by (eexists; exact H).
    apply typable_seq in C. destruct C as [[R J] _].
    destruct (app_inv _ _ _ _ J) as (L & U & C1 & C2). eauto.
Qed.

Local Lemma reference_sub F f :
  reference_type F -> reference_type (subst_poly_type f F).
Proof.
  intros (k & A & B & -> & H).
  exists k, (subst_poly_type (lift_substitution k f) A),
    (subst_poly_type (lift_substitution k f) B).
  split; [apply sub_quantify|now apply rigid_sub].
Qed.

Local Lemma reference_instance G x F T :
  nth_error G x = Some F ->
  reference_type F ->
  type_assignment G (pure_var x) T ->
  reference_type T.
Proof.
  intros Look (k & A & B & -> & HR) HT.
  pose proof (head_decompose T) as Shape.
  rewrite Shape in HT. apply typing_open_prefix in HT.
  assert (E : specialize_type [] (subst_poly_type poly_var (head_body T)) =
    Some (head_body T)) by now rewrite sub_vars.
  destruct (var_specialization _ _ _ HT _ _ _ (head_body_nonabs T) E)
    as (S & args & K & U).
  rewrite nth_error_map, Look in K. cbn in K. injection K as K. subst S.
  rewrite sub_vars, ren_as_sub, sub_quantify in U. cbn [subst_poly_type] in U.
  pose proof (specialize_nonabs_length _ _ _ _ _ (head_body_nonabs T) U) as Len.
  destruct (specialize_quantify _ _ _ _ Len U) as [f J].
  cbn [subst_poly_type] in J. rewrite !sub_sub in J.
  set (r := funcomp (subst_poly_type f)
    (lift_substitution k (fun n => poly_var (head_quantifiers T + n)))) in *.
  exists (head_quantifiers T), (subst_poly_type r A), (subst_poly_type r B).
  split; [now rewrite J|now apply rigid_sub].
Qed.

Local Lemma typing_quantify G M k A :
  type_assignment (map (ren_poly_type (Nat.add k)) G) M A ->
  type_assignment G M (quantify k A).
Proof.
  revert G. induction k as [|k IH]; intros G H.
  - cbn in *. rewrite (map_ext _ _ ren_id), map_id in H. exact H.
  - cbn [quantify]. apply type_assignment_gen. apply IH.
    rewrite map_map.
    replace (map (fun x => ren_poly_type (Nat.add k) (ren_poly_type S x)) G) with
      (map (ren_poly_type (Nat.add (S k))) G); [exact H|].
    apply map_ext. intros B. rewrite ren_ren. apply ren_ext.
    intro n. unfold funcomp. lia.
Qed.

Local Lemma cancel_context k f G :
  map (subst_poly_type (prefix_substitution k f))
    (map (ren_poly_type (Nat.add k)) G) = G.
Proof.
  rewrite map_map. rewrite <- (map_id G) at 2.
  apply map_ext. apply prefix_shift.
Qed.

Local Lemma typing_var_at G x k A B f :
  nth_error G x = Some (quantify k (poly_arr A B)) ->
  type_assignment G (pure_var x)
    (poly_arr (subst_poly_type (prefix_substitution k f) A)
              (subst_poly_type (prefix_substitution k f) B)).
Proof.
  intros H. eapply typing_specialize with (args := opening_args k f).
  - apply type_assignment_var. exact H.
  - rewrite specialize_prefix. reflexivity.
Qed.

Local Definition av := pure_var.
Local Definition ab := pure_abs.
Local Definition ap := pure_app.
Local Definition wk := rename_term S.
Local Definition tyarr := poly_arr.
Local Definition tv := poly_var.

Local Definition compare_body M N :=
  pkg_seq (ap (av 0) (ab (ab (wk (wk (wk M))))))
    (pkg_seq (ap (av 0) (ab (ab (wk (wk (wk N)))))) (av 0)).

Local Definition compare_terms M N :=
  pkg_let (ab (compare_body M N)) (ap (av 0) (av 0)).

Local Lemma compare_core G M N A B :
  rigid_type A ->
  type_assignment (A :: G) (compare_body M N) B ->
  exists T, type_assignment G M T /\ type_assignment G N T.
Proof.
  intros (k & X & Y & ->) H.
  assert (J : forall P,
    typable_in (quantify k (ren_poly_type (Nat.add k) (tyarr X Y)) :: G)
      (ap (av 0) (ab (ab (wk (wk (wk P)))))) ->
    type_assignment (quantify k (ren_poly_type (Nat.add k) (tyarr X Y)) :: G)
      (ab (ab (wk (wk (wk P))))) X).
  { intros P [U K]. destruct (app_inv _ _ _ _ K) as (L & R & L1 & L2).
    destruct (rigid_var_arrow (quantify k (ren_poly_type (Nat.add k) (tyarr X Y)) :: G)
      0 _ L R X Y k eq_refl eq_refl L1) as [-> _].
    exact L2. }
  assert (K : typable_in _ (compare_body M N)) by (exists B; exact H).
  unfold compare_body in K. apply typable_seq in K.
  destruct K as [H1 K]. apply typable_seq in K. destruct K as [H2 _].
  apply J in H1. apply J in H2.
  destruct (lambda_shape _ _ _ H1) as (i & D & E & Shape).
  apply (typing_close_abs _ _ _ _ _ _ Shape) in H1, H2.
  destruct (lambda_shape _ _ _ H1) as (j & F & T & Shape2).
  apply (typing_close_abs _ _ _ _ _ _ Shape2) in H1, H2.
  exists (subst_poly_type (prefix_substitution j (fun _ => bottom)) T).
  split.
  - do 3 (apply typing_weaken in H1). exact H1.
  - do 3 (apply typing_weaken in H2). exact H2.
Qed.

(* The let-bound identity returns its parameter after two discarded
   calls. Self-application makes this parameter rigid, so both calls
   check their padded arguments at the same domain. *)
Local Lemma comparison_sound G M N :
  typable_in G (compare_terms M N) ->
  exists T, type_assignment G M T /\ type_assignment G N T.
Proof.
  unfold compare_terms. intros K. apply typable_let in K. destruct K as (F & K & C & L).
  destruct (lambda_shape _ _ _ K) as (k & A & B & ->).
  apply typing_open_prefix in K. apply abs_inv in K.
  assert (R : rigid_type A).
  { eapply self_identity_rigid; [| |exact L].
    - pose proof (typing_seq_inv _ _ _ _ K) as J. exact (typing_seq_inv _ _ _ _ J).
    - assert (H : typable_in _ (compare_body M N)) by (exists B; exact K).
      unfold compare_body in H. apply typable_seq in H.
      destruct H as [[S H] _]. destruct (app_inv _ _ _ _ H) as (D & E & U & V).
      eauto. }
  destruct (compare_core _ _ _ _ _ R K) as (T & H1 & H2).
  set (f := prefix_substitution k (fun _ => bottom)).
  exists (subst_poly_type f T). split;
    [pose proof (typing_sub _ _ _ H1 f) as H|pose proof (typing_sub _ _ _ H2 f) as H];
    unfold f in H; now rewrite cancel_context in H.
Qed.

Local Definition comparison_frame T :=
  tyarr (tyarr (tv 0) (tyarr (tv 1) (ren_poly_type (Nat.add 4) T)))
        (tyarr (tv 2) (tv 3)).

Local Lemma comparison_frame_sub T f :
  subst_poly_type (prefix_substitution 4 f) (comparison_frame T) =
    tyarr (tyarr (f 0) (tyarr (f 1) T)) (tyarr (f 2) (f 3)).
Proof.
  unfold comparison_frame, tyarr, tv. cbn [subst_poly_type].
  rewrite prefix_shift. reflexivity.
Qed.

Local Lemma comparison_complete G M N T :
  type_assignment G M T -> type_assignment G N T ->
  typable_in G (compare_terms M N).
Proof.
  intros HM HN. unfold compare_terms. apply typable_let.
  set (A := comparison_frame T).
  exists (quantify 4 (tyarr A A)). split.
  - apply typing_quantify. apply type_assignment_abs.
    unfold compare_body.
    assert (J : forall P, type_assignment G P T ->
      typable_in (A :: map (ren_poly_type (Nat.add 4)) G)
      (ap (av 0) (ab (ab (wk (wk (wk P))))))).
    { intros P HP. pose proof (typing_ren _ _ _ HP (Nat.add 4)) as Q.
      exists (tyarr (tv 2) (tv 3)).
      eapply type_assignment_app.
      - apply type_assignment_var. reflexivity.
      - apply type_assignment_abs, type_assignment_abs.
        do 3 apply typing_weaken. exact Q. }
    apply typing_seq; [apply J; exact HM|].
    apply typing_seq; [apply J; exact HN|]. apply type_assignment_var. reflexivity.
  - set (D := tyarr (tv 0) (tyarr (tv 0) T)).
    set (E := tyarr (tv 0) T).
    set (P := tyarr D E).
    exists (tyarr P P).
    unfold ap, av. eapply (@type_assignment_app _ _ _ (tyarr P P) (tyarr P P)).
    + pose proof (typing_var_at (quantify 4 (tyarr A A) :: G) 0 4 A A (scons D (scons (tv 0) (scons D (scons E tv)))) eq_refl) as H.
      unfold A in H. rewrite !comparison_frame_sub in H. exact H.
    + pose proof (typing_var_at (quantify 4 (tyarr A A) :: G) 0 4 A A (scons (tv 0) (scons (tv 0) (scons (tv 0) (scons T tv)))) eq_refl) as H.
      unfold A in H. rewrite !comparison_frame_sub in H. exact H.
Qed.

Local Definition rigid_arrow T A B :=
  exists k, T = quantify k (ren_poly_type (Nat.add k) (tyarr A B)).

Local Lemma rigid_arrow_direct A B : rigid_arrow (tyarr A B) A B.
Proof. exists 0. cbn [Nat.add quantify tyarr]. now rewrite ren_id. Qed.

Local Lemma rigid_arrow_sub T A B f :
  rigid_arrow T A B ->
  rigid_arrow (subst_poly_type f T) (subst_poly_type f A) (subst_poly_type f B).
Proof.
  intros [k ->]. exists k. rewrite sub_quantify. f_equal.
  change (subst_poly_type (lift_substitution k f) (ren_poly_type (Nat.add k) (poly_arr A B)) =
    ren_poly_type (Nat.add k) (subst_poly_type f (poly_arr A B))).
  rewrite sub_ren, ren_sub. apply sub_ext. intro n. unfold funcomp.
  rewrite lift_substitution_index.
  assert ((k + n <? k) = false) as E by (apply Nat.ltb_ge; lia).
  rewrite E. replace (k + n - k) with n by lia. reflexivity.
Qed.

Local Lemma rigid_arrow_ren T A B r :
  rigid_arrow T A B ->
  rigid_arrow (ren_poly_type r T) (ren_poly_type r A) (ren_poly_type r B).
Proof. intros H. rewrite !ren_as_sub. now apply rigid_arrow_sub. Qed.

Local Lemma rigid_arrow_close T A B :
  rigid_arrow T A B -> close_head T = tyarr A B.
Proof. intros [k ->]. apply rigid_close. Qed.

Local Lemma rigid_arrow_typing G x T A B :
  nth_error G x = Some T -> rigid_arrow T A B ->
  type_assignment G (av x) (tyarr A B).
Proof.
  intros E [k ->].
  pose proof (typing_var_at _ _ k (ren_poly_type (Nat.add k) A)
    (ren_poly_type (Nat.add k) B) (fun _ => bottom) E) as H.
  now rewrite !prefix_shift in H.
Qed.

Local Lemma rigid_arrow_instance G x T A B U :
  nth_error G x = Some T -> rigid_arrow T A B ->
  type_assignment G (av x) U -> rigid_arrow U A B.
Proof.
  intros Look Rig HT. pose proof (head_decompose U) as Shape.
  rewrite Shape in HT. apply typing_open_prefix in HT.
  pose proof (rigid_arrow_ren _ _ _ (Nat.add (head_quantifiers U)) Rig) as [k Eq].
  assert (L : nth_error (map (ren_poly_type (Nat.add (head_quantifiers U))) G) x =
                Some (ren_poly_type (Nat.add (head_quantifiers U)) T))
    by now rewrite nth_error_map, Look.
  pose proof (instance_rigid_core _ _ _ _ _ _ _ L Eq HT (head_body_nonabs U)) as E.
  exists (head_quantifiers U). exact (eq_trans Shape (f_equal (quantify (head_quantifiers U)) E)).
Qed.

Local Lemma same_rigid_core G x y T U A B C D :
  nth_error G x = Some T -> nth_error G y = Some U ->
  rigid_arrow T A B -> rigid_arrow U C D ->
  typable_in G (compare_terms (av x) (av y)) ->
  tyarr A B = tyarr C D.
Proof.
  intros L1 L2 R1 R2 H. apply comparison_sound in H. destruct H as (V & H1 & H2).
  pose proof (rigid_arrow_instance _ _ _ _ _ _ L1 R1 H1) as V1.
  pose proof (rigid_arrow_instance _ _ _ _ _ _ L2 R2 H2) as V2.
  now rewrite <- (rigid_arrow_close _ _ _ V1), (rigid_arrow_close _ _ _ V2).
Qed.

Local Definition field_test (x : nat) (right : bool) (M : pure_term) :=
  if right then compare_terms (av x) (ab (wk M)) else ap (av x) M.

Local Lemma field_test_typing G x right M T A B :
  nth_error G x = Some T -> rigid_arrow T A B ->
  (typable_in G (field_test x right M) <->
   type_assignment G M (if right then B else A)).
Proof.
  intros L Rig. destruct right; cbn [field_test].
  - split.
    + intro H. apply comparison_sound in H. destruct H as (V & H1 & H2).
      pose proof (rigid_arrow_instance _ _ _ _ _ _ L Rig H1) as R.
      apply typing_close_head in H2. rewrite (rigid_arrow_close _ _ _ R) in H2.
      apply abs_inv in H2. now apply typing_weaken in H2.
    + intro H. eapply comparison_complete.
      * exact (rigid_arrow_typing _ _ _ _ _ L Rig).
      * apply type_assignment_abs. now apply typing_weaken.
  - split.
    + intros [U H]. destruct (app_inv _ _ _ _ H) as (X & Y & K & J).
      destruct Rig as [k Eq].
      destruct (rigid_var_arrow _ _ _ _ _ _ _ _ L Eq K) as [-> _].
      exact J.
    + intro H. exists B. exact (type_assignment_app (rigid_arrow_typing _ _ _ _ _ L Rig) H).
Qed.

(* The reference and the callback share one field type. Opening that
   type exposes a rigid callback parameter. *)
Local Definition extract_field g x right body :=
  pkg_seq (field_test x right (av g))
    (field_test x right (ab (pkg_seq body (av 0)))).

Local Lemma extract_field_sound G g x right body T A B F :
  nth_error G g = Some F -> reference_type F ->
  nth_error G x = Some T -> rigid_arrow T A B ->
  typable_in G (extract_field g x right body) ->
  exists k V W,
    (if right then B else A) = quantify k (tyarr V W) /\
    rigid_type V /\
    typable_in (V :: map (ren_poly_type (Nat.add k)) G) body.
Proof.
  intros Lg Rg Lx Rx H. apply typable_seq in H. destruct H as [H1 H2].
  apply (field_test_typing _ _ _ _ _ _ _ Lx Rx) in H1, H2.
  destruct (reference_instance _ _ _ _ Lg Rg H1) as (k & V & W & E & RV).
  rewrite E in H2. apply typing_open_prefix in H2. apply abs_inv in H2.
  exists k, V, W. repeat split; try assumption.
  assert (Q : typable_in _ (pkg_seq body (av 0))) by (exists W; exact H2).
  apply typable_seq in Q. tauto.
Qed.

Local Lemma extract_field_sound_closed G g x right body T A B F :
  nth_error G g = Some F -> reference_type F ->
  nth_error G x = Some T -> rigid_arrow T A B ->
  typable_in G (extract_field g x right body) ->
  exists k V W X,
    (if right then B else A) = quantify k (tyarr V W) /\
    X = subst_poly_type (prefix_substitution k (fun _ => bottom)) V /\
    rigid_type X /\ typable_in (X :: G) body.
Proof.
  intros Lg Rg Lx Rx H.
  destruct (extract_field_sound _ _ _ _ _ _ _ _ _ Lg Rg Lx Rx H)
    as (k & V & W & E & R & U & H').
  set (f := prefix_substitution k (fun _ => bottom)).
  exists k, V, W, (subst_poly_type f V). repeat split; try assumption.
  - now apply rigid_sub.
  - exists (subst_poly_type f U). pose proof (typing_sub _ _ _ H' f) as K.
    cbn [map] in K. unfold f in K. now rewrite cancel_context in K.
Qed.

Local Definition i_scheme :=
  quantify 2 (tyarr (tyarr (tv 0) (tv 1)) (tyarr (tv 0) (tv 1))).

Local Lemma i_scheme_at G g A B :
  nth_error G g = Some i_scheme ->
  type_assignment G (av g) (tyarr (tyarr A B) (tyarr A B)).
Proof.
  intro L. unfold i_scheme in L.
  exact (typing_var_at _ _ 2 (tyarr (tv 0) (tv 1)) (tyarr (tv 0) (tv 1))
    (scons A (scons B tv)) L).
Qed.

Local Lemma extract_field_complete G g x (right : bool) body T A B L R :
  nth_error G g = Some i_scheme ->
  nth_error G x = Some T -> rigid_arrow T A B ->
  (if right then B else A) = tyarr (tyarr L R) (tyarr L R) ->
  typable_in (tyarr L R :: G) body -> typable_in G (extract_field g x right body).
Proof.
  intros Lg Lx RX E H. apply typable_seq. split;
    apply (field_test_typing _ _ _ _ _ _ _ Lx RX); rewrite E.
  - now apply i_scheme_at.
  - apply type_assignment_abs. apply typing_seq; [exact H|].
    apply type_assignment_var. reflexivity.
Qed.

Local Definition choose_rigid g body :=
  compare_terms (av g) (ab (pkg_seq body (av 0))).

Local Lemma choose_rigid_sound G g F body :
  nth_error G g = Some F -> reference_type F ->
  typable_in G (choose_rigid g body) ->
  exists X, rigid_type X /\ typable_in (X :: G) body.
Proof.
  intros L R H. apply comparison_sound in H. destruct H as (V & H1 & H2).
  destruct (reference_instance _ _ _ _ L R H1) as (k & A & B & Eq & Rig).
  apply (typing_close_abs _ _ _ _ _ _ Eq) in H2.
  exists (subst_poly_type (prefix_substitution k (fun _ => bottom)) A). split.
  - now apply rigid_sub.
  - pose proof (proj1 (typable_seq _ body (av 0)) ltac:(eexists; exact H2)) as [J K]. exact J.
Qed.

Local Lemma choose_rigid_complete G g body A B :
  nth_error G g = Some i_scheme ->
  typable_in (tyarr A B :: G) body -> typable_in G (choose_rigid g body).
Proof.
  intros L H. eapply comparison_complete.
  - now apply i_scheme_at.
  - apply type_assignment_abs, typing_seq; [exact H|]. apply type_assignment_var. reflexivity.
Qed.

Local Lemma application_specialization G M N T :
  type_assignment G (ap M N) T ->
  forall f args R, (forall S, R <> poly_abs S) ->
  specialize_type args (subst_poly_type f T) = Some R ->
  exists A B bs,
    type_assignment (map (subst_poly_type f) G) M (tyarr A B) /\
    type_assignment (map (subst_poly_type f) G) N A /\
    specialize_type bs B = Some R.
Proof.
  intros H. remember (ap M N) as P eqn:E.
  induction H; intros f args R HR Eq; inversion E; subst.
  - exists (subst_poly_type f s), (subst_poly_type f t), args. repeat split.
    + exact (typing_sub _ _ _ H f).
    + exact (typing_sub _ _ _ H0 f).
    + exact Eq.
  - apply (IHtype_assignment eq_refl f (subst_poly_type f t :: args) R HR).
    cbn. now rewrite <- sub_inst.
  - destruct args as [|D args].
    { cbn [specialize_type subst_poly_type] in Eq. injection Eq as Eq.
      exact (False_rect _ (HR _ (eq_sym Eq))). }
    change (specialize_type args
      (subst_poly_type (scons D poly_var) (subst_poly_type (up_sub f) s)) =
      Some R) in Eq.
    rewrite sub_open in Eq.
    destruct (IHtype_assignment eq_refl (scons D f) args R HR Eq)
      as (A & B & bs & K & L & J).
    rewrite map_sub_shift in K, L. eauto 8.
Qed.

Local Lemma application_arrow G M N A B :
  type_assignment G (ap M N) (tyarr A B) ->
  exists D E args,
    type_assignment G M (tyarr D E) /\
    type_assignment G N D /\ specialize_type args E = Some (tyarr A B).
Proof.
  intro H. eapply application_specialization with (f := poly_var) (args := []) in H.
  - rewrite (map_ext _ _ sub_vars), map_id in H. exact H.
  - intros T E. discriminate E.
  - cbn [specialize_type]. now rewrite sub_vars.
Qed.

Local Lemma specialize_sub_arrow k D E f args A B :
  specialize_type args (subst_poly_type f (quantify k (tyarr D E))) =
    Some (tyarr A B) ->
  exists u, A = subst_poly_type u D /\ B = subst_poly_type u E.
Proof.
  rewrite sub_quantify. cbn [tyarr subst_poly_type]. intro H.
  pose proof (specialize_arrow_length _ _ _ _ _ _ H) as Len.
  destruct (specialize_quantify _ _ _ _ Len H) as [g Eq].
  cbn [subst_poly_type] in Eq. rewrite !sub_sub in Eq. inversion Eq. eauto.
Qed.

(* The first two arguments are padding. The third argument carries the
   source type and the record of types for the input subterms. *)
Local Definition payload_scheme k l m D E A B :=
  quantify k (tyarr D (quantify l (tyarr E (quantify m (tyarr A B))))).

Local Lemma third_argument_type G p N N' H k l m D E A B rho X Y :
  H = payload_scheme k l m D E A B ->
  nth_error G p = Some (subst_poly_type rho H) ->
  type_assignment G (ap (ap (av p) N) N') (tyarr X Y) ->
  exists u, X = subst_poly_type u A.
Proof.
  intros -> L C.
  destruct (application_arrow _ _ _ _ _ C) as (P1 & Q1 & a1 & C1 & _ & S1).
  destruct (application_arrow _ _ _ _ _ C1) as (P0 & Q0 & a0 & C0 & _ & S0).
  assert (V : specialize_type [] (subst_poly_type poly_var (tyarr P0 Q0)) =
    Some (tyarr P0 Q0)) by now rewrite sub_vars.
  destruct (var_arrow_specialization _ _ _ C0 _ _ _ _ V) as (T & a & E0 & S).
  rewrite L in E0. injection E0 as E0. subst T. rewrite sub_vars in S.
  unfold payload_scheme in S.
  destruct (specialize_sub_arrow _ _ _ _ _ _ _ S) as (r & _ & Q). subst Q0.
  destruct (specialize_sub_arrow _ _ _ _ _ _ _ S0) as (r' & _ & Q). subst Q1.
  destruct (specialize_sub_arrow _ _ _ _ _ _ _ S1) as (r'' & Eq & _). eauto.
Qed.

Local Definition third_test p d x :=
  ap (ap (ap (av p) (av d)) (av d))
    (ab (pkg_seq (ap (av 0) (av (S x))) (av (S d)))).

Local Lemma third_test_sound G p d x H k l m D E A B R h V W W0 W1 rho :
  H = payload_scheme k l m D E A B ->
  nth_error G p = Some (subst_poly_type rho H) ->
  rigid_arrow A (quantify h (tyarr V W)) R ->
  rigid_arrow V W0 W1 ->
  forall Ty X0 X1,
  nth_error G x = Some Ty -> rigid_arrow Ty X0 X1 ->
  typable_in G (third_test p d x) ->
  exists f, subst_poly_type f (tyarr W0 W1) = tyarr X0 X1.
Proof.
  intros Shape Look RA RV Ty X0 X1 Lx Rx [T Th].
  destruct (app_inv _ _ _ _ Th) as (P & Q & HP & HQ).
  destruct (third_argument_type _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Shape Look HP)
    as [u ->].
  pose proof (rigid_arrow_sub _ _ _ u RA) as R0.
  apply typing_close_head in HQ. rewrite (rigid_arrow_close _ _ _ R0) in HQ.
  apply abs_inv in HQ.
  assert (J : typable_in _ (pkg_seq (ap (av 0) (av (S x))) (av (S d))))
    by (eexists; exact HQ).
  apply typable_seq in J. destruct J as [[Y J] _].
  destruct (app_inv _ _ _ _ J) as (M & N & K & L).
  destruct (var_instance _ _ _ K ltac:(intros ? Eq; discriminate Eq)) as [args Inst].
  destruct (specialize_sub_arrow _ _ _ _ _ _ _ Inst) as [f [EM EN]]. subst M.
  pose proof (rigid_arrow_sub _ _ _ f RV) as V0.
  assert (LX : nth_error (subst_poly_type u (quantify h (tyarr V W)) :: G) (S x) =
    Some Ty) by exact Lx.
  pose proof (rigid_arrow_instance _ _ _ _ _ _ LX Rx L) as V1.
  exists f. exact (eq_trans (eq_sym (rigid_arrow_close _ _ _ V0)) (rigid_arrow_close _ _ _ V1)).
Qed.

Local Definition diag A := tyarr A A.
Local Definition pair_type A B := tyarr (diag A) (diag B).

Local Fixpoint record_type (ts : list poly_type) :=
  match ts with
  | [] => tyarr bottom bottom
  | A :: ts => pair_type A (record_type ts)
  end.

Local Fixpoint record_context ts :=
  match ts with
  | [] => []
  | A :: ts => record_context ts ++ [record_type ts; A]
  end.

Local Fixpoint unpack_record n g r body :=
  match n with
  | 0 => body
  | S n => extract_field g r false
      (extract_field (S g) (S r) true (unpack_record n (S (S g)) 0 body))
  end.

Local Definition slot_index n i := 2 * (n - S i) + 1.

Local Lemma record_context_length ts : length (record_context ts) = 2 * length ts.
Proof. induction ts; cbn; [reflexivity|]. rewrite length_app, IHts. cbn. lia. Qed.

Local Lemma slot_record_context ts G i T :
  nth_error ts i = Some T ->
  nth_error (record_context ts ++ G) (slot_index (length ts) i) = Some T.
Proof.
  revert G i. induction ts as [|A ts IH]; intros G [|i] H; cbn in *; try discriminate.
  - injection H as H. subst T.
    change (nth_error ((record_context ts ++ [record_type ts; A]) ++ G)
      (slot_index (S (length ts)) 0) = Some A).
    replace (slot_index (S (length ts)) 0) with (length (record_context ts) + 1).
    + rewrite <- app_assoc. rewrite nth_error_app2 by lia.
      replace (length (record_context ts) + 1 - length (record_context ts)) with 1 by lia.
      reflexivity.
    + rewrite record_context_length. unfold slot_index. lia.
  - rewrite <- app_assoc. exact (IH ([record_type ts; A] ++ G) i H).
Qed.

Local Lemma unpack_record_sound n G g r body F T :
  nth_error G g = Some F -> reference_type F ->
  nth_error G r = Some T -> rigid_type T ->
  typable_in G (unpack_record n g r body) ->
  exists Delta, length Delta = 2 * n /\ typable_in (Delta ++ G) body /\
    forall i, i < n ->
    exists X, nth_error (Delta ++ G) (slot_index n i) = Some X /\ rigid_type X.
Proof.
  revert G g r F T. induction n as [|n IH]; intros G g r F T Lg Rg Lr Rt H.
  - exists []. cbn in *. repeat split; auto. lia.
  - cbn [unpack_record] in H. destruct Rt as (k & A & B & E).
    assert (Rx : rigid_arrow T A B) by (exists k; exact E).
    destruct (extract_field_sound_closed _ _ _ _ _ _ _ _ _ Lg Rg Lr Rx H)
      as (j & V & W & X & LS & XE & RX & J).
    assert (Lg1 : nth_error (X :: G) (S g) = Some F) by exact Lg.
    assert (Lr1 : nth_error (X :: G) (S r) = Some T) by exact Lr.
    destruct (extract_field_sound_closed _ _ _ _ _ _ _ _ _ Lg1 Rg Lr1 Rx J)
      as (h & U & W' & Y & RS & YE & RY & K).
    assert (Lg2 : nth_error (Y :: X :: G) (S (S g)) = Some F) by exact Lg.
    destruct (IH (Y :: X :: G) (S (S g)) 0 F Y Lg2 Rg eq_refl RY K) as (Delta & Len & HT & Slots).
    exists (Delta ++ [Y;X]). rewrite length_app, Len. cbn [length].
    rewrite <- app_assoc. repeat split; try exact HT; try lia.
    intros [|i] I.
    + exists X. split; [|exact RX].
      replace (slot_index (S n) 0) with (length Delta + 1)
        by (unfold slot_index; lia).
      rewrite nth_error_app2 by lia.
      replace (length Delta + 1 - length Delta) with 1 by lia. reflexivity.
    + exact (Slots i ltac:(lia)).
Qed.

Local Definition bare_arrow T := exists A B, T = tyarr A B.

Local Lemma record_bare ts : bare_arrow (record_type ts).
Proof. destruct ts; cbn; repeat eexists. Qed.

Local Lemma unpack_record_complete ts G g r body :
  Forall bare_arrow ts ->
  nth_error G g = Some i_scheme ->
  nth_error G r = Some (record_type ts) ->
  typable_in (record_context ts ++ G) body ->
  typable_in G (unpack_record (length ts) g r body).
Proof.
  revert G g r. induction ts as [|T ts IH]; intros G g r HR Lg Lr H; [exact H|].
  inversion HR as [|? ? HA HS]; subst.
  destruct HA as (A & B & ->). destruct (record_bare ts) as (C & D & CD).
  cbn [record_context] in H. rewrite <- app_assoc in H.
  cbn [length unpack_record record_type] in *.
  eapply extract_field_complete; [exact Lg|exact Lr|apply rigid_arrow_direct|reflexivity|].
  eapply extract_field_complete.
  - exact Lg.
  - exact Lr.
  - apply rigid_arrow_direct.
  - now rewrite CD.
  - rewrite <- CD. eapply IH; [exact HS|exact Lg|reflexivity|exact H].
Qed.

Local Fixpoint subterms t :=
  t :: match t with atom _ => [] | arr l r => subterms l ++ subterms r end.

Local Lemma subterms_self t : In t (subterms t).
Proof. destruct t; now left. Qed.

Local Lemma term_eq_dec : forall s t : term, {s = t} + {s <> t}.
Proof. decide equality. apply Nat.eq_dec. Defined.

Local Fixpoint label_index t (labels : list term) : nat :=
  match labels with
  | [] => 0
  | A :: labels => if term_eq_dec t A then 0 else S (label_index t labels)
  end.

Local Lemma label_index_correct t labels :
  In t labels -> nth_error labels (label_index t labels) = Some t.
Proof.
  induction labels as [|u labels IH]; cbn; [tauto|].
  destruct (term_eq_dec t u) as [-> | N]; [reflexivity|].
  intros [H|H]; [congruence|exact (IH H)].
Qed.

Local Definition node_slot labels t := slot_index (length labels) (label_index t labels).

Local Definition pairing_nat a b := (a + b) * (a + b) + a.

Local Lemma pairing_nat_inj a b c d :
  pairing_nat a b = pairing_nat c d -> a = c /\ b = d.
Proof.
  unfold pairing_nat. intro E.
  assert (H : forall u v, u < v -> u * u + u < v * v).
  { intros u v U. assert (J : (S u)*(S u) <= v*v) by
      (apply Nat.mul_le_mono; lia). nia. }
  destruct (Nat.lt_trichotomy (a+b) (c+d)) as [F|[F|F]].
  - specialize (H _ _ F). lia.
  - rewrite F in E. lia.
  - specialize (H _ _ F). lia.
Qed.

Local Fixpoint term_code t :=
  match t with
  | atom n => 2*n
  | arr l r => S (2 * pairing_nat (term_code l) (term_code r))
  end.

Local Lemma term_code_inj s t : term_code s = term_code t -> s = t.
Proof.
  revert t. induction s; intros [m|l r] H; cbn [term_code] in H; try lia.
  - f_equal. lia.
  - assert (K : pairing_nat (term_code s1) (term_code s2) =
                pairing_nat (term_code l) (term_code r)) by lia.
    apply pairing_nat_inj in K. destruct K as [P Q].
    now rewrite (IHs1 l P), (IHs2 r Q).
Qed.

(* A node has two arrow-shaped fields. Read the domain of each field
   and give each remaining shape its own atom. Substitution preserves
   the node case, which induces a substitution on the decoded terms. *)
Local Fixpoint decode (t : term) : term :=
  match t with
  | arr (arr l _) (arr r _) => arr (decode l) (decode r)
  | _ => atom (term_code t)
  end.

Local Fixpoint decode_binding f n (ts : list term) : term :=
  match ts with
  | [] => atom n
  | T :: ts =>
      if n =? term_code T then decode (substitute f T) else decode_binding f n ts
  end.

Local Lemma decode_binding_in f T ts :
  In T ts -> decode_binding f (term_code T) ts = decode (substitute f T).
Proof.
  induction ts as [|U ts IH]; cbn; [tauto|].
  destruct (term_code T =? term_code U) eqn:E.
  - apply Nat.eqb_eq, term_code_inj in E. now subst U.
  - intros [H|H]; [subst U; now rewrite Nat.eqb_refl in E|now apply IH].
Qed.

Local Lemma decode_substitution f T :
  exists g, substitute g (decode T) = decode (substitute f T).
Proof.
  exists (fun n => decode_binding f n (subterms T)).
  assert (H : forall U, In U (subterms T) ->
                    decode_binding f (term_code U) (subterms T) = decode (substitute f U))
    by exact (fun U => decode_binding_in f U (subterms T)).
  assert (P : forall U, (forall V, In V (subterms U) -> In V (subterms T)) ->
    substitute (fun n => decode_binding f n (subterms T)) (decode U) =
    decode (substitute f U)).
  { fix IH 1. intros U V. destruct U as [n|L R].
    - exact (H (atom n) (V (atom n) (or_introl eq_refl))).
    - destruct L as [a|A B], R as [b|C D].
      + exact (H (arr (atom a) (atom b)) (V _ (or_introl eq_refl))).
      + exact (H (arr (atom a) (arr C D)) (V _ (or_introl eq_refl))).
      + exact (H (arr (arr A B) (atom b)) (V _ (or_introl eq_refl))).
      + cbn [decode substitute]. f_equal.
        * apply IH. intros W L. apply V.
          change (In W (arr (arr A B) (arr C D) :: subterms (arr A B) ++ subterms (arr C D))).
          right. apply in_or_app. left.
          change (In W (arr A B :: subterms A ++ subterms B)).
          right. apply in_or_app. now left.
        * apply IH. intros W L. apply V.
          change (In W (arr (arr A B) (arr C D) :: subterms (arr A B) ++ subterms (arr C D))).
          right. apply in_or_app. right.
          change (In W (arr C D :: subterms C ++ subterms D)).
          right. apply in_or_app. now left. }
  apply P. auto.
Qed.

Local Fixpoint project_lift k v :=
  match k with 0 => v | S k => project_lift k (scons (atom 0) v) end.

Local Lemma project_quantify k v A :
  project_type v (quantify k A) = project_type (project_lift k v) A.
Proof. revert v. induction k; cbn; auto. Qed.

Local Lemma project_lift_index k v n :
  project_lift k v n = if n <? k then atom 0 else v (n-k).
Proof.
  revert v n. induction k; intros v n.
  - change (v n = v (n-0)). now rewrite Nat.sub_0_r.
  - cbn [project_lift]. rewrite IHk.
    destruct (n <? k) eqn:E; destruct (n <? S k) eqn:J; try reflexivity;
      apply Nat.ltb_lt in E || apply Nat.ltb_ge in E;
      apply Nat.ltb_lt in J || apply Nat.ltb_ge in J; try lia.
    + replace (n-k) with 0 by lia. reflexivity.
    + replace (n-k) with (S (n-S k)) by lia. reflexivity.
Qed.

Local Lemma erase_close_head T : erase_type (close_head T) = erase_type T.
Proof.
  unfold close_head, erase_type. rewrite project_sub.
  pose proof (head_decompose T) as D.
  replace (project_type (fun n => atom (S n)) T) with
    (project_type (fun n => atom (S n)) (quantify (head_quantifiers T) (head_body T))) by now rewrite <- D.
  (* Compare the assignments to the variables of the opened type body. *)
  rewrite project_quantify. apply project_ext. intro n.
  unfold funcomp, prefix_substitution. rewrite project_lift_index.
  now destruct (n <? head_quantifiers T).
Qed.

Local Definition project_value T := decode (erase_type (close_head T)).

Local Lemma erase_field k V W :
  exists R, erase_type (quantify k (tyarr V W)) =
    arr (erase_type (subst_poly_type
                     (prefix_substitution k (fun _ => bottom)) V)) R.
Proof.
  rewrite <- erase_close_head. unfold close_head.
  rewrite head_quantifiers_quantify, head_body_quantify.
  cbn [tyarr head_quantifiers head_body]. rewrite Nat.add_0_r.
  cbn [subst_poly_type erase_type project_type]. eauto.
Qed.

Local Lemma equal_value G x y A B :
  nth_error G x = Some A -> nth_error G y = Some B ->
  rigid_type A -> rigid_type B ->
  typable_in G (compare_terms (av x) (av y)) ->
  close_head A = close_head B.
Proof.
  intros L1 L2 (j & X & Y & E1) (k & U & V & E2) H.
  assert (R1 : rigid_arrow A X Y) by (exists j; exact E1).
  assert (R2 : rigid_arrow B U V) by (exists k; exact E2).
  rewrite (rigid_arrow_close _ _ _ R1), (rigid_arrow_close _ _ _ R2).
  exact (same_rigid_core _ _ _ _ _ _ _ _ _ L1 L2 R1 R2 H).
Qed.

Local Definition link_field g x y right :=
  extract_field g x right (compare_terms (av 0) (av (S y))).

Local Lemma link_field_sound G g x y right F T A B U :
  nth_error G g = Some F -> reference_type F ->
  nth_error G x = Some T -> rigid_arrow T A B ->
  nth_error G y = Some U -> rigid_type U ->
  typable_in G (link_field g x y right) ->
  exists Q, erase_type (if right then B else A) =
    arr (erase_type (close_head U)) Q.
Proof.
  intros Lg RG Lx RX Ly RU H.
  destruct (extract_field_sound_closed _ _ _ _ _ _ _ _ _ Lg RG Lx RX H)
    as (k & V & W & X & Eq & E & R & K).
  assert (Lc : nth_error (X :: G) (S y) = Some U) by exact Ly.
  pose proof (equal_value (X :: G) 0 (S y) X U eq_refl Lc R RU K) as C.
  rewrite Eq. destruct (erase_field k V W) as [Q Qe]. exists Q.
  rewrite <- E in Qe. rewrite <- C. now rewrite erase_close_head.
Qed.

Local Definition link_node g x y z :=
  pkg_seq (link_field g x y false) (link_field g x z true).

Local Lemma link_node_sound G g x y z F T U V :
  nth_error G g = Some F -> reference_type F ->
  nth_error G x = Some T -> rigid_type T ->
  nth_error G y = Some U -> rigid_type U ->
  nth_error G z = Some V -> rigid_type V ->
  typable_in G (link_node g x y z) ->
  project_value T = arr (project_value U) (project_value V).
Proof.
  intros Lg RG Lx (k & A & B & E) Ly RU Lz RV H.
  assert (RX : rigid_arrow T A B) by (exists k; exact E).
  apply typable_seq in H. destruct H as [H1 H2].
  destruct (link_field_sound _ _ _ _ _ _ _ _ _ _ Lg RG Lx RX Ly RU H1) as [P P1].
  destruct (link_field_sound _ _ _ _ _ _ _ _ _ _ Lg RG Lx RX Lz RV H2) as [Q Q1].
  unfold project_value. rewrite (rigid_arrow_close _ _ _ RX).
  change (decode (arr (erase_type A) (erase_type B)) =
    arr (decode (erase_type (close_head U))) (decode (erase_type (close_head V)))).
  now rewrite P1, Q1.
Qed.

Local Lemma link_field_complete G g x y (right : bool) U V L R :
  nth_error G g = Some i_scheme ->
  nth_error G x = Some (pair_type U V) ->
  nth_error G y = Some (tyarr L R) ->
  (if right then V else U) = tyarr L R ->
  typable_in G (link_field g x y right).
Proof.
  intros Lg Lx Ly E. unfold link_field. eapply extract_field_complete.
  - exact Lg.
  - exact Lx.
  - apply rigid_arrow_direct.
  - destruct right; cbn in *; now rewrite E.
  - eapply comparison_complete.
    + apply type_assignment_var. reflexivity.
    + apply type_assignment_var. exact Ly.
Qed.

Local Lemma link_node_complete G g x y z U V :
  nth_error G g = Some i_scheme ->
  nth_error G x = Some (pair_type U V) ->
  nth_error G y = Some U -> bare_arrow U ->
  nth_error G z = Some V -> bare_arrow V ->
  typable_in G (link_node g x y z).
Proof.
  intros Lg Lx Ly (A & B & EU) Lz (C & D & EV).
  subst U V. apply typable_seq. split.
  - exact (link_field_complete _ _ _ _ false _ _ _ _ Lg Lx Ly eq_refl).
  - exact (link_field_complete _ _ _ _ true _ _ _ _ Lg Lx Lz eq_refl).
Qed.

Local Definition identity_term := ab (av 0).

Local Lemma identity_typable G : typable_in G identity_term.
Proof. exists (diag (tv 0)). apply type_assignment_abs, type_assignment_var. reflexivity. Qed.

Local Fixpoint link_tree g (ix : term -> nat) t :=
  match t with
  | atom _ => identity_term
  | arr l r => pkg_seq (link_node g (ix t) (ix l) (ix r))
      (pkg_seq (link_tree g ix l) (link_tree g ix r))
  end.

Local Lemma links_sound G g F ix data t :
  nth_error G g = Some F -> reference_type F ->
  (forall v, In v (subterms t) -> nth_error G (ix v) = Some (data v) /\ rigid_type (data v)) ->
  typable_in G (link_tree g ix t) ->
  project_value (data t) = substitute (fun n => project_value (data (atom n))) t.
Proof.
  intros Lg RG. induction t as [n|l IHl r IHr]; intros L H; [reflexivity|].
  apply typable_seq in H. destruct H as [N H]. apply typable_seq in H. destruct H as [Hl Hr].
  assert (LL : forall w, In w (subterms l) ->
    nth_error G (ix w) = Some (data w) /\ rigid_type (data w)).
  { intros w J. apply L. change (In w (arr l r :: subterms l ++ subterms r)).
    right. apply in_or_app. now left. }
  assert (LR : forall w, In w (subterms r) ->
    nth_error G (ix w) = Some (data w) /\ rigid_type (data w)).
  { intros w J. apply L. change (In w (arr l r :: subterms l ++ subterms r)).
    right. apply in_or_app. now right. }
  destruct (L (arr l r) (or_introl eq_refl)) as [L1 R1].
  destruct (LL l (subterms_self l)) as [L2 R2].
  destruct (LR r (subterms_self r)) as [L3 R3].
  rewrite (link_node_sound _ _ _ _ _ _ _ _ _ Lg RG L1 R1 L2 R2 L3 R3 N).
  cbn [substitute]. now rewrite (IHl LL Hl), (IHr LR Hr).
Qed.

Local Fixpoint representation t :=
  match t with
  | atom n => tyarr (tv (2*n)) (tv (S (2*n)))
  | arr l r => pair_type (representation l) (representation r)
  end.

Local Lemma representation_bare t : bare_arrow (representation t).
Proof. destruct t; cbn; repeat eexists. Qed.

Local Definition repr_action f n :=
  let T := representation (f (Nat.div2 n)) in
  match T with
  | poly_arr L R => if Nat.odd n then R else L
  | _ => tv n
  end.

Local Lemma repr_action_ok f t :
  subst_poly_type (repr_action f) (representation t) =
  representation (substitute f t).
Proof.
  induction t as [n|l IHl r IHr].
  - change (tyarr (repr_action f (2*n)) (repr_action f (S (2*n))) =
      representation (f n)).
    unfold repr_action. rewrite Nat.div2_double, Nat.div2_succ_double.
    rewrite Nat.odd_succ, Nat.odd_mul.
    assert (Ev : Nat.even (2*n) = true).
    { apply Nat.even_spec. exists n. reflexivity. }
    cbn [Nat.odd andb]. rewrite Ev. destruct (f n); reflexivity.
  - change (pair_type (subst_poly_type (repr_action f) (representation l))
                      (subst_poly_type (repr_action f) (representation r))
             = pair_type (representation (substitute f l)) (representation (substitute f r))).
    now rewrite IHl, IHr.
Qed.

Local Lemma links_complete G g ix (f : valuation) t :
  nth_error G g = Some i_scheme ->
  (forall v, In v (subterms t) -> nth_error G (ix v) = Some (representation (substitute f v))) ->
  typable_in G (link_tree g ix t).
Proof.
  intros Lg. induction t as [n|l IHl r IHr]; intros L; [apply identity_typable|].
  assert (LL : forall w, In w (subterms l) ->
    nth_error G (ix w) = Some (representation (substitute f w))).
  { intros w J. apply L. change (In w (arr l r :: subterms l ++ subterms r)).
    right. apply in_or_app. now left. }
  assert (LR : forall w, In w (subterms r) ->
    nth_error G (ix w) = Some (representation (substitute f w))).
  { intros w J. apply L. change (In w (arr l r :: subterms l ++ subterms r)).
    right. apply in_or_app. now right. }
  cbn [link_tree]. apply typable_seq. split.
  - eapply (link_node_complete _ _ _ _ _ (representation (substitute f l)) (representation (substitute f r)));
    [exact Lg|exact (L (arr l r) (subterms_self _))|apply LL, subterms_self|apply representation_bare|apply LR, subterms_self|apply representation_bare].
  - apply typable_seq. split; [now apply IHl|now apply IHr].
Qed.

Local Definition input_labels s t u := subterms s ++ subterms t ++ subterms u.

Local Lemma input_labels_in s t u v :
  In v (subterms s) \/ In v (subterms t) \/ In v (subterms u) ->
  In v (input_labels s t u).
Proof.
  unfold input_labels. rewrite !in_app_iff. tauto.
Qed.

(* The links enforce constructor equations on the shared record. The
   two final calls specialize the original payload scheme independently. *)
Local Definition verify_types s t u g p d :=
  let ix := fun v => S (node_slot (input_labels s t u) v) in
  pkg_seq (link_tree g ix s)
    (pkg_seq (link_tree g ix t)
      (pkg_seq (link_tree g ix u)
        (pkg_seq (compare_terms (av 0) (av (ix s)))
          (pkg_seq (third_test p d (ix t)) (third_test p d (ix u)))))).

Local Lemma project_instance S T A B C D f :
  rigid_arrow S A B -> rigid_arrow T C D ->
  subst_poly_type f (tyarr A B) = tyarr C D ->
  exists u, substitute u (project_value S) = project_value T.
Proof.
  intros RS RT E. unfold project_value.
  rewrite (rigid_arrow_close _ _ _ RS), (rigid_arrow_close _ _ _ RT).
  apply (f_equal erase_type) in E. rewrite erase_sub in E.
  destruct (decode_substitution (scons (atom 0) (funcomp erase_type f))
    (erase_type (tyarr A B))) as [u U].
  exists u. now rewrite E in U.
Qed.

Local Lemma verify_sound s t u G g p d F H k l m D E A B R h V W rho :
  H = payload_scheme k l m D E A B ->
  nth_error G g = Some F -> reference_type F ->
  nth_error G p = Some (subst_poly_type rho H) ->
  nth_error G 0 = Some V -> rigid_type V ->
  rigid_arrow A (quantify h (tyarr V W)) R ->
  (forall v, In v (input_labels s t u) ->
    exists T, nth_error G (S (node_slot (input_labels s t u) v)) = Some T /\ rigid_type T) ->
  typable_in G (verify_types s t u g p d) ->
  LU2SemiU (s,t,u).
Proof.
  intros Shape Lg RG Lp Lv RV RA Slots Check.
  set (ix := fun v => S (node_slot (input_labels s t u) v)).
  set (data := fun v => nth (ix v) G bottom).
  assert (L : forall v, In v (input_labels s t u) ->
    nth_error G (ix v) = Some (data v) /\ rigid_type (data v)).
  { intros v J. destruct (Slots v J) as (T & K & U).
    unfold data. pose proof (@nth_error_nth _ G _ T bottom K) as V0.
    change (nth (ix v) G bottom = T) in V0. rewrite V0. now split. }
  cbn [verify_types] in Check. fold ix in Check.
  apply typable_seq in Check. destruct Check as [Ls P].
  apply typable_seq in P. destruct P as [Lt P].
  apply typable_seq in P. destruct P as [Lu P].
  apply typable_seq in P. destruct P as [C P].
  apply typable_seq in P. destruct P as [T0 T1].
  assert (S1 : project_value (data s) = substitute (fun n => project_value (data (atom n))) s).
  { apply (links_sound G g F ix data s Lg RG); [|exact Ls].
    intros v J. apply L, input_labels_in. auto. }
  assert (S2 : project_value (data t) = substitute (fun n => project_value (data (atom n))) t).
  { apply (links_sound G g F ix data t Lg RG); [|exact Lt].
    intros v J. apply L, input_labels_in. auto. }
  assert (S3 : project_value (data u) = substitute (fun n => project_value (data (atom n))) u).
  { apply (links_sound G g F ix data u Lg RG); [|exact Lu].
    intros v J. apply L, input_labels_in. auto. }
  assert (Root : forall v, v = s \/ v = t \/ v = u ->
    nth_error G (ix v) = Some (data v) /\ rigid_type (data v)).
  { intros v [-> | [-> | ->]]; apply L, input_labels_in;
      auto using subterms_self. }
  destruct (Root s ltac:(auto)) as [L0 R0].
  pose proof (equal_value _ _ _ _ _ Lv L0 RV R0 C) as Eq.
  assert (Q : forall v, v = t \/ v = u -> typable_in G (third_test p d (ix v)) ->
    exists f, substitute f (project_value V) = project_value (data v)).
  { intros v Ov K. destruct (Root v ltac:(auto)) as (Hx & j & X & Y & J).
    destruct RV as (i & X0 & X1 & Rv).
    assert (Rs : rigid_arrow V X0 X1) by (exists i; exact Rv).
    assert (Rt : rigid_arrow (data v) X Y) by (exists j; exact J).
    destruct (third_test_sound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Shape Lp RA Rs _ _ _ Hx Rt K) as [f Z].
    exact (project_instance _ _ _ _ _ _ _ Rs Rt Z). }
  destruct (Q t ltac:(auto) T0) as [f G0].
  destruct (Q u ltac:(auto) T1) as [j G1].
  assert (EV : project_value V = project_value (data s)) by (unfold project_value; now rewrite Eq).
  rewrite EV in G0, G1.
  rewrite S1, S2 in G0. rewrite S1, S3 in G1.
  exists (fun n => project_value (data (atom n))), f, j. now split.
Qed.

Local Definition check_record s t u g a p d :=
  let n := length (input_labels s t u) in
  extract_field g a true
    (unpack_record n (S g) 0
      (extract_field (2*n + S g) (2*n + S a) false
        (verify_types s t u (S (2*n + S g)) (S (2*n + S p)) (S (2*n + S d))))).

Local Lemma lookup_add_prefix (Delta G : environment) n j T :
  length Delta = n ->
  nth_error G j = Some T ->
  nth_error (Delta ++ G) (n + j) = Some T.
Proof.
  intros <- L. rewrite nth_error_app2 by lia.
  replace (length Delta + j - length Delta) with j by lia. exact L.
Qed.

Local Lemma check_record_sound s t u G g a p d F H k l m D E A B rho :
  H = payload_scheme k l m D E A B ->
  nth_error G g = Some F -> reference_type F ->
  nth_error G a = Some A -> rigid_type A ->
  nth_error G p = Some (subst_poly_type rho H) ->
  typable_in G (check_record s t u g a p d) ->
  LU2SemiU (s,t,u).
Proof.
  intros Shape Lg RG La (j & L & R & Eq) Lp T.
  set (n := length (input_labels s t u)) in *.
  assert (RA : rigid_arrow A L R) by (exists j; exact Eq).
  cbn [check_record] in T. fold n in T.
  destruct (extract_field_sound_closed _ _ _ _ _ _ _ _ _ Lg RG La RA T)
    as (i & X & Y & Rec & Er & RecEq & RRec & T').
  assert (Lg1 : nth_error (Rec :: G) (S g) = Some F) by exact Lg.
  destruct (unpack_record_sound n (Rec :: G) (S g) 0 _ F Rec Lg1 RG eq_refl RRec T')
    as (Delta & Len & Check & Slots).
  set (G1 := Delta ++ Rec :: G) in *.
  assert (Lg2 : nth_error G1 (2*n + S g) = Some F)
    by (apply lookup_add_prefix; assumption).
  assert (La2 : nth_error G1 (2*n + S a) = Some A)
    by (apply lookup_add_prefix; [exact Len|exact La]).
  assert (Lp2 : nth_error G1 (2*n + S p) = Some (subst_poly_type rho H))
    by (apply lookup_add_prefix; [exact Len|exact Lp]).
  destruct (extract_field_sound _ _ _ _ _ _ _ _ _ Lg2 RG La2 RA Check)
    as (h & V & W & EL & RV & K).
  set (ren := ren_poly_type (Nat.add h)) in *.
  set (G2 := V :: map ren G1) in *.
  assert (Lg3 : nth_error G2 (S (2*n + S g)) = Some (ren F)).
  { unfold G2. change (nth_error (map ren G1) (2*n + S g) = Some (ren F)).
    now rewrite nth_error_map, Lg2. }
  assert (Lp3 : nth_error G2 (S (2*n + S p)) =
    Some (subst_poly_type (funcomp (subst_poly_type (fun j => tv (h + j))) rho) H)).
  { unfold G2. cbn [nth_error].
    rewrite nth_error_map, Lp2. unfold ren. cbn [option_map]. now rewrite ren_as_sub, sub_sub. }
  assert (RS : forall v, In v (input_labels s t u) ->
    exists T, nth_error G2 (S (node_slot (input_labels s t u) v)) = Some T /\ rigid_type T).
  { intros v I. pose proof (label_index_correct v _ I) as Find.
    assert (Bnd : label_index v (input_labels s t u) < n).
    { unfold n. apply nth_error_Some. now rewrite Find. }
    destruct (Slots _ Bnd) as [U [LU RU]].
    exists (ren U). split.
    - unfold G2. change (nth_error (map ren G1) (node_slot (input_labels s t u) v) =
        Some (ren U)). unfold node_slot. fold n. now rewrite nth_error_map, LU.
    - unfold ren. rewrite ren_as_sub. now apply rigid_sub. }
  assert (RF : reference_type (ren F)).
  { unfold ren. rewrite ren_as_sub. now apply reference_sub. }
  assert (RA' : rigid_arrow A (quantify h (tyarr V W)) R) by now rewrite <- EL.
  exact (verify_sound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Shape Lg3 RF Lp3
    eq_refl RV RA' RS K).
Qed.

Local Fixpoint type_bound A :=
  match A with
  | poly_var j => S j
  | poly_arr L R => Nat.max (type_bound L) (type_bound R)
  | poly_abs B => type_bound B
  end.

Local Lemma type_bound_free A p j :
  free_at A p = Some j -> j < type_bound A.
Proof.
  revert p j. induction A; intros p j E; cbn in *.
  - destruct p; try discriminate. injection E as E. lia.
  - destruct p as [|[] p]; try discriminate.
    + specialize (IHA2 _ _ E). lia.
    + specialize (IHA1 _ _ E). lia.
  - destruct (free_at A p) as [[|m]|] eqn:H; try discriminate.
    injection E as E. subst m. specialize (IHA _ _ H). lia.
Qed.

Local Definition closed_type A := forall p j, free_at A p <> Some j.

Local Lemma closed_quantify A k :
  type_bound A <= k -> closed_type (quantify k A).
Proof.
  intros B p j E. apply free_at_quantify in E.
  pose proof (type_bound_free _ _ _ E). lia.
Qed.

Local Lemma closed_ren A r : closed_type A -> ren_poly_type r A = A.
Proof.
  intros C. rewrite ren_as_sub. rewrite <- (sub_vars A) at 2.
  apply subst_free_congr. intros p n E. exfalso. exact (C p n E).
Qed.

Local Lemma closed_arrow A B : closed_type A -> closed_type B -> closed_type (tyarr A B).
Proof.
  intros L R [|[] p] n E; try discriminate; [exact (R p n E)|exact (L p n E)].
Qed.

Local Lemma bottom_closed : closed_type bottom.
Proof. exact (closed_quantify (tv 0) 1 ltac:(cbn [tv type_bound]; lia)). Qed.

Local Lemma i_scheme_closed : closed_type i_scheme.
Proof.
  apply (closed_quantify (diag (tyarr (tv 0) (tv 1))) 2). reflexivity.
Qed.

Local Lemma map_ren_closed G r : Forall closed_type G -> map (ren_poly_type r) G = G.
Proof. induction 1; cbn; [reflexivity|]. now rewrite closed_ren, IHForall. Qed.

Local Lemma bottom_typing G d T :
  nth_error G d = Some bottom -> type_assignment G (av d) T.
Proof.
  intro L. exact (@type_assignment_inst _ _ (tv 0) T (type_assignment_var L)).
Qed.

Local Lemma at_bound G p A f k :
  nth_error G p = Some (quantify k A) ->
  type_bound A <= k ->
  type_assignment G (av p) (subst_poly_type f A).
Proof.
  intros L B.
  assert (E : subst_poly_type (prefix_substitution k f) A = subst_poly_type f A).
  { apply subst_free_congr. intros q j Eq.
    pose proof (type_bound_free _ _ _ Eq) as J.
    unfold prefix_substitution. assert ((j <? k) = true) by (apply Nat.ltb_lt; lia).
    now rewrite H. }
  eapply typing_specialize with (args := opening_args k f).
  - apply type_assignment_var. exact L.
  - now rewrite specialize_prefix, E.
Qed.

Local Definition witness_record s t u f :=
  map (fun v => representation (substitute f v)) (input_labels s t u).

Local Definition witness_root s t u f :=
  pair_type (representation (substitute f s)) (record_type (witness_record s t u f)).

Local Definition witness_payload s t u f :=
  tyarr bottom (tyarr bottom (diag (witness_root s t u f))).

Local Definition witness_scheme s t u f :=
  quantify (type_bound (witness_payload s t u f)) (witness_payload s t u f).

Local Lemma witness_scheme_closed s t u f : closed_type (witness_scheme s t u f).
Proof. unfold witness_scheme. apply closed_quantify. lia. Qed.

Local Lemma third_test_complete G p d x X Y Z :
  type_assignment G (av p)
    (tyarr bottom (tyarr bottom (tyarr (pair_type X Y) Z))) ->
  nth_error G d = Some bottom -> nth_error G x = Some X ->
  typable_in G (third_test p d x).
Proof.
  intros HP LD LX.
  assert (J : type_assignment (diag X :: G) (ap (av 0) (av (S x))) X).
  { exact (type_assignment_app (@type_assignment_var (diag X :: G) 0 (diag X) eq_refl)
      (@type_assignment_var (diag X :: G) (S x) X LX)). }
  assert (K : type_assignment G
    (ab (pkg_seq (ap (av 0) (av (S x))) (av (S d)))) (pair_type X Y)).
  { apply type_assignment_abs. apply typing_seq; [now exists X|].
    apply bottom_typing. exact LD. }
  exists Z. unfold third_test.
  pose proof (bottom_typing _ _ bottom LD) as D.
  exact (type_assignment_app (type_assignment_app (type_assignment_app HP D) D) K).
Qed.

Local Lemma verify_complete s t u f G g p d j0 j1 :
  nth_error G g = Some i_scheme ->
  nth_error G p = Some (witness_scheme s t u f) ->
  nth_error G d = Some bottom ->
  nth_error G 0 = Some (representation (substitute f s)) ->
  (forall v, In v (input_labels s t u) ->
    nth_error G (S (node_slot (input_labels s t u) v)) = Some (representation (substitute f v))) ->
  substitute j0 (substitute f s) = substitute f t ->
  substitute j1 (substitute f s) = substitute f u ->
  typable_in G (verify_types s t u g p d).
Proof.
  intros Lg Lp Ld Ls Data E0 E1.
  assert (J : forall v j, In v (input_labels s t u) ->
      substitute j (substitute f s) = substitute f v ->
      typable_in G (third_test p d (S (node_slot (input_labels s t u) v)))).
  { intros v j I E.
    pose proof (at_bound _ _ _ (repr_action j) _ Lp (Nat.le_refl _)) as K.
    unfold witness_payload, witness_root, pair_type, diag, tyarr in K.
    cbn [bottom tv subst_poly_type] in K. rewrite !repr_action_ok, E in K.
    eapply third_test_complete; [exact K|exact Ld|now apply Data]. }
  cbn [verify_types]. apply typable_seq. split.
  - apply (links_complete _ _ _ f _ Lg). intros v I. apply Data, input_labels_in. auto.
  - apply typable_seq. split.
    + apply (links_complete _ _ _ f _ Lg). intros v I. apply Data, input_labels_in. auto.
    + apply typable_seq. split.
      * apply (links_complete _ _ _ f _ Lg). intros v I. apply Data, input_labels_in. auto.
      * apply typable_seq. split.
        -- eapply comparison_complete.
           ++ apply type_assignment_var. exact Ls.
           ++ apply type_assignment_var, Data, input_labels_in. auto using subterms_self.
        -- apply typable_seq. split.
           ++ apply (J t j0); [apply input_labels_in; auto using subterms_self|exact E0].
           ++ apply (J u j1); [apply input_labels_in; auto using subterms_self|exact E1].
Qed.

Local Lemma witness_slots s t u f G v :
  In v (input_labels s t u) ->
  nth_error (record_context (witness_record s t u f) ++ G)
    (node_slot (input_labels s t u) v) =
    Some (representation (substitute f v)).
Proof.
  intro H. pose proof (label_index_correct _ _ H) as E.
  unfold node_slot, witness_record.
  rewrite <- (length_map (fun v => representation (substitute f v))
                    (input_labels s t u)).
  apply slot_record_context. now rewrite nth_error_map, E.
Qed.

Local Lemma check_record_complete s t u f G g a p d j0 j1 :
  nth_error G g = Some i_scheme ->
  nth_error G a = Some (witness_root s t u f) ->
  nth_error G p = Some (witness_scheme s t u f) ->
  nth_error G d = Some bottom ->
  substitute j0 (substitute f s) = substitute f t ->
  substitute j1 (substitute f s) = substitute f u ->
  typable_in G (check_record s t u g a p d).
Proof.
  intros Lg La Lp Ld E0 E1.
  set (ts := witness_record s t u f).
  set (n := length (input_labels s t u)).
  assert (Len : length ts = n) by (unfold ts, witness_record, n; apply length_map).
  set (V := representation (substitute f s)).
  destruct (representation_bare (substitute f s)) as (X & Y & EV). fold V in EV.
  destruct (record_bare ts) as (L & R & ER).
  cbn [check_record]. fold n.
  change (nth_error G a = Some (pair_type V (record_type ts))) in La.
  eapply extract_field_complete; [exact Lg|exact La|apply rigid_arrow_direct| |].
  { now rewrite ER. }
  rewrite <- ER. unfold n in Len. rewrite <- Len at 1.
  apply (unpack_record_complete ts).
  - unfold ts, witness_record. apply Forall_map, Forall_forall.
    intros v _. apply representation_bare.
  - exact Lg.
  - reflexivity.
  - set (G1 := record_context ts ++ record_type ts :: G).
    assert (L1 : length (record_context ts) = 2*n) by now rewrite record_context_length, Len.
    assert (Gg : nth_error G1 (2*n+S g) = Some i_scheme)
      by (apply lookup_add_prefix; [exact L1|exact Lg]).
    assert (Ga : nth_error G1 (2*n+S a) = Some (pair_type V (record_type ts)))
      by (apply lookup_add_prefix; [exact L1|exact La]).
    eapply extract_field_complete; [exact Gg|exact Ga|apply rigid_arrow_direct| |].
    { now rewrite EV. }
    rewrite <- EV.
    eapply (verify_complete _ _ _ f _ _ _ _ j0 j1); try eassumption.
    + change (nth_error G1 (2*n+S p) = Some (witness_scheme s t u f)).
      apply lookup_add_prefix; [exact L1|exact Lp].
    + change (nth_error G1 (2*n+S d) = Some bottom).
      apply lookup_add_prefix; [exact L1|exact Ld].
    + reflexivity.
    + intros v I. unfold G1. exact (witness_slots s t u f (record_type ts :: G) v I).
Qed.

Local Definition bind_domain x d body :=
  compare_terms (av x) (ab (pkg_seq body (av (S d)))).

Local Lemma bind_domain_sound G x d T A B body :
  nth_error G x = Some T -> rigid_arrow T A B ->
  typable_in G (bind_domain x d body) -> typable_in (A :: G) body.
Proof.
  intros L R H. apply comparison_sound in H. destruct H as (U & H1 & H2).
  pose proof (rigid_arrow_instance _ _ _ _ _ _ L R H1) as RU.
  apply typing_close_head in H2. rewrite (rigid_arrow_close _ _ _ RU) in H2.
  apply abs_inv in H2.
  exact (proj1 (proj1 (typable_seq _ body (av (S d))) (ex_intro _ B H2))).
Qed.

Local Lemma bind_domain_complete G x d A B body :
  nth_error G x = Some (tyarr A B) -> nth_error G d = Some B ->
  typable_in (A :: G) body -> typable_in G (bind_domain x d body).
Proof.
  intros X D H. eapply comparison_complete.
  - apply type_assignment_var. exact X.
  - apply type_assignment_abs, typing_seq; [exact H|].
    apply type_assignment_var. exact D.
Qed.

Local Lemma reference_ren A r :
  reference_type A -> reference_type (ren_poly_type r A).
Proof. intro H. rewrite ren_as_sub. now apply reference_sub. Qed.

Local Lemma payload_shape Gamma g F H :
  nth_error Gamma g = Some F -> reference_type F ->
  type_assignment Gamma (ab (ab (av (S (S g))))) H ->
  exists k l m D E A B,
    H = payload_scheme k l m D E A B /\ rigid_type A.
Proof.
  intros L RF T.
  destruct (lambda_shape _ _ _ T) as (k & D & I & K).
  rewrite K in T. apply typing_open_prefix in T. apply abs_inv in T.
  destruct (lambda_shape _ _ _ T) as (l & E & J & L').
  rewrite L' in T. apply typing_open_prefix in T. apply abs_inv in T.
  set (F' := ren_poly_type (Nat.add l) (ren_poly_type (Nat.add k) F)).
  assert (Look : nth_error
    (E :: map (ren_poly_type (Nat.add l)) (D :: map (ren_poly_type (Nat.add k)) Gamma))
    (S (S g)) = Some F').
  { cbn [map nth_error]. unfold F'. now rewrite !nth_error_map, L. }
  assert (Ref : reference_type F') by (unfold F'; now do 2 apply reference_ren).
  destruct (reference_instance _ _ _ _ Look Ref T) as (m & A & B & Shape & RA).
  exists k, l, m, D, E, A, B. split; [unfold payload_scheme; now rewrite K, L', Shape|exact RA].
Qed.

Local Definition payload_context k l m D E A Gamma :=
  A :: map (ren_poly_type (Nat.add m))
    (E :: map (ren_poly_type (Nat.add l))
      (D :: map (ren_poly_type (Nat.add k)) Gamma)).

Local Lemma payload_open Gamma body k l m D E A B :
  type_assignment Gamma (ab (ab (ab (pkg_seq body (av 0)))))
    (payload_scheme k l m D E A B) ->
  typable_in (payload_context k l m D E A Gamma) body.
Proof.
  unfold payload_scheme. intro H.
  do 3 (apply typing_open_prefix in H; apply abs_inv in H).
  exact (proj1 (proj1 (typable_seq _ body (av 0)) (ex_intro _ B H))).
Qed.

Local Lemma payload_lookup Gamma k l m D E A i T :
  nth_error Gamma i = Some T ->
  nth_error (payload_context k l m D E A Gamma) (S (S (S i))) =
    Some (ren_poly_type (Nat.add m) (ren_poly_type (Nat.add l) (ren_poly_type (Nat.add k) T))).
Proof.
  intro H. unfold payload_context. cbn [map nth_error].
  now rewrite !nth_error_map, H.
Qed.

Local Definition payload_term s t u :=
  ab (ab (ab (pkg_seq (check_record s t u 5 0 3 6) (av 0)))).

(* The outer comparison makes the same scheme available as the type
   of the payload abstraction and as the type of its parameter p. *)
Local Definition reduction_term s t u :=
  pkg_let (ref_term (av 0))
    (pkg_seq (ap (av 0) (av 0))
      (choose_rigid 0
        (pkg_seq (ap (av 0) (ab (ab (av 3))))
          (bind_domain 0 2 (ap (av 1) (payload_term s t u)))))).

Local Lemma reduction_term_sound s t u Gamma :
  typable_in Gamma (reduction_term s t u) -> LU2SemiU (s,t,u).
Proof.
  unfold reduction_term. intro J. apply typable_let in J.
  destruct J as (F & HF & J). apply typable_seq in J. destruct J as [SF P].
  pose proof (ref_term_type _ _ _ _ HF SF) as RF.
  destruct (choose_rigid_sound (F :: Gamma) 0 F _ eq_refl RF P)
    as (C & (i & H & Z & HC) & P').
  assert (RC : rigid_arrow C H Z) by (exists i; exact HC).
  apply typable_seq in P'. destruct P' as [FH Q].
  change (typable_in (C :: F :: Gamma) (field_test 0 false (ab (ab (av 3))))) in FH.
  apply (field_test_typing (C :: F :: Gamma) 0 false _ C H Z eq_refl RC) in FH.
  destruct (payload_shape (C :: F :: Gamma) 1 F H eq_refl RF FH)
    as (k & l & m & D & E & A & B & Shape & RA).
  apply (bind_domain_sound (C :: F :: Gamma) 0 2 C H Z _ eq_refl RC) in Q.
  destruct Q as [V Q]. destruct (app_inv _ _ _ _ Q) as (X & Y & U & VP).
  destruct (rigid_var_arrow (H :: C :: F :: Gamma) 1 C X Y H Z i eq_refl HC U)
    as [-> _].
  rewrite Shape in VP. apply payload_open in VP. rewrite <- Shape in VP.
  set (G := payload_context k l m D E A (H :: C :: F :: Gamma)) in *.
  set (r := fun j => m + (l + (k + j))).
  assert (Lg : nth_error G 5 = Some (ren_poly_type r F)).
  { pose proof (payload_lookup (H :: C :: F :: Gamma) k l m D E A 2 F eq_refl) as K.
    rewrite !ren_ren in K. exact K. }
  assert (Lp : nth_error G 3 = Some (subst_poly_type (fun j => tv (r j)) H)).
  { pose proof (payload_lookup (H :: C :: F :: Gamma) k l m D E A 0 H eq_refl) as K.
    rewrite !ren_ren in K. unfold tv; rewrite <- (ren_as_sub r H). exact K. }
  exact (check_record_sound s t u G 5 0 3 6 _ H k l m D E A B _ Shape Lg
    (reference_ren _ _ RF) eq_refl RA Lp VP).
Qed.

Local Lemma reference_witness :
  type_assignment [bottom] (ref_term (av 0)) i_scheme.
Proof.
  unfold i_scheme. apply typing_quantify.
  rewrite map_ren_closed by (repeat constructor; apply bottom_closed).
  apply type_assignment_abs. unfold ref_term. apply typing_seq.
  - exists (tv 1). exact (type_assignment_app
      (@type_assignment_var [tyarr (tv 0) (tv 1); bottom] 0 (tyarr (tv 0) (tv 1)) eq_refl)
      (bottom_typing [tyarr (tv 0) (tv 1); bottom] 1 (tv 0) eq_refl)).
  - apply type_assignment_var. reflexivity.
Qed.

Local Lemma reference_self :
  typable_in [i_scheme; bottom] (ap (av 0) (av 0)).
Proof.
  set (A := tyarr (tv 0) (tv 1)).
  exists (diag A). exact (type_assignment_app
    (i_scheme_at [i_scheme; bottom] 0 A A eq_refl)
    (i_scheme_at [i_scheme; bottom] 0 (tv 0) (tv 1) eq_refl)).
Qed.

Local Lemma reduction_term_complete s t u :
  LU2SemiU (s,t,u) -> typable_in [bottom] (reduction_term s t u).
Proof.
  intros (f & j0 & j1 & E0 & E1).
  unfold reduction_term. apply typable_let. exists i_scheme.
  split; [apply reference_witness|].
  apply typable_seq. split; [apply reference_self|].
  set (H := witness_scheme s t u f).
  set (A := witness_root s t u f).
  assert (CH : closed_type H) by (unfold H; apply witness_scheme_closed).
  assert (CC : closed_type (tyarr H bottom)) by (apply closed_arrow; [exact CH|apply bottom_closed]).
  apply (choose_rigid_complete [i_scheme;bottom] 0 _ H bottom eq_refl).
  apply typable_seq. split.
  - change (typable_in [tyarr H bottom; i_scheme; bottom] (field_test 0 false (ab (ab (av 3))))).
    apply (field_test_typing [tyarr H bottom; i_scheme; bottom] 0 false _
      (tyarr H bottom) H bottom eq_refl (rigid_arrow_direct _ _)).
    unfold H, witness_scheme. apply typing_quantify.
    rewrite map_ren_closed by (repeat constructor; auto using i_scheme_closed, bottom_closed).
    apply type_assignment_abs, type_assignment_abs.
    unfold witness_root. apply i_scheme_at. reflexivity.
  - apply (bind_domain_complete [tyarr H bottom; i_scheme; bottom] 0 2 H bottom _ eq_refl eq_refl).
    exists bottom. eapply type_assignment_app.
    + exact (@type_assignment_var [H;tyarr H bottom;i_scheme;bottom] 1 (tyarr H bottom) eq_refl).
    + unfold H, witness_scheme. apply typing_quantify.
      rewrite map_ren_closed by (repeat constructor; auto using i_scheme_closed, bottom_closed).
      apply type_assignment_abs, type_assignment_abs, type_assignment_abs.
      apply typing_seq.
      * apply (check_record_complete s t u f [A;bottom;bottom;H;tyarr H bottom;i_scheme;bottom]
          5 0 3 6 j0 j1 eq_refl eq_refl eq_refl eq_refl E0 E1).
      * apply type_assignment_var. reflexivity.
Qed.

Theorem reduction : LU2SemiU ⪯ SysF_TYP.
Proof.
  exists (fun '(s,t,u) => reduction_term s t u).
  intros [[s t] u]. split.
  - intro H. destruct (reduction_term_complete _ _ _ H) as [T HT].
    exists [bottom], T. exact HT.
  - intros (Gamma & T & H). apply (reduction_term_sound _ _ _ Gamma).
    now exists T.
Qed.
