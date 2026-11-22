From Stdlib Require Import List.
From Stdlib Require Import Arith PeanoNat Lia.
Require Import SysF SemiU Reduction.

(* --- Auxiliary semi-unification substitution lemmas --- *)

Definition square_atom (n : nat) : term := arr (atom n) (atom n).

Fixpoint square_term (t : term) : term :=
  match t with
  | atom n => square_atom n
  | arr u v => arr (square_term u) (square_term v)
  end.

Lemma substitute_substitute : forall (f g : valuation) (t : term),
  substitute g (substitute f t) = substitute (fun n => substitute g (f n)) t.
Proof.
  intros f g t; induction t; simpl; [reflexivity|].
  now rewrite IHt1, IHt2.
Qed.

Lemma substitute_square_term : forall (f : valuation) (t : term),
  substitute f (square_term t) = substitute (fun n => arr (f n) (f n)) t.
Proof.
  intros f t; induction t; simpl; [reflexivity|].
  now rewrite IHt1, IHt2.
Qed.

Lemma substitute_ext : forall (f g : valuation) (t : term),
  (forall n, f n = g n) -> substitute f t = substitute g t.
Proof.
  intros f g t H; induction t; simpl; [apply H|now rewrite IHt1, IHt2].
Qed.

Lemma square_term_arr : forall (u : term), exists a b, square_term u = arr a b.
Proof.
  intros u; destruct u; simpl.
  - exists (atom n), (atom n); reflexivity.
  - exists (square_term u1), (square_term u2); reflexivity.
Qed.

Lemma square_term_inj : forall (t u : term), square_term t = square_term u -> t = u.
Proof.
  induction t as [n | t1 IH1 t2 IH2]; intros [m | u v] H; simpl in H.
  - injection H as H1 _. subst. reflexivity.
  - destruct (square_term_arr u) as [x [y Hxy]].
    injection H as H1 _. rewrite <- H1 in Hxy. discriminate.
  - destruct (square_term_arr t1) as [x [y Hxy]].
    injection H as H1 _. rewrite H1 in Hxy. discriminate.
  - injection H as H1 H2. subst.
    rewrite (IH1 u H1), (IH2 v H2). reflexivity.
Qed.


Lemma square_term_substitute : forall (f : valuation) (t : term),
  square_term (substitute f t) = substitute (fun n => square_term (f n)) t.
Proof.
  intros f t; induction t; simpl.
  - reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma square_term_as_subst : forall (t : term),
  square_term t = substitute (fun n => arr (atom n) (atom n)) t.
Proof.
  intros t; induction t; simpl; [reflexivity|now rewrite IHt1, IHt2].
Qed.


(* --- Shifting a solution (renaming all image atoms up by one) --- *)

Definition shift_term (t : term) : term := substitute (fun n => atom (S n)) t.
Definition shift_val (f : valuation) : valuation := fun n => shift_term (f n).
Definition up_val (g : valuation) : valuation :=
  fun n => match n with 0 => atom 0 | S k => shift_term (g k) end.

Lemma shift_term_substitute : forall (f : valuation) (t : term),
  shift_term (substitute f t) = substitute (shift_val f) t.
Proof.
  intros f t. unfold shift_term, shift_val. rewrite substitute_substitute. reflexivity.
Qed.

Lemma substitute_up_shift : forall (g : valuation) (t : term),
  substitute (up_val g) (shift_term t) = shift_term (substitute g t).
Proof.
  intros g t. unfold shift_term.
  rewrite substitute_substitute.
  rewrite substitute_substitute.
  apply substitute_ext; intro n.
  unfold up_val. simpl. unfold shift_term. reflexivity.
Qed.

Lemma shift_solution : forall (phi psi0 psi1 : valuation) (s t0 t1 : term),
  substitute psi0 (substitute phi s) = substitute phi t0 ->
  substitute psi1 (substitute phi s) = substitute phi t1 ->
  substitute (up_val psi0) (substitute (shift_val phi) s) = substitute (shift_val phi) t0 /\
  substitute (up_val psi1) (substitute (shift_val phi) s) = substitute (shift_val phi) t1.
Proof.
  intros phi psi0 psi1 s t0 t1 H0 H1. split.
  - rewrite <- (shift_term_substitute phi s).
    rewrite substitute_up_shift. rewrite H0.
    rewrite shift_term_substitute. reflexivity.
  - rewrite <- (shift_term_substitute phi s).
    rewrite substitute_up_shift. rewrite H1.
    rewrite shift_term_substitute. reflexivity.
Qed.


(* --- Basic System F typing of combinators --- *)

Lemma type_assignment_I : forall (Gamma : environment) (s : poly_type),
  type_assignment Gamma (pure_abs (pure_var 0)) (poly_arr s s).
Proof.
  intros Gamma s.
  apply type_assignment_abs.
  apply type_assignment_var. simpl. reflexivity.
Qed.

Lemma type_assignment_K : forall (Gamma : environment) (a b : poly_type),
  type_assignment Gamma (pure_abs (pure_abs (pure_var 1))) (poly_arr a (poly_arr b a)).
Proof.
  intros Gamma a b.
  apply type_assignment_abs.
  apply type_assignment_abs.
  apply type_assignment_var. simpl. reflexivity.
Qed.


(* --- Type-level renaming lemmas --- *)

Lemma ren_poly_type_ext : forall (T : poly_type) (xi xj : nat -> nat),
  (forall n, xi n = xj n) -> ren_poly_type xi T = ren_poly_type xj T.
Proof.
  induction T as [n | a IHa b IHb | c IHc]; intros xi xj H; simpl.
  - now rewrite H.
  - now rewrite (IHa xi xj H), (IHb xi xj H).
  - f_equal.
    assert (Hup : forall n, scons 0 (funcomp S xi) n = scons 0 (funcomp S xj) n).
    { intro k; destruct k; simpl; [reflexivity|]; unfold funcomp; simpl; now rewrite H. }
    rewrite (IHc _ _ Hup). reflexivity.
Qed.

Lemma ren_poly_type_comp : forall (T : poly_type) (xi xj : nat -> nat),
  ren_poly_type xi (ren_poly_type xj T) =
  ren_poly_type (fun n => xi (xj n)) T.
Proof.
  induction T as [n | a IHa b IHb | c IHc]; intros xi xj; simpl.
  - reflexivity.
  - now rewrite (IHa xi xj), (IHb xi xj).
  - f_equal.
    rewrite (IHc (scons 0 (funcomp S xi)) (scons 0 (funcomp S xj))).
    apply ren_poly_type_ext. intro n. destruct n; simpl; [reflexivity|].
    unfold funcomp; simpl; reflexivity.
Qed.

(* --- Bridge between term-level and type-level syntax --- *)

Fixpoint encode_term (t : term) : poly_type :=
  match t with
  | atom n => poly_var n
  | arr s t => poly_arr (encode_term s) (encode_term t)
  end.

Lemma encode_substitute : forall (f : valuation) (t : term),
  encode_term (substitute f t) =
  subst_poly_type (fun n => encode_term (f n)) (encode_term t).
Proof.
  intros f t; induction t; simpl.
  - reflexivity.
  - now rewrite IHt1, IHt2.
Qed.

Lemma encode_ren : forall (xi : nat -> nat) (t : term),
  encode_term (substitute (fun n => atom (xi n)) t) =
  ren_poly_type xi (encode_term t).
Proof.
  intros xi t; induction t; simpl.
  - reflexivity.
  - now rewrite IHt1, IHt2.
Qed.

Lemma encode_shift : forall (t : term),
  encode_term (shift_term t) = ren_poly_type S (encode_term t).
Proof.
  intro t. unfold shift_term. apply encode_ren.
Qed.

(* --- Facts about LU2SemiU used to analyse the problem --- *)

Lemma substitute_id : forall (t : term),
  substitute (fun n => atom n) t = t.
Proof.
  induction t; simpl; [reflexivity|now rewrite IHt1, IHt2].
Qed.

Lemma no_self_arrow : forall (psi : valuation) (x : term),
  x <> arr (substitute psi x) (substitute psi x).
Proof.
  intros psi x. induction x as [n | a IHa b IHb]; simpl in *.
  - discriminate.
  - intro H. injection H as H1 H2.
    assert (Heq : a = b).
    { transitivity (arr (substitute psi a) (substitute psi b)).
      - exact H1.
      - symmetry. exact H2. }
    subst b. apply (IHa). exact H1.
Qed.

Lemma occurs_unsolvable :
  ~ LU2SemiU (arr (atom 0) (atom 0), atom 0, atom 0).
Proof.
  intros [phi [psi0 [psi1 [H0 H1]]]].
  simpl in H0.
  apply (no_self_arrow psi0 (phi 0)).
  symmetry. exact H0.
Qed.

Lemma LU2SemiU_atom : forall (n : nat) (t0 t1 : term),
  LU2SemiU (atom n, t0, t1).
Proof.
  intros n t0 t1.
  exists (fun m => atom m).
  exists (fun m => match Nat.eq_dec m n with left _ => t0 | right _ => atom m end).
  exists (fun m => match Nat.eq_dec m n with left _ => t1 | right _ => atom m end).
  split.
  - rewrite substitute_id. simpl.
    destruct (Nat.eq_dec n n) as [e|e]; [|exfalso; apply e; reflexivity].
    rewrite substitute_id. reflexivity.
  - rewrite substitute_id. simpl.
    destruct (Nat.eq_dec n n) as [e|e]; [|exfalso; apply e; reflexivity].
    rewrite substitute_id. reflexivity.
Qed.

Lemma LU2SemiU_matching :
  forall p,
  LU2SemiU p <->
  (exists phi,
     (exists psi0, substitute psi0 (substitute phi (fst (fst p)))
                   = substitute phi (snd (fst p))) /\
     (exists psi1, substitute psi1 (substitute phi (fst (fst p)))
                   = substitute phi (snd p))).
Proof.
  intros [[s t0] t1]. simpl.
  split.
  - intros [phi [psi0 [psi1 [H0 H1]]]]. exists phi. split; eauto.
  - intros [phi [[psi0 H0] [psi1 H1]]]. exists phi, psi0, psi1. auto.
Qed.

Definition phi_arrow : valuation := fun n =>
  match n with
  | 0 => atom 0
  | 1 => atom 1
  | 2 => arr (atom 0) (atom 1)
  | S (S (S k)) => atom (S (S (S k)))
  end.

Lemma solvable_arrow_image :
  LU2SemiU (arr (atom 0) (atom 1), atom 2, atom 2).
Proof.
  exists phi_arrow, (fun n => atom n), (fun n => atom n).
  split.
  - unfold phi_arrow. cbn. reflexivity.
  - unfold phi_arrow. cbn. reflexivity.
Qed.

(* A solution cannot always be taken with phi mapping atoms to atoms. *)
Lemma no_renaming_solution :
  forall (g : nat -> nat) (psi0 : valuation),
    substitute psi0 (substitute (fun n => atom (g n)) (arr (atom 0) (atom 1)))
    <> substitute (fun n => atom (g n)) (atom 2).
Proof.
  intros g psi0. simpl. discriminate.
Qed.

(* --- The polymorphic escape in the supplied System F rules --- *)

Lemma type_assignment_xx :
  type_assignment (@nil poly_type)
    (pure_abs (pure_app (pure_var 0) (pure_var 0)))
    (poly_arr (poly_abs (poly_var 0)) (poly_var 1)).
Proof.
  refine (@type_assignment_abs nil
            (pure_app (pure_var 0) (pure_var 0))
            (poly_abs (poly_var 0)) (poly_var 1) _).
  refine (@type_assignment_app (poly_abs (poly_var 0) :: nil)
            (pure_var 0) (pure_var 0)
            (poly_abs (poly_var 0)) (poly_var 1) _ _).
  - refine (@type_assignment_inst (poly_abs (poly_var 0) :: nil)
              (pure_var 0) (poly_var 0)
              (poly_arr (poly_abs (poly_var 0)) (poly_var 1)) _).
    apply type_assignment_var. simpl. reflexivity.
  - apply type_assignment_var. simpl. reflexivity.
Qed.

Inductive app_only : pure_term -> Prop :=
| app_only_var (x : nat) : app_only (pure_var x)
| app_only_app (M N : pure_term) : app_only M -> app_only N -> app_only (pure_app M N).

Fixpoint pvar_bound (M : pure_term) : nat :=
  match M with
  | pure_var x => S x
  | pure_app M N => Nat.max (pvar_bound M) (pvar_bound N)
  | pure_abs M => pvar_bound M
  end.

Lemma app_only_typable_aux :
  forall (M : pure_term), app_only M ->
  forall (Gamma : environment) (tau : poly_type) (n : nat),
    pvar_bound M <= n ->
    (forall x, x < n -> nth_error Gamma x = Some (poly_abs (poly_var 0))) ->
    type_assignment Gamma M tau.
Proof.
  induction 1 as [x | M N HM IHm HN IHn]; intros Gamma tau n Hb Hl.
  - refine (@type_assignment_inst Gamma (pure_var x) (poly_var 0) tau _).
    apply type_assignment_var.
    apply Hl. unfold pvar_bound in Hb. lia.
  - simpl in Hb.
    assert (Hb1 : pvar_bound M <= n) by (eapply Nat.le_trans; [apply Nat.le_max_l | exact Hb]).
    assert (Hb2 : pvar_bound N <= n) by (eapply Nat.le_trans; [apply Nat.le_max_r | exact Hb]).
    refine (@type_assignment_app Gamma M N tau tau _ _).
    + apply (IHm Gamma (poly_arr tau tau) n Hb1 Hl).
    + apply (IHn Gamma tau n Hb2 Hl).
Qed.

Lemma app_only_example : forall tau,
  type_assignment (repeat (poly_abs (poly_var 0)) 3)
    (pure_app (pure_app (pure_var 0) (pure_var 1)) (pure_var 2)) tau.
Proof.
  intros tau.
  refine (@app_only_typable_aux _ _ (repeat (poly_abs (poly_var 0)) 3) tau 3 _ _).
  - apply app_only_app.
    + apply app_only_app; constructor.
    + constructor.
  - simpl. lia.
  - intros x Hx.
    destruct x as [|[|[|x]]]; simpl in *; try reflexivity; lia.
Qed.

(* --- square_term does not preserve LU2SemiU solvability --- *)

Definition t_ex : term := arr (atom 0) (arr (atom 0) (atom 0)).

Lemma original_ex_solvable : LU2SemiU (atom 1, t_ex, t_ex).
Proof.
  exists (fun n => atom n).
  exists (fun n => match Nat.eq_dec n 1 with left _ => t_ex | right _ => atom n end).
  exists (fun n => match Nat.eq_dec n 1 with left _ => t_ex | right _ => atom n end).
  split.
  - rewrite substitute_id. unfold t_ex. simpl.
    destruct (Nat.eq_dec 1 1) as [e|e].
    + reflexivity.
    + exfalso. apply e. reflexivity.
  - rewrite substitute_id. unfold t_ex. simpl.
    destruct (Nat.eq_dec 1 1) as [e|e].
    + reflexivity.
    + exfalso. apply e. reflexivity.
Qed.

Lemma squared_ex_unsolvable :
  ~ LU2SemiU (square_term (atom 1), square_term t_ex, square_term t_ex).
Proof.
  intros [phi [psi0 [psi1 [H0 _]]]].
  unfold square_term, square_atom, t_ex in H0. simpl in H0.
  injection H0 as H1 H2.
  assert (Hbad : phi 0 = arr (phi 0) (phi 0)).
  { injection (eq_trans (eq_sym H1) H2) as H3 _. exact H3. }
  apply (no_self_arrow (fun n => atom n) (phi 0)).
  rewrite substitute_id. exact Hbad.
Qed.

(* --- Environment insertion and term lifting --- *)

Fixpoint insert_env (k : nat) (X : poly_type) (Gamma : environment) : environment :=
  match k with
  | 0 => X :: Gamma
  | S k' =>
      match Gamma with
      | nil => X :: nil
      | Y :: Gamma' => Y :: insert_env k' X Gamma'
      end
  end.

Fixpoint lift (k : nat) (M : pure_term) : pure_term :=
  match M with
  | pure_var n => pure_var (if n <? k then n else S n)
  | pure_app M N => pure_app (lift k M) (lift k N)
  | pure_abs M => pure_abs (lift (S k) M)
  end.

Lemma nth_error_insert_lt :
  forall (k : nat) (X : poly_type) (Gamma : environment) (x : nat),
    x < length Gamma -> x < k ->
    nth_error (insert_env k X Gamma) x = nth_error Gamma x.
Proof.
  induction k as [|k IH]; intros X Gamma x Hlen Hlt.
  - lia.
  - destruct Gamma as [|Y Gamma']; simpl in *.
    + lia.
    + destruct x as [|x].
      * reflexivity.
      * simpl. apply IH; [simpl in Hlen; lia | lia].
Qed.

Lemma nth_error_insert_ge :
  forall (k : nat) (X : poly_type) (Gamma : environment) (x : nat),
    x < length Gamma -> k <= x ->
    nth_error (insert_env k X Gamma) (S x) = nth_error Gamma x.
Proof.
  induction k as [|k IH]; intros X Gamma x Hlen Hge.
  - simpl. reflexivity.
  - destruct Gamma as [|Y Gamma']; simpl in *.
    + lia.
    + destruct x as [|x].
      * lia.
      * simpl. apply IH; [simpl in Hlen; lia | lia].
Qed.

Lemma map_insert_env :
  forall (k : nat) (X : poly_type) (Gamma : environment),
    map (ren_poly_type S) (insert_env k X Gamma) =
    insert_env k (ren_poly_type S X) (map (ren_poly_type S) Gamma).
Proof.
  induction k as [|k IH]; intros X Gamma; simpl.
  - reflexivity.
  - destruct Gamma as [|Y Gamma']; simpl.
    + reflexivity.
    + now rewrite IH.
Qed.

Lemma type_assignment_lift :
  forall (Gamma : environment) (M : pure_term) (tau : poly_type),
    type_assignment Gamma M tau ->
    forall (k : nat) (X : poly_type),
      type_assignment (insert_env k X Gamma) (lift k M) tau.
Proof.
  intros Gamma M tau H. induction H; intros k X; simpl.
  - apply type_assignment_var.
    destruct (x <? k) eqn:E.
    + apply Nat.ltb_lt in E.
      rewrite (nth_error_insert_lt k X Gamma x); [exact H | | exact E].
      apply nth_error_Some. rewrite H. discriminate.
    + apply Nat.ltb_ge in E.
      rewrite (nth_error_insert_ge k X Gamma x); [exact H | | exact E].
      apply nth_error_Some. rewrite H. discriminate.
  - eapply type_assignment_app; [apply IHtype_assignment1 | apply IHtype_assignment2].
  - apply type_assignment_abs.
    specialize (IHtype_assignment (S k) X).
    exact IHtype_assignment.
  - apply type_assignment_inst. apply IHtype_assignment.
  - apply type_assignment_gen.
    specialize (IHtype_assignment k (ren_poly_type S X)).
    rewrite map_insert_env.
    exact IHtype_assignment.
Qed.

(* --- A gadget whose type is forced to be the arrow of two subterm types --- *)

Definition gadget (u v : pure_term) : pure_term :=
  pure_app
    (pure_abs (pure_app (pure_abs (pure_var 1))
                        (pure_app (pure_var 0) (lift 0 u))))
    (pure_abs (lift 0 v)).

Lemma type_assignment_gadget :
  forall (Gamma : environment) (u v : pure_term) (A B : poly_type),
    type_assignment Gamma u A ->
    type_assignment Gamma v B ->
    type_assignment Gamma (gadget u v) (poly_arr A B).
Proof.
  intros Gamma u v A B Hu Hv. unfold gadget.
  assert (Harg : type_assignment Gamma (pure_abs (lift 0 v)) (poly_arr A B)).
  { apply type_assignment_abs.
    exact (type_assignment_lift Gamma v B Hv 0 A). }
  assert (Hfun :
    type_assignment Gamma
      (pure_abs (pure_app (pure_abs (pure_var 1))
                          (pure_app (pure_var 0) (lift 0 u))))
      (poly_arr (poly_arr A B) (poly_arr A B))).
  { apply type_assignment_abs.
    simpl.
    refine (@type_assignment_app ((poly_arr A B) :: Gamma)
              (pure_abs (pure_var 1))
              (pure_app (pure_var 0) (lift 0 u))
              B (poly_arr A B) _ _).
    - apply type_assignment_abs.
      apply type_assignment_var. simpl. reflexivity.
    - refine (@type_assignment_app ((poly_arr A B) :: Gamma)
                (pure_var 0) (lift 0 u) A B _ _).
      + apply type_assignment_var. simpl. reflexivity.
      + exact (type_assignment_lift Gamma u A Hu 0 (poly_arr A B)).
  }
  refine (@type_assignment_app Gamma
            (pure_abs (pure_app (pure_abs (pure_var 1))
                                (pure_app (pure_var 0) (lift 0 u))))
            (pure_abs (lift 0 v))
            (poly_arr A B) (poly_arr A B) _ _).
  - exact Hfun.
  - exact Harg.
Qed.

(* --- Encoding semi-unification terms as System F types via the gadget --- *)

Fixpoint atoms (u : term) : list nat :=
  match u with
  | atom n => n :: nil
  | arr u v => atoms u ++ atoms v
  end.

Fixpoint enc (T : nat -> poly_type) (u : term) : poly_type :=
  match u with
  | atom n => T n
  | arr u v => poly_arr (enc T u) (enc T v)
  end.

Fixpoint E (u : term) : pure_term :=
  match u with
  | atom n => pure_var n
  | arr u v => gadget (E u) (E v)
  end.

Lemma type_assignment_E :
  forall (Gamma : environment) (u : term) (T : nat -> poly_type),
    (forall n, In n (atoms u) -> nth_error Gamma n = Some (T n)) ->
    type_assignment Gamma (E u) (enc T u).
Proof.
  intros Gamma u. induction u as [n | u IHu v IHv]; intros T H.
  - simpl. apply type_assignment_var. apply H. simpl. auto.
  - simpl. apply type_assignment_gadget.
    + apply IHu. intros k Hk. apply H. apply in_app_iff. left. exact Hk.
    + apply IHv. intros k Hk. apply H. apply in_app_iff. right. exact Hk.
Qed.

Definition T_of (Gamma : environment) (n : nat) : poly_type :=
  match nth_error Gamma n with Some t => t | None => poly_var n end.

Lemma type_assignment_E_env :
  forall (Gamma : environment) (u : term),
    (forall n, In n (atoms u) -> n < length Gamma) ->
    type_assignment Gamma (E u) (enc (T_of Gamma) u).
Proof.
  intros Gamma u H.
  apply type_assignment_E.
  intros n Hn.
  unfold T_of.
  destruct (nth_error Gamma n) as [t|] eqn:E'.
  - reflexivity.
  - apply nth_error_None in E'. exfalso. apply (Nat.lt_irrefl n).
    eapply Nat.lt_le_trans.
    + apply H. exact Hn.
    + exact E'.
Qed.

Lemma type_assignment_E_bottom :
  forall (Gamma : environment) (T : nat -> poly_type) (u : term),
    (forall n, In n (atoms u) -> nth_error Gamma n = Some (poly_abs (poly_var 0))) ->
    type_assignment Gamma (E u) (enc T u).
Proof.
  intros Gamma T u. induction u as [n | u IHu v IHv]; intros H.
  - simpl.
    refine (@type_assignment_inst Gamma (pure_var n) (poly_var 0) (T n) _).
    apply type_assignment_var. apply H. simpl. auto.
  - simpl. apply type_assignment_gadget.
    + apply IHu. intros k Hk. apply H. apply in_app_iff. left. exact Hk.
    + apply IHv. intros k Hk. apply H. apply in_app_iff. right. exact Hk.
Qed.

Lemma bottom_insert :
  forall (k : nat) (X : poly_type) (Gamma : environment) (n : nat),
    nth_error Gamma n = Some (poly_abs (poly_var 0)) ->
    nth_error (insert_env k X Gamma) (if n <? k then n else S n) =
      Some (poly_abs (poly_var 0)).
Proof.
  intros k X Gamma n H.
  destruct (n <? k) eqn:E.
  - apply Nat.ltb_lt in E.
    rewrite nth_error_insert_lt; [exact H | | exact E].
    apply nth_error_Some. rewrite H. discriminate.
  - apply Nat.ltb_ge in E.
    rewrite nth_error_insert_ge; [exact H | | exact E].
    apply nth_error_Some. rewrite H. discriminate.
Qed.

(* --- Instantiation of bottom-typed variables and a type-equality test --- *)

Lemma inst_bottom_any :
  forall (Gamma : environment) (x : nat) (T : poly_type),
    nth_error Gamma x = Some (poly_abs (poly_var 0)) ->
    type_assignment Gamma (pure_var x) T.
Proof.
  intros Gamma x T H.
  change (type_assignment Gamma (pure_var x)
            (subst_poly_type (scons T poly_var) (poly_var 0))).
  apply type_assignment_inst.
  apply type_assignment_var. exact H.
Qed.

Definition eqtest (u v : pure_term) : pure_term :=
  pure_app
    (pure_abs (pure_app (gadget (lift 0 u) (pure_var 0)) (pure_var 0)))
    v.

Lemma eqtest_sound :
  forall (Gamma : environment) (u v : pure_term) (B : poly_type),
    type_assignment Gamma u B ->
    type_assignment Gamma v B ->
    type_assignment Gamma (eqtest u v) B.
Proof.
  intros Gamma u v B Hu Hv. unfold eqtest.
  eapply type_assignment_app.
  - eapply type_assignment_abs.
    eapply type_assignment_app.
    + apply type_assignment_gadget.
      * apply (type_assignment_lift Gamma u B Hu 0 B).
      * apply type_assignment_var. cbn. reflexivity.
    + apply type_assignment_var. cbn. reflexivity.
  - exact Hv.
Qed.


(* --- Canonical inversion of typing derivations --- *)

(* A closure relation describing all types derivable for a variable,
   tracking the environment (because gen shifts it). *)
Inductive vtype : environment -> nat -> poly_type -> poly_type -> Prop :=
| vtype_var : forall (Gamma : environment) (x : nat) (T : poly_type),
    nth_error Gamma x = Some T -> vtype Gamma x T T
| vtype_gen : forall (Gamma : environment) (x : nat) (T : poly_type) (s : poly_type),
    nth_error Gamma x = Some T ->
    vtype (map (ren_poly_type S) Gamma) x (ren_poly_type S T) s ->
    vtype Gamma x T (poly_abs s)
| vtype_inst : forall (Gamma : environment) (x : nat) (T U V : poly_type),
    vtype Gamma x T (poly_abs U) ->
    vtype Gamma x T (subst_poly_type (scons V poly_var) U).

Lemma vtype_entry :
  forall (Gamma : environment) (x : nat) (T C : poly_type),
    vtype Gamma x T C -> nth_error Gamma x = Some T.
Proof. intros Gamma x T C H. induction H; assumption. Qed.

Lemma vtype_sound :
  forall (Gamma : environment) (x : nat) (T C : poly_type),
    vtype Gamma x T C -> type_assignment Gamma (pure_var x) C.
Proof.
  intros Gamma x T C H. induction H.
  - apply type_assignment_var. exact H.
  - apply type_assignment_gen. exact IHvtype.
  - eapply type_assignment_inst. exact IHvtype.
Qed.

Lemma vtype_complete :
  forall (Gamma : environment) (M : pure_term) (C : poly_type),
    type_assignment Gamma M C ->
    forall (x : nat), M = pure_var x ->
    exists T, vtype Gamma x T C.
Proof.
  intros Gamma M C H. induction H; intros y Heq.
  - injection Heq as Hx. subst. exists t. apply vtype_var. exact H.
  - simpl in Heq. discriminate.
  - simpl in Heq. discriminate.
  - (* inst *) apply IHtype_assignment in Heq. destruct Heq as [T HT].
    exists T. eapply vtype_inst. exact HT.
  - (* gen *) apply IHtype_assignment in Heq. destruct Heq as [T' HT'].
    pose proof (vtype_entry _ _ _ _ HT') as Hentry.
    rewrite nth_error_map in Hentry.
    destruct (nth_error Gamma y) as [T|] eqn:E; simpl in Hentry; try discriminate.
    injection Hentry as HeqT.
    exists T. rewrite <- HeqT in HT'.
    eapply vtype_gen; [exact E | exact HT'].
Qed.

(* Every typing of a variable is exactly an instance of this closure. *)
Theorem type_assignment_var_iff :
  forall (Gamma : environment) (x : nat) (C : poly_type),
    type_assignment Gamma (pure_var x) C <->
    exists T, nth_error Gamma x = Some T /\ vtype Gamma x T C.
Proof.
  intros Gamma x C. split.
  - intro H. destruct (vtype_complete Gamma (pure_var x) C H x eq_refl) as [T HT].
    exists T. split; [apply (vtype_entry _ _ _ _ HT)|exact HT].
  - intros [T [_ HT]]. exact (vtype_sound Gamma x T C HT).
Qed.

(* Inversion for application-shaped terms: every type of pure_app M N is
   either the result of the application rule (with the actual subterm typings)
   or a gen/inst wrapper around such a type. *)
Inductive apptype : environment -> pure_term -> pure_term -> poly_type -> Prop :=
| apptype_app : forall (Gamma : environment) (M N : pure_term) (A C : poly_type),
    type_assignment Gamma M (poly_arr A C) ->
    type_assignment Gamma N A ->
    apptype Gamma M N C
| apptype_gen : forall (Gamma : environment) (M N : pure_term) (s : poly_type),
    apptype (map (ren_poly_type S) Gamma) M N s ->
    apptype Gamma M N (poly_abs s)
| apptype_inst : forall (Gamma : environment) (M N : pure_term) (U V : poly_type),
    apptype Gamma M N (poly_abs U) ->
    apptype Gamma M N (subst_poly_type (scons V poly_var) U).

Lemma apptype_sound :
  forall (Gamma : environment) (M N : pure_term) (C : poly_type),
    apptype Gamma M N C -> type_assignment Gamma (pure_app M N) C.
Proof.
  intros Gamma M N C H. induction H.
  - eapply type_assignment_app; eassumption.
  - apply type_assignment_gen. exact IHapptype.
  - eapply type_assignment_inst. exact IHapptype.
Qed.

Lemma apptype_complete :
  forall (Gamma : environment) (M N : pure_term) (C : poly_type),
    type_assignment Gamma (pure_app M N) C -> apptype Gamma M N C.
Proof.
  intros Gamma M N C H. remember (pure_app M N) as T eqn:E.
  revert M N E. induction H; intros M0 N0 E.
  - simpl in E. discriminate.
  - injection E as -> ->. eapply apptype_app; eassumption.
  - simpl in E. discriminate.
  - (* inst *) eapply apptype_inst. eapply IHtype_assignment. exact E.
  - (* gen *) eapply apptype_gen. eapply IHtype_assignment. exact E.
Qed.

(* Inversion for abstraction-shaped terms.  Here abstype Gamma M C means
   Gamma |- pure_abs M : C. *)
Inductive abstype : environment -> pure_term -> poly_type -> Prop :=
| abstype_abs : forall (Gamma : environment) (M : pure_term) (A B : poly_type),
    type_assignment (A :: Gamma) M B ->
    abstype Gamma M (poly_arr A B)
| abstype_gen : forall (Gamma : environment) (M : pure_term) (s : poly_type),
    abstype (map (ren_poly_type S) Gamma) M s ->
    abstype Gamma M (poly_abs s)
| abstype_inst : forall (Gamma : environment) (M : pure_term) (U V : poly_type),
    abstype Gamma M (poly_abs U) ->
    abstype Gamma M (subst_poly_type (scons V poly_var) U).

Lemma abstype_sound :
  forall (Gamma : environment) (M : pure_term) (C : poly_type),
    abstype Gamma M C -> type_assignment Gamma (pure_abs M) C.
Proof.
  intros Gamma M C H. induction H.
  - apply type_assignment_abs. exact H.
  - apply type_assignment_gen. exact IHabstype.
  - eapply type_assignment_inst. exact IHabstype.
Qed.

Lemma abstype_complete :
  forall (Gamma : environment) (M : pure_term) (C : poly_type),
    type_assignment Gamma (pure_abs M) C -> abstype Gamma M C.
Proof.
  intros Gamma M C H. remember (pure_abs M) as T eqn:E.
  revert M E. induction H; intros M0 E.
  - simpl in E. discriminate.
  - simpl in E. discriminate.
  - injection E as ->. eapply abstype_abs. exact H.
  - (* inst *) eapply abstype_inst. eapply IHtype_assignment. exact E.
  - (* gen *) eapply abstype_gen. eapply IHtype_assignment. exact E.
Qed.


(* --- Environment insertion / lifting inversion --- *)

(* Free variables, relative to a binder depth k. *)
Fixpoint fv (k : nat) (M : pure_term) : list nat :=
  match M with
  | pure_var n => if n <? k then nil else (n - k) :: nil
  | pure_app M N => fv k M ++ fv k N
  | pure_abs M => fv (S k) M
  end.

Definition fv_ok (Gamma : environment) (M : pure_term) : Prop :=
  forall n, In n (fv 0 M) -> n < length Gamma.

Lemma fv_S_relation :
  forall (M : pure_term) (k : nat) (x : nat),
    In x (fv k M) -> x = 0 \/ (exists y, In y (fv (S k) M) /\ x = S y).
Proof.
  induction M as [n | M IHM N IHN | M IHM]; intros k x Hx; simpl in Hx.
  - destruct (n <? k) eqn:E; [contradiction|].
    cbn in Hx. destruct Hx as [Hx|[]].
    assert (Hx' : x = n - k) by lia. rewrite Hx'.
    destruct (Nat.eq_dec n k) as [->|Hne].
    + left; lia.
    + right. exists (n - S k). split.
      * assert (E2 : (n <? S k) = false).
        { apply Nat.ltb_ge. apply Nat.ltb_ge in E. lia. }
        simpl. rewrite E2. simpl. left. reflexivity.
      * apply Nat.ltb_ge in E. lia.
  - apply in_app_iff in Hx. destruct Hx as [Hx|Hx].
    + apply IHM in Hx. destruct Hx as [->|[y [Hy Hyx]]].
      * left; auto.
      * right. exists y. split; [|auto]. apply in_app_iff. left; auto.
    + apply IHN in Hx. destruct Hx as [->|[y [Hy Hyx]]].
      * left; auto.
      * right. exists y. split; [|auto]. apply in_app_iff. right; auto.
  - apply IHM in Hx. exact Hx.
Qed.

Lemma fv_ok_abs :
  forall (Gamma : environment) (A : poly_type) (M : pure_term),
    fv_ok Gamma (pure_abs M) -> fv_ok (A :: Gamma) M.
Proof.
  intros Gamma A M Hok n Hn. unfold fv_ok in Hok. simpl in Hn.
  destruct (fv_S_relation M 0 n Hn) as [->|[y [Hy Hyx]]].
  - simpl. lia.
  - subst n. pose proof (Hok y Hy) as Hlt. simpl. lia.
Qed.

Lemma vtype_uninsert_gen :
  forall (D : environment) (m : nat) (T C : poly_type),
    vtype D m T C ->
    forall (k : nat) (X : poly_type) (Gamma : environment) (n : nat),
      D = insert_env k X Gamma ->
      m = (if n <? k then n else S n) ->
      n < length Gamma ->
      vtype Gamma n T C.
Proof.
  intros D m T C Hv. induction Hv; intros k0 X0 Gamma0 n0 ED Em Hlen0.
  - (* vtype_var *)
    apply vtype_var.
    rewrite ED, Em in H.
    destruct (n0 <? k0) eqn:E.
    + apply Nat.ltb_lt in E.
      rewrite nth_error_insert_lt in H; [exact H | exact Hlen0 | exact E].
    + apply Nat.ltb_ge in E.
      rewrite nth_error_insert_ge in H; [exact H | exact Hlen0 | exact E].
  - (* vtype_gen *)
    apply vtype_gen.
    + rewrite ED, Em in H.
      destruct (n0 <? k0) eqn:E.
      * apply Nat.ltb_lt in E.
        rewrite nth_error_insert_lt in H; [exact H | exact Hlen0 | exact E].
      * apply Nat.ltb_ge in E.
        rewrite nth_error_insert_ge in H; [exact H | exact Hlen0 | exact E].
    + apply IHHv with (k := k0) (X := ren_poly_type S X0)
                       (Gamma := map (ren_poly_type S) Gamma0) (n := n0).
      * rewrite ED, map_insert_env. reflexivity.
      * exact Em.
      * simpl. rewrite length_map. exact Hlen0.
  - (* vtype_inst *) eapply vtype_inst.
    apply IHHv with (k := k0) (X := X0) (Gamma := Gamma0) (n := n0).
    + exact ED.
    + exact Em.
    + exact Hlen0.
Qed.

Lemma vtype_uninsert :
  forall (k : nat) (X : poly_type) (Gamma : environment) (n : nat)
         (T C : poly_type),
    n < length Gamma ->
    vtype (insert_env k X Gamma) (if n <? k then n else S n) T C ->
    vtype Gamma n T C.
Proof.
  intros k X Gamma n T C Hlen Hv.
  exact (vtype_uninsert_gen (insert_env k X Gamma)
           (if n <? k then n else S n) T C Hv k X Gamma n eq_refl eq_refl Hlen).
Qed.

Lemma fv_ok_app_l :
  forall (Gamma : environment) (M N : pure_term),
    fv_ok Gamma (pure_app M N) -> fv_ok Gamma M.
Proof.
  intros Gamma M N Hok n Hn. apply Hok.
  simpl. apply in_app_iff. left. exact Hn.
Qed.

Lemma fv_ok_app_r :
  forall (Gamma : environment) (M N : pure_term),
    fv_ok Gamma (pure_app M N) -> fv_ok Gamma N.
Proof.
  intros Gamma M N Hok n Hn. apply Hok.
  simpl. apply in_app_iff. right. exact Hn.
Qed.

Lemma fv_ok_map :
  forall (Gamma : environment) (M : pure_term),
    fv_ok Gamma M -> fv_ok (map (ren_poly_type S) Gamma) M.
Proof.
  intros Gamma M Hok n Hn. rewrite length_map. apply Hok. exact Hn.
Qed.

Lemma apptype_lift_inv_gen :
  forall (D : environment) (LM LN : pure_term) (C : poly_type),
    apptype D LM LN C ->
    forall (k : nat) (X : poly_type) (Gamma : environment) (M N : pure_term),
      LM = lift k M ->
      LN = lift k N ->
      D = insert_env k X Gamma ->
      fv_ok Gamma (pure_app M N) ->
      (forall (k : nat) (X : poly_type) (Gamma : environment) (B : poly_type),
          fv_ok Gamma M ->
          type_assignment (insert_env k X Gamma) (lift k M) B ->
          type_assignment Gamma M B) ->
      (forall (k : nat) (X : poly_type) (Gamma : environment) (B : poly_type),
          fv_ok Gamma N ->
          type_assignment (insert_env k X Gamma) (lift k N) B ->
          type_assignment Gamma N B) ->
      type_assignment Gamma (pure_app M N) C.
Proof.
  intros D LM LN C HAT. induction HAT;
    intros k0 X0 Gamma0 M0 N0 ELM ELN ED Hok HM HN.
  - (* apptype_app *)
    eapply type_assignment_app.
    + specialize (HM k0 X0 Gamma0 (poly_arr A C)).
      apply HM.
      * apply (fv_ok_app_l Gamma0 M0 N0). exact Hok.
      * rewrite <- ELM, <- ED. exact H.
    + specialize (HN k0 X0 Gamma0 A).
      apply HN.
      * apply (fv_ok_app_r Gamma0 M0 N0). exact Hok.
      * rewrite <- ELN, <- ED. exact H0.
  - (* apptype_gen *)
    apply type_assignment_gen.
    apply IHHAT with (k := k0) (Gamma := map (ren_poly_type S) Gamma0)
                     (X := ren_poly_type S X0) (M := M0) (N := N0).
    + exact ELM.
    + exact ELN.
    + rewrite ED, map_insert_env. reflexivity.
    + apply fv_ok_map. exact Hok.
    + exact HM.
    + exact HN.
  - (* apptype_inst *)
    eapply type_assignment_inst.
    apply IHHAT with (k := k0) (X := X0) (Gamma := Gamma0) (M := M0) (N := N0).
    + exact ELM.
    + exact ELN.
    + exact ED.
    + exact Hok.
    + exact HM.
    + exact HN.
Qed.

Lemma abstype_lift_inv_gen :
  forall (D : environment) (LM : pure_term) (C : poly_type),
    abstype D LM C ->
    forall (k : nat) (X : poly_type) (Gamma : environment) (M : pure_term),
      LM = lift (S k) M ->
      D = insert_env k X Gamma ->
      fv_ok Gamma (pure_abs M) ->
      (forall (k : nat) (X : poly_type) (Gamma : environment) (B : poly_type),
          fv_ok Gamma M ->
          type_assignment (insert_env k X Gamma) (lift k M) B ->
          type_assignment Gamma M B) ->
      type_assignment Gamma (pure_abs M) C.
Proof.
  intros D LM C HAT. induction HAT;
    intros k0 X0 Gamma0 M0 ELM ED Hok HM.
  - (* abstype_abs *)
    apply type_assignment_abs.
    specialize (HM (S k0) X0 (A :: Gamma0) B).
    apply HM.
    + apply fv_ok_abs. exact Hok.
    + cbn. rewrite <- ELM, <- ED. exact H.
  - (* abstype_gen *)
    apply type_assignment_gen.
    apply IHHAT with (k := k0) (Gamma := map (ren_poly_type S) Gamma0)
                     (X := ren_poly_type S X0) (M := M0).
    + exact ELM.
    + rewrite ED, map_insert_env. reflexivity.
    + apply fv_ok_map. exact Hok.
    + exact HM.
  - (* abstype_inst *)
    eapply type_assignment_inst.
    apply IHHAT with (k := k0) (X := X0) (Gamma := Gamma0) (M := M0).
    + exact ELM.
    + exact ED.
    + exact Hok.
    + exact HM.
Qed.

Lemma type_assignment_lift_inv :
  forall (M : pure_term),
    forall (k : nat) (X : poly_type) (Gamma : environment) (B : poly_type),
      fv_ok Gamma M ->
      type_assignment (insert_env k X Gamma) (lift k M) B ->
      type_assignment Gamma M B.
Proof.
  induction M as [n | M IHM N IHN | M IHM];
    intros k X Gamma B Hok Hty.
  - (* var *) simpl in Hty.
    destruct (vtype_complete (insert_env k X Gamma)
                (pure_var (if n <? k then n else S n)) B Hty
                (if n <? k then n else S n) eq_refl) as [T HT].
    apply (vtype_sound Gamma n T B).
    apply vtype_uninsert with (k := k) (X := X) (n := n) (T := T).
    + unfold fv_ok in Hok.
      apply Hok.
      change (In n (if n <? 0 then nil else (n - 0) :: nil)).
      destruct (n <? 0) eqn:E.
      * apply Nat.ltb_lt in E. lia.
      * simpl. left. lia.
    + exact HT.
  - (* app *) simpl in Hty.
    eapply apptype_lift_inv_gen with (D := insert_env k X Gamma)
            (LM := lift k M) (LN := lift k N) (C := B).
    + apply apptype_complete. exact Hty.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + exact Hok.
    + exact IHM.
    + exact IHN.
  - (* abs *) simpl in Hty.
    eapply abstype_lift_inv_gen with (D := insert_env k X Gamma)
            (LM := lift (S k) M) (C := B).
    + apply abstype_complete. exact Hty.
    + reflexivity.
    + reflexivity.
    + exact Hok.
    + exact IHM.
Qed.


(* --- Types of the gadget argument lambda --- *)

(* Complete characterization of the types of  abs (lift 0 v),
   the argument-lambda used by the gadget. *)
Inductive codom : environment -> pure_term -> poly_type -> Prop :=
| codom_arrow : forall (Gamma : environment) (v : pure_term) (A B : poly_type),
    fv_ok Gamma v ->
    type_assignment Gamma v B ->
    codom Gamma v (poly_arr A B)
| codom_gen : forall (Gamma : environment) (v : pure_term) (s : poly_type),
    codom (map (ren_poly_type S) Gamma) v s ->
    codom Gamma v (poly_abs s)
| codom_inst : forall (Gamma : environment) (v : pure_term) (U V : poly_type),
    codom Gamma v (poly_abs U) ->
    codom Gamma v (subst_poly_type (scons V poly_var) U).

Lemma codom_sound :
  forall (Gamma : environment) (v : pure_term) (C : poly_type),
    codom Gamma v C -> type_assignment Gamma (pure_abs (lift 0 v)) C.
Proof.
  intros Gamma v C H. induction H.
  - apply type_assignment_abs.
    change (type_assignment (insert_env 0 A Gamma) (lift 0 v) B).
    apply type_assignment_lift. exact H0.
  - apply type_assignment_gen. exact IHcodom.
  - eapply type_assignment_inst. exact IHcodom.
Qed.

Lemma codom_complete :
  forall (D : environment) (LM : pure_term) (C : poly_type),
    abstype D LM C ->
    forall (Gamma : environment) (v : pure_term),
      D = Gamma -> LM = lift 0 v -> fv_ok Gamma v -> codom Gamma v C.
Proof.
  intros D LM C HAT. induction HAT;
    intros Gamma0 v ED ELM Hok.
  - (* abstype_abs *)
    apply codom_arrow.
    + exact Hok.
    + apply (type_assignment_lift_inv v 0 A Gamma0 B Hok).
      rewrite <- ED, <- ELM. exact H.
  - (* abstype_gen *)
    apply codom_gen.
    apply IHHAT with (Gamma := map (ren_poly_type S) Gamma0) (v := v).
    + rewrite ED. reflexivity.
    + exact ELM.
    + apply fv_ok_map. exact Hok.
  - (* abstype_inst *)
    eapply codom_inst.
    apply IHHAT with (Gamma := Gamma0) (v := v).
    + exact ED.
    + exact ELM.
    + exact Hok.
Qed.

Theorem codom_iff :
  forall (Gamma : environment) (v : pure_term) (C : poly_type),
    fv_ok Gamma v ->
    (type_assignment Gamma (pure_abs (lift 0 v)) C <-> codom Gamma v C).
Proof.
  intros Gamma v C Hok. split.
  - intro H.
    apply codom_complete with (D := Gamma) (LM := lift 0 v).
    + apply abstype_complete. exact H.
    + reflexivity.
    + reflexivity.
    + exact Hok.
  - intro Hc. apply codom_sound. exact Hc.
Qed.


(* --- Complete gadget typing characterization --- *)

Inductive abvar : environment -> nat -> poly_type -> Prop :=
| abvar_core : forall (Gamma : environment) (x : nat) (A B : poly_type),
    type_assignment (A :: Gamma) (pure_var x) B ->
    abvar Gamma x (poly_arr A B)
| abvar_gen : forall (Gamma : environment) (x : nat) (s : poly_type),
    abvar (map (ren_poly_type S) Gamma) x s ->
    abvar Gamma x (poly_abs s)
| abvar_inst : forall (Gamma : environment) (x : nat) (U V : poly_type),
    abvar Gamma x (poly_abs U) ->
    abvar Gamma x (subst_poly_type (scons V poly_var) U).

Lemma abvar_sound :
  forall (Gamma : environment) (x : nat) (C : poly_type),
    abvar Gamma x C -> type_assignment Gamma (pure_abs (pure_var x)) C.
Proof.
  intros Gamma x C H. induction H.
  - apply type_assignment_abs. exact H.
  - apply type_assignment_gen. exact IHabvar.
  - eapply type_assignment_inst. exact IHabvar.
Qed.

Lemma abvar_complete :
  forall (D : environment) (LM : pure_term) (C : poly_type),
    abstype D LM C ->
    forall (Gamma : environment) (x : nat),
      D = Gamma -> LM = pure_var x -> abvar Gamma x C.
Proof.
  intros D LM C HAT. induction HAT;
    intros Gamma0 x0 ED ELM.
  - (* abstype_abs *) apply abvar_core.
    rewrite <- ED, <- ELM. exact H.
  - (* abstype_gen *) apply abvar_gen.
    apply IHHAT with (Gamma := map (ren_poly_type S) Gamma0) (x := x0).
    + rewrite ED. reflexivity.
    + exact ELM.
  - (* abstype_inst *) eapply abvar_inst.
    apply IHHAT with (Gamma := Gamma0) (x := x0); [exact ED|exact ELM].
Qed.

Theorem abvar_iff :
  forall (Gamma : environment) (x : nat) (C : poly_type),
    type_assignment Gamma (pure_abs (pure_var x)) C <-> abvar Gamma x C.
Proof.
  intros Gamma x C. split.
  - intro H.
    apply abvar_complete with (D := Gamma) (LM := pure_var x).
    + apply abstype_complete. exact H.
    + reflexivity.
    + reflexivity.
  - apply abvar_sound.
Qed.

Definition gadget_T1 : pure_term := pure_abs (pure_var 1).
Definition gadget_T2 (u : pure_term) : pure_term :=
  pure_app (pure_var 0) (lift 0 u).
Definition gadget_body (u : pure_term) : pure_term :=
  pure_app gadget_T1 (gadget_T2 u).
Definition gadget_fun (u : pure_term) : pure_term :=
  pure_abs (gadget_body u).
Definition gadget_arg (v : pure_term) : pure_term :=
  pure_abs (lift 0 v).

Lemma gadget_unfold :
  forall u v, gadget u v = pure_app (gadget_fun u) (gadget_arg v).
Proof. reflexivity. Qed.

Inductive functype : environment -> pure_term -> poly_type -> Prop :=
| functype_core : forall (Gamma : environment) (u : pure_term) (A C : poly_type),
    apptype (A :: Gamma) gadget_T1 (gadget_T2 u) C ->
    functype Gamma u (poly_arr A C)
| functype_gen : forall (Gamma : environment) (u : pure_term) (s : poly_type),
    functype (map (ren_poly_type S) Gamma) u s ->
    functype Gamma u (poly_abs s)
| functype_inst : forall (Gamma : environment) (u : pure_term) (U V : poly_type),
    functype Gamma u (poly_abs U) ->
    functype Gamma u (subst_poly_type (scons V poly_var) U).

Lemma functype_sound :
  forall (Gamma : environment) (u : pure_term) (C : poly_type),
    functype Gamma u C -> type_assignment Gamma (gadget_fun u) C.
Proof.
  intros Gamma u C H. induction H.
  - apply type_assignment_abs.
    apply apptype_sound. exact H.
  - apply type_assignment_gen. exact IHfunctype.
  - eapply type_assignment_inst. exact IHfunctype.
Qed.

Lemma functype_complete :
  forall (D : environment) (LM : pure_term) (C : poly_type),
    abstype D LM C ->
    forall (Gamma : environment) (u : pure_term),
      D = Gamma -> LM = gadget_body u -> functype Gamma u C.
Proof.
  intros D LM C HAT. induction HAT;
    intros Gamma0 u0 ED ELM.
  - (* abstype_abs *) apply functype_core.
    apply apptype_complete.
    change (type_assignment (A :: Gamma0) (gadget_body u0) B).
    rewrite <- ED, <- ELM. exact H.
  - (* abstype_gen *) apply functype_gen.
    apply IHHAT with (Gamma := map (ren_poly_type S) Gamma0) (u := u0).
    + rewrite ED. reflexivity.
    + exact ELM.
  - (* abstype_inst *) eapply functype_inst.
    apply IHHAT with (Gamma := Gamma0) (u := u0); [exact ED|exact ELM].
Qed.

Theorem functype_iff :
  forall (Gamma : environment) (u : pure_term) (C : poly_type),
    type_assignment Gamma (gadget_fun u) C <-> functype Gamma u C.
Proof.
  intros Gamma u C. split.
  - intro H.
    apply functype_complete with (D := Gamma) (LM := gadget_body u).
    + apply abstype_complete. exact H.
    + reflexivity.
    + reflexivity.
  - apply functype_sound.
Qed.

Inductive gadget_type : environment -> pure_term -> pure_term -> poly_type -> Prop :=
| gadget_type_core : forall (Gamma : environment) (u v : pure_term) (A C : poly_type),
    type_assignment Gamma (gadget_arg v) A ->
    functype Gamma u (poly_arr A C) ->
    gadget_type Gamma u v C
| gadget_type_gen : forall (Gamma : environment) (u v : pure_term) (s : poly_type),
    gadget_type (map (ren_poly_type S) Gamma) u v s ->
    gadget_type Gamma u v (poly_abs s)
| gadget_type_inst : forall (Gamma : environment) (u v : pure_term) (U V : poly_type),
    gadget_type Gamma u v (poly_abs U) ->
    gadget_type Gamma u v (subst_poly_type (scons V poly_var) U).

Lemma gadget_type_sound :
  forall (Gamma : environment) (u v : pure_term) (C : poly_type),
    gadget_type Gamma u v C -> type_assignment Gamma (gadget u v) C.
Proof.
  intros Gamma u v C H. induction H.
  - rewrite gadget_unfold.
    eapply type_assignment_app.
    + apply functype_sound. exact H0.
    + exact H.
  - apply type_assignment_gen. exact IHgadget_type.
  - eapply type_assignment_inst. exact IHgadget_type.
Qed.

Lemma apptype_gadget_complete :
  forall (D : environment) (LM LN : pure_term) (C : poly_type),
    apptype D LM LN C ->
    forall (Gamma : environment) (u v : pure_term),
      D = Gamma -> LM = gadget_fun u -> LN = gadget_arg v ->
      gadget_type Gamma u v C.
Proof.
  intros D LM LN C HAT. induction HAT;
    intros Gamma0 u0 v0 ED E1 E2.
  - (* apptype_app *)
    apply gadget_type_core with (A := A).
    + rewrite <- ED, <- E2. exact H0.
    + apply functype_complete with (D := Gamma0) (LM := gadget_body u0).
      * apply abstype_complete.
        change (type_assignment Gamma0 (gadget_fun u0) (poly_arr A C)).
        rewrite <- ED, <- E1. exact H.
      * reflexivity.
      * reflexivity.
  - (* apptype_gen *)
    apply gadget_type_gen.
    apply IHHAT with (Gamma := map (ren_poly_type S) Gamma0)
                     (u := u0) (v := v0).
    + rewrite ED. reflexivity.
    + exact E1.
    + exact E2.
  - (* apptype_inst *)
    apply gadget_type_inst.
    apply IHHAT with (Gamma := Gamma0) (u := u0) (v := v0).
    + exact ED. + exact E1. + exact E2.
Qed.

Theorem gadget_type_iff :
  forall (Gamma : environment) (u v : pure_term) (C : poly_type),
    type_assignment Gamma (gadget u v) C <-> gadget_type Gamma u v C.
Proof.
  intros Gamma u v C. split.
  - intro H. rewrite gadget_unfold in H.
    eapply apptype_gadget_complete.
    + apply apptype_complete. exact H.
    + reflexivity. + reflexivity. + reflexivity.
  - apply gadget_type_sound.
Qed.


(* --- Complete eqtest typing characterization --- *)

Definition eqtest_body (u : pure_term) : pure_term :=
  pure_app (gadget (lift 0 u) (pure_var 0)) (pure_var 0).
Definition eqtest_fun (u : pure_term) : pure_term :=
  pure_abs (eqtest_body u).

Lemma eqtest_unfold :
  forall u v, eqtest u v = pure_app (eqtest_fun u) v.
Proof. reflexivity. Qed.

Inductive eqfun_type : environment -> pure_term -> poly_type -> Prop :=
| eqfun_core : forall (Gamma : environment) (u : pure_term) (A C : poly_type),
    apptype (A :: Gamma) (gadget (lift 0 u) (pure_var 0)) (pure_var 0) C ->
    eqfun_type Gamma u (poly_arr A C)
| eqfun_gen : forall (Gamma : environment) (u : pure_term) (s : poly_type),
    eqfun_type (map (ren_poly_type S) Gamma) u s ->
    eqfun_type Gamma u (poly_abs s)
| eqfun_inst : forall (Gamma : environment) (u : pure_term) (U V : poly_type),
    eqfun_type Gamma u (poly_abs U) ->
    eqfun_type Gamma u (subst_poly_type (scons V poly_var) U).

Lemma eqfun_type_sound :
  forall (Gamma : environment) (u : pure_term) (C : poly_type),
    eqfun_type Gamma u C -> type_assignment Gamma (eqtest_fun u) C.
Proof.
  intros Gamma u C H. induction H.
  - apply type_assignment_abs. apply apptype_sound. exact H.
  - apply type_assignment_gen. exact IHeqfun_type.
  - eapply type_assignment_inst. exact IHeqfun_type.
Qed.

Lemma eqfun_type_complete :
  forall (D : environment) (LM : pure_term) (C : poly_type),
    abstype D LM C ->
    forall (Gamma : environment) (u : pure_term),
      D = Gamma -> LM = eqtest_body u -> eqfun_type Gamma u C.
Proof.
  intros D LM C HAT. induction HAT;
    intros Gamma0 u0 ED ELM.
  - apply eqfun_core. apply apptype_complete.
    change (type_assignment (A :: Gamma0) (eqtest_body u0) B).
    rewrite <- ED, <- ELM. exact H.
  - apply eqfun_gen.
    apply IHHAT with (Gamma := map (ren_poly_type S) Gamma0) (u := u0).
    + rewrite ED. reflexivity.
    + exact ELM.
  - eapply eqfun_inst.
    apply IHHAT with (Gamma := Gamma0) (u := u0); [exact ED|exact ELM].
Qed.

Theorem eqfun_type_iff :
  forall (Gamma : environment) (u : pure_term) (C : poly_type),
    type_assignment Gamma (eqtest_fun u) C <-> eqfun_type Gamma u C.
Proof.
  intros Gamma u C. split.
  - intro H.
    apply eqfun_type_complete with (D := Gamma) (LM := eqtest_body u).
    + apply abstype_complete. exact H.
    + reflexivity.
    + reflexivity.
  - apply eqfun_type_sound.
Qed.

Inductive eqtest_type : environment -> pure_term -> pure_term -> poly_type -> Prop :=
| eqtest_type_core : forall (Gamma : environment) (u v : pure_term) (A C : poly_type),
    type_assignment Gamma v A ->
    eqfun_type Gamma u (poly_arr A C) ->
    eqtest_type Gamma u v C
| eqtest_type_gen : forall (Gamma : environment) (u v : pure_term) (s : poly_type),
    eqtest_type (map (ren_poly_type S) Gamma) u v s ->
    eqtest_type Gamma u v (poly_abs s)
| eqtest_type_inst : forall (Gamma : environment) (u v : pure_term) (U V : poly_type),
    eqtest_type Gamma u v (poly_abs U) ->
    eqtest_type Gamma u v (subst_poly_type (scons V poly_var) U).

Lemma eqtest_type_sound :
  forall (Gamma : environment) (u v : pure_term) (C : poly_type),
    eqtest_type Gamma u v C -> type_assignment Gamma (eqtest u v) C.
Proof.
  intros Gamma u v C H. induction H.
  - rewrite eqtest_unfold.
    eapply type_assignment_app.
    + apply eqfun_type_sound. exact H0.
    + exact H.
  - apply type_assignment_gen. exact IHeqtest_type.
  - eapply type_assignment_inst. exact IHeqtest_type.
Qed.

Lemma apptype_eqtest_complete :
  forall (D : environment) (LM LN : pure_term) (C : poly_type),
    apptype D LM LN C ->
    forall (Gamma : environment) (u v : pure_term),
      D = Gamma -> LM = eqtest_fun u -> LN = v ->
      eqtest_type Gamma u v C.
Proof.
  intros D LM LN C HAT. induction HAT;
    intros Gamma0 u0 v0 ED E1 E2.
  - apply eqtest_type_core with (A := A).
    + rewrite <- ED, <- E2. exact H0.
    + apply eqfun_type_complete with (D := Gamma0) (LM := eqtest_body u0).
      * apply abstype_complete.
        change (type_assignment Gamma0 (eqtest_fun u0) (poly_arr A C)).
        rewrite <- ED, <- E1. exact H.
      * reflexivity.
      * reflexivity.
  - apply eqtest_type_gen.
    apply IHHAT with (Gamma := map (ren_poly_type S) Gamma0)
                     (u := u0) (v := v0).
    + rewrite ED. reflexivity.
    + exact E1.
    + exact E2.
  - apply eqtest_type_inst.
    apply IHHAT with (Gamma := Gamma0) (u := u0) (v := v0).
    + exact ED. + exact E1. + exact E2.
Qed.

Theorem eqtest_type_iff :
  forall (Gamma : environment) (u v : pure_term) (C : poly_type),
    type_assignment Gamma (eqtest u v) C <-> eqtest_type Gamma u v C.
Proof.
  intros Gamma u v C. split.
  - intro H. rewrite eqtest_unfold in H.
    eapply apptype_eqtest_complete.
    + apply apptype_complete. exact H.
    + reflexivity. + reflexivity. + reflexivity.
  - apply eqtest_type_sound.
Qed.


(* --- One-step arrow decompositions --- *)

Lemma functype_arrow_step :
  forall (Gamma : environment) (u : pure_term) (A C : poly_type),
    functype Gamma u (poly_arr A C) ->
    apptype (A :: Gamma) gadget_T1 (gadget_T2 u) C \/
    (exists U V, functype Gamma u (poly_abs U) /\
                 poly_arr A C = subst_poly_type (scons V poly_var) U).
Proof.
  intros Gamma u A C H. inversion H; subst.
  - left. eassumption.
  - right. eexists. eexists. split; [eassumption|reflexivity].
Qed.

Lemma gadget_type_arrow_step :
  forall (Gamma : environment) (u v : pure_term) (A C : poly_type),
    gadget_type Gamma u v (poly_arr A C) ->
    (exists A0, type_assignment Gamma (gadget_arg v) A0 /\
                functype Gamma u (poly_arr A0 (poly_arr A C))) \/
    (exists U V, gadget_type Gamma u v (poly_abs U) /\
                 poly_arr A C = subst_poly_type (scons V poly_var) U).
Proof.
  intros Gamma u v A C H. inversion H; subst.
  - left. eexists. split; eassumption.
  - right. eexists. eexists. split; [eassumption|reflexivity].
Qed.

Lemma eqtest_type_arrow_step :
  forall (Gamma : environment) (u v : pure_term) (A C : poly_type),
    eqtest_type Gamma u v (poly_arr A C) ->
    (exists A0, type_assignment Gamma v A0 /\
                eqfun_type Gamma u (poly_arr A0 (poly_arr A C))) \/
    (exists U V, eqtest_type Gamma u v (poly_abs U) /\
                 poly_arr A C = subst_poly_type (scons V poly_var) U).
Proof.
  intros Gamma u v A C H. inversion H; subst.
  - left. eexists. split; eassumption.
  - right. eexists. eexists. split; [eassumption|reflexivity].
Qed.

Lemma eqfun_type_arrow_step :
  forall (Gamma : environment) (u : pure_term) (A C : poly_type),
    eqfun_type Gamma u (poly_arr A C) ->
    apptype (A :: Gamma) (gadget (lift 0 u) (pure_var 0)) (pure_var 0) C \/
    (exists U V, eqfun_type Gamma u (poly_abs U) /\
                 poly_arr A C = subst_poly_type (scons V poly_var) U).
Proof.
  intros Gamma u A C H. inversion H; subst.
  - left. eassumption.
  - right. eexists. eexists. split; [eassumption|reflexivity].
Qed.

Lemma abstype_arrow_step :
  forall (Gamma : environment) (M : pure_term) (A C : poly_type),
    abstype Gamma M (poly_arr A C) ->
    type_assignment (A :: Gamma) M C \/
    (exists U V, abstype Gamma M (poly_abs U) /\
                 poly_arr A C = subst_poly_type (scons V poly_var) U).
Proof.
  intros Gamma M A C H. inversion H; subst.
  - left. eassumption.
  - right. eexists. eexists. split; [eassumption|reflexivity].
Qed.


(* --- One-step poly_abs decompositions --- *)

Lemma functype_polyabs_step :
  forall (Gamma : environment) (u : pure_term) (s : poly_type),
    functype Gamma u (poly_abs s) ->
    functype (map (ren_poly_type S) Gamma) u s \/
    (exists U V, functype Gamma u (poly_abs U) /\
                 poly_abs s = subst_poly_type (scons V poly_var) U).
Proof.
  intros Gamma u s H. inversion H; subst.
  - left. eassumption.
  - right. eexists. eexists. split; [eassumption|reflexivity].
Qed.

Lemma gadget_type_polyabs_step :
  forall (Gamma : environment) (u v : pure_term) (s : poly_type),
    gadget_type Gamma u v (poly_abs s) ->
    (exists A, type_assignment Gamma (gadget_arg v) A /\
               functype Gamma u (poly_arr A (poly_abs s))) \/
    gadget_type (map (ren_poly_type S) Gamma) u v s \/
    (exists U V, gadget_type Gamma u v (poly_abs U) /\
                 poly_abs s = subst_poly_type (scons V poly_var) U).
Proof.
  intros Gamma u v s H. inversion H; subst.
  - left. eexists. split; eassumption.
  - right. left. eassumption.
  - right. right. eexists. eexists. split; [eassumption|reflexivity].
Qed.

Lemma eqtest_type_polyabs_step :
  forall (Gamma : environment) (u v : pure_term) (s : poly_type),
    eqtest_type Gamma u v (poly_abs s) ->
    (exists A, type_assignment Gamma v A /\
               eqfun_type Gamma u (poly_arr A (poly_abs s))) \/
    eqtest_type (map (ren_poly_type S) Gamma) u v s \/
    (exists U V, eqtest_type Gamma u v (poly_abs U) /\
                 poly_abs s = subst_poly_type (scons V poly_var) U).
Proof.
  intros Gamma u v s H. inversion H; subst.
  - left. eexists. split; eassumption.
  - right. left. eassumption.
  - right. right. eexists. eexists. split; [eassumption|reflexivity].
Qed.

Lemma eqfun_type_polyabs_step :
  forall (Gamma : environment) (u : pure_term) (s : poly_type),
    eqfun_type Gamma u (poly_abs s) ->
    eqfun_type (map (ren_poly_type S) Gamma) u s \/
    (exists U V, eqfun_type Gamma u (poly_abs U) /\
                 poly_abs s = subst_poly_type (scons V poly_var) U).
Proof.
  intros Gamma u s H. inversion H; subst.
  - left. eassumption.
  - right. eexists. eexists. split; [eassumption|reflexivity].
Qed.

Lemma abstype_polyabs_step :
  forall (Gamma : environment) (M : pure_term) (s : poly_type),
    abstype Gamma M (poly_abs s) ->
    abstype (map (ren_poly_type S) Gamma) M s \/
    (exists U V, abstype Gamma M (poly_abs U) /\
                 poly_abs s = subst_poly_type (scons V poly_var) U).
Proof.
  intros Gamma M s H. inversion H; subst.
  - left. eassumption.
  - right. eexists. eexists. split; [eassumption|reflexivity].
Qed.


(* --- Parameterized encodings (separate variable maps) --- *)

Fixpoint E' (f : nat -> nat) (u : term) : pure_term :=
  match u with
  | atom n => pure_var (f n)
  | arr u v => gadget (E' f u) (E' f v)
  end.

Lemma E'_id : forall u, E' (fun n => n) u = E u.
Proof.
  induction u as [n | u IHu v IHv]; simpl.
  - reflexivity.
  - now rewrite IHu, IHv.
Qed.

Lemma type_assignment_E'_bottom :
  forall (Gamma : environment) (T : nat -> poly_type) (u : term) (f : nat -> nat),
    (forall n, In n (atoms u) ->
       nth_error Gamma (f n) = Some (poly_abs (poly_var 0))) ->
    type_assignment Gamma (E' f u) (enc T u).
Proof.
  intros Gamma T u. induction u as [n | u IHu v IHv]; intros f H; simpl.
  - apply inst_bottom_any. apply H. simpl. auto.
  - apply type_assignment_gadget.
    + apply IHu. intros k Hk. apply H. apply in_app_iff. left. exact Hk.
    + apply IHv. intros k Hk. apply H. apply in_app_iff. right. exact Hk.
Qed.

Lemma type_assignment_E'_env :
  forall (Gamma : environment) (T : nat -> poly_type) (u : term) (f : nat -> nat),
    (forall n, In n (atoms u) -> nth_error Gamma (f n) = Some (T n)) ->
    type_assignment Gamma (E' f u) (enc T u).
Proof.
  intros Gamma T u. induction u as [n | u IHu v IHv]; intros f H; simpl.
  - apply type_assignment_var. apply H. simpl. auto.
  - apply type_assignment_gadget.
    + apply IHu. intros k Hk. apply H. apply in_app_iff. left. exact Hk.
    + apply IHv. intros k Hk. apply H. apply in_app_iff. right. exact Hk.
Qed.


(* --- Non-vacuous generalisation closure --- *)

Definition bottom : poly_type := poly_abs (poly_var 0).

Lemma bottom_rewrite : bottom = poly_abs (poly_var 0). Proof. reflexivity. Qed.

Lemma ren_S_bottom : ren_poly_type S bottom = bottom.
Proof. reflexivity. Qed.

Fixpoint iter_abs (K : nat) (T : poly_type) : poly_type :=
  match K with
  | 0 => T
  | S K' => poly_abs (iter_abs K' T)
  end.

Lemma nth_map_ren_bottom :
  forall (Gamma : environment) (n : nat),
    nth_error Gamma n = Some bottom ->
    nth_error (map (ren_poly_type S) Gamma) n = Some bottom.
Proof.
  intros Gamma n H. rewrite nth_error_map, H. reflexivity.
Qed.

Lemma type_assignment_E'_bottom_closure :
  forall (K : nat) (Gamma : environment) (T : nat -> poly_type) (s : term),
    (forall n, In n (atoms s) -> nth_error Gamma n = Some bottom) ->
    type_assignment Gamma (E' (fun n => n) s) (iter_abs K (enc T s)).
Proof.
  induction K as [|K IH]; intros Gamma T s H.
  - simpl. apply type_assignment_E'_bottom. exact H.
  - simpl. apply type_assignment_gen.
    apply IH with (Gamma := map (ren_poly_type S) Gamma).
    intros n Hn. apply nth_map_ren_bottom. apply H. exact Hn.
Qed.


(* --- First-order (poly_abs-free) types --- *)

Fixpoint no_abs (T : poly_type) : Prop :=
  match T with
  | poly_var _ => True
  | poly_arr A B => no_abs A /\ no_abs B
  | poly_abs _ => False
  end.

Fixpoint subst_free (sigma : nat -> poly_type) (T : poly_type) : poly_type :=
  match T with
  | poly_var n => sigma n
  | poly_arr A B => poly_arr (subst_free sigma A) (subst_free sigma B)
  | poly_abs A => poly_abs (subst_free sigma A)
  end.

Lemma no_abs_subst :
  forall (T : poly_type), no_abs T ->
  forall (sigma : nat -> poly_type),
    subst_poly_type sigma T = subst_free sigma T.
Proof.
  induction T as [n | A IHA B IHB | A IHA]; intros H sigma; simpl in *.
  - reflexivity.
  - destruct H as [HA HB]. now rewrite IHA, IHB.
  - destruct H.
Qed.

Lemma no_abs_ren :
  forall (T : poly_type) (xi : nat -> nat),
    no_abs T -> no_abs (ren_poly_type xi T).
Proof.
  induction T as [n | A IHA B IHB | A IHA]; intros xi H; simpl in *.
  - exact I.
  - destruct H as [HA HB]. split; [apply IHA|apply IHB]; assumption.
  - destruct H.
Qed.

Lemma no_abs_subst_free :
  forall (T : poly_type) (sigma : nat -> poly_type),
    no_abs T ->
    (forall n, no_abs (sigma n)) ->
    no_abs (subst_free sigma T).
Proof.
  induction T as [n | A IHA B IHB | A IHA]; intros sigma H Hs; simpl in *.
  - apply Hs.
  - destruct H as [HA HB]. split; [apply IHA|apply IHB]; assumption.
  - destruct H.
Qed.

Lemma no_abs_enc :
  forall (T : nat -> poly_type) (u : term),
    (forall n, no_abs (T n)) -> no_abs (enc T u).
Proof.
  intros T u. induction u as [n | u IHu v IHv]; intros H; simpl.
  - apply H.
  - split; [apply IHu|apply IHv]; intros k; apply H.
Qed.


(* --- Substitution through iterated abstraction --- *)

Lemma subst_free_id_noabs :
  forall (T : poly_type), no_abs T ->
    subst_free (fun n => poly_var n) T = T.
Proof.
  induction T as [n | A IHA B IHB | A IHA]; intros H; simpl in *.
  - reflexivity.
  - destruct H as [HA HB]. now rewrite IHA, IHB.
  - destruct H.
Qed.

Lemma subst_free_comp :
  forall (T : poly_type), no_abs T ->
    forall (sigma tau : nat -> poly_type),
      subst_free sigma (subst_free tau T) =
      subst_free (fun j => subst_free sigma (tau j)) T.
Proof.
  induction T as [n | A IHA B IHB | A IHA]; intros H sigma tau; simpl in *.
  - reflexivity.
  - destruct H as [HA HB]. now rewrite IHA, IHB.
  - destruct H.
Qed.

Definition up_subst (sigma : nat -> poly_type) : nat -> poly_type :=
  scons (poly_var 0) (funcomp (ren_poly_type S) sigma).

Fixpoint up_iter (n : nat) (sigma : nat -> poly_type) : nat -> poly_type :=
  match n with
  | 0 => sigma
  | S n' => up_iter n' (up_subst sigma)
  end.

Lemma push_subst_iter :
  forall (n : nat) (sigma : nat -> poly_type) (T : poly_type),
    subst_poly_type sigma (iter_abs n T) =
    iter_abs n (subst_poly_type (up_iter n sigma) T).
Proof.
  induction n as [|n IH]; intros sigma T; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.


(* --- up_iter variable laws --- *)

Lemma ren_poly_type_id :
  forall (T : poly_type), ren_poly_type (fun n => n) T = T.
Proof.
  induction T as [n | A IHA B IHB | A IHA]; simpl.
  - reflexivity.
  - now rewrite IHA, IHB.
  - f_equal.
    transitivity (ren_poly_type (fun n => n) A).
    + apply ren_poly_type_ext. intro n. destruct n; reflexivity.
    + apply IHA.
Qed.

Lemma up_iter_ge :
  forall (n : nat) (sigma : nat -> poly_type) (j : nat),
    n <= j ->
    up_iter n sigma j =
    ren_poly_type (fun m => m + n) (sigma (j - n)).
Proof.
  induction n as [|n IH]; intros sigma j H.
  - simpl. replace (j - 0) with j by lia.
    symmetry.
    transitivity (ren_poly_type (fun n => n) (sigma j)).
    + apply ren_poly_type_ext. intro m. lia.
    + apply ren_poly_type_id.
  - simpl.
    rewrite (IH (up_subst sigma) j) by lia.
    assert (Hk : j - n = S (j - S n)) by lia.
    rewrite Hk.
    unfold up_subst, funcomp. simpl.
    rewrite ren_poly_type_comp.
    apply ren_poly_type_ext. intro m. simpl. lia.
Qed.

Lemma up_iter_lt :
  forall (n : nat) (sigma : nat -> poly_type) (j : nat),
    j < n -> up_iter n sigma j = poly_var j.
Proof.
  induction n as [|n IH]; intros sigma j H.
  - lia.
  - simpl.
    destruct (lt_eq_lt_dec j n) as [[Hlt|Heq]|Hgt].
    + apply IH. lia.
    + subst j.
      rewrite (up_iter_ge n (up_subst sigma) n) by lia.
      rewrite Nat.sub_diag. simpl. reflexivity.
    + lia.
Qed.


(* --- Auxiliaries for iterated instantiation --- *)

Lemma subst_free_ext :
  forall (T : poly_type) (sigma tau : nat -> poly_type),
    (forall n, sigma n = tau n) ->
    subst_free sigma T = subst_free tau T.
Proof.
  induction T as [n | A IHA B IHB | A IHA]; intros sigma tau H; simpl.
  - apply H.
  - now rewrite (IHA sigma tau H), (IHB sigma tau H).
  - f_equal. apply IHA. exact H.
Qed.

Lemma no_abs_ren_shift :
  forall (K : nat) (U : poly_type),
    no_abs U -> no_abs (ren_poly_type (fun m => m + K) U).
Proof. intros. apply no_abs_ren. exact H. Qed.

Lemma no_abs_up_iter_scons :
  forall (K : nat) (U : poly_type),
    no_abs U ->
    forall j, no_abs (up_iter K (scons U poly_var) j).
Proof.
  intros K U HU j.
  destruct (lt_eq_lt_dec j K) as [[Hlt|Heq]|Hgt].
  - rewrite up_iter_lt by lia. exact I.
  - subst j. rewrite up_iter_ge by lia.
    rewrite Nat.sub_diag.
    change (no_abs (ren_poly_type (fun m => m + K)
              ((scons U poly_var) 0))).
    simpl. apply no_abs_ren_shift. exact HU.
  - rewrite up_iter_ge by lia.
    destruct (j - K) as [|k] eqn:E.
    + (* j-K=0 contradicts Hgt *) lia.
    + change (no_abs (ren_poly_type (fun m => m + K) (poly_var k))).
      apply no_abs_ren_shift. exact I.
Qed.

Lemma subst_free_shift_cancel :
  forall (K : nat) (U : poly_type) (sigma : nat -> poly_type),
    no_abs U ->
    (forall m, sigma (m + K) = poly_var m) ->
    subst_free sigma (ren_poly_type (fun m => m + K) U) = U.
Proof.
  induction U as [n | A IHA B IHB | A IHA]; intros sigma H Hs; simpl in *.
  - apply Hs.
  - destruct H as [HA HB]. now rewrite IHA, IHB.
  - destruct H.
Qed.


(* --- Iterated instantiation --- *)

Definition Phi (K : nat) (U : nat -> poly_type) : nat -> poly_type :=
  fun j => if j <? K then U (K - 1 - j) else poly_var (j - K).

Lemma iter_step_point :
  forall (K j : nat) (U : nat -> poly_type),
    (forall i, no_abs (U i)) ->
    subst_free (Phi K (fun i => U (S i)))
      (up_iter K (scons (U 0) poly_var) j)
    = Phi (S K) U j.
Proof.
  intros K j U HU.
  destruct (lt_eq_lt_dec j K) as [[Hlt|Heq]|Hgt].
  - rewrite up_iter_lt by lia.
    simpl. unfold Phi.
    assert (H1 : j <? K = true) by (apply Nat.ltb_lt; lia).
    assert (H2 : j <? S K = true) by (apply Nat.ltb_lt; lia).
    rewrite H1, H2. simpl. f_equal. lia.
  - subst j.
    rewrite (up_iter_ge K (scons (U 0) poly_var) K) by lia.
    rewrite Nat.sub_diag. simpl.
    change (subst_free (Phi K (fun i => U (S i)))
              (ren_poly_type (fun m => m + K) (U 0)) = Phi (S K) U K).
    assert (Hcond : forall m, Phi K (fun i => U (S i)) (m + K) = poly_var m).
    { intro m. unfold Phi.
      assert (Hf : m + K <? K = false) by (apply Nat.ltb_ge; lia).
      rewrite Hf. simpl. rewrite Nat.add_sub. reflexivity. }
    rewrite (subst_free_shift_cancel K (U 0) (Phi K (fun i => U (S i))) (HU 0) Hcond).
    unfold Phi. simpl.
    assert (Hs : K <? S K = true) by (apply Nat.ltb_lt; lia).
    rewrite Hs. simpl. f_equal. lia.
  - rewrite (up_iter_ge K (scons (U 0) poly_var) j) by lia.
    destruct (j - K) as [|d] eqn:Ed.
    + lia.
    + simpl. unfold Phi.
      assert (Hf2 : d + K <? K = false) by (apply Nat.ltb_ge; lia).
      rewrite Hf2. simpl. rewrite Nat.add_sub.
      destruct (j <? S K) eqn:Ej.
      * apply Nat.ltb_lt in Ej. lia.
      * simpl. f_equal. lia.
Qed.

Lemma iter_step_subst :
  forall (K : nat) (T : poly_type) (U : nat -> poly_type),
    no_abs T -> (forall i, no_abs (U i)) ->
    subst_free (Phi K (fun i => U (S i)))
      (subst_poly_type (up_iter K (scons (U 0) poly_var)) T)
    = subst_free (Phi (S K) U) T.
Proof.
  intros K T U HT HU.
  rewrite (no_abs_subst T HT (up_iter K (scons (U 0) poly_var))).
  rewrite (subst_free_comp T HT (Phi K (fun i => U (S i)))
             (up_iter K (scons (U 0) poly_var))).
  apply subst_free_ext. intro j.
  apply iter_step_point. exact HU.
Qed.

Lemma no_abs_up_iter_scons_apply :
  forall (K : nat) (U : nat -> poly_type),
    (forall i, no_abs (U i)) ->
    forall j, no_abs (up_iter K (scons (U 0) poly_var) j).
Proof.
  intros K U HU j. apply no_abs_up_iter_scons. apply HU.
Qed.

Lemma iter_insts :
  forall (K : nat) (T : poly_type) (U : nat -> poly_type),
    no_abs T -> (forall i, no_abs (U i)) ->
    forall (Gamma : environment) (x : nat),
      type_assignment Gamma (pure_var x) (iter_abs K T) ->
      type_assignment Gamma (pure_var x) (subst_free (Phi K U) T).
Proof.
  induction K as [|K IH]; intros T U HT HU Gamma x D.
  - simpl in D. simpl.
    replace (subst_free (Phi 0 U) T) with T.
    + exact D.
    + transitivity (subst_free (fun n => poly_var n) T).
      * symmetry. apply subst_free_id_noabs. exact HT.
      * apply subst_free_ext. intro j. unfold Phi.
        assert (Hf : j <? 0 = false) by (apply Nat.ltb_ge; lia).
        rewrite Hf. simpl. rewrite Nat.sub_0_r. reflexivity.
  - simpl in D.
    assert (D1 : type_assignment Gamma (pure_var x)
          (subst_poly_type (scons (U 0) poly_var) (iter_abs K T))).
    { eapply type_assignment_inst. exact D. }
    rewrite push_subst_iter in D1.
    assert (HT1 : no_abs (subst_poly_type
                  (up_iter K (scons (U 0) poly_var)) T)).
    { rewrite (no_abs_subst T HT (up_iter K (scons (U 0) poly_var))).
      apply no_abs_subst_free.
      - exact HT.
      - intro j. apply no_abs_up_iter_scons. apply HU. }
    assert (HU' : forall i, no_abs ((fun i => U (S i)) i)).
    { intro i. apply HU. }
    pose proof (IH (subst_poly_type (up_iter K (scons (U 0) poly_var)) T)
                  (fun i => U (S i)) HT1 HU' Gamma x D1) as R.
    rewrite (iter_step_subst K T U HT HU) in R.
    exact R.
Qed.


(* --- Forward scheme instance (type level) --- *)

Fixpoint tvars (T : poly_type) : list nat :=
  match T with
  | poly_var n => n :: nil
  | poly_arr A B => tvars A ++ tvars B
  | poly_abs A => tvars A
  end.

Lemma subst_free_eq_on_tvars :
  forall (T : poly_type) (sigma tau : nat -> poly_type),
    no_abs T ->
    (forall n, In n (tvars T) -> sigma n = tau n) ->
    subst_free sigma T = subst_free tau T.
Proof.
  induction T as [n | A IHA B IHB | A IHA]; intros sigma tau H Hv; simpl in *.
  - apply Hv. simpl. auto.
  - destruct H as [HA HB].
    assert (HA' : forall n, In n (tvars A) -> sigma n = tau n).
    { intros n Hn. apply Hv. apply in_app_iff. left. exact Hn. }
    assert (HB' : forall n, In n (tvars B) -> sigma n = tau n).
    { intros n Hn. apply Hv. apply in_app_iff. right. exact Hn. }
    now rewrite (IHA sigma tau HA HA'), (IHB sigma tau HB HB').
  - destruct H.
Qed.

Definition tvars_max (T : poly_type) : nat := list_max (tvars T).

Lemma tvars_lt_max :
  forall (T : poly_type) (n : nat),
    In n (tvars T) -> n < S (tvars_max T).
Proof.
  intros T n H. unfold tvars_max.
  pose proof (proj1 (list_max_le (tvars T) (list_max (tvars T)))
                (Nat.le_refl (list_max (tvars T)))) as Hf.
  rewrite Forall_forall in Hf. specialize (Hf n H). lia.
Qed.

Lemma subst_free_Phi_eq :
  forall (K : nat) (T : poly_type) (U Psi : nat -> poly_type),
    no_abs T ->
    (forall n, In n (tvars T) -> n < K) ->
    (forall i, i < K -> U i = Psi (K - 1 - i)) ->
    subst_free (Phi K U) T = subst_free Psi T.
Proof.
  intros K T U Psi HT Hbound Hagree.
  apply subst_free_eq_on_tvars.
  - exact HT.
  - intros n Hn.
    assert (HnK : n < K) by (apply Hbound; exact Hn).
    unfold Phi.
    assert (Hf : n <? K = true) by (apply Nat.ltb_lt; lia).
    rewrite Hf. simpl.
    rewrite Hagree by lia.
    f_equal. lia.
Qed.

Lemma enc_substitute :
  forall (phi : valuation) (s : term),
    enc (fun n => encode_term (phi n)) s = encode_term (substitute phi s).
Proof.
  intros phi s. induction s as [n | u IHu v IHv]; simpl.
  - reflexivity.
  - now rewrite IHu, IHv.
Qed.

Lemma no_abs_encode_term :
  forall (u : term), no_abs (encode_term u).
Proof.
  induction u as [n | u IHu v IHv]; simpl.
  - exact I.
  - split; assumption.
Qed.

Lemma scheme_instance_types :
  forall (phi psi : valuation) (s t : term) (K : nat),
    substitute psi (substitute phi s) = substitute phi t ->
    (forall n, In n (tvars (enc (fun m => encode_term (phi m)) s)) -> n < K) ->
    forall (Gamma : environment) (x : nat),
      type_assignment Gamma (pure_var x)
        (iter_abs K (enc (fun m => encode_term (phi m)) s)) ->
      type_assignment Gamma (pure_var x)
        (enc (fun m => encode_term (phi m)) t).
Proof.
  intros phi psi s t K Heq Hbound Gamma x D.
  assert (HT : no_abs (enc (fun m => encode_term (phi m)) s)).
  { apply no_abs_enc. intro n. apply no_abs_encode_term. }
  assert (HU : forall i, no_abs ((fun i => encode_term (psi (K - 1 - i))) i)).
  { intro i. apply no_abs_encode_term. }
  pose proof (iter_insts K (enc (fun m => encode_term (phi m)) s)
                (fun i => encode_term (psi (K - 1 - i)))
                HT HU Gamma x D) as D1.
  assert (HPhi : subst_free (Phi K (fun i => encode_term (psi (K - 1 - i))))
                   (enc (fun m => encode_term (phi m)) s)
                 = subst_free (fun n => encode_term (psi n))
                   (enc (fun m => encode_term (phi m)) s)).
  { apply subst_free_Phi_eq.
    - exact HT.
    - exact Hbound.
    - intros i Hi. reflexivity. }
  rewrite HPhi in D1.
  rewrite <- (no_abs_subst (enc (fun m => encode_term (phi m)) s) HT
                (fun n => encode_term (psi n))) in D1.
  rewrite (enc_substitute phi s) in D1.
  rewrite <- (encode_substitute psi (substitute phi s)) in D1.
  rewrite Heq in D1.
  rewrite <- (enc_substitute phi t) in D1.
  exact D1.
Qed.


(* --- Closure for arbitrary variable maps --- *)

Lemma type_assignment_E'_bottom_closure_f :
  forall (K : nat) (Gamma : environment) (T : nat -> poly_type)
         (s : term) (f : nat -> nat),
    (forall n, In n (atoms s) -> nth_error Gamma (f n) = Some bottom) ->
    type_assignment Gamma (E' f s) (iter_abs K (enc T s)).
Proof.
  induction K as [|K IH]; intros Gamma T s f H.
  - simpl. apply type_assignment_E'_bottom. exact H.
  - simpl. apply type_assignment_gen.
    apply IH with (Gamma := map (ren_poly_type S) Gamma) (f := f).
    intros n Hn. apply nth_map_ren_bottom. apply H. exact Hn.
Qed.


(* --- Concrete environment for the forward direction --- *)

Fixpoint evenb (n : nat) : bool :=
  match n with
  | 0 => true
  | S k => negb (evenb k)
  end.

Definition half (n : nat) : nat := Nat.div2 n.

Definition entry (phi : valuation) (i : nat) : poly_type :=
  if evenb i then encode_term (phi (half i)) else bottom.

Definition env_phi (phi : valuation) (M : nat) : environment :=
  map (entry phi) (seq 0 M).

Lemma evenb_double : forall n, evenb (2 * n) = true.
Proof.
  intro n. replace (2 * n) with (n + n) by lia.
  induction n as [|n IH].
  - reflexivity.
  - replace (S n + S n) with (S (S (n + n))) by lia.
    cbn [evenb]. rewrite IH. reflexivity.
Qed.

Lemma evenb_odd : forall n, evenb (2 * n + 1) = false.
Proof.
  intro n. replace (2 * n + 1) with (S (2 * n)) by lia.
  cbn [evenb]. rewrite evenb_double. reflexivity.
Qed.

Lemma half_double : forall n, half (2 * n) = n.
Proof. intro n. unfold half. apply Nat.div2_double. Qed.

Lemma half_odd : forall n, half (2 * n + 1) = n.
Proof.
  intro n. unfold half.
  replace (2 * n + 1) with (S (2 * n)) by lia.
  apply Nat.div2_succ_double.
Qed.

Lemma entry_even : forall (phi : valuation) (n : nat),
  entry phi (2 * n) = encode_term (phi n).
Proof.
  intros phi n. unfold entry. rewrite evenb_double.
  change (encode_term (phi (half (2 * n))) = encode_term (phi n)).
  rewrite half_double. reflexivity.
Qed.

Lemma entry_odd : forall (phi : valuation) (n : nat),
  entry phi (2 * n + 1) = bottom.
Proof.
  intros phi n. unfold entry. rewrite evenb_odd. reflexivity.
Qed.

Lemma nth_env_phi :
  forall (phi : valuation) (M i : nat),
    i < M -> nth_error (env_phi phi M) i = Some (entry phi i).
Proof.
  intros phi M i H. unfold env_phi.
  rewrite nth_error_map, nth_error_seq.
  assert (Hlt : i <? M = true) by (apply Nat.ltb_lt; exact H).
  rewrite Hlt. simpl. reflexivity.
Qed.

Lemma nth_env_even :
  forall (phi : valuation) (M n : nat),
    2 * n < M ->
    nth_error (env_phi phi M) (2 * n) = Some (encode_term (phi n)).
Proof.
  intros phi M n H. rewrite nth_env_phi by exact H. rewrite entry_even. reflexivity.
Qed.

Lemma nth_env_odd :
  forall (phi : valuation) (M n : nat),
    2 * n + 1 < M ->
    nth_error (env_phi phi M) (2 * n + 1) = Some bottom.
Proof.
  intros phi M n H. rewrite nth_env_phi by exact H. rewrite entry_odd. reflexivity.
Qed.

Definition amax (s t0 t1 : term) : nat :=
  list_max (atoms s ++ atoms t0 ++ atoms t1).

Definition env_size (s t0 t1 : term) : nat := S (2 * amax s t0 t1 + 1).

Lemma in_amax :
  forall (s t0 t1 : term) (n : nat),
    In n (atoms s ++ atoms t0 ++ atoms t1) -> n <= amax s t0 t1.
Proof.
  intros s t0 t1 n H. unfold amax.
  pose proof (proj1 (list_max_le (atoms s ++ atoms t0 ++ atoms t1)
                  (list_max (atoms s ++ atoms t0 ++ atoms t1)))
                (Nat.le_refl _)) as Hf.
  rewrite Forall_forall in Hf. apply Hf. exact H.
Qed.

Lemma index_even_lt :
  forall (s t0 t1 : term) (n : nat),
    n <= amax s t0 t1 -> 2 * n < env_size s t0 t1.
Proof. intros. unfold env_size. lia. Qed.

Lemma index_odd_lt :
  forall (s t0 t1 : term) (n : nat),
    n <= amax s t0 t1 -> 2 * n + 1 < env_size s t0 t1.
Proof. intros. unfold env_size. lia. Qed.


(* Identity instance of a generalisation closure. *)
Lemma closure_self :
  forall (K : nat) (Gamma : environment) (T : poly_type) (x : nat),
    no_abs T ->
    (forall n, In n (tvars T) -> n < K) ->
    type_assignment Gamma (pure_var x) (iter_abs K T) ->
    type_assignment Gamma (pure_var x) T.
Proof.
  intros K Gamma T x HT HB D.
  set (U := fun i => poly_var (K - 1 - i)).
  assert (HU : forall i, no_abs (U i)).
  { intro i. unfold U. exact I. }
  pose proof (iter_insts K T U HT HU Gamma x D) as D1.
  assert (HPhi : subst_free (Phi K U) T =
                 subst_free (fun n => poly_var n) T).
  { apply subst_free_Phi_eq.
    - exact HT.
    - exact HB.
    - intros i Hi. unfold U. reflexivity. }
  rewrite HPhi in D1.
  rewrite subst_free_id_noabs in D1 by exact HT.
  exact D1.
Qed.

(* --- Explicit reduction term and its forward/soundness direction --- *)

Definition fR (n : nat) : nat := 2 * n.
Definition fB (n : nat) : nat := 2 * n + 1.

Definition Rterm (u : term) : pure_term := E' fR u.
Definition Bterm (u : term) : pure_term := E' fB u.

Definition EQtest (u : term) : pure_term := eqtest (Rterm u) (Bterm u).

Definition CHECK (t : term) : pure_term :=
  pure_app (gadget (lift 0 (Rterm t)) (pure_var 1)) (pure_var 0).

Definition LINK (s : term) : pure_term :=
  eqtest (pure_var 0) (lift 0 (Rterm s)).

Definition bodyF (s t0 t1 : term) : pure_term :=
  gadget (CHECK t0)
    (gadget (CHECK t1)
      (gadget (LINK s)
        (gadget (lift 0 (EQtest s))
          (gadget (lift 0 (EQtest t0))
            (gadget (lift 0 (EQtest t1)) (pure_var 1)))))).

Definition reduce (p : term * term * term) : pure_term :=
  match p with
  | ((s, t0), t1) => pure_app (pure_abs (bodyF s t0 t1)) (Bterm s)
  end.

Lemma atom_bound_s :
  forall (s t0 t1 : term) (n : nat), In n (atoms s) ->
    n <= amax s t0 t1.
Proof.
  intros. apply in_amax. apply in_app_iff. left. exact H.
Qed.

Lemma atom_bound_t0 :
  forall (s t0 t1 : term) (n : nat), In n (atoms t0) ->
    n <= amax s t0 t1.
Proof.
  intros. apply in_amax. apply in_app_iff. right. apply in_app_iff. left. exact H.
Qed.

Lemma atom_bound_t1 :
  forall (s t0 t1 : term) (n : nat), In n (atoms t1) ->
    n <= amax s t0 t1.
Proof.
  intros. apply in_amax. apply in_app_iff. right. apply in_app_iff. right. exact H.
Qed.

Lemma nthR_of :
  forall (phi : valuation) (s t0 t1 : term) (n : nat),
    n <= amax s t0 t1 ->
    nth_error (env_phi phi (env_size s t0 t1)) (fR n) =
      Some (encode_term (phi n)).
Proof.
  intros phi s t0 t1 n H. unfold fR.
  rewrite nth_env_even.
  - reflexivity.
  - apply index_even_lt. exact H.
Qed.

Lemma nthB_of :
  forall (phi : valuation) (s t0 t1 : term) (n : nat),
    n <= amax s t0 t1 ->
    nth_error (env_phi phi (env_size s t0 t1)) (fB n) = Some bottom.
Proof.
  intros phi s t0 t1 n H. unfold fB.
  rewrite nth_env_odd.
  - reflexivity.
  - apply index_odd_lt. exact H.
Qed.

Theorem forward_sound :
  forall (phi psi0 psi1 : valuation) (s t0 t1 : term),
    substitute psi0 (substitute phi s) = substitute phi t0 ->
    substitute psi1 (substitute phi s) = substitute phi t1 ->
    SysF_TYP (reduce (s, t0, t1)).
Proof.
  intros phi psi0 psi1 s t0 t1 Heq0 Heq1.
  set (M := env_size s t0 t1).
  set (G := env_phi phi M).
  set (T := fun n => encode_term (phi n)).
  set (K := S (tvars_max (enc T s))).
  set (X := iter_abs K (enc T s)).
  assert (HRs : type_assignment G (Rterm s) (enc T s)).
  { unfold Rterm. apply type_assignment_E'_env.
    intros n Hn.
    change (nth_error (env_phi phi (env_size s t0 t1)) (fR n)
              = Some (encode_term (phi n))).
    rewrite nthR_of.
    - reflexivity.
    - apply atom_bound_s. exact Hn. }
  assert (HR0 : type_assignment G (Rterm t0) (enc T t0)).
  { unfold Rterm. apply type_assignment_E'_env.
    intros n Hn.
    change (nth_error (env_phi phi (env_size s t0 t1)) (fR n)
              = Some (encode_term (phi n))).
    rewrite nthR_of.
    - reflexivity.
    - apply atom_bound_t0. exact Hn. }
  assert (HR1 : type_assignment G (Rterm t1) (enc T t1)).
  { unfold Rterm. apply type_assignment_E'_env.
    intros n Hn.
    change (nth_error (env_phi phi (env_size s t0 t1)) (fR n)
              = Some (encode_term (phi n))).
    rewrite nthR_of.
    - reflexivity.
    - apply atom_bound_t1. exact Hn. }
  assert (HBs : type_assignment G (Bterm s) (enc T s)).
  { unfold Bterm. apply type_assignment_E'_bottom.
    intros n Hn.
    change (nth_error (env_phi phi (env_size s t0 t1)) (fB n) = Some bottom).
    rewrite nthB_of.
    - reflexivity.
    - apply atom_bound_s. exact Hn. }
  assert (HB0 : type_assignment G (Bterm t0) (enc T t0)).
  { unfold Bterm. apply type_assignment_E'_bottom.
    intros n Hn.
    change (nth_error (env_phi phi (env_size s t0 t1)) (fB n) = Some bottom).
    rewrite nthB_of.
    - reflexivity.
    - apply atom_bound_t0. exact Hn. }
  assert (HB1 : type_assignment G (Bterm t1) (enc T t1)).
  { unfold Bterm. apply type_assignment_E'_bottom.
    intros n Hn.
    change (nth_error (env_phi phi (env_size s t0 t1)) (fB n) = Some bottom).
    rewrite nthB_of.
    - reflexivity.
    - apply atom_bound_t1. exact Hn. }
  assert (HEQs : type_assignment G (EQtest s) (enc T s)).
  { unfold EQtest. eapply eqtest_sound.
    - exact HRs. - exact HBs. }
  assert (HEQ0 : type_assignment G (EQtest t0) (enc T t0)).
  { unfold EQtest. eapply eqtest_sound.
    - exact HR0. - exact HB0. }
  assert (HEQ1 : type_assignment G (EQtest t1) (enc T t1)).
  { unfold EQtest. eapply eqtest_sound.
    - exact HR1. - exact HB1. }
  assert (HClos : type_assignment G (Bterm s) X).
  { unfold X, K. unfold Bterm. apply type_assignment_E'_bottom_closure_f with (f := fB).
    intros n Hn.
    change (nth_error (env_phi phi (env_size s t0 t1)) (fB n) = Some bottom).
    rewrite nthB_of.
    - reflexivity.
    - apply atom_bound_s. exact Hn. }
  assert (Hbound : forall n, In n (tvars (enc T s)) -> n < K).
  { intros n Hn. unfold K. apply tvars_lt_max. exact Hn. }
  set (D := X :: G).
  assert (Hx : type_assignment D (pure_var 0) X).
  { apply type_assignment_var. reflexivity. }
  assert (HxS : type_assignment D (pure_var 0) (enc T s)).
  { unfold X, K, T, D in *.
    eapply closure_self with
      (K := S (tvars_max (enc (fun n => encode_term (phi n)) s)))
      (T := enc (fun n => encode_term (phi n)) s).
    - apply no_abs_enc. intro n. apply no_abs_encode_term.
    - intros n Hn. apply tvars_lt_max. exact Hn.
    - exact Hx. }
  assert (Hx0 : type_assignment D (pure_var 0) (enc T t0)).
  { unfold X, K, T, D in *.
    eapply scheme_instance_types with (phi := phi) (psi := psi0)
      (s := s) (t := t0) (K := S (tvars_max (enc (fun n => encode_term (phi n)) s))).
    - exact Heq0.
    - intros n Hn. apply tvars_lt_max. exact Hn.
    - exact Hx. }
  assert (Hx1 : type_assignment D (pure_var 0) (enc T t1)).
  { unfold X, K, T, D in *.
    eapply scheme_instance_types with (phi := phi) (psi := psi1)
      (s := s) (t := t1) (K := S (tvars_max (enc (fun n => encode_term (phi n)) s))).
    - exact Heq1.
    - intros n Hn. apply tvars_lt_max. exact Hn.
    - exact Hx. }
  assert (HLRs : type_assignment D (lift 0 (Rterm s)) (enc T s)).
  { unfold D.
    change (type_assignment (insert_env 0 X G) (lift 0 (Rterm s)) (enc T s)).
    exact (type_assignment_lift G (Rterm s) (enc T s) HRs 0 X). }
  assert (HLINK : type_assignment D (LINK s) (enc T s)).
  { unfold LINK. eapply eqtest_sound.
    - exact HxS.
    - exact HLRs. }
  assert (HLR0 : type_assignment D (lift 0 (Rterm t0)) (enc T t0)).
  { unfold D.
    change (type_assignment (insert_env 0 X G) (lift 0 (Rterm t0)) (enc T t0)).
    exact (type_assignment_lift G (Rterm t0) (enc T t0) HR0 0 X). }
  assert (HLR1 : type_assignment D (lift 0 (Rterm t1)) (enc T t1)).
  { unfold D.
    change (type_assignment (insert_env 0 X G) (lift 0 (Rterm t1)) (enc T t1)).
    exact (type_assignment_lift G (Rterm t1) (enc T t1) HR1 0 X). }
  assert (HLEQs : type_assignment D (lift 0 (EQtest s)) (enc T s)).
  { unfold D.
    change (type_assignment (insert_env 0 X G) (lift 0 (EQtest s)) (enc T s)).
    exact (type_assignment_lift G (EQtest s) (enc T s) HEQs 0 X). }
  assert (HLEQ0 : type_assignment D (lift 0 (EQtest t0)) (enc T t0)).
  { unfold D.
    change (type_assignment (insert_env 0 X G) (lift 0 (EQtest t0)) (enc T t0)).
    exact (type_assignment_lift G (EQtest t0) (enc T t0) HEQ0 0 X). }
  assert (HLEQ1 : type_assignment D (lift 0 (EQtest t1)) (enc T t1)).
  { unfold D.
    change (type_assignment (insert_env 0 X G) (lift 0 (EQtest t1)) (enc T t1)).
    exact (type_assignment_lift G (EQtest t1) (enc T t1) HEQ1 0 X). }
  assert (Hd : type_assignment D (pure_var 1) (entry phi 0)).
  { unfold D. apply type_assignment_var.
    change (nth_error (env_phi phi (env_size s t0 t1)) 0 = Some (entry phi 0)).
    rewrite nth_env_phi.
    - reflexivity.
    - unfold env_size. lia. }
  assert (HC0 : type_assignment D (CHECK t0) (entry phi 0)).
  { unfold CHECK. eapply type_assignment_app.
    - eapply type_assignment_gadget.
      + exact HLR0. + exact Hd.
    - exact Hx0. }
  assert (HC1 : type_assignment D (CHECK t1) (entry phi 0)).
  { unfold CHECK. eapply type_assignment_app.
    - eapply type_assignment_gadget.
      + exact HLR1. + exact Hd.
    - exact Hx1. }
  exists G, (poly_arr (entry phi 0)
        (poly_arr (entry phi 0) (poly_arr (enc T s) (poly_arr (enc T s)
          (poly_arr (enc T t0) (poly_arr (enc T t1) (entry phi 0))))))).
  unfold reduce.
  eapply type_assignment_app.
  - refine (@type_assignment_abs G (bodyF s t0 t1) X _ _).
    unfold bodyF.
    eapply type_assignment_gadget; [exact HC0|].
    eapply type_assignment_gadget; [exact HC1|].
    eapply type_assignment_gadget; [exact HLINK|].
    eapply type_assignment_gadget; [exact HLEQs|].
    eapply type_assignment_gadget; [exact HLEQ0|].
    eapply type_assignment_gadget; [exact HLEQ1|].
    exact Hd.
  - exact HClos.
Qed.


Lemma reduction_forward :
  forall (p : term * term * term), LU2SemiU p -> SysF_TYP (reduce p).
Proof.
  intros [[s t0] t1] [phi [psi0 [psi1 [H0 H1]]]].
  apply (forward_sound phi psi0 psi1 s t0 t1 H0 H1).
Qed.


(* --- Inversion entry points for the reduction term --- *)

Lemma reduce_typing_iff :
  forall (s t0 t1 : term) (Gamma : environment) (C : poly_type),
    type_assignment Gamma (reduce (s, t0, t1)) C <->
    apptype Gamma (pure_abs (bodyF s t0 t1)) (Bterm s) C.
Proof.
  intros. unfold reduce. split.
  - apply apptype_complete.
  - apply apptype_sound.
Qed.

Lemma reduce_arrow_step :
  forall (s t0 t1 : term) (Gamma : environment) (A C : poly_type),
    type_assignment Gamma (reduce (s, t0, t1)) (poly_arr A C) ->
    (exists A0, type_assignment Gamma (pure_abs (bodyF s t0 t1)) (poly_arr A0 (poly_arr A C)) /\
                type_assignment Gamma (Bterm s) A0) \/
    (exists U V, apptype Gamma (pure_abs (bodyF s t0 t1)) (Bterm s) (poly_abs U) /\
                 poly_arr A C = subst_poly_type (scons V poly_var) U).
Proof.
  intros s t0 t1 Gamma A C H.
  apply reduce_typing_iff in H.
  inversion H; subst.
  - left. eexists. split; eassumption.
  - right. eexists. eexists. split; [eassumption|reflexivity].
Qed.


Lemma reduce_body_step :
  forall (s t0 t1 : term) (Gamma : environment) (A C : poly_type),
    type_assignment Gamma (reduce (s, t0, t1)) (poly_arr A C) ->
    (exists A0,
       type_assignment (A0 :: Gamma) (bodyF s t0 t1) (poly_arr A C) /\
       type_assignment Gamma (Bterm s) A0) \/
    (exists A0 U V,
       abstype Gamma (bodyF s t0 t1) (poly_abs U) /\
       poly_arr A0 (poly_arr A C) = subst_poly_type (scons V poly_var) U /\
       type_assignment Gamma (Bterm s) A0) \/
    (exists U V,
       apptype Gamma (pure_abs (bodyF s t0 t1)) (Bterm s) (poly_abs U) /\
       poly_arr A C = subst_poly_type (scons V poly_var) U).
Proof.
  intros s t0 t1 Gamma A C H.
  destruct (reduce_arrow_step s t0 t1 Gamma A C H) as
    [[A0 [Habs Harg]] | [U [V [Happ Heq]]]].
  - apply abstype_complete in Habs.
    destruct (abstype_arrow_step Gamma (bodyF s t0 t1) A0 (poly_arr A C) Habs)
      as [Hbody | [U [V [HabsU Heq]]]].
    + left. exists A0. split; assumption.
    + right. left. exists A0, U, V. split; [exact HabsU | split; assumption].
  - right. right. exists U, V. split; assumption.
Qed.


(* --- apptype inversion steps at arrow and poly_abs --- *)

Lemma apptype_arrow_step :
  forall (Gamma : environment) (M N : pure_term) (A C : poly_type),
    apptype Gamma M N (poly_arr A C) ->
    (exists A0, type_assignment Gamma M (poly_arr A0 (poly_arr A C)) /\
                type_assignment Gamma N A0) \/
    (exists U V, apptype Gamma M N (poly_abs U) /\
                 poly_arr A C = subst_poly_type (scons V poly_var) U).
Proof.
  intros Gamma M N A C H. inversion H; subst.
  - left. eexists. split; eassumption.
  - right. eexists. eexists. split; [eassumption|reflexivity].
Qed.

Lemma apptype_polyabs_step :
  forall (Gamma : environment) (M N : pure_term) (s : poly_type),
    apptype Gamma M N (poly_abs s) ->
    (exists A, type_assignment Gamma M (poly_arr A (poly_abs s)) /\
               type_assignment Gamma N A) \/
    apptype (map (ren_poly_type S) Gamma) M N s \/
    (exists U V, apptype Gamma M N (poly_abs U) /\
                 poly_abs s = subst_poly_type (scons V poly_var) U).
Proof.
  intros Gamma M N s H. inversion H; subst.
  - left. eexists. split; eassumption.
  - right. left. eassumption.
  - right. right. eexists. eexists. split; [eassumption|reflexivity].
Qed.


(* --- Inversion steps at atomic types --- *)

Lemma functype_atom_step :
  forall (Gamma : environment) (u : pure_term) (n : nat),
    functype Gamma u (poly_var n) ->
    exists U V, functype Gamma u (poly_abs U) /\
                poly_var n = subst_poly_type (scons V poly_var) U.
Proof.
  intros Gamma u n H. inversion H; subst.
  - eexists. eexists. split; [eassumption|reflexivity].
Qed.

Lemma eqfun_type_atom_step :
  forall (Gamma : environment) (u : pure_term) (n : nat),
    eqfun_type Gamma u (poly_var n) ->
    exists U V, eqfun_type Gamma u (poly_abs U) /\
                poly_var n = subst_poly_type (scons V poly_var) U.
Proof.
  intros Gamma u n H. inversion H; subst.
  - eexists. eexists. split; [eassumption|reflexivity].
Qed.

Lemma abstype_atom_step :
  forall (Gamma : environment) (M : pure_term) (n : nat),
    abstype Gamma M (poly_var n) ->
    exists U V, abstype Gamma M (poly_abs U) /\
                poly_var n = subst_poly_type (scons V poly_var) U.
Proof.
  intros Gamma M n H. inversion H; subst.
  - eexists. eexists. split; [eassumption|reflexivity].
Qed.

Lemma gadget_type_atom_step :
  forall (Gamma : environment) (u v : pure_term) (n : nat),
    gadget_type Gamma u v (poly_var n) ->
    (exists A, type_assignment Gamma (gadget_arg v) A /\
               functype Gamma u (poly_arr A (poly_var n))) \/
    (exists U V, gadget_type Gamma u v (poly_abs U) /\
                 poly_var n = subst_poly_type (scons V poly_var) U).
Proof.
  intros Gamma u v n H. inversion H; subst.
  - left. eexists. split; eassumption.
  - right. eexists. eexists. split; [eassumption|reflexivity].
Qed.

Lemma eqtest_type_atom_step :
  forall (Gamma : environment) (u v : pure_term) (n : nat),
    eqtest_type Gamma u v (poly_var n) ->
    (exists A, type_assignment Gamma v A /\
               eqfun_type Gamma u (poly_arr A (poly_var n))) \/
    (exists U V, eqtest_type Gamma u v (poly_abs U) /\
                 poly_var n = subst_poly_type (scons V poly_var) U).
Proof.
  intros Gamma u v n H. inversion H; subst.
  - left. eexists. split; eassumption.
  - right. eexists. eexists. split; [eassumption|reflexivity].
Qed.

Lemma apptype_atom_step :
  forall (Gamma : environment) (M N : pure_term) (n : nat),
    apptype Gamma M N (poly_var n) ->
    (exists A, type_assignment Gamma M (poly_arr A (poly_var n)) /\
               type_assignment Gamma N A) \/
    (exists U V, apptype Gamma M N (poly_abs U) /\
                 poly_var n = subst_poly_type (scons V poly_var) U).
Proof.
  intros Gamma M N n H. inversion H; subst.
  - left. eexists. split; eassumption.
  - right. eexists. eexists. split; [eassumption|reflexivity].
Qed.

Lemma vtype_atom_step :
  forall (Gamma : environment) (x : nat) (T : poly_type) (n : nat),
    vtype Gamma x T (poly_var n) ->
    T = poly_var n \/
    (exists U V, vtype Gamma x T (poly_abs U) /\
                 poly_var n = subst_poly_type (scons V poly_var) U).
Proof.
  intros Gamma x T n H. inversion H; subst.
  - left. reflexivity.
  - right. eexists. eexists. split; [eassumption|reflexivity].
Qed.


(* --- Rigidity of first-order variable types --- *)

Definition gen_iter (k : nat) (T : poly_type) : poly_type :=
  iter_abs k (ren_poly_type (fun n => n + k) T).

Lemma gen_iter_zero : forall T, gen_iter 0 T = T.
Proof.
  intro T. unfold gen_iter. simpl.
  transitivity (ren_poly_type (fun n => n) T).
  - apply ren_poly_type_ext. intro n. simpl. lia.
  - apply ren_poly_type_id.
Qed.

Lemma gen_iter_succ :
  forall (k : nat) (T : poly_type),
    gen_iter (S k) T = poly_abs (gen_iter k (ren_poly_type S T)).
Proof.
  intros k T. unfold gen_iter. simpl.
  f_equal. f_equal.
  rewrite ren_poly_type_comp.
  apply ren_poly_type_ext. intro n. simpl. lia.
Qed.

Lemma subst_free_ren :
  forall (T : poly_type) (sigma : nat -> poly_type) (c : nat),
    no_abs T ->
    subst_free sigma (ren_poly_type (fun n => n + c) T) =
    subst_free (fun n => sigma (n + c)) T.
Proof.
  induction T as [n | A IHA B IHB | A IHA]; intros sigma c H; simpl in *.
  - reflexivity.
  - destruct H as [HA HB]. now rewrite IHA, IHB.
  - destruct H.
Qed.

Lemma subst_free_shift :
  forall (T : poly_type) (c : nat),
    no_abs T ->
    subst_free (fun n => poly_var (n + c)) T =
    ren_poly_type (fun n => n + c) T.
Proof.
  induction T as [n | A IHA B IHB | A IHA]; intros c H; simpl in *.
  - reflexivity.
  - destruct H as [HA HB]. now rewrite IHA, IHB.
  - destruct H.
Qed.

Lemma subst_up_iter_ren_shift :
  forall (k : nat) (T : poly_type) (V : poly_type),
    no_abs T ->
    subst_poly_type (up_iter k (scons V poly_var))
      (ren_poly_type (fun n => n + S k) T) =
    ren_poly_type (fun n => n + k) T.
Proof.
  intros k T V HT.
  rewrite (no_abs_subst (ren_poly_type (fun n => n + S k) T)
             (no_abs_ren T (fun n => n + S k) HT)
             (up_iter k (scons V poly_var))).
  rewrite (subst_free_ren T (up_iter k (scons V poly_var)) (S k) HT).
  assert (Hpt : forall n,
            up_iter k (scons V poly_var) (n + S k) = poly_var (n + k)).
  { intro n.
    rewrite (up_iter_ge k (scons V poly_var) (n + S k)) by lia.
    replace (n + S k - k) with (S n) by lia.
    simpl. reflexivity. }
  rewrite (subst_free_ext T _ _ Hpt).
  rewrite (subst_free_shift T k HT).
  reflexivity.
Qed.

Lemma subst_gen_iter_ren :
  forall (k : nat) (T : poly_type) (V : poly_type),
    no_abs T ->
    subst_poly_type (scons V poly_var) (gen_iter k (ren_poly_type S T)) =
    gen_iter k T.
Proof.
  intros k T V HT.
  unfold gen_iter.
  rewrite push_subst_iter.
  f_equal.
  rewrite ren_poly_type_comp.
  assert (Hshift :
    ren_poly_type (fun n => S n + k) T =
    ren_poly_type (fun n => n + S k) T).
  { apply ren_poly_type_ext. intro n. simpl. lia. }
  rewrite Hshift.
  apply subst_up_iter_ren_shift. exact HT.
Qed.

Lemma vtype_no_abs_form :
  forall (Gamma : environment) (x : nat) (T C : poly_type),
    no_abs T -> vtype Gamma x T C ->
    exists k, C = gen_iter k T.
Proof.
  intros Gamma x T C HT H. induction H.
  - exists 0. symmetry. apply gen_iter_zero.
  - destruct (IHvtype (no_abs_ren T S HT)) as [k Hk].
    exists (S k). rewrite Hk.
    symmetry. apply gen_iter_succ.
  - destruct (IHvtype HT) as [k Hk].
    destruct k as [|k'].
    + rewrite gen_iter_zero in Hk. exfalso.
      destruct T as [n | A B | A]; simpl in HT; try discriminate Hk; contradiction.
    + rewrite gen_iter_succ in Hk.
      injection Hk as HU.
      exists k'. rewrite HU.
      apply subst_gen_iter_ren. exact HT.
Qed.


(* --- Rigidity under inserted binders --- *)

Lemma vtype_insert_S_no_abs :
  forall (X : poly_type) (Gamma : environment) (n : nat)
         (T C : poly_type),
    n < length Gamma -> no_abs T ->
    vtype (insert_env 0 X Gamma) (S n) T C ->
    exists k, C = gen_iter k T.
Proof.
  intros X Gamma n T C Hlen HT Hv.
  apply (vtype_no_abs_form (insert_env 0 X Gamma) (S n) T C).
  - exact HT.
  - exact Hv.
Qed.

Lemma vtype_insert_S_atom_eq :
  forall (X : poly_type) (Gamma : environment) (n : nat) (T : poly_type),
    n < length Gamma -> no_abs T ->
    vtype (insert_env 0 X Gamma) (S n) T (poly_var n) ->
    T = poly_var n.
Proof.
  intros X Gamma n T Hlen HT Hv.
  destruct (vtype_insert_S_no_abs X Gamma n T (poly_var n) Hlen HT Hv) as [k Hk].
  unfold gen_iter in Hk.
  destruct T as [m | A B | A]; simpl in HT.
  - destruct k as [|k]; [|discriminate].
    simpl in Hk. injection Hk as Hmn.
    rewrite Hmn. f_equal. lia.
  - destruct k as [|k]; [simpl in Hk; discriminate|discriminate].
  - contradiction.
Qed.


(* --- The bottom-variable polymorphic escape --- *)

Lemma vtype_bottom_any :
  forall (Gamma : environment) (x : nat) (T : poly_type),
    nth_error Gamma x = Some bottom ->
    vtype Gamma x bottom T.
Proof.
  intros Gamma x T H.
  refine (@vtype_inst Gamma x bottom (poly_var 0) T _).
  apply vtype_var. exact H.
Qed.

Lemma type_assignment_bottom_any :
  forall (Gamma : environment) (x : nat) (T : poly_type),
    nth_error Gamma x = Some bottom ->
    type_assignment Gamma (pure_var x) T.
Proof.
  intros. apply vtype_sound with (T := bottom).
  apply vtype_bottom_any. exact H.
Qed.

(* --- Arrow-skeleton (arrowish) rigidity --- *)

Definition arrowish (C : poly_type) : Prop :=
  exists k A B, C = iter_abs k (poly_arr A B).

Lemma arrowish_arr :
  forall A B, arrowish (poly_arr A B).
Proof. intros. exists 0, A, B. reflexivity. Qed.

Lemma arrowish_wrap :
  forall C, arrowish C -> arrowish (poly_abs C).
Proof.
  intros C [k [A [B H]]]. exists (S k), A, B.
  simpl. rewrite H. reflexivity.
Qed.

Lemma arrowish_ren :
  forall (T : poly_type) (xi : nat -> nat),
    arrowish T -> arrowish (ren_poly_type xi T).
Proof.
  intros T xi [k [A [B H]]]. subst.
  revert xi A B.
  induction k as [|k IH]; intros xi A B.
  - simpl. exists 0, (ren_poly_type xi A), (ren_poly_type xi B). reflexivity.
  - simpl.
    destruct (IH (scons 0 (funcomp S xi)) A B) as [j [A' [B' Hj]]].
    exists (S j), A', B'. rewrite Hj. reflexivity.
Qed.

Lemma arrowish_subst :
  forall (T : poly_type) (sigma : nat -> poly_type),
    arrowish T -> arrowish (subst_poly_type sigma T).
Proof.
  intros T sigma [k [A [B H]]]. subst.
  rewrite push_subst_iter.
  exists k, (subst_poly_type (up_iter k sigma) A),
         (subst_poly_type (up_iter k sigma) B).
  reflexivity.
Qed.

Lemma arrowish_polyabs_body :
  forall (U : poly_type), arrowish (poly_abs U) -> arrowish U.
Proof.
  intros U [k [A [B H]]].
  destruct k as [|k].
  - simpl in H. discriminate.
  - simpl in H. injection H as HU. exists k, A, B. exact HU.
Qed.

Lemma vtype_arrowish :
  forall (Gamma : environment) (x : nat) (T C : poly_type),
    vtype Gamma x T C -> arrowish T -> arrowish C.
Proof.
  intros Gamma x T C H.
  induction H; intros HT.
  - exact HT.
  - destruct (IHvtype (arrowish_ren T S HT)) as [j [A [B Hj]]].
    exists (S j), A, B. simpl. rewrite Hj. reflexivity.
  - apply arrowish_subst.
    apply arrowish_polyabs_body.
    exact (IHvtype HT).
Qed.

Lemma codom_arrowish :
  forall (Gamma : environment) (v : pure_term) (C : poly_type),
    codom Gamma v C -> arrowish C.
Proof.
  intros Gamma v C H. induction H.
  - exists 0, A, B. reflexivity.
  - destruct IHcodom as [j [A [B Hj]]].
    exists (S j), A, B. simpl. rewrite Hj. reflexivity.
  - apply arrowish_subst.
    apply arrowish_polyabs_body.
    exact IHcodom.
Qed.

(* --- Normal-form (NF) rigidity for gadget applications --- *)

Definition NF (T : poly_type) : Prop :=
  exists k X Y, T = iter_abs k (poly_arr X Y) /\ arrowish Y.

Definition Good (E : environment) (x : nat) : Prop :=
  forall (A0 T : poly_type),
    nth_error (A0 :: E) x = Some T -> arrowish T.

Lemma Good_ren :
  forall (E : environment) (x : nat),
    Good E x -> Good (map (ren_poly_type S) E) x.
Proof.
  intros E x HG A0 T Hn.
  destruct x as [|x'].
  - (* x = 0: the entry is A0 itself *)
    simpl in Hn. injection Hn as HT. subst T.
    exact (HG A0 A0 eq_refl).
  - (* x = S x': entry comes from E, renamed *)
    simpl in Hn.
    rewrite nth_error_map in Hn.
    destruct (nth_error E x') as [U|] eqn:EU; simpl in Hn; try discriminate.
    injection Hn as HT. subst T.
    apply arrowish_ren.
    exact (HG A0 U EU).
Qed.

Lemma NF_arr :
  forall X Y, arrowish Y -> NF (poly_arr X Y).
Proof. intros X Y H. exists 0, X, Y. split; [reflexivity|exact H]. Qed.

Lemma NF_wrap :
  forall T, NF T -> NF (poly_abs T).
Proof.
  intros T [k [X [Y [HT HY]]]].
  exists (S k), X, Y. split; [|exact HY].
  simpl. rewrite HT. reflexivity.
Qed.

Lemma NF_body :
  forall U, NF (poly_abs U) -> NF U.
Proof.
  intros U [k [X [Y [H HY]]]].
  destruct k as [|k].
  - simpl in H. discriminate.
  - simpl in H. injection H as HU.
    exists k, X, Y. split; [exact HU|exact HY].
Qed.

Lemma NF_subst :
  forall (T : poly_type) (sigma : nat -> poly_type),
    NF T -> NF (subst_poly_type sigma T).
Proof.
  intros T sigma [k [X [Y [HT HY]]]]. subst T.
  rewrite push_subst_iter.
  exists k, (subst_poly_type (up_iter k sigma) X),
         (subst_poly_type (up_iter k sigma) Y).
  split.
  - reflexivity.
  - apply arrowish_subst. exact HY.
Qed.

Lemma abvar_NF :
  forall (E : environment) (x : nat) (C : poly_type),
    Good E x -> abvar E x C -> NF C.
Proof.
  intros E x C HG H.
  induction H.
  - (* abvar_core *)
    destruct (proj1 (type_assignment_var_iff _ _ _) H) as [T [Hn Hv]].
    apply NF_arr.
    exact (vtype_arrowish (A :: Gamma) x T B Hv (HG A T Hn)).
  - (* abvar_gen *)
    apply NF_wrap. apply IHabvar.
    apply Good_ren. exact HG.
  - (* abvar_inst *)
    apply NF_subst. apply NF_body. apply IHabvar. exact HG.
Qed.

Lemma Good_cons_one :
  forall (A : poly_type) (Gamma : environment),
    arrowish A -> Good (A :: Gamma) 1.
Proof.
  intros A Gamma HA A0 T Hn. simpl in Hn.
  injection Hn as HT. subst T. exact HA.
Qed.

Lemma apptype_gadget_codom :
  forall (E : environment) (M N : pure_term) (C : poly_type),
    apptype E M N C -> M = gadget_T1 -> Good E 1 -> arrowish C.
Proof.
  intros E M N C H.
  induction H; intros HM HG.
  - (* apptype_app *)
    rewrite HM in H. unfold gadget_T1 in H.
    pose proof (proj1 (abvar_iff Gamma 1 (poly_arr A C)) H) as Hab.
    destruct (abvar_NF Gamma 1 (poly_arr A C) HG Hab)
      as [k [X [Y [HEq' HY]]]].
    destruct k as [|k].
    + simpl in HEq'. injection HEq' as _ HC. rewrite HC. exact HY.
    + simpl in HEq'. discriminate.
  - (* apptype_gen *)
    apply arrowish_wrap. apply IHapptype.
    + exact HM.
    + apply Good_ren. exact HG.
  - (* apptype_inst *)
    apply arrowish_subst. apply arrowish_polyabs_body.
    apply IHapptype; [exact HM|exact HG].
Qed.

Lemma apptype_gadget_codom_cons :
  forall (A : poly_type) (Gamma : environment) (u : pure_term) (C : poly_type),
    arrowish A ->
    apptype (A :: Gamma) gadget_T1 (gadget_T2 u) C -> arrowish C.
Proof.
  intros A Gamma u C HA H.
  exact (apptype_gadget_codom (A :: Gamma) gadget_T1 (gadget_T2 u) C H
           eq_refl (Good_cons_one A Gamma HA)).
Qed.

(* --- Abstractions (hence functype) always have arrow-structured types --- *)

Lemma type_assignment_abs_arrowish :
  forall (Gamma : environment) (L : pure_term) (C : poly_type),
    (exists M, L = pure_abs M) -> type_assignment Gamma L C -> arrowish C.
Proof.
  intros Gamma L C HL H. induction H.
  - (* var *) destruct HL as [Mabs HMabs]. simpl in HMabs. discriminate.
  - (* app *) destruct HL as [Mabs HMabs]. simpl in HMabs. discriminate.
  - (* abs *) apply arrowish_arr.
  - (* inst *)
    exact (arrowish_subst s (scons t poly_var)
             (arrowish_polyabs_body s (IHtype_assignment HL))).
  - (* gen *) apply arrowish_wrap. apply IHtype_assignment. exact HL.
Qed.

Lemma functype_arrowish :
  forall (Gamma : environment) (u : pure_term) (C : poly_type),
    functype Gamma u C -> arrowish C.
Proof.
  intros Gamma u C H.
  pose proof (functype_sound Gamma u C H) as Hs.
  unfold gadget_fun in Hs.
  exact (type_assignment_abs_arrowish Gamma (pure_abs (gadget_body u)) C
           (ex_intro _ (gadget_body u) eq_refl) Hs).
Qed.

(* --- Poly-type substitution: extensionality, renaming and composition --- *)

Lemma subst_poly_type_ext :
  forall (T : poly_type) (sigma tau : nat -> poly_type),
    (forall n, sigma n = tau n) ->
    subst_poly_type sigma T = subst_poly_type tau T.
Proof.
  induction T as [n | A IHA B IHB | A IHA]; intros sigma tau H; simpl.
  - apply H.
  - now rewrite (IHA sigma tau H), (IHB sigma tau H).
  - f_equal. apply IHA. intro n. destruct n; simpl.
    + reflexivity.
    + unfold funcomp. now rewrite H.
Qed.

Lemma subst_ren :
  forall (T : poly_type) (sigma : nat -> poly_type) (xi : nat -> nat),
    subst_poly_type sigma (ren_poly_type xi T) =
    subst_poly_type (fun n => sigma (xi n)) T.
Proof.
  induction T as [n | A IHA B IHB | A IHA]; intros sigma xi; simpl.
  - reflexivity.
  - now rewrite IHA, IHB.
  - f_equal.
    rewrite IHA.
    apply subst_poly_type_ext. intro n. destruct n; simpl.
    + reflexivity.
    + unfold funcomp, scons. reflexivity.
Qed.

Lemma ren_subst :
  forall (T : poly_type) (sigma : nat -> poly_type) (xi : nat -> nat),
    ren_poly_type xi (subst_poly_type sigma T) =
    subst_poly_type (fun n => ren_poly_type xi (sigma n)) T.
Proof.
  induction T as [n | A IHA B IHB | A IHA]; intros sigma xi; simpl.
  - reflexivity.
  - now rewrite IHA, IHB.
  - f_equal.
    rewrite IHA.
    apply subst_poly_type_ext. intro n. destruct n; simpl.
    + reflexivity.
    + transitivity
        (ren_poly_type (fun k => scons 0 (funcomp S xi) (S k)) (sigma n)).
      * apply ren_poly_type_comp.
      * transitivity (ren_poly_type (fun k => S (xi k)) (sigma n)).
        -- apply ren_poly_type_ext. intro k. unfold funcomp, scons. reflexivity.
        -- symmetry. apply ren_poly_type_comp.
Qed.

Lemma subst_up_ren_S :
  forall (T : poly_type) (sigma : nat -> poly_type),
    subst_poly_type (up_subst sigma) (ren_poly_type S T) =
    ren_poly_type S (subst_poly_type sigma T).
Proof.
  intros T sigma.
  rewrite subst_ren.
  rewrite ren_subst.
  apply subst_poly_type_ext. intro n. unfold up_subst, funcomp. reflexivity.
Qed.

Lemma subst_poly_type_comp :
  forall (T : poly_type) (sigma tau : nat -> poly_type),
    subst_poly_type sigma (subst_poly_type tau T) =
    subst_poly_type (fun n => subst_poly_type sigma (tau n)) T.
Proof.
  induction T as [n | A IHA B IHB | A IHA]; intros sigma tau; simpl.
  - reflexivity.
  - now rewrite IHA, IHB.
  - f_equal.
    rewrite IHA.
    apply subst_poly_type_ext. intro n. destruct n; simpl.
    + reflexivity.
    + change (subst_poly_type (up_subst sigma) (ren_poly_type S (tau n)) =
              ren_poly_type S (subst_poly_type sigma (tau n))).
      rewrite subst_up_ren_S. reflexivity.
Qed.

(* --- Head non-atomicity for gadget application + functype core normal form --- *)

Lemma apptype_head_not_atom_gen :
  forall (E : environment) (M N : pure_term) (C : poly_type) (u : pure_term),
    apptype E M N C ->
    M = pure_var 0 -> N = lift 0 u ->
    forall (n : nat) (X : poly_type) (Gamma : environment),
      E = X :: Gamma -> X = poly_var n -> False.
Proof.
  intros E M N C u H.
  induction H; intros HM HN n X Gamma0 HE HX.
  - (* apptype_app *)
    subst Gamma. subst X. rewrite HM in H.
    destruct (proj1 (type_assignment_var_iff _ _ _) H) as [T [Hn Hv]].
    simpl in Hn. injection Hn as HT. subst T.
    destruct (vtype_no_abs_form (poly_var n :: Gamma0) 0 (poly_var n) (poly_arr A C) I Hv) as [k Hk].
    destruct k as [|k]; simpl in Hk; discriminate.
  - (* apptype_gen *)
    subst Gamma. subst X.
    refine (IHapptype HM HN (S n) (poly_var (S n))
              (map (ren_poly_type S) Gamma0) eq_refl eq_refl).
  - (* apptype_inst *)
    eapply IHapptype; [exact HM|exact HN|exact HE|exact HX].
Qed.

Lemma apptype_var0_head_not_atom :
  forall (E : environment) (u : pure_term) (C : poly_type),
    apptype E (pure_var 0) (lift 0 u) C ->
    forall (n : nat) (X : poly_type) (Gamma : environment),
      E = X :: Gamma -> X = poly_var n -> False.
Proof.
  intros E u C H.
  exact (apptype_head_not_atom_gen E (pure_var 0) (lift 0 u) C u H
           eq_refl eq_refl).
Qed.

Lemma subst_poly_type_id :
  forall (T : poly_type), subst_poly_type poly_var T = T.
Proof.
  induction T as [n | A IHA B IHB | A IHA]; simpl.
  - reflexivity.
  - now rewrite IHA, IHB.
  - f_equal.
    change (subst_poly_type (up_subst poly_var) A = A).
    transitivity (subst_poly_type poly_var A).
    + apply subst_poly_type_ext. intro n. destruct n; simpl; reflexivity.
    + apply IHA.
Qed.

Lemma functype_core_repr :
  forall (Gamma : environment) (u : pure_term) (T : poly_type),
    functype Gamma u T ->
    exists (k : nat) (Gamma0 : environment) (X C : poly_type)
           (sigma : nat -> poly_type),
      T = iter_abs k (subst_poly_type sigma (poly_arr X C)) /\
      apptype (X :: Gamma0) gadget_T1 (gadget_T2 u) C.
Proof.
  intros Gamma u T H. induction H.
  - (* functype_core *)
    exists 0, Gamma, A, C, poly_var. split.
    + simpl. rewrite !subst_poly_type_id. reflexivity.
    + exact H.
  - (* functype_gen *)
    destruct IHfunctype as [k [Gamma0 [X [C0 [sigma [HT Hap]]]]]].
    exists (S k), Gamma0, X, C0, sigma. split.
    + simpl. rewrite HT. reflexivity.
    + exact Hap.
  - (* functype_inst *)
    destruct IHfunctype as [k [Gamma0 [X [C0 [sigma [HT Hap]]]]]].
    destruct k as [|k'].
    + simpl in HT. discriminate.
    + simpl in HT. injection HT as HU.
      exists k', Gamma0, X, C0,
        (fun j => subst_poly_type (up_iter k' (scons V poly_var)) (sigma j)).
      split.
      * rewrite HU. rewrite push_subst_iter.
        change (iter_abs k'
          (subst_poly_type (up_iter k' (scons V poly_var))
             (subst_poly_type sigma (poly_arr X C0))) =
          iter_abs k'
          (subst_poly_type
             (fun j => subst_poly_type (up_iter k' (scons V poly_var)) (sigma j))
             (poly_arr X C0))).
        rewrite subst_poly_type_comp. reflexivity.
      * exact Hap.
Qed.

(* --- Safe types and the arrowish/Safe/open-core trichotomy --- *)

Definition Safe (X : poly_type) : Prop :=
  forall sigma, arrowish (subst_poly_type sigma X) -> arrowish X.

Definition OpenCore (X : poly_type) : Prop :=
  exists k j, X = iter_abs k (poly_var j) /\ k <= j.

Lemma Safe_arrowish :
  forall X, arrowish X -> Safe X.
Proof. intros X H sigma _. exact H. Qed.

Lemma Safe_wrap :
  forall X, Safe X -> Safe (poly_abs X).
Proof.
  intros X HS sigma H.
  apply arrowish_wrap. apply (HS (up_subst sigma)).
  apply (arrowish_polyabs_body (subst_poly_type (up_subst sigma) X)).
  change (arrowish (poly_abs (subst_poly_type (up_subst sigma) X))).
  cbn [subst_poly_type]. exact H.
Qed.

Lemma subst_spine_below :
  forall (k j : nat), j < k ->
    forall sigma,
      subst_poly_type sigma (iter_abs k (poly_var j)) = iter_abs k (poly_var j).
Proof.
  intros k j Hk sigma.
  rewrite push_subst_iter.
  cbn [subst_poly_type].
  rewrite (up_iter_lt k sigma j Hk).
  reflexivity.
Qed.

Lemma Safe_spine_below :
  forall (k j : nat), j < k -> Safe (iter_abs k (poly_var j)).
Proof.
  intros k j Hk sigma H.
  rewrite subst_spine_below in H by exact Hk.
  exact H.
Qed.

Lemma arrowish_ren_inv :
  forall (X : poly_type) (xi : nat -> nat),
    arrowish (ren_poly_type xi X) -> arrowish X.
Proof.
  induction X as [n | A IHA B IHB | W IH]; intros xi H.
  - simpl in H. destruct H as [k [P [Q HPQ]]].
    destruct k; simpl in HPQ; discriminate.
  - apply arrowish_arr.
  - simpl in H.
    apply arrowish_wrap.
    apply (IH (scons 0 (funcomp S xi))).
    apply (arrowish_polyabs_body (ren_poly_type (scons 0 (funcomp S xi)) W)).
    exact H.
Qed.

Lemma Safe_ren_inv :
  forall X, Safe (ren_poly_type S X) -> Safe X.
Proof.
  intros X HS tau Htau.
  apply (@arrowish_ren_inv X S).
  apply (HS (scons (poly_var 0) (funcomp (ren_poly_type S) tau))).
  rewrite subst_ren.
  change (arrowish (subst_poly_type (fun n => ren_poly_type S (tau n)) X)).
  rewrite <- ren_subst.
  apply arrowish_ren. exact Htau.
Qed.

Lemma trichotomy :
  forall X, arrowish X \/ Safe X \/ OpenCore X.
Proof.
  induction X as [n | A IHA B IHB | W IH].
  - right. right. exists 0, n. split; [reflexivity|lia].
  - left. apply arrowish_arr.
  - destruct IH as [HA | [HS | [k [j [Hk Hkj]]]]].
    + left. apply arrowish_wrap. exact HA.
    + right. left. apply Safe_wrap. exact HS.
    + subst W.
      destruct (Nat.eq_dec j k) as [Heq | Hneq].
      * subst j.
        right. left.
        change (Safe (iter_abs (S k) (poly_var k))).
        apply Safe_spine_below. lia.
      * right. right. exists (S k), j. split.
        -- reflexivity.
        -- lia.
Qed.

(* --- Renaming under iterated binders (needed for gen stability) --- *)

Fixpoint liftren (k : nat) (xi : nat -> nat) : nat -> nat :=
  match k with
  | 0 => xi
  | S k' => liftren k' (scons 0 (funcomp S xi))
  end.

Lemma renable_iter :
  forall (k : nat) (xi : nat -> nat) (T : poly_type),
    ren_poly_type xi (iter_abs k T) =
    iter_abs k (ren_poly_type (liftren k xi) T).
Proof.
  induction k as [|k IH]; intros xi T; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma liftren_ext :
  forall (k : nat) (xi xj : nat -> nat),
    (forall n, xi n = xj n) ->
    forall n, liftren k xi n = liftren k xj n.
Proof.
  induction k as [|k IH]; intros xi xj H n; simpl.
  - apply H.
  - apply IH. intro p. destruct p; simpl.
    + reflexivity.
    + unfold funcomp. now rewrite H.
Qed.

Lemma liftren_prefix :
  forall (k m n : nat),
    liftren k (fun j => if j <? m then j else j + 1) n =
    if n <? (m + k) then n else n + 1.
Proof.
  induction k as [|k IH]; intros m n; simpl.
  - replace (m + 0) with m by lia. reflexivity.
  - assert (Heq : forall p,
        scons 0 (funcomp S (fun j => if j <? m then j else j + 1)) p =
        (fun j => if j <? (m + 1) then j else j + 1) p).
    { intro p. destruct p as [|p']; simpl.
      - rewrite (proj2 (Nat.ltb_lt 0 (m + 1))) by lia. reflexivity.
      - unfold funcomp. cbn [scons].
        destruct (Nat.ltb p' m) eqn:E.
        + apply Nat.ltb_lt in E.
          rewrite (proj2 (Nat.ltb_lt (S p') (m + 1))) by lia. reflexivity.
        + apply Nat.ltb_ge in E.
          rewrite (proj2 (Nat.ltb_ge (S p') (m + 1))) by lia. lia. }
    rewrite (liftren_ext k _ _ Heq n).
    rewrite (IH (m + 1) n).
    replace (m + 1 + k) with (m + S k) by lia. reflexivity.
Qed.

Lemma liftren_S :
  forall (k n : nat),
    liftren k S n = if n <? k then n else n + 1.
Proof.
  induction k as [|k IH]; intros n; simpl.
  - lia.
  - assert (Heq : forall p,
        scons 0 (funcomp S S) p =
        (fun j => if j <? 1 then j else j + 1) p).
    { intro p. destruct p as [|p']; simpl.
      - reflexivity.
      - unfold funcomp. cbn [scons]. lia. }
    rewrite (liftren_ext k _ _ Heq n).
    rewrite (liftren_prefix k 1 n).
    replace (1 + k) with (S k) by lia. reflexivity.
Qed.

Lemma ren_S_iter_var_open :
  forall (k j : nat), k <= j ->
    ren_poly_type S (iter_abs k (poly_var j)) =
    iter_abs k (poly_var (j + 1)).
Proof.
  intros k j Hkj.
  rewrite renable_iter.
  f_equal.
  cbn [ren_poly_type].
  rewrite (liftren_S k j).
  rewrite (proj2 (Nat.ltb_ge j k)) by lia.
  reflexivity.
Qed.

(* --- Open-spine vtype invariant and Safe heads --- *)

Lemma vtype_spine_form :
  forall (Gamma : environment) (x : nat) (X C : poly_type),
    vtype Gamma x X C ->
    forall d k j,
      X = iter_abs k (poly_var j) -> j = k + d ->
      exists m, C = iter_abs m (poly_var (m + d)).
Proof.
  intros Gamma x X C H.
  induction H; intros d k j HX Hj.
  - (* vtype_var *)
    exists k. rewrite HX. rewrite <- Hj. reflexivity.
  - (* vtype_gen *)
    rewrite HX in IHvtype.
    assert (Hrep' : exists k' j',
              ren_poly_type S (iter_abs k (poly_var j)) =
              iter_abs k' (poly_var j') /\ j' = k' + (d + 1)).
    { exists k, (k + (d + 1)). split.
      - assert (Hle : k <= j) by lia.
        rewrite (ren_S_iter_var_open k j Hle). do 2 f_equal. lia.
      - lia. }
    destruct Hrep' as [k' [j' [HE Hj']]].
    destruct (IHvtype (d + 1) k' j' HE Hj') as [m Hm].
    exists (S m). rewrite Hm.
    simpl. do 3 f_equal. lia.
  - (* vtype_inst *)
    destruct (IHvtype d k j HX Hj) as [m Hm].
    destruct m as [|m'].
    + simpl in Hm. discriminate.
    + simpl in Hm. injection Hm as HU.
      exists m'. rewrite HU.
      rewrite push_subst_iter.
      cbn [subst_poly_type].
      rewrite (up_iter_ge m' (scons V poly_var) (S (m' + d))) by lia.
      replace (S (m' + d) - m') with (S d) by lia.
      cbn [funcomp]. cbn [scons]. cbn [ren_poly_type].
      do 2 f_equal. lia.
Qed.

Lemma vtype_open_core_impossible_arr :
  forall (X : poly_type) (Gamma : environment) (x : nat) (A B : poly_type),
    OpenCore X -> vtype Gamma x X (poly_arr A B) -> False.
Proof.
  intros X Gamma x A B [k [j [HX Hkj]]] H.
  destruct (vtype_spine_form Gamma x X (poly_arr A B) H (j - k) k j HX (ltac:(lia)))
    as [m Hm].
  simpl in Hm.
  destruct m as [|m']; simpl in Hm; discriminate.
Qed.

Lemma vtype_arrow_safe :
  forall (X : poly_type) (Gamma : environment) (x : nat) (A B : poly_type),
    vtype Gamma x X (poly_arr A B) -> Safe X.
Proof.
  intros X Gamma x A B H.
  destruct (trichotomy X) as [Ha | [Hs | Ho]].
  - apply Safe_arrowish. exact Ha.
  - exact Hs.
  - exfalso. eapply vtype_open_core_impossible_arr; eauto.
Qed.

(* --- Safe heads, gadget codomain rigidity, and Bterm arrowishness --- *)

Lemma apptype_var0_head_safe_gen :
  forall (E : environment) (M N : pure_term) (C : poly_type) (u : pure_term),
    apptype E M N C ->
    M = pure_var 0 -> N = lift 0 u ->
    forall (X : poly_type) (Gamma : environment),
      E = X :: Gamma -> Safe X.
Proof.
  intros E M N C u H.
  induction H; intros HM HN X Gamma0 HE.
  - (* apptype_app *)
    subst Gamma. rewrite HM in H.
    destruct (proj1 (type_assignment_var_iff _ _ _) H) as [T [Hn Hv]].
    simpl in Hn. injection Hn as HT. subst T.
    exact (vtype_arrow_safe X (X :: Gamma0) 0 A C Hv).
  - (* apptype_gen *)
    destruct Gamma as [|G0 Gs].
    + simpl in HE. discriminate.
    + simpl in HE. injection HE as HX HG. subst X. subst Gamma0.
      apply Safe_ren_inv.
      exact (IHapptype HM HN (ren_poly_type S G0)
               (map (ren_poly_type S) Gs) eq_refl).
  - (* apptype_inst *)
    exact (IHapptype HM HN X Gamma0 HE).
Qed.

Lemma apptype_var0_head_safe :
  forall (X : poly_type) (Gamma : environment) (u : pure_term) (C : poly_type),
    apptype (X :: Gamma) (pure_var 0) (lift 0 u) C -> Safe X.
Proof.
  intros X Gamma u C H.
  exact (apptype_var0_head_safe_gen (X :: Gamma) (pure_var 0) (lift 0 u)
           C u H eq_refl eq_refl X Gamma eq_refl).
Qed.

Lemma apptype_gadget_head_safe_gen :
  forall (E : environment) (M N : pure_term) (C : poly_type) (u : pure_term),
    apptype E M N C ->
    N = gadget_T2 u ->
    forall (X : poly_type) (Gamma : environment),
      E = X :: Gamma -> Safe X.
Proof.
  intros E M N C u H.
  induction H; intros HN X Gamma0 HE.
  - (* apptype_app *)
    subst Gamma. rewrite HN in H0. unfold gadget_T2 in H0.
    pose proof (apptype_complete (X :: Gamma0) (pure_var 0) (lift 0 u) A H0)
      as Hap.
    exact (apptype_var0_head_safe_gen (X :: Gamma0) (pure_var 0) (lift 0 u)
             A u Hap eq_refl eq_refl X Gamma0 eq_refl).
  - (* apptype_gen *)
    destruct Gamma as [|G0 Gs].
    + simpl in HE. discriminate.
    + simpl in HE. injection HE as HX HG. subst X. subst Gamma0.
      apply Safe_ren_inv.
      exact (IHapptype HN (ren_poly_type S G0)
               (map (ren_poly_type S) Gs) eq_refl).
  - (* apptype_inst *)
    exact (IHapptype HN X Gamma0 HE).
Qed.

Lemma apptype_gadget_head_safe :
  forall (X : poly_type) (Gamma : environment) (u : pure_term) (C : poly_type),
    apptype (X :: Gamma) gadget_T1 (gadget_T2 u) C -> Safe X.
Proof.
  intros X Gamma u C H.
  exact (apptype_gadget_head_safe_gen (X :: Gamma) gadget_T1 (gadget_T2 u)
           C u H eq_refl X Gamma eq_refl).
Qed.

Lemma functype_arrow_codom_safe :
  forall (Gamma : environment) (u : pure_term) (A C : poly_type),
    arrowish A -> functype Gamma u (poly_arr A C) -> arrowish C.
Proof.
  intros Gamma u A C HA Hf.
  destruct (functype_core_repr Gamma u (poly_arr A C) Hf)
    as [k [Gamma0 [X [C0 [sigma [HT Hap]]]]]].
  destruct k as [|k].
  - simpl in HT. injection HT as HA' HC'.
    rewrite HC'. apply arrowish_subst.
    pose proof (apptype_gadget_head_safe X Gamma0 u C0 Hap) as HS.
    assert (HX : arrowish X).
    { apply (HS sigma). rewrite <- HA'. exact HA. }
    exact (apptype_gadget_codom_cons X Gamma0 u C0 HX Hap).
  - simpl in HT. discriminate.
Qed.

Lemma gadget_type_arrowish :
  forall (Gamma : environment) (u v : pure_term) (C : poly_type),
    gadget_type Gamma u v C -> arrowish C.
Proof.
  intros Gamma u v C H. induction H.
  - (* gadget_type_core *)
    apply (functype_arrow_codom_safe Gamma u A C).
    + apply (type_assignment_abs_arrowish Gamma (gadget_arg v) A).
      * exists (lift 0 v). unfold gadget_arg. reflexivity.
      * exact H.
    + exact H0.
  - (* gadget_type_gen *)
    apply arrowish_wrap. exact IHgadget_type.
  - (* gadget_type_inst *)
    apply arrowish_subst. apply arrowish_polyabs_body. exact IHgadget_type.
Qed.

Lemma Bterm_arr_arrowish :
  forall (Gamma : environment) (u v : term) (A : poly_type),
    type_assignment Gamma (Bterm (arr u v)) A -> arrowish A.
Proof.
  intros Gamma u v A H.
  apply (gadget_type_arrowish Gamma (Bterm u) (Bterm v) A).
  apply (proj1 (gadget_type_iff Gamma (Bterm u) (Bterm v) A)).
  unfold Bterm, E' in H. simpl in H. exact H.
Qed.

(* --- The array-source scheme cannot be bottom (no forall-a.a escape) --- *)

Lemma arrowish_not_bottom :
  forall T, arrowish T -> T <> bottom.
Proof.
  intros T [k [A [B H]]] Hb. subst T.
  destruct k as [|k].
  - simpl in Hb. unfold bottom in Hb. discriminate.
  - simpl in Hb. unfold bottom in Hb. injection Hb as Hk.
    destruct k as [|k]; simpl in Hk; discriminate.
Qed.

Lemma Bterm_arr_not_bottom :
  forall (Gamma : environment) (u v : term),
    type_assignment Gamma (Bterm (arr u v)) bottom -> False.
Proof.
  intros Gamma u v H.
  pose proof (Bterm_arr_arrowish Gamma u v bottom H) as Ha.
  exact (arrowish_not_bottom bottom Ha eq_refl).
Qed.

Lemma reduce_binder_arrowish :
  forall (Gamma : environment) (u v : term) (t0 t1 : term)
         (A C : poly_type),
    type_assignment Gamma (Bterm (arr u v)) A ->
    arrowish A.
Proof.
  intros. exact (Bterm_arr_arrowish Gamma u v A H).
Qed.

(* --- Completeness scaffolding for the array-source case --- *)

Lemma apptype_second_typing :
  forall (E : environment) (M N : pure_term) (C : poly_type),
    apptype E M N C -> exists E' A, type_assignment E' N A.
Proof.
  intros E M N C H. induction H.
  - exists Gamma, A. exact H0.
  - destruct IHapptype as [E' [A HA]]. exists E', A. exact HA.
  - destruct IHapptype as [E' [A HA]]. exists E', A. exact HA.
Qed.

Lemma reduce_gives_arrowish_bterm :
  forall (u v t0 t1 : term) (Gamma : environment) (C : poly_type),
    type_assignment Gamma (reduce (arr u v, t0, t1)) C ->
    exists Gamma' A,
      type_assignment Gamma' (Bterm (arr u v)) A /\ arrowish A.
Proof.
  intros u v t0 t1 Gamma C H.
  apply reduce_typing_iff in H.
  destruct (apptype_second_typing Gamma (pure_abs (bodyF (arr u v) t0 t1))
              (Bterm (arr u v)) C H) as [Gamma' [A HA]].
  exists Gamma', A. split; [exact HA|].
  exact (Bterm_arr_arrowish Gamma' u v A HA).
Qed.

(* --- Assembly: only array-source completeness remains --- *)

Theorem reduction_from_arr_complete :
  (forall (u v t0 t1 : term),
      SysF_TYP (reduce (arr u v, t0, t1)) ->
      LU2SemiU (arr u v, t0, t1)) ->
  LU2SemiU ⪯ SysF_TYP.
Proof.
  intros Harr. exists reduce. intro p.
  destruct p as [[s t0] t1]. split.
  - apply reduction_forward.
  - intro Htyp. destruct s as [n | u v].
    + apply LU2SemiU_atom.
    + apply Harr. exact Htyp.
Qed.

(* --- IMPORTANT: the array-source gadget admits forall-a.a->a --- *)

Lemma Bterm_arr00_poly :
  exists Gamma : environment,
    type_assignment Gamma (Bterm (arr (atom 0) (atom 0)))
      (poly_abs (poly_arr (poly_var 0) (poly_var 0))).
Proof.
  exists (poly_var 0 :: bottom :: nil).
  unfold Bterm, E', fB. simpl.
  apply gadget_type_sound.
  refine (@gadget_type_gen (poly_var 0 :: bottom :: nil)
            (pure_var 1) (pure_var 1) (poly_arr (poly_var 0) (poly_var 0)) _).
  change (gadget_type (poly_var 1 :: bottom :: nil)
            (pure_var 1) (pure_var 1) (poly_arr (poly_var 0) (poly_var 0))).
  refine (@gadget_type_core (poly_var 1 :: bottom :: nil)
            (pure_var 1) (pure_var 1)
            (poly_arr (poly_var 0) (poly_var 0))
            (poly_arr (poly_var 0) (poly_var 0)) _ _).
  - (* type of the argument lambda: abs (var 2) : var0 -> var0 *)
    change (type_assignment (poly_var 1 :: bottom :: nil)
              (pure_abs (pure_var 2)) (poly_arr (poly_var 0) (poly_var 0))).
    eapply type_assignment_abs.
    apply type_assignment_bottom_any. simpl. reflexivity.
  - (* functype of the first gadget component *)
    change (functype (poly_var 1 :: bottom :: nil) (pure_var 1)
              (poly_arr (poly_arr (poly_var 0) (poly_var 0))
                        (poly_arr (poly_var 0) (poly_var 0)))).
    refine (@functype_core (poly_var 1 :: bottom :: nil) (pure_var 1)
              (poly_arr (poly_var 0) (poly_var 0))
              (poly_arr (poly_var 0) (poly_var 0)) _).
    change (apptype
      (poly_arr (poly_var 0) (poly_var 0) :: poly_var 1 :: bottom :: nil)
      gadget_T1 (gadget_T2 (pure_var 1)) (poly_arr (poly_var 0) (poly_var 0))).
    refine (@apptype_app
      (poly_arr (poly_var 0) (poly_var 0) :: poly_var 1 :: bottom :: nil)
      gadget_T1 (gadget_T2 (pure_var 1)) (poly_var 0)
      (poly_arr (poly_var 0) (poly_var 0)) _ _).
    + (* gadget_T1 : var0 -> (var0 -> var0) *)
      change (type_assignment
        (poly_arr (poly_var 0) (poly_var 0) :: poly_var 1 :: bottom :: nil)
        (pure_abs (pure_var 1)) (poly_arr (poly_var 0) (poly_arr (poly_var 0) (poly_var 0)))).
      eapply type_assignment_abs.
      apply type_assignment_var. simpl. reflexivity.
    + (* gadget_T2 var1 : var0 *)
      change (type_assignment
        (poly_arr (poly_var 0) (poly_var 0) :: poly_var 1 :: bottom :: nil)
        (pure_app (pure_var 0) (pure_var 2)) (poly_var 0)).
      eapply type_assignment_app.
      * apply type_assignment_var. simpl. reflexivity.
      * apply type_assignment_bottom_any. simpl. reflexivity.
Qed.

(* --- Machine-checked refutation of the candidate reduction term --- *)

Definition T0 : poly_type := poly_arr (poly_var 0) (poly_var 0).
Definition A0 : poly_type := poly_abs (poly_arr (poly_var 0) (poly_var 0)).

Lemma gadget_var1_poly :
  forall X : poly_type,
    type_assignment (X :: bottom :: nil)
      (gadget (pure_var 1) (pure_var 1)) A0.
Proof.
  intro X.
  apply gadget_type_sound.
  refine (@gadget_type_gen (X :: bottom :: nil)
            (pure_var 1) (pure_var 1) T0 _).
  change (gadget_type (ren_poly_type S X :: bottom :: nil)
            (pure_var 1) (pure_var 1) T0).
  refine (@gadget_type_core (ren_poly_type S X :: bottom :: nil)
            (pure_var 1) (pure_var 1) T0 T0 _ _).
  - change (type_assignment (ren_poly_type S X :: bottom :: nil)
              (pure_abs (pure_var 2)) T0).
    eapply type_assignment_abs.
    apply type_assignment_bottom_any. simpl. reflexivity.
  - change (functype (ren_poly_type S X :: bottom :: nil) (pure_var 1)
              (poly_arr T0 T0)).
    refine (@functype_core (ren_poly_type S X :: bottom :: nil) (pure_var 1)
              T0 T0 _).
    change (apptype (T0 :: ren_poly_type S X :: bottom :: nil)
              gadget_T1 (gadget_T2 (pure_var 1)) T0).
    refine (@apptype_app
      (T0 :: ren_poly_type S X :: bottom :: nil)
      gadget_T1 (gadget_T2 (pure_var 1)) (poly_var 0) T0 _ _).
    + change (type_assignment
        (T0 :: ren_poly_type S X :: bottom :: nil)
        (pure_abs (pure_var 1)) (poly_arr (poly_var 0) T0)).
      eapply type_assignment_abs.
      apply type_assignment_var. simpl. reflexivity.
    + change (type_assignment
        (T0 :: ren_poly_type S X :: bottom :: nil)
        (pure_app (pure_var 0) (pure_var 2)) (poly_var 0)).
      eapply type_assignment_app.
      * apply type_assignment_var. simpl. reflexivity.
      * apply type_assignment_bottom_any. simpl. reflexivity.
Qed.

Definition Gamma0 : environment := T0 :: bottom :: nil.
Definition E0 : environment := A0 :: Gamma0.

Lemma spurious_leaves :
  (type_assignment Gamma0 (Bterm (arr (atom 0) (atom 0))) A0) /\
  (type_assignment E0 (lift 0 (Rterm (arr (atom 0) (atom 0)))) (poly_arr T0 T0)) /\
  (type_assignment E0 (lift 0 (Rterm (atom 0))) T0) /\
  (type_assignment E0 (lift 0 (EQtest (arr (atom 0) (atom 0)))) (poly_arr T0 T0)) /\
  (type_assignment E0 (lift 0 (EQtest (atom 0))) T0) /\
  (type_assignment E0 (CHECK (atom 0)) T0) /\
  (type_assignment E0 (LINK (arr (atom 0) (atom 0))) (poly_arr T0 T0)) /\
  (type_assignment E0 (pure_var 1) T0).
Proof.
  assert (HB : type_assignment Gamma0 (Bterm (arr (atom 0) (atom 0))) A0).
  { unfold Bterm, E', fB. simpl. unfold Gamma0.
    exact (gadget_var1_poly T0). }
  assert (HRs : type_assignment Gamma0 (Rterm (arr (atom 0) (atom 0)))
                                (poly_arr T0 T0)).
  { unfold Rterm, E', fR. simpl.
    eapply type_assignment_gadget.
    - apply type_assignment_var. unfold Gamma0. simpl. reflexivity.
    - apply type_assignment_var. unfold Gamma0. simpl. reflexivity. }
  assert (HRt : type_assignment Gamma0 (Rterm (atom 0)) T0).
  { unfold Rterm, E', fR. simpl.
    apply type_assignment_var. unfold Gamma0. simpl. reflexivity. }
  assert (HBt : type_assignment Gamma0 (Bterm (atom 0)) T0).
  { unfold Bterm, E', fB. simpl.
    apply type_assignment_bottom_any. unfold Gamma0. simpl. reflexivity. }
  assert (HBsInst : type_assignment Gamma0 (Bterm (arr (atom 0) (atom 0)))
                                    (poly_arr T0 T0)).
  { change (type_assignment Gamma0 (Bterm (arr (atom 0) (atom 0)))
              (subst_poly_type (scons T0 poly_var) (poly_arr (poly_var 0) (poly_var 0)))).
    eapply type_assignment_inst. exact HB. }
  assert (HEQs : type_assignment Gamma0 (EQtest (arr (atom 0) (atom 0)))
                                   (poly_arr T0 T0)).
  { unfold EQtest. apply (eqtest_sound Gamma0 _ _ (poly_arr T0 T0) HRs HBsInst). }
  assert (HEQt : type_assignment Gamma0 (EQtest (atom 0)) T0).
  { unfold EQtest. apply (eqtest_sound Gamma0 _ _ T0 HRt HBt). }
  assert (HLRs : type_assignment E0 (lift 0 (Rterm (arr (atom 0) (atom 0))))
                                   (poly_arr T0 T0)).
  { change (type_assignment (insert_env 0 A0 Gamma0)
              (lift 0 (Rterm (arr (atom 0) (atom 0)))) (poly_arr T0 T0)).
    apply (type_assignment_lift Gamma0 _ _ HRs 0 A0). }
  assert (HLRt : type_assignment E0 (lift 0 (Rterm (atom 0))) T0).
  { change (type_assignment (insert_env 0 A0 Gamma0)
              (lift 0 (Rterm (atom 0))) T0).
    apply (type_assignment_lift Gamma0 _ _ HRt 0 A0). }
  assert (HLEQs : type_assignment E0 (lift 0 (EQtest (arr (atom 0) (atom 0))))
                                    (poly_arr T0 T0)).
  { change (type_assignment (insert_env 0 A0 Gamma0)
              (lift 0 (EQtest (arr (atom 0) (atom 0)))) (poly_arr T0 T0)).
    apply (type_assignment_lift Gamma0 _ _ HEQs 0 A0). }
  assert (HLEQt : type_assignment E0 (lift 0 (EQtest (atom 0))) T0).
  { change (type_assignment (insert_env 0 A0 Gamma0)
              (lift 0 (EQtest (atom 0))) T0).
    apply (type_assignment_lift Gamma0 _ _ HEQt 0 A0). }
  assert (HxT0 : type_assignment E0 (pure_var 0) T0).
  { change (type_assignment E0 (pure_var 0)
              (subst_poly_type (scons (poly_var 0) poly_var)
                 (poly_arr (poly_var 0) (poly_var 0)))).
    eapply type_assignment_inst.
    apply type_assignment_var. unfold E0, Gamma0. simpl. reflexivity. }
  assert (HxArr : type_assignment E0 (pure_var 0) (poly_arr T0 T0)).
  { change (type_assignment E0 (pure_var 0)
              (subst_poly_type (scons T0 poly_var)
                 (poly_arr (poly_var 0) (poly_var 0)))).
    eapply type_assignment_inst.
    apply type_assignment_var. unfold E0, Gamma0. simpl. reflexivity. }
  assert (Hv1 : type_assignment E0 (pure_var 1) T0).
  { apply type_assignment_var. unfold E0, Gamma0. simpl. reflexivity. }
  assert (Hv2 : type_assignment E0 (pure_var 2) T0).
  { apply type_assignment_bottom_any. unfold E0, Gamma0. simpl. reflexivity. }
  assert (Hcheck : type_assignment E0 (CHECK (atom 0)) T0).
  { unfold CHECK, Rterm, E', fR. simpl.
    eapply type_assignment_app.
    - eapply type_assignment_gadget.
      + exact HLRt.
      + exact Hv1.
    - exact HxT0. }
  assert (Hlink : type_assignment E0 (LINK (arr (atom 0) (atom 0))) (poly_arr T0 T0)).
  { unfold LINK. apply (eqtest_sound E0 _ _ (poly_arr T0 T0) HxArr HLRs). }
  repeat split; assumption.
Qed.

Lemma reduce_arr00_typable :
  SysF_TYP (reduce (arr (atom 0) (atom 0), atom 0, atom 0)).
Proof.
  destruct spurious_leaves as
    [HB [HLRs [HLRt [HLEQs [HLEQt [Hcheck [Hlink Hd]]]]]]].
  unfold SysF_TYP.
  exists Gamma0. eexists.
  cbn [reduce].
  eapply type_assignment_app.
  - eapply type_assignment_abs.
    unfold bodyF.
    eapply type_assignment_gadget.
    + exact Hcheck.
    + eapply type_assignment_gadget.
      * exact Hcheck.
      * eapply type_assignment_gadget.
        -- exact Hlink.
        -- eapply type_assignment_gadget.
           ++ exact HLEQs.
           ++ eapply type_assignment_gadget.
              ** exact HLEQt.
              ** eapply type_assignment_gadget.
                 --- exact HLEQt.
                 --- exact Hd.
  - exact HB.
Qed.

Lemma reduce_candidate_incomplete :
  ~ (forall p : term * term * term,
       SysF_TYP (reduce p) -> LU2SemiU p).
Proof.
  intro H.
  apply occurs_unsolvable.
  apply H.
  exact reduce_arr00_typable.
Qed.

(* --- Reduction to first-order type-level semi-unification --- *)

Fixpoint decode_term (A : poly_type) : term :=
  match A with
  | poly_var n => atom n
  | poly_arr A B => arr (decode_term A) (decode_term B)
  | poly_abs _ => atom 0
  end.

Lemma decode_encode :
  forall (u : term), decode_term (encode_term u) = u.
Proof.
  induction u as [n | u IHu v IHv]; simpl.
  - reflexivity.
  - now rewrite IHu, IHv.
Qed.

Lemma encode_decode_noabs :
  forall (A : poly_type), no_abs A -> encode_term (decode_term A) = A.
Proof.
  induction A as [n | A IHA B IHB | A IHA]; intros H; simpl.
  - reflexivity.
  - destruct H as [HA HB]. now rewrite IHA, IHB.
  - destruct H.
Qed.

Lemma encode_term_inj :
  forall (u v : term), encode_term u = encode_term v -> u = v.
Proof.
  induction u as [n | u1 IHu1 u2 IHu2]; intros v H; destruct v as [m | v1 v2]; simpl in H.
  - injection H as Hnm. subst. reflexivity.
  - discriminate.
  - discriminate.
  - injection H as H1 H2. now rewrite (IHu1 v1 H1), (IHu2 v2 H2).
Qed.

Lemma enc_as_subst :
  forall (T : nat -> poly_type) (u : term),
    enc T u = subst_poly_type T (encode_term u).
Proof.
  induction u as [n | u IHu v IHv]; simpl.
  - reflexivity.
  - now rewrite IHu, IHv.
Qed.

Lemma enc_ext :
  forall (T U : nat -> poly_type) (u : term),
    (forall n, T n = U n) -> enc T u = enc U u.
Proof.
  induction u as [n | u IHu v IHv]; intros H; simpl.
  - apply H.
  - now rewrite IHu, IHv.
Qed.

Lemma subst_enc_decode :
  forall (T sigma : nat -> poly_type) (phi psi : valuation) (u : term),
    (forall n, T n = encode_term (phi n)) ->
    (forall n, sigma n = encode_term (psi n)) ->
    subst_poly_type sigma (enc T u) =
    encode_term (substitute psi (substitute phi u)).
Proof.
  intros T sigma phi psi u HT Hs.
  rewrite (enc_ext T (fun n => encode_term (phi n)) u HT).
  rewrite (enc_as_subst (fun n => encode_term (phi n)) u).
  rewrite (subst_poly_type_ext
             (subst_poly_type (fun n => encode_term (phi n)) (encode_term u))
             sigma (fun n => encode_term (psi n)))
    by (intro n; apply Hs).
  symmetry.
  rewrite encode_substitute.
  rewrite encode_substitute.
  reflexivity.
Qed.

Lemma enc_decode :
  forall (T : nat -> poly_type) (phi : valuation) (u : term),
    (forall n, T n = encode_term (phi n)) ->
    enc T u = encode_term (substitute phi u).
Proof.
  intros T phi u HT.
  rewrite (enc_ext T (fun n => encode_term (phi n)) u HT).
  rewrite (enc_as_subst (fun n => encode_term (phi n)) u).
  rewrite encode_substitute.
  reflexivity.
Qed.

Definition TY2SemiU (s t0 t1 : term) : Prop :=
  exists (T sigma0 sigma1 : nat -> poly_type),
    (forall n, no_abs (T n)) /\
    (forall n, no_abs (sigma0 n)) /\
    (forall n, no_abs (sigma1 n)) /\
    subst_poly_type sigma0 (enc T s) = enc T t0 /\
    subst_poly_type sigma1 (enc T s) = enc T t1.

Lemma TY2SemiU_iff_LU2SemiU :
  forall (s t0 t1 : term),
    TY2SemiU s t0 t1 <-> LU2SemiU (s, t0, t1).
Proof.
  intros s t0 t1. split.
  - intros [T [sigma0 [sigma1 [HT [Hs0 [Hs1 [H0 H1]]]]]]].
    pose (phi := fun n => decode_term (T n)).
    pose (psi0 := fun n => decode_term (sigma0 n)).
    pose (psi1 := fun n => decode_term (sigma1 n)).
    assert (HTeq : forall n, T n = encode_term (phi n)).
    { intro n. unfold phi. symmetry. apply encode_decode_noabs. apply HT. }
    assert (Hs0eq : forall n, sigma0 n = encode_term (psi0 n)).
    { intro n. unfold psi0. symmetry. apply encode_decode_noabs. apply Hs0. }
    assert (Hs1eq : forall n, sigma1 n = encode_term (psi1 n)).
    { intro n. unfold psi1. symmetry. apply encode_decode_noabs. apply Hs1. }
    exists phi, psi0, psi1. split.
    + apply encode_term_inj.
      transitivity (subst_poly_type sigma0 (enc T s)).
      * symmetry. apply (subst_enc_decode T sigma0 phi psi0 s HTeq Hs0eq).
      * transitivity (enc T t0).
        -- exact H0.
        -- apply (enc_decode T phi t0 HTeq).
    + apply encode_term_inj.
      transitivity (subst_poly_type sigma1 (enc T s)).
      * symmetry. apply (subst_enc_decode T sigma1 phi psi1 s HTeq Hs1eq).
      * transitivity (enc T t1).
        -- exact H1.
        -- apply (enc_decode T phi t1 HTeq).
  - intros [phi [psi0 [psi1 [H0 H1]]]].
    pose (T := fun n => encode_term (phi n)).
    pose (sigma0 := fun n => encode_term (psi0 n)).
    pose (sigma1 := fun n => encode_term (psi1 n)).
    exists T, sigma0, sigma1.
    assert (HTeq : forall n, T n = encode_term (phi n)) by (intro; reflexivity).
    assert (Hs0eq : forall n, sigma0 n = encode_term (psi0 n)) by (intro; reflexivity).
    assert (Hs1eq : forall n, sigma1 n = encode_term (psi1 n)) by (intro; reflexivity).
    repeat split.
    + intro n. apply no_abs_encode_term.
    + intro n. apply no_abs_encode_term.
    + intro n. apply no_abs_encode_term.
    + transitivity (encode_term (substitute psi0 (substitute phi s))).
      * apply (subst_enc_decode T sigma0 phi psi0 s HTeq Hs0eq).
      * rewrite H0. symmetry. apply (enc_decode T phi t0 HTeq).
    + transitivity (encode_term (substitute psi1 (substitute phi s))).
      * apply (subst_enc_decode T sigma1 phi psi1 s HTeq Hs1eq).
      * rewrite H1. symmetry. apply (enc_decode T phi t1 HTeq).
Qed.

(* --- Encoding equality determines the atom-type map --- *)

Lemma enc_eq_atom_types :
  forall (X Y : nat -> poly_type) (s : term) (n : nat),
    In n (atoms s) -> enc X s = enc Y s -> X n = Y n.
Proof.
  intros X Y s n.
  induction s as [m | u IHu v IHv]; intros Hin Heq; simpl in *.
  - destruct Hin as [Hnm | []]. subst m. exact Heq.
  - apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
    + injection Heq as H1 H2. exact (IHu Hin H1).
    + injection Heq as H1 H2. exact (IHv Hin H2).
Qed.

(* --- Decoding first-order type substitutions --- *)

Lemma decode_subst_noabs :
  forall (A : poly_type) (sigma : nat -> poly_type),
    no_abs A ->
    (forall n, no_abs (sigma n)) ->
    decode_term (subst_poly_type sigma A) =
    substitute (fun n => decode_term (sigma n)) (decode_term A).
Proof.
  induction A as [n | A IHA B IHB | A IHA]; intros sigma HA Hs; simpl in *.
  - reflexivity.
  - destruct HA as [HAA HAB]. now rewrite IHA, IHB.
  - destruct HA.
Qed.

(* --- Atomwise equality implies encoding equality --- *)

Lemma enc_eq_of_atom_eq :
  forall (X Y : nat -> poly_type) (s : term),
    (forall n, In n (atoms s) -> X n = Y n) ->
    enc X s = enc Y s.
Proof.
  induction s as [m | u IHu v IHv]; intros H; simpl in *.
  - apply H. simpl. auto.
  - assert (Hu : forall n, In n (atoms u) -> X n = Y n).
    { intros n Hin. apply H. apply in_app_iff. left. exact Hin. }
    assert (Hv : forall n, In n (atoms v) -> X n = Y n).
    { intros n Hin. apply H. apply in_app_iff. right. exact Hin. }
    rewrite (IHu Hu), (IHv Hv). reflexivity.
Qed.

(* --- Atomwise encoding-equality characterization --- *)

Lemma enc_eq_iff_atom_eq :
  forall (X Y : nat -> poly_type) (s : term),
    enc X s = enc Y s <->
    (forall n, In n (atoms s) -> X n = Y n).
Proof.
  intros X Y s. split.
  - intros H n Hin. eapply enc_eq_atom_types; eauto.
  - apply enc_eq_of_atom_eq.
Qed.

(* --- Why instance requirements cannot force the closure body --- *)

(* Every instance of the closure body T0 -> T0 is an instance of a -> a. *)
Lemma A0_instances :
  forall (U T0 : poly_type),
    exists V : poly_type,
      subst_poly_type (scons U poly_var) (poly_arr T0 T0) =
      subst_poly_type (scons V poly_var)
        (poly_arr (poly_var 0) (poly_var 0)).
Proof.
  intros U T0.
  exists (subst_poly_type (scons U poly_var) T0).
  simpl. reflexivity.
Qed.

(* --- Sharing/generalization dichotomy at the atom level --- *)

(* A rigid atom variable [var 0 : T0] and a bottom leaf [var 1 : bottom]
   can be equality-tested at T0. *)
Lemma eqtest_atom_bottom_rigid :
  forall T0 : poly_type,
    type_assignment (T0 :: bottom :: nil)
      (eqtest (pure_var 1) (pure_var 0)) T0.
Proof.
  intros T0.
  unfold eqtest.
  eapply eqtest_sound.
  - apply type_assignment_bottom_any. simpl. reflexivity.
  - apply type_assignment_var. simpl. reflexivity.
Qed.

(* Generalizing such a term shifts the rigid type by [ren S]; it cannot
   produce the unshifted closure of T0. *)
Lemma eqtest_atom_gen_shifted :
  forall T0 : poly_type,
    type_assignment (T0 :: bottom :: nil)
      (eqtest (pure_var 1) (pure_var 0))
      (poly_abs (ren_poly_type S T0)).
Proof.
  intros T0.
  eapply type_assignment_gen.
  change (type_assignment (map (ren_poly_type S) (T0 :: bottom :: nil))
            (eqtest (pure_var 1) (pure_var 0)) (ren_poly_type S T0)).
  apply (eqtest_atom_bottom_rigid (ren_poly_type S T0)).
Qed.

(* --- Formal gen-vacuity for a single shift --- *)

(* Instantiating a gen-shifted type returns the original type, for ANY
   instantiation type.  This is the formal form of gen-vacuity for
   environment-derived types. *)
Lemma subst_scons_ren_S :
  forall (T U : poly_type),
    subst_poly_type (scons U poly_var) (ren_poly_type S T) = T.
Proof.
  intros T U.
  rewrite subst_ren.
  change (subst_poly_type (fun n => poly_var n) T = T).
  apply subst_poly_type_id.
Qed.


(* --- Exact one-step instance law for a gen-shifted scheme --- *)

Lemma inst_gen_shift :
  forall (T U : poly_type),
    subst_poly_type (scons U poly_var) (poly_abs (ren_poly_type S T)) =
    poly_abs (subst_poly_type (scons (ren_poly_type S U) (funcomp poly_var S)) T).
Proof.
  intros T U. simpl.
  f_equal.
  rewrite subst_ren.
  apply subst_poly_type_ext. intro n. destruct n; simpl.
  - reflexivity.
  - unfold funcomp. reflexivity.
Qed.

(* --- The spurious scheme is a legitimate self-application scheme --- *)

Lemma type_assignment_selfapp_A0 :
  type_assignment nil
    (pure_abs (pure_app (pure_var 0) (pure_var 0)))
    (poly_arr A0 (poly_arr A0 A0)).
Proof.
  refine (@type_assignment_abs nil
            (pure_app (pure_var 0) (pure_var 0))
            A0 (poly_arr A0 A0) _).
  refine (@type_assignment_app (A0 :: nil)
            (pure_var 0) (pure_var 0)
            (poly_arr A0 A0) (poly_arr A0 A0) _ _).
  - change (type_assignment (A0 :: nil) (pure_var 0)
      (subst_poly_type (scons (poly_arr A0 A0) poly_var)
         (poly_arr (poly_var 0) (poly_var 0)))).
    eapply type_assignment_inst.
    apply type_assignment_var. simpl. reflexivity.
  - change (type_assignment (A0 :: nil) (pure_var 0)
      (subst_poly_type (scons A0 poly_var)
         (poly_arr (poly_var 0) (poly_var 0)))).
    eapply type_assignment_inst.
    apply type_assignment_var. simpl. reflexivity.
Qed.

(* --- Self-application is System F typable --- *)

Lemma SysF_TYP_selfapp :
  SysF_TYP (pure_abs (pure_app (pure_var 0) (pure_var 0))).
Proof.
  exists nil, (poly_arr A0 (poly_arr A0 A0)).
  apply type_assignment_selfapp_A0.
Qed.

(* --- A basic typable term --- *)

Lemma SysF_TYP_var : SysF_TYP (pure_var 0).
Proof.
  exists (bottom :: nil), bottom.
  apply type_assignment_var. simpl. reflexivity.
Qed.

(* --- Target --- *)

Theorem reduction : LU2SemiU ⪯ SysF_TYP.
