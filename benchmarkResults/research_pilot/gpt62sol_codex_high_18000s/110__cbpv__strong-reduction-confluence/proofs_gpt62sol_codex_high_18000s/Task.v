From CBPV Require Import StrongReduction AbstractReductionSystems.
From Stdlib Require Import Arith.PeanoNat Logic.Eqdep_dec.

Set Implicit Arguments.

(* The fusion laws use pointwise equality of environments. *)
Local Lemma up_ren_ren n m k (r : ren n m) (s : ren m k) (t : ren n k) :
  (forall x, s (r x) = t x) ->
  forall x, upRen_value_value s (upRen_value_value r x) =
            upRen_value_value t x.
Proof.
  intros H [x|]; [|reflexivity].
  change (Some (s (r x)) = Some (t x)). now rewrite H.
Qed.

Local Lemma up_subst_ren n m k (r : ren n m)
    (s : fin m -> value k) (t : fin n -> value k) :
  (forall x, s (r x) = t x) ->
  forall x, up_value_value s (upRen_value_value r x) =
            up_value_value t x.
Proof.
  intros H [x|]; [|reflexivity].
  change (ren_value shift (s (r x)) = ren_value shift (t x)).
  now rewrite H.
Qed.

Local Lemma ren_ren n :
  (forall (v : value n) m k (r : ren n m) (s : ren m k) (t : ren n k),
      (forall x, s (r x) = t x) ->
      ren_value s (ren_value r v) = ren_value t v) /\
  (forall (c : comp n) m k (r : ren n m) (s : ren m k) (t : ren n k),
      (forall x, s (r x) = t x) ->
      ren_comp s (ren_comp r c) = ren_comp t c).
Proof.
  refine (mutind_val_comp
    (fun n (v : value n) => forall m k (r : ren n m) (s : ren m k) (t : ren n k),
        (forall x, s (r x) = t x) ->
        ren_value s (ren_value r v) = ren_value t v)
    (fun n (c : comp n) => forall m k (r : ren n m) (s : ren m k) (t : ren n k),
        (forall x, s (r x) = t x) ->
        ren_comp s (ren_comp r c) = ren_comp t c)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n);
    intros; cbn; try solve [eauto]; f_equal; eauto using up_ren_ren.
Qed.

Local Lemma subst_ren n :
  (forall (v : value n) m k (r : ren n m)
      (s : fin m -> value k) (t : fin n -> value k),
      (forall x, s (r x) = t x) ->
      subst_value s (ren_value r v) = subst_value t v) /\
  (forall (c : comp n) m k (r : ren n m)
      (s : fin m -> value k) (t : fin n -> value k),
      (forall x, s (r x) = t x) ->
      subst_comp s (ren_comp r c) = subst_comp t c).
Proof.
  refine (mutind_val_comp
    (fun n (v : value n) => forall m k (r : ren n m)
        (s : fin m -> value k) (t : fin n -> value k),
        (forall x, s (r x) = t x) ->
        subst_value s (ren_value r v) = subst_value t v)
    (fun n (c : comp n) => forall m k (r : ren n m)
        (s : fin m -> value k) (t : fin n -> value k),
        (forall x, s (r x) = t x) ->
        subst_comp s (ren_comp r c) = subst_comp t c)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n);
    intros; cbn; try solve [eauto]; f_equal; eauto using up_subst_ren.
Qed.

Local Lemma up_ren_subst n m k (s : fin n -> value m) (r : ren m k)
    (t : fin n -> value k) :
  (forall x, ren_value r (s x) = t x) ->
  forall x, ren_value (upRen_value_value r) (up_value_value s x) =
            up_value_value t x.
Proof.
  intros H [x|]; [|reflexivity].
  change (ren_value (upRen_value_value r) (ren_value shift (s x)) =
          ren_value shift (t x)).
  rewrite <- H.
  rewrite (proj1 (ren_ren _) (s x) _ _ shift (upRen_value_value r)
             (fun y => Some (r y))) by reflexivity.
  symmetry. apply (proj1 (ren_ren _)). reflexivity.
Qed.

Local Lemma ren_subst n :
  (forall (v : value n) m k (s : fin n -> value m)
      (r : ren m k) (t : fin n -> value k),
      (forall x, ren_value r (s x) = t x) ->
      ren_value r (subst_value s v) = subst_value t v) /\
  (forall (c : comp n) m k (s : fin n -> value m)
      (r : ren m k) (t : fin n -> value k),
      (forall x, ren_value r (s x) = t x) ->
      ren_comp r (subst_comp s c) = subst_comp t c).
Proof.
  refine (mutind_val_comp
    (fun n (v : value n) => forall m k (s : fin n -> value m)
        (r : ren m k) (t : fin n -> value k),
        (forall x, ren_value r (s x) = t x) ->
        ren_value r (subst_value s v) = subst_value t v)
    (fun n (c : comp n) => forall m k (s : fin n -> value m)
        (r : ren m k) (t : fin n -> value k),
        (forall x, ren_value r (s x) = t x) ->
        ren_comp r (subst_comp s c) = subst_comp t c)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n);
    intros; cbn; try solve [eauto]; f_equal; eauto using up_ren_subst.
Qed.

Local Lemma up_subst_subst n m k (s : fin n -> value m)
    (r : fin m -> value k) (t : fin n -> value k) :
  (forall x, subst_value r (s x) = t x) ->
  forall x, subst_value (up_value_value r) (up_value_value s x) =
            up_value_value t x.
Proof.
  intros H [x|]; [|reflexivity].
  change (subst_value (up_value_value r) (ren_value shift (s x)) =
          ren_value shift (t x)).
  rewrite <- H.
  rewrite (proj1 (subst_ren _) (s x) _ _ shift (up_value_value r)
             (fun y => ren_value shift (r y))) by reflexivity.
  symmetry. apply (proj1 (ren_subst _)). reflexivity.
Qed.

Local Lemma subst_subst n :
  (forall (v : value n) m k (s : fin n -> value m)
      (r : fin m -> value k) (t : fin n -> value k),
      (forall x, subst_value r (s x) = t x) ->
      subst_value r (subst_value s v) = subst_value t v) /\
  (forall (c : comp n) m k (s : fin n -> value m)
      (r : fin m -> value k) (t : fin n -> value k),
      (forall x, subst_value r (s x) = t x) ->
      subst_comp r (subst_comp s c) = subst_comp t c).
Proof.
  refine (mutind_val_comp
    (fun n (v : value n) => forall m k (s : fin n -> value m)
        (r : fin m -> value k) (t : fin n -> value k),
        (forall x, subst_value r (s x) = t x) ->
        subst_value r (subst_value s v) = subst_value t v)
    (fun n (c : comp n) => forall m k (s : fin n -> value m)
        (r : fin m -> value k) (t : fin n -> value k),
        (forall x, subst_value r (s x) = t x) ->
        subst_comp r (subst_comp s c) = subst_comp t c)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n);
    intros; cbn; try solve [eauto]; f_equal; eauto using up_subst_subst.
Qed.

Local Definition inst {n} (c : comp (S n)) (v : value n) :=
  subst_comp (v .: @var_value n) c.

Local Definition inst_pair {n} (c : comp (S (S n))) (v w : value n) :=
  subst_comp (w .: (v .: @var_value n)) c.

Local Lemma ren_inst n m (r : ren n m) c v :
  ren_comp r (inst c v) =
  inst (ren_comp (upRen_value_value r) c) (ren_value r v).
Proof.
  unfold inst.
  rewrite (proj2 (ren_subst _) c _ _ (v .: @var_value n) r
             (ren_value r v .: fun x => var_value (r x)))
    by (intros [x|]; reflexivity).
  symmetry. apply (proj2 (subst_ren _)). intros [x|]; reflexivity.
Qed.

Local Lemma ren_inst_pair n m (r : ren n m) c v w :
  ren_comp r (inst_pair c v w) =
  inst_pair (ren_comp (upRen_value_value (upRen_value_value r)) c)
    (ren_value r v) (ren_value r w).
Proof.
  unfold inst_pair.
  rewrite (proj2 (ren_subst _) c _ _ (w .: (v .: @var_value n)) r
             (ren_value r w .: (ren_value r v .: fun x => var_value (r x))))
    by (intros [ [x|] | ]; reflexivity).
  symmetry. apply (proj2 (subst_ren _)). intros [ [x|] | ]; reflexivity.
Qed.

Local Lemma up_subst_id n (s : fin n -> value n) :
  (forall x, s x = var_value x) ->
  forall x, up_value_value s x = var_value x.
Proof.
  intros H [x|]; [|reflexivity].
  change (ren_value shift (s x) = @var_value (S n) (Some x)).
  now rewrite H.
Qed.

Local Lemma subst_id n :
  (forall (v : value n) (s : fin n -> value n),
      (forall x, s x = var_value x) -> subst_value s v = v) /\
  (forall (c : comp n) (s : fin n -> value n),
      (forall x, s x = var_value x) -> subst_comp s c = c).
Proof.
  refine (mutind_val_comp
    (fun n v => forall (s : fin n -> value n),
       (forall x, s x = var_value x) -> subst_value s v = v)
    (fun n c => forall (s : fin n -> value n),
       (forall x, s x = var_value x) -> subst_comp s c = c)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n);
    intros; cbn; try solve [eauto]; f_equal; eauto using up_subst_id.
Qed.

Local Lemma subst_inst n m (s : fin n -> value m) c v :
  subst_comp s (inst c v) =
  inst (subst_comp (up_value_value s) c) (subst_value s v).
Proof.
  unfold inst.
  rewrite (proj2 (subst_subst _) c _ _ (v .: @var_value n) s (subst_value s v .: s))
    by (intros [x|]; reflexivity).
  symmetry. apply (proj2 (subst_subst _)). intros [x|]; [|reflexivity].
  change (subst_value (subst_value s v .: @var_value m)
            (ren_value shift (s x)) = s x).
  rewrite (proj1 (subst_ren _) _ _ _ shift _ (@var_value m)) by reflexivity.
  apply (proj1 (subst_id _)). reflexivity.
Qed.

Local Lemma subst_inst_pair n m (s : fin n -> value m) c v w :
  subst_comp s (inst_pair c v w) =
  inst_pair (subst_comp (up_value_value (up_value_value s)) c)
    (subst_value s v) (subst_value s w).
Proof.
  unfold inst_pair.
  rewrite (proj2 (subst_subst _) c _ _ (w .: (v .: @var_value n)) s
             (subst_value s w .: (subst_value s v .: s)))
    by (intros [ [x|] | ]; reflexivity).
  symmetry. apply (proj2 (subst_subst _)). intros [ [x|] | ]; try reflexivity.
  change (subst_value (subst_value s w .: (subst_value s v .: @var_value m))
            (ren_value shift (ren_value shift (s x))) = s x).
  rewrite (proj1 (subst_ren _) (ren_value shift (s x)) _ _ shift
             (subst_value s w .: (subst_value s v .: @var_value m))
             (subst_value s v .: @var_value m)) by reflexivity.
  rewrite (proj1 (subst_ren _) _ _ _ shift _ (@var_value m)) by reflexivity.
  apply (proj1 (subst_id _)). reflexivity.
Qed.

(* Parallel reduction can contract a redex after reducing its immediate parts. *)
Local Reserved Notation "c ⇉ d" (at level 60).
Local Reserved Notation "v ⇉ᵥ w" (at level 60).

Inductive par {n : nat} : comp n -> comp n -> Prop :=
| par_cu : cu ⇉ cu
| par_force v w : v ⇉ᵥ w -> force v ⇉ force w
| par_lambda c d : c ⇉ d -> lambda c ⇉ lambda d
| par_app c d v w : c ⇉ d -> v ⇉ᵥ w -> app c v ⇉ app d w
| par_tuple c d e f : c ⇉ d -> e ⇉ f -> tuple c e ⇉ tuple d f
| par_ret v w : v ⇉ᵥ w -> ret v ⇉ ret w
| par_let c d e f : c ⇉ d -> e ⇉ f -> letin c e ⇉ letin d f
| par_proj b c d : c ⇉ d -> proj b c ⇉ proj b d
| par_case_z v w : v ⇉ᵥ w -> caseZ v ⇉ caseZ w
| par_case_s v w c d e f :
    v ⇉ᵥ w -> c ⇉ d -> e ⇉ f -> caseS v c e ⇉ caseS w d f
| par_case_p v w c d : v ⇉ᵥ w -> c ⇉ d -> caseP v c ⇉ caseP w d
| par_force_beta c d : c ⇉ d -> force (thunk c) ⇉ d
| par_app_beta c d v w :
    c ⇉ d -> v ⇉ᵥ w -> app (lambda c) v ⇉ inst d w
| par_let_beta v w c d :
    v ⇉ᵥ w -> c ⇉ d -> letin (ret v) c ⇉ inst d w
| par_proj_beta b c d e f :
    c ⇉ d -> e ⇉ f -> proj b (tuple c e) ⇉ (if b then d else f)
| par_case_s_beta b v w c d e f :
    v ⇉ᵥ w -> c ⇉ d -> e ⇉ f ->
    caseS (inj b v) c e ⇉ inst (if b then d else f) w
| par_case_p_beta v v' w w' c d :
    v ⇉ᵥ v' -> w ⇉ᵥ w' -> c ⇉ d ->
    caseP (pair v w) c ⇉ inst_pair d v' w'
where "c ⇉ d" := (@par _ c d)
with par_value {n : nat} : value n -> value n -> Prop :=
| par_var x : var_value x ⇉ᵥ var_value x
| par_u : u ⇉ᵥ u
| par_pair v v' w w' : v ⇉ᵥ v' -> w ⇉ᵥ w' -> pair v w ⇉ᵥ pair v' w'
| par_inj b v w : v ⇉ᵥ w -> inj b v ⇉ᵥ inj b w
| par_thunk c d : c ⇉ d -> thunk c ⇉ᵥ thunk d
where "v ⇉ᵥ w" := (@par_value _ v w).

Scheme par_ind_mut := Induction for par Sort Prop
  with par_value_ind_mut := Induction for par_value Sort Prop.
Combined Scheme par_mutind from par_ind_mut, par_value_ind_mut.

Local Hint Constructors par par_value : parallel.

Local Lemma par_refl n :
  (forall v : value n, v ⇉ᵥ v) /\ (forall c : comp n, c ⇉ c).
Proof.
  apply (mutind_val_comp (fun _ v => v ⇉ᵥ v) (fun _ c => c ⇉ c));
    eauto with parallel.
Qed.

Local Lemma par_refl_value n (v : value n) : v ⇉ᵥ v.
Proof. apply (proj1 (par_refl n)). Qed.

Local Lemma par_refl_comp n (c : comp n) : c ⇉ c.
Proof. apply (proj2 (par_refl n)). Qed.

Local Hint Resolve par_refl_value par_refl_comp : parallel.

Local Lemma par_ren n :
  (forall (c d : comp n), c ⇉ d ->
    forall m (r : ren n m), ren_comp r c ⇉ ren_comp r d) /\
  (forall (v w : value n), v ⇉ᵥ w ->
    forall m (r : ren n m), ren_value r v ⇉ᵥ ren_value r w).
Proof.
  apply (par_mutind
    (fun n c d _ => forall m (r : ren n m), ren_comp r c ⇉ ren_comp r d)
    (fun n v w _ => forall m (r : ren n m), ren_value r v ⇉ᵥ ren_value r w));
    intros; cbn; try solve [eauto with parallel].
  - rewrite ren_inst. eauto with parallel.
  - rewrite ren_inst. eauto with parallel.
  - destruct b; cbn;
      [eapply (par_proj_beta true)|eapply (par_proj_beta false)]; eauto.
  - rewrite ren_inst. destruct b; cbn;
      [eapply (par_case_s_beta true)|eapply (par_case_s_beta false)]; eauto.
  - rewrite ren_inst_pair. eauto with parallel.
Qed.

Local Lemma par_up n m (s t : fin n -> value m) :
  (forall x, s x ⇉ᵥ t x) ->
  forall x, up_value_value s x ⇉ᵥ up_value_value t x.
Proof.
  intros H [x|].
  - change (ren_value shift (s x) ⇉ᵥ ren_value shift (t x)).
    now apply (proj2 (par_ren m)).
  - apply par_var.
Qed.

Local Lemma par_subst n :
  (forall (c d : comp n), c ⇉ d ->
    forall m (s t : fin n -> value m), (forall x, s x ⇉ᵥ t x) ->
    subst_comp s c ⇉ subst_comp t d) /\
  (forall (v w : value n), v ⇉ᵥ w ->
    forall m (s t : fin n -> value m), (forall x, s x ⇉ᵥ t x) ->
    subst_value s v ⇉ᵥ subst_value t w).
Proof.
  apply (par_mutind
    (fun n c d _ => forall m (s t : fin n -> value m),
       (forall x, s x ⇉ᵥ t x) -> subst_comp s c ⇉ subst_comp t d)
    (fun n v w _ => forall m (s t : fin n -> value m),
       (forall x, s x ⇉ᵥ t x) -> subst_value s v ⇉ᵥ subst_value t w));
    intros; cbn; try solve [eauto 9 using par_up with parallel].
  - rewrite subst_inst. eauto 9 using par_up with parallel.
  - rewrite subst_inst. eauto 9 using par_up with parallel.
  - destruct b; cbn;
      [eapply (par_proj_beta true)|eapply (par_proj_beta false)]; eauto.
  - rewrite subst_inst. destruct b; cbn;
      [eapply (par_case_s_beta true)|eapply (par_case_s_beta false)];
      eauto using par_up.
  - rewrite subst_inst_pair. eauto 9 using par_up with parallel.
Qed.

Local Lemma par_inst n (c d : comp (S n)) (v w : value n) :
  c ⇉ d -> v ⇉ᵥ w -> inst c v ⇉ inst d w.
Proof.
  intros Hc Hv. apply (proj1 (par_subst _)); [exact Hc|].
  intros [x|]; [apply par_var|exact Hv].
Qed.

Local Lemma par_inst_pair n (c d : comp (S (S n))) (v v' w w' : value n) :
  c ⇉ d -> v ⇉ᵥ v' -> w ⇉ᵥ w' -> inst_pair c v w ⇉ inst_pair d v' w'.
Proof.
  intros Hc Hv Hw. apply (proj1 (par_subst _)); [exact Hc|].
  intros [ [x|] | ]; [apply par_var|exact Hv|exact Hw].
Qed.

(* Complete development contracts the redexes visible in the source term. *)
Local Fixpoint develop_comp {n} (c : comp n) : comp n :=
  match c with
  | cu => cu
  | force v =>
      match v with
      | thunk d => develop_comp d
      | _ => force (develop_value v)
      end
  | lambda d => lambda (develop_comp d)
  | app d v =>
      match d with
      | lambda e => inst (develop_comp e) (develop_value v)
      | _ => app (develop_comp d) (develop_value v)
      end
  | tuple d e => tuple (develop_comp d) (develop_comp e)
  | ret v => ret (develop_value v)
  | letin d e =>
      match d with
      | ret v => inst (develop_comp e) (develop_value v)
      | _ => letin (develop_comp d) (develop_comp e)
      end
  | proj b d =>
      match d with
      | tuple e f => if b then develop_comp e else develop_comp f
      | _ => proj b (develop_comp d)
      end
  | caseZ v => caseZ (develop_value v)
  | caseS v d e =>
      match v with
      | inj b w =>
          inst (if b then develop_comp d else develop_comp e) (develop_value w)
      | _ => caseS (develop_value v) (develop_comp d) (develop_comp e)
      end
  | caseP v d =>
      match v with
      | pair w w' => inst_pair (develop_comp d) (develop_value w) (develop_value w')
      | _ => caseP (develop_value v) (develop_comp d)
      end
  end
with develop_value {n} (v : value n) : value n :=
  match v with
  | var_value x => var_value x
  | u => u
  | pair w w' => pair (develop_value w) (develop_value w')
  | inj b w => inj b (develop_value w)
  | thunk c => thunk (develop_comp c)
  end.

Local Ltac invert_parallel H :=
  inversion H; clear H; subst;
  repeat match goal with
  | E : existT _ _ _ = existT _ _ _ |- _ =>
      apply (inj_pair2_eq_dec Nat.eq_dec) in E; subst
  end.

Local Hint Resolve par_inst par_inst_pair : parallel.

Local Lemma par_develop n :
  (forall (c d : comp n), c ⇉ d -> d ⇉ develop_comp c) /\
  (forall (v w : value n), v ⇉ᵥ w -> w ⇉ᵥ develop_value v).
Proof.
  apply (par_mutind (fun _ c d _ => d ⇉ develop_comp c)
                    (fun _ v w _ => w ⇉ᵥ develop_value v));
    intros; cbn [develop_comp develop_value] in *;
    try solve [eauto with parallel].
  - destruct v; cbn [develop_comp develop_value] in *;
      try solve [apply par_force; exact H].
    invert_parallel p.
    invert_parallel H.
    now apply par_force_beta.
  - destruct c; cbn [develop_comp develop_value] in *;
      try solve [now apply par_app].
    invert_parallel p.
    invert_parallel H.
    now apply par_app_beta.
  - destruct c; cbn [develop_comp develop_value] in *;
      try solve [now apply par_let].
    invert_parallel p.
    invert_parallel H.
    now apply par_let_beta.
  - destruct c; cbn [develop_comp develop_value] in *;
      try solve [now apply par_proj].
    invert_parallel p.
    invert_parallel H.
    now apply par_proj_beta.
  - destruct v; cbn [develop_comp develop_value] in *;
      try solve [now apply par_case_s].
    invert_parallel p.
    invert_parallel H.
    now apply par_case_s_beta.
  - destruct v; cbn [develop_comp develop_value] in *;
      try solve [now apply par_case_p].
    invert_parallel p.
    invert_parallel H.
    now apply par_case_p_beta.
  - destruct b; assumption.
  - apply par_inst; [destruct b|]; assumption.
Qed.


Local Lemma strong_in_parallel n :
  (forall (c d : comp n), c ↪ d -> c ⇉ d) /\
  (forall (v w : value n), v ↪ᵥ w -> v ⇉ᵥ w).
Proof.
  apply (mutind_sstep (fun _ v w _ => v ⇉ᵥ w) (fun _ c d _ => c ⇉ d));
    intros; try solve [eauto with parallel].
  destruct p; subst; eauto with parallel.
  - change (app (lambda c) v ⇉ inst c v). eauto with parallel.
  - change (letin (ret v) c ⇉ inst c v). eauto with parallel.
  - change (caseS (inj b v) c1 c2 ⇉ inst (if b then c1 else c2) v).
    eauto with parallel.
  - change (caseP (pair v1 v2) c ⇉ inst_pair c v1 v2). eauto with parallel.
Qed.

Local Lemma star_transitive {A} {R : A -> A -> Prop} x y z :
  star R x y -> star R y z -> star R x z.
Proof.
  intros Hxy Hyz. induction Hxy; eauto using star.
Qed.

Local Lemma star_single {A} {R : A -> A -> Prop} x y :
  R x y -> star R x y.
Proof. intro H. eapply starStep; [exact H|apply starRefl]. Qed.

Local Lemma star_map {A B} {R : A -> A -> Prop} {S : B -> B -> Prop}
    (f : A -> B) :
  (forall x y, R x y -> S (f x) (f y)) ->
  forall x y, star R x y -> star S (f x) (f y).
Proof.
  intros Hf x y H. induction H; eauto using star.
Qed.

Local Lemma star_map2 {A B C} {R : A -> A -> Prop} {S : B -> B -> Prop}
    {T : C -> C -> Prop} (f : A -> B -> C) :
  (forall x x' y, R x x' -> T (f x y) (f x' y)) ->
  (forall x y y', S y y' -> T (f x y) (f x y')) ->
  forall x x' y y', star R x x' -> star S y y' -> star T (f x y) (f x' y').
Proof.
  intros Hl Hr x x' y y' Hx Hy.
  apply star_transitive with (y := f x' y).
  - eapply (star_map (fun a => f a y)); eauto.
  - eapply (star_map (f x')); eauto.
Qed.

Local Hint Constructors sstep sstep_value : strong.

Local Lemma star_case_s n (v w : value n) (c c' d d' : comp (S n)) :
  v ↪ᵥ* w -> c ↪* c' -> d ↪* d' -> caseS v c d ↪* caseS w c' d'.
Proof.
  intros Hv Hc Hd.
  apply star_transitive with (y := caseS w c d).
  - eapply (star_map (fun a => caseS a c d)); eauto with strong.
  - eapply (star_map2 (caseS w)); eauto with strong.
Qed.

Local Ltac lift_strong :=
  first [assumption |
    lazymatch goal with
    | |- star _ (force _) (force _) => eapply (star_map (@force _))
    | |- star _ (lambda _) (lambda _) => eapply (star_map (@lambda _))
    | |- star _ (app _ _) (app _ _) => eapply (star_map2 (@app _))
    | |- star _ (tuple _ _) (tuple _ _) => eapply (star_map2 (@tuple _))
    | |- star _ (ret _) (ret _) => eapply (star_map (@ret _))
    | |- star _ (letin _ _) (letin _ _) => eapply (star_map2 (@letin _))
    | |- star _ (proj ?b _) (proj ?b _) => eapply (star_map (proj b))
    | |- star _ (caseZ _) (caseZ _) => eapply (star_map (@caseZ _))
    | |- star _ (caseS _ _ _) (caseS _ _ _) => apply star_case_s
    | |- star _ (caseP _ _) (caseP _ _) => eapply (star_map2 (@caseP _))
    | |- star _ (pair _ _) (pair _ _) => eapply (star_map2 (@pair _))
    | |- star _ (inj ?b _) (inj ?b _) => eapply (star_map (inj b))
    | |- star _ (thunk _) (thunk _) => eapply (star_map (@thunk _))
    end; try solve [eauto with strong]; lift_strong].

Local Lemma parallel_in_strong_star n :
  (forall (c d : comp n), c ⇉ d -> c ↪* d) /\
  (forall (v w : value n), v ⇉ᵥ w -> v ↪ᵥ* w).
Proof.
  apply (par_mutind (fun _ c d _ => c ↪* d) (fun _ v w _ => v ↪ᵥ* w));
    intros; try apply starRefl; try solve [lift_strong].
  - apply star_transitive with (y := force (thunk d)).
    + lift_strong.
    + apply star_single, sstepPrimitive, pstepForce.
  - apply star_transitive with (y := app (lambda d) w).
    + lift_strong.
    + apply star_single, sstepPrimitive, pstepApp. reflexivity.
  - apply star_transitive with (y := letin (ret w) d).
    + lift_strong.
    + apply star_single, sstepPrimitive, pstepLetin. reflexivity.
  - apply star_transitive with (y := proj b (tuple d f)).
    + lift_strong.
    + apply star_single, sstepPrimitive, pstepProj. reflexivity.
  - apply star_transitive with (y := caseS (inj b w) d f).
    + lift_strong.
    + apply star_single, sstepPrimitive, pstepCaseS. reflexivity.
  - apply star_transitive with (y := caseP (pair v' w') d).
    + lift_strong.
    + apply star_single, sstepPrimitive, pstepCaseP. reflexivity.
Qed.

Local Lemma diamond_strip {A} {R : A -> A -> Prop} :
  diamond R ->
  forall x z, star R x z -> forall y, R x y ->
    exists2 w, star R y w & R z w.
Proof.
  intros D x z Hxz.
  induction Hxz as [x|x u z Hxu Huz IH]; intros y Hxy.
  - exists y; [apply starRefl|exact Hxy].
  - destruct (D _ _ _ Hxy Hxu) as [v Hyv Huv].
    destruct (IH _ Huv) as [w Hvw Hzw].
    exists w; [eapply starStep; eauto|exact Hzw].
Qed.

Local Lemma diamond_star {A} {R : A -> A -> Prop} :
  diamond R -> confluent R.
Proof.
  intros D x y z Hxy. revert z.
  induction Hxy as [x|x u y Hxu Huy IH]; intros z Hxz.
  - exists z; [exact Hxz|apply starRefl].
  - destruct (diamond_strip D Hxz u Hxu) as [v Huv Hzv].
    destruct (IH _ Huv) as [w Hyw Hvw].
    exists w; [exact Hyw|eapply starStep; eauto].
Qed.

Local Lemma star_simulation {A} {R S : A -> A -> Prop} :
  (forall x y, R x y -> star S x y) ->
  forall x y, star R x y -> star S x y.
Proof.
  intros H x y Hxy. induction Hxy.
  - apply starRefl.
  - eapply star_transitive; eauto.
Qed.

Local Lemma confluence_from_parallel {A} (R P : A -> A -> Prop) :
  diamond P ->
  (forall x y, R x y -> P x y) ->
  (forall x y, P x y -> star R x y) ->
  confluent R.
Proof.
  intros D Hstep Hpar x y z Hxy Hxz.
  assert (Hsim : forall a b, star R a b -> star P a b).
  { apply star_simulation. eauto using star_single. }
  destruct (diamond_star D (Hsim _ _ Hxy) (Hsim _ _ Hxz)) as [w Hyw Hzw].
  exists w; eapply star_simulation; eauto.
Qed.

Theorem confluence n:
   confluent (@sstep n) /\ confluent (@sstep_value n).
Proof.
  split.
  - apply (@confluence_from_parallel _ (@sstep n) (@par n)).
    + intros c d e Hcd Hce. exists (develop_comp c);
        now apply (proj1 (par_develop n)).
    + exact (proj1 (strong_in_parallel n)).
    + exact (proj1 (parallel_in_strong_star n)).
  - apply (@confluence_from_parallel _ (@sstep_value n) (@par_value n)).
    + intros v w u Hvw Hvu. exists (develop_value v);
        now apply (proj2 (par_develop n)).
    + exact (proj2 (strong_in_parallel n)).
    + exact (proj2 (parallel_in_strong_star n)).
Qed.
